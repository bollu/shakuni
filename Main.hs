{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE Strict #-}
import Control.Parallel
import System.Random
import Debug.Trace
import Control.Applicative
import Data.List(sort, nub)
import Data.Proxy
import Control.Monad (replicateM)
import Data.Monoid
import Control.Monad
import qualified Data.Map as M


compose :: Int -> (a -> a) -> (a -> a)
compose 0 f = id
compose n f = f . compose (n - 1) f

-- | Utility library for drawing sparklines

-- | List of characters that represent sparklines
sparkchars :: String
sparkchars = "_▁▂▃▄▅▆▇█"

-- Convert an int to a sparkline character
num2spark :: RealFrac a => a -- ^ Max value
  -> a -- ^ Current value
  -> Char
num2spark maxv curv =
   sparkchars !!
     (floor $ (curv / maxv) * (fromIntegral (length sparkchars - 1)))

series2spark :: RealFrac a => [a] -> String
series2spark vs =
  let maxv = if null vs then 0 else maximum vs
  in map (num2spark maxv) vs

seriesPrintSpark :: RealFrac a => [a] -> IO ()
seriesPrintSpark = putStrLn . series2spark

-- Probabilites
-- ============
type F = Float
-- | probablity density
newtype P = P { unP :: Float } deriving(Num, Show, Eq, Ord)

-- | prob. distributions over space a
newtype D a = D { runD :: a -> P }

-- | Scale the distribution by a float value
dscale :: D a -> Float -> D a
dscale (D d) f = D $ \a -> P $ unP (d a) * f


-- | Multiply probability distributions together
dmul :: D a -> D a -> D a
dmul (D d) (D d') = D $ \a -> d a * d' a

uniform :: Int -> D a
uniform n =
  D $ \_ -> P $ 1.0 / (fromIntegral $ n)

(>$<) :: Contravariant f => (b -> a) -> f a  -> f b
(>$<) = cofmap

instance Contravariant D where
  cofmap f (D d) = D (d . f)

-- | Normal distribution with given mean
normalD :: Float ->  D Float
normalD mu = D $ \f -> P $ exp (- ((f-mu)^2))

-- | Distribution that takes on value x^p for 1 <= x <= 2.  Is normalized
polyD :: Float -> D Float
polyD p = D $ \f -> P $ if 1 <= f && f <= 2 then (f ** p) * (p + 1) / (2 ** (p+1) - 1) else 0

class Contravariant f where
  cofmap :: (b -> a) -> f a -> f b

data PL x where
    Ret :: x -> PL x
    Sample01 :: (Float -> PL x) -> PL x

instance Functor PL where
  fmap f (Ret x) = Ret (f x)
  fmap f (Sample01 r2plx) = Sample01 (\r -> fmap f (r2plx r))

instance Applicative PL where
  pure = return
  (<*>) = ap

instance Monad PL where
  return = Ret
  (Ret x) >>= x2ply = x2ply x
  (Sample01 r2plx) >>= x2ply = Sample01 (\r -> r2plx r >>= x2ply)


scoreUniform :: PL a -> PL (Particle a)
scoreUniform pla = do
  a <- pla
  return $ (Particle a 1.0)

score :: Float -> PL (Particle ())
score f = return $ Particle () f

unscore :: PL (Particle a) -> PL a
unscore = fmap pvalue

multiplyScore :: Float -> PL (Particle a) -> PL (Particle a)
multiplyScore s pla = fmap (scoreParticle s) pla


condition :: Bool -> PL (Particle ())
condition b = score $ if b then 1.0 else 0.0


conditioned :: Bool -> (a -> PL (Particle a))
conditioned b a = return $ (Particle a $ if b then 1.0 else 0.0)

-- | operation to sample from [0, 1)
sample01 :: PL Float
sample01 = Sample01 Ret

-- | A way to choose uniformly. Maybe slightly biased due to an off-by-one ;)
choose :: [a] -> PL a
choose as = do
    let l = length as
    u <- sample01
    let ix = floor $ u /  (1.0 / fromIntegral l)
    return $ as !! ix


-- Typeclass that can provide me with data to run MCMC on it
class MCMC a where
    arbitrary :: a
    uniform2val :: Float -> a

instance MCMC Float where
    arbitrary = 0
    -- map [0, 1) -> (-infty, infty)
    uniform2val v = tan (-pi/2 + pi * v)


instance MCMC Int where
    arbitrary = 0
    -- map [0, 1) -> (-infty, infty)
    uniform2val v = floor $ tan (-pi/2 + pi * v)




data Particle a = Particle { pvalue :: a, pcurscore :: Float }
  deriving(Eq, Show, Ord)


scoreParticle :: Float -> Particle a -> Particle a
scoreParticle s' (Particle a s) = Particle a (s * s')

instance Functor Particle where
  fmap f (Particle a s) = Particle (f a) s


-- | Take a sample using metropolis hastings
mhStep :: (x -> PL (Particle x)) -- ^ proposal
       -> PL (Particle x) -- ^ current distribution
       -> PL (Particle x) -- ^ new distribution. sampled according to scores and proposal
               --  of current distribution
mhStep x2proposal mx =  do
  (Particle x s) <- mx
  (Particle x' s') <- x2proposal x
  let alpha = s' / s
  u <-  sample01
  return $ if u < alpha then (Particle x' s') else (Particle x s)

mhSteps ::  Int -- ^ number of steps
  -> (x -> PL (Particle x)) -- ^ proposal
  -> PL (Particle x) -- ^ current distribution
  -> PL (Particle x) -- ^ new distribution
mhSteps steps x2proposal mx = (compose steps $ mhStep x2proposal) mx

-- | Convert a weighted sampler into a regular sampler by sampling using
-- metropolis-hastings
mh :: MCMC x => PL (Particle x) -> PL x
mh plx = unscore $  mhSteps 10 (const plx) plx


mhD :: MCMC x => D x -> PL x
mhD d = let pl = do
                   x <- uniform2val <$> sample01
                   let s = unP $ runD d x
                   return $ Particle x s
        in unscore $ mhSteps 200 (const pl) pl


-- | Treat the program as a way to generate a particle
sampleParticle :: RandomGen g => g -> PL x -> (Particle x, g)
sampleParticle g (Ret x) = (Particle x 1.0, g)
sampleParticle g (Sample01 f2plx) =
  let (r, g') = random g
  in sampleParticle g' (f2plx r)

-- | Get a single sample
sample :: RandomGen g => g -> PL x -> (x, g)
sample g plx =
  let (px, g') = sampleParticle g plx
  in (pvalue px, g')

-- | Take many samples
samples :: RandomGen g => Int -> g -> PL x -> ([x], g)
samples 0 g _ = ([], g)
samples n g plx =
  let (x, g') = sample g plx
      (xs, g'') = samples (n-1) g' plx
   in (x:xs, g'')


{-
-- | Run the probabilistic value to get a sample
sample :: RandomGen g => g -> PL a -> (a, g)
sample g (Ret a) = (a, g)
sample g (Sample01 f2plnext) = let (f, g') = random g in sample g' (f2plnext f)
sample g (SampleAp ff fx) =
    let (f, _) = sample g ff
        xg3@(x, g3) = sample g fx
    in f `par` (xg3 `par` (f x, g3))

sample g (SampleBind fa a2fb)  =
    let (a, g1) = sample g fa
    in sample g1 (a2fb a)


-- | Sample n values from the distribution
samples :: RandomGen g => Int -> g -> PL a -> ([a], g)
samples 0 g _ = ([], g)
samples n g pla = let (a, g') = sample g pla
                      (as, g'') = samples (n - 1) g' pla
                 in (a:as, g'')
-}

-- | count fraction of times value occurs in list
occurFrac :: (Eq a) => [a] -> a -> Float
occurFrac as a =
    let noccur = length (filter (==a) as)
        n = length as
    in (fromIntegral noccur) / (fromIntegral n)

-- | biased coin
coin :: Float -> PL Int -- 1 with prob. p1, 0 with prob. (1 - p1)
coin !p1 = do
    f <- sample01
    Ret $  if f <= p1 then 1 else 0

-- | fair dice
dice :: PL Int
dice = choose [1, 2, 3, 4, 5, 6]



-- | Create a histogram from values.
histogram :: Int -- ^ number of buckets
          -> [Float] -- values
          -> [Int]
histogram nbuckets as =
    let
        minv :: Float
        minv = minimum as
        maxv :: Float
        maxv = maximum as
        -- value per bucket
        perbucket :: Float
        perbucket = (maxv - minv) / (fromIntegral nbuckets)
        bucket :: Float -> Int
        bucket v = floor (v / perbucket)
        bucketed :: M.Map Int Int
        bucketed = foldl (\m v -> M.insertWith (+) (bucket v) 1 m) mempty as
     in map snd . M.toList $ bucketed


printSamples :: (Real a, Eq a, Ord a, Show a) => String -> [a] -> IO ()
printSamples s as =  do
    putStrLn $ "***" <> s
    putStrLn $ "   samples: " <> series2spark (map toRational as)

printHistogram :: [Float] -> IO ()
printHistogram samples = putStrLn $ series2spark (map fromIntegral . histogram 10 $  samples)


-- | Given a coin bias, take samples and print bias
printCoin :: Float -> IO ()
printCoin bias = do
    let g = mkStdGen 1
    let (tosses, _) = samples 100 g (coin bias)
    printSamples ("bias: " <> show bias) tosses


-- | Create normal distribution as sum of uniform distributions.
normal :: PL Float
normal =  fromIntegral . sum <$> (replicateM 100 (coin 0.5))


-- | This file can be copy-pasted and will run!

-- | Symbols
type Sym = String
-- | Environments
type E a = M.Map Sym a
-- | Newtype to represent deriative values

newtype Der = Der { under :: F } deriving(Show, Num)

infixl 7 !#
-- | We are indexing the map at a "hash" (Sym)
(!#) :: E a -> Sym -> a
(!#) = (M.!)

-- | A node in the computation graph
data Node =
  Node { name :: Sym -- ^ Name of the node
       , ins :: [Node] -- ^ inputs to the node
       , out :: E F -> F -- ^ output of the node
       , der :: (E F, E (Sym -> Der))
                  -> Sym -> Der -- ^ derivative wrt to a name
       }

-- | @ looks like a "circle", which is a node. So we are indexing the map
-- at a node.
(!@) :: E a -> Node -> a
(!@) e node = e M.! (name node)

-- | Given the current environments of values and derivatives, compute
-- | The new value and derivative for a node.
run_ :: (E F, E (Sym -> Der)) -> Node -> (E F, E (Sym -> Der))
run_ ein (Node name ins out der) =
  let (e', ed') = foldl run_ ein ins -- run all the inputs
      v = out e' -- compute the output
      dv = der (e', ed') -- and the derivative
  in (M.insert name v e', M.insert name dv ed')  -- and insert them

-- | Run the program given a node
run :: E F -> Node -> (E F, E (Sym -> Der))
run e n = run_ (e, mempty) n

-- | Let's build nodes
nconst :: Sym -> F -> Node
nconst n f = Node n [] (\_ -> f) (\_ _ -> 0)

-- | Variable
nvar :: Sym -> Node
nvar n = Node n [] (!# n) (\_ n' -> if n == n' then 1 else 0)

-- | binary operation
nbinop :: (F -> F -> F)  -- ^ output computation from inputs
 -> (F -> Der -> F -> Der -> Der) -- ^ derivative computation from outputs
 -> Sym -- ^ Name
 -> (Node, Node) -- ^ input nodes
 -> Node
nbinop f df n (in1, in2) =
  Node { name = n
       , ins = [in1, in2]
       , out = \e -> f (e !# name in1) (e !# name in2)
       , der = \(e, ed) n' ->
                 let (name1, name2) = (name in1, name in2)
                     (v1, v2) = (e !# name1, e !# name2)
                     (dv1, dv2) = (ed !# name1 $ n', ed !# name2 $ n')
                     in df v1 dv1 v2 dv2
       }

nadd :: Sym -> (Node, Node) -> Node
nadd = nbinop (+) (\v dv v' dv' -> dv + dv')

nmul :: Sym -> (Node, Node) -> Node
nmul = nbinop (*) (\v (Der dv) v' (Der dv') -> Der $ (v*dv') + (v'*dv))




-- | A distribution over coin biases, given the data of the coin
-- flips seen so far. 1 or 0
-- TODO: Think of using CPS to make you be able to scoreDistribution the distribution
-- you are sampling from!
predictCoinBias :: [Int] -> PL Float
predictCoinBias flips = mh $ do
  b <- sample01
  let s = getProduct $ foldMap (\f -> Product $ if f == 1 then b else (1 - b)) flips
  return $ Particle b s

main :: IO ()
main = do
    let g = mkStdGen 1

    printCoin 0.1
    printCoin 0.8
    printCoin 0.5
    printCoin 0.7

    let (mcmcsamples, _) = samples 10 g (dice)
    printSamples "fair dice" (fromIntegral <$> mcmcsamples)


    putStrLn $ "biased dice : (x == 1 || x == 6)"
    let (mcmcsamples, _) =
          samples 10 g
            (mh $ (dice >>= \x -> conditioned (x <= 1 || x >= 6) x))
    putStrLn $ "biased dice samples: " <> show mcmcsamples
    printSamples "bised dice: " (fromIntegral <$> mcmcsamples)

    putStrLn $ "normal distribution using central limit theorem: "
    let (nsamples, _) = samples 1000 g normal
    -- printSamples "normal: " nsamples
    printHistogram nsamples


    putStrLn $ "normal distribution using MCMC: "
    let (mcmcsamples, _) = samples 1000 g (mhD $ normalD 0.5)
    printHistogram mcmcsamples

    putStrLn $ "sampling from x^4 with finite support"
    let (mcmcsamples, _) = samples 1000 g (mhD $  polyD 4)
    printHistogram mcmcsamples


    putStrLn $ "bias distribution with supplied with []"
    let (mcmcsamples, _) = samples 1000 g (predictCoinBias [])
    printHistogram mcmcsamples

    putStrLn $ "bias distribution with supplied with [True]"
    let (mcmcsamples, _) = samples 1000 g (predictCoinBias [1, 1])
    printHistogram mcmcsamples


    putStrLn $ "bias distribution with supplied with [0] x 10"
    let (mcmcsamples, _) = samples 1000 g (predictCoinBias (replicate 10 0))
    printHistogram mcmcsamples

    putStrLn $ "bias distribution with supplied with [1] x 2"
    let (mcmcsamples, _) = samples 1000 g (predictCoinBias (replicate 2 1))
    printHistogram mcmcsamples

    putStrLn $ "bias distribution with supplied with [1] x 30"
    let (mcmcsamples, _) = samples 1000 g (predictCoinBias (replicate 30 1))
    printHistogram mcmcsamples


    putStrLn $ "bias distribution with supplied with [0, 1]"
    let (mcmcsamples, _) = samples 1000 g (predictCoinBias (mconcat $ replicate 10 [0, 1]))
    printHistogram mcmcsamples


    putStrLn $ "bias distribution with supplied with [1, 0]"
    let (mcmcsamples, _) = samples 1000 g (predictCoinBias (mconcat $ replicate 20 [1, 0]))
    printHistogram mcmcsamples

    putStrLn $ "there is some kind of exponentiation going on here, where adding a single sample makes things exponentially slower"
