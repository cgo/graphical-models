{-# LANGUAGE MultiParamTypeClasses #-}
module Main where

import Data.Ix
import Control.DeepSeq (deepseq)
import Control.Parallel.Strategies

f1 = ([]::[Int]) == ([]::[Int])
f2 = 1 == 1

type Function a = [a] -> a

f :: (Num a) => Function a
f [a,b,c] = a + b + c
f _ = undefined

class Integrate a b where
  integrate :: a -> a -> (a -> b) -> b

instance Integrate Int Int where
  integrate a b f = sum $ map f [a..b]

--instance Integrate [Int] Int where
--  integrate as bs f = undefined -- Sum over all possible combinations of the given ranges in as,bs.
  

ranges = [(1,3),(4,6),(7,9)] :: [(Int,Int)]
ranges2 = [(1,300),(4,600),(7,900)] :: [(Int,Int)]

-- Fix all arguments in the given argument list except the n'th,
-- and return a function of the n'th argument with the others fixed.
fixAllBut :: Int -> [a] -> Function a -> (a -> a)
fixAllBut n as f = ff `seq` ff 
  where
    ff = fix' n [] as
    fix' _ _ [] = undefined
    -- NOTE: This is inefficient; find a better way to combine the arguments
    -- (in an O(1) vector?)
    fix' 0 l (a:as) = let l' = reverse l 
                      in \x -> f (l' ++ [x] ++ as)
    fix' n l (a:as) = n' `seq` l' `seq` fix' n' l' as 
      where
        n' = n - 1
        l' = a : l


type Range = (Int,Int)


{-| Generate all combinations of integers with the given ranges for each position.
NOTE: This took about 28 clock ticks per generated combination on 1 core on an AMD Phenom,
compiled with ghc -O and used only to output the length of the list. Measured with ranges2 above. -}
allCombinations :: [Range] -> [[Int]]
allCombinations (r:[]) = map (:[]) (range r)
allCombinations (r:rs) = concatMap (rest' r) rest
  --rest'r `seq` rest `seq` concatMap (rest'r) rest
  where
    rest' :: Range -> [Int] -> [[Int]]
    rest' r other_digits = map (:other_digits) (range r)
                           --withStrategy (parBuffer 1000 r0) $ map (:other_digits) (range r)
    rest = allCombinations rs
allCombinations [] = undefined
{-# INLINE allCombinations #-} -- Has no real effect.

-- Integrate over all but one element and return the resulting function of that one element. 
mintegrate :: (Integrate a a, Num a) => n -> [(a,a)] -> Function a -> (a -> a)
mintegrate rs f = undefined
--  where
--    sumOver

checkit (r:rs) = r < 1

main = --putStrLn $ show $ filter checkit $ allCombinations ranges2
       putStrLn $ show $ length $ allCombinations ranges2