#!/usr/bin/env stack
-- stack --resolver lts-20.5 ghci --package QuickCheck

import Data.List
import Test.QuickCheck

-- Definitions of evenPart and oddPart
evenPart :: Fractional a => (a -> a) -> (a -> a)
evenPart f x = (f x + f (-x)) * 0.5

oddPart :: Fractional a => (a -> a) -> (a -> a)
oddPart f x = (f x - f (-x)) * 0.5

-- Definitions of isEven and isOdd
isEven :: (Eq a, Num a) => (a -> a) -> a -> Bool
isEven f x = f (-x) == f x

isOdd :: (Eq a, Num a) => (a -> a) -> a -> Bool
isOdd f x = f (-x) == -f x

-- Test properties for QuickCheck
prop_evenPart :: (Double -> Double) -> Double -> Bool
prop_evenPart f x = isEven (evenPart f) x

prop_oddPart :: (Double -> Double) -> Double -> Bool
prop_oddPart f x = isOdd (oddPart f) x

-- Example functions to test
poly1 :: Double -> Double
poly1 x = x^2 + 2*x + 1

poly2 :: Double -> Double
poly2 x = x^3 + x

sinFunc :: Double -> Double
sinFunc x = sin x

cosFunc :: Double -> Double
cosFunc x = cos x

-- Main function to run QuickCheck
main :: IO ()
main = do
  putStrLn "Testing evenPart and oddPart properties with example functions..."
  quickCheck (prop_evenPart poly1)
  quickCheck (prop_evenPart cosFunc)
  quickCheck (prop_oddPart poly2)
  quickCheck (prop_oddPart sinFunc)
  putStrLn "Testing specific functions..."
  quickCheck (\x -> isEven poly1 x)
  quickCheck (\x -> isOdd poly2 x)
  quickCheck (\x -> isOdd sinFunc x)
  quickCheck (\x -> isEven cosFunc x)
