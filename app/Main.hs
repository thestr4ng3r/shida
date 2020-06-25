module Main where

import Data.Word
import Data.Int
--import Data.Maybe
import Data.Bits
import Data.Either

import qualified BitVectorValue as BV
import Common
import Formula
import Flattening
import Solve

example0 = (Atom $ uConst (42::Word8) :==: uVar 8 "a")
           :&&:
           (Atom $ uVar 8 "b" :==: (uVar 8 "a" :^: uConst (123::Word8)))

example1 = Atom $ uVar 8 "a" :==: (uConst (13::Word8) :+: uConst (29::Word8))

bconjunction :: [Formula] -> Formula
bconjunction [x, y] = And x y
bconjunction (x : xs) = And x $ bconjunction xs
bconjunction [] = undefined

example2 :: Word8 -> Formula
example2 x = bconjunction $ map (\i ->
            if ((x `shiftR` i) .&. 1) /= 0 then
                Atom $ Pick (fromIntegral i) (uVar 8 "a")
            else
                Not $ Atom $ Pick (fromIntegral i) (uVar 8 "a")
        ) [0..7]

example3 :: Int8 -> Formula
example3 x = bconjunction $
                         (if x == -128 then [] else [
                             Atom $ sConst (x-1) :<: sVar 8 "a"
                         ]) ++ (if x == 127 then [] else [
                             Atom $ sVar 8 "a" :<: sConst (x+1)
                         ])

exampleShift :: Word8 -> Word8 -> Formula
exampleShift x s =
    Atom $ uVar 8 "a" :==: (uConst x :>>: Const Unsigned (BV.slice (BV.toBitVector s) 0 3))

exampleMult :: Word8 -> Word8 -> Formula
exampleMult l r =
    Atom $ uVar 8 "a" :==: (uConst l :*: uConst r)

exampleDiv :: Int8 -> Int8 -> Formula
exampleDiv l r =
    Atom $ sVar 8 "a" :==: (sConst l :/: sConst r)

exampleMod :: Int8 -> Int8 -> Formula
exampleMod l r =
    Atom $ sVar 8 "a" :==: (sConst l :%: sConst r)

exampleConcat :: Word8 -> Word8 -> Formula
exampleConcat l r =
    Atom $ sVar 16 "a" :==: Concat Signed (uConst l) (uConst r)

exampleTernary :: Bool -> Word8 -> Word8 -> Formula
exampleTernary c a b = Atom $ uVar 8 "a" :==: Ternary (BConst c) (uConst a) (uConst b)

exampleHardUnsat0 :: Size -> Formula
exampleHardUnsat0 sz = Atom ((uVar sz "a" :*: uVar sz "b") :==: uVar sz "c")
                :&&: Not (Atom ((uVar sz "b" :*: uVar sz "a") :==: uVar sz "c"))
                :&&: Atom (uVar sz "x" :<: uVar sz "y")
                :&&: Atom (uVar sz "y" :<: uVar sz "x")

exampleHardUnsat1 :: Size -> Formula
exampleHardUnsat1 sz = Atom ((uVar sz "a" :*: uVar sz "b") :==: uVar sz "c")
                :&&: Atom ((uVar sz "b" :*: uVar sz "a") :==: uVar sz "c")
                :&&: Atom (uVar sz "x" :<: uVar sz "y")
                :&&: Atom (uVar sz "y" :<: uVar sz "x")

exampleSat1 :: Size -> Formula
exampleSat1 sz = Atom (uVar sz "a" :==: Const Unsigned (BV.replicate sz False))
                    :&&: Not (     Not (Atom $ (uVar sz "b" :*: uVar sz "c") :<: uVar sz "d")
                              :&&: Not (Atom $ uVar sz "d" :<: (uVar sz "b" :*: uVar sz "c")))

main :: IO ()
main = do
    let x = 1::Int8
    let y = -1::Int8
    let f = Atom $ sVar 8 "a" :==: (sConst x :*: sConst y)
    putStrLn $ "Solve: " ++ show f
    putStrLn "-- Flattened:"
    let flat = fromRight undefined $ flatten f
    print flat
    putStrLn "-- Final Result:"
    print $ solve f

--main :: IO ()
--main = do
--    let x = -1::Int8
--    let y = 2::Int8
--    --print $ flatten $ exampleDiv x y
--    putStrLn $ "Solve: " ++ show x ++ " / " ++ show y
--    putStrLn $ "Result: " ++ show (solve $ exampleDiv x y)
--    putStrLn $ "Remain: " ++ show (solve $ exampleMod x y)

--main :: IO ()
--main = do
--    let x = 1
--    let f = exampleHardUnsat1 64 -- example1
--    putStrLn $ "Solve: " ++ show f
--    --putStrLn ""
--    --putStrLn "-- Flattened:"
--    --let flat = fromRight undefined $ flatten f
--    --print flat
--    --putStrLn "-- Propositional:"
--    --print $ propositional flat
--    putStrLn ""
--    putStrLn "-- Final Result:"
--    print $ solveIncremental 1 f
--    --print $ solve f
