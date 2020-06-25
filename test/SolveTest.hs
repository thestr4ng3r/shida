{-# LANGUAGE TemplateHaskell #-}
module SolveTest (runTests) where

import Test.QuickCheck (choose, Gen, Arbitrary, arbitrary, sized, (===), Property, property)
import Test.QuickCheck.All

import Data.Word
import Data.Int
import Data.Bits
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

import Common
import Formula
import Solve
import qualified BitVectorValue as BV

example0 x y = (Atom $ uConst x :==: uVar 8 "a")
               :&&:
               (Atom $ uVar 8 "b" :==: (uVar 8 "a" :^: uConst y))

prop_example0 x y =
    let f = example0 (x::Word8) (y::Word8) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector x), ("b", BV.toBitVector (x `xor` y))])

prop_example0Incremental x y =
    let f = example0 (x::Word8) (y::Word8) in
    solveIncremental 3 f === Solution (Map.fromList [("a", BV.toBitVector x), ("b", BV.toBitVector (x `xor` y))])

prop_inc x =
    let f = Atom $ uVar 8 "a" :==: Inc (uConst (x::Word8)) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector (x+1))])

prop_abs x =
    let f = Atom $ uVar 8 "a" :==: Abs (sConst (x :: Int8))
    in solve f == Solution (Map.fromList [("a", BV.toBitVector (fromIntegral (abs x) :: Word8))])

checkOperator :: BV.ToBitVector a => (Term -> Term -> Term) -> (a -> a -> a) -> BitVectorSign -> a -> a -> Bool
checkOperator top op sign x y =
    let (mVar, mConst) = if sign == Signed then (sVar, sConst) else (uVar, uConst)
        f = Atom $ mVar 8 "a" :==: (mConst x `top` mConst y) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector (x `op` y))])

prop_plus x y = checkOperator (:+:) (+) Unsigned (x::Word8) (y::Word8)
prop_plusS x y = checkOperator (:+:) (+) Signed (x::Int8) (y::Int8)
prop_minus x y = checkOperator (:-:) (-) Unsigned (x::Word8) (y::Word8)
prop_minusS x y = checkOperator (:-:) (-) Signed (x::Int8) (y::Int8)

checkDiv :: (BV.ToBitVector a, Integral a) => BitVectorSign -> a -> a -> Bool
checkDiv sign x y =
    let (mVar, mConst) = if sign == Signed then (sVar, sConst) else (uVar, uConst)
        f = Atom $ mVar 8 "a" :==: (mConst x :/: mConst y) in
    solveAll f == if y == 0 then Unsatisfiable else Solution [Map.fromList [("a", BV.toBitVector (x `quot` y))]]

prop_concat :: Word8 -> Word8 -> Bool
prop_concat x y =
    let f = Atom $ sVar 16 "a" :==: Concat Signed (uConst x) (uConst y)
        v = fromIntegral ((fromIntegral x::Word16) .|. ((fromIntegral y::Word16) `shiftL` 8))::Word16 in
    solve f == Solution (Map.fromList [("a", BV.toBitVector v)])

prop_extz :: Word8 -> Property
prop_extz x =
    let f = Atom $ uVar 16 "a" :==: Ext 16 (uConst x) in
    solve f === Solution (Map.fromList [("a", BV.toBitVector (fromIntegral x :: Word16))])

prop_exts :: Int8 -> Property
prop_exts x =
    let f = Atom $ sVar 16 "a" :==: Ext 16 (sConst x) in
    solve f === Solution (Map.fromList [("a", BV.toBitVector (fromIntegral x :: Int16))])

prop_slice :: Word64 -> Gen Property
prop_slice x = do
    let bv = BV.toBitVector x
    off <- choose (0, 62)
    sz <- choose (1, 64 - off)
    let f = Atom $ uVar sz "a" :==: Slice Unsigned off sz (Const Signed bv)
    return $ solve f === Solution (Map.fromList [("a", BV.slice bv off sz)])

prop_complement :: Word8 -> Bool
prop_complement x =
    let f = Atom $ uVar 8 "a" :==: Complement (uConst x) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector (x `xor` 0xff))])

prop_ternary :: Bool -> Word8 -> Word8 -> Property
prop_ternary c a b =
    let f = Atom $ uVar 8 "a" :==: Ternary (BConst c) (uConst a) (uConst b) in
    solve f === Solution (Map.fromList [("a", BV.toBitVector $ if c then a else b)])

prop_ternary1 :: Word8 -> Word8 -> Word8 -> Word8 -> Property
prop_ternary1 ca cb a b =
    let f = Atom $ uVar 8 "a" :==: Ternary (uConst ca :==: uConst cb) (uConst a) (uConst b) in
    solve f === Solution (Map.fromList [("a", BV.toBitVector $ if ca == cb then a else b)])

prop_atomEquals x =
    let f = Atom $ uVar 8 "a" :==: uConst (x::Word8) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector x)])

bconjunction :: [Formula] -> Formula
bconjunction [x] = x
bconjunction [x, y] = And x y
bconjunction (x : xs) = And x $ bconjunction xs
bconjunction [] = undefined

prop_atomPick :: Word8 -> Bool
prop_atomPick x =
    let f = bconjunction $ map (\i ->
                if ((x `shiftR` i) .&. 1) /= 0 then
                    Atom $ Pick (fromIntegral i) (uVar 8 "a")
                else
                    Not $ Atom $ Pick (fromIntegral i) (uVar 8 "a")
            ) [0..7] in
    solve f == Solution (Map.fromList [("a", BV.toBitVector x)])

prop_atomLessThanUnsigned :: Word8 -> Bool
prop_atomLessThanUnsigned x =
    let f = bconjunction $
            (if x == 0 then [] else [
                Atom $ uConst (x-1) :<: uVar 8 "a"
            ]) ++ (if x == 255 then [] else [
                Atom $ uVar 8 "a" :<: uConst (x+1)
            ]) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector x)])

prop_atomLessThanSigned :: Int8 -> Bool
prop_atomLessThanSigned x =
    let f = bconjunction $
            (if x == -128 then [] else [
                Atom $ sConst (x-1) :<: sVar 8 "a"
            ]) ++ (if x == 127 then [] else [
                Atom $ sVar 8 "a" :<: sConst (x+1)
            ]) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector x)])

prop_shiftL :: Word8 -> Word8 -> Bool
prop_shiftL x s =
    let f = Atom $ uVar 8 "a" :==: (uConst x :<<: Const Unsigned (BV.slice (BV.toBitVector s) 0 3)) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector (x `shiftL` fromIntegral (s .&. 0x7)))])

prop_shiftR :: Word8 -> Word8 -> Bool
prop_shiftR x s =
    let f = Atom $ uVar 8 "a" :==: (uConst x :>>: Const Unsigned (BV.slice (BV.toBitVector s) 0 3)) in
    solve f == Solution (Map.fromList [("a", BV.toBitVector (x `shiftR` fromIntegral (s .&. 0x7)))])

prop_incrementalUnsatisfiable :: Property
prop_incrementalUnsatisfiable =
    let f = Atom ((uVar 64 "a" :*: uVar 64 "b") :==: uVar 64 "c")
            :&&: Not (Atom ((uVar 64 "b" :*: uVar 64 "a") :==: uVar 64 "c"))
            :&&: Atom (uVar 64 "x" :<: uVar 64 "y")
            :&&: Atom (uVar 64 "y" :<: uVar 64 "x") in
    solveIncremental 1 f === Unsatisfiable

--prop_incrementalSatisfiable :: Word64 -> Property
--prop_incrementalSatisfiable x =
--    let f = Atom (uVar 64 "a" :==: uConst x)
--            :&&: Not (     Not (Atom $ (uVar 64 "b" :*: uVar 64 "c") :<: uVar 64 "d")
--                      :&&: Not (Atom $ uVar 64 "d" :<: (uVar 64 "b" :*: uVar 64 "c")))
--        sol = solveIncremental 1 f in
--    case sol of
--        Solution m -> m Map.! "a" === BV.toBitVector x
--        _ -> property False

prop_mult x y = checkOperator (:*:) (*) Unsigned (x::Word8) (y::Word8)
prop_multS x y = checkOperator (:*:) (*) Signed (x::Int8) (y::Int8)
prop_div x y = checkDiv Unsigned (x::Word8) (y::Word8)
prop_divS x y = checkDiv Signed (x::Int8) (y::Int8)

return []
runTests :: IO Bool
runTests = $quickCheckAll