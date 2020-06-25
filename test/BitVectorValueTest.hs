{-# LANGUAGE TemplateHaskell #-}
module BitVectorValueTest (runTests) where

import Test.QuickCheck (choose, Gen, Arbitrary, arbitrary, sized)
import Test.QuickCheck.All

import Text.Printf
import Data.Word
import Data.Bits
import Control.Monad

import BitVectorValue as BV

instance Arbitrary BV.BitVectorValue where
    arbitrary = choose (1, 128) >>= \n -> BV.pack <$> replicateM n arbitrary

prop_replicate :: Bool -> Gen Bool
prop_replicate v = do
    sz <- choose (1, 128) :: Gen Word
    let bv = BV.replicate sz v
    return $ foldl (\acc i -> acc && (BV.index bv i == v)) True [0..sz-1]

checkBase :: (ToBitVector a, Bits a, Num a) => BV.Size -> a -> Bool
checkBase sz v =
    let bv = BV.toBitVector v in
    BV.length bv == sz && foldl (\acc i -> acc && (BV.index bv i == (v .&. (1 `shiftL` fromIntegral i) /= 0))) True [0..sz-1]

prop_base8 = checkBase 8 :: Word8 -> Bool
prop_base16 = checkBase 16 :: Word16 -> Bool
prop_base32 = checkBase 32 :: Word32 -> Bool
prop_base64 = checkBase 64 :: Word64 -> Bool

prop_eq :: BV.BitVectorValue -> Bool
prop_eq bv = bv == bv

prop_neq :: Gen Bool
prop_neq = do
    bitsa <- choose (1, 128) >>= \n -> replicateM n (arbitrary::Gen Bool)
    bitsb <- choose (1, 128) >>= \n -> replicateM n (arbitrary::Gen Bool)
    return $ (bitsa == bitsb) == (BV.pack bitsa == BV.pack bitsb)

prop_compare_eq :: BV.BitVectorValue -> Bool
prop_compare_eq bv = compare bv bv == EQ

prop_compare :: Word64 -> Word64 -> Bool
prop_compare a b = compare a b == compare (BV.toBitVector a) (BV.toBitVector b)

return []
runTests :: IO Bool
runTests = $quickCheckAll