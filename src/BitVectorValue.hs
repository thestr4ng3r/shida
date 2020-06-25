module BitVectorValue (
    Size,
    BoundsException,
    BitVectorValue,
    index,
    replicate,
    length,
    unpack,
    pack,
    ToBitVector,
    toBitVector,
    FromBitVector,
    fromBitVector,
    slice
) where


import qualified Prelude as P
import Prelude hiding (length,replicate)

import Data.Word
import Data.Int
import Data.Bits
import qualified Data.ByteString as B

import Control.Exception
import Data.Function ((&))

import Common

data BoundsException = BoundsException deriving (Show)
instance Exception BoundsException

data BitVectorValue = BitVectorValue Size B.ByteString

instance Eq BitVectorValue where
    (==) (BitVectorValue lsz ldat) (BitVectorValue rsz rdat) =
        lsz == rsz && foldl (\acc i -> acc && (index (BitVectorValue lsz ldat) i == index (BitVectorValue rsz rdat) i)) True [0..lsz-1]

compareBits :: Size -> BitVectorValue -> BitVectorValue -> Ordering
compareBits 0 a b = compare (index a 0) (index b 0)
compareBits i a b =
    let r = compare (index a i) (index b i) in
    if r == EQ then
        compareBits (i-1) a b
    else
        r

instance Ord BitVectorValue where
    compare a b =
        let szc = compare (length a) (length b) in
        if szc == EQ then
            compareBits (length a - 1) a b
        else
            szc

instance Show BitVectorValue where
    show (BitVectorValue sz dat) =
        foldl (\acc i -> acc ++ (if index (BitVectorValue sz dat) i then "1" else "0")) "0b" $ reverse [0..sz-1]

index :: BitVectorValue -> Size -> Bool
index (BitVectorValue sz dat) i =
    if i >= sz then
        throw BoundsException
    else
        let byte = B.index dat $ fromIntegral $ i `shiftR` 3
            biti = i .&. 0x7 in
        ((byte `shiftR` fromIntegral biti) .&. 1) == 1

replicate :: Size -> Bool -> BitVectorValue
replicate sz v = BitVectorValue sz $ B.replicate (fromIntegral ((sz + 7) `shiftR` 3)) $ if v then 0xff else 0

length :: BitVectorValue -> Size
length (BitVectorValue sz _) = sz

unpack :: BitVectorValue -> [Bool]
unpack bv = map (index bv) [0..length bv - 1]

packByte :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Word8
packByte b0 b1 b2 b3 b4 b5 b6 b7 = foldr (\b acc -> (acc `shiftL` 1) .|. (if b then 1 else 0)) 0 [b0, b1, b2, b3, b4, b5, b6, b7]

packBytes :: [Bool] -> [Word8]
packBytes (b0 : b1 : b2 : b3 : b4 : b5 : b6 : b7 : bs) = packByte b0 b1 b2 b3 b4 b5 b6 b7 : packBytes bs
packBytes [b0, b1, b2, b3, b4, b5, b6] = [packByte b0 b1 b2 b3 b4 b5 b6 False]
packBytes [b0, b1, b2, b3, b4, b5] = [packByte b0 b1 b2 b3 b4 b5 False False]
packBytes [b0, b1, b2, b3, b4] = [packByte b0 b1 b2 b3 b4 False False False]
packBytes [b0, b1, b2, b3] = [packByte b0 b1 b2 b3 False False False False]
packBytes [b0, b1, b2] = [packByte b0 b1 b2 False False False False False]
packBytes [b0, b1] = [packByte b0 b1 False False False False False False]
packBytes [b0] = [packByte b0 False False False False False False False]
packBytes [] = []

pack :: [Bool] -> BitVectorValue
pack bits = BitVectorValue (fromIntegral $ P.length bits) $ B.pack $ packBytes bits

class ToBitVector a where
    toBitVector :: a -> BitVectorValue

instance ToBitVector Word8 where
    toBitVector w = BitVectorValue 8 $ B.singleton w

instance ToBitVector Word16 where
    toBitVector w = BitVectorValue 16 $ B.pack $ map fromIntegral [w .&. 0xff,
                                                                 (w `shiftR` 8) .&. 0xff]

instance ToBitVector Word32 where
    toBitVector w = BitVectorValue 32 $ B.pack $ map fromIntegral [w .&. 0xff,
                                                                 (w `shiftR` 8) .&. 0xff,
                                                                 (w `shiftR` 0x10) .&. 0xff,
                                                                 (w `shiftR` 0x18) .&. 0xff]
instance ToBitVector Word64 where
    toBitVector w = BitVectorValue 64 $ B.pack $ map fromIntegral [w .&. 0xff,
                                                                 (w `shiftR` 8) .&. 0xff,
                                                                 (w `shiftR` 0x10) .&. 0xff,
                                                                 (w `shiftR` 0x18) .&. 0xff,
                                                                 (w `shiftR` 0x20) .&. 0xff,
                                                                 (w `shiftR` 0x28) .&. 0xff,
                                                                 (w `shiftR` 0x30) .&. 0xff,
                                                                 (w `shiftR` 0x38) .&. 0xff]

instance ToBitVector Int8 where toBitVector v = toBitVector (fromIntegral v :: Word8)
instance ToBitVector Int16 where toBitVector v = toBitVector (fromIntegral v :: Word16)
instance ToBitVector Int32 where toBitVector v = toBitVector (fromIntegral v :: Word32)
instance ToBitVector Int64 where toBitVector v = toBitVector (fromIntegral v :: Word64)

class FromBitVector a where
    fromBitVector :: BitVectorValue -> Maybe a

instance FromBitVector Word8 where
    fromBitVector (BitVectorValue 8 v) = Just $ B.head v
    fromBitVector _ = Nothing

slice :: BitVectorValue -> Size -> Size -> BitVectorValue
slice v start sz =
    unpack v & drop (fromIntegral start) & take (fromIntegral sz) & pack