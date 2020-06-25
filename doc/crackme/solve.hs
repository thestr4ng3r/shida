import Common
import Formula
import Solve
import qualified BitVectorValue as BV

import Data.Maybe
import Data.Word
import qualified Data.Map as Map
import qualified Data.ByteString as B

import Control.Monad

hash :: [Word8]
hash = [0xa2, 0x35, 0xa3, 0x0f, 0x1c, 0xd0, 0x0e, 0x9e]

-- |Combine a list of formulas into a single formula one using And
conjunction :: [Formula] -> Formula
conjunction [a]        = a
conjunction (a : as)   = And a (conjunction as)
conjunction _          = undefined

-- |Variable name for the i-th character in the password
pwCharVarName :: Int -> String
pwCharVarName i = "pw[" ++ show i ++ "]"

-- |Term for the i-th character in the password
pwChar :: Int -> Term
pwChar = uVar 8 . pwCharVarName 

formula :: Formula
formula =
    conjunction $
        map (\i ->
            let a = pwChar $ i
                b = pwChar $ (i + 1) `rem` 8
                c = pwChar $ (i + 2) `rem` 8
                d = pwChar $ (i + 3) `rem` 8
                shiftPlus = Slice Unsigned 0 3 (b :+: c)
                shiftMinus = Slice Unsigned 0 3 (b :-: c)
                eight = Const Unsigned $ BV.pack [False, False, False] -- Only 3 bits, overflow on purpose for 8 - x
                term = ((a :<<: shiftPlus) :|: (a :>>: (eight :-: shiftMinus))) :-: d
            in (Atom $ term :==: uConst (hash!!i)) :&&: (Not $ Atom $ Pick 7 a)
        ) [0..7]

main :: IO ()
main =
    case solveAll formula of
    Solution s ->
        forM_ s (\s ->
            putStrLn $ toEnum <$> fromIntegral <$> map (\i ->
                           let bv = s Map.! (pwCharVarName i) in
                           (fromJust (BV.fromBitVector bv))::Word8) [0..7]
            )
    res -> print res
