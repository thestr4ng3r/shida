module Common where

type Size = Word
data BitVectorSign = Unsigned | Signed deriving (Eq, Ord)
data BitVectorType = BitVectorType BitVectorSign Size deriving (Eq, Ord)

instance Show BitVectorType where
    show (BitVectorType sign sz) = (if sign == Signed then "s" else "u") ++ show sz

fixedPoint :: Eq a => (a -> a) -> a -> a
fixedPoint f v =
    if r == v then v else fixedPoint f r
    where r = f v