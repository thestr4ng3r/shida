{-# LANGUAGE PatternSynonyms #-}
module Formula where

import Text.Printf

import Common
import qualified BitVectorValue as BV

type Identifier = String

data Formula =
    And Formula Formula |
    Not Formula |
    Atom Atom
    deriving (Eq, Ord)

data Atom =
    BConst Bool |
    LessThan Term Term |
    Equals Term Term |
    Pick Size Term
    deriving (Eq, Ord)

data Term =
    Plus Term Term |
    Minus Term Term |
    Mult Term Term |
    Div Term Term |
    Remainder Term Term |
    ShL Term Term |
    ShR Term Term |
    BinAnd Term Term |
    BinOr Term Term |
    BinXor Term Term |
    Var BitVectorType Identifier |
    Complement Term |
    Inc Term |
    Abs Term |
    Const BitVectorSign BV.BitVectorValue |
    Ternary Atom Term Term |
    Concat BitVectorSign Term Term |
    Ext Size Term |
    Slice BitVectorSign Size Size Term -- new sign -> start offset -> new size -> term
    deriving (Eq, Ord)

pattern (:&&:) a b = And a b
pattern (:!!:) a = Not a

pattern (:==:) a b = Equals a b
pattern (:<:) a b = LessThan a b

pattern (:+:) a b = Plus a b
pattern (:-:) a b = Minus a b
pattern (:*:) a b = Mult a b
pattern (:/:) a b = Div a b
pattern (:%:) a b = Remainder a b
pattern (:<<:) a b = ShL a b
pattern (:>>:) a b = ShR a b
pattern (:&:) a b = BinAnd a b
pattern (:|:) a b = BinOr a b
pattern (:^:) a b = BinXor a b

uVar :: BV.Size -> Identifier -> Term
uVar sz = Var (BitVectorType Unsigned sz)

sVar :: BV.Size -> Identifier -> Term
sVar sz = Var (BitVectorType Signed sz)

uConst :: BV.ToBitVector a => a -> Term
uConst v = Const Unsigned $ BV.toBitVector v

sConst :: BV.ToBitVector a => a -> Term
sConst v = Const Signed $ BV.toBitVector v

instance Show Formula where
    show (And l r)          = printf "(%s ∧ %s)" (show l) (show r)
    show (Not f)            = printf "¬%s" (show f)
    show (Atom a)           = show a

instance Show Atom where
    show (BConst True)      = printf "True"
    show (BConst False)     = printf "False"
    show (LessThan l r)     = printf "(%s < %s)" (show l) (show r)
    show (Equals l r)       = printf "(%s = %s)" (show l) (show r)
    show (Pick i t)         = printf "%s[%s]" (show t) (show i)

instance Show Term where
    show (Plus l r)         = printf "(%s + %s)" (show l) (show r)
    show (Minus l r)        = printf "(%s - %s)" (show l) (show r)
    show (Mult l r)         = printf "(%s * %s)" (show l) (show r)
    show (Div l r)          = printf "(%s / %s)" (show l) (show r)
    show (Remainder l r)    = printf "(%s %% %s)" (show l) (show r)
    show (ShL l r)          = printf "(%s << %s)" (show l) (show r)
    show (ShR l r)          = printf "(%s >> %s)" (show l) (show r)
    show (BinAnd l r)       = printf "(%s & %s)" (show l) (show r)
    show (BinOr l r)        = printf "(%s | %s)" (show l) (show r)
    show (BinXor l r)       = printf "(%s ^ %s)" (show l) (show r)
    show (Concat _ l r)     = printf "(%s ⚬ %s)" (show l) (show r)
    show (Var _ name)       = name
    show (Complement term)  = printf "~%s" (show term)
    show (Inc term)         = printf "%s+1" (show term)
    show (Abs term)         = printf "|%s|" (show term)
    show (Const _ bv)       = show bv
    show (Ternary c a b)    = printf "(%s ? %s : %s)" (show c) (show a) (show b)
    show (Ext sz term)      = printf "ext_%s %s" (show sz) (show term)
    show (Slice _ off sz t) = printf "%s[%s:%s]" (show t) (show off) (show sz)

combinedTermTypes :: Term -> Term -> Maybe BitVectorType
combinedTermTypes l r =
    case (termType l, termType r) of
        (Just tl, Just tr) | tl == tr -> Just tl
        _ -> Nothing

shiftTermTypes :: Term -> Term -> Maybe BitVectorType
shiftTermTypes l r =
    case (termType l, termType r) of
        (Just (BitVectorType sign sz), Just (BitVectorType Unsigned ssz)) | sz == 2 ^ ssz -> Just $ BitVectorType sign sz
        _ -> Nothing

-- |returns the term's type or Nothing if it is invalid wrt. typing
termType :: Term -> Maybe BitVectorType
termType (Plus l r) = combinedTermTypes l r
termType (Minus l r) = combinedTermTypes l r
termType (Mult l r) = combinedTermTypes l r
termType (Div l r) = combinedTermTypes l r
termType (Remainder l r) = combinedTermTypes l r
termType (ShL l r) = shiftTermTypes l r
termType (ShR l r) = shiftTermTypes l r
termType (BinAnd l r) = combinedTermTypes l r
termType (BinOr l r) = combinedTermTypes l r
termType (BinXor l r) = combinedTermTypes l r
termType (Concat sign l r) = do
    (BitVectorType _ lsz) <- termType l
    (BitVectorType _ rsz) <- termType r
    return $ BitVectorType sign (lsz + rsz)
termType (Var tp _) = Just tp
termType (Complement term) = termType term
termType (Inc term) = termType term
termType (Abs term) = (\(BitVectorType _ sz) -> BitVectorType Unsigned sz) <$> termType term
termType (Const sign bv) = Just $ BitVectorType sign (BV.length bv)
termType (Ternary _ a b) = combinedTermTypes a b
termType (Ext sz term) =
    case termType term of
        Just (BitVectorType sign tsz) | tsz <= sz -> Just $ BitVectorType sign sz
        _ -> Nothing
termType (Slice sign off sz term) =
    case termType term of
        Just (BitVectorType _ tsz) | off + sz <= tsz -> Just $ BitVectorType sign sz
        _ -> Nothing

subTerms :: Term -> [Term]
subTerms (Plus l r) = [l, r]
subTerms (Minus l r) = [l, r]
subTerms (Mult l r) = [l, r]
subTerms (Div l r) = [l, r]
subTerms (Remainder l r) = [l, r]
subTerms (ShL l r) = [l, r]
subTerms (ShR l r) = [l, r]
subTerms (BinAnd l r) = [l, r]
subTerms (BinOr l r) = [l, r]
subTerms (BinXor l r) = [l, r]
subTerms (Concat _ l r) = [l, r]
subTerms (Var _ _) = []
subTerms (Complement term) = [term]
subTerms (Inc term) = [term]
subTerms (Abs term) = [term]
subTerms (Const _ _) = []
subTerms (Ternary _ a b) = [a, b]
subTerms (Ext _ term) = [term]
subTerms (Slice _ _ _ t) = [t]

class Terms a where
    terms :: a -> [Term]

instance Terms Term where
    terms term =
        term : concatMap terms at ++ concatMap terms st
        where st = subTerms term
              at = case term of
                (Ternary c _ _) -> terms c
                _ -> []

instance Terms Formula where
    terms (And l r) = terms l ++ terms r
    terms (Not f) = terms f
    terms (Atom a) = terms a

instance Terms Atom where
    terms (BConst _) = []
    terms (LessThan l r) = terms l ++ terms r
    terms (Equals l r) = terms l ++ terms r
    terms (Pick _ t) = terms t

class Atoms a where
    atoms :: a -> [Atom]

instance Atoms Formula where
    atoms (And l r) = atoms l ++ atoms r
    atoms (Not f) = atoms f
    atoms (Atom a) = atoms a

instance Atoms Atom where
    atoms (BConst b) = [BConst b]
    atoms (LessThan l r) = LessThan l r : atoms l ++ atoms r
    atoms (Equals l r) = Equals l r : atoms l ++ atoms r
    atoms (Pick i t) = Pick i t : atoms t

instance Atoms Term where
    atoms (Plus l r) = atoms l ++ atoms r
    atoms (Minus l r) = atoms l ++ atoms r
    atoms (Mult l r) = atoms l ++ atoms r
    atoms (Div l r) = atoms l ++ atoms r
    atoms (Remainder l r) = atoms l ++ atoms r
    atoms (ShL l r) = atoms l ++ atoms r
    atoms (ShR l r) = atoms l ++ atoms r
    atoms (BinAnd l r) = atoms l ++ atoms r
    atoms (BinOr l r) = atoms l ++ atoms r
    atoms (BinXor l r) = atoms l ++ atoms r
    atoms (Concat _ l r) = atoms l ++ atoms r
    atoms (Var _ _) = []
    atoms (Complement t) = atoms t
    atoms (Inc t) = atoms t
    atoms (Abs t) = atoms t
    atoms (Const _ _) = []
    atoms (Ternary c a b) = atoms c ++ atoms a ++ atoms b
    atoms (Ext _ t) = atoms t
    atoms (Slice _ _ _ t) = atoms t

class Vars a where
    vars :: a -> [(BitVectorType, Identifier)]

instance Vars Formula where
    vars (And l r) = vars l ++ vars r
    vars (Not f) = vars f
    vars (Atom a) = vars a

instance Vars Atom where
    vars (BConst _) = []
    vars (LessThan l r) = vars l ++ vars r
    vars (Equals l r) = vars l ++ vars r
    vars (Pick _ t) = vars t

instance Vars Term where
    vars (Plus l r) = vars l ++ vars r
    vars (Minus l r) = vars l ++ vars r
    vars (Mult l r) = vars l ++ vars r
    vars (Div l r) = vars l ++ vars r
    vars (Remainder l r) = vars l ++ vars r
    vars (ShL l r) = vars l ++ vars r
    vars (ShR l r) = vars l ++ vars r
    vars (BinAnd l r) = vars l ++ vars r
    vars (BinOr l r) = vars l ++ vars r
    vars (BinXor l r) = vars l ++ vars r
    vars (Concat _ l r) = vars l ++ vars r
    vars (Var tp name) = [(tp, name)]
    vars (Complement t) = vars t
    vars (Inc t) = vars t
    vars (Abs t) = vars t
    vars (Const _ _) = []
    vars (Ternary c a b) = vars c ++ vars a ++ vars b
    vars (Ext _ t) = vars t
    vars (Slice _ _ _ t) = vars t