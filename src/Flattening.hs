module Flattening where

import Text.Printf
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe

import Control.Monad.Except
import Control.Monad.State

import qualified BitVectorValue as BV
import Common
import Formula
import qualified Propositional as P
import Propositional ((<->), (&&&), (|||), (^^^))

newtype FlattenState = FlattenState P.Identifier
data FlattenError =
    TermTypeError Term |
    AtomTypeMismatch Atom |
    AtomPickBoundsError Atom
    deriving (Eq, Show)

type Flattening a = StateT FlattenState (Except FlattenError) a

runFlattening :: Flattening a -> FlattenState -> Either FlattenError a
runFlattening m = runExcept . evalStateT m

type PropVector = Size -> P.Formula
data PropVectorVariable = PropVectorVariable P.Identifier Size

instance Show PropVectorVariable where
    show (PropVectorVariable base sz) = "(" ++ show base ++ ":" ++ show sz ++ ")"

variableVector :: PropVectorVariable -> PropVector
variableVector (PropVectorVariable base sz) i =
    if i < sz then
        P.Var $ base + fromIntegral i
    else
        error "overflow in reserved prop vector"

reserveProps :: Size -> Flattening PropVectorVariable
reserveProps sz = do
    FlattenState nextPropId <- get
    put $ FlattenState (nextPropId + fromIntegral sz)
    return $ PropVectorVariable nextPropId sz

class Reservable a where
    requiredProps :: a -> Flattening Size


reserveVarFor :: (Reservable a) => a -> Flattening PropVectorVariable
reserveVarFor x = requiredProps x >>= reserveProps

reserveVarsForAll :: (Reservable a, Ord a, Foldable t) => t a -> Flattening (Map a PropVectorVariable)
reserveVarsForAll =
    foldM (\map x -> do
            var <- reserveVarFor x
            return $ Map.insert x var map
        ) Map.empty

curPropsCount :: Flattening P.Identifier
curPropsCount = do
    FlattenState nextPropId <- get
    return nextPropId

maybeToFlattening :: FlattenError -> Maybe a -> Flattening a
maybeToFlattening _ (Just v) = return v
maybeToFlattening e Nothing = throwError e

getTermType :: Term -> Flattening BitVectorType
getTermType t = maybeToFlattening (TermTypeError t) $ termType t

skeleton :: (Atom -> PropVectorVariable) -> Formula -> P.Formula
skeleton atomProps (Atom atom) = variableVector (atomProps atom) 0 -- This is simply using the atom's reserved variable
skeleton atomProps (Not f) = P.Not $ skeleton atomProps f
skeleton atomProps (And l r) = skeleton atomProps l &&& skeleton atomProps r

bitwiseConstraintIff :: (Size -> P.Formula) -> (Term -> PropVectorVariable) -> Term -> Flattening P.Formula
bitwiseConstraintIff op termProps t = do
    (BitVectorType _ sz) <- getTermType t
    let tProp = variableVector $ termProps t
    return $ P.conjunction $ map (\i -> P.Iff (tProp i) $ op i) [0..sz - 1]

bitwiseConstraintBinary :: (P.Formula -> P.Formula -> P.Formula) -> (Term -> PropVectorVariable) -> Term -> Term -> Term -> Flattening P.Formula
bitwiseConstraintBinary op termProps l r =
    let lProp = variableVector $ termProps l
        rProp = variableVector $ termProps r in
    bitwiseConstraintIff (\i -> op (lProp i) (rProp i)) termProps

fullAdderSum :: P.Formula -> P.Formula -> P.Formula -> P.Formula
fullAdderSum a b cin = (a ^^^ b) ^^^ cin -- (6.37)

fullAdderCarry :: P.Formula -> P.Formula -> P.Formula -> P.Formula
fullAdderCarry a b cin = (a &&& b) ||| ((a ^^^ b) &&& cin) -- (6.38)

-- (6.39) and (6.42)
adderCarry :: PropVector -> PropVector -> P.Formula -> PropVector
adderCarry _ _ cin 0 = cin
adderCarry l r cin i = fullAdderCarry (l (i-1)) (r (i-1)) cin

adderCarryRec :: PropVector -> PropVector -> Bool -> PropVector
adderCarryRec _ _ cin 0 = P.Const cin
adderCarryRec l r cin i = adderCarry l r (adderCarryRec l r cin (i - 1)) i

adder :: PropVector -> PropVector -> Bool -> Size -> Flattening ([P.Formula], PropVector)
adder l r cin sz = do
    carriesPropVector <- reserveProps (sz-1)
    let carryProp = (\i ->
                if i == 0 then
                    P.Const cin
                else
                    variableVector carriesPropVector (i-1)
            ) :: PropVector
        adderCarryConstraints = map (\i -> carryProp i <-> adderCarry l r (carryProp $ i-1) i) [1..sz-1]
    return (adderCarryConstraints, \i -> fullAdderSum (l i) (r i) (carryProp i))

doubleIf :: P.Formula -> P.Formula -> P.Formula -> P.Formula -> P.Formula -> P.Formula
doubleIf ifa resa ifb resb els =
    (ifa &&& resa) ||| (P.Not ifa &&& ifb &&& resb) ||| (P.Not ifa &&& P.Not ifb &&& els)

singleIf :: P.Formula -> P.Formula -> P.Formula -> P.Formula
singleIf ifa resa els =
    (ifa &&& resa) ||| (P.Not ifa &&& els)

shift :: (Size -> Size -> Size) -> (Int -> Size -> Bool) -> PropVector -> PropVector -> Int -> PropVector
shift _ _ l _ (-1) i = l i -- (6.48)
shift dir cond l r s i | cond s i =
    doubleIf (r $ fromIntegral s)
                (shift dir cond l r (s - 1) (i `dir` (2^s)))
             (P.Not (r $ fromIntegral s))
                (shift dir cond l r (s - 1) i)
             -- else
                (P.Const False)
shift dir cond l r s i = -- (6.49)
    singleIf (P.Not (r $ fromIntegral s))
                (shift dir cond l r (s - 1) i)
             -- else
                (P.Const False)

shiftLStatic :: PropVector -> Size -> PropVector
shiftLStatic x s i = if i < s then P.Const False else x (i - s)

lessThanUnsigned :: PropVector -> PropVector -> Size -> P.Formula
lessThanUnsigned l r sz =
    P.Not $ adderCarryRec l (P.Not . r) True (fromIntegral sz) -- (6.46)

lessThanSigned :: PropVector -> PropVector -> PropVector
lessThanSigned l r sz =
    l (fromIntegral (sz-1)) <-> r (fromIntegral (sz-1))
    ^^^
    adderCarryRec l (P.Not . r) True (fromIntegral sz) -- (6.47) but there is a mistake in the book, see "Errata For 2nd Edition"

mult :: PropVector -> PropVector -> Size -> Int -> Flattening ([P.Formula], PropVector)
mult _ _ _ (-1) = return ([], \_ -> P.Const False) -- (6.50)
mult l r sz s = do
    (prevMultConstraints, prevMultBits) <- mult l r sz (s - 1)
    (adderConstraints, addedBits) <- adder prevMultBits (\i -> r (fromIntegral s) &&& shiftLStatic l (fromIntegral s) i) False sz
    return (adderConstraints ++ prevMultConstraints, addedBits) -- (6.51)

multiplication :: PropVector -> PropVector -> Size -> Flattening ([P.Formula], PropVector)
multiplication l r sz = mult l r sz (fromIntegral sz - 1)

extendUnsigned :: PropVector -> Size -> PropVector
extendUnsigned bv oldsz i
    | i < oldsz = bv i
    | otherwise = P.Const False

extendSigned :: PropVector -> Size -> PropVector
extendSigned bv oldsz i
    | i < oldsz - 1 = bv i
    | otherwise     = bv (oldsz - 1)

extend :: BitVectorSign -> PropVector -> Size -> PropVector
extend Signed = extendSigned
extend Unsigned = extendUnsigned

increment :: PropVector -> Size -> Flattening ([P.Formula], PropVector)
increment v sz = do
    carries <- reserveProps (sz - 1)
    let carryProp = (\i ->
                    if i == 0 then
                        P.Const True
                    else
                        variableVector carries (i-1)
                ) :: PropVector
        carryConstraints = map (\i -> carryProp i <-> if i == 0 then P.Const True else v (i-1) &&& carryProp (i-1)) [1..sz-1]
    return (carryConstraints, \i -> v i ^^^ carryProp i)

absolute :: PropVector -> Size -> Flattening ([P.Formula], PropVector)
absolute v sz = do
    let inverted i = P.Not (v i)
    (tcConstraints, tcVec) <- increment inverted sz
    let signProp = v (sz-1)
    return (tcConstraints, \i -> (signProp &&& tcVec i) ||| (P.Not signProp &&& v i))

lessThanAbsolute :: PropVector -> PropVector -> Size -> Flattening ([P.Formula], P.Formula)
lessThanAbsolute l r sz = do
    (absLConstraints, absLVec) <- absolute l sz
    (absRConstraints, absRVec) <- absolute r sz
    return (absLConstraints ++ absRConstraints, lessThanUnsigned absLVec absRVec sz)

divisionConstraint :: BitVectorSign -> PropVector -> PropVector -> PropVector -> PropVector -> Size -> Flattening P.Formula
divisionConstraint sign res l r rem sz = do
    let extsz = sz + sz
        ext = extend sign
        extl = ext l sz
        extr = ext r sz
        extres = ext res sz
        extrem = ext rem sz
    (multConstraints, multBit) <- multiplication extres extr extsz -- term * r
    (addConstraints, addedBit) <- adder multBit extrem False extsz -- (term * r) + rem
    let multAddConstraints = map (\i -> extl i <-> addedBit i) [0..extsz - 1] -- (6.52)
    remainderConstraints <-
        if sign == Signed then do -- extr
            (extraConstraints, constraint) <- lessThanAbsolute extrem extr extsz
            let signConstraint = (l (sz - 1) <-> rem (sz - 1)) ||| P.conjunction (map (P.Not . rem) [0..sz-1]) -- (sign l == sign rem) || (rem == 0)
            return $ signConstraint : constraint : extraConstraints
        else
            return [lessThanUnsigned extrem extr extsz] -- (6.53)
    return $ P.conjunction $ remainderConstraints ++ multAddConstraints ++ addConstraints ++ multConstraints

termPropVector :: (Term -> PropVectorVariable) -> Term -> PropVector
termPropVector termProps t = variableVector $ termProps t

notTermPropVector :: (Term -> PropVectorVariable) -> Term -> PropVector
notTermPropVector termProps t i = P.Not $ variableVector (termProps t) i

termConstraint :: (Atom -> PropVectorVariable) -> (Term -> PropVectorVariable) -> Term -> Flattening P.Formula
termConstraint atomProps termProps term =
    let termBit = termPropVector termProps
        notTermBit = notTermPropVector termProps in
    case term of
    (Var _ _) -> return $ P.Const True
    (Const _ bv) -> return $ P.conjunction $ map (\i ->
            if BV.index bv i then
                termBit term i
            else
                notTermBit term i
        ) [0..BV.length bv - 1] -- (6.35)
    (BinAnd l r) -> bitwiseConstraintBinary (&&&) termProps l r term
    (BinOr l r) -> bitwiseConstraintBinary (|||) termProps l r term
    --(BinXor l r) -> bitwiseConstraintBinary P.Xor termProps l r term
    (BinXor l r) -> do
        (BitVectorType _ sz) <- getTermType term
        return $ P.And $ map (\i ->
                -- Constraint for the i-th bit, bringing the output in relation to the inputs:
                termBit term i <-> (termBit l i ^^^ termBit r i)
            ) [0..sz - 1]
    (Complement t) -> bitwiseConstraintIff (notTermBit t) termProps term
    (Inc t) -> do
        (BitVectorType _ sz) <- getTermType term
        (incConstraints, incVec) <- increment (termBit t) sz
        return $ P.conjunction $ map (\i -> termBit term i <-> incVec i) [0..sz-1] ++ incConstraints
    (Abs t) -> do
        (BitVectorType sign sz) <- getTermType t
        if sign == Signed then do
            (absConstraints, absVec) <- absolute (termBit t) sz
            return $ P.conjunction $ map (\i -> termBit term i <-> absVec i) [0..sz-1] ++ absConstraints
        else
            return $ P.conjunction $ map (\i -> termBit term i <-> termBit t i) [0..sz-1]
    (Plus l r) -> do
        let (BitVectorType _ sz) = fromJust $ termType term
        (adderConstraints, addedBit) <- adder (termBit l) (termBit r) False sz
        return $ P.conjunction $ adderConstraints ++ map (\i ->
                termBit term i <-> addedBit i  -- (6.41), (6.43)
            ) [0..sz - 1]
    (Minus l r) -> do
        (BitVectorType _ sz) <- getTermType term
        (adderConstraints, addedBit) <- adder (termBit l) (notTermBit r) True sz
        return $ P.conjunction $ adderConstraints ++ map (\i ->
                termBit term i <-> addedBit i -- (6.44)
            ) [0..sz - 1] -- (6.41)
    (ShL l r) -> do
        (BitVectorType _ sz) <- getTermType l -- Term type checking ensures sz == 2^ssz
        (BitVectorType _ ssz) <- getTermType r
        return $ P.conjunction $ map (\i ->
                termBit term i <-> shift (-) (\s i -> i >= 2^s) (termBit l) (termBit r) (fromIntegral ssz - 1) i
            ) [0..fromIntegral sz - 1]
    (ShR l r) -> do
        (BitVectorType _ sz) <- getTermType l -- Term type checking ensures sz == 2^ssz
        (BitVectorType _ ssz) <- getTermType r
        return $ P.conjunction $ map (\i ->
                termBit term i <-> shift (+) (\s i -> i + (2^s) < sz) (termBit l) (termBit r) (fromIntegral ssz - 1) i
            ) [0..fromIntegral sz - 1]
    (Mult l r) -> do
        let (BitVectorType _ sz) = fromJust $ termType term
        (multConstraints, multBit) <- multiplication (termBit l) (termBit r) sz
        return $ P.conjunction $ multConstraints ++ map (\i ->
                termBit term i <-> multBit i
            ) [0..fromIntegral sz - 1]
    (Div l r) -> do
        BitVectorType sign sz <- getTermType l
        remPV <- reserveProps sz
        divisionConstraint sign (termBit term) (termBit l) (termBit r) (variableVector remPV) sz
    (Remainder l r) -> do
        BitVectorType sign sz <- getTermType l
        resPV <- reserveProps sz
        divisionConstraint sign (variableVector resPV) (termBit l) (termBit r) (termBit term) sz
    (Concat _ l r) -> do
        (BitVectorType _ lsz) <- getTermType l
        bitwiseConstraintIff (\i -> if i < lsz then termBit l i else termBit r (i-lsz)) termProps term
    (Ext _ t) -> do
        (BitVectorType sign sz) <- getTermType t
        bitwiseConstraintIff (extend sign (termBit t) sz) termProps term
    (Slice _ off _ t) ->
        bitwiseConstraintIff (\i -> termBit t (off + i)) termProps term
    (Ternary c a b) ->
        let atomProp = variableVector (atomProps c) 0 in
        bitwiseConstraintIff (\i -> (atomProp &&& termBit a i) ||| (P.Not atomProp &&& termBit b i)) termProps term

atomConstraint :: (Atom -> PropVectorVariable) -> (Term -> PropVectorVariable) -> Atom -> Flattening P.Formula
atomConstraint atomProps termProps atom =
    let atomProp = variableVector (atomProps atom) 0
        termBit = termPropVector termProps in
    case atom of
        (BConst True) -> return $ variableVector (atomProps atom) 0
        (BConst False) -> return $ P.Not $ variableVector (atomProps atom) 0
        (Equals l r) -> do
            lt <- getTermType l
            rt <- getTermType r
            when (lt /= rt) $ throwError $ AtomTypeMismatch atom
            (atomProp <->) <$> bitwiseConstraintIff (variableVector (termProps r)) termProps l
        (Pick i t) -> do
            (BitVectorType _ sz) <- getTermType t
            when (i >= sz) $ throwError $ AtomPickBoundsError atom
            return $ atomProp <-> termBit t i
        (LessThan l r) -> do
             lt <- getTermType l
             rt <- getTermType r
             when (lt /= rt) $ throwError $ AtomTypeMismatch atom
             let (BitVectorType sign sz) = lt
             return $ atomProp <->
                if sign == Signed then
                    lessThanSigned (termBit l) (termBit r) sz
                else
                    lessThanUnsigned (termBit l) (termBit r) sz


-- |reserves one propositional variable for each bit in each term
termVars :: Foldable a => a Term -> Flattening (Map Term PropVectorVariable)
termVars =
    foldM (\map term -> do
            (BitVectorType _ sz) <- getTermType term
            baseProp <- reserveProps sz
            return $ Map.insert term baseProp map
        ) Map.empty

instance Reservable Term where
    requiredProps term = (\(BitVectorType _ sz) -> sz) <$> getTermType term

instance Reservable Atom where
    requiredProps _ = return 1

data FlattenedFormula = FlattenedFormula {
    atomProps :: Map Atom PropVectorVariable,
    termProps :: Map Term PropVectorVariable,
    skeletonFormula :: P.Formula,
    termConstraints :: Map Term P.Formula,
    atomConstraints :: Map Atom P.Formula,
    propsCount :: Int
}

-- |Helper function that applies a function in m to each set member and constructs a
-- Map containing the results.
mapFromSetM :: (Ord k, Monad m) => (k -> m a) -> Set.Set k -> m (Map k a)
mapFromSetM f ks = Map.fromList <$> mapM (\a -> f a >>= \c -> return (a, c)) (Set.toList ks)

formulaFlattening :: Formula -> Flattening FlattenedFormula
formulaFlattening f = do
    let allTerms = Set.fromList $ terms f
        allAtoms = Set.fromList $ atoms f
    atomProps <- reserveVarsForAll allAtoms
    termProps <- reserveVarsForAll allTerms
    let skel = skeleton (atomProps Map.!) f
    termConstraints <- mapFromSetM (termConstraint (atomProps Map.!) (termProps Map.!)) allTerms
    atomConstraints <- mapFromSetM (atomConstraint (atomProps Map.!) (termProps Map.!)) allAtoms
    propsCount <- curPropsCount
    return $ FlattenedFormula {
        atomProps = atomProps,
        termProps = termProps,
        skeletonFormula = skel,
        termConstraints = termConstraints,
        atomConstraints = atomConstraints,
        propsCount = propsCount
    }

-- |Convenience function that calls formulaFlattening and evaluates the returned monadic value
flatten :: Formula -> Either FlattenError FlattenedFormula
flatten f = runFlattening (formulaFlattening f) (FlattenState 0)

instance Show FlattenedFormula where
    show (FlattenedFormula atomProps termProps skeletonFormula termConstraints atomConstraints _) =
        printf "skeleton: %s\nterms:\n%satoms:\n%s" (show skeletonFormula) (
                concat $
                    Map.mapWithKey (\term (prop, constraint) -> "  " ++ show term ++ " = " ++ show prop ++ " => " ++ show constraint ++ "\n") $
                    Map.intersectionWith (,) termProps termConstraints
            ) (
                concat $
                    Map.mapWithKey (\atom (prop, constraint) -> "  " ++ show atom ++ " = " ++ show prop ++ " => " ++ show constraint ++ "\n") $
                    Map.intersectionWith (,) atomProps atomConstraints
            )

propositional :: FlattenedFormula -> P.Formula
propositional (FlattenedFormula _ _ skeletonFormula termConstraints atomConstraints _) =
    P.conjunction $ skeletonFormula : Map.elems termConstraints ++ Map.elems atomConstraints

-- |Maps the result from the SAT-solver back to the original bit vector variables
reconstructResult :: Formula -> FlattenedFormula -> Map P.Identifier Bool -> Map Identifier BV.BitVectorValue
reconstructResult f flat propResults =
    let allVars = Set.fromList $ vars f in
    Map.fromList $ map (\(BitVectorType sign sz, name) ->
            let (PropVectorVariable baseProp _) = termProps flat Map.! Var (BitVectorType sign sz) name
                bits = map (\i -> Map.findWithDefault False (baseProp + i) propResults) [0..fromIntegral sz - 1] in
            (name, BV.pack bits)
        ) $ Set.toList allVars
