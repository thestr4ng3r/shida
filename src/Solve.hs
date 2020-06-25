module Solve (
    SolveResult (..),
    Solution,
    solve,
    solveAll,
    solveIncremental,
    costEstimate
) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.List
-- import Debug.Trace

import qualified SAT.MiniSat as M

import qualified BitVectorValue as BV
import qualified Propositional as P
import Formula
import Flattening
import MiniSat

data SolveResult a =
    Solution a |
    Unsatisfiable |
    FlattenError FlattenError
    deriving (Eq, Show)

type Solution = Map Identifier BV.BitVectorValue

-- |Solve to a single solution
solve :: Formula -> SolveResult Solution
solve f =
    case flatten f of
        Left e -> FlattenError e
        Right flat ->
            case M.solve $ miniSat $ propositional flat of
                Nothing -> Unsatisfiable
                Just r -> Solution $ reconstructResult f flat r

-- |Solve to all solutions as a lazy list
solveAll :: Formula -> SolveResult [Solution]
solveAll f =
    case flatten f of
        Left e -> FlattenError e
        Right flat ->
            case M.solve_all $ miniSat $ propositional flat of
                [] -> Unsatisfiable
                sols -> Solution $ map (reconstructResult f flat) sols

-- |Solve incrementally to a single solution
-- This can be significantly faster or slower than solve depending on the
-- formula, see the paper for more info.
solveIncremental :: Int -> Formula -> SolveResult Solution
solveIncremental steps f =
    case flatten f of
        Left e -> FlattenError e
        Right flat -> solveFlattenedIncremental steps f flat

costEstimate :: P.Formula -> Word
costEstimate (P.Iff l r) = 1 + costEstimate l + costEstimate r
costEstimate (P.Impl l r) = 1 + costEstimate l + costEstimate r
costEstimate (P.And fs) = foldl (\acc f -> acc + costEstimate f) (1 + fromIntegral (length fs)) fs
costEstimate (P.Or fs) = foldl (\acc f -> acc + costEstimate f) (1 + fromIntegral (length fs)) fs
costEstimate (P.Xor l r) = 1 + costEstimate l + costEstimate r
costEstimate (P.Not f) = costEstimate f
costEstimate (P.Var _) = 1
costEstimate (P.Const _) = 0

-- |Solve a formula incrementally, given the number of new constraints to add in each step
solveFlattenedIncremental :: Int -> Formula -> FlattenedFormula -> SolveResult Solution
solveFlattenedIncremental stepSize f flat =
    let (FlattenedFormula _ _ skeletonFormula termConstraints atomConstraints _) = flat
        initialFormulas = [skeletonFormula]
        incrementalFormulas = sortOn costEstimate $ filter (/= P.Const True) $ Map.elems termConstraints ++ Map.elems atomConstraints
        fullFormula = propositional flat
    in case incrementalSAT stepSize fullFormula initialFormulas incrementalFormulas of
        Nothing -> Unsatisfiable
        Just r -> Solution $ reconstructResult f flat r

-- |Solve a SAT problem incrementally by recursion, given the number of new constraints to add in
-- each step, the full formula, constraints to be considered right now and constraints to be
-- considered later.
incrementalSAT :: Int -> P.Formula -> [P.Formula] -> [P.Formula] -> Maybe (Map P.Identifier Bool)
incrementalSAT stepSize full current pending = -- trace ("incrementalSat " ++ show (length current) ++ "/" ++ show (length pending)) $
    case M.solve $ miniSat $ P.conjunction current of
        Nothing -> Nothing -- partial formula unsatisfiable => full formula unsatisfiable
        Just r -> -- partial formula satisfiable
            let conflicts = filter (not . P.eval (\id -> Map.findWithDefault False id r)) pending in
            if null conflicts then
                Just r -- no conflicts, full formula satisfied!
            else
                -- got conflicts, move the easiest ones into the current list
                let new = take stepSize conflicts -- pick the easiest conflicts
                    nextPending = filter (not . (`elem` new)) pending in -- remove them from pending
                incrementalSAT stepSize full (new ++ current) nextPending
