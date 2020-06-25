module MiniSat where

import qualified SAT.MiniSat as M

import qualified Propositional as P

-- |Convert our representation of propositional formulas to the one accepted by SAT.MiniSat
miniSat :: P.Formula -> M.Formula P.Identifier
miniSat (P.Iff l r) = miniSat l M.:<->: miniSat r
miniSat (P.Impl l r) = miniSat l M.:->: miniSat r
--miniSat (P.And l r) = miniSat l M.:&&: miniSat r
--miniSat (P.Or l r) = miniSat l M.:||: miniSat r
miniSat (P.And fs) = M.All $ map miniSat fs
miniSat (P.Or fs) = M.Some $ map miniSat fs
miniSat (P.Xor l r) = miniSat l M.:++: miniSat r
miniSat (P.Not f) = M.Not $ miniSat f
miniSat (P.Var id) = M.Var id
miniSat (P.Const c) = if c then M.Yes else M.No