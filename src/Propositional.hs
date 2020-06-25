{-# LANGUAGE LambdaCase #-}

module Propositional (
    Identifier,
    Formula (..),
    (<->),
    (-->),
    (&&&),
    (|||),
    (^^^),
    (Propositional.!!),
    conjunction,
    elimAllConsts,
    eval
) where

import Text.Printf
import Data.List

import Common

type Identifier = Int

data Formula =
    Iff Formula Formula |
    Impl Formula Formula |
    And [Formula] |
    Or [Formula] |
    Xor Formula Formula |
    Not Formula |
    Var Identifier |
    Const Bool
    deriving (Eq)

instance Show Formula where
    show (Iff l r) = printf "(%s ↔ %s)" (show l) (show r)
    show (Impl l r) = printf "(%s → %s)" (show l) (show r)
    show (And fs) = "(" ++ intercalate " ∧ " (map show fs) ++ ")"
    show (Or fs) = "(" ++ intercalate " ∨ " (map show fs) ++ ")"
    show (Xor l r) = printf "(%s ⊕ %s)" (show l) (show r)
    show (Not f)   = printf "¬%s" (show f)
    show (Var a)   = show a
    show (Const b) = show b

(<->) = Iff;
(-->) = Impl;
(&&&) l r = And [l, r];
(|||) l r = Or [l, r]
(^^^) = Xor;
(!!) = Not

conjunction :: [Formula] -> Formula
conjunction = And

elimConst :: Formula -> Formula
elimConst (Iff l (Const True)) = elimConst l
elimConst (Iff l (Const False)) = elimConst $ Not l
elimConst (Iff (Const True) r) = elimConst r
elimConst (Iff (Const False) r) = elimConst $ Not r
elimConst (Iff l r) = Iff (elimConst l) (elimConst r)
elimConst (Impl (Const True) r) = elimConst r
elimConst (Impl (Const False) _) = Const True
elimConst (Impl _ (Const True)) = Const True
elimConst (Impl l (Const False)) = Not $ elimConst l
elimConst (Impl l r) = Impl (elimConst l) (elimConst r)
elimConst (And fs) =
    if any (\case Const False -> True; _ -> False) fs then
        Const False
    else
        And $ filter (\case Const True -> False; _ -> True) $ map elimConst fs
elimConst (Or fs) =
    if any (\case Const True -> True; _ -> False) fs then
        Const True
    else
        And $ filter (\case Const False -> False; _ -> True) $ map elimConst fs
elimConst (Xor l (Const True)) = Not $ elimConst l
elimConst (Xor l (Const False)) = elimConst l
elimConst (Xor (Const True) r) = Not $ elimConst r
elimConst (Xor (Const False) r) = elimConst r
elimConst (Xor l r) = Xor (elimConst l) (elimConst r)
elimConst (Not (Const True)) = Const False
elimConst (Not (Const False)) = Const True
elimConst (Not f) = Not $ elimConst f
elimConst (Var id) = Var id
elimConst (Const v) = Const v

elimAllConsts :: Formula -> Formula
elimAllConsts = fixedPoint elimConst

eval :: (Identifier -> Bool) -> Formula -> Bool
eval ass (Iff l r) = eval ass l == eval ass r
eval ass (Impl l r) = eval ass l || (eval ass l && eval ass r)
eval ass (And fs) = foldl (\acc f -> acc && eval ass f) True fs
eval ass (Or fs) = foldl (\acc f -> acc || eval ass f) False fs
eval ass (Xor l r) = eval ass l /= eval ass r
eval ass (Not f) = not $ eval ass f
eval ass (Var id) = ass id
eval _   (Const c) = c