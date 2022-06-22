{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Tactic.Util where

open import Data.List using (List; map; reverse; take; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import Data.String using (String)

open import Function using (_$_)

open import Reflection.AST.Argument hiding (map)
open import Reflection.AST.DeBruijn using (strengthen)
open import Reflection.AST.Term


-- Tries to strip the arguments from a non-normalised predicate
-- equality _≐_.
≐-getArgs : Term → Maybe (Term × Term)
≐-getArgs (def _ xs) = go xs
  where
    go : List (Arg Term) → Maybe (Term × Term)
    go (vArg x ∷ vArg y ∷ []) = just $ x , y
    go (_ ∷ xs)               = go xs
    go _                      = nothing
≐-getArgs _ = nothing

-- Tries to strip a non-dependent Pi to its elements.
⇒-getArgs : Term → Maybe (Term × Term)
⇒-getArgs (vΠ[ _ ∶ x ] y) = do
  y ← strengthen y
  just $ x , y
⇒-getArgs _ = nothing

-- Tries to strip a Pi to its elements.
stripPi : Term → Maybe (String × Arg Type × Term)
stripPi (Π[ s ∶ a ] x) = just $ s , a , x
stripPi _ = nothing

-- Removes the last element from the list, or nothing if the list is
-- empty.
init : ∀ {a} {A : Set a} → List A → List A
init [] = []
init (x ∷ []) = []
init (x ∷ xs) = x ∷ init xs

-- Returns the last n terms of an argument list.
last : (n : ℕ) → Args Term → List Term
last n l = map unArg $ reverse $ take n $ reverse l
