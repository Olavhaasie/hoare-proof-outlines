{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Tactic.Reflection where

open import Data.List using ([])
open import Data.Vec as V using (Vec)

open import Function using (_⟨_⟩_)

open import Reflection.AST.Argument
open import Reflection.AST.Term
open import Reflection.TCM using (TC; checkType)

open import Relation.Ternary.Core using (Rel₃)
open import Relation.Ternary.Tactic.Bundles
open import Relation.Ternary.Tactic.Expression.Properties using (_∷ⁿ_; []ⁿ)


`env : ∀ {n} → Vec Term n → Term
`env V.[] = quote []ⁿ ⟨ con ⟩ []
`env (x V.∷ xs) = quote _∷ⁿ_ ⟨ con ⟩ x ⟨∷⟩ `env xs ⟨∷⟩ []

`MonoidWithUnique : Term
`MonoidWithUnique = quote MonoidWithUnique ⟨ def ⟩ 2 ⋯⟨∷⟩ []

`CommutativeMonoidWithUnique : Term
`CommutativeMonoidWithUnique = quote CommutativeMonoidWithUnique ⟨ def ⟩ 2 ⋯⟨∷⟩ []
