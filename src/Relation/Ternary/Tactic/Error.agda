{-# OPTIONS --safe --without-K #-}
-- Errors used by all solvers.
module Relation.Ternary.Tactic.Error where

open import Data.List using (List; intersperse; map)
open import Data.Nat using (ℕ)

open import Function using (_$_)

open import Level using (Level)

open import Reflection.AST.Term using (Term)
open import Reflection.TCM using (TC; typeErrorFmt; strErr; termErr)


private
  variable
    a : Level
    A : Set a

buildError : Term → TC A
buildError = typeErrorFmt "Failed to build expression from:\n%t"

envNormError : Term → Term → TC A
envNormError = typeErrorFmt "LHS and RHS have different normal forms:
lhs: %t
rhs: %t
"

envError : Term → List Term → TC A
envError found env = typeErrorFmt "Failed to align the two environments of LHS and RHS.
Found the term: %t
Which is not contained in the environment: %e
" found (intersperse (strErr " , ") $ map termErr env)

envLengthError : ℕ → ℕ → TC A
envLengthError = typeErrorFmt "LHS and RHS do not have the same amount of atoms: %u ≢ %u"

envGreaterLengthError : ℕ → ℕ → TC A
envGreaterLengthError = typeErrorFmt "RHS should have less than or equal atoms as LHS: %u ≰ %u"

malformed-≐ : Term → TC A
malformed-≐ = typeErrorFmt "Malformed call to solve.
Goal type should be of the form: LHS ≐ RHS
Instead found: %t
"

malformed-∀ : Term → TC A
malformed-∀ = typeErrorFmt "Malformed call to solve-∀.
Goal type should be of the form : ∀ a → LHS a ≐ RHS a
Instead found: %t
"

malformed-∀-≐ : Term → TC A
malformed-∀-≐ = typeErrorFmt "Malformed call to solve-∀.
Goal type inside ∀ should be of the form : LHS ≐ RHS
Instead found: %t
"

malformed-≐-✴ : Term → TC A
malformed-≐-✴ = typeErrorFmt "Malformed call to solve-frame.
Goal type should be of the form: LHS ≐ RHS ✴ _
Instead found: %t
"

malformed-✴ : Term → TC A
malformed-✴ = typeErrorFmt "Malformed RHS in call to solve-frame.
RHS should be of the form: RHS ✴ _
Instead found: %t
"

no-frame : Term → Term → TC A
no-frame = typeErrorFmt "No frame found between %t and %t"

malformed-⊆ : Term → TC A
malformed-⊆ = typeErrorFmt "Malformed call to solve-⊆.
Goal type should be of the form: LHS ⊆ RHS or ∀[ LHS ⇒ RHS ]
Instead found: %t
"
