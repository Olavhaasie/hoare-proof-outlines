{-# OPTIONS --safe --without-K #-}
{-
  This module implements the monoid solver tactic for automatically
  constructing proofs of equalities on monoid predicate expressions in
  a `PartialMonoid` from the Ternary library.
-}
module Relation.Ternary.Tactic.MonoidSolver where

open import Data.Fin using (_≟_)
open import Data.Nat using (ℕ)
open import Data.List using ([_]; _∷_; [])
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; _∷_; [])

open import Relation.Binary.PropositionalEquality using (cong; refl; _≡_)
open import Relation.Nullary using (Dec; no; yes)
open import Relation.Ternary.Tactic.Bundles
open import Relation.Ternary.Tactic.Core
open import Relation.Ternary.Tactic.Expression
open import Relation.Ternary.Tactic.Reflection
open import Relation.Unary using (_≐_)
open import Relation.Unary.Relation.Binary.Equality using (≐-setoid)


private
  variable
    n : ℕ

  -- Decidable prefix order on normal forms.
  _≤_ : NF n → NF n → Set
  _≤_ = Prefix _≡_

  _≤?_ : (x y : NF n) → Dec (x ≤ y)
  _≤?_ [] _ = yes []
  _≤?_ (_ ∷ _) [] = no λ ()
  _≤?_ (x ∷ xs) (y ∷ ys) with x ≟ y | xs ≤? ys
  ... | yes x≡y | yes xs≤ys = yes (x≡y ∷ xs≤ys)
  ... | yes x≡y | no  xs≰ys = no λ { (_ ∷ xs≤ys) → xs≰ys xs≤ys }
  ... | no  x≢y | _         = no λ { (x≡y ∷ _) → x≢y x≡y }

  module _ {a e} (monoid : MonoidWithUnique a e) where
    open MonoidWithUnique monoid hiding (_≤_)

    open import Relation.Binary.Reasoning.Setoid (≐-setoid Carrier a)
    open import Relation.Ternary.Tactic.Expression.Properties monoid


    solve : ∀ (x y : Expr n) → norm x ≡ norm y → Solution x y
    solve x y nf≡ ρ = begin
      [ x ↓] ρ      ≈˘⟨ norm-homo x ρ ⟩
      [ norm x ⇓] ρ ≡⟨ cong ([_⇓] ρ) nf≡ ⟩
      [ norm y ⇓] ρ ≈⟨ norm-homo y ρ ⟩
      [ y ↓] ρ      ∎

    -- Subtract the right normal form from the first normal form to be
    -- left with a "frame", when the right is a prefix of left.
    subtractNF≤ : (l r : NF n) → r ≤ l → NF n
    subtractNF≤ l [] [] = l
    subtractNF≤ (_ ∷ l) (_ ∷ r) (refl ∷ p) = subtractNF≤ l r p

    frame-homo : ∀ (x y : NF n) (y≤x : y ≤ x) (ρ : Env n)
      → [ x ⇓] ρ ≐ [ y ⇓] ρ ✴ [ subtractNF≤ x y y≤x ⇓] ρ
    frame-homo x .[] [] ρ = begin
      [ x ⇓] ρ                               ≈˘⟨ ✴-identityˡ ⦃ [⇓]-respects-≈ x ρ ⦄ ⟩
      Emp ✴ [ x ⇓] ρ                         ≡⟨⟩
      [ [] ⇓] ρ ✴ [ x ⇓] ρ                   ≡⟨⟩
      [ [] ⇓] ρ ✴ [ subtractNF≤ x [] [] ⇓] ρ ∎
    frame-homo (x ∷ xs) (y ∷ ys) (refl ∷ y≤x) ρ = begin
      [ x ∷ xs ⇓] ρ                                                     ≡⟨⟩
      lookup ρ x ✴ [ xs ⇓] ρ                                            ≈⟨ ✴-congˡ (frame-homo xs ys y≤x ρ) ⟩
      lookup ρ y ✴ [ ys ⇓] ρ ✴ [ subtractNF≤ xs ys y≤x ⇓] ρ             ≈˘⟨ ✴-assoc ⟩
      (lookup ρ y ✴ [ ys ⇓] ρ) ✴ [ subtractNF≤ xs ys y≤x ⇓] ρ           ≡⟨⟩
      [ y ∷ ys ⇓] ρ ✴ [ subtractNF≤ (x ∷ xs) (y ∷ ys) (refl ∷ y≤x) ⇓] ρ ∎

    frame : ∀ (x y : Expr n) → norm y ≤ norm x → Expr n
    frame x y y≤x = nf-to-expr (subtractNF≤ (norm x) (norm y) y≤x)

    solve-frame : ∀ (x y : Expr n) (y≤x : norm y ≤ norm x)
      → FrameSolution x y (frame x y y≤x)
    solve-frame x y y≤x ρ = begin
      [ x ↓] ρ                               ≈˘⟨ norm-homo x ρ ⟩
      [ norm x ⇓] ρ                          ≈⟨ frame-homo (norm x) (norm y) y≤x ρ ⟩
      [ norm y ⇓] ρ ✴ [ frame x y y≤x ↓] ρ   ≈⟨ ✴-congʳ (norm-homo y ρ) ⟩
      [ y ↓] ρ ✴ [ frame x y y≤x ↓] ρ        ∎


MonoidSolver : Solver
Solver._⇓ MonoidSolver = norm
Solver._∼_ MonoidSolver = _≤_
Solver._∼?_ MonoidSolver = _≤?_
Solver.solver MonoidSolver = quote solve
Solver.frame-solver MonoidSolver = quote solve-frame
Solver.monoidType MonoidSolver = `MonoidWithUnique

open Solver MonoidSolver public
