{-# OPTIONS --safe --without-K #-}
{-
  This module implements the monoid solver tactic for automatically
  constructing proofs of equalities on commutative monoid predicate
  expressions.
-}
module Relation.Ternary.Tactic.CommutativeMonoidSolver where

open import Data.Fin using (_≟_)
open import Data.Fin.Properties using (≤-decTotalOrder)
open import Data.List using (_++_; _∷_; [])
open import Data.List.Relation.Binary.Permutation.Propositional
private
  module _ {n} where
    open import Data.List.Relation.Binary.Sublist.DecPropositional (_≟_ {n}) using (_⊆_; _⊆?_; _∷_; _∷ʳ_; []) public
    -- The implementation does not depend on the implementation of merge
    -- sort, however, it requires a definition of a sorting algorithm to
    -- normalise a sorted list.
    open import Data.List.Sort.MergeSort (≤-decTotalOrder n) using (sort; sort-↭) public
open import Data.Nat using (ℕ)

open import Relation.Binary.PropositionalEquality using (cong; refl; _≡_)
open import Relation.Ternary.Tactic.Bundles
open import Relation.Ternary.Tactic.Core
open import Relation.Ternary.Tactic.Expression
open import Relation.Ternary.Tactic.Reflection
open import Relation.Unary using (_≐_)
open import Relation.Unary.Properties using (≐-refl)
open import Relation.Unary.Relation.Binary.Equality using (≐-setoid)


private
  variable
    n : ℕ

  module _ {a e} (monoid : CommutativeMonoidWithUnique a e) where
    open CommutativeMonoidWithUnique monoid

    open import Relation.Binary.Reasoning.Setoid (≐-setoid Carrier a)
    open import Relation.Ternary.Tactic.Expression.Properties monoidWithUnique


    -------------------------------------------------------------
    -- Homomorphism proofs

    ↭-homo : ∀ {xs ys : NF n} (ρ : Env n) → xs ↭ ys → [ xs ⇓] ρ ≐ [ ys ⇓] ρ
    ↭-homo ρ refl = ≐-refl
    ↭-homo ρ (prep {xs} {ys} x xs↭ys) = begin
      [ x ∷ xs ⇓] ρ          ≡⟨⟩
      lookup ρ x ✴ [ xs ⇓] ρ ≈⟨ ✴-congˡ (↭-homo ρ xs↭ys) ⟩
      lookup ρ x ✴ [ ys ⇓] ρ ≡⟨⟩
      [ x ∷ ys ⇓] ρ          ∎
    ↭-homo ρ (swap {xs} {ys} x y xs↭ys) = begin
      [ x ∷ y ∷ xs ⇓] ρ                     ≡⟨⟩
      lookup ρ x ✴ lookup ρ y ✴ [ xs ⇓] ρ   ≈˘⟨ ✴-assoc ⟩
      (lookup ρ x ✴ lookup ρ y) ✴ [ xs ⇓] ρ ≈⟨ ✴-congʳ ✴-comm ⟩
      (lookup ρ y ✴ lookup ρ x) ✴ [ xs ⇓] ρ ≈⟨ ✴-congˡ (↭-homo ρ xs↭ys) ⟩
      (lookup ρ y ✴ lookup ρ x) ✴ [ ys ⇓] ρ ≈⟨ ✴-assoc ⟩
      lookup ρ y ✴ lookup ρ x ✴ [ ys ⇓] ρ   ≡⟨⟩
      [ y ∷ x ∷ ys ⇓] ρ                     ∎
    ↭-homo ρ (trans {x} {z} {y} x↭z z↭y) = begin
      [ x ⇓] ρ ≈⟨ ↭-homo ρ x↭z ⟩
      [ z ⇓] ρ ≈⟨ ↭-homo ρ z↭y ⟩
      [ y ⇓] ρ ∎

    sort-homo : ∀ (x : Expr n) (ρ : Env n) → [ sort (norm x) ⇓] ρ ≐ [ x ↓] ρ
    sort-homo x ρ = begin
      [ sort (norm x) ⇓] ρ ≈⟨ ↭-homo ρ (sort-↭ (norm x)) ⟩
      [ norm x ⇓] ρ        ≈⟨ norm-homo x ρ ⟩
      [ x ↓] ρ             ∎

    solve : ∀ (x y : Expr n) → sort (norm x) ≡ sort (norm y) → Solution x y
    solve x y nf≡ ρ = begin
      [ x ↓] ρ             ≈˘⟨ sort-homo x ρ ⟩
      [ sort (norm x) ⇓] ρ ≡⟨ cong ([_⇓] ρ) nf≡ ⟩
      [ sort (norm y) ⇓] ρ ≈⟨ sort-homo y ρ ⟩
      [ y ↓] ρ             ∎


    -------------------------------------------------------------
    -- Frame homomorphism proofs

    -- Subtract the right normal form from the first normal form to be
    -- left with a "frame", when the right is a subset of left.
    subtractNF⊆  : (l r : NF n) → r ⊆ l → NF n
    subtractNF⊆ l [] []⊆l = l
    subtractNF⊆ (x ∷ l) r@(_ ∷ _) (_ ∷ʳ r⊆l) = x ∷ subtractNF⊆ l r r⊆l
    subtractNF⊆ (_ ∷ l) (_ ∷ r) (_ ∷ r⊆l) = subtractNF⊆ l r r⊆l

    frame-homo : ∀ {n} (x y : NF n) (y⊆x : y ⊆ x) (ρ : Env n)
      → [ x ⇓] ρ ≐ [ y ⇓] ρ ✴ [ subtractNF⊆ x y y⊆x ⇓] ρ
    frame-homo x [] []⊆x ρ = begin
      [ x ⇓] ρ                                 ≈˘⟨ ✴-identityˡ ⦃ [⇓]-respects-≈ x ρ ⦄ ⟩
      Emp ✴ [ x ⇓] ρ                           ≡⟨⟩
      [ [] ⇓] ρ ✴ [ x ⇓] ρ                     ≡⟨⟩
      [ [] ⇓] ρ ✴ [ subtractNF⊆ x [] []⊆x ⇓] ρ ∎
    frame-homo (x ∷ xs) y@(_ ∷ _) (x ∷ʳ y⊆x) ρ =
      begin
        [ x ∷ xs ⇓] ρ
      ≡⟨⟩
        lookup ρ x ✴ [ xs ⇓] ρ
      ≈⟨ ✴-congˡ (frame-homo xs y y⊆x ρ) ⟩
        lookup ρ x ✴ [ y ⇓] ρ ✴ [ subtractNF⊆ xs y y⊆x ⇓] ρ
      ≈˘⟨ ✴-assoc ⟩
        (lookup ρ x ✴ [ y ⇓] ρ) ✴ [ subtractNF⊆ xs y y⊆x ⇓] ρ
      ≈⟨ ✴-congʳ ✴-comm ⟩
        ([ y ⇓] ρ ✴ lookup ρ x) ✴ [ subtractNF⊆ xs y y⊆x ⇓] ρ
      ≈⟨ ✴-assoc ⟩
        [ y ⇓] ρ ✴ lookup ρ x ✴ [ subtractNF⊆ xs y y⊆x ⇓] ρ
      ≡⟨⟩
        [ y ⇓] ρ ✴ [ x ∷ subtractNF⊆ xs y y⊆x ⇓] ρ
      ≡⟨⟩
        [ y ⇓] ρ ✴ [ subtractNF⊆ (x ∷ xs) y (x ∷ʳ y⊆x) ⇓] ρ
      ∎
    frame-homo (x ∷ xs) (y ∷ ys) (refl ∷ y⊆x) ρ =
      begin
        [ x ∷ xs ⇓] ρ
      ≡⟨⟩
        lookup ρ x ✴ [ xs ⇓] ρ
      ≈⟨ ✴-congˡ (frame-homo xs ys y⊆x ρ) ⟩
        lookup ρ y ✴ [ ys ⇓] ρ ✴ [ subtractNF⊆ xs ys y⊆x ⇓] ρ
      ≈˘⟨ ✴-assoc ⟩
        (lookup ρ y ✴ [ ys ⇓] ρ) ✴ [ subtractNF⊆ xs ys y⊆x ⇓] ρ
      ≡⟨⟩
        [ y ∷ ys ⇓] ρ ✴ [ subtractNF⊆ (x ∷ xs) (y ∷ ys) (refl ∷ y⊆x) ⇓] ρ
      ∎

    frame : ∀ (x y : Expr n) → sort (norm y) ⊆ sort (norm x) → Expr n
    frame x y y⊆x = nf-to-expr (subtractNF⊆ (sort (norm x)) (sort (norm y)) y⊆x)

    solve-frame : ∀ (x y : Expr n) (y⊆x : sort (norm y) ⊆ sort (norm x))
      → FrameSolution x y (frame x y y⊆x)
    solve-frame x y y⊆x ρ =
      begin
        [ x ↓] ρ
      ≈˘⟨ sort-homo x ρ ⟩
        [ sort (norm x) ⇓] ρ
      ≈⟨ frame-homo (sort (norm x)) (sort (norm y)) y⊆x ρ ⟩
        [ sort (norm y) ⇓] ρ ✴ [ frame x y y⊆x ↓] ρ
      ≈⟨ ✴-congʳ (sort-homo y ρ) ⟩
        [ y ↓] ρ ✴ [ frame x y y⊆x ↓] ρ
      ∎


CommutativeMonoidSolver : Solver
Solver._⇓ CommutativeMonoidSolver x = sort (norm x)
Solver._∼_ CommutativeMonoidSolver = _⊆_
Solver._∼?_ CommutativeMonoidSolver = _⊆?_
Solver.solver CommutativeMonoidSolver = quote solve
Solver.frame-solver CommutativeMonoidSolver = quote solve-frame
Solver.monoidType CommutativeMonoidSolver = `CommutativeMonoidWithUnique

open Solver CommutativeMonoidSolver public
