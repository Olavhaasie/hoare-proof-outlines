{-# OPTIONS --safe --without-K #-}
open import Relation.Hoare.Bundles

module Bench {Val : Set → Set} (S : CommutativeStoreWithUnique Val) where

open CommutativeStoreWithUnique S hiding (_∙_)

open import Data.Nat

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Core using (Respect)
open import Relation.Ternary.Tactic.CommutativeMonoidSolver
open import Relation.Unary using (_≐_)

private
  variable
    s : ℕ
    x y z w t : SPred
    l k m p q : L
    a b c : Val L
    P Q R : Set

{-
  This module benchmarks the solver by comparing the definition of
  pointsto to an abstract definition of pointsto. The abstract
  definition performs significanlty better, because Agda will not try
  to quote and unquote the definition, which is slow.
-}
module _
  {{_ : Respect _≈_ x}}
  {{_ : Respect _≈_ y}}
  {{_ : Respect _≈_ z}}
  {{_ : Respect _≈_ w}}
  {{_ : Respect _≈_ t}}
  where

  abstract
    pt : L → Val L → SPred
    pt = _↦_

    instance
      pt-resp : ∀ {l} {v} → Respect _≈_ (pt l v)
      pt-resp = ↦-respects-≈

  -- fast
  bench₀ : x ✴ y ✴ z ≐ z ✴ _
  bench₀ = solve-frame CM

  -- slow
  bench₁ : l ↦ a ✴ k ↦ b ✴ m ↦ c ≐ m ↦ c ✴ _
  bench₁ = solve-frame CM

  -- fast
  bench₁′ : pt l a ✴ pt k b ✴ pt m c ≐ pt m c ✴ _
  bench₁′ = solve-frame CM

  -- Relatively fast compared to _↦_
  bench₂ : ⟦ P ⟧ ✴ ⟦ Q ⟧ ✴ ⟦ R ⟧ ≐ ⟦ R ⟧ ✴ _
  bench₂ = solve-frame CM

  -- fast
  bench₃ : x ✴ y ✴ z ✴ w ✴ t ≐ t ✴ _
  bench₃ = solve-frame CM

  -- Don't try at home
  -- bench₄ : p ↦ b ✴ l ↦ a ✴ q ↦ a ✴ k ↦ b ✴ m ↦ c ≐ m ↦ c ✴ _
  -- bench₄ = solve-frame CM

  -- fast
  bench₄′ : pt p b ✴ pt l a ✴ pt q a ✴ pt k b ✴ pt m c ≐ pt m c ✴ _
  bench₄′ = solve-frame CM

  -- slow
  bench₅ : l ↦ a ✴ k ↦ b ≐ k ↦ b ✴ l ↦ a
  bench₅ = solve CM

  -- fast
  bench₅′ : pt l a ✴ pt k b ≐ pt k b ✴ pt l a
  bench₅′ = solve CM
