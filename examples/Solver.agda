{-# OPTIONS --safe --without-K #-}
open import Level

open import Relation.Ternary.Tactic.Bundles

module Solver where

open import Relation.Ternary.Core
open import Relation.Unary
open import Relation.Unary.Properties


module MonoidSolver (M : MonoidWithUnique 0ℓ 0ℓ) where
  open MonoidWithUnique M

  open import Relation.Ternary.Tactic.MonoidSolver


  module _ {x y z : CPred}
    {{_ : Respect _≈_ x}}
    {{_ : Respect _≈_ y}}
    {{_ : Respect _≈_ z}}
    where

    example₀ : x ≐ x
    example₀ = solve M

    example₁ : x ✴ Emp ≐ Emp ✴ x
    example₁ = solve M

    example₂ : x ✴ y ≐ x ✴ y
    example₂ = solve M

    example₃ : (x ✴ y) ✴ z ≐ x ✴ (y ✴ z)
    example₃ = solve M

    example₄ : x ✴ (y ✴ Emp) ✴ z ≐ Emp ✴ x ✴ y ✴ (Emp ✴ z)
    example₄ = solve M

    example₅ : ∀[ (Emp ✴ x) ✴ (y ✴ z) ⇒ ((x ✴ y) ✴ z) ✴ Emp ]
    example₅ = solve-⊆ M

    example₆ : ∀[ Emp ✴ (x ✴ y) ✴ (Emp ✴ z) ⇒ x ✴ y ✴ z ]
    example₆ = solve-⊆ M

    example₇ : x ⊆ x
    example₇ = solve-⊆ M

    example₈ : x ✴ Emp ✴ y ≐ x ✴ _
    example₈ = solve-frame M

    example₉ : x ✴ (Emp ✴ y) ✴ (z ✴ Emp) ✴ Emp ≐ (Emp ✴ x) ✴ _
    example₉ = solve-frame M


  module _ {A : Set} {x y : A → CPred}
    {{_ : ∀ {a : A} → Respect _≈_ (x a)}}
    {{_ : ∀ {a : A} → Respect _≈_ (y a)}}
    where

    ∀-example₀ : ∀ (a : A) → x a ≐ x a
    ∀-example₀ = solve-∀ M

    ∀-example₁ : ∀ (a : A) → (Emp ✴ x a) ✴ (Emp ✴ y a) ≐ x a ✴ y a
    ∀-example₁ = solve-∀ M


module CommutativeMonoidSolver (M : CommutativeMonoidWithUnique 0ℓ 0ℓ) where
  open CommutativeMonoidWithUnique M

  open import Relation.Ternary.Tactic.CommutativeMonoidSolver


  module _ {x y z : CPred}
    {{_ : Respect _≈_ x}}
    {{_ : Respect _≈_ y}}
    {{_ : Respect _≈_ z}}
    where

    example₀ : y ✴ Emp ✴ x ✴ (Emp ✴ z ✴ Emp) ≐ z ✴ y ✴ x
    example₀ = solve M

    -- The following will produce an error, since the two expressions
    -- do not have the same amount of atoms.
    -- _ : y ✴ z ✴ x ≐ z ✴ x
    -- _ = solve M

    -- The following will produce an error, since the two expressions
    -- do not have the same atoms.
    -- _ : y ✴ z ≐ z ✴ x
    -- _ = solve M

    example₁ : z ✴ Emp ✴ Emp ✴ y ≐ (y ✴ z) ✴ _
    example₁ = solve-frame M

    example₂ : z ✴ (Emp ✴ x) ✴ Emp ✴ y ≐ (y ✴ z) ✴ _
    example₂ = solve-frame M

    example₃ : x ≐ x ✴ _
    example₃ = solve-frame M

    example₄ : x ✴ y ✴ z ⊆ z ✴ y ✴ x
    example₄ = solve-⊆ M


  module _ {A : Set} {x y : A → CPred}
    {{_ : ∀ {a : A} → Respect _≈_ (x a)}}
    {{_ : ∀ {a : A} → Respect _≈_ (y a)}}
    where

    ∀-example₀ : ∀ (a : A) → y a ✴ Emp ✴ x a ≐ x a ✴ y a ✴ Emp
    ∀-example₀ = solve-∀ M
