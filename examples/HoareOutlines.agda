{-# OPTIONS --safe --without-K #-}
open import Relation.Hoare.Pointsto
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

{-
  This module shows some (useless) examples of Hoare outlines from the
  `Relation.Hoare` module. The examples are abstract, which means they do
  not use concrete types. Because of this the examples each have an assumption
  to construct some simple Hoare triple to be used in the rule. When the logic
  is instantiated with a language, then you could use your own axioms for
  costructing primitive triples in your language.
-}
module HoareOutlines
  {T : Set} {L : Set} {V : Set} {E : Set} {S : Set}
  (_≈_ : S → S → Set) (∅ : S)
  (⟨_,_,_⟩⇊⟨_,_⟩ : T → E → S → V → S → Set)
  {{rel : Rel₃ S}}
  {{isPartialMonoid : IsPartialMonoid _≈_ rel ∅}}
  {{hasPointsto : HasPointsto _≈_ L V}}
  where

open import Level using (0ℓ)

open import Relation.Hoare.StorePredicate S
open import Relation.Hoare.PostCondition S V

open HasPointsto hasPointsto
open import Relation.Hoare _≈_ ∅ ⟨_,_,_⟩⇊⟨_,_⟩


module _
  {t : T} {l k m : L} {v v' u w : V}
  {P : Set}
  {H : SPred} {{_ : Respect _≈_ H}}
  {Q : Post} {{_ : ∀ {v} → Respect _≈_ (Q v)}}
  where


  -- Example showing pre consequence.
  example₀ :
      [ H ] t [ Q ]
    → [ Emp ✴ H ] t [ Q ]
  example₀ x =
    [ Emp ✴ H ]begin
    [ H ]by⟨ ✴-id⁻ˡ ⟩
    x
    [ Q ]∎


  -- Example showing the frame rule.
  example₁ :
      [ l ↦ v ] t [ + Emp ]
    → [ l ↦ v ✴ H ] t [ + H ]
  example₁ x =
    [ l ↦ v ✴ H ]begin
    [ l ↦ v ]frame
    x
    [ + Emp ]restore
    [ + Emp ✴ H ]by⟨⟩
    [ + H ]by⟨ ✴-id⁻ˡ ⟩
    [ + H ]∎


  -- Example using the pure rule and post consequence.
  example₂ :
      [ H ] t [ (λ v → ⟦ P ⟧ ✴ Q v) ]
    → [ ⟦ P ⟧ ✴ ⟦ P ⟧ ✴ H ] t [ Q ]
  example₂ x =
    [ ⟦ P ⟧ ✴ ⟦ P ⟧ ✴ H ]begin
    [ ⟦ P ⟧ ✴ H ]pure λ p₁ →
    [ H ]pure λ p₂ →
    x
    [ (λ v → ⟦ P ⟧ ✴ Q v) ]by⟨⟩
    [ Q ]by⟨ ✴-pure⁻ˡ ⟩
    [ Q ]∎


  module _ {{_ : IsCommutative rel}} where

    -- Example showing the combined consequence-frame rule.
    example₃ :
        [ l ↦ v ] t [ (λ _ → l ↦ v') ]
      → [ k ↦ w ✴ l ↦ v ] t [ (λ _ → k ↦ w ✴ l ↦ v') ]
    example₃ x =
      [ k ↦ w ✴ l ↦ v ]begin
      [ l ↦ v ]frameby⟨ ✴-swap ⟩
      x
      [ + k ↦ w ✴ l ↦ v' ]restoreby⟨ ✴-swap ⟩


  -- Example using exists rule
  example₄ :
      (∀ (l : L) (v : V) → [ l ↦ v ] t [ + Emp ])
    → [ ∃[ l ] ∃[ v ] (l ↦ v) ] t [ + Emp ]
  example₄ x =
    [ ∃[ l ] ∃[ v ] (l ↦ v) ]begin
    [ (λ l → ∃[ v ] (l ↦ v)) ]exists⟨ l ⟩
    [ (λ v → l ↦ v) ]exists⟨ v ⟩
    x l v
    [ + Emp ]∎


  module _ {{_ : IsUnique _≈_ ∅}} where

    open import Relation.Ternary.Tactic.Bundles
    open import Relation.Ternary.Tactic.MonoidSolver

    M : MonoidWithUnique 0ℓ 0ℓ
    MonoidWithUnique.Carrier M = S
    MonoidWithUnique._≈_ M = _≈_
    MonoidWithUnique.rel M = rel
    MonoidWithUnique.unit M = ∅
    MonoidWithUnique.isMonoid M = isPartialMonoid

    open ConsequenceSolver MonoidSolver (quoteTerm M)

    -- Example showing use of monoid solver for consequences
    example₅ :
        [ l ↦ v ✴ k ↦ u ✴ m ↦ w ] t [ (λ _ → l ↦ v ✴ m ↦ w) ]
      → [ Emp ✴ (l ↦ v ✴ k ↦ u) ✴ (Emp ✴ m ↦ w) ] t [ (λ _ → Emp ✴ l ↦ v ✴ m ↦ w) ]
    example₅ x =
      [ Emp ✴ (l ↦ v ✴ k ↦ u) ✴ (Emp ✴ m ↦ w) ]begin
      [ l ↦ v ✴ k ↦ u ✴ m ↦ w ]byauto
      x
      [ + l ↦ v ✴ m ↦ w ]by⟨⟩
      [ + Emp ✴ l ↦ v ✴ m ↦ w ]byauto

    -- Example showing use of monoid solver for consequence frame
    example₆ :
        [ l ↦ v ] t [ + Emp ]
      → [ Emp ✴ (Emp ✴ l ↦ v ✴ k ↦ u ✴ Emp) ✴ Emp ] t [ + Emp ✴ k ↦ u ]
    example₆ x =
      [ Emp ✴ (Emp ✴ l ↦ v ✴ k ↦ u ✴ Emp) ✴ Emp ]begin
      [ l ↦ v ]auto
      x
      [ + Emp ]by⟨⟩
      [ + Emp ✴ k ↦ u ]autorestore


  module _ {{isCommutative : IsCommutative rel}} {{_ : IsUnique _≈_ ∅}} where

    open import Relation.Ternary.Tactic.Bundles
    open import Relation.Ternary.Tactic.CommutativeMonoidSolver

    CM : CommutativeMonoidWithUnique 0ℓ 0ℓ
    CommutativeMonoidWithUnique.Carrier CM = S
    CommutativeMonoidWithUnique._≈_ CM = _≈_
    CommutativeMonoidWithUnique.rel CM = rel
    CommutativeMonoidWithUnique.unit CM = ∅
    CommutativeMonoidWithUnique.isMonoid CM = isPartialMonoid
    CommutativeMonoidWithUnique.isCommutative CM = isCommutative

    open ConsequenceSolver CommutativeMonoidSolver (quoteTerm CM)

    -- Example showing use of commutative monoid solver for consequences
    example₇ :
        [ m ↦ w ✴ k ↦ u ✴ l ↦ v ] t [ (λ _ → k ↦ u ✴ l ↦ v) ]
      → [ Emp ✴ (l ↦ v ✴ k ↦ u) ✴ (Emp ✴ m ↦ w) ] t [ (λ _ → Emp ✴ l ↦ v ✴ k ↦ u) ]
    example₇ x =
      [ Emp ✴ (l ↦ v ✴ k ↦ u) ✴ (Emp ✴ m ↦ w) ]begin
      [ m ↦ w ✴ k ↦ u ✴ l ↦ v ]byauto
      x
      [ + k ↦ u ✴ l ↦ v ]by⟨⟩
      [ + Emp ✴ l ↦ v ✴ k ↦ u ]byauto

    -- Example showing use of commutative monoid solver for frame consequences
    example₈ :
        [ m ↦ w ] t [ (λ _ → Emp) ]
      → [ l ↦ v ✴ k ↦ u ✴ m ↦ w ✴ Emp ] t [ (λ _ → l ↦ v ✴ k ↦ u ✴ Emp) ]
    example₈ x =
      [ l ↦ v ✴ k ↦ u ✴ m ↦ w ✴ Emp ]begin
      [ m ↦ w ]auto
      x
      [ + Emp ]by⟨⟩
      [ + l ↦ v ✴ k ↦ u ✴ Emp ]autorestore
