{-# OPTIONS --safe --without-K #-}
module Relation.Hoare.Structures.Store {S : Set} where

open import Data.Product using (_,_; Σ-syntax)

open import Relation.Binary.PropositionalEquality using (refl; _≢_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Hoare.Pointsto {S}
open import Relation.Hoare.StorePredicate S
open import Relation.Ternary.Core using (Rel₃; coe)
open import Relation.Ternary.Structures using
  ( Emptiness
  ; IsPartialMonoid
  ; IsPartialSemigroup
  ; IsPositiveWithZero
  )


{-
  The interface defines store operations necessary for implementing
  an imperative language. Where:

  - `S` is the type of store.
  - `∅` is an instance of the empty store.
  - `L` is the type of locations in the store.
  - `V` is the type of values in the store.
-}
record IsStore
  (_≈_ : S → S → Set) (rel : Rel₃ S) (∅ : S)
  (L : Set) (V : Set) : Set where

  field
    overlap {{ storeIsMonoid }}    : IsPartialMonoid _≈_ rel ∅
    overlap {{ storeHasPointsto }} : HasPointsto _≈_ L V

  open Rel₃ rel using (_∙_≣_; _∙⟨_⟩_; _✴_)
  open HasPointsto storeHasPointsto
  open IsEquivalence ≈-equivalence using (reflexive; sym)
  open IsPartialMonoid storeIsMonoid using (emptiness; isSemigroup; ∙-idˡ)
  open IsPartialSemigroup isSemigroup using (∙-assocₗ)
  open Emptiness emptiness using (Emp)

  instance _ = rel

  field
    -- Two separate parts of the store should be disjoint.  In other
    -- words, if two separate parts contain the same location then a
    -- contradiction arises.  This lemma might not belong here.
    single-conflict : ∀ {l} {v₁ v₂}
      → ∀[ l ↦ v₁ ✴ l ↦ v₂ ⇒ False ]

  -------------------------------------------------------------
  -- Store operations

  field
    ∙-insert : ∀ {v} {σ}
      → Σ[ l ∈ L ] Σ[ σ′ ∈ S ] [ l ↦ v ] ∙ σ ≣ σ′

    ∙-update : ∀ {l} {v v′} {σ σ″}
      → [ l ↦ v ] ∙ σ″ ≣ σ
      → Σ[ σ′ ∈ S ] [ l ↦ v′ ] ∙ σ″ ≣ σ′

  ✴-insert : ∀ {v} {H} → ∀[ H ⤇ ∃[ l ] (l ↦ v ✴ H) ]
  ✴-insert σ∈H =
    let l , σ′ , sep = ∙-insert
    in σ′ , l , ↦-singleton ∙⟨ sep ⟩ σ∈H

  ✴-update : ∀ {l} {v v′} {H} → ∀[ l ↦ v ✴ H ⤇ l ↦ v′ ✴ H ]
  ✴-update (single eq ∙⟨ sep ⟩ qx) =
    let σ′ , sep = ∙-update (coe (sym eq) sep)
    in σ′ , ↦-singleton ∙⟨ sep ⟩ qx

  -------------------------------------------------------------
  -- Store properties

  private
    variable
      l l₁ l₂ : L
      v v₁ v₂ : V
      σ σₗ σᵣ : S

  -- Two separated pointsto predicates implies they are not equal.
  single-disjoint : σ ∈ l₁ ↦ v₁ ✴ l₂ ↦ v₂ → l₁ ≢ l₂
  single-disjoint x refl = single-conflict x

  -- A store containing a location can be separated by the location and the rest.
  ✴-disjoint : ∀[ l ↪ v ⇒ l ↦ v ✴ l ↪× ]
  ✴-disjoint (single eq ∙⟨ sep ⟩ _) = single eq ∙⟨ sep ⟩ ∙-disjoint (coe (sym eq) sep)
    where
      ∙-disjoint : [ l ↦ v ] ∙ σᵣ ≣ σ → σᵣ ∈ l ↪×
      ∙-disjoint x (_ , px Rel₃.∙⟨ sep ⟩ qx) with ∙-assocₗ x sep
      ... | fst , fst₁ , snd = single-conflict (↦-singleton ∙⟨ fst₁ ⟩ px)

  -- The pointsto predicate does not contain the empty store.
  ∅∉single : ∅ ∉ l ↦ v
  ∅∉single x = single-conflict (x ∙⟨ ∙-idˡ ⟩ x)

  singleton∉Emp : [ l ↦ v ] ∉ Emp
  singleton∉Emp x = ∅∉single (single (sym (reflexive x)))

  ↦-∧-emp : ∀[ l ↦ v ∧ Emp ⇒ False ]
  ↦-∧-emp (x , refl) = ∅∉single x

  module _ {s} {{isPosWithZero : IsPositiveWithZero s _≈_ rel ∅}} where
    open IsPositiveWithZero isPosWithZero using (ε-split)

    -- The pointsto predicate contained in a separation does not
    -- contain the empty store.
    ∅∉contains : ∅ ∉ l ↪ v
    ∅∉contains (x ∙⟨ sep ⟩ _) with refl ← ε-split sep = ∅∉single x

    -- The empty predicate implies that no location exists.
    ∅⇒¬contains : ∀[ Emp ⇒ l ↪× ]
    ∅⇒¬contains refl (_ , x) = ∅∉contains x


  -- When the left store of a separation is asserted by a pointsto
  -- then the store may be replaced by a singleton.
  respects-singletonˡ :
      σₗ ∈ l ↦ v
    → σₗ ∙ σᵣ ≣ σ
      ------------------
    → [ l ↦ v ] ∙ σᵣ ≣ σ
  respects-singletonˡ (single eq) = coe (sym eq)

  ↦-extend : ∀[ l ↦ v ⇒ l ↪ v ]
  ↦-extend = ✴-extend
