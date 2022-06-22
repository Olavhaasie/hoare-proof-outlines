{-# OPTIONS --safe --without-K #-}
module Relation.Hoare.Pointsto {S : Set} where

open import Data.Product using (-,_)

open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Hoare.StorePredicate S
open import Relation.Ternary.Core using (Rel₃; Respect; True)


{-
  Interface for the separation logic pointsto (_↦_) predicate.
  When the singleton is implemented for a given store then the pointsto relation
  is defined as an equality on the singleton store. Where:

  - `S` is the type of store.
  - `L` is the type of locations in the store.
  - `V` is the type of values in the store.
-}
record HasPointsto (_≈_ : S → S → Set) (L : Set) (V : Set) : Set where
  field
    overlap {{ ≈-equivalence }} : IsEquivalence _≈_

    -- Singleton store containing exactly one location and value.
    [_↦_] : L → V → S

  open IsEquivalence ≈-equivalence using (refl; trans)


  -------------------------------------------------------------
  -- Store predicates

  -- The pointsto predicate asserts that a store contains exactly one location.
  record Pointsto (l : L) (v : V) (σ : S) : Set where
    constructor single
    pattern
    field
      eq : [ l ↦ v ] ≈ σ

  -- Syntax for the Pointsto relation
  _↦_ : L → V → SPred
  _↦_ = Pointsto

  -- Points to some predicate:
  -- A store is exactly a single location.
  _↦- : L → SPred
  l ↦- = ∃[ v ] (l ↦ v)

  infix 10 _↦_ _↦-


  -------------------------------------------------------------
  -- Properties of the Pointsto relation

  private
    variable
      l : L
      v : V
      H : SPred

  ↦-forget : ∀[ l ↦ v ⇒ l ↦- ]
  ↦-forget x = -, x

  -- The singleton store contains exactly one location and value.
  ↦-singleton : [ l ↦ v ] ∈ l ↦ v
  ↦-singleton = single refl

  instance
    -- The Pointsto relation respects the equivalence relation
    ↦-respects-≈ : Respect _≈_ (l ↦ v)
    Respect.coe ↦-respects-≈ x≈y (single [l↦v]≈x) = single (trans [l↦v]≈x x≈y)

  -- Alternative Pointsto predicates that use a ternary relation.
  -- These are shorthands to commonly used predicates.
  module _ {{rel : Rel₃ S}} where
    open Rel₃ rel using (_∙⟨_⟩_; _✴_)

    -------------------------------------------------------------
    -- Store predicates

    -- Contains predicate:
    -- A store contains a location and value.
    _↪_ : L → V → SPred
    l ↪ v = l ↦ v ✴ True

    -- Contains some value predicate:
    -- A store contains a location.
    _↪- : L → SPred
    l ↪- = ∃[ v ] (l ↪ v)

    -- Not contains some value predicate:
    -- A store does _not_ contain a location
    _↪× : L → SPred
    l ↪× = ∁ (l ↪-)

    infix 10 _↪_ _↪- _↪×


    -------------------------------------------------------------
    -- Properties of the Pointsto relation in ternary relations

    -- A pointsto relation in a product implies that the location
    -- is contained in the product
    containsˡ : ∀[ l ↦ v ✴ H ⇒ l ↪ v ]
    containsˡ (px ∙⟨ sep ⟩ _) = px ∙⟨ sep ⟩ _

    -- When a store contains a location with value
    -- then it also contains the location.
    ↪-forget : ∀[ l ↪ v ⇒ l ↪- ]
    ↪-forget x = -, x
