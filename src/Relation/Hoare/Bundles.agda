{-# OPTIONS --safe --without-K #-}
module Relation.Hoare.Bundles where

open import Level using (0ℓ)

open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Hoare.Pointsto
open import Relation.Hoare.Structures.Store
open import Relation.Ternary.Core using (Rel₃; Respect; IsUnique)
open import Relation.Ternary.Structures using
  ( Emptiness
  ; IsCommutative
  ; IsPartialMonoid
  ; IsPartialSemigroup
  )
open import Relation.Ternary.Tactic.Bundles


record Store (V : Set → Set) : Set₁ where
  field
    L         : Set
    Carrier   : Set
    _≈_       : Carrier → Carrier → Set
    ∅         : Carrier
    {{ rel }} : Rel₃ Carrier

    isStore   : IsStore _≈_ rel ∅ L (V L)

  open Rel₃ rel public
  module ST = IsStore isStore
  module PT = HasPointsto ST.storeHasPointsto
  open IsPartialMonoid ST.storeIsMonoid public
  open Emptiness emptiness public
  open IsPartialSemigroup isSemigroup public
  open IsEquivalence (HasPointsto.≈-equivalence ST.storeHasPointsto) renaming
    ( refl to ≈-refl
    ; sym to ≈-sym
    ; trans to ≈-trans) public

  open import Relation.Hoare.StorePredicate Carrier public

  abstract
    _↦_ : L → V L → SPred
    _↦_ = PT._↦_

    _↪_ : L → V L → SPred
    _↪_ = PT._↪_

    instance
      ↦-respects-≈ : ∀ {l} {v} → Respect _≈_ (l ↦ v)
      ↦-respects-≈ = PT.↦-respects-≈

      ↪-respects-≈ : ∀ {l} {v} → Respect _≈_ (l ↪ v)
      ↪-respects-≈ = ✴-respect-≈

    containsˡ : ∀ {l : L} {v : V L} {H : SPred} → ∀[ l ↦ v ✴ H ⇒ l ↪ v ]
    containsˡ = PT.containsˡ

    ✴-insert : ∀ {v} {H} → ∀[ H ⤇ ∃[ l ] (l ↦ v ✴ H) ]
    ✴-insert = ST.✴-insert

    ✴-update : ∀ {l} {v v′} {H} → ∀[ l ↦ v ✴ H ⤇ l ↦ v′ ✴ H ]
    ✴-update = ST.✴-update

record CommutativeStore (V : Set → Set) : Set₁ where
  field
    store : Store V

  open Store store public

  field
    {{ storeIsCommutative }} : IsCommutative rel

  open IsCommutative storeIsCommutative public


record StoreWithUnique (V : Set → Set) : Set₁ where
  field
    store : Store V

  open Store store public

  field
    {{ ∅-isUnique }} : IsUnique _≈_ ∅

  M : MonoidWithUnique 0ℓ 0ℓ
  MonoidWithUnique.Carrier M = Carrier
  MonoidWithUnique._≈_ M = _≈_
  MonoidWithUnique.rel M = rel
  MonoidWithUnique.unit M = ∅
  MonoidWithUnique.isMonoid M = IsStore.storeIsMonoid isStore
  MonoidWithUnique.isUnique M = ∅-isUnique


record CommutativeStoreWithUnique (V : Set → Set) : Set₁ where
  field
    store : Store V

  open Store store public

  field
    {{ storeIsCommutative }} : IsCommutative rel
    {{ ∅-isUnique }}         : IsUnique _≈_ ∅

  open IsCommutative storeIsCommutative public

  M : MonoidWithUnique 0ℓ 0ℓ
  MonoidWithUnique.Carrier M = Carrier
  MonoidWithUnique._≈_ M = _≈_
  MonoidWithUnique.rel M = rel
  MonoidWithUnique.unit M = ∅
  MonoidWithUnique.isMonoid M = IsStore.storeIsMonoid isStore
  MonoidWithUnique.isUnique M = ∅-isUnique

  CM : CommutativeMonoidWithUnique 0ℓ 0ℓ
  CommutativeMonoidWithUnique.Carrier CM = Carrier
  CommutativeMonoidWithUnique._≈_ CM = _≈_
  CommutativeMonoidWithUnique.rel CM = rel
  CommutativeMonoidWithUnique.unit CM = ∅
  CommutativeMonoidWithUnique.isMonoid CM = IsStore.storeIsMonoid isStore
  CommutativeMonoidWithUnique.isCommutative CM = storeIsCommutative
  CommutativeMonoidWithUnique.isUnique CM = ∅-isUnique
