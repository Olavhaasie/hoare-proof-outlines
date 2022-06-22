{-# OPTIONS --safe --without-K #-}
module Relation.Hoare.Construct.FreshList (V : Set) where

open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (n≮n; n<1+n; <-trans; _<?_)
open import Data.List.Fresh
open import Data.Product using (_,_; _×_; ∃)

open import Relation.Binary.PropositionalEquality using (refl; _≢_; ≢-sym)
open import Relation.Hoare.Bundles
open import Relation.Hoare.Pointsto
open import Relation.Hoare.Structures.Store
open import Relation.Nullary
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax


Entry = ℕ × V

_≉ₑ_ : Entry → Entry → Set
(l₁ , _) ≉ₑ (l₂ , _) = l₁ ≢ l₂


open import Relation.Ternary.Construct.FreshList _≉ₑ_

#-loc : ∀ {l} {v₁ v₂ : V} {σ : FreshList} → (l , v₁) # σ → (l , v₂) # σ
#-loc {σ = []} _ = _
#-loc {σ = cons _ _ _} (eq , #σ) = eq , #-loc #σ

instance
  freshListHasPointsto : HasPointsto {S = FreshList} _≗_ ℕ V
  HasPointsto.≈-equivalence freshListHasPointsto = ≗-isEquivalence
  HasPointsto.[_↦_] freshListHasPointsto l v = (l , v) ∷# []

open HasPointsto freshListHasPointsto

instance
  freshListIsStore : IsStore _≗_ freshSplits [] ℕ V
  IsStore.storeIsMonoid freshListIsStore = freshListIsMonoid
  IsStore.storeHasPointsto freshListIsStore = freshListHasPointsto

  IsStore.∙-insert freshListIsStore =
    let l , l#σ , _ = fresh-loc 0 _ _
    in l , cons (l , _) _ l#σ , consˡ _ l#σ l#σ ∙-idˡ
    where
      -- Very inefficient way of generating a fresh location in a list.
      fresh-loc : ∀ (k : ℕ) (v : V) (σ : FreshList) → ∃ λ l → ((l , v) # σ × k < l)
      fresh-loc k v [] = suc k , _ , n<1+n k
      fresh-loc k v (cons (l , _) σ x) with k <? l
      ... | yes k<l with fresh-loc l v σ
      ... | i , i#σ , l<i = i , ( (λ { refl → n≮n l l<i }) , i#σ) , <-trans k<l l<i
      fresh-loc k v (cons (l , _) σ x) | no k≮l with fresh-loc k v σ
      ... | i , i#σ , k<i = i , ((λ { refl → k≮l k<i }) , i#σ) , k<i

  IsStore.∙-update freshListIsStore sep =
    let #σ = #-loc (freshʳ sep)
    in _ , consˡ _ #σ #σ ∙-idˡ
    where
      freshʳ : ∀ {l} {v} {ys zs} → SplitFresh ((l , v) ∷# []) ys zs → (l , v) # ys
      freshʳ (consˡ _ #ys _ _) = #ys
      freshʳ (consʳ (z≉l , _) _ _ sep) = ≢-sym z≉l , freshʳ sep

  IsStore.single-conflict freshListIsStore = conflict
    where
      open import Relation.Hoare.StorePredicate FreshList

      conflict : ∀ {l} {v₁ v₂} → ∀[ l ↦ v₁ ✴ l ↦ v₂ ⇒ False ]
      conflict (single (cons≗ _) ∙⟨ consˡ _ _ (l≢l , _) (consʳ _ _ _ _) ⟩ single (cons≗ _)) = l≢l refl
      conflict (single (cons≗ _) ∙⟨ consʳ _ _ (l≢l , _) (consˡ _ _ _ _) ⟩ single (cons≗ _)) = l≢l refl


FreshListStore : Store λ _ → V
Store.L FreshListStore = ℕ
Store.Carrier FreshListStore = FreshList
Store._≈_ FreshListStore = _≗_
Store.∅ FreshListStore = []
Store.rel FreshListStore = freshSplits
Store.isStore FreshListStore = freshListIsStore

FreshListCommutativeStore : CommutativeStore λ _ → V
CommutativeStore.store FreshListCommutativeStore = FreshListStore
CommutativeStore.storeIsCommutative FreshListCommutativeStore = freshListIsCommutative

FreshListStoreWithUnique : StoreWithUnique λ _ → V
StoreWithUnique.store FreshListStoreWithUnique = FreshListStore
StoreWithUnique.∅-isUnique FreshListStoreWithUnique = []-unique

FreshListCommutativeStoreWithUnique : CommutativeStoreWithUnique λ _ → V
CommutativeStoreWithUnique.store FreshListCommutativeStoreWithUnique = FreshListStore
CommutativeStoreWithUnique.storeIsCommutative FreshListCommutativeStoreWithUnique = freshListIsCommutative
CommutativeStoreWithUnique.∅-isUnique FreshListCommutativeStoreWithUnique = []-unique
