{-# OPTIONS --safe --without-K #-}
module Relation.Hoare.Construct.DomainMap (V : Set) where

open import Axiom.Extensionality.Propositional using (Extensionality)

open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.Product using (_,_)

open import Level using (0ℓ)

open import Relation.Binary.PropositionalEquality using (cong; sym; trans; refl; _≡_)
open import Relation.Hoare.Bundles
open import Relation.Hoare.Pointsto
open import Relation.Hoare.Structures.Store
open import Relation.Nullary
open import Relation.Ternary.Core
open import Relation.Ternary.Respect.Propositional
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax hiding (≤-refl; ≤-trans)


-- Instantiate domain map with disjoint PCV values
open import Relation.Ternary.Construct.Empty V
open import Relation.Ternary.Construct.DomainMap empty-rel public

instance
  dmHasPointsto : HasPointsto _≗_ ℕ V
  HasPointsto.[_↦_] dmHasPointsto l v = ∅ [ l ≔ v ]

open HasPointsto dmHasPointsto

instance
  dmIsStore : IsStore _≗_ domains ∅ ℕ V

  IsStore.storeHasPointsto dmIsStore = dmHasPointsto

  IsStore.∙-insert dmIsStore {v} {σ} =
    l' σ , (σ [≔ v ]) , insert-union
    where
      lub-suc : ∀ {n} → suc n ⊔ n ≡ suc n
      lub-suc {zero} = refl
      lub-suc {suc _} = cong suc lub-suc

      insert-union : [ (l' σ) ↦ v ] ∙ σ ≣ (σ [≔ v ])
      ulookup insert-union k with l' σ ≟ k | lookup σ k in eq
      ... | yes refl | just _  with () ← trans (sym (fresh σ)) eq
      ... | yes refl | nothing            = left
      ... | no  _    | just _  rewrite eq = right
      ... | no  _    | nothing rewrite eq = nothing
      lub insert-union = lub-suc

  IsStore.∙-update dmIsStore {l = l} {v = v} {v′ = v′} {σ = σ} {σ″ = σ″} u =
    (σ [ l ≔ v′ ]) , update-union u
    where
      update-union :
          [ l ↦ v ] ∙ σ″ ≣ σ
        → [ l ↦ v′  ] ∙ σ″ ≣ (σ [ l ≔ v′ ])
      ulookup (update-union u) k with l <? l' σ
      ... | yes l<l' with l ≟ k | lookup σ″ k | lookup σ k in eq | ulookup u k
      ... | yes refl | just  _ | just _ | split ()
      ... | yes refl | nothing | _      | s = left
      ... | no  l≢k  | _       | _      | s rewrite eq = s
      ulookup (update-union u) k | no l≮l' with l ≟ k | lookup σ″ k | lookup σ k in eq | ulookup u k
      ... | yes refl | just _  | just _ | split ()
      ... | yes refl | nothing | _      | s = left
      ... | no l≢k   | _       | _      | s rewrite eq = s
      lub (update-union u) with l <? l' σ
      ... | yes _ = lub u
      ... | no l≮l' with lookup σ l in eq
      ...              | just x  = ⊥-elim (l≮l' (order σ l eq))
      ...              | nothing with l ≟ l | ulookup u l
      ...                           | yes l≡l | ul rewrite eq with () ← left-inv ul
      ...                           | no l≢l  | _  = ⊥-elim (l≢l refl)

  IsStore.single-conflict dmIsStore {l = l} {x = x} (_∙⟨_⟩_ {Φₗ} {Φᵣ} (single ≗⟨ _ , px ⟩) u (single ≗⟨ _ , qx ⟩)) with ulookup u l | lookup Φₗ l in eqₗ | lookup Φᵣ l in eqᵣ | lookup x l in eq
  ... | ul | just _  | just _  | just _  rewrite eqₗ | eqᵣ | eq with split () ← ul
  ... | ul | just _  | just _  | nothing rewrite eqₗ | eqᵣ | eq with () ← ul
  IsStore.single-conflict dmIsStore {l = l} ((single ≗⟨ _ , px ⟩) ∙⟨ _ ⟩ _) | _ | nothing | _       | _ with px l
  ... | r rewrite eqₗ with l ≟ l
  ... | yes l≡l with () ← r
  ... | no l≢l = l≢l refl
  IsStore.single-conflict dmIsStore {l = l} (_ ∙⟨ u ⟩ (single ≗⟨ _ , qx ⟩)) | _ | just _  | nothing | _ with qx l
  ... | r rewrite eqᵣ with l ≟ l
  ... | yes l≡l with () ← r
  ... | no l≢l = l≢l refl

DomainMapStore : Store λ _ → V
Store.L DomainMapStore = ℕ
Store.Carrier DomainMapStore = DomainMap
Store._≈_ DomainMapStore = _≗_
Store.∅ DomainMapStore = ∅
Store.rel DomainMapStore = domains
Store.isStore DomainMapStore = dmIsStore

DomainMapCommStore : CommutativeStore λ _ → V
CommutativeStore.store DomainMapCommStore = DomainMapStore
CommutativeStore.storeIsCommutative DomainMapCommStore = dmIsCommutative

module _ (ext : Extensionality 0ℓ 0ℓ) where
  open EmptyDomainMapIsUnique ext

  DomainMapStoreWithUnique : StoreWithUnique λ _ → V
  StoreWithUnique.store DomainMapStoreWithUnique = DomainMapStore
  StoreWithUnique.∅-isUnique DomainMapStoreWithUnique = ∅-unique

  DomainMapCommStoreWithUnique : CommutativeStoreWithUnique λ _ → V
  CommutativeStoreWithUnique.store DomainMapCommStoreWithUnique = DomainMapStore
  CommutativeStoreWithUnique.storeIsCommutative DomainMapCommStoreWithUnique = dmIsCommutative
  CommutativeStoreWithUnique.∅-isUnique DomainMapCommStoreWithUnique = ∅-unique
