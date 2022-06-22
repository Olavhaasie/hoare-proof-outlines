{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core

module Relation.Ternary.Construct.DomainMap {v} {V : Set v} (rel : Rel₃ V) where

open import Axiom.Extensionality.Propositional

open import Data.Empty
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (proj₁; proj₂; _×_; _,_; ∃)
open import Data.Sum using (inj₁; inj₂)

open import Function using (case_of_)

open import Level using (0ℓ)

open import Relation.Binary.PropositionalEquality using (cong; sym; trans; refl; _≡_)
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder)
open import Relation.Nullary
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax hiding (_≤_; ≤-refl; ≤-reflexive; ≤-trans)

-- Instantiate Ternary relation
open import Relation.Ternary.Construct.Add.Unit rel public


record DomainMap : Set v where
  field
    {l'}   : ℕ
    lookup : (k : ℕ) → Maybe V
    fresh  : lookup l' ≡ nothing
    order  : ∀ k {v} → lookup k ≡ just v → k < l'

open DomainMap public

∅ : DomainMap
l'     ∅   = 0
lookup ∅ _ = nothing
fresh  ∅   = refl
order  ∅ _ ()


-------------------------------------------------------------
-- DomainMap operations

private
  suc-≮ : ∀ {n} → suc n ≮ n
  suc-≮ (s≤s x) = suc-≮ x

-- Updating a map with a given location and value
-- with a decidable assumption whether the new location is fresh or not.
update-< : (m : DomainMap) → (l : ℕ) → V → Dec (l < l' m) → DomainMap
-- If the location to be updated is smaller than the fresh location
l' (update-< m l v (yes l<l') ) = l' m
lookup (update-< m l v (yes l<l')) k with l ≟ k
... | yes _ = just v
... | no  _ = lookup m k
fresh (update-< m l v (yes l<l')) with l ≟ l' m
... | yes refl = ⊥-elim (<-irrefl refl l<l')
... | no  _    = fresh m
order (update-< m l v (yes l<l')) k x with l ≟ k
... | yes refl = l<l'
... | no  _    = order m k x
-- If the location to be updated is larger than the fresh location
l' (update-< m l v (no l≮l')) = suc l
lookup (update-< m l v (no l≮l')) k with l ≟ k
... | yes _ = just v
... | no  _ = lookup m k
fresh (update-< m l v (no l≮l')) with l ≟ suc l
... | no _ with lookup m (suc l) in eq
... | just x  = ⊥-elim (suc-≮ (≤-trans (order m (suc l) eq) (≮⇒≥ l≮l')))
... | nothing = refl
order (update-< m l v (no l≮l')) k x with l ≟ k
... | yes refl = s≤s ≤-refl
... | no  _    = ≤-step (≤-trans (order m k x) (≮⇒≥ l≮l'))


-- Updating a map at a given location
_[_≔_] : DomainMap → ℕ → V → DomainMap
m [ l ≔ v ] = update-< m l v (l <? l' m)

-- Inserting a value at the fresh location
_[≔_] : DomainMap → V → DomainMap
m [≔ v ] = update-< m (l' m) v (no (<-irrefl refl))


-------------------------------------------------------------
-- DomainMap equivalence

record _≗_ (m₁ m₂ : DomainMap) : Set v where
  constructor ≗⟨_,_⟩
  field
    ≡-bound  : l' m₁ ≡ l' m₂
    ≡-lookup : ∀ k → lookup m₁ k ≡ lookup m₂ k

instance
  ≗-isEquivalence : IsEquivalence _≗_
  IsEquivalence.refl ≗-isEquivalence = ≗⟨ refl , (λ k → refl) ⟩
  IsEquivalence.sym ≗-isEquivalence ≗⟨ refl , eq ⟩ = ≗⟨ refl , (λ k → sym (eq k)) ⟩
  IsEquivalence.trans ≗-isEquivalence ≗⟨ refl , eq₁ ⟩ ≗⟨ refl , eq₂ ⟩ = ≗⟨ refl , (λ k → trans (eq₁ k) (eq₂ k)) ⟩


module EmptyDomainMapIsUnique (ext : Extensionality v v) where

  ext0v : Extensionality 0ℓ v
  ext0v = lower-extensionality v 0ℓ ext

  extv0 : Extensionality v 0ℓ
  extv0 = lower-extensionality 0ℓ v ext

  ext-implicit : ExtensionalityImplicit v v
  ext-implicit = implicit-extensionality ext

  instance
    -- Equality on an empty map implies a propositional equality assuming extensionality.
    ∅-unique : IsUnique _≗_ ∅
    IsUnique.unique ∅-unique ≗⟨ refl , eq ⟩ with ext0v eq
    IsUnique.unique ∅-unique {record { fresh = refl ; order = order }} ≗⟨ refl , _ ⟩ | refl rewrite
      ext0v {f = order} {g = DomainMap.order ∅} λ k →
        ext-implicit {f = order k} {g = DomainMap.order ∅ k} λ {_} →
          extv0 λ x → ⊥-elim (case order k x of λ ()) = refl


-------------------------------------------------------------
-- Preorder on DomainMaps

_≤ₘ_ : DomainMap → DomainMap → Set _
m₁ ≤ₘ m₂ = l' m₁ ≤ l' m₂

≤ₘ-isPreorder : IsPreorder _≗_ _≤ₘ_
IsPreorder.isEquivalence ≤ₘ-isPreorder = ≗-isEquivalence
IsPreorder.reflexive ≤ₘ-isPreorder ≗⟨ eq , _ ⟩ = ≤-reflexive eq
IsPreorder.trans ≤ₘ-isPreorder = ≤-trans


-------------------------------------------------------------
-- DomainMap Union

record DomainUnion (l r m : DomainMap) : Set v where
  field
    ulookup : ∀ k → (lookup l k) ∙ (lookup r k) ≣ (lookup m k)
    lub     : l' l ⊔ l' r ≡ l' m

open DomainUnion public

instance
  domains : Rel₃ DomainMap
  Rel₃._∙_≣_ domains = DomainUnion

  dmEmptiness : Emptiness ∅
  dmEmptiness = record {}


⊔-assocᵣ : ∀ {a b c ab abc}
  → a  ⊔ b ≡ ab
  → ab ⊔ c ≡ abc
  → a  ⊔ (b ⊔ c) ≡ abc
⊔-assocᵣ {a} x y rewrite sym x = trans (sym (⊔-assoc a _ _)) y


-------------------------------------------------------------
-- Ternary relations structures

module _ {{_ : IsCommutative rel}} where

  instance
    dmIsCommutative : IsCommutative domains
    ulookup (IsCommutative.∙-comm dmIsCommutative u) k = ∙-comm (ulookup u k)
    lub (IsCommutative.∙-comm dmIsCommutative {b = b} u) = trans (⊔-comm (l' b) _) (lub u)


module _
  {{_ : IsCommutative rel}}
  {{_ : IsPartialSemigroup _≡_ rel}}
  where

  instance
    -- Implement left semigroup and get the complete semigroup for free with commutativity
    dmIsSemigroupˡ : IsPartialSemigroupˡ _≗_ domains
    Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ dmIsSemigroupˡ) ≗⟨ refl , eq ⟩ u =
      record { DomainUnion u ; ulookup = λ k → coe {{∙-respects-≈}} (eq k) (ulookup u k) }
    Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ dmIsSemigroupˡ) ≗⟨ refl , eq ⟩ u =
      record { DomainUnion u ; ulookup = λ k → coe {{∙-respects-≈ˡ}} (eq k) (ulookup u k) }
    IsPartialSemigroupˡ.assocᵣ dmIsSemigroupˡ {a = a} {b = b} {c = c} {abc = abc} u₁ u₂ =
      let assoc = λ k → ∙-assocᵣ (ulookup u₁ k) (ulookup u₂ k)
      in
        assoc-map assoc
      , record {
          ulookup = λ k → let _ , sep₂ , _ = assoc k in sep₂
        ; lub = ⊔-assocᵣ {a = l' a} (lub u₁) (lub u₂)
        }
      , record {
          ulookup = λ k → let _ , _ , sep₃ = assoc k in sep₃
        ; lub = refl
        }
      where
        assoc-map :
            (∀ k → ∃ λ bc → lookup a k ∙ bc ≣ lookup abc k × lookup b k ∙ lookup c k ≣ bc)
          → DomainMap
        l' (assoc-map assoc) = l' b ⊔ l' c
        lookup (assoc-map assoc) k = proj₁ (assoc k)
        fresh (assoc-map assoc) with assoc (l' b ⊔ l' c)
        ... | nothing , _ = refl
        ... | just _  , _ , _ with
              ⊔-sel (l' b) (l' c) | lookup b (l' b ⊔ l' c) in eq₁ | lookup c (l' b ⊔ l' c) in eq₂
        ... | inj₁ lb | just _  | _       rewrite lb = ⊥-elim (<-irrefl refl (order b _ eq₁))
        ... | inj₁ lb | nothing | just _  rewrite lb = ⊥-elim ((≤⇒≯ (m⊔n≡m⇒n≤m lb)) (order c _ eq₂))
        ... | inj₂ lc | _       | just _  rewrite lc = ⊥-elim (<-irrefl refl (order c _ eq₂))
        ... | inj₂ lc | just _  | nothing rewrite lc = ⊥-elim ((≤⇒≯ (m⊔n≡n⇒m≤n lc)) (order b _ eq₁))
        order (assoc-map assoc) k x with assoc k | lookup b k in eq₁ | lookup c k in eq₂
        ... | just _ , _ , _  | just _  | _       = m≤n⇒m≤n⊔o _ (order b k eq₁)
        ... | just _ , _ , _  | nothing | just _  = m≤n⇒m≤o⊔n _ (order c k eq₂)
        ... | just _ , _ , bc | nothing | nothing rewrite eq₁ rewrite eq₂ with () ← bc

    dmIsSemigroup = IsPartialSemigroupˡ.semigroupˡ dmIsSemigroupˡ

  instance
    -- Implement left monoid and get the complete monoid for free with commutativity
    dmIsMonoidˡ : IsPartialMonoidˡ _≗_ domains ∅
    ulookup (IsPartialMonoidˡ.identityˡ dmIsMonoidˡ) k = ∙-idˡ
    lub (IsPartialMonoidˡ.identityˡ dmIsMonoidˡ) = refl
    _≗_.≡-bound (IsPartialMonoidˡ.identity⁻ˡ dmIsMonoidˡ u) = lub u
    _≗_.≡-lookup (IsPartialMonoidˡ.identity⁻ˡ dmIsMonoidˡ u) k = ∙-id⁻ˡ (ulookup u k)

    dmIsMonoid = IsPartialMonoidˡ.partialMonoidˡ dmIsMonoidˡ


instance
  dmIsPositive : IsPositive _ _≗_ domains
  IsPositive._≤ₐ_ dmIsPositive = _≤ₘ_
  IsPositive.orderₐ dmIsPositive = ≤ₘ-isPreorder
  IsPositive.positiveˡ dmIsPositive {Φ₁} {Φ₂} u with ⊔-sel (l' Φ₁) (l' Φ₂)
  ... | inj₁ x = ≤-reflexive (trans (sym x) (lub u))
  ... | inj₂ y = ≤-trans (m⊔n≡n⇒m≤n y) (≤-reflexive (trans (sym y) (lub u)))
  IsPositive.positiveʳ dmIsPositive {Φ₁} {Φ₂} u with ⊔-sel (l' Φ₁) (l' Φ₂)
  ... | inj₁ x = ≤-trans (m⊔n≡m⇒n≤m x) (≤-reflexive (trans (sym x) (lub u)))
  ... | inj₂ y = ≤-reflexive (trans (sym y) (lub u))


⊔-conical : ∀ {n m} → n ⊔ m ≡ 0 → n ≡ 0 × m ≡ 0
⊔-conical {zero}  {zero}  _ = refl , refl
⊔-conical {suc _} {zero}  ()
⊔-conical {suc _} {suc _} ()

module _ {{uniq : IsUnique _≗_ ∅}} where

  empty-bound : (m : DomainMap) → l' m ≡ 0 → ∅ ≡ m
  empty-bound m refl = (IsUnique.unique uniq) ≗⟨ refl , ∅-lookup ⟩
    where
      ∅-lookup : (k : ℕ) → nothing ≡ lookup m k
      ∅-lookup k with lookup m k in eq
      ... | just _  with () ← order m k eq
      ... | nothing = refl

  instance
    dmIsPositiveWithZero : IsPositiveWithZero _ _≗_ domains ∅
    IsPositiveWithZero.isPositive dmIsPositiveWithZero = dmIsPositive
    IsPositiveWithZero.ε-least dmIsPositiveWithZero = z≤n
    IsPositiveWithZero.ε-split dmIsPositiveWithZero {Φ₁} {Φ₂} u with ⊔-conical (lub u)
    ... | l₁≡0 , l₂≡0 rewrite sym (empty-bound Φ₁ l₁≡0) | sym (empty-bound Φ₂ l₂≡0) = refl
