{-# OPTIONS --safe --without-K #-}
open import Relation.Binary.Definitions using (Transitive)

module Relation.Ternary.Construct.OrderedList {a r} {A : Set a}
  (_∼_ : A → A → Set r)
  (∼-trans : Transitive _∼_)
  where

open import Data.Nat using (ℕ; _+_)
open import Data.Product using (-,_; _,_)
open import Data.Unit.Polymorphic using (⊤)

open import Level using (_⊔_)

open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (cong; refl; _≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures


data OrderedList : Set (a ⊔ r)
_#_ : A → OrderedList → Set r

data OrderedList where
  [] : OrderedList
  cons : (x : A) (xs : OrderedList) → x # xs → OrderedList

pattern _∷#_ x xs = cons x xs _

x # [] = ⊤
x # (y ∷# _) = x ∼ y

private
  variable
    x y z : A
    xs xs₁ xs₂ ys zs zs₁ zs₂ : OrderedList

length : OrderedList → ℕ
length [] = 0
length (_ ∷# xs) = 1 + length xs

#-trans : x ∼ y → y # xs → x # xs
#-trans {xs = []} x∼y _ = _
#-trans {xs = cons _ _ _} x∼y y∼z = ∼-trans x∼y y∼z


-------------------------------------------------------------
-- FreshList equivalence

data _≗_ : OrderedList → OrderedList → Set (a ⊔ r) where
  []≗[] : [] ≗ []
  cons≗ : ∀ {x#xs} {x#ys} → xs ≗ ys → cons x xs x#xs ≗ cons x ys x#ys

≗-refl : xs ≗ xs
≗-refl {[]} = []≗[]
≗-refl {_ ∷# _} = cons≗ ≗-refl

≗-sym : xs ≗ ys → ys ≗ xs
≗-sym []≗[] = []≗[]
≗-sym (cons≗ eq) = cons≗ (≗-sym eq)

≗-trans : xs ≗ ys → ys ≗ zs → xs ≗ zs
≗-trans []≗[] []≗[] = []≗[]
≗-trans (cons≗ eq₁) (cons≗ eq₂) = cons≗ (≗-trans eq₁ eq₂)

instance
  ≗-isEquivalence : IsEquivalence _≗_
  IsEquivalence.refl  ≗-isEquivalence = ≗-refl
  IsEquivalence.sym   ≗-isEquivalence = ≗-sym
  IsEquivalence.trans ≗-isEquivalence = ≗-trans


-------------------------------------------------------------
-- OrderedList Ternary relation

-- A separated ordered list relation.
data SplitOrder : (xs ys zs : OrderedList) → Set (a ⊔ r) where
  [] : SplitOrder [] [] []

  consˡ : ∀ (#xs : z # xs) (#zs : z # zs)
    → SplitOrder xs ys zs
    → SplitOrder (cons z xs #xs) ys (cons z zs #zs)

  consʳ : ∀ (#ys : z # ys) (#zs : z # zs)
    → SplitOrder xs ys zs
    → SplitOrder xs (cons z ys #ys) (cons z zs #zs)

instance
  ordered-splits : Rel₃ OrderedList
  Rel₃._∙_≣_ ordered-splits = SplitOrder

instance
  orderedListEmptiness : Emptiness {A = OrderedList} []
  orderedListEmptiness = record {}

instance
  []-unique : IsUnique _≗_ []
  IsUnique.unique []-unique []≗[] = refl


instance
  orderedListIsCommutative : IsCommutative ordered-splits
  IsCommutative.∙-comm orderedListIsCommutative = comm
    where
      comm : Commutative ordered-splits
      comm [] = []
      comm (consˡ #xs #zs σ) = consʳ #xs #zs (comm σ)
      comm (consʳ #ys #zs σ) = consˡ #ys #zs (comm σ)


split-orderedᵣ : ∀ (z#zs : z # zs)
  → SplitOrder xs ys zs
  → z # ys
split-orderedᵣ z#zs [] = z#zs
split-orderedᵣ z#zs (consˡ {zs = zs} #xs #zs σ) = split-orderedᵣ (#-trans {xs = zs} z#zs #zs) σ
split-orderedᵣ z#zs (consʳ #ys #zs σ) = z#zs


instance
  orderedListIsSemigroupˡ : IsPartialSemigroupˡ _≗_ ordered-splits
  IsPartialSemigroupˡ.≈-equivalence orderedListIsSemigroupˡ = ≗-isEquivalence
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ orderedListIsSemigroupˡ) = resp
    where
      resp : zs₁ ≗ zs₂ → SplitOrder xs ys zs₁ → SplitOrder xs ys zs₂
      resp []≗[] σ = σ
      resp (cons≗ eq) (consˡ #xs _ σ) = consˡ #xs _ (resp eq σ)
      resp (cons≗ eq) (consʳ #ys _ σ) = consʳ #ys _ (resp eq σ)
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ orderedListIsSemigroupˡ) = respˡ
    where
      respˡ : xs₁ ≗ xs₂ → SplitOrder xs₁ ys zs → SplitOrder xs₂ ys zs
      respˡ []≗[] σ = σ
      respˡ (cons≗ eq) (consˡ #xs #zs σ) = consˡ _ #zs (respˡ eq σ)
      respˡ (cons≗ eq) (consʳ #ys #zs σ) = consʳ #ys #zs (respˡ (cons≗ eq) σ)
  IsPartialSemigroupˡ.comm orderedListIsSemigroupˡ = orderedListIsCommutative
  IsPartialSemigroupˡ.assocᵣ orderedListIsSemigroupˡ = assocᵣ
    where
      assocᵣ : RightAssoc ordered-splits
      assocᵣ [] [] = -, [] , []
      assocᵣ (consˡ #xs₁ .#xs₂ σ₁) (consˡ #xs₂ #zs σ₂) =
        let _ , σ₃ , σ₄ = assocᵣ σ₁ σ₂
        in -, consˡ #xs₁ #zs σ₃ , σ₄
      assocᵣ (consʳ #ys .#xs σ₁) (consˡ #xs #zs σ₂) =
        let _ , σ₃ , σ₄ = assocᵣ σ₁ σ₂
            z# = split-orderedᵣ #zs σ₃
        in -, consʳ z# #zs σ₃ , consˡ #ys z# σ₄
      assocᵣ σ₁ (consʳ #ys #zs σ₂) =
        let _ , σ₃ , σ₄ = assocᵣ σ₁ σ₂
            z# = split-orderedᵣ #zs σ₃
        in -, consʳ z# #zs σ₃ , consʳ #ys z# σ₄

  orderedListIsSemigroup = IsPartialSemigroupˡ.semigroupˡ orderedListIsSemigroupˡ


instance
  orderedListIsMonoidˡ : IsPartialMonoidˡ _≗_ ordered-splits []
  IsPartialMonoidˡ.identityˡ orderedListIsMonoidˡ = idˡ
    where
      idˡ : SplitOrder [] zs zs
      idˡ {[]} = []
      idˡ {cons _ _ z#zs} = consʳ z#zs z#zs idˡ
  IsPartialMonoidˡ.identity⁻ˡ orderedListIsMonoidˡ = id⁻ˡ
    where
      id⁻ˡ : SplitOrder [] ys zs → ys ≗ zs
      id⁻ˡ [] = []≗[]
      id⁻ˡ (consʳ _ _ σ) = cons≗ (id⁻ˡ σ)

  orderedListIsMonoid = IsPartialMonoidˡ.partialMonoidˡ orderedListIsMonoidˡ


module _ where
  open import Data.Nat.SizeOf {A = OrderedList} length as SizeOf
  open import Data.Nat using (z≤n; s≤s; suc)
  open import Data.Nat.Properties using (≤-refl; ≤-step)

  instance
    orderedListIsPositive : IsPositive _ _≗_ ordered-splits
    IsPositive._≤ₐ_ orderedListIsPositive = SizeOf._≤ₐ_
    IsPositive.orderₐ orderedListIsPositive = size-pre ≗-isEquivalence ≗-length
      where
        ≗-length : xs ≗ ys → length xs ≡ length ys
        ≗-length []≗[] = refl
        ≗-length (cons≗ eq) = cong suc (≗-length eq)
    IsPositive.positiveˡ orderedListIsPositive = posˡ
      where
        posˡ : SplitOrder xs ys zs → xs SizeOf.≤ₐ zs
        posˡ [] = ≤-refl
        posˡ (consˡ _ _ σ) = s≤s (posˡ σ)
        posˡ (consʳ _ _ σ) = ≤-step (posˡ σ)
    IsPositive.positiveʳ orderedListIsPositive = posʳ
      where
        posʳ : SplitOrder xs ys zs → ys SizeOf.≤ₐ zs
        posʳ [] = ≤-refl
        posʳ (consˡ _ _ σ) = ≤-step (posʳ σ)
        posʳ (consʳ _ _ σ) = s≤s (posʳ σ)

  instance
    orderedListIsPositiveWithZero : IsPositiveWithZero _ _≗_ ordered-splits []
    IsPositiveWithZero.isPositive orderedListIsPositiveWithZero = orderedListIsPositive
    IsPositiveWithZero.ε-least orderedListIsPositiveWithZero = z≤n
    IsPositiveWithZero.ε-split orderedListIsPositiveWithZero [] = refl
