{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Construct.FreshList
  {a e} {A : Set a}
  (_≈_ : A → A → Set e)
  where

open import Data.List.Fresh
open import Data.Product using (-,_; _,_)

open import Level using (_⊔_)

open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (cong; refl; _≡_)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax hiding (_≤_; ≤-refl; ≤-reflexive; ≤-trans)


FreshList = List# A _≈_

private
  variable
    x xˡ xʳ y z : A
    xs xsˡ xsʳ xs₁ xs₂ ys zs zs₁ zs₂ : FreshList


-------------------------------------------------------------
-- FreshList equivalence

-- The proof is deemed irrelevant, because when the relation is a
-- negation you cannot show that two proofs of the relation are
-- propositionally equal.
data _≗_ : FreshList → FreshList → Set (a ⊔ e) where
  []≗[] : [] ≗ []
  cons≗ : ∀ {x#xs} {x#ys} → xs ≗ ys → cons x xs x#xs ≗ cons x ys x#ys

≗-refl : xs ≗ xs
≗-refl {[]} = []≗[]
≗-refl {cons a xs x} = cons≗ ≗-refl

≗-sym : xs ≗ ys → ys ≗ xs
≗-sym []≗[] = []≗[]
≗-sym (cons≗ x) = cons≗ (≗-sym x)

≗-trans : xs ≗ ys → ys ≗ zs → xs ≗ zs
≗-trans []≗[] []≗[] = []≗[]
≗-trans (cons≗ eq₁) (cons≗ eq₂) = cons≗ (≗-trans eq₁ eq₂)

instance
  ≗-isEquivalence : IsEquivalence _≗_
  IsEquivalence.refl ≗-isEquivalence = ≗-refl
  IsEquivalence.sym ≗-isEquivalence = ≗-sym
  IsEquivalence.trans ≗-isEquivalence = ≗-trans

≗-fresh : xs ≗ ys → x # xs → x # ys
≗-fresh []≗[] #xs = #xs
≗-fresh (cons≗ eq) (x≈y , #xs) = x≈y , ≗-fresh eq #xs


-------------------------------------------------------------
-- FreshList Ternary relation

-- A separated fresh list relation.
data SplitFresh : (xs ys zs : FreshList) → Set (a ⊔ e) where
  [] : SplitFresh [] [] []

  consˡ : ∀ (#xs : z # xs) (#ys : z # ys) (#zs : z # zs)
    → SplitFresh xs ys zs
    → SplitFresh (cons z xs #xs) ys (cons z zs #zs)

  consʳ : ∀ (#xs : z # xs) (#ys : z # ys) (#zs : z # zs)
    → SplitFresh xs ys zs
    → SplitFresh xs (cons z ys #ys) (cons z zs #zs)


instance
  freshSplits : Rel₃ FreshList
  Rel₃._∙_≣_ freshSplits = SplitFresh

instance
  freshListEmptiness : Emptiness {A = FreshList} []
  freshListEmptiness = record {}

instance
  []-unique : IsUnique _≗_ []
  IsUnique.unique []-unique []≗[] = refl


instance
  freshListIsCommutative : IsCommutative freshSplits
  IsCommutative.∙-comm freshListIsCommutative = comm
    where
      comm : Commutative freshSplits
      comm [] = []
      comm (consˡ #xs #ys #zs σ) = consʳ #ys #xs #zs (comm σ)
      comm (consʳ #xs #ys #zs σ) = consˡ #ys #xs #zs (comm σ)


private
  split-freshᵣ : ∀ (z#zs : z # zs)
    → SplitFresh xs ys zs
    → z # ys
  split-freshᵣ z#zs [] = z#zs
  split-freshᵣ (eq , z#zs) (consˡ #xs #ys #zs σ) = split-freshᵣ z#zs σ
  split-freshᵣ (eq , z#zs) (consʳ #xs #ys #zs σ) = eq , split-freshᵣ z#zs σ

  assocᵣ : RightAssoc freshSplits
  assocᵣ [] [] = -, [] , []
  assocᵣ σ₁ (consʳ #xs #ys #zs σ₂) =
    let l , σ₄ , σ₅ = assocᵣ σ₁ σ₂
        z# = split-freshᵣ #zs σ₄
        z#a = split-freshᵣ #xs (∙-comm σ₁)
        z#b = split-freshᵣ #xs σ₁
    in -, consʳ z#a z# #zs σ₄ , consʳ z#b #ys z# σ₅
  assocᵣ (consˡ #xs₁ #ys₁ .#xs₂ σ₁) (consˡ #xs₂ #ys₂ #zs σ₂) =
    let _ , σ₄ , σ₅ = assocᵣ σ₁ σ₂
        z# = split-freshᵣ #zs σ₄
    in -, consˡ #xs₁ z# #zs σ₄ , σ₅
  assocᵣ (consʳ #xs₁ #ys₁ .#xs₂ σ₁) (consˡ #xs₂ #ys₂ #zs σ₂) =
    let _ , σ₄ , σ₅ = assocᵣ σ₁ σ₂
        z# = split-freshᵣ #zs σ₄
    in -, consʳ #xs₁ z# #zs σ₄ , consˡ #ys₁ #ys₂ z# σ₅

instance
  freshListIsSemigroupˡ : IsPartialSemigroupˡ _≗_ freshSplits
  IsPartialSemigroupˡ.≈-equivalence freshListIsSemigroupˡ = ≗-isEquivalence
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ freshListIsSemigroupˡ) = resp
    where
      resp : zs₁ ≗ zs₂ → SplitFresh xs ys zs₁ → SplitFresh xs ys zs₂
      resp []≗[] σ = σ
      resp (cons≗ eq) (consˡ x#xs x#ys _ σ) = consˡ x#xs x#ys _ (resp eq σ)
      resp (cons≗ eq) (consʳ x#xs x#ys _ σ) = consʳ x#xs x#ys _ (resp eq σ)
  Respect.coe (IsPartialSemigroupˡ.∙-respects-≈ˡ freshListIsSemigroupˡ) = respˡ
    where
      respˡ : xs₁ ≗ xs₂ → SplitFresh xs₁ ys zs → SplitFresh xs₂ ys zs
      respˡ []≗[] σ = σ
      respˡ (cons≗ eq) (consˡ _ #ys _ σ) = consˡ _ #ys _ (respˡ eq σ)
      respˡ (cons≗ eq) (consʳ (z≈x , z#xs) _ _ σ) = consʳ (z≈x , ≗-fresh eq z#xs) _ _ (respˡ (cons≗ eq) σ)
  IsPartialSemigroupˡ.assocᵣ freshListIsSemigroupˡ = assocᵣ

  freshListIsSemigroup = IsPartialSemigroupˡ.semigroupˡ freshListIsSemigroupˡ


instance
  freshListIsMonoidˡ : IsPartialMonoidˡ _≗_ freshSplits []
  IsPartialMonoidˡ.identityˡ freshListIsMonoidˡ = idˡ
    where
      idˡ : SplitFresh [] zs zs
      idˡ {[]} = []
      idˡ {cons _ _ z#zs} = consʳ _ z#zs z#zs idˡ
  IsPartialMonoidˡ.identity⁻ˡ freshListIsMonoidˡ = id⁻ˡ
    where
      id⁻ˡ : SplitFresh [] ys zs → ys ≗ zs
      id⁻ˡ [] = []≗[]
      id⁻ˡ (consʳ _ _ _ σ) = cons≗ (id⁻ˡ σ)

  freshListIsMonoid = IsPartialMonoidˡ.partialMonoidˡ freshListIsMonoidˡ


module _ where
  open import Data.Nat.SizeOf {A = FreshList} length as SizeOf
  open import Data.Nat.Properties
  open import Data.Nat using (z≤n; s≤s; suc)

  instance
    freshListIsPositive : IsPositive _ _≗_ freshSplits
    IsPositive._≤ₐ_ freshListIsPositive = SizeOf._≤ₐ_
    IsPositive.orderₐ freshListIsPositive = size-pre ≗-isEquivalence ≗-length
      where
        ≗-length : xs ≗ ys → length xs ≡ length ys
        ≗-length []≗[] = refl
        ≗-length (cons≗ eq) = cong suc (≗-length eq)
    IsPositive.positiveˡ freshListIsPositive = posˡ
      where
        posˡ : SplitFresh xs ys zs → xs SizeOf.≤ₐ zs
        posˡ [] = ≤-refl
        posˡ (consˡ _ _ _ σ) = s≤s (posˡ σ)
        posˡ (consʳ _ _ _ σ) = ≤-step (posˡ σ)
    IsPositive.positiveʳ freshListIsPositive = posʳ
      where
        posʳ : SplitFresh xs ys zs → ys SizeOf.≤ₐ zs
        posʳ [] = ≤-refl
        posʳ (consˡ _ _ _ σ) = ≤-step (posʳ σ)
        posʳ (consʳ _ _ _ σ) = s≤s (posʳ σ)

  instance
    freshListIsPositiveWithZero : IsPositiveWithZero _ _≗_ freshSplits []
    IsPositiveWithZero.isPositive freshListIsPositiveWithZero = freshListIsPositive
    IsPositiveWithZero.ε-least freshListIsPositiveWithZero = z≤n
    IsPositiveWithZero.ε-split freshListIsPositiveWithZero [] = refl
