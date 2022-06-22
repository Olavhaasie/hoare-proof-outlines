{-# OPTIONS --safe --without-K #-}
module Relation.Hoare.StorePredicate (S : Set) where

open import Data.Empty using (⊥)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open import Function using (id; _∘_)
open import Function.Nary.NonDependent using (Levels; Sets; _⇉_)

open import Level using (lift; 0ℓ)

open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax
open import Relation.Unary using (Pred; Satisfiable; _∩_; _∪_; ⋃; ⋂)

open Relation.Unary using (∁; IUniversal; _⇒_; _∈_; _∉_) public


-- Store predicate
SPred : Set₁
SPred = Pred S 0ℓ

False : SPred
False _ = ⊥

-- Logical 'and' and 'or' predicates
_∧_ = _∩_
_∨_ = _∪_

∃s : ∀ {A : Set} → (A → SPred) → SPred
∃s = ⋃ _
syntax ∃s (λ x → H) = ∃[ x ] H

∀s : ∀ {A : Set} → (A → SPred) → SPred
∀s = ⋂ _
syntax ∀s (λ x → H) = ∀s[ x ] H

ls₀ : ∀ {n} → Levels n
ls₀ {zero} = lift _
ls₀ {suc n} = 0ℓ , ls₀

-- Nary versions of existential quantifiers
∃⟨_,_⟩ : ∀ n {xs : Sets n ls₀} → xs ⇉ SPred → SPred
∃⟨ zero , f ⟩ = f
∃⟨ suc n , f ⟩ = ∃s (∃⟨ n ,_⟩ ∘ f)

-- Update of store predicate.
-- Given the first predicate, the second predicate is satisfiable,
-- possibly for a different store.
_⤇_ : SPred → SPred → SPred
P ⤇ Q = λ σ → σ ∈ P → Satisfiable Q

infix  11 ∃s ∀s
infixr  9 _∧_ _∨_
infixr  8 _⤇_

private
  variable
    H H′ H₁ H₁′ H₂ H₂′ : SPred
    P Q A : Set
    Hof Hof′ Hof₁ Hof₂ : A → SPred


-------------------------------------------------------------
-- Respect instances of predicates

module _ {_≈_ : S → S → Set} where

  instance
    true-respects-≈ : ∀ {ℓ} → Respect _≈_ (True {ℓ = ℓ})
    Respect.coe true-respects-≈ eq _ = lift tt

  instance
    false-respects-≈ : Respect _≈_ False
    Respect.coe false-respects-≈ eq ()

module _
  {_≈_ : S → S → Set}
  {{_ : Respect _≈_ H₁}}
  {{_ : Respect _≈_ H₂}}
  where

  instance
    ∧-respects-≈ : Respect _≈_ (H₁ ∧ H₂)
    Respect.coe ∧-respects-≈ eq (x , y) = coe eq x , coe eq y

  instance
    ∨-respects-≈ : Respect _≈_ (H₁ ∨ H₂)
    Respect.coe ∨-respects-≈ eq (inj₁ x) = inj₁ (coe eq x)
    Respect.coe ∨-respects-≈ eq (inj₂ y) = inj₂ (coe eq y)

module _
  {_≈_ : S → S → Set}
  {H : A → SPred}
  {{_ : ∀ {x : A} → Respect _≈_ (H x)}}
  where

  instance
    ∃-respects-≈ : Respect _≈_ (∃s H)
    Respect.coe ∃-respects-≈ eq (x , H) = x , coe eq H

  instance
    ∀-respects-≈ : Respect _≈_ (∀s H)
    Respect.coe ∀-respects-≈ eq f x = coe eq (f x)


-------------------------------------------------------------
-- Logical connective rules

module _ {∅ : S} {{emptiness : Emptiness ∅}} where
  ∧-idˡ : ∀[ Emp ∧ H ⇒ Emp ]
  ∧-idˡ (refl , _) = refl

  ∧-idʳ : ∀[ H ∧ Emp ⇒ Emp ]
  ∧-idʳ (_ , refl) = refl


-------------------------------------------------------------
-- Quantifier rules

existsˡ :
    (∀ x → ∀[ Hof x ⇒ H′ ])
  → ∀[ ∃s Hof ⇒ H′ ]
existsˡ f (x , σ∈H) = f x σ∈H

existsʳ :
    ∀ x → ∀[ H ⇒ Hof′ x ]
    ---------------------
  → ∀[ H ⇒ ∃s Hof′ ]
existsʳ x f σ∈H = x , f σ∈H

∃-mono-⇒ :
    (∀ {x} → ∀[ Hof x ⇒ Hof′ x ])
    -----------------------------
  → ∀[ ∃s Hof ⇒ ∃s Hof′ ]
∃-mono-⇒ f (x , σ∈H) = x , f σ∈H

forallˡ :
    ∀ x → ∀[ Hof x ⇒ H′ ]
    ---------------------
  → ∀[ ∀s Hof ⇒ H′ ]
forallˡ x f σ∈H = f (σ∈H x)

forallʳ :
    (∀ x → ∀[ H ⇒ Hof′ x ])
    -----------------------
  → ∀[ H ⇒ ∀s Hof′ ]
forallʳ f σ∈H x = f x σ∈H

∀-mono-⇒ :
    (∀ {x} → ∀[ Hof x ⇒ Hof′ x ])
    ---------------------------
  → ∀[ ∀s Hof ⇒ ∀s Hof′ ]
∀-mono-⇒ f σ∈H x = f (σ∈H x)

module _ {H₁ : A → SPred} {{rel : Rel₃ S}} where
  ✴-exists : ∀[ (∃[ x ] H₁ x) ✴ H₂ ⇒ ∃[ x ] (H₁ x ✴ H₂) ]
  ✴-exists ((x , px) ∙⟨ sep ⟩ qx) = x , px ∙⟨ sep ⟩ qx

  ✴-exists⁻ : ∀[ ∃[ x ] (H₁ x ✴ H₂) ⇒ (∃[ x ] H₁ x) ✴ H₂ ]
  ✴-exists⁻ (x , px ∙⟨ sep ⟩ qx) = (x , px) ∙⟨ sep ⟩ qx

  ✴-forall : ∀[ (∀s[ x ] H₁ x) ✴ H₂ ⇒ ∀s[ x ] (H₁ x ✴ H₂) ]
  ✴-forall (f ∙⟨ sep ⟩ qx) x = f x ∙⟨ sep ⟩ qx

  -- Inverse of ✴-forall is not possible. Since A is abstract we have
  -- no no way to construct A and, thus, we cannot get H₁ ✴ H₂.


-------------------------------------------------------------
-- Left and right monotonicity of ✴ with respect to ⇒

module _ {{rel : Rel₃ S}} where

  ✴-monoᵣ :
      ∀[ H₁ ⇒ H₁′ ]
      -----------------------
    → ∀[ H₁ ✴ H₂ ⇒ H₁′ ✴ H₂ ]
  ✴-monoᵣ f (px ∙⟨ sep ⟩ qx) = f px ∙⟨ sep ⟩ qx

  ✴-monoₗ :
      ∀[ H₂ ⇒ H₂′ ]
      -----------------------
    → ∀[ H₁ ✴ H₂ ⇒ H₁ ✴ H₂′ ]
  ✴-monoₗ f (px ∙⟨ sep ⟩ qx) = px ∙⟨ sep ⟩ f qx

  ✴-mono :
      ∀[ H₁ ⇒ H₁′ ]
    → ∀[ H₂ ⇒ H₂′ ]
      -----------------------
    → ∀[ H₁ ✴ H₂ ⇒ H₁′ ✴ H₂′ ]
  ✴-mono f g = ✴-monoᵣ f ∘ ✴-monoₗ g


-------------------------------------------------------------
-- Pure predicates

module _ {∅ : S} {{emptiness : Emptiness ∅}} where
  -- Pure store predicate
  ⟦_⟧ : Set → SPred
  ⟦_⟧ = Empty

  pure-⇒ : (P → Q) → ∀[ ⟦ P ⟧ ⇒ ⟦ Q ⟧ ]
  pure-⇒ f (emp p) = emp (f p)

  ε⇒pure : P → ∀[ Emp ⇒ ⟦ P ⟧ ]
  ε⇒pure p refl = emp p

  pure⇒ε : ∀[ ⟦ P ⟧ ⇒ Emp ]
  pure⇒ε (emp _) = refl

module _
  {P : Set} {_≈_ : S → S → Set} {∅ : S}
  {{emptiness : Emptiness ∅}} {{_ : IsUnique _≈_ ∅}}
  where

  instance
    pure-respects-≈ : Respect _≈_ ⟦ P ⟧
    Respect.coe pure-respects-≈ x≈y (emp p) rewrite unique x≈y = emp p

module _
  {∅ : S} {{rel : Rel₃ S}}
  {{emptiness : Emptiness ∅}}
  where

  ✴-pure⁺ˡ : ∀ {σ}
    → σ ∈ ⟦ P ⟧ ✴ H
    → P
  ✴-pure⁺ˡ ((emp p) ∙⟨ _ ⟩ _) = p

  ✴-pure⁺ʳ : ∀ {σ}
    → σ ∈ H ✴ ⟦ P ⟧
    → P
  ✴-pure⁺ʳ (_ ∙⟨ _ ⟩ (emp p)) = p

module _
  {_≈_ : S → S → Set} {∅ : S}
  {{rel : Rel₃ S}} {{isMonoid : IsPartialMonoid _≈_ rel ∅}}
  where

  -- Every store predicated can be extended with `True` by implication
  -- of `emp` identity.
  ✴-extend : ∀[ H ⇒ H ✴ (True {ℓ = 0ℓ}) ]
  ✴-extend x = x ∙⟨ ∙-idʳ ⟩ lift _

  {-
  However, the inverse does not hold.

  ✴-shrink : ∀[ H ✴ True ⇒ H ]

  Without this rule the separation logic is useful for languages where
  memory has to be manually allocated/freed. This rule holds when
  proving statements about languages with garbage collection, since
  frames can be removed at any point.
  -}

module _
  {_≈_ : S → S → Set} {∅ : S}
  {{rel : Rel₃ S}} {{isMonoid : IsPartialMonoid _≈_ rel ∅}}
  where

  ✴-pure : ∀[ ⟦ P × Q ⟧ ⇒ ⟦ P ⟧ ✴ ⟦ Q ⟧ ]
  ✴-pure (emp (p , q)) = emp p ∙⟨ ∙-idˡ ⟩ emp q

  module _ {{_ : IsUnique _≈_ ∅}} where
    ∧-pure : ∀[ ⟦ P ⟧ ✴ ⟦ Q ⟧ ⇒ ⟦ P × Q ⟧ ]
    ∧-pure (emp p ∙⟨ sep ⟩ emp q) with unique (∙-id⁻ˡ sep)
    ... | refl = emp (p , q)

  module _ {H : SPred} where
    ✴-pureˡ : P → ∀[ H ⇒ ⟦ P ⟧ ✴ H ]
    ✴-pureˡ p = ✴-monoᵣ (ε⇒pure p) ∘ ✴-idˡ

    ✴-pureʳ : P → ∀[ H ⇒ H ✴ ⟦ P ⟧ ]
    ✴-pureʳ p = ✴-monoₗ (ε⇒pure p) ∘ ✴-idʳ

  module _ {H : SPred} {{resp : Respect _≈_ H}} where
    ✴-pure⁻ˡ : ∀[ ⟦ P ⟧ ✴ H ⇒ H ]
    ✴-pure⁻ˡ = ✴-id⁻ˡ ∘ ✴-monoᵣ pure⇒ε

    ✴-pure⁻ʳ : ∀[ H ✴ ⟦ P ⟧ ⇒ H ]
    ✴-pure⁻ʳ = ✴-id⁻ʳ ∘ ✴-monoₗ pure⇒ε
