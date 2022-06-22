{-# OPTIONS --safe --without-K #-}
open import Data.Lang.Lang

open import Relation.Hoare.Bundles

module LangHoareOutlines.CopyList (S : CommutativeStoreWithUnique Val) where

open CommutativeStoreWithUnique S hiding (_∙_)

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List) renaming ([] to []ˡ; _∷_ to _∷ˡ_)
open import Data.Nat
open import Data.Lang.Hoare store
open import Data.Lang.Tactic
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Vec using (_∷_)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Core using (Respect; coe; unique)
open import Relation.Ternary.Tactic.CommutativeMonoidSolver

-- The monoid has to be defined in this scope
CM₁ = CM

-- There is an annoying ℕ implicit argument from the size of the environment.
module _ {n} where
  open ConsequenceSolver {n = n} CommutativeMonoidSolver (quoteTerm CM₁) public

private
  variable
    s : ℕ
    η : Env L s

-- A recursive function that copies a list structure.
-- Returns the copied list.
copy-body : Term L (suc (suc s))
copy-body =
  switch (var zero)
    |left⇒ nil
    |right⇒
      `let snd (var zero) `in
      `let ! (var zero) `in
      `let (var (suc (suc (suc (suc zero))))) ∙ var zero `in
      `let ref (var zero) `in
      `let fst (var (suc (suc (suc (suc zero))))) `in
        cons ∙ var zero ∙ var (suc zero)
  end

copy : Term L s
copy = rec copy-body

abstract
  data IsList : Val L → List (Val L) → SPred where
    is-nil  : ε[ IsList nil-val []ˡ ]
    is-cons : ∀ {l} {x xs} {ys} → ∀[ l ↦ xs ✴ IsList xs ys ⇒ IsList (cons-val x (loc l)) (x ∷ˡ ys) ]

  instance
    IsList-respects-≈ : ∀ {v} {l} → Respect _≈_ (IsList v l)
    Respect.coe IsList-respects-≈ eq is-nil with refl ← unique eq = is-nil
    Respect.coe IsList-respects-≈ eq (is-cons l) = is-cons (coe eq l)

  list-is-sum : ∀ {l} {xs} → ∀[ IsList l xs ⇒ ∃[ v ] (⟦ l ≡ sum v ⟧ ✴ IsList l xs) ]
  list-is-sum is-nil = _ , ✴-pureˡ refl is-nil
  list-is-sum (is-cons x) = _ , ✴-pureˡ refl (is-cons x)

  emp-is-nil : ∀[ Emp ⇒ IsList nil-val []ˡ ]
  emp-is-nil refl = is-nil

  mknil : ∀ {v} → ∀[ ⟦ v ≡ nil-val ⟧ ⇒ IsList v []ˡ ]
  mknil (emp refl) = is-nil

  unnil : ∀ {v} {xs}
    → ∀[ IsList (sum (inj₁ v)) xs ⇒ ⟦ v ≡ unit × xs ≡ []ˡ ⟧ ]
  unnil is-nil = emp (refl , refl)

  mkcons : ∀ {l} {x xs} {ys} → ∀[ l ↦ xs ✴ IsList xs ys ⇒ IsList (cons-val x (loc l)) (x ∷ˡ ys) ]
  mkcons = is-cons

  uncons : ∀ {xs} {v}
    → ∀[ IsList (sum (inj₂ v)) xs
      ⇒ ∃[ l ] ∃[ x ] ∃[ t ] ∃[ ys ]
        (⟦ v ≡ prod (x , loc l) × xs ≡ x ∷ˡ ys ⟧ ✴ l ↦ t ✴ IsList t ys) ]
  uncons (is-cons x) = _ , _ , _ , _ , ✴-pureˡ (refl , refl) x

copy-body-triple : ∀ v xs
  → [ v ∷ fix η copy-body ∷ η ⊢ IsList v xs ]
      copy-body
    [ (λ w → IsList w xs ✴ IsList v xs) ]
copy-body-triple {η = η} v xs =
  [ IsList v xs ]begin
  [ ∃[ v′ ] (⟦ v ≡ sum v′ ⟧ ✴ IsList v xs) ]by⟨ list-is-sum ⟩
  [ _ ]exists⟨ v′ ⟩
  [ IsList v xs ]pure λ { refl →
  [ IsList (sum v′) xs ]by⟨⟩
  ⟨switch⟩ var! v
    |left⇒ (λ { {v₁} v₁≡nil@refl →
      [ IsList (sum (inj₁ v₁)) xs ]by⟨⟩
      [ ⟦ v₁ ≡ unit × xs ≡ []ˡ ⟧ ]by⟨ unnil ⟩
      []pure-emp (λ { (refl , refl) →
      ⟨nil⟩
      [ (λ w → ⟦ w ≡ nil-val ⟧) ]by⟨⟩
      [ (λ w → IsList w []ˡ) ]by⟨ mknil ⟩
      [ (λ w → IsList w []ˡ ✴ Emp) ]byauto
      [ (λ w → IsList w []ˡ ✴ IsList nil-val []ˡ) ]by⟨ ✴-monoₗ emp-is-nil ⟩
      [ (λ w → IsList w xs ✴ IsList v xs) ]∎ })})
    |right⇒ (λ { {v₂} v₂≡cons@refl →
      [ IsList (sum (inj₂ v₂)) xs ]by⟨⟩
      [ ∃[ l₁ ] ∃[ x ] ∃[ t₁ ] ∃[ ys ] (⟦ v₂ ≡ prod (x , loc l₁) × xs ≡ x ∷ˡ ys ⟧ ✴ l₁ ↦ t₁ ✴ IsList t₁ ys) ]by⟨ uncons ⟩
      [ _ ]existsₙ⟨ 4 ⟩ (λ { (l₁ , x , t₁ , ys) →
      [ ⟦ v₂ ≡ prod (x , loc l₁) × xs ≡ x ∷ˡ ys ⟧ ✴ l₁ ↦ t₁ ✴ IsList t₁ ys ]by⟨⟩
      [ l₁ ↦ t₁ ✴ IsList t₁ ys ]pure (λ { (refl , refl) →
      ⟨let _ =⟩
        [ Emp ]auto
        (⟨snd⟩ var! v₂)
        [ (λ w → ⟦ w ≡ loc l₁ ⟧ ✴ l₁ ↦ t₁ ✴ IsList t₁ ys) ]autorestore
      ⟨in⟩
        [ l₁ ↦ t₁ ✴ IsList t₁ ys ]pure⟨ l₁≡ ⟩
        ⟨let _ =⟩
          [ l₁ ↦ t₁ ]auto
          (⟨!⟩ var! (loc l₁))
          [ (λ w → ⟦ w ≡ t₁ ⟧ ✴ l₁ ↦ t₁ ✴ IsList t₁ ys) ]autorestore
        ⟨in⟩
          [ l₁ ↦ t₁ ✴ IsList t₁ ys ]pure⟨ t₁≡ ⟩
          ⟨let t₂ =⟩
            [ IsList t₁ ys ]auto
            var! (fix η copy-body) ⟨∙⟩ var! t₁
            ⟨rec-body⟩ copy-body-triple t₁ ys
            [ (λ w → IsList w ys ✴ l₁ ↦ t₁ ✴ IsList t₁ ys) ]autorestore
          ⟨in⟩
            ⟨let a =⟩
              [ Emp ]auto
              (⟨ref⟩ var! t₂)
              [ (λ w → ∃[ l₂ ] (⟦ w ≡ loc l₂ ⟧ ✴ l₂ ↦ t₂)) ]by⟨⟩
              [ (λ w → ∃[ l₂ ] (⟦ w ≡ loc l₂ ⟧ ✴ l₂ ↦ t₂) ✴ IsList t₂ ys ✴ l₁ ↦ t₁ ✴ IsList t₁ ys) ]autorestore
              [ (λ w → ∃[ l₂ ] ((⟦ w ≡ loc l₂ ⟧ ✴ l₂ ↦ t₂) ✴ IsList t₂ ys ✴ l₁ ↦ t₁ ✴ IsList t₁ ys)) ]by⟨ ✴-exists ⟩
            ⟨in⟩
              [ _ ]exists⟨ l₂ ⟩
              [ ⟦ a ≡ loc l₂ ⟧ ✴ l₂ ↦ t₂ ✴ IsList t₂ ys ✴ l₁ ↦ t₁ ✴ IsList t₁ ys ]by⟨ ✴-assocᵣ ⟩
              [ l₂ ↦ t₂ ✴ IsList t₂ ys ✴ l₁ ↦ t₁ ✴ IsList t₁ ys ]pure⟨ a≡l₂ ⟩
              ⟨let _ =⟩
                auto (⟨fst⟩ var! v₂)
              ⟨in⟩
                [ l₂ ↦ t₂ ✴ IsList t₂ ys ✴ l₁ ↦ t₁ ✴ IsList t₁ ys ]pure⟨ x≡ ⟩
                [ Emp ]frameby⟨ ✴-idˡ ⟩
                (var! x ⟨cons⟩ var! (loc l₂))
                [ (λ w → ((⟦ w ≡ cons-val x (loc l₂) ⟧ ✴ l₂ ↦ t₂) ✴ IsList t₂ ys) ✴ l₁ ↦ t₁ ✴ IsList t₁ ys) ]restoreby⟨ ✴-assocₗ ∘ ✴-assocₗ ⟩
                [ (λ w → (⟦ w ≡ cons-val x (loc l₂) ⟧ ✴ l₂ ↦ t₂ ✴ IsList t₂ ys) ✴ (l₁ ↦ t₁ ✴ IsList t₁ ys)) ]by⟨ ✴-monoᵣ ✴-assocᵣ ⟩
                [ (λ w → IsList w (x ∷ˡ ys) ✴ l₁ ↦ t₁ ✴ IsList t₁ ys) ]by⟨ ✴-monoᵣ (λ { x@(emp refl ∙⟨ _ ⟩ _) → mkcons (✴-pure⁻ˡ x) }) ⟩
                [ (λ w → IsList w (x ∷ˡ ys) ✴ IsList (cons-val x (loc l₁)) (x ∷ˡ ys)) ]by⟨ ✴-monoₗ mkcons ⟩
                [ (λ w → IsList w xs ✴ IsList v xs) ]∎
              ⟨end⟩
            ⟨end⟩
          ⟨end⟩
        ⟨end⟩
      ⟨end⟩ })})})
   ⟨end⟩
  [ (λ w → IsList w xs ✴ IsList v xs) ]∎
  }

copy-triple : ∀ v xs
  → [ η ⊢ IsList v xs ]
      copy ∙ val v
    [ (λ w → IsList w xs ✴ IsList v xs) ]
copy-triple v xs = rec-app₁-triple (copy-body-triple v xs)
