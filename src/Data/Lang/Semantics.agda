{-# OPTIONS --safe --without-K #-}
open import Data.Lang.Lang

open import Relation.Hoare.Bundles

module Data.Lang.Semantics (S : Store Val) where

open Store S hiding (_∙_)

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (_∷_)

open import Relation.Ternary.Core using (Own)


private
  variable
    n : ℕ
    x : Fin _
    l : L
    v v₁ v₂ : Val L
    f t t₁ t₂ : Term L _
    η η′ : Env L _
    σ σ₁ σ₂ σ₃ σ₄ : Carrier
    H : SPred


-- Big step semantics
data ⟨_,_,_⟩⇊⟨_,_⟩ : Term L n → Env L n → Carrier → Val L → Carrier → Set₁ where

  eval-var :
      η [ x ]= v
    → ⟨ var x , η , σ ⟩⇊⟨ v , σ ⟩

  eval-val : ⟨ val v , η , σ ⟩⇊⟨ v , σ ⟩

  eval-prod :
      ⟨ t₁ , η , σ ⟩⇊⟨ v₁ , σ₁ ⟩
    → ⟨ t₂ , η , σ₁ ⟩⇊⟨ v₂ , σ₂ ⟩
    → ⟨ ⟨ t₁ , t₂ ⟩ , η , σ ⟩⇊⟨ prod (v₁ , v₂) , σ₂ ⟩

  eval-fst :
      ⟨ t , η , σ ⟩⇊⟨ prod (v₁ , v₂) , σ₁ ⟩
    → ⟨ fst t , η , σ ⟩⇊⟨ v₁ , σ₁ ⟩

  eval-snd :
      ⟨ t , η , σ ⟩⇊⟨ prod (v₁ , v₂) , σ₁ ⟩
    → ⟨ snd t , η , σ ⟩⇊⟨ v₂ , σ₁ ⟩

  eval-left :
      ⟨ t , η , σ ⟩⇊⟨ v , σ₁ ⟩
    → ⟨ left t , η , σ ⟩⇊⟨ sum (inj₁ v) , σ₁ ⟩

  eval-right :
      ⟨ t , η , σ ⟩⇊⟨ v , σ₁ ⟩
    → ⟨ right t , η , σ ⟩⇊⟨ sum (inj₂ v) , σ₁ ⟩

  eval-switch-left :
      ⟨ t , η , σ ⟩⇊⟨ sum (inj₁ v) , σ₁ ⟩
    → ⟨ t₁ , v ∷ η , σ₁ ⟩⇊⟨ v₁ , σ₂ ⟩
    → ⟨ switch t |left⇒ t₁ |right⇒ t₂ end , η , σ ⟩⇊⟨ v₁ , σ₂ ⟩

  eval-switch-right :
      ⟨ t , η , σ ⟩⇊⟨ sum (inj₂ v) , σ₁ ⟩
    → ⟨ t₂ , v ∷ η , σ₁ ⟩⇊⟨ v₂ , σ₂ ⟩
    → ⟨ switch t |left⇒ t₁ |right⇒ t₂ end , η , σ ⟩⇊⟨ v₂ , σ₂ ⟩

  eval-； :
      ⟨ t₁ , η , σ ⟩⇊⟨ v₁ , σ₁ ⟩
    → ⟨ t₂ , η , σ₁ ⟩⇊⟨ v₂ , σ₂ ⟩
    → ⟨ t₁ ； t₂ , η , σ ⟩⇊⟨ v₂ , σ₂ ⟩

  eval-fun : ⟨ fun t , η , σ ⟩⇊⟨ clos η t , σ ⟩

  eval-rec : ⟨ rec t , η , σ ⟩⇊⟨ fix η t , σ ⟩

  eval-fun-app :
      ⟨ t₁ , η , σ ⟩⇊⟨ clos η′ f , σ₁ ⟩
    → ⟨ t₂ , η , σ₁ ⟩⇊⟨ v₁ , σ₂ ⟩
    → ⟨ f , v₁ ∷ η′ , σ₂ ⟩⇊⟨ v , σ₃ ⟩
    → ⟨ t₁ ∙ t₂ , η , σ ⟩⇊⟨ v , σ₃ ⟩

  eval-rec-app :
      ⟨ t₁ , η , σ ⟩⇊⟨ fix η′ f , σ₁ ⟩
    → ⟨ t₂ , η , σ₁ ⟩⇊⟨ v₁ , σ₂ ⟩
    → ⟨ f , v₁ ∷ fix η′ f ∷ η′ , σ₂ ⟩⇊⟨ v , σ₃ ⟩
    → ⟨ t₁ ∙ t₂ , η , σ ⟩⇊⟨ v , σ₃ ⟩


  ------------------------------------------------------------
  -- State operations

  eval-deref :
      ⟨ t , η , σ ⟩⇊⟨ loc l , σ₁ ⟩
    → σ₁ ∈ l ↪ v
    → ⟨ ! t , η , σ ⟩⇊⟨ v , σ₁ ⟩

  eval-ref :
      ⟨ t , η , σ ⟩⇊⟨ v , σ₁ ⟩
    → σ₂ ∈ l ↦ v ✴ Own σ₁
    → ⟨ ref t , η , σ ⟩⇊⟨ loc l , σ₂ ⟩

  eval-free :
      ⟨ t , η , σ ⟩⇊⟨ loc l , σ₁ ⟩
    → σ₁ ∈ l ↦ v ✴ Own σ₂
    → ⟨ free t , η , σ ⟩⇊⟨ unit , σ₂ ⟩

  eval-assign :
      ⟨ t₁ , η , σ ⟩⇊⟨ loc l , σ₁ ⟩
    → ⟨ t₂ , η , σ₁ ⟩⇊⟨ v₂ , σ₂ ⟩
    → σ₂ ∈ l ↦ v₁ ✴ H
    → σ₄ ∈ l ↦ v₂ ✴ H
    → ⟨ t₁ := t₂ , η , σ ⟩⇊⟨ unit , σ₄ ⟩

pattern eval-let t₁ t₂ = eval-fun-app eval-fun t₁ t₂
