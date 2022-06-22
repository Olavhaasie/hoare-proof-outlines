{-# OPTIONS --safe --without-K #-}
open import Data.Lang.Lang

open import Relation.Hoare.Bundles

module LangHoareOutlines.ModifyVal (S : StoreWithUnique Val) where

open StoreWithUnique S hiding (_∙_)

open import Data.Fin using (zero; suc)
open import Data.Nat
open import Data.Lang.Hoare store
open import Data.Lang.Tactic
open import Data.Vec using (_∷_)

open import Function using (id)

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Tactic.MonoidSolver

-- The monoid has to be defined in this scope
M₁ = M

-- There is an annoying ℕ implicit argument from the size of the environment.
module _ {n} where
  open ConsequenceSolver {n = n} MonoidSolver (quoteTerm M₁) public


private
  variable
    s : ℕ
    η : Env L s
    η′ : Env L _

-- A binary function that takes a location and an update function.  It
-- applies the current value at that location to the function and
-- stores the result at the location.  Then it returns the old value.
modify-body : Term L (suc (suc s))
modify-body =
  `let ! (var zero) `in
  `let var (suc (suc zero)) ∙ var zero `in
    var (suc (suc zero)) := var zero ；
    var (suc zero)

modify : Term L s
modify = fun (fun modify-body)

modify-body-triple : ∀ {f} l v v′
  → [ v ∷ η′ ⊢ l ↦ v ]
      f
    [ (λ w → ⟦ w ≡ v′ ⟧ ✴ l ↦ v) ]
    ------------------------------------
  → [ loc l ∷ clos η′ f ∷ η ⊢ l ↦ v ]
      modify-body
    [ (λ w → ⟦ w ≡ v ⟧ ✴ l ↦ v′) ]
modify-body-triple l v v′ t =
  [ l ↦ v ]begin
  ⟨let x =⟩ ⟨!⟩ var! (loc l) ⟨in⟩
    [ l ↦ v ]pure⟨ x≡v ⟩
    ⟨let y =⟩
      var? ⟨∙⟩ var! v
      ⟨fun-body⟩ t
    ⟨in⟩
      [ l ↦ v ]pure⟨ y≡v′ ⟩
      (var! (loc l) ⟨:=⟩ var! v′)
      [ (λ _ → l ↦ v′) ]by⟨ ✴-pure⁻ˡ ⟩
      ⟨；⟩
      auto (⟨var⟩ var! v)
    ⟨end⟩
  ⟨end⟩
  [ (λ w → ⟦ w ≡ v ⟧ ✴ l ↦ v′) ]∎

modify-triple : ∀ {f} l v v′
  → [ v ∷ η′ ⊢ l ↦ v ]
      f
    [ (λ w → ⟦ w ≡ v′ ⟧ ✴ l ↦ v) ]
    ------------------------------
  → [ η ⊢ l ↦ v ]
      modify ∙ val (clos η′ f) ∙ val (loc l)
    [ (λ w → ⟦ w ≡ v ⟧ ✴ l ↦ v′) ]
modify-triple l v v′ t = fun-app₂-triple (modify-body-triple l v v′ t)
