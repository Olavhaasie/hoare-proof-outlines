{-# OPTIONS --safe --without-K #-}
open import Data.Lang.Lang

open import Relation.Hoare.Bundles

module LangHoareOutlines.DoubleRef (S : StoreWithUnique Val) where

open StoreWithUnique S hiding (_∙_)

open import Data.Fin using (zero; suc)
open import Data.Nat
open import Data.Lang.Hoare store
open import Data.Lang.Tactic
open import Data.Product using (_,_)
open import Data.Vec using (_∷_)

open import Function using (id)

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Ternary.Tactic.MonoidSolver
open import Relation.Unary using (_≐_)

-- The monoid has to be defined in this scope
M₁ = M

-- There is an annoying ℕ implicit argument from the size of the environment.
module _ {n} where
  open ConsequenceSolver {n = n} MonoidSolver (quoteTerm M₁) public

private
  variable
    s : ℕ
    η : Env L s

-- Creates a double reference of a given value v and returns
-- the second location.
double-ref-body : Term L (suc s)
double-ref-body =
  `let ref (var zero) `in  -- l = ref v
    ref (var zero)         -- k = ref l

double-ref : Term L s
double-ref = fun double-ref-body

double-ref-body-triple : ∀ v
  → [ v ∷ η ⊢ Emp ]
      double-ref-body
    [ (λ w → ∃[ l ] ∃[ k ] (⟦ w ≡ loc k ⟧ ✴ k ↦ loc l ✴ l ↦ v)) ]
double-ref-body-triple v =
  [ Emp ]begin
  ⟨let x =⟩ ⟨ref⟩ var! v ⟨in⟩
    [ ∃[ l ] (⟦ x ≡ loc l ⟧ ✴ l ↦ v) ]by⟨⟩
    [ (λ l → ⟦ x ≡ loc l ⟧ ✴ l ↦ v) ]exists⟨ l ⟩
    [ l ↦ v ]pure⟨ x≡l ⟩
    [ Emp ]frameby⟨ ✴-idˡ ⟩
    ⟨ref⟩ var! (loc l)
    [ (λ w → ∃[ k ] ((⟦ w ≡ loc k ⟧ ✴ k ↦ loc l) ✴ l ↦ v)) ]restoreby⟨ ✴-exists ⟩
    [ (λ w → ∃[ k ] (⟦ w ≡ loc k ⟧ ✴ k ↦ loc l ✴ l ↦ v)) ]by⟨ (λ { (l , x) → l , ✴-assocᵣ x }) ⟩
    [ (λ w → ∃[ l ] ∃[ k ] (⟦ w ≡ loc k ⟧ ✴ k ↦ loc l ✴ l ↦ v)) ]by⟨ (λ { (k , x) → l , k , x }) ⟩
  ⟨end⟩
  [ (λ w → ∃[ l ] ∃[ k ] (⟦ w ≡ loc k ⟧ ✴ k ↦ loc l ✴ l ↦ v)) ]∎

double-ref-triple : ∀ v
  → [ η ⊢ Emp ]
      double-ref ∙ val v
    [ (λ w → ∃[ l ] ∃[ k ] (⟦ w ≡ loc k ⟧ ✴ k ↦ loc l ✴ l ↦ v)) ]
double-ref-triple v = fun-app₁-triple (double-ref-body-triple v)

-- Frees a double reference and returns unit.
free-double-ref-body : Term L (suc s)
free-double-ref-body =
  `let ! (var zero) `in       -- l = ! k
    free (var (suc zero)) ；  -- free k
    free (var zero)           -- free l

free-double-ref : Term L s
free-double-ref = fun free-double-ref-body

free-double-ref-body-triple : ∀ l k v
  → [ loc k ∷ η ⊢ k ↦ loc l ✴ l ↦ v ]
      free-double-ref-body
    [ (λ w → ⟦ w ≡ unit ⟧) ]
free-double-ref-body-triple l k v =
  [ k ↦ loc l ✴ l ↦ v ]begin
  ⟨let x =⟩ auto (⟨!⟩ var! (loc k)) ⟨in⟩
    [ k ↦ loc l ✴ l ↦ v ]pure⟨ x≡l ⟩ (
    auto (⟨free⟩ var! (loc k))
    [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v) ]by⟨⟩
    [ (λ _ → l ↦ v) ]by⟨ ✴-pure⁻ˡ ⟩
    ⟨；⟩
    ⟨free⟩ var! (loc l) )
  ⟨end⟩
  [ (λ w → ⟦ w ≡ unit ⟧) ]∎

free-double-ref-triple : ∀ l k v
  → [ η ⊢ k ↦ loc l ✴ l ↦ v ]
      free-double-ref ∙ val (loc k)
    [ (λ w → ⟦ w ≡ unit ⟧) ]
free-double-ref-triple l k v = fun-app₁-triple (free-double-ref-body-triple l k v)
