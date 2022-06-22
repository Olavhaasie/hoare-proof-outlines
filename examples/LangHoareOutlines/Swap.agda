{-# OPTIONS --safe --without-K #-}
open import Data.Lang.Lang

open import Relation.Hoare.Bundles

module LangHoareOutlines.Swap (S : CommutativeStoreWithUnique Val) where

open CommutativeStoreWithUnique S hiding (_∙_)

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Lang.Hoare store
open import Data.Lang.Semantics store
open import Data.Lang.Tactic
open import Data.Vec using (_∷_)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
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

-- A curried function that takes two locations and swaps the values.
-- Returns unit
swap-body-anf : Term L (suc (suc s))
swap-body-anf =
  `let ! (var zero) `in                   -- v2 = !k
  `let ! (var (suc (suc zero))) `in       -- v1 = !l
    var (suc (suc zero)) := var zero ；  -- k := v1
    (var (suc (suc (suc zero)))) := var (suc zero)    -- l := v2

-- Not ANF version of swap
swap-body : Term L (suc (suc s))
swap-body =
  `let ! (var zero) `in                           -- v = !k
    var (suc zero) := ! (var (suc (suc zero))) ； -- k := !l
    var (suc (suc zero)) := var zero              -- l := !k

swap : Term L s
swap = fun (fun swap-body)


-- Verification of swap in ANF
{-
  swap = fun l => fun k =>
    [ l ↦ v₁ ✴ k ↦ v₂ ]
    let v2 = !k in
    [ w . ⟦ w = v2 ⟧ ✴ l ↦ v₁ ✴ k ↦ v₂ ]
      (let v1 = ! l in
      [ w . ⟦ w = v1 ⟧ ✴ l ↦ v₁ ✴ k ↦ v₂ ]
        k := v1
      [ w . ⟦ w = unit ⟧ ✴ l ↦ v₁ ✴ k ↦ v₁ ]
        ) ；
      [ l ↦ v₁ ✴ k ↦ v₁ ]
      l := v2
      [ w . ⟦ w = unit ⟧ ✴ l ↦ v₂ ✴ k ↦ v₁ ]
-}

swap-body-anf-triple-without-auto : ∀ (l k : L) (v₁ v₂ : Val L)
  → [ (loc k ∷ loc l ∷ η) ⊢ l ↦ v₁ ✴ k ↦ v₂ ]
      swap-body-anf
    [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v₂ ✴ k ↦ v₁) ]
swap-body-anf-triple-without-auto l k v₁ v₂ =
  [ l ↦ v₁ ✴ k ↦ v₂ ]begin
  ⟨let x =⟩
    [ k ↦ v₂ ]frameby⟨ ✴-swap ⟩
    ⟨!⟩ here
    [ (λ w → ⟦ w ≡ v₂ ⟧ ✴ l ↦ v₁ ✴ k ↦ v₂) ]restoreby⟨ ✴-monoₗ ✴-swap ∘ ✴-assocᵣ ⟩
  ⟨in⟩
    [ l ↦ v₁ ✴ k ↦ v₂ ]pure⟨ x≡v₂ ⟩
    ⟨let y =⟩
      [ l ↦ v₁ ]frameby⟨ id ⟩
      ⟨!⟩ there (there here)
      [ (λ w → ⟦ w ≡ v₁ ⟧ ✴ l ↦ v₁ ✴ k ↦ v₂) ]restoreby⟨ ✴-assocᵣ ⟩
    ⟨in⟩
      [ l ↦ v₁ ✴ k ↦ v₂ ]pure⟨ y≡v₁ ⟩
      [ k ↦ v₂ ]frameby⟨ ✴-swap ⟩
      (there (there here) ⟨:=⟩ here≡ y≡v₁)
      [ (λ _ → k ↦ v₁) ]by⟨ ✴-pure⁻ˡ ⟩
      [ (λ _ → l ↦ v₁ ✴ k ↦ v₁) ]restoreby⟨ ✴-swap ⟩
      ⟨；⟩
      [ l ↦ v₁ ]frameby⟨ id ⟩
      there (there (there here)) ⟨:=⟩ there (here≡ x≡v₂)
      [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v₂ ✴ k ↦ v₁) ]restoreby⟨ ✴-assocᵣ ⟩
    ⟨end⟩
  ⟨end⟩
  [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v₂ ✴ k ↦ v₁) ]∎

swap-body-anf-triple : ∀ (l k : L) (v₁ v₂ : Val L)
  → [ (loc k ∷ loc l ∷ η) ⊢ l ↦ v₁ ✴ k ↦ v₂ ]
      swap-body-anf
    [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v₂ ✴ k ↦ v₁) ]
swap-body-anf-triple l k v₁ v₂ =
  [ l ↦ v₁ ✴ k ↦ v₂ ]begin
  ⟨let x =⟩ auto (⟨!⟩ var! (loc k)) ⟨in⟩
    [ l ↦ v₁ ✴ k ↦ v₂ ]pure⟨ x≡v₂ ⟩
    ⟨let y =⟩ auto (⟨!⟩ var! (loc l)) ⟨in⟩
      [ l ↦ v₁ ✴ k ↦ v₂ ]pure⟨ y≡v₁ ⟩
      auto (var! (loc k) ⟨:=⟩ var! v₁)
      [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v₁ ✴ k ↦ v₁) ]by⟨⟩
      [ (λ _ → l ↦ v₁ ✴ k ↦ v₁) ]by⟨ ✴-pure⁻ˡ ⟩
      ⟨；⟩
      [ l ↦ v₁ ✴ k ↦ v₁ ]by⟨⟩
      auto (var! (loc l) ⟨:=⟩ var! v₂)
    ⟨end⟩
  ⟨end⟩
  [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v₂ ✴ k ↦ v₁) ]∎

swap-body-triple : ∀ (l k : L) (v₁ v₂ : Val L)
  → [ (loc k ∷ loc l ∷ η) ⊢ l ↦ v₁ ✴ k ↦ v₂ ]
      swap-body
    [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v₂ ✴ k ↦ v₁) ]
swap-body-triple {η = η} l k v₁ v₂ = coe-triple (swap-body-anf-triple l k v₁ v₂) sem-eq
  where
    sem-eq : ∀ {η : Env L (suc (suc s))} {σ σ′} {v}
      → ⟨ swap-body-anf , η , σ ⟩⇊⟨ v , σ′ ⟩
        ---------------------------------
      → ⟨ swap-body , η , σ ⟩⇊⟨ v , σ′ ⟩
    sem-eq (eval-let
             (eval-deref (eval-var k∈₁η) k↪v₂)
             (eval-let
               (eval-deref (eval-var l∈₁η) l↪v₁)
               (eval-；
                 (eval-assign
                   (eval-var (there k∈₂η))
                   (eval-var here)
                   a b)
                 (eval-assign
                  (eval-var (there l∈₂η))
                  (eval-var (there !k∈η))
                   c d)))) =
      eval-let
        (eval-deref (eval-var k∈₁η) k↪v₂)
        (eval-；
          (eval-assign (eval-var k∈₂η) (eval-deref (eval-var l∈₁η) l↪v₁)
            a b)
          (eval-assign (eval-var l∈₂η) (eval-var !k∈η)
            c d))

swap-triple : ∀ (l k : L) (v₁ v₂ : Val L)
  → [ η ⊢ l ↦ v₁ ✴ k ↦ v₂ ]
      swap ∙ val (loc l) ∙ val (loc k)
    [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v₂ ✴ k ↦ v₁) ]
swap-triple l k v₁ v₂ = fun-app₂-triple (swap-body-triple l k v₁ v₂)
