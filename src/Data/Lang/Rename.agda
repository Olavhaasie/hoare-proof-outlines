{-# OPTIONS --safe --without-K #-}
module Data.Lang.Rename where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)

open import Data.Lang.Lang


private
  variable
    s s' : ℕ
    L : Set

Ren : ℕ → ℕ → Set
Ren s s' = Fin s → Fin s'

rshift : Ren s s' → Ren (suc s) (suc s')
rshift ρ zero    = zero
rshift ρ (suc k) = suc (ρ k)

rshiftₙ : ∀ n → Ren s s' → Ren (n + s) (n + s')
rshiftₙ zero ρ = ρ
rshiftₙ (suc n) ρ = rshift (rshiftₙ n ρ)

rename : Ren s s' → Term L s → Term L s'
rename ρ (var x) = var (ρ x)
rename ρ (val v) = val v
rename ρ ⟨ t₁ , t₂ ⟩ = ⟨ rename ρ t₁ , rename ρ t₂ ⟩
rename ρ (fst t) = fst (rename ρ t)
rename ρ (snd t) = snd (rename ρ t)
rename ρ (left t) = left (rename ρ t)
rename ρ (right t) = right (rename ρ t)
rename ρ switch t |left⇒ t₁ |right⇒ t₂ end = switch rename ρ t |left⇒ rename (rshift ρ) t₁ |right⇒ rename (rshift ρ) t₂ end
rename ρ (t₁ ； t₂) = rename ρ t₁ ； rename ρ t₂
rename ρ (fun t) = fun (rename (rshift ρ) t)
rename ρ (rec t) = rec (rename (rshiftₙ 2 ρ) t)
rename ρ (t₁ ∙ t₂) = (rename ρ t₁) ∙ (rename ρ t₂)
rename ρ (ref t) = ref (rename ρ t)
rename ρ (! t) = ! (rename ρ t)
rename ρ (t₁ := t₂) = (rename ρ t₁) := (rename ρ t₂)
rename ρ (free t) = free (rename ρ t)
