{-# OPTIONS --safe --without-K #-}
{-
  Unfinished module for transforming a program to ANF while preserving
  semantics.
-}
open import Data.Lang.Lang

open import Relation.Hoare.Bundles

module Data.Lang.Anf (S : Store Val) where

open Store S hiding (_∙_)

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Lang.Rename
open import Data.Lang.Semantics S
open import Data.Product using (_,_)
open import Data.Vec using (_++_; _∷_; [_]; [])

open import Function using (id)

private
  variable
    n m : ℕ

data IsAnf : (t : Term L n) → Set where
  anf-var : ∀ (x : Fin n) → IsAnf (var x)
  anf-val : ∀ (v : Val L) → IsAnf {n} (val v)
  anf-⟨_,_⟩ : ∀ (x y : Fin n) → IsAnf ⟨ var x , var y ⟩
  anf-fst : ∀ (x : Fin n) → IsAnf (fst (var x))
  anf-snd : ∀ (x : Fin n) → IsAnf (snd (var x))
  anf-left : ∀ (x : Fin n) → IsAnf (left (var x))
  anf-right : ∀ (x : Fin n) → IsAnf (right (var x))
  anf-switch : ∀ (x : Fin n) {t₁ t₂ : Term L (suc n)}
    → IsAnf t₁
    → IsAnf t₂
    → IsAnf (switch (var x) |left⇒ t₁ |right⇒ t₂ end)
  anf-seq : ∀ {t₁ t₂ : Term L n}
    → IsAnf t₁
    → IsAnf t₂
    → IsAnf (t₁ ； t₂)
  anf-fun : ∀ {t : Term L (suc n)} → IsAnf t → IsAnf (fun t)
  anf-rec : ∀ {t : Term L (suc (suc n))} → IsAnf t → IsAnf (rec t)
  anf-app : ∀ (x y : Fin n) → IsAnf (var x ∙ var y)
  anf-ref : ∀ (x : Fin n) → IsAnf (ref (var x))
  anf-deref : ∀ (x : Fin n) → IsAnf (! (var x))
  anf-assign : ∀ (x y : Fin n) → IsAnf (var x := var y)
  anf-free : ∀ (x : Fin n) → IsAnf (free (var x))
  anf-let : ∀ {t₁ : Term L n} {t₂ : Term L (suc n)}
    → IsAnf t₁
    → IsAnf t₂
    → IsAnf (`let t₁ `in t₂)

record Anf (t : Term L n) : Set₁ where
  constructor _preserves_
  field
    {a} : Term L n
    is-anf : IsAnf a
    sem : ∀ {η} {σ σ′} {v}
      → ⟨ a , η , σ ⟩⇊⟨ v , σ′ ⟩
      → ⟨ t , η , σ ⟩⇊⟨ v , σ′ ⟩

rename-is-anf : ∀ {t : Term L n} (ρ : Ren n m) → IsAnf t → IsAnf (rename ρ t)
rename-is-anf ρ (anf-var x) = anf-var (ρ x)
rename-is-anf ρ (anf-val v) = anf-val v
rename-is-anf ρ anf-⟨ x , y ⟩ = anf-⟨ ρ x , ρ y ⟩
rename-is-anf ρ (anf-fst x) = anf-fst (ρ x)
rename-is-anf ρ (anf-snd x) = anf-snd (ρ x)
rename-is-anf ρ (anf-left x) = anf-left (ρ x)
rename-is-anf ρ (anf-right x) = anf-right (ρ x)
rename-is-anf ρ (anf-switch x a₁ a₂) = anf-switch (ρ x) (rename-is-anf (rshift ρ) a₁) (rename-is-anf (rshift ρ) a₂)
rename-is-anf ρ (anf-seq a₁ a₂) = anf-seq (rename-is-anf ρ a₁) (rename-is-anf ρ a₂)
rename-is-anf ρ (anf-fun a) = anf-fun (rename-is-anf (rshift ρ) a)
rename-is-anf ρ (anf-rec a) = anf-rec (rename-is-anf (rshiftₙ 2 ρ) a)
rename-is-anf ρ (anf-app x y) = anf-app (ρ x) (ρ y)
rename-is-anf ρ (anf-ref x) = anf-ref (ρ x)
rename-is-anf ρ (anf-deref x) = anf-deref (ρ x)
rename-is-anf ρ (anf-assign x y) = anf-assign (ρ x) (ρ y)
rename-is-anf ρ (anf-free x) = anf-free (ρ x)
rename-is-anf ρ (anf-let a₁ a₂) = anf-let (rename-is-anf ρ a₁) (rename-is-anf (rshift ρ) a₂)

rshift-env : ∀ {η₁ : Env L n} {η₂ : Env L m} {x : Fin (n + m)} {v v₁}
  → (η₁ ++ v₁ ∷ η₂) [ rshiftₙ n suc x ]= v
  → (η₁ ++ η₂) [ x ]= v
rshift-env {η₁ = []} {η₂ = _ ∷ _} (there x∈η) = x∈η
rshift-env {η₁ = _ ∷ _} {x = zero} here = here
rshift-env {η₁ = _ ∷ _} {x = suc x} (there x∈η) = there (rshift-env x∈η)

rshift-sem : ∀ {η₁ : Env L n} {η₂ : Env L m} {σ₁ σ₂} {v v₁} {t : Term L (n + m)}
  → ⟨ rename (rshiftₙ n suc) t , η₁ ++ v₁ ∷ η₂ , σ₁ ⟩⇊⟨ v , σ₂ ⟩
  → ⟨ t , η₁ ++ η₂ , σ₁ ⟩⇊⟨ v , σ₂ ⟩
rshift-sem {t = var x} (eval-var x∈η) = eval-var (rshift-env x∈η)
rshift-sem {t = val _} eval-val = eval-val
rshift-sem {t = ⟨ _ , _ ⟩} (eval-prod e₁ e₂) = eval-prod (rshift-sem e₁) (rshift-sem e₂)
rshift-sem {t = fst _} (eval-fst e) = eval-fst (rshift-sem e)
rshift-sem {t = snd _} (eval-snd e) = eval-snd (rshift-sem e)
rshift-sem {t = left _} (eval-left e) = eval-left (rshift-sem e)
rshift-sem {t = right _} (eval-right e) = eval-right (rshift-sem e)
rshift-sem {η₁ = η₁} {η₂ = η₂} {t = switch _ |left⇒ _ |right⇒ _ end} (eval-switch-left e₁ e₂) =
  eval-switch-left (rshift-sem e₁) (rshift-sem {η₁ = _ ∷ η₁} {η₂ = η₂} e₂)
rshift-sem {η₁ = η₁} {η₂ = η₂} {t = switch _ |left⇒ _ |right⇒ _ end} (eval-switch-right e₁ e₂) =
  eval-switch-right (rshift-sem e₁) (rshift-sem {η₁ = _ ∷ η₁} {η₂ = η₂} e₂)
rshift-sem {t = _ ； _} (eval-； e₁ e₂) = eval-； (rshift-sem e₁) (rshift-sem e₂)
rshift-sem {t = fun _} eval-fun = {!!}
rshift-sem {t = rec _} eval-rec = {!!}
rshift-sem {t = _ ∙ _} (eval-fun-app e e₁ e₂) = eval-fun-app (rshift-sem e) (rshift-sem e₁) e₂
rshift-sem {t = _ ∙ _} (eval-rec-app e e₁ e₂) = eval-rec-app (rshift-sem e) (rshift-sem e₁) e₂
rshift-sem {t = ref _} (eval-ref e l↪v) = eval-ref (rshift-sem e) l↪v
rshift-sem {t = ! _} (eval-deref e l↪v) = eval-deref (rshift-sem e) l↪v
rshift-sem {t = _ := _} (eval-assign e₁ e₂ x y) = eval-assign (rshift-sem e₁) (rshift-sem e₂) x y
rshift-sem {t = free _} (eval-free e l↪v) = eval-free (rshift-sem e) l↪v

rshift-sem₀ : ∀ {η : Env L n} {σ₁ σ₂} {v v₁} {t : Term L n}
  → ⟨ rename suc t , v₁ ∷ η , σ₁ ⟩⇊⟨ v , σ₂ ⟩
  → ⟨ t , η , σ₁ ⟩⇊⟨ v , σ₂ ⟩
rshift-sem₀ {η = η} = rshift-sem {η₁ = []} {η₂ = η}

rshift-sem₁ : ∀ {η : Env L n} {σ₁ σ₂} {v v₁ v₂} {t : Term L (suc n)}
  → ⟨ rename (rshift suc) t , v₁ ∷ v₂ ∷ η , σ₁ ⟩⇊⟨ v , σ₂ ⟩
  → ⟨ t , v₁ ∷ η , σ₁ ⟩⇊⟨ v , σ₂ ⟩
rshift-sem₁ {v₁ = v₁} = rshift-sem {η₁ = [ v₁ ]}

to-anf : ∀ (t : Term L n) → Anf t
to-anf (var x) = (anf-var x) preserves id
to-anf (val v) = (anf-val v) preserves id
to-anf ⟨ t₁ , t₂ ⟩ with to-anf t₁ | to-anf t₂
... | a₁ preserves s₁ | a₂ preserves s₂ = anf-let a₁ (anf-let (rename-is-anf suc a₂) anf-⟨ suc zero , zero ⟩) preserves λ where
                                           (eval-let e₁ (eval-let e₂ (eval-prod (eval-var (there here)) (eval-var here)))) →
                                             eval-prod (s₁ e₁) (s₂ (rshift-sem₀ e₂))
to-anf (fst (var x)) = (anf-fst x) preserves id
to-anf (fst t) with to-anf t
... | a preserves s = (anf-let a (anf-fst zero)) preserves λ where
                        (eval-let e (eval-fst (eval-var here))) → eval-fst (s e)
to-anf (snd (var x)) = (anf-snd x) preserves id
to-anf (snd t) with to-anf t
... | a preserves s = (anf-let a (anf-snd zero)) preserves λ where
                        (eval-let e (eval-snd (eval-var here))) → eval-snd (s e)
to-anf (left (var x)) = (anf-left x) preserves id
to-anf (left t) with to-anf t
... | a preserves s = (anf-let a (anf-left zero)) preserves λ where
                        (eval-let e (eval-left (eval-var here))) → eval-left (s e)
to-anf (right (var x)) = (anf-right x) preserves id
to-anf (right t) with to-anf t
... | a preserves s = (anf-let a (anf-right zero)) preserves λ where
                        (eval-let e (eval-right (eval-var here))) → eval-right (s e)
to-anf switch (var x) |left⇒ t₁ |right⇒ t₂ end with to-anf t₁ | to-anf t₂
... | a₁ preserves s₁ | a₂ preserves s₂ = (anf-switch x a₁ a₂) preserves λ where
                                            (eval-switch-left e₁ e₂) → eval-switch-left e₁ (s₁ e₂)
                                            (eval-switch-right e₁ e₂) → eval-switch-right e₁ (s₂ e₂)
to-anf switch t |left⇒ t₁ |right⇒ t₂ end with to-anf t | to-anf t₁ | to-anf t₂
... | a preserves s | a₁ preserves s₁ | a₂ preserves s₂ = (anf-let a (anf-switch zero (rename-is-anf (rshift suc) a₁) (rename-is-anf (rshift suc) a₂))) preserves λ where
                                                            (eval-let e (eval-switch-left (eval-var here) e₁)) →
                                                              eval-switch-left (s e) (s₁ (rshift-sem₁ e₁))
                                                            (eval-let e (eval-switch-right (eval-var here) e₂)) →
                                                              eval-switch-right (s e) (s₂ (rshift-sem₁ e₂))
to-anf (t₁ ； t₂) with to-anf t₁ | to-anf t₂
... | a₁ preserves s₁ | a₂ preserves s₂ = (anf-seq a₁ a₂) preserves λ where
                                            (eval-； e₁ e₂) → eval-； (s₁ e₁) (s₂ e₂)
to-anf (fun t) with to-anf t
... | a preserves s = anf-fun a preserves λ { eval-fun → {!!} }
to-anf (rec t) = {!!}
to-anf ((fun t₁) ∙ t₂) with to-anf t₁ | to-anf t₂
... | a₁ preserves s₁ | a₂ preserves s₂ = (anf-let a₂ a₁) preserves λ where
                                            (eval-let e₁ e₂) → eval-let (s₂ e₁) (s₁ e₂)
to-anf (var x ∙ var y) = (anf-app x y) preserves id
to-anf (t₁ ∙ t₂) with to-anf t₁ | to-anf t₂
... | a₁ preserves s₁ | a₂ preserves s₂ = (anf-let a₁ (anf-let (rename-is-anf suc a₂) (anf-app (suc zero) zero))) preserves λ where
                                            (eval-let e₁ (eval-let e₂ (eval-fun-app (eval-var (there here)) (eval-var here) e))) →
                                              eval-fun-app (s₁ e₁) (s₂ (rshift-sem₀ e₂)) e
                                            (eval-let e₁ (eval-let e₂ (eval-rec-app (eval-var (there here)) (eval-var here) e))) →
                                              eval-rec-app (s₁ e₁) (s₂ (rshift-sem₀ e₂)) e
to-anf (ref (var x)) = (anf-ref x) preserves id
to-anf (ref t) with to-anf t
... | a preserves s = (anf-let a (anf-ref zero)) preserves λ where
                        (eval-let e (eval-ref (eval-var here) l↪v)) → eval-ref (s e) l↪v
to-anf (! (var x)) = (anf-deref x) preserves id
to-anf (! t) with to-anf t
... | a preserves s = (anf-let a (anf-deref zero)) preserves λ where
                        (eval-let e (eval-deref (eval-var here) l↪v)) → eval-deref (s e) l↪v
to-anf (var x := var y) = (anf-assign x y) preserves id
to-anf (t₁ := t₂) with to-anf t₁ | to-anf t₂
... | a₁ preserves s₁ | a₂ preserves s₂ = (anf-let a₁ (anf-let (rename-is-anf suc a₂) (anf-assign (suc zero) zero))) preserves λ where
                                            (eval-let e₁ (eval-let e₂ (eval-assign (eval-var (there here)) (eval-var here) l↪v₁ l↪v₂))) → eval-assign (s₁ e₁) (s₂ (rshift-sem₀ e₂)) l↪v₁ l↪v₂
to-anf (free (var x)) = (anf-free x) preserves id
to-anf (free t) with to-anf t
... | a preserves s = (anf-let a (anf-free zero)) preserves λ where
                        (eval-let e (eval-free (eval-var here) l↪v)) → eval-free (s e) l↪v
