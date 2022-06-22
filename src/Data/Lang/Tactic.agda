{-# OPTIONS --safe --without-K #-}
module Data.Lang.Tactic where

open import Data.Fin using (Fin; suc; zero)
open import Data.List as L using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Lang.Lang hiding (Term)
open import Data.Lang.Reflection
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Vec using (_∷_; [])

open import Function using (_$_)

open import Level using (0ℓ)

open import Reflection.AST.Argument
open import Reflection.AST.Term
open import Reflection.TCM
open import Reflection.TCM.Syntax

open import Relation.Binary.PropositionalEquality using (erefl; refl; _≡_)


private
  get-env-args : Args Term → Maybe (Args Term × Term × Term × Term × Term)
  get-env-args = go L.[]
    where
      go : Args Term → Args Term → Maybe (Args Term × Term × Term × Term × Term)
      go as (n ⟅∷⟆ η ⟨∷⟩ x ⟨∷⟩ v ⟨∷⟩ L.[]) = just $ as , n , η , x , v
      go as (x L.∷ xs) = go (as L.∷ʳ x) xs
      go _ _ = nothing

  choice : ∀ {A : Set} → List A → (ℕ → A → TC ⊤) → TC ⊤
  choice = go 0
    where
      go : ∀ {A : Set} → ℕ → List A → (ℕ → A → TC ⊤) → TC ⊤
      go n L.[] f = typeErrorFmt "Failed to find equality in context"
      go n (x L.∷ xs) f = f n x <|> go (suc n) xs f

blockIfMeta : Term → TC ⊤
blockIfMeta (meta x _) = blockOnMeta x
blockIfMeta t = pure _

var-macro : Term → Term → TC ⊤
var-macro `v hole = do
  (def (quote _[_]=_) as) ← inferType hole >>= reduce
    where h → typeErrorFmt "goal is not _[_]=_: %t" h
  just (as , `n , `η , `x , `r) ← pure $ get-env-args as
    where nothing → typeErrorFmt "Incorrect arguments to _[_]=_"
  unify `v `r
  commitTC
  blockIfMeta `x
  n ← unquoteTC {A = ℕ} `n
  x ← unquoteTC {A = Fin n} `x
  -- First try to construct from x, perhaps the terms are already equal.
  (unify hole (`in-env x `v)) <|> do
  -- Else, try to find an equality of the result in the context.
    ctx ← L.map unArg <$> getContext
    choice ctx λ where
      i a@(def (quote _≡_) (_ ⟅∷⟆ _ ⟅∷⟆ _ ⟨∷⟩ `v₁ ⟨∷⟩ L.[])) → do
        unify hole (`in-env≡ x as (var i L.[]))
      _ a → do
        typeErrorFmt "Argument in environment is not _≡_: %t" a

macro
  var! = var-macro
  var? = var-macro unknown

private
  variable
    L : Set
    n : ℕ

  test₀ : ∀ {v₁ v₂ : Val L} → (v₁ ∷ v₂ ∷ []) [ suc zero ]= v₂
  test₀ {v₁ = v₁} {v₂ = v₂} = var? -- var! v₂

  test₁ : ∀ (v₁ v₂ v₃ : Val L) → v₂ ≡ v₁ → v₃ ≡ v₁ → (η : Env L n) → (v₁ ∷ v₂ ∷ v₃ ∷ η) [ suc zero ]= v₁
  test₁ v₁ v₂ v₃ eq₁ eq₂ _ = var! v₁
