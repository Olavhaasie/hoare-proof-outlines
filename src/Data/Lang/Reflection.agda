{-# OPTIONS --safe --without-K #-}
module Data.Lang.Reflection where

open import Data.Fin using (Fin; suc; zero)
open import Data.List using (_∷ʳ_; [])
open import Data.Lang.Lang hiding (Term)

open import Reflection.AST.Argument
open import Reflection.AST.Term

`there : Term → Term
`there t = con (quote there) (t ⟨∷⟩ [])

`here : Term
`here = con (quote here) []

`vhere : Term → Term
`vhere v = def (quote vhere) (v ⟨∷⟩ [])

`in-env : ∀ {n} → Fin n → Term → Term
`in-env zero = `vhere
`in-env (suc n) v = `there (`in-env n v)

`here≡ : Args Term → Term → Term
`here≡ as v≡ = def (quote here≡) (as ∷ʳ vArg v≡)

`in-env≡ : ∀ {n} → Fin n → Args Term → Term → Term
`in-env≡ zero = `here≡
`in-env≡ (suc n) as v≡ = `there (`in-env≡ n as v≡)
