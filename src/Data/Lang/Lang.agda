{-# OPTIONS --safe --without-K #-}
module Data.Lang.Lang where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Vec using (Vec; _∷_; [])

open import Level using (Level) renaming (suc to lsuc)

open import Relation.Binary.PropositionalEquality using (refl; _≡_)


private
  variable
    ℓ : Level
    L : Set ℓ
    n : ℕ

data Val (L : Set ℓ) : Set ℓ
data Term (L : Set ℓ) (n : ℕ) : Set ℓ

Env : (L : Set ℓ) → ℕ → Set ℓ
Env L = Vec (Val L)

data _[_]=_ {ℓ} {L : Set ℓ} : Env L n → Fin n → Val L → Set (lsuc ℓ) where
  here : ∀ {v} {η : Env L n}
    → (v ∷ η) [ zero ]= v
  there : ∀ {v₁} {v₂} {x} {η : Env L n}
    → η [ x ]= v₁
    → (v₂ ∷ η) [ suc x ]= v₁

-- Explicit version of `here`
vhere : ∀ {η : Env L n} (v : Val L) →  (v ∷ η) [ zero ]= v
vhere _ = here

-- Reflection version of `here`
here≡ : ∀ {v₁ v₂} {η : Env L n} → v₁ ≡ v₂ → (v₁ ∷ η) [ zero ]= v₂
here≡ refl = here

data Val L where
  clos : Env L n → Term L (suc n) → Val L
  fix : Env L n → Term L (suc (suc n)) → Val L
  loc : L → Val L
  prod : Val L × Val L → Val L
  sum : Val L ⊎ Val L → Val L
  unit : Val L

data Term L n where
  -- Variables as De Bruijn Index
  var : Fin n → Term L n

  -- Values
  val : Val L → Term L n
  ⟨_,_⟩ : Term L n → Term L n → Term L n
  fst : Term L n → Term L n
  snd : Term L n → Term L n
  left : Term L n → Term L n
  right : Term L n → Term L n

  -- Program control flow
  switch_|left⇒_|right⇒_end : Term L n → Term L (suc n) → Term L (suc n) → Term L n
  _；_ : Term L n → Term L n → Term L n

  -- Functions and application
  fun : Term L (suc n) → Term L n
  rec : Term L (suc (suc n)) → Term L n
  _∙_ : Term L n → Term L n → Term L n

  -- Mutable state
  ref  : Term L n → Term L n
  free : Term L n → Term L n
  !_   : Term L n → Term L n
  _:=_ : Term L n → Term L n → Term L n

-- Let binding syntactic sugar for writing function application.
-- Evaluates t₁ first and binds its value in t₂.
-- `let` and `in` are reserved keywords so they are prefixed with a backtick (`).
`let_`in_ : Term L n → Term L (suc n) → Term L n
`let t₁ `in t₂ = (fun t₂) ∙ t₁

-- List constructors
nil-val : Val L
nil-val = sum (inj₁ unit)

cons-val : Val L → Val L → Val L
cons-val x xs = sum (inj₂ (prod (x , xs)))

nil cons : Term L n
nil  = val nil-val
cons = fun (fun (`let ⟨ var (suc zero) , var zero ⟩ `in right (var zero)))

-- unit ∷ unit ∷ []
_ : Term L 0
_ = cons ∙ val unit ∙ (cons ∙ val unit ∙ nil)

-- Tree constructors
leaf node : Term L n
leaf = val (sum (inj₁ unit))
node = fun (fun (fun (right ⟨ var (suc (suc zero)) , ⟨ var (suc zero) , var zero ⟩ ⟩)))

{-
      unit
     /    \
   unit    .
   /  \
  .    .
-}
_ : Term L 0
_ = node ∙ val unit ∙ (node ∙ val unit ∙ leaf ∙ leaf) ∙ leaf


infix 11 loc prod sum
infix  9 val var ref !_ free
infix  8 fst snd left right
infixl 7 _∙_
infix  6 _:=_
infixr 5 _；_
infix  4 `let_`in_
