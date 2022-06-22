{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Tactic.Expression where

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; _≟_; suc; zero)
open import Data.List using (List) using (_++_; [_]; _∷_; [])
open import Data.List.Properties using () renaming (≡-dec to list-≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; _×_; ∃)
open import Data.Vec as V using (Vec; lookup; toList)

open import Function using (_$_)

open import Level using (0ℓ)

open import Reflection.AST.Argument hiding (map)
open import Reflection.AST.DeBruijn using (strengthenBy)
open import Reflection.AST.Term hiding (_≟_)
open import Reflection.TCM
open import Reflection.TCM.Syntax

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (does)
open import Relation.Ternary.Core using (Rel₃)
open import Relation.Ternary.Tactic.Error
open import Relation.Ternary.Tactic.Util

-- Import `for` a `Vec` in `TC` monad
module _ {n} where
  import Data.Vec.Effectful as VEffect
  open import Reflection.TCM.Effectful using (applicative)
  open VEffect.TraversableA {0ℓ} {n} (applicative {0ℓ}) using (forA) public


-- Predicate expressions consist of the separating conjunction and
-- empty predicate. All other predicates are represented by variables.
data Expr (n : ℕ) : Set where
  _✴′_  : Expr n → Expr n → Expr n
  ε′    : Expr n
  [_↑]  : Fin n → Expr n

private
  variable
    n m : ℕ


-------------------------------------------------------------
-- Normal form

-- The normal form is represented as a list of atoms.
NF : ℕ → Set
NF n = List (Fin n)

-- Convert an expression to normal form, i.e. flatten it.
norm : Expr n → NF n
norm (x ✴′ y) = norm x ++ norm y
norm ε′ = []
norm [ x ↑] = [ x ]

-- Evaluate a normal form to an expression.
nf-to-expr : NF n → Expr n
nf-to-expr [] = ε′
nf-to-expr (x ∷ xs) = [ x ↑] ✴′ nf-to-expr xs

-- Decidable equality on normal forms is decided by the decidable
-- equality on lists and finite natural numbers.
nf-≡-dec : DecidableEquality (NF n)
nf-≡-dec = list-≡-dec _≟_


-------------------------------------------------------------
-- Expression transformations

-- Map the atoms of an expression.
map : (Fin n → Fin m) → Expr n → Expr m
map f (x ✴′ y) = map f x ✴′ map f y
map f ε′ = ε′
map f [ x ↑] = [ f x ↑]

-- Resizes all atoms in the expression by m, keeping the value of the
-- finite value.
resize : Expr n → Expr (n + m)
resize = map $ _↑ˡ _

-- Shifts all atoms in the expression by m.
shift : Expr n → Expr (m + n)
shift = map $ _ ↑ʳ_

-- A parsed expression consists of the expression and an environment,
-- which maps the atoms from the expression to the actual predicates.
Parsed = ∃ λ n → Expr n × Vec Term n

-- Remap all atoms in the expression with a given remapping.
remap : Vec (Fin m) n → Expr n → Expr m
remap v = map $ lookup v

-- Try to find a term in an environment and return its index.
index : Vec Term n → Term → TC (Maybe (Fin n))
index V.[] t = pure nothing
index (x V.∷ xs) t = (just zero <$ unify x t) <|> (may suc <$> index xs t)
  where open Data.Maybe using () renaming (map to may)

-- Try to remap a parsed expression to a given environment, so the
-- environment indexes the returned expression.
align : Parsed → Vec Term m → TC (Expr m)
align (n , x , env) env′ = do
  m ← forA {n} env $ λ t → do
    just i ← index env′ t
      where nothing → envError t $ toList env′
    pure i
  pure $ remap m x


-------------------------------------------------------------
-- Expression parsing

open Rel₃

private
  `Set : Term
  `Set = def (quote Set) (unknown ⟨∷⟩ [])

  atom : Term → Parsed
  atom t = 1 , [ zero ↑] , V.[ t ]

  parse′ : ℕ → Term → TC Parsed
  parse′ by t@(def (quote Conj) xs) = parse-conj xs
    where
      parse-conj : Args Term → TC Parsed
      parse-conj (x ⟨∷⟩ (hLam _ (vLam _ y)) ⟨∷⟩ _) = do
        n₁ , x , env₁ ← parse′ by x
        n₂ , y , env₂ ← parse′ (2 + by) y
        pure $ n₁ + n₂ , resize x ✴′ shift y , env₁ V.++ env₂
      parse-conj (_ ∷ xs) = parse-conj xs
      parse-conj _ = buildError t
  parse′ by (def (quote _≡_) xs) = pure $ 0 , ε′ , V.[]
  parse′ by t@(def n xs) = do
    just t@(def n xs) ← pure $ strengthenBy by t
      where _ → buildError t
    catchTC
      -- First try Set type,
      -- then remove the last argument to make it a predicate
      ((atom $ def n (init xs)) <$ checkType t `Set)
      -- Else assume it is a predicate
      (pure $ atom t)
  parse′ by t@(var x xs) = do
    just t@(var x xs) ← pure $ strengthenBy by t
      where _ → buildError t
    catchTC
      -- First try Set type,
      -- then remove the last argument to make it a predicate
      ((atom $ var x (init xs)) <$ checkType t `Set)
      -- Else assume it is a predicate
      (pure $ atom t)
  parse′ _ (meta m _) = blockOnMeta m
  parse′ by t = do
    just t ← pure $ strengthenBy by t
      where nothing → buildError t
    pure $ atom t

-- Parse a predicate expression to the represented expression syntax.
parse : Term → TC Parsed
parse = parse′ 0

-- First normalise the expression then parse it.
nparse : Term → TC Parsed
nparse t = normalise t >>= parse
