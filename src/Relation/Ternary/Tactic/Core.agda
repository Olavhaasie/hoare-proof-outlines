{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Tactic.Core where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤ᵇ_)
open import Data.List using (List; _∷_; [])
open import Data.Product using (proj₁; _,_)
open import Data.Unit using (⊤)

open import Function using (_$_; _⟨_⟩_)

open import Reflection.AST
open import Reflection.AST.DeBruijn using (weaken)
open import Reflection.AST.Term using (hLam; vLam)
open import Reflection.AST.Argument
open import Reflection.TCM
open import Reflection.TCM.Syntax

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (Dec; no; yes)
open import Relation.Ternary.Core using (Rel₃)

open import Relation.Ternary.Tactic.Error
open import Relation.Ternary.Tactic.Expression
open import Relation.Ternary.Tactic.Expression.Properties
open import Relation.Ternary.Tactic.Reflection
open import Relation.Ternary.Tactic.Util


MonoidTactic = (monoid : Term) → (hole : Term) → TC ⊤

private
  variable
    n : ℕ

record Solver : Set₁ where
  field
    -- Normalise an expression
    _⇓ : Expr n → NF n
    -- Decidable order on expressions to determine a frame.
    _∼_ : NF n → NF n → Set
    _∼?_ : ∀ (x y : NF n) → Dec (x ∼ y)
    -- Quoted names of the solvers
    solver : Name
    frame-solver : Name
    -- Quoted type of the monoid
    monoidType : Type

  -- Decidable equality on normalised expressions.
  expr-≡-dec : Decidable {A = Expr n} λ x y → x ⇓ ≡ y ⇓
  expr-≡-dec x y = nf-≡-dec (x ⇓) (y ⇓)

  -- Constructs a call to the solver.
  `solve : Term → Term → Term → Term → Term → Term
  `solve `mon `lhs `rhs `nf≡ `env = solver ⟨ def ⟩ `mon ⟨∷⟩ `lhs ⟨∷⟩ `rhs ⟨∷⟩ `nf≡ ⟨∷⟩ `env ⟨∷⟩ []

  `solve-frame : Term → Term → Term → Term → Term → Term
  `solve-frame `mon `lhs `rhs `rhs⊆lhs `env = frame-solver ⟨ def ⟩ `mon ⟨∷⟩ `lhs ⟨∷⟩ `rhs ⟨∷⟩ `rhs⊆lhs ⟨∷⟩ `env ⟨∷⟩ []

  -- Constructs a proof of type `x ≐ y`
  solve-≐-macro : MonoidTactic
  solve-≐-macro `mon hole = do
    _ ← checkType `mon monoidType
    commitTC
    `hole ← inferType hole
    just (lhs , rhs) ← pure $ ≐-getArgs `hole
      where nothing → malformed-≐ `hole
    nₗ , lhs , envₗ ← nparse lhs
    nᵣ , rhs , envᵣ ← nparse rhs
    yes refl ← pure $ nₗ ≟ nᵣ
      where no _ → envLengthError nₗ nᵣ
    rhs ← align (nᵣ , rhs , envᵣ) envₗ
    `lhs ← quoteTC lhs
    `rhs ← quoteTC rhs
    yes nf≡ ← pure $ expr-≡-dec lhs rhs
      where no _ → envNormError `lhs `rhs
    `nf≡ ← quoteTC nf≡
    let solution = `solve `mon `lhs `rhs `nf≡ (`env envₗ)
    unify solution hole

  -- Constructs a proof of type `∀ a → x a ≐ y a`
  solve-∀-≐-macro : MonoidTactic
  solve-∀-≐-macro `mon hole = do
    _ ← checkType `mon monoidType
    commitTC
    `hole ← inferType hole
    just (v , ty , eq) ← pure $ stripPi `hole
      where nothing → malformed-∀ `hole
    just (lhs , rhs) ← pure $ ≐-getArgs eq
      where nothing → malformed-∀-≐ eq
    -- Normalise the expression in an extended context so the DeBruijn
    -- indices will be correct.
    nₗ , lhs , envₗ ← extendContext ty $ nparse lhs
    nᵣ , rhs , envᵣ ← extendContext ty $ nparse rhs
    yes refl ← pure $ nₗ ≟ nᵣ
      where no _ → envLengthError nₗ nᵣ
    rhs ← extendContext ty $ align (nᵣ , rhs , envᵣ) envₗ
    `lhs ← quoteTC lhs
    `rhs ← quoteTC rhs
    yes nf≡ ← pure $ expr-≡-dec lhs rhs
      where no _ → envNormError `lhs `rhs
    `nf≡ ← quoteTC nf≡
    -- The DeBruijn index for the monoid instance needs to be
    -- increased, since we prepend the solution with a lambda.
    let solution = vLam v $ `solve (weaken 1 `mon) `lhs `rhs `nf≡ (`env envₗ)
    unify solution hole

  -- Constructs a proof of type `x ≐ y ✴ _`.
  -- Where `_` will be deduced from `x` and `y`.
  solve-≐-frame-macro : MonoidTactic
  solve-≐-frame-macro `mon hole = do
    _ ← checkType `mon monoidType
    commitTC
    `hole ← inferType hole
    just (lhs , rhs) ← pure $ ≐-getArgs `hole
      where _ → malformed-≐-✴ `hole
    let open Rel₃ using (Conj)
    def (quote Conj) xs ← normalise rhs
      where _ → malformed-✴ rhs
    rhs ∷ (hLam _ (vLam _ (meta _ _))) ∷ [] ← pure $ last 2 xs
      where _ → malformed-✴ rhs
    nₗ , lhs , envₗ ← nparse lhs
    nᵣ , rhs , envᵣ ← parse rhs
    true ← pure $ nᵣ ≤ᵇ nₗ
      where false → envGreaterLengthError nᵣ nₗ
    rhs ← align (nᵣ , rhs , envᵣ) envₗ
    `lhs ← quoteTC lhs
    `rhs ← quoteTC rhs
    yes rhs⊆lhs ← pure $ (rhs ⇓) ∼? (lhs ⇓)
      where no _ → no-frame `lhs `rhs
    `rhs⊆lhs ← quoteTC rhs⊆lhs
    let solution = `solve-frame `mon `lhs `rhs `rhs⊆lhs (`env envₗ)
    unify solution hole

  solve-⊆-macro : MonoidTactic
  solve-⊆-macro `mon hole = do
    _ ← checkType `mon monoidType
    commitTC
    `hole ← inferType hole >>= normalise
    just (lhs , rhs) ← pure $ ⇒-getArgs `hole
      where nothing → malformed-⊆ `hole
    nₗ , lhs , envₗ ← parse lhs
    nᵣ , rhs , envᵣ ← parse rhs
    yes refl ← pure $ nₗ ≟ nᵣ
      where no _ → envLengthError nₗ nᵣ
    rhs ← align (nᵣ , rhs , envᵣ) envₗ
    `lhs ← quoteTC lhs
    `rhs ← quoteTC rhs
    yes nf≡ ← pure $ expr-≡-dec lhs rhs
      where no _ → envNormError `lhs `rhs
    `nf≡ ← quoteTC nf≡
    let eq = `solve `mon `lhs `rhs `nf≡ (`env envₗ)
    let solution = quote proj₁ ⟨ def ⟩ eq ⟨∷⟩ []
    unify hole solution

  macro
    solve       = solve-≐-macro
    solve-∀     = solve-∀-≐-macro
    solve-frame = solve-≐-frame-macro
    solve-⊆     = solve-⊆-macro
