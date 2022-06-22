{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Tactic.Bundles

module Relation.Ternary.Tactic.Expression.Properties {a e}
  (monoid : MonoidWithUnique a e)
  where
open MonoidWithUnique monoid

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.List using (_++_; _∷_; [])

open import Level using (_⊔_) renaming (suc to lsuc)

open import Relation.Ternary.Core using (Respect; unique-respects)

open import Relation.Unary using (_≐_)
open import Relation.Unary.Properties using (≐-refl)
open import Relation.Unary.Relation.Binary.Equality using (≐-setoid)

open import Relation.Binary.Reasoning.Setoid (≐-setoid Carrier a)

open import Relation.Ternary.Tactic.Expression


private
  variable
    n : ℕ

-------------------------------------------------------------
-- Environment

-- The environment that keeps a relation between the variables in an
-- expression and its actual value. All predicates in the
-- environment must implement `Respect _≈_`.
data Env : ℕ → Set (lsuc (a ⊔ e)) where
  []ⁿ  : Env zero
  _∷ⁿ_ : ∀ (x : CPred) {{resp : Respect _≈_ x}} (xs : Env n) → Env (suc n)

infixr 7 _∷ⁿ_

lookup : Env n → Fin n → CPred
lookup (x ∷ⁿ xs) zero    = x
lookup (x ∷ⁿ xs) (suc i) = lookup xs i

-- Lookup respects ≈, since every predicate in the list also respects ≈.
lookup-respects-≈ : ∀ (ρ : Env n) {x : Fin n} → Respect _≈_ (lookup ρ x)
lookup-respects-≈ (_∷ⁿ_ x ⦃ resp ⦄ _) {zero}  = resp
lookup-respects-≈ (_ ∷ⁿ ρ)            {suc _} = lookup-respects-≈ ρ


-------------------------------------------------------------
-- Evaluation

-- Converts an expression to a predicate (i.e. evaluates it) without
-- normalising.
[_↓]_ : Expr n → Env n → CPred
[ x ✴′ y ↓] ρ = [ x ↓] ρ ✴ [ y ↓] ρ
[ ε′     ↓] ρ = Emp
[ [ x ↑] ↓] ρ = lookup ρ x

-- Evaluate a normal form.  The list is evaluated by converting to an
-- expression and then evaluating the expression. For example, the
-- normal form [1, 0, 2] and environment [y, x, z] become:
--   x ✴ y ✴ z ✴ Emp
[_⇓]_ : NF n → Env n → CPred
[ nf ⇓] ρ = [ nf-to-expr nf ↓] ρ

[⇓]-respects-≈ : ∀ (nf : NF n) (ρ : Env n) → Respect _≈_ ([ nf ⇓] ρ)
[⇓]-respects-≈ []      ρ = unique-respects
[⇓]-respects-≈ (_ ∷ _) ρ = ✴-respect-≈


-------------------------------------------------------------
-- Homomorphisms

++-homo : ∀ (xs ys : NF n) (ρ : Env n)
  → [ xs ++ ys ⇓] ρ ≐ [ xs ⇓] ρ ✴ [ ys ⇓] ρ
++-homo [] ys ρ = begin
  [ [] ++ ys ⇓] ρ       ≡⟨⟩
  [ ys ⇓] ρ             ≈˘⟨ ✴-identityˡ ⦃ [⇓]-respects-≈ ys ρ ⦄ ⟩
  Emp ✴ [ ys ⇓] ρ       ≡⟨⟩
  [ [] ⇓] ρ ✴ [ ys ⇓] ρ ∎
++-homo (x ∷ xs) ys ρ = begin
  [ (x ∷ xs) ++ ys ⇓] ρ                ≡⟨⟩
  [ x ∷ (xs ++ ys) ⇓] ρ                ≡⟨⟩
  lookup ρ x ✴ [ (xs ++ ys) ⇓] ρ       ≈⟨ ✴-congˡ (++-homo xs ys ρ) ⟩
  lookup ρ x ✴ [ xs ⇓] ρ ✴ [ ys ⇓] ρ   ≈˘⟨ ✴-assoc ⟩
  (lookup ρ x ✴ [ xs ⇓] ρ) ✴ [ ys ⇓] ρ ≡⟨⟩
  [ x ∷ xs ⇓] ρ ✴ [ ys ⇓] ρ            ∎

norm-homo : ∀ (x : Expr n) (ρ : Env n) → [ norm x ⇓] ρ ≐ [ x ↓] ρ
norm-homo ε′ η = ≐-refl
norm-homo [ x ↑] ρ = ✴-identityʳ ⦃ lookup-respects-≈ ρ ⦄
norm-homo (x ✴′ y) ρ = begin
  [ norm (x ✴′ y) ⇓] ρ          ≡⟨⟩
  [ norm x ++ norm y ⇓] ρ       ≈⟨ ++-homo (norm x) (norm y) ρ ⟩
  [ norm x ⇓] ρ ✴ [ norm y ⇓] ρ ≈⟨ ✴-cong (norm-homo x ρ) (norm-homo y ρ) ⟩
  [ x ↓] ρ ✴ [ y ↓] ρ           ≡⟨⟩
  [ x ✴′ y ↓] ρ                 ∎

Solution : Expr n → Expr n → Set (lsuc (a ⊔ e))
Solution x y = ∀ ρ → [ x ↓] ρ ≐ [ y ↓] ρ

FrameSolution : Expr n → Expr n → Expr n → Set (lsuc (a ⊔ e))
FrameSolution x y z = Solution x (y ✴′ z)
