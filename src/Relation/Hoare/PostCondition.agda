{-# OPTIONS --safe --without-K #-}
module Relation.Hoare.PostCondition (S : Set) (V : Set) where

open import Relation.Hoare.StorePredicate S
open import Relation.Ternary.Core
open import Relation.Ternary.Structures.Commutative

-- Post condition, a store predicate with a term
Post : Set₁
Post = V → SPred

-- Post condition impliciation
_⟹_ : Post → Post → Post
(Q ⟹ Q′) v = Q v ⇒ Q′ v

-- Universally quantify over post conditions
∀+[_] : Post → Set
∀+[ Q ] = ∀ {v} → ∀[ Q v ]

-- Embeds a store predicate in a post condition
+_ : SPred → Post
(+ H) _ = H

infixr 8 _⟹_
infix  7 +_

module _ {{rel : Rel₃ S}} where
  open Rel₃ rel

  -- Product of a post condition and a store predicate
  _✴+_ : Post → SPred → Post
  (Q ✴+ H) v = Q v ✴ H

  -- Magic wand for post conditions
  _──✴_ : Post → Post → SPred
  (Q ──✴ Q′) σ = ∀ v → (Q v ─✴ Q′ v) σ

  infixr 9 _✴+_
  infixr 8 _──✴_


  module _ {{comm : IsCommutative rel}} where
    open IsCommutative comm

    ──✴-elim : ∀ {v} {Q₁ Q₂}
      → ∀[ Q₁ v ✴ (Q₁ ──✴ Q₂) ⇒ Q₂ v ]
    ──✴-elim {v} (px ∙⟨ sep ⟩ f) = f v ⟨ ∙-comm sep ⟩ px
