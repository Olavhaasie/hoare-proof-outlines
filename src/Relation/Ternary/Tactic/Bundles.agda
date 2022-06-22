{-# OPTIONS --safe --without-K #-}
module Relation.Ternary.Tactic.Bundles where

open import Data.Product using (_,_)

open import Level using (suc; _⊔_)

open import Relation.Ternary.Core using (IsUnique; Rel₃; Respect)
open import Relation.Ternary.Structures using
  ( Emptiness
  ; IsCommutative
  ; IsPartialMonoid
  ; IsPartialSemigroup
  )
open import Relation.Unary using (Pred; _≐_)
open import Relation.Unary.Properties using (≐-refl)


-- Used by the Tactic solver to solve equations on predicates.
record MonoidWithUnique a e : Set (suc (a ⊔ e)) where
  field
    Carrier        : Set a
    _≈_            : Carrier → Carrier → Set e
    rel            : Rel₃ Carrier
    unit           : Carrier

    isMonoid       : IsPartialMonoid _≈_ rel unit
    {{ isUnique }} : IsUnique _≈_ unit

  open Rel₃ rel public
  open IsPartialMonoid isMonoid public
  open Emptiness emptiness public
  open IsPartialSemigroup isSemigroup public

  -- This level is not entirely correct, but that's not important (for now).
  CPred = Pred Carrier a

  private
    variable
      x y z w : CPred


  ------------------------------------------------------------
  -- Properties of equality on predicates

  ✴-cong : x ≐ z → y ≐ w → x ✴ y ≐ z ✴ w
  ✴-cong (x⊆z , z⊆x) (y⊆w , w⊆y) = ⟨ x⊆z ⟨✴⟩ y⊆w ⟩ , ⟨ z⊆x ⟨✴⟩ w⊆y ⟩

  ✴-congˡ : y ≐ z → x ✴ y ≐ x ✴ z
  ✴-congˡ y≐z = ✴-cong ≐-refl y≐z

  ✴-congʳ : x ≐ z → x ✴ y ≐ z ✴ y
  ✴-congʳ x≐z = ✴-cong x≐z ≐-refl

  ✴-assoc : (x ✴ y) ✴ z ≐ x ✴ y ✴ z
  ✴-assoc = ✴-assocᵣ , ✴-assocₗ

  module _ {{_ : Respect _≈_ x}} where
    ✴-identityˡ : Emp ✴ x ≐ x
    ✴-identityˡ = ✴-id⁻ˡ , ✴-idˡ

    ✴-identityʳ : x ✴ Emp ≐ x
    ✴-identityʳ = ✴-id⁻ʳ , ✴-idʳ


-- Used by the Tactic solver to solve equations on predicates.
record CommutativeMonoidWithUnique a e : Set (suc (a ⊔ e)) where
  field
    Carrier        : Set a
    _≈_            : Carrier → Carrier → Set e
    rel            : Rel₃ Carrier
    unit           : Carrier

    isMonoid       : IsPartialMonoid _≈_ rel unit
    isCommutative  : IsCommutative rel
    {{ isUnique }} : IsUnique _≈_ unit

  open Rel₃ rel public
  open IsCommutative isCommutative public
  open IsPartialMonoid isMonoid public
  open Emptiness emptiness public
  open IsPartialSemigroup isSemigroup public

  monoidWithUnique : MonoidWithUnique a e
  MonoidWithUnique.Carrier monoidWithUnique = Carrier
  MonoidWithUnique._≈_ monoidWithUnique = _≈_
  MonoidWithUnique.rel monoidWithUnique = rel
  MonoidWithUnique.unit monoidWithUnique = unit
  MonoidWithUnique.isMonoid monoidWithUnique = isMonoid
  MonoidWithUnique.isUnique monoidWithUnique = isUnique

  -- This level is not entirely correct, but that's not important (for now).
  CPred = Pred Carrier a

  private
    variable
      x y z w : CPred


  ------------------------------------------------------------
  -- Properties of equality on predicates

  ✴-cong : x ≐ z → y ≐ w → x ✴ y ≐ z ✴ w
  ✴-cong (x⊆z , z⊆x) (y⊆w , w⊆y) = ⟨ x⊆z ⟨✴⟩ y⊆w ⟩ , ⟨ z⊆x ⟨✴⟩ w⊆y ⟩

  ✴-congˡ : y ≐ z → x ✴ y ≐ x ✴ z
  ✴-congˡ y≐z = ✴-cong ≐-refl y≐z

  ✴-congʳ : x ≐ z → x ✴ y ≐ z ✴ y
  ✴-congʳ x≐z = ✴-cong x≐z ≐-refl

  ✴-assoc : (x ✴ y) ✴ z ≐ x ✴ y ✴ z
  ✴-assoc = ✴-assocᵣ , ✴-assocₗ

  ✴-comm : x ✴ y ≐ y ✴ x
  ✴-comm = ✴-swap , ✴-swap

  module _ {{_ : Respect _≈_ x}} where
    ✴-identityˡ : Emp ✴ x ≐ x
    ✴-identityˡ = ✴-id⁻ˡ , ✴-idˡ

    ✴-identityʳ : x ✴ Emp ≐ x
    ✴-identityʳ = ✴-id⁻ʳ , ✴-idʳ
