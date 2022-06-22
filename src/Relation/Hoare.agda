{-# OPTIONS --safe --without-K #-}
open import Relation.Ternary.Core
open import Relation.Ternary.Structures
open import Relation.Ternary.Structures.Syntax

-- The Hoare relation is defined polymorphically over Stores and
-- Terms that evaluate to values. The Store should have a ternary
-- relation and implement `IsPartialMonoid`.
module Relation.Hoare {e}
  {Term : Set} {Val : Set} {Env : Set} {Store : Set}
  (_≈_ : Store → Store → Set) (∅ : Store)
  (⟨_,_,_⟩⇊⟨_,_⟩ : Term → Env → Store → Val → Store → Set e)
  {{rel : Rel₃ Store}}
  {{isMonoid : IsPartialMonoid _≈_ rel ∅}}
  where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product using (curry; uncurry; _,_)
open import Data.Product.Nary.NonDependent using (Product; uncurryₙ)

open import Function using (const; id; _∘_)
open import Function.Nary.NonDependent using (Levels; Sets; _⇉_)

open import Level using (0ℓ; _⊔_) renaming (suc to lsuc)

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Hoare.StorePredicate Store
open import Relation.Hoare.PostCondition Store Val


-------------------------------------------------------------
-- Hoare Triples

-- A term and a store conform to a Hoare post condition if:
-- 1. The term evaluates to a value and a resulting store
-- 2. The post condition holds for the value and the store.
record Hoare (t : Term) (η : Env) (σ : Store) (Q : Post) : Set e where
  field
    {v}  : Val
    {σ′} : Store
    eval : ⟨ t , η , σ ⟩⇊⟨ v , σ′ ⟩
    post : Q v σ′

-- Hoare Triple
hoare[_⊢_]_[_] : Env → SPred → Term → Post → Set e
hoare[ η ⊢ H ] t [ Q ] = ∀ {σ} → H σ → Hoare t η σ Q

-- Separation Logic Triple
--
-- For now only defined over frames that respect the equality relation.
-- Otherwise, it is not possible to define a respect instance on the frame
-- when using this definition.
[_⊢_]_[_] : Env → SPred → Term → Post → Set (lsuc 0ℓ ⊔ e)
[ η ⊢ H ] t [ Q ] = ∀ {H′} {{frame-resp : Respect _≈_ H′}} → hoare[ η ⊢ H ✴ H′ ] t [ Q ✴+ H′ ]

[_]_[_] : SPred → Term → Post → Set (lsuc 0ℓ ⊔ e)
[ H ] t [ Q ] = ∀ {η} → [ η ⊢ H ] t [ Q ]


-------------------------------------------------------------
-- Structural Rules

private
  variable
    η : Env
    σ : Store
    P : Set
    H H′ H₁ H₁′ H₂ : SPred
    t t′ t₁ t₂ : Term
    Q Q′ Q₁ Q₂ : Post

  hoare-consequence :
      Hoare t η σ Q′
    → ∀+[ Q′ ⟹ Q ]
      -------------
    → Hoare t η σ Q
  hoare-consequence h Q′⟹Q =
    record {
        Hoare h
      ; post = Q′⟹Q (Hoare.post h)
    }

coe-triple :
    [ η ⊢ H ] t [ Q ]
  → (∀ {σ σ′} {v} → ⟨ t , η , σ ⟩⇊⟨ v , σ′ ⟩ → ⟨ t′ , η , σ ⟩⇊⟨ v , σ′ ⟩)
  → [ η ⊢ H ] t′ [ Q ]
coe-triple x f H✴H′ =
  let y = x H✴H′
  in record { Hoare y; eval = f (Hoare.eval y) }

pre-consequence :
    [ η ⊢ H′ ] t [ Q ]
  → ∀[ H ⇒ H′ ]
    ------------------
  → [ η ⊢ H ] t [ Q ]
pre-consequence x H⇒H′ H✴H′ = x (✴-monoᵣ H⇒H′ H✴H′)

post-consequence :
    [ η ⊢ H ] t [ Q′ ]
  → ∀+[ Q′ ⟹ Q ]
    -----------------
  → [ η ⊢ H ] t [ Q ]
post-consequence x Q′⇒Q H✴H′ = hoare-consequence (x H✴H′) (✴-monoᵣ Q′⇒Q)

consequence :
    ∀[ H ⇒ H′ ]
  → [ η ⊢ H′ ] t [ Q′ ]
  → ∀+[ Q′ ⟹ Q ]
    -----------------
  → [ η ⊢ H ] t [ Q ]
consequence H⇒H′ x Q′⇒Q = post-consequence (pre-consequence x H⇒H′) Q′⇒Q

frame :
    [ η ⊢ H ] t [ Q ]
    ----------------------------
  → [ η ⊢ H ✴ H′ ] t [ Q ✴+ H′ ]
frame x H✴H′✴H″ =
  let H✴H′✴H″ = ✴-assocᵣ H✴H′✴H″
      y        = x H✴H′✴H″
  in hoare-consequence y ✴-assocₗ

consequence-frame :
    [ η ⊢ H₁ ] t [ Q₁ ]
  → ∀[ H ⇒ H₁ ✴ H₂ ]
  → ∀+[ Q₁ ✴+ H₂ ⟹ Q ]
    ------------------
  → [ η ⊢ H ] t [ Q ]
consequence-frame x f g = consequence f (frame x) g

module _ {{comm : IsCommutative rel}} where
  ramified-frame :
      ∀[ H ⇒ H₁ ✴ (Q₁ ──✴ Q) ]
    → [ η ⊢ H₁ ] t [ Q₁ ]
      ------------------
    → [ η ⊢ H ] t [ Q ]
  ramified-frame f x H✴H′ =
    let H₁✴Q─✴Q′✴H′ = ✴-assocᵣ (✴-monoᵣ f H✴H′)
    in hoare-consequence (x H₁✴Q─✴Q′✴H′) (✴-monoᵣ ──✴-elim ∘ ✴-assocₗ)

exists : ∀ {A : Set} {Hof : A → SPred}
  → (∀ (x : A) → [ η ⊢ Hof x ] t [ Q ])
    -----------------------------------
  → [ η ⊢ ∃[ x ] Hof x ] t [ Q ]
exists f ((x , px) ∙⟨ sep ⟩ qx) = f x (px ∙⟨ sep ⟩ qx)

exists² : ∀ {A : Set} {Hof : A → SPred} {Qof : A → Post}
  → (∀ (x : A) → [ η ⊢ Hof x ] t [ Qof x ])
    ---------------------------------------------------------
  → [ η ⊢ ∃[ x ] Hof x ] t [ (λ v → ∃[ x ] Qof x v) ]
exists² {Qof = Qof} f ((x , px) ∙⟨ sep ⟩ qx) =
  hoare-consequence (f x (px ∙⟨ sep ⟩ qx)) (✴-monoᵣ (λ Qxv → x , Qxv))

private
  apply₁ : ∀ n {r} {a : Set} {as : Sets n ls₀}
    → (Product (suc n) (a , as) → Set r) → a → (Product n as → Set r)
  apply₁ zero f x xs = f x
  apply₁ (suc n) f x xs = f (x , xs)

  Arrows′ : ∀ n {r} (as : Sets n ls₀) → (Product n as → Set r) → Set r
  Arrows′ zero    _        b = b _
  Arrows′ (suc n) (a , as) b = (x : a) → Arrows′ n as (apply₁ n b x)

  infixr 9 _⇉′_
  _⇉′_ : ∀ {n} {r} (as : Sets n ls₀) → (Product n as → Set r) → Set r
  _⇉′_ = Arrows′ _

  curryₙ′ : ∀ n {as : Sets n ls₀} {r} {b : Product n as → Set r}
    → (∀ (ps : Product n as) → b ps) → as ⇉′ b
  curryₙ′ 0 f = f _
  curryₙ′ 1 f = f
  curryₙ′ (suc n@(suc _)) f = curryₙ′ n ∘ curry f

  uncurryₙ′ : ∀ n {as : Sets n ls₀} {r} {b : Product n as → Set r}
    → as ⇉′ b → (∀ (ps : Product n as) → b ps)
  uncurryₙ′ 0 f = const f
  uncurryₙ′ 1 f = f
  uncurryₙ′ (suc n@(suc _)) f = uncurry (uncurryₙ′ n ∘ f)

-- Nary existential rule
existsₙ : ∀ n {xs : Sets n ls₀} {H : xs ⇉ SPred}
  → (∀ (ps : Product n xs) → [ η ⊢ uncurryₙ n H ps ] t [ Q ])
    ---------------------------------------------------------
  → [ η ⊢ ∃⟨ n , H ⟩ ] t [ Q ]
existsₙ 0 f = f _
existsₙ 1 f ((x , px) ∙⟨ sep ⟩ qx) = f x (px ∙⟨ sep ⟩ qx)
existsₙ (suc n@(suc _)) f ((x , xs) ∙⟨ sep ⟩ qx) =
  let g = curryₙ′ (suc n) f
  in existsₙ n (uncurryₙ′ n (g x)) (xs ∙⟨ sep ⟩ qx)

pure : ∀ {{resp : Respect _≈_ H}}
  → (P → [ η ⊢ H ] t [ Q ])
    -------------------------
  → [ η ⊢ ⟦ P ⟧ ✴ H ] t [ Q ]
pure f p✴H✴H′ =
  let p✴H✴H′ = ✴-assocᵣ p✴H✴H′
      y      = f (✴-pure⁺ˡ p✴H✴H′)
      H✴H′   = ✴-pure⁻ˡ p✴H✴H′
  in y H✴H′

-- Special case for pure predicate without a frame.
-- Doing a right identity and then using the `pure` rule above
-- requires `IsUnique` on `Emp`.
pure-emp :
    (P → [ η ⊢ Emp ] t [ Q ])
    -------------------------
  → [ η ⊢ ⟦ P ⟧ ] t [ Q ]
pure-emp f p✴H′ = f (✴-pure⁺ˡ p✴H′) (✴-monoᵣ pure⇒ε p✴H′)


-------------------------------------------------------------
-- Convenient syntax for Hoare proof outlines
--
-- This idea is borrowed from `Relation.Binary.PropositionalEquality.≡-Reasoning`.
-- This syntax allows one to explicitly state pre and post conditions to use the
-- structural rules for Hoare triples. You can use the outline by adding the pre-
-- and postconditions that you would like to prove and leave holes in the store
-- entailments. You can start a Hoare outline proof by using the `begin` and `end`
-- syntax, which are simply the identity function. An example:
--
-- [ H ]begin
-- ...
-- [ Q ]∎
--
-- The consequence rule is split into a `pre` and `post` version, so you don't
-- have to match the consequences in the proof, which allows for easier writing
-- of proofs.
--
-- The precondition `H` in the outline is always the precondition of the triple
-- that follows. The postcondition `Q` in the outline is always the postcondition
-- of the triple after applying the weakening, except for the `frame` syntax, since
-- the frame cannot appear twice in the syntax.
--
-- See `Examples.HoareOutlines` for some examples using this syntax.

abstract
  pre-begin : (H : SPred) → [ η ⊢ H ] t [ Q ] → [ η ⊢ H ] t [ Q ]
  pre-begin H = id

  pre-id : (H : SPred) → [ η ⊢ H ] t [ Q ] → [ η ⊢ H ] t [ Q ]
  pre-id = pre-begin

  post-id : (Q : Post) → [ η ⊢ H ] t [ Q ] → [ η ⊢ H ] t [ Q ]
  post-id Q = id

  end : (Q : Post) → [ η ⊢ H ] t [ Q ] → [ η ⊢ H ] t [ Q ]
  end Q = id

  syntax pre-begin H triple =
    [ H ]begin
    triple

  syntax pre-id H triple =
    [ H ]by⟨⟩
    triple

  syntax pre-consequence {H′ = H} triple f =
    [ H ]by⟨ f ⟩
    triple

  syntax post-id Q triple =
    triple
    [ Q ]by⟨⟩

  syntax post-consequence {Q = Q} triple g =
    triple
    [ Q ]by⟨ g ⟩


  syntax frame {H = H} {Q = Q} triple =
    [ H ]frame
    triple
    [ Q ]restore

  syntax consequence-frame {H₁ = H} {Q = Q} triple f g =
    [ H ]frameby⟨ f ⟩
    triple
    [ Q ]restoreby⟨ g ⟩


  syntax exists {Hof = Hof} (λ x → triple) =
    [ Hof ]exists⟨ x ⟩
    triple

  syntax existsₙ n {H = H} f =
    [ H ]existsₙ⟨ n ⟩
    f

  syntax pure {H = H} f =
    [ H ]pure
    f

  -- Alternative syntax that does not allow for matching on pure.
  pure-syntax : ∀ {{resp : Respect _≈_ H}}
    → (P → [ η ⊢ H ] t [ Q ])
      -------------------------
    → [ η ⊢ ⟦ P ⟧ ✴ H ] t [ Q ]
  pure-syntax = pure
  syntax pure-syntax {H = H} (λ x → t) =
    [ H ]pure⟨ x ⟩
    t

  syntax pure-emp f =
    []pure-emp
    f

  -- Alternative syntax that does not allow for matching on pure.
  pure-emp-syntax :
      (P → [ η ⊢ Emp ] t [ Q ])
      -------------------------
    → [ η ⊢ ⟦ P ⟧ ] t [ Q ]
  pure-emp-syntax = pure-emp
  syntax pure-emp-syntax {H = H} (λ x → t) =
    [ H ]pure-emp⟨ x ⟩
    t

  syntax end Q triple =
    triple
    [ Q ]∎


infix 20 end
infix 10 pre-id pre-consequence exists existsₙ pure pure-syntax pure-emp pure-emp-syntax
infix 0 pre-begin


open import Reflection.AST.Term renaming (Term to AgdaTerm)
open import Relation.Ternary.Tactic.Core

{-
  Convenient syntax for automatically solving consequences with the
  help of the `Relation.Ternary.Tactic`.

  The `solver` argument is a record for the type of solver that should
  be used.

  The Term `M` should be a Structure that goes together with the given
  solver. The structure is quoted before the import for the same
  reasons as listed in `Tactic.MonoidSolver`.
-}
module ConsequenceSolver (solver : Solver) (M : AgdaTerm) where
  open import Data.Product using (proj₁)

  open import Relation.Unary using (_≐_)

  auto-pre-consequence :
      [ η ⊢ H′ ] t [ Q ]
    → {@(tactic Solver.solve-≐-macro solver M) eq : H ≐ H′}
      -----------------
    → [ η ⊢ H ] t [ Q ]
  auto-pre-consequence x {H⊆H′ , _} = pre-consequence x H⊆H′

  auto-post-consequence :
      [ η ⊢ H ] t [ Q ]
    → {@(tactic Solver.solve-∀-≐-macro solver M) eq : ∀ v → Q v ≐ Q′ v}
      ------------------
    → [ η ⊢ H ] t [ Q′ ]
  auto-post-consequence x {eq} = post-consequence x λ {v} → proj₁ (eq v)

  auto :
      [ η ⊢ H₁ ] t [ Q₁ ]
    → {@(tactic Solver.solve-≐-frame-macro solver M) pre-eq : H ≐ H₁ ✴ H₂}
    → {@(tactic Solver.solve-∀-≐-macro solver M) post-eq : ∀ v → Q₁ v ✴ H₂ ≐ Q v}
      -----------------
    → [ η ⊢ H ] t [ Q ]
  auto x {H⊆H₁✴H₂ , _} {post-eq} =
    consequence-frame x H⊆H₁✴H₂ λ {v} → proj₁ (post-eq v)

  syntax auto-pre-consequence {H′ = H} triple =
    [ H ]byauto
    triple

  syntax auto-post-consequence {Q′ = Q} triple =
    triple
    [ Q ]byauto

  syntax auto {H₁ = H₁} {Q = Q} triple =
    [ H₁ ]auto
    triple
    [ Q ]autorestore


  infix 2 auto-pre-consequence
