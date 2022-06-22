{-# OPTIONS --safe --without-K #-}
open import Data.Lang.Lang

open import Relation.Hoare.Bundles

module Data.Lang.Hoare (S : Store Val) where

open Store S hiding (_∙_)

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Lang.Semantics S
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Vec using (_∷_)

open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Hoare.PostCondition Carrier (Val L) public


module _ {n : ℕ} where
  open import Relation.Hoare _≈_ ∅ (⟨_,_,_⟩⇊⟨_,_⟩ {n = n}) public


private
  variable
    n : ℕ
    x y : Fin _
    η η′ : Env L _
    H H′ H₁ H₂ : SPred
    t t₁ t₂ : Term L _
    v v′ v₁ v₂ : Val L
    Q Q′ : Post


-------------------------------------------------------------
-- Term Rules

val-triple :
    ∀[ H ⇒ Q v ]
    ---------------------
  → [ η ⊢ H ] val v [ Q ]
val-triple f H✴H′ = record { eval = eval-val ; post = ✴-monoᵣ f H✴H′ }

-- Transform a value triple to small footprint
to-sf :
    (∀ {H} {Q} → ∀[ H ⇒ Q v ] → [ η ⊢ H ] t [ Q ])
    ----------------------------------------------
  → [ η ⊢ Emp ] t [ (λ w → ⟦ w ≡ v ⟧) ]
to-sf f = f (ε⇒pure refl)

-- Small footprint version of value triple
val-triple′ :
    ---------------------------------------
    [ η ⊢ Emp ] val v [ (λ w → ⟦ w ≡ v ⟧) ]
val-triple′ = to-sf val-triple

var-triple :
    η [ x ]= v
  → ∀[ H ⇒ Q v ]
    ---------------------
  → [ η ⊢ H ] var x [ Q ]
var-triple x∈η f H✴H′ = record { eval = eval-var x∈η ; post = ✴-monoᵣ f H✴H′ }

-- Small footprint version of var triple
var-triple′ :
    η [ x ]= v
    ---------------------------------------
  → [ η ⊢ Emp ] var x [ (λ w → ⟦ w ≡ v ⟧) ]
var-triple′ x∈η = to-sf (var-triple x∈η)

fun-triple :
    ∀[ H ⇒ Q (clos η t) ]
    ---------------------
  → [ η ⊢ H ] fun t [ Q ]
fun-triple f H✴H′ = record { eval = eval-fun ; post = ✴-monoᵣ f H✴H′ }

-- Small footprint version of fun triple
fun-triple′ :
    ----------------------------------------------
    [ η ⊢ Emp ] fun t [ (λ w → ⟦ w ≡ clos η t ⟧) ]
fun-triple′ = to-sf fun-triple

rec-triple :
    ∀[ H ⇒ Q (fix η t) ]
    ---------------------
  → [ η ⊢ H ] rec t [ Q ]
rec-triple f H✴H′ = record { eval = eval-rec ; post = ✴-monoᵣ f H✴H′ }

-- Small footprint version of fun triple
rec-triple′ :
    ---------------------------------------------
    [ η ⊢ Emp ] rec t [ (λ w → ⟦ w ≡ fix η t ⟧) ]
rec-triple′ = to-sf rec-triple

prod-triple :
    η [ x ]= v₁
  → η [ y ]= v₂
  → ∀[ H ⇒ Q (prod (v₁ , v₂))]
    ---------------------------------
  → [ η ⊢ H ] ⟨ var x , var y ⟩ [ Q ]
prod-triple x∈η y∈η f H✴H′ =
  record {
      eval = eval-prod (eval-var x∈η) (eval-var y∈η)
    ; post = ✴-monoᵣ f H✴H′
  }

prod-triple′ :
    η [ x ]= v₁
  → η [ y ]= v₂
    ----------------------------------------------------------------
  → [ η ⊢ Emp ] ⟨ var x , var y ⟩ [ (λ w → ⟦ w ≡ prod (v₁ , v₂) ⟧) ]
prod-triple′ x∈η y∈η = to-sf (prod-triple x∈η y∈η)

fst-triple :
    η [ x ]= prod (v₁ , v₂)
  → ∀[ H ⇒ Q v₁ ]
    ---------------------------
  → [ η ⊢ H ] fst (var x) [ Q ]
fst-triple x∈η f H✴H′ =
  record {
      eval = eval-fst (eval-var x∈η)
    ; post = ✴-monoᵣ f H✴H′
  }

fst-triple′ :
    η [ x ]= prod (v₁ , v₂)
    ----------------------------------------------
  → [ η ⊢ Emp ] fst (var x) [ (λ w → ⟦ w ≡ v₁ ⟧) ]
fst-triple′ x∈η = to-sf (fst-triple x∈η)

snd-triple :
    η [ x ]= prod (v₁ , v₂)
  → ∀[ H ⇒ Q v₂ ]
    ---------------------------
  → [ η ⊢ H ] snd (var x) [ Q ]
snd-triple x∈η f H✴H′ =
  record {
      eval = eval-snd (eval-var x∈η)
    ; post = ✴-monoᵣ f H✴H′
  }

snd-triple′ :
    η [ x ]= prod (v₁ , v₂)
    ----------------------------------------------
  → [ η ⊢ Emp ] snd (var x) [ (λ w → ⟦ w ≡ v₂ ⟧) ]
snd-triple′ x∈η = to-sf (snd-triple x∈η)

left-triple :
    η [ x ]= v
  → ∀[ H ⇒ Q (sum (inj₁ v)) ]
    ----------------------------
  → [ η ⊢ H ] left (var x) [ Q ]
left-triple x∈η f H✴H′ =
  record {
      eval = eval-left (eval-var x∈η)
    ; post = ✴-monoᵣ f H✴H′
  }

left-triple′ :
    η [ x ]= v
    ---------------------------------------------------------
  → [ η ⊢ Emp ] left (var x) [ (λ w → ⟦ w ≡ sum (inj₁ v) ⟧) ]
left-triple′ x∈η = to-sf (left-triple x∈η)

right-triple :
    η [ x ]= v
  → ∀[ H ⇒ Q (sum (inj₂ v)) ]
    -----------------------------
  → [ η ⊢ H ] right (var x) [ Q ]
right-triple x∈η f H✴H′ =
  record {
      eval = eval-right (eval-var x∈η)
    ; post = ✴-monoᵣ f H✴H′
  }

right-triple′ :
    η [ x ]= v
    ----------------------------------------------------------
  → [ η ⊢ Emp ] right (var x) [ (λ w → ⟦ w ≡ sum (inj₂ v) ⟧) ]
right-triple′ x∈η = to-sf (right-triple x∈η)


let-triple :
    [ η ⊢ H ] t₁ [ Q′ ]
  → (∀ v → [ v ∷ η ⊢ Q′ v ] t₂ [ Q ])
    ---------------------------------
  → [ η ⊢ H ] `let t₁ `in t₂ [ Q ]
let-triple x₁ x₂ H✴H′ =
  let y₁ = x₁ H✴H′
      y₂ = x₂ (Hoare.v y₁) (Hoare.post y₁)
  in record { Hoare y₂ ;
       eval = eval-fun-app eval-fun (Hoare.eval y₁) (Hoare.eval y₂)
     }

clos-app-triple :
    η [ x ]= clos η′ t
  → η [ y ]= v
  → [ v ∷ η′ ⊢ H ] t [ Q ]
    ---------------------------------
  → [ η ⊢ H ] (var x) ∙ (var y) [ Q ]
clos-app-triple x∈η y∈η x₁ H✴H′ =
  let y₁ = x₁ H✴H′
  in record { Hoare y₁ ;
       eval = eval-fun-app (eval-var x∈η) (eval-var y∈η) (Hoare.eval y₁)
     }

-- Special case of function application to prove a triple of a body of a unary function.
fun-app₁-triple :
    [ v ∷ η ⊢ H ] t₁ [ Q ]
    ----------------------------------
  → [ η ⊢ H ] (fun t₁) ∙ (val v) [ Q ]
fun-app₁-triple x₁ H✴H′ =
  let y₁ = x₁ H✴H′
  in record { Hoare y₁ ;
       eval = eval-fun-app eval-fun eval-val (Hoare.eval y₁)
     }

-- Special case of function application to prove a triple of a body of a binary function.
fun-app₂-triple :
    [ v₂ ∷ v₁ ∷ η ⊢ H ] t [ Q ]
    ---------------------------------------------------
  → [ η ⊢ H ] (fun (fun t)) ∙ (val v₁) ∙ (val v₂) [ Q ]
fun-app₂-triple x₁ H✴H′ =
  let y₁ = x₁ H✴H′
  in record { Hoare y₁ ;
       eval = eval-fun-app (eval-fun-app eval-fun eval-val eval-fun) eval-val (Hoare.eval y₁)
     }

fix-app-triple :
    η [ x ]= fix η′ t
  → η [ y ]= v
  → [ v ∷ fix η′ t ∷ η′ ⊢ H ] t [ Q ]
    ---------------------------------
  → [ η ⊢ H ] (var x) ∙ (var y) [ Q ]
fix-app-triple x∈η y∈η x₁ H✴H′ =
  let y₁ = x₁ H✴H′
  in record { Hoare y₁ ;
       eval = eval-rec-app (eval-var x∈η) (eval-var y∈η) (Hoare.eval y₁)
     }

-- Special case of rec application to prove a triple of a body of a
-- unary recursive function.
rec-app₁-triple :
    [ v ∷ fix η t ∷ η ⊢ H ] t [ Q ]
    ---------------------------------
  → [ η ⊢ H ] (rec t) ∙ (val v) [ Q ]
rec-app₁-triple x₁ H✴H′ =
  let y₁ = x₁ H✴H′
  in record { Hoare y₁ ;
       eval = eval-rec-app eval-rec eval-val (Hoare.eval y₁)
     }

rec-app₂-triple :
    [ v₂ ∷ v₁ ∷ fix η (fun t) ∷ η ⊢ H ] t [ Q ]
    -------------------------------------------------
  → [ η ⊢ H ] (rec (fun t)) ∙ (val v₁) ∙ (val v₂) [ Q ]
rec-app₂-triple x₁ H✴H′ =
  let y₁ = x₁ H✴H′
  in record { Hoare y₁ ;
       eval = eval-fun-app (eval-rec-app eval-rec eval-val eval-fun) eval-val (Hoare.eval y₁)
     }

sequence :
    [ η ⊢ H ] t₁ [ + H₁ ]
  → [ η ⊢ H₁ ] t₂ [ Q ]
    ------------------------
  → [ η ⊢ H ] t₁ ； t₂ [ Q ]
sequence x₁ x₂ H✶H′ =
  let y₁ = x₁ H✶H′
      y₂ = x₂ (Hoare.post y₁)
  in record { Hoare y₂ ; eval = eval-； (Hoare.eval y₁) (Hoare.eval y₂) }

switch-triple : ∀ {v}
 → η [ x ]= sum v
 → (∀ {v₁} → v ≡ inj₁ v₁ → [ v₁ ∷ η ⊢ H ] t₁ [ Q ])
 → (∀ {v₂} → v ≡ inj₂ v₂ → [ v₂ ∷ η ⊢ H ] t₂ [ Q ])
   ------------------------------------------------
 → [ η ⊢ H ]
     switch (var x)
       |left⇒  t₁
       |right⇒ t₂
     end
   [ Q ]
switch-triple {v = inj₁ v₁} x∈η x₁ _ H✴H′ =
  let y₁ = x₁ refl H✴H′
  in record { Hoare y₁ ;
       eval = eval-switch-left (eval-var x∈η) (Hoare.eval y₁)
     }
switch-triple {v = inj₂ v₂} x∈η _ x₂ H✴H′ =
  let y₂ = x₂ refl H✴H′
  in record { Hoare y₂ ;
       eval = eval-switch-right (eval-var x∈η) (Hoare.eval y₂)
     }

nil-triple :
    -------------------------------------------
    [ η ⊢ Emp ] nil [ (λ w → ⟦ w ≡ nil-val ⟧) ]
nil-triple = val-triple′

cons-triple :
    η [ x ]= v₁
  → η [ y ]= v₂
    --------------------------------------------------------------------------------
  → [ η ⊢ Emp ] cons ∙ var x ∙ var y [ (λ w → ⟦ w ≡ cons-val v₁ v₂ ⟧) ]
cons-triple x∈η y∈η ε✴H′ =
  record {
      eval = eval-fun-app
               (eval-fun-app eval-fun (eval-var x∈η) eval-fun)
               (eval-var y∈η)
               (eval-fun-app
                 eval-fun
                 (eval-prod (eval-var (there here)) (eval-var here))
                 (eval-right (eval-var here)))
    ; post = ✴-monoᵣ (ε⇒pure refl) ε✴H′
  }


-------------------------------------------------------------
-- Term rules that access the store

private
  variable
    l k : L

deref-triple :
    η [ x ]= loc l
    -----------------------------------------------------
  → [ η ⊢ l ↦ v ] ! (var x) [ (λ w → ⟦ w ≡ v ⟧ ✴ l ↦ v) ]
deref-triple x∈η l↪v =
  record {
    eval = eval-deref (eval-var x∈η) (containsˡ l↪v)
  ; post = ✴-assocₗ (✴-pureˡ refl l↪v)
  }

ref-triple :
    η [ x ]= v
    ----------------------------------------------------------------------
  → [ η ⊢ Emp ] ref (var x) [ (λ w → ∃[ l ] (⟦ w ≡ loc l ⟧ ✴ l ↦ v)) ]
ref-triple x∈η ε✴H′ =
  let _ , l , x = ✴-insert refl
  in record {
       eval = eval-ref (eval-var x∈η) x
     ; post = ⟨ (λ l↦v → l , (✴-pureˡ refl l↦v)) ⟨✴⟩ (λ { refl → ✴-id⁻ˡ ε✴H′ }) ⟩ x
     }

free-triple :
    η [ x ]= loc l
    ---------------------------------------------------
  → [ η ⊢ l ↦ v ] free (var x) [ (λ w → ⟦ w ≡ unit ⟧) ]
free-triple x∈η (px ∙⟨ sep ⟩ qx) =
  record {
    eval = eval-free (eval-var x∈η) (px ∙⟨ sep ⟩ refl)
  ; post = ✴-pureˡ refl qx
  }

assign-triple :
    η [ x ]= loc l
  → η [ y ]= v′
    ------------------------------------------------------------------
  → [ η ⊢ l ↦ v ] (var x) := (var y) [ (λ w → ⟦ w ≡ unit ⟧ ✴ l ↦ v′) ]
assign-triple x∈η y∈η l↪v =
  let _ , l↪v′ = ✴-update l↪v
  in record {
       eval = eval-assign (eval-var x∈η) (eval-var y∈η) l↪v l↪v′
     ; post = ✴-assocₗ (✴-pureˡ refl l↪v′)
     }


-------------------------------------------------------------
-- Syntax for proof outlines

abstract
  syntax val-triple′ {v = v} = ⟨val⟩ v
  syntax var-triple′ x = ⟨var⟩ x
  ⟨fun⟩ : [ η ⊢ Emp ] fun t [ (λ w → ⟦ w ≡ clos η t ⟧) ]
  ⟨fun⟩ = fun-triple′
  ⟨rec⟩ : [ η ⊢ Emp ] rec t [ (λ w → ⟦ w ≡ fix η t ⟧) ]
  ⟨rec⟩ = rec-triple′
  syntax prod-triple′ x y = ⟨ x ⟨,⟩ y ⟩
  syntax fst-triple′ x = ⟨fst⟩ x
  syntax snd-triple′ x = ⟨snd⟩ x
  syntax left-triple′ x = ⟨left⟩ x
  syntax right-triple′ x = ⟨right⟩ x

  syntax let-triple t₁ (λ v → t₂) =
    ⟨let v =⟩
      t₁
    ⟨in⟩
      t₂
    ⟨end⟩
  syntax clos-app-triple x y t =
    x ⟨∙⟩ y
    ⟨fun-body⟩
      t
  syntax fix-app-triple x y t =
    x ⟨∙⟩ y
    ⟨rec-body⟩
      t

  syntax sequence t₁ t₂ =
    t₁
    ⟨；⟩
    t₂
  syntax switch-triple x t₁ t₂ =
    ⟨switch⟩ x
      |left⇒
        t₁
      |right⇒
        t₂
    ⟨end⟩

  syntax deref-triple x = ⟨!⟩ x
  syntax ref-triple x = ⟨ref⟩ x
  syntax free-triple x = ⟨free⟩ x
  syntax assign-triple x y = x ⟨:=⟩ y

  ⟨nil⟩ : [ η ⊢ Emp ] nil [ (λ w → ⟦ w ≡ nil-val ⟧)]
  ⟨nil⟩ = nil-triple
  syntax cons-triple x y = x ⟨cons⟩ y

  infix  9 val-triple′ var-triple′ deref-triple ref-triple free-triple
  infix  8 fst-triple′ snd-triple′ left-triple′ right-triple′ cons-triple
  infix  6 assign-triple
  infixr 5 sequence
  infix  4 let-triple
