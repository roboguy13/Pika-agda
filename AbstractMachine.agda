open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Bool
open import Data.Integer

module AbstractMachine
  (Pred-Name : Set)
  (Pred-Label : Set)
  (Loc-Name : Set)
  (Loc-Name-eq-dec : ∀ (x y : Loc-Name) → (x ≡ y) ⊎ (x ≢ y))

  (Layout-Name : Set)
  (Constr-Name : Set)
  (Adt-Name : Set)
  (Fn-Name : Set)

  where

open import Expr
  (Pred-Name)
  (Pred-Label)
  (Loc-Name)
  (Layout-Name)
  (Constr-Name)
  (Adt-Name)
  (Fn-Name)


open import SSL (Pred-Name) (Pred-Label) (Loc-Name)
open import HeapDefs (Loc-Name) renaming (Val to SSL-Val)
open import SSLSatisfies (Pred-Name) (Pred-Label) (Loc-Name) (Loc-Name-eq-dec)

open Ambient-Context

data _#_ : Loc → Heap → Set where
  Fresh-Heap-Loc : ∀ {loc H dom-H} →
    Dom H dom-H →
    loc ∉ dom-H →
    loc # H

-- Evaluated layout body acting on a Heap
data Val-Layout-Body-Act :
    Val-Layout-Body →
    Heap →
    Heap →
    Set where

  Val-Layout-Body-Act-[] : ∀ {h} →
    Val-Layout-Body-Act [] h h

  Val-Layout-Body-Act-Points-To : ∀ {α} {ssl-α : SSL-Type}
                                {h h′ h′′ rest}
                                {lhs : Loc} {rhs : Val α}
                                {sll-rhs}
    (α-base-type : Base-Type α) →
    To-SSL-Val {α} {ssl-α} rhs sll-rhs →

    Val-Layout-Body-Act rest h h′ →

    h′ [ lhs ↦ sll-rhs ]== h′′ →
    --------
    Val-Layout-Body-Act
      (Val-Points-To lhs rhs α-base-type ∷ rest)
      h h′′


data _⟶_ {C} {Δ : Type-Context C} {Γ} : ∀ {α ssl-α} →
  (Expr ε Γ α × Fs-Store Γ × Store Δ × Heap) →
  (Store (Δ ,, ssl-α) × Heap) → Set

-- Transition relation extended to lists of expressions
data Args-transition {C} {Δ : Type-Context C} {Γ} : ∀ {C′} {Δ′ : Type-Context C′} {Γ′} →
  (Args Γ′ × Fs-Store Γ × Store Δ × Heap) →
  (Store Δ′ × Heap) → Set where

  Args-transition-[] : ∀ {fs-store store h} →
    Args-transition (Args-∅ , fs-store , store , h) (store , h)

  Args-transition-cons : ∀ {Γ′} {Γ₀} {α}
                           {arg : Expr ε Γ₀ α}
                           {args : Args Γ′}
                           {h h′}
                           {C′}
                           {Δ′ : Type-Context C′}
                           {store : Store Δ}
                           {store′ : Store Δ′}
                           {fs-store} →
    Args-transition (args , fs-store , store , h) (store′ , h′) →
    Args-transition (Args-cons arg args , fs-store , store , h) (store′ , h′)

-- Transition relation for one expression
data _⟶_ {C} {Δ} {Γ} where

  AM-Lit : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {h}
             {α ssl-α}
             {x : Val α} {ssl-x : SSL-Val ssl-α} →
    To-SSL-Val x ssl-x →
    (Lit x , fs-store , store , h) ⟶ (Store-cons ssl-x store , h)

  AM-Var : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {h}
             {α ssl-α}
             {v : Γ ∋ α}
             {val : SSL-Val ssl-α} →
    To-SSL-Val (fs-store-lookup fs-store v) val →
    (V v , fs-store , store , h) ⟶ (Store-cons val store , h )

  AM-Add : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {store′}
             {store′′}
             {h}
             {x y : Expr ε Γ Int-Ty}
             {x-val y-val} →
    (x , fs-store , store , h) ⟶ (Store-cons (Val-Int x-val) store′ , h) →
    (y , fs-store , store′ , h) ⟶ (Store-cons (Val-Int y-val) store′′ , h) →
    (Add x y , fs-store , store , h) ⟶ (Store-cons (Val-Int (x-val + y-val)) store′′ , h)

  -- AM-Lower-1 : ∀ {store : Fs-Store Γ}
  --                {h}
  --                {L-name ssl-α adt branches} →
  --   {constr : Constr} →
  --   {ssl-param : SSL-Var (ε ,, ssl-α) ssl-α} →
  --   (constr-prf : constr ∈ Adt.constrs adt) →
  --   (args : Args (Constr.field-Γ constr)) →

  --   ∀ {L-body : List (L-Heaplet (ε ,, ssl-α) (Constr.field-Γ constr))} →

  --   let
  --     branch : Layout-Branch L-name constr
  --     branch = record { ssl-C = S Z ; ssl-Δ = (ε ,, ssl-α) ; body = L-body }
  --   in
  --   (layout-prf : record { name = L-name ; adt = adt ; branches = branches } ∈ Global-Layout-Env) →
  --   (branch-prf : branch LB∈ branches) →

  --   --
  --   (app-Γ : Context) →
  --   Context-app Γ (Constr.field-Γ constr) app-Γ →

  --   ∀ {store′ : Fs-Store app-Γ}
  --     {h′} →
  --   Args-transition (args , store , h) (store′ , h′) →

  --   let
  --     store′′ : Fs-Store (app-Γ ,, {!!})
  --     store′′ = {!!}
  --   in

  --   -------

  --   (Lower constr ssl-param constr-prf args layout-prf branch-prf , store , h)
  --     ⟶
  --   ({!!} , {!!})
