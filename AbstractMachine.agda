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

  Val-Layout-Body-Act-Points-To : ∀ {α : SSL-Type}
                                {h h′ h′′ : Heap} {rest : Val-Layout-Body}
                                {lhs : Loc} {rhs : SSL-Val α} →

    Val-Layout-Body-Act rest h h′ →

    h′ [ lhs ↦ rhs ]== h′′ →
    --------
    Val-Layout-Body-Act
      (Val-Points-To lhs rhs ∷ rest)
      h h′′


-- _↣_ : ∀ {C C′} → Type-Context C → Type-Context C′ → Set
-- Δ ↣ Δ′ = {!!}

-- Inclusion map between contexts
data _↣_ : ∀ {C C′} → Type-Context C → Type-Context C′ → Set where
  Ctx-extension-here : ∀ {C} {Δ : Type-Context C} → Δ ↣ Δ
  Ctx-extension-there : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {α} →
    Δ ↣ Δ′ →
    Δ ↣ (Δ′ ,, α)

-- Action of context inclusion maps on variables
apply-ctx-extension : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {α} →
  Δ ↣ Δ′ →
  SSL-Var Δ α → SSL-Var Δ′ α
apply-ctx-extension Ctx-extension-here var = var
apply-ctx-extension (Ctx-extension-there prf) var = SSL-There (apply-ctx-extension prf var)

-- Composition of context inclusion maps
_C∘_ : ∀ {C C′ C′′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {Δ′′ : Type-Context C′′} →
  (Δ′ ↣ Δ′′) →
  (Δ ↣ Δ′) →
  (Δ ↣ Δ′′)
Ctx-extension-here C∘ Ctx-extension-here = Ctx-extension-here
Ctx-extension-here C∘ Ctx-extension-there prf-2 = Ctx-extension-there prf-2
Ctx-extension-there prf-1 C∘ prf-2 = Ctx-extension-there (prf-1 C∘ prf-2)

data _⟶_ {C} {Δ : Type-Context C} {Γ} : ∀ {C′} {Δ′ : Type-Context C′} {α} →
  (Expr ε Γ α × Fs-Store Γ × Store Δ × Heap) →
  (Δ ↣ Δ′ × ∃[ ssl-α ] Store Δ′ × Heap × SSL-Var Δ′ ssl-α) → Set

-- Transition relation extended to lists of expressions
data Args-transition {C} {Δ : Type-Context C} {Γ} : ∀ {C′} {Δ′ : Type-Context C′} {Γ′} →
  (Args Γ′ × Fs-Store Γ × Store Δ × Heap) →
  (Δ ↣ Δ′ × Store Δ′ × Heap × SSL-Vars Δ′ Γ′) → Set where

  Args-transition-[] : ∀ {fs-store store h} →
    Args-transition (Args-∅ , fs-store , store , h) ({!!} , store , h , SSL-Vars-∅)

  Args-transition-cons : ∀ {Γ′} {α ssl-α}
                           {arg : Expr ε Γ α}
                           {args : Args Γ′}
                           {h h′ h′′}
                           {C′ C′′}
                           {Δ′ : Type-Context C′}
                           {Δ′′ : Type-Context C′′}
                           {store : Store Δ}
                           {store′ : Store Δ′}
                           {store′′ : Store Δ′′}
                           {fs-store : Fs-Store Γ}
                           {arg-v} {args-vs}
                           {Δ↣Δ′} {Δ′↣Δ′′} →
    (to-ssl : To-SSL-Type α ssl-α) →
    (arg , fs-store , store , h) ⟶ (Δ↣Δ′ , ssl-α , store′ , h′ , arg-v) →
    Args-transition (args , fs-store , store′ , h′) (Δ′↣Δ′′ , store′′ , h′′ , args-vs) →
    Args-transition (Args-cons arg args , fs-store , store , h) (Δ′↣Δ′′ C∘ Δ↣Δ′ , store′′ , h′′ , SSL-Vars-cons to-ssl (apply-ctx-extension (Δ′↣Δ′′) arg-v) args-vs)

data Eval-Layout-Body {C} {Δ : Type-Context C} {Γ} (store : Fs-Store Γ) :
     Layout-Body Δ Γ → Val-Layout-Body → Set where
  Eval-Layout-Body-[] : Eval-Layout-Body store [] []

  Eval-Layout-Body-Points-To : ∀ {α ssl-α} {rest rest′}
                             {lhs : SSL-Expr Δ ε ssl-α} {rhs : Expr Δ Γ α}
                             {lhs-val} {rhs-val} →
    (α-base : Base-Type α) →
    (ssl-prf : To-SSL-Type α ssl-α) →
    -- ({!!} , {!!} , {!!}) ⟶ (Store-cons {!!} {!!} , {!!}) →
    Eval-Layout-Body store
      (Points-To lhs rhs α-base ssl-prf ∷ rest)
      (Val-Points-To rhs-val lhs-val ∷ rest′)

-- Transition relation for one expression
data _⟶_ {C} {Δ} {Γ} where

  AM-Lit : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {h}
             {α} {ssl-α : SSL-Type}
             {x : Val α} {ssl-x : SSL-Val ssl-α} →
    To-SSL-Val x ssl-x →
    let
      store′ : Store (Δ ,, ssl-α)
      store′ = Store-cons ssl-x store
    in
    (Lit x , fs-store , store , h) ⟶ (Ctx-extension-there Ctx-extension-here , ssl-α , store′ , h , SSL-Here)

  AM-Var : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {h}
             {α ssl-α}
             {v : Γ ∋ α}
             {val : SSL-Val ssl-α} →
    To-SSL-Val (fs-store-lookup fs-store v) val →
    (V v , fs-store , store , h) ⟶ (Ctx-extension-there Ctx-extension-here , ssl-α , Store-cons val store , h , SSL-Here )

  AM-Add : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {C′} {Δ′ : Type-Context C′}
             {C′′} {Δ′′ : Type-Context C′′}
             {store′ : Store Δ′}
             {store′′ : Store Δ′′}
             {h}
             {x y : Expr ε Γ Int-Ty}
             {x-val y-val}
             {Δ↣Δ′} {Δ′↣Δ′′}→
    (x , fs-store , store , h) ⟶ (Ctx-extension-there Δ↣Δ′ , Int-Type , Store-cons (Val-Int x-val) store′ , h , SSL-Here) →
    (y , fs-store , store′ , h) ⟶ (Ctx-extension-there Δ′↣Δ′′ , Int-Type , Store-cons (Val-Int y-val) store′′ , h , SSL-Here) →
    (Add x y , fs-store , store , h) ⟶ (Ctx-extension-there (Δ′↣Δ′′ C∘ Δ↣Δ′) , Int-Type , Store-cons (Val-Int (x-val + y-val)) store′′ , h , SSL-Here)

  AM-Lower-1 : ∀ {fs-store : Fs-Store Γ}
                 {h : Heap}
                 {L-name ssl-α adt branches} →
    {constr : Constr} →
    {ssl-param : SSL-Var (ε ,, ssl-α) ssl-α} →
    (constr-prf : constr ∈ Adt.constrs adt) →
    (args : Args (Constr.field-Γ constr)) →

    ∀ {L-body : List (L-Heaplet (ε ,, ssl-α) (Constr.field-Γ constr))} →

    let
      branch : Layout-Branch L-name constr
      branch = record { ssl-C = S Z ; ssl-Δ = (ε ,, ssl-α) ; body = L-body }
    in
    (layout-prf : record { name = L-name ; adt = adt ; branches = branches } ∈ Global-Layout-Env) →
    (branch-prf : branch LB∈ branches) →

    --

    ∀ {store : Store Δ} →

    ∀ {C′} {Δ′ : Type-Context C′} {store′ : Store Δ′}
      {h′} →
    Args-transition (args , fs-store , store , h) ({!!} , store′ , h′) →

    ∀ {ℓ} →
    ℓ # h →

    let
      store′′ = Store-cons (Val-Loc ℓ) store′
    in

    ∀ {h′} →
    Val-Layout-Body-Act {!!} h h′ →

    -------

    (Lower constr ssl-param constr-prf args layout-prf branch-prf , fs-store , store , h)
      ⟶
    ({!!} , {!!} , store′′ , {!!})
