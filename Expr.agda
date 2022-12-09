-- Some simplifications:
--   - Only functions on ADTs (not any one base types).
--   - No guards
--   - Every function is already fully instantiated

open import Data.String
open import Data.Integer
open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Empty
open import Data.Unit

module Expr
  (Var-Name : Set)
  (to-Var-Name : String → Var-Name)
  (Pred-Name : Set)
  (Pred-Label : Set)
  (Loc-Name : Set)

  (Layout-Name : Set)
  (Constr-Name : Set)
  (Adt-Name : Set)
  (Fn-Name : Set)
  where

open import SSL (Pred-Name) (Pred-Label) (Loc-Name)
open import HeapDefs (Loc-Name) renaming (Val to SSL-Val)

-- record Layout-Name : Set where
--   field
--     name : String

-- record Constr-Name : Set where
--   field
--     name : String

data Type : Set where
  Int-Ty : Type
  Bool-Ty : Type
  Layout-Ty : Layout-Name → Type

  Fn-Ty : Type → Type → Type

data Base-Type : Type → Set where
  Base-Type-Int : Base-Type Int-Ty
  Base-Type-Bool : Base-Type Bool-Ty

data First-Order : Type → Set where
  First-Order-Base : ∀ {α} → Base-Type α → First-Order α
  First-Order-Layout : ∀ {n} → First-Order (Layout-Ty n)
  First-Order-Fn : ∀ {α β} →
    Base-Type α →
    First-Order β →
    First-Order (Fn-Ty α β)

data To-SSL-Type : Type → SSL-Type → Set where
  To-SSL-Type-Int : To-SSL-Type Int-Ty Int-Type
  To-SSL-Type-Bool : To-SSL-Type Bool-Ty Bool-Type
  To-SSL-Type-Layout : ∀ {n} → To-SSL-Type (Layout-Ty n) Loc-Type

data Context : Set where
  ∅ : Context
  _,,_ : Context → Type → Context

data _∋_ : Context → Type → Set where
  Here : ∀ {Γ α} → (Γ ,, α) ∋ α
  There : ∀ {Γ α β} →
    Γ ∋ α →
    (Γ ,, β) ∋ α

data Val : Type → Set where
  Val-Int : ℤ → Val Int-Ty
  Val-Bool : Bool → Val Bool-Ty

record Constr : Set where
  field
    name : Constr-Name
    field-Γ : Context
    -- field-types : List (∃[ α ] First-Order α)

record Adt : Set where
  field
    name : Adt-Name
    constrs : List Constr

data Expr : {C : SSL-Context} → Type-Context C → Context → Type → Set

data L-Heaplet {C} (Δ : Type-Context C) (Γ : Context) : Set where
  Points-To : ∀ {α SSL-α} →
    SSL-Var Δ SSL-α → Expr Δ Γ α →
    Base-Type α →
    To-SSL-Type α SSL-α →
    L-Heaplet Δ Γ

  -- NOTE: No mutually recursive layout definitions, for now
  Ap : ∀ {SSL-α} →
    (n : Layout-Name) →
    SSL-Var Δ SSL-α →
    Expr Δ Γ (Layout-Ty n) →
    L-Heaplet Δ Γ

record Layout-Branch (name : Layout-Name) (constr : Constr) : Set where
  inductive
  field
    ssl-C : SSL-Context
    ssl-Δ : Type-Context ssl-C
    body : List (L-Heaplet ssl-Δ (Constr.field-Γ constr))

data Layout-Branches (L-name : Layout-Name) : (adt : Adt) → Set where
  Layout-Branches-[] : ∀ {name} →
    Layout-Branches L-name (record { name = name ; constrs = [] })

  Layout-Branches-cons : ∀ {name constr rest} →
    Layout-Branch L-name constr →
    Layout-Branches L-name (record { name = name ; constrs = rest }) →
    Layout-Branches L-name (record { name = name ; constrs = constr ∷ rest })

data _LB∈_ : ∀ {L-name adt constr} → Layout-Branch L-name constr → Layout-Branches L-name adt → Set where
  LB∈-here : ∀ {L-name adt constr} {branch : Layout-Branch L-name constr} {branches : Layout-Branches L-name adt} →
    branch LB∈ (Layout-Branches-cons branch branches)

  LB∈-there : ∀ {L-name adt constr constr′} {branch : Layout-Branch L-name constr} {branch′ : Layout-Branch L-name constr′} {branches : Layout-Branches L-name adt} →
    branch LB∈ branches →
    branch LB∈ (Layout-Branches-cons branch′ branches)

record Layout : Set where
  inductive
  field
    name : Layout-Name
    adt : Adt
    branches : Layout-Branches name adt

data Args : Context → Set where
  Args-∅ : Args ∅
  Args-cons : ∀ {Γ₀ Γ α} →
    Expr ε Γ₀ α →
    Args Γ →
    Args (Γ ,, α)

record Fn-Branch (β : Type) (constr : Constr) : Set where
  field
    body : Expr ε (Constr.field-Γ constr) β

data Fn-Branches (β : Type) : (adt : Adt) → Set where
  Fn-Branches-[] : ∀ {name} →
    Fn-Branches β (record { name = name ; constrs = [] })

  Fn-Branches-cons : ∀ {name constr rest} →
    Fn-Branch β constr →
    Fn-Branches β (record { name = name ; constrs = rest }) →
    Fn-Branches β (record { name = name ; constrs = constr ∷ rest })

record Fn-Def : Set where
  field
    name : Fn-Name
    arg-adt : Adt
    β : Type
    branches : Fn-Branches β arg-adt

Layout-Env : Set
Layout-Env = List Layout

-- We only keep track of the function type info here to allow recursive function definitions
Fn-Type-Env : Set
Fn-Type-Env = List (Fn-Name × Layout × Layout)

variable Global-Layout-Env : Layout-Env
variable Global-Fn-Type-Env : Fn-Type-Env

data Expr where
  V : ∀ {C} {Δ : Type-Context C} {Γ α} → Γ ∋ α → Expr Δ Γ α
  Lit : ∀ {C} {Δ : Type-Context C} {Γ α} → Val α → Expr Δ Γ α

  SSL-V : ∀ {C} {Δ : Type-Context C} {Γ α SSL-α} →
    SSL-Var Δ SSL-α →
    To-SSL-Type α SSL-α →
    Expr Δ Γ α

  Add : ∀ {Γ} →
    Expr ε Γ Int-Ty →
    Expr ε Γ Int-Ty →
    Expr ε Γ Int-Ty

  Sub : ∀ {Γ} →
    Expr ε Γ Int-Ty →
    Expr ε Γ Int-Ty →
    Expr ε Γ Int-Ty

  And : ∀ {Γ} →
    Expr ε Γ Bool-Ty →
    Expr ε Γ Bool-Ty →
    Expr ε Γ Bool-Ty

  Not : ∀ {Γ} →
    Expr ε Γ Bool-Ty →
    Expr ε Γ Bool-Ty

  Equal : ∀ {Γ α} →
    Expr ε Γ α →
    Expr ε Γ α →
    Expr ε Γ Bool-Ty

  Lower : ∀ {Γ Γ₁ L-name ssl-α adt branches} →
    (constr : Constr) →
    (ssl-param : SSL-Var (ε ,, ssl-α) ssl-α) →
    Args Γ₁ →

    constr ∈ Adt.constrs adt →

    ∀ {L-body : List (L-Heaplet (ε ,, ssl-α) (Constr.field-Γ constr))} →

    let
      branch : Layout-Branch L-name constr
      branch = record { ssl-C = S Z ; ssl-Δ = (ε ,, ssl-α) ; body = L-body }
    in
    record { name = L-name ; adt = adt ; branches = branches } ∈ Global-Layout-Env →
    branch LB∈ branches →

    Expr ε Γ (Layout-Ty L-name)

  -- NOTE: Function definitions are already fully instantiated
  Apply : ∀ {f-name} {Γ A B} {arg : Expr ε Γ (Layout-Ty (Layout.name A))} →
    (f-name , A , B) ∈ Global-Fn-Type-Env →
    Expr ε Γ (Fn-Ty (Layout-Ty (Layout.name A)) (Layout-Ty (Layout.name B)))
