open import Data.String
open import Data.Integer
open import Data.Bool
open import Data.List
open import Data.Product

module Expr
  (Var-Name : Set)
  (to-Var-Name : String → Var-Name)
  (Pred-Name : Set)
  (Pred-Label : Set)
  (Loc-Name : Set)
  where

open import SSL (Pred-Name) (Pred-Label) (Loc-Name)
  renaming (Val to SSL-Val)

record Layout-Name : Set where
  field
    name : String

record Constr-Name : Set where
  field
    name : String

-- record SSL-Param : Set where
--   field
--     name : String

-- data Type-0 : Set where
--   Int-Ty : Type-0
--   Bool-Ty : Type-0
--   Layout-Ty : Layout-Name → Type-0

-- data Type : Set where
--   Ty-0 : Type-0 → Type
--   Fn-Ty : Type-0 → Type → Type

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

data Sig : Set where
  ε : Sig
  _,_ : Type → Sig → Sig

data Expr : {C : SSL-Context} → Type-Context C → Context → Type → Set

-- data Args (Γ : Context) : Sig → Set where
--   Args-ε : Args Γ ε
--   Args-cons : ∀ {α} →
--     Expr Γ α →
--     (sig : Sig) →
--     Args Γ (α , sig)

-- Args′ : Set
-- Args′ = ∃[ sig ] ∀ Γ → Args Γ sig

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

record Layout-Branch : Set where
  field
    name : Layout-Name
    ssl-C : SSL-Context
    ssl-Δ : Type-Context ssl-C
    constr-name : Constr-Name
    constr-param-Γ : Context
    body : List (L-Heaplet ssl-Δ constr-param-Γ)



-- Layout-Env : Set
-- Layout-Env = List (Layout-Name × SSL-Param × Constr-Name × Args′ × )

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

  -- Lower : ∀ {Γ n sig} →
  --   Constr-Name →
  --   Args Γ sig →
  --   Expr ε Γ (Layout-Ty n)
