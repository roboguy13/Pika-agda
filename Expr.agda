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

data Context-app : Context → Context → Context → Set where
  Context-app-∅ : ∀ {Γ} → Context-app Γ ∅ Γ
  Context-app-cons : ∀ {Γ₁ Γ₂ Γ′ α} →
    Context-app Γ₁ Γ₂ Γ′ →
    Context-app Γ₁ (Γ₂ ,, α) (Γ′ ,, α)

data _∋_ : Context → Type → Set where
  Here : ∀ {Γ α} → (Γ ,, α) ∋ α
  There : ∀ {Γ α β} →
    Γ ∋ α →
    (Γ ,, β) ∋ α

data Val : Type → Set where
  Val-Int : ℤ → Val Int-Ty
  Val-Bool : Bool → Val Bool-Ty

-- →SSL-Type : ∀ {α} → Base-Type α → ∃[ ssl-α ] To-SSL-Type α ssl-α
-- →SSL-Type prf = {!!}

-- →SSL-Val : ∀ {α} → Val α → SSL-Val
-- →SSL-Val v = ?

data To-SSL-Val : ∀ {α ssl-α} → Val α → SSL-Val ssl-α → Set where
  To-SSL-Val-Int : ∀ {i} → To-SSL-Val (Val-Int i) (Val-Int i)
  To-SSL-Val-Bool : ∀ {b} → To-SSL-Val (Val-Bool b) (Val-Bool b)

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
  Points-To : ∀ {α} →
    SSL-Expr Δ ε Loc-Type → Expr Δ Γ α →
    Base-Type α →
    L-Heaplet Δ Γ

  -- NOTE: No mutually recursive layout definitions, for now
  Ap : ∀ {SSL-α} →
    (n : Layout-Name) →
    SSL-Var Δ SSL-α →
    Expr Δ Γ (Layout-Ty n) →
    L-Heaplet Δ Γ


Layout-Body : ∀ {C} (Δ : Type-Context C) (Γ : Context) → Set
Layout-Body Δ Γ = List (L-Heaplet Δ Γ)

-- A heaplet with no applications and all RHS's are base values
data Val-Heaplet : Set where
  Val-Points-To : ∀ {α} →
    Loc → SSL-Val α →
    Val-Heaplet

-- Gotten by applying a layout to value arguments
Val-Layout-Body : Set
Val-Layout-Body = List Val-Heaplet

record Layout-Branch (name : Layout-Name) (constr : Constr) : Set where
  inductive
  field
    ssl-C : SSL-Context
    ssl-Δ : Type-Context ssl-C
    body : Layout-Body ssl-Δ (Constr.field-Γ constr)

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
  Args-cons : ∀ {C} {Δ : Type-Context C} {Γ₀ Γ α} →
    Expr Δ Γ₀ α →
    Args Γ →
    Args (Γ ,, α)

-- Give a SuSLik variable for each fun-SuSLik variable in the given context. The
-- SuSLik variables are from SuSLik context Δ
data SSL-Vars {C} (Δ : Type-Context C) : Context → Set where
  SSL-Vars-∅ : SSL-Vars Δ ∅
  SSL-Vars-cons : ∀ {Γ α ssl-α} →
    To-SSL-Type α ssl-α →
    SSL-Var Δ ssl-α →
    SSL-Vars Δ Γ →
    SSL-Vars Δ (Γ ,, α)

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
    ∀ {C} {Δ : Type-Context C} →
    Expr Δ Γ Int-Ty →
    Expr Δ Γ Int-Ty →
    Expr Δ Γ Int-Ty

  Sub : ∀ {Γ} →
    ∀ {C} {Δ : Type-Context C} →
    Expr Δ Γ Int-Ty →
    Expr Δ Γ Int-Ty →
    Expr Δ Γ Int-Ty

  And : ∀ {Γ} →
    ∀ {C} {Δ : Type-Context C} →
    Expr Δ Γ Bool-Ty →
    Expr Δ Γ Bool-Ty →
    Expr Δ Γ Bool-Ty

  Not : ∀ {Γ} →
    ∀ {C} {Δ : Type-Context C} →
    Expr Δ Γ Bool-Ty →
    Expr Δ Γ Bool-Ty

  Equal : ∀ {Γ α} →
    ∀ {C} {Δ : Type-Context C} →
    Expr Δ Γ α →
    Expr Δ Γ α →
    Expr Δ Γ Bool-Ty

  Lower : ∀ {Γ L-name ssl-α adt branches} →
    (constr : Constr) →
    (ssl-param : SSL-Var (ε ,, ssl-α) ssl-α) →

    constr ∈ Adt.constrs adt →
    Args (Constr.field-Γ constr) →

    ∀ {L-body : List (L-Heaplet (ε ,, ssl-α) (Constr.field-Γ constr))} →

    let
      branch : Layout-Branch L-name constr
      branch = record { ssl-C = S Z ; ssl-Δ = (ε ,, ssl-α) ; body = L-body }
    in
    record { name = L-name ; adt = adt ; branches = branches } ∈ Global-Layout-Env →
    branch LB∈ branches →

    ∀ {C} {Δ : Type-Context C} →
    Expr Δ Γ (Layout-Ty L-name)

  -- NOTE: Function definitions are already fully instantiated
  Apply : ∀ f-name {Γ A B} (arg : Expr ε Γ (Layout-Ty (Layout.name A))) →
    ∀ {C} {Δ : Type-Context C} →
    (f-name , A , B) ∈ Global-Fn-Type-Env →
    Expr Δ Γ (Fn-Ty (Layout-Ty (Layout.name A)) (Layout-Ty (Layout.name B)))

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

Expr-weaken-Δ : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {Γ} {α} →
  Δ ↣ Δ′ →
  Expr Δ Γ α →
  Expr Δ′ Γ α
Expr-weaken-Δ prf (V x) = V x
Expr-weaken-Δ prf (Lit x) = Lit x
Expr-weaken-Δ prf (SSL-V x x₁) = SSL-V (apply-ctx-extension prf x) x₁
Expr-weaken-Δ prf (Add e e₁) = Add (Expr-weaken-Δ prf e₁) (Expr-weaken-Δ prf e₁)
Expr-weaken-Δ prf (Sub e e₁) = Sub (Expr-weaken-Δ prf e₁) (Expr-weaken-Δ prf e₁)
Expr-weaken-Δ prf (And e e₁) = And (Expr-weaken-Δ prf e₁) (Expr-weaken-Δ prf e₁)
Expr-weaken-Δ prf (Not e) = Not (Expr-weaken-Δ prf e)
Expr-weaken-Δ prf (Equal {_} {β} e e₁) = Equal {_} {β} (Expr-weaken-Δ prf e₁) (Expr-weaken-Δ prf e₁)
Expr-weaken-Δ prf (Lower constr ssl-param x x₁ x₂ x₃) = Lower constr ssl-param x x₁ x₂ x₃
Expr-weaken-Δ prf (Apply f {_} {A} {B} arg prf-2) = Apply f {_} {A} {B} arg prf-2

data Fs-Store : Context → Set where
  Fs-Store-∅ : Fs-Store ∅
  Fs-Store-cons : ∀ {Γ α} →
    Val α →
    Fs-Store Γ →
    Fs-Store (Γ ,, α)

fs-store-lookup : ∀ {Γ α} → Fs-Store Γ → Γ ∋ α → Val α
fs-store-lookup (Fs-Store-cons x store) Here = x
fs-store-lookup (Fs-Store-cons x store) (There var) = fs-store-lookup store var

-- data SSL-Vars {C} (Δ : Type-Context C) : Context → Set where
--   SSL-Vars-∅ : SSL-Vars Δ ∅
--   SSL-Vars-cons : ∀ {Γ α ssl-α} →
--     To-SSL-Type α ssl-α →
--     SSL-Var Δ ssl-α →
--     SSL-Vars Δ Γ →
--     SSL-Vars Δ (Γ ,, α)

-- data SSL-Vars→Store {C} {Δ : Type-Context C}  : ∀ {C′}  {Δ′ : Type-Context C′} {Γ} (store : Store Δ) → SSL-Vars Δ Γ → Store Δ′ → Set where
--   SSL-Vars→Store-∅ : ∀ {store} → SSL-Vars→Store store SSL-Vars-∅ Store-[]
--   SSL-Vars→Store-cons : ∀ {C′} {Δ′} {Γ α} {ssl-α} {store} {ssl-prf : To-SSL-Type α ssl-α} {var : SSL-Var Δ ssl-α} {rest} {rest′} →
--     SSL-Vars→Store {C} {Δ} {C′} {Δ′} {Γ} store rest rest′ →
--     SSL-Vars→Store store (SSL-Vars-cons ssl-prf var rest) (Store-cons (store-lookup store var) rest′)


data SSL-Vars→Fs-Store : ∀ {C} {Δ : Type-Context C} {Γ} (store : Store Δ) → SSL-Vars Δ Γ → Fs-Store Γ → Set where
  SSL-Vars→Fs-Store-∅ : ∀ {C} {Δ : Type-Context C} {store} → SSL-Vars→Fs-Store {C} {Δ} store SSL-Vars-∅ Fs-Store-∅
  SSL-Vars→Fs-Store-cons : ∀ {C} {Δ : Type-Context C} {Γ α} {ssl-α} {store} {ssl-prf : To-SSL-Type α ssl-α} {var : SSL-Var Δ ssl-α} {rest} {rest′}
                             {val} →
    SSL-Vars→Fs-Store {C} {Δ} {Γ} store rest rest′ →
    To-SSL-Val val (store-lookup store var) →
    (prf : To-SSL-Type α ssl-α) →
    SSL-Vars→Fs-Store store (SSL-Vars-cons prf var rest) (Fs-Store-cons val rest′)

data Fs-Store-app : ∀ {Γ Γ′ Γ′′} → Fs-Store Γ → Fs-Store Γ′ → Fs-Store Γ′′ → Set where
  Fs-Store-app-∅ : ∀ {Γ} {store : Fs-Store Γ} → Fs-Store-app Fs-Store-∅ store store
  Fs-Store-app-cons : ∀ {Γ Γ′ Γ′′} {α}
                        {store-1 : Fs-Store Γ} {store-2 : Fs-Store Γ′} {store′ : Fs-Store Γ′′} {val : Val α} →
    Fs-Store-app store-1 store-2 store′ →
    Fs-Store-app (Fs-Store-cons val store-1) store-2 (Fs-Store-cons val store′)

data To-SSL-Context : ∀ {C} → Context → Type-Context C → Set where
  To-SSL-Context-Z : To-SSL-Context ∅ ε
  To-SSL-Context-S : ∀ {C} {Γ α ssl-α Δ} →
    To-SSL-Type α ssl-α →
    To-SSL-Context {C} Γ Δ →
    To-SSL-Context (Γ ,, α) (Δ ,, ssl-α)

data To-Store : ∀ {C} {Δ : Type-Context C} {Γ} → Fs-Store Γ → Store Δ → Set where
  To-Store-∅ : To-Store Fs-Store-∅ Store-[]
  To-Store-cons : ∀ {C} {Δ : Type-Context C} {Γ α ssl-α}
                    {val : Val α}
                    {ssl-val : SSL-Val ssl-α}
                    {fs-store : Fs-Store Γ}
                    {store : Store Δ} →
    To-SSL-Type α ssl-α →
    To-SSL-Val val ssl-val →
    To-Store fs-store store →
    To-Store (Fs-Store-cons val fs-store) (Store-cons ssl-val store)

-- to-SSL-Context : Context → ∃[ C ] Type-Context C
-- to-SSL-Context ∅ = Z , ε
-- to-SSL-Context (Γ ,, x) with to-SSL-Context Γ
-- ... | n , Δ = S n , ({!!} ,, to-SSL

-- Fs-Store→Store : Fs-Store Γ → 
