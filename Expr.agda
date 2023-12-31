-- Some simplifications:
--   - Only functions on ADTs (not any one base types).
--   - No guards
--   - Every function is already fully instantiated

open import Data.String
open import Data.Integer
open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

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

data Non-Fn-Type : Type → Set where
  Non-Fn-Type-Base : ∀ {α} → Base-Type α → Non-Fn-Type α
  Non-Fn-Type-Layout : ∀ {n} → Non-Fn-Type (Layout-Ty n)

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

to-SSL-Val : ∀ {α ssl-α} → To-SSL-Type α ssl-α → (val : Val α) → ∃[ ssl-val ] To-SSL-Val {α} {ssl-α} val ssl-val
to-SSL-Val To-SSL-Type-Int (Val-Int x) = Val-Int x , To-SSL-Val-Int
to-SSL-Val To-SSL-Type-Bool (Val-Bool x) = Val-Bool x , To-SSL-Val-Bool

to-SSL-Type : ∀ {α} → Non-Fn-Type α → ∃[ ssl-α ] To-SSL-Type α ssl-α
to-SSL-Type (Non-Fn-Type-Base Base-Type-Int) = Int-Type , To-SSL-Type-Int
to-SSL-Type (Non-Fn-Type-Base Base-Type-Bool) = Bool-Type , To-SSL-Type-Bool
to-SSL-Type Non-Fn-Type-Layout = Loc-Type , To-SSL-Type-Layout

data Is-Layout-Type : Type → Set where
  mk-Is-Layout-Type : ∀ {n} → Is-Layout-Type (Layout-Ty n)

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

-- TODO: Should the Δ be a datatype parameter?
data Args {C} (Δ : Type-Context C) Γ₀ : Context → Set where
  Args-∅ : Args Δ Γ₀ ∅
  Args-cons : ∀ {Γ α} →
    Non-Fn-Type α →
    (Expr Δ Γ₀ α) ⊎ (Loc × Is-Layout-Type α) →
    Args {C} Δ Γ₀ Γ →
    Args Δ Γ₀ (Γ ,, α)

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

  Equal : ∀ {Γ} →
    ∀ {C} {Δ : Type-Context C} →
    Expr Δ Γ Int-Ty →
    Expr Δ Γ Int-Ty →
    Expr Δ Γ Bool-Ty

  Lower : ∀ {Γ L-name adt branches} →
    (constr : Constr) →
    ∀ {C} {Δ : Type-Context C} →
    (ssl-param : SSL-Var (ε ,, Loc-Type) Loc-Type) →

    constr ∈ Adt.constrs adt →
    Args {C} Δ Γ (Constr.field-Γ constr) →

    ∀ {L-body : List (L-Heaplet (ε ,, Loc-Type) (Constr.field-Γ constr))} →

    let
      branch : Layout-Branch L-name constr
      branch = record { ssl-C = S Z ; ssl-Δ = (ε ,, Loc-Type) ; body = L-body }
    in
    record { name = L-name ; adt = adt ; branches = branches } ∈ Global-Layout-Env →
    branch LB∈ branches →

    Expr Δ Γ (Layout-Ty L-name)

  -- NOTE: Function definitions are already fully instantiated
  Apply : ∀ f-name {Γ A B}
    {C} {Δ : Type-Context C}
    (arg : (Expr Δ Γ (Layout-Ty (Layout.name A))) ⊎ Loc) →
    (f-name , A , B) ∈ Global-Fn-Type-Env →
    Expr Δ Γ (Layout-Ty (Layout.name B))

-- data Shift : ∀ {C C′} → Type-Context C → Type-Context C′ → Set where

-- Inclusion map between contexts
data _↣_ : ∀ {C C′} → Type-Context C → Type-Context C′ → Set where
  Ctx-extension-here : ∀ {C} {Δ : Type-Context C} → Δ ↣ Δ
  Ctx-extension-there : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {α} →
    Δ ↣ Δ′ →
    Δ ↣ (Δ′ ,, α)

  -- Ctx-extension-S : ∀ {C} {Δ : Type-Context C} {Δ′ : Type-Context (S C)} →
  --   Δ ↣ Δ′

  -- Ctx-extension-inj₁ : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {Δ⊔Δ′} →
  --   Ctx-⊔ Δ Δ′ Δ⊔Δ′ →
  --   Δ ↣ Δ⊔Δ′

ε↣Δ : ∀ {C} {Δ : Type-Context C} → ε ↣ Δ
ε↣Δ {.Z} {ε} = Ctx-extension-here
ε↣Δ {.(S _)} {Δ ,, x} = Ctx-extension-there ε↣Δ

-- Composition of context inclusion maps
_C∘_ : ∀ {C C′ C′′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {Δ′′ : Type-Context C′′} →
  (Δ′ ↣ Δ′′) →
  (Δ ↣ Δ′) →
  (Δ ↣ Δ′′)
Ctx-extension-here C∘ Ctx-extension-here = Ctx-extension-here
Ctx-extension-here C∘ Ctx-extension-there prf-2 = Ctx-extension-there prf-2
Ctx-extension-there prf-1 C∘ prf-2 = Ctx-extension-there (prf-1 C∘ prf-2)

⊔-inj₂↣ : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} → ∀ {Δ⊔Δ′} → Ctx-⊔ Δ Δ′ Δ⊔Δ′ → Δ′ ↣ Δ⊔Δ′
⊔-inj₂↣ Ctx-⊔-ε-ε = Ctx-extension-here
⊔-inj₂↣ Ctx-⊔-ε-cons = Ctx-extension-here
⊔-inj₂↣ Ctx-⊔-cons-ε = ε↣Δ
⊔-inj₂↣ (Ctx-⊔-cons-cons prf) = Ctx-extension-there (⊔-inj₂↣ prf)

-- Action of context inclusion maps on variables
apply-ctx-extension : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {α} →
  Δ ↣ Δ′ →
  SSL-Var Δ α → SSL-Var Δ′ α
apply-ctx-extension Ctx-extension-here var = var
apply-ctx-extension (Ctx-extension-there prf) var = SSL-There (apply-ctx-extension prf var)

⊔-SSL-Vars-inj₁ : ∀ {α} {C C′} → {Δ : Type-Context C} → {Δ′ : Type-Context C′} → ∀ {Δ′′} → Ctx-⊔ Δ Δ′ Δ′′ → SSL-Vars Δ α → SSL-Vars Δ′′ α
⊔-SSL-Vars-inj₁ Ctx-⊔-ε-ε SSL-Vars-∅ = SSL-Vars-∅
⊔-SSL-Vars-inj₁ Ctx-⊔-ε-cons SSL-Vars-∅ = SSL-Vars-∅
⊔-SSL-Vars-inj₁ {α} {C} {C′} {Δ} {Δ′} Ctx-⊔-ε-cons (SSL-Vars-cons x x₁ vars) =
  let
    z = ⊔-SSL-Vars-inj₁ Ctx-⊔-ε-cons vars
  in
  SSL-Vars-cons x (apply-ctx-extension ε↣Δ x₁) z
⊔-SSL-Vars-inj₁ Ctx-⊔-cons-ε (SSL-Vars-cons x x₁ vars) = SSL-Vars-cons x x₁ vars
⊔-SSL-Vars-inj₁ Ctx-⊔-cons-ε SSL-Vars-∅ = SSL-Vars-∅
⊔-SSL-Vars-inj₁ (Ctx-⊔-cons-cons prf) SSL-Vars-∅ = SSL-Vars-∅
⊔-SSL-Vars-inj₁ (Ctx-⊔-cons-cons prf) (SSL-Vars-cons x x₁ vars) =
  let
    z = ⊔-SSL-Vars-inj₁ (Ctx-⊔-cons-cons prf) vars
    y = Ctx-⊔-inj₁ (Ctx-⊔-cons-cons prf) x₁
  in
  SSL-Vars-cons x y z



⊔-SSL-Vars-inj₂ : ∀ {α} {C C′} → {Δ : Type-Context C} → {Δ′ : Type-Context C′} → ∀ {Δ′′} → Ctx-⊔ Δ Δ′ Δ′′ → SSL-Vars Δ′ α → SSL-Vars Δ′′ α
⊔-SSL-Vars-inj₂ Ctx-⊔-ε-ε SSL-Vars-∅ = SSL-Vars-∅
⊔-SSL-Vars-inj₂ Ctx-⊔-ε-cons SSL-Vars-∅ = SSL-Vars-∅
⊔-SSL-Vars-inj₂ Ctx-⊔-ε-cons (SSL-Vars-cons x x₁ vars) = SSL-Vars-cons x x₁ vars
⊔-SSL-Vars-inj₂ Ctx-⊔-cons-ε SSL-Vars-∅ = SSL-Vars-∅
⊔-SSL-Vars-inj₂ (Ctx-⊔-cons-cons prf) SSL-Vars-∅ = SSL-Vars-∅
⊔-SSL-Vars-inj₂ (Ctx-⊔-cons-cons prf) (SSL-Vars-cons x x₁ vars) =
  let
    z = ⊔-SSL-Vars-inj₂ (Ctx-⊔-cons-cons prf) vars
    y = Ctx-⊔-inj₂ (Ctx-⊔-cons-cons prf) x₁
  in
  SSL-Vars-cons x y z


-- weaken-Store : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} →
--   Δ ↣ Δ′ →
--   Store Δ →
--   Store Δ′
-- weaken-Store Ctx-extension-here store = store
-- weaken-Store (Ctx-extension-there Δ↣Δ′) Store-[] = ?
-- weaken-Store (Ctx-extension-there Δ↣Δ′) (Store-cons val store) = {!!}

-- data Args {C} (Δ : Type-Context C) {Γ₀} : Context → Set where
Expr-weaken-Δ : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {Γ} {α} →
  Δ ↣ Δ′ →
  Expr Δ Γ α →
  Expr Δ′ Γ α

Args-weaken-Δ : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {Γ₀} {Γ} →
  Δ ↣ Δ′ →
  Args Δ Γ₀ Γ →
  Args Δ′ Γ₀ Γ
Args-weaken-Δ incl Args-∅ = Args-∅
Args-weaken-Δ incl (Args-cons x (inj₂ y) args) =
  Args-cons x (inj₂ y) (Args-weaken-Δ incl args)
Args-weaken-Δ incl (Args-cons x (inj₁ y) args)  =
  Args-cons x (inj₁ (Expr-weaken-Δ incl y)) (Args-weaken-Δ incl args)

-- apply-ctx-extension-Args : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {Γ} →
--   Δ ↣ Δ′ →
--   Args Γ → Args Δ′ Γ
-- apply-ctx-extension-Args prf Args-∅ = Args-∅
-- apply-ctx-extension-Args prf (Args-cons prf-2 (inj₁ x) args) = Args-cons prf-2 (inj₁ (Expr-weaken-Δ prf x)) (apply-ctx-extension-Args prf args)
-- apply-ctx-extension-Args prf (Args-cons {Γ₀} prf-2 (inj₂ y) args) = Args-cons {_} {_} {Γ₀} prf-2 (inj₂ y) (apply-ctx-extension-Args prf args)

Expr-weaken-Δ prf (V x) = V x
Expr-weaken-Δ prf (Lit x) = Lit x
Expr-weaken-Δ prf (SSL-V x x₁) = SSL-V (apply-ctx-extension prf x) x₁
Expr-weaken-Δ prf (Add e e₁) = Add (Expr-weaken-Δ prf e₁) (Expr-weaken-Δ prf e₁)
Expr-weaken-Δ prf (Sub e e₁) = Sub (Expr-weaken-Δ prf e₁) (Expr-weaken-Δ prf e₁)
Expr-weaken-Δ prf (And e e₁) = And (Expr-weaken-Δ prf e₁) (Expr-weaken-Δ prf e₁)
Expr-weaken-Δ prf (Not e) = Not (Expr-weaken-Δ prf e)
Expr-weaken-Δ prf (Equal e e₁) = Equal (Expr-weaken-Δ prf e₁) (Expr-weaken-Δ prf e₁)
Expr-weaken-Δ prf (Lower constr ssl-param x x₁ x₂ x₃) =
  Lower constr ssl-param x (Args-weaken-Δ prf x₁) x₂ x₃
Expr-weaken-Δ prf (Apply f {_} {A} {B} (inj₁ arg) prf-2) = Apply f {_} {A} {B} (inj₁ (Expr-weaken-Δ prf arg)) prf-2
Expr-weaken-Δ prf (Apply f {_} {A} {B} (inj₂ arg) prf-2) = Apply f {_} {A} {B} (inj₂ arg) prf-2

SSL-Vars-weaken-Δ : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} {Γ} →
  Δ ↣ Δ′ →
  SSL-Vars Δ Γ →
  SSL-Vars Δ′ Γ
SSL-Vars-weaken-Δ Ctx-extension-here SSL-Vars-∅ = SSL-Vars-∅
SSL-Vars-weaken-Δ Ctx-extension-here (SSL-Vars-cons x x₁ vars) = SSL-Vars-cons x x₁ vars
SSL-Vars-weaken-Δ (Ctx-extension-there prf) SSL-Vars-∅ = SSL-Vars-∅
SSL-Vars-weaken-Δ (Ctx-extension-there prf) (SSL-Vars-cons x x₁ vars) =
  let
    z = SSL-Vars-weaken-Δ (Ctx-extension-there prf) vars
  in
  SSL-Vars-cons x (apply-ctx-extension (Ctx-extension-there prf) x₁) z

-- ↣SΔ : ∀ {C} {Δ : Type-Context C} {Δ′ : Type-Context (S C)} → Δ ↣ Δ′
-- ↣SΔ {Z} {Δ} {Δ′} = {!!}
-- ↣SΔ {S C} {Δ} {Δ′} = {!!}

-- Ctx-⊔-↣-right : ∀ {C C′} {α β} {Δ : Type-Context C} {Δ′ : Type-Context C′} →
--   Ctx-⊔ (Δ ,, α) Δ′ ↣ Ctx-⊔ (Δ ,, α) (Δ′ ,, β)
-- Ctx-⊔-↣-right {Z} {Z} {_} {_} {ε} {ε} = {!!}
-- Ctx-⊔-↣-right {_} {_} {_} {_} {ε} {Δ′ ,, x} = {!!}
-- Ctx-⊔-↣-right {_} {_} {_} {_} {Δ ,, x} {ε} = {!!}
-- Ctx-⊔-↣-right {_} {_} {_} {_} {Δ ,, x} {Δ′ ,, x₁} = {!!}

-- Δ-inj₁ : ∀ {C C′} {Δ : Type-Context C} {Δ′ : Type-Context C′} → Δ ↣ Ctx-⊔ Δ Δ′
-- Δ-inj₁ {_} {_} {ε} {Δ′} = ε↣Δ
-- Δ-inj₁ {_} {_} {Δ ,, x} {ε} = Ctx-extension-here
-- Δ-inj₁ {_} {_} {Δ ,, x} {Δ′ ,, y} =
--   let
--     z = Δ-inj₁ {_} {_} {Δ } {Δ′ ,, y}
--   in
--   Ctx-⊔-↣-right C∘ Δ-inj₁ {_} {_} {Δ ,, x} {Δ′}

-- Expr-Δ-subst-1 : ∀ {C} {Δ : Type-Context C} {α ssl-β} {Γ} {ssl-α} → (To-SSL-Type α ssl-α) →
--   Store (Δ ,, ssl-β) →
--   Expr (Δ ,, ssl-β) Γ α →
--   Expr Δ Γ α ⊎ (Loc × Is-Layout-Type α)

-- Args-Δ-subst-1 : ∀ {C} {Δ : Type-Context C} {α} {Γ} →
--   Store (Δ ,, α) →
--   Args (Δ ,, α) Γ →
--   Args Δ Γ
-- Args-Δ-subst-1 store Args-∅ = Args-∅
-- Args-Δ-subst-1 store (Args-cons {Γ₀} prf (inj₂ y) args) = Args-cons {_} {_} {Γ₀} prf (inj₂ y) (Args-Δ-subst-1 store args)
-- Args-Δ-subst-1 store (Args-cons {Γ₀} prf (inj₁ x) args) with Expr-Δ-subst-1 (proj₂ (to-SSL-Type prf)) store x
-- ... | inj₁ x₁ = Args-cons prf (inj₁ x₁) (Args-Δ-subst-1 store args)
-- ... | inj₂ y = Args-cons {_} {_} {Γ₀} prf (inj₂ y) (Args-Δ-subst-1 store args)

-- Expr-Δ-subst-1 prf-ssl store (V x) = inj₁ (V x)
-- Expr-Δ-subst-1 prf-ssl store (Lit x) = inj₁ (Lit x)
-- Expr-Δ-subst-1 {C} {Δ} prf-ssl store (SSL-V SSL-Here To-SSL-Type-Int) with store-lookup store SSL-Here
-- ... | Val-Int x = inj₁ (Lit (Val-Int x))
-- Expr-Δ-subst-1 {C} {Δ} prf-ssl store (SSL-V SSL-Here To-SSL-Type-Bool) with store-lookup store SSL-Here
-- ... | Val-Bool x = inj₁ (Lit (Val-Bool x))
-- Expr-Δ-subst-1 {C} {Δ} To-SSL-Type-Layout store (SSL-V SSL-Here To-SSL-Type-Layout) with store-lookup store SSL-Here
-- ... | Val-Loc x = inj₂ (x , mk-Is-Layout-Type)
-- Expr-Δ-subst-1 prf-ssl store (SSL-V (SSL-There x) prf) = inj₁ (SSL-V x prf)
-- Expr-Δ-subst-1 To-SSL-Type-Int store (Add e e₁) with (Expr-Δ-subst-1 To-SSL-Type-Int store e₁) | (Expr-Δ-subst-1 To-SSL-Type-Int store e₁)
-- ... | inj₁ x | inj₁ x₁ = inj₁ (Add x x₁)
-- Expr-Δ-subst-1 To-SSL-Type-Int store (Sub e e₁) with (Expr-Δ-subst-1 To-SSL-Type-Int store e₁) | (Expr-Δ-subst-1 To-SSL-Type-Int store e₁)
-- ... | inj₁ x | inj₁ x₁ = inj₁ (Sub x x₁)
-- Expr-Δ-subst-1 To-SSL-Type-Bool store (And e e₁) with (Expr-Δ-subst-1 To-SSL-Type-Bool store e₁) | (Expr-Δ-subst-1 To-SSL-Type-Bool store e₁)
-- ... | inj₁ x | inj₁ x₁ = inj₁ (And x x₁)
-- Expr-Δ-subst-1 To-SSL-Type-Bool store (Not e) with (Expr-Δ-subst-1 To-SSL-Type-Bool store e)
-- ... | inj₁ x = inj₁ (Not x)
-- Expr-Δ-subst-1 To-SSL-Type-Bool store (Equal e e₁) with (Expr-Δ-subst-1 To-SSL-Type-Int store e₁) | (Expr-Δ-subst-1 To-SSL-Type-Int store e₁)
-- ... | inj₁ x | inj₁ x₁ = inj₁ (Equal x x₁)
-- Expr-Δ-subst-1 To-SSL-Type-Loc store (Lower constr ssl-param x x₁ x₂ x₃) = inj₁ (Lower constr ssl-param x x₁ x₂ x₃)
-- Expr-Δ-subst-1 ssl-prf store (Apply f-name (inj₁ e) x) with Expr-Δ-subst-1 To-SSL-Type-Layout store e
-- ... | inj₁ x₁ = inj₁ (Apply f-name (inj₁ x₁) x)
-- ... | inj₂ (y , y-prf) = inj₁ (Apply f-name (inj₂ y) x)
-- Expr-Δ-subst-1 ssl-prf store (Apply f-name (inj₂ loc) x) = inj₁ (Apply f-name (inj₂ loc) x )

data Expr-Δ-subst-1 {C} {Δ : Type-Context C} {Γ} : ∀ {ssl-β} {α} {ssl-α} (ssl-prf : To-SSL-Type α ssl-α) (store : Store (Δ ,, ssl-β)) →
    Expr (Δ ,, ssl-β) Γ α →
    Expr Δ Γ α ⊎ (Loc × Is-Layout-Type α) →
    Set

data Args-Δ-subst-1 {C} {Δ : Type-Context C} {Γ₀} : ∀ {Γ α} (store : Store (Δ ,, α)) →
    Args (Δ ,, α) Γ₀ Γ →
    Args Δ Γ₀ Γ →
    Set where
  Args-Δ-subst-1-∅ : ∀ {α store} →
    Args-Δ-subst-1 {_} {_} {_} {_} {α} store Args-∅ Args-∅

  Args-Δ-subst-1-cons-inj₂ : ∀ {Γ α β non-fn loc store rest rest′} →
    Args-Δ-subst-1 {_} {_} {_} {Γ} {α} store rest rest′ →
    Args-Δ-subst-1 {_} {_} {_} {Γ ,, β} store (Args-cons non-fn (inj₂ loc) rest) (Args-cons non-fn (inj₂ loc) rest′)

  Args-Δ-subst-1-cons-inj₁ : ∀ {Γ β α ssl-β non-fn} {ssl-ty : To-SSL-Type β ssl-β} {e r store rest rest′} →
    Args-Δ-subst-1 {_} {_} {_} {Γ} {α} store rest rest′ →
    Expr-Δ-subst-1 ssl-ty store e r →
    Args-Δ-subst-1 {_} {_} {_} {Γ ,, β} store (Args-cons non-fn (inj₁ e) rest) (Args-cons non-fn r rest′)

data Expr-Δ-subst-1 {C} {Δ} {Γ}
    where
  Expr-Δ-subst-1-V : ∀ {ssl-β α ssl-α} {ssl-prf : To-SSL-Type α ssl-α} {x} {store : Store (Δ ,, ssl-β)} →
    Expr-Δ-subst-1 ssl-prf store (V x) (inj₁ (V x))

  Expr-Δ-subst-1-Lit : ∀ {ssl-β α ssl-α} {ssl-prf : To-SSL-Type α ssl-α} {v} {store : Store (Δ ,, ssl-β)} →
    Expr-Δ-subst-1 ssl-prf store (Lit v) (inj₁ (Lit v))

  Expr-Δ-subst-1-SSL-V-Here-Int : ∀ {x} {store : Store (Δ ,, Int-Type)} →
    Val-Int x ≡ store-lookup store SSL-Here →
    Expr-Δ-subst-1 To-SSL-Type-Int store (SSL-V SSL-Here To-SSL-Type-Int) (inj₁ (Lit (Val-Int x)))

  Expr-Δ-subst-1-SSL-V-Here-Bool : ∀ {x} {store : Store (Δ ,, Bool-Type)} →
    Val-Bool x ≡ store-lookup store SSL-Here →
    Expr-Δ-subst-1 To-SSL-Type-Bool store (SSL-V SSL-Here To-SSL-Type-Bool) (inj₁ (Lit (Val-Bool x)))

  Expr-Δ-subst-1-SSL-V-Here-Layout : ∀ {L-name} {x} {store : Store (Δ ,, Loc-Type)} →
    Val-Loc x ≡ store-lookup store SSL-Here →
    Expr-Δ-subst-1 (To-SSL-Type-Layout {L-name}) store (SSL-V SSL-Here To-SSL-Type-Layout) (inj₂ (x , mk-Is-Layout-Type))

  Expr-Δ-subst-1-SSL-V-There : ∀ {α ssl-α ssl-β ssl-γ} {prf-ssl : To-SSL-Type α ssl-α} {prf} {store : Store (Δ ,, ssl-β)} {x : SSL-Var Δ ssl-γ} →
    Expr-Δ-subst-1 prf-ssl store (SSL-V (SSL-There x) prf) (inj₁ (SSL-V x prf))

  Expr-Δ-subst-1-Add : ∀ {ssl-β} {x y} {x′ y′} {store : Store (Δ ,, ssl-β)} →
    Expr-Δ-subst-1 To-SSL-Type-Int store x (inj₁ x′) →
    Expr-Δ-subst-1 To-SSL-Type-Int store y (inj₁ y′) →
    Expr-Δ-subst-1 To-SSL-Type-Int store (Add x y) (inj₁ (Add x′ y′))

  Expr-Δ-subst-1-Sub : ∀ {ssl-β} {x y} {x′ y′} {store : Store (Δ ,, ssl-β)} →
    Expr-Δ-subst-1 To-SSL-Type-Int store x (inj₁ x′) →
    Expr-Δ-subst-1 To-SSL-Type-Int store y (inj₁ y′) →
    Expr-Δ-subst-1 To-SSL-Type-Int store (Sub x y) (inj₁ (Sub x′ y′))

  Expr-Δ-subst-1-And : ∀ {ssl-β} {x y} {x′ y′} {store : Store (Δ ,, ssl-β)} →
    Expr-Δ-subst-1 To-SSL-Type-Bool store x (inj₁ x′) →
    Expr-Δ-subst-1 To-SSL-Type-Bool store y (inj₁ y′) →
    Expr-Δ-subst-1 To-SSL-Type-Bool store (And x y) (inj₁ (And x′ y′))

  Expr-Δ-subst-1-Not : ∀ {ssl-β} {x} {x′} {store : Store (Δ ,, ssl-β)} →
    Expr-Δ-subst-1 To-SSL-Type-Bool store x (inj₁ x′) →
    Expr-Δ-subst-1 To-SSL-Type-Bool store (Not x) (inj₁ (Not x′))

  Expr-Δ-subst-1-Equal : ∀ {ssl-β} {x y} {x′ y′} {store : Store (Δ ,, ssl-β)} →
    Expr-Δ-subst-1 To-SSL-Type-Int store x (inj₁ x′) →
    Expr-Δ-subst-1 To-SSL-Type-Int store y (inj₁ y′) →
    Expr-Δ-subst-1 To-SSL-Type-Bool store (Equal x y) (inj₁ (Equal x′ y′))

  Expr-Δ-subst-1-Lower : ∀ {L-name} {ssl-β} {adt : Adt} {L-branches} {constr : Constr} {ssl-param : SSL-Var (ε ,, Loc-Type) Loc-Type} {x : constr ∈ Adt.constrs adt} {y : Args (Δ ,, ssl-β) Γ (Constr.field-Γ constr)} {y-subst : Args Δ Γ (Constr.field-Γ constr)} {L-body} {z w} {store : Store (Δ ,, ssl-β)} →
    Args-Δ-subst-1 store y y-subst →
    Expr-Δ-subst-1 (To-SSL-Type-Layout {L-name}) store (Lower {Global-Layout-Env} {Γ} {L-name} {adt} {L-branches} constr {S C} {Δ ,, ssl-β} ssl-param x y {L-body} z w) (inj₁ (Lower constr ssl-param x y-subst z w))

  Expr-Δ-subst-1-Apply-inj₁-inj₁ : ∀ {ssl-β} {store} {f-name} {A B}
      (arg : (Expr (Δ ,, ssl-β) Γ (Layout-Ty (Layout.name A)))) →
      ∀ {arg′} →
      (prf : (f-name , A , B) ∈ Global-Fn-Type-Env) →
    Expr-Δ-subst-1 To-SSL-Type-Layout store arg (inj₁ arg′) →
    Expr-Δ-subst-1 To-SSL-Type-Layout store (Apply f-name (inj₁ arg) prf) (inj₁ (Apply f-name (inj₁ arg′) prf))

  Expr-Δ-subst-1-Apply-inj₁-inj₂ : ∀ {ssl-β} {store} {f-name} {A B}
      (arg : (Expr (Δ ,, ssl-β) Γ (Layout-Ty (Layout.name A)))) →
      ∀ {arg′} {layout-ty-prf} →
      (prf : (f-name , A , B) ∈ Global-Fn-Type-Env) →
    Expr-Δ-subst-1 To-SSL-Type-Layout store arg (inj₂ (arg′ , layout-ty-prf)) →
    Expr-Δ-subst-1 To-SSL-Type-Layout store (Apply f-name (inj₁ arg) prf) (inj₁ (Apply f-name (inj₂ arg′) prf))

  Expr-Δ-subst-1-Apply-inj₂ : ∀ {ssl-β} {store} {f-name} {A B}
      (arg : Loc) →
      (prf : (f-name , A , B) ∈ Global-Fn-Type-Env) →
    Expr-Δ-subst-1 {C} {Δ} {Γ} {ssl-β} To-SSL-Type-Layout store (Apply f-name (inj₂ arg) prf) (inj₁ (Apply f-name (inj₂ arg) prf))

expr-Δ-subst-1 : ∀ {C} {Δ : Type-Context C} {α ssl-β} {Γ} {ssl-α} → (prf : To-SSL-Type α ssl-α) →
  (store : Store (Δ ,, ssl-β)) →
  (e : Expr (Δ ,, ssl-β) Γ α) →
  ∃[ r ] Expr-Δ-subst-1 prf store e r

args-Δ-subst-1 : ∀ {C} {Δ : Type-Context C} {α} {Γ₀} {Γ} →
  (store : Store (Δ ,, α)) →
  (args : Args (Δ ,, α) Γ₀ Γ) →
  ∃[ args′ ] Args-Δ-subst-1 store args args′
args-Δ-subst-1 store Args-∅ = Args-∅ , Args-Δ-subst-1-∅
args-Δ-subst-1 store (Args-cons x (inj₁ x₁) args) =
  let
    x₁-subst = expr-Δ-subst-1 (proj₂ (to-SSL-Type x)) store x₁
    args-subst = args-Δ-subst-1 store args
  in
  Args-cons x (proj₁ x₁-subst) (proj₁ args-subst) ,
  Args-Δ-subst-1-cons-inj₁ (proj₂ args-subst) (proj₂ x₁-subst)
args-Δ-subst-1 store (Args-cons x (inj₂ y) args) =
  Args-cons x (inj₂ y) (proj₁ (args-Δ-subst-1 store args)) , Args-Δ-subst-1-cons-inj₂ (proj₂ (args-Δ-subst-1 store args))


expr-Δ-subst-1 prf store (V x) = inj₁ (V x) , Expr-Δ-subst-1-V
expr-Δ-subst-1 prf store (Lit x) = inj₁ (Lit x) , Expr-Δ-subst-1-Lit

expr-Δ-subst-1 To-SSL-Type-Int store (SSL-V SSL-Here To-SSL-Type-Int) with store-lookup store SSL-Here in eq
... | Val-Int z = inj₁ (Lit (Val-Int z)) , Expr-Δ-subst-1-SSL-V-Here-Int (sym eq)

expr-Δ-subst-1 To-SSL-Type-Bool store (SSL-V SSL-Here To-SSL-Type-Bool) with store-lookup store SSL-Here in eq
... | Val-Bool z = inj₁ (Lit (Val-Bool z)) , Expr-Δ-subst-1-SSL-V-Here-Bool (sym eq)

expr-Δ-subst-1 To-SSL-Type-Layout store (SSL-V SSL-Here To-SSL-Type-Layout) with store-lookup store SSL-Here in eq
... | Val-Loc z = inj₂ (z , mk-Is-Layout-Type) , Expr-Δ-subst-1-SSL-V-Here-Layout (sym eq)

expr-Δ-subst-1 prf store (SSL-V (SSL-There x) x₁) = inj₁ (SSL-V x x₁) , Expr-Δ-subst-1-SSL-V-There

expr-Δ-subst-1 To-SSL-Type-Int store (Add e e₁) with expr-Δ-subst-1 To-SSL-Type-Int store e | expr-Δ-subst-1 To-SSL-Type-Int store e₁
... | inj₁ x , x-prf | inj₁ y , y-prf = inj₁ (Add x y) , Expr-Δ-subst-1-Add x-prf y-prf
expr-Δ-subst-1 To-SSL-Type-Int store (Sub e e₁) with expr-Δ-subst-1 To-SSL-Type-Int store e | expr-Δ-subst-1 To-SSL-Type-Int store e₁
... | inj₁ x , x-prf | inj₁ y , y-prf = inj₁ (Sub x y) , Expr-Δ-subst-1-Sub x-prf y-prf
expr-Δ-subst-1 To-SSL-Type-Bool store (And e e₁) with expr-Δ-subst-1 To-SSL-Type-Bool store e | expr-Δ-subst-1 To-SSL-Type-Bool store e₁
... | inj₁ x , x-prf | inj₁ y , y-prf = inj₁ (And x y) , Expr-Δ-subst-1-And x-prf y-prf
expr-Δ-subst-1 To-SSL-Type-Bool store (Not e) with expr-Δ-subst-1 To-SSL-Type-Bool store e
... | inj₁ x , x-prf = inj₁ (Not x) , Expr-Δ-subst-1-Not x-prf
expr-Δ-subst-1 To-SSL-Type-Bool store (Equal e e₁) with expr-Δ-subst-1 To-SSL-Type-Int store e | expr-Δ-subst-1 To-SSL-Type-Int store e₁
... | inj₁ x , x-prf | inj₁ y , y-prf = inj₁ (Equal x y) , Expr-Δ-subst-1-Equal x-prf y-prf

expr-Δ-subst-1 {_} {_} {.(Layout-Ty _)} {ssl-β} {_} {Loc-Type} To-SSL-Type-Layout store (Lower constr ssl-param x x₁ x₂ x₃) =
  let
    args-subst = args-Δ-subst-1 store x₁
  in
  inj₁ (Lower constr ssl-param x (proj₁ args-subst) x₂ x₃) , Expr-Δ-subst-1-Lower (proj₂ args-subst)

expr-Δ-subst-1 To-SSL-Type-Layout store (Apply f-name (inj₁ arg) x) with expr-Δ-subst-1 To-SSL-Type-Layout store arg
... | inj₁ arg′ , arg′-prf = inj₁ (Apply f-name (inj₁ arg′) x) , Expr-Δ-subst-1-Apply-inj₁-inj₁ arg _ arg′-prf
... | inj₂ (loc , _) , loc-prf = inj₁ (Apply f-name (inj₂ loc) x) , Expr-Δ-subst-1-Apply-inj₁-inj₂ arg _ loc-prf

expr-Δ-subst-1 To-SSL-Type-Layout store (Apply f-name (inj₂ loc) x) = inj₁ (Apply f-name (inj₂ loc) x) , Expr-Δ-subst-1-Apply-inj₂ loc _

data Fs-Store (h : Heap) : Context → Set where
  Fs-Store-∅ : Fs-Store h ∅
  Fs-Store-cons : ∀ {Γ α} →
    Val α →
    Fs-Store h Γ →
    Fs-Store h (Γ ,, α)
  Fs-Store-cons-loc : ∀ {Γ n dom-h} →
    (loc : Loc) →
    Dom h dom-h →
    loc ∈ dom-h →
    Fs-Store h Γ →
    Fs-Store h (Γ ,, Layout-Ty n)

fs-store-lookup : ∀ {h} {Γ α} → Fs-Store h Γ → Γ ∋ α → Val α ⊎ ∃[ n ] (Loc × α ≡ Layout-Ty n)
fs-store-lookup (Fs-Store-cons x store) Here = inj₁ x
fs-store-lookup (Fs-Store-cons x store) (There var) = fs-store-lookup store var
fs-store-lookup (Fs-Store-cons-loc x Dom-h prf store) (There var) = fs-store-lookup store var
fs-store-lookup (Fs-Store-cons-loc {_} {n} x Dom-h prf store) Here = inj₂ (n , x , refl)

fs-store-lookup′ : ∀ {Γ α} → Fs-Store [] Γ → Γ ∋ α → Val α
fs-store-lookup′ (Fs-Store-cons x store) Here = x
fs-store-lookup′ (Fs-Store-cons x store) (There var) = fs-store-lookup′ store var
fs-store-lookup′ (Fs-Store-cons-loc {_} {n} x Dom-[] () store) prf-2

weaken-fs-store-[] : ∀ {h Γ} → Fs-Store [] Γ → Fs-Store h Γ
weaken-fs-store-[] {h} {.∅} Fs-Store-∅ = Fs-Store-∅
weaken-fs-store-[] {h} {.(_ ,, _)} (Fs-Store-cons x prf) = Fs-Store-cons x (weaken-fs-store-[] prf)
weaken-fs-store-[] {h} {.(_ ,, Layout-Ty _)} (Fs-Store-cons-loc loc Dom-[] () prf)

weaken-fs-store-inj₁ : ∀ {h h₁ h₂ Γ} →
  h₁ ∘ h₂ == h →
  Fs-Store h₁ Γ →
  Fs-Store h Γ
weaken-fs-store-inj₁ (mk-∘ _ _ _ x x₁) Fs-Store-∅ = Fs-Store-∅
weaken-fs-store-inj₁ prf@(mk-∘ _ _ _ x x₁) (Fs-Store-cons x₂ fs-store) = Fs-Store-cons x₂ (weaken-fs-store-inj₁ prf fs-store)
weaken-fs-store-inj₁ prf@(mk-∘ _ _ _ x x₁) (Fs-Store-cons-loc loc x₂ x₃ fs-store) =
  let
    z , w = x₁
    z′ = z (Loc-Type , loc , Dom-non-null x₂ x₃ , (Val-Loc loc)) {!!}
  in
  Fs-Store-cons-loc loc (proj₂ Dom-exists) {!!} (weaken-fs-store-inj₁ prf fs-store)

data To-SSL-Val′ : ∀ {α ssl-α} → (Val α ⊎ ∃[ n ] (Loc × α ≡ Layout-Ty n)) → SSL-Val ssl-α → Set where
  To-SSL-Val′-Int : ∀ {i} → To-SSL-Val′ (inj₁ (Val-Int i)) (Val-Int i)
  To-SSL-Val′-Bool : ∀ {b} → To-SSL-Val′ (inj₁ (Val-Bool b)) (Val-Bool b)
  To-SSL-Val′-Loc : ∀ {n loc prf} → To-SSL-Val′ {Layout-Ty n} (inj₂ (n , loc , prf)) (Val-Loc loc)

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


-- data SSL-Vars→Fs-Store : ∀ {C} {Δ : Type-Context C} {Γ} (store : Store Δ) → SSL-Vars Δ Γ → Fs-Store ? Γ → Set where
--   SSL-Vars→Fs-Store-∅ : ∀ {C} {Δ : Type-Context C} {store} → SSL-Vars→Fs-Store {C} {Δ} store SSL-Vars-∅ Fs-Store-∅
--   SSL-Vars→Fs-Store-cons : ∀ {C} {Δ : Type-Context C} {Γ α} {ssl-α} {store} {ssl-prf : To-SSL-Type α ssl-α} {var : SSL-Var Δ ssl-α} {rest} {rest′}
--                              {val} →
--     SSL-Vars→Fs-Store {C} {Δ} {Γ} store rest rest′ →
--     To-SSL-Val val (store-lookup store var) →
--     (prf : To-SSL-Type α ssl-α) →
--     SSL-Vars→Fs-Store store (SSL-Vars-cons prf var rest) (Fs-Store-cons val rest′)

-- SSL-Vars→Fs-Store-exists : ∀ {C} {Δ : Type-Context C} {Γ} (store : Store Δ) → (vars : SSL-Vars Δ Γ) → ∃[ fs-store ] SSL-Vars→Fs-Store store vars fs-store
-- SSL-Vars→Fs-Store-exists store SSL-Vars-∅ = Fs-Store-∅ , SSL-Vars→Fs-Store-∅
-- SSL-Vars→Fs-Store-exists store (SSL-Vars-cons x x₁ vars)
--   with store-lookup store x₁ in eq
-- SSL-Vars→Fs-Store-exists store (SSL-Vars-cons x x₁ vars) | Val-Loc x₂ =
--   let
--     vars′ , prf′ = SSL-Vars→Fs-Store-exists store vars
--   in
--   Fs-Store-cons {!!} {!!} , SSL-Vars→Fs-Store-cons prf′ {!!} x
-- SSL-Vars→Fs-Store-exists store (SSL-Vars-cons x x₁ vars) | Val-Int x₂ = {!!}
-- SSL-Vars→Fs-Store-exists store (SSL-Vars-cons x x₁ vars) | Val-Bool x₂ = {!!}

-- data Fs-Store-app : ∀ {Γ Γ′ Γ′′} → Fs-Store Γ → Fs-Store Γ′ → Fs-Store Γ′′ → Set where
--   Fs-Store-app-∅ : ∀ {Γ} {store : Fs-Store Γ} → Fs-Store-app Fs-Store-∅ store store
--   Fs-Store-app-cons : ∀ {Γ Γ′ Γ′′} {α}
--                         {store-1 : Fs-Store Γ} {store-2 : Fs-Store Γ′} {store′ : Fs-Store Γ′′} {val : Val α} →
--     Fs-Store-app store-1 store-2 store′ →
--     Fs-Store-app (Fs-Store-cons val store-1) store-2 (Fs-Store-cons val store′)

-- Args→Fs-Store : ∀ {C} {Δ : Type-Context C} {Γ₀ Γ} →
--   Fs-Store Γ₀ →
--   Store Δ →
--   (Args Δ Γ₀ Γ) →
--   Fs-Store Γ
-- Args→Fs-Store fs-store store Args-∅ = Fs-Store-∅
-- Args→Fs-Store fs-store store (Args-cons x (inj₂ (fst , mk-Is-Layout-Type)) args) =
--   -- let
--   --   z = 
--   -- in
--   Fs-Store-cons {!!} (Args→Fs-Store fs-store store args)
-- Args→Fs-Store fs-store store (Args-cons x (inj₁ x₁) args) = {!!}

-- close-Args : ∀ {C} {Δ : Type-Context C} {Γ₀ Γ} →
--   Fs-Store Γ₀ →
--   Store Δ →
--   Args Δ Γ₀ Γ →
--   Args ε ∅ Γ

-- close-Expr :  ∀ {C} {Δ : Type-Context C} {Γ α} →
--   Fs-Store Γ →
--   Store Δ →
--   Expr Δ Γ α →
--   Expr ε ∅ α
-- close-Expr fs-store store (V x) = Lit (fs-store-lookup fs-store x)
-- close-Expr fs-store store (Lit x) = Lit x
-- close-Expr fs-store store (SSL-V x x₁) = {!!}
-- close-Expr fs-store store (Add e e₁) = Add (close-Expr fs-store store e₁) (close-Expr fs-store store e₁)
-- close-Expr fs-store store (Sub e e₁) = Sub (close-Expr fs-store store e₁) (close-Expr fs-store store e₁)
-- close-Expr fs-store store (And e e₁) = And (close-Expr fs-store store e₁) (close-Expr fs-store store e₁)
-- close-Expr fs-store store (Not e) = Not (close-Expr fs-store store e)
-- close-Expr fs-store store (Equal e e₁) = Equal (close-Expr fs-store store e₁) (close-Expr fs-store store e₁)
-- close-Expr fs-store store (Lower constr ssl-param x x₁ x₂ x₃) = Lower constr ssl-param x (close-Args fs-store store x₁) x₂ x₃
-- close-Expr fs-store store (Apply f-name (inj₁ x₁) x) = Apply f-name (inj₁ (close-Expr fs-store store x₁)) x
-- close-Expr fs-store store (Apply f-name (inj₂ y) x) = Apply f-name (inj₂ y) x

-- close-Args fs-store store Args-∅ = Args-∅
-- close-Args fs-store store (Args-cons x (inj₁ x₁) args) = Args-cons x (inj₁ {!!}) (close-Args fs-store store args)
-- close-Args fs-store store (Args-cons x (inj₂ y) args) =
--   Args-cons x (inj₂ y) (close-Args fs-store store args)

-- data To-SSL-Context : ∀ {C} → Context → Type-Context C → Set where
--   To-SSL-Context-Z : To-SSL-Context ∅ ε
--   To-SSL-Context-S : ∀ {C} {Γ α ssl-α Δ} →
--     To-SSL-Type α ssl-α →
--     To-SSL-Context {C} Γ Δ →
--     To-SSL-Context (Γ ,, α) (Δ ,, ssl-α)

-- data To-Store : ∀ {C} {Δ : Type-Context C} {Γ} → Fs-Store Γ → Store Δ → Set where
--   To-Store-∅ : To-Store Fs-Store-∅ Store-[]
--   To-Store-cons : ∀ {C} {Δ : Type-Context C} {Γ α ssl-α}
--                     {val : Val α}
--                     {ssl-val : SSL-Val ssl-α}
--                     {fs-store : Fs-Store Γ}
--                     {store : Store Δ} →
--     To-SSL-Type α ssl-α →
--     To-SSL-Val val ssl-val →
--     To-Store fs-store store →
--     To-Store (Fs-Store-cons val fs-store) (Store-cons ssl-val store)

-- -- to-SSL-Context : Context → ∃[ C ] Type-Context C
-- -- to-SSL-Context ∅ = Z , ε
-- -- to-SSL-Context (Γ ,, x) with to-SSL-Context Γ
-- -- ... | n , Δ = S n , ({!!} ,, to-SSL

-- -- Fs-Store→Store : Fs-Store Γ → 

-- Lit-has-Base-Type : ∀ {C} {Δ : Type-Context C} {Γ} {α} (x : Val α) (e : Expr Δ Γ α) → e ≡ Lit x → Base-Type α
-- Lit-has-Base-Type (Val-Int x) .(Lit (Val-Int x)) refl = Base-Type-Int
-- Lit-has-Base-Type (Val-Bool x) .(Lit (Val-Bool x)) refl = Base-Type-Bool

-- Base-Type-to-SSL : ∀ {α} → Base-Type α → ∃[ ssl-α ] To-SSL-Type α ssl-α
-- Base-Type-to-SSL Base-Type-Int = Int-Type , To-SSL-Type-Int
-- Base-Type-to-SSL Base-Type-Bool = Bool-Type , To-SSL-Type-Bool

-- to-SSL-Type-unique : ∀ {α ssl-α-1 ssl-α-2} → To-SSL-Type α ssl-α-1 → To-SSL-Type α ssl-α-2 → ssl-α-1 ≡ ssl-α-2
-- to-SSL-Type-unique To-SSL-Type-Int To-SSL-Type-Int = refl
-- to-SSL-Type-unique To-SSL-Type-Bool To-SSL-Type-Bool = refl
-- to-SSL-Type-unique To-SSL-Type-Layout To-SSL-Type-Layout = refl
