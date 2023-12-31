-- Based on "Automatic Cyclic Termination Proofs for Recursive Procedures in Separation Logic"

open import Data.Nat hiding (_+_; _*_; _⊔_; _⊓_; _≤′_)
open import Data.Integer hiding (_≤_; _⊔_; _⊓_; _<_; ∣_∣)
open import Data.Bool hiding (_≤_; _<_)
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Maybe
open import Data.Product
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Relation.Nullary
open import Data.List.Relation.Unary.Any

open import Agda.Primitive hiding (_⊔_)

module SSL
  (Pred-Name : Set)
  (Pred-Label : Set)
  (Loc-Name : Set)
  where

open import HeapDefs (Loc-Name)

-- infix  4 _⊨[_]_
infixl 5  _,,_

Labeled-Pred-Name : Set
Labeled-Pred-Name = Pred-Name × Pred-Label

get-Pred-Name : Labeled-Pred-Name → Pred-Name
get-Pred-Name = proj₁

Pred-Name-label : Labeled-Pred-Name → Pred-Label
Pred-Name-label = proj₂

-- record Loc : Set where
--   field
--     name : Loc-Name
--     ix : ℕ

Loc-incr : Loc → ℕ → Loc
Loc-incr Null i = Null
Loc-incr (mk-Loc x x₁) i = mk-Loc x (x₁ Data.Nat.+ i)

-- | Program variable (store) context
data SSL-Context : Set where
  Z : SSL-Context
  S : SSL-Context → SSL-Context

-- data Ixed A : Set where
--   [_:+_] : A → ℕ → Ixed A

data Exist-Context : Set where
  Exist-Z : Exist-Context
  Exist-S : Exist-Context → Exist-Context

data E-Type-Context : (E : Exist-Context) → Set where
  ε : E-Type-Context Exist-Z
  _,,_ : ∀ {E} → E-Type-Context E → SSL-Type → E-Type-Context (Exist-S E)

data Type-Context : (C : SSL-Context) → Set where
  ε : Type-Context Z
  _,,_ : ∀ {C} → Type-Context C → SSL-Type → Type-Context (S C)


data SSL-Var : {C : SSL-Context} → (Γ : Type-Context C) → SSL-Type → Set where
  SSL-Here : ∀ {C Γ α} → SSL-Var {S C} (Γ ,, α) α
  SSL-There : ∀ {C Γ α β} → SSL-Var {C} Γ α → SSL-Var {S C} (Γ ,, β) α

-- SSL-Var : SSL-Context → Set
-- SSL-Var C = Ixed (SSL-Var₀ C)

data Exist-Var : {E : Exist-Context} → (Δ : E-Type-Context E) → SSL-Type → Set where
  EV-Here : ∀ {E Δ α} → Exist-Var {Exist-S E} (Δ ,, α) α
  EV-There : ∀ {E Δ α β} → Exist-Var {E} Δ α → Exist-Var {Exist-S E} (Δ ,, β) α


data SSL-Expr {C : SSL-Context} {E : Exist-Context} (Γ : Type-Context C) (Δ : E-Type-Context E) : SSL-Type → Set where
  V : ∀ {α} → SSL-Var Γ α → SSL-Expr Γ Δ α
  Exists-V : ∀ {α} → Exist-Var Δ α → SSL-Expr Γ Δ α
  -- Exists-Intro : SSL-Expr A (Exist-S E) → SSL-Expr C E
  -- Int-Lit : ℤ → SSL-Expr C E
  -- Bool-Lit : Bool → SSL-Expr C E
  -- Loc-Lit : Loc → SSL-Expr C E
  Lit : ∀ {α} → Val α → SSL-Expr Γ Δ α
  Add : SSL-Expr Γ Δ Int-Type → SSL-Expr Γ Δ Int-Type → SSL-Expr Γ Δ Int-Type
  Loc-Ix : SSL-Expr Γ Δ Loc-Type → ℕ → SSL-Expr Γ Δ Loc-Type
  Sub : SSL-Expr Γ Δ Int-Type → SSL-Expr Γ Δ Int-Type → SSL-Expr Γ Δ Int-Type
  And : SSL-Expr Γ Δ Bool-Type → SSL-Expr Γ Δ Bool-Type → SSL-Expr Γ Δ Bool-Type
  Not : SSL-Expr Γ Δ Bool-Type → SSL-Expr Γ Δ Bool-Type
  Equal : ∀ {α} → SSL-Expr Γ Δ α → SSL-Expr Γ Δ α → SSL-Expr Γ Δ Bool-Type

[_∣_]⊢_ : ∀ {C : SSL-Context} {E : Exist-Context} (Γ : Type-Context C) (Δ : E-Type-Context E) → SSL-Type → Set
[ Γ ∣ Δ ]⊢ α = SSL-Expr Γ Δ α

----

E-ext : ∀ {E E′ : Exist-Context} {Δ : E-Type-Context E} {Δ′ : E-Type-Context E′} →
  (∀ {α} → Exist-Var Δ α → Exist-Var Δ′ α) →
  (∀ {α β} → Exist-Var (Δ ,, β) α → Exist-Var (Δ′ ,, β) α)
E-ext ρ EV-Here = EV-Here
E-ext ρ (EV-There ev) = EV-There (ρ ev)

E-rename : ∀ {C} {E E′ : Exist-Context} {Γ : Type-Context C} {Δ : E-Type-Context E} {Δ′ : E-Type-Context E′} →
  (∀ {α} → Exist-Var Δ α → Exist-Var Δ′ α) →
  (∀ {α} → SSL-Expr Γ Δ α → SSL-Expr Γ Δ′ α)
E-rename ρ (V x) = V x
E-rename ρ (Exists-V x) = Exists-V (ρ x)
E-rename ρ (Lit x) = Lit x
E-rename ρ (Add e e₁) = Add (E-rename ρ e) (E-rename ρ e₁)
E-rename ρ (Loc-Ix loc i) = Loc-Ix (E-rename ρ loc) i
E-rename ρ (Sub e e₁) = Sub (E-rename ρ e) (E-rename ρ e₁)
E-rename ρ (And e e₁) = And (E-rename ρ e) (E-rename ρ e₁)
E-rename ρ (Not e) = Not (E-rename ρ e)
E-rename ρ (Equal e e₁) = Equal (E-rename ρ e) (E-rename ρ e₁)

E-exts : ∀ {C} {E E′ : Exist-Context} {Γ : Type-Context C} {Δ : E-Type-Context E} {Δ′ : E-Type-Context E′} →
  (∀ {α} → Exist-Var Δ α → SSL-Expr Γ Δ′ α) →
  (∀ {α β} → Exist-Var (Δ ,, β) α → SSL-Expr Γ (Δ′ ,, β) α)
E-exts ρ EV-Here = Exists-V EV-Here
E-exts ρ (EV-There ev) = E-rename EV-There (ρ ev)

E-subst : ∀ {C} {E E′ : Exist-Context} {Γ : Type-Context C} {Δ : E-Type-Context E} {Δ′ : E-Type-Context E′} →
  (∀ {α} → Exist-Var Δ α → SSL-Expr Γ Δ′ α) →
  (∀ {α} → SSL-Expr Γ Δ α → SSL-Expr Γ Δ′ α)
E-subst σ (V x) = V x
E-subst σ (Exists-V x) = σ x
E-subst σ (Lit x) = Lit x
E-subst σ (Add e e₁) = Add (E-subst σ e) (E-subst σ e₁)
E-subst σ (Loc-Ix loc i) = Loc-Ix (E-subst σ loc) i
E-subst σ (Sub e e₁) = Sub (E-subst σ e) (E-subst σ e₁)
E-subst σ (And e e₁) = And (E-subst σ e) (E-subst σ e₁)
E-subst σ (Not e) = Not (E-subst σ e)
E-subst σ (Equal e e₁) = Equal (E-subst σ e) (E-subst σ e₁)

E-subst-1 : ∀ {C} {E : Exist-Context} {Γ : Type-Context C} {Δ : E-Type-Context E} {α β} →
  SSL-Expr Γ (Δ ,, β) α →
  SSL-Expr Γ Δ β →
  SSL-Expr Γ Δ α
E-subst-1 {C} {E} {Γ} {Δ} {α} {β} N M = E-subst σ N
  where
    σ : ∀ {γ} → Exist-Var (Δ ,, β) γ → SSL-Expr Γ Δ γ
    σ EV-Here = M
    σ (EV-There ev) = Exists-V ev

-- E-subst-1-V : ∀ {C} {E : Exist-Context} {x} → {M : SSL-Expr C E} →
--   E-subst-1 (V x) M ≡ V x
-- E-subst-1-V {C} {E} {x} {M} = refl

----

V-ext : ∀ {C C′ : SSL-Context} {Γ : Type-Context C} {Γ′ : Type-Context C′} →
  (∀ {α} → SSL-Var Γ α → SSL-Var Γ′ α) →
  (∀ {α β} → SSL-Var (Γ ,, β) α → SSL-Var (Γ′ ,, β) α)
V-ext ρ SSL-Here = SSL-Here
V-ext ρ (SSL-There ev) = SSL-There (ρ ev)

V-rename : ∀ {C C′} {E} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} →
  (∀ {α} → SSL-Var Γ α → SSL-Var Γ′ α) →
  (∀ {α} → SSL-Expr Γ Δ α → SSL-Expr Γ′ Δ α)
V-rename ρ (V x) = V (ρ x)
V-rename ρ (Exists-V x) = Exists-V x
V-rename ρ (Lit x) = Lit x
V-rename ρ (Add e e₁) = Add (V-rename ρ e) (V-rename ρ e₁)
V-rename ρ (Loc-Ix loc i) = Loc-Ix (V-rename ρ loc) i
V-rename ρ (Sub e e₁) = Sub (V-rename ρ e) (V-rename ρ e₁)
V-rename ρ (And e e₁) = And (V-rename ρ e) (V-rename ρ e₁)
V-rename ρ (Not e) = Not (V-rename ρ e)
V-rename ρ (Equal e e₁) = Equal (V-rename ρ e) (V-rename ρ e₁)

V-exts : ∀ {C C′} {E} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} →
  (∀ {α} → SSL-Var Γ α → SSL-Expr Γ′ Δ α) →
  (∀ {α β} → SSL-Var (Γ ,, β) α → SSL-Expr (Γ′ ,, β) Δ α)
V-exts ρ SSL-Here = V SSL-Here
V-exts ρ (SSL-There ev) = V-rename SSL-There (ρ ev)

V-subst : ∀ {C C′} {E} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} →
  (∀ {α} → SSL-Var Γ α → SSL-Expr Γ′ Δ α) →
  (∀ {α} → SSL-Expr Γ Δ α → SSL-Expr Γ′ Δ α)
V-subst σ (V x) = σ x
V-subst σ (Exists-V x) = Exists-V x
V-subst σ (Lit x) = Lit x
V-subst σ (Add e e₁) = Add (V-subst σ e) (V-subst σ e₁)
V-subst σ (Loc-Ix loc i) = Loc-Ix (V-subst σ loc) i
V-subst σ (Sub e e₁) = Sub (V-subst σ e) (V-subst σ e₁)
V-subst σ (And e e₁) = And (V-subst σ e) (V-subst σ e₁)
V-subst σ (Not e) = Not (V-subst σ e)
V-subst σ (Equal e e₁) = Equal (V-subst σ e) (V-subst σ e₁)

-- -- V-subst-Exists-V : ∀ {C C′} {E : Exist-Context} {x} →
-- --   (σ : SSL-Var C → SSL-Expr C′ E) →
-- --   V-subst σ (Exists-V x) ≡ Exists-V x
-- -- V-subst-Exists-V σ = refl

V-subst-1 : ∀ {C} {E : Exist-Context} {Γ : Type-Context C} {Δ : E-Type-Context E} {α β} →
  SSL-Expr (Γ ,, β) Δ α →
  SSL-Expr Γ Δ β →
  SSL-Expr Γ Δ α
V-subst-1 {C} {E} {Γ} {Δ} {α} {β} N M = V-subst σ N
  where
    σ : ∀ {γ} → SSL-Var (Γ ,, β) γ → SSL-Expr Γ Δ γ
    σ SSL-Here = M
    σ (SSL-There v) = V v

Vec-Elem : Set₁
Vec-Elem = ∀ {C : SSL-Context} {E : Exist-Context} (Γ : Type-Context C) (Δ : E-Type-Context E) → SSL-Type → Set

data Vec (P : Vec-Elem) {C₀ : SSL-Context} {E : Exist-Context} (Γ₀ : Type-Context C₀) (Δ : E-Type-Context E)  : {C : SSL-Context} → (Γ : Type-Context C) → Set where
  Vec-Z : Vec P Γ₀ Δ ε
  Vec-S : ∀ {C Γ α} → P Γ₀ Δ α → Vec P Γ₀ Δ {C} Γ → Vec P Γ₀ Δ (Γ ,, α)
  -- Vec-Z : A → Vec A Z
  -- Vec-S : ∀ {Γ} → A → Vec A Γ → Vec A (S Γ)

Vec-map : ∀ {P : Vec-Elem} {C C′} {E E′} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} {Δ′ : E-Type-Context E′} → (∀ {α} → P Γ Δ α → P Γ Δ′ α) → Vec P Γ Δ Γ′ → Vec P Γ Δ′ Γ′
Vec-map f Vec-Z = Vec-Z
Vec-map f (Vec-S x v) = Vec-S (f x) (Vec-map f v)

Expr-Vec : ∀ {C₀ : SSL-Context}  {E : Exist-Context} (Γ₀ : Type-Context C₀) (Δ : E-Type-Context E) {C : SSL-Context} (Γ : Type-Context C) → Set
Expr-Vec = Vec SSL-Expr

Expr-Vec′ : ∀ {C E} (Γ : Type-Context C) (Δ : E-Type-Context E) → Set
Expr-Vec′ Γ Δ = Expr-Vec Γ Δ Γ

Val-Vec : ∀ {C₀ : SSL-Context}  {E : Exist-Context} (Γ₀ : Type-Context C₀) (Δ : E-Type-Context E) {C : SSL-Context} (Γ : Type-Context C) → Set
Val-Vec = Vec (λ _ _ → Val)

Val-Vec′ : ∀ {C E} (Γ : Type-Context C) (Δ : E-Type-Context E) → Set
Val-Vec′ Γ Δ = Val-Vec Γ Δ Γ

Val-Vec-any-Δ : ∀ {C C′ E E′} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} {Δ′ : E-Type-Context E′} → Val-Vec Γ Δ Γ′ → Val-Vec Γ Δ′ Γ′
Val-Vec-any-Δ {_} {_} {E} {E′} {Γ} {.ε} {Δ} {Δ′} Vec-Z = Vec-Z
Val-Vec-any-Δ {_} {_} {E} {E′} {Γ} {.(_ ,, _)} {Δ} {Δ′} (Vec-S x v) = Vec-S x (Val-Vec-any-Δ v)

-- Store : ∀ {C} (Γ : Type-Context C) → Set
-- Store Γ = ∀ {α} → SSL-Var Γ α → Val α

data Store : ∀ {C} (Γ : Type-Context C) → Set where
  Store-[] : Store ε
  Store-cons : ∀ {C} {Γ : Type-Context C} {α} →
    (val : Val α) →
    Store Γ →
    Store (Γ ,, α)

store-lookup : ∀ {C} {Γ : Type-Context C} {α} → Store Γ → SSL-Var Γ α → Val α
store-lookup {.(S _)} {.(_ ,, α)} {α} (Store-cons val store) SSL-Here = val
store-lookup {.(S _)} {.(_ ,, _)} {α} (Store-cons val store) (SSL-There var) =
  store-lookup store var

SSL-Ctx-+ : SSL-Context → SSL-Context → SSL-Context
SSL-Ctx-+ Z b = b
SSL-Ctx-+ a Z = a
SSL-Ctx-+ (S a) b = S (SSL-Ctx-+ a b)

data Ctx-⊔ : ∀ {C C′} → Type-Context C → Type-Context C′ → Type-Context (SSL-Ctx-+ C C′) → Set where
  Ctx-⊔-ε-ε : Ctx-⊔ ε ε ε
  Ctx-⊔-ε-cons : ∀ {C′} {Γ′ β} → Ctx-⊔ {Z} {S C′} ε (Γ′ ,, β) (Γ′ ,, β)
  Ctx-⊔-cons-ε : ∀ {C} {Γ α} → Ctx-⊔ {S C} {Z} (Γ ,, α) ε (Γ ,, α)
  Ctx-⊔-cons-cons : ∀ {C C′} {Γ Γ′ α β} {r} →
    Ctx-⊔ {C} {S C′} Γ (Γ′ ,, β) r →
    Ctx-⊔ (Γ ,, α) (Γ′ ,, β) (r ,, α)

Ctx-⊔-exists : ∀ {C C′} → {Γ : Type-Context C} → {Γ′ : Type-Context C′} → ∃[ Γ⊔Γ′ ] Ctx-⊔ Γ Γ′ Γ⊔Γ′
Ctx-⊔-exists {_} {_} {ε} {ε} = ε , Ctx-⊔-ε-ε
Ctx-⊔-exists {_} {_} {ε} {Γ′ ,, x} = Γ′ ,, x , Ctx-⊔-ε-cons
Ctx-⊔-exists {_} {_} {Γ ,, x} {ε} = Γ ,, x , Ctx-⊔-cons-ε
Ctx-⊔-exists {_} {_} {Γ ,, x} {Γ′ ,, x₁} =
  let
    z , z-prf = Ctx-⊔-exists {_} {_} {Γ} {Γ′ ,, x₁}
  in
  (z ,, x) , Ctx-⊔-cons-cons z-prf

Ctx-⊔-inj₁ : ∀ {α} {C C′} → {Γ : Type-Context C} → {Γ′ : Type-Context C′} → ∀ {Γ′′} → Ctx-⊔ Γ Γ′ Γ′′ → SSL-Var Γ α → SSL-Var Γ′′ α
Ctx-⊔-inj₁ Ctx-⊔-ε-ε ()
Ctx-⊔-inj₁ Ctx-⊔-ε-cons ()
Ctx-⊔-inj₁ Ctx-⊔-cons-ε SSL-Here = SSL-Here
Ctx-⊔-inj₁ Ctx-⊔-cons-ε (SSL-There var) = SSL-There var
Ctx-⊔-inj₁ (Ctx-⊔-cons-cons prf) SSL-Here = SSL-Here
Ctx-⊔-inj₁ (Ctx-⊔-cons-cons prf) (SSL-There var) = SSL-There (Ctx-⊔-inj₁ prf var)

Ctx-⊔-inj₂ : ∀ {α} {C C′} → {Γ : Type-Context C} → {Γ′ : Type-Context C′} → ∀ {Γ′′} → Ctx-⊔ Γ Γ′ Γ′′ → SSL-Var Γ′ α → SSL-Var Γ′′ α
Ctx-⊔-inj₂ Ctx-⊔-ε-ε ()
Ctx-⊔-inj₂ Ctx-⊔-ε-cons SSL-Here = SSL-Here
Ctx-⊔-inj₂ Ctx-⊔-ε-cons (SSL-There var) = SSL-There var
Ctx-⊔-inj₂ Ctx-⊔-cons-ε ()
Ctx-⊔-inj₂ (Ctx-⊔-cons-cons prf) SSL-Here = SSL-There (Ctx-⊔-inj₂ prf SSL-Here)
Ctx-⊔-inj₂ (Ctx-⊔-cons-cons prf) (SSL-There var) = SSL-There (Ctx-⊔-inj₂ prf (SSL-There var))

Ctx-⊔-store : ∀ {C C′} → {Γ : Type-Context C} → {Γ′ : Type-Context C′} → ∀ {Γ⊔Γ′} → Ctx-⊔ Γ Γ′ Γ⊔Γ′ → Store Γ → Store Γ′ → Store Γ⊔Γ′
Ctx-⊔-store Ctx-⊔-ε-ε Store-[] Store-[] = Store-[]
Ctx-⊔-store Ctx-⊔-ε-cons Store-[] (Store-cons val store-2) = Store-cons val store-2
Ctx-⊔-store Ctx-⊔-cons-ε (Store-cons val store-1) Store-[] = Store-cons val store-1
Ctx-⊔-store (Ctx-⊔-cons-cons prf) (Store-cons val store-1) (Store-cons val₁ store-2) =
  Store-cons val (Ctx-⊔-store prf store-1 (Store-cons val₁ store-2))

-- Ctx-⊔ : ∀ {C C′} → Type-Context C → Type-Context C′ → Type-Context (SSL-Ctx-+ C C′)
-- Ctx-⊔ ε ε = ε
-- Ctx-⊔ ε (b ,, x) = b ,, x
-- Ctx-⊔ (a ,, x) ε = a ,, x
-- Ctx-⊔ (a ,, x) (b ,, x₁) = Ctx-⊔ a (b ,, x₁) ,, x

-- Ctx-⊔-inj₁ : ∀ {α} {C C′} → {Γ : Type-Context C} → {Γ′ : Type-Context C′} → SSL-Var Γ α → SSL-Var (Ctx-⊔ Γ Γ′) α
-- Ctx-⊔-inj₁ {_} {_} {_} {Γ ,, x} {ε} SSL-Here = SSL-Here
-- Ctx-⊔-inj₁ {_} {_} {_} {Γ ,, x} {Γ′ ,, x₁} SSL-Here = SSL-Here
-- Ctx-⊔-inj₁ {_} {_} {_} {Γ ,, x} {ε} (SSL-There var) = SSL-There var
-- Ctx-⊔-inj₁ {_} {_} {_} {Γ ,, x} {Γ′ ,, x₁} (SSL-There var) = SSL-There (Ctx-⊔-inj₁ var)

-- Ctx-⊔-inj₂ : ∀ {α} {C C′} → {Γ : Type-Context C} → {Γ′ : Type-Context C′} → SSL-Var Γ′ α → SSL-Var (Ctx-⊔ Γ Γ′) α
-- Ctx-⊔-inj₂ {_} {_} {_} {ε} {Γ′ ,, x} SSL-Here = SSL-Here
-- Ctx-⊔-inj₂ {_} {_} {_} {ε} {Γ′ ,, x} (SSL-There var) = SSL-There var
-- Ctx-⊔-inj₂ {_} {_} {_} {Γ ,, x} {Γ′ ,, x₁} SSL-Here = SSL-There (Ctx-⊔-inj₂ {_} {_} {_} {Γ} {Γ′ ,, x₁} SSL-Here)
-- Ctx-⊔-inj₂ {_} {_} {_} {Γ ,, x} {Γ′ ,, x₁} (SSL-There var) = SSL-There (Ctx-⊔-inj₂ {_} {_} {_} {Γ} {Γ′ ,, x₁} (SSL-There var))

-- data _S[_↦_]==_ : ∀ {C} {Γ : Type-Context C} → Store Γ → where
--   -- Store-update-here 

E-Store-ap : ∀ {C} {E} {Γ : Type-Context C} {Δ : E-Type-Context E} {α} → Store Γ → SSL-Expr Γ Δ α → SSL-Expr Γ Δ α
E-Store-ap s e = V-subst (λ x → Lit (store-lookup s x)) e

module Ambient-Context
  {C : SSL-Context}
  {E : Exist-Context}
  (Γ : Type-Context C)
  (Δ : E-Type-Context E)
  -- (get-Pred-C : Labeled-Pred-Name → SSL-Context)
  -- (get-Pred-E : Labeled-Pred-Name → Exist-Context)
  -- (get-Pred-Γ : (n : Labeled-Pred-Name) → Type-Context (get-Pred-C n))
  -- (get-Pred-Δ : (n : Labeled-Pred-Name) → E-Type-Context (get-Pred-E n))
  where

  -- get-Pred-Type : Labeled-Pred-Name → Set
  -- get-Pred-Type n = Vec′ (get-Pred-Γ n) (get-Pred-Δ n)

  data Heaplet : Set where
    Points-To : ∀ {α} → (lhs : SSL-Expr Γ Δ Loc-Type) → SSL-Expr Γ Δ α → Heaplet
    -- [_,,_] : A → ℕ → Heaplet C
    _·_ : (n : Labeled-Pred-Name) → Expr-Vec′ Γ Δ → Heaplet

  record Assertion : Set where
    field
      pure : SSL-Expr Γ Δ Bool-Type
      spatial : List Heaplet

  record Ind-Pred-Branch : Set where
    field
      cond : SSL-Expr Γ Δ Bool-Type
      body : Assertion

  record Ind-Pred (n : Pred-Name) : Set where
    field
      branches : List Ind-Pred-Branch

  record Ind-Rule : Set where
    field
      name : Pred-Name
      assertion : Assertion

  H-Store-ap : Store Γ → Heaplet → Heaplet
  H-Store-ap s (Points-To lhs x) = Points-To (E-Store-ap s lhs) (E-Store-ap s x)
  H-Store-ap s (P · x) = P · Vec-map (E-Store-ap s) x

  A-Store-ap : Store Γ → Assertion → Assertion
  A-Store-ap s record { pure = pure ; spatial = spatial } =
    record
      { pure = E-Store-ap s pure
      ; spatial = Data.List.map (H-Store-ap s) spatial
      }

  data SSL-Expr-Val-⇓ (store : Store Γ) : ∀ {α} → SSL-Expr Γ Δ α → Val α → Set where
    SSL-Expr-Val-⇓-V : ∀ {α x} →
      SSL-Expr-Val-⇓ store {α} (V x) (store-lookup store x)
    SSL-Expr-Val-⇓-Lit : ∀ {α v} →
      SSL-Expr-Val-⇓ store {α} (Lit v) v

    SSL-Expr-Val-⇓-Add : ∀ {x y x-val y-val} →
      SSL-Expr-Val-⇓ store x (Val-Int x-val) →
      SSL-Expr-Val-⇓ store y (Val-Int y-val) →
      SSL-Expr-Val-⇓ store (Add x y) (Val-Int (x-val + y-val))

    SSL-Expr-Val-⇓-Loc-Ix : ∀ {x x-val i} →
      SSL-Expr-Val-⇓ store x (Val-Loc x-val) →
      SSL-Expr-Val-⇓ store (Loc-Ix x i) (Val-Loc (Loc-incr x-val i))

    SSL-Expr-Val-⇓-Sub : ∀ {x y x-val y-val} →
      SSL-Expr-Val-⇓ store x (Val-Int x-val) →
      SSL-Expr-Val-⇓ store y (Val-Int y-val) →
      SSL-Expr-Val-⇓ store (Sub x y) (Val-Int (x-val - y-val))

    SSL-Expr-Val-⇓-And : ∀ {x y x-val y-val} →
      SSL-Expr-Val-⇓ store x (Val-Bool x-val) →
      SSL-Expr-Val-⇓ store y (Val-Bool y-val) →
      SSL-Expr-Val-⇓ store (And x y) (Val-Bool (x-val ∧ y-val))

    SSL-Expr-Val-⇓-Not : ∀ {x x-val} →
      SSL-Expr-Val-⇓ store x (Val-Bool x-val) →
      SSL-Expr-Val-⇓ store (Not x) (Val-Bool (not x-val))

    SSL-Expr-Val-⇓-Equal-true : ∀ {α x y x-val y-val} →
      SSL-Expr-Val-⇓ store {α} x x-val →
      SSL-Expr-Val-⇓ store y y-val →
      x-val ≡ y-val →
      SSL-Expr-Val-⇓ store (Equal x y) (Val-Bool true)

    SSL-Expr-Val-⇓-Equal-false : ∀ {α x y x-val y-val} →
      SSL-Expr-Val-⇓ store {α} x x-val →
      SSL-Expr-Val-⇓ store y y-val →
      x-val ≢ y-val →
      SSL-Expr-Val-⇓ store (Equal x y) (Val-Bool false)

  -- data SSL-Expr′-⇓ (store : Store) : SSL-Expr Γ Δ → Val → Set where
  --   SSL-Expr′-⇓-eval : (e : SSL-Expr′ Γ E) (e-val : SSL-Expr-Val E) →
  --     (v : Val) →
  --     e-val ≡ E-Store-ap store e →
  --     SSL-Expr-Val-⇓ e-val v →
  --     SSL-Expr′-⇓ s e v


  data SSL-Expr-⇓-Vec (store : Store Γ) : ∀ {C₀ : SSL-Context} {Γ₀ : Type-Context C₀} → Expr-Vec Γ Δ Γ₀ → Val-Vec Γ Δ Γ₀ → Set where
    SSL-Expr-⇓-Vec-Z : SSL-Expr-⇓-Vec store Vec-Z Vec-Z

    SSL-Expr-⇓-Vec-S : ∀ {C₀ Γ₀ α} {x : SSL-Expr Γ Δ α} {x-val} {xs xs-vals} →
      SSL-Expr-Val-⇓ store x x-val →
      SSL-Expr-⇓-Vec store {C₀} {Γ₀} xs xs-vals →
      SSL-Expr-⇓-Vec store {S C₀} {Γ₀ ,, α} (Vec-S x xs) (Vec-S x-val xs-vals)

  -- Vec→Store : ∀ {C₀} {Γ₀ : Type-Context C₀} → Val-Vec Γ Δ Γ₀ → Store
  -- Vec→Store Vec-Z = {!!}
  -- Vec→Store (Vec-S x v) = {!!}
  -- -- Vec→Store {.Z} (Vec-Z x) [ Here :+ ix ] = ix-Val x ix
  -- -- Vec→Store {.(S _)} (Vec-S x vec) [ Here :+ ix ] = ix-Val x ix
  -- -- Vec→Store {.(S _)} (Vec-S x vec) [ There var :+ ix ] =
  -- --   Vec→Store vec [ var :+ ix ]

