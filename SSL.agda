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

-- infix  4 _⊨[_]_
infixl 5  _,,_

Labeled-Pred-Name : Set
Labeled-Pred-Name = Pred-Name × Pred-Label

get-Pred-Name : Labeled-Pred-Name → Pred-Name
get-Pred-Name = proj₁

Pred-Name-label : Labeled-Pred-Name → Pred-Label
Pred-Name-label = proj₂

record Loc : Set where
  field
    name : Loc-Name
    ix : ℕ

ix-Loc : Loc → ℕ → Loc
ix-Loc record { name = name ; ix = ix } ix-incr =
  record { name = name ; ix = ix Data.Nat.+ ix-incr }

-- | Program variable (store) context
data SSL-Context : Set where
  Z : SSL-Context
  S : SSL-Context → SSL-Context

-- data Ixed A : Set where
--   [_:+_] : A → ℕ → Ixed A

data SSL-Type : Set where
  Loc-Type : SSL-Type
  Int-Type : SSL-Type
  Bool-Type : SSL-Type
  -- Exists-Type : SSL-Type → SSL-Type

data Val : SSL-Type → Set where
  Val-Loc : Loc → Val Loc-Type
  Val-Int : ℤ → Val Int-Type
  Val-Bool : Bool → Val Bool-Type

ix-Val : ∀ {α} → Val α → ℕ → Val α
ix-Val (Val-Loc x) ix = Val-Loc (ix-Loc x ix)
ix-Val (Val-Int x) ix = Val-Int x
ix-Val (Val-Bool x) ix = Val-Bool x

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
  Here : ∀ {C Γ α} → SSL-Var {S C} (Γ ,, α) α
  There : ∀ {C Γ α β} → SSL-Var {C} Γ α → SSL-Var {S C} (Γ ,, β) α

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
V-ext ρ Here = Here
V-ext ρ (There ev) = There (ρ ev)

V-rename : ∀ {C C′} {E} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} →
  (∀ {α} → SSL-Var Γ α → SSL-Var Γ′ α) →
  (∀ {α} → SSL-Expr Γ Δ α → SSL-Expr Γ′ Δ α)
V-rename ρ (V x) = V (ρ x)
V-rename ρ (Exists-V x) = Exists-V x
V-rename ρ (Lit x) = Lit x
V-rename ρ (Add e e₁) = Add (V-rename ρ e) (V-rename ρ e₁)
V-rename ρ (Sub e e₁) = Sub (V-rename ρ e) (V-rename ρ e₁)
V-rename ρ (And e e₁) = And (V-rename ρ e) (V-rename ρ e₁)
V-rename ρ (Not e) = Not (V-rename ρ e)
V-rename ρ (Equal e e₁) = Equal (V-rename ρ e) (V-rename ρ e₁)

V-exts : ∀ {C C′} {E} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} →
  (∀ {α} → SSL-Var Γ α → SSL-Expr Γ′ Δ α) →
  (∀ {α β} → SSL-Var (Γ ,, β) α → SSL-Expr (Γ′ ,, β) Δ α)
V-exts ρ Here = V Here
V-exts ρ (There ev) = V-rename There (ρ ev)

V-subst : ∀ {C C′} {E} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} →
  (∀ {α} → SSL-Var Γ α → SSL-Expr Γ′ Δ α) →
  (∀ {α} → SSL-Expr Γ Δ α → SSL-Expr Γ′ Δ α)
V-subst σ (V x) = σ x
V-subst σ (Exists-V x) = Exists-V x
V-subst σ (Lit x) = Lit x
V-subst σ (Add e e₁) = Add (V-subst σ e) (V-subst σ e₁)
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
    σ Here = M
    σ (There v) = V v

data Vec {C₀ : SSL-Context} {E : Exist-Context} (Γ₀ : Type-Context C₀) (Δ : E-Type-Context E) : {C : SSL-Context} → (Γ : Type-Context C) → Set where
  Vec-Z : Vec Γ₀ Δ ε
  Vec-S : ∀ {C Γ α} → SSL-Expr Γ₀ Δ α → Vec Γ₀ Δ {C} Γ → Vec Γ₀ Δ (Γ ,, α)
  -- Vec-Z : A → Vec A Z
  -- Vec-S : ∀ {Γ} → A → Vec A Γ → Vec A (S Γ)

Vec-map : ∀ {C C′} {E} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} → (∀ {α} → SSL-Expr Γ Δ α → SSL-Expr Γ Δ α) → Vec Γ Δ Γ′ → Vec Γ Δ Γ′
Vec-map f Vec-Z = Vec-Z
Vec-map f (Vec-S x v) = Vec-S (f x) (Vec-map f v)

Vec′ : ∀ {C E} (Γ : Type-Context C) (Δ : E-Type-Context E) → Set
Vec′ Γ Δ = Vec Γ Δ Γ

module Ambient-Context
  (C : SSL-Context)
  (E : Exist-Context)
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
    _·_ : (n : Labeled-Pred-Name) → Vec′ Γ Δ → Heaplet

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

  Store : Set
  Store = ∀ {α} → SSL-Var Γ α → Val α

  E-Store-ap : ∀ {α} → Store → SSL-Expr Γ Δ α → SSL-Expr Γ Δ α
  E-Store-ap s e = V-subst (λ x → Lit (s x)) e

  H-Store-ap : Store → Heaplet → Heaplet
  H-Store-ap s (Points-To lhs x) = Points-To (E-Store-ap s lhs) (E-Store-ap s x)
  H-Store-ap s (P · x) = P · Vec-map (E-Store-ap s) x
  -- H-Store-ap s (x ↦ y) = Lit (s _) ↦ V (s _) --E-Store-ap s y
  -- -- H-Store-ap s [ x ,, y ] = [ s x ,, y ]
  -- H-Store-ap s (p · xs) = p · Vec-map (E-Store-ap s) xs

  -- -- -- -- -- A-Store-ap : ∀ {Γ E} → Store Γ → Assertion′ Γ E → Assertion-Val E
  -- -- -- -- -- A-Store-ap s record { pure = pure ; pure-Is-Bool = pure-Is-Bool ; spatial = spatial } =
  -- -- -- -- --   record
  -- -- -- -- --     { pure = E-Store-ap s pure
  -- -- -- -- --     ; pure-Is-Bool = E-Store-ap-preserves-Is-Bool s pure pure-Is-Bool
  -- -- -- -- --     ; spatial = Data.List.map (H-Store-ap s) spatial
  -- -- -- -- --     }

  -- -- -- -- -- data SSL-Expr-Val-⇓ {E} : SSL-Expr-Val E → Val → Set where
  -- -- -- -- --   SSL-Expr-Val-⇓-V : ∀ {x} → SSL-Expr-Val-⇓ (V x) x
  -- -- -- -- --   SSL-Expr-Val-⇓-Lit : ∀ {v} →
  -- -- -- -- --     SSL-Expr-Val-⇓ (Lit v) v

  -- -- -- -- --   SSL-Expr-Val-⇓-Add : ∀ {x y x-val y-val} →
  -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Int x-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Int y-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ (Add x y) (Val-Int (x-val + y-val))

  -- -- -- -- --   SSL-Expr-Val-⇓-Sub : ∀ {x y x-val y-val} →
  -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Int x-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Int y-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ (Sub x y) (Val-Int (x-val - y-val))

  -- -- -- -- --   SSL-Expr-Val-⇓-And : ∀ {x y x-val y-val} →
  -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Bool x-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Bool y-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ (And x y) (Val-Bool (x-val ∧ y-val))

  -- -- -- -- --   SSL-Expr-Val-⇓-Not : ∀ {x x-val} →
  -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Bool x-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ (Not x) (Val-Bool (not x-val))

  -- -- -- -- --   SSL-Expr-Val-⇓-Equal-true : ∀ {x y x-val y-val} →
  -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Int x-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Int y-val) →
  -- -- -- -- --     x-val ≡ y-val →
  -- -- -- -- --     SSL-Expr-Val-⇓ (Equal x y) (Val-Bool true)

  -- -- -- -- --   SSL-Expr-Val-⇓-Equal-false : ∀ {x y x-val y-val} →
  -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Int x-val) →
  -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Int y-val) →
  -- -- -- -- --     x-val ≢ y-val →
  -- -- -- -- --     SSL-Expr-Val-⇓ (Equal x y) (Val-Bool false)

  -- -- -- -- -- data SSL-Expr′-⇓ {E Γ} (s : Store Γ) : SSL-Expr′ Γ E → Val → Set where
  -- -- -- -- --   SSL-Expr′-⇓-eval : (e : SSL-Expr′ Γ E) (e-val : SSL-Expr-Val E) →
  -- -- -- -- --     (v : Val) →
  -- -- -- -- --     e-val ≡ E-Store-ap s e →
  -- -- -- -- --     SSL-Expr-Val-⇓ e-val v →
  -- -- -- -- --     SSL-Expr′-⇓ s e v


  -- -- -- -- -- data SSL-Expr′-⇓-Vec {E} : ∀ {Γ Γ′} (s : Store Γ) → Vec (SSL-Expr′ Γ E) Γ′ → Vec Val Γ′ → Set where
  -- -- -- -- --   SSL-Expr′-⇓-Vec-Z : ∀ {Γ} {s} {x x-val} →
  -- -- -- -- --     SSL-Expr′-⇓ s x x-val →
  -- -- -- -- --     SSL-Expr′-⇓-Vec {_} {Γ} s (Vec-Z x) (Vec-Z x-val)
  -- -- -- -- --   SSL-Expr′-⇓-Vec-S : ∀ {Γ} {Γ′} {s} {x x-val} {xs xs-vals} →
  -- -- -- -- --     SSL-Expr′-⇓ s x x-val →
  -- -- -- -- --     SSL-Expr′-⇓-Vec {_} {Γ} {Γ′} s xs xs-vals →
  -- -- -- -- --     SSL-Expr′-⇓-Vec s (Vec-S x xs) (Vec-S x-val xs-vals)

  -- -- -- -- -- Vec→Store : ∀ {Γ} → Vec Val Γ → Store Γ
  -- -- -- -- -- Vec→Store {.Z} (Vec-Z x) [ Here :+ ix ] = ix-Val x ix
  -- -- -- -- -- Vec→Store {.(S _)} (Vec-S x vec) [ Here :+ ix ] = ix-Val x ix
  -- -- -- -- -- Vec→Store {.(S _)} (Vec-S x vec) [ There var :+ ix ] =
  -- -- -- -- --   Vec→Store vec [ var :+ ix ]

  -- -- -- -- -- Satisfies-Expr : ∀ {Γ E} (s : Store Γ) → (e : SSL-Expr′ Γ E) → Is-Bool e → Set
  -- -- -- -- -- Satisfies-Expr {Γ} s (Lit (Val-Bool x)) Is-Bool-Lit = ⊤
  -- -- -- -- -- Satisfies-Expr {Γ} s (And x y) (Is-Bool-And prf-x prf-y) = (Satisfies-Expr s x prf-x) × (Satisfies-Expr s y prf-y)
  -- -- -- -- -- Satisfies-Expr {Γ} s (Not x) (Is-Bool-Not prf) = ¬ (Satisfies-Expr s x prf)
  -- -- -- -- -- Satisfies-Expr {Γ} s (Equal x y) Is-Bool-Equal = x ≡ y

  -- -- -- -- -- Heap : Set
  -- -- -- -- -- -- Heap = Loc → Maybe ℤ
  -- -- -- -- -- Heap = List (Loc × Val)

  -- -- -- -- -- data Dom : Heap → List Loc → Set where
  -- -- -- -- --   Dom-[] : Dom [] []
  -- -- -- -- --   Dom-∷ : ∀ {loc i rest locs} →
  -- -- -- -- --     Dom rest locs →
  -- -- -- -- --     Dom ((loc , i) ∷ rest) (loc ∷ locs)

  -- -- -- -- -- _∈_ : ∀ {A} → A → List A → Set
  -- -- -- -- -- x ∈ xs = Any (_≡ x) xs

  -- -- -- -- -- data Disjoint : Heap → Heap → Set where
  -- -- -- -- --   Disjoint-[] : ∀ {h} → Disjoint [] h
  -- -- -- -- --   Disjoint-∷ : ∀ {loc i rest h dom-h} →
  -- -- -- -- --     Disjoint rest h →
  -- -- -- -- --     Dom h dom-h →
  -- -- -- -- --     ¬ (loc ∈ dom-h) →
  -- -- -- -- --     Disjoint ((loc , i) ∷ rest) h

  -- -- -- -- -- _≡S_ : ∀ {A} → List A → List A → Set
  -- -- -- -- -- _≡S_ xs ys = (∀ x → x ∈ xs → x ∈ ys) × (∀ y → y ∈ ys → y ∈ xs)

  -- -- -- -- -- data _∘_==_ : Heap → Heap → Heap → Set where
  -- -- -- -- --   mk-∘ : ∀ h h′ h′′ →
  -- -- -- -- --     Disjoint h h′ →
  -- -- -- -- --     h′′ ≡S (h ++ h′) →
  -- -- -- -- --     h ∘ h′ == h′′

  -- -- -- -- -- -- Ind-Pred-Env : SSL-Context → Set
  -- -- -- -- -- -- Ind-Pred-Env Γ = (n : Pred-Name) → Ind-Pred n Γ

  -- -- -- -- -- Ind-Pred-Denotation : SSL-Context → Set₁
  -- -- -- -- -- Ind-Pred-Denotation Γ = Heap → Store Γ → Set

  -- -- -- -- -- Ind-Pred-Interpret : SSL-Context → Set₁
  -- -- -- -- -- Ind-Pred-Interpret Γ =
  -- -- -- -- --   (n : Pred-Name) →
  -- -- -- -- --   Ind-Pred-Denotation Γ

  -- -- -- -- -- data Satisfies-Heaplet₀ : ∀ {Γ} (s : Store Γ) → (h : Heap) → Ind-Pred-Interpret Γ → Heaplet′ Γ Exist-Z → Set where
  -- -- -- -- --   Satisfies-Heaplet₀-↦ : ∀ {Γ} {s : Store Γ} {h} {env} {loc-v rhs-e} {loc rhs} →
  -- -- -- -- --     SSL-Expr′-⇓ {Exist-Z} s (V loc-v) (Val-Loc loc) →
  -- -- -- -- --     SSL-Expr′-⇓ s rhs-e rhs →
  -- -- -- -- --     h ≡ ((loc , rhs) ∷ []) →
  -- -- -- -- --     Satisfies-Heaplet₀ s h env (loc-v ↦ rhs-e)

  -- -- -- -- --   Satisfies-Heaplet₀-· : ∀ {Γ} {s : Store Γ} {h} {env} {labeled-p-name p-name args} {args-vals} →
  -- -- -- -- --     p-name ≡ get-Pred-Name labeled-p-name →
  -- -- -- -- --     env p-name h (Vec→Store args-vals) →
  -- -- -- -- --     SSL-Expr′-⇓-Vec s args args-vals →
  -- -- -- -- --     Satisfies-Heaplet₀ s h env (labeled-p-name · args)

  -- -- -- -- -- data Satisfies-Heaplet₀-E {Γ} (s : Store Γ) (h : Heap) (env : Ind-Pred-Interpret Γ) : ∀ {E} → Heaplet′ Γ E → Set where
  -- -- -- -- --   Satisfies-Heaplet₀-E-Z : ∀ {heaplet} →
  -- -- -- -- --     Satisfies-Heaplet₀ s h env heaplet →
  -- -- -- -- --     Satisfies-Heaplet₀-E s h env {Exist-Z} heaplet

  -- -- -- -- --   Satisfies-Heaplet₀-E-S : ∀ {E heaplet} →
  -- -- -- -- --     (Σ Val λ v →
  -- -- -- -- --       Satisfies-Heaplet₀-E s h env {E} (Heaplet-E-subst-1 heaplet {!!})
  -- -- -- -- --     ) →
  -- -- -- -- --     Satisfies-Heaplet₀-E s h env {Exist-S E} heaplet

  -- -- -- -- -- -- data Satisfies-spatial₀ {E} : ∀ {Γ} (s : Store Γ) → (h : Heap) → Ind-Pred-Interpret Γ → List (Heaplet′ Γ E) → Set where
  -- -- -- -- -- --   Satisfies-spatial₀-[] : ∀ {Γ} {s : Store Γ} {env} →
  -- -- -- -- -- --     Satisfies-spatial₀ s [] env []

  -- -- -- -- -- --   Satisfies-spatial₀-∷ : ∀ {Γ} {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} {env} →
  -- -- -- -- -- --     h₁ ∘ h₂ == h →
  -- -- -- -- -- --     Satisfies-Heaplet₀ s h₁ env Σ₁ →
  -- -- -- -- -- --     Satisfies-spatial₀ s h₂ env Σ₂ →
  -- -- -- -- -- --     Satisfies-spatial₀ s h env (Σ₁ ∷ Σ₂)

  -- -- -- -- -- -- record Satisfies-Assertion₀ {E Γ} (s : Store Γ) (h : Heap) (env : Ind-Pred-Interpret Γ) (a : Assertion′ Γ E) : Set where
  -- -- -- -- -- --   field
  -- -- -- -- -- --     pure-prf : Satisfies-Expr s (Assertion.pure a) (Assertion.pure-Is-Bool a)
  -- -- -- -- -- --     spatial-prf : Satisfies-spatial₀ s h env (Assertion.spatial a)

  -- -- -- -- -- -- φ : ∀ {E} {Γ} → List (Ind-Rule Γ) → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
  -- -- -- -- -- -- φ {E} {Γ} rules env P h s =
  -- -- -- -- -- --   ∃[ F ] (Satisfies-Assertion₀ {E} s h env F × (record { name = P ; assertion = F } ∈ rules))

  -- -- -- -- -- -- _⊆_ : ∀ {ℓ m} {A : Set ℓ} (P Q : A → Set m) → Set (ℓ Agda.Primitive.⊔ m)
  -- -- -- -- -- -- _⊆_ P Q = ∀ a → P a → Q a

  -- -- -- -- -- -- _⊆₂_ : ∀ {ℓ m} {A B : Set ℓ} (P Q : A → B → Set m) → Set (ℓ Agda.Primitive.⊔ m)
  -- -- -- -- -- -- _⊆₂_ P Q = ∀ a b → P a b → Q a b

  -- -- -- -- -- -- _≤′_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Set
  -- -- -- -- -- -- _≤′_ X X′ = ∀ P → X P ⊆₂ X′ P

  -- -- -- -- -- -- _⊔_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
  -- -- -- -- -- -- _⊔_ {Γ} env-1 env-2 = λ n x y → env-1 n x y ⊎ env-2 n x y

  -- -- -- -- -- -- _⊓_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
  -- -- -- -- -- -- _⊓_ {Γ} env-1 env-2 = λ n x y → env-1 n x y × env-2 n x y

  -- -- -- -- -- -- ∅-interpret : ∀ {Γ} → Ind-Pred-Interpret Γ
  -- -- -- -- -- -- ∅-interpret = λ n h args → ⊥

  -- -- -- -- -- -- ∅-interpret-least : ∀ {Γ} → (X : Ind-Pred-Interpret Γ) → ∅-interpret ≤′ X
  -- -- -- -- -- -- ∅-interpret-least X P a b ()

  -- -- -- -- -- -- Satisfies-Heaplet₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-Heaplet₀ {E} s h X A → Satisfies-Heaplet₀ s h X′ A
  -- -- -- -- -- -- Satisfies-Heaplet₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ ↦ _)} prf-1 (Satisfies-Heaplet₀-↦ x x₁ x₂) = Satisfies-Heaplet₀-↦ x x₁ x₂
  -- -- -- -- -- -- Satisfies-Heaplet₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ · _)} prf-1 (Satisfies-Heaplet₀-· {_} {_} {_} {_} {_} {p-name} {args} {args-vals} refl x x₁) =
  -- -- -- -- -- --   let
  -- -- -- -- -- --     z = prf-1 p-name h (Vec→Store args-vals) x
  -- -- -- -- -- --   in
  -- -- -- -- -- --   Satisfies-Heaplet₀-· refl z x₁

  -- -- -- -- -- -- Satisfies-spatial₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-spatial₀ s h X A → Satisfies-spatial₀ s h X′ A
  -- -- -- -- -- -- Satisfies-spatial₀-monotone {E} {Γ} {s} {.[]} {X} {X′} {.[]} prf-1 Satisfies-spatial₀-[] = Satisfies-spatial₀-[]
  -- -- -- -- -- -- Satisfies-spatial₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ ∷ _)} prf-1 (Satisfies-spatial₀-∷ x x₁ prf-2) =
  -- -- -- -- -- --   Satisfies-spatial₀-∷ x (Satisfies-Heaplet₀-monotone {E} prf-1 x₁) (Satisfies-spatial₀-monotone prf-1 prf-2)

  -- -- -- -- -- -- Satisfies-Assertion₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-Assertion₀ {E} s h X A → Satisfies-Assertion₀ {E} s h X′ A
  -- -- -- -- -- -- Satisfies-Assertion₀-monotone {E} {Γ} {s} {h} {X} {X′} {A} prf-1 record { pure-prf = pure-prf ; spatial-prf = spatial-prf } =
  -- -- -- -- -- --   record { pure-prf = pure-prf ; spatial-prf = Satisfies-spatial₀-monotone prf-1 spatial-prf }

  -- -- -- -- -- -- φ-monotone : ∀ {E Γ} {rules} {X X′ : Ind-Pred-Interpret Γ} → X ≤′ X′ → φ {E} rules X ≤′ φ rules X′
  -- -- -- -- -- -- φ-monotone {E} {Γ} {rules} {X} {X′} prf-1 P a b (fst , prf-2 , prf-3) =
  -- -- -- -- -- --   fst , Satisfies-Assertion₀-monotone prf-1 prf-2 , prf-3

  -- -- -- -- -- -- Ordinal : Set
  -- -- -- -- -- -- Ordinal = ℕ

  -- -- -- -- -- -- iterate-φ : ∀ {E Γ} (rules : List (Ind-Rule Γ)) → Ordinal → Ind-Pred-Interpret Γ
  -- -- -- -- -- -- iterate-φ {E} {Γ} rules zero = ∅-interpret
  -- -- -- -- -- -- iterate-φ {E} {Γ} rules (ℕ.suc α) = φ {E} rules (iterate-φ {E} rules α)

  -- -- -- -- -- -- ⟦_⟧_ : ∀ {E Γ} → List (Ind-Rule Γ) → Ordinal → Ind-Pred-Interpret Γ
  -- -- -- -- -- -- ⟦_⟧_ {E} rules α = iterate-φ {E} rules α

  -- -- -- -- -- -- Label-Valuation : Set
  -- -- -- -- -- -- Label-Valuation = Pred-Label → Ordinal

  -- -- -- -- -- -- data Satisfies-Heaplet {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) : ∀ (s : Store Γ) → (h : Heap) → Heaplet′ Γ E → Set where
  -- -- -- -- -- --   Satisfies-Heaplet-↦ : ∀ {s : Store Γ} {h} {loc-v rhs-e} {loc rhs} →
  -- -- -- -- -- --     SSL-Expr′-⇓ {E} s (V loc-v) (Val-Loc loc) →
  -- -- -- -- -- --     SSL-Expr′-⇓ s rhs-e rhs →
  -- -- -- -- -- --     h ≡ ((loc , rhs) ∷ []) →
  -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h (loc-v ↦ rhs-e)

  -- -- -- -- -- --   Satisfies-Heaplet-· : ∀ {s : Store Γ} {h} {labeled-p-name p-name args} {args-vals} →
  -- -- -- -- -- --     let α = Pred-Name-label labeled-p-name
  -- -- -- -- -- --     in
  -- -- -- -- -- --     p-name ≡ get-Pred-Name labeled-p-name →
  -- -- -- -- -- --     (⟦_⟧_ {E} rules (ρ α)) p-name h (Vec→Store args-vals) →
  -- -- -- -- -- --     SSL-Expr′-⇓-Vec s args args-vals →
  -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h (labeled-p-name · args)

  -- -- -- -- -- -- data Satisfies-spatial {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) : ∀ (s : Store Γ) → (h : Heap) → List (Heaplet′ Γ E) → Set where
  -- -- -- -- -- --   Satisfies-spatial-[] : ∀ {s : Store Γ} →
  -- -- -- -- -- --     Satisfies-spatial rules ρ s [] []

  -- -- -- -- -- --   Satisfies-spatial-∷ : ∀ {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} →
  -- -- -- -- -- --     h₁ ∘ h₂ == h →
  -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h₁ Σ₁ →
  -- -- -- -- -- --     Satisfies-spatial rules ρ s h₂ Σ₂ →
  -- -- -- -- -- --     Satisfies-spatial rules ρ s h (Σ₁ ∷ Σ₂)

  -- -- -- -- -- -- record Satisfies-Assertion {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) (s : Store Γ) (h : Heap) (a : Assertion′ Γ E) : Set where
  -- -- -- -- -- --   field
  -- -- -- -- -- --     pure-prf : Satisfies-Expr s (Assertion.pure a) (Assertion.pure-Is-Bool a)
  -- -- -- -- -- --     spatial-prf : Satisfies-spatial rules ρ s h (Assertion.spatial a)

  -- -- -- -- -- -- data Label-Constraint : Set where
  -- -- -- -- -- --   Ord-≤ : Pred-Label → Pred-Label → Label-Constraint
  -- -- -- -- -- --   Ord-< : Pred-Label → Pred-Label → Label-Constraint

  -- -- -- -- -- -- data Constraints-hold (ρ : Label-Valuation) : List Label-Constraint → Set where
  -- -- -- -- -- --   Constraints-hold-[] : Constraints-hold ρ []
  -- -- -- -- -- --   Constraints-hold-∷-≤ : ∀ {α β rest} →
  -- -- -- -- -- --     ρ α ≤ ρ β →
  -- -- -- -- -- --     Constraints-hold ρ rest →
  -- -- -- -- -- --     Constraints-hold ρ (Ord-≤ α β ∷ rest)
  -- -- -- -- -- --   Constraints-hold-∷-< : ∀ {α β rest} →
  -- -- -- -- -- --     ρ α < ρ β →
  -- -- -- -- -- --     Constraints-hold ρ rest →
  -- -- -- -- -- --     Constraints-hold ρ (Ord-< α β ∷ rest)

  -- -- -- -- -- -- Constrained-Formula : Exist-Context → SSL-Context → Set
  -- -- -- -- -- -- Constrained-Formula E Γ =
  -- -- -- -- -- --   List Pred-Label × List Label-Constraint × Assertion′ Γ E

  -- -- -- -- -- -- _==/[_]_ : Label-Valuation → List Pred-Label → Label-Valuation → Set
  -- -- -- -- -- -- _==/[_]_ ρ αs ρ′ = ∀ α → α ∈ αs → ρ α ≡ ρ′ α

  -- -- -- -- -- -- data Satisfies-Constrained-Formula {E Γ} (rules : List (Ind-Rule Γ)) : Label-Valuation → Store Γ → Heap → Constrained-Formula E Γ → Set where
  -- -- -- -- -- --   mk-Satisfies-Constrained-Formula : ∀ {ρ s h αs constraints asn} →
  -- -- -- -- -- --     Σ Label-Valuation (λ ρ′ →
  -- -- -- -- -- --       ρ′ ==/[ αs ] ρ →
  -- -- -- -- -- --       Constraints-hold ρ′ constraints →
  -- -- -- -- -- --       Satisfies-Assertion rules ρ′ s h asn) →
  -- -- -- -- -- --     Satisfies-Constrained-Formula rules ρ s h (αs , constraints , asn)

  -- -- -- -- -- -- _,_,_⊨[_]_ : ∀ {E Γ} → Label-Valuation → Store Γ → Heap → List (Ind-Rule Γ) → Constrained-Formula E Γ → Set
  -- -- -- -- -- -- _,_,_⊨[_]_ ρ s h rules asn = Satisfies-Constrained-Formula rules ρ s h asn
