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

-- -- data Type-Of : ∀ {C E} (Γ : Type-Context C) (Δ : E-Type-Context E) → SSL-Expr C E → SSL-Type → Set where
-- --   Type-Of-V-Here : ∀ {C E Γ Δ τ} → Type-Of {S C} {E} (Γ ,, τ) Δ (V Here) τ
-- --   Type-Of-V-There : ∀ {C E Γ Δ τ x} →
-- --     Type-Of {C} {E} Γ Δ (V x) τ →
-- --     Type-Of {S C} {E} (Γ ,, τ) Δ (V (There x)) τ

-- --   Type-Of-Exists-V-Here : ∀ {C E Γ Δ τ} → Type-Of {C} {Exist-S E} Γ (Δ ,, τ) (Exists-V EV-Here) τ
-- --   Type-Of-Exists-V-There : ∀ {C E Γ Δ τ x} →
-- --     Type-Of {C} {E} Γ Δ (Exists-V x) τ →
-- --     Type-Of {C} {Exist-S E} Γ (Δ ,, τ) (Exists-V (EV-There x)) τ

-- --   Type-Of-Lit : ∀ {C E Γ Δ x α} →
-- --     Type-Of-Val x α →
-- --     Type-Of {C} {E} Γ Δ (Lit x) α

-- --   Type-Of-Add : ∀ {C E Γ Δ x y} →
-- --     Type-Of Γ Δ x Int-Type →
-- --     Type-Of Γ Δ y Int-Type →
-- --     Type-Of {C} {E} Γ Δ (Add x y) Int-Type

-- --   Type-Of-Sub : ∀ {C E Δ Γ x y} →
-- --     Type-Of Γ Δ x Int-Type →
-- --     Type-Of Γ Δ y Int-Type →
-- --     Type-Of {C} {E} Γ Δ (Sub x y) Int-Type

-- --   Type-Of-And : ∀ {C E Δ Γ x y} →
-- --     Type-Of Γ Δ x Bool-Type →
-- --     Type-Of Γ Δ y Bool-Type →
-- --     Type-Of {C} {E} Γ Δ (And x y) Bool-Type

-- --   Type-Of-Not : ∀ {C E Δ Γ x} →
-- --     Type-Of Γ Δ x Bool-Type →
-- --     Type-Of {C} {E} Γ Δ (Not x) Bool-Type

-- --   Type-Of-Equal : ∀ {C E Δ Γ x y} →
-- --     Type-Of Γ Δ x Int-Type →
-- --     Type-Of Γ Δ y Int-Type →
-- --     Type-Of {C} {E} Γ Δ (Equal x y) Bool-Type

-- -- [_∣_]⊢_∶_ : ∀ {C} {E} → (Γ : Type-Context C) (Δ : E-Type-Context E) → SSL-Expr C E → SSL-Type → Set
-- -- [ Γ ∣ Δ ]⊢ e ∶ α = Type-Of Γ Δ e α

-- -- Typed-Expr : ∀ {C} {E} → (Γ : Type-Context C) (Δ : E-Type-Context E) → SSL-Type → Set
-- -- Typed-Expr {C} {E} Γ Δ α = Σ (SSL-Expr C E) λ e → [ Γ ∣ Δ ]⊢ e ∶ α

-- -- ----

-- -- E-ext : {E E′ : Exist-Context} → (Exist-Var E → Exist-Var E′) → (Exist-Var (Exist-S E) → Exist-Var (Exist-S E′))
-- -- E-ext ρ EV-Here = EV-Here
-- -- E-ext ρ (EV-There ev) = EV-There (ρ ev)

-- -- E-rename : ∀ {C} {E E′ : Exist-Context} → (Exist-Var E → Exist-Var E′) → (SSL-Expr C E → SSL-Expr C E′)
-- -- E-rename ρ (V x) = V x
-- -- E-rename ρ (Exists-V x) = Exists-V (ρ x)
-- -- -- E-rename ρ (Exists-Intro e) = E-rename (λ _ → EV-Here) e
-- -- E-rename ρ (Lit x) = Lit x
-- -- E-rename ρ (Add e e₁) = Add (E-rename ρ e) (E-rename ρ e₁)
-- -- E-rename ρ (Sub e e₁) = Sub (E-rename ρ e) (E-rename ρ e₁)
-- -- E-rename ρ (And e e₁) = And (E-rename ρ e) (E-rename ρ e₁)
-- -- E-rename ρ (Not e) = Not (E-rename ρ e)
-- -- E-rename ρ (Equal e e₁) = Equal (E-rename ρ e) (E-rename ρ e₁)

-- -- E-exts : ∀ {C} {E E′ : Exist-Context} → (Exist-Var E → SSL-Expr C E′) → (Exist-Var (Exist-S E) → SSL-Expr C (Exist-S E′))
-- -- E-exts ρ EV-Here = Exists-V EV-Here
-- -- E-exts ρ (EV-There ev) = E-rename EV-There (ρ ev)

-- -- E-subst : ∀ {C} {E E′ : Exist-Context} → (Exist-Var E → SSL-Expr C E′) → (SSL-Expr C E → SSL-Expr C E′)
-- -- E-subst σ (V x) = V x
-- -- E-subst σ (Exists-V x) = σ x
-- -- -- E-subst σ (Exists-Intro e) = Exists-Intro (E-subst (E-exts σ) e)
-- -- E-subst σ (Lit x) = Lit x
-- -- E-subst σ (Add e e₁) = Add (E-subst σ e) (E-subst σ e₁)
-- -- E-subst σ (Sub e e₁) = Sub (E-subst σ e) (E-subst σ e₁)
-- -- E-subst σ (And e e₁) = And (E-subst σ e) (E-subst σ e₁)
-- -- E-subst σ (Not e) = Not (E-subst σ e)
-- -- E-subst σ (Equal e e₁) = Equal (E-subst σ e) (E-subst σ e₁)

-- -- E-subst-1 : ∀ {C} {E : Exist-Context} → SSL-Expr C (Exist-S E) → SSL-Expr C E → SSL-Expr C E
-- -- E-subst-1 {A} {E} N M = E-subst σ N
-- --   where
-- --     σ : Exist-Var (Exist-S E) → SSL-Expr A E
-- --     σ EV-Here = M
-- --     σ (EV-There ev) = Exists-V ev

-- -- E-subst-1-V : ∀ {C} {E : Exist-Context} {x} → {M : SSL-Expr C E} →
-- --   E-subst-1 (V x) M ≡ V x
-- -- E-subst-1-V {C} {E} {x} {M} = refl

-- -- ----

-- -- V-ext : {C C′ : SSL-Context} → (SSL-Var C → SSL-Var C′) → (SSL-Var (S C) → SSL-Var (S C′))
-- -- V-ext ρ Here = Here
-- -- V-ext ρ (There ev) = There (ρ ev)

-- -- V-rename : ∀ {C C′} {E : Exist-Context} → (SSL-Var C → SSL-Var C′) → (SSL-Expr C E → SSL-Expr C′ E)
-- -- V-rename ρ (V x) = V (ρ x)
-- -- V-rename ρ (Exists-V x) = Exists-V x
-- -- V-rename ρ (Lit x) = Lit x
-- -- V-rename ρ (Add e e₁) = Add (V-rename ρ e) (V-rename ρ e₁)
-- -- V-rename ρ (Sub e e₁) = Sub (V-rename ρ e) (V-rename ρ e₁)
-- -- V-rename ρ (And e e₁) = And (V-rename ρ e) (V-rename ρ e₁)
-- -- V-rename ρ (Not e) = Not (V-rename ρ e)
-- -- V-rename ρ (Equal e e₁) = Equal (V-rename ρ e) (V-rename ρ e₁)

-- -- V-exts : ∀ {C C′} {E : Exist-Context} → (SSL-Var C → SSL-Expr C′ E) → (SSL-Var (S C) → SSL-Expr (S C′) E)
-- -- V-exts ρ Here = V Here
-- -- V-exts ρ (There ev) = V-rename There (ρ ev)

-- -- V-subst : ∀ {C C′} {E : Exist-Context} → (SSL-Var C → SSL-Expr C′ E) → (SSL-Expr C E → SSL-Expr C′ E)
-- -- V-subst σ (V x) = σ x
-- -- V-subst σ (Exists-V x) = Exists-V x
-- -- V-subst σ (Lit x) = Lit x
-- -- V-subst σ (Add e e₁) = Add (V-subst σ e) (V-subst σ e₁)
-- -- V-subst σ (Sub e e₁) = Sub (V-subst σ e) (V-subst σ e₁)
-- -- V-subst σ (And e e₁) = And (V-subst σ e) (V-subst σ e₁)
-- -- V-subst σ (Not e) = Not (V-subst σ e)
-- -- V-subst σ (Equal e e₁) = Equal (V-subst σ e) (V-subst σ e₁)

-- -- V-subst-Exists-V : ∀ {C C′} {E : Exist-Context} {x} →
-- --   (σ : SSL-Var C → SSL-Expr C′ E) →
-- --   V-subst σ (Exists-V x) ≡ Exists-V x
-- -- V-subst-Exists-V σ = refl

-- -- -- V-subst-1 : ∀ {C} {E : Exist-Context} → SSL-Expr (S C) E → SSL-Expr C E → SSL-Expr C E
-- -- -- V-subst-1 {C} {E} N M = V-subst σ N
-- -- --   where
-- -- --     σ : SSL-Var (S C) → SSL-Expr C E
-- -- --     σ Here = M
-- -- --     σ (There v) = V v

-- -- -- V-subst-1-Exists-V : ∀ {C} {E : Exist-Context} {x} → {M : SSL-Expr C E} →
-- -- --   V-subst-1 (Exists-V x) M ≡ Exists-V x
-- -- -- V-subst-1-Exists-V {C} {E} {x} {M} = refl

-- -- change-V-ctx : ∀ {C} {E E′} {Γ : Type-Context C} {Δ : E-Type-Context E} {Δ′ : E-Type-Context E′} {α x} →
-- --   [ Γ ∣ Δ ]⊢ V x ∶ α →
-- --   [ Γ ∣ Δ′ ]⊢ V x ∶ α
-- -- change-V-ctx Type-Of-V-Here = Type-Of-V-Here
-- -- change-V-ctx (Type-Of-V-There prf) = Type-Of-V-There (change-V-ctx prf)

-- -- change-Exists-V-ctx : ∀ {C C′} {E} {Γ : Type-Context C} {Γ′ : Type-Context C′} {Δ : E-Type-Context E} {α x} →
-- --   [ Γ ∣ Δ ]⊢ Exists-V x ∶ α →
-- --   [ Γ′ ∣ Δ ]⊢ Exists-V x ∶ α
-- -- change-Exists-V-ctx Type-Of-Exists-V-Here = Type-Of-Exists-V-Here
-- -- change-Exists-V-ctx (Type-Of-Exists-V-There prf) = Type-Of-Exists-V-There (change-Exists-V-ctx prf)

-- -- Type-unique : ∀ {C} {E} {Γ Δ} {α β} (e : SSL-Expr C E) →
-- --   [ Γ ∣ Δ ]⊢ e ∶ α →
-- --   [ Γ ∣ Δ ]⊢ e ∶ β →
-- --   β ≡ α
-- -- Type-unique {.(S _)} {E} {.(_ ,, α)} {Δ} {α} {.α} .(V Here) Type-Of-V-Here Type-Of-V-Here = refl
-- -- Type-unique {.(S _)} {E} {.(_ ,, α)} {Δ} {α} {.α} .(V (There _)) (Type-Of-V-There prf-α) (Type-Of-V-There prf-β) = refl
-- -- Type-unique {C} {.(Exist-S _)} {Γ} {.(_ ,, α)} {α} {.α} .(Exists-V EV-Here) Type-Of-Exists-V-Here Type-Of-Exists-V-Here = refl
-- -- Type-unique {C} {.(Exist-S _)} {Γ} {.(_ ,, α)} {α} {.α} .(Exists-V (EV-There _)) (Type-Of-Exists-V-There prf-α) (Type-Of-Exists-V-There prf-β) = refl
-- -- Type-unique {C} {E} {Γ} {Δ} {.Loc-Type} {.Loc-Type} .(Lit (Val-Loc _)) (Type-Of-Lit Type-Of-Val-Loc) (Type-Of-Lit Type-Of-Val-Loc) = refl
-- -- Type-unique {C} {E} {Γ} {Δ} {.Int-Type} {.Int-Type} .(Lit (Val-Int _)) (Type-Of-Lit Type-Of-Val-Int) (Type-Of-Lit Type-Of-Val-Int) = refl
-- -- Type-unique {C} {E} {Γ} {Δ} {.Bool-Type} {.Bool-Type} .(Lit (Val-Bool _)) (Type-Of-Lit Type-Of-Val-Bool) (Type-Of-Lit Type-Of-Val-Bool) = refl
-- -- Type-unique {C} {E} {Γ} {Δ} {.Int-Type} {.Int-Type} .(Add _ _) (Type-Of-Add prf-α prf-α₁) (Type-Of-Add prf-β prf-β₁) = refl
-- -- Type-unique {C} {E} {Γ} {Δ} {.Int-Type} {.Int-Type} .(Sub _ _) (Type-Of-Sub prf-α prf-α₁) (Type-Of-Sub prf-β prf-β₁) = refl
-- -- Type-unique {C} {E} {Γ} {Δ} {.Bool-Type} {.Bool-Type} .(And _ _) (Type-Of-And prf-α prf-α₁) (Type-Of-And prf-β prf-β₁) = refl
-- -- Type-unique {C} {E} {Γ} {Δ} {.Bool-Type} {.Bool-Type} .(Not _) (Type-Of-Not prf-α) (Type-Of-Not prf-β) = refl
-- -- Type-unique {C} {E} {Γ} {Δ} {.Bool-Type} {.Bool-Type} .(Equal _ _) (Type-Of-Equal prf-α prf-α₁) (Type-Of-Equal prf-β prf-β₁) = refl

-- -- V-subst-V : ∀ {C C′} {E : Exist-Context} {Γ Δ} {α β} (x : SSL-Var C) →
-- --   (σ : SSL-Var C → SSL-Expr C′ E) →
-- --   [ Γ ∣ Δ ]⊢ σ x ∶ α →
-- --   [ Γ ∣ Δ ]⊢ V-subst σ (V x) ∶ β →
-- --   β ≡ α
-- -- V-subst-V {C} {C′} {E} {Γ} {Δ} {α} {β} Here σ prf-1 prf-2 = Type-unique (σ Here) prf-1 prf-2
-- -- V-subst-V {.(S _)} {C′} {E} {Γ} {Δ} {α} {β} (There x) σ prf-1 prf-2 = V-subst-V x (λ _ → σ (There x)) prf-1 prf-2

-- -- V-subst-lemma : ∀ {C C′} {E : Exist-Context} {Γ Γ′ Δ} {α β} →
-- --   (σ : SSL-Var C → SSL-Expr C′ E) →
-- --   (∀ v → [ Γ′ ∣ Δ ]⊢ σ v ∶ α) →
-- --   (e : SSL-Expr C E) →
-- --   [ Γ ∣ Δ ]⊢ e ∶ β →
-- --   [ Γ′ ∣ Δ ]⊢ V-subst σ e ∶ β
-- -- V-subst-lemma {C} {C′} {E} {Γ} {Γ′} {Δ} {α} {β} σ σ-prf (V Here) e-prf =
-- --   let
-- --     z = V-subst-V Here σ (σ-prf Here) {!!}
-- --   in
-- --   {!!}
-- -- V-subst-lemma {.(S _)} {C′} {E} {Γ} {Γ′} {Δ} {α} {β} σ σ-prf (V (There x)) e-prf = {!!}
-- -- V-subst-lemma {C} {C′} {E} {Γ} {Γ′} {Δ} {α} {β} σ σ-prf (Exists-V x) e-prf =
-- --   subst (λ z → [ Γ′ ∣ Δ ]⊢ z ∶ β) (sym (V-subst-Exists-V σ)) (change-Exists-V-ctx e-prf)
-- -- V-subst-lemma {C} {C′} {E} {Γ} {Γ′} {Δ} {α} {β} σ σ-prf (Lit x) (Type-Of-Lit x₁) = Type-Of-Lit x₁
-- -- V-subst-lemma {C} {C′} {E} {Γ} {Γ′} {Δ} {α} {.Int-Type} σ σ-prf (Add e e₁) (Type-Of-Add e-prf e-prf₁) = Type-Of-Add (V-subst-lemma σ σ-prf e e-prf) (V-subst-lemma σ σ-prf e₁ e-prf₁)
-- -- V-subst-lemma {C} {C′} {E} {Γ} {Γ′} {Δ} {α} {.Int-Type} σ σ-prf (Sub e e₁) (Type-Of-Sub e-prf e-prf₁) = Type-Of-Sub (V-subst-lemma σ σ-prf e e-prf) (V-subst-lemma σ σ-prf e₁ e-prf₁)
-- -- V-subst-lemma {C} {C′} {E} {Γ} {Γ′} {Δ} {α} {.Bool-Type} σ σ-prf (And e e₁) (Type-Of-And e-prf e-prf₁) = Type-Of-And (V-subst-lemma σ σ-prf e e-prf)
-- --                                                                                                            (V-subst-lemma σ σ-prf e₁ e-prf₁)
-- -- V-subst-lemma {C} {C′} {E} {Γ} {Γ′} {Δ} {α} {.Bool-Type} σ σ-prf (Not e) (Type-Of-Not e-prf) = Type-Of-Not (V-subst-lemma σ σ-prf e e-prf)
-- -- V-subst-lemma {C} {C′} {E} {Γ} {Γ′} {Δ} {α} {.Bool-Type} σ σ-prf (Equal e e₁) (Type-Of-Equal e-prf e-prf₁) = Type-Of-Equal (V-subst-lemma σ σ-prf e e-prf)
-- --                                                                                                                (V-subst-lemma σ σ-prf e₁ e-prf₁)

-- -- -- ----


-- -- -- E-subst-1-lemma : ∀ {C} {E : Exist-Context} → {N : SSL-Expr C (Exist-S E)} → {M : SSL-Expr C E} →
-- -- --   ∀ {Γ Δ α β} →
-- -- --   [ Γ ∣ Δ ,, β ]⊢ N ∶ α →
-- -- --   [ Γ ∣ Δ ]⊢ M ∶ β →
-- -- --   [ Γ ∣ Δ ]⊢ E-subst-1 N M ∶ α
-- -- -- E-subst-1-lemma {.(S _)} {E} {V Here} {M} {.(_ ,, α)} {Δ} {α} {β} Type-Of-V-Here prf-M = Type-Of-V-Here
-- -- -- E-subst-1-lemma {(S Γ₁)} {E} {V (There x)} {M} {Γ} {Δ} {α} {β} prf-N prf-M =
-- -- --   subst (λ z → [ Γ ∣ Δ ]⊢ z ∶ α) (sym (E-subst-1-V {S Γ₁} {E} {There x} {M})) (change-V-ctx prf-N)
-- -- -- E-subst-1-lemma {A} {E} {Exists-V .EV-Here} {M} {Γ} {Δ} {α} {.α} Type-Of-Exists-V-Here prf-M = prf-M
-- -- -- E-subst-1-lemma {A} {E} {Exists-V .(EV-There _)} {M} {Γ} {Δ} {α} {.α} (Type-Of-Exists-V-There prf-N) prf-M = prf-N
-- -- -- E-subst-1-lemma {A} {E} {Lit x} {M} {Γ} {Δ} {α} {β} (Type-Of-Lit prf) prf-M = Type-Of-Lit prf
-- -- -- E-subst-1-lemma {A} {E} {Add N N₁} {M} {Γ} {Δ} {.Int-Type} {β} (Type-Of-Add prf-N prf-N₁) prf-M = Type-Of-Add (E-subst-1-lemma prf-N prf-M) (E-subst-1-lemma prf-N₁ prf-M)
-- -- -- E-subst-1-lemma {A} {E} {Sub N N₁} {M} {Γ} {Δ} {.Int-Type} {β} (Type-Of-Sub prf-N prf-N₁) prf-M = Type-Of-Sub (E-subst-1-lemma prf-N prf-M) (E-subst-1-lemma prf-N₁ prf-M)
-- -- -- E-subst-1-lemma {A} {E} {And N N₁} {M} {Γ} {Δ} {.Bool-Type} {β} (Type-Of-And prf-N prf-N₁) prf-M = Type-Of-And (E-subst-1-lemma prf-N prf-M) (E-subst-1-lemma prf-N₁ prf-M)
-- -- -- E-subst-1-lemma {A} {E} {Not N} {M} {Γ} {Δ} {.Bool-Type} {β} (Type-Of-Not prf-N) prf-M = Type-Of-Not (E-subst-1-lemma prf-N prf-M)
-- -- -- E-subst-1-lemma {A} {E} {Equal N N₁} {M} {Γ} {Δ} {.Bool-Type} {β} (Type-Of-Equal prf-N prf-N₁) prf-M = Type-Of-Equal (E-subst-1-lemma prf-N prf-M) (E-subst-1-lemma prf-N₁ prf-M)

-- -- -- data Vec A : SSL-Context → Set where
-- -- --   Vec-Z : A → Vec A Z
-- -- --   Vec-S : ∀ {Γ} → A → Vec A Γ → Vec A (S Γ)

-- -- -- Vec-map : ∀ {Γ A B} → (A → B) → Vec A Γ → Vec B Γ
-- -- -- Vec-map f (Vec-Z x) = Vec-Z (f x)
-- -- -- Vec-map f (Vec-S x v) = Vec-S (f x) (Vec-map f v)

-- -- -- data Heaplet C (E : Exist-Context) Γ Δ : Set where
-- -- --   Points-To : (lhs : SSL-Expr C E) → SSL-Expr C E → [ Γ ∣ Δ ]⊢ lhs ∶ Loc-Type → Heaplet C E Γ Δ
-- -- --   -- [_,,_] : A → ℕ → Heaplet C
-- -- --   _·_ : ∀ {Γ′} → Labeled-Pred-Name → Vec (SSL-Expr C E) Γ′ → Heaplet C E Γ Δ

-- -- -- Heaplet-E-subst-1 : ∀ {C} {E : Exist-Context} {Γ Δ α} →
-- -- --   Heaplet C (Exist-S E) Γ (Δ ,, α) →
-- -- --   (M : SSL-Expr C E) →
-- -- --   [ Γ ∣ Δ ]⊢ M ∶ α →
-- -- --   Heaplet C E Γ Δ
-- -- -- Heaplet-E-subst-1 {A} {E} (Points-To lhs x prf) M prf-M =
-- -- --   Points-To (E-subst-1 lhs M) (E-subst-1 x M) (E-subst-1-lemma prf prf-M)
-- -- -- Heaplet-E-subst-1 {A} {E} (P · x₁) M prf-M = P · Vec-map (λ y → E-subst-1 y M) x₁

-- -- -- record Assertion C (E : Exist-Context) (Γ : Type-Context C) (Δ : E-Type-Context E) : Set where
-- -- --   field
-- -- --     pure : SSL-Expr C E
-- -- --     pure-is-Bool : [ Γ ∣ Δ ]⊢ pure ∶ Bool-Type
-- -- --     spatial : List (Heaplet C E Γ Δ)

-- -- -- Assertion-E-subst-1 : ∀ {C} {E : Exist-Context} {Γ Δ α} →
-- -- --   Assertion C (Exist-S E) Γ (Δ ,, α) →
-- -- --   (M : SSL-Expr C E) →
-- -- --   [ Γ ∣ Δ ]⊢ M ∶ α →
-- -- --   Assertion C E Γ Δ
-- -- -- Assertion-E-subst-1 {A} {E} record { pure = pure ; pure-is-Bool = pure-is-Bool ; spatial = spatial } M M-prf =
-- -- --   record
-- -- --     { pure = E-subst-1 pure M
-- -- --     ; pure-is-Bool = E-subst-1-lemma pure-is-Bool M-prf
-- -- --     ; spatial = Data.List.map (λ h → Heaplet-E-subst-1 h M M-prf) spatial
-- -- --     }

-- -- -- -- Assertion-closed : (A : Set) → Type-Context Exist-Z → Set
-- -- -- -- Assertion-closed A = Assertion A Exist-Z

-- -- -- record Ind-Pred-Branch {C : SSL-Context} {E : Exist-Context} (Γ : Type-Context C) (Δ : E-Type-Context E) : Set where
-- -- --   field
-- -- --     cond : SSL-Expr C E
-- -- --     cond-is-Bool : [ Γ ∣ Δ ]⊢ cond ∶ Bool-Type
-- -- --     body : Assertion C E Γ Δ

-- -- -- record Ind-Pred (n : Pred-Name) {C : SSL-Context} {E : Exist-Context} (Γ : Type-Context C) (Δ : E-Type-Context E) : Set where
-- -- --   field
-- -- --     branches : List (Ind-Pred-Branch Γ Δ)

-- -- -- record Ind-Rule (C : SSL-Context) {E : Exist-Context} (Γ : Type-Context C) (Δ : E-Type-Context E) : Set where
-- -- --   field
-- -- --     name : Pred-Name
-- -- --     assertion : Assertion C E Γ Δ

-- -- -- -- Store : SSL-Context → Set
-- -- -- -- Store Γ = SSL-Var Γ → Val

-- -- -- -- -- data Store {Γ} : ∀ {E} →  → SSL-Var Γ → Val → Set


-- -- -- -- -- E-Store-ap : ∀ {Γ E} → Store Γ → SSL-Expr′ Γ E → SSL-Expr-Val E
-- -- -- -- -- E-Store-ap s (V x) = Lit (s x)
-- -- -- -- -- E-Store-ap s (Exists-V x) = Exists-V x
-- -- -- -- -- -- E-Store-ap s (Exists-Intro e) = Exists-Intro (E-Store-ap s e)
-- -- -- -- -- E-Store-ap s (Lit x) = Lit x
-- -- -- -- -- E-Store-ap s (Add x y) = Add (E-Store-ap s x) (E-Store-ap s y)
-- -- -- -- -- E-Store-ap s (Sub x y) = Sub (E-Store-ap s x) (E-Store-ap s y)
-- -- -- -- -- E-Store-ap s (And x y) = And (E-Store-ap s x) (E-Store-ap s y)
-- -- -- -- -- E-Store-ap s (Not x) = Not (E-Store-ap s x)
-- -- -- -- -- E-Store-ap s (Equal x y) = Equal (E-Store-ap s x) (E-Store-ap s y)

-- -- -- -- -- E-Store-ap-preserves-Type :
-- -- -- -- --   ∀ {Γ E Δ α} (s : Store Γ) (e : SSL-Expr′ Γ E) → Δ ⊢ e ∶ α →
-- -- -- -- --   Δ ⊢ E-Store-ap s e ∶ α
-- -- -- -- -- E-Store-ap-preserves-Type s (V x) Type-Of-V with s x
-- -- -- -- -- ... | Val-Loc x₁ = {!!}
-- -- -- -- -- ... | Val-Int x₁ = {!!}
-- -- -- -- -- ... | Val-Bool x₁ = {!!}
-- -- -- -- -- E-Store-ap-preserves-Type s (Exists-V x) prf-e = {!!}
-- -- -- -- -- E-Store-ap-preserves-Type s (Lit x) prf-e = {!!}
-- -- -- -- -- E-Store-ap-preserves-Type s (Add e e₁) prf-e = {!!}
-- -- -- -- -- E-Store-ap-preserves-Type s (Sub e e₁) prf-e = {!!}
-- -- -- -- -- E-Store-ap-preserves-Type s (And e e₁) prf-e = {!!}
-- -- -- -- -- E-Store-ap-preserves-Type s (Not e) prf-e = {!!}
-- -- -- -- -- E-Store-ap-preserves-Type s (Equal e e₁) prf-e = {!!}

-- -- -- -- -- -- E-Store-ap-preserves-Is-Bool :
-- -- -- -- -- --   ∀ {Γ E} (s : Store Γ) (e : SSL-Expr′ Γ E) → (Is-Bool e) →
-- -- -- -- -- --   Is-Bool (E-Store-ap s e)
-- -- -- -- -- -- E-Store-ap-preserves-Is-Bool s .(Lit (Val-Bool _)) Is-Bool-Lit = Is-Bool-Lit
-- -- -- -- -- -- E-Store-ap-preserves-Is-Bool s (And x y) (Is-Bool-And prf prf₁) = Is-Bool-And (E-Store-ap-preserves-Is-Bool s x prf)
-- -- -- -- -- --                                                                            (E-Store-ap-preserves-Is-Bool s y prf₁)
-- -- -- -- -- -- E-Store-ap-preserves-Is-Bool s (Not x) (Is-Bool-Not prf) = Is-Bool-Not (E-Store-ap-preserves-Is-Bool s x prf)
-- -- -- -- -- -- E-Store-ap-preserves-Is-Bool s .(Equal _ _) Is-Bool-Equal = Is-Bool-Equal

-- -- -- -- -- -- H-Store-ap : ∀ {Γ E} → Store Γ → Heaplet′ Γ E → Heaplet-Val E
-- -- -- -- -- -- H-Store-ap s (x ↦ y) = Lit (s _) ↦ V (s _) --E-Store-ap s y
-- -- -- -- -- -- -- H-Store-ap s [ x ,, y ] = [ s x ,, y ]
-- -- -- -- -- -- H-Store-ap s (p · xs) = p · Vec-map (E-Store-ap s) xs

-- -- -- -- -- -- A-Store-ap : ∀ {Γ E} → Store Γ → Assertion′ Γ E → Assertion-Val E
-- -- -- -- -- -- A-Store-ap s record { pure = pure ; pure-Is-Bool = pure-Is-Bool ; spatial = spatial } =
-- -- -- -- -- --   record
-- -- -- -- -- --     { pure = E-Store-ap s pure
-- -- -- -- -- --     ; pure-Is-Bool = E-Store-ap-preserves-Is-Bool s pure pure-Is-Bool
-- -- -- -- -- --     ; spatial = Data.List.map (H-Store-ap s) spatial
-- -- -- -- -- --     }

-- -- -- -- -- -- data SSL-Expr-Val-⇓ {E} : SSL-Expr-Val E → Val → Set where
-- -- -- -- -- --   SSL-Expr-Val-⇓-V : ∀ {x} → SSL-Expr-Val-⇓ (V x) x
-- -- -- -- -- --   SSL-Expr-Val-⇓-Lit : ∀ {v} →
-- -- -- -- -- --     SSL-Expr-Val-⇓ (Lit v) v

-- -- -- -- -- --   SSL-Expr-Val-⇓-Add : ∀ {x y x-val y-val} →
-- -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Int x-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Int y-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ (Add x y) (Val-Int (x-val + y-val))

-- -- -- -- -- --   SSL-Expr-Val-⇓-Sub : ∀ {x y x-val y-val} →
-- -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Int x-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Int y-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ (Sub x y) (Val-Int (x-val - y-val))

-- -- -- -- -- --   SSL-Expr-Val-⇓-And : ∀ {x y x-val y-val} →
-- -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Bool x-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Bool y-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ (And x y) (Val-Bool (x-val ∧ y-val))

-- -- -- -- -- --   SSL-Expr-Val-⇓-Not : ∀ {x x-val} →
-- -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Bool x-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ (Not x) (Val-Bool (not x-val))

-- -- -- -- -- --   SSL-Expr-Val-⇓-Equal-true : ∀ {x y x-val y-val} →
-- -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Int x-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Int y-val) →
-- -- -- -- -- --     x-val ≡ y-val →
-- -- -- -- -- --     SSL-Expr-Val-⇓ (Equal x y) (Val-Bool true)

-- -- -- -- -- --   SSL-Expr-Val-⇓-Equal-false : ∀ {x y x-val y-val} →
-- -- -- -- -- --     SSL-Expr-Val-⇓ x (Val-Int x-val) →
-- -- -- -- -- --     SSL-Expr-Val-⇓ y (Val-Int y-val) →
-- -- -- -- -- --     x-val ≢ y-val →
-- -- -- -- -- --     SSL-Expr-Val-⇓ (Equal x y) (Val-Bool false)

-- -- -- -- -- -- data SSL-Expr′-⇓ {E Γ} (s : Store Γ) : SSL-Expr′ Γ E → Val → Set where
-- -- -- -- -- --   SSL-Expr′-⇓-eval : (e : SSL-Expr′ Γ E) (e-val : SSL-Expr-Val E) →
-- -- -- -- -- --     (v : Val) →
-- -- -- -- -- --     e-val ≡ E-Store-ap s e →
-- -- -- -- -- --     SSL-Expr-Val-⇓ e-val v →
-- -- -- -- -- --     SSL-Expr′-⇓ s e v


-- -- -- -- -- -- data SSL-Expr′-⇓-Vec {E} : ∀ {Γ Γ′} (s : Store Γ) → Vec (SSL-Expr′ Γ E) Γ′ → Vec Val Γ′ → Set where
-- -- -- -- -- --   SSL-Expr′-⇓-Vec-Z : ∀ {Γ} {s} {x x-val} →
-- -- -- -- -- --     SSL-Expr′-⇓ s x x-val →
-- -- -- -- -- --     SSL-Expr′-⇓-Vec {_} {Γ} s (Vec-Z x) (Vec-Z x-val)
-- -- -- -- -- --   SSL-Expr′-⇓-Vec-S : ∀ {Γ} {Γ′} {s} {x x-val} {xs xs-vals} →
-- -- -- -- -- --     SSL-Expr′-⇓ s x x-val →
-- -- -- -- -- --     SSL-Expr′-⇓-Vec {_} {Γ} {Γ′} s xs xs-vals →
-- -- -- -- -- --     SSL-Expr′-⇓-Vec s (Vec-S x xs) (Vec-S x-val xs-vals)

-- -- -- -- -- -- Vec→Store : ∀ {Γ} → Vec Val Γ → Store Γ
-- -- -- -- -- -- Vec→Store {.Z} (Vec-Z x) [ Here :+ ix ] = ix-Val x ix
-- -- -- -- -- -- Vec→Store {.(S _)} (Vec-S x vec) [ Here :+ ix ] = ix-Val x ix
-- -- -- -- -- -- Vec→Store {.(S _)} (Vec-S x vec) [ There var :+ ix ] =
-- -- -- -- -- --   Vec→Store vec [ var :+ ix ]

-- -- -- -- -- -- Satisfies-Expr : ∀ {Γ E} (s : Store Γ) → (e : SSL-Expr′ Γ E) → Is-Bool e → Set
-- -- -- -- -- -- Satisfies-Expr {Γ} s (Lit (Val-Bool x)) Is-Bool-Lit = ⊤
-- -- -- -- -- -- Satisfies-Expr {Γ} s (And x y) (Is-Bool-And prf-x prf-y) = (Satisfies-Expr s x prf-x) × (Satisfies-Expr s y prf-y)
-- -- -- -- -- -- Satisfies-Expr {Γ} s (Not x) (Is-Bool-Not prf) = ¬ (Satisfies-Expr s x prf)
-- -- -- -- -- -- Satisfies-Expr {Γ} s (Equal x y) Is-Bool-Equal = x ≡ y

-- -- -- -- -- -- Heap : Set
-- -- -- -- -- -- -- Heap = Loc → Maybe ℤ
-- -- -- -- -- -- Heap = List (Loc × Val)

-- -- -- -- -- -- data Dom : Heap → List Loc → Set where
-- -- -- -- -- --   Dom-[] : Dom [] []
-- -- -- -- -- --   Dom-∷ : ∀ {loc i rest locs} →
-- -- -- -- -- --     Dom rest locs →
-- -- -- -- -- --     Dom ((loc , i) ∷ rest) (loc ∷ locs)

-- -- -- -- -- -- _∈_ : ∀ {A} → A → List A → Set
-- -- -- -- -- -- x ∈ xs = Any (_≡ x) xs

-- -- -- -- -- -- data Disjoint : Heap → Heap → Set where
-- -- -- -- -- --   Disjoint-[] : ∀ {h} → Disjoint [] h
-- -- -- -- -- --   Disjoint-∷ : ∀ {loc i rest h dom-h} →
-- -- -- -- -- --     Disjoint rest h →
-- -- -- -- -- --     Dom h dom-h →
-- -- -- -- -- --     ¬ (loc ∈ dom-h) →
-- -- -- -- -- --     Disjoint ((loc , i) ∷ rest) h

-- -- -- -- -- -- _≡S_ : ∀ {A} → List A → List A → Set
-- -- -- -- -- -- _≡S_ xs ys = (∀ x → x ∈ xs → x ∈ ys) × (∀ y → y ∈ ys → y ∈ xs)

-- -- -- -- -- -- data _∘_==_ : Heap → Heap → Heap → Set where
-- -- -- -- -- --   mk-∘ : ∀ h h′ h′′ →
-- -- -- -- -- --     Disjoint h h′ →
-- -- -- -- -- --     h′′ ≡S (h ++ h′) →
-- -- -- -- -- --     h ∘ h′ == h′′

-- -- -- -- -- -- -- Ind-Pred-Env : SSL-Context → Set
-- -- -- -- -- -- -- Ind-Pred-Env Γ = (n : Pred-Name) → Ind-Pred n Γ

-- -- -- -- -- -- Ind-Pred-Denotation : SSL-Context → Set₁
-- -- -- -- -- -- Ind-Pred-Denotation Γ = Heap → Store Γ → Set

-- -- -- -- -- -- Ind-Pred-Interpret : SSL-Context → Set₁
-- -- -- -- -- -- Ind-Pred-Interpret Γ =
-- -- -- -- -- --   (n : Pred-Name) →
-- -- -- -- -- --   Ind-Pred-Denotation Γ

-- -- -- -- -- -- data Satisfies-Heaplet₀ : ∀ {Γ} (s : Store Γ) → (h : Heap) → Ind-Pred-Interpret Γ → Heaplet′ Γ Exist-Z → Set where
-- -- -- -- -- --   Satisfies-Heaplet₀-↦ : ∀ {Γ} {s : Store Γ} {h} {env} {loc-v rhs-e} {loc rhs} →
-- -- -- -- -- --     SSL-Expr′-⇓ {Exist-Z} s (V loc-v) (Val-Loc loc) →
-- -- -- -- -- --     SSL-Expr′-⇓ s rhs-e rhs →
-- -- -- -- -- --     h ≡ ((loc , rhs) ∷ []) →
-- -- -- -- -- --     Satisfies-Heaplet₀ s h env (loc-v ↦ rhs-e)

-- -- -- -- -- --   Satisfies-Heaplet₀-· : ∀ {Γ} {s : Store Γ} {h} {env} {labeled-p-name p-name args} {args-vals} →
-- -- -- -- -- --     p-name ≡ get-Pred-Name labeled-p-name →
-- -- -- -- -- --     env p-name h (Vec→Store args-vals) →
-- -- -- -- -- --     SSL-Expr′-⇓-Vec s args args-vals →
-- -- -- -- -- --     Satisfies-Heaplet₀ s h env (labeled-p-name · args)

-- -- -- -- -- -- data Satisfies-Heaplet₀-E {Γ} (s : Store Γ) (h : Heap) (env : Ind-Pred-Interpret Γ) : ∀ {E} → Heaplet′ Γ E → Set where
-- -- -- -- -- --   Satisfies-Heaplet₀-E-Z : ∀ {heaplet} →
-- -- -- -- -- --     Satisfies-Heaplet₀ s h env heaplet →
-- -- -- -- -- --     Satisfies-Heaplet₀-E s h env {Exist-Z} heaplet

-- -- -- -- -- --   Satisfies-Heaplet₀-E-S : ∀ {E heaplet} →
-- -- -- -- -- --     (Σ Val λ v →
-- -- -- -- -- --       Satisfies-Heaplet₀-E s h env {E} (Heaplet-E-subst-1 heaplet {!!})
-- -- -- -- -- --     ) →
-- -- -- -- -- --     Satisfies-Heaplet₀-E s h env {Exist-S E} heaplet

-- -- -- -- -- -- -- data Satisfies-spatial₀ {E} : ∀ {Γ} (s : Store Γ) → (h : Heap) → Ind-Pred-Interpret Γ → List (Heaplet′ Γ E) → Set where
-- -- -- -- -- -- --   Satisfies-spatial₀-[] : ∀ {Γ} {s : Store Γ} {env} →
-- -- -- -- -- -- --     Satisfies-spatial₀ s [] env []

-- -- -- -- -- -- --   Satisfies-spatial₀-∷ : ∀ {Γ} {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} {env} →
-- -- -- -- -- -- --     h₁ ∘ h₂ == h →
-- -- -- -- -- -- --     Satisfies-Heaplet₀ s h₁ env Σ₁ →
-- -- -- -- -- -- --     Satisfies-spatial₀ s h₂ env Σ₂ →
-- -- -- -- -- -- --     Satisfies-spatial₀ s h env (Σ₁ ∷ Σ₂)

-- -- -- -- -- -- -- record Satisfies-Assertion₀ {E Γ} (s : Store Γ) (h : Heap) (env : Ind-Pred-Interpret Γ) (a : Assertion′ Γ E) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     pure-prf : Satisfies-Expr s (Assertion.pure a) (Assertion.pure-Is-Bool a)
-- -- -- -- -- -- --     spatial-prf : Satisfies-spatial₀ s h env (Assertion.spatial a)

-- -- -- -- -- -- -- φ : ∀ {E} {Γ} → List (Ind-Rule Γ) → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- φ {E} {Γ} rules env P h s =
-- -- -- -- -- -- --   ∃[ F ] (Satisfies-Assertion₀ {E} s h env F × (record { name = P ; assertion = F } ∈ rules))

-- -- -- -- -- -- -- _⊆_ : ∀ {ℓ m} {A : Set ℓ} (P Q : A → Set m) → Set (ℓ Agda.Primitive.⊔ m)
-- -- -- -- -- -- -- _⊆_ P Q = ∀ a → P a → Q a

-- -- -- -- -- -- -- _⊆₂_ : ∀ {ℓ m} {A B : Set ℓ} (P Q : A → B → Set m) → Set (ℓ Agda.Primitive.⊔ m)
-- -- -- -- -- -- -- _⊆₂_ P Q = ∀ a b → P a b → Q a b

-- -- -- -- -- -- -- _≤′_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Set
-- -- -- -- -- -- -- _≤′_ X X′ = ∀ P → X P ⊆₂ X′ P

-- -- -- -- -- -- -- _⊔_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- _⊔_ {Γ} env-1 env-2 = λ n x y → env-1 n x y ⊎ env-2 n x y

-- -- -- -- -- -- -- _⊓_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- _⊓_ {Γ} env-1 env-2 = λ n x y → env-1 n x y × env-2 n x y

-- -- -- -- -- -- -- ∅-interpret : ∀ {Γ} → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- ∅-interpret = λ n h args → ⊥

-- -- -- -- -- -- -- ∅-interpret-least : ∀ {Γ} → (X : Ind-Pred-Interpret Γ) → ∅-interpret ≤′ X
-- -- -- -- -- -- -- ∅-interpret-least X P a b ()

-- -- -- -- -- -- -- Satisfies-Heaplet₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-Heaplet₀ {E} s h X A → Satisfies-Heaplet₀ s h X′ A
-- -- -- -- -- -- -- Satisfies-Heaplet₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ ↦ _)} prf-1 (Satisfies-Heaplet₀-↦ x x₁ x₂) = Satisfies-Heaplet₀-↦ x x₁ x₂
-- -- -- -- -- -- -- Satisfies-Heaplet₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ · _)} prf-1 (Satisfies-Heaplet₀-· {_} {_} {_} {_} {_} {p-name} {args} {args-vals} refl x x₁) =
-- -- -- -- -- -- --   let
-- -- -- -- -- -- --     z = prf-1 p-name h (Vec→Store args-vals) x
-- -- -- -- -- -- --   in
-- -- -- -- -- -- --   Satisfies-Heaplet₀-· refl z x₁

-- -- -- -- -- -- -- Satisfies-spatial₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-spatial₀ s h X A → Satisfies-spatial₀ s h X′ A
-- -- -- -- -- -- -- Satisfies-spatial₀-monotone {E} {Γ} {s} {.[]} {X} {X′} {.[]} prf-1 Satisfies-spatial₀-[] = Satisfies-spatial₀-[]
-- -- -- -- -- -- -- Satisfies-spatial₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ ∷ _)} prf-1 (Satisfies-spatial₀-∷ x x₁ prf-2) =
-- -- -- -- -- -- --   Satisfies-spatial₀-∷ x (Satisfies-Heaplet₀-monotone {E} prf-1 x₁) (Satisfies-spatial₀-monotone prf-1 prf-2)

-- -- -- -- -- -- -- Satisfies-Assertion₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-Assertion₀ {E} s h X A → Satisfies-Assertion₀ {E} s h X′ A
-- -- -- -- -- -- -- Satisfies-Assertion₀-monotone {E} {Γ} {s} {h} {X} {X′} {A} prf-1 record { pure-prf = pure-prf ; spatial-prf = spatial-prf } =
-- -- -- -- -- -- --   record { pure-prf = pure-prf ; spatial-prf = Satisfies-spatial₀-monotone prf-1 spatial-prf }

-- -- -- -- -- -- -- φ-monotone : ∀ {E Γ} {rules} {X X′ : Ind-Pred-Interpret Γ} → X ≤′ X′ → φ {E} rules X ≤′ φ rules X′
-- -- -- -- -- -- -- φ-monotone {E} {Γ} {rules} {X} {X′} prf-1 P a b (fst , prf-2 , prf-3) =
-- -- -- -- -- -- --   fst , Satisfies-Assertion₀-monotone prf-1 prf-2 , prf-3

-- -- -- -- -- -- -- Ordinal : Set
-- -- -- -- -- -- -- Ordinal = ℕ

-- -- -- -- -- -- -- iterate-φ : ∀ {E Γ} (rules : List (Ind-Rule Γ)) → Ordinal → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- iterate-φ {E} {Γ} rules zero = ∅-interpret
-- -- -- -- -- -- -- iterate-φ {E} {Γ} rules (ℕ.suc α) = φ {E} rules (iterate-φ {E} rules α)

-- -- -- -- -- -- -- ⟦_⟧_ : ∀ {E Γ} → List (Ind-Rule Γ) → Ordinal → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- ⟦_⟧_ {E} rules α = iterate-φ {E} rules α

-- -- -- -- -- -- -- Label-Valuation : Set
-- -- -- -- -- -- -- Label-Valuation = Pred-Label → Ordinal

-- -- -- -- -- -- -- data Satisfies-Heaplet {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) : ∀ (s : Store Γ) → (h : Heap) → Heaplet′ Γ E → Set where
-- -- -- -- -- -- --   Satisfies-Heaplet-↦ : ∀ {s : Store Γ} {h} {loc-v rhs-e} {loc rhs} →
-- -- -- -- -- -- --     SSL-Expr′-⇓ {E} s (V loc-v) (Val-Loc loc) →
-- -- -- -- -- -- --     SSL-Expr′-⇓ s rhs-e rhs →
-- -- -- -- -- -- --     h ≡ ((loc , rhs) ∷ []) →
-- -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h (loc-v ↦ rhs-e)

-- -- -- -- -- -- --   Satisfies-Heaplet-· : ∀ {s : Store Γ} {h} {labeled-p-name p-name args} {args-vals} →
-- -- -- -- -- -- --     let α = Pred-Name-label labeled-p-name
-- -- -- -- -- -- --     in
-- -- -- -- -- -- --     p-name ≡ get-Pred-Name labeled-p-name →
-- -- -- -- -- -- --     (⟦_⟧_ {E} rules (ρ α)) p-name h (Vec→Store args-vals) →
-- -- -- -- -- -- --     SSL-Expr′-⇓-Vec s args args-vals →
-- -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h (labeled-p-name · args)

-- -- -- -- -- -- -- data Satisfies-spatial {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) : ∀ (s : Store Γ) → (h : Heap) → List (Heaplet′ Γ E) → Set where
-- -- -- -- -- -- --   Satisfies-spatial-[] : ∀ {s : Store Γ} →
-- -- -- -- -- -- --     Satisfies-spatial rules ρ s [] []

-- -- -- -- -- -- --   Satisfies-spatial-∷ : ∀ {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} →
-- -- -- -- -- -- --     h₁ ∘ h₂ == h →
-- -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h₁ Σ₁ →
-- -- -- -- -- -- --     Satisfies-spatial rules ρ s h₂ Σ₂ →
-- -- -- -- -- -- --     Satisfies-spatial rules ρ s h (Σ₁ ∷ Σ₂)

-- -- -- -- -- -- -- record Satisfies-Assertion {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) (s : Store Γ) (h : Heap) (a : Assertion′ Γ E) : Set where
-- -- -- -- -- -- --   field
-- -- -- -- -- -- --     pure-prf : Satisfies-Expr s (Assertion.pure a) (Assertion.pure-Is-Bool a)
-- -- -- -- -- -- --     spatial-prf : Satisfies-spatial rules ρ s h (Assertion.spatial a)

-- -- -- -- -- -- -- data Label-Constraint : Set where
-- -- -- -- -- -- --   Ord-≤ : Pred-Label → Pred-Label → Label-Constraint
-- -- -- -- -- -- --   Ord-< : Pred-Label → Pred-Label → Label-Constraint

-- -- -- -- -- -- -- data Constraints-hold (ρ : Label-Valuation) : List Label-Constraint → Set where
-- -- -- -- -- -- --   Constraints-hold-[] : Constraints-hold ρ []
-- -- -- -- -- -- --   Constraints-hold-∷-≤ : ∀ {α β rest} →
-- -- -- -- -- -- --     ρ α ≤ ρ β →
-- -- -- -- -- -- --     Constraints-hold ρ rest →
-- -- -- -- -- -- --     Constraints-hold ρ (Ord-≤ α β ∷ rest)
-- -- -- -- -- -- --   Constraints-hold-∷-< : ∀ {α β rest} →
-- -- -- -- -- -- --     ρ α < ρ β →
-- -- -- -- -- -- --     Constraints-hold ρ rest →
-- -- -- -- -- -- --     Constraints-hold ρ (Ord-< α β ∷ rest)

-- -- -- -- -- -- -- Constrained-Formula : Exist-Context → SSL-Context → Set
-- -- -- -- -- -- -- Constrained-Formula E Γ =
-- -- -- -- -- -- --   List Pred-Label × List Label-Constraint × Assertion′ Γ E

-- -- -- -- -- -- -- _==/[_]_ : Label-Valuation → List Pred-Label → Label-Valuation → Set
-- -- -- -- -- -- -- _==/[_]_ ρ αs ρ′ = ∀ α → α ∈ αs → ρ α ≡ ρ′ α

-- -- -- -- -- -- -- data Satisfies-Constrained-Formula {E Γ} (rules : List (Ind-Rule Γ)) : Label-Valuation → Store Γ → Heap → Constrained-Formula E Γ → Set where
-- -- -- -- -- -- --   mk-Satisfies-Constrained-Formula : ∀ {ρ s h αs constraints asn} →
-- -- -- -- -- -- --     Σ Label-Valuation (λ ρ′ →
-- -- -- -- -- -- --       ρ′ ==/[ αs ] ρ →
-- -- -- -- -- -- --       Constraints-hold ρ′ constraints →
-- -- -- -- -- -- --       Satisfies-Assertion rules ρ′ s h asn) →
-- -- -- -- -- -- --     Satisfies-Constrained-Formula rules ρ s h (αs , constraints , asn)

-- -- -- -- -- -- -- _,_,_⊨[_]_ : ∀ {E Γ} → Label-Valuation → Store Γ → Heap → List (Ind-Rule Γ) → Constrained-Formula E Γ → Set
-- -- -- -- -- -- -- _,_,_⊨[_]_ ρ s h rules asn = Satisfies-Constrained-Formula rules ρ s h asn