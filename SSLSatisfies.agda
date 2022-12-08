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


module SSLSatisfies
  (Pred-Name : Set)
  (Pred-Label : Set)
  (Loc-Name : Set)
  where

open import SSL (Pred-Name) (Pred-Label) (Loc-Name)

open Ambient-Context

Satisfies-Expr₀ : ∀ {C : SSL-Context} {Γ : Type-Context C} (s : Store Γ) → (e : SSL-Expr Γ ε Bool-Type) → Set
Satisfies-Expr₀ s (V x) with s x
... | Val-Bool true = ⊤
... | Val-Bool false = ⊥
Satisfies-Expr₀ s (Lit (Val-Bool true)) = ⊤
Satisfies-Expr₀ s (Lit (Val-Bool false)) = ⊥
Satisfies-Expr₀ s (And x y) = (Satisfies-Expr₀ s x) × (Satisfies-Expr₀ s y)
Satisfies-Expr₀ s (Not x) = ¬ (Satisfies-Expr₀ s x)
Satisfies-Expr₀ s (Equal x y) = x ≡ y

Satisfies-Expr : ∀ {C : SSL-Context} {E : Exist-Context} {Γ : Type-Context C} {Δ : E-Type-Context E} (s : Store Γ) → (e : SSL-Expr Γ Δ Bool-Type) → Set
Satisfies-Expr {_} {Exist-Z} {_} {ε} s e = Satisfies-Expr₀ s e
Satisfies-Expr {_} {(Exist-S _)} {_} {Δ₀ ,, x} s e = ∃[ v ] Satisfies-Expr s (E-subst-1 e v)

Heap : Set
-- Heap = Loc → Maybe ℤ
Heap = List (∃[ α ] (Loc × Val α))

data Dom : Heap → List Loc → Set where
  Dom-[] : Dom [] []
  Dom-∷ : ∀ {α loc i rest locs} →
    Dom rest locs →
    Dom ((α , loc , i) ∷ rest) (loc ∷ locs)

_∈_ : ∀ {A} → A → List A → Set
x ∈ xs = Any (_≡ x) xs

data Disjoint : Heap → Heap → Set where
  Disjoint-[] : ∀ {h} → Disjoint [] h
  Disjoint-∷ : ∀ {α loc i rest h dom-h} →
    Disjoint rest h →
    Dom h dom-h →
    ¬ (loc ∈ dom-h) →
    Disjoint ((α , loc , i) ∷ rest) h

_≡S_ : ∀ {A} → List A → List A → Set
_≡S_ xs ys = (∀ x → x ∈ xs → x ∈ ys) × (∀ y → y ∈ ys → y ∈ xs)

data _∘_==_ : Heap → Heap → Heap → Set where
  mk-∘ : ∀ h h′ h′′ →
    Disjoint h h′ →
    h′′ ≡S (h ++ h′) →
    h ∘ h′ == h′′

Ind-Pred-Env : ∀ {C E} → Type-Context C → E-Type-Context E → Set
Ind-Pred-Env Γ Δ = (n : Pred-Name) → Ind-Pred Γ Δ n

Ind-Pred-Denotation : ∀ {C} → Type-Context C → Set₁
Ind-Pred-Denotation Γ = ∃[ E ] Σ (E-Type-Context E) λ Δ → Heap → Val-Vec Γ Δ Γ → Set

Ind-Pred-Denotation₀ : ∀ {C} → Type-Context C → Set₁
Ind-Pred-Denotation₀ Γ = Heap → Val-Vec Γ ε Γ → Set

-- close-denotation′ : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} → (Heap → Val-Vec Γ Δ Γ → Set) → Ind-Pred-Denotation₀ Γ
-- close-denotation′ {_} {.Exist-Z} {Γ} {ε} f = f
-- close-denotation′ {_} {.(Exist-S _)} {Γ} {Δ ,, x} f =
--   let
--     g : Heap → Val-Vec Γ Δ Γ → Set
--     g h v = f {!!} {!!}
--   in
--   {!!}

-- close-denotation : ∀ {C} {Γ : Type-Context C} → Ind-Pred-Denotation Γ → Ind-Pred-Denotation₀ Γ
-- close-denotation = {!!}

Ind-Pred-Interpret : ∀ {C} → Type-Context C → Set₁
Ind-Pred-Interpret Γ =
  (n : Pred-Name) →
  Ind-Pred-Denotation Γ

Heaplet-E-subst-1 : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} {α : SSL-Type} →
  SSL-Expr Γ Δ α →
  Heaplet Γ (Δ ,, α) → Heaplet Γ Δ
Heaplet-E-subst-1 e (Points-To lhs x) = Points-To (E-subst-1 lhs e) (E-subst-1 x e)
Heaplet-E-subst-1 e (n · x) = n · Vec-map (λ z → E-subst-1 z e) x

data Satisfies-Heaplet₀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} : ∀ (s : Store Γ) → (h : Heap) → Ind-Pred-Interpret Γ → Heaplet Γ Δ → Set where
  Satisfies-Heaplet₀-↦ : ∀  {s : Store Γ} {h} {env} {loc-v rhs-e} {loc rhs} →
    SSL-Expr-Val-⇓ Γ Δ s (V loc-v) (Val-Loc loc) →
    SSL-Expr-Val-⇓ Γ Δ s rhs-e rhs →
    h ≡ ((Loc-Type , loc , rhs) ∷ []) →
    Satisfies-Heaplet₀ s h env (Points-To (V loc-v) rhs-e)

  Satisfies-Heaplet₀-· : ∀ {s : Store Γ} {h} {env} {labeled-p-name p-name args} {args-vals} →
    p-name ≡ get-Pred-Name labeled-p-name →
    proj₂ (proj₂ (env p-name)) h (Val-Vec-any-Δ args-vals) →
    SSL-Expr-⇓-Vec Γ Δ s args args-vals →
    Satisfies-Heaplet₀ s h env (labeled-p-name · args)

data Satisfies-Heaplet₀-E {C} {Γ : Type-Context C} (s : Store Γ) (h : Heap) (env : Ind-Pred-Interpret Γ) : ∀ {E} {Δ : E-Type-Context E} → Heaplet Γ Δ → Set where
  Satisfies-Heaplet₀-E-Z : ∀ {heaplet : Heaplet Γ ε} →
    Satisfies-Heaplet₀ s h env heaplet →
    Satisfies-Heaplet₀-E s h env {Exist-Z} heaplet

  Satisfies-Heaplet₀-E-S : ∀ {E} {Δ : E-Type-Context E} {α heaplet} →
    (Σ (Val α) λ v →
      Satisfies-Heaplet₀-E s h env {E} {Δ} (Heaplet-E-subst-1 (Lit v) heaplet)
    ) →
    Satisfies-Heaplet₀-E s h env {Exist-S E} heaplet

data Satisfies-spatial₀ {C E} : ∀ {Γ : Type-Context C} {Δ : E-Type-Context E} (s : Store Γ) → (h : Heap) → Ind-Pred-Interpret Γ → List (Heaplet Γ Δ) → Set where
  Satisfies-spatial₀-[] : ∀ {Γ Δ} {s : Store Γ} {env} →
    Satisfies-spatial₀ {_} {_} {Γ} {Δ} s [] env []

  Satisfies-spatial₀-∷ : ∀ {Γ Δ} {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} {env} →
    h₁ ∘ h₂ == h →
    Satisfies-Heaplet₀ {_} {_} {Γ} {Δ} s h₁ env Σ₁ →
    Satisfies-spatial₀ s h₂ env Σ₂ →
    Satisfies-spatial₀ s h env (Σ₁ ∷ Σ₂)

record Satisfies-Assertion₀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} (s : Store Γ) (h : Heap) (env : Ind-Pred-Interpret Γ) (a : Assertion Γ Δ) : Set where
  field
    pure-prf : Satisfies-Expr s (Assertion.pure a)
    spatial-prf : Satisfies-spatial₀ s h env (Assertion.spatial a)

φ : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} → Store Γ → List (Ind-Rule Γ Δ) → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
φ {C} {E} {Γ} {Δ} store rules env P = E , Δ , λ H vec →
  ∃[ F ] (Satisfies-Assertion₀ {_} {E} store H env F × (record { name = P ; assertion = F } ∈ rules))

_⊆_ : ∀ {ℓ m} {A : Set ℓ} (P Q : A → Set m) → Set (ℓ Agda.Primitive.⊔ m)
_⊆_ P Q = ∀ a → P a → Q a

_⊆₂_ : ∀ {ℓ m} {A B : Set ℓ} (P Q : A → B → Set m) → Set (ℓ Agda.Primitive.⊔ m)
_⊆₂_ P Q = ∀ a b → P a b → Q a b

-- _≤′_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Set
-- _≤′_ X X′ = ∀ P → proj₂ (proj₂ (X P)) ⊆₂ proj₂ (proj₂ (X′ P))

-- _⊔_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
-- _⊔_ {Γ} env-1 env-2 = λ n x y → env-1 n x y ⊎ env-2 n x y

-- -- -- -- -- -- -- -- _⊓_ : ∀ {Γ} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- -- _⊓_ {Γ} env-1 env-2 = λ n x y → env-1 n x y × env-2 n x y

-- -- -- -- -- -- -- -- ∅-interpret : ∀ {Γ} → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- -- ∅-interpret = λ n h args → ⊥

-- -- -- -- -- -- -- -- ∅-interpret-least : ∀ {Γ} → (X : Ind-Pred-Interpret Γ) → ∅-interpret ≤′ X
-- -- -- -- -- -- -- -- ∅-interpret-least X P a b ()

-- -- -- -- -- -- -- -- Satisfies-Heaplet₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-Heaplet₀ {E} s h X A → Satisfies-Heaplet₀ s h X′ A
-- -- -- -- -- -- -- -- Satisfies-Heaplet₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ ↦ _)} prf-1 (Satisfies-Heaplet₀-↦ x x₁ x₂) = Satisfies-Heaplet₀-↦ x x₁ x₂
-- -- -- -- -- -- -- -- Satisfies-Heaplet₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ · _)} prf-1 (Satisfies-Heaplet₀-· {_} {_} {_} {_} {_} {p-name} {args} {args-vals} refl x x₁) =
-- -- -- -- -- -- -- --   let
-- -- -- -- -- -- -- --     z = prf-1 p-name h (Vec→Store args-vals) x
-- -- -- -- -- -- -- --   in
-- -- -- -- -- -- -- --   Satisfies-Heaplet₀-· refl z x₁

-- -- -- -- -- -- -- -- Satisfies-spatial₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-spatial₀ s h X A → Satisfies-spatial₀ s h X′ A
-- -- -- -- -- -- -- -- Satisfies-spatial₀-monotone {E} {Γ} {s} {.[]} {X} {X′} {.[]} prf-1 Satisfies-spatial₀-[] = Satisfies-spatial₀-[]
-- -- -- -- -- -- -- -- Satisfies-spatial₀-monotone {E} {Γ} {s} {h} {X} {X′} {.(_ ∷ _)} prf-1 (Satisfies-spatial₀-∷ x x₁ prf-2) =
-- -- -- -- -- -- -- --   Satisfies-spatial₀-∷ x (Satisfies-Heaplet₀-monotone {E} prf-1 x₁) (Satisfies-spatial₀-monotone prf-1 prf-2)

-- -- -- -- -- -- -- -- Satisfies-Assertion₀-monotone : ∀ {E} {Γ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-Assertion₀ {E} s h X A → Satisfies-Assertion₀ {E} s h X′ A
-- -- -- -- -- -- -- -- Satisfies-Assertion₀-monotone {E} {Γ} {s} {h} {X} {X′} {A} prf-1 record { pure-prf = pure-prf ; spatial-prf = spatial-prf } =
-- -- -- -- -- -- -- --   record { pure-prf = pure-prf ; spatial-prf = Satisfies-spatial₀-monotone prf-1 spatial-prf }

-- -- -- -- -- -- -- -- φ-monotone : ∀ {E Γ} {rules} {X X′ : Ind-Pred-Interpret Γ} → X ≤′ X′ → φ {E} rules X ≤′ φ rules X′
-- -- -- -- -- -- -- -- φ-monotone {E} {Γ} {rules} {X} {X′} prf-1 P a b (fst , prf-2 , prf-3) =
-- -- -- -- -- -- -- --   fst , Satisfies-Assertion₀-monotone prf-1 prf-2 , prf-3

-- -- -- -- -- -- -- -- Ordinal : Set
-- -- -- -- -- -- -- -- Ordinal = ℕ

-- -- -- -- -- -- -- -- iterate-φ : ∀ {E Γ} (rules : List (Ind-Rule Γ)) → Ordinal → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- -- iterate-φ {E} {Γ} rules zero = ∅-interpret
-- -- -- -- -- -- -- -- iterate-φ {E} {Γ} rules (ℕ.suc α) = φ {E} rules (iterate-φ {E} rules α)

-- -- -- -- -- -- -- -- ⟦_⟧_ : ∀ {E Γ} → List (Ind-Rule Γ) → Ordinal → Ind-Pred-Interpret Γ
-- -- -- -- -- -- -- -- ⟦_⟧_ {E} rules α = iterate-φ {E} rules α

-- -- -- -- -- -- -- -- Label-Valuation : Set
-- -- -- -- -- -- -- -- Label-Valuation = Pred-Label → Ordinal

-- -- -- -- -- -- -- -- data Satisfies-Heaplet {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) : ∀ (s : Store Γ) → (h : Heap) → Heaplet′ Γ E → Set where
-- -- -- -- -- -- -- --   Satisfies-Heaplet-↦ : ∀ {s : Store Γ} {h} {loc-v rhs-e} {loc rhs} →
-- -- -- -- -- -- -- --     SSL-Expr′-⇓ {E} s (V loc-v) (Val-Loc loc) →
-- -- -- -- -- -- -- --     SSL-Expr′-⇓ s rhs-e rhs →
-- -- -- -- -- -- -- --     h ≡ ((loc , rhs) ∷ []) →
-- -- -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h (loc-v ↦ rhs-e)

-- -- -- -- -- -- -- --   Satisfies-Heaplet-· : ∀ {s : Store Γ} {h} {labeled-p-name p-name args} {args-vals} →
-- -- -- -- -- -- -- --     let α = Pred-Name-label labeled-p-name
-- -- -- -- -- -- -- --     in
-- -- -- -- -- -- -- --     p-name ≡ get-Pred-Name labeled-p-name →
-- -- -- -- -- -- -- --     (⟦_⟧_ {E} rules (ρ α)) p-name h (Vec→Store args-vals) →
-- -- -- -- -- -- -- --     SSL-Expr′-⇓-Vec s args args-vals →
-- -- -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h (labeled-p-name · args)

-- -- -- -- -- -- -- -- data Satisfies-spatial {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) : ∀ (s : Store Γ) → (h : Heap) → List (Heaplet′ Γ E) → Set where
-- -- -- -- -- -- -- --   Satisfies-spatial-[] : ∀ {s : Store Γ} →
-- -- -- -- -- -- -- --     Satisfies-spatial rules ρ s [] []

-- -- -- -- -- -- -- --   Satisfies-spatial-∷ : ∀ {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} →
-- -- -- -- -- -- -- --     h₁ ∘ h₂ == h →
-- -- -- -- -- -- -- --     Satisfies-Heaplet rules ρ s h₁ Σ₁ →
-- -- -- -- -- -- -- --     Satisfies-spatial rules ρ s h₂ Σ₂ →
-- -- -- -- -- -- -- --     Satisfies-spatial rules ρ s h (Σ₁ ∷ Σ₂)

-- -- -- -- -- -- -- -- record Satisfies-Assertion {E Γ} (rules : List (Ind-Rule Γ)) (ρ : Label-Valuation) (s : Store Γ) (h : Heap) (a : Assertion′ Γ E) : Set where
-- -- -- -- -- -- -- --   field
-- -- -- -- -- -- -- --     pure-prf : Satisfies-Expr s (Assertion.pure a) (Assertion.pure-Is-Bool a)
-- -- -- -- -- -- -- --     spatial-prf : Satisfies-spatial rules ρ s h (Assertion.spatial a)

-- -- -- -- -- -- -- -- data Label-Constraint : Set where
-- -- -- -- -- -- -- --   Ord-≤ : Pred-Label → Pred-Label → Label-Constraint
-- -- -- -- -- -- -- --   Ord-< : Pred-Label → Pred-Label → Label-Constraint

-- -- -- -- -- -- -- -- data Constraints-hold (ρ : Label-Valuation) : List Label-Constraint → Set where
-- -- -- -- -- -- -- --   Constraints-hold-[] : Constraints-hold ρ []
-- -- -- -- -- -- -- --   Constraints-hold-∷-≤ : ∀ {α β rest} →
-- -- -- -- -- -- -- --     ρ α ≤ ρ β →
-- -- -- -- -- -- -- --     Constraints-hold ρ rest →
-- -- -- -- -- -- -- --     Constraints-hold ρ (Ord-≤ α β ∷ rest)
-- -- -- -- -- -- -- --   Constraints-hold-∷-< : ∀ {α β rest} →
-- -- -- -- -- -- -- --     ρ α < ρ β →
-- -- -- -- -- -- -- --     Constraints-hold ρ rest →
-- -- -- -- -- -- -- --     Constraints-hold ρ (Ord-< α β ∷ rest)

-- -- -- -- -- -- -- -- Constrained-Formula : Exist-Context → SSL-Context → Set
-- -- -- -- -- -- -- -- Constrained-Formula E Γ =
-- -- -- -- -- -- -- --   List Pred-Label × List Label-Constraint × Assertion′ Γ E

-- -- -- -- -- -- -- -- _==/[_]_ : Label-Valuation → List Pred-Label → Label-Valuation → Set
-- -- -- -- -- -- -- -- _==/[_]_ ρ αs ρ′ = ∀ α → α ∈ αs → ρ α ≡ ρ′ α

-- -- -- -- -- -- -- -- data Satisfies-Constrained-Formula {E Γ} (rules : List (Ind-Rule Γ)) : Label-Valuation → Store Γ → Heap → Constrained-Formula E Γ → Set where
-- -- -- -- -- -- -- --   mk-Satisfies-Constrained-Formula : ∀ {ρ s h αs constraints asn} →
-- -- -- -- -- -- -- --     Σ Label-Valuation (λ ρ′ →
-- -- -- -- -- -- -- --       ρ′ ==/[ αs ] ρ →
-- -- -- -- -- -- -- --       Constraints-hold ρ′ constraints →
-- -- -- -- -- -- -- --       Satisfies-Assertion rules ρ′ s h asn) →
-- -- -- -- -- -- -- --     Satisfies-Constrained-Formula rules ρ s h (αs , constraints , asn)

-- -- -- -- -- -- -- -- _,_,_⊨[_]_ : ∀ {E Γ} → Label-Valuation → Store Γ → Heap → List (Ind-Rule Γ) → Constrained-Formula E Γ → Set
-- -- -- -- -- -- -- -- _,_,_⊨[_]_ ρ s h rules asn = Satisfies-Constrained-Formula rules ρ s h asn
