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
  (Loc-Name-eq-dec : ∀ (x y : Loc-Name) → (x ≡ y) ⊎ (x ≢ y))
  where

open import SSL (Pred-Name) (Pred-Label) (Loc-Name)
open import HeapDefs (Loc-Name)

open Ambient-Context

ℕ-eq-dec : ∀ (x y : ℕ) → (x ≡ y) ⊎ (x ≢ y)
ℕ-eq-dec zero zero = inj₁ refl
ℕ-eq-dec zero (ℕ.suc y) = inj₂ (λ ())
ℕ-eq-dec (ℕ.suc x) zero = inj₂ (λ ())
ℕ-eq-dec (ℕ.suc x) (ℕ.suc y) with ℕ-eq-dec x y
... | inj₁ x₁ = inj₁ (cong ℕ.suc x₁)
... | inj₂ y₁ = inj₂ λ { _≡_.refl → y₁ refl }

Loc-eq-dec : ∀ (x y : Loc) → (x ≡ y) ⊎ (x ≢ y)
Loc-eq-dec Null Null = inj₁ refl
Loc-eq-dec Null (mk-Loc x x₁) = inj₂ (λ ())
Loc-eq-dec (mk-Loc x x₁) Null = inj₂ (λ ())
Loc-eq-dec (mk-Loc x x₁) (mk-Loc x₂ x₃) with ℕ-eq-dec x₁ x₃
... | inj₂ y = inj₂ λ { _≡_.refl → y refl }
... | inj₁ x₄ with Loc-Name-eq-dec x x₂
Loc-eq-dec (mk-Loc x x₁) (mk-Loc x₂ x₃) | inj₁ refl | inj₁ refl = inj₁ refl
Loc-eq-dec (mk-Loc x x₁) (mk-Loc x₂ x₃) | inj₁ x₄ | inj₂ w =
  inj₂ λ { _≡_.refl → w refl }

Bool-eq-dec : ∀ (x y : Bool) → (x ≡ y) ⊎ (x ≢ y)
Bool-eq-dec false false = inj₁ refl
Bool-eq-dec false true = inj₂ (λ ())
Bool-eq-dec true false = inj₂ (λ ())
Bool-eq-dec true true = inj₁ refl

ℤ-eq-dec : ∀ (x y : ℤ) → (x ≡ y) ⊎ (x ≢ y)
ℤ-eq-dec (+_ n) (+_ n₁) with ℕ-eq-dec n n₁
... | inj₁ refl = inj₁ refl
... | inj₂ y = inj₂ λ { _≡_.refl → y refl }
ℤ-eq-dec (+_ n) (-[1+_] n₁) = inj₂ (λ ())
ℤ-eq-dec (-[1+_] n) (+_ n₁) = inj₂ (λ ())
ℤ-eq-dec (-[1+_] n) (-[1+_] n₁) with ℕ-eq-dec n n₁
... | inj₁ refl = inj₁ refl
... | inj₂ y = inj₂ λ { _≡_.refl → y refl }

truncate : ∀ {ℓ} {A : Set ℓ} {x y : A} → (x ≡ y) ⊎ (x ≢ y) → Bool
truncate (inj₁ x) = true
truncate (inj₂ y) = false

eval : ∀ {C} {Γ : Type-Context C} (store : Store Γ) {α} → (e : SSL-Expr Γ ε α) →
  ∃[ v ] (SSL-Expr-Val-⇓ Γ ε store e v)
eval store (V x) = store-lookup store x , SSL-Expr-Val-⇓-V
eval store (Exists-V ())
eval store (Lit x) = x , SSL-Expr-Val-⇓-Lit
eval store (Add e e₁) with eval store e | eval store e₁
... | Val-Int x , prf-x | Val-Int y , prf-y = Val-Int (x + y) , SSL-Expr-Val-⇓-Add prf-x prf-y
eval store (Loc-Ix e i) with eval store e
... | Val-Loc loc , prf-loc = Val-Loc (Loc-incr loc i) , SSL-Expr-Val-⇓-Loc-Ix prf-loc
eval store (Sub e e₁) with eval store e | eval store e₁
... | Val-Int x , prf-x | Val-Int y , prf-y = Val-Int (x - y) , SSL-Expr-Val-⇓-Sub prf-x prf-y
eval store (And e e₁) with eval store e | eval store e₁
... | Val-Bool x , prf-x | Val-Bool y , prf-y = Val-Bool (x ∧ y) , SSL-Expr-Val-⇓-And prf-x prf-y
eval store (Not e) with eval store e
eval store (Not e) | Val-Bool x , prf-x = Val-Bool (not x) , SSL-Expr-Val-⇓-Not prf-x
eval store (Equal e e₁) with eval store e | eval store e₁
eval store (Equal e e₁) | Val-Loc x , prf-x | Val-Loc x₁ , prf-y with Loc-eq-dec x x₁
eval store (Equal e e₁) | Val-Loc x , prf-x | Val-Loc x₁ , prf-y | inj₁ refl = Val-Bool true , SSL-Expr-Val-⇓-Equal-true prf-x prf-y refl
eval store (Equal e e₁) | Val-Loc x , prf-x | Val-Loc x₁ , prf-y | inj₂ w =
  Val-Bool false , SSL-Expr-Val-⇓-Equal-false prf-x prf-y λ { _≡_.refl → w refl }

eval store (Equal e e₁) | Val-Int x , prf-x | Val-Int x₁ , prf-y with ℤ-eq-dec x x₁
eval store (Equal e e₁) | Val-Int x , prf-x | Val-Int x₁ , prf-y | inj₁ refl = Val-Bool true , SSL-Expr-Val-⇓-Equal-true prf-x prf-y refl
eval store (Equal e e₁) | Val-Int x , prf-x | Val-Int x₁ , prf-y | inj₂ w =
  Val-Bool false , SSL-Expr-Val-⇓-Equal-false prf-x prf-y λ { _≡_.refl → w refl }

eval store (Equal e e₁) | Val-Bool x , prf-x | Val-Bool x₁ , prf-y with Bool-eq-dec x x₁
eval store (Equal e e₁) | Val-Bool x , prf-x | Val-Bool x₁ , prf-y | inj₁ refl = Val-Bool true , SSL-Expr-Val-⇓-Equal-true prf-x prf-y refl
eval store (Equal e e₁) | Val-Bool x , prf-x | Val-Bool x₁ , prf-y | inj₂ w =
  Val-Bool false , SSL-Expr-Val-⇓-Equal-false prf-x prf-y λ { _≡_.refl → w refl }


Satisfies-Expr₀ : ∀ {C : SSL-Context} {Γ : Type-Context C} (s : Store Γ) → (e : SSL-Expr Γ ε Bool-Type) → Set
Satisfies-Expr₀ s (V x) with store-lookup s x
... | Val-Bool true = ⊤
... | Val-Bool false = ⊥
Satisfies-Expr₀ s (Lit (Val-Bool true)) = ⊤
Satisfies-Expr₀ s (Lit (Val-Bool false)) = ⊥
Satisfies-Expr₀ s (And x y) = (Satisfies-Expr₀ s x) × (Satisfies-Expr₀ s y)
Satisfies-Expr₀ s (Not x) = ¬ (Satisfies-Expr₀ s x)
Satisfies-Expr₀ s (Equal x y) with eval s x | eval s y
... | a , _ | b , _ = a ≡ b

Satisfies-Expr : ∀ {C : SSL-Context} {E : Exist-Context} {Γ : Type-Context C} {Δ : E-Type-Context E} (s : Store Γ) → (e : SSL-Expr Γ Δ Bool-Type) → Set
Satisfies-Expr {_} {Exist-Z} {_} {ε} s e = Satisfies-Expr₀ s e
Satisfies-Expr {_} {(Exist-S _)} {_} {Δ₀ ,, x} s e = ∃[ v ] Satisfies-Expr s (E-subst-1 e v)


-- See https://types.pl/web/@pigworker/109429538158539127
data _∘_==_ : Heap → Heap → Heap → Set where
  mk-∘ : ∀ h h′ h′′ →
    Disjoint h h′ →
    h′′ ≡S (h ++ h′) →
    h ∘ h′ == h′′

Ind-Pred-Env : ∀ {C E} → Type-Context C → E-Type-Context E → Set
Ind-Pred-Env Γ Δ = (n : Pred-Name) → Ind-Pred Γ Δ n

Ind-Pred-Denotation : ∀ {C} → Type-Context C → Set₁
Ind-Pred-Denotation Γ = Heap → Val-Vec Γ ε Γ → Set

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
    env p-name h (Val-Vec-any-Δ args-vals) →
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
φ {C} {E} {Γ} {Δ} store rules env P H vec =
  ∃[ F ] (Satisfies-Assertion₀ {_} {E} store H env F × (record { name = P ; assertion = F } ∈ rules))

_⊆_ : ∀ {ℓ m} {A : Set ℓ} (P Q : A → Set m) → Set (ℓ Agda.Primitive.⊔ m)
_⊆_ P Q = ∀ a → P a → Q a

_⊆₂_ : ∀ {ℓ m} {A B : Set ℓ} (P Q : A → B → Set m) → Set (ℓ Agda.Primitive.⊔ m)
_⊆₂_ P Q = ∀ a b → P a b → Q a b

_≤′_ : ∀ {C} {Γ : Type-Context C} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Set
_≤′_ X X′ = ∀ P → X P ⊆₂ X′ P

_⊔_ : ∀ {C} {Γ : Type-Context C} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
_⊔_ {Γ} env-1 env-2 = λ n x y → env-1 n x y ⊎ env-2 n x y

_⊓_ : ∀ {C} {Γ : Type-Context C} → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ → Ind-Pred-Interpret Γ
_⊓_ {Γ} env-1 env-2 = λ n x y → env-1 n x y × env-2 n x y

∅-interpret : ∀ {C} {Γ : Type-Context C} → Ind-Pred-Interpret Γ
∅-interpret = λ n h args → ⊥

∅-interpret-least : ∀ {C} {Γ : Type-Context C} → (X : Ind-Pred-Interpret Γ) → ∅-interpret ≤′ X
∅-interpret-least X P a b ()

Satisfies-Heaplet₀-monotone : ∀ {C} {E} {Γ : Type-Context C} {Δ : E-Type-Context E} {s : Store Γ} {h X X′ A} →
  X ≤′ X′ → Satisfies-Heaplet₀ {C} {E} {Γ} {Δ} s h X A → Satisfies-Heaplet₀ s h X′ A
Satisfies-Heaplet₀-monotone {C} {Γ} {s} {h} {X} {X′} le (Satisfies-Heaplet₀-↦ x x₁ x₂) = Satisfies-Heaplet₀-↦ x x₁ x₂
Satisfies-Heaplet₀-monotone {C} {Γ} {s} {h} {X} {X′} le (Satisfies-Heaplet₀-· {_} {_} {_} {_} {p-name} {_} {args-vals} x x₁ x₂) =
  Satisfies-Heaplet₀-· x (le p-name X′ (Val-Vec-any-Δ args-vals) x₁) x₂


Satisfies-spatial₀-monotone : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-spatial₀ {C} {E} {Γ} {Δ} s h X A → Satisfies-spatial₀ s h X′ A
Satisfies-spatial₀-monotone {C} {E} {Γ} {Δ} {s} {.[]} {X} {X′} {.[]} prf-1 Satisfies-spatial₀-[] = Satisfies-spatial₀-[]
Satisfies-spatial₀-monotone {C} {E} {Γ} {Δ} {s} {h} {X} {X′} {.(_ ∷ _)} prf-1 (Satisfies-spatial₀-∷ x x₁ prf-2) =
  Satisfies-spatial₀-∷ x (Satisfies-Heaplet₀-monotone {C} prf-1 x₁) (Satisfies-spatial₀-monotone prf-1 prf-2)

Satisfies-Assertion₀-monotone : ∀ {C E} {Γ} {Δ} {s : Store Γ} {h X X′ A} → X ≤′ X′ → Satisfies-Assertion₀ {C} {E} {Γ} {Δ} s h X A → Satisfies-Assertion₀ s h X′ A
Satisfies-Assertion₀-monotone {C} {E} {Γ} {s} {h} {X} {X′} {A} prf-1 record { pure-prf = pure-prf ; spatial-prf = spatial-prf } =
  record { pure-prf = pure-prf ; spatial-prf = Satisfies-spatial₀-monotone prf-1 spatial-prf }

φ-monotone : ∀ {C E} {Γ} {Δ} {rules} {X X′ : Ind-Pred-Interpret Γ} {store : Store Γ} → X ≤′ X′ → φ {C} {E} {Γ} {Δ} store rules X ≤′ φ store rules X′
φ-monotone prf-1 P a b (fst , prf-2 , prf-3) =
  fst , Satisfies-Assertion₀-monotone prf-1 prf-2 , prf-3

Ordinal : Set
Ordinal = ℕ

iterate-φ : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} → Store Γ → (rules : List (Ind-Rule Γ Δ)) → Ordinal → Ind-Pred-Interpret Γ
iterate-φ {C} {E} {Γ} store rules zero = ∅-interpret
iterate-φ {C} {E} {Γ} store rules (ℕ.suc α) = φ {C} store rules (iterate-φ {C} store rules α)

⟦_⟧_ : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} → List (Ind-Rule Γ Δ) → Ordinal → Store Γ → Ind-Pred-Interpret Γ
⟦_⟧_ {C} {E} rules α store = iterate-φ {C} store rules α

Label-Valuation : Set
Label-Valuation = Pred-Label → Ordinal

data Satisfies-Heaplet {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} (rules : List (Ind-Rule Γ Δ)) (ρ : Label-Valuation) : ∀ (s : Store Γ) → (h : Heap) → Heaplet Γ Δ → Set where
  Satisfies-Heaplet-↦ : ∀ {α : SSL-Type} {s : Store Γ} {loc-v} {rhs-e : SSL-Expr Γ Δ α} {loc : Loc}  {rhs : Val α} {h : Heap} →
    SSL-Expr-Val-⇓ {C} Γ Δ s (V loc-v) (Val-Loc loc) →
    SSL-Expr-Val-⇓ {C} {E} Γ Δ s rhs-e rhs →
    h ≡ ((α , loc , rhs) ∷ []) →
    Satisfies-Heaplet rules ρ s h (Points-To (V loc-v) rhs-e)

  Satisfies-Heaplet-· : ∀ {s : Store Γ} {h} {labeled-p-name p-name args} {args-vals} →
    let α = Pred-Name-label labeled-p-name
    in
    p-name ≡ get-Pred-Name labeled-p-name →
    (⟦_⟧_ {C} rules (ρ α) s) p-name h (Val-Vec-any-Δ args-vals) →
    SSL-Expr-⇓-Vec Γ Δ s args args-vals →
    Satisfies-Heaplet rules ρ s h (labeled-p-name · args)

data Satisfies-spatial {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} (rules : List (Ind-Rule Γ Δ)) (ρ : Label-Valuation) : ∀ (s : Store Γ) → (h : Heap) → List (Heaplet Γ Δ) → Set where
  Satisfies-spatial-[] : ∀ {s : Store Γ} →
    Satisfies-spatial rules ρ s [] []

  Satisfies-spatial-∷ : ∀ {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} →
    h₁ ∘ h₂ == h →
    Satisfies-Heaplet rules ρ s h₁ Σ₁ →
    Satisfies-spatial rules ρ s h₂ Σ₂ →
    Satisfies-spatial rules ρ s h (Σ₁ ∷ Σ₂)

record Satisfies-Assertion {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} (rules : List (Ind-Rule Γ Δ)) (ρ : Label-Valuation) (s : Store Γ) (h : Heap) (a : Assertion Γ Δ) : Set where
  field
    pure-prf : Satisfies-Expr s (Assertion.pure a)
    spatial-prf : Satisfies-spatial rules ρ s h (Assertion.spatial a)

data Label-Constraint : Set where
  Ord-≤ : Pred-Label → Pred-Label → Label-Constraint
  Ord-< : Pred-Label → Pred-Label → Label-Constraint

data Constraints-hold (ρ : Label-Valuation) : List Label-Constraint → Set where
  Constraints-hold-[] : Constraints-hold ρ []
  Constraints-hold-∷-≤ : ∀ {α β rest} →
    ρ α ≤ ρ β →
    Constraints-hold ρ rest →
    Constraints-hold ρ (Ord-≤ α β ∷ rest)
  Constraints-hold-∷-< : ∀ {α β rest} →
    ρ α < ρ β →
    Constraints-hold ρ rest →
    Constraints-hold ρ (Ord-< α β ∷ rest)

Constrained-Formula : ∀ {C E} → Type-Context C → E-Type-Context E → Set
Constrained-Formula Γ Δ =
  List Pred-Label × List Label-Constraint × Assertion Γ Δ

_==/[_]_ : Label-Valuation → List Pred-Label → Label-Valuation → Set
_==/[_]_ ρ αs ρ′ = ∀ α → α ∈ αs → ρ α ≡ ρ′ α

data Satisfies-Constrained-Formula {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} (rules : List (Ind-Rule Γ Δ)) : Label-Valuation → Store Γ → Heap → Constrained-Formula Γ Δ → Set where
  mk-Satisfies-Constrained-Formula : ∀ {ρ} {s : Store Γ} {h αs constraints asn} →
    Σ Label-Valuation (λ ρ′ →
      ρ′ ==/[ αs ] ρ →
      Constraints-hold ρ′ constraints →
      Satisfies-Assertion {C} {E} {Γ} {Δ} rules ρ′ s h asn) →
    Satisfies-Constrained-Formula rules ρ s h (αs , constraints , asn)

_,_,_⊨[_]_ : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} → Label-Valuation → Store Γ → Heap → List (Ind-Rule Γ Δ) → Constrained-Formula Γ Δ → Set
_,_,_⊨[_]_ ρ s h rules asn = Satisfies-Constrained-Formula rules ρ s h asn

Splitting-List : Heap → Set
Splitting-List h =
  List (∃[ h₁ ] ∃[ h₂ ] (h₁ ∘ h₂ == h))

_∈S_ : ∀ {h} → Heap × Heap → Splitting-List h → Set
_∈S_ {h} (h₁ , h₂) splitting = Any go splitting
  where
    go : (∃[ h₁′ ] ∃[ h₂′ ] (h₁′ ∘ h₂′ == h)) → Set
    go (h₁′ , h₂′ , _) = (h₁′ ≡S h₁) × (h₂′ ≡S h₂)

Universal-Splitting-List : Heap → Set
Universal-Splitting-List h =
  Σ (Splitting-List h) λ xs →
  ∀ h₁ h₂ →
  h₁ ∘ h₂ == h →
  (h₁ , h₂) ∈S xs

Heap-concat-sym : ∀ {h h₁ h₂} →
  h₁ ∘ h₂ == h →
  h₂ ∘ h₁ == h
Heap-concat-sym {.[]} {h₁} {h₂} (mk-∘ .h₁ .h₂ [] x x₁) = mk-∘ h₂ h₁ [] (Disjoint-sym x) (≡S-app-sym h₁ h₂ x₁)
Heap-concat-sym {.(x₂ ∷ h)} {h₁} {h₂} (mk-∘ .h₁ .h₂ (x₂ ∷ h) x x₁) = mk-∘ h₂ h₁ (x₂ ∷ h) (Disjoint-sym x) (≡S-app-sym h₁ h₂ x₁)

≡S-∈ : ∀ {A} {x : A} {xs ys} →
  x ∈ ys →
  xs ≡S ys →
  x ∈ xs
≡S-∈ {_} {x} prf-1 prf-2 = proj₂ prf-2 x prf-1

≡S-∉-left : ∀ {A} {x : A} {xs ys zs} →
  x ∉ zs →
  zs ≡S (xs ++ ys) →
  x ∉ xs
≡S-∉-left {A} {x} {[]} {ys} {zs} prf-1 prf-2 = λ ()
≡S-∉-left {A} {x} {x₁ ∷ xs} {ys} {zs} prf-1 prf-2 = λ x₂ →
  let
    z = ∈-app-left ys x₂
    w = ≡S-∈ z prf-2
  in
  prf-1 w

-- Heap-to-app : ∀ {h h₁ h₂ : Heap} {dom-h dom-h₁ dom-h₂} →
--   Dom h dom-h →
--   Dom h₁ dom-h₁ →
--   Dom h₂ dom-h₂ →
--   h ≡S (h₁ ++ h₂) →
--   dom-h ≡S (dom-h₁ ++ dom-h₂)
-- Heap-to-app Dom-h Dom-h₁ Dom-h₂ (fst , snd) = (λ x x₁ → {!!}) , {!!}

-- Heap-concat-∉ : ∀ {loc h h₁ h₂ dom-h dom-h₁ dom-h₂} →
--   Dom h dom-h →
--   Dom h₁ dom-h₁ →
--   Dom h₂ dom-h₂ →
--   loc ∉ dom-h →
--   h₁ ∘ h₂ == h →
--   (loc ∉ dom-h₁) × (loc ∉ dom-h₂)
-- Heap-concat-∉ {loc} {h} {h₁} {h₂} {dom-h} {dom-h₁} {dom-h₂} Dom-h Dom-h₁ Dom-h₂ prf-1 (mk-∘ .h₁ .h₂ .h x x₁) =
--   (λ x → ≡S-∉-left prf-1 (Heap-to-app Dom-h Dom-h₁ Dom-h₂ x₁) x) ,
--   λ x₂ → ≡S-∉-left prf-1 (Heap-to-app Dom-h Dom-h₂ Dom-h₁ (≡S-app-sym h₁ h₂ x₁)) x₂

-- Disjoint-extend : ∀ {α loc i h₁ h₂ h dom-h} →
--   Dom h dom-h →
--   loc ∉ dom-h →
--   Disjoint h₁ h₂ →

-- Heap-concat-cons : ∀ {α loc i h h₁ h₂ dom-h} →
--   Dom h dom-h →
--   loc ∉ dom-h →
--   h₁ ∘ h₂ == h →
--   ((α , loc , i) ∷ h₁) ∘ h₂ == ((α , loc , i) ∷ h)
-- Heap-concat-cons {α} {loc} {i} {h} {h₁} {h₂} {dom-h} Dom-h prf-1 prf-2 =
--   mk-∘ ((α , loc , i) ∷ h₁) h₂ ((α , loc , i) ∷ h)
--     -- (λ x₂ x₃ → (λ loc₁ x₄ x₅ → proj₂ (x {!!} x₃) loc₁ {!!} x₄) , {!!})
--     (λ x₂ x₃ → (λ loc₁ x₄ x₅ → proj₁ (Heap-concat-∉ {!!} {!!} x₃ {!!} prf-2) {!!}) , {!!})
--     {!!}

-- prepend-splitting-left : ∀ {h α loc i dom-h} → Dom h dom-h → loc ∉ dom-h → Splitting-List h → Splitting-List ((α , loc , i) ∷ h)
-- prepend-splitting-left {h} {α} {loc} {i} {dom-h} Dom-h prf [] = []
-- prepend-splitting-left {h} {α} {loc} {i} {dom-h} Dom-h prf ((fst , fst₁ , snd) ∷ s) =
--   (((α , loc , i) ∷ fst)
--    , fst₁
--    , {!!}
--   ) ∷ prepend-splitting-left Dom-h prf s


prepend-splitting : ∀ {h x} → Splitting-List h → Splitting-List (x ∷ h)
prepend-splitting {h} {x} [] = []
prepend-splitting {h} {x} ((fst , fst₁ , snd) ∷ s) = prepend-splitting s

-- heap-splittings : (h : Heap) → Universal-Splitting-List h
-- heap-splittings [] = ys , go
--   where
--     ys = (([] , [] , mk-∘ [] [] [] Disjoint-left-[] ((λ x x₁ → x₁) , (λ x x₁ → x₁))) ∷ [])
--     go : (h₁ h₂ : Heap) → h₁ ∘ h₂ == [] → (h₁ , h₂) ∈S ys
--     go [] [] (mk-∘ .[] .[] .[] x x₁) = here (((λ x x₁ → x₁) , (λ x x₁ → x₁)) , (λ x x₁ → x₁) , (λ x x₁ → x₁))
--     go [] (x₂ ∷ h₂) (mk-∘ .[] .(x₂ ∷ h₂) .[] x (fst , snd)) with snd x₂ (here refl)
--     ... | ()
--     go (x₂ ∷ h₁) [] (mk-∘ .(x₂ ∷ h₁) .[] .[] x (fst , snd)) with snd x₂ (here refl)
--     ... | ()
--     go (x₂ ∷ h₁) (x₃ ∷ h₂) (mk-∘ .(x₂ ∷ h₁) .(x₃ ∷ h₂) .[] x (fst , snd)) with snd x₂ (here refl)
--     ... | ()

-- heap-splittings (x ∷ xs) with heap-splittings xs
-- ... | fst , snd =
--   let
--     ys = {!!}
--   in
--   [] , {!!}

-- h₁ ∘ h₂ == h →

  -- Satisfies-spatial-∷ : ∀ {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} →
  --   h₁ ∘ h₂ == h →
  --   Satisfies-Heaplet rules ρ s h₁ Σ₁ →
  --   Satisfies-spatial rules ρ s h₂ Σ₂ →
  --   Satisfies-spatial rules ρ s h (Σ₁ ∷ Σ₂)

  -- Satisfies-Heaplet-↦ : ∀ {α : SSL-Type} {s : Store Γ} {loc-v} {rhs-e : SSL-Expr Γ Δ α} {loc : Loc}  {rhs : Val α} {h : Heap} →
  --   SSL-Expr-Val-⇓ {C} Γ Δ s (V loc-v) (Val-Loc loc) →
  --   SSL-Expr-Val-⇓ {C} {E} Γ Δ s rhs-e rhs →
  --   h ≡ ((α , loc , rhs) ∷ []) →
  --   Satisfies-Heaplet rules ρ s h (Points-To (V loc-v) rhs-e)

-- decide-Satisfies-Heaplet : ∀ {C} {Γ : Type-Context C} {rules ρ} {s : Store Γ} h₁ Σ₁ →
--   (Satisfies-Heaplet {C} {Exist-Z} {Γ} {ε} rules ρ s h₁ Σ₁)
--     ⊎
--   ¬ (Satisfies-Heaplet rules ρ s h₁ Σ₁)
-- decide-Satisfies-Heaplet {_} {_} {rules} {ρ} {s} [] (Points-To lhs x) = inj₂ λ { (Satisfies-Heaplet-↦ prf-1 prf-2 ()) }
-- decide-Satisfies-Heaplet {_} {_} {rules} {ρ} {s} (x₁ ∷ h₁) (Points-To lhs x) = {!!}
-- -- ... | fst , snd = {!!}
-- decide-Satisfies-Heaplet {_} {_} {rules} {ρ} {s} h₁ (n · x) = {!!}


-- decide-Satisfies-spatial-∷ : ∀ {C} {Γ : Type-Context C}  {ρ} {rules} {s : Store Γ} {h h₁ h₂} {Σ₁ Σ₂} →
--     h₁ ∘ h₂ == h →
--     -- Satisfies-Heaplet rules ρ s h₁ Σ₁ →
--     -- Satisfies-spatial rules ρ s h₂ Σ₂ →
--     (Satisfies-spatial {C} {_} {Γ} {Δ} rules ρ s h (Σ₁ ∷ Σ₂))
--       ⊎
--     ¬ (Satisfies-spatial rules ρ s h (Σ₁ ∷ Σ₂))
-- decide-Satisfies-spatial-∷ = {!!}

-- decide-models-split : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} →
--   (ρ : Label-Valuation) → (store : Store Γ) → (h : Heap) → (rules : List (Ind-Rule Γ Δ)) →
--   (formula : Constrained-Formula Γ Δ) →
--   (h-spl : Universal-Splitting-List h) →
--   (ρ , store , h ⊨[ rules ] formula)
--     ⊎
--   ¬ (ρ , store , h ⊨[ rules ] formula)
-- decide-models-split = {!!}


-- decide-models : ∀ {C E} {Γ : Type-Context C} {Δ : E-Type-Context E} →
--   (ρ : Label-Valuation) → (store : Store Γ) → (h : Heap) → (rules : List (Ind-Rule Γ Δ)) →
--   (formula : Constrained-Formula Γ Δ) →
--   (ρ , store , h ⊨[ rules ] formula)
--     ⊎
--   ¬ (ρ , store , h ⊨[ rules ] formula)
-- decide-models ρ store h rules (fst , snd) = {!!}
