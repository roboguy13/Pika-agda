open import Data.List
open import Data.Nat
open import Data.Integer
open import Data.Bool
open import Data.Product
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

module HeapDefs
  (Loc-Name)
  where

data Loc : Set where
  Null : Loc
  mk-Loc : Loc-Name → ℕ → Loc

data SSL-Type : Set where
  Loc-Type : SSL-Type
  Int-Type : SSL-Type
  Bool-Type : SSL-Type
  -- Exists-Type : SSL-Type → SSL-Type

data Val : SSL-Type → Set where
  Val-Loc : Loc → Val Loc-Type
  Val-Int : ℤ → Val Int-Type
  Val-Bool : Bool → Val Bool-Type

Heap : Set
-- Heap = Loc → Maybe ℤ
Heap = List (∃[ α ] (Loc × Val α))

data Dom : Heap → List Loc → Set where
  Dom-[] : Dom [] []
  Dom-∷ : ∀ {α loc i rest locs} →
    Dom rest locs →
    Dom ((α , loc , i) ∷ rest) (loc ∷ locs)

Dom-exists : ∀ {h} →
  ∃[ locs ] Dom h locs
Dom-exists {[]} = [] , Dom-[]
Dom-exists {(α , loc , i) ∷ h} with Dom-exists {h}
... | locs , prf = loc ∷ locs , Dom-∷ prf

Dom-cons : ∀ {h locs α x i} →
  Dom h locs →
  Dom ((α , x , i) ∷ h) (x ∷ locs)
Dom-cons {.[]} {.[]} {α} {x} {i} Dom-[] = Dom-∷ Dom-[]
Dom-cons {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {α} {x} {i} (Dom-∷ prf) = Dom-∷ (Dom-cons prf)

_∈_ : ∀ {A} → A → List A → Set
x ∈ xs = Any (_≡ x) xs

_∉_ : ∀ {A} → A → List A → Set
x ∉ xs = ¬ (x ∈ xs)

¬∈[] : ∀ {A} {x : A} → ¬ (x ∈ [])
¬∈[] ()

∷∈ : ∀ {A} {x y : A} {xs} → x ∈ xs → x ∈ (y ∷ xs)
∷∈ {A} {x} {y} {xs} prf = there prf

app-∷ : ∀ {A : Set} {x : A} {xs ys} → (x ∷ xs ++ ys) ≡ x ∷ (xs ++ ys)
app-∷ {A} {x} {xs} {ys} = refl

app-[] : ∀ {ℓ} {A : Set ℓ} (xs : List A) → xs ++ [] ≡ xs
app-[] {_} {_} [] = refl
app-[] {_} {_} (x ∷ xs) rewrite app-[] xs = refl

∈-app-left : ∀ {A} {x : A} {xs} (ys : List A) → x ∈ xs → x ∈ (xs ++ ys)
∈-app-left {A} {x} {xs} [] prf rewrite app-[] xs = prf
∈-app-left {A} {x} {.(_ ∷ _)} (x₁ ∷ ys) (here px) = here px
∈-app-left {A} {x} {.(_ ∷ _)} (x₁ ∷ ys) (there prf) = there (∈-app-left {_} {_} {_} (x₁ ∷ ys) prf)

∈-cons-app : ∀ {A} {x z : A} {xs ys} → x ∈ (xs ++ ys) → x ∈ (xs ++ z ∷ ys)
∈-cons-app {_} {x} {z} {[]} {ys} prf = there prf
∈-cons-app {_} {x} {z} {x₁ ∷ xs} {ys} (here px) = here px
∈-cons-app {_} {x} {z} {x₁ ∷ xs} {ys} (there prf) = there (∈-cons-app prf)

∈-app-sym : ∀ {A} {x : A} {xs ys} → x ∈ (xs ++ ys) → x ∈ (ys ++ xs)
∈-app-sym {A} {x} {[]} {ys} prf rewrite app-[] ys = prf
∈-app-sym {A} {x} {x₁ ∷ xs} {[]} prf rewrite app-[] (x₁ ∷ xs) = prf
∈-app-sym {A} {x} {x₁ ∷ xs} {x₂ ∷ ys} (here prf) = ∷∈ (∈-app-sym {_} {_} {x₁ ∷ xs} {ys} (here prf))
∈-app-sym {A} {x} {x₁ ∷ xs} {x₂ ∷ ys} (there prf) with ∷∈ {_} {x} {x₂} (∈-app-sym {_} {x} {xs} {x₂ ∷ ys} (prf))
... | here px = here px
... | there (here px) = here px
... | there (there z) = there (∈-cons-app z)

Disjoint : Heap → Heap → Set
Disjoint a b =
  ∀ {dom-a dom-b} →
  Dom a dom-a →
  Dom b dom-b →
  (∀ loc → loc ∈ dom-a → loc ∉ dom-b)
    ×
  (∀ loc → loc ∈ dom-b → loc ∉ dom-a)

Disjoint-left-[] : ∀ {h} → Disjoint [] h
Disjoint-left-[] {h} Dom-[] x₁ = (λ loc x₂ x₃ → ¬∈[] x₂) , λ loc x x₂ → ¬∈[] x₂

Disjoint-left-cons : ∀ {x a b} → Disjoint (x ∷ a) b → Disjoint a b
Disjoint-left-cons {x} {a} {b} prf dom-a dom-b =
  let
    z , w = prf (Dom-cons dom-a) dom-b
  in
  (λ loc x₁ x₂ → z loc (there x₁) x₂) ,
  λ loc x₁ x₂ → z loc (there x₂) x₁

Disjoint-sym : ∀ {a b} → Disjoint a b → Disjoint b a
Disjoint-sym {a} {b} prf Dom-b Dom-a =
  let
    z , w = prf Dom-a Dom-b
  in
  (λ loc x x₁ → proj₁ (prf Dom-a Dom-b) loc x₁ x) , (λ loc x x₁ → proj₁ (prf Dom-a Dom-b) loc x x₁)

_≡S_ : ∀ {A} → List A → List A → Set
_≡S_ xs ys = (∀ x → x ∈ xs → x ∈ ys) × (∀ y → y ∈ ys → y ∈ xs)

≡S-app-sym : ∀ {A} {zs : List A} → (xs ys : List A) → zs ≡S (xs ++ ys) → zs ≡S (ys ++ xs)
≡S-app-sym {A} {zs} xs ys (p , q) =
  (λ x x₁ → ∈-app-sym {_} {x} {xs} {ys} (p x x₁)) , λ y x → q y (∈-app-sym {_} {y} {ys} {xs} x)
