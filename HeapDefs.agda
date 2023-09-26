open import Data.List
open import Data.Nat
open import Data.Integer
open import Data.Bool
open import Data.Product
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Data.Sum
open import Data.Empty
open import Function

module HeapDefs
  (Loc-Name : Set)
  -- (Loc-Name-eq-dec : ∀ (a b : Loc-Name) → (a ≡ b) ⊎ (a ≢ b))
  where

data Loc : Set where
  Null : Loc
  mk-Loc : Loc-Name → ℕ → Loc

get-Loc-Name : (a : Loc) → a ≢ Null → Loc-Name
get-Loc-Name (mk-Loc name _) prf = name
get-Loc-Name Null prf = ⊥-elim (prf refl)


-- Loc-eq-dec : ∀ (a b : Loc) → (a ≡ b) ⊎ (a ≢ b)
-- Loc-eq-dec Null Null = inj₁ refl
-- Loc-eq-dec Null (mk-Loc x x₁) = inj₂ (λ ())
-- Loc-eq-dec (mk-Loc x x₁) Null = inj₂ (λ ())
-- Loc-eq-dec (mk-Loc x y) (mk-Loc x′ y′) with y Data.Nat.≟ y′
-- Loc-eq-dec (mk-Loc x y) (mk-Loc x′ y′) | no ¬p = inj₂ λ { _≡_.refl → ¬p refl }
-- Loc-eq-dec (mk-Loc x y) (mk-Loc x′ y′) | yes refl with Loc-Name-eq-dec x x′
-- Loc-eq-dec (mk-Loc x y) (mk-Loc x′ y) | yes refl | inj₁ refl = inj₁ refl
-- Loc-eq-dec (mk-Loc x y) (mk-Loc x′ y) | yes refl | inj₂ y₁ = inj₂ λ { _≡_.refl → y₁ refl }

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
Heap = List (∃[ α ] ∃[ loc ] (loc ≢ Null) × Val α)

-- _[_↦_] : ∀ {α} → Heap → Loc → Val α → Heap
-- _[_↦_] {α} [] loc val = (α , loc , val) ∷ []
-- _[_↦_] {α} ((β , loc′ , val′) ∷ h) loc val with Loc-eq-dec loc′ loc
-- ... | inj₁ refl = (α , loc , val) ∷ h
-- ... | inj₂ y = h [ loc ↦ val ]

-- -- Heap update
data _[_↦_]==_ : ∀ {α} → Heap → Loc → Val α → Heap → Set where
  Heap-update-[] : ∀ {α loc prf val} →
    [] [ loc ↦ val ]== ((α , loc , prf , val) ∷ [])

  Heap-update-here : ∀ {α β loc prf val val′ rest} →
    ((β , loc , val′) ∷ rest) [ loc ↦ val ]== ((α , loc , prf , val) ∷ rest)

  Heap-update-there : ∀ {α β loc loc′} {val : Val α} {val′ rest rest′} →
    rest [ loc ↦ val ]== rest′ →
    ((β , loc′ , val′) ∷ rest) [ loc ↦ val ]== ((β , loc′ , val′) ∷ rest′)

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

-- Dom-locs : ∀ {loc-names h} → Dom h loc-names → List (∃[ loc ] loc ≢ Null)
-- Dom-locs Dom-[] = []
-- Dom-locs (Dom-∷ dom) = {!!}

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

Dom-non-null : ∀ {h locs} →
  Dom h locs →
  ∀ {loc} →
  loc ∈ locs →
  loc ≢ Null
Dom-non-null (Dom-∷ {_} {_} {prf , _} dom) (here refl) = prf
Dom-non-null (Dom-∷ dom) (there prf) = Dom-non-null dom prf

get-Loc-Names : ∀ {locs} →
  (∀ {loc} → loc ∈ locs → loc ≢ Null) →
  List Loc-Name
get-Loc-Names {[]} f = []
get-Loc-Names {x ∷ locs} f = get-Loc-Name x (f (here refl)) ∷ get-Loc-Names (λ {loc} prf → f (there prf))

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

_⊆_ : ∀ {A} → List A → List A → Set
_⊆_ xs ys = ∀ x → x ∈ xs → x ∈ ys

_≡S_ : ∀ {A} → List A → List A → Set
_≡S_ xs ys = (∀ x → x ∈ xs → x ∈ ys) × (∀ y → y ∈ ys → y ∈ xs)

≡S-sym : ∀ {A} {xs ys : List A} → xs ≡S ys → ys ≡S xs
≡S-sym {_} {xs} {ys} (fst , snd) = snd , fst

≡S-app-sym : ∀ {A} {zs : List A} → (xs ys : List A) → zs ≡S (xs ++ ys) → zs ≡S (ys ++ xs)
≡S-app-sym {A} {zs} xs ys (p , q) =
  (λ x x₁ → ∈-app-sym {_} {x} {xs} {ys} (p x x₁)) , λ y x → q y (∈-app-sym {_} {y} {ys} {xs} x)

≡S-∈-subst : ∀ {A} {x} {xs ys : List A} →
  x ∈ xs →
  xs ≡S ys →
  x ∈ ys
≡S-∈-subst {_} {x} {xs} {ys} prf-1 (fst , snd) = fst x (snd x (fst x prf-1))

∈-app : ∀ {A : Set} {x} {xs ys : List A} →
  x ∈ (xs ++ ys) →
  (x ∈ xs) ⊎ (x ∈ ys)
∈-app {_} {x} {[]} {ys} prf = inj₂ prf
∈-app {_} {x} {x₁ ∷ xs} {ys} (here px) = inj₁ (here px)
∈-app {_} {x} {x₁ ∷ xs} {ys} (there prf) with ∈-app {_} {x} {xs} {ys} prf
... | inj₁ x₂ = inj₁ (there x₂)
... | inj₂ y = inj₂ y

app-∈ : ∀ {A : Set} {x} {xs ys : List A} →
  (x ∈ xs) ⊎ (x ∈ ys) →
  x ∈ (xs ++ ys)
app-∈ {_} {x} {x₁ ∷ xs} {ys} (inj₁ (here px)) = here px
app-∈ {_} {x} {x₁ ∷ xs} {ys} (inj₁ (there prf)) = there (app-∈ (inj₁ prf))
app-∈ {_} {x} {[]} {.(x ∷ _)} (inj₂ (here refl)) = here refl
app-∈ {_} {x} {x₁ ∷ xs} {.(x ∷ _)} (inj₂ (here refl)) = there (app-∈ (inj₂ (here refl)))
app-∈ {_} {x} {[]} {.(_ ∷ _)} (inj₂ (there prf)) = there prf
app-∈ {_} {x} {x₁ ∷ xs} {(y ∷ ys)} (inj₂ (there prf)) = there (app-∈ (inj₂ (there prf)))

≡S-∈-app : ∀ {A : Set} {x} {xs ys xs++ys : List A} →
  xs++ys ≡S (xs ++ ys) →
  x ∈ (xs++ys) →
  (x ∈ xs) ⊎ (x ∈ ys)
≡S-∈-app {_} {x} {xs} {ys} {xs++ys} (fst , snd) prf-2 = ∈-app (fst x prf-2)

≡S-app-∈ : ∀ {A : Set} {x} {xs ys xs++ys : List A} →
  xs++ys ≡S (xs ++ ys) →
  (x ∈ xs) ⊎ (x ∈ ys) →
  x ∈ (xs++ys)
≡S-app-∈ {_} {x} {xs} {ys} {xs++ys} (fst , snd) prf-2 = snd x (app-∈ prf-2)

data NonEmpty {A : Set} : List A → Set where
  is-NonEmpty : ∀ {x xs} → NonEmpty (x ∷ xs)

-- From https://types.pl/web/@pigworker/109429538158539127
record Choppable {X : Set}(zs : List X) : Set where
  inductive
  constructor chopMe
  field
    chopEm :
      ∀ {xs ys : List X} → (p : NonEmpty xs)
      → xs ++ ys ≡ zs
      → Choppable {X} ys

-- ≡-++-cons : ∀ {A : Set} {x x′ : A} {xs ys} →
--   x ∷ xs ++ ys ≡ x′ ∷ xs ++ ys →
--   x ≡ x′
-- ≡-++-cons {x} {x′} {.x′} refl = refl

-- NonEmpty-++-lemma : ∀ {A : Set} {x xs ys ys′} →
--   NonEmpty xs →
--   xs ++ ys ≡ x ∷ ys′ →


module _ where
  open Choppable

  choppable : {X : Set} (zs : List X) → Choppable zs
  chopEm (choppable []) {[]} {[]} () x
  chopEm (choppable []) {[]} {x₁ ∷ ys} () x
  chopEm (choppable []) {x₁ ∷ xs} {[]} _ ()
  chopEm (choppable []) {x₁ ∷ xs} {x₂ ∷ ys} _ ()
  chopEm (choppable (x₁ ∷ zs)) {xs} {[]} _ x = {!!}
  chopEm (choppable (x₁ ∷ zs)) {.x₁ ∷ []} {x₂ ∷ ys} non-empty prf@refl =
    chopEm (choppable (x₁ ∷ x₂ ∷ ys)) (is-NonEmpty {_} {x₁} {[]}) refl
    -- let
    --   q : x₂ ∷ []
    -- in
    -- chopEm (choppable zs) is-NonEmpty {!!}
    -- chopEm (choppable ((ys))) (is-NonEmpty {_} {x₁} {[]}) {!!}
    -- chopMe λ { NonEmpty.is-NonEmpty refl → chopEm (choppable {!!}) {!!} refl }
  chopEm (choppable (x₁ ∷ zs)) {.x₁ ∷ x ∷ xs} {x₂ ∷ ys} non-empty prf@refl =
    chopEm (choppable zs) is-NonEmpty refl

data _∘_==_ : Heap → Heap → Heap → Set where
  mk-∘ : ∀ h h′ h′′ →
    Disjoint h h′ →
    h′′ ≡S (h ++ h′) →
    h ∘ h′ == h′′

Dom-∈ : ∀ {h dom-h} {α loc i} →
  Dom h dom-h →
  (α , loc , i) ∈ h →
  loc ∈ dom-h
Dom-∈ {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {α} {loc} {i} (Dom-∷ Dom-h) (here refl) = here refl
Dom-∈ {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {α} {loc} {i} (Dom-∷ Dom-h) (there prf) = there (Dom-∈ Dom-h prf)

∈-Dom : ∀ {h dom-h} {loc} →
  Dom h dom-h →
  loc ∈ dom-h →
  ∃[ α ] ∃[ i ] (α , loc , i) ∈ h
∈-Dom Dom-[] ()
∈-Dom (Dom-∷ {α} {_} {i} Dom-h) (here refl) = α , i , here refl
∈-Dom (Dom-∷ Dom-h) (there prf) with ∈-Dom Dom-h prf
∈-Dom (Dom-∷ Dom-h) (there prf) | fst , z , snd = fst , z , there snd

Dom-++ : ∀ {h₁ h₂ dom-h₁ dom-h₂} →
  Dom h₁ dom-h₁ →
  Dom h₂ dom-h₂ →
  Dom (h₁ ++ h₂) (dom-h₁ ++ dom-h₂)
Dom-++ {.[]} {.[]} {.[]} {.[]} Dom-[] Dom-[] = Dom-[]
Dom-++ {.[]} {.((_ , _ , _) ∷ _)} {.[]} {.(_ ∷ _)} Dom-[] (Dom-∷ Dom-h₂) = Dom-∷ Dom-h₂
Dom-++ {((α , loc , i) ∷ rest)} {.[]} {(_ ∷ locs)} {.[]} (Dom-∷ Dom-h₁) Dom-[] rewrite (app-[] ((α , loc , i) ∷ rest)) | (app-[] (loc ∷ locs)) = Dom-∷ Dom-h₁
Dom-++ {.((_ , _ , _) ∷ _)} {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {.(_ ∷ _)} (Dom-∷ Dom-h₁) (Dom-∷ Dom-h₂) = Dom-∷ (Dom-++ Dom-h₁ (Dom-∷ Dom-h₂))

Dom-unique-≡S : ∀ {h} {dom-h dom-h′} →
  Dom h dom-h →
  Dom h dom-h′ →
  dom-h ≡S dom-h′
Dom-unique-≡S {.[]} {.[]} {.[]} Dom-[] Dom-[] = (λ x x₁ → x₁) , (λ x x₁ → x₁)
Dom-unique-≡S {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {.(_ ∷ _)} (Dom-∷ Dom-h) (Dom-∷ Dom-h′)
  with Dom-unique-≡S Dom-h Dom-h′
Dom-unique-≡S {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {.(_ ∷ _)} (Dom-∷ Dom-h) (Dom-∷ Dom-h′) | z , w =
  (λ x x₁ →
    case x₁ of
    λ { (here prf) → here prf ; (there prf) → there (z x prf) }) ,

  λ y x →
    case x of
    λ { (here prf) → here prf ; (there prf) → there (w y prf) }

-- Dom-≡S : ∀ {h h₁ h₂} {dom} →
--   h ≡S (h₁ ++ h₂) →
--   Dom (h₁ ++ h₂) dom →
--   Dom h dom
-- Dom-≡S {[]} {h₁} {h₂} {dom} eq D = {!!}
-- Dom-≡S {x ∷ h} {h₁} {h₂} {dom} eq D = {!!}
-- -- Dom-≡S {[]} {h₁} {h₂} {[]} eq D = Dom-[]
-- -- Dom-≡S {[]} {[]} {(x₁ , x , _) ∷ h₂} {x ∷ dom} (fst , snd) (Dom-∷ {α} {loc} {i} D) = ⊥-elim (¬∈[] (snd (x₁ , x , i) (here refl)))
-- -- Dom-≡S {[]} {.(_ , x , _) ∷ h₁} {h₂} {x ∷ dom} (fst , snd) (Dom-∷ {α} {loc} {i} D) = ⊥-elim (¬∈[] (snd (α , x , i) (here refl)))
-- -- Dom-≡S {(fst₁ , fst₂ , snd₁) ∷ h} {[]} {[]} {[]} (fst , snd) Dom-[] = ⊥-elim (¬∈[] (fst (fst₁ , fst₂ , snd₁) (here refl)))
-- -- Dom-≡S {(fst , fst₁ , snd) ∷ h} {[]} {.(_ , x₁ , _) ∷ h₂} {x₁ ∷ dom} prf@(fst₂ , snd₁) (Dom-∷ {α} {loc} {i} D) with snd₁ (α , x₁ , (proj₁ i) , proj₂ i) (here refl)
-- -- Dom-≡S {(fst , fst₁ , snd) ∷ h} {[]} {x₂ ∷ h₂} {x₁ ∷ dom} prf@(fst₂ , snd₁) (Dom-∷ D) | here refl = Dom-∷ (Dom-≡S {!!} D)
-- -- Dom-≡S {(fst , fst₁ , snd) ∷ h} {[]} {x₂ ∷ h₂} {x₁ ∷ dom} prf@(fst₂ , snd₁) (Dom-∷ D) | there z = {!!}
-- -- Dom-≡S {x ∷ h} {x₂ ∷ h₁} {[]} {x₁ ∷ dom} eq D = {!!}
-- -- Dom-≡S {x ∷ h} {x₂ ∷ h₁} {x₃ ∷ h₂} {x₁ ∷ dom} eq D = {!!}

-- ≡S-cons : ∀ {A} {y x} {xs ys : List A} →
--   (x ∷ xs) ≡S (y ∷ ys) →
--   ¬ (xs ≡S (y ∷ ys)) →
--   ¬ ((x ∷ xs) ≡S ys) →
--   xs ≡S ys
-- ≡S-cons = {!!}

∈-induction : ∀ {A} (xs : List A) (P : List A → Set) →
  P [] →
  (∀ x ys → x ∈ xs → P ys → P (x ∷ ys)) →
  P xs
∈-induction {_} [] P P-[] step = P-[]
∈-induction {_} (x ∷ xs) P P-[] step = step x xs (here refl)
                                         (∈-induction xs P P-[] (λ x ys z → step x ys (there z)))

++-induction : ∀ {A} (xs : List A) (P : List A → Set) →
  (∀ ys zs → xs ≡ ys ++ zs → P ys → P zs → P xs) →
  P xs
++-induction xs P step = {!!}

Dom-++-≡S : ∀ {h h₁ h₂ dom-h dom-h₁ dom-h₂} →
  Dom h dom-h →
  Dom h₁ dom-h₁ →
  Dom h₂ dom-h₂ →
  h ≡S (h₁ ++ h₂) →
  dom-h ≡S (dom-h₁ ++ dom-h₂)
Dom-++-≡S {h} {h₁} {h₂} {dom-h} {dom-h₁} {dom-h₂} Dom-h Dom-h₁ Dom-h₂ eq =
  ∈-induction dom-h (λ x → x ⊆ (dom-h₁ ++ dom-h₂)) (λ x ())
    (λ x ys x₁ x₂ x₃ x₄ →
      case x₄ of
      λ { (here refl) → {!!} ; (there prf) → {!!} })
    ,
  {!!}
  -- where
    -- go : List Loc → Set
    -- go = {!!}

-- Dom-++-≡S {h} {h₁} {h₂} {dom-h} {dom-h₁} {dom-h₂} Dom-h Dom-h₁ Dom-h₂ eq@(fst , snd) with Dom-++ Dom-h₁ Dom-h₂
-- Dom-++-≡S {.[]} {h₁} {h₂} {.[]} {dom-h₁} {dom-h₂} Dom-[] Dom-h₁ Dom-h₂ (fst , snd) | z =
--   (λ x ()) ,
--   λ y x →
--     let β , (non-null , val) , prf = ∈-Dom z x
--     in
--     ⊥-elim (¬∈[] (snd (β , (y , non-null , val)) prf))
-- Dom-++-≡S {((α , loc , i) ∷ _)} {.[]} {.[]} {.(_ ∷ _)} {.[]} {.[]} (Dom-∷ Dom-h) Dom-[] Dom-h₂ (fst , snd) | Dom-[] =
--   (λ x x₁ →
--     ⊥-elim (¬∈[] (fst (α , (loc , i)) (here refl)))) ,
--   λ y ()

-- Dom-++-≡S {.((_ , _ , _) ∷ _)} {.[]} {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {.[]} {.(_ ∷ _)} (Dom-∷ Dom-h) Dom-[] (Dom-∷ Dom-h₂) eq@(fst , snd) | Dom-∷ z =
--   let
--     w = Dom-++-≡S Dom-h Dom-[] Dom-h₂ {!!}
--   in
--   {!!}
-- Dom-++-≡S {.((_ , _ , _) ∷ _)} {.((_ , _ , _) ∷ _)} {h₂} {.(_ ∷ _)} {.(_ ∷ _)} {dom-h₂} (Dom-∷ Dom-h) (Dom-∷ Dom-h₁) Dom-h₂ (fst , snd) | z = {!!}
-- -- let
--   --   z = Dom-++ Dom-h₁ Dom-h₂
--   -- in
--   -- {!!}
--   -- -- Dom-unique-≡S Dom-h (Dom-≡S {h} {h₁} {h₂} eq z)

∘-Dom : ∀ {h h₁ h₂}
          {dom-h dom-h₁ dom-h₂} →
  Dom h dom-h →
  Dom h₁ dom-h₁ →
  Dom h₂ dom-h₂ →
  h₁ ∘ h₂ == h →
  dom-h ≡S (dom-h₁ ++ dom-h₂)
∘-Dom {h} {h₁} {h₂} {dom-h} {dom-h₁} {dom-h₂} Dom-h Dom-h₁ Dom-h₂ (mk-∘ .h₁ .h₂ .h x prf) =
  let
    prf′ = ≡S-sym prf
    prf-1 , prf-2 = prf
    dom-app = Dom-++ Dom-h₁ Dom-h₂
  in
  (λ y z →
    let
      w = ≡S-∈-subst z (Dom-++-≡S Dom-h Dom-h₁ Dom-h₂ prf)
    in w) ,
  λ y z →
    ≡S-app-∈ (Dom-++-≡S Dom-h Dom-h₁ Dom-h₂ prf) (∈-app z)

-- ∘-Dom {.[]} {.[]} {.[]} {.[]} {.[]} {.[]} Dom-[] Dom-[] Dom-[] prf = (λ x x₁ → x₁) , (λ x x₁ → x₁)
-- ∘-Dom {.[]} {.[]} {.((_ , _ , _) ∷ _)} {.[]} {.[]} {.(_ ∷ _)} Dom-[] Dom-[] (Dom-∷ {α} {loc} {i} Dom-h₂) (mk-∘ .[] .((_ , _ , _) ∷ _) .[] x (fst , snd)) =
--   let
--     z = snd (α , loc , i) (here refl)
--   in
--   ⊥-elim (¬∈[] z)
-- ∘-Dom {.[]} {.((_ , _ , _) ∷ _)} {.[]} {.[]} {.(_ ∷ _)} {.[]} Dom-[] (Dom-∷ {α} {loc} {i} Dom-h₁) Dom-[] (mk-∘ .((_ , _ , _) ∷ _) .[] .[] x (fst , snd)) =
--   let
--     z = snd (α , loc , i) (here refl)
--   in
--   ⊥-elim (¬∈[] z)

-- ∘-Dom {.[]} {.((_ , _ , _) ∷ _)} {.((_ , _ , _) ∷ _)} {.[]} {.(_ ∷ _)} {.(_ ∷ _)} Dom-[] (Dom-∷ {α} {loc} {i} Dom-h₁) (Dom-∷ Dom-h₂) (mk-∘ .((_ , _ , _) ∷ _) .((_ , _ , _) ∷ _) .[] x (fst , snd)) =
--   let
--     z = snd (α , loc , i) (here refl)
--   in
--   ⊥-elim (¬∈[] z)

-- ∘-Dom {.((_ , _ , _) ∷ _)} {h₁} {h₂} {.(_ ∷ _)} {dom-h₁} {dom-h₂} (Dom-∷ Dom-h) Dom-h₁ Dom-h₂ (mk-∘ .h₁ .h₂ ((α , loc , i) ∷ _) x (fst , snd)) =
--   let
--     z = fst {!!} {!!}
--     dom-app = Dom-++ Dom-h₁ Dom-h₂
--   in
--   (λ x₁ x₂ → {!!}) ,
--   λ y x₁ →
--     -- Dom-∈ (Dom-∷ Dom-h) {!!}
--     Dom-∈ (Dom-∷ Dom-h) (snd (α , y , Dom-non-null dom-app x₁ , proj₂ i) (fst (α , y , Dom-non-null (Dom-++ Dom-h₁ Dom-h₂) x₁ , proj₂ i) {!!}))
