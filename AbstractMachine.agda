open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Bool
open import Data.Integer
open import Data.Product
open import Function using (case_of_)
open import Data.List.Relation.Unary.Any

module AbstractMachine
  (Pred-Name : Set)
  (Pred-Label : Set)
  (Loc-Name : Set)
  (Loc-Name-eq-dec : ∀ (x y : Loc-Name) → (x ≡ y) ⊎ (x ≢ y))
  (Loc-Name-fresh : (xs : List Loc-Name) → ∃[ loc ] ∀ x → Any (_≡ x) xs → loc ≢ x)

  (Layout-Name : Set)
  (Constr-Name : Set)
  (Adt-Name : Set)
  (Fn-Name : Set)

  where

open import Expr
  (Pred-Name)
  (Pred-Label)
  (Loc-Name)
  (Layout-Name)
  (Constr-Name)
  (Adt-Name)
  (Fn-Name)


open import SSL (Pred-Name) (Pred-Label) (Loc-Name)
open import HeapDefs (Loc-Name) renaming (Val to SSL-Val)
open import SSLSatisfies (Pred-Name) (Pred-Label) (Loc-Name) (Loc-Name-eq-dec)

open Ambient-Context

data _#_ : Loc → Heap → Set where
  Fresh-Heap-Loc : ∀ {loc H dom-H} →
    Dom H dom-H →
    loc ∉ dom-H →
    loc ≢ Null →
    loc # H

fresh-name-gives-fresh-loc : ∀ {h} {dom-h} {new-loc-name} →
  (Dom-h : Dom h dom-h) →
  (∀ loc-name →
    Any (_≡ loc-name) (get-Loc-Names (Dom-non-null Dom-h)) → new-loc-name ≢ loc-name) →
  ∀ {i} →
  mk-Loc new-loc-name i ∉ dom-h
fresh-name-gives-fresh-loc {.[]} {.[]} {new-loc-name} Dom-[] f {i} = λ ()
fresh-name-gives-fresh-loc {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {new-loc-name} (Dom-∷ Dom-h) f {i} (here refl) = f new-loc-name (here refl) refl
fresh-name-gives-fresh-loc {.((_ , _ , _) ∷ _)} {.(_ ∷ _)} {new-loc-name} (Dom-∷ Dom-h) f {i} (there prf) =
  fresh-name-gives-fresh-loc Dom-h (λ loc-name₁ x x₁ → f loc-name₁ (there x) x₁) {i} prf

gen-fresh : (h : Heap) → ∃[ loc ] loc # h
gen-fresh h =
  let
    locs , dom-h = Dom-exists {h}
    fresh-loc-name , prf = Loc-Name-fresh (get-Loc-Names (Dom-non-null dom-h))

    fresh-loc = mk-Loc fresh-loc-name 0
  in
  fresh-loc , Fresh-Heap-Loc dom-h (fresh-name-gives-fresh-loc {h} {locs} {fresh-loc-name} dom-h prf) λ ()

-- Evaluated layout body acting on a Heap
data Val-Layout-Body-Act :
    Val-Layout-Body →
    Heap →
    Heap →
    Set where

  Val-Layout-Body-Act-[] : ∀ {h} →
    Val-Layout-Body-Act [] h h

  Val-Layout-Body-Act-Points-To : ∀ {α : SSL-Type}
                                {h h′ h′′ : Heap} {rest : Val-Layout-Body}
                                {lhs : Loc} {rhs : SSL-Val α} →

    Val-Layout-Body-Act rest h h′ →

    h′ [ lhs ↦ rhs ]== h′′ →
    --------
    Val-Layout-Body-Act
      (Val-Points-To lhs rhs ∷ rest)
      h h′′

data _⟶_ {C} {Δ : Type-Context C} {Γ} : ∀ {C′} {Δ′ : Type-Context C′} {α} →
  (Expr Δ Γ α × Fs-Store Γ × Store Δ × Heap) →
  (Δ ↣ Δ′ × ∃[ ssl-α ] Store Δ′ × Heap × SSL-Var Δ′ ssl-α) → Set

-- Transition relation extended to lists of expressions
data Args-transition {C} {Δ : Type-Context C} {Γ} : ∀ {vars-Γ} {C′} {Δ′ : Type-Context C′} {Γ′} →
  (Args Γ′ × Fs-Store Γ × Store Δ × Heap) →
  (Δ ↣ Δ′ × Store Δ′ × Heap × SSL-Vars Δ′ vars-Γ) → Set where

  Args-transition-[] : ∀ {fs-store store h} →
    Args-transition (Args-∅ , fs-store , store , h) (Ctx-extension-here , store , h , SSL-Vars-∅)

  Args-transition-cons : ∀ {vars-Γ} {Γ′} {α ssl-α}
                           {args : Args Γ′}
                           {h h′ h′′}
                           {C′ C′′}
                           {Δ′ : Type-Context C′}
                           {Δ′′ : Type-Context C′′}
                           {store : Store Δ}
                           {store′ : Store Δ′}
                           {store′′ : Store Δ′′}
                           {fs-store : Fs-Store Γ}
                           {arg : Expr Δ′ vars-Γ α}
                           {arg-v} {args-vs : SSL-Vars Δ′′ vars-Γ}
                           {Δ↣Δ′ : Δ ↣ Δ′}
                           {Δ′↣Δ′′ : Δ′ ↣ Δ′′}
                           {Δ↣Δ′′ : Δ ↣ Δ′′}
                           {inj₁-arg}
                           {ext-arg-v}
                           {result} →
    (to-ssl : To-SSL-Type α ssl-α) →
    (non-fn : Non-Fn-Type α) →
    -- (arg , fs-store , store , h) ⟶ (Δ↣Δ′ , ssl-α , store′ , h′ , arg-v) →
    Args-transition (args , fs-store , store′ , h′) (Δ′↣Δ′′ , store′′ , h′′ , args-vs) →
    ext-arg-v ≡ apply-ctx-extension Δ′↣Δ′′ arg-v →
    inj₁-arg ≡ inj₁ arg →
    Args-transition (Args-cons non-fn inj₁-arg args , fs-store , store , h) (Δ↣Δ′′ , store′′ , h′′ , SSL-Vars-cons to-ssl ext-arg-v args-vs)
    -- Args-transition (Args-cons non-fn inj₁-arg args , fs-store , store , h) (Δ↣Δ′′ , store′′ , h′′ , SSL-Vars-cons to-ssl ext-arg-v args-vs)
    -- Args-transition (Args-cons non-fn inj₁-arg args , fs-store , store , h) (Δ↣Δ′′ , store′′ , h′′ , SSL-Vars-cons to-ssl (apply-ctx-extension (Δ′↣Δ′′) arg-v) args-vs)

data Eval-Layout-Body {C} {Δ : Type-Context C} {Γ} (fs-store : Fs-Store Γ) (store : Store Δ) (h : Heap) :
     Layout-Body Δ Γ → Val-Layout-Body → Set where
  Eval-Layout-Body-[] : Eval-Layout-Body fs-store store h [] []

  Eval-Layout-Body-Points-To : ∀ {α ssl-α}
                             {lhs : SSL-Expr Δ ε Loc-Type} {rhs : Expr Δ Γ α}
                             {C′} {Δ′ : Type-Context C′}
                             {Δ↣Δ′ : Δ ↣ Δ′}
                             {store′ : Store Δ′}
                             {h′}
                             {rest rest′}
                             {lhs-val}
                             {rhs-var : SSL-Var Δ′ ssl-α} →
    (α-base : Base-Type α) →
    (ssl-prf : To-SSL-Type α ssl-α) →
    (rhs , fs-store , store , h) ⟶ (Δ↣Δ′ , ssl-α , store′ , h′ , rhs-var) →
    SSL-Expr-Val-⇓ Δ ε store lhs (Val-Loc lhs-val) →
    Eval-Layout-Body fs-store store h rest rest′ →  -- Should this use store′ and h′?
    Eval-Layout-Body fs-store store h
      (Points-To lhs rhs α-base ∷ rest)
      (Val-Points-To lhs-val (store-lookup store′ rhs-var) ∷ rest′)

  Eval-Layout-Body-Ap : ∀ {rest : Layout-Body Δ Γ} {rest′ : Val-Layout-Body} {SSL-α} {n : Layout-Name} {v : SSL-Var Δ SSL-α} {e : Expr Δ Γ (Layout-Ty n)} →
    Eval-Layout-Body fs-store store h rest rest′ →
    Eval-Layout-Body fs-store store h (Ap n v e ∷ rest) rest′

-- Transition relation for one expression
-- TODO: Should there be a transition for Expr.V?
data _⟶_ {C} {Δ} {Γ} where

  AM-Lit : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {h}
             {α} {ssl-α : SSL-Type}
             {x : Val α} {ssl-x : SSL-Val ssl-α} →
    To-SSL-Val x ssl-x →
    let
      store′ : Store (Δ ,, ssl-α)
      store′ = Store-cons ssl-x store
    in
    (Lit x , fs-store , store , h) ⟶ (Ctx-extension-there Ctx-extension-here , ssl-α , store′ , h , SSL-Here)

  AM-Var : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {h}
             {α ssl-α}
             {v : Γ ∋ α}
             {val : SSL-Val ssl-α} →
    To-SSL-Val (fs-store-lookup fs-store v) val →
    (V v , fs-store , store , h) ⟶ (Ctx-extension-there Ctx-extension-here , ssl-α , Store-cons val store , h , SSL-Here )

  AM-Add : ∀ {fs-store : Fs-Store Γ}
             {store : Store Δ}
             {C′} {Δ′ : Type-Context C′}
             {C′′} {Δ′′ : Type-Context C′′}
             {store′ : Store Δ′}
             {store′′ : Store Δ′′}
             {h}
             {x : Expr Δ Γ Int-Ty}
             {y : Expr Δ Γ Int-Ty}
             {x-var y-var}
             {x-val y-val}
             {h′ h′′}
             {Δ↣Δ′} {Δ′↣Δ′′}→
    (x , fs-store , store , h) ⟶ (Δ↣Δ′ , Int-Type , store′ , h′ , x-var) →
    (y , fs-store , store , h′) ⟶ (Δ′↣Δ′′ , Int-Type , store′′ , h′′ , y-var) →
    Val-Int x-val ≡ store-lookup store′ x-var →
    Val-Int y-val ≡ store-lookup store′′ y-var →
    (Add x y , fs-store , store , h) ⟶ (Ctx-extension-there Ctx-extension-here , Int-Type , Store-cons (Val-Int (x-val + y-val)) store , h′′ , SSL-Here)

  AM-Lower : ∀ {fs-store : Fs-Store Γ}
                 {h : Heap}
                 {L-name adt branches} →
    {constr : Constr} →
    {ssl-param : SSL-Var (ε ,, Loc-Type) Loc-Type} →
    (constr-prf : constr ∈ Adt.constrs adt) →
    (args : Args (Constr.field-Γ constr)) →

    ∀ {L-body : Layout-Body (ε ,, Loc-Type) (Constr.field-Γ constr)} →

    let
      branch : Layout-Branch L-name constr
      branch = record { ssl-C = S Z ; ssl-Δ = (ε ,, Loc-Type) ; body = L-body }
    in
    (layout-prf : record { name = L-name ; adt = adt ; branches = branches } ∈ Global-Layout-Env) →
    (branch-prf : branch LB∈ branches) →

    --

    ∀ {store : Store Δ} →

    ∀ {C′} {Δ′ : Type-Context C′} {store′ : Store Δ′}
      {h′}
      {vars}
      {Δ↣Δ′} →
    Args-transition (args , fs-store , store , h) (Δ↣Δ′ , store′ , h′ , vars) →

    ∀ {ℓ} →
    ℓ # h →

    let
      store′′ = Store-cons (Val-Loc ℓ) store′
    in

    ∀ {args-fs-store} {val-layout-body} {h′′} →
    SSL-Vars→Fs-Store store′ vars args-fs-store →
    Eval-Layout-Body args-fs-store (Store-cons (Val-Loc ℓ) Store-[]) h′ L-body val-layout-body →
    Val-Layout-Body-Act val-layout-body h′ h′′ →

    -------

    (Lower constr ssl-param constr-prf args layout-prf branch-prf , fs-store , store , h)
      ⟶
    (Ctx-extension-there Δ↣Δ′ , Loc-Type , store′′ , h′′ , SSL-Here)

-- weaken-transition-left : ∀ {C} {Δ : Type-Context C} {Γ} {C′ C₀} {Δ′ : Type-Context C′} {Δ₀ : Type-Context C₀} {α} →
--   {lhs : (Expr Δ₀ Γ α × Fs-Store Γ × Store Δ₀ × Heap)} →
--   {lhs′ : (Expr Δ Γ α × Fs-Store Γ × Store Δ × Heap)} →
--   {rhs : (Δ ↣ Δ′ × ∃[ ssl-α ] Store Δ′ × Heap × SSL-Var Δ′ ssl-α)} →
--   {rhs′ : (Δ₀ ↣ Δ′ × ∃[ ssl-α ] Store Δ′ × Heap × SSL-Var Δ′ ssl-α)} →
--   (Δ₀ ↣ Δ) →
--   lhs′ ⟶ rhs →
--   lhs ⟶ rhs′
-- weaken-transition-left = {!!}

-- weaken-transition-left : ∀ {C} {Δ : Type-Context C} {Γ} {C′ C′′} {Δ′ : Type-Context C′} {Δ′′ : Type-Context C′′} {α} →
--   {lhs : (Expr Δ Γ α × Fs-Store Γ × Store Δ × Heap)} →
--   {rhs : (Δ ↣ Δ′ × ∃[ ssl-α ] Store Δ′ × Heap × SSL-Var Δ′ ssl-α)} →

--   {lhs′ : (Expr Δ′′ Γ α × Fs-Store Γ × Store Δ′′ × Heap)} →
--   {rhs′ : (Δ′′ ↣ Δ′ × ∃[ ssl-α ] Store Δ′ × Heap × SSL-Var Δ′ ssl-α)} →

--   (Δ ↣ Δ′′) →
--   -- (Δ ↣ Δ′) →
--   lhs ⟶ rhs →
--   lhs′ ⟶ rhs′
-- weaken-transition-left Δ↣Δ′′ (AM-Lit x) = {!!}
-- weaken-transition-left Δ↣Δ′′ (AM-Var x) = {!!}
-- weaken-transition-left Δ↣Δ′′ (AM-Add prf prf₁ x x₁) = {!!}
-- weaken-transition-left Δ↣Δ′′ (AM-Lower constr-prf args layout-prf branch-prf x x₁ x₂ x₃ x₄) = {!!}


-- weaken-transition-right : ∀ {C} {Δ : Type-Context C} {Γ} {C′ C′′} {Δ′ : Type-Context C′} {Δ′′ : Type-Context C′′} {α} →
--   {lhs : (Expr Δ′′ Γ α × Fs-Store Γ × Store Δ′′ × Heap)} →
--   {rhs : (Δ′′ ↣ Δ′ × ∃[ ssl-α ] Store Δ′ × Heap × SSL-Var Δ′ ssl-α)} →
--   {rhs′ : (Δ ↣ Δ′′ × ∃[ ssl-α ] Store Δ′′ × Heap × SSL-Var Δ′′ ssl-α)} →
--   (Δ′′ ↣ Δ′) →
--   lhs ⟶ rhs →
--   {!!} ⟶ rhs′
-- weaken-transition-right = {!!}

  -- {C} {Δ : Type-Context C} {Γ} : ∀ {C′} {Δ′ : Type-Context C′} {α} →
  -- (Expr Δ Γ α × Fs-Store Γ × Store Δ × Heap) →
  -- (Δ ↣ Δ′ × ∃[ ssl-α ] Store Δ′ × Heap × SSL-Var Δ′ ssl-α)

-- weaken-progress : ∀ {α ssl-α h} {C} {Δ : Type-Context C} {Γ} {fs-store : Fs-Store Γ} {store : Store Δ} → (e : Expr Δ Γ α) →
--   To-SSL-Type α ssl-α →
--   Σ SSL-Context λ C →
--   Σ (Type-Context C) λ Δ′ →
--   Σ (Δ ↣ Δ′) λ ext →
--   Σ (Store Δ′) λ store′ →
--   Σ Heap λ h′ →
--   ∃[ var ]
--     ((e , fs-store , store , h) ⟶ (ext , ssl-α , store′ , h′ , var ))
-- weaken-progress {α} {ssl-α} {h} {.Z} {ε} {Γ} {fs-store} {Store-[]} e prf = progress e prf
-- weaken-progress {α} {ssl-α} {h} {.(S _)} {Δ ,, v} {Γ} {fs-store} {Store-cons val store} e prf with expr-Δ-subst-1 prf (Store-cons val store) e
-- ... | inj₁ e′@(V x) , Expr-Δ-subst-1-V =
--         let
--           C₁ , y₁ , y₂ , y₃ , y₄ , y₅ , z = weaken-progress e′ prf
--           -- _  , _  , _  , _  , _  , _  , w = weaken-progress e prf
--         in
--         {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , weaken-transition-left (Ctx-extension-there Ctx-extension-here) z
-- ... | inj₁ (Lit x) , Expr-Δ-subst-1-Lit = {!!}
-- ... | inj₁ (Lit (Val-Int x)) , Expr-Δ-subst-1-SSL-V-Here-Int v = {!!}
-- ... | inj₁ (Lit (Val-Bool x)) , Expr-Δ-subst-1-SSL-V-Here-Bool v = {!!}
-- ... | inj₁ (SSL-V x y) , Expr-Δ-subst-1-SSL-V-There = {!!}
-- ... | inj₁ (Add x y) , Expr-Δ-subst-1-Add snd snd₁ = {!!}
-- ... | inj₁ (Sub x y) , Expr-Δ-subst-1-Sub snd snd₁ = {!!}
-- ... | inj₁ (And x y) , Expr-Δ-subst-1-And snd snd₁ = {!!}
-- ... | inj₁ (Not x) , Expr-Δ-subst-1-Not snd = {!!}
-- ... | inj₁ (Equal x y) , Expr-Δ-subst-1-Equal snd snd₁ = {!!}
-- ... | inj₁ (Lower _ _ _ _ _ _) , Expr-Δ-subst-1-Lower = {!!}
-- ... | inj₁ (Apply f (inj₁ x) prf) , Expr-Δ-subst-1-Apply-inj₁-inj₁ arg prf snd = {!!}
-- ... | inj₁ (Apply f (inj₂ x) prf) , Expr-Δ-subst-1-Apply-inj₁-inj₂ arg prf snd = {!!}
-- ... | inj₁ (Apply f (inj₂ arg) prf) , Expr-Δ-subst-1-Apply-inj₂ arg prf = {!!}
-- ... | inj₂ (fst , .mk-Is-Layout-Type) , Expr-Δ-subst-1-SSL-V-Here-Layout x = {!!}


-- weaken-progress {α} {ssl-α} {h} {.Z} {ε} {Γ} {fs-store} {Store-[]} e prf = progress e prf
-- weaken-progress {α} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (SSL-V SSL-Here z) prf = {!!}
-- weaken-progress {α} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (SSL-V (SSL-There y) z) prf = {!!}
-- -- weaken-progress {α} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} e prf -- with Expr-Δ-subst-1 prf (Store-cons val store) e
-- weaken-progress {α} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (SSL-V SSL-Here z) prf = {!!}
-- weaken-progress {α} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (SSL-V (SSL-There y) z) prf = {!!}
-- weaken-progress {Layout-Ty _} {.Loc-Type} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (V x₁) To-SSL-Type-Layout with (Expr-Δ-subst-1 To-SSL-Type-Layout (Store-cons val store) (V x₁))
-- weaken-progress {Layout-Ty _} {.Loc-Type} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (V x₁) To-SSL-Type-Layout | inj₂ w = {!!}
-- weaken-progress {α} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (Lit x₁) prf = {!!}
-- weaken-progress {.Int-Ty} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (Add e e₁) prf = {!!}
-- weaken-progress {.Int-Ty} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (Sub e e₁) prf = {!!}
-- weaken-progress {.Bool-Ty} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (And e e₁) prf = {!!}
-- weaken-progress {.Bool-Ty} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (Not e) prf = {!!}
-- weaken-progress {.Bool-Ty} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (Equal e e₁) prf = {!!}
-- weaken-progress {.(Layout-Ty _)} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (Lower constr ssl-param x₁ x₂ x₃ x₄) prf = {!!}
-- weaken-progress {.(Layout-Ty _)} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} (Apply f-name arg x₁) prf = {!!}
-- weaken-progress {α} {ssl-α} {h} {.(S _)} {Δ ,, x} {Γ} {fs-store} {Store-cons val store} e prf | inj₂ y ()

  -- let
  --   Δ↣Δ′ : Δ ↣ (Δ ,, x)
  --   Δ↣Δ′ = Ctx-extension-there Ctx-extension-here

  --   z = weaken-progress {α} {ssl-α} {h} {_} {Δ} {Γ} {fs-store} {store} (Expr-Δ-subst-1 ? ? ?) {!!}
  -- in
  -- {!!}

-- eval-layout-body : ∀ {C} {Δ : Type-Context C} {Γ} (fs-store : Fs-Store Γ) (store : Store Δ) (h : Heap) →
--   (body : Layout-Body Δ Γ) → ∃[ val-body ] Eval-Layout-Body fs-store store h body val-body
-- eval-layout-body fs-store store h [] = [] , Eval-Layout-Body-[]

-- eval-layout-body fs-store store h (Points-To lhs rhs base-prf ∷ body)
--   with eval store lhs | weaken-progress {_} {_} {h} {_} {_} {_} {fs-store} {store} rhs (proj₂ (to-SSL-Type (Non-Fn-Type-Base base-prf)))
-- ... | Val-Loc val , val-prf
--     | rhs-C , x-Δ , rhs-ext , rhs-store , rhs-heap , rhs-var , rhs-transition =
--   let
--     val-body , rest = eval-layout-body fs-store store h body
--   in
--   Val-Points-To val (store-lookup rhs-store rhs-var) ∷ val-body ,
--   Eval-Layout-Body-Points-To base-prf (proj₂ (to-SSL-Type (Non-Fn-Type-Base base-prf))) rhs-transition val-prf rest

-- eval-layout-body fs-store store h (Ap n x x₁ ∷ body) =
--   let
--     val-body , rest = eval-layout-body fs-store store h body
--   in
--   val-body , Eval-Layout-Body-Ap rest
  

progress : ∀ {α ssl-α h} {Γ} {fs-store : Fs-Store Γ} {C₀} {Δ₀ : Type-Context C₀} {store : Store Δ₀} → (e : Expr Δ₀ Γ α) →
  To-SSL-Type α ssl-α →
  Σ SSL-Context λ C →
  Σ (Type-Context C) λ Δ →
  Σ (Δ₀ ↣ Δ) λ ext →
  Σ (Store Δ) λ store′ →
  Σ Heap λ h′ →
  ∃[ var ]
    ((e , fs-store , store , h) ⟶ (ext , ssl-α , store′ , h′ , var ))

Args-progress : ∀ h {Γ Γ′} (fs-store : Fs-Store Γ) {C₀} {Δ₀ : Type-Context C₀} (store : Store Δ₀) → (args : Args Γ′) →
  Σ Context λ vars-Γ →
  Σ SSL-Context λ C →
  Σ (Type-Context C) λ Δ →
  Σ (Δ₀ ↣ Δ) λ ext →
  Σ (Store Δ) λ store′ →
  Σ Heap λ h′ →
  ∃[ vars ]
    Args-transition {_} {_} {_} {vars-Γ} (args , fs-store , store , h) (ext , store′ , h′ , vars )
Args-progress h {Γ} {Γ′} fs-store {C₀} {Δ₀} store Args-∅ =
  ∅ ,
  C₀ ,
  Δ₀ ,
  Ctx-extension-here ,
  store ,
  h ,
  SSL-Vars-∅ ,
  Args-transition-[]

Args-progress h fs-store store (Args-cons x (inj₂ loc) args) = {!!}

Args-progress h {Γ} {Γ′} fs-store store (Args-cons x (inj₁ e) args)
  with progress {_} {_} {h} {Γ} {fs-store} {!!} (proj₂ (to-SSL-Type x))
Args-progress h fs-store store (Args-cons x x₁ args) | e-C , e-Δ , e-ext , e-store , e-heap , e-var , e-transition
  with Args-progress e-heap fs-store e-store args
Args-progress h {Γ} {Γ′} fs-store store (Args-cons {_} {_} {Γ₁} {Γ₂} x x₁ args)
           | e-C , e-Δ , e-ext , e-store , e-heap , e-var , e-transition
           | args-vars-Γ , args-C , args-Δ , args-ext , args-store , args-h , args-vars , args-transition =
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  let
    z = Args-transition-cons {!!} x args-transition refl refl
  in
-- Args-transition (Args-cons x (inj₁ e) args , fs-store , store , h)
-- (?5 , ?6 , ?7 , ?8)
  Args-transition-cons {{!!}} {{!!}} {{!!}} {{!!}} {Γ₂} {{!!}} {!!} {!!} {!!} {!!} {!!}


progress {α} {ssl-α} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (V x) ssl-type-prf =
  let
    val = fs-store-lookup fs-store x
    ssl-val , ssl-prf = to-SSL-Val ssl-type-prf val
  in
  S C₀ ,
  (Δ₀ ,, ssl-α) ,
  Ctx-extension-there Ctx-extension-here ,
  Store-cons ssl-val store ,
  h ,
  SSL-Here ,
  AM-Var ssl-prf

progress {α} {ssl-α} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Lit x) ssl-type-prf =
  let
    ssl-val , ssl-prf = to-SSL-Val ssl-type-prf x
  in
  S C₀ ,
  (Δ₀ ,, ssl-α) ,
  Ctx-extension-there Ctx-extension-here ,
  Store-cons ssl-val store ,
  h ,
  SSL-Here ,
  AM-Lit ssl-prf


progress {α} {ssl-α} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (SSL-V x x₁) ssl-type-prf =
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  {!!}

progress {.Int-Ty} {Int-Type} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Add e e₁) To-SSL-Type-Int
  with progress {Int-Ty} {Int-Type} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} e To-SSL-Type-Int
progress {.Int-Ty} {Int-Type} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Add e e₁) To-SSL-Type-Int | x-C , x-Δ , x-ext , x-store , x-heap , x-var , x-transition
  with progress {Int-Ty} {Int-Type} {x-heap} {Γ} {fs-store} {C₀} {Δ₀} {store} e₁ To-SSL-Type-Int
progress {.Int-Ty} {Int-Type} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Add e e₁) To-SSL-Type-Int | x-C , x-Δ , x-ext , x-store , x-heap , x-var , x-transition
                                                                                              | y-C , y-Δ , y-ext , y-store , y-heap , y-var , y-transition
  with store-lookup x-store x-var in eq-x | store-lookup y-store y-var in eq-y
progress {.Int-Ty} {Int-Type} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Add e e₁) To-SSL-Type-Int | x-C , x-Δ , x-ext , x-store , x-heap , x-var , x-transition
                                                                                              | y-C , y-Δ , y-ext , y-store , y-heap , y-var , y-transition
                                                                                              | Val-Int x-val | Val-Int y-val =
  S C₀ ,
  (Δ₀ ,, Int-Type) ,
  Ctx-extension-there Ctx-extension-here ,
  Store-cons (Val-Int (x-val + y-val)) store ,
  y-heap ,
  SSL-Here ,
  AM-Add x-transition y-transition (sym eq-x) (sym eq-y)

progress {.Int-Ty} {ssl-α} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Sub e e₁) ssl-type-prf = {!!}
progress {.Bool-Ty} {ssl-α} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (And e e₁) ssl-type-prf = {!!}
progress {.Bool-Ty} {ssl-α} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Not e) ssl-type-prf = {!!}
progress {.Bool-Ty} {ssl-α} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Equal e e₁) ssl-type-prf = {!!}

progress {.(Layout-Ty _)} {Loc-Type} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Lower constr ssl-param x e x₂ x₃) To-SSL-Type-Layout
  with Args-progress h fs-store store {!!}
progress {.(Layout-Ty _)} {Loc-Type} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Lower constr ssl-param x e x₂ x₃) To-SSL-Type-Layout
         | e-C , e-Δ , e-ext , e-store , e-heap , e-var , e-transition =
  let
    ℓ , ℓ#h = gen-fresh h
  in
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  {!!} ,
  AM-Lower x e x₂ x₃ {!!} ℓ#h {!!} {!!} {!!}

progress {.(Layout-Ty _)} {ssl-α} {h} {Γ} {fs-store} {C₀} {Δ₀} {store} (Apply f-name arg x) ssl-type-prf = {!!}

-- progress {α} {ssl-α} {h} {Γ} {fs-store} (V v) ssl-type-prf = {!!}
-- progress {α} {ssl-α} {h} (Lit x) ssl-type-prf =
--   let
--     ssl-val , ssl-prf = (to-SSL-Val ssl-type-prf x)

--   in
--   S Z ,
--   (ε ,, ssl-α) ,
--   Ctx-extension-there Ctx-extension-here ,
--   Store-cons ssl-val Store-[] ,
--   h ,
--   SSL-Here ,
--   AM-Lit ssl-prf

-- progress {.Int-Ty} {.Int-Type} {h} (Add x y) To-SSL-Type-Int
--   with progress x To-SSL-Type-Int
-- progress {.Int-Ty} {.Int-Type} {h} (Add x y) To-SSL-Type-Int | x-C , x-Δ , x-ext , x-store , x-heap , x-var , x-transition with progress y To-SSL-Type-Int
-- progress {.Int-Ty} {.Int-Type} {h} (Add x y) To-SSL-Type-Int | x-C , x-Δ , x-ext , x-store , x-heap , x-var , x-transition
--                                                              | y-C , y-Δ , y-ext , y-store , y-heap , y-var , y-transition with store-lookup x-store x-var in eq-x | store-lookup y-store y-var in eq-y
-- progress {.Int-Ty} {.Int-Type} {h} (Add x y) To-SSL-Type-Int | x-C , x-Δ , x-ext , x-store , x-heap , x-var , x-transition
--                                                              | y-C , y-Δ , y-ext , y-store , y-heap , y-var , y-transition
--                                                              | Val-Int x-val | Val-Int y-val =
--   S Z ,
--   (ε ,, Int-Type) ,
--   Ctx-extension-there Ctx-extension-here ,
--   Store-cons (Val-Int (x-val + y-val)) Store-[] ,
--   y-heap ,
--   SSL-Here ,
--   AM-Add x-transition y-transition (sym eq-x) (sym eq-y)
-- progress {.Int-Ty} {ssl-α} (Sub e e₁) ssl-type-prf = {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
-- progress {.Bool-Ty} {ssl-α} (And e e₁) ssl-type-prf = {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
-- progress {.Bool-Ty} {ssl-α} (Not e) ssl-type-prf = {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
-- progress {.Bool-Ty} {ssl-α} (Equal e e₁) ssl-type-prf = {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

-- progress {.(Layout-Ty _)} {ssl-α} {h} (Lower constr ssl-param constr-prf args layout-prf branch-prf) To-SSL-Type-Loc =
--   S Z ,
--   {!!} ,
--   {!!} ,
--   {!!} 
--   {!!} ,
--   {!!} ,
--   {!!}
--   AM-Lower {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!} {!!}
