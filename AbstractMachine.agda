open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Bool
open import Data.Integer

module AbstractMachine
  (Pred-Name : Set)
  (Pred-Label : Set)
  (Loc-Name : Set)
  (Loc-Name-eq-dec : ∀ (x y : Loc-Name) → (x ≡ y) ⊎ (x ≢ y))

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
    loc # H

-- Evaluated layout body acting on a Heap
data Val-Layout-Body-Act :
    Val-Layout-Body →
    Heap →
    Heap →
    Set where

  Val-Layout-Body-Act-[] : ∀ {h} →
    Val-Layout-Body-Act [] h h

  Val-Layout-Body-Act-Points-To : ∀ {α} {ssl-α : SSL-Type}
                                {h h′ h′′ rest}
                                {lhs : Loc} {rhs : Val α}
                                {sll-rhs}
    (α-base-type : Base-Type α) →
    To-SSL-Val {α} {ssl-α} rhs sll-rhs →

    Val-Layout-Body-Act rest h h′ →

    h′ [ lhs ↦ sll-rhs ]== h′′ →
    --------
    Val-Layout-Body-Act
      (Val-Points-To lhs rhs α-base-type ∷ rest)
      h h′′

data _⟶_ {Γ} : ∀ {α} →
  (Expr ε Γ α × Fs-Store Γ × Heap) →
  (Fs-Store (Γ ,, α) × Heap) → Set where

  AM-Lit : ∀ {store : Fs-Store Γ}
             {h}
             {α}
             {x : Val α} →
    (Lit x , store , h) ⟶ (Fs-Store-cons x store , h )

  AM-Var : ∀ {store : Fs-Store Γ}
             {h}
             {α}
             {v : Γ ∋ α}
             {val} →
    (V v , store , h) ⟶ (Fs-Store-cons val store , h )

  AM-Add : ∀ {store : Fs-Store Γ}
             {h}
             {x y : Expr ε Γ Int-Ty}
             {x-val y-val} →
    (x , store , h) ⟶ (Fs-Store-cons (Val-Int x-val) store , h) →
    (y , store , h) ⟶ (Fs-Store-cons (Val-Int y-val) store , h) →
    (Add x y , store , h) ⟶ (Fs-Store-cons (Val-Int (x-val + y-val)) store , h)

  -- AM-Lower : 
