open import Data.Sum
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Layout

module FunDef
  -- (Name : Set)
  -- (Name-eq-dec : ∀ (x y : Name) → (x ≡ y) ⊎ (x ≢ y))
  where

data Type-0 : Set where
  Int-Ty : Type-0
  Bool-Ty : Type-0
  Layout-Ty : Layout → Type-0

data Type : Set where
  Ty-0 : Type-0 → Type
  Fn-Ty : Type-0 → Type → Type

data Context : Set where
  ∅ : Context
  _,,_ : Context → Type → Context

data _∋_ : Type → Context → Set where

-- data Expr : Set where
--   V : 
