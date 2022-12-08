open import Data.String
open import Data.Nat
open import Data.List
open import Data.Integer
open import Data.Product

module SSLTests
  where

-- fromNat : ℕ → ℤ
-- fromNat = +_
-- {-# BUILTIN FROMNAT fromNat #-}


Pred-Name : Set
Pred-Name = String

data Pred-Label : Set where
  Pred-Label-Z : Pred-Label
  Pred-Label-S : Pred-Label → Pred-Label

α : Pred-Label
α = Pred-Label-Z

β : Pred-Label
β = Pred-Label-S Pred-Label-Z

data Loc-Name : Set where
  Loc-X : Loc-Name
  Loc-Y : Loc-Name
  Loc-Z : Loc-Name

open import SSLSatisfies (Pred-Name) (Pred-Label) (Loc-Name)
open import SSL (Pred-Name) (Pred-Label) (Loc-Name)
open Ambient-Context

label : Pred-Name → Pred-Label → Labeled-Pred-Name
label n ℓ = n , ℓ

sll-C : SSL-Context
sll-C = S Z

sll-E : Exist-Context
sll-E = Exist-S (Exist-S Exist-Z)

sll-Γ : Type-Context sll-C
sll-Γ = ε ,, Loc-Type

-- Existentials
sll-Δ : E-Type-Context sll-E
sll-Δ =
  ε ,,
  Loc-Type ,,  -- nxt
  Int-Type     -- v


sll : List (Ind-Rule sll-Γ sll-Δ)
sll =
  record
    { name = "sll"
    ; assertion = record
                    { pure = Equal (V Here) (Lit (Val-Loc Null))
                    ; spatial = []
                    }
    }
  ∷
  record
    { name = "sll"
    ; assertion = record
                    { pure = Not (Equal (V Here) (Lit (Val-Loc Null)))
                    ; spatial =
                      Points-To (Lit (Val-Loc (mk-Loc Loc-X 0))) (Exists-V EV-Here)  -- x :-> v
                      ∷
                      Points-To (Lit (Val-Loc (mk-Loc Loc-X 1))) (Exists-V (EV-There EV-Here)) -- (x+1) :-> nxt
                      ∷
                      (label "sll" α · Vec-S (Exists-V (EV-There EV-Here)) Vec-Z) -- sll_α(x)
                      ∷ []
                    }
    }
  ∷
  []
