open import Data.String
open import Data.Nat
open import Data.List
open import Data.Integer

module SSLTests
  where

fromNat : ℕ → ℤ
fromNat = +_
{-# BUILTIN FROMNAT fromNat #-}


Pred-Name : Set
Pred-Name = String

data Pred-Label : Set where
  Pred-Label-Z : Pred-Label
  Pred-Label-S : Pred-Label → Pred-Label

data Loc : Set where
  Loc-X : Loc
  Loc-Y : Loc
  Loc-Z : Loc

open import SSL (Pred-Name) (Pred-Label) (Loc)

sll-Γ : SSL-Context
sll-Γ = Z

sll : List (Ind-Rule sll-Γ)
sll =
  record
    { name = "sll"
    ; assertion = record
                    { pure = Equal (V [ Here :+ zero ]) (Int-Lit 0)
                    ; pure-Is-Bool = Is-Bool-Equal
                    ; spatial = []
                    }
    }
  ∷
  record
    { name = "sll"
    ; assertion = record
                    { pure = Not (Equal (V [ Here :+ zero ]) (Int-Lit 0))
                    ; pure-Is-Bool = Is-Bool-Not Is-Bool-Equal
                    ; spatial = {!!} ∷ {!!} ∷ []
                    }
    }
  ∷
  []
