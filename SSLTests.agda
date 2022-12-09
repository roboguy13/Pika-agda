open import Data.String
open import Data.Nat
open import Data.List
open import Data.Integer
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum
open import Data.Bool
open import Data.Unit

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

ρ : Pred-Label → ℕ
ρ Pred-Label-Z = 0
ρ _ = 1

data Loc-Name : Set where
  Loc-X : Loc-Name
  Loc-Y : Loc-Name
  Loc-Z : Loc-Name

Loc-Name-eq-dec : ∀ (x y : Loc-Name) → (x ≡ y) ⊎ (x ≢ y)
Loc-Name-eq-dec Loc-X Loc-X = inj₁ refl
Loc-Name-eq-dec Loc-X Loc-Y = inj₂ (λ ())
Loc-Name-eq-dec Loc-X Loc-Z = inj₂ (λ ())
Loc-Name-eq-dec Loc-Y Loc-X = inj₂ (λ ())
Loc-Name-eq-dec Loc-Y Loc-Y = inj₁ refl
Loc-Name-eq-dec Loc-Y Loc-Z = inj₂ (λ ())
Loc-Name-eq-dec Loc-Z Loc-X = inj₂ (λ ())
Loc-Name-eq-dec Loc-Z Loc-Y = inj₂ (λ ())
Loc-Name-eq-dec Loc-Z Loc-Z = inj₁ refl

open import SSLSatisfies (Pred-Name) (Pred-Label) (Loc-Name) (Loc-Name-eq-dec)
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
                      Points-To (V Here) (Exists-V EV-Here)  -- x :-> v
                      ∷
                      Points-To (Loc-Ix (V Here) 1) (Exists-V (EV-There EV-Here)) -- (x+1) :-> nxt
                      ∷
                      (label "sll" α · Vec-S (Exists-V (EV-There EV-Here)) Vec-Z) -- sll_α(x)
                      ∷ []
                    }
    }
  ∷
  []

store : Store sll-Γ
store Here = Val-Loc (mk-Loc Loc-X 0)

heap-0 : Heap
heap-0 = (Loc-Type , mk-Loc Loc-X 0 , Val-Loc Null) ∷ []
-- heap-0 = []

heap-1 : Heap
heap-1 = (Int-Type , mk-Loc Loc-X 0 , Val-Int (+ 7)) ∷ []

constrained-asn-test-1 : Constrained-Formula sll-Γ sll-Δ
constrained-asn-test-1 = ((α ∷ []) , [] , record { pure = Lit (Val-Bool true) ; spatial = (label "sll" α · Vec-S (Lit (Val-Loc (mk-Loc Loc-X 0))) Vec-Z) ∷ [] }) -- sll_α(x)

sll-test-0-formula : ρ ==/[ α ∷ [] ] ρ →
  Constraints-hold ρ [] →
  Satisfies-Assertion sll ρ store heap-0
  (record
  { pure = Lit (Val-Bool true)
  ; spatial =
      (label "sll" α · Vec-S (Lit (Val-Loc (mk-Loc Loc-X 0))) Vec-Z) ∷ []
  })
sll-test-0-formula x x₁ =
  record { pure-prf = Lit (Val-Int (+ 7)) , Lit (Val-Loc (mk-Loc Loc-X 0)) , tt ; spatial-prf = Satisfies-spatial-∷ {!!} {!!} {!!} }

sll-test-0 :
  ρ , store , heap-0 ⊨[ sll ] constrained-asn-test-1
sll-test-0 = mk-Satisfies-Constrained-Formula (ρ , sll-test-0-formula)
