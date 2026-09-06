{-# OPTIONS --safe --without-K #-}

-- Protocols: stateful, effectful, interactive programs in plain Agda.
--
-- A step answers one incoming message on the right interface, along the way
-- making finitely many calls on the left interface and flipping rational
-- coins; `dead` is divergence (mass on ⊥ under observation).  Everything is an
-- inductive syntax tree, so composition `_∘ᵖ_` — plug a protocol onto the one
-- below it and hide the shared interface — is structural recursion: no fuel,
-- no clocks, no partiality.
--
-- The zero-or-one-call special case has its own plain shape in
-- `CategoricalCrypto.OracleCall` (`Call`), embedded by `fromCall`; a
-- deterministic multi-call protocol like Merkle–Damgård writes its step
-- directly in `Calls`.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Vec.Base using (Vec; []; _∷_)

open import ProbabilisticLogic.Prelude

open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall

module CategoricalCrypto.Protocol where

private variable X Y : Set
                 A B C : Iface

------------------------------------------------------------------------
-- Call trees
------------------------------------------------------------------------

data Calls (A : Iface) (X : Set) : Set where
  ret  : X → Calls A X
  call : Neg A → (Pos A → Calls A X) → Calls A X
  coin : Dist-ℚ Bool → (Bool → Calls A X) → Calls A X
  dead : Calls A X

_>>=ᶜ_ : Calls A X → (X → Calls A Y) → Calls A Y
ret x    >>=ᶜ f = f x
call q k >>=ᶜ f = call q λ r → k r >>=ᶜ f
coin μ k >>=ᶜ f = coin μ λ b → k b >>=ᶜ f
dead     >>=ᶜ f = dead

fromCall : Call (Neg A) (Pos A) X → Calls A X
fromCall (inj₁ x)       = ret x
fromCall (inj₂ (q , k)) = call q λ r → ret (k r)

-- Sample a uniform bit vector, one fair coin per bit.
uniformVec : (n : ℕ) → (Vec Bool n → Calls A X) → Calls A X
uniformVec zero    k = k []
uniformVec (suc n) k = coin uniform-Bool λ b → uniformVec n λ v → k (b ∷ v)

------------------------------------------------------------------------
-- Protocols
------------------------------------------------------------------------

record Protocol (A B : Iface) : Set₁ where
  field
    St   : Set
    init : St
    step : St → Neg B → Calls A (St × Pos B)
open Protocol public

wireᵖ : Protocol A A
wireᵖ = record { St = ⊤ ; init = tt ; step = λ _ q → call q λ r → ret (tt , r) }

------------------------------------------------------------------------
-- Composition
------------------------------------------------------------------------

-- `graft`/`serve` are public: `Protocol.Machine.Compose` needs to name the
-- grafted continuation a suspended composite holds.
module _ (P₂ : Protocol B C) (P₁ : Protocol A B) where
  mutual
    -- Walk P₂'s tree; each of its calls runs one activation of P₁.
    graft : Calls B (St P₂ × Pos C) → St P₁ → Calls A ((St P₂ × St P₁) × Pos C)
    graft (ret (s₂ , c⁺)) s₁ = ret ((s₂ , s₁) , c⁺)
    graft (call b k)      s₁ = serve k (step P₁ s₁ b)
    graft (coin μ k)      s₁ = coin μ λ x → graft (k x) s₁
    graft dead            s₁ = dead

    -- Walk P₁'s answer tree, forwarding its own calls upward.
    serve : (Pos B → Calls B (St P₂ × Pos C))
          → Calls A (St P₁ × Pos B) → Calls A ((St P₂ × St P₁) × Pos C)
    serve k (ret (s₁ , b⁺)) = graft (k b⁺) s₁
    serve k (call a k₁)     = call a λ r → serve k (k₁ r)
    serve k (coin μ k₁)     = coin μ λ x → serve k (k₁ x)
    serve k dead            = dead

  infixl 9 _∘ᵖ_
  _∘ᵖ_ : Protocol A C
  _∘ᵖ_ = record
    { St   = St P₂ × St P₁
    ; init = init P₂ , init P₁
    ; step = λ (s₂ , s₁) c → graft (step P₂ s₂ c) s₁ }
