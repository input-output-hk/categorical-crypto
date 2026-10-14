{-# OPTIONS --safe --without-K #-}

-- A resource interpretation in SSP.Dist.Setup, not a UCSetupMorphism.
-- Every finite typed adaptive strategy is compiled, including private coins.
module CategoricalCrypto.IPDL.SSP where

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import CategoricalCrypto.IPDL.Native
open import CategoricalCrypto.IPDL.Syntax
open import CategoricalCrypto.SSP.Dist.Kernel using (Coins; done; toss; coins; sample)
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
import CategoricalCrypto.SSP.Dist.Setup as SSPᵈ
import CategoricalCrypto.SSP.Protocol as P

private variable
  I O : Ctx
  A : Iface
  X S : Set

resource : Net I O → SSPᵈ.unit SSPᵈ.⇒ API I O
resource N = record
  { St = Residual.State N ; init = Residual.initial N
  ; step = λ s c q → coins (Interaction.turn N s c q) }

compileTree : S → Strategy I O X → P.Calls (API I O) (S × X)
compileTree s (finish x) = P.ret (s , x)
compileTree s (ask c q k) = P.call c q λ r → compileTree s (k r)
compileTree s (random μ k) = P.coin μ λ b → compileTree s (k b)

tester : Strategy I O Bool → P.Protocol (API I O) Ωᴵ
tester a = record { St = ⊤ ; init = tt ; step = λ _ _ _ → compileTree tt a }

module Correspondence {I O} (N : Net I O) where
  open Residual N
  open Interaction N
  open Experiment N

  module _ (D : P.Protocol (API I O) A) where
    serve-coins : ∀ {c} (κ : Coins (State × Reply I O c))
                (k : Reply I O c → P.Calls (API I O) (P.St D × X))
              → evalC (P.mapᶜ proj₂ (P.serve D (resource N) k (coins κ)))
                ≈Mℚ (sample κ >>=ᴹ λ (s , r) → evalC (P.mapᶜ proj₂ (P.graft D (resource N) (k r) s)))
    serve-coins (done (s , r)) k = λ ξ → sym
      (>>=ᴹ-identityˡ (s , r) (λ (s′ , r′) → evalC (P.mapᶜ proj₂ (P.graft D (resource N) (k r′) s′))) ξ)
    serve-coins (toss μ f) k ξ = trans
      (>>=ᴹ-congˡ μ
        (λ b → evalC (P.mapᶜ proj₂ (P.serve D (resource N) k (coins (f b)))))
        (λ b → sample (f b) >>=ᴹ λ (s , r) → evalC (P.mapᶜ proj₂ (P.graft D (resource N) (k r) s)))
        (λ b → serve-coins (f b) k) ξ)
      (sym (>>=ᴹ-assoc μ (sample ∘ f)
        (λ (s , r) → evalC (P.mapᶜ proj₂ (P.graft D (resource N) (k r) s))) ξ))

    execution : (d : P.St D) (a : Strategy I O X) (s : State)
              → evalC (P.mapᶜ proj₂ (P.graft D (resource N) (compileTree d a) s))
                ≈Mℚ runWith return⊥ a s
    execution d (finish x) s = λ _ → refl
    execution d (ask c q k) s ξ = trans
      (serve-coins (turn s c q) (compileTree d ∘ k) ξ)
      (>>=ᴹ-congˡ (sample (turn s c q))
        (λ (s′ , r) → evalC (P.mapᶜ proj₂ (P.graft D (resource N) (compileTree d (k r)) s′)))
        (λ (s′ , r) → runWith return⊥ (k r) s′)
        (λ (s′ , r) → execution d (k r) s′) ξ)
    execution d (random μ k) s = >>=ᴹ-congˡ μ
      (λ b → evalC (P.mapᶜ proj₂ (P.graft D (resource N) (compileTree d (k b)) s)))
      (λ b → runWith return⊥ (k b) s) λ b → execution d (k b) s

  lift-run : (a : Strategy I O X) (s : State)
           → runWith return⊥ a s ≈Mℚ (runWith return-ℚ a s >>=ᴹ return⊥)
  lift-run (finish x) s ξ = sym (>>=ᴹ-identityˡ x return⊥ ξ)
  lift-run (ask c q k) s ξ = trans
    (>>=ᴹ-congˡ (sample (turn s c q))
      (λ (s′ , r) → runWith return⊥ (k r) s′)
      (λ (s′ , r) → runWith return-ℚ (k r) s′ >>=ᴹ return⊥)
      (λ (s′ , r) → lift-run (k r) s′) ξ)
    (sym (>>=ᴹ-assoc (sample (turn s c q)) (λ (s′ , r) → runWith return-ℚ (k r) s′) return⊥ ξ))
  lift-run (random μ k) s ξ = trans
    (>>=ᴹ-congˡ μ (λ b → runWith return⊥ (k b) s)
      (λ b → runWith return-ℚ (k b) s >>=ᴹ return⊥) (λ b → lift-run (k b) s) ξ)
    (sym (>>=ᴹ-assoc μ (λ b → runWith return-ℚ (k b) s) return⊥ ξ))

  agreement : (a : Strategy I O Bool)
            → runᵖ (tester a P.∘ᵖ resource N) ≈Mℚ (run a >>=ᴹ return⊥)
  agreement a ξ = trans (execution (tester a) tt a initial ξ) (lift-run a initial ξ)
