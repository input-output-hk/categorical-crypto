{-# OPTIONS --safe --without-K #-}

-- `Examples.SSP.OneTimePad`'s `otp ≤UC ideal` again, its core a chain of `≈ᵈ`
-- laws (`docs/uc-setup-ssp-dist.md` §5) in place of the induction over every
-- distinguisher's tree (`fresh`, `pending`, `revealed`).  `lazy` is the
-- simulated world on its reachable states, `draw` samples the real world's
-- ciphertext and key from each, and `defer` checks one square of call trees
-- per activation: six by computation, two pad cancellations (`xor-cancel`)
-- and the pad's bijection at Alice's send (`coin-xor`).  The core, `Phase` to
-- `lazy≲simulated`, is 55 lines of code against the run-level 53 (`play` to
-- `perfect`): what it buys is locality, not length.

module CategoricalCrypto.Examples.SSP.OneTimePad.Dist where

open import Data.Bool.Base
open import Data.Bool.Properties using (xor-comm)
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Examples.SSP.OneTimePad
open import CategoricalCrypto.SSP.Dist
open import CategoricalCrypto.SSP.Dist.Kernel
open import CategoricalCrypto.SSP.Dist.Laws
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Setup

-- Nothing sent; sent, Eve not yet polled; Eve saw ciphertext `c`.
data Phase : Set where
  idle   : Phase
  sent   : Msg → Phase
  polled : Cipher → Msg → Phase

cipher : Phase → Maybe Cipher
cipher (polled c _) = just c
cipher _            = nothing

msg : Phase → Maybe Msg
msg idle         = nothing
msg (sent m)     = just m
msg (polled _ m) = just m

lazy : unit ⇒ T₀ Eveᴵ Honᴵ
lazy = record
  { St = Phase ; init = idle
  ; step = λ where
      s            (inj₂ (inj₂ _)) _ → ret (s , msg s)
      idle         (inj₂ (inj₁ _)) m → ret (sent m , tt)
      s            (inj₂ (inj₁ _)) _ → ret (s , tt)
      idle         (inj₁ _)        _ → ret (idle , nothing)
      (sent m)     (inj₁ _)        _ → coin uniform-Bool λ c → ret (polled c m , just c)
      (polled c m) (inj₁ _)        _ → ret (polled c m , just c) }

-- The key is the pad `c xor m`.
draw : Phase → Coins (Maybe Cipher × Maybe Key)
draw idle         = done (nothing , nothing)
draw (sent m)     = toss uniform-Bool λ c → done (just c , just (c xor m))
draw (polled c m) = done (just c , just (c xor m))

xor-cancel : ∀ c m → c xor (c xor m) ≡ m
xor-cancel false m     = refl
xor-cancel true  false = refl
xor-cancel true  true  = refl

lazy≈real : lazy ≈ᵈ real
lazy≈real = defer draw (λ _ → refl) λ where
  idle         (inj₁ _)        _ → ≈ᵏ-refl
  (sent _)     (inj₁ _)        _ → ≈ᵏ-refl
  (polled _ _) (inj₁ _)        _ → ≈ᵏ-refl
  idle         (inj₂ (inj₁ _)) m → ≈ᵏ-trans
    (≈ᶜ⇒≈ᵏ (coin λ k → ret (cong (λ x → (just (m xor k) , just x) , tt)
                                 (sym (trans (xor-comm (m xor k) m) (xor-cancel m k))))))
    (coin-xor m λ c → ret ((just c , just (c xor m)) , tt))
  (sent _)     (inj₂ (inj₁ _)) _ → ≈ᵏ-refl
  (polled _ _) (inj₂ (inj₁ _)) _ → ≈ᵏ-refl
  idle         (inj₂ (inj₂ _)) _ → ≈ᵏ-refl
  (sent m)     (inj₂ (inj₂ _)) _ →
    ≈ᶜ⇒≈ᵏ (coin λ c → ret (cong (λ x → (just c , just (c xor m)) , just x) (xor-cancel c m)))
  (polled c m) (inj₂ (inj₂ _)) _ → ≈ᶜ⇒≈ᵏ (ret (cong (λ x → (just c , just (c xor m)) , just x) (xor-cancel c m)))

lazy≲simulated : lazy ≲ᵖ simulated
lazy≲simulated = record
  { θ = λ s → cipher s , msg s ; θ-init = refl
  ; θ-step = λ where
      _            (inj₂ (inj₂ _)) _ → ≈ᶜ-refl
      idle         (inj₂ (inj₁ _)) _ → ≈ᶜ-refl
      (sent _)     (inj₂ (inj₁ _)) _ → ≈ᶜ-refl
      (polled _ _) (inj₂ (inj₁ _)) _ → ≈ᶜ-refl
      idle         (inj₁ _)        _ → ≈ᶜ-refl
      (sent _)     (inj₁ _)        _ → ≈ᶜ-refl
      (polled _ _) (inj₁ _)        _ → ≈ᶜ-refl }

otp≤idealᵈ : otp ≤UC ideal
otp≤idealᵈ = dummy-complete (sim , ≈ᵈ⇒≈ᵁ (≈ᵈ.trans (≈ᵖ⇒≈ᵈ (≲⇒≈ᵖ otp≲real))
  (≈ᵈ.trans (≈ᵈ.sym lazy≈real) (≈ᵈ.trans (≈ᵖ⇒≈ᵈ (≲⇒≈ᵖ lazy≲simulated)) (≈ᵈ.sym (≈ᵖ⇒≈ᵈ (≲⇒≈ᵖ ideal≲simulated)))))))
