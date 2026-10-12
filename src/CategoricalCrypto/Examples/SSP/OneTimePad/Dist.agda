{-# OPTIONS --safe --without-K #-}

-- Deferred sampling for the OTP, with separate results in `SSP.Setup`
-- (`otp≤idealᵈ`) and the distributional quotient `SSP.Dist.Setup`
-- (`otp≤ideal-dist`).  The latter includes the concrete simulator against
-- every adversary, ancilla, distinguisher and game, and reflects the
-- authenticated-channel impossibility.  See `docs/uc-setup-ssp-dist.md` §5.

module CategoricalCrypto.Examples.SSP.OneTimePad.Dist where

open import Data.Bool.Base
open import Data.Bool.Properties
open import Data.Bool.Properties.Ext
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Examples.SSP.OneTimePad
open import CategoricalCrypto.SSP.Dist
open import CategoricalCrypto.SSP.Dist.Kernel
open import CategoricalCrypto.SSP.Dist.Laws
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol

import CategoricalCrypto.SSP.Dist.Setup as SSPᵈ
import CategoricalCrypto.SSP.Setup as SSP

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

lazy : SSP.unit SSP.⇒ SSP.T₀ Eveᴵ Honᴵ
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

lazy≈real : lazy ≈ᵈ real
lazy≈real = defer draw (λ _ → refl) λ where
  idle         (inj₁ _)        _ → ≈ᵏ-refl
  (sent _)     (inj₁ _)        _ → ≈ᵏ-refl
  (polled _ _) (inj₁ _)        _ → ≈ᵏ-refl
  idle         (inj₂ (inj₁ _)) m → ≈ᵏ-trans
    (≈ᶜ⇒≈ᵏ (coin λ k → ret (cong (λ x → (just (m xor k) , just x) , tt)
                                 (sym (trans (xor-comm (m xor k) m) (xor-cancelˡ m k))))))
    (coin-xor m λ c → ret ((just c , just (c xor m)) , tt))
  (sent _)     (inj₂ (inj₁ _)) _ → ≈ᵏ-refl
  (polled _ _) (inj₂ (inj₁ _)) _ → ≈ᵏ-refl
  idle         (inj₂ (inj₂ _)) _ → ≈ᵏ-refl
  (sent m)     (inj₂ (inj₂ _)) _ →
    ≈ᶜ⇒≈ᵏ (coin λ c → ret (cong (λ x → (just c , just (c xor m)) , just x) (xor-cancelˡ c m)))
  (polled c m) (inj₂ (inj₂ _)) _ → ≈ᶜ⇒≈ᵏ (ret (cong (λ x → (just c , just (c xor m)) , just x) (xor-cancelˡ c m)))

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

otp≈idealᵈ : otp ≈ᵈ (SSP.sub sim SSP.∘ ideal)
otp≈idealᵈ = ≈ᵈ.trans (≈ᵖ⇒≈ᵈ (≲⇒≈ᵖ otp≲real))
  (≈ᵈ.trans (≈ᵈ.sym lazy≈real) (≈ᵈ.trans (≈ᵖ⇒≈ᵈ (≲⇒≈ᵖ lazy≲simulated)) (≈ᵈ.sym (≈ᵖ⇒≈ᵈ (≲⇒≈ᵖ ideal≲simulated)))))

otp≤idealᵈ : otp SSP.≤UC ideal
otp≤idealᵈ = SSP.dummy-complete (sim , ≈ᵈ⇒≈ᵁ otp≈idealᵈ)

------------------------------------------------------------------------
-- The actual distributional setup
------------------------------------------------------------------------

otp≤ideal-dist : otp SSPᵈ.≤UC ideal
otp≤ideal-dist = SSPᵈ.dummy-complete (sim , SSPᵈ.≈C⇒≈ᵁ otp≈idealᵈ)

otp≤ideal-image-dist : Transfer.G SSPᵈ.ssp⇒dist otp SSPᵈ.≤UC Transfer.G SSPᵈ.ssp⇒dist ideal
otp≤ideal-image-dist = SSPᵈ.preserves-≤UC otp≤idealᵈ

otp-simulator-dist : ∀ {X} (a : Protocol Eveᴵ X)
                   → (SSPᵈ.sub a SSPᵈ.∘ otp) SSPᵈ.≈ᵁ (SSPᵈ.sub (a ∘ᵖ sim) SSPᵈ.∘ ideal)
otp-simulator-dist a = proj₂ (otp≤ideal-dist a)

otp-observations-dist : ∀ {X} (a : Protocol Eveᴵ X) (W : Iface)
                      (D : Protocol ((W ⊗ᴵ X) ⊗ᴵ Honᴵ) Ωᴵ)
                      (G : Protocol unitᴵ (W ⊗ᴵ unitᴵ))
                    → runᵖ ((D ∘ᵖ SSPᵈ.prefix W (SSPᵈ.sub a SSPᵈ.∘ otp)) ∘ᵖ G)
                      SSP.S.≈
                      runᵖ ((D ∘ᵖ SSPᵈ.prefix W (SSPᵈ.sub (a ∘ᵖ sim) SSPᵈ.∘ ideal)) ∘ᵖ G)
otp-observations-dist a W D G = SSPᵈ.KE.run∼ (otp-simulator-dist a W) {D} G

leaky-not-secure-dist : ¬ (aut SSPᵈ.≤UC ideal)
leaky-not-secure-dist le = leaky-not-secure (SSPᵈ.dist≤⇒ssp≤ le)

leaky-no-simulator-dist : (s : Protocol (Pollᴵ Bool) Eveᴵ)
                        → ¬ (aut SSPᵈ.≈ᵁ (SSPᵈ.sub s SSPᵈ.∘ ideal))
leaky-no-simulator-dist s e = leaky-not-secure-dist (SSPᵈ.dummy-complete (s , e))
