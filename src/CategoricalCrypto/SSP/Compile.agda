{-# OPTIONS --safe --without-K #-}

-- Compiling a channel-indexed protocol to a flat one, the machine layer's wire
-- format (`docs/uc-setup-ssp.md` §3.1).  A query is tagged with its channel,
-- and a reply is checked against the open call's channel, a mismatch being
-- `dead`: CryptHOL's respectfulness (lochbihler2019cc Def. 3), checked at run
-- time.  Compilation preserves simulation and composition, so the compiled
-- semantics `morphism ∘ toProtocol` respects `≈ᵖ` (`Protocol.Machine.Resp`)
-- and `∘ᵖ` (`Protocol.Machine.Compose`), but not the identity
-- (`docs/uc-setup-ssp.md` §4.1).

open import Class.DecEq
open import Data.Product.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core
import Relation.Binary.Construct.Closure.Equivalence as EqC

import CategoricalCrypto.Protocol as Flat
import CategoricalCrypto.Protocol.Sim as FlatSim
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol

module CategoricalCrypto.SSP.Compile where

private variable
  A B C : Iface
  S S′ X Y Z : Set

module _ ⦃ _ : DecEq (Ch A) ⦄ where

  -- The continuation of a call on `c`, at a reply on `c′`.
  reply : {c c′ : Ch A} → Dec (c′ ≡ c) → R A c′ → (R A c → Flat.Calls (flat A) X) → Flat.Calls (flat A) X
  reply (yes refl) r k = k r
  reply (no _)     _ _ = Flat.dead

  reply-refl : {c : Ch A} (r : R A c) (k : R A c → Flat.Calls (flat A) X) → reply (c ≟ c) r k ≡ k r
  reply-refl r k = cong (λ d → reply d r k) (≡-≟-identity _≟_ refl)

  reply-≈ : (F : Flat.Calls (flat A) X → Flat.Calls (flat A) Z)
            (G : Flat.Calls (flat A) Y → Flat.Calls (flat A) Z)
            {c c′ : Ch A} (d : Dec (c′ ≡ c)) (r : R A c′)
            {k : R A c → Flat.Calls (flat A) X} {k′ : R A c → Flat.Calls (flat A) Y}
          → (∀ r → F (k r) FlatSim.≈ᶜ G (k′ r)) → F Flat.dead FlatSim.≈ᶜ G Flat.dead
          → F (reply d r k) FlatSim.≈ᶜ G (reply d r k′)
  reply-≈ F G (yes refl) r h _ = h r
  reply-≈ F G (no _)     r _ z = z

  toCalls : Calls A X → Flat.Calls (flat A) X
  toCalls (ret x)      = Flat.ret x
  toCalls (call c q k) = Flat.call (c , q) λ (c′ , r) → reply (c′ ≟ c) r λ r → toCalls (k r)
  toCalls (coin μ k)   = Flat.coin μ λ b → toCalls (k b)
  toCalls dead         = Flat.dead

  -- A step simulation survives compilation and re-pairing the leaves.
  toCalls-sim : {θ : S → S′} {F : S × Y → X} {F′ : S′ × Y → Z} {G : X → Z}
              → (∀ x → G (F x) ≡ F′ (map₁ θ x))
              → (t : Calls A (S × Y)) {t′ : Calls A (S′ × Y)} → mapᶜ (map₁ θ) t ≈ᶜ t′
              → toCalls (mapᶜ F t) Flat.>>=ᶜ (Flat.ret ∘ G) FlatSim.≈ᶜ toCalls (mapᶜ F′ t′)
  toCalls-sim         h (ret x)      (ret refl) = FlatSim.ret (h x)
  toCalls-sim {G = G} h (call c _ k) (call e)   = FlatSim.call λ (c′ , r) →
    reply-≈ (Flat._>>=ᶜ (Flat.ret ∘ G)) id (c′ ≟ c) r (λ r → toCalls-sim h (k r) (e r)) FlatSim.dead
  toCalls-sim         h (coin _ k)   (coin e)   = FlatSim.coin λ x → toCalls-sim h (k x) (e x)
  toCalls-sim         h dead         dead       = FlatSim.dead

  toProtocol : Protocol A B → Flat.Protocol (flat A) (flat B)
  toProtocol P = record
    { St   = St P
    ; init = init P
    ; step = λ s (c , q) → toCalls (mapᶜ (map₂ (c ,_)) (step P s c q)) }

  toProtocol-sim : {P P′ : Protocol A B} → P ≲ᵖ P′ → toProtocol P FlatSim.≲ᵖ toProtocol P′
  toProtocol-sim {P = P} σ = record
    { θ      = θ σ
    ; θ-init = θ-init σ
    ; θ-step = λ s (c , q) → toCalls-sim (λ _ → refl) (step P s c q) (θ-step σ s c q) }

  toProtocol-resp : {P P′ : Protocol A B} → P ≈ᵖ P′ → toProtocol P FlatSim.≈ᵖ toProtocol P′
  toProtocol-resp = EqC.gmap toProtocol toProtocol-sim

module _ ⦃ _ : DecEq (Ch A) ⦄ ⦃ _ : DecEq (Ch B) ⦄ (P₂ : Protocol B C) (P₁ : Protocol A B) where

  private
    mutual
      graft-toCalls : {c : Ch C} (t : Calls B (St P₂ × R C c)) (s₁ : St P₁)
                    → toCalls (mapᶜ (map₂ (c ,_)) (graft P₂ P₁ t s₁)) Flat.>>=ᶜ (Flat.ret ∘ map₁ id)
                      FlatSim.≈ᶜ Flat.graft (toProtocol P₂) (toProtocol P₁) (toCalls (mapᶜ (map₂ (c ,_)) t)) s₁
      graft-toCalls (ret _)      s₁ = FlatSim.ret refl
      graft-toCalls (call b q k) s₁ = serve-toCalls k (step P₁ s₁ b q)
      graft-toCalls (coin _ k)   s₁ = FlatSim.coin λ x → graft-toCalls (k x) s₁
      graft-toCalls dead         s₁ = FlatSim.dead

      serve-toCalls : {c : Ch C} {b : Ch B} (k : R B b → Calls B (St P₂ × R C c)) (u : Calls A (St P₁ × R B b))
                    → toCalls (mapᶜ (map₂ (c ,_)) (serve P₂ P₁ k u)) Flat.>>=ᶜ (Flat.ret ∘ map₁ id)
                      FlatSim.≈ᶜ Flat.serve (toProtocol P₂) (toProtocol P₁)
                                   (λ (b′ , r) → reply (b′ ≟ b) r λ r → toCalls (mapᶜ (map₂ (c ,_)) (k r)))
                                   (toCalls (mapᶜ (map₂ (b ,_)) u))
      serve-toCalls {c} k (ret (s₁ , r)) =
        subst (λ t → _ FlatSim.≈ᶜ Flat.graft (toProtocol P₂) (toProtocol P₁) t s₁)
              (sym (reply-refl r λ r → toCalls (mapᶜ (map₂ (c ,_)) (k r))))
              (graft-toCalls (k r) s₁)
      serve-toCalls k (call a q k′) = FlatSim.call λ (a′ , r) →
        reply-≈ (Flat._>>=ᶜ (Flat.ret ∘ map₁ id)) (Flat.serve (toProtocol P₂) (toProtocol P₁) _)
                (a′ ≟ a) r (λ r → serve-toCalls k (k′ r)) FlatSim.dead
      serve-toCalls k (coin _ k′) = FlatSim.coin λ x → serve-toCalls k (k′ x)
      serve-toCalls k dead        = FlatSim.dead

  toProtocol-∘ : toProtocol (P₂ ∘ᵖ P₁) FlatSim.≲ᵖ toProtocol P₂ Flat.∘ᵖ toProtocol P₁
  toProtocol-∘ = record
    { θ      = id
    ; θ-init = refl
    ; θ-step = λ (s₂ , s₁) (c , q) → graft-toCalls (step P₂ s₂ c q) s₁ }
