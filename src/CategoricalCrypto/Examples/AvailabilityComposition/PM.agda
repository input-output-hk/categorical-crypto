{-# OPTIONS --safe --without-K --guardedness #-}

open import Categories.Category
open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Rational.Base using (0ℚ; _+_)
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (id)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (point-⊛)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.Tensor
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Model.Quantitative
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Seal.Monoidal
open import CategoricalCrypto.UC.Quantitative.Availability.Composition ℚ-ordered

import CategoricalCrypto.Examples.RandomSystems.Availability as Bits
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Model.Availability.Composition as PM

module CategoricalCrypto.Examples.AvailabilityComposition.PM where

module Honest = Serial QSetupᵒ
open Honest

private
  module G = MonoidalCategory 𝔾ᵒ
  module P = Category 𝒫ᴵ
  module M = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

flipᴹ : Proc Ωᴵ Ωᴵ
flipᴹ = wireᴹ not id

flip : ifaceᵒ Ωᴵ G.⇒ T₀ G.unit (ifaceᵒ Ωᴵ)
flip = G.unitorˡ.to G.∘ procᵒ flipᴹ

server : SecureAvailable 0ℚ 0ℚ (Bits.mode false) (Bits.mode true) (Bits.adapted not) Bits.ideal
server = secure-mode-preserving {s = Bits.adaptᵒ not} (Bits.mode-adapt-hom false not) ctx-refl

other-server : SecureAvailable 0ℚ 0ℚ (Bits.mode true) (Bits.mode false) (Bits.adapted not) Bits.ideal
other-server = secure-mode-preserving {s = Bits.adaptᵒ not} (Bits.mode-adapt-hom true not) ctx-refl

converter : SecureAvailable 0ℚ 0ℚ G.id G.id flip flip
converter = secure-mode-preserving {s = G.id} G.identityˡ
  (ctx-resp G.Equiv.refl (G.Equiv.sym (sub-identityˡ flip)) ctx-refl)

honest-serial : SecureAvailable (0ℚ + 0ℚ) (0ℚ + 0ℚ)
  (cap-compose (Bits.mode false) G.id) (cap-compose (Bits.mode true) G.id)
  (flip ∙ Bits.adapted not) (flip ∙ Bits.ideal)
honest-serial = secure-compose server converter

honest-serial-availability : Availability (0ℚ + 0ℚ)
  (cap-compose (Bits.mode false) G.id) (cap-compose (Bits.mode true) G.id)
  (flip ∙ Bits.adapted not) (flip ∙ Bits.ideal)
honest-serial-availability = availability-compose (SecureAvailable.availability server)
  (SecureAvailable.availability converter)

serial-mode-square :
  (cap-compose (Bits.mode false) G.id G.∘ ((G.id G.⊗₁ G.id) G.∘ (Bits.adaptᵒ not G.⊗₁ G.id)))
  G.≈ cap-compose (Bits.mode true) G.id
serial-mode-square = mode-compose (Bits.mode-adapt-hom false not) G.identityˡ

flip-bit : (b : Bool) → P._≈_ {unitᴵ} {Ωᴵ} (P._∘_ {unitᴵ} {Ωᴵ} {Ωᴵ} flipᴹ (Bits.bitᴹ b)) (Bits.bitᴹ (not b))
flip-bit b = wire-∘ᴹ {unitᴵ} {Ωᴵ} {Ωᴵ} not id (Bits.bitᴹ b)
  S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
    (_ , inj₁ ())
    (s , inj₂ tt) → >>=ₚ-identityˡ (s , inj₂ b) _)

flip-bitᵒ : (b : Bool) → (procᵒ flipᴹ G.∘ procᵒ (Bits.bitᴹ b)) G.≈ procᵒ (Bits.bitᴹ (not b))
flip-bitᵒ b = G.Equiv.trans (G.Equiv.sym (procᵒ-∘ flipᴹ (Bits.bitᴹ b))) (≈ᴹ⇒≈ᵒ (flip-bit b))

flip-bit-run : (b : Bool) → runˢ (P._∘_ {unitᴵ} {Ωᴵ} {Ωᴵ} flipᴹ (Bits.bitᴹ b)) Bits.tell ≈ₚ returnₚ (not b)
flip-bit-run b = runˢ-resp-≈ᴹ (flip-bit b) Bits.tell ⟨≈⟩ Bits.bit-run (not b)

flip-closed : (G.unitorˡ.from G.∘ close G.id flip) G.≈ procᵒ flipᴹ
flip-closed = G.Equiv.trans (G.∘-resp-≈ʳ (sub-identityˡ flip))
  (G.Equiv.trans G.sym-assoc
    (G.Equiv.trans (G.∘-resp-≈ˡ G.unitorˡ.isoʳ) G.identityˡ))

adapted-closed : (b : Bool)
               → (G.unitorˡ.from G.∘ close (Bits.mode b) (Bits.adapted not))
                 G.≈ procᵒ (Bits.bitᴹ (not b))
adapted-closed b = G.Equiv.trans
  (G.∘-resp-≈ʳ (G.Equiv.trans G.sym-assoc
    (G.Equiv.trans (G.∘-resp-≈ˡ (G.Equiv.sym sub-homomorphism))
      (close-resp-cap Bits.ideal (Bits.mode-adapt-hom b not)))))
  (Bits.mode-bit (not b))

serial-real-closed : (b : Bool)
                  → (G.unitorˡ.from G.∘ close (cap-compose (Bits.mode b) G.id) (flip ∙ Bits.adapted not))
                    G.≈ procᵒ (Bits.bitᴹ (not (not b)))
serial-real-closed b = G.Equiv.trans
  (PM.no-adversary-compose (Bits.mode b) G.id (Bits.adapted not) flip)
  (G.Equiv.trans (G.∘-resp-≈ flip-closed (adapted-closed b)) (flip-bitᵒ (not b)))

serial-ideal-closed : (b : Bool)
                   → (G.unitorˡ.from G.∘ close (cap-compose (Bits.mode b) G.id) (flip ∙ Bits.ideal))
                     G.≈ procᵒ (Bits.bitᴹ (not b))
serial-ideal-closed b = G.Equiv.trans
  (PM.no-adversary-compose (Bits.mode b) G.id Bits.ideal flip)
  (G.Equiv.trans (G.∘-resp-≈ flip-closed (Bits.mode-bit b)) (flip-bitᵒ b))

opaque
  unfolding procᵒ unprocᵒ

  honest-serial-reply :
    runˢ (unprocᵒ (G.unitorˡ.from G.∘ close (cap-compose (Bits.mode false) G.id)
      (flip ∙ Bits.adapted not))) Bits.tell ≈ₚ returnₚ false
  honest-serial-reply = runˢ-resp-≈ᴹ (≈ᵒ⇒≈ᴹ (serial-real-closed false)) Bits.tell
    ⟨≈⟩ Bits.bit-run false

  honest-serial-ideal-reply :
    runˢ (unprocᵒ (G.unitorˡ.from G.∘ close (cap-compose (Bits.mode true) G.id)
      (flip ∙ Bits.ideal))) Bits.tell ≈ₚ returnₚ false
  honest-serial-ideal-reply = runˢ-resp-≈ᴹ (≈ᵒ⇒≈ᴹ (serial-ideal-closed true)) Bits.tell
    ⟨≈⟩ Bits.bit-run false

module Together = PM.QParallelᵒ

honest-parallel : SecureAvailable (0ℚ + 0ℚ) (0ℚ + 0ℚ)
  (cap-compose (Bits.mode false) (Bits.mode true))
  (cap-compose (Bits.mode true) (Bits.mode false))
  (Together.pair (Bits.adapted not) (Bits.adapted not)) (Together.pair Bits.ideal Bits.ideal)
honest-parallel = Together.secure-parallel server other-server

honest-parallel-availability : Availability (0ℚ + 0ℚ)
  (cap-compose (Bits.mode false) (Bits.mode true))
  (cap-compose (Bits.mode true) (Bits.mode false))
  (Together.pair (Bits.adapted not) (Bits.adapted not)) (Together.pair Bits.ideal Bits.ideal)
honest-parallel-availability = Together.availability-parallel
  (SecureAvailable.availability server) (SecureAvailable.availability other-server)

parallel-mode-square :
  (cap-compose (Bits.mode false) (Bits.mode true) G.∘ (Bits.adaptᵒ not G.⊗₁ Bits.adaptᵒ not))
  G.≈ cap-compose (Bits.mode true) (Bits.mode false)
parallel-mode-square = Together.mode-parallel
  (Bits.mode-adapt-hom false not) (Bits.mode-adapt-hom true not)

parallel-real-closed : (b c : Bool)
  → (G.unitorˡ.from G.∘ close (cap-compose (Bits.mode b) (Bits.mode c))
      (Together.pair (Bits.adapted not) (Bits.adapted not)))
    G.≈ tensorᵒ (tensorᴹ (Bits.bitᴹ (not b)) (Bits.bitᴹ (not c)))
parallel-real-closed b c = G.Equiv.trans
  (PM.no-adversary-parallel (Bits.mode b) (Bits.mode c) (Bits.adapted not) (Bits.adapted not))
  (G.Equiv.trans (G.⊗.F-resp-≈ (adapted-closed b , adapted-closed c))
    (procᵒ-tensor (Bits.bitᴹ (not b)) (Bits.bitᴹ (not c))))

parallel-ideal-closed : (b c : Bool)
  → (G.unitorˡ.from G.∘ close (cap-compose (Bits.mode b) (Bits.mode c))
      (Together.pair Bits.ideal Bits.ideal))
    G.≈ tensorᵒ (tensorᴹ (Bits.bitᴹ b) (Bits.bitᴹ c))
parallel-ideal-closed b c = G.Equiv.trans
  (PM.no-adversary-parallel (Bits.mode b) (Bits.mode c) Bits.ideal Bits.ideal)
  (G.Equiv.trans (G.⊗.F-resp-≈ (Bits.mode-bit b , Bits.mode-bit c))
    (procᵒ-tensor (Bits.bitᴹ b) (Bits.bitᴹ c)))

pair-tell : Strat (Pos (unitᴵ ⊗ᴵ unitᴵ) ⊎ Neg (Ωᴵ ⊗ᴵ Ωᴵ))
                  (Neg (unitᴵ ⊗ᴵ unitᴵ) ⊎ Pos (Ωᴵ ⊗ᴵ Ωᴵ))
pair-tell = ask (inj₂ (inj₁ tt)) λ where
  (inj₁ (inj₁ ()))
  (inj₁ (inj₂ ()))
  (inj₂ (inj₂ _)) → out false
  (inj₂ (inj₁ b)) → ask (inj₂ (inj₂ tt)) λ where
    (inj₁ (inj₁ ()))
    (inj₁ (inj₂ ()))
    (inj₂ (inj₁ _)) → out false
    (inj₂ (inj₂ c)) → out (b ∧ not c)

paired-bit-run : (b c : Bool)
  → runˢ (tensorᴹ (Bits.bitᴹ b) (Bits.bitᴹ c)) pair-tell ≈ₚ returnₚ (b ∧ not c)
paired-bit-run b c =
  bindˣ (point-⊛ M.Iˢ M.Iˢ ttᵛ
    ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _ ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _)
  ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , ttᵛ) _
  ⟨≈⟩ bindˣ (tensor-stepˡ (Bits.bitᴹ b) (Bits.bitᴹ c) ttᵛ ttᵛ tt
    ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , inj₂ b) _)
  ⟨≈⟩ >>=ₚ-identityˡ ((ttᵛ , ttᵛ) , inj₂ (inj₁ b)) _
  ⟨≈⟩ bindˣ (tensor-stepʳ (Bits.bitᴹ b) (Bits.bitᴹ c) ttᵛ ttᵛ tt
    ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , inj₂ c) _)
  ⟨≈⟩ >>=ₚ-identityˡ ((ttᵛ , ttᵛ) , inj₂ (inj₂ c)) _

opaque
  unfolding tensorᵒ untensorᵒ

  honest-parallel-reply :
    runˢ (untensorᵒ (G.unitorˡ.from G.∘ close (cap-compose (Bits.mode false) (Bits.mode true))
      (Together.pair (Bits.adapted not) (Bits.adapted not)))) pair-tell ≈ₚ returnₚ true
  honest-parallel-reply =
    runˢ-resp-≈ᴹ (≈⊗ᵒ⇒≈ᴹ (parallel-real-closed false true)) pair-tell
    ⟨≈⟩ paired-bit-run true false

  honest-parallel-ideal-reply :
    runˢ (untensorᵒ (G.unitorˡ.from G.∘ close (cap-compose (Bits.mode true) (Bits.mode false))
      (Together.pair Bits.ideal Bits.ideal))) pair-tell ≈ₚ returnₚ true
  honest-parallel-ideal-reply =
    runˢ-resp-≈ᴹ (≈⊗ᵒ⇒≈ᴹ (parallel-ideal-closed true false)) pair-tell
    ⟨≈⟩ paired-bit-run true false
