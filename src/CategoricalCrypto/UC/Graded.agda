{-# OPTIONS --safe --without-K --guardedness #-}

-- Emulation at a NONTRIVIAL grade, from a machine-level factoring.
--
-- `UC.Seam.Grounded`'s `closedᵒ`/`stageᵒ` inflate a protocol image to the
-- TRIVIAL grade `𝟘ᴳ`, where every simulator is a scalar and provably blind
-- (`subBlind`).  The graded image is already there and needs no new relation:
-- `UC.Model.Seal.gradedᵒ` reads a `Proc A (X ⊗ᴵ B)` — a process carrying an
-- adversary interface `X` beside its honest one — as a hom
-- `ifaceᵒ A ⇒ T₀ (ifaceᵒ X) (ifaceᵒ B)`, which is what `_≤UC_` compares, and a
-- simulator `Proc Y X` is `procᵒ` of one.  What this module adds is the bridge
-- that makes such an emulation PROVABLE from the machine layer: a simulator in
-- front of a graded image is the relay `subᴵ` composed with it, so a factoring
-- of the real process through the simulator and the ideal one — one machine
-- equality — is an emulation at that grade, with no error at all.
--
-- The unit grade is the special case at `X = Y = 𝟭ᴵ`, in the sense that the
-- statements here are the `ιᴳ`-free ones and specialize to it; nothing in
-- `UC.Seam.Grounded` is weakened or re-proved.

open import Categories.Category using (Category; _[_≈_])

open import Data.Product.Base using (_,_)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; subᴵ′)
open import CategoricalCrypto.UC.Model.Graded using (sub-gradedᵒ; ≈ᴹ⇒≈ᵍ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup

module CategoricalCrypto.UC.Graded where

private
  module M = Category (𝒢ₚ 0ℓ)

  variable A B X Y : Iface

-- The factoring the emulation consumes: the real process IS the simulator's
-- relay in front of the ideal one, at the machine layer.  This is `𝒢ₚ`'s own
-- hom equality under a name, not a relation of its own — the simulator stays a
-- grade morphism `Y ⇒ X` acting through `sub`, and nothing here wraps it.
Factors : Proc A (X ⊗ᴵ B) → Proc Y X → Proc A (Y ⊗ᴵ B) → Set₁
Factors f s g = 𝒢ₚ 0ℓ [ f ≈ M._∘_ (subᴵ′ s) g ]

-- `UC.Model.Graded.sub-gradedᵒ` in the grading's vocabulary: `sub c` is
-- `c ⊗₁ id` on the nose (`CurriedTensor.Properties.sub-⊗`), so no step is
-- spent here.
sub-graded : (s : Proc Y X) (g : Proc A (Y ⊗ᴵ B))
           → sub (procᵒ s) ∘ gradedᵒ g ≈ gradedᵒ (M._∘_ (subᴵ′ s) g)
sub-graded = sub-gradedᵒ

emulᵍ : {f : Proc A (X ⊗ᴵ B)} {s : Proc Y X} {g : Proc A (Y ⊗ᴵ B)}
      → Factors f s g → gradedᵒ f ≈ᵁ sub (procᵒ s) ∘ gradedᵒ g
emulᵍ {s = s} {g} e = ≈C⇒≈ᵁ (Equiv.trans (≈ᴹ⇒≈ᵍ e) (Equiv.sym (sub-graded s g)))

-- …hence an emulation in the INHERITED order, at the grade `ifaceᵒ X` and with
-- the simulator `procᵒ s`, whose interface is `ifaceᵒ Y`.
≤UCᵍ : {f : Proc A (X ⊗ᴵ B)} {s : Proc Y X} {g : Proc A (Y ⊗ᴵ B)}
     → Factors f s g → gradedᵒ f ≤UC gradedᵒ g
≤UCᵍ {s = s} e = dummy-complete (procᵒ s , emulᵍ e)
