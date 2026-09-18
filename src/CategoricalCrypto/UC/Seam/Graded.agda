{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Graded`'s emulation with the simulator's query budget attached.
--
-- `UC.Audit._≤UC[_]_` is the premise the graded carry consumes, and the two
-- halves it wants are already separate: the query bound is the machine layer's
-- (`UC.QueryBound.QB`, crossed by `UC.Model.Enrichment.qbᵒ`) and the agreement
-- is `emulᵍ`'s, read into the core's kernel by `UC.Model.Setup.≈ᵁ⇒≈ℰᶜ`.  Its
-- own module because it is the first thing in the graded cone that imports the
-- seam.

open import Data.Nat.Base using (ℕ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Graded using (Factors; emulᵍ)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Model.Enrichment using (qbᵒ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup using (≈ᵁ⇒≈ℰᶜ)
open import CategoricalCrypto.UC.QueryBound using (QB)
open import CategoricalCrypto.UC.Seam.Audit using (_≤UC[_]_)

module CategoricalCrypto.UC.Seam.Graded where

≤UC[]ᵍ : {A B X Y : Iface} {f : Proc A (X ⊗ᴵ B)} {s : Proc Y X} {g : Proc A (Y ⊗ᴵ B)}
         {c : ℕ} → QB c s → Factors f s g → gradedᵒ f ≤UC[ c ] gradedᵒ g
≤UC[]ᵍ {s = s} q e =
  record { sim = procᵒ s ; sim-qb = qbᵒ q ; emulate = ≈ᵁ⇒≈ℰᶜ (emulᵍ e) }
