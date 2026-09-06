{-# OPTIONS --safe --without-K --guardedness #-}

-- Where the pinned relays meet the derived grading.
--
-- The grading itself is `UC.Machine.gradingᴹ` and comes for free; there is no
-- `GradingLawsᴹ` any more and no `Cast`/`Laws` cone under it — `UC.Machine`'s
-- header prices why.  What is left is the resource layer: a `UC.QueryBound`
-- certificate is about the pinned relay (`T₁ᴵ`/`subᴵ`/`a⇒ᴵ`/`a⇐ᴵ`), the
-- grading's action is `_⊗₁_` with an identity and the 𝒢-associator, and
-- `UC.Machine.Dictionary`'s zigzags carry one to the other through
-- `qb-resp-≈`.  Those four are the entire content the retired cone was buying.
--
-- Each is stated in pure `Iface` vocabulary, and that is measured: with the
-- objects re-indexed through `retᴵ` in the STATEMENT a re-basing costs 42 s —
-- one `Proc` inversion per re-indexed object — and stated at `Iface`, 5.9 s.
-- Re-indexing belongs at a use site, which is the medicine
-- `UC.QueryBound.Certified` already takes one level down.
--
-- A `Budget (𝒢ₚ 0ℓ) gradingᴹ` assembly is OWED, not built, and the reason is
-- the same inversion counted nine times: the record's nine fields each
-- re-index their objects, measured at >250 s together against `Compose.Laws`'
-- ~55 s per field for four.  Inhabiting it needs `UC.QueryBound`'s `QB` and
-- `Certified` indexed by 𝒢's objects rather than by `Iface`, which is a
-- generalization of their statements and a separate change.

open import Categories.Category using (Category; _[_≈_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚᴹ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.Machine.Grading where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

qb-T₁ᴳ : ({Y A B : Iface} {f g : Proc A B} → 𝒫ᴵ [ f ≈ g ] → 𝒫ᴵ [ T₁ᴵ Y f ≈ T₁ᴵ Y g ])
       → (Y A B : Iface) {c : ℕ} (f : Proc A B)
       → QB c f
       → QB (c ℕ.⊔ 1) (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f)
qb-T₁ᴳ resp Y A B f q =
  qb-resp-≈ (T₁-⊗₁ {Y} {A} {B} f) (qb-T₁ᴹ resp Y A B f q)

qb-subᴳ : ({X Y A : Iface} {s t : Proc X Y} → 𝒫ᴵ [ s ≈ t ] → 𝒫ᴵ [ subᴵ s {A} ≈ subᴵ t ])
        → (X Y A : Iface) {c : ℕ} (s : Proc X Y)
        → QB c s
        → QB (c ℕ.⊔ 1) (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ A ⟧ᴵ} s (𝒫.id {A}))
qb-subᴳ resp X Y A s q =
  qb-resp-≈ (sub-⊗₁ {X} {Y} {A} s) (qb-subᴹ resp X Y A s q)

qb-a⇒ᴳ : (X Y A : Iface) → QB 1 (𝔾.associator.to {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
qb-a⇒ᴳ X Y A =
  qb-resp-≈ (a⇒-α⇐ {X} {Y} {A})
    (certified⇒QB (qbᵢ-wire {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A} ⊎assocˡ ⊎assocʳ))

qb-a⇐ᴳ : (X Y A : Iface) → QB 1 (𝔾.associator.from {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
qb-a⇐ᴳ X Y A =
  qb-resp-≈ (a⇐-α⇒ {X} {Y} {A})
    (certified⇒QB (qbᵢ-wire {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)} ⊎assocʳ ⊎assocˡ))
