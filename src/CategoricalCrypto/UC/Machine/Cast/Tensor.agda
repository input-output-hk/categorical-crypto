{-# OPTIONS --safe --without-K --guardedness #-}

-- Reading a `𝒫ᴵ`-composite as the 𝒢-composite it definitionally is, at the two
-- shapes `⊗.homomorphism` is stated at.
--
-- `𝒫ᴵ`'s composition IS `𝒢ₚ`'s at `⟦_⟧ᴵ`-spelled objects, so both equations are
-- `Equiv.refl`.  What they buy is the SPELLING: a 𝒢-monoidal law states its
-- composite at `_⊗₀_`-spelled objects, the machine layer states its own at
-- `⟦_⟧ᴵ`-spelled ones, and the elaborator has to reconcile the two somewhere.
--
-- Where it does is the whole cost question, and the answer decides this cone's
-- shape:
--
--   * with the two factors left VARIABLE the reconciliation is affordable — the
--     ⊕-trace both sides reduce to has variable leaves, so the comparison stays
--     structural.
--   * with the factors CONCRETE it is not.  `𝔾.associator.isoʳ` given its own
--     type, every implicit pinned, burns 7 min of CPU without returning (M4
--     measured the same at 900 s / 12.8 GiB, and called it the branch's gate).
--
-- So every conversion in this cone happens in a `…Cast.*` module, once per
-- composite shape, at variable factors; a law is then
-- `Dictionary bridge ○ cast ○ 𝒢-law`, in which every step is a plain
-- application.  That is also why there is one cast per shape rather than one
-- general cast: a general one would leave the tensor spelling to be reconciled
-- at the law, where the factors are concrete.
--
-- One shape per module is measured, not tidy (house rule 31): the five casts in
-- one module run past `pagda`'s 900 s cap.  Measured warm, single module, on a
-- contended gate: 997 s here, 418 s for `…Cast.Assoc`, 822 s for `…Cast.Nat` —
-- two conversions in this one, one and two there, at ~400–450 s apiece.  All of
-- that is the comparison; none of it is a proof step.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚᴹ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ)

module CategoricalCrypto.UC.Machine.Cast.Tensor where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

-- The ancilla on the left…
∘ᴳ-T₁ : (Y A B C : Iface)
        (g : Proc (Y ⊗ᴵ B) (Y ⊗ᴵ C)) (f : Proc (Y ⊗ᴵ A) (Y ⊗ᴵ B))
      → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ C}
          (𝒫._∘_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Y ⊗ᴵ C} g f)
          (𝔾._∘_ {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ}
                 {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ B ⟧ᴵ}
                 {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ C ⟧ᴵ} g f)
∘ᴳ-T₁ Y A B C g f = 𝒫.Equiv.refl {Y ⊗ᴵ A} {Y ⊗ᴵ C}

-- …and on the right.
∘ᴳ-sub : (X Y Z A : Iface)
         (t : Proc (Y ⊗ᴵ A) (Z ⊗ᴵ A)) (s : Proc (X ⊗ᴵ A) (Y ⊗ᴵ A))
       → 𝒫._≈_ {X ⊗ᴵ A} {Z ⊗ᴵ A}
           (𝒫._∘_ {X ⊗ᴵ A} {Y ⊗ᴵ A} {Z ⊗ᴵ A} t s)
           (𝔾._∘_ {𝔾._⊗₀_ ⟦ X ⟧ᴵ ⟦ A ⟧ᴵ}
                  {𝔾._⊗₀_ ⟦ Y ⟧ᴵ ⟦ A ⟧ᴵ}
                  {𝔾._⊗₀_ ⟦ Z ⟧ᴵ ⟦ A ⟧ᴵ} t s)
∘ᴳ-sub X Y Z A t s = 𝒫.Equiv.refl {X ⊗ᴵ A} {Z ⊗ᴵ A}
