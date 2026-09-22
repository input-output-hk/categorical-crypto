{-# OPTIONS --safe --without-K --guardedness #-}

-- The hole wire's interchange: a closed ancilla wired in beside the hole
-- crosses a relay ON the hole.  The closure acts on the ancilla leg and the
-- relay on the hole, so the two cross, and every other factor is a wire; the
-- only facts it spends are the hole wire's naturality and its triangle
-- (`UC.Machine.Slide`'s `λ-nat` and `λ-tri`).
--
-- Its own module because the chain below is monoidal reasoning in 𝒢, and its
-- elaborated form is a measured 17 s that every importer of
-- `UC.Machine.Slide` — `Monitor.Agree` and `Monitor.Tight` among them — would
-- otherwise deserialize for a lemma only `Monitor.Slide` uses.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒢ₚᴹ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇐)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁; sub-⊗₁; a⇒-α⇐)
open import CategoricalCrypto.UC.Machine.Slide using (λ-nat; λ-tri)

import Categories.Category.Monoidal.Reasoning as MR
import Categories.Category.Monoidal.Utilities as MU
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Slide.Relay where

private
  module 𝒫 = Category 𝒫ᴵ
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

open MR 𝔾.monoidal
open MU.Shorthands 𝔾.monoidal using () renaming (α⇐ to α⇐ᴳ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

relay-slide : {Y B F : Iface} (w : Proc unitᴵ Y) (μ : Proc B (B ⊗ᴵ F))
            → 𝒫._≈_ {B} {(Y ⊗ᴵ B) ⊗ᴵ F}
                (a⇒ᴵ 𝒫.∘ (T₁ᴵ Y μ 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐)))
                (subᴵ (subᴵ w 𝒫.∘ λᴵ⇐) 𝒫.∘ μ)
relay-slide {Y} {B} {F} w μ = begin
  a⇒ᴵ 𝒫.∘ (T₁ᴵ Y μ 𝒫.∘ (subᴵ w 𝒫.∘ λᴵ⇐))
    ≈⟨ 𝒫.∘-resp-≈ (a⇒-α⇐ {Y} {B} {F})
         (𝒫.∘-resp-≈ (T₁-⊗₁ {Y} μ) (𝒫.∘-resp-≈ˡ (sub-⊗₁ {unitᴵ} {Y} {B} w))) ⟩
  α⇐ᴳ 𝒫.∘ (𝔾._⊗₁_ (𝒫.id {Y}) μ 𝒫.∘ (𝔾._⊗₁_ w (𝒫.id {B}) 𝒫.∘ λᴵ⇐))
    ≈⟨ refl⟩∘⟨ 𝒫.sym-assoc ⟩
  α⇐ᴳ 𝒫.∘ ((𝔾._⊗₁_ (𝒫.id {Y}) μ 𝒫.∘ 𝔾._⊗₁_ w (𝒫.id {B})) 𝒫.∘ λᴵ⇐)
    ≈⟨ refl⟩∘⟨ (⟺ serialize₂₁ ⟩∘⟨refl) ⟩
  α⇐ᴳ 𝒫.∘ (𝔾._⊗₁_ w μ 𝒫.∘ λᴵ⇐)
    ≈⟨ refl⟩∘⟨ (serialize₁₂ ⟩∘⟨refl) ⟩
  α⇐ᴳ 𝒫.∘ ((𝔾._⊗₁_ w (𝒫.id {B ⊗ᴵ F}) 𝒫.∘ 𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ) 𝒫.∘ λᴵ⇐)
    ≈⟨ refl⟩∘⟨ 𝒫.assoc ⟩
  α⇐ᴳ 𝒫.∘ (𝔾._⊗₁_ w (𝒫.id {B ⊗ᴵ F}) 𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐))
    ≈⟨ 𝒫.sym-assoc ⟩
  (α⇐ᴳ 𝒫.∘ 𝔾._⊗₁_ w (𝒫.id {B ⊗ᴵ F})) 𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐)
    ≈⟨ (refl⟩∘⟨ (refl⟩⊗⟨ ⟺ 𝔾.⊗.identity)) ⟩∘⟨refl ⟩
  (α⇐ᴳ 𝒫.∘ 𝔾._⊗₁_ w (𝔾._⊗₁_ (𝒫.id {B}) (𝒫.id {F})))
    𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐)
    ≈⟨ 𝔾.assoc-commute-to ⟩∘⟨refl ⟩
  (𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ α⇐ᴳ)
    𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐)
    ≈⟨ 𝒫.assoc ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F})
    𝒫.∘ (α⇐ᴳ 𝒫.∘ (𝔾._⊗₁_ (𝒫.id {unitᴵ}) μ 𝒫.∘ λᴵ⇐))
    ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ (λ-nat μ ○ᴹ 𝒫.∘-resp-≈ˡ (T₁-⊗₁ {unitᴵ} μ))) ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ (α⇐ᴳ 𝒫.∘ (λᴵ⇐ 𝒫.∘ μ))
    ≈⟨ refl⟩∘⟨ 𝒫.sym-assoc ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ ((α⇐ᴳ 𝒫.∘ λᴵ⇐) 𝒫.∘ μ)
    ≈˘⟨ refl⟩∘⟨ ((a⇒-α⇐ {unitᴵ} {B} {F} ⟩∘⟨refl) ⟩∘⟨refl) ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ ((a⇒ᴵ 𝒫.∘ λᴵ⇐) 𝒫.∘ μ)
    ≈⟨ refl⟩∘⟨ (λ-tri ⟩∘⟨refl) ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ (subᴵ λᴵ⇐ 𝒫.∘ μ)
    ≈⟨ refl⟩∘⟨ (sub-⊗₁ {B} {unitᴵ ⊗ᴵ B} {F} λᴵ⇐ ⟩∘⟨refl) ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ (𝔾._⊗₁_ λᴵ⇐ (𝒫.id {F}) 𝒫.∘ μ)
    ≈⟨ 𝒫.sym-assoc ⟩
  (𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B})) (𝒫.id {F}) 𝒫.∘ 𝔾._⊗₁_ λᴵ⇐ (𝒫.id {F})) 𝒫.∘ μ
    ≈˘⟨ 𝔾.⊗.homomorphism ⟩∘⟨refl ⟩
  𝔾._⊗₁_ (𝔾._⊗₁_ w (𝒫.id {B}) 𝒫.∘ λᴵ⇐) (𝒫.id {F} 𝒫.∘ 𝒫.id {F}) 𝒫.∘ μ
    ≈⟨ ((⟺ (sub-⊗₁ {unitᴵ} {Y} {B} w) ⟩∘⟨refl) ⟩⊗⟨ 𝒫.identity²) ⟩∘⟨refl ⟩
  𝔾._⊗₁_ (subᴵ w 𝒫.∘ λᴵ⇐) (𝒫.id {F}) 𝒫.∘ μ
    ≈˘⟨ sub-⊗₁ {B} {Y ⊗ᴵ B} {F} (subᴵ w 𝒫.∘ λᴵ⇐) ⟩∘⟨refl ⟩
  subᴵ (subᴵ w 𝒫.∘ λᴵ⇐) 𝒫.∘ μ ∎
