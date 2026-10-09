{-# OPTIONS --safe #-}

-- ============================================================================
-- The Kleisli shuffles `∘ᴷ-fwd` and `⊗ᴷ-fwd` are natural.
--
-- Both shuffles are composites of associators and symmetries
-- (`Machine.Monoidal.Coherence`), and the machine category is symmetric
-- monoidal (`Machine.MonoidalCategory`), so each law is the naturality of
-- the structural isomorphisms, one slide at a time.
-- ============================================================================

module CategoricalCrypto.Machine.Monoidal.Naturality where

open import categorical-crypto.Prelude hiding (id; _∘_)

open import Categories.Category
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonoidalR
import Categories.Morphism.Reasoning as MR

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Monoidal.Associator using (⊗-assoc⃖-natural)
open import CategoricalCrypto.Machine.Monoidal.Braiding using (σ-natural)
open import CategoricalCrypto.Machine.Monoidal.Coherence
  using (∘ᴷ-fwd-decomp; ⊗ᴷ-fwd-decomp; mid4-decomp)
open import CategoricalCrypto.Machine.MonoidalCategory

open Category MachineCategory using (assoc; sym-assoc)
open MR MachineCategory
open Monoidal machine-monoidal using (assoc-commute-from)
open MonoidalR machine-monoidal

∘ᴷ-fwd-natural : ∀ {C C' E₁ E₁' E₂ E₂'}
                 (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
               → ((c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ∘ᴷ-fwd)
                 ≅ᴹ (∘ᴷ-fwd CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁))
∘ᴷ-fwd-natural c u₁ u₂ = begin
    (c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ∘ᴷ-fwd
  ≈⟨ refl⟩∘⟨ ∘ᴷ-fwd-decomp ⟩
    (c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ((CC.id ⊗₁ ⊗-symₘ) CC.∘ ⊗-assoc)
  ≈⟨ pullˡ merge₂ʳ ⟩
    (c ⊗₁ ((u₁ ⊗₁ u₂) CC.∘ ⊗-symₘ)) CC.∘ ⊗-assoc
  ≈⟨ (refl⟩⊗⟨ ⟺ (σ-natural u₂ u₁)) ⟩∘⟨refl ⟩
    (c ⊗₁ (⊗-symₘ CC.∘ (u₂ ⊗₁ u₁))) CC.∘ ⊗-assoc
  ≈⟨ pushˡ split₂ˡ ⟩
    (CC.id ⊗₁ ⊗-symₘ) CC.∘ ((c ⊗₁ (u₂ ⊗₁ u₁)) CC.∘ ⊗-assoc)
  ≈⟨ pushʳ (⟺ assoc-commute-from) ⟩
    ((CC.id ⊗₁ ⊗-symₘ) CC.∘ ⊗-assoc) CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁)
  ≈⟨ ⟺ ∘ᴷ-fwd-decomp ⟩∘⟨refl ⟩
    ∘ᴷ-fwd CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁)
  ∎

private
  -- The single crossing inside `mid4-core`, `Q ⊗ (R ⊗ S) → R ⊗ (Q ⊗ S)`.
  inner : ∀ {Q R S} → Machine (Q ⊗₀ (R ⊗₀ S)) (R ⊗₀ (Q ⊗₀ S))
  inner = ⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖)

  inner-natural : ∀ {Q Q' R R' S S'} (q : Machine Q Q') (r : Machine R R') (s : Machine S S')
                → ((r ⊗₁ (q ⊗₁ s)) CC.∘ inner) ≅ᴹ (inner CC.∘ (q ⊗₁ (r ⊗₁ s)))
  inner-natural q r s = begin
      (r ⊗₁ (q ⊗₁ s)) CC.∘ (⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖))
    ≈⟨ pullˡ (⟺ assoc-commute-from) ⟩
      (⊗-assoc CC.∘ ((r ⊗₁ q) ⊗₁ s)) CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖)
    ≈⟨ assoc ⟩
      ⊗-assoc CC.∘ (((r ⊗₁ q) ⊗₁ s) CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖))
    ≈⟨ refl⟩∘⟨ pullˡ merge₁ʳ ⟩
      ⊗-assoc CC.∘ ((((r ⊗₁ q) CC.∘ ⊗-symₘ) ⊗₁ s) CC.∘ ⊗-assoc⃖)
    ≈⟨ refl⟩∘⟨ (⟺ (σ-natural q r) ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      ⊗-assoc CC.∘ (((⊗-symₘ CC.∘ (q ⊗₁ r)) ⊗₁ s) CC.∘ ⊗-assoc⃖)
    ≈⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
      ⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ (((q ⊗₁ r) ⊗₁ s) CC.∘ ⊗-assoc⃖))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-assoc⃖-natural q r s ⟩
      ⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ (⊗-assoc⃖ CC.∘ (q ⊗₁ (r ⊗₁ s))))
    ≈⟨ (refl⟩∘⟨ sym-assoc) ○ sym-assoc ⟩
      (⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖)) CC.∘ (q ⊗₁ (r ⊗₁ s))
    ∎

⊗ᴷ-fwd-natural : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
                 (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
                 (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
               → (((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd)
                 ≅ᴹ (⊗ᴷ-fwd CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂)))
⊗ᴷ-fwd-natural b₁ u₁ b₂ u₂ = begin
    ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd
  ≈⟨ refl⟩∘⟨ (⊗ᴷ-fwd-decomp ○ mid4-decomp) ⟩
    ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ (⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ inner) CC.∘ ⊗-assoc))
  ≈⟨ pullˡ (⊗-assoc⃖-natural b₁ b₂ (u₁ ⊗₁ u₂)) ⟩
    (⊗-assoc⃖ CC.∘ (b₁ ⊗₁ (b₂ ⊗₁ (u₁ ⊗₁ u₂)))) CC.∘ ((CC.id ⊗₁ inner) CC.∘ ⊗-assoc)
  ≈⟨ assoc ⟩
    ⊗-assoc⃖ CC.∘ ((b₁ ⊗₁ (b₂ ⊗₁ (u₁ ⊗₁ u₂))) CC.∘ ((CC.id ⊗₁ inner) CC.∘ ⊗-assoc))
  ≈⟨ refl⟩∘⟨ pullˡ merge₂ʳ ⟩
    ⊗-assoc⃖ CC.∘ ((b₁ ⊗₁ ((b₂ ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ inner)) CC.∘ ⊗-assoc)
  ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ inner-natural u₁ b₂ u₂) ⟩∘⟨refl ⟩
    ⊗-assoc⃖ CC.∘ ((b₁ ⊗₁ (inner CC.∘ (u₁ ⊗₁ (b₂ ⊗₁ u₂)))) CC.∘ ⊗-assoc)
  ≈⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    ⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ inner) CC.∘ ((b₁ ⊗₁ (u₁ ⊗₁ (b₂ ⊗₁ u₂))) CC.∘ ⊗-assoc))
  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ assoc-commute-from ⟩
    ⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ inner) CC.∘ (⊗-assoc CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))))
  ≈⟨ (refl⟩∘⟨ sym-assoc) ○ sym-assoc ⟩
    (⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ inner) CC.∘ ⊗-assoc)) CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
  ≈⟨ ⟺ (⊗ᴷ-fwd-decomp ○ mid4-decomp) ⟩∘⟨refl ⟩
    ⊗ᴷ-fwd CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
  ∎
