{-# OPTIONS --safe #-}

-- ============================================================================
-- The machine category is monoidal: the laws relating `_⊗₁_`, `_∘_`, the
-- structural forwarders of `Machine.Core`, and the Kleisli builders `_∘ᴷ_` and
-- `_⊗ᴷ_`, all at `_≅ᴹ_`.  Each is proved in its own module; this one collects
-- them.
--
--   `⊗₁-id`, `ρ-∘ᴷ-fwd`, `ρ-idᴷ`, `λ-zip-idᴷ` — forwarders are closed under
--     `_⊗₁_`, `modifyStepRel` and `_∘_` (`Machine.Forwarder`);
--   `⊗₁-interchange` — `_⊗₁_` is a functor for `_∘_`
--     (`Machine.Monoidal.Interchange`);
--   `∘ᴷ-fwd-natural`, `⊗ᴷ-fwd-natural` — the Kleisli shuffles are natural
--     (`Machine.Monoidal.Naturality`);
--   `∘ᴷ-assoc`, `⊗ᴷ-∘ᴷ` — `_∘ᴷ_` associates and interchanges with `_⊗ᴷ_`
--     (`Machine.Monoidal.Kleisli`).
-- ============================================================================

module CategoricalCrypto.Machine.Monoidal where

open import CategoricalCrypto.Machine.Forwarder public
  using (⊗₁-id; ρ-∘ᴷ-fwd; ρ-idᴷ; λ-zip-idᴷ)
open import CategoricalCrypto.Machine.Monoidal.Interchange public
  using (⊗₁-interchange)
open import CategoricalCrypto.Machine.Monoidal.Naturality public
  using (∘ᴷ-fwd-natural; ⊗ᴷ-fwd-natural; ⊗-assoc⃖-natural)
open import CategoricalCrypto.Machine.Monoidal.Kleisli public
  using (∘ᴷ-assoc; ⊗ᴷ-∘ᴷ)
