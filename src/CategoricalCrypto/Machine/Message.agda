{-# OPTIONS --safe #-}

-- ============================================================================
-- Message-level helpers shared by the machine layer.
--
-- Messages on a channel pair are sums, outputs are `Maybe`s, and every
-- bisimulation proof in `Machine.Iso`, `Machine.Forwarder` and
-- `Machine.Reindex.*` ends in the same handful of facts about them:
-- constructors are injective and pairwise distinct, and `mapᴹ` is a functor
-- with a few inversion properties.
--
-- Most of that is `Data.Sum.Properties` and `Data.Maybe.Properties`, which the
-- project prelude does not re-export.  This module is the machine layer's
-- façade over them, fixing the short project spellings that ten files share,
-- and it adds the five facts the libraries do not have.  Everything is stated
-- over transparent types, so that it applies to opaque-typed equations by
-- conversion inside the `unfolding` blocks that need it.
-- ============================================================================

module CategoricalCrypto.Machine.Message where

open import categorical-crypto.Prelude hiding (id; _∘_)

import Data.Maybe.Properties as Maybeₚ

-- `mapᴹ` is the prelude's `_<$>_` at `Maybe` under a name that needs no
-- instance resolution, which is what the step-relation proofs reason about.
open import Data.Maybe.Base public
  using () renaming (map to mapᴹ)

open import Data.Maybe.Properties public
  using () renaming (just-injective to just-inj; map-id to mapᴹ-id;
                     map-cong to mapᴹ-cong)

open import Data.Sum.Properties public
  using () renaming (inj₁-injective to inj₁-inj; inj₂-injective to inj₂-inj)

-- The library states composition in the other direction.
mapᴹ-∘ : ∀ {X Y Z : Type} (v : Y → Z) (w : X → Y) (o : Maybe X)
       → mapᴹ v (mapᴹ w o) ≡ mapᴹ (λ x → v (w x)) o
mapᴹ-∘ v w o = sym (Maybeₚ.map-∘ {g = v} {f = w} o)

-- A pointwise inverse lifts through `mapᴹ`.  Five proofs in `Machine.Reindex*`
-- reached this conclusion by chaining `mapᴹ-∘`, `mapᴹ-cong` and `mapᴹ-id` by
-- hand.
mapᴹ-invol : ∀ {X Y : Type} {v : Y → X} {w : X → Y}
           → (∀ x → v (w x) ≡ x) → ∀ o → mapᴹ v (mapᴹ w o) ≡ o
mapᴹ-invol {v = v} {w} h o =
  trans (mapᴹ-∘ v w o) (trans (mapᴹ-cong h o) (mapᴹ-id o))

-- ----------------------------------------------------------------------------
-- Disjointness of the constructors, which neither library provides.
-- ----------------------------------------------------------------------------

inj₁≢inj₂ : ∀ {a b} {X : Type a} {Y : Type b} {x : X} {y : Y} {ℓ} {W : Type ℓ}
          → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₂ y) → W
inj₁≢inj₂ ()

just≢nothing : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ}
             → just x ≡ nothing → W
just≢nothing ()

nothing≢just : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ}
             → nothing ≡ just x → W
nothing≢just ()

-- ----------------------------------------------------------------------------
-- Two inversion principles for `mapᴹ`.
-- ----------------------------------------------------------------------------

-- A `just` under `mapᴹ` comes from a `just`.
mapᴹ-just : ∀ {X Y : Type} (v : X → Y) (O : Maybe X) (y : Y)
          → mapᴹ v O ≡ just y → ∃ λ x → (O ≡ just x) × (v x ≡ y)
mapᴹ-just v nothing  y e = nothing≢just e
mapᴹ-just v (just x) y e = x , refl , just-inj e

-- Two `mapᴹ`s that agree are pulled back along a pointwise inverse.
mapᴹ-pull : ∀ {X Y Z : Type} (v : X → Z) (w : Y → Z) (k : Y → X)
          → (∀ x y → v x ≡ w y → x ≡ k y)
          → ∀ O mo → mapᴹ v O ≡ mapᴹ w mo → O ≡ mapᴹ k mo
mapᴹ-pull v w k pt nothing  nothing  e = refl
mapᴹ-pull v w k pt nothing  (just _) e = nothing≢just e
mapᴹ-pull v w k pt (just _) nothing  e = just≢nothing e
mapᴹ-pull v w k pt (just x) (just y) e = cong just (pt x y (just-inj e))
