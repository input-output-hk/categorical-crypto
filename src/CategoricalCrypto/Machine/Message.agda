{-# OPTIONS --safe #-}

-- ============================================================================
-- Message-level helpers shared by the machine layer.
--
-- Messages on a channel pair are sums, outputs are `Maybe`s, and every
-- bisimulation proof in `Machine.Iso`, `Machine.Forwarder` and
-- `Machine.Reindex.*` ends in the same handful of facts about them:
-- constructors are injective and pairwise distinct, and `mapᴹ` is a functor
-- with a few inversion properties.  They are stated over transparent types,
-- so that they can be applied to opaque-typed equations by conversion inside
-- the `unfolding` blocks that need them.
-- ============================================================================

module CategoricalCrypto.Machine.Message where

open import categorical-crypto.Prelude hiding (id; _∘_)

-- ----------------------------------------------------------------------------
-- Injectivity and disjointness of the constructors of `_⊎_` and `Maybe`.
-- ----------------------------------------------------------------------------

inj₁-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : X}
         → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y) → x ≡ y
inj₁-inj refl = refl

inj₂-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : Y}
         → _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y) → x ≡ y
inj₂-inj refl = refl

inj₁≢inj₂ : ∀ {a b} {X : Type a} {Y : Type b} {x : X} {y : Y} {ℓ} {W : Type ℓ}
          → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₂ y) → W
inj₁≢inj₂ ()

just-inj : ∀ {a} {X : Type a} {x y : X} → just x ≡ just y → x ≡ y
just-inj refl = refl

just≢nothing : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ}
             → just x ≡ nothing → W
just≢nothing ()

nothing≢just : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ}
             → nothing ≡ just x → W
nothing≢just ()

-- ----------------------------------------------------------------------------
-- `mapᴹ`: the prelude's `_<$>_` at `Maybe`, spelled out, so that it can be
-- reasoned about without instance resolution getting in the way.
-- Definitionally equal to `f <$> o`, which is what `modifyStepRel` uses.
-- ----------------------------------------------------------------------------

mapᴹ : ∀ {X Y : Type} → (X → Y) → Maybe X → Maybe Y
mapᴹ f = maybe (λ x → just (f x)) nothing

mapᴹ-id : ∀ {X : Type} (o : Maybe X) → mapᴹ (λ x → x) o ≡ o
mapᴹ-id (just _) = refl
mapᴹ-id nothing  = refl

mapᴹ-cong : ∀ {X Y : Type} {v v' : X → Y}
          → (∀ x → v x ≡ v' x) → ∀ o → mapᴹ v o ≡ mapᴹ v' o
mapᴹ-cong e (just x) = cong just (e x)
mapᴹ-cong e nothing  = refl

mapᴹ-∘ : ∀ {X Y Z : Type} (v : Y → Z) (w : X → Y) (o : Maybe X)
       → mapᴹ v (mapᴹ w o) ≡ mapᴹ (λ x → v (w x)) o
mapᴹ-∘ v w (just _) = refl
mapᴹ-∘ v w nothing  = refl

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
