{-# OPTIONS --safe #-}

-- ============================================================================
-- Pre-composition with a forwarder, and the right identity law.
--
-- `Reindex.Post` ends with `Xfwd-∘-Post`: post-composing a machine with a
-- crossing forwarder is a `Post`, a relabelling that is covariant on the
-- output side.  This module is the mirror image on the domain side.  The
-- forwarder now sits in the FIRST component of the `Pair`, so the traced
-- channel `B` lies between the forwarder's codomain and `N`'s domain, and
-- every trace chain of the normal form `∘-Reindex (Xfwd f g) N` contains
-- exactly one `N`-step.  It is preceded by a relay hop iff the external input
-- arrived on `A` (it reaches `N` as `f a`), and followed by one iff `N`
-- emitted on its domain `B` (it leaves as `g b` on `A`).  `Trc-relay-dom`
-- says so directly on the normal form, by case analysis on the chain and on
-- `Step₁`/`Step₂`; the old hand proof of the right identity law did the same
-- on the raw machine, with view lemmas for every reshuffle.
--
-- The corollaries are `∘-Xfwd-Post` (pre-composing with a crossing forwarder
-- is a `Post`) and `∘-identityʳ-Post` (the right identity law), the latter
-- obtained from `id-is-Xfwd` and `Post-id` instead of by hand.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex
open import CategoricalCrypto.Machine.Reindex.Slide
open import CategoricalCrypto.Machine.Reindex.Post
open import CategoricalCrypto.Machine.Forwarder

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso hiding (∘-assoc-≅ᴹ)
open import Tactic.Defaults

module CategoricalCrypto.Machine.Reindex.PostDom where

open _≅ᴹ_

private
  just-inj : ∀ {a} {X : Type a} {x y : X} → just x ≡ just y → x ≡ y
  just-inj refl = refl

  inj₁-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : X}
           → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₁ y) → x ≡ y
  inj₁-inj refl = refl

  inj₂-inj : ∀ {a b} {X : Type a} {Y : Type b} {x y : Y}
           → _≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y) → x ≡ y
  inj₂-inj refl = refl

  inj₁≢inj₂ : ∀ {a b} {X : Type a} {Y : Type b} {x : X} {y : Y} {ℓ} {W : Type ℓ}
            → _≡_ {A = X ⊎ Y} (inj₁ x) (inj₂ y) → W
  inj₁≢inj₂ ()

  just≢nothing : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ} → just x ≡ nothing → W
  just≢nothing ()

  nothing≢just : ∀ {a} {X : Type a} {x : X} {ℓ} {W : Type ℓ} → nothing ≡ just x → W
  nothing≢just ()

  -- Inversion view for `CompRel` at fully general indices.
  CompView : ∀ {A B C D} (M₁ : Machine A B) (M₂ : Machine C D)
             (sp : Machine.State M₁ × Machine.State M₂)
             (x : Channel.inType (Tensor.AllCs M₁ M₂))
             (y : Maybe (Channel.outType (Tensor.AllCs M₁ M₂)))
             (sp' : Machine.State M₁ × Machine.State M₂) → Type
  CompView M₁ M₂ sp x y sp' =
      (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (ϵ ⊗R) ↑ᵢ mᵢ) × (y ≡ ((ϵ ⊗R) ↑ₒ_ <$> mo))
         × (proj₂ sp' ≡ proj₂ sp)
         × Machine.stepRel M₁ (proj₁ sp) mᵢ mo (proj₁ sp'))
    ⊎ (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (L⊗ ϵ) ↑ᵢ mᵢ) × (y ≡ ((L⊗ ϵ) ↑ₒ_ <$> mo))
         × (proj₁ sp' ≡ proj₁ sp)
         × Machine.stepRel M₂ (proj₂ sp) mᵢ mo (proj₂ sp'))

  comp-view :
    ∀ {A B C D} {M₁ : Machine A B} {M₂ : Machine C D}
      {sp : Machine.State M₁ × Machine.State M₂} {x y sp'}
    → Tensor.CompRel M₁ M₂ sp x y sp' → CompView M₁ M₂ sp x y sp'
  comp-view (Tensor.Step₁ q) = inj₁ (_ , _ , refl , refl , refl , q)
  comp-view (Tensor.Step₂ q) = inj₂ (_ , _ , refl , refl , refl , q)

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

-- The traced core of `N CC.∘ Xfwd f g`, as `∘-Reindex` presents it.
relay-core : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                       (g : Channel.outType B → Channel.outType A)
             (N : Machine B C) → Machine (A ⊗₀ B) (C ⊗₀ B)
relay-core {A} {B} {C} f g N =
  Reindex (Pair (Xfwd f g) N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ ∘κᵢ cdᵢ Xφ

  -- ------------------------------------------------------------------------
  -- Relabelling of the domain only, covariant on the output side.  `dmᵢ`
  -- from `Reindex.Slide` serves for the input side unchanged.
  -- ------------------------------------------------------------------------

  -- Relabel the domain of `Machine A B` to `A'`, leaving the codomain alone.
  dmₒ⁺ : ∀ {A A' B} → (Channel.outType A → Channel.outType A')
       → Channel.outType (A ⊗ᵀ B) → Channel.outType (A' ⊗ᵀ B)
  dmₒ⁺ vA (inj₁ α) = inj₁ (vA α)
  dmₒ⁺ vA (inj₂ b) = inj₂ b

  private
    -- Named ports.  The type of an opaque definition is checked without
    -- unfolding, so signatures cannot spell messages out as sums; these do it
    -- once, in bodies.  First the traced machine's channel: the forwarder's
    -- domain `A` and `N`'s ports, whose domain `B` is the traced channel seen
    -- from the domain side and whose codomain `C` is external.
    aᵢ : ∀ {A B C} → Channel.inType A → Channel.inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    aᵢ a = inj₁ (inj₁ a)

    aₒ : ∀ {A B C} → Channel.outType A → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    aₒ ao = inj₁ (inj₁ ao)

    nᵢ : ∀ {A B C} → Channel.inType (B ⊗ᵀ C) → Channel.inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    nᵢ (inj₁ b)  = inj₁ (inj₂ b)
    nᵢ (inj₂ co) = inj₂ (inj₁ co)

    nₒ : ∀ {A B C} → Channel.outType (B ⊗ᵀ C) → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    nₒ (inj₁ bo) = inj₁ (inj₂ bo)
    nₒ (inj₂ ci) = inj₂ (inj₁ ci)

    -- Domain outputs of the composite and of `N`.
    eₒ : ∀ {A C} → Channel.outType A → Channel.outType (A ⊗ᵀ C)
    eₒ ao = inj₁ ao

    bₒ : ∀ {B C} → Channel.outType B → Channel.outType (B ⊗ᵀ C)
    bₒ bo = inj₁ bo

    -- The `Pair`'s channel: the forwarder's two output ports, and `N`'s side.
    pAₒ : ∀ {A B C} → Channel.outType A → Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
    pAₒ ao = inj₁ (inj₁ ao)

    pBᵢ : ∀ {A B C} → Channel.inType B → Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
    pBᵢ b = inj₁ (inj₂ b)

    p₂ᵢ : ∀ {A B C} → Channel.inType (B ⊗ᵀ C) → Channel.inType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
    p₂ᵢ j = inj₂ j

    p₂ₒ : ∀ {A B C} → Channel.outType (B ⊗ᵀ C) → Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
    p₂ₒ y = inj₂ y

    -- `∘κ` routes `N`'s ports to the second component of the `Pair`.
    κᵢ-N : ∀ {A B C} (j : Channel.inType (B ⊗ᵀ C))
         → ∘κᵢ {A} {B} {C} (nᵢ {A} {B} {C} j) ≡ p₂ᵢ {A} {B} {C} j
    κᵢ-N (inj₁ _) = refl
    κᵢ-N (inj₂ _) = refl

    κₒ-nₒ : ∀ {A B C} (mo : Maybe (Channel.outType (B ⊗ᵀ C)))
          → mapᴹ (∘κₒ {A} {B} {C}) (mapᴹ (nₒ {A} {B} {C}) mo) ≡ mapᴹ (p₂ₒ {A} {B} {C}) mo
    κₒ-nₒ nothing          = refl
    κₒ-nₒ (just (inj₁ _))  = refl
    κₒ-nₒ (just (inj₂ _))  = refl

    -- Reading `∘κₒ` backwards, one image at a time.
    κₒ-A : ∀ {A B C} (x : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) (ao : Channel.outType A)
         → ∘κₒ {A} {B} {C} x ≡ pAₒ {A} {B} {C} ao → x ≡ aₒ {A} {B} {C} ao
    κₒ-A {A} {B} {C} (inj₁ (inj₁ _)) ao e = cong (aₒ {A} {B} {C}) (inj₁-inj (inj₁-inj e))
    κₒ-A (inj₁ (inj₂ _)) ao e = inj₁≢inj₂ (sym e)
    κₒ-A (inj₂ (inj₁ _)) ao e = inj₁≢inj₂ (sym e)
    κₒ-A (inj₂ (inj₂ _)) ao e = inj₁≢inj₂ (sym (inj₁-inj e))

    κₒ-B : ∀ {A B C} (x : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) (b : Channel.inType B)
         → ∘κₒ {A} {B} {C} x ≡ pBᵢ {A} {B} {C} b → x ≡ cZᵢ {A} {C} {B} b
    κₒ-B (inj₁ (inj₁ _)) b e = inj₁≢inj₂ (inj₁-inj e)
    κₒ-B (inj₁ (inj₂ _)) b e = inj₁≢inj₂ (sym e)
    κₒ-B (inj₂ (inj₁ _)) b e = inj₁≢inj₂ (sym e)
    κₒ-B (inj₂ (inj₂ _)) b e = cong (λ z → inj₂ (inj₂ z)) (inj₂-inj (inj₁-inj e))

    κₒ-N : ∀ {A B C} (x : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) (y : Channel.outType (B ⊗ᵀ C))
         → ∘κₒ {A} {B} {C} x ≡ p₂ₒ {A} {B} {C} y → x ≡ nₒ {A} {B} {C} y
    κₒ-N {A} {B} {C} (inj₁ (inj₁ _)) y e = inj₁≢inj₂ e
    κₒ-N {A} {B} {C} (inj₁ (inj₂ _)) y e = cong (nₒ {A} {B} {C}) (inj₂-inj e)
    κₒ-N {A} {B} {C} (inj₂ (inj₁ _)) y e = cong (nₒ {A} {B} {C}) (inj₂-inj e)
    κₒ-N {A} {B} {C} (inj₂ (inj₂ _)) y e = inj₁≢inj₂ e

    -- What the external output map `tιₒ` and `N`'s output map `nₒ` can hit.
    tιₒ-A : ∀ {A B C} (o : Maybe (Channel.outType (A ⊗ᵀ C))) (ao : Channel.outType A)
          → mapᴹ (tιₒ {A} {C} {B}) o ≡ just (aₒ {A} {B} {C} ao) → o ≡ just (eₒ {A} {C} ao)
    tιₒ-A nothing         ao e = nothing≢just e
    tιₒ-A (just (inj₁ _)) ao e = cong (λ z → just (inj₁ z)) (inj₁-inj (inj₁-inj (just-inj e)))
    tιₒ-A (just (inj₂ _)) ao e = inj₁≢inj₂ (sym (just-inj e))

    tιₒ-cZᵢ : ∀ {A B C} {ℓ} {W : Type ℓ} (o : Maybe (Channel.outType (A ⊗ᵀ C))) (b : Channel.inType B)
            → mapᴹ (tιₒ {A} {C} {B}) o ≡ just (cZᵢ {A} {C} {B} b) → W
    tιₒ-cZᵢ nothing         b e = nothing≢just e
    tιₒ-cZᵢ (just (inj₁ _)) b e = inj₁≢inj₂ (just-inj e)
    tιₒ-cZᵢ (just (inj₂ _)) b e = inj₁≢inj₂ (inj₂-inj (just-inj e))

    nₒ-dZₒ : ∀ {A B C} (o₀ : Maybe (Channel.outType (B ⊗ᵀ C))) (bo : Channel.outType B)
           → mapᴹ (nₒ {A} {B} {C}) o₀ ≡ just (dZₒ {A} {C} {B} bo) → o₀ ≡ just (bₒ {B} {C} bo)
    nₒ-dZₒ nothing         bo e = nothing≢just e
    nₒ-dZₒ (just (inj₁ _)) bo e = cong (λ z → just (inj₁ z)) (inj₂-inj (inj₁-inj (just-inj e)))
    nₒ-dZₒ (just (inj₂ _)) bo e = inj₁≢inj₂ (sym (just-inj e))

    nₒ-cZᵢ : ∀ {A B C} {ℓ} {W : Type ℓ} (o₀ : Maybe (Channel.outType (B ⊗ᵀ C))) (b : Channel.inType B)
           → mapᴹ (nₒ {A} {B} {C}) o₀ ≡ just (cZᵢ {A} {C} {B} b) → W
    nₒ-cZᵢ nothing         b e = nothing≢just e
    nₒ-cZᵢ (just (inj₁ _)) b e = inj₁≢inj₂ (just-inj e)
    nₒ-cZᵢ (just (inj₂ _)) b e = inj₁≢inj₂ (inj₂-inj (just-inj e))

    -- An `N`-output that leaves through the trace is a codomain output, and
    -- `dmₒ⁺` fixes it.
    nₒ-ext : ∀ {A B C} (g : Channel.outType B → Channel.outType A)
             (o₀ : Maybe (Channel.outType (B ⊗ᵀ C))) (o : Maybe (Channel.outType (A ⊗ᵀ C)))
           → mapᴹ (nₒ {A} {B} {C}) o₀ ≡ mapᴹ (tιₒ {A} {C} {B}) o
           → mapᴹ (dmₒ⁺ {B} {A} {C} g) o₀ ≡ o
    nₒ-ext g nothing         nothing         e = refl
    nₒ-ext g nothing         (just _)        e = nothing≢just e
    nₒ-ext g (just _)        nothing         e = just≢nothing e
    nₒ-ext g (just (inj₁ _)) (just (inj₁ _)) e = inj₁≢inj₂ (sym (inj₁-inj (just-inj e)))
    nₒ-ext g (just (inj₁ _)) (just (inj₂ _)) e = inj₁≢inj₂ (just-inj e)
    nₒ-ext g (just (inj₂ _)) (just (inj₁ _)) e = inj₁≢inj₂ (sym (just-inj e))
    nₒ-ext g (just (inj₂ _)) (just (inj₂ _)) e =
      cong (λ z → just (inj₂ z)) (inj₁-inj (inj₂-inj (just-inj e)))

    -- ----------------------------------------------------------------------
    -- The three kinds of step of the traced core, by the port the input
    -- arrives on.  An input on `A` is relayed onto the traced channel as
    -- `f a`; a traced output `bo` re-entering on the codomain side is relayed
    -- out on `A` as `g bo`; anything arriving on one of `N`'s ports is an
    -- `N`-step, routed through `nᵢ`/`nₒ`.
    -- ----------------------------------------------------------------------

    step-A : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                       (g : Channel.outType B → Channel.outType A) (N : Machine B C)
             {S S' : Machine.State (relay-core f g N)} (a : Channel.inType A)
             (O : Maybe (Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))))
           → Machine.stepRel (relay-core f g N) S (aᵢ {A} {B} {C} a) O S'
           → (proj₂ S' ≡ proj₂ S) × (O ≡ just (cZᵢ {A} {C} {B} (f a)))
    step-A {A} {B} {C} f g N {S} {S'} a O x = go (comp-view x)
      where
      go : CompView (Xfwd f g) N S (∘κᵢ {A} {B} {C} (aᵢ {A} {B} {C} a)) (mapᴹ (∘κₒ {A} {B} {C}) O) S'
         → (proj₂ S' ≡ proj₂ S) × (O ≡ just (cZᵢ {A} {C} {B} (f a)))
      go (inj₂ (_ , _ , xeq , _)) = inj₁≢inj₂ xeq
      go (inj₁ (mᵢ , mo , xeq , yeq , steq , q)) =
        let mo≡ : mo ≡ just (inj₂ (f a))
            mo≡ = trans (sym q) (cong (λ z → just (Xφ f g z)) (sym (inj₁-inj xeq)))
            O≡ : mapᴹ (∘κₒ {A} {B} {C}) O ≡ just (inj₁ (inj₂ (f a)))
            O≡ = trans yeq (cong (mapᴹ inj₁) mo≡)
            (x₀ , Ox , κx) = mapᴹ-just (∘κₒ {A} {B} {C}) O (inj₁ (inj₂ (f a))) O≡
        in steq , trans Ox (cong just (κₒ-B x₀ (f a) κx))

    step-Bo : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                        (g : Channel.outType B → Channel.outType A) (N : Machine B C)
              {S S' : Machine.State (relay-core f g N)} (bo : Channel.outType B)
              (O : Maybe (Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))))
            → Machine.stepRel (relay-core f g N) S (cZₒ {A} {C} {B} bo) O S'
            → (proj₂ S' ≡ proj₂ S) × (O ≡ just (aₒ {A} {B} {C} (g bo)))
    step-Bo {A} {B} {C} f g N {S} {S'} bo O x = go (comp-view x)
      where
      go : CompView (Xfwd f g) N S (∘κᵢ {A} {B} {C} (cZₒ {A} {C} {B} bo)) (mapᴹ (∘κₒ {A} {B} {C}) O) S'
         → (proj₂ S' ≡ proj₂ S) × (O ≡ just (aₒ {A} {B} {C} (g bo)))
      go (inj₂ (_ , _ , xeq , _)) = inj₁≢inj₂ xeq
      go (inj₁ (mᵢ , mo , xeq , yeq , steq , q)) =
        let mo≡ : mo ≡ just (inj₁ (g bo))
            mo≡ = trans (sym q) (cong (λ z → just (Xφ f g z)) (sym (inj₁-inj xeq)))
            O≡ : mapᴹ (∘κₒ {A} {B} {C}) O ≡ just (inj₁ (inj₁ (g bo)))
            O≡ = trans yeq (cong (mapᴹ inj₁) mo≡)
            (x₀ , Ox , κx) = mapᴹ-just (∘κₒ {A} {B} {C}) O (inj₁ (inj₁ (g bo))) O≡
        in steq , trans Ox (cong just (κₒ-A x₀ (g bo) κx))

    step-N : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                       (g : Channel.outType B → Channel.outType A) (N : Machine B C)
             {S S' : Machine.State (relay-core f g N)} (j : Channel.inType (B ⊗ᵀ C))
             (O : Maybe (Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))))
           → Machine.stepRel (relay-core f g N) S (nᵢ {A} {B} {C} j) O S'
           → ∃ λ o₀ → Machine.stepRel N (proj₂ S) j o₀ (proj₂ S') × (mapᴹ (nₒ {A} {B} {C}) o₀ ≡ O)
    step-N {A} {B} {C} f g N {S} {S'} j O x = go (comp-view x)
      where
      go : CompView (Xfwd f g) N S (∘κᵢ {A} {B} {C} (nᵢ {A} {B} {C} j)) (mapᴹ (∘κₒ {A} {B} {C}) O) S'
         → ∃ λ o₀ → Machine.stepRel N (proj₂ S) j o₀ (proj₂ S') × (mapᴹ (nₒ {A} {B} {C}) o₀ ≡ O)
      go (inj₁ (_ , _ , xeq , _)) = inj₁≢inj₂ (sym (trans (sym (κᵢ-N {A} {B} {C} j)) xeq))
      go (inj₂ (mᵢ , mo , xeq , yeq , _ , q)) =
        mo
        , subst (λ z → Machine.stepRel N (proj₂ S) z mo (proj₂ S'))
                (sym (inj₂-inj (trans (sym (κᵢ-N {A} {B} {C} j)) xeq))) q
        , sym (mapᴹ-pull (∘κₒ {A} {B} {C}) (p₂ₒ {A} {B} {C}) (nₒ {A} {B} {C}) (κₒ-N {A} {B} {C}) O mo yeq)

    -- The same three steps, built.
    mk-A : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                     (g : Channel.outType B → Channel.outType A) (N : Machine B C)
           {u : Machine.State (Xfwd f g)} (s : Machine.State N) (a : Channel.inType A)
         → Machine.stepRel (relay-core f g N) (u , s) (aᵢ {A} {B} {C} a)
                           (just (cZᵢ {A} {C} {B} (f a))) (u , s)
    mk-A f g N s a = Tensor.Step₁ {m = inj₁ a} {m' = just (inj₂ (f a))} refl

    mk-Bo : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                      (g : Channel.outType B → Channel.outType A) (N : Machine B C)
            {u : Machine.State (Xfwd f g)} (s : Machine.State N) (bo : Channel.outType B)
          → Machine.stepRel (relay-core f g N) (u , s) (cZₒ {A} {C} {B} bo)
                            (just (aₒ {A} {B} {C} (g bo))) (u , s)
    mk-Bo f g N s bo = Tensor.Step₁ {m = inj₂ bo} {m' = just (inj₁ (g bo))} refl

    mk-N : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                     (g : Channel.outType B → Channel.outType A) (N : Machine B C)
           {u : Machine.State (Xfwd f g)} {s s' : Machine.State N} (j : Channel.inType (B ⊗ᵀ C))
           (o₀ : Maybe (Channel.outType (B ⊗ᵀ C)))
         → Machine.stepRel N s j o₀ s'
         → Machine.stepRel (relay-core f g N) (u , s) (nᵢ {A} {B} {C} j)
                           (mapᴹ (nₒ {A} {B} {C}) o₀) (u , s')
    mk-N {A} {B} {C} f g N {u} {s} {s'} j o₀ q =
      subst₂ (λ I O → Tensor.CompRel (Xfwd f g) N (u , s) I O (u , s'))
             (sym (κᵢ-N {A} {B} {C} j)) (sym (κₒ-nₒ {A} {B} {C} o₀))
             (Tensor.Step₂ {m = j} {m' = o₀} q)

    -- ----------------------------------------------------------------------
    -- The chains.  Forward: a chain starting on one of `N`'s ports is the
    -- `N`-step, followed by a relay hop iff `N` emitted on its domain; a chain
    -- starting with a traced output re-entering is that relay hop and nothing
    -- else; a chain from an external input is one of the two, with a relay
    -- hop in front iff the input arrived on `A`.
    -- ----------------------------------------------------------------------

    chain-Bo : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                         (g : Channel.outType B → Channel.outType A) (N : Machine B C)
               {S S' : Machine.State (relay-core f g N)} (bo : Channel.outType B)
               (o : Maybe (Channel.outType (A ⊗ᵀ C)))
             → TraceRel (relay-core f g N) S (cZₒ {A} {C} {B} bo) (mapᴹ (tιₒ {A} {C} {B}) o) S'
             → (proj₂ S' ≡ proj₂ S) × (o ≡ just (eₒ {A} {C} (g bo)))
    chain-Bo {A} {B} {C} f g N bo o Trace[ x ] =
      let (st , O≡) = step-Bo f g N bo (mapᴹ (tιₒ {A} {C} {B}) o) x
      in st , tιₒ-A {A} {B} {C} o (g bo) O≡
    chain-Bo {A} {B} {C} f g N bo o (_Trace∷ₒ_ {outC = zc} x rest) =
      let (_ , O≡) = step-Bo f g N bo (just (dZₒ {A} {C} {B} zc)) x
      in inj₁≢inj₂ (sym (inj₁-inj (just-inj O≡)))
    chain-Bo {A} {B} {C} f g N bo o (_Trace∷ᵢ_ {inC = zc} x rest) =
      let (_ , O≡) = step-Bo f g N bo (just (cZᵢ {A} {C} {B} zc)) x
      in inj₁≢inj₂ (sym (just-inj O≡))

    chain-N : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                        (g : Channel.outType B → Channel.outType A) (N : Machine B C)
              {S S' : Machine.State (relay-core f g N)} (j : Channel.inType (B ⊗ᵀ C))
              (o : Maybe (Channel.outType (A ⊗ᵀ C)))
            → TraceRel (relay-core f g N) S (nᵢ {A} {B} {C} j) (mapᴹ (tιₒ {A} {C} {B}) o) S'
            → ∃ λ o₀ → Machine.stepRel N (proj₂ S) j o₀ (proj₂ S')
                     × mapᴹ (dmₒ⁺ {B} {A} {C} g) o₀ ≡ o
    chain-N {A} {B} {C} f g N j o Trace[ x ] =
      let (o₀ , q , e) = step-N f g N j (mapᴹ (tιₒ {A} {C} {B}) o) x
      in o₀ , q , nₒ-ext g o₀ o e
    chain-N {A} {B} {C} f g N {S} {S'} j o (_Trace∷ₒ_ {s' = S₁} {outC = zc} x rest) =
      let (o₀ , q , e) = step-N f g N j (just (dZₒ {A} {C} {B} zc)) x
          o₀≡ : o₀ ≡ just (inj₁ zc)
          o₀≡ = nₒ-dZₒ {A} {B} {C} o₀ zc e
          (st , o≡) = chain-Bo f g N zc o rest
      in just (inj₁ zc)
       , subst₂ (λ y z → Machine.stepRel N (proj₂ S) j y z) o₀≡ (sym st) q
       , sym o≡
    chain-N {A} {B} {C} f g N j o (_Trace∷ᵢ_ {inC = zc} x rest) =
      let (o₀ , q , e) = step-N f g N j (just (cZᵢ {A} {C} {B} zc)) x
      in nₒ-cZᵢ {A} {B} {C} o₀ zc e

    chain : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                      (g : Channel.outType B → Channel.outType A) (N : Machine B C)
            {S S' : Machine.State (relay-core f g N)} (i : Channel.inType (A ⊗ᵀ C))
            (o : Maybe (Channel.outType (A ⊗ᵀ C)))
          → TraceRel (relay-core f g N) S (tιᵢ {A} {C} {B} i) (mapᴹ (tιₒ {A} {C} {B}) o) S'
          → ∃ λ o₀ → Machine.stepRel N (proj₂ S) (dmᵢ {B} {A} {C} f i) o₀ (proj₂ S')
                   × mapᴹ (dmₒ⁺ {B} {A} {C} g) o₀ ≡ o
    chain {A} {B} {C} f g N (inj₂ co) o tr = chain-N f g N (inj₂ co) o tr
    chain {A} {B} {C} f g N (inj₁ a) o Trace[ x ] =
      let (_ , O≡) = step-A f g N a (mapᴹ (tιₒ {A} {C} {B}) o) x
      in tιₒ-cZᵢ {A} {B} {C} o (f a) O≡
    chain {A} {B} {C} f g N (inj₁ a) o (_Trace∷ₒ_ {outC = zc} x rest) =
      let (_ , O≡) = step-A f g N a (just (dZₒ {A} {C} {B} zc)) x
      in inj₁≢inj₂ (just-inj O≡)
    chain {A} {B} {C} f g N {S} {S'} (inj₁ a) o (_Trace∷ᵢ_ {s' = S₁} {inC = zc} x rest) =
      let (st , O≡) = step-A f g N a (just (cZᵢ {A} {C} {B} zc)) x
          zc≡ : zc ≡ f a
          zc≡ = inj₂-inj (inj₂-inj (just-inj O≡))
          (o₀ , q , e) = chain-N f g N (inj₁ zc) o rest
      in o₀ , subst₂ (λ y z → Machine.stepRel N y (inj₁ z) o₀ (proj₂ S')) st zc≡ q , e

    -- Backward: the 1-, 2- or 3-hop chain of a `Post` step.
    build-N : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                        (g : Channel.outType B → Channel.outType A) (N : Machine B C)
              {u : Machine.State (Xfwd f g)} {s s' : Machine.State N} (j : Channel.inType (B ⊗ᵀ C))
              (o₀ : Maybe (Channel.outType (B ⊗ᵀ C)))
            → Machine.stepRel N s j o₀ s'
            → TraceRel (relay-core f g N) (u , s) (nᵢ {A} {B} {C} j)
                       (mapᴹ (tιₒ {A} {C} {B}) (mapᴹ (dmₒ⁺ {B} {A} {C} g) o₀)) (u , s')
    build-N f g N j nothing          q = Trace[ mk-N f g N j nothing q ]
    build-N f g N j (just (inj₂ ci)) q = Trace[ mk-N f g N j (just (inj₂ ci)) q ]
    build-N f g N {u} {s} {s'} j (just (inj₁ bo)) q =
      _Trace∷ₒ_ {outC = bo} (mk-N f g N j (just (inj₁ bo)) q) Trace[ mk-Bo f g N s' bo ]

    build : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                      (g : Channel.outType B → Channel.outType A) (N : Machine B C)
            {u : Machine.State (Xfwd f g)} {s s' : Machine.State N} (i : Channel.inType (A ⊗ᵀ C))
            (o₀ : Maybe (Channel.outType (B ⊗ᵀ C)))
          → Machine.stepRel N s (dmᵢ {B} {A} {C} f i) o₀ s'
          → TraceRel (relay-core f g N) (u , s) (tιᵢ {A} {C} {B} i)
                     (mapᴹ (tιₒ {A} {C} {B}) (mapᴹ (dmₒ⁺ {B} {A} {C} g) o₀)) (u , s')
    build f g N (inj₂ co) o₀ q = build-N f g N (inj₂ co) o₀ q
    build f g N {u} {s} (inj₁ a) o₀ q =
      _Trace∷ᵢ_ {inC = f a} (mk-A f g N s a) (build-N f g N (inj₁ (f a)) o₀ q)

  -- ------------------------------------------------------------------------
  -- The relay lemma: the traced normal form of `N CC.∘ Xfwd f g` is `N` with
  -- its domain relabelled, contravariantly by `f` on inputs and covariantly
  -- by `g` on outputs.  States are `⊤ × State N` against `State N`.
  -- ------------------------------------------------------------------------

  Trc-relay-dom : ∀ {A B C} (f : Channel.inType A → Channel.inType B)
                            (g : Channel.outType B → Channel.outType A) (N : Machine B C)
                → Reindex (Trc (Reindex (Pair (Xfwd f g) N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                          (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
                  ≅ᴹ Post N (dmᵢ {B} {A} {C} f) (dmₒ⁺ {B} {A} {C} g)
  Trc-relay-dom {A} {B} {C} f g N =
    MkIso proj₂ (λ s → tt , s) (λ _ → refl) (λ _ → refl)
      (λ {S} {i} {o} tr → chain f g N i o tr)
      (λ {s} {i} {o} (o₀ , q , e) →
         subst (λ z → TraceRel (relay-core f g N) (tt , s) (tιᵢ {A} {C} {B} i)
                               (mapᴹ (tιₒ {A} {C} {B}) z) (tt , _))
               e (build f g N i o₀ q))

  -- Pre-composing with a crossing forwarder is a `Post`.
  ∘-Xfwd-Post : ∀ {A B C} (N : Machine B C)
                (f : Channel.inType A → Channel.inType B)
                (g : Channel.outType B → Channel.outType A)
              → (N CC.∘ Xfwd f g) ≅ᴹ Post N (dmᵢ {B} {A} {C} f) (dmₒ⁺ {B} {A} {C} g)
  ∘-Xfwd-Post {A} {B} {C} N f g =
    ≅ᴹ-trans (∘-Reindex (Xfwd f g) N) (Trc-relay-dom f g N)

  private
    dmᵢ-id : ∀ {A B} (i : Channel.inType (A ⊗ᵀ B))
           → dmᵢ {A} {A} {B} (λ a → a) i ≡ i
    dmᵢ-id (inj₁ _) = refl
    dmᵢ-id (inj₂ _) = refl

    dmₒ⁺-id : ∀ {A B} (o : Channel.outType (A ⊗ᵀ B))
            → dmₒ⁺ {A} {A} {B} (λ α → α) o ≡ o
    dmₒ⁺-id (inj₁ _) = refl
    dmₒ⁺-id (inj₂ _) = refl

  -- The right identity law, with the identity read as a crossing forwarder.
  ∘-identityʳ-Post : ∀ {A B} (N : Machine A B) → (N CC.∘ CC.id) ≅ᴹ N
  ∘-identityʳ-Post {A} {B} N =
    ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl id-is-Xfwd)
    (≅ᴹ-trans (∘-Xfwd-Post N (λ a → a) (λ o → o))
    (≅ᴹ-trans (Post-cong N (dmᵢ {A} {A} {B} (λ a → a)) (λ i → i)
                           (dmₒ⁺ {A} {A} {B} (λ o → o)) (λ o → o)
                           (dmᵢ-id {A} {B}) (dmₒ⁺-id {A} {B}))
              (Post-id N)))
