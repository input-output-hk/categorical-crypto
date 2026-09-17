{-# OPTIONS --safe #-}

-- ============================================================================
-- `_⊗₁_` is a functor for the trace composition `_∘_`:
--
--     (g ∘ f) ⊗₁ (k ∘ h)  ≅ᴹ  (g ⊗₁ k) ∘ (f ⊗₁ h)
--
-- This was the last piece of genuinely categorical content assumed by
-- `CategoricalCrypto.Machine.NAry`, and the hard one: `_∘_` traces out the shared
-- channel, so the two sides are not obviously the same bisimulation.
--
-- The proof rests on an observation about where the difficulty actually is.
-- Every machine builder in sight is one of three things:
--
--   `Pair M₁ M₂`   — `Tensor.CompRel` as a machine, at its own raw indices;
--   `Trc M`        — `TraceRel M` as a machine, likewise;
--   `Reindex M u v` — `M` with its messages relabelled by `u` and `v`.
--
-- `_⊗₁_`, `_∘_` and `modifyStepRel` are all composites of these, and
-- `Pair`/`Trc` carry FULLY GENERAL indices, so `CompRel`/`TraceRel`
-- constructors can be matched directly — none of the `SplitError.Unification
-- Stuck` grief that comes from matching them under a channel reshuffle.  All
-- the reshuffling is pushed into `Reindex`, where it is an ordinary function on
-- messages, and where it composes by `Reindex-fuse` and is compared by
-- `Reindex-cong`.
--
-- The structural lemmas here are the following:
--
--   `Pair-Reindex` — `Pair` commutes with `Reindex`;
--   `Pair-mid4`    — the middle-four interchange for `Pair` (pure re-tagging);
--   `Trc-Pair`     — tracing distributes over `Pair`.  The content: a trace
--                    chain cannot change column, because the port it continues
--                    at is a function of the port it emitted on.
--
-- ============================================================================


open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Reindex where

-- Re-exported: every module of this layer reaches `mapᴹ` and the constructor
-- lemmas through `Reindex`.
open import CategoricalCrypto.Machine.Message public

open _≅ᴹ_

private
  -- Inversion view for `CompRel` at fully general indices.
  comp-view :
    ∀ {A B C D} {M₁ : Machine A B} {M₂ : Machine C D}
      {sp : Machine.State M₁ × Machine.State M₂} {x y sp'}
    → Tensor.CompRel M₁ M₂ sp x y sp'
    → (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (ϵ ⊗R) ↑ᵢ mᵢ) × (y ≡ ((ϵ ⊗R) ↑ₒ_ <$> mo))
         × (proj₂ sp' ≡ proj₂ sp)
         × Machine.stepRel M₁ (proj₁ sp) mᵢ mo (proj₁ sp'))
    ⊎ (∃ λ mᵢ → ∃ λ mo →
         (x ≡ (L⊗ ϵ) ↑ᵢ mᵢ) × (y ≡ ((L⊗ ϵ) ↑ₒ_ <$> mo))
         × (proj₁ sp' ≡ proj₁ sp)
         × Machine.stepRel M₂ (proj₂ sp) mᵢ mo (proj₂ sp'))
  comp-view (Tensor.Step₁ q) = inj₁ (_ , _ , refl , refl , refl , q)
  comp-view (Tensor.Step₂ q) = inj₂ (_ , _ , refl , refl , refl , q)

-- ----------------------------------------------------------------------------
-- Three primitives.  `_⊗₁_`, `_∘_` and `modifyStepRel` are all built from
-- them, and — crucially — `Pair` and `Trc` carry their step relations at
-- FULLY GENERAL indices, so `CompRel`/`TraceRel` constructors can be matched
-- directly.  Every channel reshuffle is pushed into `Reindex`, where it is an
-- ordinary function on messages.
-- ----------------------------------------------------------------------------

Reindex : ∀ {A B C D} (M : Machine A B)
        → (Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
        → (Channel.outType (C ⊗ᵀ D) → Channel.outType (A ⊗ᵀ B))
        → Machine C D
Reindex M u v = MkMachine λ s i o s' → Machine.stepRel M s (u i) (mapᴹ v o) s'

Pair : ∀ {A B C D} (M₁ : Machine A B) (M₂ : Machine C D)
     → Machine (A ⊗₀ B ᵀ) ((C ⊗₀ D ᵀ) ᵀ)
Pair M₁ M₂ = MkMachine (Tensor.CompRel M₁ M₂)

Trc : ∀ {A B C} (M : Machine (A ⊗₀ C) (B ⊗₀ C)) → Machine (A ⊗₀ C) (B ⊗₀ C)
Trc M = MkMachine (TraceRel M)

-- `modifyStepRel` IS `Reindex` with the same map twice.
modifyStepRel-Reindex : ∀ {A B C D} (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
                        (M : Machine A B)
                      → modifyStepRel p M ≡ Reindex M (app (p {In})) (app (p {Out}))
modifyStepRel-Reindex _ _ = refl

-- `_⊗₁_` is `Reindex` of `Pair`.
⊗₁-Reindex-Pair : ∀ {A B C D} (M₁ : Machine A B) (M₂ : Machine C D)
                → (M₁ ⊗₁ M₂) ≡ Reindex (Pair M₁ M₂) (app (⊗σ {m = In})) (app (⊗σ {m = Out}))
⊗₁-Reindex-Pair _ _ = refl

-- ----------------------------------------------------------------------------
-- Congruences and fusion for the three primitives.
-- ----------------------------------------------------------------------------

Reindex-resp-≅ᴹ : ∀ {A B C D} {M N : Machine A B}
                  (u : Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
                  (v : Channel.outType (C ⊗ᵀ D) → Channel.outType (A ⊗ᵀ B))
                → M ≅ᴹ N → Reindex M u v ≅ᴹ Reindex N u v
Reindex-resp-≅ᴹ u v φ =
  MkIso (to φ) (from φ) (from∘to φ) (to∘from φ) (step-to φ) (step-from φ)

Reindex-cong : ∀ {A B C D} (M : Machine A B)
               (u u' : Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
               (v v' : Channel.outType (C ⊗ᵀ D) → Channel.outType (A ⊗ᵀ B))
             → (∀ i → u i ≡ u' i) → (∀ o → v o ≡ v' o)
             → Reindex M u v ≅ᴹ Reindex M u' v'
Reindex-cong M u u' v v' eu ev = MkIso _ _ (λ _ → refl) (λ _ → refl)
  (λ {s} {i} {o} {s'} p → subst₂ (λ x y → Machine.stepRel M s x y _)
                                 (eu i) (mapᴹ-cong ev o) p)
  (λ {s} {i} {o} {s'} p → subst₂ (λ x y → Machine.stepRel M s x y _)
                                 (sym (eu i)) (sym (mapᴹ-cong ev o)) p)

Reindex-fuse : ∀ {A B C D E F} (M : Machine A B) u v u' v'
             → Reindex {C = E} {F} (Reindex {C = C} {D} M u v) u' v'
               ≅ᴹ Reindex M (λ i → u (u' i)) (λ o → v (v' o))
Reindex-fuse M u v u' v' = MkIso _ _ (λ _ → refl) (λ _ → refl)
  (λ {s} {i} {o} p → subst (λ y → Machine.stepRel M s _ y _) (mapᴹ-∘ v v' o) p)
  (λ {s} {i} {o} p → subst (λ y → Machine.stepRel M s _ y _) (sym (mapᴹ-∘ v v' o)) p)

Pair-resp-≅ᴹ : ∀ {A B C D} {M₁ N₁ : Machine A B} {M₂ N₂ : Machine C D}
             → M₁ ≅ᴹ N₁ → M₂ ≅ᴹ N₂ → Pair M₁ M₂ ≅ᴹ Pair N₁ N₂
Pair-resp-≅ᴹ φ ψ = MkIso
  (λ (s₁ , s₂) → to φ s₁ , to ψ s₂)
  (λ (s₁ , s₂) → from φ s₁ , from ψ s₂)
  (λ (s₁ , s₂) → cong₂ _,_ (from∘to φ s₁) (from∘to ψ s₂))
  (λ (s₁ , s₂) → cong₂ _,_ (to∘from φ s₁) (to∘from ψ s₂))
  (go φ ψ) (go (≅ᴹ-sym φ) (≅ᴹ-sym ψ))
  where
  go : ∀ {A B C D} {M₁ N₁ : Machine A B} {M₂ N₂ : Machine C D}
       (φ : M₁ ≅ᴹ N₁) (ψ : M₂ ≅ᴹ N₂) {s i o s'}
     → Tensor.CompRel M₁ M₂ s i o s'
     → Tensor.CompRel N₁ N₂ (to φ (proj₁ s) , to ψ (proj₂ s)) i o
                            (to φ (proj₁ s') , to ψ (proj₂ s'))
  go φ ψ (Tensor.Step₁ p) = Tensor.Step₁ (step-to φ p)
  go φ ψ (Tensor.Step₂ p) = Tensor.Step₂ (step-to ψ p)

Trc-resp-≅ᴹ : ∀ {A B C} {M N : Machine (A ⊗₀ C) (B ⊗₀ C)} → M ≅ᴹ N → Trc M ≅ᴹ Trc N
Trc-resp-≅ᴹ φ = MkIso (to φ) (from φ) (from∘to φ) (to∘from φ) (go φ) (go (≅ᴹ-sym φ))
  where
  go : ∀ {A B C} {M N : Machine (A ⊗₀ C) (B ⊗₀ C)} (ρ : M ≅ᴹ N) {s i o s'}
     → TraceRel M s i o s' → TraceRel N (to ρ s) i o (to ρ s')
  go ρ Trace[ p ]     = Trace[ step-to ρ p ]
  go ρ (p Trace∷ₒ t)  = step-to ρ p Trace∷ₒ go ρ t
  go ρ (p Trace∷ᵢ t)  = step-to ρ p Trace∷ᵢ go ρ t

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine

  -- ------------------------------------------------------------------------
  -- Message-level maps, at the exact channel shapes that `Pair` produces.
  -- Spelling the shapes out avoids asking Agda to invert `_⊗₀_`.
  -- ------------------------------------------------------------------------

  ⊎ᵢ : ∀ {A B C D A' B' C' D'}
     → (Channel.inType (A' ⊗ᵀ B') → Channel.inType (A ⊗ᵀ B))
     → (Channel.inType (C' ⊗ᵀ D') → Channel.inType (C ⊗ᵀ D))
     → Channel.inType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ))
     → Channel.inType ((A  ⊗₀ B  ᵀ) ⊗ᵀ ((C  ⊗₀ D  ᵀ) ᵀ))
  ⊎ᵢ u₁ u₂ (inj₁ x) = inj₁ (u₁ x)
  ⊎ᵢ u₁ u₂ (inj₂ y) = inj₂ (u₂ y)

  ⊎ₒ : ∀ {A B C D A' B' C' D'}
     → (Channel.outType (A' ⊗ᵀ B') → Channel.outType (A ⊗ᵀ B))
     → (Channel.outType (C' ⊗ᵀ D') → Channel.outType (C ⊗ᵀ D))
     → Channel.outType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ))
     → Channel.outType ((A  ⊗₀ B  ᵀ) ⊗ᵀ ((C  ⊗₀ D  ᵀ) ᵀ))
  ⊎ₒ v₁ v₂ (inj₁ x) = inj₁ (v₁ x)
  ⊎ₒ v₁ v₂ (inj₂ y) = inj₂ (v₂ y)

  -- `Pair` commutes with `Reindex`: the two component relabellings become one
  -- sum map.
  Pair-Reindex : ∀ {A B C D A' B' C' D'}
                 (M₁ : Machine A B) (M₂ : Machine C D)
                 (u₁ : Channel.inType (A' ⊗ᵀ B') → Channel.inType (A ⊗ᵀ B))
                 (v₁ : Channel.outType (A' ⊗ᵀ B') → Channel.outType (A ⊗ᵀ B))
                 (u₂ : Channel.inType (C' ⊗ᵀ D') → Channel.inType (C ⊗ᵀ D))
                 (v₂ : Channel.outType (C' ⊗ᵀ D') → Channel.outType (C ⊗ᵀ D))
               → Pair (Reindex M₁ u₁ v₁) (Reindex M₂ u₂ v₂)
                 ≅ᴹ Reindex (Pair M₁ M₂) (⊎ᵢ {A} {B} {C} {D} {A'} {B'} {C'} {D'} u₁ u₂)
                                       (⊎ₒ {A} {B} {C} {D} {A'} {B'} {C'} {D'} v₁ v₂)
  Pair-Reindex {A} {B} {C} {D} {A'} {B'} {C'} {D'} M₁ M₂ u₁ v₁ u₂ v₂ =
    MkIso _ _ (λ _ → refl) (λ _ → refl) t (λ {_} {i} {o} p → f i o p)
    where
    t : ∀ {s i o s'}
      → Tensor.CompRel (Reindex M₁ u₁ v₁) (Reindex M₂ u₂ v₂) s i o s'
      → Tensor.CompRel M₁ M₂ s (⊎ᵢ {A} {B} {C} {D} {A'} {B'} {C'} {D'} u₁ u₂ i)
                               (mapᴹ (⊎ₒ {A} {B} {C} {D} {A'} {B'} {C'} {D'} v₁ v₂) o) s'
    t (Tensor.Step₁ {m' = just _}  p) = Tensor.Step₁ p
    t (Tensor.Step₁ {m' = nothing} p) = Tensor.Step₁ p
    t (Tensor.Step₂ {m' = just _}  p) = Tensor.Step₂ p
    t (Tensor.Step₂ {m' = nothing} p) = Tensor.Step₂ p
    f : ∀ {s s'} (i : Channel.inType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ)))
                 (o : Maybe (Channel.outType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ))))
      → Tensor.CompRel M₁ M₂ s (⊎ᵢ {A} {B} {C} {D} {A'} {B'} {C'} {D'} u₁ u₂ i)
                               (mapᴹ (⊎ₒ {A} {B} {C} {D} {A'} {B'} {C'} {D'} v₁ v₂) o) s'
      → Tensor.CompRel (Reindex M₁ u₁ v₁) (Reindex M₂ u₂ v₂) s i o s'
    -- left component
    f (inj₁ x) (just (inj₁ w)) p with comp-view p
    ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
    ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
    ... | inj₁ (mᵢ , just w' , xeq , yeq , steq , q)
        with inj₁-inj xeq | inj₁-inj (just-inj yeq)
    ... | refl | refl = subst (λ z → Tensor.CompRel _ _ _ _ _ (_ , z)) (sym steq)
                              (Tensor.Step₁ {m = x} {m' = just w} q)
    f (inj₁ x) nothing p with comp-view p
    ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
    ... | inj₁ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
    ... | inj₁ (mᵢ , nothing , xeq , yeq , steq , q) with inj₁-inj xeq
    ... | refl = subst (λ z → Tensor.CompRel _ _ _ _ _ (_ , z)) (sym steq)
                       (Tensor.Step₁ {m = x} {m' = nothing} q)
    f (inj₁ x) (just (inj₂ z)) p with comp-view p
    ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
    ... | inj₁ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
    ... | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
    -- right component
    f (inj₂ y) (just (inj₂ z)) p with comp-view p
    ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
    ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
    ... | inj₂ (mᵢ , just z' , xeq , yeq , steq , q)
        with inj₂-inj xeq | inj₂-inj (just-inj yeq)
    ... | refl | refl = subst (λ z₀ → Tensor.CompRel _ _ _ _ _ (z₀ , _)) (sym steq)
                              (Tensor.Step₂ {m = y} {m' = just z} q)
    f (inj₂ y) nothing p with comp-view p
    ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
    ... | inj₂ (_ , just _ , _ , yeq , _ , _) = nothing≢just yeq
    ... | inj₂ (mᵢ , nothing , xeq , yeq , steq , q) with inj₂-inj xeq
    ... | refl = subst (λ z₀ → Tensor.CompRel _ _ _ _ _ (z₀ , _)) (sym steq)
                       (Tensor.Step₂ {m = y} {m' = nothing} q)
    f (inj₂ y) (just (inj₁ w)) p with comp-view p
    ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
    ... | inj₂ (_ , nothing , _ , yeq , _ , _) = just≢nothing yeq
    ... | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)

  -- ------------------------------------------------------------------------
  -- The middle-four interchange for `Pair`.  All four leaf steps are simply
  -- re-tagged; `mid4ᵢ`/`mid4ₒ` are involutions, which is what lets the second
  -- direction reuse the first at the swapped machines.
  -- ------------------------------------------------------------------------

  mid4ᵢ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄}
        → Channel.inType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ ((A₃ ⊗ᵀ B₃) ⊗₀ (A₄ ⊗ᵀ B₄)))
        → Channel.inType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₃ ⊗ᵀ B₃)) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₄ ⊗ᵀ B₄)))
  mid4ᵢ (inj₁ (inj₁ w)) = inj₁ (inj₁ w)
  mid4ᵢ (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
  mid4ᵢ (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
  mid4ᵢ (inj₂ (inj₂ z)) = inj₂ (inj₂ z)

  mid4ₒ : ∀ {A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄}
        → Channel.outType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₂ ⊗ᵀ B₂)) ⊗₀ ((A₃ ⊗ᵀ B₃) ⊗₀ (A₄ ⊗ᵀ B₄)))
        → Channel.outType (((A₁ ⊗ᵀ B₁) ⊗₀ (A₃ ⊗ᵀ B₃)) ⊗₀ ((A₂ ⊗ᵀ B₂) ⊗₀ (A₄ ⊗ᵀ B₄)))
  mid4ₒ (inj₁ (inj₁ w)) = inj₁ (inj₁ w)
  mid4ₒ (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
  mid4ₒ (inj₂ (inj₁ y)) = inj₁ (inj₂ y)
  mid4ₒ (inj₂ (inj₂ z)) = inj₂ (inj₂ z)

  sw4 : ∀ {W X Y Z : Type} → (W × X) × (Y × Z) → (W × Y) × (X × Z)
  sw4 ((w , x) , (y , z)) = (w , y) , (x , z)

  Pair-mid4-to : ∀ {A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄}
                 (M₁ : Machine A₁ B₁) (M₂ : Machine A₂ B₂)
                 (M₃ : Machine A₃ B₃) (M₄ : Machine A₄ B₄) {s i o s'}
               → Tensor.CompRel (Pair M₁ M₂) (Pair M₃ M₄) s i o s'
               → Tensor.CompRel (Pair M₁ M₃) (Pair M₂ M₄)
                   (sw4 s) (mid4ᵢ i) (mapᴹ mid4ₒ o) (sw4 s')
  Pair-mid4-to _ _ _ _ (Tensor.Step₁ (Tensor.Step₁ {m' = just _}  r)) = Tensor.Step₁ (Tensor.Step₁ r)
  Pair-mid4-to _ _ _ _ (Tensor.Step₁ (Tensor.Step₁ {m' = nothing} r)) = Tensor.Step₁ (Tensor.Step₁ r)
  Pair-mid4-to _ _ _ _ (Tensor.Step₁ (Tensor.Step₂ {m' = just _}  r)) = Tensor.Step₂ (Tensor.Step₁ r)
  Pair-mid4-to _ _ _ _ (Tensor.Step₁ (Tensor.Step₂ {m' = nothing} r)) = Tensor.Step₂ (Tensor.Step₁ r)
  Pair-mid4-to _ _ _ _ (Tensor.Step₂ (Tensor.Step₁ {m' = just _}  r)) = Tensor.Step₁ (Tensor.Step₂ r)
  Pair-mid4-to _ _ _ _ (Tensor.Step₂ (Tensor.Step₁ {m' = nothing} r)) = Tensor.Step₁ (Tensor.Step₂ r)
  Pair-mid4-to _ _ _ _ (Tensor.Step₂ (Tensor.Step₂ {m' = just _}  r)) = Tensor.Step₂ (Tensor.Step₂ r)
  Pair-mid4-to _ _ _ _ (Tensor.Step₂ (Tensor.Step₂ {m' = nothing} r)) = Tensor.Step₂ (Tensor.Step₂ r)

  private
    mid4ᵢ-invol : ∀ {A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄} i
                → mid4ᵢ {A₁} {B₁} {A₃} {B₃} {A₂} {B₂} {A₄} {B₄}
                    (mid4ᵢ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} {A₄} {B₄} i) ≡ i
    mid4ᵢ-invol (inj₁ (inj₁ _)) = refl
    mid4ᵢ-invol (inj₁ (inj₂ _)) = refl
    mid4ᵢ-invol (inj₂ (inj₁ _)) = refl
    mid4ᵢ-invol (inj₂ (inj₂ _)) = refl

    mid4ₒ-invol : ∀ {A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄} o
                → mid4ₒ {A₁} {B₁} {A₃} {B₃} {A₂} {B₂} {A₄} {B₄}
                    (mid4ₒ {A₁} {B₁} {A₂} {B₂} {A₃} {B₃} {A₄} {B₄} o) ≡ o
    mid4ₒ-invol (inj₁ (inj₁ _)) = refl
    mid4ₒ-invol (inj₁ (inj₂ _)) = refl
    mid4ₒ-invol (inj₂ (inj₁ _)) = refl
    mid4ₒ-invol (inj₂ (inj₂ _)) = refl

  Pair-mid4 : ∀ {A₁ B₁ A₂ B₂ A₃ B₃ A₄ B₄}
              (M₁ : Machine A₁ B₁) (M₂ : Machine A₂ B₂)
              (M₃ : Machine A₃ B₃) (M₄ : Machine A₄ B₄)
            → Pair (Pair M₁ M₂) (Pair M₃ M₄)
              ≅ᴹ Reindex (Pair (Pair M₁ M₃) (Pair M₂ M₄)) mid4ᵢ mid4ₒ
  Pair-mid4 M₁ M₂ M₃ M₄ = MkIso sw4 sw4 (λ _ → refl) (λ _ → refl)
    (Pair-mid4-to M₁ M₂ M₃ M₄)
    (λ {_} {i} {o} p → subst₂ (λ x y → Tensor.CompRel (Pair M₁ M₂) (Pair M₃ M₄) _ x y _)
                              (mid4ᵢ-invol i)
                              (trans (mapᴹ-∘ mid4ₒ mid4ₒ o)
                                     (trans (mapᴹ-cong mid4ₒ-invol o) (mapᴹ-id o)))
                              (Pair-mid4-to M₁ M₃ M₂ M₄ p))

  -- ------------------------------------------------------------------------
  -- Tracing distributes over `Pair`.
  --
  -- `π` splits the combined machine's ports into the two columns; `π⁻` puts
  -- them back.  The content is that a trace chain cannot change column: the
  -- port a `Trace∷ₒ`/`Trace∷ᵢ` step continues at is a function of the port it
  -- emitted on, and both live in the same column.
  -- ------------------------------------------------------------------------

  πᵢ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
     → Channel.inType (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))
     → Channel.inType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
  πᵢ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  πᵢ (inj₁ (inj₁ (inj₂ x))) = inj₂ (inj₁ (inj₁ x))
  πᵢ (inj₁ (inj₂ (inj₁ z))) = inj₁ (inj₁ (inj₂ z))
  πᵢ (inj₁ (inj₂ (inj₂ z))) = inj₂ (inj₁ (inj₂ z))
  πᵢ (inj₂ (inj₁ (inj₁ y))) = inj₁ (inj₂ (inj₁ y))
  πᵢ (inj₂ (inj₁ (inj₂ y))) = inj₂ (inj₂ (inj₁ y))
  πᵢ (inj₂ (inj₂ (inj₁ z))) = inj₁ (inj₂ (inj₂ z))
  πᵢ (inj₂ (inj₂ (inj₂ z))) = inj₂ (inj₂ (inj₂ z))

  πₒ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
     → Channel.outType (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))
     → Channel.outType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
  πₒ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  πₒ (inj₁ (inj₁ (inj₂ x))) = inj₂ (inj₁ (inj₁ x))
  πₒ (inj₁ (inj₂ (inj₁ z))) = inj₁ (inj₁ (inj₂ z))
  πₒ (inj₁ (inj₂ (inj₂ z))) = inj₂ (inj₁ (inj₂ z))
  πₒ (inj₂ (inj₁ (inj₁ y))) = inj₁ (inj₂ (inj₁ y))
  πₒ (inj₂ (inj₁ (inj₂ y))) = inj₂ (inj₂ (inj₁ y))
  πₒ (inj₂ (inj₂ (inj₁ z))) = inj₁ (inj₂ (inj₂ z))
  πₒ (inj₂ (inj₂ (inj₂ z))) = inj₂ (inj₂ (inj₂ z))

  πᵢ⁻ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
      → Channel.inType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
      → Channel.inType (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))
  πᵢ⁻ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  πᵢ⁻ (inj₁ (inj₁ (inj₂ z))) = inj₁ (inj₂ (inj₁ z))
  πᵢ⁻ (inj₁ (inj₂ (inj₁ y))) = inj₂ (inj₁ (inj₁ y))
  πᵢ⁻ (inj₁ (inj₂ (inj₂ z))) = inj₂ (inj₂ (inj₁ z))
  πᵢ⁻ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  πᵢ⁻ (inj₂ (inj₁ (inj₂ z))) = inj₁ (inj₂ (inj₂ z))
  πᵢ⁻ (inj₂ (inj₂ (inj₁ y))) = inj₂ (inj₁ (inj₂ y))
  πᵢ⁻ (inj₂ (inj₂ (inj₂ z))) = inj₂ (inj₂ (inj₂ z))

  πₒ⁻ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
      → Channel.outType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
      → Channel.outType (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))
  πₒ⁻ (inj₁ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₁ x))
  πₒ⁻ (inj₁ (inj₁ (inj₂ z))) = inj₁ (inj₂ (inj₁ z))
  πₒ⁻ (inj₁ (inj₂ (inj₁ y))) = inj₂ (inj₁ (inj₁ y))
  πₒ⁻ (inj₁ (inj₂ (inj₂ z))) = inj₂ (inj₂ (inj₁ z))
  πₒ⁻ (inj₂ (inj₁ (inj₁ x))) = inj₁ (inj₁ (inj₂ x))
  πₒ⁻ (inj₂ (inj₁ (inj₂ z))) = inj₁ (inj₂ (inj₂ z))
  πₒ⁻ (inj₂ (inj₂ (inj₁ y))) = inj₂ (inj₁ (inj₂ y))
  πₒ⁻ (inj₂ (inj₂ (inj₂ z))) = inj₂ (inj₂ (inj₂ z))

  private
    πᵢ-πᵢ⁻ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
               (x : Channel.inType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂))))
           → πᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} (πᵢ⁻ x) ≡ x
    πᵢ-πᵢ⁻ (inj₁ (inj₁ (inj₁ _))) = refl
    πᵢ-πᵢ⁻ (inj₁ (inj₁ (inj₂ _))) = refl
    πᵢ-πᵢ⁻ (inj₁ (inj₂ (inj₁ _))) = refl
    πᵢ-πᵢ⁻ (inj₁ (inj₂ (inj₂ _))) = refl
    πᵢ-πᵢ⁻ (inj₂ (inj₁ (inj₁ _))) = refl
    πᵢ-πᵢ⁻ (inj₂ (inj₁ (inj₂ _))) = refl
    πᵢ-πᵢ⁻ (inj₂ (inj₂ (inj₁ _))) = refl
    πᵢ-πᵢ⁻ (inj₂ (inj₂ (inj₂ _))) = refl

    πₒ-πₒ⁻ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} x
           → πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} (πₒ⁻ x) ≡ x
    πₒ-πₒ⁻ (inj₁ (inj₁ (inj₁ _))) = refl
    πₒ-πₒ⁻ (inj₁ (inj₁ (inj₂ _))) = refl
    πₒ-πₒ⁻ (inj₁ (inj₂ (inj₁ _))) = refl
    πₒ-πₒ⁻ (inj₁ (inj₂ (inj₂ _))) = refl
    πₒ-πₒ⁻ (inj₂ (inj₁ (inj₁ _))) = refl
    πₒ-πₒ⁻ (inj₂ (inj₁ (inj₂ _))) = refl
    πₒ-πₒ⁻ (inj₂ (inj₂ (inj₁ _))) = refl
    πₒ-πₒ⁻ (inj₂ (inj₂ (inj₂ _))) = refl

    πₒ⁻-πₒ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} x
           → πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} (πₒ x) ≡ x
    πₒ⁻-πₒ (inj₁ (inj₁ (inj₁ _))) = refl
    πₒ⁻-πₒ (inj₁ (inj₁ (inj₂ _))) = refl
    πₒ⁻-πₒ (inj₁ (inj₂ (inj₁ _))) = refl
    πₒ⁻-πₒ (inj₁ (inj₂ (inj₂ _))) = refl
    πₒ⁻-πₒ (inj₂ (inj₁ (inj₁ _))) = refl
    πₒ⁻-πₒ (inj₂ (inj₁ (inj₂ _))) = refl
    πₒ⁻-πₒ (inj₂ (inj₂ (inj₁ _))) = refl
    πₒ⁻-πₒ (inj₂ (inj₂ (inj₂ _))) = refl

  -- The column injections and the column halves of `π⁻`, at channel-shaped
  -- types (so that nothing has to be inferred through `_⊗₀_`).
  ι₁ᵢ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
      → Channel.inType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁))
      → Channel.inType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
  ι₁ᵢ x = inj₁ x

  ι₂ᵢ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
      → Channel.inType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂))
      → Channel.inType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
  ι₂ᵢ x = inj₂ x

  ι₁ₒ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
      → Channel.outType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁))
      → Channel.outType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
  ι₁ₒ x = inj₁ x

  ι₂ₒ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
      → Channel.outType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂))
      → Channel.outType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
  ι₂ₒ x = inj₂ x

  πᵢ⁻₁ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
       → Channel.inType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁))
       → Channel.inType (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))
  πᵢ⁻₁ (inj₁ (inj₁ x)) = inj₁ (inj₁ (inj₁ x))
  πᵢ⁻₁ (inj₁ (inj₂ z)) = inj₁ (inj₂ (inj₁ z))
  πᵢ⁻₁ (inj₂ (inj₁ y)) = inj₂ (inj₁ (inj₁ y))
  πᵢ⁻₁ (inj₂ (inj₂ z)) = inj₂ (inj₂ (inj₁ z))

  πᵢ⁻₂ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
       → Channel.inType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂))
       → Channel.inType (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))
  πᵢ⁻₂ (inj₁ (inj₁ x)) = inj₁ (inj₁ (inj₂ x))
  πᵢ⁻₂ (inj₁ (inj₂ z)) = inj₁ (inj₂ (inj₂ z))
  πᵢ⁻₂ (inj₂ (inj₁ y)) = inj₂ (inj₁ (inj₂ y))
  πᵢ⁻₂ (inj₂ (inj₂ z)) = inj₂ (inj₂ (inj₂ z))

  πₒ⁻₁ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
       → Channel.outType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁))
       → Channel.outType (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))
  πₒ⁻₁ (inj₁ (inj₁ x)) = inj₁ (inj₁ (inj₁ x))
  πₒ⁻₁ (inj₁ (inj₂ z)) = inj₁ (inj₂ (inj₁ z))
  πₒ⁻₁ (inj₂ (inj₁ y)) = inj₂ (inj₁ (inj₁ y))
  πₒ⁻₁ (inj₂ (inj₂ z)) = inj₂ (inj₂ (inj₁ z))

  πₒ⁻₂ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
       → Channel.outType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂))
       → Channel.outType (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))
  πₒ⁻₂ (inj₁ (inj₁ x)) = inj₁ (inj₁ (inj₂ x))
  πₒ⁻₂ (inj₁ (inj₂ z)) = inj₁ (inj₂ (inj₂ z))
  πₒ⁻₂ (inj₂ (inj₁ y)) = inj₂ (inj₁ (inj₂ y))
  πₒ⁻₂ (inj₂ (inj₂ z)) = inj₂ (inj₂ (inj₂ z))

  private
    πᵢ-πᵢ⁻₁ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} m
            → πᵢ (πᵢ⁻₁ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} m) ≡ ι₁ᵢ m
    πᵢ-πᵢ⁻₁ (inj₁ (inj₁ _)) = refl
    πᵢ-πᵢ⁻₁ (inj₁ (inj₂ _)) = refl
    πᵢ-πᵢ⁻₁ (inj₂ (inj₁ _)) = refl
    πᵢ-πᵢ⁻₁ (inj₂ (inj₂ _)) = refl

    πᵢ-πᵢ⁻₂ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} m
            → πᵢ (πᵢ⁻₂ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} m) ≡ ι₂ᵢ m
    πᵢ-πᵢ⁻₂ (inj₁ (inj₁ _)) = refl
    πᵢ-πᵢ⁻₂ (inj₁ (inj₂ _)) = refl
    πᵢ-πᵢ⁻₂ (inj₂ (inj₁ _)) = refl
    πᵢ-πᵢ⁻₂ (inj₂ (inj₂ _)) = refl

    πₒ-πₒ⁻₁ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} m
            → πₒ (πₒ⁻₁ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} m) ≡ ι₁ₒ m
    πₒ-πₒ⁻₁ (inj₁ (inj₁ _)) = refl
    πₒ-πₒ⁻₁ (inj₁ (inj₂ _)) = refl
    πₒ-πₒ⁻₁ (inj₂ (inj₁ _)) = refl
    πₒ-πₒ⁻₁ (inj₂ (inj₂ _)) = refl

    πₒ-πₒ⁻₂ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} m
            → πₒ (πₒ⁻₂ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} m) ≡ ι₂ₒ m
    πₒ-πₒ⁻₂ (inj₁ (inj₁ _)) = refl
    πₒ-πₒ⁻₂ (inj₁ (inj₂ _)) = refl
    πₒ-πₒ⁻₂ (inj₂ (inj₁ _)) = refl
    πₒ-πₒ⁻₂ (inj₂ (inj₂ _)) = refl

  private
    stepN₁ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Channel}
             (M₁ : Machine (X₁ ⊗₀ Z₁) (Y₁ ⊗₀ Z₁)) (M₂ : Machine (X₂ ⊗₀ Z₂) (Y₂ ⊗₀ Z₂))
             {s₁ s₁' : Machine.State M₁} {s₂ : Machine.State M₂} {m mo}
           → Machine.stepRel M₁ s₁ m mo s₁'
           → Machine.stepRel (Reindex (Pair M₁ M₂) πᵢ πₒ) (s₁ , s₂)
                             (πᵢ⁻₁ m) (mapᴹ πₒ⁻₁ mo) (s₁' , s₂)
    stepN₁ M₁ M₂ {m = m} {mo} p =
      subst₂ (λ a b → Tensor.CompRel M₁ M₂ _ a b _)
             (sym (πᵢ-πᵢ⁻₁ m))
             (sym (trans (mapᴹ-∘ πₒ πₒ⁻₁ mo) (mapᴹ-cong πₒ-πₒ⁻₁ mo)))
             (Tensor.Step₁ {m = m} {m' = mo} p)

    stepN₂ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Channel}
             (M₁ : Machine (X₁ ⊗₀ Z₁) (Y₁ ⊗₀ Z₁)) (M₂ : Machine (X₂ ⊗₀ Z₂) (Y₂ ⊗₀ Z₂))
             {s₁ : Machine.State M₁} {s₂ s₂' : Machine.State M₂} {m mo}
           → Machine.stepRel M₂ s₂ m mo s₂'
           → Machine.stepRel (Reindex (Pair M₁ M₂) πᵢ πₒ) (s₁ , s₂)
                             (πᵢ⁻₂ m) (mapᴹ πₒ⁻₂ mo) (s₁ , s₂')
    stepN₂ M₁ M₂ {m = m} {mo} p =
      subst₂ (λ a b → Tensor.CompRel M₁ M₂ _ a b _)
             (sym (πᵢ-πᵢ⁻₂ m))
             (sym (trans (mapᴹ-∘ πₒ πₒ⁻₂ mo) (mapᴹ-cong πₒ-πₒ⁻₂ mo)))
             (Tensor.Step₂ {m = m} {m' = mo} p)

  -- Every column-1 trace of `M₁` is a trace of the combined machine, and
  -- likewise for column 2.  The ports line up by construction: `πₒ⁻₁` sends
  -- `M₁`'s Z-output port to the combined Z-output port on the left, and `πᵢ⁻₁`
  -- sends the port the chain continues at to the matching combined one.
  trace₁ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Channel}
           (M₁ : Machine (X₁ ⊗₀ Z₁) (Y₁ ⊗₀ Z₁)) (M₂ : Machine (X₂ ⊗₀ Z₂) (Y₂ ⊗₀ Z₂))
           {s₁ s₁' : Machine.State M₁} {s₂ : Machine.State M₂} {m mo}
         → TraceRel M₁ s₁ m mo s₁'
         → TraceRel (Reindex (Pair M₁ M₂) πᵢ πₒ) (s₁ , s₂)
                    (πᵢ⁻₁ m) (mapᴹ πₒ⁻₁ mo) (s₁' , s₂)
  trace₁ M₁ M₂ Trace[ p ]       = Trace[ stepN₁ M₁ M₂ p ]
  trace₁ M₁ M₂ (p Trace∷ₒ rest) = stepN₁ M₁ M₂ p Trace∷ₒ trace₁ M₁ M₂ rest
  trace₁ M₁ M₂ (p Trace∷ᵢ rest) = stepN₁ M₁ M₂ p Trace∷ᵢ trace₁ M₁ M₂ rest

  trace₂ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Channel}
           (M₁ : Machine (X₁ ⊗₀ Z₁) (Y₁ ⊗₀ Z₁)) (M₂ : Machine (X₂ ⊗₀ Z₂) (Y₂ ⊗₀ Z₂))
           {s₁ : Machine.State M₁} {s₂ s₂' : Machine.State M₂} {m mo}
         → TraceRel M₂ s₂ m mo s₂'
         → TraceRel (Reindex (Pair M₁ M₂) πᵢ πₒ) (s₁ , s₂)
                    (πᵢ⁻₂ m) (mapᴹ πₒ⁻₂ mo) (s₁ , s₂')
  trace₂ M₁ M₂ Trace[ p ]       = Trace[ stepN₂ M₁ M₂ p ]
  trace₂ M₁ M₂ (p Trace∷ₒ rest) = stepN₂ M₁ M₂ p Trace∷ₒ trace₂ M₁ M₂ rest
  trace₂ M₁ M₂ (p Trace∷ᵢ rest) = stepN₂ M₁ M₂ p Trace∷ᵢ trace₂ M₁ M₂ rest

  private
    πₒ⁻-ι₁ₒ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (x : Channel.outType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)))
            → πₒ⁻ (ι₁ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} x) ≡ πₒ⁻₁ x
    πₒ⁻-ι₁ₒ (inj₁ (inj₁ _)) = refl
    πₒ⁻-ι₁ₒ (inj₁ (inj₂ _)) = refl
    πₒ⁻-ι₁ₒ (inj₂ (inj₁ _)) = refl
    πₒ⁻-ι₁ₒ (inj₂ (inj₂ _)) = refl

    πₒ⁻-ι₂ₒ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (x : Channel.outType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
            → πₒ⁻ (ι₂ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} x) ≡ πₒ⁻₂ x
    πₒ⁻-ι₂ₒ (inj₁ (inj₁ _)) = refl
    πₒ⁻-ι₂ₒ (inj₁ (inj₂ _)) = refl
    πₒ⁻-ι₂ₒ (inj₂ (inj₁ _)) = refl
    πₒ⁻-ι₂ₒ (inj₂ (inj₂ _)) = refl

    MO-recover : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (MO : Maybe (Channel.outType
                   (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))))
               → mapᴹ πₒ⁻ (mapᴹ πₒ MO) ≡ MO
    MO-recover MO = trans (mapᴹ-∘ πₒ⁻ πₒ MO) (trans (mapᴹ-cong πₒ⁻-πₒ MO) (mapᴹ-id MO))

    recover₁ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
               (MO : Maybe (Channel.outType
                 (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))))
               (mo : Maybe (Channel.outType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁))))
             → mapᴹ πₒ MO ≡ mapᴹ ι₁ₒ mo → MO ≡ mapᴹ πₒ⁻₁ mo
    recover₁ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} MO mo e =
      trans (sym (MO-recover MO))
            (trans (cong (mapᴹ (πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})) e)
                   (trans (mapᴹ-∘ (πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) (ι₁ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)
                          (mapᴹ-cong (πₒ⁻-ι₁ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)))

    recover₂ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
               (MO : Maybe (Channel.outType
                 (((X₁ ⊗₀ X₂) ⊗₀ (Z₁ ⊗₀ Z₂)) ⊗ᵀ ((Y₁ ⊗₀ Y₂) ⊗₀ (Z₁ ⊗₀ Z₂)))))
               (mo : Maybe (Channel.outType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂))))
             → mapᴹ πₒ MO ≡ mapᴹ ι₂ₒ mo → MO ≡ mapᴹ πₒ⁻₂ mo
    recover₂ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} MO mo e =
      trans (sym (MO-recover MO))
            (trans (cong (mapᴹ (πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})) e)
                   (trans (mapᴹ-∘ (πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) (ι₂ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)
                          (mapᴹ-cong (πₒ⁻-ι₂ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)))

  -- The inversion: a trace of the combined machine that starts on a column-1
  -- port is a trace of `M₁`, with `M₂`'s state untouched.  A `Trace∷ₒ`/`Trace∷ᵢ`
  -- step continues at a port determined by the one it emitted on, and `πₒ`
  -- sends the column-1 Z-ports to `M₁`'s — that is why the chain cannot leave
  -- the column.
  trace₁⁻ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Channel}
            (M₁ : Machine (X₁ ⊗₀ Z₁) (Y₁ ⊗₀ Z₁)) (M₂ : Machine (X₂ ⊗₀ Z₂) (Y₂ ⊗₀ Z₂))
            {S S' : Machine.State M₁ × Machine.State M₂} {I MO}
            (m : Channel.inType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)))
          → πᵢ I ≡ ι₁ᵢ m
          → TraceRel (Reindex (Pair M₁ M₂) πᵢ πₒ) S I MO S'
          → ∃ λ mo → (MO ≡ mapᴹ πₒ⁻₁ mo) × (proj₂ S' ≡ proj₂ S)
                    × TraceRel M₁ (proj₁ S) m mo (proj₁ S')
  trace₁⁻ M₁ M₂ {S} {S'} {I} {MO} m eq Trace[ p ]
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x (mapᴹ πₒ MO) S') eq p)
  ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
  ... | inj₁ (mᵢ , mo , xeq , yeq , steq , q) =
    mo
    , recover₁ MO mo yeq
    , steq
    , Trace[ subst (λ z → Machine.stepRel M₁ (proj₁ S) z mo (proj₁ S')) (sym (inj₁-inj xeq)) q ]
  trace₁⁻ M₁ M₂ {S} {S'} m eq (_Trace∷ₒ_ {s' = S''} {outC = inj₁ zc} p rest)
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x _ S'') eq p)
  ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
  ... | inj₁ (mᵢ , nothing , xeq , yeq , steq , q) = nothing≢just (sym yeq)
  ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
      with inj₁-inj xeq | inj₁-inj (just-inj yeq)
  ... | refl | refl with trace₁⁻ M₁ M₂ (inj₂ (inj₂ zc)) refl rest
  ... | mo , MOeq , steq' , tr = mo , MOeq , trans steq' steq , (q Trace∷ₒ tr)
  trace₁⁻ M₁ M₂ {S} {S'} m eq (_Trace∷ₒ_ {s' = S''} {outC = inj₂ zc} p rest)
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x _ S'') eq p)
  ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
  ... | inj₁ (_ , nothing , _ , yeq , _ , _) = nothing≢just (sym yeq)
  ... | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))
  trace₁⁻ M₁ M₂ {S} {S'} m eq (_Trace∷ᵢ_ {s' = S''} {inC = inj₁ zc} p rest)
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x _ S'') eq p)
  ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
  ... | inj₁ (mᵢ , nothing , xeq , yeq , steq , q) = nothing≢just (sym yeq)
  ... | inj₁ (mᵢ , just w , xeq , yeq , steq , q)
      with inj₁-inj xeq | inj₁-inj (just-inj yeq)
  ... | refl | refl with trace₁⁻ M₁ M₂ (inj₁ (inj₂ zc)) refl rest
  ... | mo , MOeq , steq' , tr = mo , MOeq , trans steq' steq , (q Trace∷ᵢ tr)
  trace₁⁻ M₁ M₂ {S} {S'} m eq (_Trace∷ᵢ_ {s' = S''} {inC = inj₂ zc} p rest)
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x _ S'') eq p)
  ... | inj₂ (_ , _ , xeq , _) = inj₁≢inj₂ xeq
  ... | inj₁ (_ , nothing , _ , yeq , _ , _) = nothing≢just (sym yeq)
  ... | inj₁ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (sym (just-inj yeq))

  trace₂⁻ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Channel}
            (M₁ : Machine (X₁ ⊗₀ Z₁) (Y₁ ⊗₀ Z₁)) (M₂ : Machine (X₂ ⊗₀ Z₂) (Y₂ ⊗₀ Z₂))
            {S S' : Machine.State M₁ × Machine.State M₂} {I MO}
            (m : Channel.inType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
          → πᵢ I ≡ ι₂ᵢ m
          → TraceRel (Reindex (Pair M₁ M₂) πᵢ πₒ) S I MO S'
          → ∃ λ mo → (MO ≡ mapᴹ πₒ⁻₂ mo) × (proj₁ S' ≡ proj₁ S)
                    × TraceRel M₂ (proj₂ S) m mo (proj₂ S')
  trace₂⁻ M₁ M₂ {S} {S'} {I} {MO} m eq Trace[ p ]
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x (mapᴹ πₒ MO) S') eq p)
  ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
  ... | inj₂ (mᵢ , mo , xeq , yeq , steq , q) =
    mo , recover₂ MO mo yeq , steq
    , Trace[ subst (λ z → Machine.stepRel M₂ (proj₂ S) z mo (proj₂ S')) (sym (inj₂-inj xeq)) q ]
  trace₂⁻ M₁ M₂ {S} {S'} m eq (_Trace∷ₒ_ {s' = S''} {outC = inj₂ zc} p rest)
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x _ S'') eq p)
  ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
  ... | inj₂ (mᵢ , nothing , xeq , yeq , steq , q) = nothing≢just (sym yeq)
  ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
      with inj₂-inj xeq | inj₂-inj (just-inj yeq)
  ... | refl | refl with trace₂⁻ M₁ M₂ (inj₂ (inj₂ zc)) refl rest
  ... | mo , MOeq , steq' , tr = mo , MOeq , trans steq' steq , (q Trace∷ₒ tr)
  trace₂⁻ M₁ M₂ {S} {S'} m eq (_Trace∷ₒ_ {s' = S''} {outC = inj₁ zc} p rest)
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x _ S'') eq p)
  ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
  ... | inj₂ (_ , nothing , _ , yeq , _ , _) = nothing≢just (sym yeq)
  ... | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)
  trace₂⁻ M₁ M₂ {S} {S'} m eq (_Trace∷ᵢ_ {s' = S''} {inC = inj₂ zc} p rest)
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x _ S'') eq p)
  ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
  ... | inj₂ (mᵢ , nothing , xeq , yeq , steq , q) = nothing≢just (sym yeq)
  ... | inj₂ (mᵢ , just w , xeq , yeq , steq , q)
      with inj₂-inj xeq | inj₂-inj (just-inj yeq)
  ... | refl | refl with trace₂⁻ M₁ M₂ (inj₁ (inj₂ zc)) refl rest
  ... | mo , MOeq , steq' , tr = mo , MOeq , trans steq' steq , (q Trace∷ᵢ tr)
  trace₂⁻ M₁ M₂ {S} {S'} m eq (_Trace∷ᵢ_ {s' = S''} {inC = inj₁ zc} p rest)
    with comp-view (subst (λ x → Tensor.CompRel M₁ M₂ S x _ S'') eq p)
  ... | inj₁ (_ , _ , xeq , _) = inj₁≢inj₂ (sym xeq)
  ... | inj₂ (_ , nothing , _ , yeq , _ , _) = nothing≢just (sym yeq)
  ... | inj₂ (_ , just _ , _ , yeq , _ , _) = inj₁≢inj₂ (just-inj yeq)

  private
    πᵢ⁻-ι₁ᵢ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (m : Channel.inType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)))
            → πᵢ⁻ (ι₁ᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} m) ≡ πᵢ⁻₁ m
    πᵢ⁻-ι₁ᵢ (inj₁ (inj₁ _)) = refl
    πᵢ⁻-ι₁ᵢ (inj₁ (inj₂ _)) = refl
    πᵢ⁻-ι₁ᵢ (inj₂ (inj₁ _)) = refl
    πᵢ⁻-ι₁ᵢ (inj₂ (inj₂ _)) = refl

    πᵢ⁻-ι₂ᵢ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (m : Channel.inType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))
            → πᵢ⁻ (ι₂ᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} m) ≡ πᵢ⁻₂ m
    πᵢ⁻-ι₂ᵢ (inj₁ (inj₁ _)) = refl
    πᵢ⁻-ι₂ᵢ (inj₁ (inj₂ _)) = refl
    πᵢ⁻-ι₂ᵢ (inj₂ (inj₁ _)) = refl
    πᵢ⁻-ι₂ᵢ (inj₂ (inj₂ _)) = refl

    o-recover : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
                (o : Maybe (Channel.outType
                  (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))))
              → mapᴹ πₒ (mapᴹ πₒ⁻ o) ≡ o
    o-recover o = trans (mapᴹ-∘ πₒ πₒ⁻ o) (trans (mapᴹ-cong πₒ-πₒ⁻ o) (mapᴹ-id o))

    outrec₁ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
              (o : Maybe (Channel.outType
                (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))))
              (mo : Maybe (Channel.outType ((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁))))
            → mapᴹ πₒ⁻ o ≡ mapᴹ πₒ⁻₁ mo → o ≡ mapᴹ ι₁ₒ mo
    outrec₁ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} o mo e =
      trans (sym (o-recover o))
            (trans (cong (mapᴹ (πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})) e)
                   (trans (mapᴹ-∘ (πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})
                                  (πₒ⁻₁ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)
                          (mapᴹ-cong (πₒ-πₒ⁻₁ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)))

    outrec₂ : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂}
              (o : Maybe (Channel.outType
                (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))))
              (mo : Maybe (Channel.outType ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂))))
            → mapᴹ πₒ⁻ o ≡ mapᴹ πₒ⁻₂ mo → o ≡ mapᴹ ι₂ₒ mo
    outrec₂ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} o mo e =
      trans (sym (o-recover o))
            (trans (cong (mapᴹ (πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})) e)
                   (trans (mapᴹ-∘ (πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})
                                  (πₒ⁻₂ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)
                          (mapᴹ-cong (πₒ-πₒ⁻₂ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)))

  -- Tracing distributes over `Pair`.
  Trc-Pair : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : Channel}
             (M₁ : Machine (X₁ ⊗₀ Z₁) (Y₁ ⊗₀ Z₁)) (M₂ : Machine (X₂ ⊗₀ Z₂) (Y₂ ⊗₀ Z₂))
           → Pair (Trc M₁) (Trc M₂)
             ≅ᴹ Reindex (Trc (Reindex (Pair M₁ M₂) πᵢ πₒ)) πᵢ⁻ πₒ⁻
  Trc-Pair {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} M₁ M₂ =
    MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl) t (λ {_} {i} {o} p → f i o p)
    where
    t : ∀ {S i o S'} → Tensor.CompRel (Trc M₁) (Trc M₂) S i o S'
      → TraceRel (Reindex (Pair M₁ M₂) (πᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) (πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})) S (πᵢ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} i) (mapᴹ (πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) o) S'
    t (Tensor.Step₁ {m = m} {m' = mo} p) =
      subst₂ (λ a b → TraceRel (Reindex (Pair M₁ M₂) (πᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) (πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})) _ a b _)
             (sym (πᵢ⁻-ι₁ᵢ m))
             (sym (trans (mapᴹ-∘ (πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})
                                 (ι₁ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)
                         (mapᴹ-cong (πₒ⁻-ι₁ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)))
             (trace₁ M₁ M₂ p)
    t (Tensor.Step₂ {m = m} {m' = mo} p) =
      subst₂ (λ a b → TraceRel (Reindex (Pair M₁ M₂) (πᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) (πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})) _ a b _)
             (sym (πᵢ⁻-ι₂ᵢ m))
             (sym (trans (mapᴹ-∘ (πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})
                                 (ι₂ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)
                         (mapᴹ-cong (πₒ⁻-ι₂ₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) mo)))
             (trace₂ M₁ M₂ p)
    f : ∀ {S S'} (i : Channel.inType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂))))
          (o : Maybe (Channel.outType (((X₁ ⊗₀ Z₁) ⊗ᵀ (Y₁ ⊗₀ Z₁)) ⊗₀ ((X₂ ⊗₀ Z₂) ⊗ᵀ (Y₂ ⊗₀ Z₂)))))
      → TraceRel (Reindex (Pair M₁ M₂) (πᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) (πₒ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂})) S (πᵢ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} i) (mapᴹ (πₒ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂}) o) S'
      → Tensor.CompRel (Trc M₁) (Trc M₂) S i o S'
    f {S} {S'} (inj₁ m) o p with trace₁⁻ M₁ M₂ m (πᵢ-πᵢ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} (ι₁ᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} m)) p
    ... | mo , oeq , steq , tr =
      subst₂ (λ b S₀ → Tensor.CompRel (Trc M₁) (Trc M₂) S (inj₁ m) b S₀)
             (sym (outrec₁ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} o mo oeq)) (cong (proj₁ S' ,_) (sym steq))
             (Tensor.Step₁ {m = m} {m' = mo} tr)
    f {S} {S'} (inj₂ m) o p with trace₂⁻ M₁ M₂ m (πᵢ-πᵢ⁻ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} (ι₂ᵢ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} m)) p
    ... | mo , oeq , steq , tr =
      subst₂ (λ b S₀ → Tensor.CompRel (Trc M₁) (Trc M₂) S (inj₂ m) b S₀)
             (sym (outrec₂ {X₁} {Y₁} {Z₁} {X₂} {Y₂} {Z₂} o mo oeq)) (cong (_, proj₂ S') (sym steq))
             (Tensor.Step₂ {m = m} {m' = mo} tr)

  -- ------------------------------------------------------------------------
  -- `tr` as a `Reindex` of `Trc`.
  -- ------------------------------------------------------------------------

  tιᵢ : ∀ {A B C} → Channel.inType (A ⊗ᵀ B) → Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
  tιᵢ (inj₁ a)  = inj₁ (inj₁ a)
  tιᵢ (inj₂ bo) = inj₂ (inj₁ bo)

  tιₒ : ∀ {A B C} → Channel.outType (A ⊗ᵀ B) → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
  tιₒ (inj₁ ao) = inj₁ (inj₁ ao)
  tιₒ (inj₂ bi) = inj₂ (inj₁ bi)

∘-named : ∀ {A B C} (M : Machine A B) (N : Machine B C)
        → (N CC.∘ M) ≡ tr {A} {C} {B} (modifyStepRel ∘σ (M ⊗₁ N))
∘-named _ _ = refl

tr-named : ∀ {A B C} (M : Machine (A ⊗₀ C) (B ⊗₀ C))
         → tr M ≡ modifyStepRel (∣^ˡσ {C = C}) (modifyStepRel ∣ˡσ (Trc M))
tr-named _ = refl

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            tιᵢ tιₒ

  tr-Reindex : ∀ {A B C} (M : Machine (A ⊗₀ C) (B ⊗₀ C))
             → tr M ≅ᴹ Reindex (Trc M) (tιᵢ {A} {B} {C}) (tιₒ {A} {B} {C})
  tr-Reindex {A} {B} {C} M = ≅ᴹ-trans step₁ step₂
    where
    uᵗ : Channel.inType (A ⊗ᵀ B) → Channel.inType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
    uᵗ i = app (∣ˡσ {A} {C} {B ⊗₀ C} {In}) (app (∣^ˡσ {A} {B} {C} {In}) i)

    vᵗ : Channel.outType (A ⊗ᵀ B) → Channel.outType ((A ⊗₀ C) ⊗ᵀ (B ⊗₀ C))
    vᵗ o = app (∣ˡσ {A} {C} {B ⊗₀ C} {Out}) (app (∣^ˡσ {A} {B} {C} {Out}) o)

    step₁ : tr M ≅ᴹ Reindex (Trc M) uᵗ vᵗ
    step₁ = Reindex-fuse (Trc M) (app (∣ˡσ {A} {C} {B ⊗₀ C} {In}))
                                 (app (∣ˡσ {A} {C} {B ⊗₀ C} {Out}))
                                 (app (∣^ˡσ {A} {B} {C} {In}))
                                 (app (∣^ˡσ {A} {B} {C} {Out}))

    step₂ : Reindex (Trc M) uᵗ vᵗ ≅ᴹ Reindex (Trc M) (tιᵢ {A} {B} {C}) (tιₒ {A} {B} {C})
    step₂ = Reindex-cong (Trc M) uᵗ (tιᵢ {A} {B} {C}) vᵗ (tιₒ {A} {B} {C})
                         (λ { (inj₁ _) → refl ; (inj₂ _) → refl })
                         (λ { (inj₁ _) → refl ; (inj₂ _) → refl })

  -- ------------------------------------------------------------------------
  -- `_∘_` as a `Reindex` of a `Trc` of a `Reindex` of a `Pair`.
  -- ------------------------------------------------------------------------

  ∘κᵢ : ∀ {A B C} → Channel.inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
      → Channel.inType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
  ∘κᵢ {A} {B} {C} i = app (⊗σ {A} {B} {B} {C} {In}) (app (∘σ {A} {B} {C} {In}) i)

  ∘κₒ : ∀ {A B C} → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
      → Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
  ∘κₒ {A} {B} {C} o = app (⊗σ {A} {B} {B} {C} {Out}) (app (∘σ {A} {B} {C} {Out}) o)

  ∘-core : ∀ {A B C} (M : Machine A B) (N : Machine B C)
         → modifyStepRel (∘σ {A} {B} {C}) (M ⊗₁ N)
           ≅ᴹ Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})
  ∘-core {A} {B} {C} M N =
    Reindex-fuse (Pair M N) (app (⊗σ {A} {B} {B} {C} {In})) (app (⊗σ {A} {B} {B} {C} {Out}))
                            (app (∘σ {A} {B} {C} {In})) (app (∘σ {A} {B} {C} {Out}))

  ∘-Reindex : ∀ {A B C} (M : Machine A B) (N : Machine B C)
            → (N CC.∘ M)
              ≅ᴹ Reindex (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                         (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
  ∘-Reindex {A} {B} {C} M N =
    ≅ᴹ-trans (tr-Reindex (modifyStepRel (∘σ {A} {B} {C}) (M ⊗₁ N)))
             (Reindex-resp-≅ᴹ (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
                              (Trc-resp-≅ᴹ (∘-core M N)))
