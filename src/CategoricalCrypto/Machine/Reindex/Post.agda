{-# OPTIONS --safe #-}

-- ============================================================================
-- Covariant output relabelling, and post-composition with a forwarder.
--
-- `Reindex M u v` relabels new-side messages to old-side ones: its output map
-- `v` runs from the new machine's outputs to `M`'s.  That is the right
-- direction for a channel permutation, but the wrong one for a forwarder
-- whose forward map is not invertible — a simulator that turns a leaked
-- message into its length, say.  `Xfwd-cod` in `Reindex.FwdId` accordingly
-- needs the input map of the forwarder to be invertible.
--
-- `Post M u w` keeps `Reindex`'s contravariant input map `u` and makes the
-- output map `w` covariant: a step of `Post M u w` is a step of `M` whose
-- output has been pushed through `w`.  Since `w` need not be injective, the
-- original output is existentially quantified.
--
-- The lemmas are the ones the collapse recipe of `Reindex.Collapse` uses,
-- redone for `Post`: `Pair-Post` (it commutes with `Pair`), `Trc-Post` (it
-- slides through `Trc` when it fixes the traced ports, up to their preimages),
-- `Reindex-Post-slide` (it slides through a `Reindex` along a routing square),
-- `Post-Fwd`/`Xfwd-Post` (a crossing forwarder is a `Post` of `CC.id`, with
-- no invertibility asked of either map), and `∘-collapse-cod-post`: a `Post`
-- of the codomain slides out of a composite.
--
-- The last section is the relay lemma `Trc-relay-cod`, proved directly on
-- the trace normal form of `Reindex`: tracing `M` against a crossing
-- forwarder is `Post M`, because every chain through the traced channel is
-- one `M`-step with at most one relay hop on either side.  It gives
-- `Xfwd-∘-Post` (post-composing any machine with a crossing forwarder is a
-- `Post`) and, at `f = g = id`, the left identity law `∘-identityˡ-Post`.
-- Nothing here uses the identity or associativity laws of `Machine.Iso`;
-- the identity law is derived, not assumed.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex
open import CategoricalCrypto.Machine.Reindex.Slide
open import CategoricalCrypto.Machine.Reindex.Collapse using (cod-routeᵢ; cod-outᵢ)
open import CategoricalCrypto.Machine.Forwarder

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Reindex.Post where

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

  mapᴹ-id : ∀ {X : Type} (o : Maybe X) → mapᴹ (λ x → x) o ≡ o
  mapᴹ-id (just _) = refl
  mapᴹ-id nothing  = refl

  mapᴹ-cong : ∀ {X Y : Type} {v v' : X → Y} → (∀ x → v x ≡ v' x) → ∀ o → mapᴹ v o ≡ mapᴹ v' o
  mapᴹ-cong e (just x) = cong just (e x)
  mapᴹ-cong e nothing  = refl

-- ----------------------------------------------------------------------------
-- The primitive.
-- ----------------------------------------------------------------------------

-- `M` with its inputs relabelled by `u` (new to old, as in `Reindex`) and its
-- outputs pushed forward through `w` (old to new).
Post : ∀ {A B C D} (M : Machine A B)
     → (Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
     → (Channel.outType (A ⊗ᵀ B) → Channel.outType (C ⊗ᵀ D))
     → Machine C D
Post M u w = MkMachine {State = Machine.State M}
  λ s i o s' → ∃ λ o₀ → Machine.stepRel M s (u i) o₀ s' × mapᴹ w o₀ ≡ o

Post-resp-≅ᴹ : ∀ {A B C D} {M N : Machine A B}
               (u : Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
               (w : Channel.outType (A ⊗ᵀ B) → Channel.outType (C ⊗ᵀ D))
             → M ≅ᴹ N → Post M u w ≅ᴹ Post N u w
Post-resp-≅ᴹ u w φ = MkIso (to φ) (from φ) (from∘to φ) (to∘from φ)
  (λ (o₀ , x , e) → o₀ , step-to φ x , e)
  (λ (o₀ , x , e) → o₀ , step-from φ x , e)

Post-cong : ∀ {A B C D} (M : Machine A B)
            (u u' : Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
            (w w' : Channel.outType (A ⊗ᵀ B) → Channel.outType (C ⊗ᵀ D))
          → (∀ i → u i ≡ u' i) → (∀ o → w o ≡ w' o)
          → Post M u w ≅ᴹ Post M u' w'
Post-cong M u u' w w' eu ew = MkIso _ _ (λ _ → refl) (λ _ → refl)
  (λ {s} {i} {o} (o₀ , x , e) →
     o₀ , subst (λ z → Machine.stepRel M s z o₀ _) (eu i) x
        , trans (sym (mapᴹ-cong ew o₀)) e)
  (λ {s} {i} {o} (o₀ , x , e) →
     o₀ , subst (λ z → Machine.stepRel M s z o₀ _) (sym (eu i)) x
        , trans (mapᴹ-cong ew o₀) e)

Post-id : ∀ {A B} (M : Machine A B) → Post M (λ i → i) (λ o → o) ≅ᴹ M
Post-id M = MkIso _ _ (λ _ → refl) (λ _ → refl)
  (λ {s} {i} {o} (o₀ , x , e) →
     subst (λ y → Machine.stepRel M s i y _) (trans (sym (mapᴹ-id o₀)) e) x)
  (λ {s} {i} {o} x → o , x , mapᴹ-id o)

-- A `Post` of a forwarder is a forwarder; unlike `Reindex-Fwd`, no side
-- condition is needed, since a `nothing` output stays `nothing` under `mapᴹ`.
Post-Fwd : ∀ {A B C D} (χ : Channel.inType (A ⊗ᵀ B) → Channel.outType (A ⊗ᵀ B))
                       (κ : Channel.inType (C ⊗ᵀ D) → Channel.outType (C ⊗ᵀ D))
           (u : Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
           (w : Channel.outType (A ⊗ᵀ B) → Channel.outType (C ⊗ᵀ D))
         → (∀ i → w (χ (u i)) ≡ κ i)
         → Post (Fwd χ) u w ≅ᴹ Fwd κ
Post-Fwd χ κ u w sq = MkIso _ _ (λ _ → refl) (λ _ → refl)
  (λ {_} {i} {o} (o₀ , e₁ , e₂) →
     trans (cong just (sym (sq i))) (trans (cong (mapᴹ w) e₁) e₂))
  (λ {_} {i} {o} e → just (χ (u i)) , refl , trans (cong just (sq i)) e)

-- `Reindex` slides through `Post` along a routing square.  The contravariant
-- pair `(u , v)` on the outside becomes `(u' , v')` on the inside, provided
-- the input maps commute and the output maps commute AND every preimage
-- under `q` of a `v`-relabelled output is itself `v'`-relabelled.  The last
-- hypothesis is what a non-injective `q` costs; it holds for the two
-- instances used below, since there `q` acts on the ports that `v` misses
-- only by permuting them.
Reindex-Post-slide :
  ∀ {A B C D E F G H} (T : Machine A B)
    (p  : Channel.inType (C ⊗ᵀ D) → Channel.inType (A ⊗ᵀ B))
    (q  : Channel.outType (A ⊗ᵀ B) → Channel.outType (C ⊗ᵀ D))
    (u  : Channel.inType (E ⊗ᵀ F) → Channel.inType (C ⊗ᵀ D))
    (v  : Channel.outType (E ⊗ᵀ F) → Channel.outType (C ⊗ᵀ D))
    (u' : Channel.inType (G ⊗ᵀ H) → Channel.inType (A ⊗ᵀ B))
    (v' : Channel.outType (G ⊗ᵀ H) → Channel.outType (A ⊗ᵀ B))
    (p' : Channel.inType (E ⊗ᵀ F) → Channel.inType (G ⊗ᵀ H))
    (q' : Channel.outType (G ⊗ᵀ H) → Channel.outType (E ⊗ᵀ F))
  → (∀ i → p (u i) ≡ u' (p' i))
  → (∀ o → q (v' o) ≡ v (q' o))
  → (∀ o₀ o → q o₀ ≡ v o → ∃ λ o₁ → (o₀ ≡ v' o₁) × (q' o₁ ≡ o))
  → Reindex (Post T p q) u v ≅ᴹ Post (Reindex T u' v') p' q'
Reindex-Post-slide T p q u v u' v' p' q' sqᵢ sqₒ pre =
  MkIso _ _ (λ _ → refl) (λ _ → refl)
    (λ {s} {i} {o} (o₀ , x , e) → t s i o o₀ x e)
    (λ {s} {i} {o} (o₁ , x , e) → f s i o o₁ x e)
  where
  t : ∀ s i o o₀ {s'} → Machine.stepRel T s (p (u i)) o₀ s' → mapᴹ q o₀ ≡ mapᴹ v o
    → Machine.stepRel (Post (Reindex T u' v') p' q') s i o s'
  t s i nothing  nothing  x e = nothing , subst (λ z → Machine.stepRel T s z nothing _) (sqᵢ i) x , refl
  t s i (just _) nothing  x e = nothing≢just e
  t s i nothing  (just _) x e = just≢nothing e
  t s i (just b) (just a) x e =
    let (o₁ , a≡ , q'≡) = pre a b (just-inj e)
    in just o₁
     , subst₂ (λ z y → Machine.stepRel T s z (just y) _) (sqᵢ i) a≡ x
     , cong just q'≡
  f : ∀ s i o o₁ {s'} → Machine.stepRel T s (u' (p' i)) (mapᴹ v' o₁) s' → mapᴹ q' o₁ ≡ o
    → Machine.stepRel (Reindex (Post T p q) u v) s i o s'
  f s i o (just c) x e =
    just (v' c) , subst (λ z → Machine.stepRel T s z _ _) (sym (sqᵢ i)) x
                , trans (cong just (sqₒ c)) (cong (mapᴹ v) e)
  f s i o nothing  x e =
    nothing , subst (λ z → Machine.stepRel T s z _ _) (sym (sqᵢ i)) x , cong (mapᴹ v) e

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ ∘κᵢ cdᵢ Xφ

  -- ------------------------------------------------------------------------
  -- `Post` commutes with `Pair`.  The covariant sum map is `⊎ₒ` read
  -- backwards: `⊎ₒ` is only a sum map, its direction is in the implicits.
  -- ------------------------------------------------------------------------

  Pair-Post : ∀ {A B C D A' B' C' D'}
              (M₁ : Machine A B) (M₂ : Machine C D)
              (u₁ : Channel.inType (A' ⊗ᵀ B') → Channel.inType (A ⊗ᵀ B))
              (w₁ : Channel.outType (A ⊗ᵀ B) → Channel.outType (A' ⊗ᵀ B'))
              (u₂ : Channel.inType (C' ⊗ᵀ D') → Channel.inType (C ⊗ᵀ D))
              (w₂ : Channel.outType (C ⊗ᵀ D) → Channel.outType (C' ⊗ᵀ D'))
            → Pair (Post M₁ u₁ w₁) (Post M₂ u₂ w₂)
              ≅ᴹ Post (Pair M₁ M₂) (⊎ᵢ {A} {B} {C} {D} {A'} {B'} {C'} {D'} u₁ u₂)
                                  (⊎ₒ {A'} {B'} {C'} {D'} {A} {B} {C} {D} w₁ w₂)
  Pair-Post {A} {B} {C} {D} {A'} {B'} {C'} {D'} M₁ M₂ u₁ w₁ u₂ w₂ =
    MkIso _ _ (λ _ → refl) (λ _ → refl) t (λ {s} {i} {o} (o₀ , p , e) → f s i o o₀ p e)
    where
    W : Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((C ⊗₀ D ᵀ) ᵀ))
      → Channel.outType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ))
    W = ⊎ₒ {A'} {B'} {C'} {D'} {A} {B} {C} {D} w₁ w₂
    U : Channel.inType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ))
      → Channel.inType ((A ⊗₀ B ᵀ) ⊗ᵀ ((C ⊗₀ D ᵀ) ᵀ))
    U = ⊎ᵢ {A} {B} {C} {D} {A'} {B'} {C'} {D'} u₁ u₂
    t : ∀ {s i o s'}
      → Tensor.CompRel (Post M₁ u₁ w₁) (Post M₂ u₂ w₂) s i o s'
      → ∃ λ o₀ → Tensor.CompRel M₁ M₂ s (U i) o₀ s' × mapᴹ W o₀ ≡ o
    t (Tensor.Step₁ {m = m} (just a  , x , e)) = just (inj₁ a) , Tensor.Step₁ {m = u₁ m} {m' = just a} x , cong (mapᴹ inj₁) e
    t (Tensor.Step₁ {m = m} (nothing , x , e)) = nothing , Tensor.Step₁ {m = u₁ m} {m' = nothing} x , cong (mapᴹ inj₁) e
    t (Tensor.Step₂ {m = m} (just a  , x , e)) = just (inj₂ a) , Tensor.Step₂ {m = u₂ m} {m' = just a} x , cong (mapᴹ inj₂) e
    t (Tensor.Step₂ {m = m} (nothing , x , e)) = nothing , Tensor.Step₂ {m = u₂ m} {m' = nothing} x , cong (mapᴹ inj₂) e
    -- the covariant sum map, past `mapᴹ inj₁`/`mapᴹ inj₂`
    W₁ : ∀ mo → mapᴹ W (mapᴹ inj₁ mo) ≡ mapᴹ inj₁ (mapᴹ w₁ mo)
    W₁ (just _) = refl
    W₁ nothing  = refl
    W₂ : ∀ mo → mapᴹ W (mapᴹ inj₂ mo) ≡ mapᴹ inj₂ (mapᴹ w₂ mo)
    W₂ (just _) = refl
    W₂ nothing  = refl
    go₁ : ∀ s x o o₀ s' → mapᴹ W o₀ ≡ o → CompView M₁ M₂ s (U (inj₁ x)) o₀ s'
        → Tensor.CompRel (Post M₁ u₁ w₁) (Post M₂ u₂ w₂) s (inj₁ x) o s'
    go₁ s x o o₀ s' e (inj₂ (_ , _ , xeq , _)) = inj₁≢inj₂ xeq
    go₁ s x o o₀ s' e (inj₁ (mᵢ , mo , xeq , yeq , steq , q)) =
      subst₂ (λ y z → Tensor.CompRel (Post M₁ u₁ w₁) (Post M₂ u₂ w₂) s (inj₁ x) y (proj₁ s' , z))
             (trans (sym (W₁ mo)) (trans (cong (mapᴹ W) (sym yeq)) e)) (sym steq)
             (Tensor.Step₁ {m = x} {m' = mapᴹ w₁ mo}
                (mo , subst (λ z → Machine.stepRel M₁ (proj₁ s) z mo (proj₁ s')) (sym (inj₁-inj xeq)) q , refl))
    go₂ : ∀ s y o o₀ s' → mapᴹ W o₀ ≡ o → CompView M₁ M₂ s (U (inj₂ y)) o₀ s'
        → Tensor.CompRel (Post M₁ u₁ w₁) (Post M₂ u₂ w₂) s (inj₂ y) o s'
    go₂ s y o o₀ s' e (inj₁ (_ , _ , xeq , _)) = inj₁≢inj₂ (sym xeq)
    go₂ s y o o₀ s' e (inj₂ (mᵢ , mo , xeq , yeq , steq , q)) =
      subst₂ (λ z₀ z → Tensor.CompRel (Post M₁ u₁ w₁) (Post M₂ u₂ w₂) s (inj₂ y) z₀ (z , proj₂ s'))
             (trans (sym (W₂ mo)) (trans (cong (mapᴹ W) (sym yeq)) e)) (sym steq)
             (Tensor.Step₂ {m = y} {m' = mapᴹ w₂ mo}
                (mo , subst (λ z → Machine.stepRel M₂ (proj₂ s) z mo (proj₂ s')) (sym (inj₂-inj xeq)) q , refl))

    f : ∀ s (i : Channel.inType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ)))
          (o : Maybe (Channel.outType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ)))) o₀ {s'}
      → Tensor.CompRel M₁ M₂ s (U i) o₀ s' → mapᴹ W o₀ ≡ o
      → Tensor.CompRel (Post M₁ u₁ w₁) (Post M₂ u₂ w₂) s i o s'
    f s (inj₁ x) o o₀ {s'} p e = go₁ s x o o₀ s' e (comp-view p)
    f s (inj₂ y) o o₀ {s'} p e = go₂ s y o o₀ s' e (comp-view p)
  -- ------------------------------------------------------------------------
  -- A covariant relabelling that fixes the traced channel's ports, together
  -- with their preimages, commutes with `Trc`.  Same shape as `Trc-slide`;
  -- the two extra hypotheses recover the traced port from its image.
  -- ------------------------------------------------------------------------

  Trc-Post : ∀ {X Y Z X' Y' : Channel} (W : Machine (X ⊗₀ Z) (Y ⊗₀ Z))
             (p : Channel.inType ((X' ⊗₀ Z) ⊗ᵀ (Y' ⊗₀ Z))
                → Channel.inType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z)))
             (q : Channel.outType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
                → Channel.outType ((X' ⊗₀ Z) ⊗ᵀ (Y' ⊗₀ Z)))
           → (∀ z → p (dZᵢ {X'} {Y'} {Z} z) ≡ dZᵢ {X} {Y} {Z} z)
           → (∀ z → p (cZₒ {X'} {Y'} {Z} z) ≡ cZₒ {X} {Y} {Z} z)
           → (∀ z → q (dZₒ {X} {Y} {Z} z) ≡ dZₒ {X'} {Y'} {Z} z)
           → (∀ z → q (cZᵢ {X} {Y} {Z} z) ≡ cZᵢ {X'} {Y'} {Z} z)
           → (∀ o z → q o ≡ dZₒ {X'} {Y'} {Z} z → o ≡ dZₒ {X} {Y} {Z} z)
           → (∀ o z → q o ≡ cZᵢ {X'} {Y'} {Z} z → o ≡ cZᵢ {X} {Y} {Z} z)
           → Trc (Post W p q) ≅ᴹ Post (Trc W) p q
  Trc-Post {X} {Y} {Z} {X'} {Y'} W p q pi po qo qi qo⁻ qi⁻ =
    MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl) t
          (λ {_} {i} {o} (O₀ , tr , e) → f tr i o refl e)
    where
    t : ∀ {s I MO s'} → TraceRel (Post W p q) s I MO s'
      → ∃ λ O₀ → TraceRel W s (p I) O₀ s' × mapᴹ q O₀ ≡ MO
    t Trace[ (o₀ , x , e) ] = o₀ , Trace[ x ] , e
    t (_Trace∷ₒ_ {outC = zc} (nothing , x , e) rest) = nothing≢just e
    t (_Trace∷ₒ_ {outC = zc} (just a , x , e) rest) =
      let (O₀ , tr , e') = t rest
      in O₀
       , (subst (λ y → Machine.stepRel W _ (p _) (just y) _) (qo⁻ a zc (just-inj e)) x
          Trace∷ₒ subst (λ y → TraceRel W _ y O₀ _) (po zc) tr)
       , e'
    t (_Trace∷ᵢ_ {inC = zc} (nothing , x , e) rest) = nothing≢just e
    t (_Trace∷ᵢ_ {inC = zc} (just a , x , e) rest) =
      let (O₀ , tr , e') = t rest
      in O₀
       , (subst (λ y → Machine.stepRel W _ (p _) (just y) _) (qi⁻ a zc (just-inj e)) x
          Trace∷ᵢ subst (λ y → TraceRel W _ y O₀ _) (pi zc) tr)
       , e'
    -- Indices generalised and re-tied by equations, so that the recursion is
    -- on the `TraceRel` itself.
    f : ∀ {s I₀ O₀ s'} → TraceRel W s I₀ O₀ s'
      → ∀ I MO → I₀ ≡ p I → mapᴹ q O₀ ≡ MO
      → TraceRel (Post W p q) s I MO s'
    f Trace[ x ] I MO ieq oeq =
      Trace[ (_ , subst (λ a → Machine.stepRel W _ a _ _) ieq x , oeq) ]
    f (_Trace∷ₒ_ {outC = zc} x rest) I MO ieq oeq =
      (just (dZₒ {X} {Y} {Z} zc)
        , subst (λ a → Machine.stepRel W _ a _ _) ieq x
        , cong just (qo zc))
      Trace∷ₒ f rest (cZₒ {X'} {Y'} {Z} zc) MO (sym (po zc)) oeq
    f (_Trace∷ᵢ_ {inC = zc} x rest) I MO ieq oeq =
      (just (cZᵢ {X} {Y} {Z} zc)
        , subst (λ a → Machine.stepRel W _ a _ _) ieq x
        , cong just (qi zc))
      Trace∷ᵢ f rest (dZᵢ {X'} {Y'} {Z} zc) MO (sym (pi zc)) oeq

  -- ------------------------------------------------------------------------
  -- Relabellings of the codomain only, covariant on the output side.  `cdᵢ`
  -- from `Reindex.Slide` serves for the input side unchanged.
  -- ------------------------------------------------------------------------

  -- Relabel the codomain of `Machine B C` to `C'`, leaving the domain alone.
  cdₒ⁺ : ∀ {B C C'} → (Channel.inType C → Channel.inType C')
       → Channel.outType (B ⊗ᵀ C) → Channel.outType (B ⊗ᵀ C')
  cdₒ⁺ vC (inj₁ β) = inj₁ β
  cdₒ⁺ vC (inj₂ c) = inj₂ (vC c)

  -- The same at the traced machine's channel; fixes the traced ports.
  wcₒ⁺ : ∀ {A B C C'} → (Channel.inType C → Channel.inType C')
       → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)) → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B))
  wcₒ⁺ vC (inj₁ x)        = inj₁ x
  wcₒ⁺ vC (inj₂ (inj₁ c)) = inj₂ (inj₁ (vC c))
  wcₒ⁺ vC (inj₂ (inj₂ β)) = inj₂ (inj₂ β)

  -- `∘κₒ` is a permutation of four ports; this is its inverse.
  ∘κₒ⁻ : ∀ {A B C} → Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
       → Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  ∘κₒ⁻ (inj₁ (inj₁ ao)) = inj₁ (inj₁ ao)
  ∘κₒ⁻ (inj₁ (inj₂ bi)) = inj₂ (inj₂ bi)
  ∘κₒ⁻ (inj₂ (inj₁ bo)) = inj₁ (inj₂ bo)
  ∘κₒ⁻ (inj₂ (inj₂ ci)) = inj₂ (inj₁ ci)

  private
    ∘κₒ-rt : ∀ {A B C} (o : Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ)))
           → ∘κₒ {A} {B} {C} (∘κₒ⁻ {A} {B} {C} o) ≡ o
    ∘κₒ-rt (inj₁ (inj₁ _)) = refl
    ∘κₒ-rt (inj₁ (inj₂ _)) = refl
    ∘κₒ-rt (inj₂ (inj₁ _)) = refl
    ∘κₒ-rt (inj₂ (inj₂ _)) = refl

    ∘κₒ-tr : ∀ {A B C} (o : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
           → ∘κₒ⁻ {A} {B} {C} (∘κₒ {A} {B} {C} o) ≡ o
    ∘κₒ-tr (inj₁ (inj₁ _)) = refl
    ∘κₒ-tr (inj₁ (inj₂ _)) = refl
    ∘κₒ-tr (inj₂ (inj₁ _)) = refl
    ∘κₒ-tr (inj₂ (inj₂ _)) = refl

  -- ------------------------------------------------------------------------
  -- The routing squares.  Inside the `Pair`, relabelling `N`'s codomain is a
  -- sum map; at the traced machine's channel it is `wcₒ⁺`; past the trace it
  -- is `cdₒ⁺`.  The input side is `cod-routeᵢ`/`cod-outᵢ` from `Collapse`.
  -- ------------------------------------------------------------------------

  cod-route⁺ₒ : ∀ {A B C C'} (vC : Channel.inType C → Channel.inType C')
                (o : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
              → ⊎ₒ {A} {B} {B} {C'} {A} {B} {B} {C} (λ x → x) (cdₒ⁺ {B} {C} {C'} vC)
                  (∘κₒ {A} {B} {C} o)
                ≡ ∘κₒ {A} {B} {C'} (wcₒ⁺ {A} {B} {C} {C'} vC o)
  cod-route⁺ₒ vC (inj₁ (inj₁ _)) = refl
  cod-route⁺ₒ vC (inj₁ (inj₂ _)) = refl
  cod-route⁺ₒ vC (inj₂ (inj₁ _)) = refl
  cod-route⁺ₒ vC (inj₂ (inj₂ _)) = refl

  private
    -- The same square read from the other corner, which is what the preimage
    -- hypothesis of `Reindex-Post-slide` asks for.
    cod-route⁺ₒ' : ∀ {A B C C'} (vC : Channel.inType C → Channel.inType C')
                   (o₀ : Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ)))
                 → wcₒ⁺ {A} {B} {C} {C'} vC (∘κₒ⁻ {A} {B} {C} o₀)
                   ≡ ∘κₒ⁻ {A} {B} {C'}
                       (⊎ₒ {A} {B} {B} {C'} {A} {B} {B} {C} (λ x → x) (cdₒ⁺ {B} {C} {C'} vC) o₀)
    cod-route⁺ₒ' vC (inj₁ (inj₁ _)) = refl
    cod-route⁺ₒ' vC (inj₁ (inj₂ _)) = refl
    cod-route⁺ₒ' vC (inj₂ (inj₁ _)) = refl
    cod-route⁺ₒ' vC (inj₂ (inj₂ _)) = refl

    cod-pre : ∀ {A B C C'} (vC : Channel.inType C → Channel.inType C')
              (o₀ : Channel.outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ)))
              (o : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B)))
            → ⊎ₒ {A} {B} {B} {C'} {A} {B} {B} {C} (λ x → x) (cdₒ⁺ {B} {C} {C'} vC) o₀
              ≡ ∘κₒ {A} {B} {C'} o
            → ∃ λ o₁ → (o₀ ≡ ∘κₒ {A} {B} {C} o₁) × (wcₒ⁺ {A} {B} {C} {C'} vC o₁ ≡ o)
    cod-pre {A} {B} {C} {C'} vC o₀ o e =
      ∘κₒ⁻ {A} {B} {C} o₀
      , sym (∘κₒ-rt o₀)
      , trans (cod-route⁺ₒ' vC o₀) (trans (cong (∘κₒ⁻ {A} {B} {C'}) e) (∘κₒ-tr o))

  cod-out⁺ₒ : ∀ {A B C C'} (vC : Channel.inType C → Channel.inType C')
              (o : Channel.outType (A ⊗ᵀ C))
            → wcₒ⁺ {A} {B} {C} {C'} vC (tιₒ {A} {C} {B} o)
              ≡ tιₒ {A} {C'} {B} (cdₒ⁺ {A} {C} {C'} vC o)
  cod-out⁺ₒ vC (inj₁ _) = refl
  cod-out⁺ₒ vC (inj₂ _) = refl

  private
    -- Only external ports map to external ports under `wcₒ⁺`.
    cod-out-pre : ∀ {A B C C'} (vC : Channel.inType C → Channel.inType C')
                  (o₀ : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
                  (o : Channel.outType (A ⊗ᵀ C'))
                → wcₒ⁺ {A} {B} {C} {C'} vC o₀ ≡ tιₒ {A} {C'} {B} o
                → ∃ λ o₁ → (o₀ ≡ tιₒ {A} {C} {B} o₁) × (cdₒ⁺ {A} {C} {C'} vC o₁ ≡ o)
    cod-out-pre vC (inj₁ (inj₁ a)) (inj₁ _) e = inj₁ a , refl , cong inj₁ (inj₁-inj (inj₁-inj e))
    cod-out-pre vC (inj₁ (inj₁ a)) (inj₂ _) e = inj₁≢inj₂ e
    cod-out-pre vC (inj₁ (inj₂ _)) (inj₁ _) e = inj₁≢inj₂ (sym (inj₁-inj e))
    cod-out-pre vC (inj₁ (inj₂ _)) (inj₂ _) e = inj₁≢inj₂ e
    cod-out-pre vC (inj₂ (inj₁ c)) (inj₁ _) e = inj₁≢inj₂ (sym e)
    cod-out-pre vC (inj₂ (inj₁ c)) (inj₂ _) e = inj₂ c , refl , cong inj₂ (inj₁-inj (inj₂-inj e))
    cod-out-pre vC (inj₂ (inj₂ _)) (inj₁ _) e = inj₁≢inj₂ (sym e)
    cod-out-pre vC (inj₂ (inj₂ _)) (inj₂ _) e = inj₁≢inj₂ (sym (inj₂-inj e))

    -- `wcₒ⁺` fixes the traced ports, and nothing else lands on them.
    wc-dZₒ : ∀ {A B C C'} (vC : Channel.inType C → Channel.inType C')
             (o : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) z
           → wcₒ⁺ {A} {B} {C} {C'} vC o ≡ dZₒ {A} {C'} {B} z → o ≡ dZₒ {A} {C} {B} z
    wc-dZₒ vC (inj₁ (inj₁ _)) z e = inj₁≢inj₂ (inj₁-inj e)
    wc-dZₒ vC (inj₁ (inj₂ _)) z e = cong (λ x → inj₁ (inj₂ x)) (inj₂-inj (inj₁-inj e))
    wc-dZₒ vC (inj₂ (inj₁ _)) z e = inj₁≢inj₂ (sym e)
    wc-dZₒ vC (inj₂ (inj₂ _)) z e = inj₁≢inj₂ (sym e)

    wc-cZᵢ : ∀ {A B C C'} (vC : Channel.inType C → Channel.inType C')
             (o : Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) z
           → wcₒ⁺ {A} {B} {C} {C'} vC o ≡ cZᵢ {A} {C'} {B} z → o ≡ cZᵢ {A} {C} {B} z
    wc-cZᵢ vC (inj₁ (inj₁ _)) z e = inj₁≢inj₂ e
    wc-cZᵢ vC (inj₁ (inj₂ _)) z e = inj₁≢inj₂ e
    wc-cZᵢ vC (inj₂ (inj₁ _)) z e = inj₁≢inj₂ (inj₂-inj e)
    wc-cZᵢ vC (inj₂ (inj₂ _)) z e = cong (λ x → inj₂ (inj₂ x)) (inj₂-inj (inj₂-inj e))

  -- ------------------------------------------------------------------------
  -- The collapse, step by step, in the order of `∘-collapse-cod`.
  -- ------------------------------------------------------------------------

  -- Sliding the relabelling out of the `Pair`.
  cod-pairP : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
              (uC : Channel.outType C' → Channel.outType C)
              (vC : Channel.inType C → Channel.inType C')
            → Pair M (Post N (cdᵢ {B} {C} {C'} uC) (cdₒ⁺ {B} {C} {C'} vC))
              ≅ᴹ Post (Pair M N)
                   (⊎ᵢ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x) (cdᵢ {B} {C} {C'} uC))
                   (⊎ₒ {A} {B} {B} {C'} {A} {B} {B} {C} (λ x → x) (cdₒ⁺ {B} {C} {C'} vC))
  cod-pairP {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (Pair-resp-≅ᴹ (≅ᴹ-sym (Post-id M)) ≅ᴹ-refl)
             (Pair-Post M N (λ x → x) (λ x → x) (cdᵢ {B} {C} {C'} uC) (cdₒ⁺ {B} {C} {C'} vC))

  -- Through the inner `Reindex`, so that the outer relabelling is
  -- `wcᵢ`/`wcₒ⁺`, the form `Trc-Post` accepts.
  cod-innerP : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
               (uC : Channel.outType C' → Channel.outType C)
               (vC : Channel.inType C → Channel.inType C')
             → Reindex (Pair M (Post N (cdᵢ {B} {C} {C'} uC) (cdₒ⁺ {B} {C} {C'} vC)))
                       (∘κᵢ {A} {B} {C'}) (∘κₒ {A} {B} {C'})
               ≅ᴹ Post (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C}))
                       (wcᵢ {A} {B} {C} {C'} uC) (wcₒ⁺ {A} {B} {C} {C'} vC)
  cod-innerP {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (∘κᵢ {A} {B} {C'}) (∘κₒ {A} {B} {C'}) (cod-pairP M N uC vC))
             (Reindex-Post-slide (Pair M N)
                (⊎ᵢ {A} {B} {B} {C} {A} {B} {B} {C'} (λ x → x) (cdᵢ {B} {C} {C'} uC))
                (⊎ₒ {A} {B} {B} {C'} {A} {B} {B} {C} (λ x → x) (cdₒ⁺ {B} {C} {C'} vC))
                (∘κᵢ {A} {B} {C'}) (∘κₒ {A} {B} {C'})
                (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})
                (wcᵢ {A} {B} {C} {C'} uC) (wcₒ⁺ {A} {B} {C} {C'} vC)
                (cod-routeᵢ {A} {B} {C} {C'} uC) (cod-route⁺ₒ {A} {B} {C} {C'} vC)
                (cod-pre {A} {B} {C} {C'} vC))

  -- Through the trace.
  cod-trcP : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
             (uC : Channel.outType C' → Channel.outType C)
             (vC : Channel.inType C → Channel.inType C')
           → Trc (Reindex (Pair M (Post N (cdᵢ {B} {C} {C'} uC) (cdₒ⁺ {B} {C} {C'} vC)))
                          (∘κᵢ {A} {B} {C'}) (∘κₒ {A} {B} {C'}))
             ≅ᴹ Post (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                     (wcᵢ {A} {B} {C} {C'} uC) (wcₒ⁺ {A} {B} {C} {C'} vC)
  cod-trcP {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (Trc-resp-≅ᴹ (cod-innerP M N uC vC))
             (Trc-Post (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C}))
                       (wcᵢ {A} {B} {C} {C'} uC) (wcₒ⁺ {A} {B} {C} {C'} vC)
                       (λ _ → refl) (λ _ → refl) (λ _ → refl) (λ _ → refl)
                       (wc-dZₒ {A} {B} {C} {C'} vC) (wc-cZᵢ {A} {B} {C} {C'} vC))

  -- Past the outer `Reindex` onto the external ports.
  cod-outerP : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
               (uC : Channel.outType C' → Channel.outType C)
               (vC : Channel.inType C → Channel.inType C')
             → Reindex (Post (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                             (wcᵢ {A} {B} {C} {C'} uC) (wcₒ⁺ {A} {B} {C} {C'} vC))
                       (tιᵢ {A} {C'} {B}) (tιₒ {A} {C'} {B})
               ≅ᴹ Post (Reindex (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                                (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B}))
                       (cdᵢ {A} {C} {C'} uC) (cdₒ⁺ {A} {C} {C'} vC)
  cod-outerP {A} {B} {C} {C'} M N uC vC =
    Reindex-Post-slide (Trc (Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
      (wcᵢ {A} {B} {C} {C'} uC) (wcₒ⁺ {A} {B} {C} {C'} vC)
      (tιᵢ {A} {C'} {B}) (tιₒ {A} {C'} {B})
      (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
      (cdᵢ {A} {C} {C'} uC) (cdₒ⁺ {A} {C} {C'} vC)
      (cod-outᵢ {A} {B} {C} {C'} uC) (cod-out⁺ₒ {A} {B} {C} {C'} vC)
      (cod-out-pre {A} {B} {C} {C'} vC)

  ∘-collapse-cod-post : ∀ {A B C C'} (M : Machine A B) (N : Machine B C)
                        (uC : Channel.outType C' → Channel.outType C)
                        (vC : Channel.inType C → Channel.inType C')
                      → ((Post N (cdᵢ {B} {C} {C'} uC) (cdₒ⁺ {B} {C} {C'} vC)) CC.∘ M)
                        ≅ᴹ Post (N CC.∘ M) (cdᵢ {A} {C} {C'} uC) (cdₒ⁺ {A} {C} {C'} vC)
  ∘-collapse-cod-post {A} {B} {C} {C'} M N uC vC =
    ≅ᴹ-trans (∘-Reindex M (Post N (cdᵢ {B} {C} {C'} uC) (cdₒ⁺ {B} {C} {C'} vC)))
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (tιᵢ {A} {C'} {B}) (tιₒ {A} {C'} {B}) (cod-trcP M N uC vC))
    (≅ᴹ-trans (cod-outerP M N uC vC)
              (Post-resp-≅ᴹ (cdᵢ {A} {C} {C'} uC) (cdₒ⁺ {A} {C} {C'} vC)
                            (≅ᴹ-sym (∘-Reindex M N)))))

  -- ------------------------------------------------------------------------
  -- A crossing forwarder is a `Post` of the identity, with no invertibility
  -- asked of either map: the input map `f` is applied covariantly on the
  -- output side, the backward map `g` contravariantly on the input side.
  -- ------------------------------------------------------------------------

  private
    relay : ∀ {X} → Channel.inType (X ⊗ᵀ X) → Channel.outType (X ⊗ᵀ X)
    relay {X} = Xφ (λ (x : Channel.inType X) → x) (λ (x : Channel.outType X) → x)

  Xfwd-Post : ∀ {A B} (f : Channel.inType A → Channel.inType B)
                      (g : Channel.outType B → Channel.outType A)
            → Xfwd f g ≅ᴹ Post (CC.id {A}) (cdᵢ {A} {A} {B} g) (cdₒ⁺ {A} {A} {B} f)
  Xfwd-Post {A} {B} f g =
    ≅ᴹ-trans (≅ᴹ-sym (Post-Fwd (relay {A}) (Xφ f g)
                               (cdᵢ {A} {A} {B} g) (cdₒ⁺ {A} {A} {B} f) sq))
             (Post-resp-≅ᴹ (cdᵢ {A} {A} {B} g) (cdₒ⁺ {A} {A} {B} f) (≅ᴹ-sym id-is-Xfwd))
    where
    sq : ∀ i → cdₒ⁺ {A} {A} {B} f (relay {A} (cdᵢ {A} {A} {B} g i)) ≡ Xφ f g i
    sq (inj₁ _) = refl
    sq (inj₂ _) = refl

  -- ------------------------------------------------------------------------
  -- The relay lemma, in the trace normal form of `Reindex`.  In
  -- `Trc (Reindex (Pair M (Xfwd f g)) ∘κᵢ ∘κₒ)` the traced channel `B` sits
  -- between `M`'s codomain and the forwarder's domain, and the forwarder is
  -- stateless, total and deterministic.  Every chain therefore contains
  -- exactly one `M`-step: it is preceded by a relay hop iff the input arrived
  -- on `C` (it reaches `M` as `g c`), and followed by one iff `M` emitted on
  -- `B` (it leaves as `f b`).  Forwards, the chain is inverted with
  -- `comp-view` at each step; backwards, the one-, two- or three-step chain
  -- is built by cases on the input port and on `M`'s output.
  -- ------------------------------------------------------------------------

  private
    -- `mapᴹ inj₁`/`mapᴹ inj₂` against a `just` on the same or the other side.
    mapᴹ-inj₁-just : ∀ {X Y : Type} {x : X} (mo : Maybe X)
                   → _≡_ {A = Maybe (X ⊎ Y)} (just (inj₁ x)) (mapᴹ inj₁ mo) → mo ≡ just x
    mapᴹ-inj₁-just (just _) e = cong just (sym (inj₁-inj (just-inj e)))
    mapᴹ-inj₁-just nothing  e = just≢nothing e

    mapᴹ-inj₂-just : ∀ {X Y : Type} {y : Y} (mo : Maybe Y)
                   → _≡_ {A = Maybe (X ⊎ Y)} (just (inj₂ y)) (mapᴹ inj₂ mo) → mo ≡ just y
    mapᴹ-inj₂-just (just _) e = cong just (sym (inj₂-inj (just-inj e)))
    mapᴹ-inj₂-just nothing  e = just≢nothing e

    mapᴹ-inj₁≢inj₂ : ∀ {X Y : Type} {y : Y} (mo : Maybe X) {ℓ} {Z : Type ℓ}
                   → _≡_ {A = Maybe (X ⊎ Y)} (just (inj₂ y)) (mapᴹ inj₁ mo) → Z
    mapᴹ-inj₁≢inj₂ (just _) e = inj₁≢inj₂ (sym (just-inj e))
    mapᴹ-inj₁≢inj₂ nothing  e = just≢nothing e

    mapᴹ-inj₂≢inj₁ : ∀ {X Y : Type} {x : X} (mo : Maybe Y) {ℓ} {Z : Type ℓ}
                   → _≡_ {A = Maybe (X ⊎ Y)} (just (inj₁ x)) (mapᴹ inj₂ mo) → Z
    mapᴹ-inj₂≢inj₁ (just _) e = inj₁≢inj₂ (just-inj e)
    mapᴹ-inj₂≢inj₁ nothing  e = just≢nothing e

  Trc-relay-cod : ∀ {A B C} (M : Machine A B)
                  (f : Channel.inType B → Channel.inType C)
                  (g : Channel.outType C → Channel.outType B)
                → Reindex (Trc (Reindex (Pair M (Xfwd f g)) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                          (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
                  ≅ᴹ Post M (cdᵢ {A} {B} {C} g) (cdₒ⁺ {A} {B} {C} f)
  Trc-relay-cod {A} {B} {C} M f g =
    MkIso proj₁ (λ s → s , tt) (λ _ → refl) (λ _ → refl)
          (λ {_} {i} {o} c → fwd i o c) (λ {_} {i} {o} p → bwd i o p)
    where
    N : Machine B C
    N = Xfwd f g
    W : Machine (A ⊗₀ B) (C ⊗₀ B)
    W = Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})
    S : Type
    S = Machine.State M × ⊤
    Iᵗ Oᵗ Iᵂ Oᵂ Iᴹ Oᴹ : Type
    Iᵗ = Channel.inType (A ⊗ᵀ C)
    Oᵗ = Maybe (Channel.outType (A ⊗ᵀ C))
    Iᵂ = Channel.inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    Oᵂ = Maybe (Channel.outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
    Iᴹ = Channel.inType (A ⊗ᵀ B)
    Oᴹ = Maybe (Channel.outType (A ⊗ᵀ B))

    -- What a step of `Post M (cdᵢ g) (cdₒ⁺ f)` is, with `M`'s input spelled out.
    PostStep : Machine.State M → Iᴹ → Oᵗ → Machine.State M → Type
    PostStep s mᵢ o s' = ∃ λ o₀ → Machine.stepRel M s mᵢ o₀ s' × mapᴹ (cdₒ⁺ {A} {B} {C} f) o₀ ≡ o

    -- The external output of an `M`-step, read back through `∘κₒ` and `tιₒ`.
    ext-out : ∀ (o : Oᵗ) (mo : Oᴹ)
            → mapᴹ (∘κₒ {A} {B} {C}) (mapᴹ (tιₒ {A} {C} {B}) o) ≡ mapᴹ inj₁ mo
            → mapᴹ (cdₒ⁺ {A} {B} {C} f) mo ≡ o
    ext-out nothing         nothing          e = refl
    ext-out nothing         (just _)         e = nothing≢just e
    ext-out (just _)        nothing          e = just≢nothing e
    ext-out (just (inj₁ _)) (just (inj₁ _))  e = cong (λ z → just (inj₁ z)) (sym (inj₁-inj (inj₁-inj (just-inj e))))
    ext-out (just (inj₁ _)) (just (inj₂ _))  e = inj₁≢inj₂ (inj₁-inj (just-inj e))
    ext-out (just (inj₂ _)) (just _)         e = inj₁≢inj₂ (sym (just-inj e))

    -- The external output of a relay hop `B → C` is on `C`.
    relay-out : ∀ (o : Oᵗ) (c : Channel.inType C)
              → mapᴹ (∘κₒ {A} {B} {C}) (mapᴹ (tιₒ {A} {C} {B}) o) ≡ just (inj₂ (inj₂ c))
              → o ≡ just (inj₂ c)
    relay-out nothing         c e = nothing≢just e
    relay-out (just (inj₁ _)) c e = inj₁≢inj₂ (just-inj e)
    relay-out (just (inj₂ _)) c e = cong (λ z → just (inj₂ z)) (inj₂-inj (inj₂-inj (just-inj e)))

    -- No external output is a relay hop `C → B`.
    no-relay-out : ∀ (o : Oᵗ) (bo : Channel.outType B) {ℓ} {Z : Type ℓ}
                 → mapᴹ (∘κₒ {A} {B} {C}) (mapᴹ (tιₒ {A} {C} {B}) o) ≡ just (inj₂ (inj₁ bo)) → Z
    no-relay-out nothing         bo e = nothing≢just e
    no-relay-out (just (inj₁ _)) bo e = inj₁≢inj₂ (just-inj e)
    no-relay-out (just (inj₂ _)) bo e = inj₁≢inj₂ (sym (inj₂-inj (just-inj e)))

    -- ---- Forwards: the chain after the input has reached the forwarder on `B`.
    -- A relay hop `B → C` ends the chain, leaves `M`'s state alone, and
    -- exits on `C`.
    HopOut : S → Oᵗ → S → Channel.inType B → Type
    HopOut sp o sp' b = (proj₁ sp' ≡ proj₁ sp) × (o ≡ just (inj₂ (f b)))

    hop-stop : ∀ {sp sp' : S} (b : Channel.inType B) (o : Oᵗ) {O : Oᵂ} → mapᴹ (tιₒ {A} {C} {B}) o ≡ O
             → CompView M N sp (∘κᵢ {A} {B} {C} (dZᵢ {A} {C} {B} b)) (mapᴹ (∘κₒ {A} {B} {C}) O) sp'
             → HopOut sp o sp' b
    hop-stop b o oe (inj₁ (_ , _ , xeq , _)) = inj₁≢inj₂ (sym xeq)
    hop-stop b o oe (inj₂ (mᵢ , mo , xeq , yeq , steq , q)) =
      steq , relay-out o (f b) (trans (cong (mapᴹ (∘κₒ {A} {B} {C})) oe) (trans yeq (cong (mapᴹ inj₂) (sym q'))))
      where
      q' : just (inj₂ (f b)) ≡ mo
      q' = subst (λ m → just (Xφ f g m) ≡ mo) (sym (inj₂-inj xeq)) q

    hop-noₒ : ∀ {sp sp₁ : S} (b : Channel.inType B) (zc : Channel.outType B) {ℓ} {Z : Type ℓ}
            → CompView M N sp (∘κᵢ {A} {B} {C} (dZᵢ {A} {C} {B} b))
                              (mapᴹ (∘κₒ {A} {B} {C}) (just (dZₒ {A} {C} {B} zc))) sp₁
            → Z
    hop-noₒ b zc (inj₁ (_ , _ , xeq , _)) = inj₁≢inj₂ (sym xeq)
    hop-noₒ b zc (inj₂ (mᵢ , mo , xeq , yeq , steq , q)) =
      inj₁≢inj₂ (sym (just-inj (trans q' (mapᴹ-inj₂-just mo yeq))))
      where
      q' : just (inj₂ (f b)) ≡ mo
      q' = subst (λ m → just (Xφ f g m) ≡ mo) (sym (inj₂-inj xeq)) q

    hop-noᵢ : ∀ {sp sp₁ : S} (b : Channel.inType B) (zc : Channel.inType B) {ℓ} {Z : Type ℓ}
            → CompView M N sp (∘κᵢ {A} {B} {C} (dZᵢ {A} {C} {B} b))
                              (mapᴹ (∘κₒ {A} {B} {C}) (just (cZᵢ {A} {C} {B} zc))) sp₁
            → Z
    hop-noᵢ b zc (inj₁ (_ , _ , xeq , _))       = inj₁≢inj₂ (sym xeq)
    hop-noᵢ b zc (inj₂ (_ , mo , _ , yeq , _)) = mapᴹ-inj₂≢inj₁ mo yeq

    hopᵢ : ∀ {sp : S} {O : Oᵂ} {sp' : S} (b : Channel.inType B) → TraceRel W sp (dZᵢ {A} {C} {B} b) O sp'
         → ∀ (o : Oᵗ) → mapᴹ (tιₒ {A} {C} {B}) o ≡ O → HopOut sp o sp' b
    hopᵢ b Trace[ x ]                        o oe = hop-stop b o oe (comp-view x)
    hopᵢ b (_Trace∷ₒ_ {outC = zc} x rest) o oe = hop-noₒ b zc (comp-view x)
    hopᵢ b (_Trace∷ᵢ_ {inC = zc} x rest)  o oe = hop-noᵢ b zc (comp-view x)

    -- ---- Forwards: the chain from the step at which `M` reads its input.
    M-stop : ∀ {sp sp' : S} (I : Iᵂ) (mᵢ : Iᴹ) (o : Oᵗ) {O : Oᵂ}
           → ∘κᵢ {A} {B} {C} I ≡ inj₁ mᵢ → mapᴹ (tιₒ {A} {C} {B}) o ≡ O
           → CompView M N sp (∘κᵢ {A} {B} {C} I) (mapᴹ (∘κₒ {A} {B} {C}) O) sp'
           → PostStep (proj₁ sp) mᵢ o (proj₁ sp')
    M-stop I mᵢ o e oe (inj₂ (_ , _ , xeq , _)) = inj₁≢inj₂ (trans (sym e) xeq)
    M-stop {sp} {sp'} I mᵢ o e oe (inj₁ (mᵢ' , mo , xeq , yeq , steq , q)) =
      mo , subst (λ z → Machine.stepRel M (proj₁ sp) z mo (proj₁ sp')) (inj₁-inj (trans (sym xeq) e)) q
         , ext-out o mo (trans (cong (mapᴹ (∘κₒ {A} {B} {C})) oe) yeq)

    M-noₒ : ∀ {sp sp₁ : S} (I : Iᵂ) (mᵢ : Iᴹ) (zc : Channel.outType B) {ℓ} {Z : Type ℓ}
          → ∘κᵢ {A} {B} {C} I ≡ inj₁ mᵢ
          → CompView M N sp (∘κᵢ {A} {B} {C} I) (mapᴹ (∘κₒ {A} {B} {C}) (just (dZₒ {A} {C} {B} zc))) sp₁
          → Z
    M-noₒ I mᵢ zc e (inj₂ (_ , _ , xeq , _))       = inj₁≢inj₂ (trans (sym e) xeq)
    M-noₒ I mᵢ zc e (inj₁ (_ , mo , _ , yeq , _)) = mapᴹ-inj₁≢inj₂ mo yeq

    M-relay : ∀ {sp sp₁ sp' : S} (I : Iᵂ) (mᵢ : Iᴹ) (zc : Channel.inType B) (o : Oᵗ)
            → ∘κᵢ {A} {B} {C} I ≡ inj₁ mᵢ
            → CompView M N sp (∘κᵢ {A} {B} {C} I) (mapᴹ (∘κₒ {A} {B} {C}) (just (cZᵢ {A} {C} {B} zc))) sp₁
            → HopOut sp₁ o sp' zc
            → PostStep (proj₁ sp) mᵢ o (proj₁ sp')
    M-relay I mᵢ zc o e (inj₂ (_ , _ , xeq , _)) _ = inj₁≢inj₂ (trans (sym e) xeq)
    M-relay {sp} {sp₁} {sp'} I mᵢ zc o e (inj₁ (mᵢ' , mo , xeq , yeq , steq , q)) (seq , oeq) =
      just (inj₂ zc)
      , subst (λ z → Machine.stepRel M (proj₁ sp) mᵢ (just (inj₂ zc)) z) (sym seq)
          (subst (λ z → Machine.stepRel M (proj₁ sp) mᵢ z (proj₁ sp₁)) (mapᴹ-inj₁-just mo yeq)
            (subst (λ z → Machine.stepRel M (proj₁ sp) z mo (proj₁ sp₁)) (inj₁-inj (trans (sym xeq) e)) q))
      , sym oeq

    M-first : ∀ {sp : S} {I : Iᵂ} {O : Oᵂ} {sp' : S} → TraceRel W sp I O sp'
            → ∀ (mᵢ : Iᴹ) (o : Oᵗ) → ∘κᵢ {A} {B} {C} I ≡ inj₁ mᵢ → mapᴹ (tιₒ {A} {C} {B}) o ≡ O
            → PostStep (proj₁ sp) mᵢ o (proj₁ sp')
    M-first {I = I} Trace[ x ]                        mᵢ o e oe = M-stop I mᵢ o e oe (comp-view x)
    M-first {I = I} (_Trace∷ₒ_ {outC = zc} x rest) mᵢ o e oe = M-noₒ I mᵢ zc e (comp-view x)
    M-first {I = I} (_Trace∷ᵢ_ {inC = zc} x rest)  mᵢ o e oe = M-relay I mᵢ zc o e (comp-view x) (hopᵢ zc rest o oe)

    -- ---- Forwards: the chain from an input on `C`, which must relay first.
    C-stop : ∀ {sp sp' : S} (co : Channel.outType C) (o : Oᵗ) {ℓ} {Z : Type ℓ}
           → CompView M N sp (∘κᵢ {A} {B} {C} (tιᵢ {A} {C} {B} (inj₂ co)))
                             (mapᴹ (∘κₒ {A} {B} {C}) (mapᴹ (tιₒ {A} {C} {B}) o)) sp'
           → Z
    C-stop co o (inj₁ (_ , _ , xeq , _)) = inj₁≢inj₂ (sym xeq)
    C-stop co o (inj₂ (mᵢ , mo , xeq , yeq , steq , q)) =
      no-relay-out o (g co) (trans yeq (cong (mapᴹ inj₂) (sym q')))
      where
      q' : just (inj₁ (g co)) ≡ mo
      q' = subst (λ m → just (Xφ f g m) ≡ mo) (sym (inj₂-inj xeq)) q

    C-hop : ∀ {sp sp₁ sp' : S} (co : Channel.outType C) (zc : Channel.outType B) (o : Oᵗ)
          → CompView M N sp (∘κᵢ {A} {B} {C} (tιᵢ {A} {C} {B} (inj₂ co)))
                            (mapᴹ (∘κₒ {A} {B} {C}) (just (dZₒ {A} {C} {B} zc))) sp₁
          → PostStep (proj₁ sp₁) (inj₂ zc) o (proj₁ sp')
          → PostStep (proj₁ sp) (inj₂ (g co)) o (proj₁ sp')
    C-hop co zc o (inj₁ (_ , _ , xeq , _)) _ = inj₁≢inj₂ (sym xeq)
    C-hop co zc o (inj₂ (mᵢ , mo , xeq , yeq , steq , q)) (o₀ , x , e) =
      o₀ , subst₂ (λ s z → Machine.stepRel M s (inj₂ z) o₀ _) steq (sym zc≡) x , e
      where
      q' : just (inj₁ (g co)) ≡ mo
      q' = subst (λ m → just (Xφ f g m) ≡ mo) (sym (inj₂-inj xeq)) q
      zc≡ : g co ≡ zc
      zc≡ = inj₁-inj (just-inj (trans q' (mapᴹ-inj₂-just mo yeq)))

    C-noᵢ : ∀ {sp sp₁ : S} (co : Channel.outType C) (zc : Channel.inType B) {ℓ} {Z : Type ℓ}
          → CompView M N sp (∘κᵢ {A} {B} {C} (tιᵢ {A} {C} {B} (inj₂ co)))
                            (mapᴹ (∘κₒ {A} {B} {C}) (just (cZᵢ {A} {C} {B} zc))) sp₁
          → Z
    C-noᵢ co zc (inj₁ (_ , _ , xeq , _))       = inj₁≢inj₂ (sym xeq)
    C-noᵢ co zc (inj₂ (_ , mo , _ , yeq , _)) = mapᴹ-inj₂≢inj₁ mo yeq

    fwd : ∀ {sp sp' : S} (i : Iᵗ) (o : Oᵗ)
        → TraceRel W sp (tιᵢ {A} {C} {B} i) (mapᴹ (tιₒ {A} {C} {B}) o) sp'
        → PostStep (proj₁ sp) (cdᵢ {A} {B} {C} g i) o (proj₁ sp')
    fwd (inj₁ a)  o c                                 = M-first c (inj₁ a) o refl refl
    fwd (inj₂ co) o Trace[ x ]                        = C-stop co o (comp-view x)
    fwd (inj₂ co) o (_Trace∷ₒ_ {outC = zc} x rest) = C-hop co zc o (comp-view x) (M-first rest (inj₂ zc) o refl refl)
    fwd (inj₂ co) o (_Trace∷ᵢ_ {inC = zc} x rest)  = C-noᵢ co zc (comp-view x)

    -- ---- Backwards: the chain from the step at which `M` reads its input.
    M-chain : ∀ {s s' : Machine.State M} (I : Iᵂ) (mᵢ : Iᴹ) → ∘κᵢ {A} {B} {C} I ≡ inj₁ mᵢ
            → ∀ (o₀ : Oᴹ) → Machine.stepRel M s mᵢ o₀ s'
            → TraceRel W (s , tt) I (mapᴹ (tιₒ {A} {C} {B}) (mapᴹ (cdₒ⁺ {A} {B} {C} f) o₀)) (s' , tt)
    M-chain {s} {s'} I mᵢ e nothing x =
      Trace[ subst (λ z → Tensor.CompRel M N (s , tt) z nothing (s' , tt)) (sym e)
                   (Tensor.Step₁ {m = mᵢ} {m' = nothing} x) ]
    M-chain {s} {s'} I mᵢ e (just (inj₁ ao)) x =
      Trace[ subst (λ z → Tensor.CompRel M N (s , tt) z (just (inj₁ (inj₁ ao))) (s' , tt)) (sym e)
                   (Tensor.Step₁ {m = mᵢ} {m' = just (inj₁ ao)} x) ]
    M-chain {s} {s'} I mᵢ e (just (inj₂ b)) x =
      _Trace∷ᵢ_ {inC = b}
        (subst (λ z → Tensor.CompRel M N (s , tt) z (just (inj₁ (inj₂ b))) (s' , tt)) (sym e)
               (Tensor.Step₁ {m = mᵢ} {m' = just (inj₂ b)} x))
        Trace[ Tensor.Step₂ {m = inj₁ b} {m' = just (inj₂ (f b))} refl ]

    bwd : ∀ {s s' : Machine.State M} (i : Iᵗ) (o : Oᵗ) → PostStep s (cdᵢ {A} {B} {C} g i) o s'
        → TraceRel W (s , tt) (tιᵢ {A} {C} {B} i) (mapᴹ (tιₒ {A} {C} {B}) o) (s' , tt)
    bwd {s} {s'} (inj₁ a) o (o₀ , x , e) =
      subst (λ z → TraceRel W (s , tt) (tιᵢ {A} {C} {B} (inj₁ a)) (mapᴹ (tιₒ {A} {C} {B}) z) (s' , tt)) e
            (M-chain (tιᵢ {A} {C} {B} (inj₁ a)) (inj₁ a) refl o₀ x)
    bwd {s} {s'} (inj₂ co) o (o₀ , x , e) =
      subst (λ z → TraceRel W (s , tt) (tιᵢ {A} {C} {B} (inj₂ co)) (mapᴹ (tιₒ {A} {C} {B}) z) (s' , tt)) e
            (_Trace∷ₒ_ {outC = g co}
               (Tensor.Step₂ {m = inj₂ co} {m' = just (inj₁ (g co))} refl)
               (M-chain (cZₒ {A} {C} {B} (g co)) (inj₂ (g co)) refl o₀ x))

  -- Post-composing with a crossing forwarder is a `Post`.
  Xfwd-∘-Post : ∀ {A B C} (M : Machine A B)
                (f : Channel.inType B → Channel.inType C)
                (g : Channel.outType C → Channel.outType B)
              → (Xfwd f g CC.∘ M) ≅ᴹ Post M (cdᵢ {A} {B} {C} g) (cdₒ⁺ {A} {B} {C} f)
  Xfwd-∘-Post {A} {B} {C} M f g = ≅ᴹ-trans (∘-Reindex M (Xfwd f g)) (Trc-relay-cod M f g)

  -- ------------------------------------------------------------------------
  -- The left identity law is the relay lemma at `f = g = id`.
  -- ------------------------------------------------------------------------

  ∘-identityˡ-Post : ∀ {A B} (M : Machine A B) → (CC.id CC.∘ M) ≅ᴹ M
  ∘-identityˡ-Post {A} {B} M =
    ≅ᴹ-trans (∘-resp-≅ᴹ (id-is-Xfwd {B}) ≅ᴹ-refl)
    (≅ᴹ-trans (Xfwd-∘-Post M (λ b → b) (λ o → o))
    (≅ᴹ-trans (Post-cong M (cdᵢ {A} {B} {B} (λ o → o)) (λ i → i)
                           (cdₒ⁺ {A} {B} {B} (λ b → b)) (λ o → o) cdᵢ-id cdₒ⁺-id)
              (Post-id M)))
    where
    cdᵢ-id : ∀ i → cdᵢ {A} {B} {B} (λ o → o) i ≡ i
    cdᵢ-id (inj₁ _) = refl
    cdᵢ-id (inj₂ _) = refl
    cdₒ⁺-id : ∀ o → cdₒ⁺ {A} {B} {B} (λ b → b) o ≡ o
    cdₒ⁺-id (inj₁ _) = refl
    cdₒ⁺-id (inj₂ _) = refl
