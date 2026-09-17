{-# OPTIONS --safe #-}

-- ============================================================================
-- Covariant output relabelling, composition with a forwarder, and the two
-- identity laws.
--
-- `Reindex M u v` relabels new-side messages to old-side ones: its output map
-- `v` runs from the new machine's outputs to `M`'s.  That is the right
-- direction for a channel permutation, but the wrong one for a forwarder
-- whose forward map is not invertible — a simulator that turns a leaked
-- message into its length, say.  `Xfwd-cod` below accordingly needs the
-- input map of the forwarder to be invertible.
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
-- of the codomain slides out of a composite.  `Post-is-Reindex` turns a
-- `Post` back into a `Reindex` when the covariant output map is invertible,
-- which is what `Xfwd-dom` and `Xfwd-cod` need.
--
-- The last section holds the two relay lemmas, proved directly on the trace
-- normal form `Trc (Reindex (Pair M N) ∘κᵢ ∘κₒ)` of `N CC.∘ M`.  When one
-- component is a crossing forwarder, every chain through the traced channel
-- `B` is one step of the other machine with at most one relay hop on either
-- side, so the composite is a `Post` of that machine.  `Trc-relay-cod` has
-- the forwarder in the second component and relabels `M`'s codomain;
-- `Trc-relay-dom` has it in the first and relabels `N`'s domain.  The two
-- proofs are mirror images: they share the step views, the step builders and
-- the routing table of `∘κᵢ`/`∘κₒ`, and differ only in which component the
-- forwarder is.  The corollaries are `Xfwd-∘-Post` and `∘-Xfwd-Post`
-- (composing with a crossing forwarder on either side is a `Post`) and, at
-- `f = g = id`, the identity laws `∘-identityˡ-Post` and `∘-identityʳ-Post`.
-- Nothing here uses the identity or associativity laws of `Machine.Iso`; the
-- identity laws are derived, not assumed.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex
open import CategoricalCrypto.Machine.Reindex.Slide
open import CategoricalCrypto.Machine.Reindex.Collapse using (cod-routeᵢ; cod-outᵢ)
open import CategoricalCrypto.Machine.Forwarder

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Message
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Machine.Reindex.Post where

open Channel

open _≅ᴹ_

-- ----------------------------------------------------------------------------
-- The primitive.
-- ----------------------------------------------------------------------------

-- `M` with its inputs relabelled by `u` (new to old, as in `Reindex`) and its
-- outputs pushed forward through `w` (old to new).
Post : ∀ {A B C D} (M : Machine A B)
     → (inType (C ⊗ᵀ D) → inType (A ⊗ᵀ B))
     → (outType (A ⊗ᵀ B) → outType (C ⊗ᵀ D))
     → Machine C D
Post M u w = MkMachine {State = Machine.State M}
  λ s i o s' → ∃ λ o₀ → Machine.stepRel M s (u i) o₀ s' × mapᴹ w o₀ ≡ o

Post-resp-≅ᴹ : ∀ {A B C D} {M N : Machine A B}
               (u : inType (C ⊗ᵀ D) → inType (A ⊗ᵀ B))
               (w : outType (A ⊗ᵀ B) → outType (C ⊗ᵀ D))
             → M ≅ᴹ N → Post M u w ≅ᴹ Post N u w
Post-resp-≅ᴹ u w φ = MkIso (to φ) (from φ) (from∘to φ) (to∘from φ)
  (λ (o₀ , x , e) → o₀ , step-to φ x , e)
  (λ (o₀ , x , e) → o₀ , step-from φ x , e)

Post-cong : ∀ {A B C D} (M : Machine A B)
            (u u' : inType (C ⊗ᵀ D) → inType (A ⊗ᵀ B))
            (w w' : outType (A ⊗ᵀ B) → outType (C ⊗ᵀ D))
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

-- A `Post` of a forwarder is a forwarder; unlike the `Reindex` of one, no
-- side condition is needed, since a `nothing` output stays `nothing` under
-- `mapᴹ`.
Post-Fwd : ∀ {A B C D} (χ : inType (A ⊗ᵀ B) → outType (A ⊗ᵀ B))
                       (κ : inType (C ⊗ᵀ D) → outType (C ⊗ᵀ D))
           (u : inType (C ⊗ᵀ D) → inType (A ⊗ᵀ B))
           (w : outType (A ⊗ᵀ B) → outType (C ⊗ᵀ D))
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
    (p  : inType (C ⊗ᵀ D) → inType (A ⊗ᵀ B))
    (q  : outType (A ⊗ᵀ B) → outType (C ⊗ᵀ D))
    (u  : inType (E ⊗ᵀ F) → inType (C ⊗ᵀ D))
    (v  : outType (E ⊗ᵀ F) → outType (C ⊗ᵀ D))
    (u' : inType (G ⊗ᵀ H) → inType (A ⊗ᵀ B))
    (v' : outType (G ⊗ᵀ H) → outType (A ⊗ᵀ B))
    (p' : inType (E ⊗ᵀ F) → inType (G ⊗ᵀ H))
    (q' : outType (G ⊗ᵀ H) → outType (E ⊗ᵀ F))
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

-- ----------------------------------------------------------------------------
-- The traced core of `N CC.∘ M`, as `∘-Reindex` presents it.  `relay-core`
-- is the instance whose first component is a crossing forwarder.
-- ----------------------------------------------------------------------------

private
  Core : ∀ {A B C} (M : Machine A B) (N : Machine B C) → Machine (A ⊗₀ B) (C ⊗₀ B)
  Core {A} {B} {C} M N = Reindex (Pair M N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})

relay-core : ∀ {A B C} (f : inType A → inType B)
                       (g : outType B → outType A)
             (N : Machine B C) → Machine (A ⊗₀ B) (C ⊗₀ B)
relay-core f g N = Core (Xfwd f g) N

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ ∘κᵢ cdᵢ cdₒ dmᵢ dmₒ Xφ

  -- ------------------------------------------------------------------------
  -- `Post` commutes with `Pair`.  The covariant sum map is `⊎ₒ` read
  -- backwards: `⊎ₒ` is only a sum map, its direction is in the implicits.
  -- ------------------------------------------------------------------------

  Pair-Post : ∀ {A B C D A' B' C' D'}
              (M₁ : Machine A B) (M₂ : Machine C D)
              (u₁ : inType (A' ⊗ᵀ B') → inType (A ⊗ᵀ B))
              (w₁ : outType (A ⊗ᵀ B) → outType (A' ⊗ᵀ B'))
              (u₂ : inType (C' ⊗ᵀ D') → inType (C ⊗ᵀ D))
              (w₂ : outType (C ⊗ᵀ D) → outType (C' ⊗ᵀ D'))
            → Pair (Post M₁ u₁ w₁) (Post M₂ u₂ w₂)
              ≅ᴹ Post (Pair M₁ M₂) (⊎ᵢ {A} {B} {C} {D} {A'} {B'} {C'} {D'} u₁ u₂)
                                  (⊎ₒ {A'} {B'} {C'} {D'} {A} {B} {C} {D} w₁ w₂)
  Pair-Post {A} {B} {C} {D} {A'} {B'} {C'} {D'} M₁ M₂ u₁ w₁ u₂ w₂ =
    MkIso _ _ (λ _ → refl) (λ _ → refl) t (λ {s} {i} {o} (o₀ , p , e) → f s i o o₀ p e)
    where
    W : outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((C ⊗₀ D ᵀ) ᵀ))
      → outType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ))
    W = ⊎ₒ {A'} {B'} {C'} {D'} {A} {B} {C} {D} w₁ w₂
    U : inType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ))
      → inType ((A ⊗₀ B ᵀ) ⊗ᵀ ((C ⊗₀ D ᵀ) ᵀ))
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

    f : ∀ s (i : inType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ)))
          (o : Maybe (outType ((A' ⊗₀ B' ᵀ) ⊗ᵀ ((C' ⊗₀ D' ᵀ) ᵀ)))) o₀ {s'}
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
             (p : inType ((X' ⊗₀ Z) ⊗ᵀ (Y' ⊗₀ Z))
                → inType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z)))
             (q : outType ((X ⊗₀ Z) ⊗ᵀ (Y ⊗₀ Z))
                → outType ((X' ⊗₀ Z) ⊗ᵀ (Y' ⊗₀ Z)))
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
  -- Relabellings of one end only, covariant on the output side.  `cdᵢ` and
  -- `dmᵢ` from `Reindex.Slide` serve for the input side unchanged.
  -- ------------------------------------------------------------------------

  -- Relabel the codomain of `Machine B C` to `C'`, leaving the domain alone.
  cdₒ⁺ : ∀ {B C C'} → (inType C → inType C')
       → outType (B ⊗ᵀ C) → outType (B ⊗ᵀ C')
  cdₒ⁺ vC (inj₁ β) = inj₁ β
  cdₒ⁺ vC (inj₂ c) = inj₂ (vC c)

  -- Relabel the domain of `Machine A B` to `A'`, leaving the codomain alone.
  dmₒ⁺ : ∀ {A A' B} → (outType A → outType A')
       → outType (A ⊗ᵀ B) → outType (A' ⊗ᵀ B)
  dmₒ⁺ vA (inj₁ α) = inj₁ (vA α)
  dmₒ⁺ vA (inj₂ b) = inj₂ b

  -- `cdₒ⁺` at the traced machine's channel; fixes the traced ports.
  wcₒ⁺ : ∀ {A B C C'} → (inType C → inType C')
       → outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)) → outType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B))
  wcₒ⁺ vC (inj₁ x)        = inj₁ x
  wcₒ⁺ vC (inj₂ (inj₁ c)) = inj₂ (inj₁ (vC c))
  wcₒ⁺ vC (inj₂ (inj₂ β)) = inj₂ (inj₂ β)

  -- ------------------------------------------------------------------------
  -- The routing table of `∘κᵢ`/`∘κₒ`.  The traced core `Core M N` has the
  -- channel `(A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)`, whose port positions are `M`'s four and
  -- `N`'s four; `∘κᵢ`/`∘κₒ` send `M`'s to the first summand of the `Pair`'s
  -- channel and `N`'s to the second.  The external ports `tιᵢ`/`tιₒ` of
  -- `Reindex` and the traced ports of `Reindex.Slide` are, by definition,
  --
  --   tιᵢ (inj₁ a)  = Lᵢ (inj₁ a)      tιₒ (inj₁ ao) = Lₒ (inj₁ ao)
  --   tιᵢ (inj₂ co) = Rᵢ (inj₂ co)     tιₒ (inj₂ ci) = Rₒ (inj₂ ci)
  --   cZₒ bo        = Lᵢ (inj₂ bo)     cZᵢ b         = Lₒ (inj₂ b)
  --   dZᵢ b         = Rᵢ (inj₁ b)      dZₒ bo        = Rₒ (inj₁ bo)
  --
  -- and the relay proofs below use these identities silently.  An opaque
  -- signature is checked without unfolding, so it cannot spell messages out
  -- as sums; the port names do so once, in bodies.
  -- ------------------------------------------------------------------------

  private
    Lᵢ : ∀ {A B C} → inType (A ⊗ᵀ B) → inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    Lᵢ (inj₁ a)  = inj₁ (inj₁ a)
    Lᵢ (inj₂ bo) = inj₂ (inj₂ bo)

    Lₒ : ∀ {A B C} → outType (A ⊗ᵀ B) → outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    Lₒ (inj₁ ao) = inj₁ (inj₁ ao)
    Lₒ (inj₂ b)  = inj₂ (inj₂ b)

    Rᵢ : ∀ {A B C} → inType (B ⊗ᵀ C) → inType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    Rᵢ (inj₁ b)  = inj₁ (inj₂ b)
    Rᵢ (inj₂ co) = inj₂ (inj₁ co)

    Rₒ : ∀ {A B C} → outType (B ⊗ᵀ C) → outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
    Rₒ (inj₁ bo) = inj₁ (inj₂ bo)
    Rₒ (inj₂ ci) = inj₂ (inj₁ ci)

    -- The `Pair`'s channel: `M`'s ports in the first summand, `N`'s in the second.
    κLᵢ : ∀ {A B C} → inType (A ⊗ᵀ B) → inType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
    κLᵢ x = inj₁ x

    κRᵢ : ∀ {A B C} → inType (B ⊗ᵀ C) → inType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
    κRᵢ j = inj₂ j

    κLₒ : ∀ {A B C} → outType (A ⊗ᵀ B) → outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
    κLₒ y = inj₁ y

    κRₒ : ∀ {A B C} → outType (B ⊗ᵀ C) → outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
    κRₒ y = inj₂ y

    -- `∘κᵢ`/`∘κₒ` route each component's ports to its summand.
    ∘κᵢ-L : ∀ {A B C} (x : inType (A ⊗ᵀ B))
          → ∘κᵢ {A} {B} {C} (Lᵢ {A} {B} {C} x) ≡ κLᵢ {A} {B} {C} x
    ∘κᵢ-L (inj₁ _) = refl
    ∘κᵢ-L (inj₂ _) = refl

    ∘κᵢ-R : ∀ {A B C} (j : inType (B ⊗ᵀ C))
          → ∘κᵢ {A} {B} {C} (Rᵢ {A} {B} {C} j) ≡ κRᵢ {A} {B} {C} j
    ∘κᵢ-R (inj₁ _) = refl
    ∘κᵢ-R (inj₂ _) = refl

    ∘κₒ-L : ∀ {A B C} (y : outType (A ⊗ᵀ B))
          → ∘κₒ {A} {B} {C} (Lₒ {A} {B} {C} y) ≡ κLₒ {A} {B} {C} y
    ∘κₒ-L (inj₁ _) = refl
    ∘κₒ-L (inj₂ _) = refl

    ∘κₒ-R : ∀ {A B C} (y : outType (B ⊗ᵀ C))
          → ∘κₒ {A} {B} {C} (Rₒ {A} {B} {C} y) ≡ κRₒ {A} {B} {C} y
    ∘κₒ-R (inj₁ _) = refl
    ∘κₒ-R (inj₂ _) = refl

  -- `∘κₒ` is a permutation of four ports; this is its inverse.
  ∘κₒ⁻ : ∀ {A B C} → outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ))
       → outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))
  ∘κₒ⁻ {A} {B} {C} (inj₁ y) = Lₒ {A} {B} {C} y
  ∘κₒ⁻ {A} {B} {C} (inj₂ y) = Rₒ {A} {B} {C} y

  private
    ∘κₒ-rt : ∀ {A B C} (o : outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ)))
           → ∘κₒ {A} {B} {C} (∘κₒ⁻ {A} {B} {C} o) ≡ o
    ∘κₒ-rt (inj₁ (inj₁ _)) = refl
    ∘κₒ-rt (inj₁ (inj₂ _)) = refl
    ∘κₒ-rt (inj₂ (inj₁ _)) = refl
    ∘κₒ-rt (inj₂ (inj₂ _)) = refl

    ∘κₒ-tr : ∀ {A B C} (o : outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
           → ∘κₒ⁻ {A} {B} {C} (∘κₒ {A} {B} {C} o) ≡ o
    ∘κₒ-tr (inj₁ (inj₁ _)) = refl
    ∘κₒ-tr (inj₁ (inj₂ _)) = refl
    ∘κₒ-tr (inj₂ (inj₁ _)) = refl
    ∘κₒ-tr (inj₂ (inj₂ _)) = refl

    -- Reading `∘κₒ` backwards: an output that lands in a summand came from
    -- that component's port.
    ∘κₒ-L⁻ : ∀ {A B C} (o : outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) (y : outType (A ⊗ᵀ B))
           → ∘κₒ {A} {B} {C} o ≡ κLₒ {A} {B} {C} y → o ≡ Lₒ {A} {B} {C} y
    ∘κₒ-L⁻ {A} {B} {C} o y e = trans (sym (∘κₒ-tr o)) (cong (∘κₒ⁻ {A} {B} {C}) e)

    ∘κₒ-R⁻ : ∀ {A B C} (o : outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) (y : outType (B ⊗ᵀ C))
           → ∘κₒ {A} {B} {C} o ≡ κRₒ {A} {B} {C} y → o ≡ Rₒ {A} {B} {C} y
    ∘κₒ-R⁻ {A} {B} {C} o y e = trans (sym (∘κₒ-tr o)) (cong (∘κₒ⁻ {A} {B} {C}) e)

    -- The two components' output ports are told apart by `∘κₒ`.
    Lₒ-inj : ∀ {A B C} (y y' : outType (A ⊗ᵀ B))
           → Lₒ {A} {B} {C} y ≡ Lₒ {A} {B} {C} y' → y ≡ y'
    Lₒ-inj {A} {B} {C} y y' e =
      inj₁-inj (trans (sym (∘κₒ-L {A} {B} {C} y))
                      (trans (cong (∘κₒ {A} {B} {C}) e) (∘κₒ-L {A} {B} {C} y')))

    Rₒ-inj : ∀ {A B C} (y y' : outType (B ⊗ᵀ C))
           → Rₒ {A} {B} {C} y ≡ Rₒ {A} {B} {C} y' → y ≡ y'
    Rₒ-inj {A} {B} {C} y y' e =
      inj₂-inj (trans (sym (∘κₒ-R {A} {B} {C} y))
                      (trans (cong (∘κₒ {A} {B} {C}) e) (∘κₒ-R {A} {B} {C} y')))

    Lₒ≢Rₒ : ∀ {A B C} (y : outType (A ⊗ᵀ B)) (y' : outType (B ⊗ᵀ C))
            {ℓ} {W : Type ℓ}
          → Lₒ {A} {B} {C} y ≡ Rₒ {A} {B} {C} y' → W
    Lₒ≢Rₒ {A} {B} {C} y y' e =
      inj₁≢inj₂ (trans (sym (∘κₒ-L {A} {B} {C} y))
                       (trans (cong (∘κₒ {A} {B} {C}) e) (∘κₒ-R {A} {B} {C} y')))

    -- Where the external output map lands: on `M`'s domain port or on `N`'s
    -- codomain port, never on a traced port, and relabelling the other end of
    -- the composite does not touch it.
    tιₒ-inj : ∀ {A B C} (o o' : outType (A ⊗ᵀ C))
            → tιₒ {A} {C} {B} o ≡ tιₒ {A} {C} {B} o' → o ≡ o'
    tιₒ-inj (inj₁ _) (inj₁ _) e = cong inj₁ (inj₁-inj (inj₁-inj e))
    tιₒ-inj (inj₁ _) (inj₂ _) e = inj₁≢inj₂ e
    tιₒ-inj (inj₂ _) (inj₁ _) e = inj₁≢inj₂ (sym e)
    tιₒ-inj (inj₂ _) (inj₂ _) e = cong inj₂ (inj₁-inj (inj₂-inj e))

    tιₒ≢dZₒ : ∀ {A B C} (o : outType (A ⊗ᵀ C)) (bo : outType B) {ℓ} {W : Type ℓ}
            → tιₒ {A} {C} {B} o ≡ dZₒ {A} {C} {B} bo → W
    tιₒ≢dZₒ (inj₁ _) bo e = inj₁≢inj₂ (inj₁-inj e)
    tιₒ≢dZₒ (inj₂ _) bo e = inj₁≢inj₂ (sym e)

    tιₒ≢cZᵢ : ∀ {A B C} (o : outType (A ⊗ᵀ C)) (b : inType B) {ℓ} {W : Type ℓ}
            → tιₒ {A} {C} {B} o ≡ cZᵢ {A} {C} {B} b → W
    tιₒ≢cZᵢ (inj₁ _) b e = inj₁≢inj₂ e
    tιₒ≢cZᵢ (inj₂ _) b e = inj₁≢inj₂ (inj₂-inj e)

    tιₒ-L : ∀ {A B C} (h : inType B → inType C)
            (o : outType (A ⊗ᵀ C)) (y : outType (A ⊗ᵀ B))
          → tιₒ {A} {C} {B} o ≡ Lₒ {A} {B} {C} y → o ≡ cdₒ⁺ {A} {B} {C} h y
    tιₒ-L h (inj₁ _) (inj₁ _) e = cong inj₁ (inj₁-inj (inj₁-inj e))
    tιₒ-L h (inj₁ _) (inj₂ _) e = inj₁≢inj₂ e
    tιₒ-L h (inj₂ _) (inj₁ _) e = inj₁≢inj₂ (sym e)
    tιₒ-L h (inj₂ _) (inj₂ _) e = inj₁≢inj₂ (inj₂-inj e)

    tιₒ-R : ∀ {A B C} (h : outType B → outType A)
            (o : outType (A ⊗ᵀ C)) (y : outType (B ⊗ᵀ C))
          → tιₒ {A} {C} {B} o ≡ Rₒ {A} {B} {C} y → o ≡ dmₒ⁺ {B} {A} {C} h y
    tιₒ-R h (inj₁ _) (inj₁ _) e = inj₁≢inj₂ (inj₁-inj e)
    tιₒ-R h (inj₁ _) (inj₂ _) e = inj₁≢inj₂ e
    tιₒ-R h (inj₂ _) (inj₁ _) e = inj₁≢inj₂ (sym e)
    tιₒ-R h (inj₂ _) (inj₂ _) e = cong inj₂ (inj₁-inj (inj₂-inj e))

  -- ------------------------------------------------------------------------
  -- The routing squares.  Inside the `Pair`, relabelling `N`'s codomain is a
  -- sum map; at the traced machine's channel it is `wcₒ⁺`; past the trace it
  -- is `cdₒ⁺`.  The input side is `cod-routeᵢ`/`cod-outᵢ` from `Collapse`.
  -- ------------------------------------------------------------------------

  cod-route⁺ₒ : ∀ {A B C C'} (vC : inType C → inType C')
                (o : outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
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
    cod-route⁺ₒ' : ∀ {A B C C'} (vC : inType C → inType C')
                   (o₀ : outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ)))
                 → wcₒ⁺ {A} {B} {C} {C'} vC (∘κₒ⁻ {A} {B} {C} o₀)
                   ≡ ∘κₒ⁻ {A} {B} {C'}
                       (⊎ₒ {A} {B} {B} {C'} {A} {B} {B} {C} (λ x → x) (cdₒ⁺ {B} {C} {C'} vC) o₀)
    cod-route⁺ₒ' vC (inj₁ (inj₁ _)) = refl
    cod-route⁺ₒ' vC (inj₁ (inj₂ _)) = refl
    cod-route⁺ₒ' vC (inj₂ (inj₁ _)) = refl
    cod-route⁺ₒ' vC (inj₂ (inj₂ _)) = refl

    cod-pre : ∀ {A B C C'} (vC : inType C → inType C')
              (o₀ : outType ((A ⊗₀ B ᵀ) ⊗ᵀ ((B ⊗₀ C ᵀ) ᵀ)))
              (o : outType ((A ⊗₀ B) ⊗ᵀ (C' ⊗₀ B)))
            → ⊎ₒ {A} {B} {B} {C'} {A} {B} {B} {C} (λ x → x) (cdₒ⁺ {B} {C} {C'} vC) o₀
              ≡ ∘κₒ {A} {B} {C'} o
            → ∃ λ o₁ → (o₀ ≡ ∘κₒ {A} {B} {C} o₁) × (wcₒ⁺ {A} {B} {C} {C'} vC o₁ ≡ o)
    cod-pre {A} {B} {C} {C'} vC o₀ o e =
      ∘κₒ⁻ {A} {B} {C} o₀
      , sym (∘κₒ-rt o₀)
      , trans (cod-route⁺ₒ' vC o₀) (trans (cong (∘κₒ⁻ {A} {B} {C'}) e) (∘κₒ-tr o))

  cod-out⁺ₒ : ∀ {A B C C'} (vC : inType C → inType C')
              (o : outType (A ⊗ᵀ C))
            → wcₒ⁺ {A} {B} {C} {C'} vC (tιₒ {A} {C} {B} o)
              ≡ tιₒ {A} {C'} {B} (cdₒ⁺ {A} {C} {C'} vC o)
  cod-out⁺ₒ vC (inj₁ _) = refl
  cod-out⁺ₒ vC (inj₂ _) = refl

  private
    -- Only external ports map to external ports under `wcₒ⁺`.
    cod-out-pre : ∀ {A B C C'} (vC : inType C → inType C')
                  (o₀ : outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B)))
                  (o : outType (A ⊗ᵀ C'))
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
    wc-dZₒ : ∀ {A B C C'} (vC : inType C → inType C')
             (o : outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) z
           → wcₒ⁺ {A} {B} {C} {C'} vC o ≡ dZₒ {A} {C'} {B} z → o ≡ dZₒ {A} {C} {B} z
    wc-dZₒ vC (inj₁ (inj₁ _)) z e = inj₁≢inj₂ (inj₁-inj e)
    wc-dZₒ vC (inj₁ (inj₂ _)) z e = cong (λ x → inj₁ (inj₂ x)) (inj₂-inj (inj₁-inj e))
    wc-dZₒ vC (inj₂ (inj₁ _)) z e = inj₁≢inj₂ (sym e)
    wc-dZₒ vC (inj₂ (inj₂ _)) z e = inj₁≢inj₂ (sym e)

    wc-cZᵢ : ∀ {A B C C'} (vC : inType C → inType C')
             (o : outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))) z
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
              (uC : outType C' → outType C)
              (vC : inType C → inType C')
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
               (uC : outType C' → outType C)
               (vC : inType C → inType C')
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
             (uC : outType C' → outType C)
             (vC : inType C → inType C')
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
               (uC : outType C' → outType C)
               (vC : inType C → inType C')
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
                        (uC : outType C' → outType C)
                        (vC : inType C → inType C')
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
    relay : ∀ {X} → inType (X ⊗ᵀ X) → outType (X ⊗ᵀ X)
    relay {X} = Xφ (λ (x : inType X) → x) (λ (x : outType X) → x)

  Xfwd-Post : ∀ {A B} (f : inType A → inType B)
                      (g : outType B → outType A)
            → Xfwd f g ≅ᴹ Post (CC.id {A}) (cdᵢ {A} {A} {B} g) (cdₒ⁺ {A} {A} {B} f)
  Xfwd-Post {A} {B} f g =
    ≅ᴹ-trans (≅ᴹ-sym (Post-Fwd (relay {A}) (Xφ f g)
                               (cdᵢ {A} {A} {B} g) (cdₒ⁺ {A} {A} {B} f) sq))
             (Post-resp-≅ᴹ (cdᵢ {A} {A} {B} g) (cdₒ⁺ {A} {A} {B} f) (≅ᴹ-sym id-is-Xfwd))
    where
    sq : ∀ i → cdₒ⁺ {A} {A} {B} f (relay {A} (cdᵢ {A} {A} {B} g i)) ≡ Xφ f g i
    sq (inj₁ _) = refl
    sq (inj₂ _) = refl

  -- The mirror image: the domain of `CC.id {B}` is relabelled instead, so `g`
  -- is the covariant map on the output side and `f` the contravariant one on
  -- the input side.
  Xfwd-Post-dom : ∀ {A B} (f : inType A → inType B)
                          (g : outType B → outType A)
                → Xfwd f g ≅ᴹ Post (CC.id {B}) (dmᵢ {B} {A} {B} f) (dmₒ⁺ {B} {A} {B} g)
  Xfwd-Post-dom {A} {B} f g =
    ≅ᴹ-trans (≅ᴹ-sym (Post-Fwd (relay {B}) (Xφ f g)
                               (dmᵢ {B} {A} {B} f) (dmₒ⁺ {B} {A} {B} g) sq))
             (Post-resp-≅ᴹ (dmᵢ {B} {A} {B} f) (dmₒ⁺ {B} {A} {B} g) (≅ᴹ-sym id-is-Xfwd))
    where
    sq : ∀ i → dmₒ⁺ {B} {A} {B} g (relay {B} (dmᵢ {B} {A} {B} f i)) ≡ Xφ f g i
    sq (inj₁ _) = refl
    sq (inj₂ _) = refl

  -- ------------------------------------------------------------------------
  -- A forwarder is a relabelled identity.
  --
  -- `Post` and `Reindex` differ only in the direction of the output map, so a
  -- `Post` whose covariant map has a two-sided inverse is the `Reindex` along
  -- that inverse.  Feeding the two readings of a crossing forwarder as a
  -- `Post` of `CC.id` through this bridge gives the two ways to read it as a
  -- reindexed identity: either fix the codomain and relabel the domain, or fix
  -- the domain and relabel the codomain.  Each orientation keeps one of `f`,
  -- `g` verbatim, and so needs the other to be invertible — a crossing
  -- forwarder with a non-invertible backward map is genuinely not `CC.id` in
  -- disguise.
  -- ------------------------------------------------------------------------

  Post-is-Reindex : ∀ {A B C D} (M : Machine A B)
                    (u : inType (C ⊗ᵀ D) → inType (A ⊗ᵀ B))
                    (w : outType (A ⊗ᵀ B) → outType (C ⊗ᵀ D))
                    (v : outType (C ⊗ᵀ D) → outType (A ⊗ᵀ B))
                  → (∀ o → v (w o) ≡ o) → (∀ o → w (v o) ≡ o)
                  → Post M u w ≅ᴹ Reindex M u v
  Post-is-Reindex M u w v vw wv = MkIso _ _ (λ _ → refl) (λ _ → refl)
    (λ {s} {i} {o} (o₀ , x , e) →
       subst (λ y → Machine.stepRel M s (u i) y _) (sym (pull o o₀ e)) x)
    (λ {s} {i} {o} x → mapᴹ v o , x , push o)
    where
    pull : ∀ o o₀ → mapᴹ w o₀ ≡ o → mapᴹ v o ≡ o₀
    pull o o₀ e = trans (cong (mapᴹ v) (sym e))
                        (trans (mapᴹ-∘ v w o₀)
                               (trans (mapᴹ-cong vw o₀) (mapᴹ-id o₀)))
    push : ∀ o → mapᴹ w (mapᴹ v o) ≡ o
    push o = trans (mapᴹ-∘ w v o) (trans (mapᴹ-cong wv o) (mapᴹ-id o))

  -- Fixing the codomain `B` and relabelling the domain `A` keeps `f` verbatim,
  -- so it is `g` that must be invertible.
  Xfwd-dom : ∀ {A B} (f : inType A → inType B)
                     (g : outType B → outType A)
                     (g⁻ : outType A → outType B)
           → (∀ β → g⁻ (g β) ≡ β) → (∀ α → g (g⁻ α) ≡ α)
           → Xfwd f g ≅ᴹ Reindex (CC.id {B}) (dmᵢ f) (dmₒ g⁻)
  Xfwd-dom {A} {B} f g g⁻ gl gr =
    ≅ᴹ-trans (Xfwd-Post-dom f g)
             (Post-is-Reindex (CC.id {B}) (dmᵢ {B} {A} {B} f)
                              (dmₒ⁺ {B} {A} {B} g) (dmₒ {B} {A} {B} g⁻) vw wv)
    where
    vw : ∀ o → dmₒ {B} {A} {B} g⁻ (dmₒ⁺ {B} {A} {B} g o) ≡ o
    vw (inj₁ β) = cong inj₁ (gl β)
    vw (inj₂ _) = refl
    wv : ∀ o → dmₒ⁺ {B} {A} {B} g (dmₒ {B} {A} {B} g⁻ o) ≡ o
    wv (inj₁ α) = cong inj₁ (gr α)
    wv (inj₂ _) = refl

  -- The mirror image: fixing the domain `A` keeps `g` verbatim and asks `f` to
  -- be invertible instead.
  Xfwd-cod : ∀ {A B} (f : inType A → inType B)
                     (g : outType B → outType A)
                     (f⁻ : inType B → inType A)
           → (∀ a → f⁻ (f a) ≡ a) → (∀ b → f (f⁻ b) ≡ b)
           → Xfwd f g ≅ᴹ Reindex (CC.id {A}) (cdᵢ g) (cdₒ f⁻)
  Xfwd-cod {A} {B} f g f⁻ fl fr =
    ≅ᴹ-trans (Xfwd-Post f g)
             (Post-is-Reindex (CC.id {A}) (cdᵢ {A} {A} {B} g)
                              (cdₒ⁺ {A} {A} {B} f) (cdₒ {A} {A} {B} f⁻) vw wv)
    where
    vw : ∀ o → cdₒ {A} {A} {B} f⁻ (cdₒ⁺ {A} {A} {B} f o) ≡ o
    vw (inj₁ _) = refl
    vw (inj₂ a) = cong inj₂ (fl a)
    wv : ∀ o → cdₒ⁺ {A} {A} {B} f (cdₒ {A} {A} {B} f⁻ o) ≡ o
    wv (inj₁ _) = refl
    wv (inj₂ b) = cong inj₂ (fr b)


  -- ------------------------------------------------------------------------
  -- The relay lemmas, in the trace normal form of `Reindex`.  A step of
  -- `Core M N` is a step of one component, read off with `comp-view` and
  -- routed with the table above; when that component is a forwarder `Fwd φ`
  -- the step is a relay hop, stateless and deterministic.  These views and
  -- their converses, the step builders, are what both relay proofs are made
  -- of; each proof adds the chain analysis for its side.
  -- ------------------------------------------------------------------------

  private
    -- Step views: a step on a first-component port is a step of `M` with
    -- `N`'s state untouched, and symmetrically.
    step-L : ∀ {A B C} (M : Machine A B) (N : Machine B C) {S S' : Machine.State (Core M N)}
             (x : inType (A ⊗ᵀ B)) (O : Maybe (outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))))
           → Machine.stepRel (Core M N) S (Lᵢ {A} {B} {C} x) O S'
           → ∃ λ mo → Machine.stepRel M (proj₁ S) x mo (proj₁ S')
                    × (O ≡ mapᴹ (Lₒ {A} {B} {C}) mo) × (proj₂ S' ≡ proj₂ S)
    step-L {A} {B} {C} M N {S} {S'} x O p = go (comp-view p)
      where
      go : CompView M N S (∘κᵢ {A} {B} {C} (Lᵢ {A} {B} {C} x)) (mapᴹ (∘κₒ {A} {B} {C}) O) S'
         → ∃ λ mo → Machine.stepRel M (proj₁ S) x mo (proj₁ S')
                  × (O ≡ mapᴹ (Lₒ {A} {B} {C}) mo) × (proj₂ S' ≡ proj₂ S)
      go (inj₂ (_ , _ , xeq , _)) = inj₁≢inj₂ (trans (sym (∘κᵢ-L {A} {B} {C} x)) xeq)
      go (inj₁ (mᵢ , mo , xeq , yeq , steq , q)) =
        mo
        , subst (λ z → Machine.stepRel M (proj₁ S) z mo (proj₁ S'))
                (sym (inj₁-inj (trans (sym (∘κᵢ-L {A} {B} {C} x)) xeq))) q
        , mapᴹ-pull (∘κₒ {A} {B} {C}) (κLₒ {A} {B} {C}) (Lₒ {A} {B} {C})
                    (∘κₒ-L⁻ {A} {B} {C}) O mo yeq
        , steq

    step-R : ∀ {A B C} (M : Machine A B) (N : Machine B C) {S S' : Machine.State (Core M N)}
             (j : inType (B ⊗ᵀ C)) (O : Maybe (outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))))
           → Machine.stepRel (Core M N) S (Rᵢ {A} {B} {C} j) O S'
           → ∃ λ mo → Machine.stepRel N (proj₂ S) j mo (proj₂ S')
                    × (O ≡ mapᴹ (Rₒ {A} {B} {C}) mo) × (proj₁ S' ≡ proj₁ S)
    step-R {A} {B} {C} M N {S} {S'} j O p = go (comp-view p)
      where
      go : CompView M N S (∘κᵢ {A} {B} {C} (Rᵢ {A} {B} {C} j)) (mapᴹ (∘κₒ {A} {B} {C}) O) S'
         → ∃ λ mo → Machine.stepRel N (proj₂ S) j mo (proj₂ S')
                  × (O ≡ mapᴹ (Rₒ {A} {B} {C}) mo) × (proj₁ S' ≡ proj₁ S)
      go (inj₁ (_ , _ , xeq , _)) = inj₁≢inj₂ (sym (trans (sym (∘κᵢ-R {A} {B} {C} j)) xeq))
      go (inj₂ (mᵢ , mo , xeq , yeq , steq , q)) =
        mo
        , subst (λ z → Machine.stepRel N (proj₂ S) z mo (proj₂ S'))
                (sym (inj₂-inj (trans (sym (∘κᵢ-R {A} {B} {C} j)) xeq))) q
        , mapᴹ-pull (∘κₒ {A} {B} {C}) (κRₒ {A} {B} {C}) (Rₒ {A} {B} {C})
                    (∘κₒ-R⁻ {A} {B} {C}) O mo yeq
        , steq

    -- Relay-hop views: a forwarder component moves no state and emits `φ`
    -- of its input, on its own ports.
    hop-L : ∀ {A B C} (φ : inType (A ⊗ᵀ B) → outType (A ⊗ᵀ B)) (N : Machine B C)
            {S S' : Machine.State (Core (Fwd φ) N)}
            (x : inType (A ⊗ᵀ B)) (O : Maybe (outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))))
          → Machine.stepRel (Core (Fwd φ) N) S (Lᵢ {A} {B} {C} x) O S'
          → (proj₂ S' ≡ proj₂ S) × (O ≡ just (Lₒ {A} {B} {C} (φ x)))
    hop-L {A} {B} {C} φ N x O p =
      let (mo , q , Oeq , st) = step-L (Fwd φ) N x O p
      in st , trans Oeq (cong (mapᴹ (Lₒ {A} {B} {C})) (sym q))

    hop-R : ∀ {A B C} (M : Machine A B) (φ : inType (B ⊗ᵀ C) → outType (B ⊗ᵀ C))
            {S S' : Machine.State (Core M (Fwd φ))}
            (j : inType (B ⊗ᵀ C)) (O : Maybe (outType ((A ⊗₀ B) ⊗ᵀ (C ⊗₀ B))))
          → Machine.stepRel (Core M (Fwd φ)) S (Rᵢ {A} {B} {C} j) O S'
          → (proj₁ S' ≡ proj₁ S) × (O ≡ just (Rₒ {A} {B} {C} (φ j)))
    hop-R {A} {B} {C} M φ j O p =
      let (mo , q , Oeq , st) = step-R M (Fwd φ) j O p
      in st , trans Oeq (cong (mapᴹ (Rₒ {A} {B} {C})) (sym q))

    -- Step builders, the converses.
    mk-L : ∀ {A B C} (M : Machine A B) (N : Machine B C)
           {s s' : Machine.State M} (u : Machine.State N)
           (x : inType (A ⊗ᵀ B)) (mo : Maybe (outType (A ⊗ᵀ B)))
         → Machine.stepRel M s x mo s'
         → Machine.stepRel (Core M N) (s , u) (Lᵢ {A} {B} {C} x) (mapᴹ (Lₒ {A} {B} {C}) mo) (s' , u)
    mk-L {A} {B} {C} M N {s} {s'} u x mo q =
      subst₂ (λ I O → Tensor.CompRel M N (s , u) I O (s' , u))
             (sym (∘κᵢ-L {A} {B} {C} x))
             (sym (trans (mapᴹ-∘ (∘κₒ {A} {B} {C}) (Lₒ {A} {B} {C}) mo)
                         (mapᴹ-cong (∘κₒ-L {A} {B} {C}) mo)))
             (Tensor.Step₁ {m = x} {m' = mo} q)

    mk-R : ∀ {A B C} (M : Machine A B) (N : Machine B C)
           (u : Machine.State M) {s s' : Machine.State N}
           (j : inType (B ⊗ᵀ C)) (mo : Maybe (outType (B ⊗ᵀ C)))
         → Machine.stepRel N s j mo s'
         → Machine.stepRel (Core M N) (u , s) (Rᵢ {A} {B} {C} j) (mapᴹ (Rₒ {A} {B} {C}) mo) (u , s')
    mk-R {A} {B} {C} M N u {s} {s'} j mo q =
      subst₂ (λ I O → Tensor.CompRel M N (u , s) I O (u , s'))
             (sym (∘κᵢ-R {A} {B} {C} j))
             (sym (trans (mapᴹ-∘ (∘κₒ {A} {B} {C}) (Rₒ {A} {B} {C}) mo)
                         (mapᴹ-cong (∘κₒ-R {A} {B} {C}) mo)))
             (Tensor.Step₂ {m = j} {m' = mo} q)

    mk-hop-L : ∀ {A B C} (φ : inType (A ⊗ᵀ B) → outType (A ⊗ᵀ B)) (N : Machine B C)
               {u : Machine.State (Fwd φ)} (s : Machine.State N) (x : inType (A ⊗ᵀ B))
             → Machine.stepRel (Core (Fwd φ) N) (u , s) (Lᵢ {A} {B} {C} x)
                               (just (Lₒ {A} {B} {C} (φ x))) (u , s)
    mk-hop-L φ N s x = mk-L (Fwd φ) N s x (just (φ x)) refl

    mk-hop-R : ∀ {A B C} (M : Machine A B) (φ : inType (B ⊗ᵀ C) → outType (B ⊗ᵀ C))
               (s : Machine.State M) {u : Machine.State (Fwd φ)} (j : inType (B ⊗ᵀ C))
             → Machine.stepRel (Core M (Fwd φ)) (s , u) (Rᵢ {A} {B} {C} j)
                               (just (Rₒ {A} {B} {C} (φ j))) (s , u)
    mk-hop-R M φ s j = mk-R M (Fwd φ) s j (just (φ j)) refl

  -- ------------------------------------------------------------------------
  -- Forwarder in the second component: the traced normal form of
  -- `Xfwd f g CC.∘ M` is `M` with its codomain relabelled, contravariantly
  -- by `g` on inputs and covariantly by `f` on outputs.  Every chain is one
  -- `M`-step, preceded by a relay hop iff the input arrived on `C` (it
  -- reaches `M` as `g co`) and followed by one iff `M` emitted on `B` (it
  -- leaves as `f b`).  States are `State M × ⊤` against `State M`.
  -- ------------------------------------------------------------------------

  Trc-relay-cod : ∀ {A B C} (M : Machine A B)
                  (f : inType B → inType C)
                  (g : outType C → outType B)
                → Reindex (Trc (Reindex (Pair M (Xfwd f g)) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                          (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
                  ≅ᴹ Post M (cdᵢ {A} {B} {C} g) (cdₒ⁺ {A} {B} {C} f)
  Trc-relay-cod {A} {B} {C} M f g =
    MkIso proj₁ (λ s → s , tt) (λ _ → refl) (λ _ → refl)
          (λ {_} {i} {o} tr → chain i o tr)
          (λ {s} {i} {o} {s'} (o₀ , x , e) →
             subst (λ z → TraceRel W (s , tt) (tιᵢ {A} {C} {B} i)
                                    (mapᴹ (tιₒ {A} {C} {B}) z) (s' , tt))
                   e (build i o₀ x))
    where
    N : Machine B C
    N = Xfwd f g
    W : Machine (A ⊗₀ B) (C ⊗₀ B)
    W = Core M N
    S Iᵗ Oᵗ Iᴹ Oᴹ : Type
    S  = Machine.State M × ⊤
    Iᵗ = inType (A ⊗ᵀ C)
    Oᵗ = Maybe (outType (A ⊗ᵀ C))
    Iᴹ = inType (A ⊗ᵀ B)
    Oᴹ = Maybe (outType (A ⊗ᵀ B))

    -- What a step of `Post M (cdᵢ g) (cdₒ⁺ f)` is, with `M`'s input spelled out.
    PostStep : Machine.State M → Iᴹ → Oᵗ → Machine.State M → Type
    PostStep s mᵢ o s' = ∃ λ o₀ → Machine.stepRel M s mᵢ o₀ s' × mapᴹ (cdₒ⁺ {A} {B} {C} f) o₀ ≡ o

    -- ---- Relay hop out.  Once `M`'s output has reached the forwarder on
    -- `B`, the chain ends with the hop that leaves on `C` as `f b`.
    hop-out : ∀ {sp sp' : S} (b : inType B) (o : Oᵗ)
            → TraceRel W sp (dZᵢ {A} {C} {B} b) (mapᴹ (tιₒ {A} {C} {B}) o) sp'
            → (proj₁ sp' ≡ proj₁ sp) × (o ≡ just (inj₂ (f b)))
    hop-out b o Trace[ x ] =
      let (st , Oeq)       = hop-R M (Xφ f g) (inj₁ b) _ x
          (o' , oeq , teq) = mapᴹ-just (tιₒ {A} {C} {B}) o _ Oeq
      in st , trans oeq (cong just (tιₒ-inj {A} {B} {C} o' (inj₂ (f b)) teq))
    hop-out b o (_Trace∷ₒ_ {outC = zc} x rest) =
      let (_ , Oeq) = hop-R M (Xφ f g) (inj₁ b) _ x
      in inj₁≢inj₂ (Rₒ-inj {A} {B} {C} (inj₁ zc) (inj₂ (f b)) (just-inj Oeq))
    hop-out b o (_Trace∷ᵢ_ {inC = zc} x rest) =
      let (_ , Oeq) = hop-R M (Xφ f g) (inj₁ b) _ x
      in Lₒ≢Rₒ {A} {B} {C} (inj₂ zc) (inj₂ (f b)) (just-inj Oeq)

    -- ---- Chain inversion, from the step at which `M` reads its input: `M`
    -- ends the chain unless it emits on `B`, and then the relay hop does.
    M-first : ∀ {sp sp' : S} (mᵢ : Iᴹ) (o : Oᵗ)
            → TraceRel W sp (Lᵢ {A} {B} {C} mᵢ) (mapᴹ (tιₒ {A} {C} {B}) o) sp'
            → PostStep (proj₁ sp) mᵢ o (proj₁ sp')
    M-first mᵢ o Trace[ x ] =
      let (mo , q , Oeq , _) = step-L M N mᵢ _ x
      in mo , q , sym (mapᴹ-pull (tιₒ {A} {C} {B}) (Lₒ {A} {B} {C}) (cdₒ⁺ {A} {B} {C} f)
                                 (tιₒ-L {A} {B} {C} f) o mo Oeq)
    M-first mᵢ o (_Trace∷ₒ_ {outC = zc} x rest) =
      let (mo , _ , Oeq , _) = step-L M N mᵢ _ x
          (y , _ , Ly)       = mapᴹ-just (Lₒ {A} {B} {C}) mo _ (sym Oeq)
      in Lₒ≢Rₒ {A} {B} {C} y (inj₁ zc) Ly
    M-first {sp} {sp'} mᵢ o (_Trace∷ᵢ_ {inC = zc} x rest) =
      let (mo , q , Oeq , _) = step-L M N mᵢ _ x
          (y , moeq , Ly)    = mapᴹ-just (Lₒ {A} {B} {C}) mo _ (sym Oeq)
          (st , oeq)         = hop-out zc o rest
      in just (inj₂ zc)
       , subst₂ (λ z s → Machine.stepRel M (proj₁ sp) mᵢ z s)
                (trans moeq (cong just (Lₒ-inj {A} {B} {C} y (inj₂ zc) Ly))) (sym st) q
       , sym oeq

    -- ---- Chain inversion, from the external input: on `A` it is `M`'s at
    -- once; on `C` it is relayed onto the trace as `g co` first.
    chain : ∀ {sp sp' : S} (i : Iᵗ) (o : Oᵗ)
          → TraceRel W sp (tιᵢ {A} {C} {B} i) (mapᴹ (tιₒ {A} {C} {B}) o) sp'
          → PostStep (proj₁ sp) (cdᵢ {A} {B} {C} g i) o (proj₁ sp')
    chain (inj₁ a)  o tr = M-first (inj₁ a) o tr
    chain (inj₂ co) o Trace[ x ] =
      let (_ , Oeq)      = hop-R M (Xφ f g) (inj₂ co) _ x
          (o' , _ , teq) = mapᴹ-just (tιₒ {A} {C} {B}) o _ Oeq
      in tιₒ≢dZₒ {A} {B} {C} o' (g co) teq
    chain (inj₂ co) o (_Trace∷ₒ_ {outC = zc} x rest) =
      let (st , Oeq)   = hop-R M (Xφ f g) (inj₂ co) _ x
          (o₀ , q , e) = M-first (inj₂ zc) o rest
      in o₀
       , subst₂ (λ s z → Machine.stepRel M s (inj₂ z) o₀ _) st
                (inj₁-inj (Rₒ-inj {A} {B} {C} (inj₁ zc) (inj₁ (g co)) (just-inj Oeq))) q
       , e
    chain (inj₂ co) o (_Trace∷ᵢ_ {inC = zc} x rest) =
      let (_ , Oeq) = hop-R M (Xφ f g) (inj₂ co) _ x
      in Lₒ≢Rₒ {A} {B} {C} (inj₂ zc) (inj₁ (g co)) (just-inj Oeq)

    -- ---- Chain builder, from `M`'s step: nothing more unless `M` emitted on
    -- `B`, and then the relay hop out on `C`.
    M-chain : ∀ {s s' : Machine.State M} (mᵢ : Iᴹ) (o₀ : Oᴹ) → Machine.stepRel M s mᵢ o₀ s'
            → TraceRel W (s , tt) (Lᵢ {A} {B} {C} mᵢ)
                       (mapᴹ (tιₒ {A} {C} {B}) (mapᴹ (cdₒ⁺ {A} {B} {C} f) o₀)) (s' , tt)
    M-chain mᵢ nothing          x = Trace[ mk-L M N tt mᵢ nothing x ]
    M-chain mᵢ (just (inj₁ ao)) x = Trace[ mk-L M N tt mᵢ (just (inj₁ ao)) x ]
    M-chain {s' = s'} mᵢ (just (inj₂ b)) x =
      _Trace∷ᵢ_ {inC = b} (mk-L M N tt mᵢ (just (inj₂ b)) x)
                          Trace[ mk-hop-R M (Xφ f g) s' (inj₁ b) ]

    -- ---- Chain builder, from the external input: on `C`, the relay hop onto
    -- the trace comes first.
    build : ∀ {s s' : Machine.State M} (i : Iᵗ) (o₀ : Oᴹ)
          → Machine.stepRel M s (cdᵢ {A} {B} {C} g i) o₀ s'
          → TraceRel W (s , tt) (tιᵢ {A} {C} {B} i)
                     (mapᴹ (tιₒ {A} {C} {B}) (mapᴹ (cdₒ⁺ {A} {B} {C} f) o₀)) (s' , tt)
    build (inj₁ a) o₀ x = M-chain (inj₁ a) o₀ x
    build {s} (inj₂ co) o₀ x =
      _Trace∷ₒ_ {outC = g co} (mk-hop-R M (Xφ f g) s (inj₂ co)) (M-chain (inj₂ (g co)) o₀ x)

  -- ------------------------------------------------------------------------
  -- Forwarder in the first component: the traced normal form of
  -- `N CC.∘ Xfwd f g` is `N` with its domain relabelled, contravariantly by
  -- `f` on inputs and covariantly by `g` on outputs.  Every chain is one
  -- `N`-step, preceded by a relay hop iff the input arrived on `A` (it
  -- reaches `N` as `f a`) and followed by one iff `N` emitted on `B` (it
  -- leaves as `g bo`).  States are `⊤ × State N` against `State N`.
  -- ------------------------------------------------------------------------

  Trc-relay-dom : ∀ {A B C} (f : inType A → inType B)
                            (g : outType B → outType A) (N : Machine B C)
                → Reindex (Trc (Reindex (Pair (Xfwd f g) N) (∘κᵢ {A} {B} {C}) (∘κₒ {A} {B} {C})))
                          (tιᵢ {A} {C} {B}) (tιₒ {A} {C} {B})
                  ≅ᴹ Post N (dmᵢ {B} {A} {C} f) (dmₒ⁺ {B} {A} {C} g)
  Trc-relay-dom {A} {B} {C} f g N =
    MkIso proj₂ (λ s → tt , s) (λ _ → refl) (λ _ → refl)
          (λ {_} {i} {o} tr → chain i o tr)
          (λ {s} {i} {o} {s'} (o₀ , x , e) →
             subst (λ z → TraceRel W (tt , s) (tιᵢ {A} {C} {B} i)
                                    (mapᴹ (tιₒ {A} {C} {B}) z) (tt , s'))
                   e (build i o₀ x))
    where
    M : Machine A B
    M = Xfwd f g
    W : Machine (A ⊗₀ B) (C ⊗₀ B)
    W = Core M N
    S Iᵗ Oᵗ Iᴺ Oᴺ : Type
    S  = ⊤ × Machine.State N
    Iᵗ = inType (A ⊗ᵀ C)
    Oᵗ = Maybe (outType (A ⊗ᵀ C))
    Iᴺ = inType (B ⊗ᵀ C)
    Oᴺ = Maybe (outType (B ⊗ᵀ C))

    -- What a step of `Post N (dmᵢ f) (dmₒ⁺ g)` is, with `N`'s input spelled out.
    PostStep : Machine.State N → Iᴺ → Oᵗ → Machine.State N → Type
    PostStep s j o s' = ∃ λ o₀ → Machine.stepRel N s j o₀ s' × mapᴹ (dmₒ⁺ {B} {A} {C} g) o₀ ≡ o

    -- ---- Relay hop out.  Once `N`'s output has reached the forwarder on
    -- `B`, the chain ends with the hop that leaves on `A` as `g bo`.
    hop-out : ∀ {sp sp' : S} (bo : outType B) (o : Oᵗ)
            → TraceRel W sp (cZₒ {A} {C} {B} bo) (mapᴹ (tιₒ {A} {C} {B}) o) sp'
            → (proj₂ sp' ≡ proj₂ sp) × (o ≡ just (inj₁ (g bo)))
    hop-out bo o Trace[ x ] =
      let (st , Oeq)       = hop-L (Xφ f g) N (inj₂ bo) _ x
          (o' , oeq , teq) = mapᴹ-just (tιₒ {A} {C} {B}) o _ Oeq
      in st , trans oeq (cong just (tιₒ-inj {A} {B} {C} o' (inj₁ (g bo)) teq))
    hop-out bo o (_Trace∷ₒ_ {outC = zc} x rest) =
      let (_ , Oeq) = hop-L (Xφ f g) N (inj₂ bo) _ x
      in Lₒ≢Rₒ {A} {B} {C} (inj₁ (g bo)) (inj₁ zc) (sym (just-inj Oeq))
    hop-out bo o (_Trace∷ᵢ_ {inC = zc} x rest) =
      let (_ , Oeq) = hop-L (Xφ f g) N (inj₂ bo) _ x
      in inj₁≢inj₂ (sym (Lₒ-inj {A} {B} {C} (inj₂ zc) (inj₁ (g bo)) (just-inj Oeq)))

    -- ---- Chain inversion, from the step at which `N` reads its input: `N`
    -- ends the chain unless it emits on `B`, and then the relay hop does.
    N-first : ∀ {sp sp' : S} (j : Iᴺ) (o : Oᵗ)
            → TraceRel W sp (Rᵢ {A} {B} {C} j) (mapᴹ (tιₒ {A} {C} {B}) o) sp'
            → PostStep (proj₂ sp) j o (proj₂ sp')
    N-first j o Trace[ x ] =
      let (mo , q , Oeq , _) = step-R M N j _ x
      in mo , q , sym (mapᴹ-pull (tιₒ {A} {C} {B}) (Rₒ {A} {B} {C}) (dmₒ⁺ {B} {A} {C} g)
                                 (tιₒ-R {A} {B} {C} g) o mo Oeq)
    N-first {sp} {sp'} j o (_Trace∷ₒ_ {outC = zc} x rest) =
      let (mo , q , Oeq , _) = step-R M N j _ x
          (y , moeq , Ry)    = mapᴹ-just (Rₒ {A} {B} {C}) mo _ (sym Oeq)
          (st , oeq)         = hop-out zc o rest
      in just (inj₁ zc)
       , subst₂ (λ z s → Machine.stepRel N (proj₂ sp) j z s)
                (trans moeq (cong just (Rₒ-inj {A} {B} {C} y (inj₁ zc) Ry))) (sym st) q
       , sym oeq
    N-first j o (_Trace∷ᵢ_ {inC = zc} x rest) =
      let (mo , _ , Oeq , _) = step-R M N j _ x
          (y , _ , Ry)       = mapᴹ-just (Rₒ {A} {B} {C}) mo _ (sym Oeq)
      in Lₒ≢Rₒ {A} {B} {C} (inj₂ zc) y (sym Ry)

    -- ---- Chain inversion, from the external input: on `C` it is `N`'s at
    -- once; on `A` it is relayed onto the trace as `f a` first.
    chain : ∀ {sp sp' : S} (i : Iᵗ) (o : Oᵗ)
          → TraceRel W sp (tιᵢ {A} {C} {B} i) (mapᴹ (tιₒ {A} {C} {B}) o) sp'
          → PostStep (proj₂ sp) (dmᵢ {B} {A} {C} f i) o (proj₂ sp')
    chain (inj₂ co) o tr = N-first (inj₂ co) o tr
    chain (inj₁ a)  o Trace[ x ] =
      let (_ , Oeq)      = hop-L (Xφ f g) N (inj₁ a) _ x
          (o' , _ , teq) = mapᴹ-just (tιₒ {A} {C} {B}) o _ Oeq
      in tιₒ≢cZᵢ {A} {B} {C} o' (f a) teq
    chain (inj₁ a)  o (_Trace∷ₒ_ {outC = zc} x rest) =
      let (_ , Oeq) = hop-L (Xφ f g) N (inj₁ a) _ x
      in Lₒ≢Rₒ {A} {B} {C} (inj₂ (f a)) (inj₁ zc) (sym (just-inj Oeq))
    chain (inj₁ a)  o (_Trace∷ᵢ_ {inC = zc} x rest) =
      let (st , Oeq)   = hop-L (Xφ f g) N (inj₁ a) _ x
          (o₀ , q , e) = N-first (inj₁ zc) o rest
      in o₀
       , subst₂ (λ s z → Machine.stepRel N s (inj₁ z) o₀ _) st
                (inj₂-inj (Lₒ-inj {A} {B} {C} (inj₂ zc) (inj₂ (f a)) (just-inj Oeq))) q
       , e

    -- ---- Chain builder, from `N`'s step: nothing more unless `N` emitted on
    -- `B`, and then the relay hop out on `A`.
    N-chain : ∀ {s s' : Machine.State N} (j : Iᴺ) (o₀ : Oᴺ) → Machine.stepRel N s j o₀ s'
            → TraceRel W (tt , s) (Rᵢ {A} {B} {C} j)
                       (mapᴹ (tιₒ {A} {C} {B}) (mapᴹ (dmₒ⁺ {B} {A} {C} g) o₀)) (tt , s')
    N-chain j nothing          x = Trace[ mk-R M N tt j nothing x ]
    N-chain j (just (inj₂ ci)) x = Trace[ mk-R M N tt j (just (inj₂ ci)) x ]
    N-chain {s' = s'} j (just (inj₁ bo)) x =
      _Trace∷ₒ_ {outC = bo} (mk-R M N tt j (just (inj₁ bo)) x)
                            Trace[ mk-hop-L (Xφ f g) N s' (inj₂ bo) ]

    -- ---- Chain builder, from the external input: on `A`, the relay hop onto
    -- the trace comes first.
    build : ∀ {s s' : Machine.State N} (i : Iᵗ) (o₀ : Oᴺ)
          → Machine.stepRel N s (dmᵢ {B} {A} {C} f i) o₀ s'
          → TraceRel W (tt , s) (tιᵢ {A} {C} {B} i)
                     (mapᴹ (tιₒ {A} {C} {B}) (mapᴹ (dmₒ⁺ {B} {A} {C} g) o₀)) (tt , s')
    build (inj₂ co) o₀ x = N-chain (inj₂ co) o₀ x
    build {s} (inj₁ a) o₀ x =
      _Trace∷ᵢ_ {inC = f a} (mk-hop-L (Xφ f g) N s (inj₁ a)) (N-chain (inj₁ (f a)) o₀ x)

  -- ------------------------------------------------------------------------
  -- Composing with a crossing forwarder, on either side, is a `Post`.
  -- ------------------------------------------------------------------------

  Xfwd-∘-Post : ∀ {A B C} (M : Machine A B)
                (f : inType B → inType C)
                (g : outType C → outType B)
              → (Xfwd f g CC.∘ M) ≅ᴹ Post M (cdᵢ {A} {B} {C} g) (cdₒ⁺ {A} {B} {C} f)
  Xfwd-∘-Post {A} {B} {C} M f g = ≅ᴹ-trans (∘-Reindex M (Xfwd f g)) (Trc-relay-cod M f g)

  ∘-Xfwd-Post : ∀ {A B C} (N : Machine B C)
                (f : inType A → inType B)
                (g : outType B → outType A)
              → (N CC.∘ Xfwd f g) ≅ᴹ Post N (dmᵢ {B} {A} {C} f) (dmₒ⁺ {B} {A} {C} g)
  ∘-Xfwd-Post {A} {B} {C} N f g = ≅ᴹ-trans (∘-Reindex (Xfwd f g) N) (Trc-relay-dom f g N)

  -- ------------------------------------------------------------------------
  -- The identity laws are the relay lemmas at `f = g = id`, with the identity
  -- read as a crossing forwarder.
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

  ∘-identityʳ-Post : ∀ {A B} (N : Machine A B) → (N CC.∘ CC.id) ≅ᴹ N
  ∘-identityʳ-Post {A} {B} N =
    ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (id-is-Xfwd {A}))
    (≅ᴹ-trans (∘-Xfwd-Post N (λ a → a) (λ o → o))
    (≅ᴹ-trans (Post-cong N (dmᵢ {A} {A} {B} (λ a → a)) (λ i → i)
                           (dmₒ⁺ {A} {A} {B} (λ o → o)) (λ o → o) dmᵢ-id dmₒ⁺-id)
              (Post-id N)))
    where
    dmᵢ-id : ∀ i → dmᵢ {A} {A} {B} (λ a → a) i ≡ i
    dmᵢ-id (inj₁ _) = refl
    dmᵢ-id (inj₂ _) = refl
    dmₒ⁺-id : ∀ o → dmₒ⁺ {A} {A} {B} (λ o → o) o ≡ o
    dmₒ⁺-id (inj₁ _) = refl
    dmₒ⁺-id (inj₂ _) = refl
