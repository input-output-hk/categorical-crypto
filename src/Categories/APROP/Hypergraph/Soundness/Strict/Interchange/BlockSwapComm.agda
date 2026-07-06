{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict block-swap-commutation residual `bswap-σ` of
-- `Strict/DecodeSigma.agda` (the parameter `BSwapσ : Scr.BswapSig`).
--
--   block-swap-comm
--     : ∀ (L R : List V)
--     → permuteˢ (bswap L R)
--       ≈ˢ castˢ (sym (map-++ vlab L R)) (sym (map-++ vlab R L))
--           (σˢ (map vlab L) (map vlab R))
--
-- This is the strict, VERTEX-LEVEL twin of the non-strict keystone
-- `BNV.σ-block-comm` (`pvl (++-comm L R) ≈ σ-block`), proven entirely from the
-- `FreeStrictSMC.Build` axioms + the reusable `σ-hexˢʳ` (RIGHT-hexagon)
-- companion lemma and the `[]` base cases proven in `DecodeSigma`.
--
-- Proof structure (mirrors `BlockNFBraid.σ-block-comm` / `prep-step`):
--
--   * `shift-sym v R L` — the FULL `permuteˢ (↭-sym (shift v R L))` slide
--     (induction on `R`).  Its `[]` case is `Scr.permuteˢ-shift-sym-base`; the
--     `(x ∷ R)` step is a `σ-hexˢʳ` application at the SINGLETON frames
--     `a = [vlab v]`, `b = [vlab x]`, `c = map R` (all three associators
--     collapse to `coe refl`), reconciled with the `castˢ` map-distribution
--     bookkeeping.
--
--   * `block-swap-comm L R` — induction on `L`.  `[]` is `Scr.bswap-σ-base`;
--     the `(v ∷ L)` step composes `shift-sym v R L` with the framed IH, then
--     reconciles the two `castˢ` bracketings (via `shift-sym` directly — no
--     further hexagon).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Boundary sig _≟X_
  using (coe; coe-id≈)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_
  using (σ-hexˢʳ; module Scr)

open import Data.List using (List; []; _∷_; _++_; map; [_])
open import Data.List.Properties using (++-identityʳ; ++-assoc; map-++)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------

module _ (V : Set) (vlab : V → X) where

  open Scr V vlab
    using (bswap; mdom; mcod
          ; permuteˢ-shift-sym-base; bswap-σ-base; BswapSig)
  open Support V vlab using (permuteˢ)

  private
    m : List V → List X
    m = map vlab

  --------------------------------------------------------------------------
  -- (A)  The full shift-sym slide, by induction on R.
  --
  --   permuteˢ (↭-sym (shift v R L))
  --     ≈ˢ castˢ (mdom v R L) (mcod v R L)
  --         (σˢ [vlab v] (map R) ⊗ˢ idˢ {map L})

  shift-sym
    : (v : V) (R L : List V)
    → permuteˢ (Perm.↭-sym (PermProp.shift v R L))
      ≈ˢ castˢ (mdom v R L) (mcod v R L)
          (σˢ (vlab v ∷ []) (m R) ⊗ˢ idˢ {m L})
  shift-sym v []      L = permuteˢ-shift-sym-base v L
  shift-sym v (x ∷ R) L = goal
    where
      -- the hexagon at singleton frames a=[vlab v], b=[vlab x], c=map R
      a b c : List X
      a = vlab v ∷ []
      b = vlab x ∷ []
      c = m R

      -- σ-hexˢʳ a b c, with all three associators = refl (singleton b/a).
      hex : σˢ a (b ++ c)
            ≈ˢ coe (sym (++-assoc b c a))
                ∘ˢ (((idˢ {b} ⊗ˢ σˢ a c)
                      ∘ˢ coe (++-assoc b a c) ∘ˢ (σˢ a b ⊗ˢ idˢ {c}))
                    ∘ˢ coe (sym (++-assoc a b c)))
      hex = σ-hexˢʳ a b c

      -- all three associators are `++-assoc (singleton) _ _` ≡ refl, so the
      -- `coe`s collapse to `idˢ` and `hex` simplifies to a 2-block composite.
      hex' : σˢ a (vlab x ∷ m R) ≈ˢ (idˢ {b} ⊗ˢ σˢ a c) ∘ˢ (σˢ a b ⊗ˢ idˢ {c})
      hex' =
        ≈-trans hex
        (≈-trans (∘-resp (coe-id≈ (sym (++-assoc b c a))) ≈-refl)
        (≈-trans idˡ
        (≈-trans (∘-resp ≈-refl (coe-id≈ (sym (++-assoc a b c))))
        (≈-trans idʳ
          (∘-resp ≈-refl
            (≈-trans (∘-resp (coe-id≈ (++-assoc b a c)) ≈-refl) idˡ))))))

      -- LHS reduces definitionally to this composite.
      lhs-reduce
        : permuteˢ (Perm.↭-sym (PermProp.shift v (x ∷ R) L))
          ≈ˢ (idˢ {b} ⊗ˢ permuteˢ (Perm.↭-sym (PermProp.shift v R L)))
              ∘ˢ (σˢ a b ⊗ˢ idˢ {m (R ++ L)})
      lhs-reduce = ≈-refl

      -- the IH on the inner shift-sym, at R.
      ih : permuteˢ (Perm.↭-sym (PermProp.shift v R L))
           ≈ˢ castˢ (mdom v R L) (mcod v R L) (σˢ a c ⊗ˢ idˢ {m L})
      ih = shift-sym v R L

      -- the two ⊗-blocks of the common composite NF.
      Blk1 Blk2 : _
      Blk1 = (idˢ {b} ⊗ˢ σˢ a c) ⊗ˢ idˢ {m L}
      Blk2 = (σˢ a b ⊗ˢ idˢ {c}) ⊗ˢ idˢ {m L}

      -- (i) RHS → the framed-hexagon composite Blk1 ∘ˢ Blk2 (no cast inside).
      hexframe : σˢ a (vlab x ∷ m R) ⊗ˢ idˢ {m L} ≈ˢ Blk1 ∘ˢ Blk2
      hexframe =
        ≈-trans (⊗-resp hex' ≈-refl)
        (≈-trans (⊗-resp ≈-refl (≈-sym idˡ))
          (≈-sym interchangeˢ))

      -- (ii) LHS factor 1: framed IH.  `idˢ{b} ⊗ˢ castₘ(σˢ a c ⊗ˢ idˢ{mL})`
      -- equals `Blk1` up to a cast (pull cast out of the ⊗, then ⊗-assocˢ).
      F1 : idˢ {b} ⊗ˢ permuteˢ (Perm.↭-sym (PermProp.shift v R L))
           ≈ˢ castˢ (cong (b ++_) (mdom v R L))
                    (cong (b ++_) (mcod v R L))
                    (idˢ {b} ⊗ˢ (σˢ a c ⊗ˢ idˢ {m L}))
      F1 =
        ≈-trans (⊗-resp ≈-refl ih)
          (≈-sym (cast-⊗-frame (idˢ {b}) (mdom v R L) (mcod v R L)
                    (σˢ a c ⊗ˢ idˢ {m L})
                    (cong (b ++_) (mdom v R L)) (cong (b ++_) (mcod v R L))))

      -- ⊗-assocˢ relates `idˢ{b} ⊗ˢ (σˢ a c ⊗ˢ idˢ{mL})` to `Blk1`.
      assoc1
        : castˢ (++-assoc b (a ++ c) (m L)) (++-assoc b (c ++ a) (m L)) Blk1
          ≈ˢ idˢ {b} ⊗ˢ (σˢ a c ⊗ˢ idˢ {m L})
      assoc1 = ⊗-assocˢ (idˢ {b}) (σˢ a c) (idˢ {m L})

      -- box-suffix relates Blk2 to LHS factor 2 (`σˢ a b ⊗ˢ idˢ{c ++ mL}`).
      box2
        : castˢ (++-assoc (a ++ b) c (m L)) (++-assoc (b ++ a) c (m L)) Blk2
          ≈ˢ σˢ a b ⊗ˢ idˢ {c ++ m L}
      box2 = box-suffix-ˢ (σˢ a b) c (m L)

      -- factor 1 reduced to a single cast of Blk1.
      f1nf : idˢ {b} ⊗ˢ permuteˢ (Perm.↭-sym (PermProp.shift v R L))
             ≈ˢ castˢ (trans (++-assoc b (a ++ c) (m L))
                             (cong (b ++_) (mdom v R L)))
                      (trans (++-assoc b (c ++ a) (m L))
                             (cong (b ++_) (mcod v R L)))
                 Blk1
      f1nf =
        ≈-trans F1
        (≈-trans (cast-resp (cong (b ++_) (mdom v R L))
                            (cong (b ++_) (mcod v R L)) (≈-sym assoc1))
          (≡⇒≈ˢ (cast-fuse (++-assoc b (a ++ c) (m L))
                           (cong (b ++_) (mdom v R L))
                           (++-assoc b (c ++ a) (m L))
                           (cong (b ++_) (mcod v R L)) Blk1)))

      -- factor 2 reduced to a single cast of Blk2.
      MP : m (R ++ L) ≡ c ++ m L
      MP = map-++ vlab R L

      f2nf : σˢ a b ⊗ˢ idˢ {m (R ++ L)}
             ≈ˢ castˢ (trans (++-assoc (a ++ b) c (m L))
                             (cong ((a ++ b) ++_) (sym MP)))
                      (trans (++-assoc (b ++ a) c (m L))
                             (cong ((b ++ a) ++_) (sym MP)))
                 Blk2
      f2nf =
        ≈-trans (⊗-resp ≈-refl (≈-sym (cast-id (sym MP) (sym MP))))
        (≈-trans (≈-sym (cast-⊗-frame (σˢ a b) (sym MP) (sym MP) (idˢ {c ++ m L})
                   (cong ((a ++ b) ++_) (sym MP)) (cong ((b ++ a) ++_) (sym MP))))
        (≈-trans (cast-resp (cong ((a ++ b) ++_) (sym MP))
                            (cong ((b ++ a) ++_) (sym MP)) (≈-sym box2))
          (≡⇒≈ˢ (cast-fuse (++-assoc (a ++ b) c (m L)) (cong ((a ++ b) ++_) (sym MP))
                           (++-assoc (b ++ a) c (m L)) (cong ((b ++ a) ++_) (sym MP))
                           Blk2))))

      M1d = trans (++-assoc b (a ++ c) (m L)) (cong (b ++_) (mdom v R L))
      M1c = trans (++-assoc b (c ++ a) (m L)) (cong (b ++_) (mcod v R L))
      M2d = trans (++-assoc (a ++ b) c (m L)) (cong ((a ++ b) ++_) (sym MP))

      lhs-nf
        : permuteˢ (Perm.↭-sym (PermProp.shift v (x ∷ R) L))
          ≈ˢ castˢ (mdom v (x ∷ R) L) (mcod v (x ∷ R) L) (Blk1 ∘ˢ Blk2)
      lhs-nf =
        ≈-trans lhs-reduce
        (≈-trans (∘-resp f1nf f2nf)
        (≈-trans (∘-resp ≈-refl
                   (≡⇒≈ˢ (cast-irrel M2d M2d _ M1d Blk2)))
        (≈-trans (≈-sym (∘-cast-split M2d M1d M1c Blk1 Blk2))
          (≡⇒≈ˢ (cast-irrel M2d (mdom v (x ∷ R) L) M1c (mcod v (x ∷ R) L)
                   (Blk1 ∘ˢ Blk2))))))

      goal : permuteˢ (Perm.↭-sym (PermProp.shift v (x ∷ R) L))
             ≈ˢ castˢ (mdom v (x ∷ R) L) (mcod v (x ∷ R) L)
                 (σˢ a (vlab x ∷ m R) ⊗ˢ idˢ {m L})
      goal = ≈-trans lhs-nf (≈-sym (cast-resp _ _ hexframe))

  --------------------------------------------------------------------------
  -- (B)  The block-swap commutation, by induction on L.

  block-swap-comm : BswapSig
  block-swap-comm []      R = bswap-σ-base R
  block-swap-comm (v ∷ L) R = step
    where
      a c : List X
      a = vlab v ∷ []
      c = m R

      -- LHS reduces definitionally to this composite.
      lhs-reduce
        : permuteˢ (bswap (v ∷ L) R)
          ≈ˢ permuteˢ (Perm.↭-sym (PermProp.shift v R L))
              ∘ˢ (idˢ {a} ⊗ˢ permuteˢ (bswap L R))
      lhs-reduce = ≈-refl

      -- the cast-free core of both sides.
      CORE : _
      CORE = (σˢ a (m R) ⊗ˢ idˢ {m L}) ∘ˢ (idˢ {a} ⊗ˢ σˢ (m L) (m R))

      -- LEFT hexagon at the singleton frame `a = [vlab v]`: the two `++-assoc a …`
      -- associators collapse to refl, leaving only the genuine cod-cast.
      hexL : σˢ (vlab v ∷ m L) (m R) ≈ˢ castˢ refl (++-assoc (m R) a (m L)) CORE
      hexL = σ-hexˢ a (m L) (m R)

      -- the IH on the inner block.
      ih : permuteˢ (bswap L R)
           ≈ˢ castˢ (sym (map-++ vlab L R)) (sym (map-++ vlab R L)) (σˢ (m L) (m R))
      ih = block-swap-comm L R

      -- factor 2: pull the IH cast out of the right ⊗-factor.
      f2 : idˢ {a} ⊗ˢ permuteˢ (bswap L R)
           ≈ˢ castˢ (cong (a ++_) (sym (map-++ vlab L R)))
                    (cong (a ++_) (sym (map-++ vlab R L)))
               (idˢ {a} ⊗ˢ σˢ (m L) (m R))
      f2 =
        ≈-trans (⊗-resp ≈-refl ih)
          (≈-sym (cast-⊗-frame (idˢ {a}) (sym (map-++ vlab L R))
                    (sym (map-++ vlab R L)) (σˢ (m L) (m R))
                    (cong (a ++_) (sym (map-++ vlab L R)))
                    (cong (a ++_) (sym (map-++ vlab R L)))))

      F1d = mdom v R L
      F1c = mcod v R L
      F2d = cong (a ++_) (sym (map-++ vlab L R))
      F2c = cong (a ++_) (sym (map-++ vlab R L))

      -- LHS → a single cast of CORE (the dom is factor 2's dom F2d, the cod is
      -- factor 1's cod F1c; the middle is factor 1's dom F1d).
      lhs-nf : permuteˢ (bswap (v ∷ L) R) ≈ˢ castˢ F2d F1c CORE
      lhs-nf =
        ≈-trans lhs-reduce
        (≈-trans (∘-resp (shift-sym v R L) f2)
        (≈-trans (∘-resp ≈-refl (≡⇒≈ˢ (cast-irrel F2d F2d F2c F1d
                                         (idˢ {a} ⊗ˢ σˢ (m L) (m R)))))
          (≈-sym (∘-cast-split F2d F1d F1c
                    (σˢ a (m R) ⊗ˢ idˢ {m L}) (idˢ {a} ⊗ˢ σˢ (m L) (m R))))))

      step : permuteˢ (bswap (v ∷ L) R)
             ≈ˢ castˢ (sym (map-++ vlab (v ∷ L) R)) (sym (map-++ vlab R (v ∷ L)))
                 (σˢ (vlab v ∷ m L) (m R))
      step =
        ≈-trans lhs-nf
        (≈-trans (≡⇒≈ˢ (cast-irrel F2d (sym (map-++ vlab (v ∷ L) R))
                          F1c (trans (++-assoc (m R) a (m L))
                                     (sym (map-++ vlab R (v ∷ L)))) CORE))
        (≈-sym
          (≈-trans (cast-resp (sym (map-++ vlab (v ∷ L) R))
                              (sym (map-++ vlab R (v ∷ L))) hexL)
            (≡⇒≈ˢ (cast-fuse refl (sym (map-++ vlab (v ∷ L) R))
                     (++-assoc (m R) a (m L)) (sym (map-++ vlab R (v ∷ L)))
                     CORE)))))
