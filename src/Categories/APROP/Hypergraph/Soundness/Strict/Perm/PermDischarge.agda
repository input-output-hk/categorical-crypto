{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- DISCHARGE of the strict Kelly residual `permˢ-K` (the single deep residual
-- of the strictified soundness pipeline; see `PermSupport`).
--
-- Strategy (route (i) of the migration brief): rather than transporting the
-- non-strict `permute`-faithfulness through the embedding `embF` and then
-- RE-REFLECTING `≈Term → ≈ˢ` (which `embF` does NOT do in general, since its
-- generator family is arbitrary `HomTerm`s), we re-run the proven inductive
-- congruence `_≅↭ⁱ_` DIRECTLY at the strict level.
--
-- The combinatorial core `complete : eval-↭ p ≈-fb eval-↭ q → p ≅↭ⁱ q`
-- (the Coxeter / word-problem kernel of `FaithfulnessInductive`) is purely
-- element-level: it never touches term structure, so it is reusable verbatim
-- at the vertex set `V` by instantiating it there directly.  We then prove
-- the STRICT mirror of `permute-resp-≅↭ⁱ`:
--
--     permuteˢ-resp-≅↭ⁱ : p ≅↭ⁱ q → permuteˢ p ≈ˢ permuteˢ q
--
-- one strict-SMC axiom per `_≅↭ⁱ_` generator.  Because `permuteˢ` builds the
-- swap as the BARE block `σˢ [vx] [vy] ⊗ˢ permuteˢ p` (no associator framing —
-- the strict `++` makes singleton frames reduce definitionally), the swap
-- coherence cases are SIMPLER than their non-strict counterparts.
--
-- Composing `complete` with `permuteˢ-resp-≅↭ⁱ` gives `permˢ-K`.
--------------------------------------------------------------------------------

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermDischarge
  (X : Set) (_≟X_ : DecidableEquality X)
  where

open import Categories.FreeStrictSMC using (module Build)

open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (_≈-fb_)

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.Braid X _≟X_ as BR

--------------------------------------------------------------------------------
-- The element-level inductive congruence `_≅↭ⁱ_` and its combinatorial
-- completeness `complete`, instantiated directly at the vertex set `V`.

module Discharge (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X)
  (mor : List X → List X → Set) where

  open import Categories.PermuteCoherence.Coxeter.FaithfulnessInductive V _≟V_
    using (_≅↭ⁱ_; complete)
  open _≅↭ⁱ_

  open Build X _≟X_ mor
  open Perm′ V vlab
  module BG = BR.Generic mor

  ------------------------------------------------------------------------
  -- The SINGLE residual of this discharge: the strict Yang-Baxter braid on
  -- three single strands `[a] [b] [c]` with a common right tail `M`, i.e.
  -- `Braid.Generic.BraidAt` at this very `Build X _≟X_ mor` instance — a
  -- closed, semantics-free coherence equation (`s₁s₂s₁ = s₂s₁s₂`), TRUE in
  -- every symmetric monoidal category and proven for every generator family by
  -- `Braid.Generic.strict-braid`.  It is threaded as a parameter here;
  -- everything else is constructed.

  StrictBraid : Set
  StrictBraid = ∀ (a b c : X) (M : List X) → BG.BraidAt a b c M

  module Main (braidX : StrictBraid) where

    ----------------------------------------------------------------------
    -- Swap-case helpers.  Notation: `permuteˢ (swap a b p) = σˢ [va] [vb] ⊗ˢ
    -- permuteˢ p` and `permuteˢ (prep a p) = idˢ {[va]} ⊗ˢ permuteˢ p`, with
    -- `[va] = vlab a ∷ []`.  As the σ-block frames are SINGLETONS, the
    -- associativity proofs `++-assoc [va] [vb] _` reduce to `refl`, so the
    -- `⊗-assocˢ` casts vanish definitionally.

    private
      -- σ-naturality (right square): a swap with inner `p` factors as the
      -- prep-tower followed by a bare front swap.
      swap-nat-case
        : ∀ {x y : V} {xs ys : List V} (p : xs ↭ ys)
        → σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ permuteˢ p
          ≈ˢ (σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ idˢ {map vlab ys})
              ∘ˢ (idˢ {vlab x ∷ []} ⊗ˢ (idˢ {vlab y ∷ []} ⊗ˢ permuteˢ p))
      swap-nat-case {x} {y} p =
        ≈-sym
          (≈-trans (∘-resp ≈-refl (≈-sym (⊗-assocˢ (idˢ {vlab x ∷ []})
                                                   (idˢ {vlab y ∷ []})
                                                   (permuteˢ p))))
          (≈-trans interchangeˢ
                   (⊗-resp (≈-trans (∘-resp ≈-refl ⊗-id) idʳ) idˡ)))

      -- σ-naturality (left square): matches `permuteˢ (swap x y p)` after the
      -- id-tower on the right collapses (no interchange needed).
      swap-nat-left-case
        : ∀ {x y : V} {xs ys : List V} (p : xs ↭ ys)
        → σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ permuteˢ p
          ≈ˢ (idˢ {vlab y ∷ []} ⊗ˢ (idˢ {vlab x ∷ []} ⊗ˢ permuteˢ p))
              ∘ˢ (σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ idˢ {map vlab xs})
      swap-nat-left-case {x} {y} p =
        ≈-sym
          (≈-trans (∘-resp (≈-sym (⊗-assocˢ (idˢ {vlab y ∷ []})
                                            (idˢ {vlab x ∷ []})
                                            (permuteˢ p))) ≈-refl)
          (≈-trans interchangeˢ
                   (⊗-resp (≈-trans (∘-resp ⊗-id ≈-refl) idˡ) idʳ)))

      -- The Yang-Baxter braid in the exact shape produced by `permuteˢ` of
      -- the two `swap-braid` derivations; delegated to the `braidX` residual.
      braid₃ : ∀ (x y z : V) (M : List X) → BG.BraidAt (vlab x) (vlab y) (vlab z) M
      braid₃ x y z M = braidX (vlab x) (vlab y) (vlab z) M

      swap-braid-case
        : ∀ {x y z : V} {xs : List V}
        → permuteˢ (Perm.trans (Perm.swap x y (Perm.refl {xs = z ∷ xs}))
                     (Perm.trans (Perm.prep y (Perm.swap x z (Perm.refl {xs = xs})))
                                 (Perm.swap y z (Perm.refl {xs = x ∷ xs}))))
          ≈ˢ
          permuteˢ (Perm.trans (Perm.prep x (Perm.swap y z (Perm.refl {xs = xs})))
                     (Perm.trans (Perm.swap x z (Perm.refl {xs = y ∷ xs}))
                                 (Perm.prep z (Perm.swap x y (Perm.refl {xs = xs})))))
      swap-braid-case {x} {y} {z} {xs} = braid₃ x y z (map vlab xs)

    --------------------------------------------------------------------
    -- The strict mirror of `permute-resp-≅↭ⁱ`: one strict-SMC axiom per
    -- `_≅↭ⁱ_` generator.

    permuteˢ-resp-≅↭ⁱ
      : ∀ {xs ys : List V} {p q : xs ↭ ys}
      → p ≅↭ⁱ q → permuteˢ p ≈ˢ permuteˢ q
    permuteˢ-resp-≅↭ⁱ iref          = ≈-refl
    permuteˢ-resp-≅↭ⁱ (isym h)      = ≈-sym (permuteˢ-resp-≅↭ⁱ h)
    permuteˢ-resp-≅↭ⁱ (itrn h₁ h₂)  = ≈-trans (permuteˢ-resp-≅↭ⁱ h₁) (permuteˢ-resp-≅↭ⁱ h₂)
    permuteˢ-resp-≅↭ⁱ (prepc h)     = ⊗-resp ≈-refl (permuteˢ-resp-≅↭ⁱ h)
    permuteˢ-resp-≅↭ⁱ (trc h₁ h₂)   = ∘-resp (permuteˢ-resp-≅↭ⁱ h₂) (permuteˢ-resp-≅↭ⁱ h₁)
    -- trans refl p ↦ permuteˢ p ∘ˢ idˢ
    permuteˢ-resp-≅↭ⁱ tr-unitˡ      = idʳ
    -- trans p refl ↦ idˢ ∘ˢ permuteˢ p
    permuteˢ-resp-≅↭ⁱ tr-unitʳ      = idˡ
    permuteˢ-resp-≅↭ⁱ tr-assoc      = ≈-sym assocˢ
    permuteˢ-resp-≅↭ⁱ prep-id       = ⊗-id
    permuteˢ-resp-≅↭ⁱ prep-tr       = ≈-sym (≈-trans interchangeˢ (⊗-resp idˡ ≈-refl))
    permuteˢ-resp-≅↭ⁱ swap-invol    = ≈-trans interchangeˢ (≈-trans (⊗-resp σ-σˢ idˡ) ⊗-id)
    permuteˢ-resp-≅↭ⁱ (swap-nat {p = p})      = swap-nat-case p
    permuteˢ-resp-≅↭ⁱ (swap-nat-left {p = p}) = swap-nat-left-case p
    permuteˢ-resp-≅↭ⁱ swap-braid              = swap-braid-case

    --------------------------------------------------------------------
    -- The headline residual: the strict Kelly residual `permˢ-K`, modulo the
    -- single `StrictBraid` coherence.

    permˢ-K
      : ∀ {xs ys : List V} (p q : xs ↭ ys)
      → eval-↭ p ≈-fb eval-↭ q
      → permuteˢ p ≈ˢ permuteˢ q
    permˢ-K p q eq = permuteˢ-resp-≅↭ⁱ (complete eq)
