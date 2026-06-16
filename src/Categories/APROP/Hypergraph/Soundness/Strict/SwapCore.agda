{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The STRICT EMPTY-TAIL two-edge interchange core `run-interchange₀ˢ`.
--
-- Strict twin of `Discharge/Sub/RunInterchangeEmptyTail.run-interchange₀`.
-- For two adjacent INCOMPARABLE edges `e , e'` fired from the same stack,
-- processing `[e , e']` versus `[e' , e]` yields `≈ˢ`-equal strict terms
-- (modulo the stack-permutation reshuffle).
--
-- The non-strict proof pays ~5000 LOC of Mac-Lane mass (the `BlockNF`
-- view frames `view-in≅`/`view-out≅`, the σ-block-comm/Yang–Baxter
-- algebra, the `unflatten-++-≅` conjugations).  In the strict SMC `S`
-- (`FreeStrictSMC.Build` at `FlatGen`), `⊗ˢ = ++` on the nose, so the
-- two-box commutation is the 4-line `box-commute-ˢ`, and all bracketing
-- becomes the UIP-trivial `castˢ` kit.
--
-- ARCHITECTURE (per §4 of `docs/strictification-part2-map.md`):
--   * `fire-midˢ`/`fire-termˢ` — the strict fired layer, matching the
--     strict decoder's `edge-stepˢ` fire branch on the nose, so that the
--     `EdgeStepRˢ` view's `fireRˢ` index is DEFINITIONALLY
--     `proj₂ (edge-stepˢ s e)`.
--   * `EdgeStepRˢ` — the inductive graph of `edge-stepˢ`; matching its
--     `skipRˢ`/`fireRˢ` constructors refines the otherwise-stuck
--     `edge-stepˢ` redex (dodges green-slime).
--   * `fire-mid-interchangeˢ` — the both-fire core: the two framed boxes
--     on disjoint blocks commute, via `box-commute-ˢ`, transported through
--     the `SimLoc`-located permutes (the deferred K residual `permˢ-K`
--     enters exactly here, via `perm-rigidˢ`).
--   * `build` + `run-interchange₀ˢ` — the four-way firing split, mirroring
--     the non-strict skeleton with `Reservoir≤1`-sourced `Unique`
--     witnesses (bridged from the non-strict reservoir via `stacks-agree`).
--
-- The TERM-FREE combinatorics (`SimLoc`, `extract-ein'`, the stability
-- lemmas, the reservoir machinery) are REUSED AS-IS from the non-strict
-- leaves — they live at the `_↭_`/`count`/`process-edges` level and the
-- strict stacks are DEFINITIONALLY equal to the non-strict ones
-- (`stacks-agree`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.SwapCore
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (extract-prefix; process-edges; edge-step)
open import Categories.APROP.Hypergraph.Soundness.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_

import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidInterchangeComb sig
  as FMIC
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig
  as SUR

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

private
  nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
  nothing≢just ()

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open StrictDecoder H

  -- The deferred strict Kelly residual, specialised to this hypergraph's
  -- vertex set.  `perm-rigidˢ` is its only consumer.
  module Kmod = Support (Fin H.nV) H.vlab
  open Kmod using (PermK)

  --------------------------------------------------------------------
  -- The strict fired layer, matching `edge-stepˢ`'s fire branch.
  --------------------------------------------------------------------

  -- The framed box of an edge `e` on the residual `rest`, with the input
  -- locating permute `perm`.  This is EXACTLY `proj₂ (edge-stepˢ s e)` on
  -- the FIRE branch (`extract-prefix (H.ein e) s ≡ just (rest , perm)`).
  fire-termˢ
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
    → s Perm.↭ H.ein e ++ rest
    → HomS (map vl s) (map vl (H.eout e ++ rest))
  fire-termˢ e s rest perm =
    castˢ refl (sym (map-++ vl (H.eout e) rest))
      ((genˢ (H.elab e) ⊗ˢ idˢ {map vl rest})
        ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ perm))

  --------------------------------------------------------------------
  -- The graph of `edge-stepˢ` as an inductive relation.
  --------------------------------------------------------------------

  data EdgeStepRˢ (s : List (Fin H.nV)) (e : Fin H.nE)
       : (s' : List (Fin H.nV)) → HomS (map vl s) (map vl s') → Set where
    skipRˢ : extract-prefix (H.ein e) s ≡ nothing
           → EdgeStepRˢ s e s idˢ
    fireRˢ : ∀ (rest : List (Fin H.nV)) (perm : s Perm.↭ H.ein e ++ rest)
           → extract-prefix (H.ein e) s ≡ just (rest , perm)
           → EdgeStepRˢ s e (H.eout e ++ rest) (fire-termˢ e s rest perm)

  -- The function realises the relation.
  edge-stepˢ-graph
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
    → EdgeStepRˢ s e (proj₁ (edge-stepˢ s e)) (proj₂ (edge-stepˢ s e))
  edge-stepˢ-graph s e with extract-prefix (H.ein e) s in eq
  ... | nothing            = skipRˢ eq
  ... | just (rest , perm) = fireRˢ rest perm eq

  --------------------------------------------------------------------
  -- Abbreviations for the two `process-edgesˢ` projections + `Incomp`.
  --------------------------------------------------------------------

  Incomp : Fin H.nE → Fin H.nE → Set
  Incomp e e' = (¬ Dep H e e') × (¬ Dep H e' e)

  pe-stackˢ : List (Fin H.nE) → List (Fin H.nV) → List (Fin H.nV)
  pe-stackˢ o s = proj₁ (process-edgesˢ o s)

  pe-termˢ : (o : List (Fin H.nE)) (s : List (Fin H.nV))
           → HomS (map vl s) (map vl (pe-stackˢ o s))
  pe-termˢ o s = proj₂ (process-edgesˢ o s)

  --------------------------------------------------------------------
  -- LEFT-FRAME for `permuteˢ` (the `++⁺ˡ` mirror of `permuteˢ-frame`;
  -- §4's `permuteˢ-frameˡ`).  A `++⁺ˡ ls` framing of a permute factors
  -- through `idˢ {map vl ls} ⊗ˢ_`.  K-FREE; cons clauses reduce.
  --------------------------------------------------------------------

  permuteˢ-frameˡ
    : ∀ (ls : List (Fin H.nV)) {xs ys : List (Fin H.nV)} (p : xs Perm.↭ ys)
    → castˢ (map-++ vl ls xs) (map-++ vl ls ys)
        (permuteˢ (PermProp.++⁺ˡ ls p))
      ≈ˢ idˢ {map vl ls} ⊗ˢ permuteˢ p
  permuteˢ-frameˡ []       {xs} {ys} p =
    ≈-trans (≡⇒≈ˢ (cast-irrel (map-++ vl [] xs) refl
                              (map-++ vl [] ys) refl (permuteˢ p)))
            (≈-sym (⊗-unitˡˢ (permuteˢ p)))
  permuteˢ-frameˡ (l ∷ ls) {xs} {ys} p =
    ≈-trans
      (cast-⊗-frame (idˢ {vl l ∷ []})
        (map-++ vl ls xs) (map-++ vl ls ys)
        (permuteˢ (PermProp.++⁺ˡ ls p))
        (map-++ vl (l ∷ ls) xs) (map-++ vl (l ∷ ls) ys))
      (≈-trans (⊗-resp (≈-refl {f = idˢ {vl l ∷ []}}) (permuteˢ-frameˡ ls p))
        (≈-trans (≈-sym (⊗-assocˢ (idˢ {vl l ∷ []}) (idˢ {map vl ls})
                                  (permuteˢ p)))
          (cast-resp (++-assoc (vl l ∷ []) (map vl ls) _)
                     (++-assoc (vl l ∷ []) (map vl ls) _)
                     (⊗-resp ⊗-id ≈-refl))))

  --------------------------------------------------------------------
  -- THE BOTH-FIRE CORE (M) — `fire-mid-interchangeˢ`.
  --
  -- The two framed boxes on DISJOINT wire blocks commute via
  -- `box-commute-ˢ`, transported through the `SimLoc`-located permutes.
  -- The deferred K residual `permˢ-K` enters via `perm-rigidˢ`.
  --------------------------------------------------------------------

  module _ (permˢ-K : PermK) where
    perm-rigidˢ
      : ∀ {xs ys : List (Fin H.nV)} → Unique ys
        → (p q : xs Perm.↭ ys) → permuteˢ p ≈ˢ permuteˢ q
    perm-rigidˢ = Kmod.perm-rigidˢ permˢ-K

    ----------------------------------------------------------------
    -- Located single fire box.  Given a derivation `loc : s ↭
    -- (ein e ++ B) ++ R` that factors the fire input `perm : s ↭
    -- ein e ++ rest` through `rest ↭ B ++ R` (`q : rest ↭ B ++ R`),
    -- the fire box locates its residual into the two blocks `B`, `R`:
    --
    --   fire-termˢ e s rest perm
    --     ≈ˢ castˢ (out-cast) ((genˢ e ⊗ˢ idˢ{B}) ⊗ˢ idˢ{R})
    --          ∘ˢ castˢ (in-cast) (permuteˢ loc)
    --
    -- where `loc = trans perm (++⁺ˡ (ein e) q)` re-bracketed.  All the
    -- bracketing is the `castˢ` kit; `perm-rigidˢ` is NOT needed for a
    -- single box (the derivation is CHOSEN to factor), only the
    -- equality `permuteˢ perm ≈ˢ permuteˢ (trans ...)` which is
    -- definitional when `loc` is built from `perm`.
    ----------------------------------------------------------------
    -- The LOCATED two-box interchange kernel (the strict heart, the
    -- analogue §4 calls `box-crossˢ`).  Two boxes `g : A → B`,
    -- `g' : A' → B'` sitting side by side, framed by a residual `R`,
    -- commute through the block braidings on their (co)domains:
    --
    --   ((g' ⊗ˢ g) ⊗ˢ idˢ{R})
    --     ≈ˢ ((σ B B' ⊗ˢ idˢ{R}) ∘ˢ ((g ⊗ˢ g') ⊗ˢ idˢ{R})) ∘ˢ (σ A' A ⊗ˢ idˢ{R})
    --
    -- This is the genuine N-content of the both-fire interchange,
    -- already located at the 3-block level; it is `box-commute-ˢ`-style
    -- σ-conjugation lifted by `_⊗ˢ idˢ{R}` and is K-free.
    box-crossˢ
      : ∀ {A B A' B' : List X} (g : HomS A B) (g' : HomS A' B')
          (R : List X)
      → (g' ⊗ˢ g) ⊗ˢ idˢ {R}
        ≈ˢ ((σˢ B B' ⊗ˢ idˢ {R}) ∘ˢ ((g ⊗ˢ g') ⊗ˢ idˢ {R}))
             ∘ˢ (σˢ A' A ⊗ˢ idˢ {R})
    box-crossˢ {A} {B} {A'} {B'} g g' R =
      ≈-trans (⊗-resp conj ≈-refl)
        (≈-trans (⊗id-dist (σˢ B B') ((g ⊗ˢ g') ∘ˢ σˢ A' A))
          (≈-trans (∘-resp ≈-refl (⊗id-dist (g ⊗ˢ g') (σˢ A' A)))
            (≈-sym assocˢ)))
      where
        -- `(X ∘ˢ Y) ⊗ˢ id  ≈  (X ⊗ˢ id) ∘ˢ (Y ⊗ˢ id)`
        ⊗id-dist
          : ∀ {as bs cs} (Xt : HomS bs cs) (Yt : HomS as bs)
          → (Xt ∘ˢ Yt) ⊗ˢ idˢ {R} ≈ˢ (Xt ⊗ˢ idˢ {R}) ∘ˢ (Yt ⊗ˢ idˢ {R})
        ⊗id-dist Xt Yt =
          ≈-trans (⊗-resp ≈-refl (≈-sym idˡ)) (≈-sym interchangeˢ)
        -- σ-conjugation form: `g' ⊗ˢ g ≈ σ ∘ (g ⊗ˢ g') ∘ σ`.
        conj : g' ⊗ˢ g ≈ˢ σˢ B B' ∘ˢ ((g ⊗ˢ g') ∘ˢ σˢ A' A)
        conj =
          ≈-sym
            (≈-trans (≈-sym assocˢ)
              (≈-trans (∘-resp σ-natˢ ≈-refl)
                (≈-trans assocˢ
                  (≈-trans (∘-resp ≈-refl σ-σˢ) idʳ))))

    ----------------------------------------------------------------
    -- `permuteˢ` of an inverse derivation is the categorical inverse
    -- (K-FREE, structural on the derivation).  §4's `permuteˢ-inv`.
    ----------------------------------------------------------------

    permuteˢ-inv-left
      : ∀ {xs ys : List (Fin H.nV)} (p : xs Perm.↭ ys)
      → permuteˢ (Perm.↭-sym p) ∘ˢ permuteˢ p ≈ˢ idˢ {map vl xs}
    permuteˢ-inv-left Perm.refl         = idˡ
    permuteˢ-inv-left (Perm.prep x p)   =
      ≈-trans interchangeˢ
        (≈-trans (⊗-resp idˡ (permuteˢ-inv-left p)) ⊗-id)
    permuteˢ-inv-left (Perm.swap x y p) =
      ≈-trans interchangeˢ
        (≈-trans (⊗-resp σ-σˢ (permuteˢ-inv-left p)) ⊗-id)
    permuteˢ-inv-left (Perm.trans p q)  =
      ≈-trans assocˢ
        (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
          (≈-trans (∘-resp ≈-refl (∘-resp (permuteˢ-inv-left q) ≈-refl))
            (≈-trans (∘-resp ≈-refl idˡ) (permuteˢ-inv-left p))))

    permuteˢ-inv-right
      : ∀ {xs ys : List (Fin H.nV)} (p : xs Perm.↭ ys)
      → permuteˢ p ∘ˢ permuteˢ (Perm.↭-sym p) ≈ˢ idˢ {map vl ys}
    permuteˢ-inv-right Perm.refl         = idˡ
    permuteˢ-inv-right (Perm.prep x p)   =
      ≈-trans interchangeˢ
        (≈-trans (⊗-resp idˡ (permuteˢ-inv-right p)) ⊗-id)
    permuteˢ-inv-right (Perm.swap x y p) =
      ≈-trans interchangeˢ
        (≈-trans (⊗-resp σ-σˢ (permuteˢ-inv-right p)) ⊗-id)
    permuteˢ-inv-right (Perm.trans p q)  =
      ≈-trans assocˢ
        (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
          (≈-trans (∘-resp ≈-refl (∘-resp (permuteˢ-inv-right p) ≈-refl))
            (≈-trans (∘-resp ≈-refl idˡ) (permuteˢ-inv-right q))))

    ----------------------------------------------------------------
    -- Residual decomposition of a fire box: the identity on the
    -- residual `rest` is split through a relocating permute `q :
    -- rest ↭ B ++ R`, exposing the box as a relocate-output followed
    -- by the box with a relocated residual input.  K-FREE (uses only
    -- permuteˢ-inv-left + interchange).
    --
    --   genˢ e ⊗ˢ idˢ{map vl rest}
    --     ≈ˢ (idˢ{map vl (eout e)} ⊗ˢ permuteˢ (↭-sym q))
    --          ∘ˢ (genˢ e ⊗ˢ permuteˢ q)
    ----------------------------------------------------------------
    box-residual-split
      : ∀ (e : Fin H.nE) {rest : List (Fin H.nV)} {BR : List (Fin H.nV)}
          (q : rest Perm.↭ BR)
      → genˢ (H.elab e) ⊗ˢ idˢ {map vl rest}
        ≈ˢ (idˢ {map vl (H.eout e)} ⊗ˢ permuteˢ (Perm.↭-sym q))
             ∘ˢ (genˢ (H.elab e) ⊗ˢ permuteˢ q)
    box-residual-split e {rest} q =
      ≈-trans (⊗-resp (≈-sym idˡ) (≈-sym (permuteˢ-inv-left q)))
        (≈-sym interchangeˢ)
