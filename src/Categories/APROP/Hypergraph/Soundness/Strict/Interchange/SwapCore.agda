{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The STRICT `EdgeStepRˢ` algebra bricks for the two-edge interchange.
--
--   * `fire-termˢ`/`EdgeStepRˢ`/`edge-stepˢ-graph` — the strict fired layer
--     and the inductive graph of `edge-stepˢ`, re-exported from the shared
--     `EdgeStepRel` leaf under this module's `(H)` telescope.
--   * `Incomp`, `pe-stackˢ`/`pe-termˢ` — incomparability + `process-edgesˢ`
--     projection abbreviations.
--   * `permuteˢ-frameˡ`, `box-crossˢ`, `permuteˢ-inv-left/right` — the
--     located two-box interchange kernel and its permute algebra (the
--     deferred K residual `permˢ-K` enters via `perm-rigidˢ`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.EdgeStepRel sig _≟X_
  using (module EdgeStepView)
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl; cong)

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H

  -- The deferred strict Kelly residual, specialised to this hypergraph's
  -- vertex set.  `perm-rigidˢ` is its only consumer.
  module Kmod = Support (Fin H.nV) H.vlab
  open Kmod using (PermK)

  --------------------------------------------------------------------
  -- The strict fired layer (`fire-termˢ`) + the `EdgeStepRˢ` graph of
  -- `edge-stepˢ`, re-exported from the shared `EdgeStepRel` leaf.
  --------------------------------------------------------------------

  open EdgeStepView H public

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
        (≈-trans (⊗id-distˢ (σˢ B B') ((g ⊗ˢ g') ∘ˢ σˢ A' A))
          (≈-trans (∘-resp ≈-refl (⊗id-distˢ (g ⊗ˢ g') (σˢ A' A)))
            (≈-sym assocˢ)))
      where
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

    -- the mirror of `permuteˢ-inv-left`, derived from it (rather than
    -- re-derived by structural induction on `p`) via stdlib's
    -- `↭-sym-involutive : ↭-sym (↭-sym p) ≡ p`.
    permuteˢ-inv-right
      : ∀ {xs ys : List (Fin H.nV)} (p : xs Perm.↭ ys)
      → permuteˢ p ∘ˢ permuteˢ (Perm.↭-sym p) ≈ˢ idˢ {map vl ys}
    permuteˢ-inv-right p =
      ≈-trans
        (∘-resp (≈-sym (≡⇒≈ˢ (cong permuteˢ (PermProp.↭-sym-involutive p)))) ≈-refl)
        (permuteˢ-inv-left (Perm.↭-sym p))

