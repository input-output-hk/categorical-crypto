{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict decoder `∘`-SHAPE (part (I)ˢ), Stage 1: the block-level
-- factoring of the strict run.
--
-- GOAL (full):
--     decodePˢ (g ∘ f) ≈ˢ decodePˢ g ∘ˢ decodePˢ f
--
-- The non-strict original is `Discharge.Sub.DecodeComposePruned.decodeP-∘-shape`
-- (~650 LOC over `hComposeP`).  Its skeleton:
--   1. `⟪ g ∘ f ⟫ = hComposeP ⟪f⟫ ⟪g⟫`, edges factor as `gblk ++ kblk`;
--   2. RUN-SPLIT: the composite run factors `kblk-run ∘ gblk-run` (`pe-term-++`);
--   3. G-block / K-block TWINS: each block-run relabels onto the sub-decoder
--      run via `TermEmbed.process-edges-term-emb` (φ = injL / remapP);
--   4. EQUIVARIANCE (`StackEquivariance`): the K-block on the actual post-G
--      stack ≈ the K-block on the canonical stack, conjugated by a permute,
--      via the Kelly residual `Kf`;
--   5. perm-coherence via `Kf` / `permˢ-K`.
--
-- DELIVERED so far (green, committed):
--
--   §0  permuteˢ-X      — the CROSS-VERTEX-TYPE permute bridge: a V-level
--                         strict permute equals (modulo a `map-id` boundary
--                         cast) the X-LEVEL permute (`permuteˣ`) of the
--                         label-pushed derivation `map⁺ vlab p`.  This is the
--                         keystone that makes the single-vertex-type residual
--                         `permˢ-K X id` able to discharge CROSS-hypergraph
--                         permute equalities (composite `Fin C.nV` vs
--                         sub-decoder `Fin G.nV`/`Fin K.nV`).  The strict
--                         analogue of routing through `PermProp.map⁺ vlab`
--                         into the non-strict X-level FaithfulnessResidual.
--
--   §1  pe-stack-++ˢ    — strict stack factoring (refl-pure, inherited shape);
--       pe-term-++ˢ     — strict TERM factoring of `process-edgesˢ (ps ++ rest)`
--                         into `rest`-run ∘ˢ `ps`-run, modulo a stack cast;
--       run-split-atˢ   — the composite run at any `es ≡ gblk ++ kblk` factors.
--                         (The strict `castˢ` kit collapses the non-strict
--                         `coe-cod`/`subst`/`assoc` plumbing.)
--
-- ────────────────────────────────────────────────────────────────────────
-- OBSTRUCTION MAP for the remaining `decodePˢ (g ∘ f) ≈ˢ …` assembly.
--
-- What is left is the strict port of two non-strict modules and the final
-- assembly (~650 LOC non-strict total):
--
--   (A) `ProcessEdgesTermShape.TermEmbed.process-edges-term-emb` — the
--       per-edge + iterated RELABELLING-EQUIVARIANCE twin, parameterised by an
--       injective, label-preserving vertex embedding (φ, ψ).  Its FIRE case
--       splits into:
--         • BOX factor (`fire-mid-emb`): in the strict world this is a
--           `genˢ`-relabelling cast.  REQUIRES a new strict lemma
--               gen-cast : castˢ p q (genˢ g) ≡ genˢ (subst₂ FlatGen p q g)
--           (provable `gen-cast refl refl g = refl`), composed with the
--           edge-endpoint label equalities `atom-ein/atom-eout` and `ψ-elab`
--           (these transport unchanged from `hComposeP-impl`).
--         • PERMUTE factor (`fire-perm-emb`): REDUCES to §0 `permuteˢ-X` (both
--           sides) + `permˢ-K X id` driven by `eval-coincide`.  `eval-coincide`
--           delivers a `subst₂ FinBij`-cast of the J-side `eval-↭`; aligning it
--           with the bare `permˢ-K` premise is the main residual cast algebra.
--       The SKIP/FIRE lock-step uses `extract-prefix-via-injective-{just,nothing}`
--       (already in `DecodeProperties`), exactly as the non-strict
--       `extract-prefix-J-{just,nothing}`.
--
--   (B) `StackEquivariance.process-edges-equivariant` — the K-block on the
--       ACTUAL post-G stack `after-G` ≈ the K-block on the CANONICAL stack
--       `map remapP K.dom`, conjugated by a `permuteˢ`.  Strict version needs
--       the run on a permuted start stack to be the conjugate of the run on
--       the canonical stack: `runˢ (perm·s) ≈ permuteˢ⁻¹ ∘ runˢ s ∘ permuteˢ`.
--       This is the genuinely-new equivariance (no strict counterpart yet);
--       the non-strict proof threads `Kf` and a reservoir argument
--       (`StackUniqueReach`).  §0 again supplies the cross-V permute identity
--       its conjugation step needs.
--
--   (C) Final assembly (`decodeP-∘-shape`): RUN-SPLIT (§1 `run-split-atˢ`) →
--       block twins (A, φ = injL / remapP) → equivariance (B) → reassoc →
--       `permˢ-K`-coherence on the final permutes (the strict analogues of
--       `permC-coh`/`permRemap-coh`, both via `perm-rigidˢ` on `Unique`
--       codomains, available from `PermSupport`).  The boundary `castˢ`
--       (`⟪⟫-domL`/`-codL` for `g ∘ f`) align definitionally as in `DecodeS`.
--
-- The pruned ingredients `process-edges-↑ˡ-pure-L` / `remapP-injective` /
-- `map-remapP-K-dom` are STACK-level (term-free) and transfer verbatim from
-- the non-strict `DecodeAttemptLinearP` / `LinearHComposeP` (the strict and
-- non-strict runs walk the SAME stacks — `Run.stacks-agree`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.DecodeComposeS
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (edge-step; process-edges)

open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeS sig _≟X_ public

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-id)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- ## §0.  The cross-vertex-type permute bridge.
--
-- The strict Kelly residual `permˢ-K` is parameterised by a SINGLE vertex
-- type `V`.  The composition `∘`-shape, however, relates the run over the
-- relabelled composite (vertex type `Fin C.nV`) to the sub-decoder runs
-- (vertex types `Fin G.nV` / `Fin K.nV`).  To compare `permuteˢ` derivations
-- across vertex types we route both through the X-LEVEL permute (vertex type
-- `X`, label `id`): `permuteˢ {V} vlab p` and the X-level permute of
-- `map⁺ vlab p` build the SAME `HomS` term, modulo the `map-id`/`map-∘`
-- relabelling of the boundary lists.  Then `permˢ-K X id` (driven by
-- `eval-coincide`) identifies the two X-level permutes.

module XPerm where
  open Perm′ X (λ x → x) public renaming (permuteˢ to permuteˣ)

-- `permuteˢ` at a vertex type `V` equals (up to the `map-id ∘ map-∘`
-- boundary cast) the X-level permute of the label-pushed derivation.
module _ (V : Set) (vlab : V → X) where
  open Perm′ V vlab using (permuteˢ)
  open XPerm using (permuteˣ)

  -- boundary: map id (map vlab xs) ≡ map vlab xs
  mp : (xs : List V) → map (λ x → x) (map vlab xs) ≡ map vlab xs
  mp xs = map-id (map vlab xs)

  permuteˢ-X
    : ∀ {xs ys : List V} (p : xs Perm.↭ ys)
    → castˢ (mp xs) (mp ys) (permuteˣ (PermProp.map⁺ vlab p)) ≈ˢ permuteˢ p
  permuteˢ-X {xs} Perm.refl =
    cast-id (mp xs) (mp xs)
  permuteˢ-X (Perm.prep x p) =
    ≈-trans
      (cast-⊗-frame (idˢ {vlab x ∷ []}) (mp _) (mp _)
        (permuteˣ (PermProp.map⁺ vlab p)) _ _)
      (⊗-resp ≈-refl (permuteˢ-X p))
  permuteˢ-X (Perm.swap x y p) =
    ≈-trans
      (cast-⊗-frame (σˢ (vlab x ∷ []) (vlab y ∷ [])) (mp _) (mp _)
        (permuteˣ (PermProp.map⁺ vlab p)) _ _)
      (⊗-resp ≈-refl (permuteˢ-X p))
  permuteˢ-X (Perm.trans p q) =
    ≈-trans
      (∘-cast-split (mp _) (mp _) (mp _)
        (permuteˣ (PermProp.map⁺ vlab q)) (permuteˣ (PermProp.map⁺ vlab p)))
      (∘-resp (permuteˢ-X q) (permuteˢ-X p))

--------------------------------------------------------------------------------
-- ## §1.  Per-hypergraph block factoring (strict).

module RunBlocks (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open Run H public

  ------------------------------------------------------------------------
  -- STACK factoring.  Running `ps ++ rest` from `s` leaves the same stack
  -- as running `rest` from the post-`ps` stack.  Refl-pure (same shape as
  -- the non-strict `pe-stack-++`); the per-edge term is irrelevant.

  pe-stack-++ˢ
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → proj₁ (process-edgesˢ (ps ++ rest) s)
      ≡ proj₁ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s)))
  pe-stack-++ˢ []       rest s = refl
  pe-stack-++ˢ (e ∷ ps) rest s = pe-stack-++ˢ ps rest (proj₁ (edge-stepˢ s e))

  ------------------------------------------------------------------------
  -- TERM factoring.  On the term level, the composite run is the `rest`-run
  -- precomposed with the `ps`-run, modulo a stack cast on the codomain.
  --
  -- The non-strict proof pays a `coe-cod`-transport + `assoc` per edge; in
  -- the strict world the cast is `castˢ refl (cong (map vl) …)` and the
  -- per-edge reassoc is `assocˢ`.

  coeCod
    : ∀ {d : List (Fin H.nV)} {s s' : List (Fin H.nV)} → s ≡ s'
    → HomS (map vl d) (map vl s)
    → HomS (map vl d) (map vl s')
  coeCod e = castˢ refl (cong (map vl) e)

  pe-term-++ˢ
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → proj₂ (process-edgesˢ (ps ++ rest) s)
      ≈ˢ coeCod (sym (pe-stack-++ˢ ps rest s))
           (proj₂ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s)))
             ∘ˢ proj₂ (process-edgesˢ ps s))
  pe-term-++ˢ []       rest s = ≈-sym idʳ
  pe-term-++ˢ (e ∷ ps) rest s =
    ≈-trans (∘-resp (pe-term-++ˢ ps rest s') ≈-refl)
            (coeCod-reassoc E R G t)
    where
      s' = proj₁ (edge-stepˢ s e)
      t  = proj₂ (edge-stepˢ s e)
      G  = proj₂ (process-edgesˢ ps s')
      R  = proj₂ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s')))
      E  = sym (pe-stack-++ˢ ps rest s')

      -- coeCod E (R ∘ˢ G) ∘ˢ t ≈ coeCod E (R ∘ˢ (G ∘ˢ t))
      -- (the cast slides past ∘ˢ on the codomain, then re-associate).
      coeCod-reassoc
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (R0 : HomS (map vl (proj₁ (process-edgesˢ ps s'))) (map vl a))
            (G0 : HomS (map vl s') (map vl (proj₁ (process-edgesˢ ps s'))))
            (t0 : HomS (map vl s) (map vl s'))
        → coeCod eq (R0 ∘ˢ G0) ∘ˢ t0 ≈ˢ coeCod eq (R0 ∘ˢ (G0 ∘ˢ t0))
      coeCod-reassoc refl R0 G0 t0 = assocˢ

  ------------------------------------------------------------------------
  -- RUN at an arbitrary edge list `es` equal to `gblk ++ kblk`: the run
  -- term factors into the `kblk`-run on the post-`gblk` stack precomposed
  -- with the `gblk`-run.  `range C.nE` instantiates `es` via `range-++`.

  run-split-atˢ
    : ∀ {es : List (Fin H.nE)} (gblk kblk : List (Fin H.nE))
        (eq : es ≡ gblk ++ kblk) (s : List (Fin H.nV))
    → proj₂ (process-edgesˢ es s)
      ≈ˢ coeCod (trans (sym (pe-stack-++ˢ gblk kblk s))
                       (cong (λ z → proj₁ (process-edgesˢ z s)) (sym eq)))
           (proj₂ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk s)))
             ∘ˢ proj₂ (process-edgesˢ gblk s))
  run-split-atˢ gblk kblk refl s =
      ≈-trans (pe-term-++ˢ gblk kblk s)
        (≡⇒≈ˢ (cast-irrel
                 refl refl
                 (cong (map vl) (sym (pe-stack-++ˢ gblk kblk s)))
                 (cong (map vl) (trans (sym (pe-stack-++ˢ gblk kblk s)) refl))
                 (proj₂ (process-edgesˢ kblk (proj₁ (process-edgesˢ gblk s)))
                   ∘ˢ proj₂ (process-edgesˢ gblk s))))
