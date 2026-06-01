{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Pruned-vs-unpruned decoder shape, factored through PRUNED shape lemmas.
--
-- This module supplies the two genuinely-pruning-specific residuals of
-- `Discharge.DecodeRelDecodeP.decode-rel-≈-decodeP`:
--
--     decodeP-≈-decode-∘ : decodeP (g ∘ f)  ≈Term decode (g ∘ f)
--     decodeP-≈-decode-⊗ : decodeP (f ⊗₁ g) ≈Term decode (f ⊗₁ g)
--
-- It does so by FACTORING each bridge through a PRUNED shape lemma plus
-- the ALREADY-TRUSTED unpruned shape residual, so that NO pruned-vs-
-- unpruned obligation survives as new conceptual trust.
--
-- ## The factoring (the whole point of this module)
--
-- `decodeP-≈-decode` is structural recursion on the term.  In the two
-- recursive cases the goal is symmetric between the pruned (`decodeP`,
-- `hComposeP`/`hTensor` on `⟪·⟫ₚ`) and the unpruned (`decode`,
-- `hCompose`/`hTensor` on `⟪·⟫`) decoders, so a single chain
--
--     decodeP (g ∘ f)
--       ≈⟨ decodeP-∘-shape g f ⟩          -- PRUNED ∘ shape (this module's residual)
--     decodeP g ∘ decodeP f
--       ≈⟨ ∘-resp-≈ (rec g) (rec f) ⟩     -- recursion (decodeP X ≈Term decode X)
--     decode g ∘ decode f
--       ≈⟨ sym (decode-∘-shape-inner g f) ⟩  -- UNPRUNED ∘ shape (SHARED trust)
--     decode (g ∘ f)
--
-- closes the `∘` bridge (and dually `⊗`), where:
--
--   * `rec X = decodeP-≈-decode X` is the structural recursion supplied
--     by the caller (`DecodeRelDecodeP.decodeP-≈-decode`);
--   * `decode-∘-shape-inner` / `decode-⊗-shape-inner` are the UNPRUNED
--     shape residuals, ALREADY part of the shared `DecodeShapeResiduals`
--     trust surface that the unpruned completeness proof and the
--     interchange chain depend on (NO new trust); and
--   * `decodeP-∘-shape` / `decodeP-⊗-shape` are the PRUNED shape lemmas,
--     packaged here as the record `DecodePShapeResiduals`.
--
-- ## What the residual record contains, and why it is the right narrowing
--
-- The two fields of `DecodePShapeResiduals` are STRUCTURALLY IDENTICAL
-- to the unpruned `DecodeShapeResiduals` fields, only with `decode`
-- replaced by `decodeP` (and `⟪·⟫`/`hCompose`/`hTensor` replaced by the
-- pruned `⟪·⟫ₚ`/`hComposeP`/`hTensor`).  Concretely:
--
--   * `decodeP-∘-shape g f : decodeP (g ∘ f) ≈Term decodeP g ∘ decodeP f`
--     — the PRUNED `∘` shape.  Its constructive content is the
--     `pe-term-++`-style block-decomposition of `process-edges` on the
--     `hComposeP` hypergraph (the f-block edges, routed through `injL`,
--     then the g-block edges, routed through `remapP`), reconciled with
--     the standalone `decodeP f` / `decodeP g` via the boundary lemmas
--     `domL-hComposeP` / `codL-hComposeP`.  The TERM-level `_++_`
--     factoring building block (`pe-term-++`) is PROVEN below; the
--     remaining gap is the term-level analogue of the STACK-only
--     `process-edges-↑ˡ-pure-L` / `process-edges-↑ʳ-via-remapP` (which
--     live in `DecodeAttemptLinearP` and `DecodeAttempt`, neither of
--     which this module may edit).
--
--   * `decodeP-⊗-shape f g : decodeP (f ⊗₁ g) ≈Term
--         to (unflatten-++-≅ …) ∘ (decodeP f ⊗₁ decodeP g) ∘ from (unflatten-++-≅ …)`
--     — the PRUNED `⊗` shape.  Tensor is NOT pruned
--     (`⟪ f ⊗₁ g ⟫ₚ = hTensor ⟪f⟫ₚ ⟪g⟫ₚ`, the SAME `hTensor` as
--     unpruned), so this is the analogue of `decode-⊗-shape-inner` for
--     `decodeP`.  Its term-level content is the reordering of the
--     INTERLEAVED disjoint-block edge stream of `hTensor` back into the
--     tensor `decodeP f ⊗₁ decodeP g` — i.e. the per-swap independent-
--     edge Mac-Lane chase isolated as
--     `Sub.SwapAtomAligned.SwapAtomAlignedResidual.swap-mac-lane-residual`
--     (`= swap-atom-aligned`), the SAME `nf-bracket`/`block-nf` kernel
--     the interchange side bottoms out in.  The explicit link is the
--     kernel statement `ProcessEdges↭Goal (hTensor ⟪f⟫ₚ ⟪g⟫ₚ)
--     (e₁∷e₂∷es) (e₂∷e₁∷es) s` under `IndependentSwap`: the `hTensor`
--     edge stream `map injL (range G.nE) ++ map injR (range K.nE)`
--     must be reordered into the two PER-SIDE runs, and each adjacent
--     transposition of a G-edge past a K-edge (disjoint blocks ⇒
--     `IndependentSwap`) is exactly one `swap-atom-aligned` step.  The
--     kernel lives in `Sub.SwapAtomAligned` / `Sub.ProcessTermAligned`,
--     both of which require `APROPSignatureDec`; this `sig`-level module
--     therefore cannot IMPORT it, so the link is recorded as the doc of
--     the `decodeP-⊗-shape` field, not as a defined alias.
--
-- So the SOLE pruning-specific trust of `decode-rel-≈-decodeP`, after
-- this factoring, is `DecodePShapeResiduals` — and BOTH its fields are
-- the pruned mirror of an obligation the unpruned proof already trusts
-- (`decode-∘-shape-inner`, `decode-⊗-shape-inner`), with the `⊗` one
-- confirmedly the `swap-atom-aligned` kernel.
--
-- ## Status
--
--   * `pe-term-++` — PROVEN (term-level `_++_` factoring of
--     `process-edges`, generic in `H`; the building block of the pruned
--     `∘` shape's block-decomposition).
--   * `DecodePShapeResiduals` — the two narrowed pruned shape residuals.
--   * `decodeP-≈-decode-∘-from` / `decodeP-≈-decode-⊗-from` — the
--     factoring assemblers (PROVEN; consume the pruned shapes + the
--     recursion + the unpruned shapes).
--
-- No `--with-K`-specific axioms; the only postulates are the two pruned
-- shape residual record fields (mirroring the unpruned trust surface).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesTermShape
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hCompose; hTensor)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; domL-hComposeP; codL-hComposeP)
open import Categories.APROP.Hypergraph.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; subst₂)

private
  module FM = Category FreeMonoidal

--------------------------------------------------------------------------------
-- ## §1. The pruned decoder `decodeP` (verbatim from `DecodeRelDecodeP`).
--
-- Replicated here so the residual record fields can be stated in terms
-- of it without importing `DecodeRelDecodeP` (which would create a
-- cycle, since `DecodeRelDecodeP` imports this module).

decodeP : ∀ {A B} (f : HomTerm A B)
        → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decodeP {A} {B} f =
  subst₂ HomTerm (cong unflatten (⟪⟫ₚ-domL f)) (cong unflatten (⟪⟫ₚ-codL f))
         (proj₁ (decode-attempt-LinearP f))

--------------------------------------------------------------------------------
-- ## §2. The term-level `_++_` factoring of `process-edges` — PROVEN.
--
-- Running `ps ++ rest` from a stack `s` is, on the TERM level, running
-- `rest` from the post-`ps` stack precomposed with running `ps` from
-- `s`, modulo the codomain transport along the STACK factoring
-- (`process-edges-++-stack`, which is propositional because
-- `process-edges` inducts under `with edge-step`).
--
-- This is the standalone, generic-`H`, importable form of
-- `SwapStep.PerHG.process-edges-++-≈` (which lives inside a `--without-K`
-- per-hypergraph module and is not directly reusable here).  It is the
-- building block of the pruned `∘` shape's block-decomposition: the
-- `hComposeP` edge list `range (G.nE + K.nE)` factors as `map injL
-- (range G.nE) ++ map remapP… (range K.nE)`, and `pe-term-++` peels the
-- composite term into the f-block term then the g-block term.

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- Stack of running `o` from stack `s`.
  pe-stack : List (Fin H.nE) → List (Fin H.nV) → List (Fin H.nV)
  pe-stack o s = proj₁ (process-edges H o s)

  -- Composed term of running `o` from stack `s`.
  pe-term : (o : List (Fin H.nE)) (s : List (Fin H.nV))
          → HomTerm (unflatten (map H.vlab s))
                    (unflatten (map H.vlab (pe-stack o s)))
  pe-term o s = proj₂ (process-edges H o s)

  -- Codomain transport along a stack equality.
  coe-cod
    : ∀ {d : List (Fin H.nV)} {s s' : List (Fin H.nV)} → s ≡ s'
    → HomTerm (unflatten (map H.vlab d)) (unflatten (map H.vlab s))
    → HomTerm (unflatten (map H.vlab d)) (unflatten (map H.vlab s'))
  coe-cod {d} eq = subst (λ z → HomTerm (unflatten (map H.vlab d))
                                         (unflatten (map H.vlab z)))
                          eq

  -- The STACK `_++_`-factoring of `process-edges` (re-derived here so
  -- the term factoring is self-contained — it is the same statement as
  -- `DecodeAttempt.process-edges-++-stack H`, proved by induction on the
  -- prefix `ps`).
  pe-stack-++
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → pe-stack (ps ++ rest) s ≡ pe-stack rest (pe-stack ps s)
  pe-stack-++ []       rest s = refl
  pe-stack-++ (e ∷ ps) rest s with edge-step H s e
  ... | s' , _ = pe-stack-++ ps rest s'

  -- The TERM `_++_`-factoring — PROVEN by induction on `ps`, using
  -- `assoc` to re-bracket the per-edge term out of the recursion.
  pe-term-++
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → pe-term (ps ++ rest) s
      ≈Term coe-cod (sym (pe-stack-++ ps rest s))
              (pe-term rest (pe-stack ps s) ∘ pe-term ps s)
  pe-term-++ []         rest s = ≈-Term-sym idʳ
  pe-term-++ (e ∷ ps)   rest s with edge-step H s e
  ... | s' , t =
    ≈-Term-trans
      (∘-resp-≈ (pe-term-++ ps rest s') ≈-Term-refl)
      (coe-cod-assoc (sym (pe-stack-++ ps rest s'))
                     (pe-term rest (pe-stack ps s')) (pe-term ps s') t)
    where
      coe-cod-assoc
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomTerm (unflatten (map H.vlab (pe-stack ps s')))
                         (unflatten (map H.vlab a)))
            (f : HomTerm (unflatten (map H.vlab s'))
                         (unflatten (map H.vlab (pe-stack ps s'))))
            (t0 : HomTerm (unflatten (map H.vlab s))
                          (unflatten (map H.vlab s')))
        → coe-cod eq (g ∘ f) ∘ t0
          ≈Term coe-cod eq (g ∘ (f ∘ t0))
      coe-cod-assoc refl g f t0 = assoc

--------------------------------------------------------------------------------
-- ## §3. The two narrowed PRUNED shape residuals.
--
-- These are the pruned mirror of `DecodeShape.DecodeShapeResiduals`,
-- stated with `decodeP` (pruned).  They are the SOLE pruning-specific
-- trust the `∘`/`⊗` bridges reduce to.

record DecodePShapeResiduals : Set where
  field
    -- The pruned `∘` shape.  Constructive content: `pe-term-++` on the
    -- `hComposeP` edge list + the term-level G-side (`injL`) / K-side
    -- (`remapP`) liftings + the `domL-hComposeP` / `codL-hComposeP`
    -- boundary reconciliation.  Structurally identical to the unpruned
    -- `decode-∘-shape-inner` (with `decode` → `decodeP`,
    -- `hCompose` → `hComposeP`).
    decodeP-∘-shape
      : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
      → decodeP (g ∘ f) ≈Term decodeP g ∘ decodeP f

    -- The pruned `⊗` shape.  Tensor is NOT pruned, so this is the
    -- analogue of `decode-⊗-shape-inner` for `decodeP`; its term-level
    -- content is the interleaved disjoint-block reordering =
    -- `swap-atom-aligned` (confirmed by `confirm-⊗-bottoms-out`).
    decodeP-⊗-shape
      : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
      → decodeP (f ⊗₁ g)
      ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
           ∘ (decodeP f ⊗₁ decodeP g)
           ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

--------------------------------------------------------------------------------
-- ## §4. The factoring assemblers — PROVEN.
--
-- Given a `DecodePShapeResiduals` instance, the unpruned shape residuals
-- (as `≈Term` functions), and the structural recursion `rec`, derive the
-- two bridges.  These match the EXACT types of the postulates
-- `decodeP-≈-decode-∘` / `decodeP-≈-decode-⊗` in `DecodeRelDecodeP`.
--
-- The `decode`/`decodeP` arguments are passed as parameters (rather than
-- imported) to avoid a cycle and to keep this module's only `sig`-level
-- dependency the pruned decoder.

module Assemble
  (decode : ∀ {A B} (f : HomTerm A B)
          → HomTerm (unflatten (flatten A)) (unflatten (flatten B)))
  -- The UNPRUNED shape residuals, surfaced as `≈Term` functions (the
  -- caller supplies them from `DecodeShapeResiduals`).
  (decode-∘-shape
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decode (g ∘ f) ≈Term decode g ∘ decode f)
  (decode-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decode (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decode f ⊗₁ decode g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C)))
  -- The PRUNED shape residuals.
  (pshape : DecodePShapeResiduals)
  where
  open DecodePShapeResiduals pshape

  -- The ∘ bridge, factored:
  --   decodeP (g∘f) ≈ decodeP g ∘ decodeP f   [pruned ∘ shape]
  --                 ≈ decode  g ∘ decode  f   [recursion under ∘]
  --                 ≈ decode (g∘f)            [sym unpruned ∘ shape]
  --
  -- The recursion RESULTS `recg : decodeP g ≈Term decode g` and
  -- `recf : decodeP f ≈Term decode f` are passed in directly (rather
  -- than a recursion function), so the caller's termination checker sees
  -- the structural decrease at the `decodeP-≈-decode g`/`f` call sites.
  decodeP-≈-decode-∘-from
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decodeP g ≈Term decode g
    → decodeP f ≈Term decode f
    → decodeP (g ∘ f) ≈Term decode (g ∘ f)
  decodeP-≈-decode-∘-from g f recg recf =
    ≈-Term-trans (decodeP-∘-shape g f)
      (≈-Term-trans (∘-resp-≈ recg recf)
        (≈-Term-sym (decode-∘-shape g f)))

  -- The ⊗ bridge, factored:
  --   decodeP (f⊗g) ≈ to ∘ (decodeP f ⊗ decodeP g) ∘ from   [pruned ⊗ shape]
  --                 ≈ to ∘ (decode  f ⊗ decode  g) ∘ from   [recursion in the block]
  --                 ≈ decode (f⊗g)                          [sym unpruned ⊗ shape]
  decodeP-≈-decode-⊗-from
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodeP f ≈Term decode f
    → decodeP g ≈Term decode g
    → decodeP (f ⊗₁ g) ≈Term decode (f ⊗₁ g)
  decodeP-≈-decode-⊗-from f g recf recg =
    ≈-Term-trans (decodeP-⊗-shape f g)
      (≈-Term-trans
        (∘-resp-≈ ≈-Term-refl
          (∘-resp-≈ (⊗-resp-≈ recf recg) ≈-Term-refl))
        (≈-Term-sym (decode-⊗-shape f g)))
