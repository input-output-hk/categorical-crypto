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
  using (process-edges; edge-step; extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab; permute)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-via-injective-just; extract-prefix-via-injective-nothing)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; box-of; box-of-cong;
         edge-step-graph)

-- The eval-coincidence (injective relabel ⇒ same evaluated bijection) and
-- the `FaithfulnessResidual` keystone interface.  Both need ONLY the
-- injective + label-preserving embedding data, NOT a full iso.
open import Categories.Hypergraph.ExtractPrefixEvalPhi using (eval-coincide)
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-∘; map-cong; map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

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

--------------------------------------------------------------------------------
-- ## §5. The TERM-tracking `process-edges` extraction lemmas (the GATE).
--
-- These are the term-level twins of the STACK-level liftings in
-- `DecodeAttempt`/`DecodeAttemptLinearP` (`process-edges-↑ˡ-pure-L`,
-- `process-edges-↑ʳ-via-remap{,P}`, `process-edges-↑ˡ-on-mixed`,
-- `process-edges-↑ʳ-on-perm`).  Where the stack liftings track only
-- `proj₁` (the stack) and leave the per-edge term opaque behind an
-- existential `∃[ t ]`, these expose `proj₂` — the actual composed
-- HomTerm — as the relabel-transport of the SUB-decoder's term.
--
-- ### The embedding abstraction
--
-- All four stack liftings instantiate ONE pattern: an *injective,
-- label-preserving vertex embedding* `φ : Fin H.nV → Fin J.nV` together
-- with an edge map `ψ : Fin H.nE → Fin J.nE` whose endpoints/labels are
-- the `map φ`-image of `H`'s.  This is exactly the data of a hypergraph
-- iso (`Iso._≅ᴴ_`) MINUS surjectivity (`φ⁻¹`/`φ-rght`/`ψ⁻¹`/…), which
-- the per-edge term reduction never uses (only `φ-inj` from a left
-- inverse, `φ-lab`, `ψ-ein`/`ψ-eout`, and the atom-level `ψ-elab`).
--
--   * G-side of hCompose/hComposeP : `φ = injL`, `ψ = _↑ˡ K.nE`
--     (`vlab-injL`, `ein-c-inj₁-red`, `eout-c-inj₁-red`, `elab-c-inj₁`).
--   * K-side of hCompose/hComposeP : `φ = remap{,P}`, `ψ = G.nE ↑ʳ_`
--     (`remap-vlab`, `ein-c-inj₂-red`, …), run on a permutation-equivalent
--     stack (handled by `process-edges-term-emb` taking the stack as
--     `map φ s` literally, after the caller absorbs the `↭` via the
--     stack-level lifting).
--
-- The proof mirrors `EdgeStepNaturality` verbatim (over `EdgeStepR`),
-- but parameterised by the embedding rather than an iso.  The two
-- residual obligations of the per-edge FIRE case are:
--   * box factor — PROVEN here (`fire-mid-emb`, via `box-of-cong`);
--   * permute factor — reduced to the keystone `K` (`fire-perm-emb`,
--     via `eval-coincide` + `permute-resp-≅↭`).
--
-- `objUIP` (UIP on `ObjTerm`, available from `DecidableEquality X` via
-- `Discharge.ObjUIP.objUIP′`) is taken as a parameter exactly as in
-- `EdgeStepNaturality`.
--------------------------------------------------------------------------------

-- ≈Term / subst₂ plumbing (refl-pattern; local copies as in
-- `EdgeStepNaturality` §0).
private
  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

  just≢nothing : ∀ {a} {A : Set a} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

  just-injective-fst
    : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A} {p : B x} {q : B y}
    → just (x , p) ≡ just (y , q) → x ≡ y
  just-injective-fst refl = refl

  subst₂-HomTerm-id : ∀ {A B} (p : A ≡ B) → subst₂ HomTerm p p id ≡ id
  subst₂-HomTerm-id refl = refl

  subst₂-∘-distrib
    : ∀ {As₁ As₂ Bs₁ Bs₂ Cs₁ Cs₂ : List X}
        (p : As₁ ≡ As₂) (q : Bs₁ ≡ Bs₂) (r : Cs₁ ≡ Cs₂)
        (f : HomTerm (unflatten Bs₁) (unflatten Cs₁))
        (g : HomTerm (unflatten As₁) (unflatten Bs₁))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten r) (f ∘ g)
      ≡ subst₂ HomTerm (cong unflatten q) (cong unflatten r) f
        ∘ subst₂ HomTerm (cong unflatten p) (cong unflatten q) g
  subst₂-∘-distrib refl refl refl _ _ = refl

  subst₂-∘
    : ∀ {A A' A'' B B' B''}
        (p₁ : A ≡ A') (p₂ : A' ≡ A'') (q₁ : B ≡ B') (q₂ : B' ≡ B'')
        (f : HomTerm A B)
    → subst₂ HomTerm p₂ q₂ (subst₂ HomTerm p₁ q₁ f)
      ≡ subst₂ HomTerm (trans p₁ p₂) (trans q₁ q₂) f
  subst₂-∘ refl refl refl refl f = refl

  permute-subst₂
    : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
        (r : xs Perm.↭ ys)
    → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (permute r)
      ≡ permute (subst₂ Perm._↭_ p q r)
  permute-subst₂ refl refl r = refl

  eval-subst₂-↭
    : ∀ {a} {A : Set a} {xs xs' ys ys' : List A}
        (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
    → eval-↭ (subst₂ Perm._↭_ p q r)
      ≡ subst₂ FinBij (cong length p) (cong length q) (eval-↭ r)
  eval-subst₂-↭ refl refl r = refl

--------------------------------------------------------------------------------
-- The generic embedding-based per-edge + process-edges term-twins.

module TermEmbed
  {H J : Hypergraph FlatGen}
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (K : FaithfulnessResidual)
  (let module H = Hypergraph H)
  (let module J = Hypergraph J)
  -- Injective, label-preserving vertex embedding.
  (φ      : Fin H.nV → Fin J.nV)
  (φ-inj  : ∀ {x y} → φ x ≡ φ y → x ≡ y)
  (φ-lab  : ∀ i → J.vlab (φ i) ≡ H.vlab i)
  -- Edge map with endpoints/labels mirroring H's under `map φ`.
  (ψ      : Fin H.nE → Fin J.nE)
  (ψ-ein  : ∀ e → J.ein  (ψ e) ≡ map φ (H.ein  e))
  (ψ-eout : ∀ e → J.eout (ψ e) ≡ map φ (H.eout e))
  (atom-ein  : ∀ e → map J.vlab (J.ein  (ψ e)) ≡ map H.vlab (H.ein  e))
  (atom-eout : ∀ e → map J.vlab (J.eout (ψ e)) ≡ map H.vlab (H.eout e))
  (ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (J.elab (ψ e))
                ≡ H.elab e)
  where
  open FaithfulnessResidual K using (permute-resp-≅↭)

  -- "vertex relabel is free": map J.vlab (map φ s) ≡ map H.vlab s.
  vlab-φ : ∀ (s : List (Fin H.nV)) → map J.vlab (map φ s) ≡ map H.vlab s
  vlab-φ s = trans (sym (map-∘ s)) (map-cong φ-lab s)

  -- J-side extract-prefix results lock-step with the H-side ones.
  extract-prefix-J-nothing
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
    → extract-prefix (H.ein e) sH ≡ nothing
    → extract-prefix (J.ein (ψ e)) (map φ sH) ≡ nothing
  extract-prefix-J-nothing e sH eqH =
    subst (λ ks → extract-prefix ks (map φ sH) ≡ nothing) (sym (ψ-ein e))
          (extract-prefix-via-injective-nothing φ φ-inj (H.ein e) sH eqH)

  extract-prefix-J-just
    : ∀ (e : Fin H.nE) (sH restH : List (Fin H.nV))
        (pH : sH Perm.↭ H.ein e ++ restH)
    → extract-prefix (H.ein e) sH ≡ just (restH , pH)
    → Σ[ q ∈ map φ sH Perm.↭ J.ein (ψ e) ++ map φ restH ]
        extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (map φ restH , q)
  extract-prefix-J-just e sH restH pH eqH =
    subst (λ ks → Σ[ q ∈ map φ sH Perm.↭ ks ++ map φ restH ]
                    extract-prefix ks (map φ sH) ≡ just (map φ restH , q))
          (sym (ψ-ein e))
          (extract-prefix-via-injective-just φ φ-inj (H.ein e) sH restH pH eqH)

  -- SKIP closer (objUIP collapses the boundary loop).
  subst₂-id-≈ : ∀ {A B : ObjTerm} (p q : A ≡ B) → subst₂ HomTerm p q id ≈Term id
  subst₂-id-≈ p q =
    ≡⇒≈Term (trans (cong (λ z → subst₂ HomTerm z q id) (objUIP p q))
                   (subst₂-HomTerm-id q))

  -- FIRE box factor — PROVEN (box-of-cong + objUIP + ψ-elab).
  fire-mid-emb
    : ∀ (e : Fin H.nE)
        (restH : List (Fin H.nV)) (restJ : List (Fin J.nV))
        (restJ≡ : restJ ≡ map φ restH)
        (q : map J.vlab (J.ein  (ψ e) ++ restJ) ≡ map H.vlab (H.ein  e ++ restH))
        (r : map J.vlab (J.eout (ψ e) ++ restJ) ≡ map H.vlab (H.eout e ++ restH))
    → subst₂ HomTerm (cong unflatten q) (cong unflatten r) (fire-mid J (ψ e) restJ)
      ≈Term fire-mid H e restH
  fire-mid-emb e restH restJ restJ≡ q r = ≡⇒≈Term goal-≡
    where
      rest-lab : map J.vlab restJ ≡ map H.vlab restH
      rest-lab = trans (cong (map J.vlab) restJ≡) (vlab-φ restH)

      box-J : HomTerm (unflatten (map J.vlab (J.ein  (ψ e)) ++ map J.vlab restJ))
                      (unflatten (map J.vlab (J.eout (ψ e)) ++ map J.vlab restJ))
      box-J = box-of (map J.vlab (J.ein (ψ e))) (map J.vlab (J.eout (ψ e)))
                     (map J.vlab restJ) (J.elab (ψ e))

      aJ = cong unflatten (sym (map-++ J.vlab (J.ein  (ψ e)) restJ))
      bJ = cong unflatten (sym (map-++ J.vlab (J.eout (ψ e)) restJ))
      aH = cong unflatten (sym (map-++ H.vlab (H.ein  e) restH))
      bH = cong unflatten (sym (map-++ H.vlab (H.eout e) restH))

      goal-≡ : subst₂ HomTerm (cong unflatten q) (cong unflatten r) (fire-mid J (ψ e) restJ)
               ≡ fire-mid H e restH
      goal-≡ =
        trans (subst₂-∘ aJ (cong unflatten q) bJ (cong unflatten r) box-J)
        (trans (cong₂ (λ P Q → subst₂ HomTerm P Q box-J) (objUIP _ _) (objUIP _ _))
        (trans (sym (subst₂-∘
                      (cong unflatten (cong₂ _++_ (atom-ein e) rest-lab)) aH
                      (cong unflatten (cong₂ _++_ (atom-eout e) rest-lab)) bH
                      box-J))
               (cong (subst₂ HomTerm aH bH)
                     (box-of-cong (atom-ein e) (atom-eout e) rest-lab
                                  (J.elab (ψ e)) (H.elab e) (ψ-elab e)))))

  -- FIRE permute factor — reduced to the keystone K (eval-coincide).
  fire-perm-emb
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (restH : List (Fin H.nV)) (permH : sH Perm.↭ H.ein e ++ restH)
        (eqH : extract-prefix (H.ein e) sH ≡ just (restH , permH))
        (restJ : List (Fin J.nV)) (permJ : map φ sH Perm.↭ J.ein (ψ e) ++ restJ)
        (eqJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (restJ , permJ))
        (p : map J.vlab (map φ sH) ≡ map H.vlab sH)
        (q : map J.vlab (J.ein (ψ e) ++ restJ) ≡ map H.vlab (H.ein e ++ restH))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (permute-via-vlab J.vlab permJ)
      ≈Term permute-via-vlab H.vlab permH
  fire-perm-emb e sH restH permH eqH restJ permJ eqJ p q =
    helper restJ permJ eqJ q
      (just-injective-fst
        (trans (sym eqJ) (proj₂ (extract-prefix-J-just e sH restH permH eqH))))
    where
      helper
        : (rJ : List (Fin J.nV))
          (pJ : map φ sH Perm.↭ J.ein (ψ e) ++ rJ)
          (eJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (rJ , pJ))
          (qq : map J.vlab (J.ein (ψ e) ++ rJ) ≡ map H.vlab (H.ein e ++ restH))
        → rJ ≡ map φ restH
        → subst₂ HomTerm (cong unflatten p) (cong unflatten qq)
            (permute-via-vlab J.vlab pJ)
          ≈Term permute-via-vlab H.vlab permH
      helper .(map φ restH) pJ eJ qq refl rewrite ψ-ein e =
        ≈-Term-trans
          (≡⇒≈Term (permute-subst₂ p qq (PermProp.map⁺ J.vlab pJ)))
          (permute-resp-≅↭
            (subst₂ Perm._↭_ p qq (PermProp.map⁺ J.vlab pJ))
            (PermProp.map⁺ H.vlab permH)
            ≅↭ev)
        where
          ≅↭ev : eval-↭ (subst₂ Perm._↭_ p qq (PermProp.map⁺ J.vlab pJ))
               ≈-fb eval-↭ (PermProp.map⁺ H.vlab permH)
          ≅↭ev rewrite eval-subst₂-↭ p qq (PermProp.map⁺ J.vlab pJ) =
            eval-coincide φ φ-inj J.vlab H.vlab φ-lab
              (H.ein e) sH restH permH pJ p qq eqH eJ

  -- FIRE/FIRE assembled.
  edge-step-fire-emb
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        (restH : List (Fin H.nV)) (permH : sH Perm.↭ H.ein e ++ restH)
        (eqH : extract-prefix (H.ein e) sH ≡ just (restH , permH))
        (restJ : List (Fin J.nV)) (permJ : map φ sH Perm.↭ J.ein (ψ e) ++ restJ)
        (eqJ : extract-prefix (J.ein (ψ e)) (map φ sH) ≡ just (restJ , permJ))
        (stk : J.eout (ψ e) ++ restJ ≡ map φ (H.eout e ++ restH))
    → subst₂ HomTerm
        (cong unflatten (vlab-φ sH))
        (cong unflatten (trans (cong (map J.vlab) stk) (vlab-φ (H.eout e ++ restH))))
        (fire-term J (ψ e) (map φ sH) restJ permJ)
      ≈Term fire-term H e sH restH permH
  edge-step-fire-emb e sH restH permH eqH restJ permJ eqJ stk =
    ≈-Term-trans
      (≡⇒≈Term (subst₂-∘-distrib pDom pMidBox rPath
                  (fire-mid J (ψ e) restJ) (permute-via-vlab J.vlab permJ)))
      (∘-resp-≈ (fire-mid-emb e restH restJ restJ≡ pMidBox rPath)
                (fire-perm-emb e sH restH permH eqH restJ permJ eqJ pDom pMidBox))
    where
      pDom : map J.vlab (map φ sH) ≡ map H.vlab sH
      pDom = vlab-φ sH
      restJ≡ : restJ ≡ map φ restH
      restJ≡ = just-injective-fst
                 (trans (sym eqJ) (proj₂ (extract-prefix-J-just e sH restH permH eqH)))
      pMidBox : map J.vlab (J.ein (ψ e) ++ restJ) ≡ map H.vlab (H.ein e ++ restH)
      pMidBox = trans (cong (map J.vlab)
                        (trans (cong₂ _++_ (ψ-ein e) restJ≡)
                               (sym (map-++ φ (H.ein e) restH))))
                      (vlab-φ (H.ein e ++ restH))
      rPath : map J.vlab (J.eout (ψ e) ++ restJ) ≡ map H.vlab (H.eout e ++ restH)
      rPath = trans (cong (map J.vlab) stk) (vlab-φ (H.eout e ++ restH))

  -- Per-edge term-twin, over the `EdgeStepR` witnesses.
  edge-step-term-emb
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
        {s'H : List (Fin H.nV)}
        {tH : HomTerm (unflatten (map H.vlab sH)) (unflatten (map H.vlab s'H))}
        {s'J : List (Fin J.nV)}
        {tJ : HomTerm (unflatten (map J.vlab (map φ sH))) (unflatten (map J.vlab s'J))}
        (wH : EdgeStepR H sH e s'H tH)
        (wJ : EdgeStepR J (map φ sH) (ψ e) s'J tJ)
        (stk : s'J ≡ map φ s'H)
    → subst₂ HomTerm
        (cong unflatten (vlab-φ sH))
        (cong unflatten (trans (cong (map J.vlab) stk) (vlab-φ s'H)))
        tJ
      ≈Term tH
  edge-step-term-emb e sH (skipR eqH) (skipR eqJ) stk =
    subst₂-id-≈ (cong unflatten (vlab-φ sH))
                (cong unflatten (trans (cong (map J.vlab) stk) (vlab-φ sH)))
  edge-step-term-emb e sH (skipR eqH) (fireR restJ permJ eqJ) stk =
    ⊥-elim (just≢nothing (trans (sym eqJ) (extract-prefix-J-nothing e sH eqH)))
  edge-step-term-emb e sH (fireR restH permH eqH) (skipR eqJ) stk =
    ⊥-elim (just≢nothing
      (trans (sym (proj₂ (extract-prefix-J-just e sH restH permH eqH))) eqJ))
  edge-step-term-emb e sH (fireR restH permH eqH) (fireR restJ permJ eqJ) stk =
    edge-step-fire-emb e sH restH permH eqH restJ permJ eqJ stk

  --------------------------------------------------------------------
  -- Per-edge STACK agreement, derived from the relation (lock-step).
  -- (The existing STACK liftings prove this for the concrete G/K cases;
  -- here it falls out of `edge-step-term-emb`'s case split for free.)

  edge-step-stack-emb
    : ∀ (e : Fin H.nE) (sH : List (Fin H.nV))
    → proj₁ (edge-step J (map φ sH) (ψ e))
      ≡ map φ (proj₁ (edge-step H sH e))
  edge-step-stack-emb e sH = aux (edge-step-graph H sH e) (edge-step-graph J (map φ sH) (ψ e))
    where
      aux : ∀ {s'H tH s'J tJ}
          → EdgeStepR H sH e s'H tH
          → EdgeStepR J (map φ sH) (ψ e) s'J tJ
          → s'J ≡ map φ s'H
      aux (skipR _) (skipR _) = refl
      aux (skipR eqH) (fireR restJ permJ eqJ) =
        ⊥-elim (just≢nothing (trans (sym eqJ) (extract-prefix-J-nothing e sH eqH)))
      aux (fireR restH permH eqH) (skipR eqJ) =
        ⊥-elim (just≢nothing
          (trans (sym (proj₂ (extract-prefix-J-just e sH restH permH eqH))) eqJ))
      aux (fireR restH permH eqH) (fireR restJ permJ eqJ) =
        trans (cong (J.eout (ψ e) ++_)
                 (just-injective-fst
                   (trans (sym eqJ) (proj₂ (extract-prefix-J-just e sH restH permH eqH)))))
              (trans (cong (_++ map φ restH) (ψ-eout e))
                     (sym (map-++ φ (H.eout e) restH)))

  --------------------------------------------------------------------
  -- The ITERATED `process-edges` term-twin (the GATE).
  --
  --   subst₂ HomTerm (vlab-φ sH) (vlab-φ (proc-stack es sH))
  --     (proj₂ (process-edges J (map ψ es) (map φ sH)))
  --   ≈Term proj₂ (process-edges H es sH)
  --
  -- modulo the stack agreement `proc-stack-emb` (J-side stack is the
  -- `map φ`-image of H's).  This exposes the J-side composed term as the
  -- relabel-transport of the H-side composed term — exactly the
  -- `decode-attempt` block-decomposition the shape residuals consume.

  -- J-side stack agreement, iterated.
  proc-stack-emb
    : ∀ (es : List (Fin H.nE)) (sH : List (Fin H.nV))
    → proj₁ (process-edges J (map ψ es) (map φ sH))
      ≡ map φ (proj₁ (process-edges H es sH))
  proc-stack-emb []       sH = refl
  proc-stack-emb (e ∷ es) sH
      with edge-step-graph H sH e
         | edge-step-stack-emb e sH
  ... | _ | stepEq
      rewrite stepEq = proc-stack-emb es (proj₁ (edge-step H sH e))

  -- Boundary-transport helper for the term recursion: a `subst₂` whose
  -- codomain factors through the stack agreement at the head step.
  private
    coe-cod-φ
      : ∀ {dH : List (Fin H.nV)} {sH sH' : List (Fin H.nV)} (eq : sH ≡ sH')
      → HomTerm (unflatten (map H.vlab dH)) (unflatten (map H.vlab sH))
      → HomTerm (unflatten (map H.vlab dH)) (unflatten (map H.vlab sH'))
    coe-cod-φ {dH} eq = subst (λ z → HomTerm (unflatten (map H.vlab dH))
                                              (unflatten (map H.vlab z)))
                             eq

  -- The iterated term-twin, GENERALISED over the J-start stack `sJ`
  -- (with `sJ ≡ map φ sH`) so the head-step's post-stack equality
  -- (`edge-step-stack-emb`) threads cleanly into the recursion — and
  -- the two `subst₂`s recombine over `∘` (`subst₂-∘-distrib`).
  --
  -- Both boundary equalities are taken as ARBITRARY list-equations
  -- `pDom`/`pCod`; `subst₂-id-≈`/`objUIP` collapse the (necessarily
  -- equal-endpoint) loops, so the conclusion is independent of which
  -- equality proofs are supplied — this is what makes the recursion
  -- well-typed without pinning the proc-stack equation by `with`.
  process-edges-term-emb-gen
    : ∀ (es : List (Fin H.nE)) (sH : List (Fin H.nV))
        (sJ : List (Fin J.nV)) (sJ≡ : sJ ≡ map φ sH)
        (pDom : map J.vlab sJ ≡ map H.vlab sH)
        (pCod : map J.vlab (proj₁ (process-edges J (map ψ es) sJ))
              ≡ map H.vlab (proj₁ (process-edges H es sH)))
    → subst₂ HomTerm (cong unflatten pDom) (cong unflatten pCod)
        (proj₂ (process-edges J (map ψ es) sJ))
      ≈Term proj₂ (process-edges H es sH)
  process-edges-term-emb-gen [] sH sJ sJ≡ pDom pCod =
    subst₂-id-≈ (cong unflatten pDom) (cong unflatten pCod)
  process-edges-term-emb-gen (e ∷ es) sH sJ refl pDom pCod = goal
    where
      s'H  = proj₁ (edge-step H sH e)
      s'J  = proj₁ (edge-step J (map φ sH) (ψ e))

      -- Head step's post-stack agreement + the mid boundary equality.
      stepStk : s'J ≡ map φ s'H
      stepStk = edge-step-stack-emb e sH
      pMid : map J.vlab s'J ≡ map H.vlab s'H
      pMid = trans (cong (map J.vlab) stepStk) (vlab-φ s'H)

      -- Head-step term twin: read off `edge-step-term-emb` (over the
      -- relation witnesses), then bridge its fixed `vlab-φ sH`/`pMid`
      -- transports to the supplied `pDom`/`pMid` via `objUIP`.
      headTwin
        : subst₂ HomTerm (cong unflatten pDom) (cong unflatten pMid)
            (proj₂ (edge-step J (map φ sH) (ψ e)))
          ≈Term proj₂ (edge-step H sH e)
      headTwin =
        ≈-Term-trans
          (≡⇒≈Term
            (cong (λ z → subst₂ HomTerm z (cong unflatten pMid)
                           (proj₂ (edge-step J (map φ sH) (ψ e))))
                  (objUIP (cong unflatten pDom) (cong unflatten (vlab-φ sH)))))
          (edge-step-term-emb e sH
            (edge-step-graph H sH e) (edge-step-graph J (map φ sH) (ψ e)) stepStk)

      -- Recursion term twin, run from the post-head J stack `s'J`.
      recTwin
        : subst₂ HomTerm (cong unflatten pMid) (cong unflatten pCod)
            (proj₂ (process-edges J (map ψ es) s'J))
          ≈Term proj₂ (process-edges H es s'H)
      recTwin =
        process-edges-term-emb-gen es s'H s'J stepStk pMid pCod

      goal
        : subst₂ HomTerm (cong unflatten pDom) (cong unflatten pCod)
            (proj₂ (process-edges J (map ψ es) s'J)
             ∘ proj₂ (edge-step J (map φ sH) (ψ e)))
          ≈Term proj₂ (process-edges H es s'H) ∘ proj₂ (edge-step H sH e)
      goal =
        ≈-Term-trans
          (≡⇒≈Term
            (subst₂-∘-distrib pDom pMid pCod
              (proj₂ (process-edges J (map ψ es) s'J))
              (proj₂ (edge-step J (map φ sH) (ψ e)))))
          (∘-resp-≈ recTwin headTwin)

  -- The headline iterated term-twin, at the canonical `sJ = map φ sH`.
  process-edges-term-emb
    : ∀ (es : List (Fin H.nE)) (sH : List (Fin H.nV))
    → subst₂ HomTerm
        (cong unflatten (vlab-φ sH))
        (cong unflatten
          (trans (cong (map J.vlab) (proc-stack-emb es sH))
                 (vlab-φ (proj₁ (process-edges H es sH)))))
        (proj₂ (process-edges J (map ψ es) (map φ sH)))
      ≈Term proj₂ (process-edges H es sH)
  process-edges-term-emb es sH =
    process-edges-term-emb-gen es sH (map φ sH) refl (vlab-φ sH)
      (trans (cong (map J.vlab) (proc-stack-emb es sH))
             (vlab-φ (proj₁ (process-edges H es sH))))
