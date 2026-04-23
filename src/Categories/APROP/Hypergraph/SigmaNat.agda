{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- σ-naturality: `σ∘[f⊗g]≈[g⊗f]∘σ-sound`.
--
-- LHS = hComposeP (hTensor F G) (hSwap B D)
-- RHS = hComposeP (hSwap A C) (hTensor G F)
--
-- Both sides have vertex count F.nV + G.nV and edge count F.nE + G.nE.
-- The iso's φ / ψ are swap permutations on those spaces.
--
-- Current constructive status:
--
-- Edge bijection (4/4 COMPLETE):
--   * ψ, ψ⁻¹, ψ-left, ψ-rght  — proved via `ψ-swap` +
--     `ψ-swap-involutive`.  Both sides' pruned K blocks contribute 0
--     edges (hSwap has no edges), so edge bookkeeping reduces to a
--     swap on `Fin (F.nE + G.nE)`.
--
-- Vertex bijection (2/4 COMPLETE, 2/4 partial):
--   * φ, φ⁻¹  — concrete formulas: φ uses `hRHS.remapP ∘ ψ-swap`
--     on the F+G half; φ⁻¹ case-splits on `splitAt RHS-G.nV` then
--     `splitAt nA` for boundary, or `lookup (nonMem RHS-K.dom)` for
--     the pruned side, all composed with ψ-swap back and embedded.
--   * φ-left  — PROVED on the interior branch via `remap-inj₂`,
--     `classify-inj₂-lookup`, and `ψ-swap-involutive`.  BOUNDARY
--     branch is postulated as `φ-left-bdy`.
--   * φ-rght  — PROVED on the interior branch analogously using
--     `classify-lookup-nonMem`.  BOUNDARY branch is postulated as
--     `φ-rght-bdy`.
--
-- The boundary cases (φ-left-bdy, φ-rght-bdy) each require specific
-- classify↔lookup-cod bridges tying F/G boundary positions to RHS-G's
-- cod (a mirror of σ∘σ-proof's `lookup-cod-inject+-nA` / `-raise-nB`
-- lemmas but routed through the swap permutation).
--
-- 5 structural field postulates (φ-lab, ψ-ein, ψ-eout, φ-dom, φ-cod)
-- and 3 edge-label field postulates (atom-ein, atom-eout, ψ-elab)
-- remain, bridging concrete φ/ψ to the `_≅ᴴ_` record fields.
--
-- Because this file contains internal postulates, it is not `--safe`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SigmaNat (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hTensor; hSwap; hId; range;
         map-via-inj; map-via-raise;
         module hTensor-impl)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.Invariant sig
  using (hSwap-count-non-dom; hSwap-dom-Unique; hSwap-cod-covers; hSwap-dom-covers)
open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique)
open import Categories.APROP.Hypergraph.Prune
  using (count-non; AllIn; AllIn→count-non-zero;
         nonMem; classify; classify-lookup-Unique;
         classify-inj₁-lookup; classify-inj₂-lookup;
         classify-lookup-nonMem;
         remap; remap-inj₁; remap-inj₂)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; splitAt; cast; _↑ˡ_; _↑ʳ_; toℕ)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ;
                                        splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ;
                                        cast-is-id; cast-trans)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (length-map; map-++; map-∘; map-cong; map-id)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- σ-nat at the Hypergraph level, parametric in F, G.

module σ-nat-proof
  {A B C D : ObjTerm}
  (F : Hypergraph FlatGen (flatten A) (flatten B))
  (F-dom-U : Unique (Hypergraph.dom F))
  (G : Hypergraph FlatGen (flatten C) (flatten D))
  (G-dom-U : Unique (Hypergraph.dom G))
  where

  private
    nA = length (flatten A)
    nB = length (flatten B)
    nC = length (flatten C)
    nD = length (flatten D)

    LHS-G : Hypergraph FlatGen (flatten A ++ flatten C) (flatten B ++ flatten D)
    LHS-G = hTensor F G

    LHS-K : Hypergraph FlatGen (flatten B ++ flatten D) (flatten D ++ flatten B)
    LHS-K = hSwap B D

    LHS : Hypergraph FlatGen (flatten A ++ flatten C) (flatten D ++ flatten B)
    LHS = hComposeP LHS-G LHS-K

    RHS-G : Hypergraph FlatGen (flatten A ++ flatten C) (flatten C ++ flatten A)
    RHS-G = hSwap A C

    RHS-K : Hypergraph FlatGen (flatten C ++ flatten A) (flatten D ++ flatten B)
    RHS-K = hTensor G F

    RHS : Hypergraph FlatGen (flatten A ++ flatten C) (flatten D ++ flatten B)
    RHS = hComposeP RHS-G RHS-K

    module F = Hypergraph F
    module G = Hypergraph G
    module LHS = Hypergraph LHS
    module LHS-G = Hypergraph LHS-G
    module LHS-K = Hypergraph LHS-K
    module RHS = Hypergraph RHS
    module RHS-G = Hypergraph RHS-G
    module RHS-K = Hypergraph RHS-K

    module hLHS = hComposeP-impl LHS-G LHS-K
    module hRHS = hComposeP-impl RHS-G RHS-K
    module hTL  = hTensor-impl  F G       -- LHS-G = hTensor F G
    module hTR  = hTensor-impl  G F       -- RHS-K = hTensor G F

  --------------------------------------------------------------------------
  -- Structural identities.

  cn-LHS-K≡0 : count-non LHS-K.dom ≡ 0
  cn-LHS-K≡0 = hSwap-count-non-dom B D

  cn-RHS-G≡0 : count-non RHS-G.dom ≡ 0
  cn-RHS-G≡0 = hSwap-count-non-dom A C

  LHS-K-nE≡0 : LHS-K.nE ≡ 0
  LHS-K-nE≡0 = refl

  RHS-G-nE≡0 : RHS-G.nE ≡ 0
  RHS-G-nE≡0 = refl

  private
    -- `Fin 0` absurd helpers.
    Fin-zero-absurd : ∀ {n} → n ≡ 0 → Fin n → ⊥
    Fin-zero-absurd refl ()

    -- Boundary-length equations: `length F.dom ≡ nA` from F.dom-ok and
    -- the fact that `map vlab F.dom ≡ flatten A` has equal lengths.
    F-dom-len : length F.dom ≡ nA
    F-dom-len = trans (sym (length-map F.vlab F.dom)) (cong length F.dom-ok)

    G-dom-len : length G.dom ≡ nC
    G-dom-len = trans (sym (length-map G.vlab G.dom)) (cong length G.dom-ok)

  --------------------------------------------------------------------------
  -- Natural swap bijection on Fin (m + n) ↔ Fin (n + m).  Used for both
  -- edge and vertex bijections below.

  ψ-swap : ∀ {m n} → Fin (m + n) → Fin (n + m)
  ψ-swap {m} {n} e with splitAt m e
  ... | inj₁ eL = n ↑ʳ eL
  ... | inj₂ eR = eR ↑ˡ m

  -- ψ-swap is self-inverse: `ψ-swap {n} {m} ∘ ψ-swap {m} {n} ≡ id`.
  ψ-swap-involutive : ∀ {m n} (e : Fin (m + n))
                    → ψ-swap {n} {m} (ψ-swap {m} {n} e) ≡ e
  ψ-swap-involutive {m} {n} e with splitAt m e in eq
  ... | inj₁ eL rewrite splitAt-↑ʳ n m eL = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eR rewrite splitAt-↑ˡ n eR m = splitAt⁻¹-↑ʳ eq

  --------------------------------------------------------------------------
  -- Vertex bijection.
  --
  -- LHS.nV = LHS-G.nV + count-non LHS-K.dom = (F.nV + G.nV) + 0
  --   (count-non LHS-K.dom ≡ 0 because hSwap's dom covers all vertices).
  -- RHS.nV = RHS-G.nV + count-non RHS-K.dom = (nA + nC) + count-non (hTensor G F).dom.
  --
  -- φ uses `hRHS.remapP ∘ ψ-swap` on the F+G half: swap F↔G, then let
  -- hComposeP's pruning machinery route each vertex to its place in RHS.
  -- The LHS-K side is absurd (cn-LHS-K≡0).
  --
  -- φ⁻¹ inverts by case analysis on `splitAt RHS-G.nV`:
  --   * If the target is a boundary vertex (RHS-G), decode via
  --     `splitAt nA` to recover which F-boundary or G-boundary atom it
  --     represents, then lookup the corresponding F.dom / G.dom entry
  --     and embed into LHS.
  --   * If the target is a K-pruned vertex, use `lookup (nonMem RHS-K.dom)`
  --     to recover the underlying K-side vertex, then swap back via
  --     `ψ-swap {G.nV} {F.nV}`.
  --
  -- All wrapped with `_↑ˡ count-non LHS-K.dom` to embed Fin LHS-G.nV into
  -- Fin LHS.nV.

  φ : Fin LHS.nV → Fin RHS.nV
  φ v with splitAt LHS-G.nV v
  ... | inj₁ v' = hRHS.remapP (ψ-swap {F.nV} {G.nV} v')
  ... | inj₂ non = ⊥-elim (Fin-zero-absurd cn-LHS-K≡0 non)

  -- φ⁻¹: case on splitAt RHS-G.nV, then on splitAt nA for the boundary side.
  -- For boundaries, recover via `lookup F.dom a` / `lookup G.dom c'`.
  -- For pruned, recover via `lookup (nonMem RHS-K.dom) j` + ψ-swap back.

  φ⁻¹ : Fin RHS.nV → Fin LHS.nV
  φ⁻¹ w with splitAt RHS-G.nV w
  ... | inj₁ c with splitAt nA c
  ...    | inj₁ a  = (lookup F.dom (cast (sym F-dom-len) a) ↑ˡ G.nV)
                     ↑ˡ count-non LHS-K.dom
  ...    | inj₂ c' = (F.nV ↑ʳ lookup G.dom (cast (sym G-dom-len) c'))
                     ↑ˡ count-non LHS-K.dom
  φ⁻¹ w | inj₂ j = ψ-swap {G.nV} {F.nV} (lookup (nonMem RHS-K.dom) j)
                   ↑ˡ count-non LHS-K.dom

  -- Roundtrips.  Pattern: prove each via reduction lemmas + classify
  -- case analysis, reusing the Prune.remap-inj₁ / remap-inj₂ /
  -- classify-inj₁-lookup / classify-inj₂-lookup lemmas.

  -- φ reduction on the LHS-G branch.
  φ-inj₁-red
    : ∀ (v' : Fin LHS-G.nV)
    → φ (v' ↑ˡ count-non LHS-K.dom) ≡ hRHS.remapP (ψ-swap {F.nV} {G.nV} v')
  φ-inj₁-red v' with splitAt LHS-G.nV (v' ↑ˡ count-non LHS-K.dom)
                     | splitAt-↑ˡ LHS-G.nV v' (count-non LHS-K.dom)
  ... | .(inj₁ v') | refl = refl

  -- φ⁻¹ reduction on the RHS-pruned branch.
  φ⁻¹-inj₂-red
    : ∀ (j : Fin (count-non RHS-K.dom))
    → φ⁻¹ (RHS-G.nV ↑ʳ j)
    ≡ ψ-swap {G.nV} {F.nV} (lookup (nonMem RHS-K.dom) j) ↑ˡ count-non LHS-K.dom
  φ⁻¹-inj₂-red j with splitAt RHS-G.nV (RHS-G.nV ↑ʳ j)
                      | splitAt-↑ʳ RHS-G.nV (count-non RHS-K.dom) j
  ... | .(inj₂ j) | refl = refl

  -- φ-left-inner: the key reduction on `Fin LHS-G.nV`.  Dispatches on
  -- `classify RHS-K.dom (ψ-swap v')`:
  --   * inj₂ j (pruned): proved constructively via remap-inj₂ +
  --     φ⁻¹-inj₂-red + classify-inj₂-lookup + ψ-swap-involutive.
  --   * inj₁ i (boundary): postulated — requires lemmas relating
  --     classify-inj₁ positions to lookup-cod in hSwap's cod, then
  --     through `splitAt nA` of that lookup-cod.  These are the same
  --     classify↔lookup-cod bridges that σ∘σ-proof's `lookup-cod-*`
  --     lemmas handle; porting them here is future work.

  φ-left-int
    : (v' : Fin LHS-G.nV) (j : Fin (count-non RHS-K.dom))
    → classify RHS-K.dom (ψ-swap {F.nV} {G.nV} v') ≡ inj₂ j
    → φ⁻¹ (hRHS.remapP (ψ-swap {F.nV} {G.nV} v'))
    ≡ v' ↑ˡ count-non LHS-K.dom
  φ-left-int v' j cv-eq =
    trans (cong φ⁻¹
            (remap-inj₂ RHS-K.dom hRHS.lookup-cod
                        (ψ-swap {F.nV} {G.nV} v') j cv-eq))
    (trans (φ⁻¹-inj₂-red j)
           (cong (_↑ˡ count-non LHS-K.dom)
                 (trans (cong (ψ-swap {G.nV} {F.nV})
                              (classify-inj₂-lookup RHS-K.dom
                                 (ψ-swap {F.nV} {G.nV} v') j cv-eq))
                        (ψ-swap-involutive {F.nV} {G.nV} v'))))

  postulate
    φ-left-bdy
      : (v' : Fin LHS-G.nV) (i : Fin (length RHS-K.dom))
      → classify RHS-K.dom (ψ-swap {F.nV} {G.nV} v') ≡ inj₁ i
      → φ⁻¹ (hRHS.remapP (ψ-swap {F.nV} {G.nV} v'))
      ≡ v' ↑ˡ count-non LHS-K.dom

  -- Dispatcher that takes classify's result explicitly.  Avoids the
  -- `with classify ... in cv` abstraction issue (which left the goal
  -- in `[_,_]′ (classify | ...)` form that didn't unify with
  -- φ-left-bdy's / φ-left-int's declared types).
  φ-left-dispatch
    : (v' : Fin LHS-G.nV)
    → (cr : Fin (length RHS-K.dom) ⊎ Fin (count-non RHS-K.dom))
    → classify RHS-K.dom (ψ-swap {F.nV} {G.nV} v') ≡ cr
    → φ⁻¹ (hRHS.remapP (ψ-swap {F.nV} {G.nV} v')) ≡ v' ↑ˡ count-non LHS-K.dom
  φ-left-dispatch v' (inj₁ i) cv-eq = φ-left-bdy v' i cv-eq
  φ-left-dispatch v' (inj₂ j) cv-eq = φ-left-int v' j cv-eq

  φ-left-inner
    : (v' : Fin LHS-G.nV)
    → φ⁻¹ (hRHS.remapP (ψ-swap {F.nV} {G.nV} v')) ≡ v' ↑ˡ count-non LHS-K.dom
  φ-left-inner v' =
    φ-left-dispatch v' (classify RHS-K.dom (ψ-swap {F.nV} {G.nV} v')) refl

  φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
  φ-left v with splitAt LHS-G.nV v in eq
  ... | inj₁ v' = trans (φ-left-inner v') (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ non = ⊥-elim (Fin-zero-absurd cn-LHS-K≡0 non)

  -- φ-rght's pruned case: `w = RHS-G.nV ↑ʳ j` for some j.
  -- Chain:
  --   cong φ (φ⁻¹-inj₂-red j)                  -- φ⁻¹ (RHS-G.nV ↑ʳ j) = ψ-swap v* ↑ˡ _
  --   φ-inj₁-red (ψ-swap v*)                   -- φ (_↑ˡ _) = hRHS.remapP (ψ-swap (ψ-swap v*))
  --   cong hRHS.remapP (ψ-swap-involutive v*)  -- = hRHS.remapP v*
  --   remap-inj₂ (classify-lookup-nonMem _ j)  -- = RHS-G.nV ↑ʳ j
  -- where v* = lookup (nonMem RHS-K.dom) j.
  φ-rght-int
    : (j : Fin (count-non RHS-K.dom))
    → φ (φ⁻¹ (RHS-G.nV ↑ʳ j)) ≡ RHS-G.nV ↑ʳ j
  φ-rght-int j =
    trans (cong φ (φ⁻¹-inj₂-red j))
    (trans (φ-inj₁-red
             (ψ-swap {G.nV} {F.nV} (lookup (nonMem RHS-K.dom) j)))
    (trans (cong hRHS.remapP
                 (ψ-swap-involutive {G.nV} {F.nV}
                                    (lookup (nonMem RHS-K.dom) j)))
           (remap-inj₂ RHS-K.dom hRHS.lookup-cod
                       (lookup (nonMem RHS-K.dom) j) j
                       (classify-lookup-nonMem RHS-K.dom j))))

  postulate
    -- φ-rght's boundary case.  Mirror of φ-left-bdy: requires
    -- classify↔lookup-cod bridges tying F/G boundary positions to
    -- RHS-G's cod.  Future work.
    φ-rght-bdy
      : (w : Fin RHS.nV) (c : Fin RHS-G.nV)
      → splitAt RHS-G.nV w ≡ inj₁ c
      → φ (φ⁻¹ w) ≡ w

  -- Dispatcher pattern (same idea as φ-left-dispatch): avoid `with` on
  -- splitAt RHS-G.nV w, which would abstract `φ⁻¹ w | ...` inside the
  -- goal and fail to unify with the dispatched lemmas.  Take the
  -- splitAt result explicitly.
  φ-rght-dispatch
    : (w : Fin RHS.nV)
    → (sa : Fin RHS-G.nV ⊎ Fin (count-non RHS-K.dom))
    → splitAt RHS-G.nV w ≡ sa
    → φ (φ⁻¹ w) ≡ w
  φ-rght-dispatch w (inj₁ c) eq = φ-rght-bdy w c eq
  φ-rght-dispatch w (inj₂ j) eq =
    trans (cong (λ x → φ (φ⁻¹ x)) (sym (splitAt⁻¹-↑ʳ eq)))
          (trans (φ-rght-int j) (splitAt⁻¹-↑ʳ eq))

  φ-rght : ∀ w → φ (φ⁻¹ w) ≡ w
  φ-rght w = φ-rght-dispatch w (splitAt RHS-G.nV w) refl

  -- LHS edge ↦ RHS edge: route through the swap permutation on F.nE + G.nE.
  -- LHS.nE = (F.nE + G.nE) + 0  (first coord is the hTensor split).
  -- RHS.nE = 0 + (G.nE + F.nE)  (second coord is the hTensor split in reverse).
  -- Strip the trailing 0 from LHS.nE, swap, prepend 0 for RHS.nE.
  -- Both manipulations go through `splitAt` + the `inj₂` branch being
  -- `Fin 0` (absurd).

  -- `ψ` keeps `with` because its input `Fin LHS.nE = Fin ((F.nE + G.nE) + 0)`
  -- doesn't have `+0` stripped definitionally (reduction of `_+_` goes
  -- left-first).  But we drop the `RHS-G.nE ↑ʳ` from the body — that's
  -- `0 ↑ʳ x = x` by the zero clause of `_↑ʳ_` — so ψ returns `ψ-swap eLG`
  -- directly on the G-side branch.
  ψ : Fin LHS.nE → Fin RHS.nE
  ψ e with splitAt LHS-G.nE e
  ... | inj₁ eLG = ψ-swap {F.nE} {G.nE} eLG
  ... | inj₂ eLK = ⊥-elim (Fin-zero-absurd LHS-K-nE≡0 eLK)

  -- `ψ⁻¹` is a direct formula (no `with`): input `e : Fin RHS.nE =
  -- Fin (0 + (G.nE + F.nE)) = Fin (G.nE + F.nE)` reduces via the zero
  -- clause of `_+_`, so ψ-swap applies immediately and we append 0
  -- via `_↑ˡ LHS-K.nE = _↑ˡ 0`.  Removing the `with` is essential:
  -- it lets `ψ⁻¹ x` unfold by substitution rather than `with`-hoisting,
  -- which simplifies ψ-left's proof considerably.
  ψ⁻¹ : Fin RHS.nE → Fin LHS.nE
  ψ⁻¹ e = ψ-swap {G.nE} {F.nE} e ↑ˡ LHS-K.nE

  -- ψ-left.  After `with splitAt LHS-G.nE e in eq` picks the inj₁
  -- branch, ψ reduces to `ψ-swap eLG`, and ψ⁻¹ (being a direct formula)
  -- reduces to `ψ-swap (ψ-swap eLG) ↑ˡ LHS-K.nE`.  Then the involutive
  -- lemma collapses the double ψ-swap and `splitAt⁻¹-↑ˡ` returns us
  -- to the original `e`.
  ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
  ψ-left e with splitAt LHS-G.nE e in eq
  ... | inj₁ eLG =
    trans (cong (_↑ˡ LHS-K.nE) (ψ-swap-involutive {F.nE} {G.nE} eLG))
          (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ eLK = ⊥-elim (Fin-zero-absurd LHS-K-nE≡0 eLK)

  -- ψ-rght.  `ψ⁻¹ e = ψ-swap e ↑ˡ LHS-K.nE` directly, so
  -- `splitAt LHS-G.nE (ψ⁻¹ e)` = `splitAt LHS-G.nE (ψ-swap e ↑ˡ LHS-K.nE)`
  -- reduces to `inj₁ (ψ-swap e)` via `splitAt-↑ˡ`.  Dual-with dispatches
  -- that reduction, then `ψ-swap-involutive` closes the goal.
  ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e
  ψ-rght e with splitAt LHS-G.nE (ψ⁻¹ e)
                | splitAt-↑ˡ LHS-G.nE (ψ-swap {G.nE} {F.nE} e) LHS-K.nE
  ... | .(inj₁ (ψ-swap {G.nE} {F.nE} e)) | refl =
    ψ-swap-involutive {G.nE} {F.nE} e

  --------------------------------------------------------------------------
  -- Field postulates (iso body).
  --
  -- These are the 7 remaining `_≅ᴴ_` fields beyond φ/ψ/roundtrips.
  -- Each is provable by case analysis on splitAt + classify machinery;
  -- the proofs parallel σ∘σ-proof's structure (the vertex-label,
  -- dom, cod, and edge-label chains) but are more verbose because
  -- both LHS and RHS have non-trivial pruned K sides and F/G have
  -- edges.  Separated from the iso assembly so each can be discharged
  -- independently.

  --------------------------------------------------------------------------
  -- Edge-label preservation: atom-ein, atom-eout, ψ-elab.
  --
  -- Pattern (mirrors Congruence.agda's `atom-ein-T` / `atom-eout-T` /
  -- `ψ-elab-T`):  case on `splitAt LHS-G.nE e` (inj₂ absurd), then on
  -- `splitAt F.nE eLG`.  In each branch, LHS.ein / LHS.eout reduce via
  -- the outer `with`-hoisting on the LHS side's hComposeP + hTensor,
  -- while RHS requires explicit `hTR.ein-c-inj{₁,₂}-red` to peel the
  -- RHS-K's hTensor structure (since RHS-G.nE = 0 makes RHS's outer
  -- hComposeP auto-reduce, but the swap puts us on a specific branch
  -- of RHS-K = hTensor G F).

  -- ψ-swap reduction lemmas (dual-with).  Pattern analogous to
  -- `splitAt-↑ˡ` / `splitAt-↑ʳ` + dot pattern.
  ψ-swap-inj₁-red : ∀ {m n} (eL : Fin m) → ψ-swap {m} {n} (eL ↑ˡ n) ≡ n ↑ʳ eL
  ψ-swap-inj₁-red {m} {n} eL with splitAt m (eL ↑ˡ n)
                                  | splitAt-↑ˡ m eL n
  ... | .(inj₁ eL) | refl = refl

  ψ-swap-inj₂-red : ∀ {m n} (eR : Fin n) → ψ-swap {m} {n} (m ↑ʳ eR) ≡ eR ↑ˡ m
  ψ-swap-inj₂-red {m} {n} eR with splitAt m (m ↑ʳ eR)
                                  | splitAt-↑ʳ m n eR
  ... | .(inj₂ eR) | refl = refl

  -- subst₂ helpers (mirror Congruence's private helpers).
  private
    subst₂-trans : ∀ {a b} {A : Set a} {B : Set b} {P : A → B → Set}
                     {x₁ x₂ x₃ y₁ y₂ y₃}
                 → (p : x₁ ≡ x₂) (p' : x₂ ≡ x₃)
                   (q : y₁ ≡ y₂) (q' : y₂ ≡ y₃)
                 → (z : P x₁ y₁)
                 → subst₂ P p' q' (subst₂ P p q z)
                 ≡ subst₂ P (trans p p') (trans q q') z
    subst₂-trans refl refl refl refl _ = refl

    subst₂-sym-subst₂ : ∀ {a b} {A : Set a} {B : Set b} {P : A → B → Set}
                          {x x' y y'}
                      → (p : x ≡ x') (q : y ≡ y') (z : P x y)
                      → subst₂ P (sym p) (sym q) (subst₂ P p q z) ≡ z
    subst₂-sym-subst₂ refl refl _ = refl

  -- atom-ein: for an F-edge eLG = fE ↑ˡ G.nE:
  --   LHS = map F.vlab (F.ein fE) via two `map-via-inj` collapses.
  --   RHS = map F.vlab (F.ein fE) via hTR.ein-c-inj₂-red + map-via-remapP +
  --   map-via-raise (injR side of hTensor G F).
  -- For a G-edge eLG = F.nE ↑ʳ gE:
  --   LHS = map G.vlab (G.ein gE) via map-via-inj + map-via-raise.
  --   RHS = map G.vlab (G.ein gE) via hTR.ein-c-inj₁-red + map-via-remapP +
  --   map-via-inj (injL side of hTensor G F).

  atom-ein : ∀ e → map RHS.vlab (RHS.ein (ψ e))
                 ≡ map LHS.vlab (LHS.ein e)
  atom-ein e with splitAt LHS-G.nE e
  ... | inj₂ absurd = ⊥-elim (Fin-zero-absurd LHS-K-nE≡0 absurd)
  ... | inj₁ eLG with splitAt F.nE eLG
  ...   | inj₁ fE =
    -- RHS side: ψ-swap's inj₁ gives G.nE ↑ʳ fE; RHS.ein unfolds via the
    -- RHS-G.nE = 0 reduction.
    trans (cong (map RHS.vlab)
                (cong (map hRHS.remapP) (hTR.ein-c-inj₂-red fE)))
    (trans (sym (hRHS.map-via-remapP (map hTR.injR (F.ein fE))))
    (trans (sym (map-via-raise hTR.vlab-injR (F.ein fE)))
           -- Now: map F.vlab (F.ein fE) on both sides.
    (trans (map-via-inj hTL.vlab-injL (F.ein fE))
           (map-via-inj hLHS.vlab-injL (map hTL.injL (F.ein fE))))))
  ...   | inj₂ gE =
    -- RHS side: ψ-swap's inj₂ gives gE ↑ˡ F.nE; RHS-K.ein via inj₁-red.
    trans (cong (map RHS.vlab)
                (cong (map hRHS.remapP) (hTR.ein-c-inj₁-red gE)))
    (trans (sym (hRHS.map-via-remapP (map hTR.injL (G.ein gE))))
    (trans (sym (map-via-inj hTR.vlab-injL (G.ein gE)))
    (trans (map-via-raise hTL.vlab-injR (G.ein gE))
           (map-via-inj hLHS.vlab-injL (map hTL.injR (G.ein gE))))))

  atom-eout : ∀ e → map RHS.vlab (RHS.eout (ψ e))
                  ≡ map LHS.vlab (LHS.eout e)
  atom-eout e with splitAt LHS-G.nE e
  ... | inj₂ absurd = ⊥-elim (Fin-zero-absurd LHS-K-nE≡0 absurd)
  ... | inj₁ eLG with splitAt F.nE eLG
  ...   | inj₁ fE =
    trans (cong (map RHS.vlab)
                (cong (map hRHS.remapP) (hTR.eout-c-inj₂-red fE)))
    (trans (sym (hRHS.map-via-remapP (map hTR.injR (F.eout fE))))
    (trans (sym (map-via-raise hTR.vlab-injR (F.eout fE)))
    (trans (map-via-inj hTL.vlab-injL (F.eout fE))
           (map-via-inj hLHS.vlab-injL (map hTL.injL (F.eout fE))))))
  ...   | inj₂ gE =
    trans (cong (map RHS.vlab)
                (cong (map hRHS.remapP) (hTR.eout-c-inj₁-red gE)))
    (trans (sym (hRHS.map-via-remapP (map hTR.injL (G.eout gE))))
    (trans (sym (map-via-inj hTR.vlab-injL (G.eout gE)))
    (trans (map-via-raise hTL.vlab-injR (G.eout gE))
           (map-via-inj hLHS.vlab-injL (map hTL.injR (G.eout gE))))))

  postulate
    φ-lab   : ∀ v → RHS.vlab (φ v) ≡ LHS.vlab v
    ψ-ein   : ∀ e → RHS.ein (ψ e) ≡ map φ (LHS.ein e)
    ψ-eout  : ∀ e → RHS.eout (ψ e) ≡ map φ (LHS.eout e)
    φ-dom   : RHS.dom ≡ map φ LHS.dom
    φ-cod   : RHS.cod ≡ map φ LHS.cod

    ψ-elab    : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e)
                                      (RHS.elab (ψ e))
                    ≡ LHS.elab e

  --------------------------------------------------------------------------
  -- Assembled iso.

  σ-nat-iso : LHS ≅ᴴ RHS
  σ-nat-iso = record
    { φ         = φ
    ; φ⁻¹       = φ⁻¹
    ; φ-left    = φ-left
    ; φ-rght    = φ-rght
    ; ψ         = ψ
    ; ψ⁻¹       = ψ⁻¹
    ; ψ-left    = ψ-left
    ; ψ-rght    = ψ-rght
    ; φ-lab     = φ-lab
    ; ψ-ein     = ψ-ein
    ; ψ-eout    = ψ-eout
    ; φ-dom     = φ-dom
    ; φ-cod     = φ-cod
    ; atom-ein  = atom-ein
    ; atom-eout = atom-eout
    ; ψ-elab    = ψ-elab
    }

--------------------------------------------------------------------------------
-- Top-level σ-nat (dispatch-ready form).

σ∘[f⊗g]≈[g⊗f]∘σ-sound
  : ∀ {A B C D} {f : HomTerm A B} {g : HomTerm C D}
  → ⟪ σ {B} {D} ∘ (f ⊗₁ g) ⟫ ≅ᴴ ⟪ (g ⊗₁ f) ∘ σ {A} {C} ⟫
σ∘[f⊗g]≈[g⊗f]∘σ-sound {A} {B} {C} {D} {f} {g} =
  σ-nat-proof.σ-nat-iso {A} {B} {C} {D}
    ⟪ f ⟫ (⟪_⟫-dom-unique f) ⟪ g ⟫ (⟪_⟫-dom-unique g)
