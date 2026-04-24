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
-- Vertex bijection (4/4 COMPLETE):
--   * φ, φ⁻¹  — concrete formulas: φ uses `hRHS.remapP ∘ ψ-swap`
--     on the F+G half; φ⁻¹ case-splits on `splitAt RHS-G.nV` then
--     `splitAt nA` for boundary, or `lookup (nonMem RHS-K.dom)` for
--     the pruned side, all composed with ψ-swap back and embedded.
--   * φ-left  — PROVED: interior branch via `remap-inj₂`,
--     `classify-inj₂-lookup`, and `ψ-swap-involutive`; boundary
--     branch via remapP-F-bdy / remapP-G-bdy + contradiction helpers.
--   * φ-rght  — PROVED: interior branch analogously using
--     `classify-lookup-nonMem`; boundary branch via φ⁻¹-F-bdy-red /
--     φ⁻¹-G-bdy-red + cast-cancel chain.
--
-- Edge label preservation (3/3 COMPLETE):
--   * atom-ein, atom-eout — case analysis on F-edge / G-edge + 5-step
--     trans chain through map-via-inj / map-via-remapP / map-via-raise.
--   * ψ-elab — 10-step chain via subst₂-trans, subst₂-sym-subst₂,
--     map-via-remapP-natural, hTR.elab-c-inj{₁,₂}.
--
-- Boundary compatibility (2/2 COMPLETE):
--   * φ-dom, φ-cod — list-wise compatibility via remapP-F-bdy /
--     remapP-G-bdy (dom side) and remapP-LHS-D / remapP-LHS-B (cod
--     side), both using map-cast-range + map-lookup-range' to bridge
--     between range-indexed and dom/cod-indexed lists.
--
-- 3 remaining structural field postulates:
--   * φ-lab, ψ-ein, ψ-eout
-- These bridge concrete φ/ψ to the record's label/edge invariants.
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
  using (hSwap-count-non-dom; hSwap-dom-Unique; hSwap-cod-covers; hSwap-dom-covers;
         inject+-inj; raise-inj; range-covers; length-range;
         toℕ-index-++⁺ˡ; toℕ-index-++⁺ʳ; toℕ-index-range-covers;
         disj-L-R; map-cast-range)
open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique)
open import Categories.APROP.Hypergraph.CoherenceHelpers sig
  using (subst₂-trans; subst₂-sym-subst₂; trans-reflʳ)
open import Categories.APROP.Hypergraph.Prune
  using (count-non; AllIn; AllIn→count-non-zero;
         nonMem; classify; classify-lookup-Unique;
         classify-inj₁-lookup; classify-inj₂-lookup;
         classify-inj₂-∉;
         classify-lookup-nonMem;
         remap; remap-inj₁; remap-inj₂;
         ∈-map⁺-index-cast)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; splitAt; cast; _↑ˡ_; _↑ʳ_; toℕ)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ;
                                        splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ;
                                        cast-is-id; cast-trans; toℕ-cast)
  renaming (toℕ-injective to Fin-toℕ-injective)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (length-map; map-++; map-∘; map-cong; map-id)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻; ∈-lookup)
open import Data.List.Relation.Unary.Any using (index; here; there)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
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

    -- And the corresponding cod-length equations.
    F-cod-len : length F.cod ≡ nB
    F-cod-len = trans (sym (length-map F.vlab F.cod)) (cong length F.cod-ok)

    G-cod-len : length G.cod ≡ nD
    G-cod-len = trans (sym (length-map G.vlab G.cod)) (cong length G.cod-ok)

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

  -- ψ-swap reduction lemmas (dual-with).  Moved up here so they're
  -- available in the vertex bijection's boundary proofs.
  ψ-swap-inj₁-red : ∀ {m n} (eL : Fin m) → ψ-swap {m} {n} (eL ↑ˡ n) ≡ n ↑ʳ eL
  ψ-swap-inj₁-red {m} {n} eL with splitAt m (eL ↑ˡ n)
                                  | splitAt-↑ˡ m eL n
  ... | .(inj₁ eL) | refl = refl

  ψ-swap-inj₂-red : ∀ {m n} (eR : Fin n) → ψ-swap {m} {n} (m ↑ʳ eR) ≡ eR ↑ˡ m
  ψ-swap-inj₂-red {m} {n} eR with splitAt m (m ↑ʳ eR)
                                  | splitAt-↑ʳ m n eR
  ... | .(inj₂ eR) | refl = refl

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

  ------------------------------------------------------------------------
  -- Boundary-case helpers for φ-left-bdy / φ-rght-bdy.
  --
  -- Mirrors σ∘σ-proof's `remapP-kcod-*` / `lookup-cod-*` pattern:
  --   * Prove RHS-K.dom is Unique (via `Uniq-Prop.++⁺` + `disj-L-R`).
  --   * Port `remapP-via-member`: given a witness v ∈ RHS-K.dom,
  --     remapP v reduces to lookup-cod (index witness) ↑ˡ _.
  --   * Prove `lookup-cod-F-bdy` / `lookup-cod-G-bdy` via toℕ-injective:
  --     at a specific F.dom/G.dom-based witness, lookup-cod gives a
  --     specific value in RHS-G.cod.
  --   * Combine into `remapP-F-bdy` / `remapP-G-bdy`.

  -- Index of ∈-lookup (stdlib only has it for Vec, not List).
  index-∈-lookup
    : ∀ {ℓ} {X : Set ℓ} (xs : List X) (i : Fin (length xs))
    → index (∈-lookup {xs = xs} i) ≡ i
  index-∈-lookup (_ ∷ _)  zero    = refl
  index-∈-lookup (_ ∷ xs) (suc i) = cong suc (index-∈-lookup xs i)

  -- RHS-K.dom is Unique: both halves are Unique via map⁺ on inject+/raise
  -- injectivity, and they're disjoint via `disj-L-R`.
  RHS-K-dom-Unique : Unique RHS-K.dom
  RHS-K-dom-Unique =
    Uniq-Prop.++⁺
      (Uniq-Prop.map⁺ (inject+-inj F.nV) G-dom-U)
      (Uniq-Prop.map⁺ (raise-inj G.nV)   F-dom-U)
      (disj-L-R G.dom F.dom)

  -- Port of σ∘σ-proof's `remapP-via-member`.
  remapP-via-member
    : ∀ {v : Fin RHS-K.nV} (v∈K-dom : v ∈ RHS-K.dom)
    → hRHS.remapP v ≡ hRHS.lookup-cod (index v∈K-dom) ↑ˡ count-non RHS-K.dom
  remapP-via-member {v} v∈K-dom =
    remap-inj₁ RHS-K.dom hRHS.lookup-cod v (index v∈K-dom) classify-eq
    where
      classify-eq : classify RHS-K.dom v ≡ inj₁ (index v∈K-dom)
      classify-eq = trans (cong (classify RHS-K.dom) (lookup-index v∈K-dom))
                          (classify-lookup-Unique RHS-K.dom RHS-K-dom-Unique
                                                  (index v∈K-dom))

  -- lookup-cod at F-boundary position.  Mirrors σ∘σ-proof's
  -- `lookup-cod-raise-nB`: for v = G.nV ↑ʳ lookup F.dom pos_F (= injR v_F),
  -- looking up in RHS-G.cod at the cast-matched position gives
  -- (cast F-dom-len pos_F) ↑ˡ nC.
  lookup-cod-F-bdy
    : ∀ (pos_F : Fin (length F.dom))
    → hRHS.lookup-cod
        (index (∈-++⁺ʳ (map (_↑ˡ F.nV) G.dom)
                       (∈-map⁺ (G.nV ↑ʳ_) (∈-lookup {xs = F.dom} pos_F))))
    ≡ cast F-dom-len pos_F ↑ˡ nC
  lookup-cod-F-bdy pos_F =
    trans (cong (lookup RHS-G.cod) cast-k≡mirror)
          (sym (lookup-index mirror-in-G))
    where
      k-witness : G.nV ↑ʳ lookup F.dom pos_F ∈ RHS-K.dom
      k-witness = ∈-++⁺ʳ (map (_↑ˡ F.nV) G.dom)
                        (∈-map⁺ (G.nV ↑ʳ_) (∈-lookup {xs = F.dom} pos_F))

      mirror-in-G : cast F-dom-len pos_F ↑ˡ nC ∈ RHS-G.cod
      mirror-in-G = ∈-++⁺ʳ (map (nA ↑ʳ_) (range nC))
                          (∈-map⁺ (_↑ˡ nC)
                                  (range-covers nA (cast F-dom-len pos_F)))

      k-idx : Fin (length RHS-K.dom)
      k-idx = index k-witness

      g-idx : Fin (length RHS-G.cod)
      g-idx = cast hRHS.dom-cod-len k-idx

      k-side-toℕ : toℕ g-idx ≡ length (map (_↑ˡ F.nV) G.dom) + toℕ pos_F
      k-side-toℕ =
        trans (toℕ-cast _ k-idx)
        (trans (toℕ-index-++⁺ʳ (map (_↑ˡ F.nV) G.dom)
                  (∈-map⁺ (G.nV ↑ʳ_) (∈-lookup {xs = F.dom} pos_F)))
        (cong (length (map (_↑ˡ F.nV) G.dom) +_)
              (trans (cong toℕ (∈-map⁺-index-cast (G.nV ↑ʳ_)
                                                  (raise-inj _)
                                                  (∈-lookup {xs = F.dom} pos_F)))
              (trans (toℕ-cast _ _)
                     (cong toℕ (index-∈-lookup F.dom pos_F))))))

      g-side-toℕ : toℕ (index mirror-in-G) ≡ length (map (nA ↑ʳ_) (range nC)) + toℕ pos_F
      g-side-toℕ =
        trans (toℕ-index-++⁺ʳ (map (nA ↑ʳ_) (range nC))
                 (∈-map⁺ (_↑ˡ nC)
                         (range-covers nA (cast F-dom-len pos_F))))
        (cong (length (map (nA ↑ʳ_) (range nC)) +_)
              (trans (cong toℕ (∈-map⁺-index-cast (_↑ˡ nC)
                                                  (inject+-inj _)
                                                  (range-covers nA
                                                    (cast F-dom-len pos_F))))
              (trans (toℕ-cast _ _)
              (trans (toℕ-index-range-covers nA (cast F-dom-len pos_F))
                     (toℕ-cast _ pos_F)))))

      -- The two halves have equal length (both = length G.dom = nC).
      len-eq : length (map (_↑ˡ F.nV) G.dom) ≡ length (map (nA ↑ʳ_) (range nC))
      len-eq = trans (length-map (_↑ˡ F.nV) G.dom)
              (trans G-dom-len
              (trans (sym (length-range nC))
                     (sym (length-map (nA ↑ʳ_) (range nC)))))

      cast-k≡mirror : g-idx ≡ index mirror-in-G
      cast-k≡mirror = Fin-toℕ-injective
        (trans k-side-toℕ (trans (cong (_+ toℕ pos_F) len-eq) (sym g-side-toℕ)))

  -- lookup-cod at G-boundary position.  Mirror of lookup-cod-F-bdy.
  lookup-cod-G-bdy
    : ∀ (pos_G : Fin (length G.dom))
    → hRHS.lookup-cod
        (index (∈-++⁺ˡ {ys = map (G.nV ↑ʳ_) F.dom}
                       (∈-map⁺ (_↑ˡ F.nV) (∈-lookup {xs = G.dom} pos_G))))
    ≡ nA ↑ʳ cast G-dom-len pos_G
  lookup-cod-G-bdy pos_G =
    trans (cong (lookup RHS-G.cod) cast-k≡mirror)
          (sym (lookup-index mirror-in-G))
    where
      k-witness : lookup G.dom pos_G ↑ˡ F.nV ∈ RHS-K.dom
      k-witness = ∈-++⁺ˡ {ys = map (G.nV ↑ʳ_) F.dom}
                        (∈-map⁺ (_↑ˡ F.nV) (∈-lookup {xs = G.dom} pos_G))

      mirror-in-G : nA ↑ʳ cast G-dom-len pos_G ∈ RHS-G.cod
      mirror-in-G = ∈-++⁺ˡ {ys = map (_↑ˡ nC) (range nA)}
                          (∈-map⁺ (nA ↑ʳ_)
                                  (range-covers nC (cast G-dom-len pos_G)))

      k-idx : Fin (length RHS-K.dom)
      k-idx = index k-witness

      g-idx : Fin (length RHS-G.cod)
      g-idx = cast hRHS.dom-cod-len k-idx

      k-side-toℕ : toℕ g-idx ≡ toℕ pos_G
      k-side-toℕ =
        trans (toℕ-cast _ k-idx)
        (trans (toℕ-index-++⁺ˡ
                  (∈-map⁺ (_↑ˡ F.nV) (∈-lookup {xs = G.dom} pos_G)))
        (trans (cong toℕ (∈-map⁺-index-cast (_↑ˡ F.nV)
                                             (inject+-inj _)
                                             (∈-lookup {xs = G.dom} pos_G)))
        (trans (toℕ-cast _ _)
               (cong toℕ (index-∈-lookup G.dom pos_G)))))

      g-side-toℕ : toℕ (index mirror-in-G) ≡ toℕ pos_G
      g-side-toℕ =
        trans (toℕ-index-++⁺ˡ
                (∈-map⁺ (nA ↑ʳ_)
                        (range-covers nC (cast G-dom-len pos_G))))
        (trans (cong toℕ (∈-map⁺-index-cast (nA ↑ʳ_)
                                             (raise-inj _)
                                             (range-covers nC
                                               (cast G-dom-len pos_G))))
        (trans (toℕ-cast _ _)
        (trans (toℕ-index-range-covers nC (cast G-dom-len pos_G))
               (toℕ-cast _ pos_G))))

      cast-k≡mirror : g-idx ≡ index mirror-in-G
      cast-k≡mirror = Fin-toℕ-injective (trans k-side-toℕ (sym g-side-toℕ))

  -- Combined remap lemmas.
  remapP-F-bdy
    : ∀ (pos_F : Fin (length F.dom))
    → hRHS.remapP (G.nV ↑ʳ lookup F.dom pos_F)
    ≡ (cast F-dom-len pos_F ↑ˡ nC) ↑ˡ count-non RHS-K.dom
  remapP-F-bdy pos_F =
    trans (remapP-via-member witness)
          (cong (_↑ˡ count-non RHS-K.dom) (lookup-cod-F-bdy pos_F))
    where
      witness : G.nV ↑ʳ lookup F.dom pos_F ∈ RHS-K.dom
      witness = ∈-++⁺ʳ (map (_↑ˡ F.nV) G.dom)
                      (∈-map⁺ (G.nV ↑ʳ_) (∈-lookup {xs = F.dom} pos_F))

  remapP-G-bdy
    : ∀ (pos_G : Fin (length G.dom))
    → hRHS.remapP (lookup G.dom pos_G ↑ˡ F.nV)
    ≡ (nA ↑ʳ cast G-dom-len pos_G) ↑ˡ count-non RHS-K.dom
  remapP-G-bdy pos_G =
    trans (remapP-via-member witness)
          (cong (_↑ˡ count-non RHS-K.dom) (lookup-cod-G-bdy pos_G))
    where
      witness : lookup G.dom pos_G ↑ˡ F.nV ∈ RHS-K.dom
      witness = ∈-++⁺ˡ {ys = map (G.nV ↑ʳ_) F.dom}
                      (∈-map⁺ (_↑ˡ F.nV) (∈-lookup {xs = G.dom} pos_G))

  ------------------------------------------------------------------------
  -- LHS-side helpers for φ-cod.
  --
  -- Mirror of the RHS-side helpers above, but with (hSwap B D) as K
  -- and (hTensor F G) as G (the LHS's hComposeP components).  These
  -- compute `hLHS.remapP` on specific hSwap.cod-equivalent positions
  -- and relate them to elements of LHS-G.cod (= hTensor F G.cod).

  -- (hSwap B D).dom is Unique.
  LHS-K-dom-Unique : Unique LHS-K.dom
  LHS-K-dom-Unique = hSwap-dom-Unique B D

  -- remapP-via-member for hLHS.
  remapP-via-member-LHS
    : ∀ {v : Fin LHS-K.nV} (v∈K-dom : v ∈ LHS-K.dom)
    → hLHS.remapP v ≡ hLHS.lookup-cod (index v∈K-dom) ↑ˡ count-non LHS-K.dom
  remapP-via-member-LHS {v} v∈K-dom =
    remap-inj₁ LHS-K.dom hLHS.lookup-cod v (index v∈K-dom) classify-eq
    where
      classify-eq : classify LHS-K.dom v ≡ inj₁ (index v∈K-dom)
      classify-eq = trans (cong (classify LHS-K.dom) (lookup-index v∈K-dom))
                          (classify-lookup-Unique LHS-K.dom LHS-K-dom-Unique
                                                  (index v∈K-dom))

  -- lookup-cod at LHS-side D-boundary position.  For d : Fin nD, the
  -- position `nB ↑ʳ d` is in the SECOND half of (hSwap B D).dom
  -- (which is `map (_↑ˡ nD) (range nB) ++ map (nB ↑ʳ_) (range nD)`).
  -- After lookup-cod it lands in the SECOND half of LHS-G.cod =
  -- `map hTL.injL F.cod ++ map hTL.injR G.cod`, i.e., at an F.nV ↑ʳ
  -- lookup G.cod position.
  lookup-cod-LHS-D
    : ∀ (d : Fin nD)
    → hLHS.lookup-cod
        (index (∈-++⁺ʳ (map (_↑ˡ nD) (range nB))
                       (∈-map⁺ (nB ↑ʳ_) (range-covers nD d))))
    ≡ F.nV ↑ʳ lookup G.cod (cast (sym G-cod-len) d)
  lookup-cod-LHS-D d =
    trans (cong (lookup LHS-G.cod) cast-k≡mirror)
          (sym (lookup-index mirror-in-G))
    where
      k-witness : nB ↑ʳ d ∈ LHS-K.dom
      k-witness = ∈-++⁺ʳ (map (_↑ˡ nD) (range nB))
                        (∈-map⁺ (nB ↑ʳ_) (range-covers nD d))

      mirror-in-G : F.nV ↑ʳ lookup G.cod (cast (sym G-cod-len) d) ∈ LHS-G.cod
      mirror-in-G = ∈-++⁺ʳ (map hTL.injL F.cod)
                          (∈-map⁺ (F.nV ↑ʳ_)
                                  (∈-lookup {xs = G.cod}
                                            (cast (sym G-cod-len) d)))

      k-idx : Fin (length LHS-K.dom)
      k-idx = index k-witness

      g-idx : Fin (length LHS-G.cod)
      g-idx = cast hLHS.dom-cod-len k-idx

      k-side-toℕ : toℕ g-idx
                 ≡ length (map (_↑ˡ nD) (range nB)) + toℕ d
      k-side-toℕ =
        trans (toℕ-cast _ k-idx)
        (trans (toℕ-index-++⁺ʳ (map (_↑ˡ nD) (range nB))
                  (∈-map⁺ (nB ↑ʳ_) (range-covers nD d)))
        (cong (length (map (_↑ˡ nD) (range nB)) +_)
              (trans (cong toℕ (∈-map⁺-index-cast (nB ↑ʳ_)
                                                  (raise-inj _)
                                                  (range-covers nD d)))
              (trans (toℕ-cast _ _)
                     (toℕ-index-range-covers nD d)))))

      g-side-toℕ : toℕ (index mirror-in-G)
                 ≡ length (map hTL.injL F.cod) + toℕ d
      g-side-toℕ =
        trans (toℕ-index-++⁺ʳ (map hTL.injL F.cod)
                 (∈-map⁺ (F.nV ↑ʳ_)
                         (∈-lookup {xs = G.cod} (cast (sym G-cod-len) d))))
        (cong (length (map hTL.injL F.cod) +_)
              (trans (cong toℕ (∈-map⁺-index-cast (F.nV ↑ʳ_)
                                                  (raise-inj _)
                                                  (∈-lookup {xs = G.cod}
                                                            (cast (sym G-cod-len) d))))
              (trans (toℕ-cast _ _)
              (trans (cong toℕ (index-∈-lookup G.cod (cast (sym G-cod-len) d)))
                     (toℕ-cast _ d)))))

      len-eq : length (map (_↑ˡ nD) (range nB))
             ≡ length (map hTL.injL F.cod)
      len-eq = trans (length-map (_↑ˡ nD) (range nB))
              (trans (length-range nB)
              (trans (sym F-cod-len)
                     (sym (length-map hTL.injL F.cod))))

      cast-k≡mirror : g-idx ≡ index mirror-in-G
      cast-k≡mirror = Fin-toℕ-injective
        (trans k-side-toℕ
        (trans (cong (_+ toℕ d) len-eq)
               (sym g-side-toℕ)))

  -- lookup-cod at LHS-side B-boundary position.  Mirror of lookup-cod-LHS-D.
  lookup-cod-LHS-B
    : ∀ (b : Fin nB)
    → hLHS.lookup-cod
        (index (∈-++⁺ˡ {ys = map (nB ↑ʳ_) (range nD)}
                       (∈-map⁺ (_↑ˡ nD) (range-covers nB b))))
    ≡ lookup F.cod (cast (sym F-cod-len) b) ↑ˡ G.nV
  lookup-cod-LHS-B b =
    trans (cong (lookup LHS-G.cod) cast-k≡mirror)
          (sym (lookup-index mirror-in-G))
    where
      k-witness : b ↑ˡ nD ∈ LHS-K.dom
      k-witness = ∈-++⁺ˡ {ys = map (nB ↑ʳ_) (range nD)}
                        (∈-map⁺ (_↑ˡ nD) (range-covers nB b))

      mirror-in-G : lookup F.cod (cast (sym F-cod-len) b) ↑ˡ G.nV ∈ LHS-G.cod
      mirror-in-G = ∈-++⁺ˡ {ys = map hTL.injR G.cod}
                          (∈-map⁺ (_↑ˡ G.nV)
                                  (∈-lookup {xs = F.cod}
                                            (cast (sym F-cod-len) b)))

      k-idx : Fin (length LHS-K.dom)
      k-idx = index k-witness

      g-idx : Fin (length LHS-G.cod)
      g-idx = cast hLHS.dom-cod-len k-idx

      k-side-toℕ : toℕ g-idx ≡ toℕ b
      k-side-toℕ =
        trans (toℕ-cast _ k-idx)
        (trans (toℕ-index-++⁺ˡ
                  (∈-map⁺ (_↑ˡ nD) (range-covers nB b)))
        (trans (cong toℕ (∈-map⁺-index-cast (_↑ˡ nD)
                                             (inject+-inj _)
                                             (range-covers nB b)))
        (trans (toℕ-cast _ _)
               (toℕ-index-range-covers nB b))))

      g-side-toℕ : toℕ (index mirror-in-G) ≡ toℕ b
      g-side-toℕ =
        trans (toℕ-index-++⁺ˡ
                (∈-map⁺ (_↑ˡ G.nV)
                        (∈-lookup {xs = F.cod} (cast (sym F-cod-len) b))))
        (trans (cong toℕ (∈-map⁺-index-cast (_↑ˡ G.nV)
                                             (inject+-inj _)
                                             (∈-lookup {xs = F.cod}
                                                       (cast (sym F-cod-len) b))))
        (trans (toℕ-cast _ _)
        (trans (cong toℕ (index-∈-lookup F.cod (cast (sym F-cod-len) b)))
               (toℕ-cast _ b))))

      cast-k≡mirror : g-idx ≡ index mirror-in-G
      cast-k≡mirror = Fin-toℕ-injective (trans k-side-toℕ (sym g-side-toℕ))

  -- Combined: hLHS.remapP on the D/B halves of (hSwap B D).cod.
  remapP-LHS-D
    : ∀ (d : Fin nD)
    → hLHS.remapP (nB ↑ʳ d)
    ≡ (F.nV ↑ʳ lookup G.cod (cast (sym G-cod-len) d)) ↑ˡ count-non LHS-K.dom
  remapP-LHS-D d =
    trans (remapP-via-member-LHS witness)
          (cong (_↑ˡ count-non LHS-K.dom) (lookup-cod-LHS-D d))
    where
      witness : nB ↑ʳ d ∈ LHS-K.dom
      witness = ∈-++⁺ʳ (map (_↑ˡ nD) (range nB))
                      (∈-map⁺ (nB ↑ʳ_) (range-covers nD d))

  remapP-LHS-B
    : ∀ (b : Fin nB)
    → hLHS.remapP (b ↑ˡ nD)
    ≡ (lookup F.cod (cast (sym F-cod-len) b) ↑ˡ G.nV) ↑ˡ count-non LHS-K.dom
  remapP-LHS-B b =
    trans (remapP-via-member-LHS witness)
          (cong (_↑ˡ count-non LHS-K.dom) (lookup-cod-LHS-B b))
    where
      witness : b ↑ˡ nD ∈ LHS-K.dom
      witness = ∈-++⁺ˡ {ys = map (nB ↑ʳ_) (range nD)}
                      (∈-map⁺ (_↑ˡ nD) (range-covers nB b))

  ------------------------------------------------------------------------
  -- Contradiction helpers: if f ∉ F.dom then G.nV ↑ʳ f ∉ RHS-K.dom
  -- (and symmetric for G-side).  Used to discharge off-path classify
  -- cases in φ-left-bdy / φ-rght-bdy.

  injR-∉-RHS-K-dom
    : ∀ {f : Fin F.nV} → f ∉ F.dom → G.nV ↑ʳ f ∉ RHS-K.dom
  injR-∉-RHS-K-dom {f} f∉F v∈
    with ∈-++⁻ (map (_↑ˡ F.nV) G.dom) v∈
  ... | inj₁ v∈L =
    let mapped = ∈-map⁻ (_↑ˡ F.nV) v∈L
        g      = proj₁ mapped
        eq     = proj₂ (proj₂ mapped)  -- G.nV ↑ʳ f ≡ g ↑ˡ F.nV
        splitL : splitAt G.nV (G.nV ↑ʳ f) ≡ inj₁ g
        splitL = trans (cong (splitAt G.nV) eq) (splitAt-↑ˡ G.nV g F.nV)
        splitR : splitAt G.nV (G.nV ↑ʳ f) ≡ inj₂ f
        splitR = splitAt-↑ʳ G.nV F.nV f
        abs : inj₁ g ≡ inj₂ f
        abs = trans (sym splitL) splitR
    in case abs of λ ()
    where open import Function using (case_of_)
  ... | inj₂ v∈R =
    let mapped = ∈-map⁻ (G.nV ↑ʳ_) v∈R
        f'     = proj₁ mapped
        f'∈F   = proj₁ (proj₂ mapped)
        eq     = proj₂ (proj₂ mapped)  -- G.nV ↑ʳ f ≡ G.nV ↑ʳ f'
    in f∉F (subst (_∈ F.dom) (sym (raise-inj G.nV eq)) f'∈F)

  injL-∉-RHS-K-dom
    : ∀ {g : Fin G.nV} → g ∉ G.dom → g ↑ˡ F.nV ∉ RHS-K.dom
  injL-∉-RHS-K-dom {g} g∉G v∈
    with ∈-++⁻ (map (_↑ˡ F.nV) G.dom) v∈
  ... | inj₁ v∈L =
    let mapped = ∈-map⁻ (_↑ˡ F.nV) v∈L
        g'     = proj₁ mapped
        g'∈G   = proj₁ (proj₂ mapped)
        eq     = proj₂ (proj₂ mapped)  -- g ↑ˡ F.nV ≡ g' ↑ˡ F.nV
    in g∉G (subst (_∈ G.dom) (sym (inject+-inj F.nV eq)) g'∈G)
  ... | inj₂ v∈R =
    let mapped = ∈-map⁻ (G.nV ↑ʳ_) v∈R
        f      = proj₁ mapped
        eq     = proj₂ (proj₂ mapped)  -- g ↑ˡ F.nV ≡ G.nV ↑ʳ f
        splitL : splitAt G.nV (g ↑ˡ F.nV) ≡ inj₁ g
        splitL = splitAt-↑ˡ G.nV g F.nV
        splitR : splitAt G.nV (g ↑ˡ F.nV) ≡ inj₂ f
        splitR = trans (cong (splitAt G.nV) eq) (splitAt-↑ʳ G.nV F.nV f)
        abs : inj₁ g ≡ inj₂ f
        abs = trans (sym splitL) splitR
    in case abs of λ ()
    where open import Function using (case_of_)

  -- Classify-inj₁ implies membership.
  classify-inj₁-∈
    : ∀ {v i} → classify RHS-K.dom v ≡ inj₁ i → v ∈ RHS-K.dom
  classify-inj₁-∈ {v} {i} eq =
    subst (_∈ RHS-K.dom) (classify-inj₁-lookup RHS-K.dom v i eq)
          (∈-lookup {xs = RHS-K.dom} i)

  -- φ⁻¹ reduction lemmas for boundary cases (F-side and G-side).
  -- Use nested dual-with to collapse both splitAt levels.

  φ⁻¹-F-bdy-red
    : (a : Fin nA)
    → φ⁻¹ ((a ↑ˡ nC) ↑ˡ count-non RHS-K.dom)
    ≡ (lookup F.dom (cast (sym F-dom-len) a) ↑ˡ G.nV) ↑ˡ count-non LHS-K.dom
  φ⁻¹-F-bdy-red a
    with splitAt RHS-G.nV ((a ↑ˡ nC) ↑ˡ count-non RHS-K.dom)
       | splitAt-↑ˡ RHS-G.nV (a ↑ˡ nC) (count-non RHS-K.dom)
  ... | .(inj₁ (a ↑ˡ nC)) | refl
    with splitAt nA (a ↑ˡ nC) | splitAt-↑ˡ nA a nC
  ...   | .(inj₁ a) | refl = refl

  φ⁻¹-G-bdy-red
    : (c' : Fin nC)
    → φ⁻¹ ((nA ↑ʳ c') ↑ˡ count-non RHS-K.dom)
    ≡ (F.nV ↑ʳ lookup G.dom (cast (sym G-dom-len) c')) ↑ˡ count-non LHS-K.dom
  φ⁻¹-G-bdy-red c'
    with splitAt RHS-G.nV ((nA ↑ʳ c') ↑ˡ count-non RHS-K.dom)
       | splitAt-↑ˡ RHS-G.nV (nA ↑ʳ c') (count-non RHS-K.dom)
  ... | .(inj₁ (nA ↑ʳ c')) | refl
    with splitAt nA (nA ↑ʳ c') | splitAt-↑ʳ nA nC c'
  ...   | .(inj₂ c') | refl = refl

  -- φ-left-bdy: case-split v' via splitAt F.nV, then classify F.dom / G.dom
  -- to get pos_F / pos_G.  The inj₂ (not-in-dom) cases derive ⊥ via the
  -- contradiction helpers (injR-∉-RHS-K-dom, injL-∉-RHS-K-dom) + classify-inj₂-∉
  -- + classify-inj₁-∈.  The in-dom cases use remapP-F-bdy / remapP-G-bdy
  -- + cast-cancel via cast-trans + cast-is-id, then φ⁻¹-F-bdy-red / -G-bdy-red
  -- + classify-inj₁-lookup for F.dom / G.dom.

  φ-left-bdy
    : (v' : Fin LHS-G.nV) (i : Fin (length RHS-K.dom))
    → classify RHS-K.dom (ψ-swap {F.nV} {G.nV} v') ≡ inj₁ i
    → φ⁻¹ (hRHS.remapP (ψ-swap {F.nV} {G.nV} v'))
    ≡ v' ↑ˡ count-non LHS-K.dom
  -- Note: after `with splitAt F.nV v'`, Agda reduces `ψ-swap v'` via
  -- internal with-hoisting to `G.nV ↑ʳ f` (inj₁) or `g ↑ˡ F.nV` (inj₂),
  -- so no `cong ψ-swap ...` bridge is needed.
  φ-left-bdy v' i cv-eq with splitAt F.nV v' in ev-v'
  ... | inj₁ f with classify F.dom f in cf
  ...   | inj₁ a =
    let lookup-eq : lookup F.dom a ≡ f
        lookup-eq = classify-inj₁-lookup F.dom f a cf
        cast-cancel : cast (sym F-dom-len) (cast F-dom-len a) ≡ a
        cast-cancel =
          trans (cast-trans F-dom-len (sym F-dom-len) a)
                (cast-is-id (trans F-dom-len (sym F-dom-len)) a)
    in trans (cong (λ v → φ⁻¹ (hRHS.remapP (G.nV ↑ʳ v))) (sym lookup-eq))
       (trans (cong φ⁻¹ (remapP-F-bdy a))
       (trans (φ⁻¹-F-bdy-red (cast F-dom-len a))
       (trans (cong (λ x → (lookup F.dom x ↑ˡ G.nV) ↑ˡ count-non LHS-K.dom)
                    cast-cancel)
       (trans (cong (λ x → (x ↑ˡ G.nV) ↑ˡ count-non LHS-K.dom) lookup-eq)
              (cong (_↑ˡ count-non LHS-K.dom) (splitAt⁻¹-↑ˡ ev-v'))))))
  ...   | inj₂ j-F =
    ⊥-elim (injR-∉-RHS-K-dom (classify-inj₂-∉ cf) (classify-inj₁-∈ cv-eq))
  φ-left-bdy v' i cv-eq | inj₂ g with classify G.dom g in cg
  ...   | inj₁ c' =
    let lookup-eq : lookup G.dom c' ≡ g
        lookup-eq = classify-inj₁-lookup G.dom g c' cg
        cast-cancel : cast (sym G-dom-len) (cast G-dom-len c') ≡ c'
        cast-cancel =
          trans (cast-trans G-dom-len (sym G-dom-len) c')
                (cast-is-id (trans G-dom-len (sym G-dom-len)) c')
    in trans (cong (λ v → φ⁻¹ (hRHS.remapP (v ↑ˡ F.nV))) (sym lookup-eq))
       (trans (cong φ⁻¹ (remapP-G-bdy c'))
       (trans (φ⁻¹-G-bdy-red (cast G-dom-len c'))
       (trans (cong (λ x → (F.nV ↑ʳ lookup G.dom x) ↑ˡ count-non LHS-K.dom)
                    cast-cancel)
       (trans (cong (λ x → (F.nV ↑ʳ x) ↑ˡ count-non LHS-K.dom) lookup-eq)
              (cong (_↑ˡ count-non LHS-K.dom) (splitAt⁻¹-↑ʳ ev-v'))))))
  ...   | inj₂ j-G =
    ⊥-elim (injL-∉-RHS-K-dom (classify-inj₂-∉ cg) (classify-inj₁-∈ cv-eq))

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

  -- φ-rght-bdy: chain via splitAt⁻¹-↑ˡ to rewrite w into the canonical
  -- (a ↑ˡ nC) ↑ˡ _ form, then apply φ⁻¹-F-bdy-red + φ-inj₁-red +
  -- ψ-swap-inj₁-red + remapP-F-bdy + cast-cancel.
  φ-rght-bdy
    : (w : Fin RHS.nV) (c : Fin RHS-G.nV)
    → splitAt RHS-G.nV w ≡ inj₁ c
    → φ (φ⁻¹ w) ≡ w
  φ-rght-bdy w c eq with splitAt nA c in ec
  ... | inj₁ a =
    let pos_F = cast (sym F-dom-len) a
        v_F   = lookup F.dom pos_F
        cast-cancel : cast F-dom-len pos_F ≡ a
        cast-cancel =
          trans (cast-trans (sym F-dom-len) F-dom-len a)
                (cast-is-id (trans (sym F-dom-len) F-dom-len) a)
        w-eq : (a ↑ˡ nC) ↑ˡ count-non RHS-K.dom ≡ w
        w-eq = trans (cong (_↑ˡ count-non RHS-K.dom) (splitAt⁻¹-↑ˡ ec))
                     (splitAt⁻¹-↑ˡ eq)
    in trans (cong (λ w' → φ (φ⁻¹ w')) (sym w-eq))
       (trans (cong φ (φ⁻¹-F-bdy-red a))
       (trans (φ-inj₁-red (v_F ↑ˡ G.nV))
       (trans (cong hRHS.remapP (ψ-swap-inj₁-red {F.nV} {G.nV} v_F))
       (trans (remapP-F-bdy pos_F)
       (trans (cong (λ x → (x ↑ˡ nC) ↑ˡ count-non RHS-K.dom) cast-cancel)
              w-eq)))))
  ... | inj₂ c' =
    let pos_G = cast (sym G-dom-len) c'
        v_G   = lookup G.dom pos_G
        cast-cancel : cast G-dom-len pos_G ≡ c'
        cast-cancel =
          trans (cast-trans (sym G-dom-len) G-dom-len c')
                (cast-is-id (trans (sym G-dom-len) G-dom-len) c')
        w-eq : (nA ↑ʳ c') ↑ˡ count-non RHS-K.dom ≡ w
        w-eq = trans (cong (_↑ˡ count-non RHS-K.dom) (splitAt⁻¹-↑ʳ ec))
                     (splitAt⁻¹-↑ˡ eq)
    in trans (cong (λ w' → φ (φ⁻¹ w')) (sym w-eq))
       (trans (cong φ (φ⁻¹-G-bdy-red c'))
       (trans (φ-inj₁-red (F.nV ↑ʳ v_G))
       (trans (cong hRHS.remapP (ψ-swap-inj₂-red {F.nV} {G.nV} v_G))
       (trans (remapP-G-bdy pos_G)
       (trans (cong (λ x → (nA ↑ʳ x) ↑ˡ count-non RHS-K.dom) cast-cancel)
              w-eq)))))

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

  -- (ψ-swap-inj{₁,₂}-red moved up near ψ-swap so they're available in
  -- the vertex bijection's boundary proofs.)

  -- subst₂ helpers moved to `CoherenceHelpers`; imported at the top.

  private
    -- Naturality of `hRHS.map-via-remapP` in its list argument.  For
    -- any `p : xs₁ ≡ xs₂`, the square commutes:
    --
    --   map RHS-K.vlab xs₁  ━━(map-via-remapP xs₁)━━▶  map RHS.vlab (map hRHS.remapP xs₁)
    --          │                                                   │
    --   cong (map RHS-K.vlab) p                      cong (map RHS.vlab ∘ map hRHS.remapP) p
    --          ▼                                                   ▼
    --   map RHS-K.vlab xs₂  ━━(map-via-remapP xs₂)━━▶  map RHS.vlab (map hRHS.remapP xs₂)
    --
    -- Proved by pattern-matching p = refl + trans-reflʳ.
    map-via-remapP-natural
      : ∀ {xs₁ xs₂ : List (Fin RHS-K.nV)} (p : xs₁ ≡ xs₂)
      → trans (hRHS.map-via-remapP xs₁)
              (cong (map RHS.vlab) (cong (map hRHS.remapP) p))
      ≡ trans (cong (map RHS-K.vlab) p) (hRHS.map-via-remapP xs₂)
    map-via-remapP-natural refl = trans-reflʳ (hRHS.map-via-remapP _)

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

  -- ψ-elab.  Case-by-case chain using the foundations above.
  --
  -- For the F-edge branch (splitAt F.nE eLG = inj₁ fE):
  --   atom-ein = trans A (trans (sym β̄) (trans (sym γ) (trans D E)))
  -- Chain:
  --   Σ₁: sym (subst₂-trans A rest …) — split A off outer
  --   Σ₂: subst₂-trans β̄o A …        — combine inner β̄o + A
  --   Σ₃: cong₂ … nat nat'           — nat: trans β̄o A ≡ trans π β̄
  --   Σ₄: sym (subst₂-trans π β̄ …)   — split π off
  --   Σ₅: cong … hTR.elab-c-inj₂ fE  — RHS-K.elab → subst₂ γ (F.elab fE)
  --   Σ₆: sym (subst₂-trans (sym β̄) rest₂ …) — split (sym β̄) off
  --   Σ₇: subst₂-sym-subst₂ β̄ β̄'     — cancel β̄ + sym β̄
  --   Σ₈: sym (subst₂-trans (sym γ) (trans D E) …) — split (sym γ) off
  --   Σ₉: subst₂-sym-subst₂ γ γ'     — cancel γ + sym γ
  --   Σ₁₀: sym (subst₂-trans D E …)  — split (trans D E) back into D then E
  --         which matches LHS.elab e (definitional in the with context).

  ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e)
                                 (RHS.elab (ψ e))
               ≡ LHS.elab e
  ψ-elab e with splitAt LHS-G.nE e
  ... | inj₂ absurd = ⊥-elim (Fin-zero-absurd LHS-K-nE≡0 absurd)
  ... | inj₁ eLG with splitAt F.nE eLG
  ...   | inj₁ fE =
    let
      A   = cong (map RHS.vlab) (cong (map hRHS.remapP) (hTR.ein-c-inj₂-red  fE))
      A'  = cong (map RHS.vlab) (cong (map hRHS.remapP) (hTR.eout-c-inj₂-red fE))
      β̄   = hRHS.map-via-remapP (map hTR.injR (F.ein  fE))
      β̄'  = hRHS.map-via-remapP (map hTR.injR (F.eout fE))
      β̄o  = hRHS.map-via-remapP (RHS-K.ein  (G.nE ↑ʳ fE))
      β̄o' = hRHS.map-via-remapP (RHS-K.eout (G.nE ↑ʳ fE))
      π   = cong (map RHS-K.vlab) (hTR.ein-c-inj₂-red  fE)
      π'  = cong (map RHS-K.vlab) (hTR.eout-c-inj₂-red fE)
      γ   = map-via-raise hTR.vlab-injR (F.ein  fE)
      γ'  = map-via-raise hTR.vlab-injR (F.eout fE)
      D   = map-via-inj   hTL.vlab-injL (F.ein  fE)
      D'  = map-via-inj   hTL.vlab-injL (F.eout fE)
      E   = map-via-inj   hLHS.vlab-injL (map hTL.injL (F.ein  fE))
      E'  = map-via-inj   hLHS.vlab-injL (map hTL.injL (F.eout fE))
      rest1  = trans (sym β̄) (trans (sym γ) (trans D E))
      rest1' = trans (sym β̄') (trans (sym γ') (trans D' E'))
      rest2  = trans (sym γ) (trans D E)
      rest2' = trans (sym γ') (trans D' E')
      z   = RHS-K.elab (G.nE ↑ʳ fE)
      nat  : trans β̄o  A  ≡ trans π  β̄
      nat  = map-via-remapP-natural (hTR.ein-c-inj₂-red  fE)
      nat' : trans β̄o' A' ≡ trans π' β̄'
      nat' = map-via-remapP-natural (hTR.eout-c-inj₂-red fE)
      -- Sub-chain: subst₂ A A' (subst₂ β̄o β̄o' z)
      --         ≡ subst₂ β̄ β̄' (subst₂ γ γ' (F.elab fE))
      step-inner : subst₂ FlatGen A A' (subst₂ FlatGen β̄o β̄o' z)
                 ≡ subst₂ FlatGen β̄ β̄' (subst₂ FlatGen γ γ' (F.elab fE))
      step-inner =
        trans (subst₂-trans β̄o A β̄o' A' z)
        (trans (cong₂ (λ p q → subst₂ FlatGen p q z) nat nat')
        (trans (sym (subst₂-trans π β̄ π' β̄' z))
               (cong (subst₂ FlatGen β̄ β̄') (hTR.elab-c-inj₂ fE))))
    in
      trans (sym (subst₂-trans A rest1 A' rest1'
                    (subst₂ FlatGen β̄o β̄o' z)))
      (trans (cong (subst₂ FlatGen rest1 rest1') step-inner)
      (trans (sym (subst₂-trans (sym β̄) rest2 (sym β̄') rest2'
                    (subst₂ FlatGen β̄ β̄' (subst₂ FlatGen γ γ' (F.elab fE)))))
      (trans (cong (subst₂ FlatGen rest2 rest2')
                   (subst₂-sym-subst₂ β̄ β̄' (subst₂ FlatGen γ γ' (F.elab fE))))
      (trans (sym (subst₂-trans (sym γ) (trans D E) (sym γ') (trans D' E')
                    (subst₂ FlatGen γ γ' (F.elab fE))))
      (trans (cong (subst₂ FlatGen (trans D E) (trans D' E'))
                   (subst₂-sym-subst₂ γ γ' (F.elab fE)))
             (sym (subst₂-trans D E D' E' (F.elab fE))))))))
  ...   | inj₂ gE =
    -- G-edge case mirrors F-edge: ψ-swap's inj₂ gives gE ↑ˡ F.nE;
    -- RHS-K uses hTR.ein-c-inj₁-red (injL side of hTensor G F) instead.
    let
      A   = cong (map RHS.vlab) (cong (map hRHS.remapP) (hTR.ein-c-inj₁-red  gE))
      A'  = cong (map RHS.vlab) (cong (map hRHS.remapP) (hTR.eout-c-inj₁-red gE))
      β̄   = hRHS.map-via-remapP (map hTR.injL (G.ein  gE))
      β̄'  = hRHS.map-via-remapP (map hTR.injL (G.eout gE))
      β̄o  = hRHS.map-via-remapP (RHS-K.ein  (gE ↑ˡ F.nE))
      β̄o' = hRHS.map-via-remapP (RHS-K.eout (gE ↑ˡ F.nE))
      π   = cong (map RHS-K.vlab) (hTR.ein-c-inj₁-red  gE)
      π'  = cong (map RHS-K.vlab) (hTR.eout-c-inj₁-red gE)
      γ   = map-via-inj   hTR.vlab-injL (G.ein  gE)
      γ'  = map-via-inj   hTR.vlab-injL (G.eout gE)
      D   = map-via-raise hTL.vlab-injR (G.ein  gE)
      D'  = map-via-raise hTL.vlab-injR (G.eout gE)
      E   = map-via-inj   hLHS.vlab-injL (map hTL.injR (G.ein  gE))
      E'  = map-via-inj   hLHS.vlab-injL (map hTL.injR (G.eout gE))
      rest1  = trans (sym β̄) (trans (sym γ) (trans D E))
      rest1' = trans (sym β̄') (trans (sym γ') (trans D' E'))
      rest2  = trans (sym γ) (trans D E)
      rest2' = trans (sym γ') (trans D' E')
      z   = RHS-K.elab (gE ↑ˡ F.nE)
      nat  : trans β̄o  A  ≡ trans π  β̄
      nat  = map-via-remapP-natural (hTR.ein-c-inj₁-red  gE)
      nat' : trans β̄o' A' ≡ trans π' β̄'
      nat' = map-via-remapP-natural (hTR.eout-c-inj₁-red gE)
      step-inner : subst₂ FlatGen A A' (subst₂ FlatGen β̄o β̄o' z)
                 ≡ subst₂ FlatGen β̄ β̄' (subst₂ FlatGen γ γ' (G.elab gE))
      step-inner =
        trans (subst₂-trans β̄o A β̄o' A' z)
        (trans (cong₂ (λ p q → subst₂ FlatGen p q z) nat nat')
        (trans (sym (subst₂-trans π β̄ π' β̄' z))
               (cong (subst₂ FlatGen β̄ β̄') (hTR.elab-c-inj₁ gE))))
    in
      trans (sym (subst₂-trans A rest1 A' rest1'
                    (subst₂ FlatGen β̄o β̄o' z)))
      (trans (cong (subst₂ FlatGen rest1 rest1') step-inner)
      (trans (sym (subst₂-trans (sym β̄) rest2 (sym β̄') rest2'
                    (subst₂ FlatGen β̄ β̄' (subst₂ FlatGen γ γ' (G.elab gE)))))
      (trans (cong (subst₂ FlatGen rest2 rest2')
                   (subst₂-sym-subst₂ β̄ β̄' (subst₂ FlatGen γ γ' (G.elab gE))))
      (trans (sym (subst₂-trans (sym γ) (trans D E) (sym γ') (trans D' E')
                    (subst₂ FlatGen γ γ' (G.elab gE))))
      (trans (cong (subst₂ FlatGen (trans D E) (trans D' E'))
                   (subst₂-sym-subst₂ γ γ' (G.elab gE)))
             (sym (subst₂-trans D E D' E' (G.elab gE))))))))

  --------------------------------------------------------------------------
  -- φ-dom: list-wise compatibility of the dom boundary.
  --
  -- LHS.dom = map hLHS.injL (map hTL.injL F.dom ++ map hTL.injR G.dom)
  --         (definitional: hComposeP.dom = map injL G.dom; hTensor.dom = ...).
  -- RHS.dom = map hRHS.injL (map (_↑ˡ nC) (range nA) ++ map (nA ↑ʳ_) (range nC))
  --         (definitional: hSwap A C.dom covers).
  --
  -- For each f ∈ F.dom (at position pos_F : Fin (length F.dom)):
  --   φ (hLHS.injL (hTL.injL (lookup F.dom pos_F)))
  --   = hRHS.remapP (G.nV ↑ʳ lookup F.dom pos_F)  (φ-inj₁-red + ψ-swap-inj₁-red)
  --   = (cast F-dom-len pos_F ↑ˡ nC) ↑ˡ count-non RHS-K.dom   (remapP-F-bdy)
  -- After reindexing F.dom via `map (lookup F.dom) (range (length F.dom))`
  -- and applying `map-cast-range F-dom-len`, the F-half becomes
  -- `map ((_↑ˡ count-non RHS-K.dom) ∘ (_↑ˡ nC)) (range nA) = RHS.dom's A-half`.
  -- G-half is symmetric.

  -- Polymorphic `map-lookup-range` (FromAPROP's version is restricted to
  -- the APROP label type `List X`).
  private
    map-lookup-range'
      : ∀ {a} {A : Set a} (xs : List A)
      → map (lookup xs) (range (length xs)) ≡ xs
    map-lookup-range' [] = refl
    map-lookup-range' (x ∷ xs) =
      cong (x ∷_)
        (trans (sym (map-∘ (range (length xs))))
               (map-lookup-range' xs))

    -- F-half pointwise reduction: (φ ∘ hLHS.injL ∘ hTL.injL) ∘ lookup F.dom
    -- pointwise equals (the RHS-G A-half function) ∘ cast F-dom-len.
    F-half-point
      : ∀ (pos_F : Fin (length F.dom))
      → φ (hLHS.injL (hTL.injL (lookup F.dom pos_F)))
      ≡ (cast F-dom-len pos_F ↑ˡ nC) ↑ˡ count-non RHS-K.dom
    F-half-point pos_F =
      trans (φ-inj₁-red (lookup F.dom pos_F ↑ˡ G.nV))
      (trans (cong hRHS.remapP
                   (ψ-swap-inj₁-red {F.nV} {G.nV} (lookup F.dom pos_F)))
             (remapP-F-bdy pos_F))

    G-half-point
      : ∀ (pos_G : Fin (length G.dom))
      → φ (hLHS.injL (hTL.injR (lookup G.dom pos_G)))
      ≡ (nA ↑ʳ cast G-dom-len pos_G) ↑ˡ count-non RHS-K.dom
    G-half-point pos_G =
      trans (φ-inj₁-red (F.nV ↑ʳ lookup G.dom pos_G))
      (trans (cong hRHS.remapP
                   (ψ-swap-inj₂-red {F.nV} {G.nV} (lookup G.dom pos_G)))
             (remapP-G-bdy pos_G))

    -- F-half chain: map φ (map hLHS.injL (map hTL.injL F.dom))
    --             ≡ map ((_↑ˡ _) ∘ (_↑ˡ nC)) (range nA).
    map-φ-F-half
      : map φ (map hLHS.injL (map hTL.injL F.dom))
      ≡ map (λ a → (a ↑ˡ nC) ↑ˡ count-non RHS-K.dom) (range nA)
    map-φ-F-half =
      trans (sym (map-∘ (map hTL.injL F.dom)))
      (trans (sym (map-∘ F.dom))
      (trans (cong (map (λ f → φ (hLHS.injL (hTL.injL f))))
                   (sym (map-lookup-range' F.dom)))
      (trans (sym (map-∘ (range (length F.dom))))
      (trans (map-cong F-half-point (range (length F.dom)))
      (trans (map-∘ (range (length F.dom)))
             (cong (map (λ a → (a ↑ˡ nC) ↑ˡ count-non RHS-K.dom))
                   (map-cast-range F-dom-len)))))))

    map-φ-G-half
      : map φ (map hLHS.injL (map hTL.injR G.dom))
      ≡ map (λ c → (nA ↑ʳ c) ↑ˡ count-non RHS-K.dom) (range nC)
    map-φ-G-half =
      trans (sym (map-∘ (map hTL.injR G.dom)))
      (trans (sym (map-∘ G.dom))
      (trans (cong (map (λ g → φ (hLHS.injL (hTL.injR g))))
                   (sym (map-lookup-range' G.dom)))
      (trans (sym (map-∘ (range (length G.dom))))
      (trans (map-cong G-half-point (range (length G.dom)))
      (trans (map-∘ (range (length G.dom)))
             (cong (map (λ c → (nA ↑ʳ c) ↑ˡ count-non RHS-K.dom))
                   (map-cast-range G-dom-len)))))))

  -- Assemble φ-dom.  LHS.dom = map hLHS.injL LHS-G.dom reduces via
  -- map-++ to map hLHS.injL (F-half ++ G-half), then map φ distributes.
  -- Each half matches RHS.dom's half via map-φ-F-half / map-φ-G-half.
  private
    -- Bridge the final map-∘ between the "λ a → …" form used in
    -- map-φ-F-half and the explicit "_↑ˡ _" form used in RHS.dom.
    F-half-reassoc
      : map (λ a → (a ↑ˡ nC) ↑ˡ count-non RHS-K.dom) (range nA)
      ≡ map (_↑ˡ count-non RHS-K.dom) (map (_↑ˡ nC) (range nA))
    F-half-reassoc = map-∘ (range nA)

    G-half-reassoc
      : map (λ c → (nA ↑ʳ c) ↑ˡ count-non RHS-K.dom) (range nC)
      ≡ map (_↑ˡ count-non RHS-K.dom) (map (nA ↑ʳ_) (range nC))
    G-half-reassoc = map-∘ (range nC)

  φ-dom : RHS.dom ≡ map φ LHS.dom
  φ-dom = sym
    (trans (cong (map φ) (map-++ hLHS.injL (map hTL.injL F.dom)
                                           (map hTL.injR G.dom)))
    (trans (map-++ φ (map hLHS.injL (map hTL.injL F.dom))
                     (map hLHS.injL (map hTL.injR G.dom)))
    (trans (cong₂ _++_ (trans map-φ-F-half F-half-reassoc)
                       (trans map-φ-G-half G-half-reassoc))
           (sym (map-++ hRHS.injL (map (_↑ˡ nC) (range nA))
                                   (map (nA ↑ʳ_) (range nC)))))))

  --------------------------------------------------------------------------
  -- φ-cod: list-wise compatibility of the cod boundary.
  --
  -- LHS.cod = map hLHS.remapP ((hSwap B D).cod)
  --         = map hLHS.remapP (map (nB ↑ʳ_) (range nD) ++ map (_↑ˡ nD) (range nB))
  -- RHS.cod = map hRHS.remapP ((hTensor G F).cod)
  --         = map hRHS.remapP (map hTR.injL G.cod ++ map hTR.injR F.cod)
  --         = map hRHS.remapP (map (_↑ˡ F.nV) G.cod ++ map (G.nV ↑ʳ_) F.cod)
  --
  -- The D-half (range nD, indexed by d) on LHS maps (via remapP-LHS-D +
  -- φ-inj₁-red + ψ-swap-inj₂-red) to `hRHS.remapP (lookup G.cod _ ↑ˡ F.nV)`,
  -- which after reindexing (map-cast-range + map-lookup-range') becomes
  -- `map (hRHS.remapP ∘ (_↑ˡ F.nV)) G.cod` = RHS.cod's G-half.  Symmetric for B-half.

  private
    -- D-half pointwise reduction.
    D-half-point
      : ∀ (d : Fin nD)
      → φ (hLHS.remapP (nB ↑ʳ d))
      ≡ hRHS.remapP (lookup G.cod (cast (sym G-cod-len) d) ↑ˡ F.nV)
    D-half-point d =
      trans (cong φ (remapP-LHS-D d))
      (trans (φ-inj₁-red
               (F.nV ↑ʳ lookup G.cod (cast (sym G-cod-len) d)))
             (cong hRHS.remapP
                   (ψ-swap-inj₂-red {F.nV} {G.nV}
                                     (lookup G.cod (cast (sym G-cod-len) d)))))

    B-half-point
      : ∀ (b : Fin nB)
      → φ (hLHS.remapP (b ↑ˡ nD))
      ≡ hRHS.remapP (G.nV ↑ʳ lookup F.cod (cast (sym F-cod-len) b))
    B-half-point b =
      trans (cong φ (remapP-LHS-B b))
      (trans (φ-inj₁-red
               (lookup F.cod (cast (sym F-cod-len) b) ↑ˡ G.nV))
             (cong hRHS.remapP
                   (ψ-swap-inj₁-red {F.nV} {G.nV}
                                     (lookup F.cod (cast (sym F-cod-len) b)))))

    -- D-half chain: map φ (map hLHS.remapP (map (nB ↑ʳ_) (range nD)))
    --             ≡ map hRHS.remapP (map hTR.injL G.cod).
    map-φ-cod-D-half
      : map φ (map hLHS.remapP (map (nB ↑ʳ_) (range nD)))
      ≡ map hRHS.remapP (map hTR.injL G.cod)
    map-φ-cod-D-half =
      trans (sym (map-∘ (map (nB ↑ʳ_) (range nD))))
      (trans (sym (map-∘ (range nD)))
      (trans (map-cong D-half-point (range nD))
      (trans (map-∘ (range nD))
      (trans (cong (map (λ g → hRHS.remapP (g ↑ˡ F.nV)))
                   (trans (map-∘ (range nD))
                   (trans (cong (map (lookup G.cod))
                                (map-cast-range (sym G-cod-len)))
                          (map-lookup-range' G.cod))))
             (map-∘ G.cod)))))

    map-φ-cod-B-half
      : map φ (map hLHS.remapP (map (_↑ˡ nD) (range nB)))
      ≡ map hRHS.remapP (map hTR.injR F.cod)
    map-φ-cod-B-half =
      trans (sym (map-∘ (map (_↑ˡ nD) (range nB))))
      (trans (sym (map-∘ (range nB)))
      (trans (map-cong B-half-point (range nB))
      (trans (map-∘ (range nB))
      (trans (cong (map (λ f → hRHS.remapP (G.nV ↑ʳ f)))
                   (trans (map-∘ (range nB))
                   (trans (cong (map (lookup F.cod))
                                (map-cast-range (sym F-cod-len)))
                          (map-lookup-range' F.cod))))
             (map-∘ F.cod)))))

  φ-cod : RHS.cod ≡ map φ LHS.cod
  φ-cod = sym
    (trans (cong (map φ) (map-++ hLHS.remapP
                                  (map (nB ↑ʳ_) (range nD))
                                  (map (_↑ˡ nD) (range nB))))
    (trans (map-++ φ (map hLHS.remapP (map (nB ↑ʳ_) (range nD)))
                     (map hLHS.remapP (map (_↑ˡ nD) (range nB))))
    (trans (cong₂ _++_ map-φ-cod-D-half map-φ-cod-B-half)
           (sym (map-++ hRHS.remapP (map hTR.injL G.cod)
                                     (map hTR.injR F.cod))))))

  postulate
    φ-lab   : ∀ v → RHS.vlab (φ v) ≡ LHS.vlab v
    ψ-ein   : ∀ e → RHS.ein (ψ e) ≡ map φ (LHS.ein e)
    ψ-eout  : ∀ e → RHS.eout (ψ e) ≡ map φ (LHS.eout e)

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
