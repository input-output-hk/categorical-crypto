{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- FEASIBILITY SPIKE: run the *matrix* coherence representation on a
-- *hypergraph*, by translating between the two worlds.
--
--   hg→mat  : Hypergraph FlatGen → BlockMatrix Bool …      (incidence encoding)
--   align   : (H J) → candidate (φ , ψ) bijections          (CANONICAL read)
--   matIso→hgIso : (φ , ψ) → H ≅ᴴ J                          (record assembly)
--
-- `align` is now a REAL canonical-labelling read (no backtracking search):
-- it computes a canonical DAG labelling of each hypergraph and reads the
-- bijection off the canonical ranks.  See §2.  The proof fields of `_≅ᴴ_`
-- (vlab/ein/eout/dom/cod/elab agreement) remain POSTULATED — this spike
-- validates the *data flow* and `align`'s computational correctness (the
-- demo discharges the incidence conditions by `refl` on a concrete
-- non-identity example); it does not yet *prove* preservation in general.
--
-- Drops `--safe` (postulates + brings in the matrix world); the underlying
-- hypergraph modules remain `--safe --without-K`.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.MatrixBridge
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

-- The matrix world (brought over from branch `smc-coherence`).
open import Categories.SymmetricMonoidalCoherence.Matrix
  using (Matrix; tabulateM; BlockMatrix; RowG; ColG; v⁻; v⁺; t⁺; t⁻;
         module Sizes)

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; length; lookup; map; _++_; foldr)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    H J : Hypergraph FlatGen

--------------------------------------------------------------------------------
-- §1.  hg→mat : encode a hypergraph's incidence as a `BlockMatrix Bool`.
--
-- INDEX CORRESPONDENCE (the documented choice):
--
--   * Row group `v⁻`    : the `length H.dom` domain boundary wires.
--   * Row group `t⁺ e`  : the `length (H.eout e)` output ports of edge `e`.
--   * Col group `t⁻ e`  : the `length (H.ein e)`  input  ports of edge `e`.
--   * Col group `v⁺`    : the `length H.cod` codomain boundary wires.
--
-- Each *index* of a row/column group is BACKED BY a hypergraph vertex
-- (`Fin H.nV`), via `lookup`:
--
--   v⁻ row  i ↦ lookup H.dom    i      (a `Fin H.nV`)
--   t⁺ e    i ↦ lookup (H.eout e) i
--   t⁻ e    j ↦ lookup (H.ein  e) j
--   v⁺ col  j ↦ lookup H.cod    j
--
-- The Bool entry of block (r,c) at (i,j) is `true` iff the vertex backing
-- the row endpoint equals the vertex backing the column endpoint.  That is
-- the *incidence*: a `true` says "this row wire and this column wire are the
-- SAME vertex" — i.e. that vertex feeds from one side and into the other.
-- The full BlockMatrix therefore records the complete wiring of the
-- hypergraph relative to its boundary + ports.

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- Block sizes.
  sA : ℕ
  sA = length H.dom
  sB : ℕ
  sB = length H.cod
  ds : Fin H.nE → ℕ
  ds e = length (H.ein e)
  cs : Fin H.nE → ℕ
  cs e = length (H.eout e)

  open Sizes sA sB ds cs

  -- The vertex (`Fin H.nV`) backing a row index of group `r`.
  rowVtx : (r : RowG H.nE) → Fin (rSz r) → Fin H.nV
  rowVtx v⁻     i = lookup H.dom i
  rowVtx (t⁺ e) i = lookup (H.eout e) i

  -- The vertex backing a column index of group `c`.
  colVtx : (c : ColG H.nE) → Fin (cSz c) → Fin H.nV
  colVtx (t⁻ e) j = lookup (H.ein e) j
  colVtx v⁺     j = lookup H.cod j

  -- Incidence entry: do the row/column endpoints name the same vertex?
  same? : Fin H.nV → Fin H.nV → Bool
  same? u v with u ≟F v
  ... | yes _ = true
  ... | no  _ = false

  hg→mat : BlockMatrix sA sB H.nE ds cs
  hg→mat r c = tabulateM (λ i j → same? (rowVtx r i) (colVtx c j))

--------------------------------------------------------------------------------
-- §2.  Canonical alignment via DAG canonical labelling (NO search).
--
-- The input hypergraphs are `⟪_⟫`-translations: monogamous (each wire
-- produced once / consumed once) and acyclic.  We compute a canonical
-- labelling of each one and read the bijection straight off the canonical
-- ranks.  This is the "canonical form, no backtracking" idea made real.
--
-- ALGORITHM (per hypergraph H):
--
--   1.  Canonical VERTEX order seeds with `H.dom` (boundary inputs, in
--       order).  Subsequently, vertices enter in the order their producing
--       edge is canonically peeled (every non-dom vertex is some edge's
--       output, by monogamy).
--
--   2.  Canonical EDGE order is a topological peel: repeatedly take an edge
--       all of whose input vertices are ALREADY ranked (boundary or an
--       output of an already-peeled edge).  Among the ready edges, break
--       ties by an INTRINSIC signature: the sorted list of the
--       already-assigned canonical ranks of the edge's input vertices.  The
--       tie-break uses ONLY ranks (intrinsic structural data), never the raw
--       `Fin` edge index — so two isomorphic graphs with different index
--       layouts get the SAME canonical edge order.
--
--   3.  After peeling an edge, append its `eout` vertices (in `eout` order)
--       to the canonical vertex order.
--
--   The two canonical orders `canonV`/`canonE` are permutations of
--   `Fin H.nV` / `Fin H.nE`.  The alignment is then
--
--       φ v = canonV J ‼ rank of v in canonV H
--       ψ e = canonE J ‼ rank of e in canonE H
--
--   i.e. "the J-vertex/edge sitting at the same canonical slot".  This is a
--   genuine computation (it produces a NON-identity permutation whenever the
--   two layouts differ); it is NOT proven to be a bijection here.
--
-- TIE-BREAK SCOPE.  The signature distinguishes ready edges by which
-- already-ranked vertices they consume.  It is fully intrinsic and correctly
-- canonicalises any two graphs in which the ready edges at every peel step
-- consume DISTINCT rank-multisets of inputs — in particular the σ-naturality
-- example (the two generators read distinct boundary wires).  It does NOT
-- distinguish two ready edges that consume the *identical* input-rank
-- multiset (genuine automorphisms / parallel edges with equal arities); for
-- those a generator-label code would be needed.  See the report.

private
  -- All indices of `Fin n`, in order: 0, 1, …, n-1.
  allFins : (n : ℕ) → List (Fin n)
  allFins zero    = []
  allFins (suc n) = zero ∷ map suc (allFins n)

  -- Lexicographic strict comparison of `ℕ` lists ("is xs < ys?").
  ltList : List ℕ → List ℕ → Bool
  ltList []       []       = false
  ltList []       (_ ∷ _)  = true
  ltList (_ ∷ _)  []       = false
  ltList (x ∷ xs) (y ∷ ys) =
    (x <ᵇ y) ∨ ((x ≡ᵇ y) ∧ ltList xs ys)

  -- Insertion sort of an `ℕ` list (ascending).  Used to make the
  -- input-rank signature order-independent.
  insert-sorted : ℕ → List ℕ → List ℕ
  insert-sorted x []       = x ∷ []
  insert-sorted x (y ∷ ys) with x <ᵇ y
  ... | true  = x ∷ y ∷ ys
  ... | false = y ∷ insert-sorted x ys

  sortℕ : List ℕ → List ℕ
  sortℕ = foldr insert-sorted []

  -- Position of `v` in a `Fin`-list, as a ℕ; returns `length xs`
  -- (one-past-the-end, an "unranked" sentinel) when absent.
  posIn : ∀ {n} → List (Fin n) → Fin n → ℕ
  posIn []       _ = 0
  posIn (x ∷ xs) v with x ≟F v
  ... | yes _ = 0
  ... | no  _ = suc (posIn xs v)

  -- Membership test in a `Fin`-list.
  memberOf : ∀ {n} → List (Fin n) → Fin n → Bool
  memberOf []       _ = false
  memberOf (x ∷ xs) v with x ≟F v
  ... | yes _ = true
  ... | no  _ = memberOf xs v

  -- "Are all of `vs` present in `ranked`?"  (edge readiness)
  allMember : ∀ {n} → List (Fin n) → List (Fin n) → Bool
  allMember ranked []       = true
  allMember ranked (v ∷ vs) = memberOf ranked v ∧ allMember ranked vs

  -- The list lookup that DEFAULTS to its first arg when the index runs off
  -- the end (used only with in-range indices in practice).
  lookupD : ∀ {n} → Fin n → List (Fin n) → ℕ → Fin n
  lookupD d []       _       = d
  lookupD d (x ∷ _)  zero    = x
  lookupD d (_ ∷ xs) (suc i) = lookupD d xs i

module Canon (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open import Data.Product using (_×_; _,_; proj₁; proj₂)

  -- Signature of an edge given the current canonical vertex order
  -- `rankedV`: the SORTED list of canonical ranks of its input vertices.
  edgeSig : List (Fin H.nV) → Fin H.nE → List ℕ
  edgeSig rankedV e = sortℕ (map (posIn rankedV) (H.ein e))

  -- Is edge `e` ready to peel?  (all inputs already ranked, and e not yet
  -- peeled).  `peeled` : edges already in canonical order.  `rankedV` :
  -- vertices already ranked.
  ready? : List (Fin H.nE) → List (Fin H.nV) → Fin H.nE → Bool
  ready? peeled rankedV e =
    not (memberOf peeled e) ∧ allMember rankedV (H.ein e)

  open import Data.Maybe using (Maybe; just; nothing)

  -- Among the scanned `candidates`, pick the ready edge of minimal
  -- signature, carrying the best-so-far as a `Maybe (Fin nE × List ℕ)`.
  -- Returns `nothing` iff no candidate is ready (cannot happen on a
  -- well-formed acyclic monogamous DAG before all edges are peeled).
  pickMin : List (Fin H.nE) → List (Fin H.nV)
          → Maybe (Fin H.nE × List ℕ)    -- best edge so far + its sig
          → List (Fin H.nE)               -- candidates to scan
          → Maybe (Fin H.nE)
  pickMin peeled rankedV nothing             [] = nothing
  pickMin peeled rankedV (just (best , _))   [] = just best
  pickMin peeled rankedV acc (e ∷ es) with ready? peeled rankedV e
  ... | false = pickMin peeled rankedV acc es
  ... | true  with acc
  ...   | nothing = -- first ready edge: it's the new best
                    pickMin peeled rankedV (just (e , edgeSig rankedV e)) es
  ...   | just (best , bestSig) with ltList (edgeSig rankedV e) bestSig
  ...     | true  = pickMin peeled rankedV (just (e , edgeSig rankedV e)) es
  ...     | false = pickMin peeled rankedV (just (best , bestSig)) es

  -- One peel step: choose the minimal ready edge, append it to `peeled`,
  -- and append its outputs to `rankedV`.  If no edge is ready, the state is
  -- returned unchanged (so `peelN` is a no-op past the last peelable edge).
  step : List (Fin H.nE) × List (Fin H.nV)
       → List (Fin H.nE) × List (Fin H.nV)
  step (peeled , rankedV) with pickMin peeled rankedV nothing (allFins H.nE)
  ... | nothing = (peeled , rankedV)
  ... | just e  = (peeled ++ (e ∷ []) , rankedV ++ H.eout e)

  -- Iterate `step` `fuel` times (fuel = nE suffices: one edge per step).
  peelN : ℕ → List (Fin H.nE) × List (Fin H.nV)
        → List (Fin H.nE) × List (Fin H.nV)
  peelN zero    st = st
  peelN (suc k) st = peelN k (step st)

  -- Canonical orders.  The vertex order seeds with `H.dom`; the peel runs
  -- for `nE` steps (each step peels one edge).
  canonV-canonE : List (Fin H.nE) × List (Fin H.nV)
  canonV-canonE = peelN H.nE ([] , H.dom)

  canonE : List (Fin H.nE)
  canonE = proj₁ canonV-canonE

  canonV : List (Fin H.nV)
  canonV = proj₂ canonV-canonE

record Alignment (H J : Hypergraph FlatGen) : Set where
  field
    φ   : Fin (Hypergraph.nV H) → Fin (Hypergraph.nV J)
    φ⁻¹ : Fin (Hypergraph.nV J) → Fin (Hypergraph.nV H)
    ψ   : Fin (Hypergraph.nE H) → Fin (Hypergraph.nE J)
    ψ⁻¹ : Fin (Hypergraph.nE J) → Fin (Hypergraph.nE H)

-- The REAL canonical read.  `align H J` computes the canonical labellings of
-- both hypergraphs and composes H's rank with J's inverse-rank:
--
--   φ v  =  canonV J  at  (rank of v in canonV H)
--
-- This GENUINELY COMPUTES the aligning permutation.  No `nV ≡ nV` / `nE ≡ nE`
-- arguments are needed; the orders carry the layout information.
--
-- `lookupD` needs a well-typed default in the TARGET space, only ever forced
-- when a rank runs off the end (i.e. never, for in-range vertices/edges of
-- well-formed iso graphs).  Defaults are provided as the second explicit
-- argument of `align`; in the validating demo they are concrete `Fin`s.
align : (H J : Hypergraph FlatGen)
      → (dV  : Fin (Hypergraph.nV J)) (dV' : Fin (Hypergraph.nV H))
      → (dE  : Fin (Hypergraph.nE J)) (dE' : Fin (Hypergraph.nE H))
      → Alignment H J
align H J dV dV' dE dE' = record
  { φ   = λ v → lookupD dV  (Canon.canonV J) (posIn (Canon.canonV H) v)
  ; φ⁻¹ = λ v → lookupD dV' (Canon.canonV H) (posIn (Canon.canonV J) v)
  ; ψ   = λ e → lookupD dE  (Canon.canonE J) (posIn (Canon.canonE H) e)
  ; ψ⁻¹ = λ e → lookupD dE' (Canon.canonE H) (posIn (Canon.canonE J) e)
  }

--------------------------------------------------------------------------------
-- §3.  matIso→hgIso : turn an alignment into a hypergraph isomorphism.
--
-- The bijection FIELDS are filled from the alignment (genuine data).  The
-- proof FIELDS (label / endpoint / boundary / elab agreement) are POSTULATED
-- — preservation is explicitly deferred for this spike.  The point is that
-- the `_≅ᴴ_` record is *constructible* end-to-end.

module _ {H J : Hypergraph FlatGen} where
  private
    module H = Hypergraph H
    module J = Hypergraph J

  open import Data.List using (map)
  open import Relation.Binary.PropositionalEquality using (subst₂)

  postulate
    -- Deferred preservation proofs (the genuine mathematical content of a
    -- *proven* version).  Quantified over an alignment so they sit at the
    -- right types.
    align-φ-left  : (al : Alignment H J) → ∀ i → Alignment.φ⁻¹ al (Alignment.φ al i) ≡ i
    align-φ-rght  : (al : Alignment H J) → ∀ i → Alignment.φ al (Alignment.φ⁻¹ al i) ≡ i
    align-ψ-left  : (al : Alignment H J) → ∀ e → Alignment.ψ⁻¹ al (Alignment.ψ al e) ≡ e
    align-ψ-rght  : (al : Alignment H J) → ∀ e → Alignment.ψ al (Alignment.ψ⁻¹ al e) ≡ e
    align-φ-lab   : (al : Alignment H J) → ∀ i → J.vlab (Alignment.φ al i) ≡ H.vlab i
    align-ψ-ein   : (al : Alignment H J) → ∀ e →
                    J.ein  (Alignment.ψ al e) ≡ map (Alignment.φ al) (H.ein e)
    align-ψ-eout  : (al : Alignment H J) → ∀ e →
                    J.eout (Alignment.ψ al e) ≡ map (Alignment.φ al) (H.eout e)
    align-φ-dom   : (al : Alignment H J) → J.dom ≡ map (Alignment.φ al) H.dom
    align-φ-cod   : (al : Alignment H J) → J.cod ≡ map (Alignment.φ al) H.cod
    align-atom-ein  : (al : Alignment H J) → ∀ e →
                      map J.vlab (J.ein  (Alignment.ψ al e)) ≡ map H.vlab (H.ein e)
    align-atom-eout : (al : Alignment H J) → ∀ e →
                      map J.vlab (J.eout (Alignment.ψ al e)) ≡ map H.vlab (H.eout e)
    align-ψ-elab : (al : Alignment H J) → ∀ e →
                   subst₂ FlatGen (align-atom-ein al e) (align-atom-eout al e)
                                  (J.elab (Alignment.ψ al e))
                 ≡ H.elab e

  matIso→hgIso : Alignment H J → H ≅ᴴ J
  matIso→hgIso al = record
    { φ         = Alignment.φ   al
    ; φ⁻¹       = Alignment.φ⁻¹ al
    ; φ-left    = align-φ-left al
    ; φ-rght    = align-φ-rght al
    ; ψ         = Alignment.ψ   al
    ; ψ⁻¹       = Alignment.ψ⁻¹ al
    ; ψ-left    = align-ψ-left al
    ; ψ-rght    = align-ψ-rght al
    ; φ-lab     = align-φ-lab al
    ; ψ-ein     = align-ψ-ein al
    ; ψ-eout    = align-ψ-eout al
    ; φ-dom     = align-φ-dom al
    ; φ-cod     = align-φ-cod al
    ; atom-ein  = align-atom-ein al
    ; atom-eout = align-atom-eout al
    ; ψ-elab    = align-ψ-elab al
    }
