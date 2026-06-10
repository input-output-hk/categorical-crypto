{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- FEASIBILITY SPIKE: run the *matrix* coherence representation on a
-- *hypergraph*, by translating between the two worlds.
--
--   hg→mat  : Hypergraph FlatGen → BlockMatrix Bool …      (incidence encoding)
--   align   : (H J) → candidate (φ , ψ) bijections          (CANONICAL read)
--   CanonMatch al  : a DECIDABLE witness that `al` aligns H's diagram onto J's
--   decCanonMatch  : Alignment → Maybe CanonMatch           (no-search decide)
--   matIso→hgIso : (al)(BijLaws al)(CanonMatch al) → H ≅ᴴ J  (record assembly)
--
-- `align` is a REAL canonical-labelling read (no backtracking search): it
-- computes a canonical DAG labelling of each hypergraph and reads the
-- bijection off the canonical ranks.  See §2.
--
-- ALL TWELVE `_≅ᴴ_` FIELDS ARE NOW REAL PROOFS — no postulate, no `trustMe`,
-- in the `≅ᴴ` construction:
--
--   * The FOUR BIJECTION-LAW fields (`φ-left`/`φ-rght`/`ψ-left`/`ψ-rght`, the
--     inverse round-trips) follow from the canonical orders being PERMUTATIONS
--     of their `Fin` index spaces plus an equal-count match; see §2½ (the
--     abstract `Composite` lemma over `posIn`/`lookupD`), §2¾ (`CanonPerm` /
--     `BijLaws` / `align-bijLaws`).  The permutation property is taken as the
--     EXPLICIT, documented `CanonPerm` hypothesis (it holds for every
--     well-formed monogamous acyclic covering input; for concrete inputs the
--     orders compute to explicit enumerations and `CanonPerm` is discharged
--     constructively — see `MatrixBridgeDemo`).
--
--   * The EIGHT PRESERVATION fields (vlab / endpoint / boundary / elab
--     agreement) are PROVEN from a canonical-match WITNESS (`CanonMatch`) — a
--     decidable predicate (the no-search analogue of the search-side `Verify`)
--     asserting, at `align`'s own `φ`/`ψ`, the primitive incidence equations.
--     These facts are FALSE for an arbitrary `Alignment` (see §3 CRUX); so the
--     witness is essential.  `decCanonMatch` PRODUCES it with no search.
--
-- `matIso→hgIso al bij match` therefore assembles a fully-proven `H ≅ᴴ J`.
-- `MatrixBridgeDemo` discharges BOTH inputs constructively on a concrete iso
-- pair (`CanonPerm` by `refl`-witnesses, `CanonMatch` by `decCanonMatch`).
--
-- Drops `--safe` (brings in the matrix world); the underlying hypergraph
-- modules remain `--safe --without-K`.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.MatrixBridge
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig; _≟X_)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

-- The matrix world (brought over from branch `smc-coherence`).
open import Categories.SymmetricMonoidalCoherence.Matrix
  using (Matrix; tabulateM; BlockMatrix; RowG; ColG; v⁻; v⁺; t⁺; t⁻;
         module Sizes)

-- Decidable-equality + view machinery reused from the search-side verifier:
-- `flat-match` (conservative `FlatGen` equality via `FlatView`), `dec→maybe`,
-- `∀F?` (∀-over-Fin decider).  We reuse these wholesale so the canonical
-- (no-search) match-decider stays in lock-step with `Verify`.
open import Categories.APROP.Hypergraph.Solver.Verify sig-dec
  using (flat-match; dec→maybe; ∀F?)

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ; cast)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; length; lookup; map; _++_; foldr)
open import Data.List.Properties using (map-∘; map-cong; ≡-dec)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

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
-- TIE-BREAK SCOPE.  The signature distinguishes ready edges by a pair
--
--     edgeSig e = (ecode e , sortℕ (map (rank) (ein e)))
--
-- compared LEXICOGRAPHICALLY with the GENERATOR CODE first.  `ecode` is a
-- per-edge ℕ supplied by the caller (`Canon`/`align` are parameterised by
-- it): it is the position of the edge's generator in some fixed enumeration
-- of the signature's generators (the demo builds a concrete one off each
-- edge's `FlatGen` label — see `MatrixBridgeDemo`).
--
-- WHY THE CODE MATTERS.  Under MONOGAMY (each wire produced once / consumed
-- once — true of every `⟪_⟫` translation) two distinct *non-input-free*
-- edges read DISJOINT input vertices, hence disjoint canonical ranks, hence
-- DISTINCT rank-multisets: they never tie on the structural part alone.  The
-- ONLY structural ties are between INPUT-FREE edges (`ein = []`, so the
-- rank-multiset is `[]` for all of them).  Among input-free edges:
--   * DIFFERENT generators (e.g. two distinct states `u v : unit → X`) used
--     to tie on `[]` and got mis-ordered between two differently-laid-out
--     iso graphs.  The generator code RESOLVES this: `u`/`v` get distinct
--     codes, so the lexicographic compare separates them canonically.
--   * SAME generator (two copies of one state) → a genuine automorphism; any
--     pairing is a valid iso, so the residual index tie-break is harmless.
-- So with a faithful `ecode` the canonical read is correct for ALL
-- monogamous inputs except genuine same-generator automorphisms (harmless).
-- See the report / `MatrixBridgeDemo`.

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

  -- Lexicographic strict comparison of an edge signature
  -- `(code , rank-multiset)`, GENERATOR CODE FIRST: a smaller code wins
  -- outright; on a code tie, fall back to the structural rank-multiset.
  ltSig : (ℕ × List ℕ) → (ℕ × List ℕ) → Bool
  ltSig (c , xs) (d , ys) =
    (c <ᵇ d) ∨ ((c ≡ᵇ d) ∧ ltList xs ys)

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

  -- §2-empty.  The empty-`Fin` fix lives in `align'` (below): `align`
  -- originally demanded explicit `Fin (nV J)` / `Fin (nE J)` defaults so that
  -- `lookupD` had a fallback for its `[]` branch.  Those defaults are
  -- UNINHABITED when a count is `0` (an edge-free structural equation has
  -- `nE = 0`), so `align` could not even be *called* there.  `align'` derives
  -- `lookupD`'s default FROM THE INPUT via `cast` along the count equality, so
  -- no uninhabited `Fin 0` is ever demanded.  See `align'`.

--------------------------------------------------------------------------------
-- §2½.  PERMUTATION CALCULUS for `posIn` / `lookupD`.
--
-- The four bijection-law fields of `_≅ᴴ_` (`φ-left`/`φ-rght`/`ψ-left`/
-- `ψ-rght`) say that `align`'s `φ`/`φ⁻¹` (and `ψ`/`ψ⁻¹`) are mutually
-- inverse.  `align` builds them as the composite
--
--     φ v = lookupD dy (canonV J) (posIn (canonV H) v)     (and dually).
--
-- This composite is a bijection PROVIDED the two canonical orders involved
-- are PERMUTATIONS of their index spaces (each Fin appears exactly once) and
-- have EQUAL LENGTH.  This section proves that implication ABSTRACTLY, purely
-- from `posIn` / `lookupD`; the only inputs are list-completeness,
-- list-distinctness and a length match.  No hypergraph structure is used here
-- — see `CanonPerm` / `bijLaws` / `matIso→hgIso` (§3) for how the canonical
-- orders supply these inputs.
--
-- The predicates `_∈L_` / `Distinct` / `Complete` are PUBLIC so callers can
-- discharge the explicit permutation hypotheses on the canonical orders.

-- Membership predicate matching `posIn`'s structural recursion.
data _∈L_ {n : ℕ} : Fin n → List (Fin n) → Set where
  here  : ∀ {x xs}             → x ∈L (x ∷ xs)
  there : ∀ {x y xs} → x ∈L xs → x ∈L (y ∷ xs)

-- No-duplicates predicate.
infixr 5 _∷ᵈ_
data Distinct {n : ℕ} : List (Fin n) → Set where
  []ᵈ  : Distinct []
  _∷ᵈ_ : ∀ {x xs} → (x ∈L xs → ⊥) → Distinct xs → Distinct (x ∷ xs)

-- Completeness: every index appears in the list.
Complete : ∀ {n} → List (Fin n) → Set
Complete {n} xs = (v : Fin n) → v ∈L xs

private
  -- R1.  Reading back the recorded position recovers the element — needs only
  -- membership.
  pos-look : ∀ {n} (d : Fin n) (xs : List (Fin n)) (v : Fin n)
           → v ∈L xs → lookupD d xs (posIn xs v) ≡ v
  pos-look d (x ∷ xs) v mem with x ≟F v
  ... | yes p = p
  ... | no ¬p with mem
  ...   | here       = ⊥-elim (¬p refl)
  ...   | there mem' = pos-look d xs v mem'

  -- Recorded positions are in range.
  pos-bound : ∀ {n} (xs : List (Fin n)) (v : Fin n)
            → v ∈L xs → posIn xs v < length xs
  pos-bound (x ∷ xs) v mem with x ≟F v
  ... | yes _ = s≤s z≤n
  ... | no ¬p with mem
  ...   | here       = ⊥-elim (¬p refl)
  ...   | there mem' = s≤s (pos-bound xs v mem')

  -- `lookupD` at an in-range index lands inside the list.
  look-mem : ∀ {n} (d : Fin n) (ys : List (Fin n)) (q : ℕ)
           → q < length ys → lookupD d ys q ∈L ys
  look-mem d (y ∷ ys) zero    _        = here
  look-mem d (y ∷ ys) (suc q) (s≤s qb) = there (look-mem d ys q qb)

  -- R2.  Looking up position `p` then re-reading its position gives `p` back —
  -- needs distinctness (so the looked-up element occurs nowhere earlier).
  look-pos : ∀ {n} (d : Fin n) (xs : List (Fin n)) (p : ℕ)
           → p < length xs → Distinct xs
           → posIn xs (lookupD d xs p) ≡ p
  look-pos d (x ∷ xs) zero    (s≤s _)   (x∉ ∷ᵈ dist) with x ≟F x
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)
  look-pos d (x ∷ xs) (suc p) (s≤s p<l) (x∉ ∷ᵈ dist) with x ≟F lookupD d xs p
  ... | yes x≡e = ⊥-elim (x∉ (subst (_∈L xs) (sym x≡e) (look-mem d xs p p<l)))
  ... | no _ = cong suc (look-pos d xs p p<l dist)

-- The composite-bijection lemma.  Two enumerating lists `xs` (of `Fin m`) and
-- `ys` (of `Fin n`) of equal length give mutually-inverse maps via
-- `posIn`/`lookupD`.  This is the heart of the four bijection-law proofs.
module Composite {m n : ℕ}
  (xs : List (Fin m)) (ys : List (Fin n))
  (xs-comp : Complete xs) (ys-comp : Complete ys)
  (xs-dist : Distinct xs) (ys-dist : Distinct ys)
  (len≡ : length xs ≡ length ys)
  (dx : Fin m) (dy : Fin n)
  where

  f : Fin m → Fin n
  f v = lookupD dy ys (posIn xs v)

  g : Fin n → Fin m
  g w = lookupD dx xs (posIn ys w)

  left : ∀ v → g (f v) ≡ v
  left v =
    let p<lxs = pos-bound xs v (xs-comp v)
        p<lys = subst (posIn xs v <_) len≡ p<lxs
    in trans (cong (lookupD dx xs) (look-pos dy ys (posIn xs v) p<lys ys-dist))
             (pos-look dx xs v (xs-comp v))

  right : ∀ w → f (g w) ≡ w
  right w =
    let q<lys = pos-bound ys w (ys-comp w)
        q<lxs = subst (posIn ys w <_) (sym len≡) q<lys
    in trans (cong (lookupD dy ys) (look-pos dx xs (posIn ys w) q<lxs xs-dist))
             (pos-look dy ys w (ys-comp w))

-- `Canon` is parameterised by a per-edge GENERATOR CODE `ecode`.  The code
-- is folded into the signature ahead of the structural rank-multiset, so it
-- dominates the tie-break (see §2).  A faithful `ecode` (distinct generators
-- ↦ distinct codes) makes the canonical read correct for all monogamous
-- inputs except same-generator automorphisms.
module Canon (H : Hypergraph FlatGen) (ecode : Fin (Hypergraph.nE H) → ℕ) where
  private module H = Hypergraph H

  -- Signature of an edge given the current canonical vertex order
  -- `rankedV`: the pair (generator code, SORTED canonical ranks of the
  -- edge's input vertices), compared lexicographically with the code first.
  edgeSig : List (Fin H.nV) → Fin H.nE → ℕ × List ℕ
  edgeSig rankedV e = (ecode e , sortℕ (map (posIn rankedV) (H.ein e)))

  -- Is edge `e` ready to peel?  (all inputs already ranked, and e not yet
  -- peeled).  `peeled` : edges already in canonical order.  `rankedV` :
  -- vertices already ranked.
  ready? : List (Fin H.nE) → List (Fin H.nV) → Fin H.nE → Bool
  ready? peeled rankedV e =
    not (memberOf peeled e) ∧ allMember rankedV (H.ein e)

  open import Data.Maybe using (Maybe; just; nothing)

  -- Among the scanned `candidates`, pick the ready edge of minimal
  -- signature, carrying the best-so-far as a `Maybe (Fin nE × (ℕ × List ℕ))`.
  -- Returns `nothing` iff no candidate is ready (cannot happen on a
  -- well-formed acyclic monogamous DAG before all edges are peeled).
  pickMin : List (Fin H.nE) → List (Fin H.nV)
          → Maybe (Fin H.nE × (ℕ × List ℕ))  -- best edge so far + its sig
          → List (Fin H.nE)                    -- candidates to scan
          → Maybe (Fin H.nE)
  pickMin peeled rankedV nothing             [] = nothing
  pickMin peeled rankedV (just (best , _))   [] = just best
  pickMin peeled rankedV acc (e ∷ es) with ready? peeled rankedV e
  ... | false = pickMin peeled rankedV acc es
  ... | true  with acc
  ...   | nothing = -- first ready edge: it's the new best
                    pickMin peeled rankedV (just (e , edgeSig rankedV e)) es
  ...   | just (best , bestSig) with ltSig (edgeSig rankedV e) bestSig
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
-- well-formed iso graphs).  Defaults are provided as explicit arguments of
-- `align`; in the validating demo they are concrete `Fin`s.
--
-- `align` is parameterised by the two generator-code functions `ecodeH`,
-- `ecodeJ` (one per hypergraph), fed straight into `Canon`.  For the canonical
-- reads of `H` and `J` to MATCH, the two codes must agree on corresponding
-- edges — i.e. they should both be the same `morCode ∘ (generator of edge)`,
-- as the demo arranges.
align : (H J : Hypergraph FlatGen)
      → (ecodeH : Fin (Hypergraph.nE H) → ℕ)
      → (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
      → (dV  : Fin (Hypergraph.nV J)) (dV' : Fin (Hypergraph.nV H))
      → (dE  : Fin (Hypergraph.nE J)) (dE' : Fin (Hypergraph.nE H))
      → Alignment H J
align H J ecodeH ecodeJ dV dV' dE dE' = record
  { φ   = λ v → lookupD dV  (Canon.canonV J ecodeJ) (posIn (Canon.canonV H ecodeH) v)
  ; φ⁻¹ = λ v → lookupD dV' (Canon.canonV H ecodeH) (posIn (Canon.canonV J ecodeJ) v)
  ; ψ   = λ e → lookupD dE  (Canon.canonE J ecodeJ) (posIn (Canon.canonE H ecodeH) e)
  ; ψ⁻¹ = λ e → lookupD dE' (Canon.canonE H ecodeH) (posIn (Canon.canonE J ecodeJ) e)
  }

--------------------------------------------------------------------------------
-- §2-empty.  `align'` — the DEFAULT-FREE drop-in (the empty-`Fin` fix).
--
-- `align` above demands four uninhabited-when-zero `Fin` defaults
-- (`dV/dV'/dE/dE'`), so it cannot be CALLED when a count is `0` (e.g. an
-- edge-free structural equation has `nE = 0`, making `dE : Fin 0` impossible).
--
-- `align'` removes that obstruction.  It takes the two COUNT EQUALITIES
-- (`nV H ≡ nV J` and `nE H ≡ nE J`) — exactly the data a candidate iso must
-- satisfy, and which `findIsoᴮ` decides up front — and derives `lookupD`'s
-- default FROM THE INPUT, under the binder, via `cast`:
--
--     φ v = lookupD (cast pV v) (canonV J) (posIn (canonV H) v)
--
-- `cast pV v : Fin (nV J)` is total for EVERY input `v` (no uninhabited value
-- demanded), and is only ever consulted off-the-end — which never happens for
-- in-range permutation lookups.  So `align'`'s observable behaviour on
-- well-formed inputs is identical to `align`'s, and `align'` is callable for
-- ALL counts, including `nE = 0` and `nV = 0` (where the corresponding map has
-- empty domain and the default is vacuously fine).
align' : (H J : Hypergraph FlatGen)
       → (ecodeH : Fin (Hypergraph.nE H) → ℕ)
       → (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
       → (pV : Hypergraph.nV H ≡ Hypergraph.nV J)
       → (pE : Hypergraph.nE H ≡ Hypergraph.nE J)
       → Alignment H J
align' H J ecodeH ecodeJ pV pE = record
  { φ   = λ v → lookupD (cast pV v)        (Canon.canonV J ecodeJ) (posIn (Canon.canonV H ecodeH) v)
  ; φ⁻¹ = λ v → lookupD (cast (sym pV) v)  (Canon.canonV H ecodeH) (posIn (Canon.canonV J ecodeJ) v)
  ; ψ   = λ e → lookupD (cast pE e)        (Canon.canonE J ecodeJ) (posIn (Canon.canonE H ecodeH) e)
  ; ψ⁻¹ = λ e → lookupD (cast (sym pE) e)  (Canon.canonE H ecodeH) (posIn (Canon.canonE J ecodeJ) e)
  }

--------------------------------------------------------------------------------
-- §2¾.  The FOUR bijection laws are REAL proofs.
--
-- `BijLaws al` packages the four round-trips of an alignment (the
-- `φ-left`/`φ-rght`/`ψ-left`/`ψ-rght` fields of `_≅ᴴ_`).  `CanonPerm`
-- packages the EXPLICIT permutation hypotheses on the canonical orders that
-- `align` reads off:
--
--   * each of `canonV H`, `canonV J`, `canonE H`, `canonE J` is `Complete`
--     (covers every index) and `Distinct` (no repeats) — i.e. a PERMUTATION
--     of its `Fin` index space;
--   * the two vertex orders have equal length and the two edge orders have
--     equal length (the EQUAL-COUNT side-condition; together with
--     completeness this forces `nV H ≡ nV J` and `nE H ≡ nE J`, as it must,
--     since `φ : Fin (nV H) → Fin (nV J)` is only ever a bijection then).
--
-- These conditions hold for every well-formed (monogamous, acyclic, covering)
-- input hypergraph: the topological peel emits each edge once and each vertex
-- once.  We do NOT re-derive that combinatorial fact from the peel here; it is
-- taken as the explicit, clearly-documented `CanonPerm` hypothesis.  Given it,
-- `align-bijLaws` PROVES all four laws via the abstract `Composite` lemma — no
-- postulate, no `trustMe`.  (For concrete inputs the canonical orders compute
-- to explicit enumerations, so `CanonPerm` is discharged by short witnesses;
-- see `MatrixBridgeDemo`.)

record BijLaws {H J : Hypergraph FlatGen} (al : Alignment H J) : Set where
  open Alignment al
  field
    φ-left : ∀ i → φ⁻¹ (φ i) ≡ i
    φ-rght : ∀ i → φ (φ⁻¹ i) ≡ i
    ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
    ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e

-- Explicit permutation hypotheses on the four canonical orders that `align H J
-- ecodeH ecodeJ …` reads.  The orders are determined by `ecodeH`/`ecodeJ`, so
-- those are parameters here too.
record CanonPerm (H J : Hypergraph FlatGen)
                 (ecodeH : Fin (Hypergraph.nE H) → ℕ)
                 (ecodeJ : Fin (Hypergraph.nE J) → ℕ) : Set where
  field
    -- vertex orders are permutations of equal length
    cVH-comp : Complete (Canon.canonV H ecodeH)
    cVJ-comp : Complete (Canon.canonV J ecodeJ)
    cVH-dist : Distinct (Canon.canonV H ecodeH)
    cVJ-dist : Distinct (Canon.canonV J ecodeJ)
    cV-len   : length (Canon.canonV H ecodeH) ≡ length (Canon.canonV J ecodeJ)
    -- edge orders are permutations of equal length
    cEH-comp : Complete (Canon.canonE H ecodeH)
    cEJ-comp : Complete (Canon.canonE J ecodeJ)
    cEH-dist : Distinct (Canon.canonE H ecodeH)
    cEJ-dist : Distinct (Canon.canonE J ecodeJ)
    cE-len   : length (Canon.canonE H ecodeH) ≡ length (Canon.canonE J ecodeJ)

-- The four bijection laws of `align H J ecodeH ecodeJ …`, PROVEN from a
-- `CanonPerm`.  Definitionally, `align`'s φ/φ⁻¹ are exactly the f/g of
-- `Composite (canonV H) (canonV J) …` (and dually for ψ on the edge orders),
-- so `Composite.left`/`Composite.right` discharge the laws on the nose.
align-bijLaws :
  (H J : Hypergraph FlatGen)
  (ecodeH : Fin (Hypergraph.nE H) → ℕ)
  (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
  (dV  : Fin (Hypergraph.nV J)) (dV' : Fin (Hypergraph.nV H))
  (dE  : Fin (Hypergraph.nE J)) (dE' : Fin (Hypergraph.nE H))
  → CanonPerm H J ecodeH ecodeJ
  → BijLaws (align H J ecodeH ecodeJ dV dV' dE dE')
align-bijLaws H J ecodeH ecodeJ dV dV' dE dE' cp = record
  { φ-left = CV.left
  ; φ-rght = CV.right
  ; ψ-left = CE.left
  ; ψ-rght = CE.right
  }
  where
    open CanonPerm cp
    module CV = Composite (Canon.canonV H ecodeH) (Canon.canonV J ecodeJ)
                          cVH-comp cVJ-comp cVH-dist cVJ-dist cV-len dV' dV
    module CE = Composite (Canon.canonE H ecodeH) (Canon.canonE J ecodeJ)
                          cEH-comp cEJ-comp cEH-dist cEJ-dist cE-len dE' dE

--------------------------------------------------------------------------------
-- §3.  The CANONICAL-MATCH WITNESS and `matIso→hgIso`.
--
-- ALL TWELVE `_≅ᴴ_` fields are now REAL proofs.  The FOUR bijection-law
-- fields come from a `BijLaws al` argument (real proofs, §2¾).  The EIGHT
-- preservation fields come from a `CanonMatch al` witness, as follows.
--
-- CRUX (see the module header / the report).  The incidence-preservation
-- facts (vlab / endpoint / boundary / elab agreement) are FALSE for an
-- arbitrary `Alignment H J`: `align` always returns *some* `(φ, ψ)`, but the
-- incidence only agrees when `H` and `J` actually realise the same diagram.
-- So they cannot be proven against a bare `Alignment`.
--
-- The fix is to make `matIso→hgIso` consume a WITNESS that the alignment's
-- `φ`/`ψ` really do match `H`'s incidence onto `J`'s.  `CanonMatch al`
-- packages exactly the PRIMITIVE preservation equations — the same ones the
-- search-side `Verify.verify` checks decidably — phrased against `al`'s own
-- `φ`/`ψ`.  Crucially each field is a DECIDABLE equation, so a solver can
-- PRODUCE the witness with no search (`decCanonMatch` below: the no-search
-- analogue of `Verify`).  The derived facts (`atom-ein`/`atom-eout`) and the
-- whole `_≅ᴴ_` record are then PROVEN from the witness + `BijLaws`.

module _ {H J : Hypergraph FlatGen} where
  private
    module H = Hypergraph H
    module J = Hypergraph J

  -- The canonical-match witness over a fixed alignment `al`.  These are the
  -- five PRIMITIVE incidence equations plus the `subst₂`-transported edge
  -- label equation — exactly the data `Verify.verify` decides.  Everything
  -- else an `_≅ᴴ_` needs is derived below.
  record CanonMatch (al : Alignment H J) : Set where
    private
      φ = Alignment.φ al
      ψ = Alignment.ψ al
    field
      m-lab  : ∀ i → J.vlab (φ i) ≡ H.vlab i
      m-ein  : ∀ e → J.ein  (ψ e) ≡ map φ (H.ein  e)
      m-eout : ∀ e → J.eout (ψ e) ≡ map φ (H.eout e)
      m-dom  : J.dom ≡ map φ H.dom
      m-cod  : J.cod ≡ map φ H.cod
      -- Edge labels agree up to the `subst₂ FlatGen` transport along the
      -- (derived) atom-list equalities.  This is the `ψ-elab` field at the
      -- canonical `φ`/`ψ`.  The atom-list equalities it transports along are
      -- the *derived* ones (`derive-atom-ein/-eout` below).
      m-elab : ∀ e →
        subst₂ FlatGen
          (trans (cong (map J.vlab) (m-ein e))
                 (trans (sym (map-∘ (H.ein e))) (map-cong m-lab (H.ein e))))
          (trans (cong (map J.vlab) (m-eout e))
                 (trans (sym (map-∘ (H.eout e))) (map-cong m-lab (H.eout e))))
          (J.elab (ψ e))
        ≡ H.elab e

  -- ── Derived facts (PROVEN from the witness) ──────────────────────────────
  module _ {al : Alignment H J} (mt : CanonMatch al) where
    private
      module Mt = CanonMatch mt
      φ = Alignment.φ al
      ψ = Alignment.ψ al

    -- `map J.vlab ys ≡ map H.vlab xs` from `ys ≡ map φ xs` and the pointwise
    -- vertex-label agreement `J.vlab (φ i) ≡ H.vlab i`.  This is exactly
    -- `Verify.deriveAtomEq`: it turns ψ-ein/ψ-eout + φ-lab into atom-ein/-eout
    -- with NO new assumptions.  (Reproduced here to keep `CanonMatch` free of
    -- the `Verify.Verify` module's bijection parameters.)
    private
      deriveAtomEq : ∀ (xs : List (Fin H.nV)) (ys : List (Fin J.nV))
                   → ys ≡ map φ xs
                   → map J.vlab ys ≡ map H.vlab xs
      deriveAtomEq xs ys p =
        trans (cong (map J.vlab) p)
        (trans (sym (map-∘ xs)) (map-cong Mt.m-lab xs))

    derive-atom-ein : ∀ e → map J.vlab (J.ein  (ψ e)) ≡ map H.vlab (H.ein  e)
    derive-atom-ein e = deriveAtomEq (H.ein  e) (J.ein  (ψ e)) (Mt.m-ein  e)

    derive-atom-eout : ∀ e → map J.vlab (J.eout (ψ e)) ≡ map H.vlab (H.eout e)
    derive-atom-eout e = deriveAtomEq (H.eout e) (J.eout (ψ e)) (Mt.m-eout e)

  -- ── `matIso→hgIso` : turn a MATCHED + BIJECTIVE alignment into an iso ──────
  -- ALL twelve fields are now PROVEN: the four bijection laws from `BijLaws`
  -- (§2¾), the eight incidence/label/boundary/elab fields from `CanonMatch`.
  -- No `postulate` anywhere in the construction.
  matIso→hgIso : (al : Alignment H J) → BijLaws al → CanonMatch al → H ≅ᴴ J
  matIso→hgIso al bl mt = record
    { φ         = Alignment.φ   al
    ; φ⁻¹       = Alignment.φ⁻¹ al
    ; φ-left    = BijLaws.φ-left bl
    ; φ-rght    = BijLaws.φ-rght bl
    ; ψ         = Alignment.ψ   al
    ; ψ⁻¹       = Alignment.ψ⁻¹ al
    ; ψ-left    = BijLaws.ψ-left bl
    ; ψ-rght    = BijLaws.ψ-rght bl
    ; φ-lab     = Mt.m-lab
    ; ψ-ein     = Mt.m-ein
    ; ψ-eout    = Mt.m-eout
    ; φ-dom     = Mt.m-dom
    ; φ-cod     = Mt.m-cod
    ; atom-ein  = derive-atom-ein  mt
    ; atom-eout = derive-atom-eout mt
    ; ψ-elab    = Mt.m-elab
    }
    where module Mt = CanonMatch mt

  -- ── `decCanonMatch` : the NO-SEARCH match decider ─────────────────────────
  -- Given any alignment, decide its canonical-match witness by running the
  -- same decidable incidence checks `Verify.verify` runs (but at `align`'s
  -- canonical `φ`/`ψ`, with no backtracking).  `just` ⇒ the alignment really
  -- aligns `H`'s diagram onto `J`'s, so the incidence fields produced via
  -- `matIso→hgIso al` are sound.
  private
    _≟LF_ : DecidableEquality (List (Fin J.nV))
    _≟LF_ = ≡-dec _≟F_

  decCanonMatch : (al : Alignment H J) → Maybe (CanonMatch al)
  decCanonMatch al
    with ∀F? (λ i → dec→maybe (J.vlab (φ i) ≟X H.vlab i))
       | ∀F? (λ e → dec→maybe (J.ein  (ψ e) ≟LF map φ (H.ein  e)))
       | ∀F? (λ e → dec→maybe (J.eout (ψ e) ≟LF map φ (H.eout e)))
       | J.dom ≟LF map φ H.dom
       | J.cod ≟LF map φ H.cod
    where φ = Alignment.φ al
          ψ = Alignment.ψ al
  ... | nothing | _ | _ | _ | _ = nothing
  ... | _ | nothing | _ | _ | _ = nothing
  ... | _ | _ | nothing | _ | _ = nothing
  ... | _ | _ | _ | no _ | _ = nothing
  ... | _ | _ | _ | _ | no _ = nothing
  ... | just lab | just ein | just eout | yes dom | yes cod
        with ∀F? (λ e → flat-match
               (subst₂ FlatGen
                 (trans (cong (map J.vlab) (ein  e))
                        (trans (sym (map-∘ (H.ein  e))) (map-cong lab (H.ein  e))))
                 (trans (cong (map J.vlab) (eout e))
                        (trans (sym (map-∘ (H.eout e))) (map-cong lab (H.eout e))))
                 (J.elab (Alignment.ψ al e)))
               (H.elab e))
  ...   | nothing = nothing
  ...   | just elab = just record
              { m-lab  = lab
              ; m-ein  = ein
              ; m-eout = eout
              ; m-dom  = dom
              ; m-cod  = cod
              ; m-elab = elab
              }

  -- ── `decBijLaws` : DECIDE the four bijection round-trips ───────────────────
  -- The PURELY-DECIDED analogue of `align-bijLaws`: instead of assuming a
  -- `CanonPerm` hypothesis, it decides each of the four round-trips
  -- (`φ⁻¹ (φ i) ≡ i`, `φ (φ⁻¹ i) ≡ i`, `ψ⁻¹ (ψ e) ≡ e`, `ψ (ψ⁻¹ e) ≡ e`)
  -- the SAME way `decCanonMatch` decides the incidence equations — via
  -- `∀F?`/`dec→maybe` over `Data.Fin.Properties._≟_`.  A `just` therefore
  -- carries genuine round-trip proofs, with NO `CanonPerm` input.  (If the
  -- alignment's `φ`/`ψ` are not mutually inverse — e.g. a wrong `align`
  -- read — some round-trip fails decidably and the result is `nothing`.)
  decBijLaws : (al : Alignment H J) → Maybe (BijLaws al)
  decBijLaws al
    with ∀F? (λ i → dec→maybe (φ⁻¹ (φ i) ≟F i))
       | ∀F? (λ i → dec→maybe (φ (φ⁻¹ i) ≟F i))
       | ∀F? (λ e → dec→maybe (ψ⁻¹ (ψ e) ≟F e))
       | ∀F? (λ e → dec→maybe (ψ (ψ⁻¹ e) ≟F e))
    where φ   = Alignment.φ   al
          φ⁻¹ = Alignment.φ⁻¹ al
          ψ   = Alignment.ψ   al
          ψ⁻¹ = Alignment.ψ⁻¹ al
  ... | nothing | _ | _ | _ = nothing
  ... | _ | nothing | _ | _ = nothing
  ... | _ | _ | nothing | _ = nothing
  ... | _ | _ | _ | nothing = nothing
  ... | just φl | just φr | just ψl | just ψr = just record
        { φ-left = φl
        ; φ-rght = φr
        ; ψ-left = ψl
        ; ψ-rght = ψr
        }

--------------------------------------------------------------------------------
-- §4.  `findIsoᴮ` : a SOUND, NO-SEARCH drop-in for `findIso`.
--
-- Builds the canonical alignment `align'` (the default-free variant, §2-empty)
-- and assembles `H ≅ᴴ J` from the THREE purely-decided witnesses:
--
--   * the count equalities `nV H ≡ nV J`, `nE H ≡ nE J`, decided up front
--     (a bijection is impossible unless they hold — so deciding them is sound
--     and they are exactly what `align'` needs to drop its `Fin` defaults);
--   * `decBijLaws  al` — the four bijection round-trips, decided;
--   * `decCanonMatch al` — the eight incidence/label/boundary fields, decided.
--
-- Every field of the resulting `_≅ᴴ_` is a genuine proof produced by
-- `matIso→hgIso` (no postulate anywhere in the iso path).  A wrong `align'`
-- read is REJECTED by the deciders (`nothing`); a `just` is a genuine iso.
--
-- COVERAGE.  Unlike `findIso`, this is callable even for `nE = 0` (edge-free
-- structural equations) and `nV = 0`, since `align'` demands no uninhabited
-- `Fin` defaults.  It is SOUND for all inputs; it is COMPLETE on monogamous
-- acyclic `⟪_⟫`-translations whose canonical reads agree under `ecodeH`/
-- `ecodeJ` (a FAITHFUL pair of generator codes is needed to canonicalise
-- input-free generator ties — a `const 0` ecode is still SOUND but only
-- complete for non-tie cases; see §2).
findIsoᴮ : (H J : Hypergraph FlatGen)
         → (ecodeH : Fin (Hypergraph.nE H) → ℕ)
         → (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
         → Maybe (H ≅ᴴ J)
findIsoᴮ H J ecodeH ecodeJ
  with Hypergraph.nV H ≟ℕ Hypergraph.nV J
     | Hypergraph.nE H ≟ℕ Hypergraph.nE J
... | no _  | _     = nothing
... | _     | no _  = nothing
... | yes pV | yes pE =
      let al = align' H J ecodeH ecodeJ pV pE
      in decBijLaws al >>= λ bij →
         decCanonMatch al >>= λ mt →
         just (matIso→hgIso al bij mt)
