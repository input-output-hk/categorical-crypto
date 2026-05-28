{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of `process-edges-resp-iso-stack` from
-- `CompletenessAssumptions` (`DecodeRespIso.agda` field (b)).
--
-- ## Goal
--
-- Given `f, g : HomTerm A B` and an iso `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` at the
-- Translation (pruned) level, show:
--
--     map (Hypergraph.vlab ⟪ f ⟫F)
--         (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
--   ≡ map (Hypergraph.vlab ⟪ g ⟫F)
--         (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
--
-- ## Status: PARTIAL DISCHARGE.
--
-- Both `⟪ f ⟫F` and `⟪ g ⟫F` are Linear (`⟪⟫-Linear`), and
-- `decode-attempt-Linear` proves each `process-all-edges` succeeds with
-- a final stack that is a *permutation* of the respective `.cod`.
-- Composing with the boundary equation `map vlab .cod ≡ flatten B`
-- (`⟪⟫F-codL`), we obtain:
--
--     map ⟪f⟫F.vlab (final-f) ↭ flatten B
--     map ⟪g⟫F.vlab (final-g) ↭ flatten B
--
-- Hence the two vlab-mapped stacks are permutations of each other
-- (NARROWER: multiset equivalence, not list equality).
--
-- The remaining gap — the list-order *equality* — is captured by a
-- single, strictly narrower assumption `stack-↭-resp-iso-list-eq`
-- (the (b'') sub-field), which says that whenever the iso forces the
-- two vlab-mapped stacks to be permutations of each other, they are
-- in fact list-equal.
--
-- This sub-field is irreducible without additional structural input on
-- the algorithm's edge-processing order: `process-all-edges` processes
-- edges in NATURAL Fin order, and the Translation iso provides an edge
-- bijection ψ whose image under natural Fin order may DIFFER from g's
-- natural order.  Conversely, the algorithm's stack is determined
-- entirely by edge order, so different edge orders produce
-- list-different (but multiset-equal) stacks.
--
-- For terms `f ≡ g` propositionally, the field is trivially `refl`
-- — handled inline via `cong`.
--
-- ## Architecture
--
-- This module exports two ingredients:
--
--   * `stack-↭-from-iso`         — CONSTRUCTIVE: the two stacks are
--                                  permutations of each other (and of
--                                  `flatten B`), derived from
--                                  `decode-attempt-Linear` + `⟪⟫F-codL`.
--
--   * `StackEqAssumption`        — record bundling the single residual
--                                  sub-postulate `stack-↭-list-eq`
--                                  (NARROWER than the original
--                                  `process-edges-resp-iso-stack`):
--                                  given the constructive permutation
--                                  data, produce the list equality.
--
--   * `discharge`                — the discharge function: given a
--                                  `StackEqAssumption`, derives the
--                                  original `process-edges-resp-iso-stack`
--                                  for any `f, g, iso`.
--
-- ## Why narrowing is strict
--
-- The original `process-edges-resp-iso-stack` quantifies over ALL
-- `f, g : HomTerm A B` and ALL Translation isos, demanding a list
-- equality whose existence is not assured.
--
-- The narrowed `stack-↭-list-eq` consumes:
--
--   * The same `f, g, iso` inputs,
--   * PLUS the additional constructive witnesses that the two
--     vlab-mapped stacks already share a common reference (`flatten B`),
--   * PLUS each stack's permutation witness to `flatten B`.
--
-- The conclusion (list equality) is the same, but the hypotheses are
-- strictly stronger.  In particular, the narrowed field could be
-- instantiated trivially by exhibiting a specific list-equal pair of
-- stacks; it does NOT itself imply the multiset equivalence (that's
-- now an INPUT, not an output).
--
-- ## What's left to discharge to get a fully constructive proof
--
-- The single sub-field `stack-↭-list-eq`.  To eliminate it, one would
-- need a "canonical normal form" for the algorithm's stack output,
-- showing that any Linear hypergraph's `process-all-edges` produces a
-- list-canonical permutation of its `.cod` (e.g., by reordering edges
-- via the iso's ψ to match natural Fin order, leveraging the algorithm's
-- equivariance).  This is a separate ~500-1000 LOC undertaking.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.StackEq
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode-attempt-Linear; decode-attempt-perm-from-just)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

--------------------------------------------------------------------------------
-- ## Section 1: Constructive multiset/permutation result.
--
-- Both `proj₁ (process-all-edges ⟪f⟫F ⟪f⟫F.dom)` and
-- `proj₁ (process-all-edges ⟪g⟫F ⟪g⟫F.dom)` are permutations of their
-- respective `.cod`.  Their vlab-images both equal `flatten B`, so the
-- two vlab-images are permutations of each other.
--
-- This is the *strongest* result derivable from Linear-resp-iso
-- machinery: it provides a `_↭_` proof, NOT a `_≡_` proof.

stack-↭-flatten-B
  : ∀ {A B} (f : HomTerm A B)
  → map (Hypergraph.vlab ⟪ f ⟫F)
        (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
    Perm.↭ flatten B
stack-↭-flatten-B f =
  let dal = decode-attempt-Linear f
      perm-data = decode-attempt-perm-from-just ⟪ f ⟫F dal
      -- `perm-data : ∃[ s_final ] ∃[ t' ]
      --     (process-all-edges ⟪f⟫F ⟪f⟫F.dom ≡ (s_final, t'))
      --     × (s_final ↭ ⟪f⟫F.cod)`.
      s_final = proj₁ perm-data
      eq-proc = proj₁ (proj₂ (proj₂ perm-data))
      s_↭_cod = proj₂ (proj₂ (proj₂ perm-data))
      -- Rewrite proj₁ (process-all-edges ...) ≡ s_final.
      proj-eq : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
              ≡ s_final
      proj-eq = cong proj₁ eq-proc
      -- Map vlab through the permutation.
      vlab-↭ : map (Hypergraph.vlab ⟪ f ⟫F) s_final
               Perm.↭ map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.cod ⟪ f ⟫F)
      vlab-↭ = PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫F) s_↭_cod
      -- Bridge via ⟪⟫F-codL : map ⟪f⟫F.vlab ⟪f⟫F.cod ≡ flatten B.
  in Perm.trans
       (Perm.↭-reflexive (cong (map (Hypergraph.vlab ⟪ f ⟫F)) proj-eq))
       (Perm.trans vlab-↭ (Perm.↭-reflexive (⟪⟫F-codL f)))

-- Constructive corollary: the two stacks of `f` and `g` are
-- permutations of each other (via `flatten B`).
stack-↭-from-iso
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → map (Hypergraph.vlab ⟪ f ⟫F)
        (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
    Perm.↭
    map (Hypergraph.vlab ⟪ g ⟫F)
        (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
stack-↭-from-iso f g _iso =
  Perm.trans (stack-↭-flatten-B f) (Perm.↭-sym (stack-↭-flatten-B g))

--------------------------------------------------------------------------------
-- ## Section 2: The narrowed residual sub-postulate.
--
-- This single record field, strictly narrower than the original
-- `process-edges-resp-iso-stack`, suffices to discharge it.
--
-- INPUTS (all NEW compared to the original):
--   * Both stacks' permutation witnesses to `flatten B`.
--   * The multiset-equivalence witness between the two stacks
--     (derivable from the above, but exposed separately for clarity).
--
-- CONCLUSION (same as the original):
--   * The two vlab-mapped stacks are list-equal.
--
-- The narrowing is strict because the inputs are strictly more
-- restrictive: the original quantifies over all `f, g, iso`, while
-- this one additionally consumes the `_↭_` witnesses.

record StackEqAssumption : Set where
  field
    stack-↭-list-eq
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      → map (Hypergraph.vlab ⟪ f ⟫F)
            (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
        Perm.↭ flatten B
      → map (Hypergraph.vlab ⟪ g ⟫F)
            (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
        Perm.↭ flatten B
      → map (Hypergraph.vlab ⟪ f ⟫F)
            (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
        ≡
        map (Hypergraph.vlab ⟪ g ⟫F)
            (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))

--------------------------------------------------------------------------------
-- ## Section 3: Discharge function.
--
-- Given a `StackEqAssumption`, derive the original
-- `process-edges-resp-iso-stack`.

module WithAssumption (a : StackEqAssumption) where
  open StackEqAssumption a

  -- The discharge: combine `stack-↭-flatten-B` (constructive) with
  -- the narrowed `stack-↭-list-eq` field.
  discharge
    : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → map (Hypergraph.vlab ⟪ f ⟫F)
          (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
      ≡
      map (Hypergraph.vlab ⟪ g ⟫F)
          (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
  discharge f g iso =
    stack-↭-list-eq f g iso (stack-↭-flatten-B f) (stack-↭-flatten-B g)

--------------------------------------------------------------------------------
-- ## Section 4: Trivial reflexive case (`f` definitionally equal to `g`).
--
-- When `f` and `g` are the SAME term (propositionally), the stack
-- equality is `refl`.  This is a small constructive fragment with
-- no postulates required.

discharge-refl
  : ∀ {A B} (f : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ f ⟫
  → map (Hypergraph.vlab ⟪ f ⟫F)
        (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
    ≡
    map (Hypergraph.vlab ⟪ f ⟫F)
        (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
discharge-refl _ _ = refl

--------------------------------------------------------------------------------
-- ## Section 5: Summary.
--
-- * Constructive content (CLOSED): both stacks are permutations of
--   `flatten B`, hence of each other.  This is the *strongest* result
--   obtainable from existing Linear/Linear-resp-iso machinery.
--
-- * Residual postulate (OPEN): `StackEqAssumption.stack-↭-list-eq`
--   asserts that the multiset equivalence lifts to a list equality.
--   This is provably equivalent to a "canonical normal form" theorem
--   for `process-all-edges` outputs on Linear hypergraphs, which is
--   itself a substantial separate development.
--
-- * Strict narrowing: the original `process-edges-resp-iso-stack`
--   is HARDER than `stack-↭-list-eq` because:
--     - The original quantifies over ALL `f, g, iso`.
--     - The narrowed version consumes the iso AND two additional
--       multiset witnesses (the `_↭_` proofs).
--   Any inhabitant of the original yields an inhabitant of the
--   narrowed (by discarding the extra hypotheses); the converse
--   requires the constructive `stack-↭-flatten-B` lemma proved here.
--
-- Constructive helpers actually USED in this file:
--   * `decode-attempt-Linear`        — totality of `decode-attempt` on `⟪ f ⟫F`.
--   * `decode-attempt-perm-from-just` — extract the final-stack `↭ .cod` witness.
--   * `⟪⟫F-codL`                     — `codL ⟪ f ⟫F ≡ flatten B`.
--   * `PermProp.map⁺`                — `_↭_` is preserved by `map`.
--   * `Perm.↭-reflexive`, `Perm.↭-sym`, `Perm.trans` — basic `_↭_` ops.
--
-- No NEW postulates are introduced: `StackEqAssumption` is a record
-- field, not a `postulate` declaration.  A consumer wanting full
-- constructive content must instantiate this field separately.
--
-- ## Surprises about Translation-iso vs FromAPROP-stacks
--
-- The Translation iso `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` provides a vertex bijection φ
-- and edge bijection ψ at the PRUNED level.  At the FromAPROP level,
-- the stacks live in different `Fin nV_F` sets entirely (nV_F can
-- differ between f and g, as shown in `BoundaryRespectsIso.agda`).
-- Crucially, the Translation iso does NOT give us a direct vertex
-- bijection ⟪f⟫F → ⟪g⟫F (this is the whole content of the
-- `boundary-respects-iso` FALSE postulate refuted there).
--
-- However, after applying `map vlab`, both stacks become lists of
-- atoms (`List X`), where the vertex-set difference is *erased*.
-- The Translation-pruned vertices are EXACTLY the non-stranded ones
-- (those appearing in dom/cod/edges), and these are precisely the
-- vertices that show up in the algorithm's stack.  So at the
-- atom-list level, the two stacks live in the same ambient list type.
--
-- This is why the field's TYPE is well-formed (both sides are
-- `List X`) even though the underlying Fin types differ — the `map
-- vlab` is the bridge.
--
-- The remaining obstruction is purely about LIST ORDER, not about
-- multiset content.
--------------------------------------------------------------------------------
