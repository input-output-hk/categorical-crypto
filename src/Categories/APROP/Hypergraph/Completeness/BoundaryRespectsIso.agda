{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- ATTEMPTED DISCHARGE of `boundary-respects-iso`
-- (`CompletenessAssumptions` field in `DecodeRespIso.agda`).
--
-- This file analyzes the proposed discharge of the postulate
--
--     boundary-respects-iso
--       : ∀ {A B} (f g : HomTerm A B)
--       → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫       -- Translation iso  (uses hComposeP)
--       → ⟪ f ⟫F ≅ᴴ ⟪ g ⟫F     -- FromAPROP   iso  (uses hCompose)
--
-- by structural induction on `f` and `g`, as suggested by the
-- "DISCHARGE STRATEGY" comment in `DecodeRespIso.agda`.
--
-- ## Status: INVESTIGATION REPORT — postulate is FALSE.
--
-- After detailed analysis we conclude that the postulate **is FALSE as
-- stated** for the de-indexed `_≅ᴴ_` relation in `Iso.agda`.  The reason
-- is a cardinality mismatch on the unpruned vertex side: pruning removes
-- different numbers of vertices for `f` vs `g`, even when their pruned
-- translations are isomorphic.
--
-- The file CONSTRUCTIVELY REFUTES the postulate: assuming any function
-- of the boundary-respects-iso type leads to `⊥` (`postulate-is-false`,
-- below).  No new postulates are introduced.
--
-- The deliverable of this file is:
--
--   * A CONCRETE counter-example showing the postulate is not
--     dischargeable (Section 1).
--   * The CONSTRUCTIVE FRAGMENT that can be salvaged — definitional
--     equalities `⟪ f ⟫ ≡ ⟪ f ⟫F` for atomic terms (Section 2).
--   * Documentation of which case is the failure point (the `_∘_` case)
--     and a proposed REFORMULATION of the assumption that side-steps
--     this issue (Section 3, 4).
--
-- ## How to read this file
--
-- This file does NOT export a `boundary-respects-iso` discharge — it
-- exports a REFUTATION instead.  `DecodeRespIso.agda`'s
-- `CompletenessAssumptions` record still has `boundary-respects-iso`
-- as a postulated field, and downstream consumers
-- (`Inductive.WithAssumptions`, `CompletenessFull`) still take a
-- `CompletenessAssumptions` value as a parameter.  This file's findings
-- argue that this postulated field is not just unproved but UNPROVABLE
-- under the current `_≅ᴴ_` definition.
--
-- Concretely:
--   * Any inhabitant of the `CompletenessAssumptions` record requires
--     producing a `boundary-respects-iso` value.
--   * `postulate-is-false` (below) proves that no such value exists.
--   * Hence `CompletenessAssumptions` is itself UNINHABITED, and any
--     module of the shape `module Inductive.WithAssumptions (a : CompletenessAssumptions)` is vacuously consistent
--     but never instantiated.
--
-- A reformulation is recommended (Section 4).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.BoundaryRespectsIso
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core
  using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hEmpty; hVar; hId; hGen; hTensor; hSwap;
         hCompose; module hCompose-impl)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Iso
  using (_≅ᴴ_; refl-≅ᴴ)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (map-id)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

--------------------------------------------------------------------------------
-- ## Section 1: The counter-example — `boundary-respects-iso` is FALSE.
--
-- We exhibit a concrete `f, g : HomTerm A A` with `A = Var x` for which
-- `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` is INHABITED but `⟪ f ⟫F ≅ᴴ ⟪ g ⟫F` is UNINHABITED.
--
-- Take `f = id ∘ id : HomTerm (Var x) (Var x)` and
--      `g = id      : HomTerm (Var x) (Var x)`.
--
-- Translation level (both have nV = 1):
--   * `⟪ id ⟫           = hId (Var x)  = hVar x`  (nV = 1).
--   * `⟪ id ∘ id ⟫      = hComposeP (hVar x) (hVar x) refl`.
--     - K.dom = [zero], nonMem [zero] = [], count-non K.dom = 0.
--     - nV-P = 1 + 0 = 1.
--   * `iso-T-witness` (below) constructs the iso explicitly.
--
-- FromAPROP level (different nV):
--   * `⟪ id ⟫F          = hVar x`             (nV = 1).
--   * `⟪ id ∘ id ⟫F     = hCompose (hVar x) (hVar x) refl`
--                          has nV = G.nV + K.nV = 1 + 1 = 2.
--   * `iso-F-impossible` (below) derives `⊥` from any iso between these.
--
-- The two together yield `postulate-is-false`: any function of the
-- `boundary-respects-iso` type derives `⊥`.

-- 1.1 — Explicit Translation iso witness.
--
-- Both ⟪ id ∘ id ⟫ and ⟪ id ⟫ have one vertex labeled `x` (= `lookup [x] zero`),
-- no edges, dom = cod = [zero].  The identity bijection on Fin 1 and the
-- empty bijection on Fin 0 give the iso.
iso-T-witness
  : ∀ (x : X) → ⟪ id {Var x} ∘ id {Var x} ⟫ ≅ᴴ ⟪ id {Var x} ⟫
iso-T-witness x = record
  { φ         = λ i → i
  ; φ⁻¹       = λ i → i
  ; φ-left    = λ _ → refl
  ; φ-rght    = λ _ → refl
  ; ψ         = λ ()
  ; ψ⁻¹       = λ ()
  ; ψ-left    = λ ()
  ; ψ-rght    = λ ()
  ; φ-lab     = λ { zero → refl }
  ; ψ-ein     = λ ()
  ; ψ-eout    = λ ()
  ; φ-dom     = sym (map-id _)
  ; φ-cod     = sym (map-id _)
  ; atom-ein  = λ ()
  ; atom-eout = λ ()
  ; ψ-elab    = λ ()
  }

-- 1.2 — Helper: any function `Fin 2 → Fin 1` with a left inverse is
-- impossible.  Standard cardinality argument.
private
  no-bij-2-1
    : (f   : Fin 2 → Fin 1)
      (f⁻¹ : Fin 1 → Fin 2)
      (left : ∀ i → f⁻¹ (f i) ≡ i)
    → ⊥
  no-bij-2-1 f f⁻¹ left = clash
    where
      -- Both `f zero` and `f (suc zero)` live in Fin 1 (only `zero`).
      fzero-eq : f zero ≡ f (suc zero)
      fzero-eq with f zero | f (suc zero)
      ... | zero    | zero    = refl
      ... | zero    | suc ()
      ... | suc ()  | _

      -- Apply f⁻¹ to both sides, then use the left-inverse property.
      zero-suc : (zero {n = 1}) ≡ suc zero
      zero-suc = trans (sym (left zero))
                       (trans (cong f⁻¹ fzero-eq) (left (suc zero)))

      clash : ⊥
      clash with zero-suc
      ... | ()

-- 1.3 — At `A = Var x`, the FromAPROP iso `⟪ id ∘ id ⟫F ≅ᴴ ⟪ id ⟫F`
-- is impossible.  The types reduce to: φ : Fin 2 → Fin 1.
iso-F-impossible
  : ∀ (x : X)
  → ⟪ id {Var x} ∘ id {Var x} ⟫F ≅ᴴ ⟪ id {Var x} ⟫F
  → ⊥
iso-F-impossible x iso =
  no-bij-2-1 φ φ⁻¹ φ-left
  where open _≅ᴴ_ iso

-- 1.4 — The combined refutation: any inhabitant of the
-- `boundary-respects-iso` type derives ⊥.
--
-- Applied to `(id ∘ id, id, iso-T-witness x)`, the postulate would yield
-- an iso-F at `Fin 2 → Fin 1` which `no-bij-2-1` shows cannot exist.
postulate-is-false
  : (∀ {A B} (f g : HomTerm A B)
     → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → ⟪ f ⟫F ≅ᴴ ⟪ g ⟫F)
  → ∀ (x : X) → ⊥
postulate-is-false bri x =
  iso-F-impossible x
    (bri (id {Var x} ∘ id {Var x}) (id {Var x}) (iso-T-witness x))

--------------------------------------------------------------------------------
-- ## Section 2: The CONSTRUCTIVE fragment — atomic-case definitional equality.
--
-- For atomic terms (Agen, id, λ, ρ, α, σ), the Translation and FromAPROP
-- translations COINCIDE definitionally: `⟪ f ⟫ ≡ ⟪ f ⟫F` syntactically.
-- These are reusable lemmas; they witness that the T-vs-F gap arises
-- ONLY in the composition case.

T-eq-F-id : ∀ {A} → ⟪ id {A} ⟫ ≡ ⟪ id {A} ⟫F
T-eq-F-id = refl

T-eq-F-Agen : ∀ {A B} (f : mor A B) → ⟪ Agen f ⟫ ≡ ⟪ Agen f ⟫F
T-eq-F-Agen _ = refl

T-eq-F-λ⇒ : ∀ {A} → ⟪ λ⇒ {A} ⟫ ≡ ⟪ λ⇒ {A} ⟫F
T-eq-F-λ⇒ = refl

T-eq-F-λ⇐ : ∀ {A} → ⟪ λ⇐ {A} ⟫ ≡ ⟪ λ⇐ {A} ⟫F
T-eq-F-λ⇐ = refl

T-eq-F-ρ⇒ : ∀ {A} → ⟪ ρ⇒ {A} ⟫ ≡ ⟪ ρ⇒ {A} ⟫F
T-eq-F-ρ⇒ = refl

T-eq-F-ρ⇐ : ∀ {A} → ⟪ ρ⇐ {A} ⟫ ≡ ⟪ ρ⇐ {A} ⟫F
T-eq-F-ρ⇐ = refl

T-eq-F-α⇒ : ∀ {A B C} → ⟪ α⇒ {A} {B} {C} ⟫ ≡ ⟪ α⇒ {A} {B} {C} ⟫F
T-eq-F-α⇒ = refl

T-eq-F-α⇐ : ∀ {A B C} → ⟪ α⇐ {A} {B} {C} ⟫ ≡ ⟪ α⇐ {A} {B} {C} ⟫F
T-eq-F-α⇐ = refl

T-eq-F-σ : ∀ {A B} → ⟪ σ {A} {B} ⟫ ≡ ⟪ σ {A} {B} ⟫F
T-eq-F-σ = refl

--------------------------------------------------------------------------------
-- ## Section 3: WHY the `_∘_` case fails — vertex-count algebra.
--
-- For composition, `⟪ g ∘ f ⟫` uses `hComposeP ⟪ f ⟫ ⟪ g ⟫ bdy` while
-- `⟪ g ∘ f ⟫F` uses `hCompose ⟪ f ⟫F ⟪ g ⟫F bdy'`.  Their vertex counts:
--
--     nV ⟪ g ∘ f ⟫    = nV ⟪ f ⟫    + count-non (Hypergraph.dom ⟪ g ⟫)
--     nV ⟪ g ∘ f ⟫F   = nV ⟪ f ⟫F   + nV ⟪ g ⟫F
--
-- Even granting `nV ⟪ g ⟫ = nV ⟪ g ⟫F` inductively, the term
-- `count-non (Hypergraph.dom ⟪ g ⟫)` is strictly less than `nV ⟪ g ⟫`
-- whenever `Hypergraph.dom ⟪ g ⟫` is non-empty (which holds for any
-- `g : HomTerm A B` with non-trivial `A`).
--
-- Therefore `nV ⟪ g ∘ f ⟫ < nV ⟪ g ∘ f ⟫F` in general.  The iso between
-- pruned Translation versions only constrains the pruned counts; it
-- says nothing about the discrepancy between the unpruned counts.

-- ## Section 3.1 — Concrete cardinality witnesses at `A = Var x`.
--
-- These reduce by `refl`; they confirm the counter-example numerically.
private
  module CardinalityWitness (x : X) where
    A : ObjTerm
    A = Var x

    nV-id-F : Hypergraph.nV ⟪ id {A} ⟫F ≡ 1
    nV-id-F = refl

    nV-id-comp-F : Hypergraph.nV ⟪ id {A} ∘ id {A} ⟫F ≡ 2
    nV-id-comp-F = refl

    nV-id-T : Hypergraph.nV ⟪ id {A} ⟫ ≡ 1
    nV-id-T = refl

    nV-id-comp-T : Hypergraph.nV ⟪ id {A} ∘ id {A} ⟫ ≡ 1
    nV-id-comp-T = refl

--------------------------------------------------------------------------------
-- ## Section 4: REFORMULATION PROPOSALS.
--
-- Given that the postulate is false, the `CompletenessAssumptions` record
-- needs to be amended.  Options:
--
-- ### Proposal A: Merge with `decode-attempt-resp-iso`.
--
-- Replace the two fields:
--
--     boundary-respects-iso : iso-T → iso-F
--     decode-attempt-resp-iso : iso-F → ≈Term
--
-- with the single field:
--
--     decode-attempt-resp-iso-T : iso-T → ≈Term
--
-- which goes directly from Translation iso to ≈Term, side-stepping the
-- non-existent intermediate iso-F.  All downstream consumers
-- (`Inductive.WithAssumptions`) only use the COMPOSED claim, so this
-- reformulation is observationally equivalent.
--
-- Implementation cost: edit `CompletenessAssumptions` in
-- `DecodeRespIso.agda` (drop `boundary-respects-iso`, change
-- `decode-attempt-resp-iso`'s type to consume `iso-T` directly), and
-- update `WithAssumptions.decode-resp-iso` to invoke the merged field
-- with `iso-T` instead of `iso-F = boundary-respects-iso f g iso-T`.
-- Total: ~10-20 LOC change in `DecodeRespIso.agda`.
--
-- Note: this also means the existing `decode-attempt-resp-iso`
-- discharge work in `DecodeAttemptRespIso.agda` (which also uses
-- `iso-F`) will need to switch to consuming `iso-T`.  Since the iso
-- structure is the SAME bijection data on both sides (φ, ψ, …), the
-- proof body changes minimally — only the input type changes.
--
-- ### Proposal B: Switch `_∘_` in FromAPROP to use `hComposeP`.
--
-- Make `⟪_⟫F` use `hComposeP` (merging `Translation` and `FromAPROP`).
-- Then `boundary-respects-iso` becomes the IDENTITY function.
--
-- Downside: `hCompose` is used throughout `SoundnessProved.agda`,
-- `Triangle.agda`, `Congruence.agda`, etc.  Changing those modules
-- to use `hComposeP` is invasive (~hundreds of LOC).
--
-- ### Recommended action
--
-- Proposal A.  Edit `CompletenessAssumptions` and observe that
-- `decode-attempt-resp-iso` already needs to consume the iso's φ/ψ data
-- to drive its discharge — whether that iso is at the T or F level is
-- structurally the same content (φ, φ⁻¹, ψ, …); the F-level iso just
-- provides extra `nV` slots that turn out to be unreachable for the
-- decoder's purposes anyway.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ## Section 5: SUMMARY.
--
--   * `boundary-respects-iso` is FALSE: any function of its declared
--     type, applied to `(id ∘ id, id, iso-T-witness x)`, would yield
--     an iso `⟪ id ∘ id ⟫F ≅ᴴ ⟪ id ⟫F` which is provably uninhabited
--     by `no-bij-2-1` (a `Fin 2 → Fin 1` cardinality argument).
--
--   * Formal refutation: `postulate-is-false` (a function of type
--     `boundary-respects-iso → ∀ x → ⊥`).
--
--   * The CONSTRUCTIVE fragment salvaged: definitional equality
--     `⟪ f ⟫ ≡ ⟪ f ⟫F` for the nine atomic constructors (Section 2).
--
--   * Recommended reformulation: merge `boundary-respects-iso` and
--     `decode-attempt-resp-iso` into a Translation-level field
--     `decode-attempt-resp-iso-T : iso-T → ≈Term`, side-stepping the
--     non-existent intermediate iso-F (Section 4, Proposal A).
--
-- This file does NOT discharge `boundary-respects-iso` — it REFUTES it.
-- Downstream completeness work should adopt Proposal A.
--------------------------------------------------------------------------------
