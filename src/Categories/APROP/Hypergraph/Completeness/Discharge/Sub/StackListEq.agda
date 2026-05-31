{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- # Discharge analysis of `StackEqAssumption.stack-↭-list-eq`.
--
-- ## Background
--
-- The sub-postulate `stack-↭-list-eq` (introduced by `Discharge/StackEq.agda`
-- as the narrowest residual gap from `process-edges-resp-iso-stack`) asks:
--
--     ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--     → (perm-f : map vlab-f (final-stack-f) ↭ flatten B)
--     → (perm-g : map vlab-g (final-stack-g) ↭ flatten B)
--     → map vlab-f (final-stack-f) ≡ map vlab-g (final-stack-g)
--
-- where `final-stack-h = proj₁ (process-all-edges ⟪ h ⟫F (Hypergraph.dom ⟪ h ⟫F))`.
--
-- The two hypotheses say both vlab-mapped stacks are permutations of
-- `flatten B`.  The conclusion asks they be LIST-EQUAL.
--
-- ## Outcome: B — `stack-↭-list-eq` is FALSE in general.
--
-- This file constructs a CONCRETE COUNTER-EXAMPLE showing the
-- sub-postulate is not dischargeable as stated.  Following the
-- `BoundaryRespectsIso.agda` pattern, it exposes a refutation
-- `postulate-is-false : (any-discharge-of-stack-↭-list-eq) → ⊥`
-- (parametrised on the existence of 4 distinct atoms and 2 generators).
--
-- The iso witness is constructed FULLY EXPLICITLY (no postulates) —
-- all 14 record fields, including the `subst₂`-laden `ψ-elab`,
-- discharge by `refl`-pattern-match on `Fin 4` / `Fin 2`.
--
-- ## The counter-example
--
-- Take 4 atoms `x, y, z, w : X` (with `z ≢ w`), and two generators
--
--   φ₁ : mor (Var x) (Var z)
--   φ₂ : mor (Var y) (Var w)
--
-- Define
--
--   f, g : HomTerm (Var x ⊗₀ Var y) (Var z ⊗₀ Var w)
--   f = Agen φ₁ ⊗₁ Agen φ₂
--   g = σ {Var w}{Var z} ∘ (Agen φ₂ ⊗₁ Agen φ₁) ∘ σ {Var x}{Var y}
--
-- The Translation iso `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` is constructed below
-- (`iso-witness`), with non-identity edge bijection `ψ = swap`.  But:
--
--   * `map vlab-f (final-stack ⟪ f ⟫F) ≡ w ∷ z ∷ []`
--   * `map vlab-g (final-stack ⟪ g ⟫F) ≡ z ∷ w ∷ []`
--
-- These two lists are NOT propositionally equal (the head equation
-- forces `w ≡ z`, violating `z≢w`).  Hence the sub-postulate's
-- conclusion (list equality) cannot hold.
--
-- ## Why the iso constraint is INSUFFICIENT
--
-- The Translation iso identifies `f`'s and `g`'s pruned hypergraphs
-- via an edge bijection `ψ`.  But `process-all-edges` runs on the
-- UNPRUNED `⟪ _ ⟫F` versions and processes edges in NATURAL Fin order
-- (i.e. `[0, 1, …, nE-1]`).  When `ψ` is not the identity, G's
-- natural order corresponds to K's permuted order — exactly the case
-- EdgeReorder.agda's counter-example shows produces DIFFERENT stack
-- orderings.
--
-- Concretely in our example:
--   * `⟪ f ⟫F`'s natural order: process φ₁ (eout=z) first, then φ₂
--     (eout=w prepended).  Final-stack maps to `[w, z]`.
--   * `⟪ g ⟫F`'s natural order: process the σ-σ inner φ₂ first
--     (eout=w), then φ₁ (eout=z prepended).  Final-stack maps to
--     `[z, w]`.
--
-- The two algorithms prepend different generators' codomain atoms first,
-- producing different orderings of `flatten (Var z ⊗ Var w) = z ∷ w ∷ []`.
--
-- ## What this file delivers
--
--   1. The CONSTRUCTIVE iso witness `iso-witness : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫`.
--   2. The CONSTRUCTIVE REFUTATION `postulate-is-false`.
--   3. A `Reformulation` discussion: the narrowed `stack-↭-list-eq`
--      should be weakened to `_↭_` rather than `_≡_`, OR the field
--      `process-edges-resp-iso-stack` (parent) should be refactored.
--
-- No new postulates introduced.  The file is `--safe --with-K`-clean.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackListEq
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hEmpty; hVar; hId; hGen; hTensor; hSwap;
         hCompose; module hCompose-impl)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)

--------------------------------------------------------------------------------
-- ## Section 1: The type signature of the sub-postulate we are refuting.
--
-- This is the EXACT signature of `StackEqAssumption.stack-↭-list-eq`
-- from `Discharge/StackEq.agda`, expanded inline.

StackEq-Type : Set
StackEq-Type =
  ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
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
-- ## Section 2: Setup — the parameters of the counter-example.
--
-- We parametrise on:
--   * 4 atoms (x, y, z, w : X) — used for the boundary atoms.
--   * A "z ≢ w" witness — atoms z and w must be distinct so that
--     the two stack orderings `[w, z]` and `[z, w]` are
--     propositionally distinct lists.
--   * Two generators φ₁ : mor (Var x) (Var z), φ₂ : mor (Var y) (Var w).
--
-- These four atoms and two generators are NOT assumed to exist in
-- every signature — only in signatures rich enough to expose the
-- counter-example.  The refutation is parameterised over the
-- existence of such data.

module CounterExample
  (x y z w : X)
  (z≢w : z ≡ w → ⊥)
  (φ₁ : mor (Var x) (Var z))
  (φ₂ : mor (Var y) (Var w))
  where

  --------------------------------------------------------------------
  -- ### 2.1 — The two parallel terms.

  A B : ObjTerm
  A = Var x ⊗₀ Var y
  B = Var z ⊗₀ Var w

  -- "Parallel" form: φ₁ on left, φ₂ on right.
  f : HomTerm A B
  f = Agen φ₁ ⊗₁ Agen φ₂

  -- "Swapped" form: swap, parallel in opposite order, swap back.
  --   σ : (Var x ⊗ Var y) → (Var y ⊗ Var x)
  --   (Agen φ₂) ⊗ (Agen φ₁) : (Var y ⊗ Var x) → (Var w ⊗ Var z)
  --   σ : (Var w ⊗ Var z) → (Var z ⊗ Var w)
  g : HomTerm A B
  g = σ {Var w} {Var z} ∘ (Agen φ₂ ⊗₁ Agen φ₁) ∘ σ {Var x} {Var y}

  --------------------------------------------------------------------
  -- ### 2.2 — Stack outputs.
  --
  -- We claim:
  --
  --     map vlab (final-stack ⟪ f ⟫F) ≡ w ∷ z ∷ []
  --     map vlab (final-stack ⟪ g ⟫F) ≡ z ∷ w ∷ []
  --
  -- Both reduce to the literal forms via Agda's definitional reduction
  -- on the algorithm's `process-all-edges` (which is fully recursive
  -- on the concrete edge list).
  --
  -- ⟪ f ⟫F = hTensor (hGen φ₁) (hGen φ₂):
  --   nV = 4, vlab = [x, z, y, w], dom = [0, 2], cod = [1, 3], nE = 2.
  --   ein 0 = [0], eout 0 = [1]; ein 1 = [2], eout 1 = [3].
  --
  -- process-all-edges trace:
  --   Stack = [0, 2].
  --   Edge 0: ein=[0] found at position 0.  New stack = [1, 2].
  --   Edge 1: ein=[2] found at position 1.  New stack = [3, 1].
  --   Final: [3, 1].  map vlab = [vlab 3, vlab 1] = [w, z].
  --
  -- ⟪ g ⟫F = hCompose (hCompose ⟪σ⟫F ⟪Agen φ₂ ⊗ Agen φ₁⟫F _) ⟪σ⟫F _:
  --   nV = 8 (G.nV=6 + K.nV=2 from outer hCompose).
  --   The natural edge order processes φ₂ first (eout's remapped to
  --   the w-vertex), then φ₁ (eout's remapped to the z-vertex,
  --   prepended).  Final stack maps to [z, w].

  stack-f : List X
  stack-f = map (Hypergraph.vlab ⟪ f ⟫F)
                (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))

  stack-g : List X
  stack-g = map (Hypergraph.vlab ⟪ g ⟫F)
                (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))

  stack-f-≡ : stack-f ≡ w ∷ z ∷ []
  stack-f-≡ = refl

  stack-g-≡ : stack-g ≡ z ∷ w ∷ []
  stack-g-≡ = refl

  --------------------------------------------------------------------
  -- ### 2.3 — Both stacks ↭ flatten B = z ∷ w ∷ [].

  perm-f : stack-f Perm.↭ flatten B
  perm-f rewrite stack-f-≡ =
    Perm.swap w z Perm.refl

  perm-g : stack-g Perm.↭ flatten B
  perm-g rewrite stack-g-≡ = Perm.refl

  --------------------------------------------------------------------
  -- ### 2.4 — The Translation iso `⟪ f ⟫ ≅ᴴ ⟪ g ⟫`.
  --
  -- All 14 fields are constructively verified (most discharge by
  -- `refl` after a single Fin-pattern-match).
  --
  -- ⟪ f ⟫: vlab = [x, z, y, w], dom = [0, 2], cod = [1, 3], nE = 2.
  -- ⟪ g ⟫: vlab = [x, y, w, z], dom = [0, 1], cod = [3, 2], nE = 2.
  --   ein 0 = [1], eout 0 = [2] (φ₂ : y → w, after remapping).
  --   ein 1 = [0], eout 1 = [3] (φ₁ : x → z, after remapping).
  --
  -- The bijection:
  --   φ : Fin 4 → Fin 4 = [0↦0, 1↦3, 2↦1, 3↦2]
  --     (preserves labels: x↦x, z↦z, y↦y, w↦w).
  --   ψ : Fin 2 → Fin 2 = swap (since g's edge 0 is φ₂, but f's
  --     edge 0 is φ₁).

  private
    φ-bij : Fin 4 → Fin 4
    φ-bij zero                   = zero
    φ-bij (suc zero)             = suc (suc (suc zero))
    φ-bij (suc (suc zero))       = suc zero
    φ-bij (suc (suc (suc zero))) = suc (suc zero)
    φ-bij (suc (suc (suc (suc ()))))

    φ⁻¹-bij : Fin 4 → Fin 4
    φ⁻¹-bij zero                   = zero
    φ⁻¹-bij (suc zero)             = suc (suc zero)
    φ⁻¹-bij (suc (suc zero))       = suc (suc (suc zero))
    φ⁻¹-bij (suc (suc (suc zero))) = suc zero
    φ⁻¹-bij (suc (suc (suc (suc ()))))

    φ-left-pf : ∀ i → φ⁻¹-bij (φ-bij i) ≡ i
    φ-left-pf zero                   = refl
    φ-left-pf (suc zero)             = refl
    φ-left-pf (suc (suc zero))       = refl
    φ-left-pf (suc (suc (suc zero))) = refl
    φ-left-pf (suc (suc (suc (suc ()))))

    φ-rght-pf : ∀ i → φ-bij (φ⁻¹-bij i) ≡ i
    φ-rght-pf zero                   = refl
    φ-rght-pf (suc zero)             = refl
    φ-rght-pf (suc (suc zero))       = refl
    φ-rght-pf (suc (suc (suc zero))) = refl
    φ-rght-pf (suc (suc (suc (suc ()))))

    ψ-bij : Fin 2 → Fin 2
    ψ-bij zero       = suc zero
    ψ-bij (suc zero) = zero
    ψ-bij (suc (suc ()))

    ψ⁻¹-bij : Fin 2 → Fin 2
    ψ⁻¹-bij zero       = suc zero
    ψ⁻¹-bij (suc zero) = zero
    ψ⁻¹-bij (suc (suc ()))

    ψ-left-pf : ∀ e → ψ⁻¹-bij (ψ-bij e) ≡ e
    ψ-left-pf zero       = refl
    ψ-left-pf (suc zero) = refl
    ψ-left-pf (suc (suc ()))

    ψ-rght-pf : ∀ e → ψ-bij (ψ⁻¹-bij e) ≡ e
    ψ-rght-pf zero       = refl
    ψ-rght-pf (suc zero) = refl
    ψ-rght-pf (suc (suc ()))

    φ-lab-pf : ∀ i → Hypergraph.vlab ⟪ g ⟫ (φ-bij i) ≡ Hypergraph.vlab ⟪ f ⟫ i
    φ-lab-pf zero                   = refl
    φ-lab-pf (suc zero)             = refl
    φ-lab-pf (suc (suc zero))       = refl
    φ-lab-pf (suc (suc (suc zero))) = refl
    φ-lab-pf (suc (suc (suc (suc ()))))

    ψ-ein-pf : ∀ e → Hypergraph.ein ⟪ g ⟫ (ψ-bij e)
                    ≡ map φ-bij (Hypergraph.ein ⟪ f ⟫ e)
    ψ-ein-pf zero       = refl  -- g.ein 1 = [0] = map φ [0]
    ψ-ein-pf (suc zero) = refl  -- g.ein 0 = [1] = map φ [2]
    ψ-ein-pf (suc (suc ()))

    ψ-eout-pf : ∀ e → Hypergraph.eout ⟪ g ⟫ (ψ-bij e)
                    ≡ map φ-bij (Hypergraph.eout ⟪ f ⟫ e)
    ψ-eout-pf zero       = refl  -- g.eout 1 = [3] = map φ [1]
    ψ-eout-pf (suc zero) = refl  -- g.eout 0 = [2] = map φ [3]
    ψ-eout-pf (suc (suc ()))

    φ-dom-pf : Hypergraph.dom ⟪ g ⟫ ≡ map φ-bij (Hypergraph.dom ⟪ f ⟫)
    φ-dom-pf = refl  -- g.dom = [0,1]; map φ [0,2] = [0,1]

    φ-cod-pf : Hypergraph.cod ⟪ g ⟫ ≡ map φ-bij (Hypergraph.cod ⟪ f ⟫)
    φ-cod-pf = refl  -- g.cod = [3,2]; map φ [1,3] = [3,2]

    atom-ein-pf : ∀ e
                → map (Hypergraph.vlab ⟪ g ⟫) (Hypergraph.ein ⟪ g ⟫ (ψ-bij e))
                ≡ map (Hypergraph.vlab ⟪ f ⟫) (Hypergraph.ein ⟪ f ⟫ e)
    atom-ein-pf zero       = refl
    atom-ein-pf (suc zero) = refl
    atom-ein-pf (suc (suc ()))

    atom-eout-pf : ∀ e
                 → map (Hypergraph.vlab ⟪ g ⟫) (Hypergraph.eout ⟪ g ⟫ (ψ-bij e))
                 ≡ map (Hypergraph.vlab ⟪ f ⟫) (Hypergraph.eout ⟪ f ⟫ e)
    atom-eout-pf zero       = refl
    atom-eout-pf (suc zero) = refl
    atom-eout-pf (suc (suc ()))

    ψ-elab-pf : ∀ e
              → subst₂ FlatGen (atom-ein-pf e) (atom-eout-pf e)
                       (Hypergraph.elab ⟪ g ⟫ (ψ-bij e))
              ≡ Hypergraph.elab ⟪ f ⟫ e
    ψ-elab-pf zero       = refl
    ψ-elab-pf (suc zero) = refl
    ψ-elab-pf (suc (suc ()))

  -- The constructive iso witness.
  iso-witness : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  iso-witness = record
    { φ         = φ-bij
    ; φ⁻¹       = φ⁻¹-bij
    ; φ-left    = φ-left-pf
    ; φ-rght    = φ-rght-pf
    ; ψ         = ψ-bij
    ; ψ⁻¹       = ψ⁻¹-bij
    ; ψ-left    = ψ-left-pf
    ; ψ-rght    = ψ-rght-pf
    ; φ-lab     = φ-lab-pf
    ; ψ-ein     = ψ-ein-pf
    ; ψ-eout    = ψ-eout-pf
    ; φ-dom     = φ-dom-pf
    ; φ-cod     = φ-cod-pf
    ; atom-ein  = atom-ein-pf
    ; atom-eout = atom-eout-pf
    ; ψ-elab    = ψ-elab-pf
    }

--------------------------------------------------------------------------------
-- ## Section 3: The refutation.
--
-- Given any function of type `StackEq-Type` (i.e. any putative
-- discharge of `stack-↭-list-eq`), we apply it to our counter-example
-- and derive `⊥` from the resulting equation between `[w, z]` and
-- `[z, w]` (using `z≢w`).

module Refutation
  (x y z w : X)
  (z≢w : z ≡ w → ⊥)
  (φ₁ : mor (Var x) (Var z))
  (φ₂ : mor (Var y) (Var w))
  where

  open CounterExample x y z w z≢w φ₁ φ₂

  -- A list-level equation `[w, z] ≡ [z, w]` implies `w ≡ z` (by
  -- taking the head), which violates `z≢w`.
  list-eq-impossible : w ∷ z ∷ [] ≡ z ∷ w ∷ [] → ⊥
  list-eq-impossible eq with eq
  ... | refl = z≢w refl

  -- The refutation: any function discharging `stack-↭-list-eq`
  -- applied to our counter-example yields the impossible equation.
  postulate-is-false : StackEq-Type → ⊥
  postulate-is-false discharge =
    list-eq-impossible
      (trans (sym stack-f-≡)
        (trans (discharge f g iso-witness perm-f perm-g)
                stack-g-≡))

--------------------------------------------------------------------------------
-- ## Section 4: Discussion and reformulation proposal.
--
-- The refutation above shows that the literal `stack-↭-list-eq` field
-- is not dischargeable.  Several options for moving forward:
--
-- ### Option A: Weaken the field to `_↭_`.
--
-- The PARENT field `process-edges-resp-iso-stack` was originally:
--
--     ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
--     → map vlab-f (final-stack-f) ≡ map vlab-g (final-stack-g)
--
-- The `Discharge/StackEq.agda` work proved the `_↭_` version
-- CONSTRUCTIVELY (`stack-↭-from-iso`).  The remaining gap (`_≡_` vs
-- `_↭_`) is exactly what this file's counter-example exhibits.
--
-- Reformulating the parent field to require only `_↭_`:
--
--     process-edges-resp-iso-stack
--       : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
--       → map vlab-f (final-stack-f) Perm.↭ map vlab-g (final-stack-g)
--
-- is then immediately discharged by `Discharge/StackEq.stack-↭-from-iso`
-- (no postulate needed).  However, downstream consumers (notably
-- `process-edges-resp-iso-term` and the `subst₂ HomTerm` plumbing in
-- `DecodeRespIso.agda`) currently rely on the `_≡_` form to align
-- boundary types.  Weakening to `_↭_` requires propagating the
-- weakening through the entire chain — non-trivial refactor.
--
-- ### Option B: Add a topological-success precondition.
--
-- The `EdgeReorder.agda` analysis (existing in this codebase) suggests
-- the correct precondition is `AllFire H natural-Fin-order` plus
-- `AllFire H (map ψ⁻¹ natural-Fin-order)`.  Under both AllFire
-- preconditions, the algorithm's output IS invariant.  However,
-- the AllFire predicate is itself non-trivial to discharge for
-- translated hypergraphs.
--
-- ### Option C: Replace `process-edges-resp-iso-stack` by an
-- `≈Term`-level statement.
--
-- Skip the list-equality entirely and go directly to a `≈Term`
-- statement at the HomTerm level.  This is the long-term direction
-- (see `Discharge/Sub/ProcessTermAligned.agda` for the existing
-- decomposition).
--
-- ### Recommendation
--
-- Adopt Option A (weaken to `_↭_`).  This is the change that minimises
-- algebraic content of the assumptions: the `_↭_` version is
-- constructively true; the `_≡_` version is false.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ## Section 5: SUMMARY.
--
--   * `stack-↭-list-eq` (the residual sub-postulate from
--     `Discharge/StackEq.agda`) is FALSE in general.  The
--     `Refutation` module above constructs an explicit counter-example
--     parametrised on 4 distinct atoms + 2 generators (along with a
--     fully constructive iso witness `iso-witness`).
--
--   * The strongest result derivable constructively is the `_↭_`
--     version (`Discharge/StackEq.stack-↭-from-iso`).  The list
--     equality is too strong: process-all-edges' natural-Fin-order
--     processing produces orderings that depend on edge structure,
--     and the iso's `ψ` (when non-identity) creates a mismatch.
--
--   * Recommended: weaken the parent
--     `process-edges-resp-iso-stack` field to `_↭_`, propagating the
--     weakening downstream.  This eliminates the entire sub-postulate
--     chain `StackEqAssumption.stack-↭-list-eq`.
--
--   * No new postulates introduced: all 14 fields of the iso, plus
--     the stack computations, plus the refutation, are
--     `--safe`-checked.
--------------------------------------------------------------------------------
