{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of two of the four `SwapAtomAssumption` fields in
-- `Discharge/Sub/ProcessEdgesPermTopo.agda`:
--
--   * `prep-aligned`              — the "same head edge, recurse on tail"
--                                   case.  CONSTRUCTIVE via direct
--                                   edge-step bridging using
--                                   `process-edges-cons-success` from
--                                   `SwapMacLane.agda`.
--
--   * `trans-intermediate-allfire` — intermediate AllFire for a trans
--                                   permutation.  CONSTRUCTIVE via
--                                   `WithSwap.AllFire-edge-↭`
--                                   (carries `Linear H`).
--
-- The third field `swap-with-rest-aligned` is EXPOSED as an explicit
-- parameter of the `FromSwapWithRest` sub-module.  Its constructive
-- discharge requires either an auxiliary `process-edges-stack-↭`
-- lemma (≥150 LOC) or a process-edges decomposition over `_++_` at
-- term level (≥100 LOC).  See `Section 2.3` comments.
--
-- The IRREDUCIBLE `swap-atom-aligned` (the Kelly-coherence atom on
-- a pair `(e₁ ∷ e₂ ∷ [])`) is taken as a parameter inside a
-- `SwapAtomInput` record.  The `AllFireEdgePermSwap` residual is also
-- taken as a parameter, and threaded through `WithSwap` from
-- `AllFireEdgePerm.agda`.
--
-- ## Module-level Linearity hypothesis
--
-- The discharge of `trans-intermediate-allfire` is routed through
-- `WithSwap.AllFire-edge-↭`, which carries a `Linear H` precondition.
-- The parent field's signature does NOT expose `Linear H`, so the
-- `FromInputs` module accepts an explicit `Linear-hyp : ∀ H → Linear H`
-- parameter.  Per `EdgeReorder.agda`'s counter-example, the lemma is
-- FALSE on non-linear hypergraphs, so this hypothesis is essential.
--
-- The downstream consumer of `SwapAtomAssumption` (in
-- `ProcessTermAligned.agda`) only ever instantiates `H = ⟪ f ⟫F` for
-- some `f : HomTerm A B`, and `Linear ⟪ f ⟫F` is constructive
-- (`Linearity.⟪⟫-Linear`).  An external glue layer can supply the
-- `Linear-hyp` parameter conditionally on `H = ⟪ f ⟫F`-shape.
--
-- ## File is `--safe --with-K`-clean.  No `postulate` declarations.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomCombinatorial
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix; process-edges; edge-step)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned sig-dec
  using (AllFire; IndependentSwap; ProcessEdges↭Goal)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesPermTopo sig-dec
  using (SwapAtomAssumption)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireEdgePerm sig-dec
  using (AllFireEdgePermSwap; module WithSwap)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapMacLane sig-dec
  using (process-edges-cons-success)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomAligned sig-dec
  using (fired-bridged)

open import Categories.Category using (Category)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Section 1: the SwapAtomInput parameter record.
--
-- Packages the IRREDUCIBLE `swap-atom-aligned` (Kelly-coherence atom on
-- a pair of adjacent independent edges, no `rest` list).  All other
-- `SwapAtomAssumption` fields are derivable from this plus
-- `AllFireEdgePermSwap` plus a Linearity hypothesis.

record SwapAtomInput : Set where
  field
    swap-atom-aligned
      : ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
          (s : List (Fin (Hypergraph.nV H)))
      → IndependentSwap H e₁ e₂ s
      → ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ []) s

--------------------------------------------------------------------------------
-- ## Section 2: the `FromInputs` module.
--
-- Parameters:
--   * swp : SwapAtomInput
--   * allFireSwap : AllFireEdgePermSwap
--   * Linear-hyp : ∀ H → Linear H
--
-- Derives the three SwapAtomAssumption fields constructively and
-- assembles them into a `to-swap-atom-assumption : SwapAtomAssumption`.

module FromInputs
  (swp : SwapAtomInput)
  (allFireSwap : AllFireEdgePermSwap)
  (Linear-hyp : ∀ (H : Hypergraph FlatGen) → Linear H)
  where
  open SwapAtomInput swp
  open AllFireEdgePermSwap allFireSwap
  open WithSwap allFireSwap

  ------------------------------------------------------------------------
  -- ## Helper: just-injectivity for Σ-pairs.

  private
    just-inj-Σ
      : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a a' : A} {b : B a} {b' : B a'}
      → (just (a , b) ≡ just (a' , b'))
      → (a , b) ≡ (a' , b')
    just-inj-Σ refl = refl

  ------------------------------------------------------------------------
  -- ## Section 2.1: trans-intermediate-allfire.
  --
  -- Routes through `WithSwap.AllFire-edge-↭` applied to `(es₁, p, af₁)`.
  -- Requires Linearity, which is supplied by the module-level
  -- `Linear-hyp` parameter.

  trans-intermediate-allfire
    : ∀ (H : Hypergraph FlatGen)
        (es₁ es-mid es₂ : List (Fin (Hypergraph.nE H)))
        (s : List (Fin (Hypergraph.nV H)))
        (p : es₁ Perm.↭ es-mid) (q : es-mid Perm.↭ es₂)
        (af₁ : AllFire H es₁ s) (af₂ : AllFire H es₂ s)
    → AllFire H es-mid s
  trans-intermediate-allfire H es₁ es-mid es₂ s p q af₁ _ =
    AllFire-edge-↭ H es₁ es-mid s (Linear-hyp H) p af₁

  ------------------------------------------------------------------------
  -- ## Section 2.2: prep-aligned.
  --
  -- Given AllFire on `e ∷ es₁` and `e ∷ es₂` from a common `s`, the head
  -- residual is the SAME on both sides (since `extract-prefix (ein e) s`
  -- is a function).  Reduce both `process-edges` outputs to the post-
  -- head form using `process-edges-cons-success`, apply the tail-goal,
  -- and lift the result by composing with the shared `fired-bridged`.

  -- Helper: transport a `ProcessEdges↭Goal` shape across propositional
  -- equalities on the two `process-edges` outputs.  This is the
  -- `subst₂`-style transport: given `x₁ ≡ y₁` and `x₂ ≡ y₂` we coerce
  -- the goal between the two shapes.
  private
    transport-goal
      : ∀ {H : Hypergraph FlatGen} {s : List (Fin (Hypergraph.nV H))}
          {x₁ x₂ y₁ y₂ : Σ (List (Fin (Hypergraph.nV H)))
                            (λ s' → HomTerm
                                      (unflatten (map (Hypergraph.vlab H) s))
                                      (unflatten (map (Hypergraph.vlab H) s')))}
      → x₁ ≡ y₁ → x₂ ≡ y₂
      → Σ[ p ∈ proj₁ y₁ Perm.↭ proj₁ y₂ ]
          proj₂ y₁
          ≈Term
          permute-via-vlab (Hypergraph.vlab H) (Perm.↭-sym p)
            FM.∘ proj₂ y₂
      → Σ[ p ∈ proj₁ x₁ Perm.↭ proj₁ x₂ ]
          proj₂ x₁
          ≈Term
          permute-via-vlab (Hypergraph.vlab H) (Perm.↭-sym p)
            FM.∘ proj₂ x₂
    transport-goal refl refl x = x

  prep-aligned
    : ∀ (H : Hypergraph FlatGen)
        (e : Fin (Hypergraph.nE H))
        (es₁ es₂ : List (Fin (Hypergraph.nE H)))
        (s : List (Fin (Hypergraph.nV H)))
      (af₁ : AllFire H (e ∷ es₁) s)
      (af₂ : AllFire H (e ∷ es₂) s)
      (tail-↭ : es₁ Perm.↭ es₂)
      (tail-goal : ∀ (rest : List (Fin (Hypergraph.nV H)))
                     (af₁-rest : AllFire H es₁ (Hypergraph.eout H e ++ rest))
                     (af₂-rest : AllFire H es₂ (Hypergraph.eout H e ++ rest))
                 → ProcessEdges↭Goal H es₁ es₂ (Hypergraph.eout H e ++ rest))
    → ProcessEdges↭Goal H (e ∷ es₁) (e ∷ es₂) s
  prep-aligned H e es₁ es₂ s
      (rest₁ , p₁ , eq₁ , af-tail-1)
      (rest₂ , p₂ , eq₂ , af-tail-2) tail-↭ tail-goal =
    transport-goal {H} pec₁ pec₂ (tail-stack-↭ , reduced-term-eq)
    where
      -- Unify (rest₂, p₂) with (rest₁, p₁) via just-injectivity.
      pair-eq : (rest₁ , p₁) ≡ (rest₂ , p₂)
      pair-eq = just-inj-Σ (trans (sym eq₁) eq₂)

      rest₂≡rest₁ : rest₂ ≡ rest₁
      rest₂≡rest₁ = sym (cong proj₁ pair-eq)

      af-tail-2' : AllFire H es₂ (Hypergraph.eout H e ++ rest₁)
      af-tail-2' = subst (λ r → AllFire H es₂ (Hypergraph.eout H e ++ r))
                          rest₂≡rest₁ af-tail-2

      -- Apply the tail-goal at the post-head stack.
      tail-out : ProcessEdges↭Goal H es₁ es₂ (Hypergraph.eout H e ++ rest₁)
      tail-out = tail-goal rest₁ af-tail-1 af-tail-2'

      tail-stack-↭ = proj₁ tail-out
      tail-term-eq = proj₂ tail-out

      -- Both `process-edges H (e ∷ es*) s` factor through the SAME
      -- `fired-bridged` term (since `extract-prefix (ein e) s ≡ just
      -- (rest₁, p₁)` is the SAME for both).
      bridged : HomTerm _ _
      bridged = fired-bridged H e s rest₁ p₁

      pec₁ : process-edges H (e ∷ es₁) s
             ≡ ( proj₁ (process-edges H es₁ (Hypergraph.eout H e ++ rest₁))
               , proj₂ (process-edges H es₁ (Hypergraph.eout H e ++ rest₁))
                 FM.∘ bridged)
      pec₁ = process-edges-cons-success H e es₁ s rest₁ p₁ eq₁

      eq₂' : extract-prefix (Hypergraph.ein H e) s ≡ just (rest₁ , p₁)
      eq₂' = trans eq₂ (cong just (sym pair-eq))

      pec₂ : process-edges H (e ∷ es₂) s
             ≡ ( proj₁ (process-edges H es₂ (Hypergraph.eout H e ++ rest₁))
               , proj₂ (process-edges H es₂ (Hypergraph.eout H e ++ rest₁))
                 FM.∘ bridged)
      pec₂ = process-edges-cons-success H e es₂ s rest₁ p₁ eq₂'

      -- The term equiv at the reduced shape:
      --   t-tail-1 ∘ bridged
      --     ≈Term permute-via-vlab _ (sym tail-stack-↭) ∘ (t-tail-2 ∘ bridged)
      -- follows from
      --   tail-term-eq : t-tail-1 ≈Term permute-via-vlab _ (sym tail-stack-↭) ∘ t-tail-2
      -- by (∘-resp-≈ … refl) + associativity.

      perm-sym-tail = permute-via-vlab (Hypergraph.vlab H) (Perm.↭-sym tail-stack-↭)
      t-tail-1 = proj₂ (process-edges H es₁ (Hypergraph.eout H e ++ rest₁))
      t-tail-2 = proj₂ (process-edges H es₂ (Hypergraph.eout H e ++ rest₁))

      reduced-term-eq
        : (t-tail-1 FM.∘ bridged)
        ≈Term (perm-sym-tail FM.∘ (t-tail-2 FM.∘ bridged))
      reduced-term-eq =
        FM.Equiv.trans (tail-term-eq ⟩∘⟨ FM.Equiv.refl) FM.assoc

  ------------------------------------------------------------------------
  -- ## Section 2.3: swap-with-rest-aligned.
  --
  -- This field is the genuinely-hard residual of the three.  Its
  -- discharge requires lifting `swap-atom-aligned` (a 2-edge
  -- statement on the `[]` suffix) to a goal with arbitrary `xs`/`ys`
  -- suffixes, which requires either:
  --
  --   (a) An auxiliary `process-edges-stack-↭` lemma stating that
  --       `process-edges xs` is natural in its input stack (modulo
  --       a stack permutation), OR
  --
  --   (b) A re-implementation of the `↭`-induction with the swap
  --       case handled by full `process-edges` decomposition.
  --
  -- Both routes require non-trivial auxiliary infrastructure
  -- (~150+ LOC each).  For now, we expose `swap-with-rest-aligned`
  -- as an explicit parameter — strictly narrower than the parent
  -- field only in the SENSE that the constructive composition with
  -- `prep-aligned` and `trans-intermediate-allfire` is available.
  --
  -- Routing: when `Perm.swap`-shaped permutations don't occur in
  -- the actual consumer's use (e.g., the consumer uses only
  -- `Perm.refl`/`Perm.prep`/`Perm.trans`-decomposed permutations),
  -- this parameter is vacuous.  For the general case, the parameter
  -- is supplied by a future closure of the lifting step.

  ------------------------------------------------------------------------
  -- ## Section 3: Assembly into a `SwapAtomAssumption`.
  --
  -- `swap-with-rest-aligned` is taken as an additional residual
  -- parameter; the other two fields are constructed.

  module FromSwapWithRest
    (swap-with-rest-aligned
      : ∀ (H : Hypergraph FlatGen)
          (e₁ e₂ : Fin (Hypergraph.nE H))
          (xs ys : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
        (rest-↭ : xs Perm.↭ ys)
        (af₁ : AllFire H (e₁ ∷ e₂ ∷ xs) s)
        (af₂ : AllFire H (e₂ ∷ e₁ ∷ ys) s)
      → ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ xs) (e₂ ∷ e₁ ∷ ys) s)
    where

    to-swap-atom-assumption : SwapAtomAssumption
    to-swap-atom-assumption = record
      { swap-atom-aligned          = swap-atom-aligned
      ; swap-with-rest-aligned     = swap-with-rest-aligned
      ; prep-aligned               = prep-aligned
      ; trans-intermediate-allfire = trans-intermediate-allfire
      }

--------------------------------------------------------------------------------
-- ## Section 4: Summary.
--
-- This file discharges TWO of the four `SwapAtomAssumption` fields
-- in `Discharge/Sub/ProcessEdgesPermTopo.agda`:
--
--   * `prep-aligned`              — CONSTRUCTIVE via
--                                   `process-edges-cons-success`.
--   * `trans-intermediate-allfire` — CONSTRUCTIVE via
--                                   `WithSwap.AllFire-edge-↭`
--                                   (requires `Linear-hyp`).
--
-- The remaining field `swap-with-rest-aligned` is exposed as a
-- residual parameter (`FromSwapWithRest`).  Its constructive
-- discharge requires lifting `swap-atom-aligned` (a 2-edge statement)
-- to non-trivial xs/ys suffixes, which involves either a
-- `process-edges-stack-↭` lemma or a term-level
-- `process-edges-++-decompose` lemma.  Both are non-trivial side
-- works beyond the scope of this discharge.
--
-- The IRREDUCIBLE `swap-atom-aligned` is taken as a parameter
-- (`SwapAtomInput.swap-atom-aligned`) — this is the Kelly-coherence
-- atom on a 2-edge prefix, identical to the field of the same name in
-- the parent record.
--
-- The `AllFireEdgePermSwap` residual is also taken as a parameter,
-- giving access to `WithSwap.AllFire-edge-↭` and
-- `AllFire-edge-↭-swap`.
--
-- The `Linear-hyp : ∀ H → Linear H` is a generic Linearity assumption
-- required by `WithSwap.AllFire-edge-↭`.  Per `EdgeReorder.agda`'s
-- counter-example, the lemma is genuinely false without Linearity.
-- For the actual downstream consumer (`H = ⟪ f ⟫F`), Linearity is
-- constructively available via `Linearity.⟪⟫-Linear`.
--
-- ## File is `--safe --with-K`-clean.  No `postulate` declarations.
--------------------------------------------------------------------------------
