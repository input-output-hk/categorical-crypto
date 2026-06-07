{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic "Steps" infrastructure over a FreeMonoidalData with Symm ≤ v.
--
-- This module mirrors APROP's process-edges machinery
-- (`Categories/APROP/Hypergraph/Soundness/{Decode,Permute,Unflatten}.agda`)
-- minus the `Hypergraph FlatGen` wrapper.  Each `Step` packages a typed
-- morphism with its own ein/eout vertex lists; a `Steps = List Step`
-- replaces "list of edges of a hypergraph".
--
-- The module is parameterised over an abstract vertex set
-- `(n : ℕ) (vlab : Fin n → X)` — this is precisely the structure
-- supplied by a Hypergraph's `nV`/`vlab`, but no hypergraph is needed.
-- Stacks live in `List (Fin n)` (NOT `List X`), matching APROP exactly;
-- this lets `process-steps` be DEFINITIONALLY EQUAL to APROP's
-- `process-edges` after the trivial edge→step lift.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.Steps
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d

-- Generic `unflatten`, `unflatten-++-≅`, and `permute` (already defined
-- parametrically there).
open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; unflatten-++-≅; permute) public

open import Categories.Morphism FreeMonoidal using (_≅_; module ≅)

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; subst₂)
open import Relation.Nullary.Decidable using (yes; no)

--------------------------------------------------------------------------------
-- Generic `permute-via-vlab` — same definition as APROP's, but parameterised
-- only over a labelling function (no APROP signature).

permute-via-vlab
  : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X)
  → xs Perm.↭ ys
  → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
permute-via-vlab vlab p = permute (PermProp.map⁺ vlab p)

--------------------------------------------------------------------------------
-- Re-export generic `extract-elem` and `extract-prefix`.  Sharing the
-- definition with APROP's `Decode` lets the
-- `process-steps-maybe ≡ process-edges` correspondence in
-- `Discharge.APROPMacLaneFromSMC` reduce via the `with`-pattern.

open import Categories.Hypergraph.ExtractPrefix public
  using (extract-elem; extract-prefix)

--------------------------------------------------------------------------------
-- Parameterised section: abstract vertex set `(n, vlab)`.  All
-- step-level / stack-level / process-level definitions live here.

module _ (n : ℕ) (vlab : Fin n → X) where

  --------------------------------------------------------------------
  -- A "step": typed morphism between unflattened input/output lists.
  -- ein/eout are `List (Fin n)` — the morphism's type is determined
  -- by the vertex labelling `vlab`.

  Step : Set
  Step = Σ[ ein ∈ List (Fin n) ] Σ[ eout ∈ List (Fin n) ]
         HomTerm (unflatten (map vlab ein)) (unflatten (map vlab eout))

  Steps : Set
  Steps = List Step

  -- Convenience projections.
  ein-of : Step → List (Fin n)
  ein-of (ein , _ , _) = ein

  eout-of : Step → List (Fin n)
  eout-of (_ , eout , _) = eout

  op-of : (s : Step) → HomTerm (unflatten (map vlab (ein-of s)))
                                (unflatten (map vlab (eout-of s)))
  op-of (_ , _ , op) = op

  --------------------------------------------------------------------
  -- `splitJoin op rest`: apply a block morphism `op` to the `ein`-prefix
  -- of a `(ein ++ rest)` stack, identity on `rest`.  This is the clean,
  -- permute-free core of `fire-bridged` — it bundles the `map-++`
  -- `subst₂` and the two `unflatten-++-≅` half-isos into one named
  -- morphism, so downstream reasoning never manipulates `subst₂`.

  splitJoin
    : ∀ {ein eout : List (Fin n)}
    → HomTerm (unflatten (map vlab ein)) (unflatten (map vlab eout))
    → (rest : List (Fin n))
    → HomTerm (unflatten (map vlab (ein  ++ rest)))
              (unflatten (map vlab (eout ++ rest)))
  splitJoin {ein} {eout} op rest =
    subst₂ HomTerm
      (cong unflatten (sym (map-++ vlab ein  rest)))
      (cong unflatten (sym (map-++ vlab eout rest)))
      ( _≅_.to   (unflatten-++-≅ (map vlab eout) (map vlab rest))
        ∘ (op ⊗₁ id)
        ∘ _≅_.from (unflatten-++-≅ (map vlab ein) (map vlab rest)) )

  --------------------------------------------------------------------
  -- Apply one step at the front of a stack, given the locating
  -- permutation.  Body MATCHES APROP's `edge-step`-success branch
  -- exactly.

  fire-bridged
    : ∀ (e : Step) (s rest : List (Fin n))
    → s Perm.↭ ein-of e ++ rest
    → HomTerm (unflatten (map vlab s))
              (unflatten (map vlab (eout-of e ++ rest)))
  fire-bridged (ein , eout , op) s rest perm =
    splitJoin op rest ∘ permute-via-vlab vlab perm

  -- `fire-clean`: fire factors as a block application after a permute.
  -- Definitional (holds by `refl`), so downstream proofs can rewrite
  -- `fire-bridged` to `splitJoin _ _ ∘ permute-via-vlab _ _` for free.
  fire-clean
    : ∀ (e : Step) (s rest : List (Fin n))
        (p : s Perm.↭ ein-of e ++ rest)
    → fire-bridged e s rest p
      ≡ splitJoin (op-of e) rest ∘ permute-via-vlab vlab p
  fire-clean (ein , eout , op) s rest p = refl

  --------------------------------------------------------------------
  -- AllFire: each step's input list is locatable in the running stack.

  AllFire : Steps → List (Fin n) → Set
  AllFire []                       _ = ⊤
  AllFire ((ein , eout , _) ∷ es) s =
    Σ[ rest ∈ List (Fin n) ]
    Σ[ p ∈ s Perm.↭ ein ++ rest ]
      AllFire es (eout ++ rest)

  --------------------------------------------------------------------
  -- IndependentSwap: both orderings AllFire.

  IndependentSwap : Step → Step → List (Fin n) → Set
  IndependentSwap e₁ e₂ s =
    AllFire (e₁ ∷ e₂ ∷ []) s × AllFire (e₂ ∷ e₁ ∷ []) s

  --------------------------------------------------------------------
  -- Process a step list under an AllFire witness.  Returns (final
  -- stack, composed morphism).  Body MATCHES APROP's `process-edges`
  -- under the `just` branch of `edge-step`'s `extract-prefix`.

  process-steps
    : (es : Steps) (s : List (Fin n)) → AllFire es s
    → Σ[ s' ∈ List (Fin n) ]
        HomTerm (unflatten (map vlab s)) (unflatten (map vlab s'))
  process-steps []                       s _                   = (s , id)
  process-steps ((ein , eout , op) ∷ es) s (rest , perm , af) =
    let (s' , t) = process-steps es (eout ++ rest) af
    in  (s' , t ∘ fire-bridged (ein , eout , op) s rest perm)

  --------------------------------------------------------------------
  -- ProcessEdges↭Goal: stack permutation + term equation between two
  -- AllFire orderings of step lists with the same starting stack.

  ProcessEdges↭Goal : (es₁ es₂ : Steps) (s : List (Fin n))
      (af₁ : AllFire es₁ s) (af₂ : AllFire es₂ s) → Set
  ProcessEdges↭Goal es₁ es₂ s af₁ af₂ =
    Σ[ stack-↭ ∈
        proj₁ (process-steps es₁ s af₁)
        Perm.↭
        proj₁ (process-steps es₂ s af₂) ]
      proj₂ (process-steps es₁ s af₁)
      ≈Term
      permute-via-vlab vlab (Perm.↭-sym stack-↭)
        ∘ proj₂ (process-steps es₂ s af₂)

  --------------------------------------------------------------------
  -- Maybe-style `process-steps-maybe` matches APROP's `process-edges`
  -- structure exactly (with `with extract-prefix` and `nothing`
  -- fallback to `(s, id)`).  Used by atom (4)'s `ProcessEdges↭Goal-maybe`
  -- below — no AllFire required as a precondition, since the
  -- stack-↭ / b-stack-↭ inputs implicitly constrain the firing pattern.

  edge-step-maybe
    : (s : List (Fin n)) (e : Step)
    → Σ[ s' ∈ List (Fin n) ]
        HomTerm (unflatten (map vlab s)) (unflatten (map vlab s'))
  edge-step-maybe s (ein , eout , op) with extract-prefix ein s
  ... | nothing            = (s , id)
  ... | just (rest , perm) =
      ( eout ++ rest , fire-bridged (ein , eout , op) s rest perm )

  process-steps-maybe
    : (es : Steps) (s : List (Fin n))
    → Σ[ s' ∈ List (Fin n) ]
        HomTerm (unflatten (map vlab s)) (unflatten (map vlab s'))
  process-steps-maybe []       s = (s , id)
  process-steps-maybe (e ∷ es) s =
    let (s'  , t)  = edge-step-maybe       s  e
        (s'' , t') = process-steps-maybe   es s'
    in  (s'' , t' ∘ t)
