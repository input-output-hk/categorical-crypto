{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `edge-step` as an inductive relation (`EdgeStepR`, its graph), with the
-- two "view" lemmas:
--   * `edge-step-graph` : the function realises the relation;
--   * `edge-step-sound` : the relation pins the function value.
--
-- Case analysis on the relation's constructors (`skipR`/`fireR`) avoids the
-- green-slime with-abstraction of the opaque `edge-step`: once the FIRE/SKIP
-- branch is a constructor carrying its `extract-prefix` evidence, downstream
-- proofs never have to re-run the `with` buried inside `edge-step`.  See
-- `Categories.Examples.RelationViewGreenSlime` for the same technique distilled
-- to toy types.
--
-- `edge-step` is the demoted bare-stack fold
-- `List (Fin nV) → Fin nE → List (Fin nV)` (Review-2 F2 weak-decoder demotion);
-- `EdgeStepR` is the graph of that stack function.  The FIRE branch no longer
-- carries a `HomTerm` factor, so the relation is indexed by the output stack
-- alone.
--
-- OFF-CONE DEMONSTRATION: nothing imports this module.  The load-bearing copy
-- of `EdgeStepR`/`edge-step-graph` is private to
-- `Soundness.Discharge.SwapValidity`, which needs it at the `↭`-respect
-- lemmas; this file exists to present the same construction on its own.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.Examples.EdgeStepRelation
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (edge-step; extract-prefix)

open import Data.Fin using (Fin)
open import Data.List using (List; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)

module _ (G : Hypergraph FlatGen) where
  private module G = Hypergraph G

  -- The graph of the stack fold `edge-step G`: `skipR` records the FIRE test
  -- failing (stack unchanged); `fireR` records it succeeding with the located
  -- residual `rest` (drop `G.ein e`, prepend `G.eout e`).
  data EdgeStepR (s : List (Fin G.nV)) (e : Fin G.nE)
       : List (Fin G.nV) → Set where
    skipR : extract-prefix (G.ein e) s ≡ nothing → EdgeStepR s e s
    fireR : ∀ (rest : List (Fin G.nV)) (perm : s Perm.↭ G.ein e ++ rest)
          → extract-prefix (G.ein e) s ≡ just (rest , perm)
          → EdgeStepR s e (G.eout e ++ rest)

  -- The function realises the relation.
  edge-step-graph
    : ∀ (s : List (Fin G.nV)) (e : Fin G.nE)
    → EdgeStepR s e (edge-step G s e)
  edge-step-graph s e with extract-prefix (G.ein e) s in eq
  ... | nothing            = skipR eq
  ... | just (rest , perm) = fireR rest perm eq

  -- The relation pins the function value.
  edge-step-sound
    : ∀ {s : List (Fin G.nV)} {e : Fin G.nE} {s' : List (Fin G.nV)}
    → EdgeStepR s e s'
    → edge-step G s e ≡ s'
  edge-step-sound (skipR eq)           rewrite eq = refl
  edge-step-sound (fireR rest perm eq) rewrite eq = refl
