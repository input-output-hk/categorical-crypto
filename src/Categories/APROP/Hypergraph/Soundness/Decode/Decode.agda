{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The cospan-form decode algorithm (STACK/TOTALITY SKELETON).  For a
-- hypergraph `H`, run a stack fold and decide whether it lands on `H.cod`:
--
--   1. Start with stack `s = H.dom`.
--   2. For each edge `e` (in natural Fin order): if `H.ein e` is a
--      sub-multiset prefix of the stack, drop it and prepend `H.eout e`;
--      otherwise skip (stack unchanged).
--   3. Finally extract `H.cod` as a full sub-multiset of the final stack;
--      `decode-attempt` is the TOTALITY WITNESS `Maybe (s_final ↭ H.cod)`.
--
-- The `nothing` case captures non-linear inputs and non-topologically-
-- sound edge orders.  For `⟪ f ⟫` the natural Fin order is sound, so
-- `decode-attempt ⟪ f ⟫` always returns `just _`.
--
-- NOTE (weak-decoder demotion, Review-2 F2): this decoder used to also
-- build a `HomTerm` alongside the stack, but the live (strict) pipeline
-- reads only the stack trajectory + this totality witness — the morphism
-- value was never observed.  The `HomTerm` apparatus (`Agen-edge`, the
-- `unflatten-++-≅`/`permute-via-vlab` per-edge wrapping, `final-permute`)
-- has therefore been deleted; the generic per-edge generator survives as
-- the top-level `Agen-edge-aux`, still used by the rewrite-engine decoder.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Decode.Decode (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig

open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig


open import Data.Fin
open import Data.Fin.Properties
open import Data.List
open import Data.List.Properties
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality

open import Relation.Nullary

--------------------------------------------------------------------------------
-- Multiset search (hypergraph-independent).  `extract-elem`/`extract-prefix`
-- are re-exported from a generic module so APROP and SMC versions are
-- definitionally equal.

open import Categories.Hypergraph.ExtractPrefix public
  using (extract-elem; extract-prefix)

-- Specialised search for an exact multiset match: look for `ks`
-- with empty residual.  Used at the final step to bridge to `H.cod`.
extract-exact : ∀ {n} (ks xs : List (Fin n)) → Maybe (xs Perm.↭ ks)
extract-exact ks xs with extract-prefix ks xs
... | nothing       = nothing
... | just ([]    , p) = just (Perm.trans p (PermProp.++-identityʳ ks))
... | just (_ ∷ _ , _) = nothing

--------------------------------------------------------------------------------
-- Apply an edge: recover the generator `g : mor A B` from `FlatGen.flat`,
-- then wrap with the unflatten-flatten coherence iso on each side.
-- Top-level (not under the `H` module) so downstream files can
-- `cong`-rewrite `Agen-edge` along `elab` equations without an `H` arg.
Agen-edge-aux
  : ∀ {ins outs : List X} → FlatGen ins outs
  → HomTerm (unflatten ins) (unflatten outs)
Agen-edge-aux (flat-rec {A} {B} okA okB g) =
  subst₂ (λ a b → HomTerm (unflatten a) (unflatten b)) okA okB
    (_≅_.from (unflatten-flatten-≈ B) ∘ Agen g ∘ _≅_.to (unflatten-flatten-≈ A))

--------------------------------------------------------------------------------
-- The cospan algorithm, with `H` fixed.

module _ (H : Hypergraph FlatGen) where

  private
    module H = Hypergraph H

  --------------------------------------------------------------------
  -- Per-edge step (stack fold).  On finding `H.ein e` in the stack: drop
  -- it and prepend `H.eout e`.  On failure: identity on the stack.

  edge-step
    : (s : List (Fin H.nV)) (e : Fin H.nE)
    → List (Fin H.nV)
  edge-step s e with extract-prefix (H.ein e) s
  ... | nothing            = s
  ... | just (rest , perm) = H.eout e ++ rest

  -- Generic `edge-step` reduction lemmas, proven once over the ABSTRACT `H`.
  -- Call sites (hTensor/hComposeP liftings) feed the already-transported
  -- `extract-prefix` equation here instead of forcing `edge-step` of a large
  -- computed `H` to normalise at the use site.
  edge-step-just
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
        {rest : List (Fin H.nV)} {perm}
    → extract-prefix (H.ein e) s ≡ just (rest , perm)
    → edge-step s e ≡ H.eout e ++ rest
  edge-step-just s e eq rewrite eq = refl

  edge-step-nothing
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
    → extract-prefix (H.ein e) s ≡ nothing
    → edge-step s e ≡ s
  edge-step-nothing s e eq rewrite eq = refl

  --------------------------------------------------------------------
  -- Process all edges in natural Fin order; returns the final stack.

  process-edges
    : List (Fin H.nE) → ∀ (s : List (Fin H.nV))
    → List (Fin H.nV)
  process-edges []       s = s
  process-edges (e ∷ es) s = process-edges es (edge-step s e)

  process-all-edges
    : ∀ (s : List (Fin H.nV))
    → List (Fin H.nV)
  process-all-edges = process-edges (range H.nE)

  --------------------------------------------------------------------
  -- Run the algorithm from `H.dom`; the TOTALITY WITNESS is the
  -- permutation of the final stack onto `H.cod` (`nothing` when the run
  -- does not land on the codomain multiset).

  decode-attempt : Maybe (process-all-edges H.dom Perm.↭ H.cod)
  decode-attempt = extract-exact H.cod (process-all-edges H.dom)
