{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Gate-only LEAN decode.
--
-- A drop-in replacement for `Soundness.Decode.decode-attempt`, used at the
-- deep-rewrite search call site (`Solver.Deep.At.tryEmb`, run over the
-- EXTENDED signature `sig⁺`).  It clones `Decode`'s control flow verbatim —
-- same `process-edges` over `range H.nE` in kahn order, same `extract-prefix`
-- branching, same `Agen-edge` emission, same `nothing` cases — so it returns
-- `just` on EXACTLY the same graphs, with EXACTLY the same `Agen` edges in the
-- same order.  Hence the downstream gate (`findIso`/`Verify` and DeepProv's
-- `pairsO` predictions) is unchanged.
--
-- The ONE difference: at each `permute-via-vlab` slot it adds a *decidable*
-- identity pre-check.  When the running stack already coincides (as a LIST,
-- not merely as a multiset) with the target list — `s ≟ ein e ++ rest` for an
-- edge step, `s_final ≟ H.cod` for the final permute — the locating
-- permutation is the identity, and the soundness decode emits a full
-- `permute Perm.refl`-flavoured `id ⊗₁ (id ⊗₁ …)` tower of `O(nV)` `id`s.
-- That tower translates (`⟪_⟫`) to edge-free `hId`s that are *pruned* at the
-- `hComposeP` seam, so dropping it leaves `⟪frame⟫` IDENTICAL.  We therefore
-- emit a single `id` (well-typed by the `refl` from the `≟`), collapsing the
-- bulk identity padding.  A *non*-identity permutation never passes the `≟`
-- guard, so it is never collapsed.
--
-- Because the identity-guard collapse keeps the translated graph identical,
-- the produced frame is iso-equivalent to the soundness decoder's frame, so
-- this needs no `decode-lean ≈Term decode-attempt` proof: correctness comes
-- from the downstream `findIso ⟪ s ⟫ ⟪ frame ⟫` gate, which is decidable and
-- fails closed if a candidate is ever wrong.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.DecodeLean (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
  using (permute-via-vlab)

-- Shared (unchanged) helpers from the soundness decoder: `Agen-edge-aux`
-- (so the emitted generator wrapping is byte-identical) and `extract-exact`
-- (the final exact-match search).  Reusing them keeps the `Agen` edges and
-- the `nothing` discipline definitionally aligned with `Decode`.
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (Agen-edge-aux; extract-exact; extract-prefix)

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong; subst; subst₂)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- The cospan algorithm, with `H` fixed.  Structure verbatim from
-- `Soundness.Decode`; only the two `permute-via-vlab` slots gain an identity
-- guard.

module _ (H : Hypergraph FlatGen) where

  private
    module H = Hypergraph H

    _≟L_ : DecidableEquality (List (Fin H.nV))
    _≟L_ = ≡-dec _≟F_   -- decidable equality on `List (Fin H.nV)`

  Agen-edge
    : (e : Fin H.nE)
    → HomTerm (unflatten (map H.vlab (H.ein e)))
              (unflatten (map H.vlab (H.eout e)))
  Agen-edge e = Agen-edge-aux (H.elab e)

  --------------------------------------------------------------------
  -- Per-edge step.  IDENTICAL to `Decode.edge-step` except: when the located
  -- stack `s` already equals `ein e ++ rest` as a list, the permute is the
  -- identity, so we drop the `∘ permute-via-vlab …` factor (emit `mid'`
  -- alone) instead of the full id-tower.

  edge-step
    : (s : List (Fin H.nV)) (e : Fin H.nE)
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  edge-step s e with extract-prefix (H.ein e) s
  ... | nothing             = (s , id)
  ... | just (rest , perm)  = (H.eout e ++ rest , bridged)
    where
      ein-l  = map H.vlab (H.ein e)
      eout-l = map H.vlab (H.eout e)
      rest-l = map H.vlab rest

      -- Apply the edge generator at the front, identity on the rest.
      mid : HomTerm (unflatten (ein-l  ++ rest-l))
                    (unflatten (eout-l ++ rest-l))
      mid = _≅_.to   (unflatten-++-≅ eout-l rest-l)
            ∘ (Agen-edge e ⊗₁ id)
            ∘ _≅_.from (unflatten-++-≅ ein-l  rest-l)

      -- Bridge `map vlab (xs ++ ys) ≡ map vlab xs ++ map vlab ys` (`map-++`).
      mid' : HomTerm (unflatten (map H.vlab (H.ein e  ++ rest)))
                     (unflatten (map H.vlab (H.eout e ++ rest)))
      mid' = subst₂ HomTerm
              (cong unflatten (sym (map-++ H.vlab (H.ein  e) rest)))
              (cong unflatten (sym (map-++ H.vlab (H.eout e) rest)))
              mid

      -- LEAN: collapse the identity permute (s ≡ ein e ++ rest) ⇒ drop it.
      -- Transport `mid'`'s domain along the decided list equality with `subst`
      -- rather than pattern-matching `refl`, since `s` occurs in the result
      -- type via `map H.vlab s` and so cannot be unified directly under the
      -- `with`-abstraction.
      bridged : HomTerm (unflatten (map H.vlab s))
                        (unflatten (map H.vlab (H.eout e ++ rest)))
      bridged with s ≟L (H.ein e ++ rest)
      ... | yes eq = subst (λ z → HomTerm (unflatten (map H.vlab z))
                                          (unflatten (map H.vlab (H.eout e ++ rest))))
                           (sym eq) mid'
      ... | no  _  = mid' ∘ permute-via-vlab H.vlab perm

  --------------------------------------------------------------------
  -- Process all edges in natural Fin order; returns the final stack and a
  -- HomTerm from the original stack.  Verbatim from `Decode.process-edges`.

  process-edges
    : List (Fin H.nE) → ∀ (s : List (Fin H.nV))
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  process-edges []       s = (s , id)
  process-edges (e ∷ es) s =
    let (s'  , t)  = edge-step    s  e
        (s'' , t') = process-edges es s'
    in  (s'' , t' ∘ t)

  process-all-edges
    : ∀ (s : List (Fin H.nV))
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  process-all-edges = process-edges (range H.nE)

  --------------------------------------------------------------------
  -- Run from `H.dom`, then bridge the final stack to `H.cod`.  LEAN: collapse
  -- the final permute when `s_final ≡ H.cod` as a list.

  decode-attempt
    : Maybe (HomTerm (unflatten (domL H)) (unflatten (codL H)))
  decode-attempt with process-all-edges H.dom
  ... | (s_final , process-term) with extract-exact H.cod s_final
  ...    | nothing   = nothing
  ...    | just perm = just (final-permute ∘ process-term)
    where
      final-permute : HomTerm (unflatten (map H.vlab s_final))
                              (unflatten (map H.vlab H.cod))
      final-permute with s_final ≟L H.cod
      ... | yes eq = subst (λ z → HomTerm (unflatten (map H.vlab s_final))
                                          (unflatten (map H.vlab z)))
                           eq id
      ... | no  _  = permute-via-vlab H.vlab perm
