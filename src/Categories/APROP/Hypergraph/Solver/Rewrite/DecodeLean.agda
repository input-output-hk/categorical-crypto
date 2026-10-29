{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Term-building decoder for deep-rewrite candidates, certified downstream.
--
-- When the stack already equals the target list, a full locating permutation
-- would emit an O(nV) identity tensor tower. Replace it with one id; the
-- translated graph differs only by allFin-++ reindexing. Non-identity
-- permutations still use the full coherence term.
--------------------------------------------------------------------------------

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Solver.Rewrite.DecodeLean (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅; _≅_)
open import Categories.Combinatorics.ExtractPrefix

open import Data.Fin
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Properties
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary

open APROP sig
open import Categories.PermuteCoherence.Unflatten asFreeMonoidalData
  using (permute)

Agen-edge-aux
  : ∀ {ins outs : List X} → FlatGen ins outs
  → HomTerm (unflatten ins) (unflatten outs)
Agen-edge-aux (flat-rec {A} {B} okA okB g) =
  subst₂ (λ a b → HomTerm (unflatten a) (unflatten b)) okA okB
    (_≅_.from (unflatten-flatten-≈ B) ∘ Agen g ∘ _≅_.to (unflatten-flatten-≈ A))

permute-via-vlab
  : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X)
  → xs Perm.↭ ys
  → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
permute-via-vlab vlab p = permute (PermProp.map⁺ vlab p)

module _ (H : Hypergraph FlatGen) where

  private
    module H = Hypergraph H

  -- Use subst, not a refl match: s occurs through map H.vlab in the result
  -- type and cannot be unified under the with-abstraction.
  permOrId
    : {s t : List (Fin H.nV)} → s Perm.↭ t
    → HomTerm (unflatten (map H.vlab s)) (unflatten (map H.vlab t))
  permOrId {s} {t} perm with ≡-dec _≟F_ s t
  ... | yes eq = subst (λ z → HomTerm (unflatten (map H.vlab s))
                                      (unflatten (map H.vlab z)))
                       eq id
  ... | no  _  = permute-via-vlab H.vlab perm

  Agen-edge
    : (e : Fin H.nE)
    → HomTerm (unflatten (map H.vlab (H.ein e)))
              (unflatten (map H.vlab (H.eout e)))
  Agen-edge e = Agen-edge-aux (H.elab e)

  edge-step
    : (s : List (Fin H.nV)) (e : Fin H.nE)
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  edge-step s e with extract-prefix (H.ein e) s
  ... | nothing             = (s , id)
  ... | just (rest , perm)  = (H.eout e ++ rest , mid' ∘ permOrId perm)
    where
      ein-l  = map H.vlab (H.ein e)
      eout-l = map H.vlab (H.eout e)
      rest-l = map H.vlab rest

      mid : HomTerm (unflatten (ein-l  ++ rest-l)) (unflatten (eout-l ++ rest-l))
      mid = _≅_.to   (unflatten-++-≅ eout-l rest-l)
            ∘ (Agen-edge e ⊗₁ id)
            ∘ _≅_.from (unflatten-++-≅ ein-l  rest-l)

      mid' : HomTerm (unflatten (map H.vlab (H.ein e  ++ rest)))
                     (unflatten (map H.vlab (H.eout e ++ rest)))
      mid' = subst₂ HomTerm
              (cong unflatten (sym (map-++ H.vlab (H.ein  e) rest)))
              (cong unflatten (sym (map-++ H.vlab (H.eout e) rest)))
              mid

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
  process-all-edges = process-edges (allFin H.nE)

  decode-attempt : Maybe (HomTerm (unflatten (domL H)) (unflatten (codL H)))
  decode-attempt with process-all-edges H.dom
  ... | (s_final , process-term) with extract-exact H.cod s_final
  ...    | nothing   = nothing
  ...    | just perm = just (permOrId perm ∘ process-term)
