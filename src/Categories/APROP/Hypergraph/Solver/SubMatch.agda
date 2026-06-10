{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Sub-hypergraph matching (TensorRocq §4.2, the matcher half of DPO
-- rewriting).  Where `findIso` decides a *full* isomorphism `H ≅ᴴ J`, this
-- module finds an *embedding* of a (rule-LHS) hypergraph `L` as a
-- sub-hypergraph of a (target) hypergraph `S`:
--
--     subMatch : (L S : Hypergraph FlatGen) → Maybe (L ↪ᴴ S)
--
-- An embedding is an injective vertex map `φ`, an injective edge map `ψ`, and
-- the usual label/endpoint-preservation data — but, unlike `_≅ᴴ_`, *no*
-- surjectivity and *no* boundary-onto requirement (L's interface may sit in
-- the interior of S).  A caller carves the rewrite context by deleting the
-- `ψ`-image edges and exposing the boundary vertices `map φ L.dom` /
-- `map φ L.cod` as new interface holes.
--
-- The search reuses the full-iso machinery verbatim: `searchIso` already tries
-- *every* S-edge for L's first edge (it only looked interface-pinned because
-- `findIso` pre-seeds the boundary).  We start from the *empty* vertex seed and
-- loosen the verification stage (forward-only totalisation; injectivity
-- round-trips instead of two-sided bijection laws).
--
-- Like `findIso`, this is SOUND but not complete (fuel/label pruning), and an
-- *un*verified component of the rewrite pipeline: a returned embedding is a
-- genuine label/endpoint-preserving injection, but the engine's soundness
-- still rests solely on the downstream `findIso` re-check in `rewriteH!`.
--
-- NB: an `L` with no edges (e.g. a pure identity/swap LHS) has no edge
-- constraints to bind its vertices, so forward-totalisation fails and
-- `subMatch` returns `nothing` for it.  Rule LHSs always carry generator
-- content, so this is not a limitation in practice.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.SubMatch (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; flat; flatten)
open import Categories.APROP.Hypergraph.Solver.PBij
  using (PBij; forward; backward; emptyBij)
open import Categories.APROP.Hypergraph.Solver.Search sig-dec
  using (searchAll-default)
open import Categories.APROP.Hypergraph.Solver.Totals using (Total; totalise)
open import Categories.APROP.Hypergraph.Solver.Verify sig-dec
  using (flat-match; ∀F?; dec→maybe)

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Properties using (map-∘; map-cong) renaming (≡-dec to ≡-decL)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Properties using () renaming (≡-dec to ≡-decM)
open import Data.Product using (_,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst₂)

--------------------------------------------------------------------------------
-- The embedding relation `L ↪ᴴ S`.  Its label/endpoint fields mirror those of
-- `_≅ᴴ_`, but the bijection is one-directional (injective, witnessed by a
-- *partial* inverse with a one-sided round-trip law) and there is no boundary
-- requirement on S.

module _ {X : Set} {Gen : List X → List X → Set} where

  infix 4 _↪ᴴ_

  record _↪ᴴ_ (L S : Hypergraph Gen) : Set where
    private
      module L = Hypergraph L
      module S = Hypergraph S
    field
      -- Injective vertex map (φ⁻¹ a partial inverse; φ-inv ⇒ φ injective).
      φ      : Fin L.nV → Fin S.nV
      φ⁻¹    : Fin S.nV → Maybe (Fin L.nV)
      φ-inv  : ∀ i → φ⁻¹ (φ i) ≡ just i

      -- Injective edge map.
      ψ      : Fin L.nE → Fin S.nE
      ψ⁻¹    : Fin S.nE → Maybe (Fin L.nE)
      ψ-inv  : ∀ e → ψ⁻¹ (ψ e) ≡ just e

      -- Vertex labels agree: S.vlab ∘ φ ≗ L.vlab.
      φ-lab  : ∀ i → S.vlab (φ i) ≡ L.vlab i

      -- Edge endpoints: S.ein/eout ∘ ψ = map φ of L.ein/eout.
      ψ-ein  : ∀ e → S.ein  (ψ e) ≡ map φ (L.ein  e)
      ψ-eout : ∀ e → S.eout (ψ e) ≡ map φ (L.eout e)

      -- Atom-list equalities at each edge (derived, kept as fields).
      atom-ein  : ∀ e → map S.vlab (S.ein  (ψ e)) ≡ map L.vlab (L.ein  e)
      atom-eout : ∀ e → map S.vlab (S.eout (ψ e)) ≡ map L.vlab (L.eout e)

      -- Edge labels agree up to `subst₂` along the atom-list equalities.
      ψ-elab : ∀ e → subst₂ Gen (atom-ein e) (atom-eout e) (S.elab (ψ e))
                   ≡ L.elab e

    -- The boundary (cut) vertices of S that are the images of L's interface;
    -- a caller carves the rewrite context around these.
    boundary-dom : List (Fin S.nV)
    boundary-dom = map φ L.dom

    boundary-cod : List (Fin S.nV)
    boundary-cod = map φ L.cod

--------------------------------------------------------------------------------
-- Verification stage: turn a search-produced `(φB, ψB)` into an `L ↪ᴴ S`.
-- Mirrors `Verify.verify` with `H := L`, `J := S`, but: forward-only
-- totalisation (the backward maps are partial — only L's image is hit), the
-- injectivity round-trips replace the two-sided bijection laws, and the
-- `J.dom`/`J.cod` boundary-onto checks are dropped.

module Verify-Sub (L S : Hypergraph FlatGen)
                  (φB : PBij (Hypergraph.nV L) (Hypergraph.nV S))
                  (ψB : PBij (Hypergraph.nE L) (Hypergraph.nE S)) where

  module L = Hypergraph L
  module S = Hypergraph S

  private
    _≟LF-S_ : DecidableEquality (List (Fin S.nV))
    _≟LF-S_ = ≡-decL _≟F_

    _≟MV_ : DecidableEquality (Maybe (Fin L.nV))
    _≟MV_ = ≡-decM _≟F_

    _≟ME_ : DecidableEquality (Maybe (Fin L.nE))
    _≟ME_ = ≡-decM _≟F_

    -- `map S.vlab ys ≡ map L.vlab xs` from `ys ≡ map φ xs` and `φ-lab`.
    deriveAtomEq
      : (φ : Fin L.nV → Fin S.nV)
      → (∀ i → S.vlab (φ i) ≡ L.vlab i)
      → ∀ (xs : List (Fin L.nV)) (ys : List (Fin S.nV))
      → ys ≡ map φ xs
      → map S.vlab ys ≡ map L.vlab xs
    deriveAtomEq φ φ-lab xs ys p =
      trans (cong (map S.vlab) p)
      (trans (sym (map-∘ xs))
             (map-cong φ-lab xs))

  verifySub : Maybe (L ↪ᴴ S)
  verifySub with totalise (forward φB) | totalise (forward ψB)
  ... | nothing       | _            = nothing
  ... | _             | nothing      = nothing
  ... | just (φ , _)  | just (ψ , _)
        with ∀F? (λ i → dec→maybe (backward φB (φ i) ≟MV just i))
           | ∀F? (λ e → dec→maybe (backward ψB (ψ e) ≟ME just e))
           | ∀F? (λ i → dec→maybe (S.vlab (φ i) ≟X L.vlab i))
           | ∀F? (λ e → dec→maybe (S.ein  (ψ e) ≟LF-S map φ (L.ein  e)))
           | ∀F? (λ e → dec→maybe (S.eout (ψ e) ≟LF-S map φ (L.eout e)))
  ...     | nothing | _ | _ | _ | _ = nothing
  ...     | _ | nothing | _ | _ | _ = nothing
  ...     | _ | _ | nothing | _ | _ = nothing
  ...     | _ | _ | _ | nothing | _ = nothing
  ...     | _ | _ | _ | _ | nothing = nothing
  ...     | just φ-inv | just ψ-inv | just φ-lab | just ψ-ein | just ψ-eout
            with ∀F? (λ e → flat-match
                   (subst₂ FlatGen
                     (deriveAtomEq φ φ-lab (L.ein  e) (S.ein  (ψ e)) (ψ-ein  e))
                     (deriveAtomEq φ φ-lab (L.eout e) (S.eout (ψ e)) (ψ-eout e))
                     (S.elab (ψ e)))
                   (L.elab e))
  ...       | nothing      = nothing
  ...       | just ψ-elab  = just record
                { φ         = φ
                ; φ⁻¹       = backward φB
                ; φ-inv     = φ-inv
                ; ψ         = ψ
                ; ψ⁻¹       = backward ψB
                ; ψ-inv     = ψ-inv
                ; φ-lab     = φ-lab
                ; ψ-ein     = ψ-ein
                ; ψ-eout    = ψ-eout
                ; atom-ein  = λ e → deriveAtomEq φ φ-lab (L.ein  e) (S.ein  (ψ e)) (ψ-ein  e)
                ; atom-eout = λ e → deriveAtomEq φ φ-lab (L.eout e) (S.eout (ψ e)) (ψ-eout e)
                ; ψ-elab    = ψ-elab
                }

--------------------------------------------------------------------------------
-- Top-level: search (no interface seed) then verify.
--
-- `subMatchAll` enumerates every verified embedding, in the DFS's order.
-- Consumers with acceptance criteria beyond the embedding itself — notably
-- the rewrite carve, which also needs the occurrence to be *convex* — must
-- retry down this list rather than committing to the first match.

subMatchAll : (L S : Hypergraph FlatGen) → List (L ↪ᴴ S)
subMatchAll L S = collect (searchAll-default L S emptyBij emptyBij)
  where
    collect : List _ → List (L ↪ᴴ S)
    collect []               = []
    collect ((φB , ψB) ∷ xs) with Verify-Sub.verifySub L S φB ψB
    ... | just emb = emb ∷ collect xs
    ... | nothing  = collect xs

subMatch : (L S : Hypergraph FlatGen) → Maybe (L ↪ᴴ S)
subMatch L S with subMatchAll L S
... | []      = nothing
... | emb ∷ _ = just emb
