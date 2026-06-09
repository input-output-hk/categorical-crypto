{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Literalization of a hypergraph's function fields ("tabulation").
--
-- `findIso`'s measured cost is dominated by RE-evaluation: the
-- `Hypergraph` fields `vlab`/`ein`/`eout` are functions, and every
-- application re-walks the nested `hComposeP` tower — Agda's evaluator
-- is call-by-need for clause-level argument thunks but never memoizes
-- function *results* (docs/smc-solver-performance.md, cost attribution +
-- strictness/sharing probes).
--
-- `tabH` rebuilds the hypergraph with the function fields tabulated into
-- lazy `Vec`s.  Sharing discipline (this is the load-bearing part): the
-- vectors are *parameters* of the `Impl` module, so the record's field
-- closures capture the argument thunks created at the single `Impl.tabbed`
-- application inside `tabH` — every later application of the new
-- `vlab`/`ein`/`eout` reads the SAME memoizing vector, and each original
-- field value is computed at most once.  (A `let` would be inlined at
-- elaboration, and a `tabulate` written inside a lambda body would be
-- re-instantiated per application — neither shares.)
--
-- The dependent `elab` field cannot be tabulated into a homogeneous
-- `Vec`; it is transported per access by `subst₂` along the
-- (propositional) `lookup∘tabulate` equalities — cheap: the incidence
-- lists are short, the proofs normalize to `refl`, and the solver only
-- demands `elab` once per edge.
--
-- `tab-≅ᴴ : tabH H ≅ᴴ H` (identity bijections, `ψ-elab = refl` because
-- the iso's `atom-ein`/`atom-eout` are *definitionally* the transports
-- baked into `tabbed.elab`) lets callers transport an iso found on the
-- tabulated graphs back to the originals; see `Solver.FindIsoTab`.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Tabulate where

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Properties using (map-cong; map-id)
open import Data.Vec using (Vec; tabulate; lookup)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Function using (id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)

module _ {X : Set} {Gen : List X → List X → Set} where

  private
    -- All shared values flow through `Impl`'s parameter bindings: the
    -- single application in `tabH` creates one thunk per vector, captured
    -- by every field closure of `tabbed`.
    module Impl (H : Hypergraph Gen)
      (let module H = Hypergraph H)
      (vlabV : Vec X H.nV)
      (einV eoutV : Vec (List (Fin H.nV)) H.nE)
      (vlab-ok : ∀ v → lookup vlabV v ≡ H.vlab v)
      (ein-ok  : ∀ e → lookup einV  e ≡ H.ein  e)
      (eout-ok : ∀ e → lookup eoutV e ≡ H.eout e)
      where

      -- `map (lookup vlabV) (lookup einV e) ≡ map H.vlab (H.ein e)`:
      -- pointwise label agreement, then incidence agreement.
      eq-in : ∀ e → map (λ v → lookup vlabV v) (lookup einV e)
                  ≡ map H.vlab (H.ein e)
      eq-in e = trans (map-cong vlab-ok (lookup einV e))
                      (cong (map H.vlab) (ein-ok e))

      eq-out : ∀ e → map (λ v → lookup vlabV v) (lookup eoutV e)
                   ≡ map H.vlab (H.eout e)
      eq-out e = trans (map-cong vlab-ok (lookup eoutV e))
                       (cong (map H.vlab) (eout-ok e))

      tabbed : Hypergraph Gen
      tabbed = record
        { nV   = H.nV
        ; vlab = λ v → lookup vlabV v
        ; nE   = H.nE
        ; ein  = λ e → lookup einV  e
        ; eout = λ e → lookup eoutV e
        ; elab = λ e → subst₂ Gen (sym (eq-in e)) (sym (eq-out e)) (H.elab e)
        ; dom  = H.dom
        ; cod  = H.cod
        }

      -- The transport back: `tabbed` is isomorphic to `H` via identity
      -- bijections.  `atom-ein`/`atom-eout` are chosen to be exactly the
      -- (inverted) transports inside `tabbed.elab`, so `ψ-elab` is `refl`.
      tab-iso : tabbed ≅ᴴ H
      tab-iso = record
        { φ         = id
        ; φ⁻¹       = id
        ; φ-left    = λ _ → refl
        ; φ-rght    = λ _ → refl
        ; ψ         = id
        ; ψ⁻¹       = id
        ; ψ-left    = λ _ → refl
        ; ψ-rght    = λ _ → refl
        ; φ-lab     = λ v → sym (vlab-ok v)
        ; ψ-ein     = λ e → trans (sym (ein-ok e))
                                  (sym (map-id (lookup einV e)))
        ; ψ-eout    = λ e → trans (sym (eout-ok e))
                                  (sym (map-id (lookup eoutV e)))
        ; φ-dom     = sym (map-id H.dom)
        ; φ-cod     = sym (map-id H.cod)
        ; atom-ein  = λ e → sym (eq-in e)
        ; atom-eout = λ e → sym (eq-out e)
        ; ψ-elab    = λ _ → refl
        }

  tabH : Hypergraph Gen → Hypergraph Gen
  tabH H = Impl.tabbed H
    (tabulate H.vlab) (tabulate H.ein) (tabulate H.eout)
    (lookup∘tabulate H.vlab) (lookup∘tabulate H.ein) (lookup∘tabulate H.eout)
    where module H = Hypergraph H

  -- `tabH H ≅ᴴ H`, postulate-free.  Definitionally `tabH H` is the
  -- `Impl.tabbed` instance below, so `Impl.tab-iso` applies.
  tab-≅ᴴ : (H : Hypergraph Gen) → tabH H ≅ᴴ H
  tab-≅ᴴ H = Impl.tab-iso H
    (tabulate H.vlab) (tabulate H.ein) (tabulate H.eout)
    (lookup∘tabulate H.vlab) (lookup∘tabulate H.ein) (lookup∘tabulate H.eout)
    where module H = Hypergraph H
