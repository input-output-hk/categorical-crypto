{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Literalization of a hypergraph's function fields ("tabulation").
--
-- `findIso`'s measured cost is dominated by RE-evaluation: the
-- `Hypergraph` fields `vlab`/`ein`/`eout`/`elab` are functions, and
-- every application re-walks the nested `hComposeP` tower — Agda's
-- evaluator is call-by-need for clause-level argument thunks but never
-- memoizes function *results* (docs/smc-solver-performance.md, cost
-- attribution + strictness/sharing probes).
--
-- `tabH` rebuilds the hypergraph with the function fields tabulated into
-- lazy `Vec`s.  Sharing discipline (this is the load-bearing part): the
-- vectors are *parameters* of the `Impl` module, so the record's field
-- closures capture the argument thunks created at the single `Impl.tabbed`
-- application inside `tabH` — every later application of the new
-- `vlab`/`ein`/`eout`/`elab` reads the SAME memoizing vector, and each
-- original field value is computed at most once.  (A `let` would be
-- inlined at elaboration, and a `tabulate` written inside a lambda body
-- would be re-instantiated per application — neither shares.)
--
-- The `elab` field is dependent: `elab e : Gen (map vlab (ein e))
-- (map vlab (eout e))` depends on `e` through `ein`/`eout`, so it cannot
-- go in a *homogeneous* `Vec`.  We tabulate it into a Σ-`Vec` whose entry
-- per edge stores the original boundary atom-lists together with the
-- original generator: `Σ[ (As , Bs) ] Gen As Bs`.  The new `elab e` reads
-- that entry (one memoizing `lookup`, forcing the original `H.elab e`
-- through the `hComposeP` tower at most once) and transports it into the
-- demanded type along the (propositional) `lookup∘tabulate` equalities.
-- This makes every `flat-match-subst`/`matchEdge` access of `elab` an
-- O(1) lookup of an already-`whnf` generator (was: a fresh `subst₂`
-- cascade re-walking the frame tower per access).
--
-- `tab-≅ᴴ : tabH H ≅ᴴ H` (identity bijections) lets callers transport an
-- iso found on the tabulated graphs back to the originals; see
-- `Solver.FindIsoTab`.  Its `ψ-elab` is a `lookup∘tabulate` roundtrip
-- (no longer `refl`, but provable from `elab-ok`).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Tabulate where

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Properties using (map-cong; map-id)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; tabulate; lookup)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Function using (id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)

module _ {X : Set} {Gen : List X → List X → Set} where

  -- A tabulated edge label: its boundary atom-lists, paired with the
  -- generator at those boundaries.  Homogeneous in `e`, so it fits a `Vec`.
  ElabEntry : Set
  ElabEntry = Σ[ st ∈ (List X × List X) ] Gen (proj₁ st) (proj₂ st)

  private
    -- All shared values flow through `Impl`'s parameter bindings: the
    -- single application in `tabH` creates one thunk per vector, captured
    -- by every field closure of `tabbed`.
    module Impl (H : Hypergraph Gen)
      (let module H = Hypergraph H)
      (vlabV : Vec X H.nV)
      (einV eoutV : Vec (List (Fin H.nV)) H.nE)
      (elabV : Vec ElabEntry H.nE)
      (vlab-ok : ∀ v → lookup vlabV v ≡ H.vlab v)
      (ein-ok  : ∀ e → lookup einV  e ≡ H.ein  e)
      (eout-ok : ∀ e → lookup eoutV e ≡ H.eout e)
      (elab-ok : ∀ e → lookup elabV e
                     ≡ ((map H.vlab (H.ein e) , map H.vlab (H.eout e))
                        , H.elab e))
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

      -- Generic transport of a stored entry's generator into a demanded
      -- type, given an equation `eq` pinning the entry's boundaries.  This
      -- is the single dependent operation; `tab-elab` and `ψ-elab-tab` are
      -- both expressed through it so their proof terms line up
      -- definitionally when `eq` is `refl`.
      transport-entry
        : ∀ {As' Bs' As Bs} (g : Gen As Bs)
            (entry : ElabEntry)
            (eq : entry ≡ ((As , Bs) , g))
            (p : As' ≡ As) (q : Bs' ≡ Bs)
        → Gen As' Bs'
      transport-entry g entry eq p q =
        subst₂ Gen
          (trans (cong (λ z → proj₁ (proj₁ z)) eq) (sym p))
          (trans (cong (λ z → proj₂ (proj₁ z)) eq) (sym q))
          (proj₂ entry)

      -- When the entry equation is `refl` (the `lookup∘tabulate`
      -- roundtrip on a literal edge), `transport-entry` collapses to the
      -- plain `subst₂ Gen p q g` — i.e. the original un-tabulated label.
      transport-entry-refl
        : ∀ {As' Bs' As Bs} (g : Gen As Bs)
            (entry : ElabEntry)
            (eq : entry ≡ ((As , Bs) , g))
            (p : As' ≡ As) (q : Bs' ≡ Bs)
        → subst₂ Gen (sym p) (sym q) g ≡ transport-entry g entry eq p q
      transport-entry-refl g .((_ , _) , g) refl p q = refl

      -- The tabulated `elab`: read the stored entry's generator and
      -- transport it from the stored boundaries to the demanded
      -- (tabulated) boundaries.  `proj₂ (lookup elabV e)` forces the
      -- memoizing vector entry (and hence `H.elab e`) at most once.
      tab-elab : ∀ e → Gen (map (λ v → lookup vlabV v) (lookup einV e))
                           (map (λ v → lookup vlabV v) (lookup eoutV e))
      tab-elab e =
        transport-entry (H.elab e) (lookup elabV e) (elab-ok e)
          (eq-in e) (eq-out e)

      tabbed : Hypergraph Gen
      tabbed = record
        { nV   = H.nV
        ; vlab = λ v → lookup vlabV v
        ; nE   = H.nE
        ; ein  = λ e → lookup einV  e
        ; eout = λ e → lookup eoutV e
        ; elab = tab-elab
        ; dom  = H.dom
        ; cod  = H.cod
        }

      -- The `ψ-elab` law for the iso `tabbed ≅ᴴ H`.  With `ψ = id` and
      -- `atom-ein/out = sym (eq-in/out)`, the goal is
      --   subst₂ Gen (sym (eq-in e)) (sym (eq-out e)) (H.elab e) ≡ tab-elab e.
      -- Substituting `elab-ok e` (the `lookup∘tabulate` roundtrip) turns
      -- `proj₂ (lookup elabV e)` into `H.elab e` and the entry-boundary
      -- `cong`s into `refl`, after which `tab-elab e` is *definitionally*
      -- `subst₂ Gen (trans refl (sym eq-in)) (trans refl (sym eq-out))
      -- (H.elab e)` = the LHS.  We discharge it by matching `elab-ok e`
      -- against `refl` on a general entry.
      ψ-elab-tab : ∀ e
                 → subst₂ Gen (sym (eq-in e)) (sym (eq-out e)) (H.elab e)
                 ≡ tab-elab e
      ψ-elab-tab e =
        transport-entry-refl (H.elab e) (lookup elabV e) (elab-ok e)
          (eq-in e) (eq-out e)

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
        ; ψ-elab    = ψ-elab-tab
        }

  tabH : Hypergraph Gen → Hypergraph Gen
  tabH H = Impl.tabbed H
    (tabulate H.vlab) (tabulate H.ein) (tabulate H.eout)
    (tabulate (λ e → (map H.vlab (H.ein e) , map H.vlab (H.eout e)) , H.elab e))
    (lookup∘tabulate H.vlab) (lookup∘tabulate H.ein) (lookup∘tabulate H.eout)
    (lookup∘tabulate (λ e → (map H.vlab (H.ein e) , map H.vlab (H.eout e)) , H.elab e))
    where module H = Hypergraph H

  -- `tabH H ≅ᴴ H`, postulate-free.  Definitionally `tabH H` is the
  -- `Impl.tabbed` instance below, so `Impl.tab-iso` applies.
  tab-≅ᴴ : (H : Hypergraph Gen) → tabH H ≅ᴴ H
  tab-≅ᴴ H = Impl.tab-iso H
    (tabulate H.vlab) (tabulate H.ein) (tabulate H.eout)
    (tabulate (λ e → (map H.vlab (H.ein e) , map H.vlab (H.eout e)) , H.elab e))
    (lookup∘tabulate H.vlab) (lookup∘tabulate H.ein) (lookup∘tabulate H.eout)
    (lookup∘tabulate (λ e → (map H.vlab (H.ein e) , map H.vlab (H.eout e)) , H.elab e))
    where module H = Hypergraph H
