{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Tabulating function fields avoids re-walking the hComposeP tower on each
-- access (docs/smc-solver-performance.md).
--
-- Vectors must be Impl parameters: field closures capture the thunks of its
-- single application, so each original field value is computed at most once.
-- A let is inlined during elaboration; tabulate inside a lambda is recreated
-- at every application.
--
-- Dependent edge labels need a Σ-Vec storing their original boundaries.
-- lookup∘tabulate then transports each label to the tabulated boundaries.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Tabulate where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.Iso

open import Data.Fin
open import Data.List using (List; map)
open import Data.List.Properties
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; tabulate; lookup)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Function
open import Relation.Binary.PropositionalEquality

module _ {X : Set} {Gen : List X → List X → Set} where

  ElabEntry : Set
  ElabEntry = Σ[ st ∈ (List X × List X) ] Gen (proj₁ st) (proj₂ st)

  private
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

      eq-in : ∀ e → map (lookup vlabV) (lookup einV e) ≡ map H.vlab (H.ein e)
      eq-in e = trans (map-cong vlab-ok (lookup einV e)) (cong (map H.vlab) (ein-ok e))

      eq-out : ∀ e → map (lookup vlabV) (lookup eoutV e) ≡ map H.vlab (H.eout e)
      eq-out e = trans (map-cong vlab-ok (lookup eoutV e))
                       (cong (map H.vlab) (eout-ok e))

      -- Sharing this transport makes the two label proofs line up
      -- definitionally when the entry equation is refl.
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

      transport-entry-refl
        : ∀ {As' Bs' As Bs} (g : Gen As Bs)
            (entry : ElabEntry)
            (eq : entry ≡ ((As , Bs) , g))
            (p : As' ≡ As) (q : Bs' ≡ Bs)
        → subst₂ Gen (sym p) (sym q) g ≡ transport-entry g entry eq p q
      transport-entry-refl g .((_ , _) , g) refl p q = refl

      tab-elab : ∀ e → Gen (map (lookup vlabV) (lookup einV e))
                           (map (lookup vlabV) (lookup eoutV e))
      tab-elab e =
        transport-entry (H.elab e) (lookup elabV e) (elab-ok e)
          (eq-in e) (eq-out e)

      tabbed : Hypergraph Gen
      tabbed = record
        { nV   = H.nV
        ; vlab = lookup vlabV
        ; nE   = H.nE
        ; ein  = lookup einV
        ; eout = lookup eoutV
        ; elab = tab-elab
        ; dom  = H.dom
        ; cod  = H.cod
        }

      -- Matching a general entry equation against refl avoids dependent
      -- elimination on the fixed lookup expression.
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

  private
    module Tab (H : Hypergraph Gen) (let module H = Hypergraph H) =
      Impl H
        (tabulate H.vlab) (tabulate H.ein) (tabulate H.eout)
        (tabulate (λ e → (map H.vlab (H.ein e) , map H.vlab (H.eout e)) , H.elab e))
        (lookup∘tabulate H.vlab) (lookup∘tabulate H.ein) (lookup∘tabulate H.eout)
        (lookup∘tabulate
          (λ e → (map H.vlab (H.ein e) , map H.vlab (H.eout e)) , H.elab e))

  tabH : Hypergraph Gen → Hypergraph Gen
  tabH = Tab.tabbed

  tab-≅ᴴ : (H : Hypergraph Gen) → tabH H ≅ᴴ H
  tab-≅ᴴ = Tab.tab-iso
