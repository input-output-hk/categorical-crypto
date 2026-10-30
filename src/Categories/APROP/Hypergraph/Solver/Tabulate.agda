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
-- WithTransport permits a proved lazy transport: FlatGen can retain boundary
-- equalities without forcing them while Search and Verify inspect its payload.
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
    module Impl
      (transport : ∀ {As Bs As' Bs'} → As ≡ As' → Bs ≡ Bs' → Gen As Bs → Gen As' Bs')
      (transport-≡ : ∀ {As Bs As' Bs'} (p : As ≡ As') (q : Bs ≡ Bs') (g : Gen As Bs)
                   → transport p q g ≡ subst₂ Gen p q g)
      (H : Hypergraph Gen)
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

      -- The entry equation relates the stored boundaries to the original label;
      -- the transport implementation decides whether those proofs must reduce.
      transport-entry
        : ∀ {As' Bs' As Bs} (g : Gen As Bs)
            (entry : ElabEntry)
            (eq : entry ≡ ((As , Bs) , g))
            (p : As' ≡ As) (q : Bs' ≡ Bs)
        → Gen As' Bs'
      transport-entry g entry eq p q =
        transport
          (trans (cong (λ z → proj₁ (proj₁ z)) eq) (sym p))
          (trans (cong (λ z → proj₂ (proj₁ z)) eq) (sym q))
          (proj₂ entry)

      transport-entry-refl
        : ∀ {As' Bs' As Bs} (g : Gen As Bs)
            (entry : ElabEntry)
            (eq : entry ≡ ((As , Bs) , g))
            (p : As' ≡ As) (q : Bs' ≡ Bs)
        → subst₂ Gen (sym p) (sym q) g ≡ transport-entry g entry eq p q
      transport-entry-refl g .((_ , _) , g) refl p q = sym (transport-≡ (sym p) (sym q) g)

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

  module WithTransport
    (transport : ∀ {As Bs As' Bs'} → As ≡ As' → Bs ≡ Bs' → Gen As Bs → Gen As' Bs')
    (transport-≡ : ∀ {As Bs As' Bs'} (p : As ≡ As') (q : Bs ≡ Bs') (g : Gen As Bs)
                 → transport p q g ≡ subst₂ Gen p q g)
    where

    private
      module Tab (H : Hypergraph Gen) (let module H = Hypergraph H) =
        Impl transport transport-≡ H
          (tabulate H.vlab) (tabulate H.ein) (tabulate H.eout)
          (tabulate (λ e → (map H.vlab (H.ein e) , map H.vlab (H.eout e)) , H.elab e))
          (lookup∘tabulate H.vlab) (lookup∘tabulate H.ein) (lookup∘tabulate H.eout)
          (lookup∘tabulate
            (λ e → (map H.vlab (H.ein e) , map H.vlab (H.eout e)) , H.elab e))

    tabH : Hypergraph Gen → Hypergraph Gen
    tabH = Tab.tabbed

    tab-≅ᴴ : (H : Hypergraph Gen) → tabH H ≅ᴴ H
    tab-≅ᴴ = Tab.tab-iso

  tabH : Hypergraph Gen → Hypergraph Gen
  tabH = WithTransport.tabH (subst₂ Gen) (λ _ _ _ → refl)

  tab-≅ᴴ : (H : Hypergraph Gen) → tabH H ≅ᴴ H
  tab-≅ᴴ = WithTransport.tab-≅ᴴ (subst₂ Gen) (λ _ _ _ → refl)
