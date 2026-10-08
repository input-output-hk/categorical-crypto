{-# OPTIONS --safe --without-K #-}

-- Associativity coherence for the strong-monoidal structure
-- (List X, _++_, []) → (ObjTerm, _⊗₀_, unit).

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using ( unflatten; unflatten-++-≅; _≅_
        ; subst-id-cod; subst-id-dom; cast-cancel′; subst-cod-cons )

open import Categories.Category
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Morphism.Reasoning.Ext FreeMonoidal using (inv-resp)

open import Data.Fin.Patterns
open import Data.List.Properties
import Data.Vec as Vec

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

c-iso-assoc-from
  : ∀ xs₁ xs₂ ys
  → α⇒ {unflatten xs₁} {unflatten xs₂} {unflatten ys}
    ∘ (_≅_.from (unflatten-++-≅ xs₁ xs₂) ⊗₁ id)
    ∘ _≅_.from (unflatten-++-≅ (xs₁ ++ xs₂) ys)
  ≈Term (id {unflatten xs₁} ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys))
        ∘ _≅_.from (unflatten-++-≅ xs₁ (xs₂ ++ ys))
        ∘ subst-id-cod (++-assoc xs₁ xs₂ ys)

c-iso-assoc-from [] xs₂ ys = solveMor! lhsᵗ rhsᵗ
  where
    open FinSetup FMC
      ( unflatten xs₂ Vec.∷ unflatten ys Vec.∷ unflatten (xs₂ ++ ys) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F
    open Sig {1} (λ { 0F → v2 , v0 ⊗ᵒ v1 })
    open WithGen (λ { (genS 0F) → _≅_.from (unflatten-++-≅ xs₂ ys) })
    g0 = gen 0F
    lhsᵗ rhsᵗ : S.HomTerm v2 (unitᵒ ⊗ᵒ (v0 ⊗ᵒ v1))
    lhsᵗ = S._∘_ S.α⇒ (S._∘_ (S._⊗₁_ S.λ⇐ S.id) g0)
    rhsᵗ = S._∘_ (S._⊗₁_ S.id g0) (S._∘_ S.λ⇐ S.id)

c-iso-assoc-from (x ∷ xs₁') xs₂ ys = body
  where
    U₁'   = unflatten xs₁'
    U₂    = unflatten xs₂
    U-ys  = unflatten ys
    U-12  = unflatten (xs₁' ++ xs₂)
    U-23  = unflatten (xs₂ ++ ys)
    Vx    = Var x

    c-1   = _≅_.from (unflatten-++-≅ xs₁' xs₂)
    c-2   = _≅_.from (unflatten-++-≅ (xs₁' ++ xs₂) ys)
    c-3   = _≅_.from (unflatten-++-≅ xs₂ ys)
    c-4   = _≅_.from (unflatten-++-≅ xs₁' (xs₂ ++ ys))

    e     = ++-assoc xs₁' xs₂ ys
    e'    = ++-assoc (x ∷ xs₁') xs₂ ys  -- = cong (x ∷_) e definitionally.

    subst-id-xs₁' = subst-id-cod e

    -- Both shuffles must share this FinSetup application.
    open FinSetup FMC
      ( Vx Vec.∷ U₁' Vec.∷ U₂ Vec.∷ U-ys Vec.∷ U-12 Vec.∷ U-23
          Vec.∷ unflatten ((xs₁' ++ xs₂) ++ ys)
          Vec.∷ unflatten (xs₁' ++ xs₂ ++ ys) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F
    v4 = V 4F ; v5 = V 5F ; v6 = V 6F ; v7 = V 7F

    ih : α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2
       ≈Term (id {U₁'} ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁'
    ih = c-iso-assoc-from xs₁' xs₂ ys

    shuffle₁
      : α⇒ {Vx ⊗₀ U₁'} {U₂} {U-ys}
          ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
          ∘ (α⇐ ∘ id ⊗₁ c-2)
      ≈Term α⇐ ∘ id ⊗₁ (α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2)
    shuffle₁ = solveMor! lhsᵗ rhsᵗ
      where
        open Sig {2} (λ { 0F → v4 , v1 ⊗ᵒ v2 ; 1F → v6 , v4 ⊗ᵒ v3 })
        open WithGen (λ { (genS 0F) → c-1 ; (genS 1F) → c-2 })
        g1 = gen 0F ; g2 = gen 1F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v6) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
        lhsᵗ = S._∘_ S.α⇒
                 (S._∘_ (S._⊗₁_ (S._∘_ S.α⇐ (S._⊗₁_ S.id g1)) S.id)
                        (S._∘_ S.α⇐ (S._⊗₁_ S.id g2)))
        rhsᵗ = S._∘_ S.α⇐ (S._⊗₁_ S.id (S._∘_ S.α⇒ (S._∘_ (S._⊗₁_ g1 S.id) g2)))

    shuffle₂
      : α⇐ ∘ id ⊗₁ ((id {U₁'} ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁')
      ≈Term id ⊗₁ c-3
            ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
            ∘ (id ⊗₁ subst-id-xs₁')
    shuffle₂ = solveMor! lhsᵗ rhsᵗ
      where
        open Sig {3} (λ { 0F → v5 , v2 ⊗ᵒ v3 ; 1F → v7 , v1 ⊗ᵒ v5 ; 2F → v6 , v7 })
        open WithGen (λ { (genS 0F) → c-3 ; (genS 1F) → c-4
                        ; (genS 2F) → subst-id-xs₁' })
        g3 = gen 0F ; g4 = gen 1F ; gs = gen 2F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v6) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
        lhsᵗ = S._∘_ S.α⇐ (S._⊗₁_ S.id (S._∘_ (S._⊗₁_ S.id g3) (S._∘_ g4 gs)))
        rhsᵗ = S._∘_ (S._⊗₁_ S.id g3)
                 (S._∘_ (S._∘_ S.α⇐ (S._⊗₁_ S.id g4)) (S._⊗₁_ S.id gs))

    body = begin
      α⇒ {Vx ⊗₀ U₁'} {U₂} {U-ys}
        ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
        ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ shuffle₁ ⟩
      α⇐
        ∘ id ⊗₁ (α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2)
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
      α⇐
        ∘ id ⊗₁ ((id ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁')
          ≈⟨ shuffle₂ ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
        ∘ (id ⊗₁ subst-id-xs₁')
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ subst-cod-cons e ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
        ∘ subst-id-cod e' ∎

-- Each side has a three-fold inverse cancelling pairwise; inv-resp
-- transports the from-side equation to the to-side equation.

c-iso-assoc-to
  : ∀ xs₁ xs₂ ys
  → _≅_.to (unflatten-++-≅ (xs₁ ++ xs₂) ys)
    ∘ (_≅_.to (unflatten-++-≅ xs₁ xs₂) ⊗₁ id)
    ∘ α⇐ {unflatten xs₁} {unflatten xs₂} {unflatten ys}
  ≈Term subst-id-dom (++-assoc xs₁ xs₂ ys)
        ∘ _≅_.to (unflatten-++-≅ xs₁ (xs₂ ++ ys))
        ∘ (id {unflatten xs₁} ⊗₁ _≅_.to (unflatten-++-≅ xs₂ ys))
c-iso-assoc-to xs₁ xs₂ ys =
  ⟺ (inv-resp RhsinvRhs LhsLhsinv (⟺ (c-iso-assoc-from xs₁ xs₂ ys)))
  where
    RhsinvRhs = cancel₃ (⊗-cancel idˡ (_≅_.isoˡ (unflatten-++-≅ xs₂ ys)))
                        (_≅_.isoˡ (unflatten-++-≅ xs₁ (xs₂ ++ ys)))
                        (cast-cancel′ (++-assoc xs₁ xs₂ ys))

    LhsLhsinv = cancel₃ (_≅_.isoʳ (unflatten-++-≅ (xs₁ ++ xs₂) ys))
                        (⊗-cancel (_≅_.isoʳ (unflatten-++-≅ xs₁ xs₂)) idˡ)
                        α⇒∘α⇐≈id
