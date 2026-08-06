{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Monoidal-coherence data for `unflatten`, viewed as the strong monoidal
-- functor
--
--   (List X, _++_, [])  ⟶  (ObjTerm, _⊗₀_, unit)     over `FreeMonoidal`.
--
-- NOTE: no `Functor` / `MonoidalFunctor` record is actually built here — this
-- module only collects the coherence isos and transport lemmas that such a
-- functor would carry, as consumed by `Strict/{Boundary,Embed}`.  The object
-- map is `unflatten : List X → ObjTerm` (the right-associated, `unit`-padded
-- fold from `Soundness/Base/Unflatten.agda`) and the structure iso (laxator)
-- is `unflatten-++-≅`.  It gathers the associativity coherence (both
-- directions):
--   * `c-iso-assoc-from` — re-exported from `Discharge/CIsoAssocFromCons.agda`
--     (the `from`-side pentagon);
--   * `c-iso-assoc-to`   — its `to`-side dual, by composite inversion;
--   * `cancel-mid-iso`.
-- The transported identities `subst-id-{dom,cod}` and their groupoid laws live
-- one level down, in `Soundness/Base/Unflatten.agda`, and are re-exported here.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal
  (sig : APROPSignature) where

open APROP sig

-- Re-export `unflatten` / `unflatten-++-≅` and the transported-identity kit so
-- consumers can open this module alone for the full boundary-coherence
-- interface.
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig public
  using ( unflatten; unflatten-++-≅; _≅_; flatten-unflatten; unflatten-flatten-≈
        ; subst-id-cod; subst-id-dom; cast-dc; cast-cancel′
        ; cod-cancel; dom-cancel; subst-cod-cons )

-- The `from`-side associativity pentagon, imported and re-exported as-is.
open import Categories.APROP.Hypergraph.Soundness.Discharge.CIsoAssocFromCons sig public
  using (c-iso-assoc-from)

open import Categories.Category using (Category)

open import Data.List using (_++_)
open import Data.List.Properties using (++-assoc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## 0.  Generic middle-iso cancellation.
--
-- Two 3-fold composites sharing a middle iso `Fm ∘ Tm ≈ id` cancel it, leaving
-- `To ∘ M₁ ∘ M₂ ∘ Ff`.  No assumption on `M₁` / `M₂`.  (Part of the
-- transport-absorption algebra, kept here because the `c-iso-assoc-to`
-- inversion chases below consume it.)
cancel-mid-iso
  : ∀ {A₀ A₁ A₂ A₃ A₄ A₅ : ObjTerm}
      (To : HomTerm A₄ A₅) (M₁ : HomTerm A₂ A₄) (Fm : HomTerm A₃ A₂)
      (Tm : HomTerm A₂ A₃) (M₂ : HomTerm A₁ A₂) (Ff : HomTerm A₀ A₁)
  → Fm ∘ Tm ≈Term id
  → (To ∘ M₁ ∘ Fm) ∘ (Tm ∘ M₂ ∘ Ff)
    ≈Term To ∘ M₁ ∘ M₂ ∘ Ff
cancel-mid-iso To M₁ Fm Tm M₂ Ff m-iso = begin
  (To ∘ M₁ ∘ Fm) ∘ (Tm ∘ M₂ ∘ Ff)
    ≈⟨ FM.assoc ⟩
  To ∘ (M₁ ∘ Fm) ∘ (Tm ∘ M₂ ∘ Ff)
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  To ∘ M₁ ∘ Fm ∘ Tm ∘ M₂ ∘ Ff
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  To ∘ M₁ ∘ (Fm ∘ Tm) ∘ M₂ ∘ Ff
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ m-iso ⟩∘⟨refl ⟩
  To ∘ M₁ ∘ id ∘ M₂ ∘ Ff
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
  To ∘ M₁ ∘ M₂ ∘ Ff ∎

--------------------------------------------------------------------------------
-- ## 1.  Associativity coherence, `to`-side.
--
-- `c-iso-assoc-from` (re-exported above) is the `from`-side pentagon.  Its
-- `to`-side dual is obtained by composite inversion:
--   `Lhsinv ≈ Rhsinv ∘ Rhs ∘ Lhsinv ≈ Rhsinv ∘ Lhs ∘ Lhsinv ≈ Rhsinv`,
-- using `c-iso-assoc-from` for `Rhs ≈ Lhs` and the `unflatten-++-≅` iso laws
-- to collapse `Lhs ∘ Lhsinv ≈ id` and `Rhsinv ∘ Rhs ≈ id`.

c-iso-assoc-to
  : ∀ xs₁ xs₂ ys
  → _≅_.to (unflatten-++-≅ (xs₁ ++ xs₂) ys)
    ∘ (_≅_.to (unflatten-++-≅ xs₁ xs₂) ⊗₁ id)
    ∘ α⇐ {unflatten xs₁} {unflatten xs₂} {unflatten ys}
  ≈Term subst-id-dom (++-assoc xs₁ xs₂ ys)
        ∘ _≅_.to (unflatten-++-≅ xs₁ (xs₂ ++ ys))
        ∘ (id {unflatten xs₁} ⊗₁ _≅_.to (unflatten-++-≅ xs₂ ys))
c-iso-assoc-to xs₁ xs₂ ys = begin
  Lhsinv
    ≈⟨ ≈-Term-sym idˡ ⟩
  id ∘ Lhsinv
    ≈⟨ ≈-Term-sym RhsinvRhs ⟩∘⟨refl ⟩
  (Rhsinv ∘ Rhs) ∘ Lhsinv
    ≈⟨ (refl⟩∘⟨ ≈-Term-sym (c-iso-assoc-from xs₁ xs₂ ys)) ⟩∘⟨refl ⟩
  (Rhsinv ∘ Lhs) ∘ Lhsinv
    ≈⟨ FM.assoc ⟩
  Rhsinv ∘ (Lhs ∘ Lhsinv)
    ≈⟨ refl⟩∘⟨ LhsLhsinv ⟩
  Rhsinv ∘ id
    ≈⟨ idʳ ⟩
  Rhsinv ∎
  where
    U₁  = unflatten xs₁
    U₂  = unflatten xs₂
    Uys = unflatten ys

    from₁₂   = _≅_.from (unflatten-++-≅ xs₁ xs₂)
    to₁₂     = _≅_.to   (unflatten-++-≅ xs₁ xs₂)
    from₁₂ys = _≅_.from (unflatten-++-≅ (xs₁ ++ xs₂) ys)
    to₁₂ys   = _≅_.to   (unflatten-++-≅ (xs₁ ++ xs₂) ys)
    from₂₃   = _≅_.from (unflatten-++-≅ xs₂ ys)
    to₂₃     = _≅_.to   (unflatten-++-≅ xs₂ ys)
    from₁₂₃  = _≅_.from (unflatten-++-≅ xs₁ (xs₂ ++ ys))
    to₁₂₃    = _≅_.to   (unflatten-++-≅ xs₁ (xs₂ ++ ys))

    e     = ++-assoc xs₁ xs₂ ys
    s-id  = subst-id-cod e
    s-id⁻ = subst-id-dom e

    Lhs    = α⇒ {U₁} {U₂} {Uys} ∘ (from₁₂ ⊗₁ id) ∘ from₁₂ys
    Rhs    = (id {U₁} ⊗₁ from₂₃) ∘ from₁₂₃ ∘ s-id
    Lhsinv = to₁₂ys ∘ (to₁₂ ⊗₁ id) ∘ α⇐ {U₁} {U₂} {Uys}
    Rhsinv = s-id⁻ ∘ to₁₂₃ ∘ (id {U₁} ⊗₁ to₂₃)

    LhsLhsinv : Lhs ∘ Lhsinv ≈Term id
    LhsLhsinv = begin
      (α⇒ ∘ (from₁₂ ⊗₁ id) ∘ from₁₂ys) ∘ (to₁₂ys ∘ (to₁₂ ⊗₁ id) ∘ α⇐)
        ≈⟨ cancel-mid-iso α⇒ (from₁₂ ⊗₁ id) from₁₂ys to₁₂ys (to₁₂ ⊗₁ id) α⇐
             (_≅_.isoʳ (unflatten-++-≅ (xs₁ ++ xs₂) ys)) ⟩
      α⇒ ∘ (from₁₂ ⊗₁ id) ∘ (to₁₂ ⊗₁ id) ∘ α⇐
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      α⇒ ∘ ((from₁₂ ⊗₁ id) ∘ (to₁₂ ⊗₁ id)) ∘ α⇐
        ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
      α⇒ ∘ ((from₁₂ ∘ to₁₂) ⊗₁ (id ∘ id)) ∘ α⇐
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (_≅_.isoʳ (unflatten-++-≅ xs₁ xs₂)) idˡ ⟩∘⟨refl ⟩
      α⇒ ∘ (id ⊗₁ id) ∘ α⇐
        ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
      α⇒ ∘ id ∘ α⇐
        ≈⟨ refl⟩∘⟨ idˡ ⟩
      α⇒ ∘ α⇐
        ≈⟨ α⇒∘α⇐≈id ⟩
      id ∎

    RhsinvRhs : Rhsinv ∘ Rhs ≈Term id
    RhsinvRhs = begin
      (s-id⁻ ∘ to₁₂₃ ∘ (id ⊗₁ to₂₃)) ∘ ((id ⊗₁ from₂₃) ∘ from₁₂₃ ∘ s-id)
        ≈⟨ cancel-mid-iso s-id⁻ to₁₂₃ (id ⊗₁ to₂₃) (id ⊗₁ from₂₃) from₁₂₃ s-id
             mid-iso ⟩
      s-id⁻ ∘ to₁₂₃ ∘ from₁₂₃ ∘ s-id
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      s-id⁻ ∘ (to₁₂₃ ∘ from₁₂₃) ∘ s-id
        ≈⟨ refl⟩∘⟨ _≅_.isoˡ (unflatten-++-≅ xs₁ (xs₂ ++ ys)) ⟩∘⟨refl ⟩
      s-id⁻ ∘ id ∘ s-id
        ≈⟨ refl⟩∘⟨ idˡ ⟩
      s-id⁻ ∘ s-id
        ≈⟨ cast-cancel′ e ⟩
      id ∎
      where
        mid-iso : (id {U₁} ⊗₁ to₂₃) ∘ (id ⊗₁ from₂₃) ≈Term id
        mid-iso =
          ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
            (≈-Term-trans (⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ xs₂ ys)))
                          id⊗id≈id)
