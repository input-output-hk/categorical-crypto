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
open import Categories.Morphism.Reasoning FreeMonoidal
  using (center; cancelʳ; cancelˡ)
open import Categories.Morphism.Reasoning.Ext FreeMonoidal using (inv-resp)

open import Data.List using (_++_)
open import Data.List.Properties using (++-assoc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## 0.  Generic middle-iso cancellation.
--
-- Two 3-fold composites sharing a middle iso `Fm ∘ Tm ≈ id` cancel it, leaving
-- `To ∘ M₁ ∘ M₂ ∘ Ff`.  No assumption on `M₁` / `M₂`.
cancel-mid-iso
  : ∀ {A₀ A₁ A₂ A₃ A₄ A₅ : ObjTerm}
      (To : HomTerm A₄ A₅) (M₁ : HomTerm A₂ A₄) (Fm : HomTerm A₃ A₂)
      (Tm : HomTerm A₂ A₃) (M₂ : HomTerm A₁ A₂) (Ff : HomTerm A₀ A₁)
  → Fm ∘ Tm ≈Term id
  → (To ∘ M₁ ∘ Fm) ∘ (Tm ∘ M₂ ∘ Ff)
    ≈Term To ∘ M₁ ∘ M₂ ∘ Ff
-- `cancelʳ m-iso : (M₁ ∘ Fm) ∘ Tm ≈ M₁`, in the `center` of the composite.
cancel-mid-iso _ _ _ _ _ _ m-iso = center (cancelʳ m-iso)

-- A 3-fold composite and its reverse cancel, innermost pair first.
cancel₃
  : ∀ {A₀ A₁ A₂ A₃ : ObjTerm}
      {a : HomTerm A₂ A₃} {b : HomTerm A₁ A₂} {c : HomTerm A₀ A₁}
      {c⁻ : HomTerm A₁ A₀} {b⁻ : HomTerm A₂ A₁} {a⁻ : HomTerm A₃ A₂}
  → c ∘ c⁻ ≈Term id → b ∘ b⁻ ≈Term id → a ∘ a⁻ ≈Term id
  → (a ∘ b ∘ c) ∘ (c⁻ ∘ b⁻ ∘ a⁻) ≈Term id
cancel₃ hc hb ha = center (cancelʳ hc) ○ (refl⟩∘⟨ cancelˡ hb) ○ ha

--------------------------------------------------------------------------------
-- ## 1.  Associativity coherence, `to`-side.
--
-- `c-iso-assoc-from` (re-exported above) is the `from`-side pentagon.  Its
-- `to`-side dual is that same equation between the two INVERSE composites:
-- each side is a 3-fold composite whose reverse cancels pairwise (`cancel₃`),
-- so `inv-resp` transports `Rhs ≈ Lhs` to `Rhsinv ≈ Lhsinv`.

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
