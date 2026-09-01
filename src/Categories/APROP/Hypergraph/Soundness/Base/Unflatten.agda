{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `unflatten : List X → ObjTerm`, the right-associated `unit`-padded
-- decoder.  `unflatten ∘ flatten` holds only up to `≈Term`, so it is
-- packaged as a FreeMonoidal iso built from α/λ/ρ.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Base.Unflatten (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)


open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal using (_⊗ᵢ_)
open import Categories.Morphism FreeMonoidal public using (_≅_; module ≅)

open Monoidal Monoidal-FreeMonoidal using (unitorʳ)

--------------------------------------------------------------------------------
-- `unflatten` is re-exported from `PermuteCoherence.Unflatten` (same
-- definition over generic `FreeMonoidalData`) so SMC bridges observe
-- definitional equality between the two unflattens.

open import Categories.PermuteCoherence.Unflatten asFreeMonoidalData public
  using (unflatten; unflatten-++-≅)

--------------------------------------------------------------------------------
-- The `unflatten ∘ flatten` round-trip is a coherence iso, not a
-- propositional equality.

unflatten-flatten-≈ : ∀ (A : ObjTerm) → A ≅ unflatten (flatten A)
unflatten-flatten-≈ unit     = ≅.refl
unflatten-flatten-≈ (Var x)  = ≅.sym unitorʳ
unflatten-flatten-≈ (A ⊗₀ B) =
  ≅.trans (unflatten-flatten-≈ A ⊗ᵢ unflatten-flatten-≈ B)
          (≅.sym (unflatten-++-≅ (flatten A) (flatten B)))

--------------------------------------------------------------------------------
-- `bridge`: `f` composed with the unflatten-flatten coherence isos on each
-- side (needed because `flatten`/`unflatten` are inverse only up to iso).
-- Lives next to `unflatten-flatten-≈` — the only thing it depends on — so the
-- bridge/boundary layer need not import the heavy decoder.

bridge : ∀ {A B} → HomTerm A B → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
bridge {A} {B} f = _≅_.from (unflatten-flatten-≈ B) ∘ f ∘ _≅_.to (unflatten-flatten-≈ A)

--------------------------------------------------------------------------------
-- `subst`-identity morphisms on the domain / codomain, over `unflatten`, and
-- their groupoid laws.  They live here — below every consumer — so that the
-- bridge/boundary layer (`Bridge/BridgeCoherence`, `Strict/Soundness`), the
-- coherence-iso layer (`Base/UnflattenMonoidal`) and `Strict/Embed` (which
-- imports this leaf DIRECTLY — nothing re-exports the kit) all share ONE
-- spelling.

subst-id-cod : ∀ {c d : List X} → c ≡ d → HomTerm (unflatten c) (unflatten d)
subst-id-cod {c} q = subst (λ z → HomTerm (unflatten c) (unflatten z)) q id

-- The domain-side spelling IS the codomain-side one at the inverse proof, and
-- is kept as a name because that is how the `Embed` chains read.  Being
-- definitional, it costs no `≈Term` step to cross.
subst-id-dom : ∀ {a b : List X} → a ≡ b → HomTerm (unflatten b) (unflatten a)
subst-id-dom p = subst-id-cod (sym p)

-- `sym`-exchange (the OTHER direction, where `sym (sym p)` is not `p`), the
-- cancellations, and the cons-frame law.
cast-dc : ∀ {a b : List X} (p : a ≡ b) → subst-id-dom (sym p) ≈Term subst-id-cod p
cast-dc refl = ≈-Term-refl

cast-cancel′ : ∀ {a b : List X} (p : a ≡ b) → subst-id-dom p ∘ subst-id-cod p ≈Term id
cast-cancel′ refl = idˡ

cod-cancel : ∀ {a b : List X} (p : a ≡ b) → subst-id-cod p ∘ subst-id-cod (sym p) ≈Term id
cod-cancel refl = idˡ

dom-cancel : ∀ {a b : List X} (p : a ≡ b) → subst-id-dom (sym p) ∘ subst-id-dom p ≈Term id
dom-cancel refl = idˡ

subst-cod-cons
  : ∀ {x : X} {a b : List X} (e : a ≡ b)
  → id {Var x} ⊗₁ subst-id-cod e ≈Term subst-id-cod (cong (x ∷_) e)
subst-cod-cons refl = id⊗id≈id
