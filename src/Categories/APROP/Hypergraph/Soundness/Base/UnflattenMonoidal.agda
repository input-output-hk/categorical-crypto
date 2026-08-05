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
--   * `cancel-mid-iso` and the `subst`-identity morphisms
--     `subst-id-{dom,cod}`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal
  (sig : APROPSignature) where

open APROP sig

-- Re-export `unflatten` / `unflatten-++-≅` so consumers can open this module
-- alone for the full boundary-coherence interface.
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig public
  using (unflatten; unflatten-++-≅; _≅_; flatten-unflatten; unflatten-flatten-≈)

-- The `from`-side associativity pentagon, imported and re-exported as-is.
open import Categories.APROP.Hypergraph.Soundness.Discharge.CIsoAssocFromCons sig public
  using (c-iso-assoc-from)

open import Categories.Category using (Category)

open import Data.List using (List; _∷_; _++_)
open import Data.List.Properties using (++-assoc)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## 0.  Generic middle-iso cancellation.
--
-- Two 3-fold composites sharing a middle iso `Fm ∘ Tm ≈ id` cancel it, leaving
-- `To ∘ M₁ ∘ M₂ ∘ Ff`.  No assumption on `M₁` / `M₂`.  (Part of the
-- transport-absorption algebra of §2, hoisted above §1 because the
-- `c-iso-assoc-to` inversion chases below consume it.)
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
  ≈Term subst (λ z → HomTerm (unflatten z) (unflatten ((xs₁ ++ xs₂) ++ ys)))
              (++-assoc xs₁ xs₂ ys) id
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

    e   = ++-assoc xs₁ xs₂ ys
    s-id : HomTerm (unflatten ((xs₁ ++ xs₂) ++ ys)) (unflatten (xs₁ ++ (xs₂ ++ ys)))
    s-id = subst (λ z → HomTerm (unflatten ((xs₁ ++ xs₂) ++ ys)) (unflatten z)) e id
    s-id⁻ : HomTerm (unflatten (xs₁ ++ (xs₂ ++ ys))) (unflatten ((xs₁ ++ xs₂) ++ ys))
    s-id⁻ = subst (λ z → HomTerm (unflatten z) (unflatten ((xs₁ ++ xs₂) ++ ys))) e id

    Lhs    = α⇒ {U₁} {U₂} {Uys} ∘ (from₁₂ ⊗₁ id) ∘ from₁₂ys
    Rhs    = (id {U₁} ⊗₁ from₂₃) ∘ from₁₂₃ ∘ s-id
    Lhsinv = to₁₂ys ∘ (to₁₂ ⊗₁ id) ∘ α⇐ {U₁} {U₂} {Uys}
    Rhsinv = s-id⁻ ∘ to₁₂₃ ∘ (id {U₁} ⊗₁ to₂₃)

    s-id⁻-s-id : s-id⁻ ∘ s-id ≈Term id
    s-id⁻-s-id = lemma e
      where
        lemma : ∀ {a b : List X} (p : a ≡ b)
              → subst (λ z → HomTerm (unflatten z) (unflatten a)) p id
                ∘ subst (λ z → HomTerm (unflatten a) (unflatten z)) p id
                ≈Term id
        lemma refl = idˡ

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
        ≈⟨ s-id⁻-s-id ⟩
      id ∎
      where
        mid-iso : (id {U₁} ⊗₁ to₂₃) ∘ (id ⊗₁ from₂₃) ≈Term id
        mid-iso =
          ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
            (≈-Term-trans (⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ xs₂ ys)))
                          id⊗id≈id)

--------------------------------------------------------------------------------
-- ## 2.  `subst`-identity morphisms on the domain / codomain, over
-- `unflatten` (the surviving slice of the transport-absorption algebra).

subst-id-dom : ∀ {a b : List X} → a ≡ b → HomTerm (unflatten b) (unflatten a)
subst-id-dom {a} p = subst (λ z → HomTerm (unflatten z) (unflatten a)) p id

subst-id-cod : ∀ {c d : List X} → c ≡ d → HomTerm (unflatten c) (unflatten d)
subst-id-cod {c} q = subst (λ z → HomTerm (unflatten c) (unflatten z)) q id

-- Their groupoid laws: `sym`-exchange between the two sides, the four
-- cancellations, the cons-frame law, and the `subst₂` presentation.
cast-dc : ∀ {a b : List X} (p : a ≡ b) → subst-id-dom (sym p) ≈Term subst-id-cod p
cast-dc refl = ≈-Term-refl

cast-cd : ∀ {a b : List X} (p : a ≡ b) → subst-id-dom p ≈Term subst-id-cod (sym p)
cast-cd refl = ≈-Term-refl

cast-cancel : ∀ {a b : List X} (p : a ≡ b) → subst-id-cod p ∘ subst-id-dom p ≈Term id
cast-cancel refl = idˡ

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

cod-as-subst₂ : ∀ {a b : List X} (e : a ≡ b)
              → subst-id-cod e ≡ subst₂ HomTerm refl (cong unflatten e) (id {unflatten a})
cod-as-subst₂ refl = refl

dom-as-subst₂ : ∀ {a b : List X} (e : a ≡ b)
              → subst-id-cod (sym e) ≡ subst₂ HomTerm (cong unflatten e) refl (id {unflatten a})
dom-as-subst₂ refl = refl
