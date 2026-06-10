{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `unflatten` packaged as a STRONG MONOIDAL FUNCTOR
--
--   (List X, _++_, [])  ⟶  (ObjTerm, _⊗₀_, unit)     over `FreeMonoidal`.
--
-- The object map is `unflatten : List X → ObjTerm` (the right-associated,
-- `unit`-padded fold from `Soundness/Unflatten.agda`) and the structure iso
-- (laxator) is `unflatten-++-≅`.  This module collects the associativity
-- coherence (both directions) and the transport-absorption algebra that the
-- downstream box-coherence proofs (`Discharge/Sub/DecodeTensorShape.agda`)
-- consume, RELOCATING/generalising them out of those modules into one clean
-- reusable interface.
--
-- Provenance of the proofs:
--   * `c-iso-assoc-from`  — imported and re-exported from
--     `Discharge/CIsoAssocFromCons.agda` (the `from`-side pentagon).
--   * `c-iso-assoc-to`    — the `to`-side dual, reproved here by composite
--     inversion (the technique used inline in `module BoxAssoc` of
--     `Discharge/Sub/DecodeTensorShape.agda`).
--   * the transport-absorption lemmas (`cancel-mid-iso`, `conj-lemma`,
--     `subst-id-{dom,cod}`, `bridge-{dom,cod}`, `to-uf-cong`, `from-uf-cong`,
--     `subst-2`) — reproved standalone here (they were `private` in
--     `DecodeTensorShape.agda`).
--   * laxator naturality under `map φ` — `to-uf-map-++` / `from-uf-map-++`,
--     the `map-++` specialisation of the cong-transport lemmas (this is the
--     form the per-edge `box-of` bridges actually use, cf. `Decode.agda`'s
--     `mid'`).
--
-- Everything is honestly proven; the module is `--safe` and postulate-free.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.UnflattenMonoidal
  (sig : APROPSignature) where

open APROP sig

-- Re-export `unflatten` / `unflatten-++-≅` so consumers can open this module
-- alone for the full strong-monoidal interface.
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig public
  using (unflatten; unflatten-++-≅; _≅_; flatten-unflatten; unflatten-flatten-≈)

-- The `from`-side associativity pentagon, imported and re-exported as-is.
open import Categories.APROP.Hypergraph.Soundness.Discharge.CIsoAssocFromCons sig public
  using (c-iso-assoc-from; c-iso-assoc-from-cons)

open import Categories.Category using (Category)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; map-++)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst; subst₂)

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
-- ## 2.  Transport-absorption algebra.
--
-- These are the `subst`/`subst₂`-shuffling lemmas the block ladders use to
-- move list-equality transports across composition, tensor, and the laxator.

-- (`cancel-mid-iso`, the generic middle-iso cancellation, lives in §0 above.)

-- `subst₂ HomTerm p q t` re-expressed as the conjugation
-- `(subst on cod) ∘ t ∘ (subst on dom)` by `subst`-identity morphisms.
-- General over arbitrary `ObjTerm` boundaries.
conj-lemma
  : ∀ {A B A' B' : ObjTerm} (p : A ≡ A') (q : B ≡ B') (t : HomTerm A B)
  → subst₂ HomTerm p q t
    ≈Term subst (λ z → HomTerm B z) q id
          ∘ t
          ∘ subst (λ z → HomTerm z A) p id
conj-lemma refl refl t = ≈-Term-trans (≈-Term-sym idˡ) (refl⟩∘⟨ ≈-Term-sym idʳ)

-- `subst`-identity morphisms on the domain / codomain, over `unflatten`.
subst-id-dom : ∀ {a b : List X} → a ≡ b
             → HomTerm (unflatten b) (unflatten a)
subst-id-dom {a} p = subst (λ z → HomTerm (unflatten z) (unflatten a)) p id

subst-id-cod : ∀ {c d : List X} → c ≡ d
             → HomTerm (unflatten c) (unflatten d)
subst-id-cod {c} q = subst (λ z → HomTerm (unflatten c) (unflatten z)) q id

-- `subst`-on-left/right re-expressed across `cong unflatten (sym e)` / `e`.
bridge-dom : ∀ {a b : List X} (e : a ≡ b)
           → subst (λ z → HomTerm z (unflatten b)) (cong unflatten (sym e)) id
             ≡ subst (λ z → HomTerm (unflatten a) (unflatten z)) e id
bridge-dom refl = refl

bridge-cod : ∀ {a b : List X} (e : a ≡ b)
           → subst (λ z → HomTerm (unflatten b) z) (cong unflatten (sym e)) id
             ≡ subst (λ z → HomTerm (unflatten z) (unflatten a)) e id
bridge-cod refl = refl

-- The laxator's `to` / `from` transported along block-list equalities; this is
-- naturality of `unflatten-++-≅` with respect to `_++_`.
to-uf-cong
  : ∀ {Xs Xs' Ys Ys' : List X} (pX : Xs ≡ Xs') (pY : Ys ≡ Ys')
  → subst₂ HomTerm (cong₂ _⊗₀_ (cong unflatten pX) (cong unflatten pY))
                   (cong unflatten (cong₂ _++_ pX pY))
      (_≅_.to (unflatten-++-≅ Xs Ys))
    ≡ _≅_.to (unflatten-++-≅ Xs' Ys')
to-uf-cong refl refl = refl

from-uf-cong
  : ∀ {Xs Xs' Ys Ys' : List X} (pX : Xs ≡ Xs') (pY : Ys ≡ Ys')
  → subst₂ HomTerm (cong unflatten (cong₂ _++_ pX pY))
                   (cong₂ _⊗₀_ (cong unflatten pX) (cong unflatten pY))
      (_≅_.from (unflatten-++-≅ Xs Ys))
    ≡ _≅_.from (unflatten-++-≅ Xs' Ys')
from-uf-cong refl refl = refl

-- A single-index `subst` over `HomTerm (f z) (h z)` re-expressed as the
-- two-index `subst₂` over `cong f` / `cong h`.
subst-2 : ∀ {a b : List X} (f h : List X → ObjTerm) (r : a ≡ b)
            (t : HomTerm (f a) (h a))
        → subst (λ z → HomTerm (f z) (h z)) r t
          ≡ subst₂ HomTerm (cong f r) (cong h r) t
subst-2 f h refl t = refl

--------------------------------------------------------------------------------
-- ## 3.  Laxator naturality under `map φ`.
--
-- For `φ : X → X`, the laxator at the mapped lists, transported along
-- `map-++ φ a b : map φ (a ++ b) ≡ map φ a ++ map φ b`, equals the laxator at
-- the already-split index `map φ a , map φ b`.  This is the precise transport
-- the per-edge `box-of` bridges consume (cf. `mid'` in `Decode.agda`, which
-- frames each block factor by `subst₂ … (cong unflatten (sym (map-++ …)))`).
-- Specialisations of `to-uf-cong` / `from-uf-cong` at the `map-++` equality.

to-uf-map-++
  : ∀ (φ : X → X) (a b : List X)
  → subst₂ HomTerm (cong₂ _⊗₀_ (cong unflatten (map-++ φ a b)) refl)
                   (cong unflatten (cong₂ _++_ (map-++ φ a b) refl))
      (_≅_.to (unflatten-++-≅ (map φ (a ++ b)) (map φ b)))
    ≡ _≅_.to (unflatten-++-≅ (map φ a ++ map φ b) (map φ b))
to-uf-map-++ φ a b = to-uf-cong (map-++ φ a b) refl

from-uf-map-++
  : ∀ (φ : X → X) (a b : List X)
  → subst₂ HomTerm (cong unflatten (cong₂ _++_ (map-++ φ a b) refl))
                   (cong₂ _⊗₀_ (cong unflatten (map-++ φ a b)) refl)
      (_≅_.from (unflatten-++-≅ (map φ (a ++ b)) (map φ b)))
    ≡ _≅_.from (unflatten-++-≅ (map φ a ++ map φ b) (map φ b))
from-uf-map-++ φ a b = from-uf-cong (map-++ φ a b) refl
