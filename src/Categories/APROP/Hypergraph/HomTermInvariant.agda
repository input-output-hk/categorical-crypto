{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Translation-level invariant: for every APROP term `f : HomTerm A B`,
-- the hypergraph `⟪ f ⟫` has a `Unique` domain interface.
--
-- Used by the composition congruence `hComposeP-resp-≅ᴴ`: the `Unique
-- K₁.dom` side condition is always met when K₁ is `⟪ some HomTerm ⟫`.
--
-- Proof by structural induction on `f`. Each case follows from:
--   * `hId-dom-Unique`   (for `id`, `λ⇒`, `λ⇐` whose translation is `hId`).
--   * `hSwap-dom-Unique` (for `σ`).
--   * `hGen-dom-Unique`  (for `Agen`).
--   * `map⁺` + `++⁺`     (for `_∘_`, `_⊗₁_` which are built from `hComposeP`
--                        and `hTensor`).
--   * `subst Unique`      (for `ρ⇒`/`ρ⇐`/`α⇒`/`α⇐` which use `subst₂` over
--                        `++-identityʳ` / `++-assoc`).
--
-- The `subst Unique (sym (dom-subst₂ _ _ _))` step uses a helper that
-- commutes `Hypergraph.dom` past `subst₂`. The helper is defined by
-- refl-refl pattern match, so the Agda term gets stuck on non-refl
-- proofs — but the typechecker still accepts the expression because
-- `dom-subst₂` returns an equality of the right type.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.HomTermInvariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hGen; hSwap)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Invariant sig
  using ( hId-dom-Unique; hSwap-dom-Unique; hGen-dom-Unique
        ; inject+-inj; raise-inj; disj-L-R)

open import Data.Fin using (Fin; inject+; raise)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; subst₂)

--------------------------------------------------------------------------------
-- Helper: `subst₂` over Hypergraph preserves `dom` (up to propositional
-- equality). Used to discharge the ρ/α cases of `⟪_⟫-dom-unique`.
--
-- Defined by pattern on both equalities as `refl`. For non-refl inputs the
-- body doesn't reduce, but the typechecker still accepts it as a term of
-- the given equality type because there is no other canonical element.

private
  -- Transport `Unique` across the `subst₂` wrapper on the Hypergraph.
  -- Pattern-matches both equalities as `refl`, at which point
  -- `subst₂ _ refl refl = id` and the Unique witness passes through.
  Unique-subst₂-dom
    : ∀ {As Bs As' Bs' : List X}
        (eq₁ : As ≡ As') (eq₂ : Bs ≡ Bs')
        (G : Hypergraph FlatGen As Bs)
    → Unique (Hypergraph.dom G)
    → Unique (Hypergraph.dom (subst₂ (Hypergraph FlatGen) eq₁ eq₂ G))
  Unique-subst₂-dom refl refl G p = p

--------------------------------------------------------------------------------
-- `⟪ f ⟫.dom` is Unique for every APROP term.

⟪_⟫-dom-unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.dom ⟪ f ⟫)

-- Generator: dom = map (inject+ nB) (range nA).  `range-Unique` + map⁺.
⟪ Agen g ⟫-dom-unique = hGen-dom-Unique g

-- Identity: dom = (hId A).dom.
⟪ id {A} ⟫-dom-unique = hId-dom-Unique A

-- Composition: ⟪g ∘ h⟫ = hComposeP ⟪h⟫ ⟪g⟫; its dom = map injL ⟪h⟫.dom
-- where injL = inject+ (count-non ⟪g⟫.dom) is injective.
⟪ g ∘ h ⟫-dom-unique =
  Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫-dom-unique h)

-- Tensor: ⟪f ⊗₁ g⟫.dom = map injL ⟪f⟫.dom ++ map injR ⟪g⟫.dom.
-- map⁺ for each side + ++⁺ with the inject+/raise disjointness.
⟪ f ⊗₁ g ⟫-dom-unique =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫-dom-unique f))
    (Uniq-Prop.map⁺ (raise-inj   _) (⟪_⟫-dom-unique g))
    (disj-L-R (Hypergraph.dom ⟪ f ⟫) (Hypergraph.dom ⟪ g ⟫))

-- Unitors that are translated to `hId` directly.
⟪ λ⇒ {A} ⟫-dom-unique = hId-dom-Unique A
⟪ λ⇐ {A} ⟫-dom-unique = hId-dom-Unique A

-- Right unitors: subst₂ over hId (A ⊗₀ unit). Lift Unique of the
-- inner hId.dom through the subst via the refl-refl transport helper.
--
-- The specific subst₂ proofs from `⟪_⟫` must match — pass them explicitly
-- so Agda can unify the goal with `Unique (Hypergraph.dom (subst₂ ...))`.
⟪ ρ⇒ {A} ⟫-dom-unique =
  Unique-subst₂-dom
    refl (++-identityʳ (flatten A))
    (hId (A ⊗₀ unit))
    (hId-dom-Unique (A ⊗₀ unit))

⟪ ρ⇐ {A} ⟫-dom-unique =
  Unique-subst₂-dom
    (++-identityʳ (flatten A)) refl
    (hId (A ⊗₀ unit))
    (hId-dom-Unique (A ⊗₀ unit))

-- Associators: subst₂ over hId ((A ⊗₀ B) ⊗₀ C).
⟪ α⇒ {A} {B} {C} ⟫-dom-unique =
  Unique-subst₂-dom
    refl (++-assoc (flatten A) (flatten B) (flatten C))
    (hId ((A ⊗₀ B) ⊗₀ C))
    (hId-dom-Unique ((A ⊗₀ B) ⊗₀ C))

⟪ α⇐ {A} {B} {C} ⟫-dom-unique =
  Unique-subst₂-dom
    (++-assoc (flatten A) (flatten B) (flatten C)) refl
    (hId ((A ⊗₀ B) ⊗₀ C))
    (hId-dom-Unique ((A ⊗₀ B) ⊗₀ C))

-- Braiding: dom = map (inject+ _) (range nA) ++ map (raise _) (range nB).
⟪ σ {A} {B} ⟫-dom-unique = hSwap-dom-Unique A B
