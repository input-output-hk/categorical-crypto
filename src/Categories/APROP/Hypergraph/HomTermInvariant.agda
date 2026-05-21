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
        ; hId-cod-Unique; hSwap-cod-Unique; hGen-cod-Unique
        ; inject+-inj; raise-inj; disj-L-R)
open import Categories.APROP.Hypergraph.Prune
  using (remap-injective; lookup-injective-unique; nonMem-Unique)

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

-- DE-INDEXED REFACTOR: `Unique-subst₂-dom` was a refl-refl pattern
-- match that transported `Unique` across `subst₂ (Hypergraph FlatGen)`.
-- Under de-indexing, no such subst₂ on Hypergraph arises.

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

-- ρ⇒/ρ⇐/α⇒/α⇐: under de-indexing, `⟪ ρ⇒ {A} ⟫ = hId (A ⊗₀ unit)` directly,
-- so we just delegate to `hId-dom-Unique`.
⟪ ρ⇒ {A} ⟫-dom-unique = hId-dom-Unique (A ⊗₀ unit)
⟪ ρ⇐ {A} ⟫-dom-unique = hId-dom-Unique (A ⊗₀ unit)
⟪ α⇒ {A} {B} {C} ⟫-dom-unique = hId-dom-Unique ((A ⊗₀ B) ⊗₀ C)
⟪ α⇐ {A} {B} {C} ⟫-dom-unique = hId-dom-Unique ((A ⊗₀ B) ⊗₀ C)

-- Braiding: dom = map (inject+ _) (range nA) ++ map (raise _) (range nB).
⟪ σ {A} {B} ⟫-dom-unique = hSwap-dom-Unique A B

--------------------------------------------------------------------------------
-- `⟪ f ⟫.cod` is Unique for every APROP term — the cod-side counterpart
-- of `⟪_⟫-dom-unique`.
--
-- The structural cases (atomic NoSigma + atomic Agen + σ + ⊗) follow
-- straightforwardly from the existing `hX-cod-Unique` lemmas and
-- `map⁺` / `++⁺`.  The composition case `g ∘ h` reduces to showing
-- `Unique (map remapP K.cod)` where `K = ⟪g⟫`, which is closed by
-- `remap-injective` (in `Prune`) — `remapP` is globally injective when
-- `K.dom` is Unique (always, by `⟪_⟫-dom-unique`) and `G.cod` (= `⟪h⟫.cod`)
-- is Unique (by the IH).

⟪_⟫-cod-unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.cod ⟪ f ⟫)

-- Generator: cod = map (nA ↑ʳ_) (range nB).
⟪ Agen g ⟫-cod-unique = hGen-cod-Unique g

-- Identity: cod = (hId A).cod.
⟪ id {A} ⟫-cod-unique = hId-cod-Unique A

-- Composition: ⟪g ∘ h⟫ = hComposeP ⟪h⟫ ⟪g⟫; cod = map remapP ⟪g⟫.cod.
-- `remapP = remap K.dom lookup-cod` where K = ⟪g⟫, lookup-cod uses ⟪h⟫.cod.
-- `remap-injective` requires:
--   * Unique K.dom = Unique ⟪g⟫.dom: from `⟪_⟫-dom-unique g`.
--   * lookup-cod injective: requires Unique ⟪h⟫.cod (from IH on h)
--     plus cast injective.
-- Then we get globally-injective remapP and apply Uniq-Prop.map⁺ to
-- Unique ⟪g⟫.cod (IH on g).
⟪ g ∘ h ⟫-cod-unique =
  Uniq-Prop.map⁺ remapP-inj (⟪_⟫-cod-unique g)
  where
    open import Data.Fin using (cast)
    open import Data.Fin.Properties using (toℕ-cast; toℕ-injective)
    open import Relation.Binary.PropositionalEquality using (trans; cong)
    open import Categories.APROP.Hypergraph.Translation sig using (⟪⟫-codL; ⟪⟫-domL)

    bdy = trans (⟪⟫-codL h) (sym (⟪⟫-domL g))
    module hCP = hComposeP-impl ⟪ h ⟫ ⟪ g ⟫ bdy

    -- lookup-cod : Fin (length K.dom) → Fin G.nV
    -- lookup-cod i = lookup G.cod (cast dom-cod-len i).
    -- Injective: lookup G.cod is injective on Unique G.cod (IH on h),
    -- and cast is injective.
    open import Data.Nat using (ℕ)
    cast-inj : ∀ {i j} → cast hCP.dom-cod-len i ≡ cast hCP.dom-cod-len j → i ≡ j
    cast-inj {i} {j} eq = toℕ-injective
      (trans (sym (toℕ-cast hCP.dom-cod-len i))
             (trans (cong (Data.Fin.toℕ) eq) (toℕ-cast hCP.dom-cod-len j)))
      where open import Data.Fin

    lookup-cod-inj : ∀ {i j} → hCP.lookup-cod i ≡ hCP.lookup-cod j → i ≡ j
    lookup-cod-inj {i} {j} eq =
      cast-inj (lookup-injective-unique (⟪_⟫-cod-unique h) _ _ eq)

    remapP-inj : ∀ {i j} → hCP.remapP i ≡ hCP.remapP j → i ≡ j
    remapP-inj eq =
      remap-injective _ _ (⟪_⟫-dom-unique g) lookup-cod-inj eq

-- Tensor: ⟪f ⊗₁ g⟫.cod = map injL ⟪f⟫.cod ++ map injR ⟪g⟫.cod.
⟪ f ⊗₁ g ⟫-cod-unique =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫-cod-unique f))
    (Uniq-Prop.map⁺ (raise-inj   _) (⟪_⟫-cod-unique g))
    (disj-L-R (Hypergraph.cod ⟪ f ⟫) (Hypergraph.cod ⟪ g ⟫))

-- Unitors that translate to hId.
⟪ λ⇒ {A} ⟫-cod-unique = hId-cod-Unique A
⟪ λ⇐ {A} ⟫-cod-unique = hId-cod-Unique A

-- ρ/α translated to hId via de-indexing.
⟪ ρ⇒ {A} ⟫-cod-unique = hId-cod-Unique (A ⊗₀ unit)
⟪ ρ⇐ {A} ⟫-cod-unique = hId-cod-Unique (A ⊗₀ unit)
⟪ α⇒ {A} {B} {C} ⟫-cod-unique = hId-cod-Unique ((A ⊗₀ B) ⊗₀ C)
⟪ α⇐ {A} {B} {C} ⟫-cod-unique = hId-cod-Unique ((A ⊗₀ B) ⊗₀ C)

-- Braiding.
⟪ σ {A} {B} ⟫-cod-unique = hSwap-cod-Unique A B
