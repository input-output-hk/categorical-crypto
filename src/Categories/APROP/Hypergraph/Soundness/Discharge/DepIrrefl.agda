{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Dependency-irreflexivity for the PRUNED translation `⟪_⟫`:
--
--     dep-irrefl-⟪⟫ : ∀ {A B} (f : HomTerm A B) {e} → ¬ (Dep ⟪ f ⟫ e e)
--
-- i.e. no translated edge's in-vertices and out-vertices share a vertex.
--
-- ROUTE: structural induction on `f`.  Like `FinOrderNoInv`'s `NoInv`, this
-- is FORCED: irreflexivity is a property of the TRANSLATION and does NOT
-- follow from `Linear H` plus the decoder's totality witness
-- `IW.PerHG.Valid (range H.nE)`.  The self-loop `nV = nE = 1`,
-- `ein = eout = v₀ ∷ []`, `dom = cod = []` is `Linear` (v₀ produced once,
-- consumed once) AND `Valid` (the edge SKIPS, so the final stack is
-- `dom = []` `↭ cod = []`), yet `Dep H e e` holds.
--
-- Zero-edge cases are vacuous; `hGen`
-- has `ein`/`eout` of disjoint `_↑ˡ_`/`_↑ʳ_` form; `hTensor`/`hComposeP`
-- route each composite edge through an injective `h` (`injL`/`injR`/the
-- pruned `remapP`), so `EdgeDependency.Dep-reflect` reflects a composite
-- self-dependency down to the sub-graph, where the IH refutes it.  For
-- `hComposeP`, `remapP` is injective on a *translated* `K = ⟪g⟫` because
-- `⟪g⟫.dom`/`⟪h⟫.cod` are `Unique` (`HomTermInvariant`).
--
-- NOTE: `IsoInvarianceWiring.PerHG` asks `¬ Dep H e e` for an ARBITRARY `H`,
-- which is FALSE in general (a self-loop edge).  This module proves the
-- honest `⟪f⟫`-specific statement, supplied at the `H = ⟪f⟫` call site.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.DepIrrefl
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; hGen; hId; hTensor; hSwap; hEmpty; hVar
        ; module hTensor-impl)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Model.HomTermInvariant sig
  using (⟪_⟫-dom-unique; ⟪_⟫-cod-unique)
open import Categories.APROP.Hypergraph.Model.Invariant sig using (↑ˡ≢↑ʳ)
open import Categories.APROP.Hypergraph.Util.Prune
  using (count-non)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep; Dep-reflect)

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; _↑ˡ_; _↑ʳ_; splitAt; join)
open import Data.Fin.Properties
  using (join-splitAt; ↑ˡ-injective; ↑ʳ-injective)
open import Data.List using (List; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans; subst)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- `NoSelfDep G`: no edge of `G` depends on itself.  This is the invariant
-- we carry through the structural induction.

NoSelfDep : Hypergraph FlatGen → Set
NoSelfDep G = ∀ {e} → ¬ Dep {X} {FlatGen} G e e

--------------------------------------------------------------------------------
-- Base cases with `nE = 0`: no edge exists, so `Dep` is vacuous.

NoSelfDep-hEmpty : NoSelfDep hEmpty
NoSelfDep-hEmpty {()}

NoSelfDep-hVar : ∀ x → NoSelfDep (hVar x)
NoSelfDep-hVar x {()}

NoSelfDep-hSwap : ∀ A B → NoSelfDep (hSwap A B)
NoSelfDep-hSwap A B {()}

--------------------------------------------------------------------------------
-- `hGen f`: the unique edge has `ein` of `_↑ˡ_` form and `eout` of `_↑ʳ_`
-- form, disjoint by `↑ˡ≢↑ʳ`.

NoSelfDep-hGen : ∀ {A B} (f : mor A B) → NoSelfDep (hGen f)
NoSelfDep-hGen {A} {B} f {zero} (v , v∈out , v∈in)
  with ∈-map⁻ (length (flatten A) ↑ʳ_) v∈out
     | ∈-map⁻ (_↑ˡ length (flatten B)) v∈in
... | jB , _ , v≡raise | iA , _ , v≡inject =
  ↑ˡ≢↑ʳ iA jB (trans (sym v≡inject) v≡raise)

--------------------------------------------------------------------------------
-- Tensor: a composite edge is a G-edge (via injective `injL`) or a K-edge
-- (via injective `injR`); `Dep-reflect` down to the sub-graph + sub-graph IH
-- closes it.

NoSelfDep-hTensor : ∀ G K → NoSelfDep G → NoSelfDep K → NoSelfDep (hTensor G K)
NoSelfDep-hTensor G K G-nd K-nd {e} (v , v∈out , v∈in) =
  dispatch (splitAt G.nE e)
           (subst (λ x → v ∈ eout-c x) (sym peq) v∈out)
           (subst (λ x → v ∈ ein-c  x) (sym peq) v∈in)
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hTensor-impl G K

    peq : join G.nE K.nE (splitAt G.nE e) ≡ e
    peq = join-splitAt G.nE K.nE e

    injL-inj : ∀ {x y} → injL x ≡ injL y → x ≡ y
    injL-inj {x} {y} eq = ↑ˡ-injective K.nV x y eq

    injR-inj : ∀ {x y} → injR x ≡ injR y → x ≡ y
    injR-inj {x} {y} eq = ↑ʳ-injective G.nV x y eq

    dispatch : (s : Fin G.nE ⊎ Fin K.nE)
             → v ∈ eout-c (join G.nE K.nE s)
             → v ∈ ein-c  (join G.nE K.nE s)
             → ⊥
    dispatch (inj₁ eG) vo vi =
      G-nd (Dep-reflect {sub = G} {H = hTensor G K} injL injL-inj (_↑ˡ K.nE)
              eout-c-inj₁-red ein-c-inj₁-red (v , vo , vi))
    dispatch (inj₂ eK) vo vi =
      K-nd (Dep-reflect {sub = K} {H = hTensor G K} injR injR-inj (G.nE ↑ʳ_)
              eout-c-inj₂-red ein-c-inj₂-red (v , vo , vi))

--------------------------------------------------------------------------------
-- `hId A`: structural on `A`.

NoSelfDep-hId : ∀ A → NoSelfDep (hId A)
NoSelfDep-hId unit       {e} = NoSelfDep-hEmpty {e}
NoSelfDep-hId (Var x)    {e} = NoSelfDep-hVar x {e}
NoSelfDep-hId (A ⊗₀ B)   {e} =
  NoSelfDep-hTensor (hId A) (hId B) (NoSelfDep-hId A) (NoSelfDep-hId B) {e}

--------------------------------------------------------------------------------
-- Pruned composition: like the tensor, but the K-side routing map is the
-- pruned `remapP` (injective when `K.dom`/`G.cod` are `Unique`).
-- Parameterised on `remapP-inj`, instantiated at `⟪h⟫`/`⟪g⟫` below.

NoSelfDep-hComposeP
  : ∀ G K (bdy : codL G ≡ domL K)
  → (let module hCP = hComposeP-impl G K bdy in
     ∀ {i j} → hCP.remapP i ≡ hCP.remapP j → i ≡ j)
  → NoSelfDep G → NoSelfDep K → NoSelfDep (hComposeP G K bdy)
NoSelfDep-hComposeP G K bdy remapP-inj G-nd K-nd {e} (v , v∈out , v∈in) =
  dispatch (splitAt G.nE e)
           (subst (λ x → v ∈ eout-c x) (sym peq) v∈out)
           (subst (λ x → v ∈ ein-c  x) (sym peq) v∈in)
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hComposeP-impl G K bdy

    peq : join G.nE K.nE (splitAt G.nE e) ≡ e
    peq = join-splitAt G.nE K.nE e

    dispatch : (s : Fin G.nE ⊎ Fin K.nE)
             → v ∈ eout-c (join G.nE K.nE s)
             → v ∈ ein-c  (join G.nE K.nE s)
             → ⊥
    dispatch (inj₁ eG) vo vi =
      G-nd (Dep-reflect {sub = G} {H = hComposeP G K bdy}
              injL (λ {x} {y} eq → ↑ˡ-injective (count-non K.dom) x y eq) (_↑ˡ K.nE)
              eout-c-inj₁-red ein-c-inj₁-red (v , vo , vi))
    dispatch (inj₂ eK) vo vi =
      K-nd (Dep-reflect {sub = K} {H = hComposeP G K bdy} remapP remapP-inj (G.nE ↑ʳ_)
              eout-c-inj₂-red ein-c-inj₂-red (v , vo , vi))

--------------------------------------------------------------------------------
-- The `remapP`-injectivity instance for a pruned composition of two
-- *translated* hypergraphs `⟪h⟫`, `⟪g⟫`.

module _ {A B C} (g : HomTerm B C) (h : HomTerm A B) where
  private
    bdy : codL ⟪ h ⟫ ≡ domL ⟪ g ⟫
    bdy = trans (⟪⟫-codL h) (sym (⟪⟫-domL g))

    module hCP = hComposeP-impl ⟪ h ⟫ ⟪ g ⟫ bdy

  -- `remapP` is injective from the `Unique` boundaries of the two translated
  -- hypergraphs (shared `PrunedCompose.remapP-injective-from-unique`).
  ∘-remapP-inj : ∀ {i j} → hCP.remapP i ≡ hCP.remapP j → i ≡ j
  ∘-remapP-inj = hCP.remapP-injective-from-unique (⟪_⟫-cod-unique h) (⟪_⟫-dom-unique g)

--------------------------------------------------------------------------------
-- The invariant holds for every translated hypergraph, by induction on `f`.

NoSelfDep-⟪⟫ : ∀ {A B} (f : HomTerm A B) → NoSelfDep ⟪ f ⟫
NoSelfDep-⟪⟫ (Agen f)        {e} = NoSelfDep-hGen f {e}
NoSelfDep-⟪⟫ (id {A})        {e} = NoSelfDep-hId A {e}
NoSelfDep-⟪⟫ (g ∘ f)         {e} =
  NoSelfDep-hComposeP ⟪ f ⟫ ⟪ g ⟫
    (trans (⟪⟫-codL f) (sym (⟪⟫-domL g)))
    (∘-remapP-inj g f)
    (NoSelfDep-⟪⟫ f) (NoSelfDep-⟪⟫ g) {e}
NoSelfDep-⟪⟫ (f ⊗₁ g)        {e} =
  NoSelfDep-hTensor ⟪ f ⟫ ⟪ g ⟫ (NoSelfDep-⟪⟫ f) (NoSelfDep-⟪⟫ g) {e}
NoSelfDep-⟪⟫ (λ⇒ {A})        {e} = NoSelfDep-hId A {e}
NoSelfDep-⟪⟫ (λ⇐ {A})        {e} = NoSelfDep-hId A {e}
NoSelfDep-⟪⟫ (ρ⇒ {A})        {e} = NoSelfDep-hId (A ⊗₀ unit) {e}
NoSelfDep-⟪⟫ (ρ⇐ {A})        {e} = NoSelfDep-hId (A ⊗₀ unit) {e}
NoSelfDep-⟪⟫ (α⇒ {A}{B}{C})  {e} = NoSelfDep-hId ((A ⊗₀ B) ⊗₀ C) {e}
NoSelfDep-⟪⟫ (α⇐ {A}{B}{C})  {e} = NoSelfDep-hId ((A ⊗₀ B) ⊗₀ C) {e}
NoSelfDep-⟪⟫ (σ {A}{B})      {e} = NoSelfDep-hSwap A B {e}

--------------------------------------------------------------------------------
-- The headline statement.

dep-irrefl-⟪⟫ : ∀ {A B} (f : HomTerm A B) {e} → ¬ (Dep ⟪ f ⟫ e e)
dep-irrefl-⟪⟫ f = NoSelfDep-⟪⟫ f
