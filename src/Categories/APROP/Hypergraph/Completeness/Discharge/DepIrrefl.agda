{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Dependency-irreflexivity for the PRUNED translation `⟪_⟫`.
--
-- For every APROP term `f` and every edge `e` of the translated hypergraph
-- `⟪ f ⟫`, the edge does not depend on itself:
--
--     dep-irrefl-⟪⟫ : ∀ {A B} (f : HomTerm A B) {e} → ¬ (Dep ⟪ f ⟫ e e)
--
-- Recall `Dep G e e = ∃[ v ] (v ∈ eout G e × v ∈ ein G e)`, i.e. the
-- in-vertices and out-vertices of `e` share a vertex.  We prove this never
-- happens for a translated edge.
--
-- ROUTE: structural induction on `f`, following how `⟪_⟫` builds edges
-- (`hGen` / `hId` / `hSwap` / `hTensor` / `hComposeP`):
--
--   * `hId`, `hSwap`        : `nE = 0`, no edges — vacuous.
--   * `hGen f`              : the single edge has
--                              `ein  = map (_↑ˡ nB) (range nA)`  (left  Fins)
--                              `eout = map (nA ↑ʳ_) (range nB)`  (right Fins)
--                             which are disjoint by `↑ˡ-↑ʳ-disjoint`.
--   * `hTensor G K`         : an edge is a G-edge routed through `injL`
--                             (an `_↑ˡ_`, injective) or a K-edge routed
--                             through `injR` (a `_↑ʳ_`, injective).  In
--                             either case `ein`/`eout` of the composite
--                             edge are `map h (sub.ein/eout)`; an injective
--                             `h` carries the sub-graph's edge-disjointness
--                             (the IH) to the composite.
--   * `hComposeP G K`       : same, with the K-side routed through the
--                             pruned `remapP`.  `remapP` is injective on a
--                             *translated* `K = ⟪g⟫` because `⟪g⟫.dom` and
--                             `⟪h⟫.cod` are `Unique` (imported from
--                             `HomTermInvariant`), exactly the side
--                             conditions of `Prune.remap-injective`.
--
-- NOTE: the postulate in `IsoInvarianceWiring.PerHG` asks `∀ {e} → ¬ Dep H
-- e e` for an ARBITRARY `H`, which is FALSE in general (an arbitrary
-- hypergraph may have a self-loop edge).  This module proves the honest,
-- `⟪f⟫`-specific statement; wiring it into `PerHG` requires restructuring
-- `PerHG` to consume the `⟪f⟫` version rather than an arbitrary-`H` one.
--
-- This module is `--without-K` (not `--safe`) only because it imports
-- `HomTermInvariant`, which is itself `--without-K`.  It adds no postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DepIrrefl
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hGen; hId; hTensor; hSwap; hEmpty; hVar
        ; module hTensor-impl)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique; ⟪_⟫-cod-unique)
open import Categories.APROP.Hypergraph.Prune
  using (remap-injective; lookup-injective-unique; count-non)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; cast; toℕ)
open import Data.Fin.Properties
  using (join-splitAt; toℕ-cast; toℕ-injective
        ; ↑ˡ-injective; ↑ʳ-injective; splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- `NoSelfDep G`: no edge of `G` depends on itself.  This is the invariant
-- we carry through the structural induction.

NoSelfDep : Hypergraph FlatGen → Set
NoSelfDep G = ∀ {e} → ¬ Dep {X} {FlatGen} G e e

--------------------------------------------------------------------------------
-- Disjointness of the `_↑ˡ k` and `m ↑ʳ_` ranges (a left Fin can never
-- equal a right Fin).  Local copy; `Prune.↑ˡ-↑ʳ-disjoint` lives in a module
-- parameterised on an unused `n`, which would leave a stray metavariable at
-- every call site.

↑ˡ≢↑ʳ : ∀ {m k} (i : Fin m) (j : Fin k) → i ↑ˡ k ≡ m ↑ʳ j → ⊥
↑ˡ≢↑ʳ {m} {k} i j eq
  with splitAt-↑ˡ m i k | splitAt-↑ʳ m k j | cong (splitAt m) eq
... | i-red | j-red | split-eq = case-absurd (trans (sym i-red) (trans split-eq j-red))
  where
    case-absurd : ∀ {S T : Set} {x : S} {y : T} → inj₁ x ≡ inj₂ y → ⊥
    case-absurd ()

--------------------------------------------------------------------------------
-- Generic transport lemma.
--
-- If `h` is injective and the lists `xout`, `xin` share no vertex, then
-- `map h xout` and `map h xin` share no vertex.  This is the engine that
-- carries edge-disjointness from a sub-graph to a composite, since every
-- composite edge's `ein`/`eout` is `map h (sub.ein/eout)` for an injective
-- routing map `h`.

map-inj-disjoint
  : ∀ {p q} (h : Fin p → Fin q)
  → (∀ {x y} → h x ≡ h y → x ≡ y)
  → {xout xin : List (Fin p)}
  → (∀ {u} → u ∈ xout → u ∈ xin → ⊥)
  → ∀ {w} → w ∈ map h xout → w ∈ map h xin → ⊥
map-inj-disjoint h h-inj {xout} {xin} disj {w} w∈out w∈in
  with ∈-map⁻ h w∈out | ∈-map⁻ h w∈in
... | u₁ , u₁∈out , w≡hu₁ | u₂ , u₂∈in , w≡hu₂ =
  disj u₁∈out (subst (_∈ xin) (sym u₁≡u₂) u₂∈in)
  where
    u₁≡u₂ : u₁ ≡ u₂
    u₁≡u₂ = h-inj (trans (sym w≡hu₁) w≡hu₂)

--------------------------------------------------------------------------------
-- Base cases with `nE = 0`: no edge exists, so `Dep` is vacuous.

NoSelfDep-hEmpty : NoSelfDep hEmpty
NoSelfDep-hEmpty {()}

NoSelfDep-hVar : ∀ x → NoSelfDep (hVar x)
NoSelfDep-hVar x {()}

NoSelfDep-hSwap : ∀ A B → NoSelfDep (hSwap A B)
NoSelfDep-hSwap A B {()}

--------------------------------------------------------------------------------
-- `hGen f`: the unique edge `e = zero` has
--   `ein  e = map (_↑ˡ nB) (range nA)`   (all `_↑ˡ_` form),
--   `eout e = map (nA ↑ʳ_) (range nB)`   (all `_↑ʳ_` form).
-- A shared vertex `v` would be both `iA ↑ˡ nB` and `nA ↑ʳ jB`, impossible.

NoSelfDep-hGen : ∀ {A B} (f : mor A B) → NoSelfDep (hGen f)
NoSelfDep-hGen {A} {B} f {zero} (v , v∈out , v∈in)
  with ∈-map⁻ (length (flatten A) ↑ʳ_) v∈out
     | ∈-map⁻ (_↑ˡ length (flatten B)) v∈in
... | jB , _ , v≡raise | iA , _ , v≡inject =
  ↑ˡ≢↑ʳ iA jB (trans (sym v≡inject) v≡raise)

--------------------------------------------------------------------------------
-- Tensor: a composite edge `e : Fin (G.nE + K.nE)` is either a G-edge
-- (routed via `injL = _↑ˡ K.nV`, injective) or a K-edge (routed via
-- `injR = G.nV ↑ʳ_`, injective).  Either way `ein`/`eout` of the composite
-- edge are `map h (sub.ein/eout)`, so `map-inj-disjoint` plus the sub-graph
-- IH closes it.

NoSelfDep-hTensor
  : ∀ G K → NoSelfDep G → NoSelfDep K → NoSelfDep (hTensor G K)
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
      map-inj-disjoint injL injL-inj
        {G.eout eG} {G.ein eG}
        (λ uo ui → G-nd (_ , uo , ui))
        (subst (v ∈_) (eout-c-inj₁-red eG) vo)
        (subst (v ∈_) (ein-c-inj₁-red  eG) vi)
    dispatch (inj₂ eK) vo vi =
      map-inj-disjoint injR injR-inj
        {K.eout eK} {K.ein eK}
        (λ uo ui → K-nd (_ , uo , ui))
        (subst (v ∈_) (eout-c-inj₂-red eK) vo)
        (subst (v ∈_) (ein-c-inj₂-red  eK) vi)

--------------------------------------------------------------------------------
-- `hId A`: structural on `A`.

NoSelfDep-hId : ∀ A → NoSelfDep (hId A)
NoSelfDep-hId unit       {e} = NoSelfDep-hEmpty {e}
NoSelfDep-hId (Var x)    {e} = NoSelfDep-hVar x {e}
NoSelfDep-hId (A ⊗₀ B)   {e} =
  NoSelfDep-hTensor (hId A) (hId B) (NoSelfDep-hId A) (NoSelfDep-hId B) {e}

--------------------------------------------------------------------------------
-- Pruned composition.  Same structure as tensor, but the K-side routing
-- map is the pruned `remapP`.  `remapP` is injective whenever
-- `K.dom` and `G.cod` are `Unique` (the side conditions of
-- `Prune.remap-injective`); for `G = ⟪h⟫`, `K = ⟪g⟫` these come from
-- `HomTermInvariant.⟪_⟫-dom-unique` / `⟪_⟫-cod-unique`.
--
-- We parameterise on the proof `remapP-inj` so the geometric argument is
-- shared, then instantiate it at `⟪h⟫`/`⟪g⟫` in the `_∘_` case below.

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
      map-inj-disjoint injL (λ {x} {y} eq → ↑ˡ-injective (count-non K.dom) x y eq)
        {G.eout eG} {G.ein eG}
        (λ uo ui → G-nd (_ , uo , ui))
        (subst (v ∈_) (eout-c-inj₁-red eG) vo)
        (subst (v ∈_) (ein-c-inj₁-red  eG) vi)
    dispatch (inj₂ eK) vo vi =
      map-inj-disjoint remapP remapP-inj
        {K.eout eK} {K.ein eK}
        (λ uo ui → K-nd (_ , uo , ui))
        (subst (v ∈_) (eout-c-inj₂-red eK) vo)
        (subst (v ∈_) (ein-c-inj₂-red  eK) vi)

--------------------------------------------------------------------------------
-- The `remapP`-injectivity instance for a pruned composition of two
-- *translated* hypergraphs `⟪h⟫`, `⟪g⟫`.  Mirrors the recipe in
-- `HomTermInvariant.⟪ g ∘ h ⟫-cod-unique`.

module _ {A B C} (g : HomTerm B C) (h : HomTerm A B) where
  private
    bdy : codL ⟪ h ⟫ ≡ domL ⟪ g ⟫
    bdy = trans (⟪⟫-codL h) (sym (⟪⟫-domL g))

    module hCP = hComposeP-impl ⟪ h ⟫ ⟪ g ⟫ bdy

    cast-inj : ∀ {i j} → cast hCP.dom-cod-len i ≡ cast hCP.dom-cod-len j → i ≡ j
    cast-inj {i} {j} eq = toℕ-injective
      (trans (sym (toℕ-cast hCP.dom-cod-len i))
             (trans (cong toℕ eq) (toℕ-cast hCP.dom-cod-len j)))

    lookup-cod-inj : ∀ {i j} → hCP.lookup-cod i ≡ hCP.lookup-cod j → i ≡ j
    lookup-cod-inj {i} {j} eq =
      cast-inj (lookup-injective-unique (⟪_⟫-cod-unique h) _ _ eq)

  ∘-remapP-inj : ∀ {i j} → hCP.remapP i ≡ hCP.remapP j → i ≡ j
  ∘-remapP-inj eq =
    remap-injective _ _ (⟪_⟫-dom-unique g) lookup-cod-inj eq

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
