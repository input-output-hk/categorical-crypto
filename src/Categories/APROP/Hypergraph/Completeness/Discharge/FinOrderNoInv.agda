{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- (LemC) The natural `Fin` edge-order of a TRANSLATED hypergraph is a
-- linear extension of its immediate dependency relation `Dep`.
--
-- Goal:
--
--   fin-order-NoInv-⟪⟫
--     : ∀ {A B} (f : HomTerm A B) → PH.NoInv (range (Hypergraph.nE ⟪ f ⟫))
--
-- where `module PH = IW.PerHG ⟪ f ⟫`, so that `PH.NoInv` is
-- `Combinatorics.LinearExtension.NoInv` instantiated at `(Fin nE, Dep ⟪f⟫)`,
-- i.e.
--
--   PH.NoInv (range nE) = AllPairs (λ a b → ¬ Dep ⟪f⟫ b a) (range nE)
--
-- — "for edges `a` before `b` in `range`, `b` does not produce a wire that
-- `a` consumes" (no earlier-consumes-later inversion).
--
-- ## Route
--
-- A DIRECT structural induction on `f`.  This avoids the
-- `AllFire-natural-range ⇒ NoInv` bridge — `AllFire-natural-range` lives in a
-- module parameterised over `APROPSignatureDec` (it needs decidable equality
-- via `Linearity`), whereas this module is parameterised over a bare
-- `APROPSignature`, so that proven kernel is *not reachable* from here.  The
-- translation's smart constructors lay edges down in a topologically-sound
-- order, so the `NoInv` predicate follows constructor-by-constructor:
--
--   * Zero-edge cases (`id`, `λ⇒/λ⇐`, `ρ⇒/ρ⇐`, `α⇒/α⇐`, `σ`): `nE = 0`, so
--     `range nE = []` and `AllPairs _ [] = []`.
--
--   * Single-edge case (`Agen g`): `nE = 1`, `range 1 = e ∷ []`; `AllPairs`
--     on a singleton is `[] ∷ []` (no pairs).
--
--   * Tensor case (`f ⊗₁ g`):  `hTensor G K` lays the G-edges (vertices via
--     `injL = _↑ˡ_`) before the K-edges (vertices via `injR = _↑ʳ_`).  The
--     two vertex images are DISJOINT (`Invariant.disj-L-R`), so NO
--     cross-block dependency exists in either direction; within each block,
--     dependency reflects through the injective vertex embedding to the
--     sub-hypergraph, where the IH applies.  FULLY CONSTRUCTIVE.
--
--   * Composition case (`g ∘ f`):  `hComposeP G K` lays the G-edges (`= ⟪f⟫`,
--     vertices via `injL`) before the K-edges (`= ⟪g⟫`, vertices via the
--     pruning `remapP`).  The G-block reflection (`compose-GG-reflect`) is
--     PROVEN exactly like the tensor's (it only touches the `injL` block).
--     The remaining two facts — the K-block reflection through `remapP`
--     (`compose-KK-reflect`) and the cross-block acyclicity (`remapP`-images
--     of K-outputs are never consumed by a G-edge, `compose-cross-acyclic`) —
--     rest on the FULL LINEARITY invariant of the translation, available only
--     through `Completeness.Linearity` (an `APROPSignatureDec`-parameterised
--     module).  They are isolated as TWO precisely-scoped `-- TODO:`
--     postulates; see their individual docstrings.  Everything else in the
--     `∘` case is proven.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.FinOrderNoInv
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range; hGen; hId; hTensor; hSwap
        ; module hTensor-impl)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)
import Categories.APROP.Hypergraph.Invariant sig as Inv
open Inv using (inject+-inj; raise-inj; disj-L-R; range-++)

import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig
  as IW
open import Categories.APROP.Hypergraph.Completeness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
  renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsProp
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- ## The `NoInv` predicate as a bare `AllPairs`.
--
-- We work with the bare `AllPairs` form rather than `IW.PerHG.NoInv` so that
-- the proof is independent of the `Dep-irrefl` postulate hidden inside
-- `PerHG` (NoInv itself never uses irreflexivity).  The two coincide
-- definitionally — witnessed by the final `fin-order-NoInv-⟪⟫`, whose body is
-- just `NoInvH-range-⟪⟫` retyped at `IW.PerHG.NoInv`.

-- `BelowH H a b := ¬ Dep H b a` is the per-edge "no inversion" relation:
-- `b` (later) does not produce a wire that `a` (earlier) consumes.
BelowH : (H : Hypergraph FlatGen)
       → Fin (Hypergraph.nE H) → Fin (Hypergraph.nE H) → Set
BelowH H a b = ¬ Dep H b a

-- `NoInvH H xs` = `AllPairs (BelowH H) xs`.
NoInvH : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nE H)) → Set
NoInvH H = AllPairs (BelowH H)

--------------------------------------------------------------------------------
-- ## Generic membership bridge: a shared vertex witnessing `Dep`.
--
-- `Dep H e e'` is `∃ v. v ∈ eout H e × v ∈ ein H e'`.  We repeatedly need to
-- read off such a witness after rewriting `eout`/`ein` to a concrete `map`.

--------------------------------------------------------------------------------
-- ## Tensor case (FULLY CONSTRUCTIVE).

module _ (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module T = hTensor-impl G K

  H = hTensor G K

  -- Edge embeddings into the tensor's edge index `Fin (G.nE + K.nE)`.
  injLE : Fin G.nE → Fin (G.nE + K.nE)
  injLE eG = eG ↑ˡ K.nE

  injRE : Fin K.nE → Fin (G.nE + K.nE)
  injRE eK = G.nE ↑ʳ eK

  ------------------------------------------------------------------------------
  -- A dependency between two G-block edges reflects to a dependency in G.
  -- Uses `eout/ein` reduction (`T.eout-c-inj₁-red`, `T.ein-c-inj₁-red`) and
  -- injectivity of the vertex injection `injL = _↑ˡ_`.
  tensor-GG-reflect : ∀ {ea eb : Fin G.nE}
                    → Dep H (injLE eb) (injLE ea)
                    → Dep G eb ea
  tensor-GG-reflect {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (T.eout-c-inj₁-red eb) v∈out
       | subst (v ∈_) (T.ein-c-inj₁-red ea) v∈in
  ... | v∈out' | v∈in'
    with ∈-map⁻ T.injL v∈out' | ∈-map⁻ T.injL v∈in'
  ... | wb , wb∈ , v≡wb | wa , wa∈ , v≡wa =
        wb
      , wb∈
      , subst (_∈ G.ein ea)
              (inject+-inj K.nV (trans (sym v≡wa) v≡wb))
              wa∈

  -- Symmetric: a dependency between two K-block edges reflects to K.
  tensor-KK-reflect : ∀ {ea eb : Fin K.nE}
                    → Dep H (injRE eb) (injRE ea)
                    → Dep K eb ea
  tensor-KK-reflect {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (T.eout-c-inj₂-red eb) v∈out
       | subst (v ∈_) (T.ein-c-inj₂-red ea) v∈in
  ... | v∈out' | v∈in'
    with ∈-map⁻ T.injR v∈out' | ∈-map⁻ T.injR v∈in'
  ... | wb , wb∈ , v≡wb | wa , wa∈ , v≡wa =
        wb
      , wb∈
      , subst (_∈ K.ein ea)
              (raise-inj G.nV (trans (sym v≡wa) v≡wb))
              wa∈

  -- No K-block edge produces a wire consumed by a G-block edge: the K-output
  -- vertices live in `map injR …` and the G-input vertices in `map injL …`,
  -- which are disjoint (`disj-L-R`).
  tensor-cross-acyclic : ∀ {ea : Fin G.nE} {eb : Fin K.nE}
                       → ¬ Dep H (injRE eb) (injLE ea)
  tensor-cross-acyclic {ea} {eb} (v , v∈out , v∈in) =
    disj-L-R (G.ein ea) (K.eout eb)
             ( subst (v ∈_) (T.ein-c-inj₁-red ea) v∈in
             , subst (v ∈_) (T.eout-c-inj₂-red eb) v∈out )

  ------------------------------------------------------------------------------
  -- Assemble `NoInvH H (range (G.nE + K.nE))` from `NoInvH G/K`.

  -- `BelowH G` ⇒ `BelowH H` along `injLE` (G-block).
  Below-injLE : ∀ {a b : Fin G.nE} → BelowH G a b → BelowH H (injLE a) (injLE b)
  Below-injLE noG dep = noG (tensor-GG-reflect dep)

  -- `BelowH K` ⇒ `BelowH H` along `injRE` (K-block).
  Below-injRE : ∀ {a b : Fin K.nE} → BelowH K a b → BelowH H (injRE a) (injRE b)
  Below-injRE noK dep = noK (tensor-KK-reflect dep)

  -- Every G-block edge is `BelowH H` every K-block edge (the cross `All`).
  cross-all-row : ∀ (ea : Fin G.nE) (ks : List (Fin K.nE))
                → All (BelowH H (injLE ea)) (map injRE ks)
  cross-all-row ea []        = []
  cross-all-row ea (eb ∷ ks) = tensor-cross-acyclic ∷ cross-all-row ea ks

  cross-all : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
            → All (λ a → All (BelowH H a) (map injRE ks)) (map injLE gs)
  cross-all []        ks = []
  cross-all (ea ∷ gs) ks = cross-all-row ea ks ∷ cross-all gs ks

  -- The two `AllPairs.Properties.map⁺` inputs: relabel a sub-`AllPairs`
  -- through `injLE`/`injRE` using the `Below-inj*` transports.
  mapAP-G : ∀ {gs} → AllPairs (BelowH G) gs
          → AllPairs (λ a b → BelowH H (injLE a) (injLE b)) gs
  mapAP-G []          = []
  mapAP-G (px ∷ rest) = All-map Below-injLE px ∷ mapAP-G rest

  mapAP-K : ∀ {ks} → AllPairs (BelowH K) ks
          → AllPairs (λ a b → BelowH H (injRE a) (injRE b)) ks
  mapAP-K []          = []
  mapAP-K (px ∷ rest) = All-map Below-injRE px ∷ mapAP-K rest

  NoInvH-tensor : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                → NoInvH G gs → NoInvH K ks
                → NoInvH H (map injLE gs ++ map injRE ks)
  NoInvH-tensor gs ks noG noK =
    AllPairsProp.++⁺
      (AllPairsProp.map⁺ (mapAP-G noG))
      (AllPairsProp.map⁺ (mapAP-K noK))
      (cross-all gs ks)

--------------------------------------------------------------------------------
-- ## Composition case.
--
-- `hComposeP G K bdy` lays G-edges (vertices via `injL = _↑ˡ_`) before
-- K-edges (vertices via the pruning map `remapP`).  Unlike the tensor, a
-- K-edge MAY legitimately depend on a G-edge (data flows from `f` to `g`),
-- but the *order* keeps every G-edge before every K-edge, so the only thing
-- to rule out is the REVERSE flow plus the within-block reflections.
--
-- The G-block reflection is proven directly.  The remaining two facts (the
-- K-block reflection through `remapP`, and the cross-block acyclicity) hinge
-- on the full LINEARITY invariant of the translation (each wire
-- produced/consumed at most once; output-boundary vertices are never
-- re-consumed inside a block).  That invariant is proven only in
-- `Completeness.Linearity`, an `APROPSignatureDec`-parameterised module
-- unreachable from here.  We isolate the irreducible content as two
-- precisely-scoped postulates.

module _ (G K : Hypergraph FlatGen) (bdy : codL G ≡ domL K) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = hComposeP-impl G K bdy

  Hc = hComposeP G K bdy

  injLEc : Fin G.nE → Fin (G.nE + K.nE)
  injLEc eG = eG ↑ˡ K.nE

  injREc : Fin K.nE → Fin (G.nE + K.nE)
  injREc eK = G.nE ↑ʳ eK

  -- G-block dependency reflects to G.  FULLY CONSTRUCTIVE — identical in
  -- shape to `tensor-GG-reflect` (G-side vertices via `injL = _↑ˡ_`, the
  -- `C.ein-c-inj₁-red`/`C.eout-c-inj₁-red` reductions, `inject+-inj` for the
  -- vertex injection).  No Linearity content is required.
  compose-GG-reflect : ∀ {ea eb : Fin G.nE}
                     → Dep Hc (injLEc eb) (injLEc ea) → Dep G eb ea
  compose-GG-reflect {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (C.eout-c-inj₁-red eb) v∈out
       | subst (v ∈_) (C.ein-c-inj₁-red ea) v∈in
  ... | v∈out' | v∈in'
    with ∈-map⁻ C.injL v∈out' | ∈-map⁻ C.injL v∈in'
  ... | wb , wb∈ , v≡wb | wa , wa∈ , v≡wa =
        wb
      , wb∈
      , subst (_∈ G.ein ea)
              (inject+-inj _ (trans (sym v≡wa) v≡wb))
              wa∈

  -- TODO: K-block dependency reflects to K.  Needs injectivity of the pruning
  -- map `remapP : Fin K.nV → Fin (G.nV + count-non K.dom)` ON THE VERTICES
  -- THAT ACTUALLY OCCUR in K's edge ports.  `remapP` is NOT globally
  -- injective (all `K.dom` members collapse onto their `G.cod` images), so
  -- this requires the LINEARITY fact that distinct edge-port vertices of `K`
  -- stay distinct under `remapP` (equivalently: at most the boundary
  -- collapses, and boundary vertices are not interior ports).  Proven inside
  -- `Completeness.Linearity` as `hCompose-Linear-utils.remap-injective`
  -- (requires `Linear G`, `Linear K`), which is reachable only from an
  -- `APROPSignatureDec` module.
  postulate
    compose-KK-reflect : ∀ {ea eb : Fin K.nE}
                       → Dep Hc (injREc eb) (injREc ea) → Dep K eb ea

  -- TODO: the cross-block acyclicity — no K-block edge produces a wire that an
  -- earlier G-block edge consumes.  This is the substantive ACYCLICITY fact:
  -- `eout (K-edge) = map remapP (K.eout)` and `ein (G-edge) = map injL
  -- (G.ein)`; a shared vertex would force a `remapP`-image of a K-output to
  -- equal an `injL`-image of a G-input.  Since `remapP` hits the `injL` block
  -- only on `K.dom` members (mapped to their `G.cod` boundary images), this
  -- reduces to "a `G.cod` (output-boundary) vertex is never a member of any
  -- `G.ein` (an edge input)" — exactly the linearity/acyclicity invariant of
  -- the FromAPROP translation.  Proven (in the AllFire form) constructively
  -- in `Discharge/Sub/AllFireNatural.agda`, but only over `APROPSignatureDec`.
  postulate
    compose-cross-acyclic : ∀ {ea : Fin G.nE} {eb : Fin K.nE}
                          → ¬ Dep Hc (injREc eb) (injLEc ea)

  ------------------------------------------------------------------------------
  -- Assembly of `NoInvH Hc (range (G.nE + K.nE))` from the three facts above
  -- plus the sub-NoInvs — entirely PARALLEL to the tensor assembly.

  Below-injLEc : ∀ {a b : Fin G.nE} → BelowH G a b → BelowH Hc (injLEc a) (injLEc b)
  Below-injLEc noG dep = noG (compose-GG-reflect dep)

  Below-injREc : ∀ {a b : Fin K.nE} → BelowH K a b → BelowH Hc (injREc a) (injREc b)
  Below-injREc noK dep = noK (compose-KK-reflect dep)

  cross-all-row-c : ∀ (ea : Fin G.nE) (ks : List (Fin K.nE))
                  → All (BelowH Hc (injLEc ea)) (map injREc ks)
  cross-all-row-c ea []        = []
  cross-all-row-c ea (eb ∷ ks) = compose-cross-acyclic ∷ cross-all-row-c ea ks

  cross-all-c : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
              → All (λ a → All (BelowH Hc a) (map injREc ks)) (map injLEc gs)
  cross-all-c []        ks = []
  cross-all-c (ea ∷ gs) ks = cross-all-row-c ea ks ∷ cross-all-c gs ks

  mapAP-G-c : ∀ {gs} → AllPairs (BelowH G) gs
            → AllPairs (λ a b → BelowH Hc (injLEc a) (injLEc b)) gs
  mapAP-G-c []          = []
  mapAP-G-c (px ∷ rest) = All-map Below-injLEc px ∷ mapAP-G-c rest

  mapAP-K-c : ∀ {ks} → AllPairs (BelowH K) ks
            → AllPairs (λ a b → BelowH Hc (injREc a) (injREc b)) ks
  mapAP-K-c []          = []
  mapAP-K-c (px ∷ rest) = All-map Below-injREc px ∷ mapAP-K-c rest

  NoInvH-compose : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                 → NoInvH G gs → NoInvH K ks
                 → NoInvH Hc (map injLEc gs ++ map injREc ks)
  NoInvH-compose gs ks noG noK =
    AllPairsProp.++⁺
      (AllPairsProp.map⁺ (mapAP-G-c noG))
      (AllPairsProp.map⁺ (mapAP-K-c noK))
      (cross-all-c gs ks)

--------------------------------------------------------------------------------
-- ## `hId A` has no inversions.
--
-- `nE (hId A)` is not literally `0` for an abstract `A` (it is
-- `nE (hId A₁) + nE (hId A₂)` for a tensor), so we recurse: the base cases
-- (`hEmpty`/`hVar`) are literally `nE = 0` ⇒ `range 0 = []`, and the
-- `A ⊗₀ B` case is `hTensor (hId A) (hId B)` handled by the tensor assembly.

NoInvH-hId : ∀ A → NoInvH (hId A) (range (Hypergraph.nE (hId A)))
NoInvH-hId unit      = []
NoInvH-hId (Var x)   = []
NoInvH-hId (A ⊗₀ B)  =
  subst (NoInvH (hTensor (hId A) (hId B)))
        (sym (range-++ (Hypergraph.nE (hId A)) (Hypergraph.nE (hId B))))
        (NoInvH-tensor (hId A) (hId B)
          (range (Hypergraph.nE (hId A)))
          (range (Hypergraph.nE (hId B)))
          (NoInvH-hId A) (NoInvH-hId B))

--------------------------------------------------------------------------------
-- ## The structural induction.
--
-- For every `f`, `NoInvH ⟪ f ⟫ (range (nE ⟪ f ⟫))`.

NoInvH-range-⟪⟫ : ∀ {A B} (f : HomTerm A B)
                → NoInvH ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫))

-- Zero-edge `hId`-shaped cases, via `NoInvH-hId`.
NoInvH-range-⟪⟫ (id {A})       = NoInvH-hId A
NoInvH-range-⟪⟫ (λ⇒ {A})       = NoInvH-hId A
NoInvH-range-⟪⟫ (λ⇐ {A})       = NoInvH-hId A
NoInvH-range-⟪⟫ (ρ⇒ {A})       = NoInvH-hId (A ⊗₀ unit)
NoInvH-range-⟪⟫ (ρ⇐ {A})       = NoInvH-hId (A ⊗₀ unit)
NoInvH-range-⟪⟫ (α⇒ {A}{B}{C}) = NoInvH-hId ((A ⊗₀ B) ⊗₀ C)
NoInvH-range-⟪⟫ (α⇐ {A}{B}{C}) = NoInvH-hId ((A ⊗₀ B) ⊗₀ C)

-- `σ`: `⟪ σ ⟫ = hSwap A B`, which has `nE = 0` literally ⇒ `range 0 = []`.
NoInvH-range-⟪⟫ (σ {A}{B})     = []

-- Single edge: `nE = 1`, `range 1 = zero ∷ []`; the singleton has no pairs.
NoInvH-range-⟪⟫ (Agen g)       = [] ∷ []

-- Tensor: split `range (G.nE + K.nE)` via `range-++` and reuse the IHs.
NoInvH-range-⟪⟫ (f ⊗₁ g) =
  subst (NoInvH (hTensor F G))
        (sym (range-++ F.nE G.nE))
        (NoInvH-tensor F G (range F.nE) (range G.nE)
          (NoInvH-range-⟪⟫ f) (NoInvH-range-⟪⟫ g))
  where
    F = ⟪ f ⟫
    G = ⟪ g ⟫
    module F = Hypergraph F
    module G = Hypergraph G

-- Composition: `⟪ g ∘ f ⟫ = hComposeP ⟪ f ⟫ ⟪ g ⟫ bdy`.  Split and reuse.
NoInvH-range-⟪⟫ (g ∘ f) =
  subst (NoInvH (hComposeP F G bdy))
        (sym (range-++ F.nE G.nE))
        (NoInvH-compose F G bdy (range F.nE) (range G.nE)
          (NoInvH-range-⟪⟫ f) (NoInvH-range-⟪⟫ g))
  where
    F = ⟪ f ⟫
    G = ⟪ g ⟫
    module F = Hypergraph F
    module G = Hypergraph G
    bdy : codL F ≡ domL G
    bdy = trans (⟪⟫-codL f) (sym (⟪⟫-domL g))

--------------------------------------------------------------------------------
-- ## The target, in `IW.PerHG.NoInv` form.
--
-- `IW.PerHG.NoInv = LinExt.NoInv = AllPairs (λ a b → ¬ Dep ⟪f⟫ b a)`, which
-- is `NoInvH ⟪ f ⟫` definitionally; so the structural result above already
-- has the requested type.

fin-order-NoInv-⟪⟫
  : ∀ {A B} (f : HomTerm A B)
  → IW.PerHG.NoInv ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫))
fin-order-NoInv-⟪⟫ f = NoInvH-range-⟪⟫ f
