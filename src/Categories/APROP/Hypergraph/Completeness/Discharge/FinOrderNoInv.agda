{-# OPTIONS --safe --without-K #-}

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
--     rest on the FULL LINEARITY invariant of the translation.  They are now
--     also PROVEN, by threading `Linear ⟪f⟫`/`Linear ⟪g⟫` (the pruned-
--     translation linearity witness `⟪⟫-LinearP` from `DecodeAttemptLinearP`)
--     into the composition assembly:
--       - `compose-KK-reflect` reuses `LinearHComposeP.remapP-injective`
--         (injectivity of the pruning map on edge-port vertices; needs
--         `Linear G`, `Linear K`), mirroring `tensor-KK-reflect`;
--       - `compose-cross-acyclic` observes that a `remapP`-image of a K-output
--         that is also an `injL`-image forces the K-output vertex into
--         `K.dom`, so it occurs in BOTH summands of `producedList K`, giving
--         `count ≥ 2`, contradicting the `Linear K` bound `≤ 1`.
--     ALL reachable from a bare `APROPSignature`: both `Linearity` and the
--     spike `LinearHComposeP` / `DecodeAttemptLinearP` are bare-`sig` modules,
--     so NO `APROPSignatureDec` parameterisation is needed.  The whole `∘`
--     case is now constructive.
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

-- Linearity layer (bare `APROPSignature`-parameterised): the `Linear`
-- invariant, `count`, the pruned-translation linearity witness, and the
-- pruning machinery needed to discharge the two composition postulates.
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear; count; count-++; producedList)
import Categories.APROP.Hypergraph.Completeness.Discharge.LinearHComposeP sig as LHC
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (⟪⟫-LinearP)
open import Categories.APROP.Hypergraph.Prune
  using (count-non; classify; classify-inj₁-∈)
open import Data.Fin.Properties using (_≟_; splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional.Properties
  using (∈-concat⁺′; ∈-tabulate⁺)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using () renaming (_<_ to _ℕ<_)
import Data.Nat.Properties as Nat

import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig
  as IW
open import Categories.APROP.Hypergraph.Completeness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.List using (List; []; _∷_; _++_; map; concat; tabulate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
  renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsProp
open import Data.Nat using (ℕ; zero; suc; _+_; s≤s; z≤n; _≤_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- ## Generic count / disjointness helpers (used by the `∘` cross-acyclicity).

-- Membership ⇒ positive `count`.  `count` (from `Linearity`) walks the list
-- testing `v ≟ x`; an occurrence of `v` forces at least one `suc`.
∈→count-pos : ∀ {n} (v : Fin n) (xs : List (Fin n)) → v ∈ xs → 0 ℕ< count v xs
∈→count-pos v (x ∷ xs) (here  refl) with v ≟ x
... | yes _ = s≤s z≤n
... | no  q = ⊥-elim (q refl)
∈→count-pos v (x ∷ xs) (there p) with v ≟ x
... | yes _ = s≤s z≤n
... | no  _ = ∈→count-pos v xs p

-- The `_↑ˡ_` and `_↑ʳ_` images of `Fin (m + k)` are disjoint.
↑ˡ-↑ʳ-disjoint : ∀ {m k} (i : Fin m) (j : Fin k) → i ↑ˡ k ≡ m ↑ʳ j → ⊥
↑ˡ-↑ʳ-disjoint {m} {k} i j eq
  with splitAt-↑ˡ m i k | splitAt-↑ʳ m k j | cong (splitAt m) eq
... | i-red | j-red | split-eq = case-absurd (trans (sym i-red) (trans split-eq j-red))
  where
    case-absurd : ∀ {Y : Set} {x : Fin m} {y : Fin k} → inj₁ x ≡ inj₂ y → Y
    case-absurd ()

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
-- re-consumed inside a block).  That invariant — `Linear` from
-- `Completeness.Linearity` — is reachable from a bare `APROPSignature`, so we
-- thread `Linear G`/`Linear K` in as module parameters and PROVE both facts
-- (no postulates); the call site supplies `⟪⟫-LinearP` for `G = ⟪f⟫`,
-- `K = ⟪g⟫`.

module _ (G K : Hypergraph FlatGen) (bdy : codL G ≡ domL K)
         (lin-G : Linear G) (lin-K : Linear K) where
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

  -- K-block dependency reflects to K.  PROVEN — identical in shape to
  -- `tensor-KK-reflect`, with the K-side vertex injection `injR` replaced by
  -- the pruning map `remapP` and `raise-inj` replaced by `remapP`'s
  -- injectivity ON EDGE-PORT VERTICES.  That injectivity is precisely the
  -- spike's `LinearHComposeP.remapP-injective`, which needs `Linear G` and
  -- `Linear K` (both threaded in as module parameters).
  remapP-inj : ∀ {v v'} → C.remapP v ≡ C.remapP v' → v ≡ v'
  remapP-inj = LHC.remapP-injective G K bdy lin-G lin-K

  compose-KK-reflect : ∀ {ea eb : Fin K.nE}
                     → Dep Hc (injREc eb) (injREc ea) → Dep K eb ea
  compose-KK-reflect {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (C.eout-c-inj₂-red eb) v∈out
       | subst (v ∈_) (C.ein-c-inj₂-red ea) v∈in
  ... | v∈out' | v∈in'
    with ∈-map⁻ C.remapP v∈out' | ∈-map⁻ C.remapP v∈in'
  ... | wb , wb∈ , v≡wb | wa , wa∈ , v≡wa =
        wb
      , wb∈
      , subst (_∈ K.ein ea)
              (remapP-inj (trans (sym v≡wa) v≡wb))
              wa∈

  -- The cross-block acyclicity — no K-block edge produces a wire that an
  -- earlier G-block edge consumes.  PROVEN.  A shared vertex `v` would be both
  -- a `remapP`-image of a K-output `k₀ ∈ K.eout eb` and an `injL`-image
  -- (`_↑ˡ cn`) of a G-input.  Case-split `classify K.dom k₀`:
  --   * `inj₂ j`: `remapP k₀ = G.nV ↑ʳ j`, which can't be an `_↑ˡ cn` image
  --     (`↑ˡ-↑ʳ-disjoint`).
  --   * `inj₁ i`: `k₀ ∈ K.dom`.  But also `k₀ ∈ K.eout eb`, so `k₀` occurs in
  --     BOTH summands of `producedList K = K.dom ++ concat (tabulate K.eout)`,
  --     giving `count k₀ (producedList K) ≥ 2`, contradicting the `Linear K`
  --     bound `≤ 1`.  This is the linearity/acyclicity invariant.
  private
    cn = count-non K.dom

    -- `producedList K` count of an edge-output that is also in `K.dom` is ≥ 2.
    dom-and-out→absurd
      : ∀ (k : Fin K.nV) (eb : Fin K.nE)
      → k ∈ K.dom → k ∈ K.eout eb → ⊥
    dom-and-out→absurd k eb k∈dom k∈out =
      Nat.<-irrefl refl
        (Nat.<-≤-trans 1<prod (proj₂ lin-K k))
      where
        k∈eb : k ∈ concat (tabulate K.eout)
        k∈eb = ∈-concat⁺′ k∈out (∈-tabulate⁺ eb)

        prod-eq : count k (producedList K)
                ≡ count k K.dom + count k (concat (tabulate K.eout))
        prod-eq = count-++ k K.dom (concat (tabulate K.eout))

        1<prod : 1 ℕ< count k (producedList K)
        1<prod =
          subst (1 ℕ<_) (sym prod-eq)
            (Nat.+-mono-≤ (∈→count-pos k K.dom k∈dom)
                          (∈→count-pos k (concat (tabulate K.eout)) k∈eb))

    -- Only `K.dom` members route to the `_↑ˡ cn` (G-side) slots: if
    -- `remapP k ≡ i ↑ˡ cn` then `k ∈ K.dom`.  We case-split `classify K.dom k`
    -- (`rewrite`-ing the hypothesis so `remapP k` reduces along that branch):
    -- the `inj₂` branch routes to a `G.nV ↑ʳ_` slot, disjoint from `_↑ˡ cn`.
    -- Only `K.dom` members route to `_↑ˡ cn` (G-side) slots.  Case-split
    -- `classify K.dom k`: `inj₁` gives `k ∈ K.dom` (`classify-inj₁-∈`).  In the
    -- `inj₂ j` branch the `with`-abstraction reduces `C.remapP k` to its
    -- non-member image, so `hyp` already reads `G.nV ↑ʳ j ≡ i ↑ˡ cn`, which is
    -- absurd by `↑ˡ-↑ʳ-disjoint`.
    remapP-injL→dom
      : ∀ (k : Fin K.nV) (i : Fin G.nV) → C.remapP k ≡ i ↑ˡ cn → k ∈ K.dom
    remapP-injL→dom k i hyp with classify K.dom k in cls
    ... | inj₁ _ = classify-inj₁-∈ cls
    ... | inj₂ j = ⊥-elim (↑ˡ-↑ʳ-disjoint i j (sym hyp))

  compose-cross-acyclic : ∀ {ea : Fin G.nE} {eb : Fin K.nE}
                        → ¬ Dep Hc (injREc eb) (injLEc ea)
  compose-cross-acyclic {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (C.eout-c-inj₂-red eb) v∈out
       | subst (v ∈_) (C.ein-c-inj₁-red ea) v∈in
  ... | v∈out' | v∈in'
    with ∈-map⁻ C.remapP v∈out' | ∈-map⁻ C.injL v∈in'
  ... | k₀ , k₀∈out , v≡rk | i₀ , i₀∈in , v≡injL =
        -- `C.remapP k₀ ≡ i₀ ↑ˡ cn`, so `k₀ ∈ K.dom`; but `k₀ ∈ K.eout eb`,
        -- contradicting `Linear K`.
        dom-and-out→absurd k₀ eb
          (remapP-injL→dom k₀ i₀ (trans (sym v≡rk) v≡injL))
          k₀∈out

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
        (NoInvH-compose F G bdy (⟪⟫-LinearP f) (⟪⟫-LinearP g)
          (range F.nE) (range G.nE)
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
