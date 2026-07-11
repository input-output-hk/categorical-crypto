{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- (LemC) The natural `Fin` edge-order of a TRANSLATED hypergraph is a
-- linear extension of its immediate dependency relation `Dep`.
--
-- Goal: `fin-order-NoInv-⟪⟫ : ∀ {A B} (f : HomTerm A B) → PH.NoInv (range
-- nE)`, where `PH.NoInv (range nE) = AllPairs (λ a b → ¬ Dep ⟪f⟫ b a) (range
-- nE)` — "for edges `a` before `b` in `range`, `b` does not produce a wire
-- that `a` consumes" (no earlier-consumes-later inversion).
--
-- ## Route
--
-- A DIRECT structural induction on `f`.  This avoids the
-- `AllFire-natural-range ⇒ NoInv` bridge, which lives in an
-- `APROPSignatureDec`-parameterised module (decidable equality) and so is
-- NOT reachable from this bare-`APROPSignature` module.  The translation's
-- smart constructors lay edges in a topologically-sound order, so `NoInv`
-- follows constructor-by-constructor:
--
--   * Zero-edge cases (`id`, `λ`, `ρ`, `α`, `σ`): `range 0 = []`.
--   * Single-edge `Agen g`: singleton has no pairs.
--   * Tensor `f ⊗₁ g`: `hTensor` lays G-edges (`injL = _↑ˡ_`) before K-edges
--     (`injR = _↑ʳ_`); the two vertex images are DISJOINT (`disj-L-R`), so no
--     cross-block dependency exists; within each block dependency reflects
--     through the injective vertex embedding to the sub-hypergraph (IH).
--   * Composition `g ∘ f`: `hComposeP` lays G-edges (`injL`) before K-edges
--     (pruning `remapP`).  A K-edge MAY depend on a G-edge (forward flow), so
--     the only things to rule out are the within-block reflections and the
--     REVERSE flow.  The G-block reflection is like the tensor's; the K-block
--     reflection and cross-block acyclicity rest on the LINEARITY invariant
--     (`Linear`), threaded in as `Linear G`/`Linear K`:
--       - `compose-KK-reflect` reuses `LinearHComposeP.remapP-injective`;
--       - `compose-cross-acyclic`: a `remapP`-image of a K-output that is also
--         an `injL`-image forces the K-output into `K.dom`, occurring in BOTH
--         summands of `producedList K` (`count ≥ 2`), contradicting `Linear K`.
--     `Linearity` and `LinearHComposeP`/`DecodeAttemptLinearP` are all
--     bare-`sig` modules, so the whole `∘` case is reachable here.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; range; hGen; hId; hTensor; hSwap
        ; module hTensor-impl)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)
import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open Inv using (inject+-inj; raise-inj; disj-L-R; range-++)

-- Linearity layer: the `Linear` invariant, `count`, the pruned-translation
-- linearity witness, and the pruning machinery for the `∘` case.
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (Linear; count; count-++; producedList)
import Categories.APROP.Hypergraph.Soundness.Discharge.LinearHComposeP sig as LHC
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (⟪⟫-LinearP)
open import Categories.APROP.Hypergraph.Util.Prune
  using (count-non; classify; classify-inj₁-∈)
open import Data.Fin.Properties using (_≟_; splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional.Properties
  using (∈-concat⁺′; ∈-tabulate⁺)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Nat using () renaming (_<_ to _ℕ<_)
import Data.Nat.Properties as Nat

import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig
  as IW

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

-- Membership ⇒ positive `count`: shared `CountCombinatorics` leaf.
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.CountCombinatorics sig
  using (∈→count-pos)

-- The `_↑ˡ_` and `_↑ʳ_` images of `Fin (m + k)` are disjoint (shared from Invariant).
↑ˡ-↑ʳ-disjoint : ∀ {m k} (i : Fin m) (j : Fin k) → i ↑ˡ k ≡ m ↑ʳ j → ⊥
↑ˡ-↑ʳ-disjoint = Inv.↑ˡ≢↑ʳ

--------------------------------------------------------------------------------
-- ## The `NoInv` predicate as a bare `AllPairs`.
--
-- Convenient per-`H` abbreviations; `NoInvH H` coincides definitionally
-- with `IW.PerHG.NoInv H` (the predicates are irreflexivity-free).

-- `BelowH H a b := ¬ Dep H b a`: `b` (later) does not produce a wire that
-- `a` (earlier) consumes.
BelowH : (H : Hypergraph FlatGen)
       → Fin (Hypergraph.nE H) → Fin (Hypergraph.nE H) → Set
BelowH H a b = ¬ Dep H b a

-- `NoInvH H xs` = `AllPairs (BelowH H) xs`.
NoInvH : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nE H)) → Set
NoInvH H = AllPairs (BelowH H)

--------------------------------------------------------------------------------
-- ## Tensor case.

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
  tensor-GG-reflect : ∀ {ea eb : Fin G.nE} → Dep H (injLE eb) (injLE ea) → Dep G eb ea
  tensor-GG-reflect {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (T.eout-c-inj₁-red eb) v∈out
       | subst (v ∈_) (T.ein-c-inj₁-red ea) v∈in
  ... | v∈out' | v∈in' with ∈-map⁻ T.injL v∈out' | ∈-map⁻ T.injL v∈in'
  ... | wb , wb∈ , v≡wb | wa , wa∈ , v≡wa =
        wb
      , wb∈
      , subst (_∈ G.ein ea)
              (inject+-inj K.nV (trans (sym v≡wa) v≡wb))
              wa∈

  -- Symmetric: a dependency between two K-block edges reflects to K.
  tensor-KK-reflect : ∀ {ea eb : Fin K.nE} → Dep H (injRE eb) (injRE ea) → Dep K eb ea
  tensor-KK-reflect {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (T.eout-c-inj₂-red eb) v∈out
       | subst (v ∈_) (T.ein-c-inj₂-red ea) v∈in
  ... | v∈out' | v∈in' with ∈-map⁻ T.injR v∈out' | ∈-map⁻ T.injR v∈in'
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
-- ## Composition case.  `hComposeP G K bdy` lays G-edges (`injL = _↑ˡ_`)
-- before K-edges (pruning `remapP`).  `Linear G`/`Linear K` are threaded in
-- as parameters for the K-block reflection and cross-block acyclicity; the
-- call site supplies `⟪⟫-LinearP`.

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

  -- G-block dependency reflects to G (like `tensor-GG-reflect`; no Linearity).
  compose-GG-reflect : ∀ {ea eb : Fin G.nE}
                     → Dep Hc (injLEc eb) (injLEc ea) → Dep G eb ea
  compose-GG-reflect {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (C.eout-c-inj₁-red eb) v∈out
       | subst (v ∈_) (C.ein-c-inj₁-red ea) v∈in
  ... | v∈out' | v∈in' with ∈-map⁻ C.injL v∈out' | ∈-map⁻ C.injL v∈in'
  ... | wb , wb∈ , v≡wb | wa , wa∈ , v≡wa =
        wb
      , wb∈
      , subst (_∈ G.ein ea)
              (inject+-inj _ (trans (sym v≡wa) v≡wb))
              wa∈

  -- K-block dependency reflects to K (like `tensor-KK-reflect`, with `injR`
  -- replaced by `remapP` and `raise-inj` by `remapP`'s injectivity on
  -- edge-port vertices = `LinearHComposeP.remapP-injective`).
  remapP-inj : ∀ {v v'} → C.remapP v ≡ C.remapP v' → v ≡ v'
  remapP-inj = LHC.remapP-injective G K bdy lin-G lin-K

  compose-KK-reflect : ∀ {ea eb : Fin K.nE}
                     → Dep Hc (injREc eb) (injREc ea) → Dep K eb ea
  compose-KK-reflect {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (C.eout-c-inj₂-red eb) v∈out
       | subst (v ∈_) (C.ein-c-inj₂-red ea) v∈in
  ... | v∈out' | v∈in' with ∈-map⁻ C.remapP v∈out' | ∈-map⁻ C.remapP v∈in'
  ... | wb , wb∈ , v≡wb | wa , wa∈ , v≡wa =
        wb
      , wb∈
      , subst (_∈ K.ein ea)
              (remapP-inj (trans (sym v≡wa) v≡wb))
              wa∈

  -- The cross-block acyclicity — no K-block edge produces a wire an earlier
  -- G-block edge consumes.  A shared vertex `v` would be both a `remapP`-image
  -- of a K-output `k₀ ∈ K.eout eb` and an `injL`-image (`_↑ˡ cn`).  Then
  -- `classify K.dom k₀`: `inj₂` routes to a `G.nV ↑ʳ_` slot, disjoint from
  -- `_↑ˡ cn`; `inj₁` puts `k₀ ∈ K.dom`, so `k₀` occurs in BOTH summands of
  -- `producedList K` (`count ≥ 2`), contradicting `Linear K`'s bound `≤ 1`.
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
            (Nat.+-mono-≤ (∈→count-pos k∈dom) (∈→count-pos k∈eb))

    -- Only `K.dom` members route to the `_↑ˡ cn` (G-side) slots: if
    -- `remapP k ≡ i ↑ˡ cn` then `k ∈ K.dom`.  Case-split `classify K.dom k`:
    -- `inj₁` gives `k ∈ K.dom`; `inj₂ j` reduces `remapP k` to `G.nV ↑ʳ j`,
    -- absurd against `i ↑ˡ cn` by `↑ˡ-↑ʳ-disjoint`.
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
  ... | v∈out' | v∈in' with ∈-map⁻ C.remapP v∈out' | ∈-map⁻ C.injL v∈in'
  ... | k₀ , k₀∈out , v≡rk | i₀ , i₀∈in , v≡injL =
        dom-and-out→absurd k₀ eb
          (remapP-injL→dom k₀ i₀ (trans (sym v≡rk) v≡injL))
          k₀∈out

  ------------------------------------------------------------------------------
  -- Assembly of `NoInvH Hc (range …)`, parallel to the tensor assembly.

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
-- ## The target, in `IW.PerHG.NoInv` form (= `NoInvH ⟪ f ⟫` definitionally).

fin-order-NoInv-⟪⟫
  : ∀ {A B} (f : HomTerm A B)
  → IW.PerHG.NoInv ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫))
fin-order-NoInv-⟪⟫ f = NoInvH-range-⟪⟫ f
