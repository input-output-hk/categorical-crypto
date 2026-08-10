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
-- Second goal, on the DIAGONAL that `AllPairs` never reaches:
-- `dep-irrefl-⟪⟫ : ∀ {A B} (f : HomTerm A B) {e} → ¬ Dep ⟪f⟫ e e` — no
-- translated edge's in- and out-vertices share a vertex.  It is proven here
-- because it needs exactly the same per-block reflections at `ea ≡ eb`, and
-- is refuted by the same kind of counterexample (below) from the run-level
-- facts alone.
--
-- ## Route
--
-- A DIRECT structural induction on `f`.  This is FORCED, not a convenience:
-- `NoInv (range nE)` is a property of the TRANSLATION, not of the decoder's
-- run, and it does NOT follow from the two order-free facts the Stack layer
-- tracks for an arbitrary hypergraph — `Linear H` (`Linearity`) and the
-- decoder's totality witness `IW.PerHG.Valid (range H.nE)`, i.e.
-- `process-all-edges H H.dom ↭ H.cod` (what
-- `DecodeAttemptLinearP.decode-attempt-LinearP` supplies).  Counterexample:
-- `nV = nE = 2`, `dom = cod = []`, `ein/eout` a 2-cycle (`e₀ : v₀ ↦ v₁`,
-- `e₁ : v₁ ↦ v₀`).  It is `Linear` (each vertex produced once and consumed
-- once) and `Valid` — BOTH edges SKIP, since neither `ein` is ever on the
-- stack, so the final stack is `dom = []`, which is `↭ cod = []` — yet
-- `e₁ ≺ e₀` while `e₀` precedes `e₁` in `range 2`: an inversion.  Validity is
-- blind to skipped edges, so "every edge fires in the natural order" is a
-- strictly stronger and likewise `⟪·⟫`-specific claim; routing `NoInv`
-- through it (`Reservoir≤1` then supplies the contradiction in one step)
-- would still need every per-constructor argument below, plus the run
-- threading on top.  Likewise for the diagonal: the self-loop `nV = nE = 1`,
-- `ein = eout = v₀ ∷ []`, `dom = cod = []` is `Linear` and `Valid` (the edge
-- SKIPS) yet has `Dep H e e`.
--
-- The translation's smart constructors lay edges in a topologically-sound
-- order, so both facts follow constructor-by-constructor:
--
--   * `hId`-shaped cases (`id`, `λ`, `ρ`, `α`): `nE (hId A)` is not literally
--     `0` for an abstract `A`, so `NoInvH-hId`/`NoSelfDep-hId` recurse on `A`
--     (`hEmpty`/`hVar` have `nE = 0`; `A ⊗₀ B` is the tensor case).
--   * `σ`: `nE (hSwap A B) = 0` literally ⇒ `range 0 = []`.
--   * Single-edge `Agen g`: `range 1`'s singleton has no pairs; on the
--     diagonal, `ein`/`eout` are disjoint `_↑ˡ_`/`_↑ʳ_` images.
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
  using (FlatGen; range; flatten; hEmpty; hVar; hGen; hId; hSwap; hTensor
        ; module hTensor-impl)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep; Dep-reflect)
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
  using (count-non; classify; classify-view; ClassifyV; is-mem; is-non)
open import Data.List.Membership.Propositional.Properties
  using (∈-concat⁺′; ∈-tabulate⁺)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using () renaming (_<_ to _ℕ<_)
import Data.Nat.Properties as Nat

import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig
  as IW

open import Data.Fin using (Fin; zero; _↑ˡ_; _↑ʳ_; splitAt; join)
open import Data.Fin.Properties using (join-splitAt)
open import Data.List using (List; []; _∷_; _++_; length; map; concat; tabulate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
  renaming (map to All-map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsProp
open import Data.Nat using (_+_; _≤_)
open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

--------------------------------------------------------------------------------
-- ## Generic count / disjointness helpers (used by the `∘` cross-acyclicity).

-- Membership ⇒ positive `count`: shared `CountCombinatorics` leaf.
open import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics sig
  using (∈→count-pos)

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

-- The DIAGONAL of `BelowH`: `NoSelfDep H = ∀ {e} → BelowH H e e`, i.e. no
-- edge produces a wire it also consumes.  `AllPairs` never pairs an element
-- with itself, so this is genuinely extra content, not a consequence of
-- `NoInvH H (range nE)` — but it is refuted by the very same per-block
-- reflections (`EdgeDependency.Dep-reflect` at `ea ≡ eb`), so it rides along
-- on this induction rather than repeating it in a second module.
NoSelfDep : Hypergraph FlatGen → Set
NoSelfDep H = ∀ {e} → ¬ Dep H e e

--------------------------------------------------------------------------------
-- ## `NoSelfDep` base cases.

-- `nE = 0`: no edge exists, so `Dep` is vacuous.
NoSelfDep-hEmpty : NoSelfDep hEmpty
NoSelfDep-hEmpty {()}

NoSelfDep-hVar : ∀ x → NoSelfDep (hVar x)
NoSelfDep-hVar x {()}

NoSelfDep-hSwap : ∀ A B → NoSelfDep (hSwap A B)
NoSelfDep-hSwap A B {()}

-- `hGen f`: the unique edge has `ein` of `_↑ˡ_` form and `eout` of `_↑ʳ_`
-- form, disjoint by `Inv.↑ˡ≢↑ʳ`.
NoSelfDep-hGen : ∀ {A B} (f : mor A B) → NoSelfDep (hGen f)
NoSelfDep-hGen {A} {B} f {zero} (v , v∈out , v∈in)
  with ∈-map⁻ (length (flatten A) ↑ʳ_) v∈out
     | ∈-map⁻ (_↑ˡ length (flatten B)) v∈in
... | jB , _ , v≡raise | iA , _ , v≡inject =
  Inv.↑ˡ≢↑ʳ iA jB (trans (sym v≡inject) v≡raise)

--------------------------------------------------------------------------------
-- ## Generic two-block assembly (shared by the tensor and `∘` cases).
--
-- Both cases lay a G-block of edges (embedded by `iL`) before a K-block
-- (embedded by `iR`) and assemble `NoInvH H` of the concatenation from
-- `NoInvH G`/`NoInvH K`.  Given the two per-block `BelowH` transports and the
-- cross-block acyclicity, the assembly is pure stdlib
-- `AllPairs.Properties.++⁺`/`map⁺` plumbing — proved once here and instantiated
-- by each case with its own transports.

module Assemble
  (G K H : Hypergraph FlatGen)
  (iL : Fin (Hypergraph.nE G) → Fin (Hypergraph.nE H))
  (iR : Fin (Hypergraph.nE K) → Fin (Hypergraph.nE H))
  (bLE   : ∀ {a b} → BelowH G a b → BelowH H (iL a) (iL b))
  (bRE   : ∀ {a b} → BelowH K a b → BelowH H (iR a) (iR b))
  (cross : ∀ {ea eb} → BelowH H (iL ea) (iR eb))
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K

  -- Every G-block edge is `BelowH H` every K-block edge (the cross `All`).
  cross-all-row : ∀ (ea : Fin G.nE) (ks : List (Fin K.nE))
                → All (BelowH H (iL ea)) (map iR ks)
  cross-all-row ea []        = []
  cross-all-row ea (eb ∷ ks) = cross ∷ cross-all-row ea ks

  cross-all : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
            → All (λ a → All (BelowH H a) (map iR ks)) (map iL gs)
  cross-all []        ks = []
  cross-all (ea ∷ gs) ks = cross-all-row ea ks ∷ cross-all gs ks

  -- Relabel a sub-`AllPairs` through `iL`/`iR` using the `Below` transports.
  mapAP-G : ∀ {gs} → AllPairs (BelowH G) gs
          → AllPairs (λ a b → BelowH H (iL a) (iL b)) gs
  mapAP-G []          = []
  mapAP-G (px ∷ rest) = All-map bLE px ∷ mapAP-G rest

  mapAP-K : ∀ {ks} → AllPairs (BelowH K) ks
          → AllPairs (λ a b → BelowH H (iR a) (iR b)) ks
  mapAP-K []          = []
  mapAP-K (px ∷ rest) = All-map bRE px ∷ mapAP-K rest

  NoInvH-assemble : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                  → NoInvH G gs → NoInvH K ks
                  → NoInvH H (map iL gs ++ map iR ks)
  NoInvH-assemble gs ks noG noK =
    AllPairsProp.++⁺
      (AllPairsProp.map⁺ (mapAP-G noG))
      (AllPairsProp.map⁺ (mapAP-K noK))
      (cross-all gs ks)

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
  -- A dependency between two G-block edges reflects to a dependency in G, and
  -- symmetrically for K — both are instances of the generic `Dep-reflect`
  -- block-reflection engine along the injective vertex injections
  -- `injL = _↑ˡ_` / `injR = _↑ʳ_` with the `eout/ein` block reductions.
  tensor-GG-reflect : ∀ {ea eb : Fin G.nE} → Dep H (injLE eb) (injLE ea) → Dep G eb ea
  tensor-GG-reflect =
    Dep-reflect {sub = G} {H = H} T.injL (inject+-inj K.nV) injLE
      T.eout-c-inj₁-red T.ein-c-inj₁-red

  tensor-KK-reflect : ∀ {ea eb : Fin K.nE} → Dep H (injRE eb) (injRE ea) → Dep K eb ea
  tensor-KK-reflect =
    Dep-reflect {sub = K} {H = H} T.injR (raise-inj G.nV) injRE
      T.eout-c-inj₂-red T.ein-c-inj₂-red

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

  -- Assemble via the shared `Assemble` skeleton with the tensor transports.
  NoInvH-tensor : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                → NoInvH G gs → NoInvH K ks
                → NoInvH H (map injLE gs ++ map injRE ks)
  NoInvH-tensor =
    Assemble.NoInvH-assemble G K H injLE injRE
      Below-injLE Below-injRE tensor-cross-acyclic

  ------------------------------------------------------------------------------
  -- The diagonal.  An arbitrary composite edge is `splitAt`-dispatched into
  -- the G- or the K-block, where the SAME two reflections apply at `ea ≡ eb`.

  NoSelfDep-tensor : NoSelfDep G → NoSelfDep K → NoSelfDep H
  NoSelfDep-tensor G-nd K-nd {e} dep =
    dispatch (splitAt G.nE e)
             (subst (λ x → Dep H x x) (sym (join-splitAt G.nE K.nE e)) dep)
    where
      dispatch : (s : Fin G.nE ⊎ Fin K.nE)
               → Dep H (join G.nE K.nE s) (join G.nE K.nE s) → ⊥
      dispatch (inj₁ eG) d = G-nd (tensor-GG-reflect d)
      dispatch (inj₂ eK) d = K-nd (tensor-KK-reflect d)

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
  compose-GG-reflect =
    Dep-reflect {sub = G} {H = Hc} C.injL (inject+-inj _) injLEc
      C.eout-c-inj₁-red C.ein-c-inj₁-red

  -- K-block dependency reflects to K (like `tensor-KK-reflect`, with `injR`
  -- replaced by `remapP` and `raise-inj` by `remapP`'s injectivity on
  -- edge-port vertices = `LinearHComposeP.remapP-injective`).
  remapP-inj : ∀ {v v'} → C.remapP v ≡ C.remapP v' → v ≡ v'
  remapP-inj = LHC.remapP-injective G K bdy lin-G lin-K

  compose-KK-reflect : ∀ {ea eb : Fin K.nE}
                     → Dep Hc (injREc eb) (injREc ea) → Dep K eb ea
  compose-KK-reflect =
    Dep-reflect {sub = K} {H = Hc} C.remapP remapP-inj injREc
      C.eout-c-inj₂-red C.ein-c-inj₂-red

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
    -- `remapP k ≡ i ↑ˡ cn` then `k ∈ K.dom`.  `Prune.classify-view` splits
    -- `classify K.dom k`: `mem` *is* the wanted `k ∈ K.dom`; `out` reduces
    -- `remapP k` to a `G.nV ↑ʳ_` slot, absurd against `i ↑ˡ cn` by `Inv.↑ˡ≢↑ʳ`.
    remapP-injL→dom
      : ∀ (k : Fin K.nV) (i : Fin G.nV) → C.remapP k ≡ i ↑ˡ cn → k ∈ K.dom
    remapP-injL→dom k i hyp with classify K.dom k | classify-view K.dom k
    ... | _ | is-mem k∈  = k∈
    ... | _ | is-non _   = ⊥-elim (Inv.↑ˡ≢↑ʳ i _ (sym hyp))

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

  -- Assemble via the shared `Assemble` skeleton with the composition transports.
  NoInvH-compose : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                 → NoInvH G gs → NoInvH K ks
                 → NoInvH Hc (map injLEc gs ++ map injREc ks)
  NoInvH-compose =
    Assemble.NoInvH-assemble G K Hc injLEc injREc
      Below-injLEc Below-injREc compose-cross-acyclic

  ------------------------------------------------------------------------------
  -- The diagonal, exactly as in the tensor case: `splitAt`-dispatch, then the
  -- two block reflections at `ea ≡ eb`.  Note that `remapP`-injectivity comes
  -- from `Linear G`/`Linear K` here — the `Unique`-boundary route
  -- (`PrunedCompose.remapP-injective-from-unique`) is not needed.

  NoSelfDep-compose : NoSelfDep G → NoSelfDep K → NoSelfDep Hc
  NoSelfDep-compose G-nd K-nd {e} dep =
    dispatch (splitAt G.nE e)
             (subst (λ x → Dep Hc x x) (sym (join-splitAt G.nE K.nE e)) dep)
    where
      dispatch : (s : Fin G.nE ⊎ Fin K.nE)
               → Dep Hc (join G.nE K.nE s) (join G.nE K.nE s) → ⊥
      dispatch (inj₁ eG) d = G-nd (compose-GG-reflect d)
      dispatch (inj₂ eK) d = K-nd (compose-KK-reflect d)

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
-- ## The same induction on the diagonal: `NoSelfDep ⟪ f ⟫`.

NoSelfDep-hId : ∀ A → NoSelfDep (hId A)
NoSelfDep-hId unit      {e} = NoSelfDep-hEmpty {e}
NoSelfDep-hId (Var x)   {e} = NoSelfDep-hVar x {e}
NoSelfDep-hId (A ⊗₀ B)  {e} =
  NoSelfDep-tensor (hId A) (hId B) (NoSelfDep-hId A) (NoSelfDep-hId B) {e}

NoSelfDep-⟪⟫ : ∀ {A B} (f : HomTerm A B) → NoSelfDep ⟪ f ⟫
NoSelfDep-⟪⟫ (id {A})       {e} = NoSelfDep-hId A {e}
NoSelfDep-⟪⟫ (λ⇒ {A})       {e} = NoSelfDep-hId A {e}
NoSelfDep-⟪⟫ (λ⇐ {A})       {e} = NoSelfDep-hId A {e}
NoSelfDep-⟪⟫ (ρ⇒ {A})       {e} = NoSelfDep-hId (A ⊗₀ unit) {e}
NoSelfDep-⟪⟫ (ρ⇐ {A})       {e} = NoSelfDep-hId (A ⊗₀ unit) {e}
NoSelfDep-⟪⟫ (α⇒ {A}{B}{C}) {e} = NoSelfDep-hId ((A ⊗₀ B) ⊗₀ C) {e}
NoSelfDep-⟪⟫ (α⇐ {A}{B}{C}) {e} = NoSelfDep-hId ((A ⊗₀ B) ⊗₀ C) {e}
NoSelfDep-⟪⟫ (σ {A}{B})     {e} = NoSelfDep-hSwap A B {e}
NoSelfDep-⟪⟫ (Agen g)       {e} = NoSelfDep-hGen g {e}
NoSelfDep-⟪⟫ (f ⊗₁ g)       {e} =
  NoSelfDep-tensor ⟪ f ⟫ ⟪ g ⟫ (NoSelfDep-⟪⟫ f) (NoSelfDep-⟪⟫ g) {e}
NoSelfDep-⟪⟫ (g ∘ f)        {e} =
  NoSelfDep-compose ⟪ f ⟫ ⟪ g ⟫ (trans (⟪⟫-codL f) (sym (⟪⟫-domL g)))
    (⟪⟫-LinearP f) (⟪⟫-LinearP g)
    (NoSelfDep-⟪⟫ f) (NoSelfDep-⟪⟫ g) {e}

--------------------------------------------------------------------------------
-- ## The targets.  `fin-order-NoInv-⟪⟫` in `IW.PerHG.NoInv` form
-- (= `NoInvH ⟪ f ⟫` definitionally); `dep-irrefl-⟪⟫` on the diagonal.
--
-- `IsoInvarianceWiring.PerHG` asks `¬ Dep H e e` for an ARBITRARY `H`, which
-- is FALSE in general (a self-loop edge); `dep-irrefl-⟪⟫` is the honest
-- `⟪f⟫`-specific statement, supplied at the `H = ⟪f⟫` call site.

fin-order-NoInv-⟪⟫
  : ∀ {A B} (f : HomTerm A B)
  → IW.PerHG.NoInv ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫))
fin-order-NoInv-⟪⟫ f = NoInvH-range-⟪⟫ f

dep-irrefl-⟪⟫ : ∀ {A B} (f : HomTerm A B) {e} → ¬ (Dep ⟪ f ⟫ e e)
dep-irrefl-⟪⟫ f = NoSelfDep-⟪⟫ f
