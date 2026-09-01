{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- (LemC) The natural `Fin` edge-order of a TRANSLATED hypergraph is a
-- linear extension of its immediate dependency relation `Dep`.
--
-- Goal: `fin-order-NoInv-⟪⟫ : ∀ {A B} (f : HomTerm A B) → NoInvH ⟪f⟫ (range
-- nE)`, where `NoInvH H = AllPairs (λ a b → ¬ Dep H b a)` — "for edges `a`
-- before `b` in `range`, `b` does not produce a wire that `a` consumes" (no
-- earlier-consumes-later inversion).
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
-- decoder's totality witness `IsoInvarianceWiring.PerHG.Valid`, i.e.
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
--       - `compose-KK-reflect` reuses `DecodeAttemptLinearP.remapP-injective`;
--       - `compose-cross-acyclic`: a `remapP`-image of a K-output that is also
--         an `injL`-image forces the K-output into `K.dom`, occurring in BOTH
--         summands of `producedList K` (`count ≥ 2`), contradicting `Linear K`.
--     `Linearity` and `DecodeAttemptLinearP` are both
--     bare-`sig` modules, so the whole `∘` case is reachable here.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; range; flatten; hGen; hId; hTensor; module hTensor-impl)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep; Dep-reflect)
import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open Inv using (inject+-inj; raise-inj; disj-L-R; range-++)

-- Linearity layer: the `Linear` invariant, the pruned-translation linearity
-- witness, and the pruning machinery for the `∘` case.
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (⟪⟫-LinearP; remapP-injective)
open import Categories.APROP.Hypergraph.Util.Prune
  using (remap-↑ˡ→∈)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)

open import Data.Fin using (Fin; zero; _↑ˡ_; _↑ʳ_; splitAt; join)
open import Data.Fin.Properties using (join-splitAt)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁻; ∈-concat⁺′; ∈-tabulate⁺)
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
import Data.List.Relation.Unary.All.Properties as AllProp
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs as AP
import Data.List.Relation.Unary.AllPairs.Properties as AllPairsProp
open import Data.Nat using (_+_)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- The one count fact the `∘` cross-acyclicity needs, from the shared
-- `CountCombinatorics` leaf: a `count ≤ 1` bound on a `_++_` makes its two
-- sides disjoint.
open import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics sig
  using (++-bnd→disjoint)

--------------------------------------------------------------------------------
-- ## The `NoInv` predicate as a bare `AllPairs`.
--
-- Convenient per-`H` abbreviations; `NoInvH H` coincides definitionally
-- with `IsoInvarianceWiring.PerHG.NoInv H` (both are irreflexivity-free
-- `AllPairs`), which is what lets the consumers take these two exports
-- where that spelling is expected -- no wrapper here restates them.

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

-- Every edge index of a two-block hypergraph is an `_↑ˡ_`- or an `_↑ʳ_`-image,
-- so a property of a single index (i.e. a DIAGONAL property) that holds on both
-- blocks holds everywhere.  Used by both two-block `NoSelfDep` cases.
splitE : ∀ {m n} (P : Fin (m + n) → Set)
       → (∀ a → P (a ↑ˡ n)) → (∀ b → P (m ↑ʳ b)) → ∀ e → P e
splitE {m} {n} P pl pr e = subst P (join-splitAt m n e) (go (splitAt m e))
  where
    go : ∀ s → P (join m n s)
    go (inj₁ a) = pl a
    go (inj₂ b) = pr b

--------------------------------------------------------------------------------
-- ## `NoSelfDep` for the single edge.  The zero-edge shapes (`hEmpty`,
-- `hVar`, `hSwap`) need no lemma: `Dep` is vacuous there, and the two
-- inductions below discharge them by an absurd pattern in place.

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
-- `NoInvH G`/`NoInvH K`.  Given the two per-block dependency REFLECTIONS and
-- the cross-block acyclicity, the assembly is pure stdlib plumbing
-- (`AllPairs.map` to relabel each block, `AllPairs.Properties.map⁺`/`++⁺` to
-- concatenate, `All.universal` for the constant cross rows) — proved once here
-- and instantiated by each case with its own reflections.
--
-- The reflections (rather than pre-composed `BelowH` transports) are the
-- parameters because they are also what the DIAGONAL needs, so each case
-- supplies exactly two lemmas for both jobs.

module Assemble
  (G K H : Hypergraph FlatGen)
  (iL : Fin (Hypergraph.nE G) → Fin (Hypergraph.nE H))
  (iR : Fin (Hypergraph.nE K) → Fin (Hypergraph.nE H))
  (rL : ∀ {ea eb} → Dep H (iL eb) (iL ea) → Dep G eb ea)
  (rR : ∀ {ea eb} → Dep H (iR eb) (iR ea) → Dep K eb ea)
  (cross : ∀ {ea eb} → BelowH H (iL ea) (iR eb))
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K

  NoInvH-assemble : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                  → NoInvH G gs → NoInvH K ks
                  → NoInvH H (map iL gs ++ map iR ks)
  NoInvH-assemble gs ks noG noK =
    AllPairsProp.++⁺
      (AllPairsProp.map⁺ (AP.map (λ nd dep → nd (rL dep)) noG))
      (AllPairsProp.map⁺ (AP.map (λ nd dep → nd (rR dep)) noK))
      (AllProp.map⁺ (universal (λ _ → AllProp.map⁺ (universal (λ _ → cross) ks)) gs))

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

  -- Assemble via the shared `Assemble` skeleton with the tensor reflections.
  NoInvH-tensor : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                → NoInvH G gs → NoInvH K ks
                → NoInvH H (map injLE gs ++ map injRE ks)
  NoInvH-tensor =
    Assemble.NoInvH-assemble G K H injLE injRE
      tensor-GG-reflect tensor-KK-reflect tensor-cross-acyclic

  ------------------------------------------------------------------------------
  -- The diagonal.  An arbitrary composite edge is `splitE`-dispatched into the
  -- G- or the K-block, where the SAME two reflections apply at `ea ≡ eb`.

  NoSelfDep-tensor : NoSelfDep G → NoSelfDep K → NoSelfDep H
  NoSelfDep-tensor G-nd K-nd {e} =
    splitE {G.nE} {K.nE} (λ x → ¬ Dep H x x)
           (λ _ d → G-nd (tensor-GG-reflect d)) (λ _ d → K-nd (tensor-KK-reflect d)) e

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
  -- edge-port vertices = `DecodeAttemptLinearP.remapP-injective`).
  remapP-inj : ∀ {v v'} → C.remapP v ≡ C.remapP v' → v ≡ v'
  remapP-inj = remapP-injective G K bdy lin-G lin-K

  compose-KK-reflect : ∀ {ea eb : Fin K.nE}
                     → Dep Hc (injREc eb) (injREc ea) → Dep K eb ea
  compose-KK-reflect =
    Dep-reflect {sub = K} {H = Hc} C.remapP remapP-inj injREc
      C.eout-c-inj₂-red C.ein-c-inj₂-red

  -- The cross-block acyclicity — no K-block edge produces a wire an earlier
  -- G-block edge consumes.  A shared vertex `v` would be both a `remapP`-image
  -- of a K-output `k₀ ∈ K.eout eb` and an `injL`-image (`_↑ˡ cn`), so
  -- `Prune.remap-↑ˡ→∈` puts `k₀ ∈ K.dom` — whence `k₀` occurs in BOTH
  -- summands of `producedList K` (`count ≥ 2`), contradicting `Linear K`'s
  -- bound `≤ 1`.
  private
    -- An edge-output that is also in `K.dom` occurs in BOTH summands of
    -- `producedList K = K.dom ++ concat (tabulate eout)`, so `Linear K`'s
    -- `count ≤ 1` bound on that concatenation refutes it.
    dom-and-out→absurd
      : ∀ (k : Fin K.nV) (eb : Fin K.nE)
      → k ∈ K.dom → k ∈ K.eout eb → ⊥
    dom-and-out→absurd k eb k∈dom k∈out =
      ++-bnd→disjoint K.dom (concat (tabulate K.eout)) (proj₂ lin-K k)
                      k∈dom (∈-concat⁺′ k∈out (∈-tabulate⁺ eb))

  compose-cross-acyclic : ∀ {ea : Fin G.nE} {eb : Fin K.nE}
                        → ¬ Dep Hc (injREc eb) (injLEc ea)
  compose-cross-acyclic {ea} {eb} (v , v∈out , v∈in)
    with subst (v ∈_) (C.eout-c-inj₂-red eb) v∈out
       | subst (v ∈_) (C.ein-c-inj₁-red ea) v∈in
  ... | v∈out' | v∈in' with ∈-map⁻ C.remapP v∈out' | ∈-map⁻ C.injL v∈in'
  ... | k₀ , k₀∈out , v≡rk | i₀ , i₀∈in , v≡injL =
        dom-and-out→absurd k₀ eb
          (remap-↑ˡ→∈ K.dom C.lookup-cod k₀ i₀ (trans (sym v≡rk) v≡injL))
          k₀∈out

  ------------------------------------------------------------------------------
  -- Assembly of `NoInvH Hc (range …)`, parallel to the tensor assembly.

  -- Assemble via the shared `Assemble` skeleton with the composition reflections.
  NoInvH-compose : ∀ (gs : List (Fin G.nE)) (ks : List (Fin K.nE))
                 → NoInvH G gs → NoInvH K ks
                 → NoInvH Hc (map injLEc gs ++ map injREc ks)
  NoInvH-compose =
    Assemble.NoInvH-assemble G K Hc injLEc injREc
      compose-GG-reflect compose-KK-reflect compose-cross-acyclic

  ------------------------------------------------------------------------------
  -- The diagonal, exactly as in the tensor case: `splitE`-dispatch, then the
  -- two block reflections at `ea ≡ eb`.  Note that `remapP`-injectivity comes
  -- from `Linear G`/`Linear K` here.

  NoSelfDep-compose : NoSelfDep G → NoSelfDep K → NoSelfDep Hc
  NoSelfDep-compose G-nd K-nd {e} =
    splitE {G.nE} {K.nE} (λ x → ¬ Dep Hc x x)
           (λ _ d → G-nd (compose-GG-reflect d)) (λ _ d → K-nd (compose-KK-reflect d)) e

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

fin-order-NoInv-⟪⟫ : ∀ {A B} (f : HomTerm A B)
                → NoInvH ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫))

-- Zero-edge `hId`-shaped cases, via `NoInvH-hId`.
fin-order-NoInv-⟪⟫ (id {A})       = NoInvH-hId A
fin-order-NoInv-⟪⟫ (λ⇒ {A})       = NoInvH-hId A
fin-order-NoInv-⟪⟫ (λ⇐ {A})       = NoInvH-hId A
fin-order-NoInv-⟪⟫ (ρ⇒ {A})       = NoInvH-hId (A ⊗₀ unit)
fin-order-NoInv-⟪⟫ (ρ⇐ {A})       = NoInvH-hId (A ⊗₀ unit)
fin-order-NoInv-⟪⟫ (α⇒ {A}{B}{C}) = NoInvH-hId ((A ⊗₀ B) ⊗₀ C)
fin-order-NoInv-⟪⟫ (α⇐ {A}{B}{C}) = NoInvH-hId ((A ⊗₀ B) ⊗₀ C)

-- `σ`: `⟪ σ ⟫ = hSwap A B`, which has `nE = 0` literally ⇒ `range 0 = []`.
fin-order-NoInv-⟪⟫ (σ {A}{B})     = []

-- Single edge: `nE = 1`, `range 1 = zero ∷ []`; the singleton has no pairs.
fin-order-NoInv-⟪⟫ (Agen g)       = [] ∷ []

-- Tensor: split `range (G.nE + K.nE)` via `range-++` and reuse the IHs.
fin-order-NoInv-⟪⟫ (f ⊗₁ g) =
  subst (NoInvH (hTensor F G))
        (sym (range-++ F.nE G.nE))
        (NoInvH-tensor F G (range F.nE) (range G.nE)
          (fin-order-NoInv-⟪⟫ f) (fin-order-NoInv-⟪⟫ g))
  where
    F = ⟪ f ⟫
    G = ⟪ g ⟫
    module F = Hypergraph F
    module G = Hypergraph G

-- Composition: `⟪ g ∘ f ⟫ = hComposeP ⟪ f ⟫ ⟪ g ⟫ bdy`.  Split and reuse.
fin-order-NoInv-⟪⟫ (g ∘ f) =
  subst (NoInvH (hComposeP F G bdy))
        (sym (range-++ F.nE G.nE))
        (NoInvH-compose F G bdy (⟪⟫-LinearP f) (⟪⟫-LinearP g)
          (range F.nE) (range G.nE)
          (fin-order-NoInv-⟪⟫ f) (fin-order-NoInv-⟪⟫ g))
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
NoSelfDep-hId unit      {()}
NoSelfDep-hId (Var x)   {()}
NoSelfDep-hId (A ⊗₀ B)  {e} =
  NoSelfDep-tensor (hId A) (hId B) (NoSelfDep-hId A) (NoSelfDep-hId B) {e}

dep-irrefl-⟪⟫ : ∀ {A B} (f : HomTerm A B) → NoSelfDep ⟪ f ⟫
dep-irrefl-⟪⟫ (id {A})       {e} = NoSelfDep-hId A {e}
dep-irrefl-⟪⟫ (λ⇒ {A})       {e} = NoSelfDep-hId A {e}
dep-irrefl-⟪⟫ (λ⇐ {A})       {e} = NoSelfDep-hId A {e}
dep-irrefl-⟪⟫ (ρ⇒ {A})       {e} = NoSelfDep-hId (A ⊗₀ unit) {e}
dep-irrefl-⟪⟫ (ρ⇐ {A})       {e} = NoSelfDep-hId (A ⊗₀ unit) {e}
dep-irrefl-⟪⟫ (α⇒ {A}{B}{C}) {e} = NoSelfDep-hId ((A ⊗₀ B) ⊗₀ C) {e}
dep-irrefl-⟪⟫ (α⇐ {A}{B}{C}) {e} = NoSelfDep-hId ((A ⊗₀ B) ⊗₀ C) {e}
dep-irrefl-⟪⟫ (σ {A}{B})     {()}
dep-irrefl-⟪⟫ (Agen g)       {e} = NoSelfDep-hGen g {e}
dep-irrefl-⟪⟫ (f ⊗₁ g)       {e} =
  NoSelfDep-tensor ⟪ f ⟫ ⟪ g ⟫ (dep-irrefl-⟪⟫ f) (dep-irrefl-⟪⟫ g) {e}
dep-irrefl-⟪⟫ (g ∘ f)        {e} =
  NoSelfDep-compose ⟪ f ⟫ ⟪ g ⟫ (trans (⟪⟫-codL f) (sym (⟪⟫-domL g)))
    (⟪⟫-LinearP f) (⟪⟫-LinearP g)
    (dep-irrefl-⟪⟫ f) (dep-irrefl-⟪⟫ g) {e}

