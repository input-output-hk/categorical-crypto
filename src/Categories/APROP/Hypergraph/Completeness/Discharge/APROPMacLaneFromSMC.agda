{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Bridge module: SMC/Combinatorial narrowed atoms ⇒ APROPMacLaneAtoms parts.
--
-- ## Status
--
-- FULL constructive bridge `SMCMacLaneAtoms + LinearityCombinatorial →
-- APROPMacLaneAtoms`, including:
--
--   * `linear-APROP→COMB` / `linear-COMB→APROP`
--   * `allFire-APROP→COMB` / `allFire-COMB→APROP`
--   * `swap-already-fires-from-combinatorial`           (atom 3)
--   * `process-edges-≡-process-steps`                   (correspondence lemma)
--   * `swap-atom-aligned-from-SMC`                      (atom 1)
--   * `swap-with-rest-aligned-from-SMC`                 (atom 2)
--   * `bridge-to-g-permute-from-SMC`                    (atom 4)
--   * `APROPMacLaneFromSMC`                             (full bridge)
--
-- The Fin-layer SMC refactor (in `Categories.FreeSMC.Steps`) ensures
-- `SMC.process-steps` is DEFINITIONALLY EQUAL to APROP's
-- `process-edges` after the trivial `edge→step` lift, so the
-- correspondence lemma collapses to a `process-edges-cons-success`
-- chain plus structural induction.
--
-- ## File is `--safe --with-K` clean.  NO postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.APROPMacLaneFromSMC
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)

-- APROP-side `Linear` and `count`.
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin

-- APROP-side `AllFire` (with extract-prefix evidence).
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec as APR
open APR using (AllFire)

-- The decoder's `extract-prefix`, `process-edges`, and `Agen-edge`.
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix; process-edges; Agen-edge)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↭-residual)

-- `process-edges-cons-success` + `fired-bridged` for the correspondence proof.
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapMacLane
  sig-dec
  using (process-edges-cons-success)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomAligned
  sig-dec
  using (fired-bridged)

-- Generic combinatorial Linear/AllFire (no APROP dependency).
import Categories.Hypergraph.LinearityCombinatorial as Comb
open Comb using (LinearityCombinatorial)

-- SMC-side Steps and atoms.
import Categories.FreeSMC.Steps           asFreeMonoidalData as SMC
import Categories.FreeSMC.MacLaneAtoms    asFreeMonoidalData as SMC-Atoms
open SMC-Atoms using (SMCMacLaneAtoms)

-- The SwapAtomResidual record + the c'-chain atom record.
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomAssumptionDischarge
  sig-dec
  using (SwapAtomResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTermPermuteAlignedFromIrreducibles
  sig-dec
  using (APROPMacLaneAtoms)

-- For atom (4): the iso machinery.
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (range; ⟪⟫-domL)
  renaming (⟪_⟫ to ⟪_⟫F)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)

open import Categories.Category using (Category)
open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_; map; tabulate; concat)
open import Data.List.Properties using (map-++)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary.Decidable using (yes; no)

private
  module FM = Category FreeMonoidal

--------------------------------------------------------------------------------
-- ## Section 1: `count` correspondence (APROP ≡ Combinatorial).

count-correspond
  : ∀ {n} (v : Fin n) (xs : List (Fin n))
  → Lin.count v xs ≡ Comb.count v xs
count-correspond v []       = refl
count-correspond v (x ∷ xs) with v ≟ x
... | yes _ = cong suc (count-correspond v xs)
... | no  _ = count-correspond v xs

--------------------------------------------------------------------------------
-- ## Section 2: `producedList` / `consumedList` correspondence.

producedList-correspond
  : (H : Hypergraph FlatGen)
  → Lin.producedList H ≡ Comb.producedList H
producedList-correspond H = refl

consumedList-correspond
  : (H : Hypergraph FlatGen)
  → Lin.consumedList H ≡ Comb.consumedList H
consumedList-correspond H = refl

--------------------------------------------------------------------------------
-- ## Section 3: `Linear` correspondence.

linear-APROP→COMB
  : (H : Hypergraph FlatGen) → Lin.Linear H → Comb.Linear H
linear-APROP→COMB H (bal , bnd) = bal-COMB , bnd-COMB
  where
    bal-COMB : ∀ v → Comb.count v (Comb.producedList H)
                  ≡ Comb.count v (Comb.consumedList H)
    bal-COMB v = trans (sym (count-correspond v (Lin.producedList H)))
                  (trans (bal v) (count-correspond v (Lin.consumedList H)))

    bnd-COMB : ∀ v → Comb.count v (Comb.producedList H) Nat.≤ 1
    bnd-COMB v = subst (λ n → n Nat.≤ 1) (count-correspond v (Lin.producedList H)) (bnd v)

linear-COMB→APROP
  : (H : Hypergraph FlatGen) → Comb.Linear H → Lin.Linear H
linear-COMB→APROP H (bal , bnd) = bal-APROP , bnd-APROP
  where
    bal-APROP : ∀ v → Lin.count v (Lin.producedList H)
                   ≡ Lin.count v (Lin.consumedList H)
    bal-APROP v = trans (count-correspond v (Lin.producedList H))
                   (trans (bal v) (sym (count-correspond v (Lin.consumedList H))))

    bnd-APROP : ∀ v → Lin.count v (Lin.producedList H) Nat.≤ 1
    bnd-APROP v =
      subst (λ n → n Nat.≤ 1) (sym (count-correspond v (Lin.producedList H))) (bnd v)

--------------------------------------------------------------------------------
-- ## Section 4: `AllFire` correspondence (APROP ↔ Combinatorial).

allFire-APROP→COMB
  : (H : Hypergraph FlatGen)
    (es : List (Fin (Hypergraph.nE H)))
    (s : List (Fin (Hypergraph.nV H)))
  → AllFire H es s
  → Comb.AllFire H es s
allFire-APROP→COMB H []       s tt = tt
allFire-APROP→COMB H (e ∷ es) s (rest , p , _ , af-tail) =
  rest , p , allFire-APROP→COMB H es (Hypergraph.eout H e ++ rest) af-tail

allFire-COMB→APROP
  : (H : Hypergraph FlatGen)
    (es : List (Fin (Hypergraph.nE H)))
    (s : List (Fin (Hypergraph.nV H)))
  → Comb.AllFire H es s
  → AllFire H es s
allFire-COMB→APROP H []       s tt = tt
allFire-COMB→APROP H (e ∷ es) s (rest , p , af-tail)
  with extract-prefix-↭-residual (Hypergraph.ein H e) s rest p
... | rest' , p' , eq , rest-↭-rest' =
      let af-tail-COMB : Comb.AllFire H es (Hypergraph.eout H e ++ rest)
          af-tail-COMB = af-tail

          tail-perm : (Hypergraph.eout H e ++ rest)
                       Perm.↭ (Hypergraph.eout H e ++ rest')
          tail-perm = perm-++-cong-right (Hypergraph.eout H e) rest-↭-rest'

          af-tail-at-rest' : Comb.AllFire H es (Hypergraph.eout H e ++ rest')
          af-tail-at-rest' = comb-allFire-↭-stack H es _ _ tail-perm af-tail-COMB

          af-tail-APROP : AllFire H es (Hypergraph.eout H e ++ rest')
          af-tail-APROP =
            allFire-COMB→APROP H es (Hypergraph.eout H e ++ rest') af-tail-at-rest'
      in rest' , p' , eq , af-tail-APROP
  where
    perm-++-cong-right
      : ∀ {n} (xs : List (Fin n)) {ys zs : List (Fin n)}
      → ys Perm.↭ zs
      → (xs ++ ys) Perm.↭ (xs ++ zs)
    perm-++-cong-right []       p = p
    perm-++-cong-right (x ∷ xs) p = Perm.prep x (perm-++-cong-right xs p)

    comb-allFire-↭-stack
      : (H : Hypergraph FlatGen)
        (es : List (Fin (Hypergraph.nE H)))
        (s s' : List (Fin (Hypergraph.nV H)))
      → s Perm.↭ s'
      → Comb.AllFire H es s
      → Comb.AllFire H es s'
    comb-allFire-↭-stack H []       s s' _      tt = tt
    comb-allFire-↭-stack H (e ∷ es) s s' s-perm (rest , p , af-tail) =
      rest , Perm.↭-trans (Perm.↭-sym s-perm) p , af-tail

--------------------------------------------------------------------------------
-- ## Section 5: The atom-(3) bridge.

swap-already-fires-from-combinatorial
  : LinearityCombinatorial {X = X} {Gen = FlatGen}
  → ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
      (xs : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → Lin.Linear H
  → AllFire H (e₁ ∷ e₂ ∷ xs) s
  → AllFire H (e₂ ∷ e₁ ∷ []) s
swap-already-fires-from-combinatorial lin H e₁ e₂ xs s lin-APROP af-APROP =
  let lin-COMB    = linear-APROP→COMB H lin-APROP
      af-COMB     = allFire-APROP→COMB H (e₁ ∷ e₂ ∷ xs) s af-APROP
      result-COMB = LinearityCombinatorial.swap-already-fires
                      lin H e₁ e₂ xs s lin-COMB af-COMB
  in allFire-COMB→APROP H (e₂ ∷ e₁ ∷ []) s result-COMB

--------------------------------------------------------------------------------
-- ## Section 6: SMC ↔ APROP correspondence helpers.
--
-- The Fin-layer SMC `process-steps` matches APROP's `process-edges`
-- DEFINITIONALLY after the trivial `edge→step` lift.  Specifically:
--   * `SMC.fire-bridged (edge→step H e) s rest perm` reduces to the
--     SAME term as `APR.fired-bridged H e s rest perm`.
--   * `SMC.process-steps H.nV H.vlab` mirrors the structure of
--     APROP's `process-edges H` under AllFire-success branches.

edge→step
  : (H : Hypergraph FlatGen) → Fin (Hypergraph.nE H)
  → SMC.Step (Hypergraph.nV H) (Hypergraph.vlab H)
edge→step H e =
  Hypergraph.ein H e , Hypergraph.eout H e , Agen-edge H e

-- Verify `fire-bridged ≡ fired-bridged` definitionally.  If this
-- typechecks with `refl`, the bridge for the inductive case of
-- `process-edges-≡-process-steps` follows by `cong`.

fire-bridged≡fired-bridged
  : ∀ (H : Hypergraph FlatGen) (e : Fin (Hypergraph.nE H))
      (s rest : List (Fin (Hypergraph.nV H)))
      (perm : s Perm.↭ Hypergraph.ein H e ++ rest)
  → SMC.fire-bridged (Hypergraph.nV H) (Hypergraph.vlab H)
        (edge→step H e) s rest perm
    ≡ fired-bridged H e s rest perm
fire-bridged≡fired-bridged H e s rest perm = refl

-- Lift APROP AllFire to SMC AllFire (drop extract-prefix evidence).

lift-AllFire
  : (H : Hypergraph FlatGen)
    (es : List (Fin (Hypergraph.nE H)))
    (s : List (Fin (Hypergraph.nV H)))
  → AllFire H es s
  → SMC.AllFire (Hypergraph.nV H) (Hypergraph.vlab H)
                 (map (edge→step H) es) s
lift-AllFire H []       s tt = tt
lift-AllFire H (e ∷ es) s (rest , perm , _ , af-tail) =
  rest , perm , lift-AllFire H es (Hypergraph.eout H e ++ rest) af-tail

-- Correspondence: APROP `process-edges` and SMC `process-steps` produce
-- equal results under (lifted) APROP AllFire.

process-edges-≡-process-steps
  : (H : Hypergraph FlatGen)
    (es : List (Fin (Hypergraph.nE H)))
    (s : List (Fin (Hypergraph.nV H)))
    (af : AllFire H es s)
  → process-edges H es s
    ≡ SMC.process-steps (Hypergraph.nV H) (Hypergraph.vlab H)
        (map (edge→step H) es) s (lift-AllFire H es s af)
process-edges-≡-process-steps H []       s tt = refl
process-edges-≡-process-steps H (e ∷ es) s (rest , perm , eq , af-tail) =
  let ih = process-edges-≡-process-steps H es (Hypergraph.eout H e ++ rest) af-tail
      cs = process-edges-cons-success H e es s rest perm eq
  in trans cs
       (cong (λ x → proj₁ x , proj₂ x FM.∘ fired-bridged H e s rest perm) ih)

--------------------------------------------------------------------------------
-- ## Section 7: Atom (1)/(2)/(4) bridges via `ProcessEdges↭Goal-abs`.
--
-- Introduce a `ProcessEdges↭Goal-abs` abstraction that takes the two
-- Σ-pairs (process-edges/process-steps outputs) as direct inputs.
-- Both APROP and SMC `ProcessEdges↭Goal` reduce to this abstraction.
-- Then `subst₂` over the correspondence equations transports the SMC
-- atom output to the APROP goal.

-- An abstraction over the two Σ-pair outputs (suitable for both
-- APROP `process-edges` and SMC `process-steps`).

private
  PEGoal-abs
    : (H : Hypergraph FlatGen) (s : List (Fin (Hypergraph.nV H)))
      (p₁ p₂ : Σ[ s' ∈ List (Fin (Hypergraph.nV H)) ]
                HomTerm (unflatten (map (Hypergraph.vlab H) s))
                         (unflatten (map (Hypergraph.vlab H) s')))
    → Set
  PEGoal-abs H s p₁ p₂ =
    Σ[ stack-↭ ∈ proj₁ p₁ Perm.↭ proj₁ p₂ ]
      proj₂ p₁
      ≈Term
      permute-via-vlab (Hypergraph.vlab H) (Perm.↭-sym stack-↭)
        ∘ proj₂ p₂

  -- APR.ProcessEdges↭Goal definitionally unfolds to PEGoal-abs.
  PEGoal-abs-APR
    : ∀ H (es₁ es₂ : List (Fin (Hypergraph.nE H)))
        (s : List (Fin (Hypergraph.nV H)))
    → APR.ProcessEdges↭Goal H es₁ es₂ s
      ≡ PEGoal-abs H s (process-edges H es₁ s) (process-edges H es₂ s)
  PEGoal-abs-APR H es₁ es₂ s = refl

  -- SMC.ProcessEdges↭Goal definitionally unfolds to PEGoal-abs (when
  -- both `permute-via-vlab` and `unflatten` are the shared re-exports).
  PEGoal-abs-SMC
    : ∀ H (es₁ es₂ : SMC.Steps (Hypergraph.nV H) (Hypergraph.vlab H))
        (s : List (Fin (Hypergraph.nV H)))
        (af₁ : SMC.AllFire (Hypergraph.nV H) (Hypergraph.vlab H) es₁ s)
        (af₂ : SMC.AllFire (Hypergraph.nV H) (Hypergraph.vlab H) es₂ s)
    → SMC.ProcessEdges↭Goal (Hypergraph.nV H) (Hypergraph.vlab H)
        es₁ es₂ s af₁ af₂
      ≡ PEGoal-abs H s
          (SMC.process-steps (Hypergraph.nV H) (Hypergraph.vlab H)
             es₁ s af₁)
          (SMC.process-steps (Hypergraph.nV H) (Hypergraph.vlab H)
             es₂ s af₂)
  PEGoal-abs-SMC H es₁ es₂ s af₁ af₂ = refl

swap-atom-aligned-from-SMC
  : SMCMacLaneAtoms
  → ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
      (s : List (Fin (Hypergraph.nV H)))
  → APR.IndependentSwap H e₁ e₂ s
  → APR.ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ []) s
swap-atom-aligned-from-SMC smc H e₁ e₂ s (af1 , af2) =
  subst₂ (PEGoal-abs H s)
    (sym (process-edges-≡-process-steps H (e₁ ∷ e₂ ∷ []) s af1))
    (sym (process-edges-≡-process-steps H (e₂ ∷ e₁ ∷ []) s af2))
    (SMCMacLaneAtoms.swap-atom-aligned smc
       (Hypergraph.nV H) (Hypergraph.vlab H)
       (edge→step H e₁) (edge→step H e₂) s
       ( lift-AllFire H (e₁ ∷ e₂ ∷ []) s af1
       , lift-AllFire H (e₂ ∷ e₁ ∷ []) s af2 ))

--------------------------------------------------------------------------------
-- ## Section 7b: Atom (4) bridge — `bridge-to-g-permute-from-SMC`.
--
-- More involved than (1)/(2): APROP atom (4) involves TWO hypergraphs
-- (⟪f⟫F, ⟪g⟫F) whose vertex spaces differ (Translation prunes,
-- FromAPROP keeps).  The SMC atom (4) was redesigned to take two
-- (n, vlab) spaces with a `dom-eq` bridge.
--
-- Crucially: the SMC atom (4) uses `process-steps-maybe` (matches
-- APROP's `process-edges` definitionally after edge→step lift) — so
-- no AllFire is needed.

import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTermAligned2
  sig-dec as PTA2

-- After the edge→step lift, SMC `process-steps-maybe` agrees with
-- APROP's `process-edges` definitionally — they have the SAME body.
-- Verify this as a refl test.

process-steps-maybe≡process-edges
  : ∀ (H : Hypergraph FlatGen) (es : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → SMC.process-steps-maybe (Hypergraph.nV H) (Hypergraph.vlab H)
        (map (edge→step H) es) s
    ≡ process-edges H es s
process-steps-maybe≡process-edges H []       s = refl
process-steps-maybe≡process-edges H (e ∷ es) s
  with extract-prefix (Hypergraph.ein H e) s
... | nothing            = body-nothing
  where
    body-nothing = cong (λ x → proj₁ x , proj₂ x FM.∘ FM.id)
                        (process-steps-maybe≡process-edges H es s)
... | just (rest , perm) = body-just
  where
    body-just = cong (λ x → proj₁ x , proj₂ x FM.∘ fired-bridged H e s rest perm)
                     (process-steps-maybe≡process-edges H es (Hypergraph.eout H e ++ rest))

bridge-to-g-permute-from-SMC
  : SMCMacLaneAtoms
  → ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      (ψF : Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F))
      (stack-↭ :
        map (Hypergraph.vlab ⟪ f ⟫F)
            (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
        Perm.↭
        map (Hypergraph.vlab ⟪ g ⟫F)
            (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
      (b-stack-↭ :
        proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
        Perm.↭
        proj₁ (process-edges ⟪ f ⟫F
                 (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                 (Hypergraph.dom ⟪ f ⟫F)))
  → permute (Perm.↭-sym stack-↭)
    ∘ subst₂ HomTerm
        (cong unflatten (PTA2.full-dom-eq f g))
        refl
        (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
    ≈Term
    permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) (Perm.↭-sym b-stack-↭)
      ∘ proj₂ (process-edges ⟪ f ⟫F
                 (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                 (Hypergraph.dom ⟪ f ⟫F))
bridge-to-g-permute-from-SMC smc {A} {B} f g iso ψF stack-↭ b-stack-↭
  rewrite sym (process-steps-maybe≡process-edges
                 ⟪ f ⟫F (range (Hypergraph.nE ⟪ f ⟫F))
                 (Hypergraph.dom ⟪ f ⟫F))
        | sym (process-steps-maybe≡process-edges
                 ⟪ g ⟫F (range (Hypergraph.nE ⟪ g ⟫F))
                 (Hypergraph.dom ⟪ g ⟫F))
        | sym (process-steps-maybe≡process-edges
                 ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                 (Hypergraph.dom ⟪ f ⟫F))
        = SMCMacLaneAtoms.bridge-to-g-permute smc
            (Hypergraph.nV ⟪ f ⟫F) (Hypergraph.nV ⟪ g ⟫F)
            (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.vlab ⟪ g ⟫F)
            (map (edge→step ⟪ f ⟫F) (range (Hypergraph.nE ⟪ f ⟫F)))
            (map (edge→step ⟪ f ⟫F) (map ψF (range (Hypergraph.nE ⟪ g ⟫F))))
            (map (edge→step ⟪ g ⟫F) (range (Hypergraph.nE ⟪ g ⟫F)))
            (Hypergraph.dom ⟪ f ⟫F) (Hypergraph.dom ⟪ g ⟫F)
            (PTA2.full-dom-eq f g)
            stack-↭ b-stack-↭

swap-with-rest-aligned-from-SMC
  : SMCMacLaneAtoms
  → ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
      (xs ys : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
      (rest-↭ : xs Perm.↭ ys)
      (af₁ : AllFire H (e₁ ∷ e₂ ∷ xs) s)
      (af₂ : AllFire H (e₂ ∷ e₁ ∷ ys) s)
  → APR.ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ xs) (e₂ ∷ e₁ ∷ ys) s
swap-with-rest-aligned-from-SMC smc H e₁ e₂ xs ys s rest-↭ af₁ af₂ =
  subst₂ (PEGoal-abs H s)
    (sym (process-edges-≡-process-steps H (e₁ ∷ e₂ ∷ xs) s af₁))
    (sym (process-edges-≡-process-steps H (e₂ ∷ e₁ ∷ ys) s af₂))
    (SMCMacLaneAtoms.swap-with-rest-aligned smc
       (Hypergraph.nV H) (Hypergraph.vlab H)
       (edge→step H e₁) (edge→step H e₂)
       (map (edge→step H) xs) (map (edge→step H) ys) s
       (lift-Perm-↭ rest-↭)
       (lift-AllFire H (e₁ ∷ e₂ ∷ xs) s af₁)
       (lift-AllFire H (e₂ ∷ e₁ ∷ ys) s af₂))
  where
    open import Data.List.Relation.Binary.Permutation.Propositional.Properties
      using () renaming (map⁺ to perm-map⁺)

    lift-Perm-↭ : xs Perm.↭ ys → map (edge→step H) xs Perm.↭ map (edge→step H) ys
    lift-Perm-↭ p = perm-map⁺ (edge→step H) p

--------------------------------------------------------------------------------
-- ## Section 9: The full bridge — `APROPMacLaneFromSMC`.
--
-- Assembles all atom bridges into a single function:
--   SMCMacLaneAtoms + LinearityCombinatorial ⇒ APROPMacLaneAtoms
--
-- This is THE main result of this file.  Downstream auditors who want
-- the strictly-narrowed trust surface can postulate just
-- `SMCMacLaneAtoms` + `LinearityCombinatorial` and use this bridge to
-- produce `APROPMacLaneAtoms`, which then feeds into
-- `process-term-permute-aligned-from-atoms` to give the c'-chain field
-- of `Build`.

APROPMacLaneFromSMC
  : SMCMacLaneAtoms
  → LinearityCombinatorial {X = X} {Gen = FlatGen}
  → APROPMacLaneAtoms
APROPMacLaneFromSMC smc lin = record
  { swap-atom-residual = record
      { swap-atom-aligned     = swap-atom-aligned-from-SMC smc
      ; swap-with-rest-aligned = swap-with-rest-aligned-from-SMC smc
      ; swap-already-fires    = swap-already-fires-from-combinatorial lin
      }
  ; bridge-to-g-permute    = bridge-to-g-permute-from-SMC smc
  }
