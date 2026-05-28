{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Bridge module: SMC/Combinatorial narrowed atoms ⇒ APROPMacLaneAtoms parts.
--
-- ## Status
--
-- This file lands the CONSTRUCTIVE parts of the narrowing bridge:
--
--   * `linear-APROP→COMB` / `linear-COMB→APROP`
--       — equivalence of `Linearity.Linear H` and
--         `LinearityCombinatorial.Linear H` (definitionally equal up
--         to `count` definitions; bridged by `count-correspond`).
--
--   * `allFire-APROP→COMB` / `allFire-COMB→APROP`
--       — drop / recompute the `extract-prefix ≡ just` evidence field.
--         Both directions constructive; the COMB→APROP direction uses
--         `extract-prefix-↭-residual` to recover the locating evidence.
--
--   * `swap-already-fires-from-combinatorial`
--       — the (3) field of `SwapAtomResidual`, constructively derived
--         from a `LinearityCombinatorial` instance.
--
-- The full bridge `SMCMacLaneAtoms + LinearityCombinatorial →
-- APROPMacLaneAtoms` requires correspondence lemmas between APROP's
-- `process-edges` and SMC's `process-steps` (~300-500 LOC of
-- subst-juggling).  Until those land, fields (1), (2), (4) of
-- `APROPMacLaneAtoms` cannot be constructively derived from
-- `SMCMacLaneAtoms`; they remain at the APROP level.
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

-- The decoder's `extract-prefix` and the constructive
-- `extract-prefix-↭-residual` lemma.
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↭-residual)

-- Generic combinatorial Linear/AllFire (no APROP dependency).
import Categories.Hypergraph.LinearityCombinatorial as Comb
open Comb using (LinearityCombinatorial)

-- The SwapAtomResidual record (one of whose fields, `swap-already-fires`,
-- this file constructs).
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomAssumptionDischarge
  sig-dec
  using (SwapAtomResidual)

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_; tabulate; concat)
import Data.Nat as Nat
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)

--------------------------------------------------------------------------------
-- ## Section 1: `count` correspondence (APROP ≡ Combinatorial).
--
-- Both `Lin.count` and `Comb.count` have the same body and use the
-- same `Data.Fin._≟_`; they differ only in the module they're defined
-- in.  Pointwise equality follows by induction on the list.

count-correspond
  : ∀ {n} (v : Fin n) (xs : List (Fin n))
  → Lin.count v xs ≡ Comb.count v xs
count-correspond v []       = refl
count-correspond v (x ∷ xs) with v ≟ x
... | yes _ = cong suc (count-correspond v xs)
... | no  _ = count-correspond v xs

--------------------------------------------------------------------------------
-- ## Section 2: `producedList` / `consumedList` correspondence.
--
-- Both APROP and Combinatorial use the SAME definition body
-- (`H.dom ++ concat (tabulate H.eout)` etc.), but in different modules.
-- They are propositionally equal as definitions on `Hypergraph FlatGen`.

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
--
-- APROP `AllFire H (e ∷ es) s` has FOUR fields:
--   (rest , p , extract-prefix-eq , AllFire-tail)
-- Combinatorial `AllFire H (e ∷ es) s` has THREE fields:
--   (rest , p , AllFire-tail)
-- The drop direction is mechanical; the recompute direction uses
-- `extract-prefix-↭-residual` to recover a (possibly different)
-- `extract-prefix ≡ just (rest' , p')` evidence.

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

          -- Lift AllFire-tail from `eout e ++ rest` to `eout e ++ rest'`.
          -- We rely on Perm.++⁺ʳ to lift `rest ↭ rest'` to
          -- `eout e ++ rest ↭ eout e ++ rest'`.
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
    -- Local helper: `xs ++ ys ↭ xs ++ zs` from `ys ↭ zs`.
    perm-++-cong-right
      : ∀ {n} (xs : List (Fin n)) {ys zs : List (Fin n)}
      → ys Perm.↭ zs
      → (xs ++ ys) Perm.↭ (xs ++ zs)
    perm-++-cong-right []       p = p
    perm-++-cong-right (x ∷ xs) p = Perm.prep x (perm-++-cong-right xs p)

    -- Local helper: transport `Comb.AllFire H es s` along `s ↭ s'`.
    -- (The combinatorial AllFire is closed under perm of the stack:
    -- the locating perm `p : s ↭ ein e ++ rest` can be precomposed
    -- with the stack-↭.)
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
--
-- Constructive derivation of `SwapAtomResidual.swap-already-fires`
-- from a `LinearityCombinatorial` instance.  Pure combinatorics — no
-- SMC or correspondence-lemma content.

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
-- ## Section 6: Future-work documentation for atoms (1), (2), (4).
--
-- The fields `swap-atom-aligned`, `swap-with-rest-aligned`, and
-- `bridge-to-g-permute` of `APROPMacLaneAtoms` cannot YET be
-- constructively derived from `SMCMacLaneAtoms` because the bridge
-- requires a correspondence lemma between APROP's `process-edges`
-- (in `Decode.agda`) and SMC's `process-steps` (in
-- `Categories/FreeSMC/Steps.agda`).
--
-- The lemma's shape:
--
--   process-edges H es s ≡ <subst chain on map-++> (process-steps
--                            (map (edge→step H) es) (map H.vlab s)
--                            (lift-AllFire ...))
--
-- where `edge→step H e = (map H.vlab (H.ein e), map H.vlab (H.eout e),
--                          Agen-edge H e)`.
--
-- Estimated ~300-500 LOC of mechanical subst manipulation.  When
-- written, the bridges become one-liners:
--
--   swap-atom-aligned-from-SMC : SMCMacLaneAtoms → APROP shape
--   swap-atom-aligned-from-SMC smc H e₁ e₂ s indep =
--     correspondence-lemma ...  -- ports the SMC atom's output back
--
-- Until then, the SMC atoms in `Categories/FreeSMC/MacLaneAtoms.agda`
-- are AVAILABLE as a strictly-stronger trust surface (smaller atomic
-- statements, easier to discharge by a future `solveM-σ`), but they
-- do not yet feed back into the APROP c'-chain via this bridge.
--------------------------------------------------------------------------------
