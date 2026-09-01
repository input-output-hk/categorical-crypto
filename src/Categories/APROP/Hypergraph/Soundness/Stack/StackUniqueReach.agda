{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The stack-Uniqueness reachability invariant — the keystone supplying the
-- `Unique`-codomain witness the stack-`≅↭` family needs.
--
-- Per-edge-step `Unique`-preservation is FALSE for an arbitrary `Unique s`
-- (firing an edge whose `eout e` is already live duplicates a wire); it
-- holds ALONG `process-edges` because the running stack stays "fresh".
-- We capture that with a 1-safety invariant on the stack together with the
-- not-yet-processed edges `qs`:
--
--   Reservoir≤1 qs s  :=  Unique (s ++ reservoir qs)
--      where reservoir qs = concat (map H.eout qs)
--
-- (equivalently `∀ v → count v s + count v (reservoir qs) ≤ 1`).  It is
-- preserved by every step (SKIP shrinks the reservoir; FIRE moves `eout e`
-- from reservoir to stack, discarding the consumed `ein e`).  It gives
-- `Unique s` at every stage.  The invariant holds for an ARBITRARY edge list
-- (instantiated at `range H.nE`); the sole hypothesis
-- `∀ v → count v (producedList H) ≤ 1` is the bound half of `Linear H`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach
  (sig : APROPSignature) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; concat; tabulate)
open import Data.List.Properties using (map-++; concat-++; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)

open Perm using (_↭_)


open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (count; count-++; producedList)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (process-edges; edge-step; extract-prefix)

open import Data.Nat using () renaming (_≤_ to _≤ⁿ_)
import Data.Nat.Properties as Nat

open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig
  using (count≤1⇒Unique; Unique⇒count≤1; Unique-resp-↭)

private
  variable
    n : ℕ

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  reservoir : List (Fin H.nE) → List (Fin H.nV)
  reservoir qs = concat (map H.eout qs)

  Reservoir≤1 : List (Fin H.nE) → List (Fin H.nV) → Set
  Reservoir≤1 qs s = Unique (s ++ reservoir qs)

  ------------------------------------------------------------------------
  -- 0.  Shared list/permutation algebra of `reservoir` and `Unique`-of-`++`.

  private
    -- `concat` respects `↭` (not in stdlib).
    concat-↭ : {L₁ L₂ : List (List (Fin H.nV))} → L₁ ↭ L₂ → concat L₁ ↭ concat L₂
    concat-↭ Perm.refl       = Perm.refl
    concat-↭ (Perm.prep x p) = PermProp.++⁺ˡ x (concat-↭ p)
    concat-↭ (Perm.swap {xs} {ys} x y p) =
      Perm.trans (Perm.↭-reflexive (sym (++-assoc x y (concat xs))))
        (Perm.trans (PermProp.++⁺ʳ (concat xs) (PermProp.++-comm x y))
          (Perm.trans (Perm.↭-reflexive (++-assoc y x (concat xs)))
            (PermProp.++⁺ˡ y (PermProp.++⁺ˡ x (concat-↭ p)))))
    concat-↭ (Perm.trans p q) = Perm.trans (concat-↭ p) (concat-↭ q)

    reservoir-↭ : {xs ys : List (Fin H.nE)} → xs ↭ ys → reservoir xs ↭ reservoir ys
    reservoir-↭ p = concat-↭ (PermProp.map⁺ H.eout p)

    reservoir-++ : ∀ (o rest : List (Fin H.nE))
                 → reservoir (o ++ rest) ≡ reservoir o ++ reservoir rest
    reservoir-++ o rest =
      trans (cong concat (map-++ H.eout o rest)) (sym (concat-++ (map H.eout o) (map H.eout rest)))

    -- `Unique`-of-`++` splitting (stdlib lacks `++⁻`; via the count bridge).
    Unique-++ˡ : ∀ {xs ys : List (Fin H.nV)} → Unique (xs ++ ys) → Unique xs
    Unique-++ˡ {xs} {ys} u = count≤1⇒Unique λ v →
      Nat.≤-trans (Nat.m≤m+n (count v xs) (count v ys))
        (Nat.≤-trans (Nat.≤-reflexive (sym (count-++ v xs ys))) (Unique⇒count≤1 u v))

    Unique-++ʳ : ∀ {xs ys : List (Fin H.nV)} → Unique (xs ++ ys) → Unique ys
    Unique-++ʳ {xs} {ys} u = count≤1⇒Unique λ v →
      Nat.≤-trans (Nat.m≤n+m (count v ys) (count v xs))
        (Nat.≤-trans (Nat.≤-reflexive (sym (count-++ v xs ys))) (Unique⇒count≤1 u v))

  ------------------------------------------------------------------------
  -- 1.  The invariant gives a `Unique` stack, and is preserved by a step.

  Reservoir≤1⇒Unique
    : ∀ (qs : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 qs s → Unique s
  Reservoir≤1⇒Unique qs s inv = Unique-++ˡ inv

  edge-step-Reservoir≤1
    : ∀ (e : Fin H.nE) (qs : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 (e ∷ qs) s
    → Reservoir≤1 qs ((edge-step H s e))
  edge-step-Reservoir≤1 e qs s inv with extract-prefix (H.ein e) s in eq
  -- SKIP: the stack is unchanged; drop the unfired `eout e` from the middle.
  ... | nothing =
        Unique-++ʳ {xs = H.eout e}
          (Unique-resp-↭ (skip-↭ s) inv)
    where
      -- s ++ (eout e ++ reservoir qs)  ↭  eout e ++ (s ++ reservoir qs)
      skip-↭ : ∀ (s : List (Fin H.nV))
             → s ++ (H.eout e ++ reservoir qs) ↭ H.eout e ++ (s ++ reservoir qs)
      skip-↭ s = PermProp.shifts s (H.eout e)
  -- FIRE: `s ↭ ein e ++ rest`; the fired stack is `eout e ++ rest`, and the
  -- consumed `ein e` is dropped.
  ... | just (rest , perm) =
        Unique-++ʳ {xs = H.ein e}
          (Unique-resp-↭ fire-↭ inv)
    where
      -- s ++ (eout e ++ res)  ↭  ein e ++ ((eout e ++ rest) ++ res)
      fire-↭ : s ++ (H.eout e ++ reservoir qs)
             ↭ H.ein e ++ ((H.eout e ++ rest) ++ reservoir qs)
      fire-↭ =
        Perm.trans (PermProp.++⁺ʳ (H.eout e ++ reservoir qs) perm)
          (Perm.trans (Perm.↭-reflexive (++-assoc (H.ein e) rest (H.eout e ++ reservoir qs)))
            (PermProp.++⁺ˡ (H.ein e)
              (Perm.trans (Perm.↭-reflexive (sym (++-assoc rest (H.eout e) (reservoir qs))))
                          (PermProp.++⁺ʳ (reservoir qs) (PermProp.++-comm rest (H.eout e))))))

  ------------------------------------------------------------------------
  -- 2.  Descend the invariant along a processed prefix.

  reservoir-split
    : ∀ (ps qs : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 (ps ++ qs) s
    → Reservoir≤1 qs ((process-edges H ps s))
  reservoir-split []        qs s inv = inv
  reservoir-split (e ∷ ps') qs s inv =
    reservoir-split ps' qs ((edge-step H s e))
      (edge-step-Reservoir≤1 e (ps' ++ qs) s inv)

  ------------------------------------------------------------------------
  -- 3.  Bridge: the initial reservoir `reservoir (range nE)` is
  --     `concat (tabulate H.eout)`, so `producedList H = H.dom ++ reservoir
  --     (range nE)`.

  private
    map-map-suc
      : ∀ {A : Set} {m} (f : Fin (suc m) → A) (xs : List (Fin m))
      → map f (map suc xs) ≡ map (λ i → f (suc i)) xs
    map-map-suc f []       = refl
    map-map-suc f (x ∷ xs) = cong (f (suc x) ∷_) (map-map-suc f xs)

    map-range≡tabulate
      : ∀ {A : Set} {m} (f : Fin m → A)
      → map f (range m) ≡ tabulate f
    map-range≡tabulate {m = zero}  f = refl
    map-range≡tabulate {m = suc m} f =
      cong (f zero ∷_)
        (trans (map-map-suc f (range m)) (map-range≡tabulate (λ i → f (suc i))))

    reservoir-range≡producedList
      : H.dom ++ reservoir (range H.nE) ≡ producedList H
    reservoir-range≡producedList =
      cong (H.dom ++_) (cong concat (map-range≡tabulate H.eout))

  ------------------------------------------------------------------------
  -- 4.  PROVENANCE-SOURCED reservoir.  `Reservoir≤1 o H.dom` is NOT true for
  --     an arbitrary order `o` (a repeated edge duplicates its `eout`), but
  --     IS true for `o ↭ range H.nE`.

  dom-reservoir-prov
    : (∀ v → count v (producedList H) ≤ⁿ 1)
    → ∀ (o : List (Fin H.nE)) → o Perm.↭ range H.nE
    → Reservoir≤1 o H.dom
  dom-reservoir-prov prod-bnd o o↭range =
    Unique-resp-↭
      (PermProp.++⁺ˡ H.dom (reservoir-↭ (Perm.↭-sym o↭range)))
      (subst Unique (sym reservoir-range≡producedList) (count≤1⇒Unique prod-bnd))

  reservoir-prefix
    : ∀ (o rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 (o ++ rest) s → Reservoir≤1 o s
  reservoir-prefix o rest s inv =
    Unique-++ˡ {xs = s ++ reservoir o}
      (Unique-resp-↭ split-↭ inv)
    where
      -- s ++ reservoir (o ++ rest)  ↭  (s ++ reservoir o) ++ reservoir rest
      split-↭ : s ++ reservoir (o ++ rest) ↭ (s ++ reservoir o) ++ reservoir rest
      split-↭ =
        Perm.trans (Perm.↭-reflexive (cong (s ++_) (reservoir-++ o rest)))
                   (Perm.↭-reflexive (sym (++-assoc s (reservoir o) (reservoir rest))))

  reservoir-resp-↭
    : ∀ {o₁ o₂ : List (Fin H.nE)} (s : List (Fin H.nV))
    → o₁ Perm.↭ o₂ → Reservoir≤1 o₁ s → Reservoir≤1 o₂ s
  reservoir-resp-↭ s o₁↭o₂ inv =
    Unique-resp-↭ (PermProp.++⁺ˡ s (reservoir-↭ o₁↭o₂)) inv
