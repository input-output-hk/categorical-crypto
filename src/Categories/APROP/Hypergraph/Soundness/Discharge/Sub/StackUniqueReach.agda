{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The stack-Uniqueness reachability invariant — the keystone supplying the
-- `Unique`-codomain witness the eval-coincidence family needs.
--
-- Per-edge-step `Unique`-preservation is FALSE for an arbitrary `Unique s`
-- (firing an edge whose `eout e` is already live duplicates a wire); it
-- holds ALONG `process-edges` because the running stack stays "fresh".
-- We capture that with a count invariant on the not-yet-processed edges `qs`:
--
--   Reservoir qs s  :=  ∀ v → count v s + count v (reservoir qs) ≤ 1
--      where reservoir qs = concat (map H.eout qs)
--
-- preserved by every step (SKIP shrinks the reservoir; FIRE moves `eout e`
-- from reservoir to stack).  It gives `count v s ≤ 1`, i.e. `Unique s`, at
-- every stage.  The bound flows entirely from the reservoir count, so the
-- lemma holds for an ARBITRARY edge list (instantiated at `range H.nE`).
-- The sole hypothesis `∀ v → count v (producedList H) ≤ 1` is the bound
-- half of `Linear H`, so `Linear H` alone suffices.
--
-- Downstream (`StackEquivariance`/`ResidualRecon`), the `Unique` codomain
-- `eval-rigid` requires is a `↭`-image of the decoder stack, supplied by
-- `Unique-resp-↭` once this lemma gives `Unique s`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach
  (sig : APROPSignature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹)
  renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.List using (List; []; _∷_; _++_; map; concat; tabulate)
open import Data.List.Properties using (++-identityʳ; map-++; concat-++)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (Maybe; just; nothing)

import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Linearity sig
  using (count; count-++; producedList)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (process-edges; edge-step; extract-prefix)

-- The uniqueness ⇔ count-bound bridge from `StackUnique`.
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig
  using (count≤1⇒Unique; Unique-resp-↭)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- 0.  `count`-cons reductions + `↭`-invariance (shared leaf).

open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.CountCombinatorics sig
  using (count-cons-yes; count-cons-no; ↭⇒count)

--------------------------------------------------------------------------------
-- Fix `H` and open it.

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- The reservoir: outputs of the not-yet-processed edges.
  reservoir : List (Fin H.nE) → List (Fin H.nV)
  reservoir qs = concat (map H.eout qs)

  -- The running invariant: stack + reservoir has every count ≤ 1.
  Reservoir≤1 : List (Fin H.nE) → List (Fin H.nV) → Set
  Reservoir≤1 qs s = ∀ v → count v s + count v (reservoir qs) ≤ⁿ 1

  ------------------------------------------------------------------------
  -- 1.  The single inductive lemma: the invariant is preserved by
  --     `process-edges`, and at every stage gives a stack count ≤ 1.

  -- The reservoir of `e ∷ qs` decomposes as `eout e ++ reservoir qs`.
  private
    reservoir-cons-count
      : ∀ (e : Fin H.nE) (qs : List (Fin H.nE)) (v : Fin H.nV)
      → count v (reservoir (e ∷ qs))
      ≡ count v (H.eout e) + count v (reservoir qs)
    reservoir-cons-count e qs v = count-++ v (H.eout e) (reservoir qs)

  ------------------------------------------------------------------------
  -- 1b.  The single-edge invariant advance.
  --   * `Reservoir≤1⇒Unique`   : the invariant bounds the stack count, so
  --     the stack is `Unique`.
  --   * `edge-step-Reservoir≤1` : the invariant survives one `edge-step`.

  Reservoir≤1⇒Unique
    : ∀ (qs : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 qs s → Unique s
  Reservoir≤1⇒Unique qs s inv =
    count≤1⇒Unique (λ v → Nat.≤-trans (Nat.m≤m+n (count v s) _) (inv v))

  edge-step-Reservoir≤1
    : ∀ (e : Fin H.nE) (qs : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 (e ∷ qs) s
    → Reservoir≤1 qs (proj₁ (edge-step H s e))
  edge-step-Reservoir≤1 e qs s inv
      with extract-prefix (H.ein e) s in eq
  ... | nothing = inv-skip
    where
      inv-skip : Reservoir≤1 qs s
      inv-skip w =
        Nat.≤-trans
          (Nat.+-monoʳ-≤ (count w s)
            (Nat.≤-trans (Nat.m≤n+m _ (count w (H.eout e)))
                         (Nat.≤-reflexive (sym (reservoir-cons-count e qs w)))))
          (inv w)
  ... | just (rest , perm) = inv-fire
    where
      inv-fire : Reservoir≤1 qs (H.eout e ++ rest)
      inv-fire w =
        Nat.≤-trans new≤old (inv w)
        where
          post-stack : count w (H.eout e ++ rest)
                     ≡ count w (H.eout e) + count w rest
          post-stack = count-++ w (H.eout e) rest
          pre-stack : count w s ≡ count w (H.ein e) + count w rest
          pre-stack = trans (↭⇒count perm w) (count-++ w (H.ein e) rest)
          lhs≡ : count w (H.eout e ++ rest) + count w (reservoir qs)
               ≡ (count w (H.eout e) + count w rest) + count w (reservoir qs)
          lhs≡ = cong (_+ count w (reservoir qs)) post-stack
          rhs≡ : count w s + count w (reservoir (e ∷ qs))
               ≡ (count w (H.ein e) + count w rest)
                 + (count w (H.eout e) + count w (reservoir qs))
          rhs≡ = cong₂ _+_ pre-stack (reservoir-cons-count e qs w)
          a = count w (H.eout e)
          b = count w rest
          c = count w (reservoir qs)
          d = count w (H.ein e)
          eq1 : (a + b) + c ≡ b + (a + c)
          eq1 = trans (cong (_+ c) (Nat.+-comm a b)) (Nat.+-assoc b a c)
          step2 : b + (a + c) ≤ⁿ (d + b) + (a + c)
          step2 = Nat.+-monoˡ-≤ (a + c) (Nat.m≤n+m b d)
          arith : (a + b) + c ≤ⁿ (d + b) + (a + c)
          arith = Nat.≤-trans (Nat.≤-reflexive eq1) step2
          new≤old : count w (H.eout e ++ rest) + count w (reservoir qs)
                  ≤ⁿ count w s + count w (reservoir (e ∷ qs))
          new≤old =
            Nat.≤-trans (Nat.≤-reflexive lhs≡)
              (Nat.≤-trans arith (Nat.≤-reflexive (sym rhs≡)))

  ------------------------------------------------------------------------
  -- 1c.  RESERVOIR-SPLIT.  A `Reservoir≤1 (ps ++ qs) s` invariant for the
  --      full edge list descends to a `Reservoir≤1 qs` invariant for the
  --      stack reached after running `ps` from `s` (iterating
  --      `edge-step-Reservoir≤1` along `ps`).

  reservoir-split
    : ∀ (ps qs : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 (ps ++ qs) s
    → Reservoir≤1 qs (proj₁ (process-edges H ps s))
  reservoir-split []        qs s inv = inv
  reservoir-split (e ∷ ps') qs s inv =
    reservoir-split ps' qs (proj₁ (edge-step H s e))
      (edge-step-Reservoir≤1 e (ps' ++ qs) s inv)

  ------------------------------------------------------------------------
  -- 2.  Bridge: `map H.eout (range nE) ≡ tabulate H.eout`, so the initial
  --     reservoir `reservoir (range nE)` is `concat (tabulate H.eout)`, and
  --     `producedList H = H.dom ++ concat (tabulate H.eout)`.

  private
    -- `map f (map suc xs) ≡ map (f ∘ suc) xs`.
    map-map-suc
      : ∀ {A : Set} {m} (f : Fin (suc m) → A) (xs : List (Fin m))
      → map f (map suc xs) ≡ map (λ i → f (suc i)) xs
    map-map-suc f []       = refl
    map-map-suc f (x ∷ xs) = cong (f (suc x) ∷_) (map-map-suc f xs)

    -- generic: `map f (range m) ≡ tabulate f`.
    map-range≡tabulate
      : ∀ {A : Set} {m} (f : Fin m → A)
      → map f (range m) ≡ tabulate f
    map-range≡tabulate {m = zero}  f = refl
    map-range≡tabulate {m = suc m} f =
      cong (f zero ∷_)
        (trans (map-map-suc f (range m)) (map-range≡tabulate (λ i → f (suc i))))

    reservoir-range≡concat-tabulate
      : reservoir (range H.nE) ≡ concat (tabulate H.eout)
    reservoir-range≡concat-tabulate =
      cong concat (map-range≡tabulate H.eout)

  ------------------------------------------------------------------------
  -- 3.  Initial reservoir condition from the `producedList` bound.

  private
    producedList-count
      : ∀ v → count v (producedList H)
            ≡ count v H.dom + count v (reservoir (range H.nE))
    producedList-count v =
      trans (count-++ v H.dom (concat (tabulate H.eout)))
            (cong (count v H.dom +_)
                  (cong (count v) (sym reservoir-range≡concat-tabulate)))

  ------------------------------------------------------------------------
  -- 3b.  PROVENANCE-SOURCED reservoir.  `Reservoir≤1 H o H.dom` is NOT
  --      true for an arbitrary order `o` (a repeated edge over-counts its
  --      `eout`), but IS true for `o ↭ range H.nE` — the orders the
  --      connectivity chase visits.  We thread that provenance and
  --      discharge the reservoir using `↭`-invariance of its per-vertex count.

  private
    -- Per-vertex count of `concat (map H.eout xs)` is `↭`-invariant in `xs`.
    reservoir-↭-count
      : ∀ {xs ys : List (Fin H.nE)} → xs Perm.↭ ys
      → ∀ v → count v (reservoir xs) ≡ count v (reservoir ys)
    reservoir-↭-count Perm.refl v = refl
    reservoir-↭-count (Perm.prep {xs = xs} {ys = ys} e p) v =
      trans (count-++ v (H.eout e) (reservoir xs))
      (trans (cong (count v (H.eout e) +_) (reservoir-↭-count p v))
             (sym (count-++ v (H.eout e) (reservoir ys))))
    reservoir-↭-count (Perm.swap {xs = xs} {ys = ys} e e' p) v =
      trans (count-++ v (H.eout e) (H.eout e' ++ reservoir xs))
      (trans (cong (count v (H.eout e) +_)
                   (count-++ v (H.eout e') (reservoir xs)))
      (trans (sym (Nat.+-assoc (count v (H.eout e)) (count v (H.eout e'))
                               (count v (reservoir xs))))
      (trans (cong (_+ count v (reservoir xs))
                   (Nat.+-comm (count v (H.eout e)) (count v (H.eout e'))))
      (trans (Nat.+-assoc (count v (H.eout e')) (count v (H.eout e))
                          (count v (reservoir xs)))
      (trans (cong (λ z → count v (H.eout e') + (count v (H.eout e) + z))
                   (reservoir-↭-count p v))
      (trans (cong (count v (H.eout e') +_)
                   (sym (count-++ v (H.eout e) (reservoir ys))))
             (sym (count-++ v (H.eout e') (H.eout e ++ reservoir ys)))))))))
    reservoir-↭-count (Perm.trans p₁ p₂) v =
      trans (reservoir-↭-count p₁ v) (reservoir-↭-count p₂ v)

  -- For any `o ↭ range H.nE`, the `dom`-reservoir invariant holds: its
  -- per-vertex count equals that of `range H.nE`, which is the
  -- `Linear`-backed `producedList` bound.
  dom-reservoir-prov
    : (∀ v → count v (producedList H) ≤ⁿ 1)
    → ∀ (o : List (Fin H.nE)) → o Perm.↭ range H.nE
    → Reservoir≤1 o H.dom
  dom-reservoir-prov prod-bnd o o↭range v =
    Nat.≤-trans
      (Nat.≤-reflexive
        (trans (cong (count v H.dom +_) (reservoir-↭-count o↭range v))
               (sym (producedList-count v))))
      (prod-bnd v)

  -- Prefix monotonicity: a `Reservoir≤1 (o ++ rest) s` invariant descends
  -- to its prefix `o` (dropping `rest` only shrinks each per-vertex count).
  private
    reservoir-++-count
      : ∀ (o rest : List (Fin H.nE)) (v : Fin H.nV)
      → count v (reservoir (o ++ rest))
      ≡ count v (reservoir o) + count v (reservoir rest)
    reservoir-++-count o rest v =
      trans (cong (count v)
                  (trans (cong concat (map-++ H.eout o rest))
                         (sym (concat-++ (map H.eout o) (map H.eout rest)))))
            (count-++ v (reservoir o) (reservoir rest))

  reservoir-prefix
    : ∀ (o rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 (o ++ rest) s → Reservoir≤1 o s
  reservoir-prefix o rest s inv v =
    Nat.≤-trans
      (Nat.+-monoʳ-≤ (count v s)
        (Nat.≤-trans
          (Nat.m≤m+n (count v (reservoir o)) (count v (reservoir rest)))
          (Nat.≤-reflexive (sym (reservoir-++-count o rest v)))))
      (inv v)

  -- Order-`↭`-invariance: a `Reservoir≤1 o₁ s` invariant transports along
  -- any `o₁ ↭ o₂` (the reservoir count depends only on the edge multiset).
  reservoir-resp-↭
    : ∀ {o₁ o₂ : List (Fin H.nE)} (s : List (Fin H.nV))
    → o₁ Perm.↭ o₂ → Reservoir≤1 o₁ s → Reservoir≤1 o₂ s
  reservoir-resp-↭ s o₁↭o₂ inv v =
    Nat.≤-trans
      (Nat.+-monoʳ-≤ (count v s)
        (Nat.≤-reflexive (sym (reservoir-↭-count o₁↭o₂ v))))
      (inv v)
