{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- The stack-Uniqueness REACHABILITY invariant — the KEYSTONE that supplies the
-- `Unique`-codomain witness the eval-coincidence family (`residual-recon`,
-- `located-fixes-0`, `coh-in`/`coh-out`) needs.
--
-- ## What is proved
--
-- `pe-stack-Unique : (∀ v → count v (producedList H) ≤ 1)`
--                  → `Unique (proj₁ (process-edges H (range H.nE) H.dom))`
--
-- i.e. the natural-order decoder run, started at the dom stack, ends with a
-- `Unique` stack — under the SOLE hypothesis that `producedList H` has every
-- count ≤ 1.  That hypothesis is exactly the *bound* half of `Linear H`
-- (`proj₂ lin`), so `Linear H` ALONE suffices: no `⟪f⟫`/`FromAPROP` structure
-- is needed beyond what `Linear` already packages, and at `H = ⟪ f ⟫` it is
-- discharged by `Linearity.⟪⟫-Linear` (or its `DecodeAttemptLinearP` proof).
--
-- ## The reservoir invariant (why `disj` holds along the run)
--
-- `StackUnique` documents that per-edge-step `Unique`-preservation is FALSE for
-- an arbitrary `Unique s`: firing an edge whose `eout e` is already live
-- duplicates a wire.  It holds ALONG `process-edges` because the running stack
-- is "fresh".  We make that precise with a single count invariant on the
-- running edge list `qs` (the edges NOT YET processed):
--
--   Reservoir qs s  :=  ∀ v → count v s + count v (reservoir qs) ≤ 1
--      where reservoir qs = concat (map H.eout qs)
--
-- This is preserved by every `process-edges` step:
--
--   * SKIP (e doesn't fire): the stack is unchanged and the reservoir SHRINKS
--     by `eout e`, so `count v s + count v (reservoir qs)
--        ≤ count v s + count v (eout e ++ reservoir qs) ≤ 1`.
--   * FIRE (e fires, `s ↭ ein e ++ rest`): the new stack is `eout e ++ rest`;
--     since `count v s = count v (ein e) + count v rest`, the post-step sum
--     `count v (eout e ++ rest) + count v (reservoir qs)
--        = count v (eout e) + count v rest + count v (reservoir qs)
--        ≤ count v (ein e) + count v rest + count v (eout e)
--          + count v (reservoir qs)  =  pre-step sum  ≤ 1`.
--
-- The invariant trivially gives `count v s ≤ 1`, i.e. `Unique s`, at every
-- stage — in particular at the end.  No DISTINCTNESS of the edges in `qs` is
-- needed: the bound flows entirely from the reservoir count, so the lemma holds
-- for an ARBITRARY edge list (we then instantiate at `range H.nE`).
--
-- ## How it closes the eval-coincidence family
--
-- At the `StackEquivariance` / `ResidualRecon` call sites the codomain whose
-- `Unique`-ness `eval-rigid` requires is a `↭`-IMAGE of the decoder stack `s'`:
--   * `residual-recon (ein e) s' restH (trans ρ permH)` needs
--     `Unique (ein e ++ restH)` — and `s' ↭ ein e ++ restH`, so
--     `Unique-resp-↭ (trans ρ permH) (Unique s')` from `StackUnique` supplies it
--     once `Unique s'` is in hand.
--   * `located-fixes-0` / `coh-in` / `coh-out` (in `ExtractElemEval`) compare two
--     `↭`s with the SAME stack-image codomain; `coh-fin-rigid`/`eval-rigid`
--     close them given that same `Unique` witness.
-- This module is the source of `Unique s'`: threaded by giving
-- `StackEquivariance.process-edges-equivariant` a `Unique s` hypothesis, which
-- this lemma discharges at `H = ⟪ f ⟫`, `s = dom`, `qs = range nE`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach
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
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (count; count-++; producedList)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; extract-prefix)

-- Re-use the (postulate-free) uniqueness ⇔ count-bound bridge from `StackUnique`.
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique sig
  using (count≤1⇒Unique; Unique-resp-↭)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- 0.  `count`-cons reductions + `↭`-invariance (re-derived; the copies in
--     `Linearity`/`StackUnique`/`SwapValidity` are `private`).

private
  count-cons-yes : (v : Fin n) (xs : List (Fin n))
                 → count v (v ∷ xs) ≡ suc (count v xs)
  count-cons-yes v xs with v ≟ v
  ... | yes _ = refl
  ... | no  q = ⊥-elim (q refl)

  count-cons-no : (v x : Fin n) (xs : List (Fin n)) → ¬ (v ≡ x)
                → count v (x ∷ xs) ≡ count v xs
  count-cons-no v x xs v≢x with v ≟ x
  ... | yes p = ⊥-elim (v≢x p)
  ... | no  _ = refl

  ↭⇒count : {xs ys : List (Fin n)} → xs Perm.↭ ys → ∀ v → count v xs ≡ count v ys
  ↭⇒count Perm.refl                       v = refl
  ↭⇒count (Perm.prep x p)                 v with v ≟ x
  ... | yes _ = cong suc (↭⇒count p v)
  ... | no  _ = ↭⇒count p v
  ↭⇒count (Perm.swap {xs = xs} {ys = ys} x y p) v = swap-case (v ≟ x) (v ≟ y)
    where
      swap-case : _ → _ → count v (x ∷ y ∷ xs) ≡ count v (y ∷ x ∷ ys)
      swap-case (yes refl) (yes refl) =
        trans (count-cons-yes v (v ∷ xs))
        (trans (cong suc (count-cons-yes v xs))
        (trans (cong suc (cong suc (↭⇒count p v)))
        (trans (cong suc (sym (count-cons-yes v ys)))
               (sym (count-cons-yes v (v ∷ ys))))))
      swap-case (yes refl) (no  q) =
        trans (count-cons-yes v (y ∷ xs))
        (trans (cong suc (count-cons-no v y xs q))
        (trans (cong suc (↭⇒count p v))
        (trans (sym (count-cons-yes v ys))
               (sym (count-cons-no v y (v ∷ ys) q)))))
      swap-case (no  q) (yes refl) =
        trans (count-cons-no v x (v ∷ xs) q)
        (trans (count-cons-yes v xs)
        (trans (cong suc (↭⇒count p v))
        (trans (cong suc (sym (count-cons-no v x ys q)))
               (sym (count-cons-yes v (x ∷ ys))))))
      swap-case (no  q₁) (no  q₂) =
        trans (count-cons-no v x (y ∷ xs) q₁)
        (trans (count-cons-no v y xs q₂)
        (trans (↭⇒count p v)
        (trans (sym (count-cons-no v x ys q₁))
               (sym (count-cons-no v y (x ∷ ys) q₂)))))
  ↭⇒count (Perm.trans p₁ p₂)              v = trans (↭⇒count p₁ v) (↭⇒count p₂ v)

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

  -- The CORE: under the reservoir invariant, the final stack of
  -- `process-edges H qs s` again satisfies the invariant for the EMPTY
  -- remaining edge list — i.e. its plain count is ≤ 1.
  process-edges-count≤1
    : ∀ (qs : List (Fin H.nE)) (s : List (Fin H.nV))
    → Reservoir≤1 qs s
    → ∀ v → count v (proj₁ (process-edges H qs s)) ≤ⁿ 1
  -- Base: no edges left.  The reservoir is `[]`, so `count v s + 0 ≤ 1`
  -- gives `count v s ≤ 1`, and `process-edges H [] s = (s , id)`.
  process-edges-count≤1 [] s inv v =
    Nat.≤-trans (Nat.≤-reflexive (sym (Nat.+-identityʳ (count v s)))) (inv v)
  -- Step: split on whether edge `e` fires (matches `Decode.edge-step`).
  process-edges-count≤1 (e ∷ qs) s inv v
      with extract-prefix (H.ein e) s in eq
  -- SKIP: `edge-step H s e = (s , id)`, so we recurse on `qs` from the
  -- SAME stack `s`; the reservoir shrinks by `eout e`, so the invariant
  -- for `qs , s` follows from the one for `e ∷ qs , s` by monotonicity.
  ... | nothing =
        process-edges-count≤1 qs s inv-skip v
    where
      inv-skip : Reservoir≤1 qs s
      inv-skip w =
        Nat.≤-trans
          (Nat.+-monoʳ-≤ (count w s)
            (Nat.≤-trans (Nat.m≤n+m _ (count w (H.eout e)))
                         (Nat.≤-reflexive (sym (reservoir-cons-count e qs w)))))
          (inv w)
  -- FIRE: `edge-step H s e = (eout e ++ rest , _)` with
  -- `perm : s ↭ ein e ++ rest`.  We recurse on `qs` from `eout e ++ rest`;
  -- the new invariant follows because, per vertex,
  --   count w (eout e ++ rest) + count w (reservoir qs)
  --     ≤ count w (ein e ++ rest) + count w (eout e) + count w (reservoir qs)
  --     = count w s + count w (reservoir (e ∷ qs))   [perm + reservoir-cons]
  --     ≤ 1.
  ... | just (rest , perm) =
        process-edges-count≤1 qs (H.eout e ++ rest) inv-fire v
    where
      inv-fire : Reservoir≤1 qs (H.eout e ++ rest)
      inv-fire w =
        Nat.≤-trans new≤old (inv w)
        where
          -- post-fire stack count = eout + rest.
          post-stack : count w (H.eout e ++ rest)
                     ≡ count w (H.eout e) + count w rest
          post-stack = count-++ w (H.eout e) rest

          -- pre-fire stack count = ein + rest  (via `perm`).
          pre-stack : count w s ≡ count w (H.ein e) + count w rest
          pre-stack = trans (↭⇒count perm w) (count-++ w (H.ein e) rest)

          -- LHS = (eout + rest) + reservoir qs.
          lhs≡ : count w (H.eout e ++ rest) + count w (reservoir qs)
               ≡ (count w (H.eout e) + count w rest) + count w (reservoir qs)
          lhs≡ = cong (_+ count w (reservoir qs)) post-stack

          -- RHS = count s + reservoir (e ∷ qs)
          --     = (ein + rest) + (eout + reservoir qs).
          rhs≡ : count w s + count w (reservoir (e ∷ qs))
               ≡ (count w (H.ein e) + count w rest)
                 + (count w (H.eout e) + count w (reservoir qs))
          rhs≡ = cong₂ _+_ pre-stack (reservoir-cons-count e qs w)

          -- The arithmetic core: (eout + rest) + res
          --                       ≤ (ein + rest) + (eout + res).
          -- Abbreviations.
          a = count w (H.eout e)
          b = count w rest
          c = count w (reservoir qs)
          d = count w (H.ein e)

          -- (a + b) + c ≡ b + (a + c).
          eq1 : (a + b) + c ≡ b + (a + c)
          eq1 =
            trans (cong (_+ c) (Nat.+-comm a b))
                  (Nat.+-assoc b a c)

          -- b + (a + c) ≤ (d + b) + (a + c)   [add 0 ≤ d on the left summand].
          step2 : b + (a + c) ≤ⁿ (d + b) + (a + c)
          step2 = Nat.+-monoˡ-≤ (a + c) (Nat.m≤n+m b d)

          arith : (a + b) + c ≤ⁿ (d + b) + (a + c)
          arith = Nat.≤-trans (Nat.≤-reflexive eq1) step2

          new≤old : count w (H.eout e ++ rest) + count w (reservoir qs)
                  ≤ⁿ count w s + count w (reservoir (e ∷ qs))
          new≤old =
            Nat.≤-trans
              (Nat.≤-reflexive lhs≡)
              (Nat.≤-trans arith (Nat.≤-reflexive (sym rhs≡)))

  ------------------------------------------------------------------------
  -- 1b.  The SINGLE-EDGE invariant advance (the `inv-skip`/`inv-fire`
  --      step of `process-edges-count≤1`, factored out so the
  --      `StackEquivariance.process-edges-equivariant` recursion can
  --      thread the invariant across one `edge-step` and recover
  --      `Unique` of every running stack along the way).
  --
  --   * `Reservoir≤1⇒Unique`  : the invariant for the running stack
  --      bounds its plain count by 1, hence `Unique`.
  --   * `edge-step-Reservoir≤1` : the invariant survives one `edge-step`
  --      (SKIP keeps the stack, FIRE replaces it by `eout e ++ rest`).

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
  -- 1c.  RESERVOIR-SPLIT — the GLOBAL reservoir specialises to a mid-run
  --      context.  Iterating `edge-step-Reservoir≤1` along a prefix `ps`,
  --      a `Reservoir≤1 (ps ++ qs) s` invariant for the full edge list
  --      descends to a `Reservoir≤1 qs` invariant for the stack reached
  --      AFTER running `ps` from `s`.  This lets a `Linear`-sourced GLOBAL
  --      reservoir feed any mid-run `(qs , pe-stack ps s)`.
  --
  --   * `ps = []`     : `process-edges [] s = (s , id)` and `[] ++ qs = qs`,
  --     so the invariant is unchanged.
  --   * `ps = e ∷ ps'`: `(e ∷ ps') ++ qs = e ∷ (ps' ++ qs)`; one
  --     `edge-step-Reservoir≤1` advances `s` to `proj₁ (edge-step H s e)`
  --     and drops the head edge, then recurse on `ps'` (the running stack
  --     of `process-edges (e ∷ ps') s` is exactly `process-edges ps'
  --     (proj₁ (edge-step H s e))` definitionally).

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
  -- 3.  THE KEYSTONE.  Started at `H.dom` over the natural edge order
  --     `range H.nE`, with `producedList H` count-bounded, the final stack
  --     is `Unique`.

  -- Initial reservoir condition from the `producedList` bound.
  private
    producedList-count
      : ∀ v → count v (producedList H)
            ≡ count v H.dom + count v (reservoir (range H.nE))
    producedList-count v =
      trans (count-++ v H.dom (concat (tabulate H.eout)))
            (cong (count v H.dom +_)
                  (cong (count v) (sym reservoir-range≡concat-tabulate)))

  -- `pe-stack-Unique` — the deliverable.  Hypothesis is exactly the
  -- *bound* half of `Linear H` (`proj₂ lin`); no other structure is used.
  pe-stack-Unique
    : (∀ v → count v (producedList H) ≤ⁿ 1)
    → Unique (proj₁ (process-edges H (range H.nE) H.dom))
  pe-stack-Unique prod-bnd =
    count≤1⇒Unique
      (process-edges-count≤1 (range H.nE) H.dom inv-init)
    where
      inv-init : Reservoir≤1 (range H.nE) H.dom
      inv-init v =
        Nat.≤-trans
          (Nat.≤-reflexive (sym (producedList-count v)))
          (prod-bnd v)

  ------------------------------------------------------------------------
  -- 3b.  PROVENANCE-SOURCED reservoir.  The `Reservoir≤1 H o H.dom`
  --      invariant is NOT true for an arbitrary edge order `o` (a repeated
  --      edge over-counts its `eout` in the reservoir).  But it IS true for
  --      every order `o` that is a PERMUTATION of `range H.nE` — exactly the
  --      orders the downstream connectivity chase visits (each `↝` swap is
  --      an adjacent transposition, preserving the multiset).  We thread
  --      that provenance `o ↭ range nE` here and discharge the reservoir
  --      from the `Linear`-backed `range`-order bound (`pe-stack-Unique`'s
  --      `inv-init`), using `↭`-invariance of the reservoir's per-vertex
  --      count.

  private
    -- Per-vertex count of `concat (map H.eout xs)` is `↭`-invariant in
    -- `xs` (a "weighted" version of the `↭⇒count` lemma above, weight
    -- `count v (H.eout ·)`).  Inducts on the `↭`-derivation; each step
    -- rearranges the `concat`/`++` blocks with `count-++` + arithmetic.
    reservoir-↭-count
      : ∀ {xs ys : List (Fin H.nE)} → xs Perm.↭ ys
      → ∀ v → count v (reservoir xs) ≡ count v (reservoir ys)
    reservoir-↭-count Perm.refl v = refl
    reservoir-↭-count (Perm.prep {xs = xs} {ys = ys} e p) v =
      trans (count-++ v (H.eout e) (reservoir xs))
      (trans (cong (count v (H.eout e) +_) (reservoir-↭-count p v))
             (sym (count-++ v (H.eout e) (reservoir ys))))
    reservoir-↭-count (Perm.swap {xs = xs} {ys = ys} e e' p) v =
      -- reservoir (e ∷ e' ∷ xs) = eout e ++ (eout e' ++ reservoir xs)
      -- reservoir (e' ∷ e ∷ ys) = eout e' ++ (eout e ++ reservoir ys)
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

  -- THE PROVENANCE-SOURCED reservoir.  For any order `o ↭ range H.nE`, the
  -- `dom`-reservoir invariant holds — the per-vertex reservoir count of `o`
  -- equals that of `range H.nE` (`reservoir-↭-count`), and the `range`-order
  -- bound `count v dom + count v (reservoir (range nE)) ≤ 1` is exactly the
  -- `Linear`-backed `producedList` bound (`producedList-count` + `prod-bnd`).
  --
  -- This is the SOUND replacement for the (FALSE-as-stated) `∀ o → …`
  -- reservoir: the `o ↭ range` hypothesis is the missing side condition.
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

  -- PREFIX MONOTONICITY of the `dom`-reservoir.  A `Reservoir≤1` invariant
  -- for the full order `o ++ rest` descends to its prefix `o`: the
  -- reservoir of `o` is a sub-multiset of that of `o ++ rest`
  -- (`reservoir (o ++ rest) = reservoir o ++ reservoir rest`), so every
  -- per-vertex count only shrinks when `rest` is dropped, keeping the
  -- bound ≤ 1.  This lets a swap-site reservoir feed the truncated orders
  -- `ps` / `ps ++ e' ∷ e ∷ []` that the empty-tail core consumes.
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

  ------------------------------------------------------------------------
  -- 4.  Eval-coincidence interface — the `Unique` codomain witnesses.
  --
  -- `process-edges-stack-Unique-from-↭` packages exactly what the
  -- `residual-recon` / `located-fixes-0` / `coh-in`/`coh-out` call sites
  -- need: given the final stack is `Unique` (from `pe-stack-Unique`) and a
  -- `↭` from it to the comparison codomain `cod-list` (`ein e ++ restH`,
  -- `eout e ++ r₁`, …), `Unique cod-list` follows by `Unique-resp-↭`.

  -- Generic transport (the `StackEquivariance` half₂ shape): the codomain
  -- `ein e ++ restH` is a `↭`-image of the stack `s'`, so given `Unique s'`
  -- it is itself `Unique` and `eval-rigid` (via `residual-recon-unique` in
  -- `StackUnique`) closes the comparison.
  stack-↭-codomain-Unique
    : ∀ {s' cod-list : List (Fin H.nV)}
    → Unique s' → s' Perm.↭ cod-list → Unique cod-list
  stack-↭-codomain-Unique us' ρ = Unique-resp-↭ ρ us'

--------------------------------------------------------------------------------
-- ## Residual / verdict
--
-- The keystone `pe-stack-Unique` is PROVEN with the SOLE hypothesis
-- `∀ v → count v (producedList H) ≤ 1`, which is `proj₂ (lin : Linear H)`.
-- Hence `Linear H` ALONE suffices — NO `⟪f⟫`/`FromAPROP` structure is needed
-- (the natural-order run `range H.nE` and the dom-stack are the only
-- specialisations; the reservoir invariant tolerates an ARBITRARY edge list,
-- so even distinct-edges is not required).  At `H = ⟪ f ⟫` the hypothesis is
-- the REAL `Linearity.⟪⟫-Linear` (its `proj₂`), so the lemma is honestly leaf-
-- free: there is NO residual postulate.
--------------------------------------------------------------------------------
