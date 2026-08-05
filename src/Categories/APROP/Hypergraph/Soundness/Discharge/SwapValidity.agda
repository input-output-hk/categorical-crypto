-- `swap-validity` for `IsoInvarianceWiring.agda`'s `PerHG` module:
--
--   swap-validity : ∀ {o₁ o₂} → o₁ ↝ o₂ → Valid o₁ → Valid o₂
--
-- where `Valid o = (process-edges H o dom) Perm.↭ cod` and a step
-- `o₁ ↝ o₂` is `swap-step ps qs (inc : Incomp (Dep H) e e')` swapping an
-- adjacent `Dep`-incomparable pair after a prefix `ps`.
--
-- The final live-wire multiset is order-independent for such a swap, so
-- `Valid o₁` transports to `Valid o₂` by `Perm.↭`-transitivity.
--
-- Decomposition:
--
--   (1) `++-stack` (imported): reduces the general swap to a FRONT swap
--       (`ps = []`) on the shared post-prefix stack.
--
--   (2) `front-swap-stack-↭`, reduced (via `pe-stack-resp-↭`) to the
--       two-edge head bridge `two-edge-swap-stack-↭`, which case-splits
--       the four `extract-prefix` firing outcomes (both-skip / both-fire /
--       two firing-divergence cases) as flat clauses over the `EdgeStepR`
--       view of `edge-step`.
--
--   (3) `swap-validity` — (1) + (2) + `Perm.↭`-transitivity.
--
-- IMPORTANT: the firing-divergence case is FALSE under `Incomp` ALONE
-- (which constrains only `eout`-vs-`ein`, NOT `ein`-vs-`ein`): two `Incomp`
-- edges sharing an INPUT wire give different final stacks in the two orders
-- on a NON-linear `H`.  `PerHG` therefore takes `lin : Linear H`, under
-- which the `ein`s of distinct edges are count-disjoint, making `e'`'s
-- firing decision stable across the step.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.SwapValidity
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (process-edges; edge-step; edge-step-just; edge-step-nothing; extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig
  using (extract-prefix-↭-residual; extract-prefix-↭-nothing)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

-- Imported read-only: `PH.Valid`, `PH.↝`, `PH.Order`, and the LinExt
-- instantiation (`Incomp`, `swap-step`).
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig
  using (process-edges-++-stack)

-- Shared per-H combinatorics: firing stability + the both-fire multiset
-- bridge live in the `Sub/FireMidInterchangeComb` leaf (also consumed by
-- `Sub/RunInterchangeEmptyTail`).
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidInterchangeComb sig as FMIC

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H`, a `Dep`-irreflexivity witness `dih`, and
-- `lin : Linear H`.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H) where
  private module H = Hypergraph H

  -- The per-hypergraph module from the chain (read-only); we match its
  -- `Order`, `Valid`, `_↝_` definitionally.
  module PH = IW.PerHG H

  -- `Incomp e e' = (¬ Dep H e e') × (¬ Dep H e' e)` and the swap-step
  -- constructor, from the LinExt instantiation `PH.L`.
  open PH.L public using (Incomp; swap-step)

  private
    nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
    nothing≢just ()

  ------------------------------------------------------------------------
  -- The final stack of running an order from a stack (generalised over
  -- the starting stack `s`).
  ------------------------------------------------------------------------

  pe-stack : PH.Order → List (Fin H.nV) → List (Fin H.nV)
  pe-stack o s = (process-edges H o s)

  -- The final stack of `ps ++ rest` from `s` is that of `rest` from the
  -- post-`ps` stack.
  ++-stack
    : ∀ (ps rest : PH.Order) (s : List (Fin H.nV))
    → pe-stack (ps ++ rest) s ≡ pe-stack rest (pe-stack ps s)
  ++-stack = process-edges-++-stack H

  ------------------------------------------------------------------------
  -- (2) THE ANALYTIC CORE — front-of-stack two-edge stack permutation.
  --
  -- For `Dep`-INCOMPARABLE `e , e'`, running `e ∷ e' ∷ qs` from `s`
  -- reaches a `Perm.↭`-permutation of the result of `e' ∷ e ∷ qs`.
  --
  --   * `edge-step-stack-resp-↭` / `pe-stack-resp-↭` — the final-stack
  --     projection of `process-edges` respects `Perm.↭` of the starting
  --     stack (via `extract-prefix-↭-{residual,nothing}`).
  --   * `post-swap-stack-↭` — the both-fire multiset content is order
  --     independent (pure `_↭_` reasoning).
  --   * `front-swap-stack-↭` reduces (via `pe-stack-resp-↭`) to the
  --     two-edge head bridge `two-edge-swap-stack-↭`, itself the
  --     `EdgeStepR`-view split `two-edge-swap-gen` at the four graph
  --     witnesses.
  --
  -- The firing-divergence cases use firing-stability: under `lin` the
  -- `ein`s of distinct edges are count-disjoint (`ein-ein-disjoint`), and
  -- with `Incomp`'s `eout`-vs-`ein` disjointness, the `s ↝ eout e ++ r₁`
  -- step leaves every `ein e'`-vertex count unchanged (`count-ein'-pres`).
  -- Hence `e'`'s firing decision is stable across the step, collapsing the
  -- divergence branches to equal stacks or impossibilities.
  ------------------------------------------------------------------------

  -- The inductive graph of `edge-step` (the non-strict twin of
  -- `Interchange.EdgeStepRel.EdgeStepRˢ`).  Matching `skipR`/`fireR` refines
  -- the otherwise-stuck `edge-step` redex, so a case analysis over it needs
  -- neither a CPS continuation nor a `subst₂ Perm._↭_` transport: the output
  -- stack IS the constructor's index.
  data EdgeStepR (s : List (Fin H.nV)) (e : Fin H.nE)
       : List (Fin H.nV) → Set where
    skipR : extract-prefix (H.ein e) s ≡ nothing → EdgeStepR s e s
    fireR : ∀ (rest : List (Fin H.nV)) (perm : s Perm.↭ H.ein e ++ rest)
          → extract-prefix (H.ein e) s ≡ just (rest , perm)
          → EdgeStepR s e (H.eout e ++ rest)

  edge-step-graph
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE) → EdgeStepR s e (edge-step H s e)
  edge-step-graph s e with extract-prefix (H.ein e) s in eq
  ... | nothing            = skipR eq
  ... | just (rest , perm) = fireR rest perm eq

  -- Over the view: the `a`-side transport vanishes (the output stack IS the
  -- constructor index), leaving only the `b`-side reduction.
  edge-step-stack-resp-↭
    : ∀ {a b : List (Fin H.nV)} (e : Fin H.nE)
    → a Perm.↭ b
    → (edge-step H a e) Perm.↭ (edge-step H b e)
  edge-step-stack-resp-↭ {a} {b} e a↭b = go (edge-step-graph a e)
    where
      go : ∀ {x : List (Fin H.nV)} → EdgeStepR a e x → x Perm.↭ (edge-step H b e)
      -- `a` skips ⇒ `b` skips.
      go (skipR eqa) =
        subst (a Perm.↭_)
              (sym (edge-step-nothing H b e
                      (extract-prefix-↭-nothing (H.ein e) a b a↭b eqa)))
              a↭b
      -- `a` fires with residual `ra`; then `b` fires with `rb ↭ ra`, so the
      -- projected stacks are `++⁺ˡ`-related.
      go (fireR ra pa eqa) =
        subst ((H.eout e ++ ra) Perm.↭_)
              (sym (edge-step-just H b e (proj₁ (proj₂ (proj₂ stepb)))))
              (PermProp.++⁺ˡ (H.eout e) (proj₂ (proj₂ (proj₂ stepb))))
        where
          stepb = extract-prefix-↭-residual (H.ein e) b ra
                    (Perm.↭-trans (Perm.↭-sym a↭b) pa)

  pe-stack-resp-↭
    : ∀ (qs : PH.Order) {a b : List (Fin H.nV)}
    → a Perm.↭ b
    → pe-stack qs a Perm.↭ pe-stack qs b
  pe-stack-resp-↭ []       a↭b = a↭b
  pe-stack-resp-↭ (e ∷ qs) {a} {b} a↭b = pe-stack-resp-↭ qs (edge-step-stack-resp-↭ e a↭b)

  ------------------------------------------------------------------------
  -- BOTH-FIRE multiset bridge + FIRING STABILITY, shared with
  -- `Sub/RunInterchangeEmptyTail` via the `Sub/FireMidInterchangeComb`
  -- leaf: `post-swap-stack-↭` is the pure `_↭_` order-independence of
  -- the both-fire multiset content; `e'-fires-stable` / `e'-skips-stable`
  -- say `e'`'s firing decision is the same on `s` and on the post-`e`
  -- stack (under `Linear` + `Incomp` count-disjointness).
  ------------------------------------------------------------------------

  post-swap-stack-↭ = FMIC.post-swap-stack-↭ H dih lin

  private
    e'-fires-stable = FMIC.e'-fires-stable H dih lin
    e'-skips-stable = FMIC.e'-skips-stable H dih lin

  -- The four-way firing split at ABSTRACT stack indices, over the
  -- `EdgeStepR` view: the non-strict twin of
  -- `Interchange.SwapCoreRun.RunInterchange.build`, and flat for the same
  -- reason — each witness's output stack is its constructor's index, so the
  -- nine impossible combinations are one `⊥-elim` each and the three real
  -- ones need no transport.
  two-edge-swap-gen
    : ∀ {e e' : Fin H.nE} (e≢e' : ¬ (e ≡ e')) (inc : Incomp e e')
        (s : List (Fin H.nV))
        {a} (we  : EdgeStepR s e  a) {b} (we' : EdgeStepR a e' b)
        {c} (ue  : EdgeStepR s e' c) {d} (ue' : EdgeStepR c e  d)
    → b Perm.↭ d
  -- (1) e SKIPS s.
  two-edge-swap-gen e≢e' inc s (skipR eqe) (skipR eqe') (skipR _) (skipR _) =
    Perm.refl
  two-edge-swap-gen e≢e' inc s (skipR eqe) (skipR eqe') (fireR ur₂' up₂' ueqe') _ =
    ⊥-elim (nothing≢just (trans (sym eqe') ueqe'))
  two-edge-swap-gen e≢e' inc s (skipR eqe) (skipR eqe') (skipR ueqe')
                    (fireR ur₁ up₁ ueqe1) =
    ⊥-elim (nothing≢just (trans (sym eqe) ueqe1))
  two-edge-swap-gen e≢e' inc s (skipR eqe) (fireR r₂' p₂' eqe') (skipR eqe'-bad) _ =
    ⊥-elim (nothing≢just (trans (sym eqe'-bad) eqe'))
  two-edge-swap-gen e≢e' inc s (skipR eqe) (fireR r₂' p₂' eqe')
                    (fireR ur₂' up₂' ueqe') (fireR r₁' p₁' eqe1) =
    ⊥-elim (nothing≢just
      (trans (sym (e'-skips-stable (λ eq → e≢e' (sym eq)) (proj₂ inc)
                     ur₂' s up₂' eqe)) eqe1))
  two-edge-swap-gen e≢e' inc s (skipR eqe) (fireR r₂' p₂' eqe')
                    (fireR ur₂' up₂' ueqe') (skipR eqe1) =
    pin (just-injective (trans (sym ueqe') eqe'))
    where
      pin : (ur₂' , up₂') ≡ (r₂' , p₂') → _
      pin refl = Perm.refl
  -- (2) e FIRES s.
  two-edge-swap-gen e≢e' inc s (fireR r₁ p₁ eqe) (skipR eqe2)
                    (fireR ur₂' up₂' ueqe') _ =
    ⊥-elim (nothing≢just
      (trans (sym eqe2)
        (proj₂ (proj₂ (e'-fires-stable e≢e' (proj₁ inc) r₁ s p₁ ueqe')))))
  two-edge-swap-gen e≢e' inc s (fireR r₁ p₁ eqe) (skipR eqe2) (skipR eqe'n)
                    (skipR eqe-bad) =
    ⊥-elim (nothing≢just (trans (sym eqe-bad) eqe))
  two-edge-swap-gen e≢e' inc s (fireR r₁ p₁ eqe) (skipR eqe2) (skipR eqe'n)
                    (fireR ur₁ up₁ ueqe) =
    pin (just-injective (trans (sym ueqe) eqe))
    where
      pin : (ur₁ , up₁) ≡ (r₁ , p₁) → _
      pin refl = Perm.refl
  two-edge-swap-gen e≢e' inc s (fireR r₁ p₁ eqe) (fireR r₂ p₂ eqe2)
                    (skipR eqe'n) _ =
    ⊥-elim (nothing≢just
      (trans (sym (e'-skips-stable e≢e' (proj₁ inc) r₁ s p₁ eqe'n)) eqe2))
  two-edge-swap-gen e≢e' inc s (fireR r₁ p₁ eqe) (fireR r₂ p₂ eqe2)
                    (fireR r₂' p₂' eqe') (skipR eqe1) =
    ⊥-elim (nothing≢just
      (trans (sym eqe1)
        (proj₂ (proj₂
          (e'-fires-stable (λ eq → e≢e' (sym eq)) (proj₂ inc)
            r₂' s p₂' eqe)))))
  -- BOTH-FIRE — the genuine content.
  two-edge-swap-gen {e} {e'} e≢e' inc s (fireR r₁ p₁ eqe) (fireR r₂ p₂ eqe2)
                    (fireR r₂' p₂' eqe') (fireR r₁' p₁' eqe1) =
    post-swap-stack-↭ e e' s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁'

  two-edge-swap-stack-↭
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e') (s : List (Fin H.nV))
    → (edge-step H ((edge-step H s e )) e')
      Perm.↭
      (edge-step H ((edge-step H s e')) e )
  two-edge-swap-stack-↭ {e} {e'} inc s with e ≟ e'
  -- e ≡ e': the two orders are identical compositions.
  ... | yes refl = Perm.refl
  ... | no  e≢e' =
    two-edge-swap-gen e≢e' inc s
      (edge-step-graph s e) (edge-step-graph (edge-step H s e ) e')
      (edge-step-graph s e') (edge-step-graph (edge-step H s e') e )

  -- `front-swap-stack-↭` — threading the shared tail `qs` through
  -- `pe-stack-resp-↭` reduces to the two-edge head bridge.
  front-swap-stack-↭
    : ∀ (qs : PH.Order) {e e' : Fin H.nE}
        (inc : Incomp e e') (s : List (Fin H.nV))
    → pe-stack (e ∷ e' ∷ qs) s  Perm.↭  pe-stack (e' ∷ e ∷ qs) s
  front-swap-stack-↭ qs {e} {e'} inc s = pe-stack-resp-↭ qs (two-edge-swap-stack-↭ inc s)

  ------------------------------------------------------------------------
  -- (general swap) reduce to the front swap via `++-stack`, then apply
  -- `front-swap-stack-↭` at the shared post-prefix stack.
  ------------------------------------------------------------------------

  swap-stack-↭
    : ∀ (ps qs : PH.Order) {e e' : Fin H.nE} (inc : Incomp e e')
    → pe-stack (ps ++ e ∷ e' ∷ qs) H.dom
      Perm.↭ pe-stack (ps ++ e' ∷ e ∷ qs) H.dom
  swap-stack-↭ ps qs {e} {e'} inc =
    subst (Perm._↭ pe-stack (ps ++ e' ∷ e ∷ qs) H.dom)
          (sym (++-stack ps (e ∷ e' ∷ qs) H.dom))
      (subst (pe-stack (e ∷ e' ∷ qs) (pe-stack ps H.dom) Perm.↭_)
             (sym (++-stack ps (e' ∷ e ∷ qs) H.dom))
        (front-swap-stack-↭ qs inc (pe-stack ps H.dom)))

  ------------------------------------------------------------------------
  -- (3) `swap-validity`: transport `Valid` along `swap-stack-↭`.
  ------------------------------------------------------------------------

  swap-validity : ∀ {o₁ o₂ : PH.Order} → o₁ PH.↝ o₂ → PH.Valid o₁ → PH.Valid o₂
  swap-validity (swap-step ps qs inc) p₁ =
    Perm.↭-trans (Perm.↭-sym (swap-stack-↭ ps qs inc)) p₁
