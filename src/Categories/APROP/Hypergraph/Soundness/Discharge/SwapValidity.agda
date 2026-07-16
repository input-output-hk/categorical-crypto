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
--       two firing-divergence cases).
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
  using (process-edges; edge-step; extract-prefix)
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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

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
  --     two-edge head bridge `two-edge-swap-stack-↭`.
  --
  -- The firing-divergence cases use firing-stability: under `lin` the
  -- `ein`s of distinct edges are count-disjoint (`ein-ein-disjoint`), and
  -- with `Incomp`'s `eout`-vs-`ein` disjointness, the `s ↝ eout e ++ r₁`
  -- step leaves every `ein e'`-vertex count unchanged (`count-ein'-pres`).
  -- Hence `e'`'s firing decision is stable across the step, collapsing the
  -- divergence branches to equal stacks or impossibilities.
  ------------------------------------------------------------------------

  -- `(edge-step H s e)` characterised by the `extract-prefix`
  -- outcome (so we reason about it without unfolding the internal `with`).
  step-stack-skip
    : ∀ (e : Fin H.nE) (s : List (Fin H.nV))
    → extract-prefix (H.ein e) s ≡ nothing
    → (edge-step H s e) ≡ s
  step-stack-skip e s eq with extract-prefix (H.ein e) s
  ... | nothing = refl

  step-stack-fire
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
        (p : s Perm.↭ H.ein e ++ rest)
    → extract-prefix (H.ein e) s ≡ just (rest , p)
    → (edge-step H s e) ≡ H.eout e ++ rest
  step-stack-fire e s rest p eq with extract-prefix (H.ein e) s
  ... | just _ = cong (λ x → H.eout e ++ proj₁ x) (just-inj eq)
    where
      just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
      just-inj refl = refl

  -- Case on `extract-prefix (H.ein e) a` without abstracting the goal,
  -- so `(edge-step H a e)` stays literal and `step-stack-*` apply.
  edge-step-stack-resp-↭
    : ∀ {a b : List (Fin H.nV)} (e : Fin H.nE)
    → a Perm.↭ b
    → (edge-step H a e) Perm.↭ (edge-step H b e)
  edge-step-stack-resp-↭ {a} {b} e a↭b =
    go (extract-prefix (H.ein e) a) refl
    where
      go : (m : Maybe (Σ[ rest ∈ List (Fin H.nV) ] a Perm.↭ H.ein e ++ rest))
         → extract-prefix (H.ein e) a ≡ m
         → (edge-step H a e) Perm.↭ (edge-step H b e)
      go nothing eqa =
        -- `a` skips ⇒ `b` skips.
        let eqb-nothing = extract-prefix-↭-nothing (H.ein e) a b a↭b eqa
        in subst₂ Perm._↭_
                  (sym (step-stack-skip e a eqa))
                  (sym (step-stack-skip e b eqb-nothing))
                  a↭b
      go (just (ra , pa)) eqa =
        -- `a` fires with residual `ra`; then `b` fires with residual
        -- rb ↭ ra, so the projected stacks `eout e ++ ra` ↭ `eout e ++ rb`.
        let stepb = extract-prefix-↭-residual (H.ein e) b ra
                      (Perm.↭-trans (Perm.↭-sym a↭b) pa)
            rb    = proj₁ stepb
            pb    = proj₁ (proj₂ stepb)
            eqb   = proj₁ (proj₂ (proj₂ stepb))
            ra↭rb = proj₂ (proj₂ (proj₂ stepb))
        in subst₂ Perm._↭_
                  (sym (step-stack-fire e a ra pa eqa))
                  (sym (step-stack-fire e b rb pb eqb))
                  (PermProp.++⁺ˡ (H.eout e) ra↭rb)

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

  -- Both edges skip in BOTH orders ⇒ both final stacks are `s`.
  two-edge-swap-both-skip
    : ∀ {e e' : Fin H.nE} (s : List (Fin H.nV))
    → extract-prefix (H.ein e ) s ≡ nothing
    → extract-prefix (H.ein e') s ≡ nothing
    → (edge-step H ((edge-step H s e )) e')
      Perm.↭
      (edge-step H ((edge-step H s e')) e )
  two-edge-swap-both-skip {e} {e'} s eqe eqe' =
    -- Both orders reduce to `s`.
    subst₂ Perm._↭_
      (sym lhs≡s) (sym rhs≡s) Perm.refl
    where
      s-e≡s  : (edge-step H s e ) ≡ s
      s-e≡s  = step-stack-skip e s eqe
      s-e'≡s : (edge-step H s e') ≡ s
      s-e'≡s = step-stack-skip e' s eqe'
      lhs≡s : (edge-step H ((edge-step H s e )) e') ≡ s
      lhs≡s = trans (cong (λ x → (edge-step H x e')) s-e≡s) (step-stack-skip e' s eqe')
      rhs≡s : (edge-step H ((edge-step H s e')) e ) ≡ s
      rhs≡s = trans (cong (λ x → (edge-step H x e )) s-e'≡s) (step-stack-skip e s eqe)

  -- Both edges fire in BOTH orders ⇒ `post-swap-stack-↭` closes it.
  two-edge-swap-both-fire
    : ∀ {e e' : Fin H.nE} (s r₁ r₂ r₁' r₂' : List (Fin H.nV))
        (p₁  : s Perm.↭ H.ein e ++ r₁)
        (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (p₂' : s Perm.↭ H.ein e' ++ r₂')
        (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    → extract-prefix (H.ein e ) s ≡ just (r₁ , p₁)
    → extract-prefix (H.ein e') (H.eout e  ++ r₁ ) ≡ just (r₂  , p₂ )
    → extract-prefix (H.ein e') s ≡ just (r₂' , p₂')
    → extract-prefix (H.ein e ) (H.eout e' ++ r₂') ≡ just (r₁' , p₁')
    → (edge-step H ((edge-step H s e )) e')
      Perm.↭
      (edge-step H ((edge-step H s e')) e )
  two-edge-swap-both-fire {e} {e'} s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁'
                          eqe eqe2 eqe' eqe1 =
    subst₂ Perm._↭_ (sym lhs≡) (sym rhs≡)
      (post-swap-stack-↭ e e' s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁')
    where
      lhs≡ : (edge-step H ((edge-step H s e )) e') ≡ H.eout e' ++ r₂
      lhs≡ = trans (cong (λ x → (edge-step H x e'))
                         (step-stack-fire e s r₁ p₁ eqe))
                   (step-stack-fire e' (H.eout e ++ r₁) r₂ p₂ eqe2)
      rhs≡ : (edge-step H ((edge-step H s e')) e ) ≡ H.eout e ++ r₁'
      rhs≡ = trans (cong (λ x → (edge-step H x e ))
                         (step-stack-fire e' s r₂' p₂' eqe'))
                   (step-stack-fire e (H.eout e' ++ r₂') r₁' p₁' eqe1)

  two-edge-swap-stack-↭
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e') (s : List (Fin H.nV))
    → (edge-step H ((edge-step H s e )) e')
      Perm.↭
      (edge-step H ((edge-step H s e')) e )
  two-edge-swap-stack-↭ {e} {e'} inc s with e ≟ e'
  -- e ≡ e': the two orders are identical compositions.
  ... | yes refl = Perm.refl
  ... | no  e≢e' =
    decide-e (extract-prefix (H.ein e) s) refl
    where
      ¬dep-ee' : ¬ (Dep H e e')
      ¬dep-ee' = proj₁ inc
      ¬dep-e'e : ¬ (Dep H e' e)
      ¬dep-e'e = proj₂ inc

      decide-e
        : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ] s Perm.↭ H.ein e ++ r))
        → extract-prefix (H.ein e) s ≡ m
        → (edge-step H ((edge-step H s e )) e')
          Perm.↭
          (edge-step H ((edge-step H s e')) e )
      -- e SKIPS from s.  Decide e' from s.
      decide-e nothing eqe =
        decide-e'-after-eskip (extract-prefix (H.ein e') s) refl
        where
          decide-e'-after-eskip
            : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ] s Perm.↭ H.ein e' ++ r))
            → extract-prefix (H.ein e') s ≡ m
            → (edge-step H ((edge-step H s e )) e')
              Perm.↭
              (edge-step H ((edge-step H s e')) e )
          decide-e'-after-eskip nothing eqe' = two-edge-swap-both-skip s eqe eqe'         -- both skip
          decide-e'-after-eskip (just (r₂' , p₂')) eqe' =
            -- e skips, e' fires: both orders end at `eout e' ++ r₂'`.
            subst₂ Perm._↭_ (sym lhs≡) (sym rhs≡) Perm.refl
            where
              e-skips-post : extract-prefix (H.ein e) (H.eout e' ++ r₂') ≡ nothing
              e-skips-post = e'-skips-stable (λ eq → e≢e' (sym eq)) ¬dep-e'e r₂' s p₂' eqe
              lhs≡ : (edge-step H ((edge-step H s e )) e') ≡ H.eout e' ++ r₂'
              lhs≡ = trans (cong (λ x → (edge-step H x e'))
                                 (step-stack-skip e s eqe))
                           (step-stack-fire e' s r₂' p₂' eqe')
              rhs≡ : (edge-step H ((edge-step H s e')) e ) ≡ H.eout e' ++ r₂'
              rhs≡ = trans (cong (λ x → (edge-step H x e ))
                                 (step-stack-fire e' s r₂' p₂' eqe'))
                           (step-stack-skip e (H.eout e' ++ r₂') e-skips-post)
      -- e FIRES from s with residual r₁.
      decide-e (just (r₁ , p₁)) eqe =
        decide-e'-fire (extract-prefix (H.ein e') (H.eout e ++ r₁)) refl
        where
          decide-e'-fire
            : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ]
                            H.eout e ++ r₁ Perm.↭ H.ein e' ++ r))
            → extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ m
            → (edge-step H ((edge-step H s e )) e')
              Perm.↭
              (edge-step H ((edge-step H s e')) e )
          -- e fires, e' skips post-e: both orders end at `eout e ++ r₁`.
          decide-e'-fire nothing eqe2 =
            decide-e'-from-s-skip (extract-prefix (H.ein e') s) refl
            where
              decide-e'-from-s-skip
                : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ] s Perm.↭ H.ein e' ++ r))
                → extract-prefix (H.ein e') s ≡ m
                → (edge-step H ((edge-step H s e )) e')
                  Perm.↭
                  (edge-step H ((edge-step H s e')) e )
              decide-e'-from-s-skip nothing eqe'n =
                subst₂ Perm._↭_ (sym lhs≡) (sym rhs≡) Perm.refl
                where
                  lhs≡ : (edge-step H ((edge-step H s e )) e') ≡ H.eout e ++ r₁
                  lhs≡ = trans (cong (λ x → (edge-step H x e'))
                                     (step-stack-fire e s r₁ p₁ eqe))
                               (step-stack-skip e' (H.eout e ++ r₁) eqe2)
                  rhs≡ : (edge-step H ((edge-step H s e')) e ) ≡ H.eout e ++ r₁
                  rhs≡ = trans (cong (λ x → (edge-step H x e ))
                                     (step-stack-skip e' s eqe'n))
                               (step-stack-fire e s r₁ p₁ eqe)
              -- e' fires from s but skips post-e — IMPOSSIBLE by stability.
              decide-e'-from-s-skip (just (r₂' , p₂')) eqe'j =
                ⊥-elim (nothing≢just
                  (trans (sym eqe2)
                    (proj₂ (proj₂ (e'-fires-stable e≢e' ¬dep-ee' r₁ s p₁ eqe'j)))))
          decide-e'-fire (just (r₂ , p₂)) eqe2 =
            decide-e'-from-s (extract-prefix (H.ein e') s) refl
            where
              decide-e'-from-s
                : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ] s Perm.↭ H.ein e' ++ r))
                → extract-prefix (H.ein e') s ≡ m
                → (edge-step H ((edge-step H s e )) e')
                  Perm.↭
                  (edge-step H ((edge-step H s e')) e )
              -- e' fires post-e but skips from s — IMPOSSIBLE by stability.
              decide-e'-from-s nothing eqe'n =
                ⊥-elim (nothing≢just
                  (trans (sym (e'-skips-stable e≢e' ¬dep-ee' r₁ s p₁ eqe'n)) eqe2))
              decide-e'-from-s (just (r₂' , p₂')) eqe' =
                decide-e-after-e'
                  (extract-prefix (H.ein e) (H.eout e' ++ r₂')) refl
                where
                  decide-e-after-e'
                    : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ]
                                    H.eout e' ++ r₂' Perm.↭ H.ein e ++ r))
                    → extract-prefix (H.ein e) (H.eout e' ++ r₂') ≡ m
                    → (edge-step H ((edge-step H s e )) e')
                      Perm.↭
                      (edge-step H ((edge-step H s e')) e )
                  decide-e-after-e' (just (r₁' , p₁')) eqe1 =   -- both fire
                    two-edge-swap-both-fire s r₁ r₂ r₁' r₂'
                      p₁ p₂ p₂' p₁' eqe eqe2 eqe' eqe1
                  -- e' fires from s, e fires post-e — yet e SKIPS post-e':
                  -- IMPOSSIBLE by stability (e fires from s, so it fires
                  -- from the post-e' stack too).
                  decide-e-after-e' nothing eqe1 =
                    ⊥-elim (nothing≢just
                      (trans (sym eqe1)
                        (proj₂ (proj₂
                          (e'-fires-stable (λ eq → e≢e' (sym eq)) ¬dep-e'e
                            r₂' s p₂' eqe)))))

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
