{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The STRICT EMPTY-TAIL two-edge interchange `run-interchange₀ˢ` and its
-- both-fire core `fire-mid-interchangeˢ`.
--
-- This is the assembly file for part (II)ˢ's per-swap lemma: it consumes the
-- algebra bricks of `Strict.SwapCore` (`EdgeStepRˢ`,
-- `box-crossˢ`, `permuteˢ-frameˡ`, `permuteˢ-inv-{left,right}`,
-- `perm-rigidˢ`) and the TERM-FREE combinatorics of
-- `Discharge.Sub.FireMidInterchangeComb` (`SimLoc`, `sim-loc`, the stability
-- lemmas) and `Discharge.Sub.StackUniqueReach` (`Reservoir≤1`) to build:
--
--   * `fire-mid-interchangeˢ` — the both-fire interchange core.
--   * `run-interchange₀ˢ`     — the four-way firing split (skeleton).
--
-- The concrete `permˢ-K` is supplied via `Strict.PermK`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCoreRun
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (process-edges)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig
  using (process-edges-++-stack)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  using (module Run)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig _≟X_

import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidInterchangeComb sig
  as FMIC
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig
  as SUR

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

private
  nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
  nothing≢just ()

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open StrictDecoder H

  ------------------------------------------------------------------------
  -- Local aliases for the SwapCore bricks (whose anonymous module exposes
  -- them as functions of `H`).
  ------------------------------------------------------------------------

  fire-termˢ′ = fire-termˢ H
  Incompˢ     = Incomp H
  pe-stackˢ′  = pe-stackˢ H
  pe-termˢ′   = pe-termˢ H

  -- EdgeStepRˢ view aliases.
  EdgeStepRˢ′      = EdgeStepRˢ H
  edge-stepˢ-graph′ = edge-stepˢ-graph H

  ------------------------------------------------------------------------
  -- The both-fire interchange core, AS A STATEMENT (the strict twin of
  -- `FireMidInterchange.fire-mid-interchange`).  The four framed fire
  -- boxes on disjoint blocks commute, modulo a stack reshuffle.
  ------------------------------------------------------------------------

  FireMidInterchangeˢ : Set
  FireMidInterchangeˢ =
    ∀ {e e' : Fin H.nE} (inc : Incompˢ e e')
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
        (us-sp : Unique sp)
        (us-mid₁ : Unique (H.eout e ++ r₁)) (us-mid₂ : Unique (H.eout e' ++ r₂'))
        (us-cod : Unique (H.eout e ++ r₁'))
    → Σ[ r ∈ (H.eout e' ++ r₂) Perm.↭ (H.eout e ++ r₁') ]
        ( fire-termˢ′ e (H.eout e' ++ r₂') r₁' p₁'
            ∘ˢ fire-termˢ′ e' sp r₂' p₂' )
        ≈ˢ permuteˢ r
              ∘ˢ ( fire-termˢ′ e' (H.eout e ++ r₁) r₂ p₂
                     ∘ˢ fire-termˢ′ e sp r₁ p₁ )

  ------------------------------------------------------------------------
  -- The strict reservoir → `Unique (pe-stackˢ o dom)` bridge.  The
  -- reservoir invariant is stated over the NON-strict `process-edges`;
  -- since the strict and non-strict stacks are definitionally/
  -- propositionally equal (`Run.stacks-agree`), `Unique` transfers.
  ------------------------------------------------------------------------

  private module RH = Run H

  pe-stack-agree : ∀ o s → pe-stackˢ′ o s ≡ (process-edges H o s)
  pe-stack-agree o s = RH.stacks-agree o s

  reached-Uniqueˢ-from
    : ∀ (o : List (Fin H.nE)) → SUR.Reservoir≤1 H (o ++ []) H.dom
    → Unique (pe-stackˢ′ o H.dom)
  reached-Uniqueˢ-from o inv =
    subst Unique (sym (pe-stack-agree o H.dom))
      (SUR.Reservoir≤1⇒Unique H [] ((process-edges H o H.dom))
        (SUR.reservoir-split H o [] H.dom inv))

  private
    e'-fires-stable = FMIC.e'-fires-stable H dih lin
    e'-skips-stable = FMIC.e'-skips-stable H dih lin

  ------------------------------------------------------------------------
  -- The four-way firing split + empty-tail interchange, parameterised by
  -- the both-fire core `FMI : FireMidInterchangeˢ`.
  ------------------------------------------------------------------------

  module RunInterchange (FMI : FireMidInterchangeˢ) where

    -- `build`: the abstract-index four-way split (strict twin of
    -- `RunInterchangeEmptyTail.build`).  The three `Unique` arguments feed
    -- the both-fire branch only.
    build
      : ∀ {e e' : Fin H.nE} (e≢e' : ¬ (e ≡ e')) (inc : Incompˢ e e')
          (sp : List (Fin H.nV))
          {s1 t1} (we  : EdgeStepRˢ′ sp e  s1 t1)
          {s2 t2} (we' : EdgeStepRˢ′ s1 e' s2 t2)
          {u1 v1} (ue  : EdgeStepRˢ′ sp e' u1 v1)
          {u2 w2} (ue' : EdgeStepRˢ′ u1 e  u2 w2)
          (us-s1 : Unique s1) (us-u1 : Unique u1) (us-u2 : Unique u2)
          (us-sp : Unique sp)
      → Σ[ r ∈ s2 Perm.↭ u2 ]
          ((idˢ ∘ˢ w2) ∘ˢ v1)
          ≈ˢ permuteˢ r ∘ˢ ((idˢ ∘ˢ t2) ∘ˢ t1)

    -- (1) e SKIPS sp.
    -- BOTH-SKIP.
    build e≢e' inc sp (skipRˢ eqe) (skipRˢ eqe') (skipRˢ _) (skipRˢ _) _ _ _ _ =
      Perm.refl , ≈-sym idˡ
    build e≢e' inc sp (skipRˢ eqe) (skipRˢ eqe') (fireRˢ ur₂' up₂' ueqe') _ _ _ _ _ =
      ⊥-elim (nothing≢just (trans (sym eqe') ueqe'))
    build e≢e' inc sp (skipRˢ eqe) (skipRˢ eqe') (skipRˢ ueqe') (fireRˢ ur₁ up₁ ueqe1) _ _ _ _ =
      ⊥-elim (nothing≢just (trans (sym eqe) ueqe1))
    build e≢e' inc sp (skipRˢ eqe) (fireRˢ r₂' p₂' eqe') (skipRˢ eqe'-bad) _ _ _ _ _ =
      ⊥-elim (nothing≢just (trans (sym eqe'-bad) eqe'))
    build e≢e' inc sp (skipRˢ eqe) (fireRˢ r₂' p₂' eqe') (fireRˢ ur₂' up₂' ueqe')
          (fireRˢ r₁' p₁' eqe1) _ _ _ _ =
      ⊥-elim (nothing≢just
        (trans (sym (e'-skips-stable (λ eq → e≢e' (sym eq)) (proj₂ inc)
                       ur₂' sp up₂' eqe)) eqe1))
    build e≢e' inc sp (skipRˢ eqe) (fireRˢ r₂' p₂' eqe') (fireRˢ ur₂' up₂' ueqe')
          (skipRˢ eqe1) _ _ _ _ =
      pin (just-injective (trans (sym ueqe') eqe'))
      where
        pin : (ur₂' , up₂') ≡ (r₂' , p₂') → _
        pin refl =
          Perm.refl ,
          ≈-trans (∘-resp idˡ ≈-refl)
            (≈-trans idˡ
              (≈-sym (≈-trans idˡ (≈-trans (∘-resp idˡ ≈-refl) idʳ))))

    -- (2) e FIRES sp.
    build e≢e' inc sp (fireRˢ r₁ p₁ eqe) (skipRˢ eqe2) (fireRˢ ur₂' up₂' ueqe') _ _ _ _ _ =
      ⊥-elim (nothing≢just
        (trans (sym eqe2)
          (proj₂ (proj₂ (e'-fires-stable e≢e' (proj₁ inc) r₁ sp p₁ ueqe')))))
    build e≢e' inc sp (fireRˢ r₁ p₁ eqe) (skipRˢ eqe2) (skipRˢ eqe'n) (skipRˢ eqe-bad) _ _ _ _ =
      ⊥-elim (nothing≢just (trans (sym eqe-bad) eqe))
    build e≢e' inc sp (fireRˢ r₁ p₁ eqe) (skipRˢ eqe2) (skipRˢ eqe'n)
          (fireRˢ ur₁ up₁ ueqe) _ _ _ _ =
      pin (just-injective (trans (sym ueqe) eqe))
      where
        pin : (ur₁ , up₁) ≡ (r₁ , p₁) → _
        pin refl =
          Perm.refl ,
          ≈-trans (∘-resp idˡ ≈-refl)
            (≈-trans idʳ
              (≈-sym (≈-trans idˡ (≈-trans (∘-resp idˡ ≈-refl) idˡ))))
    build e≢e' inc sp (fireRˢ r₁ p₁ eqe) (fireRˢ r₂ p₂ eqe2) (skipRˢ eqe'n) _ _ _ _ _ =
      ⊥-elim (nothing≢just
        (trans (sym (e'-skips-stable e≢e' (proj₁ inc) r₁ sp p₁ eqe'n)) eqe2))
    build e≢e' inc sp (fireRˢ r₁ p₁ eqe) (fireRˢ r₂ p₂ eqe2) (fireRˢ r₂' p₂' eqe')
          (skipRˢ eqe1) _ _ _ _ =
      ⊥-elim (nothing≢just
        (trans (sym eqe1)
          (proj₂ (proj₂
            (e'-fires-stable (λ eq → e≢e' (sym eq)) (proj₂ inc)
              r₂' sp p₂' eqe)))))
    -- BOTH-FIRE — the genuine content.
    build {e} {e'} e≢e' inc sp (fireRˢ r₁ p₁ eqe) (fireRˢ r₂ p₂ eqe2)
          (fireRˢ r₂' p₂' eqe') (fireRˢ r₁' p₁' eqe1) us-s1 us-u1 us-u2 us-sp =
      r ,
      ≈-trans (∘-resp idˡ ≈-refl)
        (≈-trans box-eq
          (∘-resp ≈-refl (∘-resp (≈-sym idˡ) ≈-refl)))
      where
        RI = FMI inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-s1 us-u1 us-u2
        r  = proj₁ RI
        box-eq
          : ( fire-termˢ′ e (H.eout e' ++ r₂') r₁' p₁'
                ∘ˢ fire-termˢ′ e' sp r₂' p₂' )
            ≈ˢ permuteˢ r
                ∘ˢ ( fire-termˢ′ e' (H.eout e ++ r₁) r₂ p₂
                       ∘ˢ fire-termˢ′ e sp r₁ p₁ )
        box-eq = proj₂ RI

    -- Strict `++`-factoring of the stack (bridged to the non-strict
    -- `process-edges-++-stack` through `Run.stacks-agree`).
    ++-stackˢ
      : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
      → pe-stackˢ′ (ps ++ rest) s ≡ pe-stackˢ′ rest (pe-stackˢ′ ps s)
    ++-stackˢ ps rest s =
      trans (RH.stacks-agree (ps ++ rest) s)
      (trans (process-edges-++-stack H ps rest s)
      (trans (cong (λ z → (process-edges H rest z))
                   (sym (RH.stacks-agree ps s)))
             (sym (RH.stacks-agree rest (pe-stackˢ′ ps s)))))

    ----------------------------------------------------------------------
    -- The EMPTY-TAIL interchange core: strict twin of
    -- `RunInterchangeEmptyTail.run-interchange₀`.
    ----------------------------------------------------------------------

    run-interchange₀ˢ
      : ∀ (ps : List (Fin H.nE)) {e e' : Fin H.nE} (inc : Incompˢ e e')
      → SUR.Reservoir≤1 H (ps ++ e' ∷ e ∷ []) H.dom
      → let sp = pe-stackˢ′ ps H.dom in
        Σ[ r ∈ pe-stackˢ′ (e ∷ e' ∷ []) sp Perm.↭ pe-stackˢ′ (e' ∷ e ∷ []) sp ]
          pe-termˢ′ (e' ∷ e ∷ []) sp
          ≈ˢ permuteˢ r ∘ˢ pe-termˢ′ (e ∷ e' ∷ []) sp
    run-interchange₀ˢ ps {e} {e'} inc res with e ≟F e'
    ... | yes refl = Perm.refl , ≈-sym idˡ
    ... | no  e≢e' =
          build e≢e' inc sp
            (edge-stepˢ-graph′ sp e)
            (edge-stepˢ-graph′ (proj₁ (edge-stepˢ sp e)) e')
            (edge-stepˢ-graph′ sp e')
            (edge-stepˢ-graph′ (proj₁ (edge-stepˢ sp e')) e)
            us-s1 us-u1 us-u2 us-sp
      where
        sp = pe-stackˢ′ ps H.dom

        us-sp : Unique sp
        us-sp = reached-Uniqueˢ-from ps res-ps
          where
            res-ps : SUR.Reservoir≤1 H (ps ++ []) H.dom
            res-ps = subst (λ z → SUR.Reservoir≤1 H z H.dom)
                       (sym (++-identityʳ ps))
                       (SUR.reservoir-prefix H ps (e' ∷ e ∷ []) H.dom res)

        -- The three reservoir restrictions to the run prefixes.
        res-e' : SUR.Reservoir≤1 H ((ps ++ e' ∷ []) ++ []) H.dom
        res-e' =
          subst (λ z → SUR.Reservoir≤1 H z H.dom)
            (sym (++-identityʳ (ps ++ e' ∷ [])))
            (SUR.reservoir-prefix H (ps ++ e' ∷ []) (e ∷ []) H.dom
              (subst (λ z → SUR.Reservoir≤1 H z H.dom)
                     (sym (++-assoc ps (e' ∷ []) (e ∷ [])))
                     res))

        res-e : SUR.Reservoir≤1 H ((ps ++ e ∷ []) ++ []) H.dom
        res-e =
          subst (λ z → SUR.Reservoir≤1 H z H.dom)
            (sym (++-identityʳ (ps ++ e ∷ [])))
            (SUR.reservoir-prefix H (ps ++ e ∷ []) (e' ∷ []) H.dom
              (subst (λ z → SUR.Reservoir≤1 H z H.dom)
                     (sym (++-assoc ps (e ∷ []) (e' ∷ [])))
                     (SUR.reservoir-resp-↭ H H.dom
                       (PermProp.++⁺ˡ ps (Perm.swap e' e Perm.refl))
                       res)))

        res-comb : SUR.Reservoir≤1 H ((ps ++ e' ∷ e ∷ []) ++ []) H.dom
        res-comb = subst (λ z → SUR.Reservoir≤1 H z H.dom)
                     (sym (++-identityʳ (ps ++ e' ∷ e ∷ []))) res

        us-s1 : Unique (proj₁ (edge-stepˢ sp e))
        us-s1 = subst Unique
                  (trans (++-stackˢ ps (e ∷ []) H.dom) refl)
                  (reached-Uniqueˢ-from (ps ++ e ∷ []) res-e)

        us-u1 : Unique (proj₁ (edge-stepˢ sp e'))
        us-u1 = subst Unique
                  (trans (++-stackˢ ps (e' ∷ []) H.dom) refl)
                  (reached-Uniqueˢ-from (ps ++ e' ∷ []) res-e')

        us-u2 : Unique (proj₁ (edge-stepˢ (proj₁ (edge-stepˢ sp e')) e))
        us-u2 = subst Unique
                  (trans (++-stackˢ ps (e' ∷ e ∷ []) H.dom) refl)
                  (reached-Uniqueˢ-from (ps ++ e' ∷ e ∷ []) res-comb)
