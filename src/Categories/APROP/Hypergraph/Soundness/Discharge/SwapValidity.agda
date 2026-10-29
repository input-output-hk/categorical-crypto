-- Incomp alone does not prevent two edges sharing an input wire and reaching
-- different final stacks in different orders. Linearity makes their input
-- counts disjoint, stabilising the firing decision across an incomparable swap.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Discharge.SwapValidity
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using ( process-edges; process-edges-++; edge-step; edge-step-just
        ; edge-step-nothing )
open import Categories.Combinatorics.ExtractPrefix
open import Categories.Combinatorics.ExtractPrefix.Properties
  using (extract-prefix-↭-residual; extract-prefix-↭-nothing)

import Categories.APROP.Hypergraph.Soundness.Discharge.FireMidInterchangeComb sig as FMIC
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Ext
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary

module PerHG (H : Hypergraph FlatGen) (lin : Linear H) where
  private module H = Hypergraph H

  module PH = IW.PerHG H

  open PH

  pe-stack : PH.Order → List (Fin H.nV) → List (Fin H.nV)
  pe-stack = process-edges H

  ------------------------------------------------------------------------
  -- Stack permutations
  ------------------------------------------------------------------------

  -- The view indexes the output stack, refining a stuck edge-step redex
  -- without a transport on that side.
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

  edge-step-stack-resp-↭
    : ∀ {a b : List (Fin H.nV)} (e : Fin H.nE)
    → a Perm.↭ b
    → (edge-step H a e) Perm.↭ (edge-step H b e)
  edge-step-stack-resp-↭ {a} {b} e a↭b = go (edge-step-graph a e)
    where
      go : ∀ {x : List (Fin H.nV)} → EdgeStepR a e x → x Perm.↭ (edge-step H b e)
      go (skipR eqa) =
        subst (a Perm.↭_)
              (sym (edge-step-nothing H b e
                      (extract-prefix-↭-nothing (H.ein e) a b a↭b eqa)))
              a↭b
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

  private
    post-swap-stack-↭ = FMIC.post-swap-stack-↭ H
    e'-fires-stable   = FMIC.e'-fires-stable H lin
    e'-skips-stable   = FMIC.e'-skips-stable H lin

  two-edge-swap-gen
    : ∀ {e e' : Fin H.nE} (e≢e' : ¬ (e ≡ e')) (inc : Incomp e e')
        (s : List (Fin H.nV))
        {a} (we  : EdgeStepR s e  a) {b} (we' : EdgeStepR a e' b)
        {c} (ue  : EdgeStepR s e' c) {d} (ue' : EdgeStepR c e  d)
    → b Perm.↭ d
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
    Perm.↭-reflexive (cong (λ z → H.eout _ ++ proj₁ z)
                           (sym (just-injective (trans (sym ueqe') eqe'))))
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
    Perm.↭-reflexive (cong (λ z → H.eout _ ++ proj₁ z)
                           (sym (just-injective (trans (sym ueqe) eqe))))
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
  two-edge-swap-gen {e} {e'} e≢e' inc s (fireR r₁ p₁ eqe) (fireR r₂ p₂ eqe2)
                    (fireR r₂' p₂' eqe') (fireR r₁' p₁' eqe1) =
    post-swap-stack-↭ e e' s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁'

  two-edge-swap-stack-↭
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e') (s : List (Fin H.nV))
    → (edge-step H ((edge-step H s e )) e')
      Perm.↭
      (edge-step H ((edge-step H s e')) e )
  two-edge-swap-stack-↭ {e} {e'} inc s with e ≟ e'
  ... | yes refl = Perm.refl
  ... | no  e≢e' =
    two-edge-swap-gen e≢e' inc s
      (edge-step-graph s e) (edge-step-graph (edge-step H s e ) e')
      (edge-step-graph s e') (edge-step-graph (edge-step H s e') e )

  swap-stack-↭
    : ∀ (ps qs : PH.Order) {e e' : Fin H.nE} (inc : Incomp e e')
    → pe-stack (ps ++ e ∷ e' ∷ qs) H.dom
      Perm.↭ pe-stack (ps ++ e' ∷ e ∷ qs) H.dom
  swap-stack-↭ ps qs {e} {e'} inc =
    subst (Perm._↭ pe-stack (ps ++ e' ∷ e ∷ qs) H.dom)
          (sym (process-edges-++ H ps (e ∷ e' ∷ qs) H.dom))
      (subst (pe-stack (e ∷ e' ∷ qs) (pe-stack ps H.dom) Perm.↭_)
             (sym (process-edges-++ H ps (e' ∷ e ∷ qs) H.dom))
        (pe-stack-resp-↭ qs (two-edge-swap-stack-↭ inc (pe-stack ps H.dom))))

  swap-validity : ∀ {o₁ o₂ : PH.Order} → o₁ PH.↝ o₂ → PH.Valid o₁ → PH.Valid o₂
  swap-validity (swap-step ps qs inc) p₁ =
    Perm.↭-trans (Perm.↭-sym (swap-stack-↭ ps qs inc)) p₁
