{-# OPTIONS --safe --without-K #-}

-- Empty-tail two-edge interchange, parameterised by the both-fire core.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCoreRun
  (sig : APROPSignature)
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (process-edges)
import Categories.APROP.Hypergraph.Soundness.Discharge.FireMidInterchangeComb sig
  as FMIC
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig
  as SUR
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig

open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Properties
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe.Ext
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (¬_; yes; no)

module _ (H : Hypergraph FlatGen)
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open StrictDecoder H

  Incompˢ     = Incomp H
  pe-stackˢ′  = pe-stackˢ H
  pe-termˢ′   = pe-termˢ H

  EdgeStepRˢ′      = EdgeStepRˢ H
  edge-stepˢ-graph′ = edge-stepˢ-graph H

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
        ( fire-termˢ e (H.eout e' ++ r₂') r₁' p₁'
            ∘ˢ fire-termˢ e' sp r₂' p₂' )
        ≈ˢ permuteˢ r
              ∘ˢ ( fire-termˢ e' (H.eout e ++ r₁) r₂ p₂
                     ∘ˢ fire-termˢ e sp r₁ p₁ )

  reached-Uniqueˢ-from
    : ∀ (o : List (Fin H.nE)) → SUR.Reservoir≤1 H o H.dom
    → Unique (pe-stackˢ′ o H.dom)
  reached-Uniqueˢ-from o inv =
    SUR.Reservoir≤1⇒Unique H [] ((process-edges H o H.dom))
      (SUR.reservoir-split H o [] H.dom
        (subst (λ z → SUR.Reservoir≤1 H z H.dom) (sym (++-identityʳ o)) inv))

  private
    e'-fires-stable = FMIC.e'-fires-stable H lin
    e'-skips-stable = FMIC.e'-skips-stable H lin

  module RunInterchange (FMI : FireMidInterchangeˢ) where

    private
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
            : ( fire-termˢ e (H.eout e' ++ r₂') r₁' p₁'
                  ∘ˢ fire-termˢ e' sp r₂' p₂' )
              ≈ˢ permuteˢ r
                  ∘ˢ ( fire-termˢ e' (H.eout e ++ r₁) r₂ p₂
                         ∘ˢ fire-termˢ e sp r₁ p₁ )
          box-eq = proj₂ RI

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

        res-prefix
          : ∀ (x y : Fin H.nE) → SUR.Reservoir≤1 H (ps ++ x ∷ y ∷ []) H.dom
          → SUR.Reservoir≤1 H (ps ++ x ∷ []) H.dom
        res-prefix x y r =
          SUR.reservoir-prefix H (ps ++ x ∷ []) (y ∷ []) H.dom
            (subst (λ z → SUR.Reservoir≤1 H z H.dom)
                   (sym (++-assoc ps (x ∷ []) (y ∷ []))) r)

        us-of
          : ∀ (o : List (Fin H.nE)) → SUR.Reservoir≤1 H (ps ++ o) H.dom
          → Unique (pe-stackˢ′ o sp)
        us-of o r = subst Unique (pe-stack-++ˢ ps o H.dom)
                      (reached-Uniqueˢ-from (ps ++ o) r)

        us-sp : Unique sp
        us-sp =
          reached-Uniqueˢ-from ps
            (SUR.reservoir-prefix H ps (e' ∷ e ∷ []) H.dom res)

        us-s1 : Unique (proj₁ (edge-stepˢ sp e))
        us-s1 = us-of (e ∷ []) (res-prefix e e'
                  (SUR.reservoir-resp-↭ H H.dom
                    (PermProp.++⁺ˡ ps (Perm.swap e' e Perm.refl)) res))

        us-u1 : Unique (proj₁ (edge-stepˢ sp e'))
        us-u1 = us-of (e' ∷ []) (res-prefix e' e res)

        us-u2 : Unique (proj₁ (edge-stepˢ (proj₁ (edge-stepˢ sp e')) e))
        us-u2 = us-of (e' ∷ e ∷ []) res
