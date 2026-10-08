{-# OPTIONS --safe --without-K #-}

-- Decoder equivariance under input stack permutations.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.Combinatorics.ExtractPrefix
open import Categories.Combinatorics.ExtractPrefix.Properties
  using (extract-prefix-↭-residual; extract-prefix-↭-nothing)

import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig as SU
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose sig public
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.EdgeStepRel sig
  using (module EdgeStepView)

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig as PK
open import Categories.Morphism.Reasoning SCat

open import Categories.PermuteCoherence.Rigid using (_≅↭_)

open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just)
open import Data.Maybe.Ext
open import Data.Maybe.Properties using (just-injective)

module EquivStep (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open Run H public
  open Equivariantˢ H public using (pvv-transˢ; pvv-inverse-leftˢ; pvv-inverse-rightˢ)

  open Restrict (Fin H.nV) vl

  private
    permˢ-K-H : PK.Support.PermK (Fin H.nV) H.vlab
    permˢ-K-H = PK.permˢ-K (Fin H.nV) _≟F_ H.vlab

  open EdgeStepView H public

  box-core-natᵛ
    : ∀ (e : Fin H.nE) {restH restH' : List (Fin H.nV)}
        (μ : restH Perm.↭ restH')
    → genˢ (H.elab e) ⊗ᵛ idᵛ {restH'}
      ≈ᵛ (idᵛ {H.eout e} ⊗ᵛ permuteᵛ μ)
           ∘ᵛ ( (genˢ (H.elab e) ⊗ᵛ idᵛ {restH})
                ∘ᵛ (idᵛ {H.ein e} ⊗ᵛ permuteᵛ (Perm.↭-sym μ)) )
  box-core-natᵛ e μ =
    ≈-sym
      (≈-trans (∘-resp ≈-refl interchangeᵛ)
      (≈-trans (∘-resp ≈-refl (⊗-respᵛ idʳ idˡ))
      (≈-trans interchangeᵛ
      (⊗-respᵛ idˡ (pvv-inverse-rightˢ μ)))))

  fire-midˢ
    : ∀ (e : Fin H.nE) (rest : List (Fin H.nV))
    → HomS (map vl (H.ein e ++ rest)) (map vl (H.eout e ++ rest))
  fire-midˢ e rest = fire-termˢ e (H.ein e ++ rest) rest Perm.refl

  fire-midˢ-cast
    : ∀ (e : Fin H.nE) (rest : List (Fin H.nV))
    → fire-midˢ e rest ≈ᵛ genˢ (H.elab e) ⊗ᵛ idᵛ {rest}
  fire-midˢ-cast e rest =
    ≈-trans (edge-step-firedᵛ e rest Perm.refl) idʳ

  fire-term-factorˢ
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
        (perm : s Perm.↭ H.ein e ++ rest)
    → fire-termˢ e s rest perm ≈ˢ fire-midˢ e rest ∘ˢ permuteˢ perm
  fire-term-factorˢ e s rest perm =
    ≈-trans (edge-step-firedᵛ e rest perm)
            (≈-sym (∘-resp (fire-midˢ-cast e rest) ≈-refl))

  fire-mid-equivariantˢ
    : ∀ (e : Fin H.nE) {restH restH' : List (Fin H.nV)}
        (μ : restH Perm.↭ restH')
    → fire-midˢ e restH'
      ≈ᵛ permuteᵛ (PermProp.++⁺ˡ (H.eout e) μ)
           ∘ᵛ ( fire-midˢ e restH
                ∘ᵛ permuteᵛ (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym μ)) )
  fire-mid-equivariantˢ e μ =
    ≈-trans (fire-midˢ-cast e _)
    (≈-trans (box-core-natᵛ e μ)
      (∘-resp (≈-sym (permuteᵛ-frameˡ (H.eout e) μ))
        (∘-resp (≈-sym (fire-midˢ-cast e _))
                (≈-sym (permuteᵛ-frameˡ (H.ein e) (Perm.↭-sym μ))))))

  module _ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
           {restH restH' : List (Fin H.nV)}
           (permH  : s  Perm.↭ H.ein e ++ restH)
           (permH' : s' Perm.↭ H.ein e ++ restH')
           (eqH' : extract-prefix (H.ein e) s' ≡ just (restH' , permH'))
           (us' : Unique s')
           where
    private
      xpr = extract-prefix-↭-residual (H.ein e) s' restH (Perm.trans ρ permH)
      restHc  = proj₁ xpr
      permHc  = proj₁ (proj₂ xpr)
      eqHc    = proj₁ (proj₂ (proj₂ xpr))
      rpc     = proj₂ (proj₂ (proj₂ xpr))

      pair-eq : (restHc , permHc) ≡ (restH' , permH')
      pair-eq = just-injective (trans (sym eqHc) eqH')

      restHc≡ : restHc ≡ restH'
      restHc≡ = cong proj₁ pair-eq

    fire-μ : restH Perm.↭ restH'
    fire-μ = subst (restH Perm.↭_) restHc≡ rpc

    private
      recon-collapse
        : ∀ {rc} (pc : s' Perm.↭ H.ein e ++ rc) (rp : restH Perm.↭ rc)
            (req : rc ≡ restH')
            (peq : permH' ≡ subst (λ r → s' Perm.↭ H.ein e ++ r) req pc)
        → Perm.trans permH'
            (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym (subst (restH Perm.↭_) req rp)))
          ≅↭ Perm.trans pc (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym rp))
      recon-collapse pc rp refl refl i = refl

      permHc≡ : permH' ≡ subst (λ r → s' Perm.↭ H.ein e ++ r) restHc≡ permHc
      permHc≡ = sym (subst-pair-snd pair-eq)
        where
          subst-pair-snd
            : ∀ {rc : List (Fin H.nV)} {pc : s' Perm.↭ H.ein e ++ rc}
                (pe : (rc , pc) ≡ (restH' , permH'))
            → subst (λ r → s' Perm.↭ H.ein e ++ r) (cong proj₁ pe) pc ≡ permH'
          subst-pair-snd refl = refl

    locate-coherentˢ
      : Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))
        ≅↭ Perm.trans ρ permH
    locate-coherentˢ i = trans (half₁ i) (half₂ i)
      where
        mid : s' Perm.↭ H.ein e ++ restH
        mid = Perm.trans permHc (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym rpc))

        half₁ : Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ)) ≅↭ mid
        half₁ = recon-collapse permHc rpc restHc≡ permHc≡

        half₂ : mid ≅↭ Perm.trans ρ permH
        half₂ = SU.residual-recon (H.ein e) s' restH (Perm.trans ρ permH)
                  (SU.Unique-resp-↭ (Perm.trans ρ permH) us')

    perm-reconcileˢ
      : permuteˢ (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))
          ∘ˢ permuteˢ permH'
        ≈ˢ permuteˢ permH ∘ˢ permuteˢ ρ
    perm-reconcileˢ =
      ≈-trans (≈-sym (pvv-transˢ permH'
                       (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ))))
        (≈-trans
          (permˢ-K-H
            (Perm.trans permH' (PermProp.++⁺ˡ (H.ein e) (Perm.↭-sym fire-μ)))
            (Perm.trans ρ permH)
            locate-coherentˢ)
          (pvv-transˢ ρ permH))

    edge-step-fire-equivariantˢ
      : fire-termˢ e s' restH' permH'
        ≈ˢ permuteˢ (PermProp.++⁺ˡ (H.eout e) fire-μ)
              ∘ˢ ( fire-termˢ e s restH permH ∘ˢ permuteˢ ρ )
    edge-step-fire-equivariantˢ =
      ≈-trans (fire-term-factorˢ e s' restH' permH')
      (≈-trans (∘-resp (fire-mid-equivariantˢ e fire-μ) ≈-refl)
        (pullʳ (≈-trans (pullʳ perm-reconcileˢ)
                        (pullˡ (≈-sym (fire-term-factorˢ e s restH permH))))))

  private
    ++⁺ˡ-↭-sym
      : ∀ (xs : List (Fin H.nV)) {ys zs : List (Fin H.nV)} (p : ys Perm.↭ zs)
      → Perm.↭-sym (PermProp.++⁺ˡ xs p) ≡ PermProp.++⁺ˡ xs (Perm.↭-sym p)
    ++⁺ˡ-↭-sym []       p = refl
    ++⁺ˡ-↭-sym (x ∷ xs) p = cong (Perm.prep x) (++⁺ˡ-↭-sym xs p)

  edge-step-equivariantˢ
    : ∀ (e : Fin H.nE) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
        {s'H : List (Fin H.nV)} {tH : HomS (map vl s) (map vl s'H)}
        {s'H' : List (Fin H.nV)} {tH' : HomS (map vl s') (map vl s'H')}
        (wH  : EdgeStepRˢ s e s'H tH) (wH' : EdgeStepRˢ s' e s'H' tH')
        (us' : Unique s')
    → Σ[ ρf ∈ s'H' Perm.↭ s'H ]
        tH' ≈ˢ permuteˢ (Perm.↭-sym ρf) ∘ˢ ( tH ∘ˢ permuteˢ ρ )
  edge-step-equivariantˢ e ρ (skipRˢ eqH) (skipRˢ eqH') us' =
    ρ , ≈-sym (≈-trans (∘-resp ≈-refl idˡ) (pvv-inverse-leftˢ ρ))
  edge-step-equivariantˢ e {s} {s'} ρ (skipRˢ eqH) (fireRˢ restH' permH' eqH') us' =
    ⊥-elim (just≢nothing
      (trans (sym eqH') (extract-prefix-↭-nothing (H.ein e) s s' (Perm.↭-sym ρ) eqH)))
  edge-step-equivariantˢ e {s} {s'} ρ (fireRˢ restH permH eqH) (skipRˢ eqH') us' =
    ⊥-elim (just≢nothing
      (trans (sym (proj₁ (proj₂ (proj₂
                (extract-prefix-↭-residual (H.ein e) s' restH (Perm.trans ρ permH))))))
             eqH'))
  edge-step-equivariantˢ e {s} {s'} ρ
      (fireRˢ restH permH eqH) (fireRˢ restH' permH' eqH') us' =
        PermProp.++⁺ˡ (H.eout e) (Perm.↭-sym μ)
      , subst (λ z → fire-termˢ e s' restH' permH'
                       ≈ˢ permuteˢ z
                            ∘ˢ ( fire-termˢ e s restH permH ∘ˢ permuteˢ ρ ))
              (sym (trans (++⁺ˡ-↭-sym (H.eout e) (Perm.↭-sym μ))
                          (cong (PermProp.++⁺ˡ (H.eout e))
                                (PermProp.↭-sym-involutive μ))))
              (edge-step-fire-equivariantˢ e ρ permH permH' eqH' us')
    where
      μ : restH Perm.↭ restH'
      μ = fire-μ e ρ permH permH' eqH' us'

  process-edges-equivariantˢ
    : ∀ (qs : List (Fin H.nE)) {s s' : List (Fin H.nV)} (ρ : s' Perm.↭ s)
    → SUR.Reservoir≤1 H qs s'
    → Σ[ ρf ∈ pe-stackˢ qs s' Perm.↭ pe-stackˢ qs s ]
        pe-termˢ qs s'
          ≈ˢ permuteˢ (Perm.↭-sym ρf)
                ∘ˢ ( pe-termˢ qs s ∘ˢ permuteˢ ρ )
  process-edges-equivariantˢ [] {s} {s'} ρ _ =
    ρ , ≈-sym (≈-trans (∘-resp ≈-refl idˡ) (pvv-inverse-leftˢ ρ))
  process-edges-equivariantˢ (e ∷ qs) {s} {s'} ρ inv
      with edge-step-equivariantˢ e ρ (edge-stepˢ-graph s e) (edge-stepˢ-graph s' e)
              (SUR.Reservoir≤1⇒Unique H (e ∷ qs) s' inv)
  ... | ρ1 , step-eq
      with process-edges-equivariantˢ qs
             {proj₁ (edge-stepˢ s e)} {proj₁ (edge-stepˢ s' e)} ρ1
             (SUR.edge-step-Reservoir≤1 H e qs s' inv)
  ... | ρf , tail-eq =
        ρf , goal
    where
      s1  = proj₁ (edge-stepˢ s  e)
      s1' = proj₁ (edge-stepˢ s' e)
      tH  = proj₂ (edge-stepˢ s  e)
      tH' = proj₂ (edge-stepˢ s' e)

      mid-collapse : permuteˢ ρ1 ∘ˢ tH' ≈ˢ tH ∘ˢ permuteˢ ρ
      mid-collapse =
        ≈-trans (∘-resp ≈-refl step-eq)
          (≈-trans (≈-sym assocˢ)
            (≈-trans
              (∘-resp (pvv-inverse-rightˢ ρ1) ≈-refl)
              idˡ))

      goal
        : (pe-termˢ qs s1' ∘ˢ tH')
          ≈ˢ permuteˢ (Perm.↭-sym ρf)
                ∘ˢ ( (pe-termˢ qs s1 ∘ˢ tH) ∘ˢ permuteˢ ρ )
      goal =
        ≈-trans (∘-resp tail-eq (≈-refl {f = tH'}))
                (pullʳ (≈-trans (pullʳ mid-collapse) (≈-sym assocˢ)))
