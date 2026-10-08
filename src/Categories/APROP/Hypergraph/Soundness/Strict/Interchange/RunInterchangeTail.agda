{-# OPTIONS --safe --without-K #-}

-- Extend two-edge interchange through a suffix by decoder equivariance.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail
  (sig : APROPSignature)
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig using (process-edges)
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig
  using (module EquivStep)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig as SC
open import Categories.Morphism.Reasoning SCat
open import Data.Fin using (Fin)

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open EquivStep H
    using ( permuteˢ; pe-stackˢ; pe-termˢ; process-edges-equivariantˢ
          ; pvv-inverse-leftˢ )

  Incompˢ = SC.Incomp H

  record RunInterchangeˢ (ps qs : List (Fin H.nE)) {e e' : Fin H.nE}
                         (inc : Incompˢ e e') : Set where
    private
      sp  = pe-stackˢ ps H.dom
      fs₁ = pe-stackˢ (e ∷ e' ∷ qs) sp
      fs₂ = pe-stackˢ (e' ∷ e ∷ qs) sp
    field reshuffle : fs₁ Perm.↭ fs₂
          run-eq
            : pe-termˢ (e' ∷ e ∷ qs) sp
              ≈ˢ permuteˢ reshuffle ∘ˢ pe-termˢ (e ∷ e' ∷ qs) sp

  tail-reservoir
    : ∀ (ps qs : List (Fin H.nE)) (e e' : Fin H.nE)
    → SUR.Reservoir≤1 H (ps ++ e' ∷ e ∷ qs) H.dom
    → SUR.Reservoir≤1 H qs (pe-stackˢ (e' ∷ e ∷ []) (pe-stackˢ ps H.dom))
  tail-reservoir ps qs e e' res =
    SUR.reservoir-split H (e' ∷ e ∷ []) qs ((process-edges H ps H.dom))
      (SUR.reservoir-split H ps (e' ∷ e ∷ qs) H.dom res)

  run-interchange-tailˢ
    : ∀ (ps qs : List (Fin H.nE)) {e e' : Fin H.nE} (inc : Incompˢ e e')
    → SUR.Reservoir≤1 H (ps ++ e' ∷ e ∷ qs) H.dom
    → RunInterchangeˢ ps [] inc
    → RunInterchangeˢ ps qs inc
  run-interchange-tailˢ ps qs {e} {e'} inc res RI₀ =
    record { reshuffle = Perm.↭-sym ρf ; run-eq = run-eq }
    where
      sp : List (Fin H.nV)
      sp = pe-stackˢ ps H.dom

      A : List (Fin H.nV)
      A = pe-stackˢ (e ∷ e' ∷ []) sp
      B : List (Fin H.nV)
      B = pe-stackˢ (e' ∷ e ∷ []) sp

      r₀ : A Perm.↭ B
      r₀ = RunInterchangeˢ.reshuffle RI₀

      run-eq₀ : pe-termˢ (e' ∷ e ∷ []) sp ≈ˢ permuteˢ r₀ ∘ˢ pe-termˢ (e ∷ e' ∷ []) sp
      run-eq₀ = RunInterchangeˢ.run-eq RI₀

      equivar
        : Σ[ ρf ∈ pe-stackˢ qs B Perm.↭ pe-stackˢ qs A ]
            pe-termˢ qs B
              ≈ˢ permuteˢ (Perm.↭-sym ρf)
                    ∘ˢ ( pe-termˢ qs A ∘ˢ permuteˢ (Perm.↭-sym r₀) )
      equivar =
        process-edges-equivariantˢ qs {s = A} {s' = B} (Perm.↭-sym r₀)
          (tail-reservoir ps qs e e' res)

      ρf : pe-stackˢ qs B Perm.↭ pe-stackˢ qs A
      ρf = proj₁ equivar

      split₂ : pe-termˢ (e' ∷ e ∷ qs) sp ≈ˢ pe-termˢ qs B ∘ˢ pe-termˢ (e' ∷ e ∷ []) sp
      split₂ = pullʳ (∘-resp (≈-sym idˡ) ≈-refl)

      split₁ : pe-termˢ qs A ∘ˢ pe-termˢ (e ∷ e' ∷ []) sp ≈ˢ pe-termˢ (e ∷ e' ∷ qs) sp
      split₁ = ≈-trans (∘-resp ≈-refl (∘-resp idˡ ≈-refl)) (≈-sym assocˢ)

      run-eq
        : pe-termˢ (e' ∷ e ∷ qs) sp
          ≈ˢ permuteˢ (Perm.↭-sym ρf) ∘ˢ pe-termˢ (e ∷ e' ∷ qs) sp
      run-eq =
        ≈-trans split₂
          (≈-trans
            (∘-resp (proj₂ equivar) run-eq₀)
            (≈-trans
              (pullʳ (pullʳ (≈-sym assocˢ)))
              (∘-resp ≈-refl
                (≈-trans
                  (∘-resp ≈-refl
                    (≈-trans
                      (∘-resp (pvv-inverse-leftˢ r₀) ≈-refl)
                      idˡ))
                  split₁))))
