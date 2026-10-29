{-# OPTIONS --safe --without-K #-}

-- The element-level Coxeter completeness theorem applies unchanged to the
-- vertex set; strict-SMC coherence interprets its inductive congruence.

open import Categories.FreeStrictSMC
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (_≈-fb_)

open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Relation.Binary using (DecidableEquality)

module Categories.FreeStrictSMC.Perm.Coherence
  (X : Set) (_≟X_ : DecidableEquality X)
  where

import Categories.FreeStrictSMC.Perm.Braid X _≟X_ as BR

module Discharge (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X)
  (mor : List X → List X → Set) where

  open import Categories.PermuteCoherence.Coxeter.FaithfulnessInductive V _≟V_
    using (_≅↭ⁱ_; complete)
  open _≅↭ⁱ_

  open Build X _≟X_ mor
  open Perm′ V vlab
  module BG = BR.Generic mor

  private
    variable
      x y z : V
      xs ys : List V

  StrictBraid : Set
  StrictBraid = ∀ (a b c : X) (M : List X) → BG.BraidAt a b c M

  module Main (braidX : StrictBraid) where

    -- Singleton associators reduce as in `Braid.Generic`.
    private
      swap-nat-case
        : (p : xs ↭ ys)
        → σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ permuteˢ p
          ≈ˢ (σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ idˢ {map vlab ys})
              ∘ˢ (idˢ {vlab x ∷ []} ⊗ˢ (idˢ {vlab y ∷ []} ⊗ˢ permuteˢ p))
      swap-nat-case {x = x} {y = y} p =
        ≈-sym
          (≈-trans (∘-resp ≈-refl (≈-sym (⊗-assocˢ (idˢ {vlab x ∷ []})
                                                   (idˢ {vlab y ∷ []})
                                                   (permuteˢ p))))
          (≈-trans interchangeˢ
                   (⊗-resp (≈-trans (∘-resp ≈-refl ⊗-id) idʳ) idˡ)))

      swap-nat-left-case
        : (p : xs ↭ ys)
        → σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ permuteˢ p
          ≈ˢ (idˢ {vlab y ∷ []} ⊗ˢ (idˢ {vlab x ∷ []} ⊗ˢ permuteˢ p))
              ∘ˢ (σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ idˢ {map vlab xs})
      swap-nat-left-case {x = x} {y = y} p =
        ≈-sym
          (≈-trans (∘-resp (≈-sym (⊗-assocˢ (idˢ {vlab y ∷ []})
                                            (idˢ {vlab x ∷ []})
                                            (permuteˢ p))) ≈-refl)
          (≈-trans interchangeˢ
                   (⊗-resp (≈-trans (∘-resp ⊗-id ≈-refl) idˡ) idʳ)))

      swap-braid-case
        : permuteˢ (Perm.trans (Perm.swap x y (Perm.refl {xs = z ∷ xs}))
                     (Perm.trans (Perm.prep y (Perm.swap x z (Perm.refl {xs = xs})))
                                 (Perm.swap y z (Perm.refl {xs = x ∷ xs}))))
          ≈ˢ
          permuteˢ (Perm.trans (Perm.prep x (Perm.swap y z (Perm.refl {xs = xs})))
                     (Perm.trans (Perm.swap x z (Perm.refl {xs = y ∷ xs}))
                                 (Perm.prep z (Perm.swap x y (Perm.refl {xs = xs})))))
      swap-braid-case {x = x} {y = y} {z = z} {xs = xs} =
        braidX (vlab x) (vlab y) (vlab z) (map vlab xs)

    permuteˢ-resp-≅↭ⁱ
      : {p q : xs ↭ ys}
      → p ≅↭ⁱ q → permuteˢ p ≈ˢ permuteˢ q
    permuteˢ-resp-≅↭ⁱ iref          = ≈-refl
    permuteˢ-resp-≅↭ⁱ (isym h)      = ≈-sym (permuteˢ-resp-≅↭ⁱ h)
    permuteˢ-resp-≅↭ⁱ (itrn h₁ h₂)  = ≈-trans (permuteˢ-resp-≅↭ⁱ h₁) (permuteˢ-resp-≅↭ⁱ h₂)
    permuteˢ-resp-≅↭ⁱ (prepc h)     = ⊗-resp ≈-refl (permuteˢ-resp-≅↭ⁱ h)
    permuteˢ-resp-≅↭ⁱ (trc h₁ h₂)   = ∘-resp (permuteˢ-resp-≅↭ⁱ h₂) (permuteˢ-resp-≅↭ⁱ h₁)
    permuteˢ-resp-≅↭ⁱ tr-unitˡ      = idʳ
    permuteˢ-resp-≅↭ⁱ tr-unitʳ      = idˡ
    permuteˢ-resp-≅↭ⁱ tr-assoc      = ≈-sym assocˢ
    permuteˢ-resp-≅↭ⁱ prep-id       = ⊗-id
    permuteˢ-resp-≅↭ⁱ prep-tr       = ≈-sym (≈-trans interchangeˢ (⊗-resp idˡ ≈-refl))
    permuteˢ-resp-≅↭ⁱ swap-invol    = ≈-trans interchangeˢ (≈-trans (⊗-resp σ-σˢ idˡ) ⊗-id)
    permuteˢ-resp-≅↭ⁱ (swap-nat {p = p})      = swap-nat-case p
    permuteˢ-resp-≅↭ⁱ (swap-nat-left {p = p}) = swap-nat-left-case p
    permuteˢ-resp-≅↭ⁱ swap-braid              = swap-braid-case

    permˢ-K
      : (p q : xs ↭ ys)
      → eval-↭ p ≈-fb eval-↭ q
      → permuteˢ p ≈ˢ permuteˢ q
    permˢ-K p q eq = permuteˢ-resp-≅↭ⁱ (complete eq)
