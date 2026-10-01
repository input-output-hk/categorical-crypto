{-# OPTIONS --safe --without-K #-}

-- The reactive interaction model: an ADAPTIVE distinguisher probing a stateful
-- response kernel, totally (`runWith`) or partially (`runWith⊥`), returning the
-- verdict bit.  This is the semantics every concrete-security statement in the
-- library is phrased in.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.Rational renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ)
import Relation.Binary.Reasoning.Setoid as RS

open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

module CategoricalCrypto.Interaction where

private variable Q R St : Type

------------------------------------------------------------------------
-- Running a distinguisher, totally and partially

runWith : (St → Q → Dist-ℚ (St × R)) → St → Strat Q R → Dist-ℚ Bool
runWith resp s (out b)    = return-ℚ b
runWith resp s (ask q k)  = resp s q >>=ᴹ λ sr → runWith resp (proj₁ sr) (k (proj₂ sr))
runWith resp s (coin μ k) = μ >>=ᴹ λ b → runWith resp s (k b)

runWith⊥ : (St → Q → Dist⊥ (St × R)) → St → Strat Q R → Dist⊥ Bool
runWith⊥ resp s (out b)    = return⊥ b
runWith⊥ resp s (ask q k)  = resp s q >>=⊥ λ sr → runWith⊥ resp (proj₁ sr) (k (proj₂ sr))
runWith⊥ resp s (coin μ k) = μ >>=ᴹ λ b → runWith⊥ resp s (k b)

-- Along a state embedding: a partial kernel that is, on the image of `emb`,
-- the embedded image of a total one runs like that total one at EVERY
-- distinguisher.  The embedding is what lets a system carry ancillary state
-- the total kernel does not (a protocol composite's second component, say).
runWith⊥-emb : {Q R S T : Type}
               (resp : S → Q → Dist-ℚ (S × R)) (resp⊥ : T → Q → Dist⊥ (T × R))
               (emb : S → T)
             → (∀ s q → resp⊥ (emb s) q
                        ≈Mℚ (resp s q >>=ᴹ λ sr → return⊥ (emb (proj₁ sr) , proj₂ sr)))
             → ∀ s d → runWith⊥ resp⊥ (emb s) d ≈Mℚ Dmap just (runWith resp s d)
runWith⊥-emb resp resp⊥ emb ker s (out b) = begin
  return⊥ b                                  ≈˘⟨ >>=ᴹ-identityˡ b (return-ℚ ∘ just) ⟩
  Dmap just (return-ℚ b)                      ∎
  where open RS (Mℚ-setoid _)
runWith⊥-emb {R = R} resp resp⊥ emb ker s (ask q k) = begin
  (resp⊥ (emb s) q >>=⊥ K⊥)
    ≈⟨ >>=⊥-congʳ K⊥ (resp⊥ (emb s) q) (resp s q >>=ᴹ Eret) (ker s q) ⟩
  ((resp s q >>=ᴹ Eret) >>=⊥ K⊥)
    ≈⟨ >>=ᴹ-assoc (resp s q) Eret (kmaybe K⊥) ⟩
  (resp s q >>=ᴹ λ sr → (Eret sr >>=⊥ K⊥))
    ≈⟨ >>=ᴹ-cong {μ = resp s q} {resp s q} {λ sr → Eret sr >>=⊥ K⊥}
         {λ sr → Dmap just (G sr)} (λ P → refl)
         (λ sr → Mℚ.trans {i = Eret sr >>=⊥ K⊥}
                          {j = runWith⊥ resp⊥ (emb (proj₁ sr)) (k (proj₂ sr))}
                          {k = Dmap just (G sr)}
                   (>>=⊥-identityˡ (emb (proj₁ sr) , proj₂ sr) K⊥)
                   (runWith⊥-emb resp resp⊥ emb ker (proj₁ sr) (k (proj₂ sr)))) ⟩
  (resp s q >>=ᴹ λ sr → Dmap just (G sr))
    ≈˘⟨ >>=ᴹ-assoc (resp s q) G (return-ℚ ∘ just) ⟩
  Dmap just (resp s q >>=ᴹ G) ∎
  where
    Eret = λ (sr : _ × R) → return⊥ (emb (proj₁ sr) , proj₂ sr)
    G    = λ sr → runWith resp (proj₁ sr) (k (proj₂ sr))
    K⊥   = λ sr → runWith⊥ resp⊥ (proj₁ sr) (k (proj₂ sr))
    open RS (Mℚ-setoid _)
runWith⊥-emb resp resp⊥ emb ker s (coin μ k) = begin
  (μ >>=ᴹ λ b → runWith⊥ resp⊥ (emb s) (k b))
    ≈⟨ >>=ᴹ-cong {μ = μ} {μ} {λ b → runWith⊥ resp⊥ (emb s) (k b)}
         {λ b → Dmap just (G b)} (λ P → refl)
         (λ b → runWith⊥-emb resp resp⊥ emb ker s (k b)) ⟩
  (μ >>=ᴹ λ b → Dmap just (G b))
    ≈˘⟨ >>=ᴹ-assoc μ G (return-ℚ ∘ just) ⟩
  Dmap just (μ >>=ᴹ G) ∎
  where
    G = λ b → runWith resp s (k b)
    open RS (Mℚ-setoid _)
