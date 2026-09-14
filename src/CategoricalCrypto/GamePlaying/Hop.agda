{-# OPTIONS --safe --without-K #-}

-- Assembling a game hop out of `GamePlaying`'s two bridges.
--
--   • `runWith-bisim` — two kernels that are COUPLED step by step (their
--     one-query expectations agree at related states, on any pair of
--     integrands that agrees at related outcomes) run alike at EVERY adaptive
--     distinguisher.  This is the induction that identifies a coupling's
--     marginals with the reference kernels they are supposed to be:
--     `Examples.MerkleDamgard.Core`'s `ghost-erase` (real side) and
--     `ideal-marginal` (ideal side) are its two instances, and both are
--     EXACT — no ε.
--   • `hop-bound` — the ε-statement.  With both marginals identified and a
--     `SuperCert` bounding the coupling's flag, the advantage of any m-query
--     distinguisher between the two REFERENCE kernels is at most `ε m`.
--     `Coupling.FLGP` supplies the identical-until-bad half and
--     `badProb-bounded` the supermartingale half; this is the last step of
--     every proof in that shape.
--   • `runWith-join` — the same identical-until-bad half for two kernels that
--     keep their OWN state spaces: instead of one coupled kernel with two
--     projections, each step exhibits a joint draw whose marginals are the two
--     kernels.  `Coupling.FLGP` is the case where that join is `respB`'s two
--     projections; where the two games' states diverge once the flag is up,
--     carrying both of them inside one coupled state is exactly what this
--     avoids.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational using (ℚ; 0ℚ) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; +-inverseʳ; 0≤p⇒∣p∣≡p)
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation

module CategoricalCrypto.GamePlaying.Hop where

------------------------------------------------------------------------
-- Coupled kernels run alike

module _ {Q R St St′ : Type} (resp : St → Q → Dist-ℚ (St × R))
         (resp′ : St′ → Q → Dist-ℚ (St′ × R)) (_≋_ : St → St′ → Type) where

  -- One query's coupling: at related states the two kernels give the same
  -- expectation to integrands that cannot tell related outcomes apart.  The
  -- relation is what carries the ancillary state one side has and the other
  -- does not (a flag, a ghost table).
  StepBisim : Type
  StepBisim = ∀ s s′ → s ≋ s′ → ∀ q (F : St × R → ℚ) (F′ : St′ × R → ℚ)
            → (∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ proj₂ t′ → F t ≡ F′ t′)
            → E (resp s q) F ≡ E (resp′ s′ q) F′

  runWith-bisim : StepBisim → ∀ d s s′ → s ≋ s′
                → Pr₁ (runWith resp s d) ≡ Pr₁ (runWith resp′ s′ d)
  runWith-bisim bis (out b) s s′ rel = refl
  runWith-bisim bis (ask q k) s s′ rel =
    trans (Pr₁-bind (resp s q) K)
   (trans (bis s s′ rel q (λ t → Pr₁ (K t)) (λ t′ → Pr₁ (K′ t′)) point)
          (sym (Pr₁-bind (resp′ s′ q) K′)))
    where
      K  = λ (t : St × R) → runWith resp (proj₁ t) (k (proj₂ t))
      K′ = λ (t′ : St′ × R) → runWith resp′ (proj₁ t′) (k (proj₂ t′))
      point : ∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ proj₂ t′ → Pr₁ (K t) ≡ Pr₁ (K′ t′)
      point t t′ r eq =
        subst (λ z → Pr₁ (K t) ≡ Pr₁ (runWith resp′ (proj₁ t′) (k z))) eq
          (runWith-bisim bis (k (proj₂ t)) (proj₁ t) (proj₁ t′) r)
  runWith-bisim bis (coin μ k) s s′ rel =
    trans (Pr₁-bind μ (λ b → runWith resp s (k b)))
   (trans (lookupᴰℚ-cong-P (entries μ) (λ b → runWith-bisim bis (k b) s s′ rel))
          (sym (Pr₁-bind μ (λ b → runWith resp′ s′ (k b)))))

------------------------------------------------------------------------
-- Coupled up to the flag

module _ {Q R S S′ : Type} (resp : S → Q → Dist-ℚ (S × R))
         (resp′ : S′ → Q → Dist-ℚ (S′ × R)) (bad : S → Bool)
         (_≋_ : S → S′ → Type) where

  -- One query's coupling UP TO the flag: at related states the two kernels
  -- are the two marginals of a single joint draw, every outcome of which has
  -- either kept the two sides related with the same answer, or raised the
  -- flag.  Because the relation is dropped as soon as the flag is up, neither
  -- side has to be tracked inside the other's state after they part.
  JoinStep : Type
  JoinStep = ∀ s s′ → s ≋ s′ → ∀ q
           → Σ[ ν ∈ Dist-ℚ ((S × R) × (S′ × R)) ]
               ( (∀ F  → E ν (λ p → F  (proj₁ p)) ≡ E (resp  s  q) F )
               × (∀ F′ → E ν (λ p → F′ (proj₂ p)) ≡ E (resp′ s′ q) F′)
               × OnSupport (λ p → (bad (proj₁ (proj₁ p)) ≡ true)
                                ⊎ ((proj₁ (proj₁ p) ≋ proj₁ (proj₂ p))
                                   × (proj₂ (proj₁ p) ≡ proj₂ (proj₂ p)))) ν )

  runWith-join : (∀ s s′ → s ≋ s′ → bad s ≡ false) → JoinStep
               → ∀ d s s′ → s ≋ s′
               → ∣ Pr₁ (runWith resp s d) -ℚ Pr₁ (runWith resp′ s′ d) ∣ℚ
                 ≤ℚ badProb resp bad s d
  runWith-join good jn (out b) s s′ rel =
    subst (_≤ℚ bool→ℚ (bad s)) (sym lhs≡0) (0≤bool (bad s))
    where lhs≡0 : ∣ Pr₁ (return-ℚ b) -ℚ Pr₁ (return-ℚ b) ∣ℚ ≡ 0ℚ
          lhs≡0 = trans (cong ∣_∣ℚ (+-inverseʳ (Pr₁ (return-ℚ b))))
                        (0≤p⇒∣p∣≡p ≤-refl)
  runWith-join good jn (ask q k) s s′ rel rewrite good s s′ rel =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) eqL eqR))
     (≤-trans (E-abs-diff ν AL AR)
     (≤-trans (E-mono-on ν (λ p → ∣ AL p -ℚ AR p ∣ℚ) BB (ListAll.map dominated sup))
              (≤-reflexive (mL (λ t → badProb resp bad (proj₁ t) (k (proj₂ t)))))))
    where
      jnq = jn s s′ rel q
      ν   = proj₁ jnq
      mL  = proj₁ (proj₂ jnq)
      mR  = proj₁ (proj₂ (proj₂ jnq))
      sup = proj₂ (proj₂ (proj₂ jnq))

      KL = λ (t  : S  × R) → runWith resp  (proj₁ t ) (k (proj₂ t ))
      KR = λ (t′ : S′ × R) → runWith resp′ (proj₁ t′) (k (proj₂ t′))

      AL AR BB : (S × R) × (S′ × R) → ℚ
      AL p = Pr₁ (KL (proj₁ p))
      AR p = Pr₁ (KR (proj₂ p))
      BB p = badProb resp bad (proj₁ (proj₁ p)) (k (proj₂ (proj₁ p)))

      eqL : Pr₁ (runWith resp s (ask q k)) ≡ E ν AL
      eqL = trans (Pr₁-bind (resp s q) KL) (sym (mL (λ t → Pr₁ (KL t))))

      eqR : Pr₁ (runWith resp′ s′ (ask q k)) ≡ E ν AR
      eqR = trans (Pr₁-bind (resp′ s′ q) KR) (sym (mR (λ t′ → Pr₁ (KR t′))))

      dominated : ∀ {p} → (bad (proj₁ (proj₁ p)) ≡ true)
                        ⊎ ((proj₁ (proj₁ p) ≋ proj₁ (proj₂ p))
                           × (proj₂ (proj₁ p) ≡ proj₂ (proj₂ p)))
                → ∣ AL p -ℚ AR p ∣ℚ ≤ℚ BB p
      dominated {p} (inj₁ bd) =
        subst (∣ AL p -ℚ AR p ∣ℚ ≤ℚ_)
              (sym (badProb-bad resp bad (proj₁ (proj₁ p)) (k (proj₂ (proj₁ p))) bd))
              (∣Pr-Pr∣≤1 (KL (proj₁ p)) (KR (proj₂ p)))
      dominated {p} (inj₂ (rel′ , ans)) =
        subst (λ z → ∣ AL p -ℚ Pr₁ (runWith resp′ (proj₁ (proj₂ p)) (k z)) ∣ℚ ≤ℚ BB p)
              ans (runWith-join good jn (k (proj₂ (proj₁ p)))
                     (proj₁ (proj₁ p)) (proj₁ (proj₂ p)) rel′)
  runWith-join good jn (coin μ k) s s′ rel rewrite good s s′ rel =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
                             (Pr₁-bind μ (λ b → runWith resp  s  (k b)))
                             (Pr₁-bind μ (λ b → runWith resp′ s′ (k b)))))
     (≤-trans (E-abs-diff μ AL AR)
              (E-mono μ (λ b → ∣ AL b -ℚ AR b ∣ℚ) BB
                (λ b → runWith-join good jn (k b) s s′ rel)))
    where
      AL AR BB : Bool → ℚ
      AL b = Pr₁ (runWith resp  s  (k b))
      AR b = Pr₁ (runWith resp′ s′ (k b))
      BB b = badProb resp bad s (k b)

------------------------------------------------------------------------
-- The hop

module _ {Q R St StR StI : Type} (bad : St → Bool)
         (respB : St → Q → Dist-ℚ (St × (R × R))) where

  open Coupling bad respB

  hop-bound : {ε : ℕ → ℚ} (respR : StR → Q → Dist-ℚ (StR × R))
              (respI : StI → Q → Dist-ℚ (StI × R)) (s₀ : St) (sR : StR) (sI : StI)
            → (∀ d → Pr₁ (runWith realK s₀ d) ≡ Pr₁ (runWith respR sR d))
            → (∀ d → Pr₁ (runWith idealK s₀ d) ≡ Pr₁ (runWith respI sI d))
            → SuperCert realK bad s₀ ε
            → ∀ m d → asks≤ m d
            → ∣ Pr₁ (runWith respI sI d) -ℚ Pr₁ (runWith respR sR d) ∣ℚ ≤ℚ ε m
  hop-bound {ε} respR respI s₀ sR sI eR eI cert m d le =
    subst (_≤ℚ ε m) (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) (eI d) (eR d))
      (≤-trans (FLGP s₀ d) (badProb-bounded cert m d le))
