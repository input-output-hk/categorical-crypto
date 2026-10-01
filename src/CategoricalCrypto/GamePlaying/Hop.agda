{-# OPTIONS --safe --without-K #-}

-- Assembling a game hop out of `GamePlaying`'s two bridges.
--
--   • `runWith-bisim` — two kernels COUPLED step by step (their one-query
--     expectations agree at related states, on any pair of integrands that
--     agrees at related outcomes) run alike at EVERY adaptive distinguisher,
--     exactly.  This identifies a coupling's marginals with the reference
--     kernels they stand for.
--   • `hop-bound` — with both marginals identified and a `SuperCert` bounding
--     the coupling's flag, the advantage of any m-query distinguisher between
--     the two REFERENCE kernels is at most `ε m`.
--   • `runWith-join` — the identical-until-bad half for two kernels that keep
--     their OWN state spaces: each step exhibits a joint draw whose marginals
--     are the two kernels.  `FLGP` is the case where that join is
--     `respB`'s two projections; where the two games' states diverge once the
--     flag is up, carrying both inside one coupled state is what this avoids.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

module CategoricalCrypto.GamePlaying.Hop where

------------------------------------------------------------------------
-- Coupled kernels run alike

module _ {Q R St St′ : Type} (resp : St → Q → Dist-ℚ (St × R))
         (resp′ : St′ → Q → Dist-ℚ (St′ × R)) (_≋_ : St → St′ → Type) where

  -- The relation carries the ancillary state one side has and the other does
  -- not (a flag, a ghost table).
  StepBisim : Type
  StepBisim = ∀ s s′ → s ≋ s′ → ∀ q (F : St × R → ℚ) (F′ : St′ × R → ℚ)
            → (∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ proj₂ t′ → F t ≡ F′ t′)
            → E (resp s q) F ≡ E (resp′ s′ q) F′

  -- Both kernels cut where related states agree to cut: on the cut both
  -- score nothing, off it the coupling is the total one.
  prune-bisim : (dead : St → Q → Bool) (dead′ : St′ → Q → Bool)
              → (∀ s s′ → s ≋ s′ → ∀ q → dead s q ≡ dead′ s′ q)
              → StepBisim → StepBisim⊥ (prune dead resp) (prune dead′ resp′) _≋_
  prune-bisim dead dead′ agree bis s s′ r q F F′ h rewrite agree s s′ r q with dead′ s′ q
  ... | true  = E-return-cong nothing nothing (maybeℚ F) (maybeℚ F′) refl
  ... | false = trans (Eⱼ (resp s q) F) (trans (bis s s′ r q F F′ h) (sym (Eⱼ (resp′ s′ q) F′)))

  runWith-bisim : StepBisim → ∀ d s s′ → s ≋ s′
                → Pr₁ (runWith resp s d) ≡ Pr₁ (runWith resp′ s′ d)
  runWith-bisim bis d s s′ rel =
    trans (sym (total⇒⊥ resp s d))
   (trans (runWith⊥-bisim (embedᵏ resp) (embedᵏ resp′) _≋_
            (prune-bisim (λ _ _ → false) (λ _ _ → false) (λ _ _ _ _ → refl) bis) d s s′ rel bool→ℚ)
          (total⇒⊥ resp′ s′ d))

------------------------------------------------------------------------
-- Coupled up to the flag

module _ {Q R S S′ : Type} (resp : S → Q → Dist-ℚ (S × R))
         (resp′ : S′ → Q → Dist-ℚ (S′ × R)) (bad : S → Bool)
         (_≋_ : S → S′ → Type) where

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
    subst (_≤ℚ bool→ℚ (bad s)) (sym (∣x-x∣≡0 (Pr₁ (return-ℚ b)))) (0≤bool (bad s))
  runWith-join good jn (ask q k) s s′ rel =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) eqL eqR))
     (≤-trans (E-abs-diff ν AL AR)
     (≤-trans (E-mono-on ν (λ p → ∣ AL p -ℚ AR p ∣ℚ) BB (ListAll.map dominated sup))
              (≤-reflexive (trans (mL (λ t → badProb resp bad (proj₁ t) (k (proj₂ t))))
                           (trans (sym (Eⱼ (resp s q) _))
                                  (sym (badProb⊥-ask (embedᵏ resp) bad s q k (good s s′ rel))))))))
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
              (sym (badProb⊥-bad (embedᵏ resp) bad (proj₁ (proj₁ p)) (k (proj₂ (proj₁ p))) bd))
              (∣Pr-Pr∣≤1 (KL (proj₁ p)) (KR (proj₂ p)))
      dominated {p} (inj₂ (rel′ , ans)) =
        subst (λ z → ∣ AL p -ℚ Pr₁ (runWith resp′ (proj₁ (proj₂ p)) (k z)) ∣ℚ ≤ℚ BB p)
              ans (runWith-join good jn (k (proj₂ (proj₁ p)))
                     (proj₁ (proj₁ p)) (proj₁ (proj₂ p)) rel′)
  runWith-join good jn (coin μ k) s s′ rel =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
                             (Pr₁-bind μ (λ b → runWith resp  s  (k b)))
                             (Pr₁-bind μ (λ b → runWith resp′ s′ (k b)))))
     (≤-trans (E-abs-diff μ AL AR)
     (≤-trans (E-mono μ (λ b → ∣ AL b -ℚ AR b ∣ℚ) BB
                (λ b → runWith-join good jn (k b) s s′ rel))
              (≤-reflexive (sym (badProb⊥-coin (embedᵏ resp) bad s μ k (good s s′ rel))))))
    where
      AL AR BB : Bool → ℚ
      AL b = Pr₁ (runWith resp  s  (k b))
      AR b = Pr₁ (runWith resp′ s′ (k b))
      BB b = badProb resp bad s (k b)

module _ {Q R St StR StI : Type} (bad : St → Bool)
         (respB : St → Q → Dist-ℚ (St × (R × R))) where

  open Coupling bad respB

  private
    _≈_ : St → St → Type
    s ≈ s′ = s ≡ s′ × bad s ≡ false

    coupled : JoinStep realK idealK bad _≈_
    coupled s .s (refl , _) q =
        Dmap (λ t → fR t , fI t) (respB s q)
      , (λ F → trans (lookupᴰℚ-Dmap _ (respB s q) _) (sym (lookupᴰℚ-Dmap fR (respB s q) F)))
      , (λ F → trans (lookupᴰℚ-Dmap _ (respB s q) _) (sym (lookupᴰℚ-Dmap fI (respB s q) F)))
      , OnSupport-Dmap _ (respB s q) (ListAll.tabulate λ {e} _ → pt (proj₂ e))
      where
      pt : ∀ t → (bad (proj₁ t) ≡ true)
               ⊎ ((proj₁ t ≈ proj₁ t)
                  × (proj₁ (proj₂ t) ≡ cond (bad (proj₁ t)) (proj₂ (proj₂ t)) (proj₁ (proj₂ t))))
      pt t with bad (proj₁ t)
      ... | true  = inj₁ refl
      ... | false = inj₂ ((refl , refl) , refl)

  -- The coupled Fundamental Lemma: identical until bad by construction, so the
  -- join is the coupling itself.
  FLGP : ∀ s₀ d → ∣ Pr₁ (runWith idealK s₀ d) -ℚ Pr₁ (runWith realK s₀ d) ∣ℚ
                ≤ℚ badProb realK bad s₀ d
  FLGP s d = split (bad s) refl
    where
    split : ∀ b → bad s ≡ b → ∣ Pr₁ (runWith idealK s d) -ℚ Pr₁ (runWith realK s d) ∣ℚ
                              ≤ℚ badProb realK bad s d
    split true  eqb = subst (∣ Pr₁ (runWith idealK s d) -ℚ Pr₁ (runWith realK s d) ∣ℚ ≤ℚ_)
                        (sym (badProb⊥-bad (embedᵏ realK) bad s d eqb))
                        (∣Pr-Pr∣≤1 (runWith idealK s d) (runWith realK s d))
    split false eqb = subst (_≤ℚ badProb realK bad s d)
                        (∣-∣-comm (Pr₁ (runWith realK s d)) (Pr₁ (runWith idealK s d)))
                        (runWith-join realK idealK bad _≈_ (λ _ _ → proj₂) coupled d s s (refl , eqb))

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
