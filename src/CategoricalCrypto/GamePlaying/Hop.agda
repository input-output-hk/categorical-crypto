{-# OPTIONS --safe --without-K #-}

-- Assembling a game hop: `runWith-bisim` identifies a coupling's marginals with
-- the reference kernels they stand for, and `hop-bound` then bounds the
-- advantage between the two reference kernels by the coupling's `SuperCert`.
-- `runWith-join` is `Partial.runWith-join⊥`, the identical-until-bad step for
-- two kernels on their OWN state spaces, at total kernels.  `FLGP` is its
-- instance at `Coupling`.

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

module _ {R S S′ : Type} (bad : S → Bool) (_≋_ : S → S′ → Type) where

  -- A joint draw with marginals `μ` and `μ′` whose every outcome is flagged or
  -- related at a common answer.
  JoinAt : Dist-ℚ (S × R) → Dist-ℚ (S′ × R) → Type
  JoinAt μ μ′ = Σ[ ν ∈ Dist-ℚ ((S × R) × (S′ × R)) ]
                  ( (∀ F  → E ν (λ p → F  (proj₁ p)) ≡ E μ  F )
                  × (∀ F′ → E ν (λ p → F′ (proj₂ p)) ≡ E μ′ F′)
                  × OnSupport (λ p → (bad (proj₁ (proj₁ p)) ≡ true)
                                   ⊎ ((proj₁ (proj₁ p) ≋ proj₁ (proj₂ p))
                                      × (proj₂ (proj₁ p) ≡ proj₂ (proj₂ p)))) ν )

  join-return : (w : S × R) (w′ : S′ × R) → proj₁ w ≋ proj₁ w′ → proj₂ w ≡ proj₂ w′
              → JoinAt (return-ℚ w) (return-ℚ w′)
  join-return w w′ rel ans = return-ℚ (w , w′)
    , (λ F  → trans (lookupᴰℚ-return (w , w′) (λ p → F  (proj₁ p))) (sym (lookupᴰℚ-return w  F )))
    , (λ F′ → trans (lookupᴰℚ-return (w , w′) (λ p → F′ (proj₂ p))) (sym (lookupᴰℚ-return w′ F′)))
    , OnSupport-return (inj₂ (rel , ans))

module _ {Q R S S′ : Type} (resp : S → Q → Dist-ℚ (S × R))
         (resp′ : S′ → Q → Dist-ℚ (S′ × R)) (bad : S → Bool)
         (_≋_ : S → S′ → Type) where

  JoinStep : Type
  JoinStep = ∀ s s′ → s ≋ s′ → bad s ≡ false → ∀ q → JoinAt bad _≋_ (resp s q) (resp′ s′ q)

  -- `Partial.runWith-join⊥` at the embedded kernels.
  runWith-join : JoinStep → ∀ d s s′ → s ≋ s′
               → ∣ Pr₁ (runWith resp s d) -ℚ Pr₁ (runWith resp′ s′ d) ∣ℚ
                 ≤ℚ badProb resp bad s d
  runWith-join jn d s s′ rel =
    subst₂ (λ x y → ∣ x -ℚ y ∣ℚ ≤ℚ badProb resp bad s d) (total⇒⊥ resp s d) (total⇒⊥ resp′ s′ d)
      (runWith-join⊥ (embedᵏ resp) (embedᵏ resp′) bad _≋_ jn⊥ d s s′ rel)
    where
    jn⊥ : JoinStep⊥ (embedᵏ resp) (embedᵏ resp′) bad _≋_
    jn⊥ s s′ rel g q =
      let ν , mL , mR , sup = jn s s′ rel g q in
        Dmap just ν
      , (λ F  → trans (Eⱼ ν _) (trans (mL F ) (sym (Eⱼ (resp s q) F ))))
      , (λ F′ → trans (Eⱼ ν _) (trans (mR F′) (sym (Eⱼ (resp′ s′ q) F′))))
      , OnSupport-Dmap just ν sup

module _ {Q R St : Type} (bad : St → Bool)
         (respB : St → Q → Dist-ℚ (St × (R × R))) where

  open Coupling bad respB

  private
    coupled : JoinStep realK idealK bad _≡_
    coupled s .s refl _ q =
        Dmap (λ t → fR t , fI t) (respB s q)
      , (λ F → trans (lookupᴰℚ-Dmap _ (respB s q) _) (sym (lookupᴰℚ-Dmap fR (respB s q) F)))
      , (λ F → trans (lookupᴰℚ-Dmap _ (respB s q) _) (sym (lookupᴰℚ-Dmap fI (respB s q) F)))
      , OnSupport-Dmap _ (respB s q) (ListAll.tabulate λ {e} _ → pt (proj₂ e))
      where
      pt : ∀ t → (bad (proj₁ t) ≡ true)
               ⊎ ((proj₁ t ≡ proj₁ t)
                  × (proj₁ (proj₂ t) ≡ cond (bad (proj₁ t)) (proj₂ (proj₂ t)) (proj₁ (proj₂ t))))
      pt t with bad (proj₁ t)
      ... | true  = inj₁ refl
      ... | false = inj₂ (refl , refl)

  -- The coupled Fundamental Lemma: identical until bad by construction, so the
  -- join is the coupling itself.
  FLGP : ∀ s₀ d → ∣ Pr₁ (runWith idealK s₀ d) -ℚ Pr₁ (runWith realK s₀ d) ∣ℚ
                ≤ℚ badProb realK bad s₀ d
  FLGP s d = subst (_≤ℚ badProb realK bad s d)
                   (∣-∣-comm (Pr₁ (runWith realK s d)) (Pr₁ (runWith idealK s d)))
                   (runWith-join realK idealK bad _≡_ coupled d s s refl)

  hop-bound : {StR StI : Type} {ε : ℕ → ℚ} (respR : StR → Q → Dist-ℚ (StR × R))
              (respI : StI → Q → Dist-ℚ (StI × R)) (s₀ : St) (sR : StR) (sI : StI)
            → (∀ d → Pr₁ (runWith realK s₀ d) ≡ Pr₁ (runWith respR sR d))
            → (∀ d → Pr₁ (runWith idealK s₀ d) ≡ Pr₁ (runWith respI sI d))
            → SuperCert realK bad s₀ ε
            → ∀ m d → asks≤ m d
            → ∣ Pr₁ (runWith respI sI d) -ℚ Pr₁ (runWith respR sR d) ∣ℚ ≤ℚ ε m
  hop-bound {ε = ε} respR respI s₀ sR sI eR eI cert m d le =
    subst (_≤ℚ ε m) (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) (eI d) (eR d))
      (≤-trans (FLGP s₀ d) (badProb-bounded cert m d le))
