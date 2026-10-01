{-# OPTIONS --safe --without-K #-}

-- The supermartingale bound for a flag that reads a PLANTED secret.
--
-- No `SuperCert` bounds such a flag (see `GamePlaying.Potential`): what is
-- small is the AVERAGE of that flag over the plant, and `badProb-avg` is the bound in
-- that shape: the run is read at a FAMILY of initial states indexed by the
-- plant, and the potential is the average of the flag plus the remaining
-- query budget's worth of drift.
--
-- Two things make the induction go through where `badProb-super`'s does not.
-- `endProb` — the probability that the flag is up at the END of the run,
-- equal to `badProb` for a MONOTONE flag — has no case split on the flag, so
-- the average never has to be split inside the integral.  And a family whose
-- answers no longer depend on the plant is what lets one adaptive strategy
-- serve every plant at once; once the plant IS revealed, the strategies part,
-- and `Fz` is the frozen mode — a state the flag no longer changes from,
-- where the run's contribution is the flag itself whatever the adversary does.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

module CategoricalCrypto.GamePlaying.Average where

private variable Q R St : Type

------------------------------------------------------------------------
-- The flag at the end of the run

endProb : (St → Q → Dist-ℚ (St × R)) → (St → Bool) → St → Strat Q R → ℚ
endProb resp bad s (out _)    = bool→ℚ (bad s)
endProb resp bad s (ask q k)  = E (resp s q) (λ sr → endProb resp bad (proj₁ sr) (k (proj₂ sr)))
endProb resp bad s (coin μ k) = E μ (λ b → endProb resp bad s (k b))

module _ (resp : St → Q → Dist-ℚ (St × R)) (bad : St → Bool) where

  Monotone : Type
  Monotone = ∀ s q → bad s ≡ true → OnSupport (λ sr → bad (proj₁ sr) ≡ true) (resp s q)

  Frozen : (St → Type) → Type
  Frozen Fz = ∀ s q → Fz s
            → OnSupport (λ sr → Fz (proj₁ sr) × (bad (proj₁ sr) ≡ bad s)) (resp s q)

  endProb-frozen : {Fz : St → Type} → Frozen Fz
                 → ∀ s d → Fz s → endProb resp bad s d ≡ bool→ℚ (bad s)
  endProb-frozen frz s (out _)    fz = refl
  endProb-frozen frz s (ask q k)  fz = trans
    (E-cong-on (resp s q) (λ sr → endProb resp bad (proj₁ sr) (k (proj₂ sr)))
      (λ _ → bool→ℚ (bad s))
      (ListAll.map (λ {e} p → trans (endProb-frozen frz (proj₁ (proj₂ e))
                                       (k (proj₂ (proj₂ e))) (proj₁ p))
                                    (cong bool→ℚ (proj₂ p)))
        (frz s q fz)))
    (E-const (resp s q) (bool→ℚ (bad s)))
  endProb-frozen frz s (coin μ k) fz = trans
    (lookupᴰℚ-cong-P (entries μ) (λ b → endProb-frozen frz s (k b) fz))
    (E-const μ (bool→ℚ (bad s)))

  endProb-bad : Monotone → ∀ s d → bad s ≡ true → endProb resp bad s d ≡ 1ℚ
  endProb-bad mono s d eq = trans
    (endProb-frozen {Fz = λ s → bad s ≡ true}
       (λ s q b → ListAll.map (λ b′ → b′ , trans b′ (sym b)) (mono s q b)) s d eq)
    (cong bool→ℚ eq)

  badProb≡endProb : Monotone → ∀ s d → badProb resp bad s d ≡ endProb resp bad s d
  badProb≡endProb mono s (out b) = refl
  badProb≡endProb mono s d@(ask q k) = split (bad s) refl
    where
    split : ∀ b → bad s ≡ b → badProb resp bad s d ≡ endProb resp bad s d
    split true  eqb = trans (badProb⊥-bad (embedᵏ resp) bad s d eqb) (sym (endProb-bad mono s d eqb))
    split false eqb = trans (badProb⊥-ask (embedᵏ resp) bad s q k eqb)
      (trans (Eⱼ (resp s q) _) (lookupᴰℚ-cong-P (entries (resp s q))
        (λ sr → badProb≡endProb mono (proj₁ sr) (k (proj₂ sr)))))
  badProb≡endProb mono s d@(coin μ k) = split (bad s) refl
    where
    split : ∀ b → bad s ≡ b → badProb resp bad s d ≡ endProb resp bad s d
    split true  eqb = trans (badProb⊥-bad (embedᵏ resp) bad s d eqb) (sym (endProb-bad mono s d eqb))
    split false eqb = trans (badProb⊥-coin (embedᵏ resp) bad s μ k eqb)
      (lookupᴰℚ-cong-P (entries μ) (λ b → badProb≡endProb mono s (k b)))

------------------------------------------------------------------------
-- The averaged bound

module _ {V : Type} (μ : Dist-ℚ V) (resp : St → Q → Dist-ℚ (St × R)) (bad : St → Bool)
         (Rel : (V → St) → Type) (Fz : St → Type) (e : ℚ) where

  -- The families one adaptive distinguisher can chase at once: either the
  -- plant is still hidden — the states are related and the answer is the same
  -- whatever the plant is — or every member is frozen, where the answers are
  -- free to part.
  Cont : (V → St × R) → Type
  Cont g = (Σ[ a ∈ R ] (Rel (λ v → proj₁ (g v)) × (∀ v → proj₂ (g v) ≡ a)))
         ⊎ (∀ v → Fz (proj₁ (g v)))

  -- One query's averaged drift, in continuation-passing form: the consumer
  -- owes the exchange of `μ` with the kernel's own draws and the `e` the flag
  -- rises by, and takes the bound on the continuation as given — the shape
  -- `Defer.AvgBisim` states an averaged bisimulation in.
  AvgDrift : Type
  AvgDrift = ∀ f q → Rel f → ∀ (F : V → St × R → ℚ) (B : ℚ)
           → (∀ g → Cont g → E μ (λ v → F v (g v))
                             ≤ℚ E μ (λ v → bool→ℚ (bad (proj₁ (g v)))) +ℚ B)
           → E μ (λ v → E (resp (f v) q) (F v))
             ≤ℚ (E μ (λ v → bool→ℚ (bad (f v))) +ℚ e) +ℚ B

  private
    Φ : ℕ → (V → St) → ℚ
    Φ m f = E μ (λ v → bool→ℚ (bad (f v))) +ℚ fromℕ m *ℚ e

  endProb-avg : 0ℚ ≤ℚ e → Frozen resp bad Fz → AvgDrift
              → ∀ m d f → asks≤ m d → (Rel f ⊎ (∀ v → Fz (f v)))
              → E μ (λ v → endProb resp bad (f v) d)
                ≤ℚ E μ (λ v → bool→ℚ (bad (f v))) +ℚ fromℕ m *ℚ e
  endProb-avg 0≤e frz drift m (out b) f le ok = ≤-trans
    (≤-reflexive (sym (+-identityʳ (E μ (λ v → bool→ℚ (bad (f v)))))))
    (+-monoʳ-≤ (E μ (λ v → bool→ℚ (bad (f v)))) (0≤* (0≤fromℕ m) 0≤e))
  endProb-avg 0≤e frz drift zero (ask q k) f () ok
  endProb-avg 0≤e frz drift (suc m) (ask q k) f le (inj₂ fz) = ≤-trans
    (≤-reflexive (trans (lookupᴰℚ-cong-P (entries μ)
                          (λ v → endProb-frozen resp bad frz (f v) (ask q k) (fz v)))
                        (sym (+-identityʳ (E μ (λ v → bool→ℚ (bad (f v))))))))
    (+-monoʳ-≤ (E μ (λ v → bool→ℚ (bad (f v)))) (0≤* (0≤fromℕ (suc m)) 0≤e))
  endProb-avg 0≤e frz drift (suc m) (ask q k) f le (inj₁ rel) = ≤-trans
    (drift f q rel (λ _ sr → endProb resp bad (proj₁ sr) (k (proj₂ sr)))
      (fromℕ m *ℚ e) cont)
    (≤-reflexive (trans (+-assoc (E μ (λ v → bool→ℚ (bad (f v)))) e (fromℕ m *ℚ e))
                        (cong (E μ (λ v → bool→ℚ (bad (f v))) +ℚ_) (suc·c (fromℕ m) e))))
    where
      cont : ∀ g → Cont g
           → E μ (λ v → endProb resp bad (proj₁ (g v)) (k (proj₂ (g v))))
             ≤ℚ E μ (λ v → bool→ℚ (bad (proj₁ (g v)))) +ℚ fromℕ m *ℚ e
      cont g (inj₁ (a , rel′ , ans)) = ≤-trans
        (≤-reflexive (lookupᴰℚ-cong-P (entries μ)
          (λ v → cong (λ z → endProb resp bad (proj₁ (g v)) (k z)) (ans v))))
        (endProb-avg 0≤e frz drift m (k a) (λ v → proj₁ (g v)) (le a) (inj₁ rel′))
      cont g (inj₂ fz) = ≤-trans
        (≤-reflexive (trans (lookupᴰℚ-cong-P (entries μ)
                              (λ v → endProb-frozen resp bad frz (proj₁ (g v))
                                       (k (proj₂ (g v))) (fz v)))
                            (sym (+-identityʳ (E μ (λ v → bool→ℚ (bad (proj₁ (g v)))))))))
        (+-monoʳ-≤ (E μ (λ v → bool→ℚ (bad (proj₁ (g v))))) (0≤* (0≤fromℕ m) 0≤e))
  endProb-avg 0≤e frz drift m (coin ν k) f le ok = ≤-trans
    (≤-reflexive (E-swap μ ν (λ v b → endProb resp bad (f v) (k b))))
    (≤-trans (E-mono ν (λ b → E μ (λ v → endProb resp bad (f v) (k b))) (λ _ → Φ m f)
               (λ b → endProb-avg 0≤e frz drift m (k b) f (le b) ok))
             (≤-reflexive (E-const ν (Φ m f))))

  -- …read at `badProb`, which is what `Hop.runWith-join` hands out.
  badProb-avg : 0ℚ ≤ℚ e → Monotone resp bad → Frozen resp bad Fz → AvgDrift
              → ∀ m d f → asks≤ m d → (Rel f ⊎ (∀ v → Fz (f v)))
              → E μ (λ v → badProb resp bad (f v) d)
                ≤ℚ E μ (λ v → bool→ℚ (bad (f v))) +ℚ fromℕ m *ℚ e
  badProb-avg 0≤e mono frz drift m d f le ok = ≤-trans
    (≤-reflexive (lookupᴰℚ-cong-P (entries μ) (λ v → badProb≡endProb resp bad mono (f v) d)))
    (endProb-avg 0≤e frz drift m d f le ok)
