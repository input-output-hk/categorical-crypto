{-# OPTIONS --safe --without-K #-}

-- `GamePlaying`'s two bridges at a PARTIAL kernel.
--
-- A machine's step DIVERGES where a game's kernel idles, so the transport of
-- `Protocol.Machine.Raw` lands on a `Dist⊥`-valued kernel and the total
-- statements do not apply to it.  `Dist⊥` is `Dist-ℚ ∘ Maybe`, so every
-- statement below is its total counterpart with `E⊥`/`Pr₁⊥`/`OnSupport⊥` in
-- place of `E`/`Pr₁`/`OnSupport`, and every proof is the same induction: the
-- sink scores 0, which only helps the supermartingale and which the coupling
-- carries through untouched.
--
-- `GamePlaying`'s own statements are the special case at `embedᵏ`: `total⇒⊥`
-- identifies the two runs and `prune`/`prune-cert` are the general form, where
-- a kernel is cut down to the activations a machine actually serves.  They are
-- kept as they are — every existing consumer is stated at them.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
  renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans; +-inverseʳ; 0≤p⇒∣p∣≡p)

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

module CategoricalCrypto.GamePlaying.Partial where

private variable Q R St : Type

-- `Pr₁⊥` through the coin junction, whose distribution is total.
private
  Pr₁⊥-coin : (μ : Dist-ℚ Bool) (k : Bool → Dist⊥ Bool)
            → Pr₁⊥ (μ >>=ᴹ k) ≡ E μ (λ b → Pr₁⊥ (k b))
  Pr₁⊥-coin μ k = E-bind μ k mb

------------------------------------------------------------------------
-- The bad event

badProb⊥ : (St → Q → Dist⊥ (St × R)) → (St → Bool) → St → Strat Q R → ℚ
badProb⊥ resp bad s (out _)    = bool→ℚ (bad s)
badProb⊥ resp bad s (ask q k)  with bad s
... | true  = 1ℚ
... | false = E⊥ (resp s q) (λ sr → badProb⊥ resp bad (proj₁ sr) (k (proj₂ sr)))
badProb⊥ resp bad s (coin μ k) with bad s
... | true  = 1ℚ
... | false = E μ (λ b → badProb⊥ resp bad s (k b))

badProb⊥-bad : (resp : St → Q → Dist⊥ (St × R)) (bad : St → Bool)
             → ∀ s (d : Strat Q R) → bad s ≡ true → badProb⊥ resp bad s d ≡ 1ℚ
badProb⊥-bad resp bad s (out _)    eq rewrite eq = refl
badProb⊥-bad resp bad s (ask q k)  eq rewrite eq = refl
badProb⊥-bad resp bad s (coin μ k) eq rewrite eq = refl

------------------------------------------------------------------------
-- What a concrete system owes

-- Divergence constrains nothing: an activation the machine refuses to serve
-- reaches no state, so it preserves any invariant.
Preserved⊥ : (St → Type) → (St → Q → Dist⊥ (St × R)) → Type
Preserved⊥ Inv resp = ∀ s q → Inv s → OnSupport⊥ (λ sr → Inv (proj₁ sr)) (resp s q)

record SuperCert⊥ (resp : St → Q → Dist⊥ (St × R)) (bad : St → Bool)
                  (s₀ : St) (ε : ℕ → ℚ) : Type₁ where
  field
    Inv    : St → Type
    φ      : ℕ → St → ℚ
    inv₀   : Inv s₀
    pres   : Preserved⊥ Inv resp
    φ-nn   : ∀ m s → Inv s → 0ℚ ≤ℚ φ m s
    φ-bad  : ∀ m s → Inv s → bad s ≡ true → 1ℚ ≤ℚ φ m s
    φ-step : ∀ m s q → Inv s → E⊥ (resp s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s
    φ-init : ∀ m → φ m s₀ ≤ℚ ε m

------------------------------------------------------------------------
-- The two bridges

badProb⊥-super :
  (resp : St → Q → Dist⊥ (St × R)) (bad : St → Bool)
  (Inv : St → Type) (φ : ℕ → St → ℚ)
  → Preserved⊥ Inv resp
  → (∀ m s → Inv s → 0ℚ ≤ℚ φ m s)
  → (∀ m s → Inv s → bad s ≡ true → 1ℚ ≤ℚ φ m s)
  → (∀ m s q → Inv s → E⊥ (resp s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s)
  → ∀ m d s → asks≤ m d → Inv s → badProb⊥ resp bad s d ≤ℚ φ m s
badProb⊥-super resp bad Inv φ pres nn lb step m (out b) s le inv with bad s in eqb
... | true  = lb m s inv eqb
... | false = nn m s inv
badProb⊥-super resp bad Inv φ pres nn lb step zero (ask q kd) s () inv
badProb⊥-super resp bad Inv φ pres nn lb step (suc m) (ask q kd) s le inv
  with bad s in eqb
... | true  = lb (suc m) s inv eqb
... | false = ≤-trans
    (E⊥-mono-on (resp s q)
      (λ sr → badProb⊥ resp bad (proj₁ sr) (kd (proj₂ sr)))
      (λ sr → φ m (proj₁ sr))
      (ListAll.map (λ {e} → sink (proj₂ e)) (pres s q inv)))
    (step m s q inv)
  where
  sink : (x : Maybe _)
       → Mb (λ sr → Inv (proj₁ sr)) x
       → Mb (λ sr → badProb⊥ resp bad (proj₁ sr) (kd (proj₂ sr)) ≤ℚ φ m (proj₁ sr)) x
  sink (just sr) inv′ = badProb⊥-super resp bad Inv φ pres nn lb step m
                          (kd (proj₂ sr)) (proj₁ sr) (le (proj₂ sr)) inv′
  sink nothing   _    = tt
badProb⊥-super resp bad Inv φ pres nn lb step m (coin μ kd) s le inv with bad s in eqb
... | true  = lb m s inv eqb
... | false = ≤-trans
    (E-mono μ (λ b → badProb⊥ resp bad s (kd b)) (λ _ → φ m s)
      (λ b → badProb⊥-super resp bad Inv φ pres nn lb step m (kd b) s (le b) inv))
    (≤-reflexive (E-const μ (φ m s)))

badProb⊥-bounded :
  {resp : St → Q → Dist⊥ (St × R)} {bad : St → Bool} {s₀ : St} {ε : ℕ → ℚ}
  → SuperCert⊥ resp bad s₀ ε
  → ∀ m d → asks≤ m d → badProb⊥ resp bad s₀ d ≤ℚ ε m
badProb⊥-bounded {resp = resp} {bad} {s₀} c m d le = ≤-trans
  (badProb⊥-super resp bad (SuperCert⊥.Inv c) (SuperCert⊥.φ c) (SuperCert⊥.pres c)
    (SuperCert⊥.φ-nn c) (SuperCert⊥.φ-bad c) (SuperCert⊥.φ-step c)
    m d s₀ le (SuperCert⊥.inv₀ c))
  (SuperCert⊥.φ-init c m)

------------------------------------------------------------------------
-- The coupled Fundamental Lemma of Game-Playing, partially

module Coupling⊥ (bad : St → Bool)
                 (respB : St → Q → Dist⊥ (St × (R × R))) where

  fR fI : St × (R × R) → St × R
  fR t = proj₁ t , proj₁ (proj₂ t)
  fI t = proj₁ t , cond (bad (proj₁ t)) (proj₂ (proj₂ t)) (proj₁ (proj₂ t))

  realK idealK : St → Q → Dist⊥ (St × R)
  realK  s q = Dmap⊥ fR (respB s q)
  idealK s q = Dmap⊥ fI (respB s q)

  FLGP⊥ : ∀ s₀ d → ∣ Pr₁⊥ (runWith⊥ idealK s₀ d) -ℚ Pr₁⊥ (runWith⊥ realK s₀ d) ∣ℚ
                 ≤ℚ badProb⊥ realK bad s₀ d
  FLGP⊥ s (out b) = subst (_≤ℚ bool→ℚ (bad s)) (sym lhs≡0) (0≤bool (bad s))
    where lhs≡0 : ∣ Pr₁⊥ (return⊥ b) -ℚ Pr₁⊥ (return⊥ b) ∣ℚ ≡ 0ℚ
          lhs≡0 = trans (cong ∣_∣ℚ (+-inverseʳ (Pr₁⊥ (return⊥ b))))
                        (0≤p⇒∣p∣≡p ≤-refl)
  FLGP⊥ s (ask q k) with bad s in eqbad
  ... | true  = ∣Pr⊥-Pr⊥∣≤1 (runWith⊥ idealK s (ask q k)) (runWith⊥ realK s (ask q k))
  ... | false =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) eqI eqR))
     (≤-trans (E⊥-abs-diff (respB s q) AI AR)
     (≤-trans (E⊥-mono (respB s q) (λ t → ∣ AI t -ℚ AR t ∣ℚ) BB pointwise)
              (≤-reflexive (sym eqB))))
    where
      KI KR : St × R → Dist⊥ Bool
      KI sr = runWith⊥ idealK (proj₁ sr) (k (proj₂ sr))
      KR sr = runWith⊥ realK  (proj₁ sr) (k (proj₂ sr))

      AI AR BB : St × (R × R) → ℚ
      AI t = Pr₁⊥ (KI (fI t))
      AR t = Pr₁⊥ (KR (fR t))
      BB t = badProb⊥ realK bad (proj₁ t) (k (proj₁ (proj₂ t)))

      eqI : Pr₁⊥ (runWith⊥ idealK s (ask q k)) ≡ E⊥ (respB s q) AI
      eqI = trans (E⊥-bind (idealK s q) KI (λ b → bool→ℚ b))
                  (E⊥-map fI (respB s q) (λ sr → Pr₁⊥ (KI sr)))

      eqR : Pr₁⊥ (runWith⊥ realK s (ask q k)) ≡ E⊥ (respB s q) AR
      eqR = trans (E⊥-bind (realK s q) KR (λ b → bool→ℚ b))
                  (E⊥-map fR (respB s q) (λ sr → Pr₁⊥ (KR sr)))

      eqB : E⊥ (realK s q) (λ sr → badProb⊥ realK bad (proj₁ sr) (k (proj₂ sr)))
          ≡ E⊥ (respB s q) BB
      eqB = E⊥-map fR (respB s q)
              (λ sr → badProb⊥ realK bad (proj₁ sr) (k (proj₂ sr)))

      pointwise : ∀ t → ∣ AI t -ℚ AR t ∣ℚ ≤ℚ BB t
      pointwise t with bad (proj₁ t) in eqt
      ... | false = FLGP⊥ (proj₁ t) (k (proj₁ (proj₂ t)))
      ... | true  =
        subst (λ z → ∣ Pr₁⊥ (KI (proj₁ t , proj₂ (proj₂ t))) -ℚ AR t ∣ℚ ≤ℚ z)
              (sym (badProb⊥-bad realK bad (proj₁ t) (k (proj₁ (proj₂ t))) eqt))
              (∣Pr⊥-Pr⊥∣≤1 (KI (proj₁ t , proj₂ (proj₂ t))) (KR (fR t)))
  FLGP⊥ s (coin μ k) with bad s
  ... | true  = ∣Pr⊥-Pr⊥∣≤1 (runWith⊥ idealK s (coin μ k)) (runWith⊥ realK s (coin μ k))
  ... | false =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
                             (Pr₁⊥-coin μ (λ b → runWith⊥ idealK s (k b)))
                             (Pr₁⊥-coin μ (λ b → runWith⊥ realK s (k b)))))
     (≤-trans (E-abs-diff μ AI AR)
              (E-mono μ (λ b → ∣ AI b -ℚ AR b ∣ℚ) BB (λ b → FLGP⊥ s (k b))))
    where
      AI AR BB : Bool → ℚ
      AI b = Pr₁⊥ (runWith⊥ idealK s (k b))
      AR b = Pr₁⊥ (runWith⊥ realK  s (k b))
      BB b = badProb⊥ realK bad s (k b)

------------------------------------------------------------------------
-- Coupled partial kernels run alike

module _ {Q R St St′ : Type} (resp : St → Q → Dist⊥ (St × R))
         (resp′ : St′ → Q → Dist⊥ (St′ × R)) (_≋_ : St → St′ → Type) where

  StepBisim⊥ : Type
  StepBisim⊥ = ∀ s s′ → s ≋ s′ → ∀ q (F : St × R → ℚ) (F′ : St′ × R → ℚ)
             → (∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ proj₂ t′ → F t ≡ F′ t′)
             → E⊥ (resp s q) F ≡ E⊥ (resp′ s′ q) F′

  runWith⊥-bisim : StepBisim⊥ → ∀ d s s′ → s ≋ s′
                 → Pr₁⊥ (runWith⊥ resp s d) ≡ Pr₁⊥ (runWith⊥ resp′ s′ d)
  runWith⊥-bisim bis (out b) s s′ rel = refl
  runWith⊥-bisim bis (ask q k) s s′ rel =
    trans (E⊥-bind (resp s q) K (λ b → bool→ℚ b))
   (trans (bis s s′ rel q (λ t → Pr₁⊥ (K t)) (λ t′ → Pr₁⊥ (K′ t′)) point)
          (sym (E⊥-bind (resp′ s′ q) K′ (λ b → bool→ℚ b))))
    where
      K  = λ (t : St × R) → runWith⊥ resp (proj₁ t) (k (proj₂ t))
      K′ = λ (t′ : St′ × R) → runWith⊥ resp′ (proj₁ t′) (k (proj₂ t′))
      point : ∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ proj₂ t′ → Pr₁⊥ (K t) ≡ Pr₁⊥ (K′ t′)
      point t t′ r eq =
        subst (λ z → Pr₁⊥ (K t) ≡ Pr₁⊥ (runWith⊥ resp′ (proj₁ t′) (k z))) eq
          (runWith⊥-bisim bis (k (proj₂ t)) (proj₁ t) (proj₁ t′) r)
  runWith⊥-bisim bis (coin μ k) s s′ rel =
    trans (Pr₁⊥-coin μ (λ b → runWith⊥ resp s (k b)))
   (trans (lookupᴰℚ-cong-P (entries μ) (λ b → runWith⊥-bisim bis (k b) s s′ rel))
          (sym (Pr₁⊥-coin μ (λ b → runWith⊥ resp′ s′ (k b)))))

------------------------------------------------------------------------
-- Where the two layers meet: pruning a total kernel
--
-- A machine serves an activation or diverges on it.  `prune dead K` is the
-- kernel `K` cut down to the served ones, and `dead ≡ λ _ _ → false` is the
-- embedding of `K` itself.  `total⇒⊥` says the embedding changes no run, and
-- `prune-cert` says a supermartingale survives the cut — the dead branch
-- scores 0, which `φ-nn` already dominates.

embedᵏ : (St → Q → Dist-ℚ (St × R)) → St → Q → Dist⊥ (St × R)
embedᵏ K s q = Dmap just (K s q)

total⇒⊥ : (K : St → Q → Dist-ℚ (St × R)) (s : St) (d : Strat Q R)
        → Pr₁⊥ (runWith⊥ (embedᵏ K) s d) ≡ Pr₁ (runWith K s d)
total⇒⊥ K s d =
  trans (Pr₁⊥-cong (runWith⊥ (embedᵏ K) s d) (Dmap just (runWith K s d))
                   (runWith⊥-emb K (embedᵏ K) (λ x → x) (λ _ _ _ → refl) s d))
        (Pr₁⊥-just (runWith K s d))

prune : (St → Q → Bool) → (St → Q → Dist-ℚ (St × R)) → St → Q → Dist⊥ (St × R)
prune dead K s q = cond (dead s q) (return-ℚ nothing) (embedᵏ K s q)

prune-cert : {Q R St : Type} {K : St → Q → Dist-ℚ (St × R)} {bad : St → Bool}
             {s₀ : St} {ε : ℕ → ℚ} (dead : St → Q → Bool)
           → SuperCert K bad s₀ ε → SuperCert⊥ (prune dead K) bad s₀ ε
prune-cert {R = R} {St = St} {K = K} dead c = record
  { Inv = C.Inv ; φ = C.φ ; inv₀ = C.inv₀ ; φ-nn = C.φ-nn ; φ-bad = C.φ-bad
  ; φ-init = C.φ-init ; pres = pres⊥ ; φ-step = step⊥ }
  where
  module C = SuperCert c

  Φ : ℕ → St × R → ℚ
  Φ m sr = C.φ m (proj₁ sr)

  pres⊥ : Preserved⊥ C.Inv (prune dead K)
  pres⊥ s q inv with dead s q
  ... | true  = OnSupport-return tt
  ... | false = OnSupport-Dmap just (K s q) (C.pres s q inv)

  step⊥ : ∀ m s q → C.Inv s
        → E⊥ (prune dead K s q) (λ sr → C.φ m (proj₁ sr)) ≤ℚ C.φ (suc m) s
  step⊥ m s q inv with dead s q
  ... | true  = ≤-trans (≤-reflexive (lookupᴰℚ-return nothing (maybeℚ (Φ m))))
                        (C.φ-nn (suc m) s inv)
  ... | false = ≤-trans (≤-reflexive (Eⱼ (K s q) (Φ m))) (C.φ-step m s q inv)

------------------------------------------------------------------------
-- The hop

module _ {Q R St StR StI : Type} (bad : St → Bool)
         (respB : St → Q → Dist⊥ (St × (R × R))) where

  open Coupling⊥ bad respB

  hop-bound⊥ : {ε : ℕ → ℚ} (respR : StR → Q → Dist⊥ (StR × R))
               (respI : StI → Q → Dist⊥ (StI × R)) (s₀ : St) (sR : StR) (sI : StI)
             → (∀ d → Pr₁⊥ (runWith⊥ realK s₀ d) ≡ Pr₁⊥ (runWith⊥ respR sR d))
             → (∀ d → Pr₁⊥ (runWith⊥ idealK s₀ d) ≡ Pr₁⊥ (runWith⊥ respI sI d))
             → SuperCert⊥ realK bad s₀ ε
             → ∀ m d → asks≤ m d
             → ∣ Pr₁⊥ (runWith⊥ respI sI d) -ℚ Pr₁⊥ (runWith⊥ respR sR d) ∣ℚ ≤ℚ ε m
  hop-bound⊥ {ε} respR respI s₀ sR sI eR eI cert m d le =
    subst (_≤ℚ ε m) (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) (eI d) (eR d))
      (≤-trans (FLGP⊥ s₀ d) (badProb⊥-bounded cert m d le))
