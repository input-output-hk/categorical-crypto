{-# OPTIONS --safe --without-K #-}

-- The supermartingale bound and the coupled Fundamental Lemma at a PARTIAL
-- kernel, which is the general case.
--
-- A machine's step DIVERGES where a game's kernel idles, so the transport of
-- `Machines.Run.Raw` lands on a `Dist⊥`-valued kernel.  The sink scores 0,
-- which only helps the supermartingale and which the coupling carries through untouched.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational
  renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext

open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform

module CategoricalCrypto.GamePlaying.Partial where

private variable Q R St : Type

-- Case combinator (the prelude hides `if_then_else_`).
cond : {A : Type} → Bool → A → A → A
cond true  x _ = x
cond false _ y = y

cond-diag : {A : Type} (b : Bool) (x : A) → cond b x x ≡ x
cond-diag true  x = refl
cond-diag false x = refl

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

-- The unfoldings at a good state, for a consumer whose goal carries a large
-- kernel: a `with` on the flag there normalises the whole goal.
badProb⊥-ask : (resp : St → Q → Dist⊥ (St × R)) (bad : St → Bool) (s : St) (q : Q)
               (k : R → Strat Q R) → bad s ≡ false
             → badProb⊥ resp bad s (ask q k)
               ≡ E⊥ (resp s q) (λ sr → badProb⊥ resp bad (proj₁ sr) (k (proj₂ sr)))
badProb⊥-ask resp bad s q k eq rewrite eq = refl

badProb⊥-coin : (resp : St → Q → Dist⊥ (St × R)) (bad : St → Bool) (s : St)
                (μ : Dist-ℚ Bool) (k : Bool → Strat Q R) → bad s ≡ false
              → badProb⊥ resp bad s (coin μ k) ≡ E μ (λ b → badProb⊥ resp bad s (k b))
badProb⊥-coin resp bad s μ k eq rewrite eq = refl

badProb⊥-cong : (resp resp′ : St → Q → Dist⊥ (St × R)) (bad : St → Bool)
              → (∀ s q (G : St × R → ℚ) → E⊥ (resp s q) G ≡ E⊥ (resp′ s q) G)
              → ∀ s (d : Strat Q R) → badProb⊥ resp bad s d ≡ badProb⊥ resp′ bad s d
badProb⊥-cong resp resp′ bad eq s (out _)   = refl
badProb⊥-cong resp resp′ bad eq s (ask q k) with bad s
... | true  = refl
... | false =
  trans (eq s q λ sr → badProb⊥ resp bad (proj₁ sr) (k (proj₂ sr)))
        (E⊥-cong-P (resp′ s q) _ _ λ sr →
          badProb⊥-cong resp resp′ bad eq (proj₁ sr) (k (proj₂ sr)))
badProb⊥-cong resp resp′ bad eq s (coin μ k) with bad s
... | true  = refl
... | false = lookupᴰℚ-cong-P (entries μ) λ b → badProb⊥-cong resp resp′ bad eq s (k b)

------------------------------------------------------------------------
-- What a concrete system owes

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
-- The supermartingale bound

module _ {resp : St → Q → Dist⊥ (St × R)} {bad : St → Bool} {s₀ : St} {ε : ℕ → ℚ}
         (c : SuperCert⊥ resp bad s₀ ε) where

  open SuperCert⊥ c

  badProb⊥-super : ∀ m d s → asks≤ m d → Inv s → badProb⊥ resp bad s d ≤ℚ φ m s
  badProb⊥-super m (out b) s le inv with bad s in eqb
  ... | true  = φ-bad m s inv eqb
  ... | false = φ-nn m s inv
  badProb⊥-super zero (ask q kd) s () inv
  badProb⊥-super (suc m) (ask q kd) s le inv with bad s in eqb
  ... | true  = φ-bad (suc m) s inv eqb
  ... | false = ≤-trans
      (E⊥-mono-on (resp s q)
        (λ sr → badProb⊥ resp bad (proj₁ sr) (kd (proj₂ sr)))
        (λ sr → φ m (proj₁ sr))
        (ListAll.map (λ {e} → sink (proj₂ e)) (pres s q inv)))
      (φ-step m s q inv)
    where
    sink : (x : Maybe _)
         → Mb (λ sr → Inv (proj₁ sr)) x
         → Mb (λ sr → badProb⊥ resp bad (proj₁ sr) (kd (proj₂ sr)) ≤ℚ φ m (proj₁ sr)) x
    sink (just sr) inv′ = badProb⊥-super m (kd (proj₂ sr)) (proj₁ sr) (le (proj₂ sr)) inv′
    sink nothing   _    = tt
  badProb⊥-super m (coin μ kd) s le inv with bad s in eqb
  ... | true  = φ-bad m s inv eqb
  ... | false = ≤-trans
      (E-mono μ (λ b → badProb⊥ resp bad s (kd b)) (λ _ → φ m s)
        (λ b → badProb⊥-super m (kd b) s (le b) inv))
      (≤-reflexive (E-const μ (φ m s)))

  badProb⊥-bounded : ∀ m d → asks≤ m d → badProb⊥ resp bad s₀ d ≤ℚ ε m
  badProb⊥-bounded m d le = ≤-trans (badProb⊥-super m d s₀ le inv₀) (φ-init m)

------------------------------------------------------------------------
-- The coupled Fundamental Lemma of Game-Playing, partially

-- A joint draw with marginals `μ` and `μ′` whose every outcome is flagged or
-- related at a common answer.
module _ {R S S′ : Type} (bad : S → Bool) (_≋_ : S → S′ → Type) where

  JoinAt⊥ : Dist⊥ (S × R) → Dist⊥ (S′ × R) → Type
  JoinAt⊥ μ μ′ = Σ[ ν ∈ Dist⊥ ((S × R) × (S′ × R)) ]
                   ( (∀ F  → E⊥ ν (λ p → F  (proj₁ p)) ≡ E⊥ μ  F )
                   × (∀ F′ → E⊥ ν (λ p → F′ (proj₂ p)) ≡ E⊥ μ′ F′)
                   × OnSupport⊥ (λ p → (bad (proj₁ (proj₁ p)) ≡ true)
                                     ⊎ ((proj₁ (proj₁ p) ≋ proj₁ (proj₂ p))
                                        × (proj₂ (proj₁ p) ≡ proj₂ (proj₂ p)))) ν )

-- The identical-until-bad step for two kernels on their OWN state spaces:
-- where the games' states part once the flag is up, one coupled state would
-- have to carry both.
module _ {Q R S S′ : Type} (resp : S → Q → Dist⊥ (S × R))
         (resp′ : S′ → Q → Dist⊥ (S′ × R)) (bad : S → Bool)
         (_≋_ : S → S′ → Type) where

  JoinStep⊥ : Type
  JoinStep⊥ = ∀ s s′ → s ≋ s′ → bad s ≡ false → ∀ q → JoinAt⊥ bad _≋_ (resp s q) (resp′ s′ q)

  runWith-join⊥ : JoinStep⊥ → ∀ d s s′ → s ≋ s′
                → ∣ Pr₁⊥ (runWith⊥ resp s d) -ℚ Pr₁⊥ (runWith⊥ resp′ s′ d) ∣ℚ
                  ≤ℚ badProb⊥ resp bad s d
  runWith-join⊥ jn (out b) s s′ rel =
    subst (_≤ℚ bool→ℚ (bad s)) (sym (∣x-x∣≡0 (Pr₁⊥ (return⊥ b)))) (0≤bool (bad s))
  runWith-join⊥ jn (ask q k) s s′ rel with bad s in g
  ... | true  = ∣Pr⊥-Pr⊥∣≤1 (runWith⊥ resp s (ask q k)) (runWith⊥ resp′ s′ (ask q k))
  ... | false =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) eqL eqR))
     (≤-trans (E⊥-abs-diff ν AL AR)
     (≤-trans (E⊥-mono-on ν (λ p → ∣ AL p -ℚ AR p ∣ℚ) BB (OnSupport-mono ν sink sup))
              (≤-reflexive (mL (λ t → badProb⊥ resp bad (proj₁ t) (k (proj₂ t)))))))
    where
      jnq = jn s s′ rel g q
      ν   = proj₁ jnq
      mL  = proj₁ (proj₂ jnq)
      mR  = proj₁ (proj₂ (proj₂ jnq))
      sup = proj₂ (proj₂ (proj₂ jnq))

      KL = λ (t  : S  × R) → runWith⊥ resp  (proj₁ t ) (k (proj₂ t ))
      KR = λ (t′ : S′ × R) → runWith⊥ resp′ (proj₁ t′) (k (proj₂ t′))

      AL AR BB : (S × R) × (S′ × R) → ℚ
      AL p = Pr₁⊥ (KL (proj₁ p))
      AR p = Pr₁⊥ (KR (proj₂ p))
      BB p = badProb⊥ resp bad (proj₁ (proj₁ p)) (k (proj₂ (proj₁ p)))

      eqL : Pr₁⊥ (runWith⊥ resp s (ask q k)) ≡ E⊥ ν AL
      eqL = trans (E⊥-bind (resp s q) KL bool→ℚ) (sym (mL (λ t → Pr₁⊥ (KL t))))

      eqR : Pr₁⊥ (runWith⊥ resp′ s′ (ask q k)) ≡ E⊥ ν AR
      eqR = trans (E⊥-bind (resp′ s′ q) KR bool→ℚ) (sym (mR (λ t′ → Pr₁⊥ (KR t′))))

      sink : (x : Maybe ((S × R) × (S′ × R)))
           → Mb (λ p → (bad (proj₁ (proj₁ p)) ≡ true)
                     ⊎ ((proj₁ (proj₁ p) ≋ proj₁ (proj₂ p))
                        × (proj₂ (proj₁ p) ≡ proj₂ (proj₂ p)))) x
           → Mb (λ p → ∣ AL p -ℚ AR p ∣ℚ ≤ℚ BB p) x
      sink nothing  _ = tt
      sink (just p) (inj₁ bd) =
        subst (∣ AL p -ℚ AR p ∣ℚ ≤ℚ_)
              (sym (badProb⊥-bad resp bad (proj₁ (proj₁ p)) (k (proj₂ (proj₁ p))) bd))
              (∣Pr⊥-Pr⊥∣≤1 (KL (proj₁ p)) (KR (proj₂ p)))
      sink (just p) (inj₂ (rel′ , ans)) =
        subst (λ z → ∣ AL p -ℚ Pr₁⊥ (runWith⊥ resp′ (proj₁ (proj₂ p)) (k z)) ∣ℚ ≤ℚ BB p)
              ans (runWith-join⊥ jn (k (proj₂ (proj₁ p))) (proj₁ (proj₁ p)) (proj₁ (proj₂ p)) rel′)
  runWith-join⊥ jn (coin μ k) s s′ rel with bad s
  ... | true  = ∣Pr⊥-Pr⊥∣≤1 (runWith⊥ resp s (coin μ k)) (runWith⊥ resp′ s′ (coin μ k))
  ... | false =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
                             (E-bind μ (λ b → runWith⊥ resp  s  (k b)) mb)
                             (E-bind μ (λ b → runWith⊥ resp′ s′ (k b)) mb)))
     (≤-trans (E-abs-diff μ AL AR)
              (E-mono μ (λ b → ∣ AL b -ℚ AR b ∣ℚ) BB (λ b → runWith-join⊥ jn (k b) s s′ rel)))
    where
      AL AR BB : Bool → ℚ
      AL b = Pr₁⊥ (runWith⊥ resp  s  (k b))
      AR b = Pr₁⊥ (runWith⊥ resp′ s′ (k b))
      BB b = badProb⊥ resp bad s (k b)

module Coupling⊥ (bad : St → Bool)
                 (respB : St → Q → Dist⊥ (St × (R × R))) where

  fR fI : St × (R × R) → St × R
  fR t = proj₁ t , proj₁ (proj₂ t)
  fI t = proj₁ t , cond (bad (proj₁ t)) (proj₂ (proj₂ t)) (proj₁ (proj₂ t))

  realK idealK : St → Q → Dist⊥ (St × R)
  realK  s q = Dmap⊥ fR (respB s q)
  idealK s q = Dmap⊥ fI (respB s q)

  private
    coupled : JoinStep⊥ realK idealK bad _≡_
    coupled s .s refl _ q =
        Dmap⊥ (λ t → fR t , fI t) (respB s q)
      , (λ F → trans (E⊥-map _ (respB s q) _) (sym (E⊥-map fR (respB s q) F)))
      , (λ F → trans (E⊥-map _ (respB s q) _) (sym (E⊥-map fI (respB s q) F)))
      , OnSupport-bind (respB s q) (kmaybe (λ t → return⊥ (fR t , fI t))) (OnSupport-⊤ (respB s q)) λ where
          (just t) _ → OnSupport-return (pt t)
          nothing  _ → OnSupport-return tt
      where
      pt : ∀ t → (bad (proj₁ t) ≡ true)
               ⊎ ((proj₁ t ≡ proj₁ t)
                  × (proj₁ (proj₂ t) ≡ cond (bad (proj₁ t)) (proj₂ (proj₂ t)) (proj₁ (proj₂ t))))
      pt t with bad (proj₁ t)
      ... | true  = inj₁ refl
      ... | false = inj₂ (refl , refl)

  FLGP⊥ : ∀ s₀ d → ∣ Pr₁⊥ (runWith⊥ idealK s₀ d) -ℚ Pr₁⊥ (runWith⊥ realK s₀ d) ∣ℚ
                 ≤ℚ badProb⊥ realK bad s₀ d
  FLGP⊥ s d = subst (_≤ℚ badProb⊥ realK bad s d)
                    (∣-∣-comm (Pr₁⊥ (runWith⊥ realK s d)) (Pr₁⊥ (runWith⊥ idealK s d)))
                    (runWith-join⊥ realK idealK bad _≡_ coupled d s s refl)

------------------------------------------------------------------------
-- Coupled partial kernels run alike

-- Coupled kernels with the ALPHABET moved: the two kernels answer the same
-- questions under a relabelling `u` of the asks, and their answers correspond
-- under a section `v` of the answers — which is what a machine's ports and a
-- game's letters are related by when the game has letters (`idleR`) no machine
-- activation produces.
module _ {Q Q′ R R′ St St′ : Type} (u : Q → Q′) (v : R′ → R)
         (resp : St → Q → Dist⊥ (St × R)) (resp′ : St′ → Q′ → Dist⊥ (St′ × R′))
         (_≋_ : St → St′ → Type) where

  StepBisim⊥ʳ : Type
  StepBisim⊥ʳ = ∀ s s′ → s ≋ s′ → ∀ q (F : St × R → ℚ) (F′ : St′ × R′ → ℚ)
              → (∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ v (proj₂ t′) → F t ≡ F′ t′)
              → E⊥ (resp s q) F ≡ E⊥ (resp′ s′ (u q)) F′

  runWith⊥-bisimʳ : StepBisim⊥ʳ → ∀ d s s′ → s ≋ s′ → (G : Bool → ℚ)
                  → E⊥ (runWith⊥ resp s d) G ≡ E⊥ (runWith⊥ resp′ s′ (mapStrat u v d)) G
  runWith⊥-bisimʳ bis (out b) s s′ rel G = refl
  runWith⊥-bisimʳ bis (ask q k) s s′ rel G =
    trans (E⊥-bind (resp s q) K G)
   (trans (bis s s′ rel q (λ t → E⊥ (K t) G) (λ t′ → E⊥ (K′ t′) G) point)
          (sym (E⊥-bind (resp′ s′ (u q)) K′ G)))
    where
      K  = λ (t : St × R) → runWith⊥ resp (proj₁ t) (k (proj₂ t))
      K′ = λ (t′ : St′ × R′) → runWith⊥ resp′ (proj₁ t′) (mapStrat u v (k (v (proj₂ t′))))
      point : ∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ v (proj₂ t′)
            → E⊥ (K t) G ≡ E⊥ (K′ t′) G
      point t t′ r eq =
        subst (λ z → E⊥ (K t) G
                   ≡ E⊥ (runWith⊥ resp′ (proj₁ t′) (mapStrat u v (k z))) G) eq
          (runWith⊥-bisimʳ bis (k (proj₂ t)) (proj₁ t) (proj₁ t′) r G)
  runWith⊥-bisimʳ bis (coin μ k) s s′ rel G =
    trans (E-bind μ (λ b → runWith⊥ resp s (k b)) (maybeℚ G))
   (trans (lookupᴰℚ-cong-P (entries μ) (λ b → runWith⊥-bisimʳ bis (k b) s s′ rel G))
          (sym (E-bind μ (λ b → runWith⊥ resp′ s′ (mapStrat u v (k b))) (maybeℚ G))))

module _ {Q R St St′ : Type} (resp : St → Q → Dist⊥ (St × R))
         (resp′ : St′ → Q → Dist⊥ (St′ × R)) (_≋_ : St → St′ → Type) where

  StepBisim⊥ : Type
  StepBisim⊥ = StepBisim⊥ʳ id id resp resp′ _≋_

  -- `runWith⊥-bisimʳ` at the identities, twice: `mapStrat id id` rebuilds the
  -- tree, and the run against `resp′` itself removes it without funext.
  runWith⊥-bisim : StepBisim⊥ → ∀ d s s′ → s ≋ s′ → (G : Bool → ℚ)
                 → E⊥ (runWith⊥ resp s d) G ≡ E⊥ (runWith⊥ resp′ s′ d) G
  runWith⊥-bisim bis d s s′ rel G =
    trans (runWith⊥-bisimʳ id id resp resp′ _≋_ bis d s s′ rel G)
          (sym (runWith⊥-bisimʳ id id resp′ resp′ _≡_
                  (λ { s .s refl q F F′ h → E⊥-cong-P (resp′ s q) F F′ λ t → h t t refl refl })
                  d s′ s′ refl G))

------------------------------------------------------------------------
-- Where the two layers meet: embedding and pruning a total kernel
--
-- A machine serves an activation or diverges on it.  `prune dead K` is the
-- kernel `K` cut down to the served ones, and `dead ≡ λ _ _ → false` is the
-- embedding of `K` itself.

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

prune-Dmap : {A : Type} (dead : St → Q → Bool) (K : St → Q → Dist-ℚ (St × A))
             (p : St × A → St × R) (s : St) (q : Q) (G : St × R → ℚ)
           → E⊥ (Dmap⊥ p (prune dead K s q)) G ≡ E⊥ (prune dead (λ s q → Dmap p (K s q)) s q) G
prune-Dmap dead K p s q G with dead s q
... | true  = trans (E⊥-map p (return-ℚ nothing) G)
                    (E-return-cong nothing nothing (maybeℚ (G ∘ p)) (maybeℚ G) refl)
... | false = trans (E⊥-map p (Dmap just (K s q)) G)
              (trans (Eⱼ (K s q) (G ∘ p))
                     (sym (trans (Eⱼ (Dmap p (K s q)) G) (lookupᴰℚ-Dmap p (K s q) G))))

------------------------------------------------------------------------
-- The hop

module _ {Q R St : Type} (bad : St → Bool)
         (respB : St → Q → Dist⊥ (St × (R × R))) where

  open Coupling⊥ bad respB

  -- The hop with the supermartingale already spent, for a consumer whose
  -- certificate is about a kernel only `E⊥`-equal to `realK`.
  hop-boundᵇ⊥ : {StR StI : Type} {ε : ℕ → ℚ} (respR : StR → Q → Dist⊥ (StR × R))
                (respI : StI → Q → Dist⊥ (StI × R)) (s₀ : St) (sR : StR) (sI : StI)
              → (∀ d → Pr₁⊥ (runWith⊥ realK s₀ d) ≡ Pr₁⊥ (runWith⊥ respR sR d))
              → (∀ d → Pr₁⊥ (runWith⊥ idealK s₀ d) ≡ Pr₁⊥ (runWith⊥ respI sI d))
              → (∀ m d → asks≤ m d → badProb⊥ realK bad s₀ d ≤ℚ ε m)
              → ∀ m d → asks≤ m d
              → ∣ Pr₁⊥ (runWith⊥ respI sI d) -ℚ Pr₁⊥ (runWith⊥ respR sR d) ∣ℚ ≤ℚ ε m
  hop-boundᵇ⊥ {ε = ε} respR respI s₀ sR sI eR eI bnd m d le =
    subst (_≤ℚ ε m) (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) (eI d) (eR d))
      (≤-trans (FLGP⊥ s₀ d) (bnd m d le))
