{-# OPTIONS --safe --without-K --guardedness #-}

-- Composition of quantitative emulation witnesses, with the error kept.
--
-- Sequential composition follows `Abstract2.≤UC-trans`'s simulator
-- construction with each `≈ᵁ` step replaced by `UC.Asymptotic.Contextual`'s
-- kit; graded composition follows `Abstract2.UC-compose`'s, reusing
-- `sub-decomp`, `∙-decomp`, `sub-commute₁`/`sub-commute₂` as the algebraic
-- rearrangements.  `Abstract2.UC-compose` itself is untouched and stays
-- unconditional.
--
-- What the quantitative versions add are CERTIFICATES for the morphisms the
-- proof moves into a context, and their allowance substitutions.  Two kinds
-- occur and they behave differently: absorbing into the TEST multiplies its
-- budget, so the substitution `simCost _ c` is exact; absorbing into the
-- CLOSURE hits the leg `ctxBudget` guards, so the substitution is only a bound
-- (`UC.Budget.ctxBudget-closure≤`) and reading `ε` at it needs the schedule's
-- monotonicity as a premise.  The raw relation's domain is untouched: the
-- certificates are hypotheses of these theorems, not of `_≈ctx[_]_`.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗; μ-α⇐)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-*; poly-⊔; poly-const)
open import Data.Nat.Properties using (*-identityʳ; *-identityˡ)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; trans)

open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_; ≈ₚ[]-mono; ≈ₚ[]-resp)

open import CategoricalCrypto.UC.Approximate
  using (GradedBound-+[_]; Negligible; Negligible-+; NegligibleBound)
open import CategoricalCrypto.UC.Asymptotic.Contextual
open import CategoricalCrypto.UC.Budget
  using (Budget; ctxBudget; ctxBudget-closure≤; ctxBudget-simCost; simCost)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; obs-resp; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)
open import CategoricalCrypto.UC.Model.Setup

module CategoricalCrypto.UC.Asymptotic.Compose where

open Budget budgetᵒ using (QB; qb-∘; qb-a⇒; qb-a⇐; qb-resp-≈; qb-sub; qb-T₁)
open HomReasoning

private variable A B C X Y Z P Q : ℕ → Channel

------------------------------------------------------------------------
-- Sequential composition

-- `Abstract2.≤UC-trans`'s construction, quantitatively.  The second comparison
-- is pulled back along the first simulator, so what is added to `ε₁` is `ε₂`
-- read at `simCost _ (cost s₁)` and not `ε₂` itself; the composed simulator's
-- certificate is `qb-∘` and its polynomial `poly-*`, both inside `_∘ᶜ_`.
≤UC^ωᵉ-trans : {f : Homᶠ A X B} {g : Homᶠ A Y B} {h : Homᶠ A Z B}
             → f ≤UC^ωᵉ g → g ≤UC^ωᵉ h → f ≤UC^ωᵉ h
≤UC^ωᵉ-trans {B = B} {h = h} (s₁ , ε₁ , n₁ , e₁) (s₂ , ε₂ , n₂ , e₂) =
    s₁ ∘ᶜ s₂
  , (λ n q → ε₁ n q ℚ.+ ε₂′ n q)
  , GradedBound-+[ Negligible ] Negligible-+ ε₁ ε₂′ n₁
      (NegligibleBound-simCost (cost s₁) (cost-poly s₁) ε₂ n₂)
  , ≈ctx-trans ε₁ ε₂′ e₁ (≈ctx-resp ε₂′ (λ _ → Equiv.refl) merge (≈ctx-sub s₁ ε₂ e₂))
  where
  ε₂′ : ℕ → ℕ → ℚ
  ε₂′ n q = ε₂ n (simCost q (cost s₁ n))

  merge : (n : ℕ) → sub (sim s₁ n) {B n} ∘ sub (sim s₂ n) {B n} ∘ h n
                  ≈ sub (sim s₁ n ∘ sim s₂ n) {B n} ∘ h n
  merge _ = sym-assoc ○ ∘-resp-≈ˡ (⟺ sub-homomorphism)

-- A SPLIT regrading acts on a witness, which `Abstract2.Factor.≤UC-sub` is for
-- the qualitative order and for the same reason: post-composing `sub c` is no
-- congruence unless the simulator commutes with `c`, and a retraction `r`
-- conjugates it.  What the quantitative version adds is the allowance, and the
-- substitution is `≈ctx-sub`'s — EXACT, `c` being absorbed into the test.
≤UC^ωᵉ-sub : (c : Certified X Z) (r : Certified Z X)
           → ((n : ℕ) → sim r n ℐ.∘ sim c n ℐ.≈ ℐ.id)
           → {f g : Homᶠ A X B} → f ≤UC^ωᵉ g → subᶠ c f ≤UC^ωᵉ subᶠ c g
≤UC^ωᵉ-sub {B = B} c r inv {g = g} (s , ε , neg , e) =
    c ∘ᶜ s ∘ᶜ r
  , (λ n q → ε n (simCost q (cost c n)))
  , NegligibleBound-simCost (cost c) (cost-poly c) ε neg
  , ≈ctx-resp (λ n q → ε n (simCost q (cost c n))) (λ _ → Equiv.refl) strict
              (≈ctx-sub c ε e)
  where
  -- The conjugation, which is where the retraction is spent.
  grade : (n : ℕ) → (sim c n ℐ.∘ sim s n ℐ.∘ sim r n) ℐ.∘ sim c n ℐ.≈ sim c n ℐ.∘ sim s n
  grade n = ℐ.Equiv.trans ℐ.assoc
              (ℐ.∘-resp-≈ʳ (ℐ.Equiv.trans ℐ.assoc
                (ℐ.Equiv.trans (ℐ.∘-resp-≈ʳ (inv n)) ℐ.identityʳ)))

  strict : (n : ℕ) → sub (sim c n) {B n} ∘ sub (sim s n) {B n} ∘ g n
                   ≈ sub (sim (c ∘ᶜ s ∘ᶜ r) n) {B n} ∘ sub (sim c n) {B n} ∘ g n
  strict n = begin
      sub (sim c n) ∘ sub (sim s n) ∘ g n                        ≈⟨ sym-assoc ⟩
      (sub (sim c n) ∘ sub (sim s n)) ∘ g n                      ≈⟨ (⟺ sub-homomorphism) ⟩∘⟨refl ⟩
      sub (sim c n ℐ.∘ sim s n) ∘ g n                            ≈⟨ sub-resp-≈ (ℐ.Equiv.sym (grade n)) ⟩∘⟨refl ⟩
      sub (sim (c ∘ᶜ s ∘ᶜ r) n ℐ.∘ sim c n) ∘ g n                ≈⟨ sub-homomorphism ⟩∘⟨refl ⟩
      (sub (sim (c ∘ᶜ s ∘ᶜ r) n) ∘ sub (sim c n)) ∘ g n          ≈⟨ assoc ⟩
      sub (sim (c ∘ᶜ s ∘ᶜ r) n) ∘ sub (sim c n) ∘ g n            ∎

------------------------------------------------------------------------
-- Plugging processes around a relation

infixr 8 _⊗ᶠ_
infixr 9 _∙ᶠ_

_⊗ᶠ_ : (ℕ → Channel) → (ℕ → Channel) → ℕ → Channel
(X ⊗ᶠ P) n = X n ⊗₀ P n

-- `Abstract2._∙_`, levelwise.
_∙ᶠ_ : Homᶠ B P C → Homᶠ A X B → Homᶠ A (X ⊗ᶠ P) C
_∙ᶠ_ {X = X} k f n = ext (X n) (k n) ∘ f n

-- Moving a CONTINUATION into the test.  `∙-decomp` factors the context of
-- `k ∙ᶠ f` as `sub α⇒ ∘ ext (W ⊗ X) k` in front of `f`'s own, and `k`'s
-- certificate is what pays for it: the test's budget is multiplied by
-- `ck ⊔ 1`, hence the allowance by exactly `simCost _ ck`.
≈ctx-ext : (k : Homᶠ B P C) (ck : ℕ → ℕ) → ((n : ℕ) → QB (ck n) (k n))
         → (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g
         → (k ∙ᶠ f) ≈ctx[ (λ n q → ε n (simCost q (ck n))) ] (k ∙ᶠ g)
≈ctx-ext {B = B} {P = P} {C = C} {A = A} {X = X} k ck qk ε {f} {g} hy n W E m {c} {c′} qE qm =
  ≈ₚ[]-resp (obs-resp (⟺ (cut (f n)))) (obs-resp (⟺ (cut (g n)))) inner
  where
  U : Channel
  U = W ⊗₀ X n

  E′ : T₀ U (B n) ⇒ Ωᵒ
  E′ = E ∘ (sub (α⇒ {W} {X n} {P n}) {C n} ∘ ext U (k n))

  cut : (x : A n ⇒ T₀ (X n) (B n))
      → (E ∘ prefixᵒ W (ext (X n) (k n) ∘ x)) ∘ m ≈ (E′ ∘ prefixᵒ W x) ∘ m
  cut x = ∘-resp-≈ˡ (∘-resp-≈ʳ (∙-decomp (k n) x W) ○ sym-assoc)

  qE′ : QB (c ℕ.* (ck n ℕ.⊔ 1)) E′
  qE′ = subst (λ j → QB (c ℕ.* j) E′) norm
          (qb-∘ qE (qb-∘ (qb-sub {A = C n} (qb-a⇐ {W} {X n} {P n}))
                         (qb-∘ (qb-a⇒ {U} {P n} {C n}) (qb-T₁ {U} (qk n)))))
    where
    norm : 1 ℕ.* (1 ℕ.* (ck n ℕ.⊔ 1)) ≡ ck n ℕ.⊔ 1
    norm = trans (*-identityˡ _) (*-identityˡ _)

  inner : Obs ((E′ ∘ prefixᵒ W (f n)) ∘ m)
            ≈ₚ[ ε n (simCost (ctxBudget c c′) (ck n)) ]
          Obs ((E′ ∘ prefixᵒ W (g n)) ∘ m)
  inner = subst (λ j → Obs ((E′ ∘ prefixᵒ W (f n)) ∘ m) ≈ₚ[ ε n j ]
                       Obs ((E′ ∘ prefixᵒ W (g n)) ∘ m))
                (ctxBudget-simCost c c′ (ck n)) (hy n W E′ m qE′ qm)

-- Moving the earlier PROCESS into the closure.  `∙-decomp` read the other way:
-- the context of `u ∙ᶠ f` at ancilla `W` IS `u`'s context at ancilla `W ⊗ X`,
-- with `f`'s own prefix pushed into the closure.  So `f`'s certificate pays,
-- and it pays on the leg `ctxBudget` GUARDS rather than multiplies: the
-- substitution is a bound, and reading `ε` at it is the explicit
-- `Allowance-mono` premise.
≈ctx-pre : (f : Homᶠ A X B) (cf : ℕ → ℕ) → ((n : ℕ) → QB (cf n) (f n))
         → (ε : ℕ → ℕ → ℚ) → Allowance-mono ε
         → {u v : Homᶠ B P C} → u ≈ctx[ ε ] v
         → (u ∙ᶠ f) ≈ctx[ (λ n q → ε n (simCost q (cf n))) ] (v ∙ᶠ f)
≈ctx-pre {A = A} {X = X} {B = B} {P = P} {C = C} f cf qf ε mono {u} {v} hy n W E m {c} {c′} qE qm =
  ≈ₚ[]-resp (obs-resp (⟺ (cut (u n)))) (obs-resp (⟺ (cut (v n))))
            (≈ₚ[]-mono (mono n (ctxBudget-closure≤ c c′ (cf n))) inner)
  where
  U : Channel
  U = W ⊗₀ X n

  E′ : T₀ (U ⊗₀ P n) (C n) ⇒ Ωᵒ
  E′ = E ∘ sub (α⇒ {W} {X n} {P n}) {C n}

  m′ : 𝟘ᵒ ⇒ T₀ U (B n)
  m′ = prefixᵒ W (f n) ∘ m

  cut : (x : B n ⇒ T₀ (P n) (C n))
      → (E ∘ prefixᵒ W (ext (X n) x ∘ f n)) ∘ m ≈ (E′ ∘ prefixᵒ U x) ∘ m′
  cut x = begin
      (E ∘ prefixᵒ W (ext (X n) x ∘ f n)) ∘ m
        ≈⟨ (refl⟩∘⟨ ∙-decomp x (f n) W) ⟩∘⟨refl ⟩
      (E ∘ (sub α⇒ ∘ ext U x) ∘ prefixᵒ W (f n)) ∘ m
        ≈⟨ (refl⟩∘⟨ ((refl⟩∘⟨ ⟺ (μT x)) ⟩∘⟨refl)) ⟩∘⟨refl ⟩
      (E ∘ (sub α⇒ ∘ prefixᵒ U x) ∘ prefixᵒ W (f n)) ∘ m
        ≈⟨ (refl⟩∘⟨ assoc) ⟩∘⟨refl ⟩
      (E ∘ sub α⇒ ∘ prefixᵒ U x ∘ prefixᵒ W (f n)) ∘ m
        ≈⟨ sym-assoc ⟩∘⟨refl ⟩
      ((E ∘ sub α⇒) ∘ prefixᵒ U x ∘ prefixᵒ W (f n)) ∘ m
        ≈⟨ assoc ⟩
      (E ∘ sub α⇒) ∘ (prefixᵒ U x ∘ prefixᵒ W (f n)) ∘ m
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (E ∘ sub α⇒) ∘ prefixᵒ U x ∘ prefixᵒ W (f n) ∘ m
        ≈⟨ sym-assoc ⟩
      ((E ∘ sub α⇒) ∘ prefixᵒ U x) ∘ m′  ∎

  qE′ : QB c E′
  qE′ = subst (λ j → QB j E′) (*-identityʳ c)
              (qb-∘ qE (qb-sub {A = C n} (qb-a⇐ {W} {X n} {P n})))

  qm′ : QB ((cf n ℕ.⊔ 1) ℕ.* c′) m′
  qm′ = subst (λ j → QB (j ℕ.* c′) m′) (*-identityˡ (cf n ℕ.⊔ 1))
              (qb-∘ (qb-∘ qμ qT) qm)
    where
    qμ : QB 1 (μ W (X n) {B n})
    qμ = qb-resp-≈ (Equiv.sym (μ-α⇐ 𝔾ᵒ W (X n))) (qb-a⇒ {W} {X n} {B n})

    qT : QB (cf n ℕ.⊔ 1) (T₁ W (f n))
    qT = qb-resp-≈ (Equiv.sym (T₁-⊗ 𝔾ᵒ W (f n))) (qb-T₁ {W} (qf n))

  inner : Obs ((E′ ∘ prefixᵒ U (u n)) ∘ m′)
            ≈ₚ[ ε n (ctxBudget c ((cf n ℕ.⊔ 1) ℕ.* c′)) ]
          Obs ((E′ ∘ prefixᵒ U (v n)) ∘ m′)
  inner = hy n U E′ m′ qE′ qm′

-- Plugging a process under the DOMAIN, where `≈ctx-pre` plugs one under the
-- SUBROUTINE.  The closure absorbs it and at rate `0` that is free: the
-- closure's budget becomes `(0 ⊔ 1) * c′`, which `ctxBudget` reads as `c′`
-- itself, so the schedule is unchanged and no `Allowance-mono` is spent.  This
-- is what puts a comparison at a CLOSED domain, with the resource the two
-- sides must agree about moved out of the context's control
-- (`docs/coin-toss.md` §5).
≈ctx-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → QB 0 (p n))
         → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ A X B} → u ≈ctx[ ε ] v
         → (λ n → u n ∘ p n) ≈ctx[ ε ] (λ n → v n ∘ p n)
≈ctx-dom {A = A} {X = X} {B = B} p qp ε {u} {v} hy n W E m {c} {c′} qE qm =
  ≈ₚ[]-resp (obs-resp (⟺ (cut (u n)))) (obs-resp (⟺ (cut (v n)))) inner
  where
  m′ : 𝟘ᵒ ⇒ T₀ W (A n)
  m′ = T₁ W (p n) ∘ m

  cut : (x : A n ⇒ T₀ (X n) (B n))
      → (E ∘ prefixᵒ W (x ∘ p n)) ∘ m ≈ (E ∘ prefixᵒ W x) ∘ m′
  cut x = begin
      (E ∘ prefixᵒ W (x ∘ p n)) ∘ m
        ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ T-homomorphism)) ⟩∘⟨refl ⟩
      (E ∘ (μ W (X n) ∘ (T₁ W x ∘ T₁ W (p n)))) ∘ m
        ≈⟨ (refl⟩∘⟨ sym-assoc) ⟩∘⟨refl ⟩
      (E ∘ ((μ W (X n) ∘ T₁ W x) ∘ T₁ W (p n))) ∘ m
        ≈⟨ sym-assoc ⟩∘⟨refl ⟩
      ((E ∘ prefixᵒ W x) ∘ T₁ W (p n)) ∘ m
        ≈⟨ assoc ⟩
      (E ∘ prefixᵒ W x) ∘ m′  ∎

  qm′ : QB (1 ℕ.* c′) m′
  qm′ = qb-∘ (qb-resp-≈ (Equiv.sym (T₁-⊗ 𝔾ᵒ W (p n))) (qb-T₁ {W} (qp n))) qm

  inner : Obs ((E ∘ prefixᵒ W (u n)) ∘ m′) ≈ₚ[ ε n (ctxBudget c c′) ]
          Obs ((E ∘ prefixᵒ W (v n)) ∘ m′)
  inner = subst (λ j → Obs ((E ∘ prefixᵒ W (u n)) ∘ m′) ≈ₚ[ ε n (ctxBudget c j) ]
                       Obs ((E ∘ prefixᵒ W (v n)) ∘ m′))
                (*-identityˡ c′) (hy n W E m′ qE qm′)

-- …hence on a whole witness, with the simulator and the schedule untouched.
≤UC^ωᵉ-dom : {A′ : ℕ → Channel} (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → QB 0 (p n))
           → {f : Homᶠ A X B} {g : Homᶠ A Y B} → f ≤UC^ωᵉ g
           → (λ n → f n ∘ p n) ≤UC^ωᵉ (λ n → g n ∘ p n)
≤UC^ωᵉ-dom p qp (s , ε , neg , e) =
  s , ε , neg , ≈ctx-resp ε (λ _ → Equiv.refl) (λ _ → assoc) (≈ctx-dom p qp ε e)

------------------------------------------------------------------------
-- Graded composition

-- The ε-analogue of `Abstract2.UC-compose`, following its construction step by
-- step.  Its two extra hypotheses are exactly the certificates for the
-- morphisms it moves: `f`, which goes into the closure (hence
-- `Allowance-mono εh`), and `k`, which with the simulator `t` in front of it
-- goes into the test.  The composed simulator is `UC-compose`'s own, at the
-- identity adversary.
UC-composeᵉ :
    {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
    (sf : Certified Y X) (εf : ℕ → ℕ → ℚ) → NegligibleBound εf
  → f ≈ctx[ εf ] subᶠ sf g
  → (t : Certified Q P) (εu : ℕ → ℕ → ℚ) → NegligibleBound εu → Allowance-mono εu
  → u ≈ctx[ εu ] subᶠ t v
  → (cf : ℕ → ℕ) → Poly cf → ((n : ℕ) → QB (cf n) (f n))
  → (cv : ℕ → ℕ) → Poly cv → ((n : ℕ) → QB (cv n) (v n))
  → (u ∙ᶠ f) ≤UC^ωᵉ (v ∙ᶠ g)
UC-composeᵉ {A = A} {X = X} {B = B} {Y = Y} {P = P} {C = C} {Q = Q}
            {f = f} {g} {u} {v} sf εf nf ef t εu nu mono eu cf Pcf qf cv Pcv qv =
    s , (λ n q → εu′ n q ℚ.+ εf′ n q)
  , GradedBound-+[ Negligible ] Negligible-+ εu′ εf′
      (NegligibleBound-simCost cf Pcf εu nu)
      (NegligibleBound-simCost ctv Pctv εf nf)
  , ≈ctx-trans εu′ εf′ (≈ctx-pre f cf qf εu mono eu)
      (≈ctx-resp εf′ (λ _ → Equiv.refl) strict-final
                 (≈ctx-ext (subᶠ t v) ctv qtv εf ef))
  where
  ctv : ℕ → ℕ
  ctv n = (cost t n ℕ.⊔ 1) ℕ.* cv n

  εu′ εf′ : ℕ → ℕ → ℚ
  εu′ n q = εu n (simCost q (cf n))
  εf′ n q = εf n (simCost q (ctv n))

  Pctv : Poly ctv
  Pctv = poly-* (poly-⊔ (cost-poly t) (poly-const 1)) Pcv

  qtv : (n : ℕ) → QB (ctv n) (subᶠ t v n)
  qtv n = qb-∘ (qb-sub {A = C n} (sim-qb t n)) (qv n)

  s : Certified (Y ⊗ᶠ Q) (X ⊗ᶠ P)
  s = (λ n → ℐ.id {X n} ⊗₁ sim t n ∘ sim sf n ⊗₁ ℐ.id {Q n})
    , (λ n → (cost t n ℕ.⊔ 1) ℕ.* (cost sf n ℕ.⊔ 1))
    , poly-* (poly-⊔ (cost-poly t) (poly-const 1)) (poly-⊔ (cost-poly sf) (poly-const 1))
    , λ n → qb-∘ (qb-T₁ {X n} (sim-qb t n)) (qb-sub {A = Q n} (sim-qb sf n))

  strict-final : (n : ℕ)
               → ext (X n) (sub (sim t n) {C n} ∘ v n) ∘ sub (sim sf n) {B n} ∘ g n
                 ≈ sub (sim s n) {C n} ∘ ext (Y n) (v n) ∘ g n
  strict-final n = begin
      ext (X n) (sub (sim t n) ∘ v n) ∘ sub (sim sf n) ∘ g n
        ≈⟨ sub-commute₂ ⟩∘⟨refl ⟩
      (sub (ℐ.id ⊗₁ sim t n) ∘ ext (X n) (v n)) ∘ sub (sim sf n) ∘ g n
        ≈⟨ assoc ⟩
      sub (ℐ.id ⊗₁ sim t n) ∘ ext (X n) (v n) ∘ sub (sim sf n) ∘ g n
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      sub (ℐ.id ⊗₁ sim t n) ∘ (ext (X n) (v n) ∘ sub (sim sf n)) ∘ g n
        ≈⟨ refl⟩∘⟨ (sub-commute₁ ⟩∘⟨refl) ⟩
      sub (ℐ.id ⊗₁ sim t n) ∘ (sub (sim sf n ⊗₁ ℐ.id) ∘ ext (Y n) (v n)) ∘ g n
        ≈⟨ refl⟩∘⟨ assoc ⟩
      sub (ℐ.id ⊗₁ sim t n) ∘ sub (sim sf n ⊗₁ ℐ.id) ∘ ext (Y n) (v n) ∘ g n
        ≈⟨ sym-assoc ⟩
      (sub (ℐ.id ⊗₁ sim t n) ∘ sub (sim sf n ⊗₁ ℐ.id)) ∘ ext (Y n) (v n) ∘ g n
        ≈⟨ (⟺ sub-homomorphism) ⟩∘⟨refl ⟩
      sub (sim s n) ∘ ext (Y n) (v n) ∘ g n  ∎
