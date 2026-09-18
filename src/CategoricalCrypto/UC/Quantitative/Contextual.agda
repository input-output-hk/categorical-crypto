{-# OPTIONS --safe --without-K #-}

-- The query-sensitive contextual comparison, and the one principle behind its
-- schedule substitutions (`docs/quantitative-uc-setup-plan.typ` §7.3).
--
-- The compared morphisms are NOT certified — only the test and the closure
-- are, which is what `UC.Asymptotic.Contextual._≈ctxᴬ[_]_` also does and what
-- keeps certified simulators from forcing every compared process to be
-- certified.  The allowance is therefore an index of the RELATION, never of
-- the computation category.
--
-- `ctx-absorb` is the whole quantitative content of both existing
-- substitutions: moving a certified morphism in front of the test multiplies
-- the test's budget by that morphism's, and `UC.Budget.ctxBudget-simCost`
-- turns that into `simCost _ cs` on the allowance — EXACTLY, the test being
-- the leg `ctxBudget` multiplies rather than the one it guards.  `ctx-sub` is
-- the instance at a simulator's action; `UC.Asymptotic.Compose.≈ctx-ext` is
-- the same lemma at a continuation.

open import Categories.Category using (Category)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.UC.Approximate using (Approximation; ℚ-errors)
open import CategoricalCrypto.UC.Budget
  using (Budget; ctxBudget; ctxBudget-simCost; simCost)
open import CategoricalCrypto.UC.Core using (Grading)

import CategoricalCrypto.Approx.Space as Spaceᴹ
import Data.Nat.Properties as ℕₚ

module CategoricalCrypto.UC.Quantitative.Contextual
  {o ℓ e os ℓa qs : Level}
  (𝒞 : Category o ℓ e) (G : Grading 𝒞) (Bg : Budget 𝒞 G qs)
  {Obs : Set os} (Ap : Approximation Obs ℚ-errors ℓa)
  (𝟙 Ω : Category.Obj 𝒞)
  (⟦_⟧ : Category._⇒_ 𝒞 𝟙 Ω → Obs)
  (obs-resp : {u v : Category._⇒_ 𝒞 𝟙 Ω}
            → Category._≈_ 𝒞 u v → Approximation._≈[_]_ Ap ⟦ u ⟧ 0ℚ ⟦ v ⟧)
  where

open Category 𝒞
open Grading G
open Budget Bg

private
  module Oq = Spaceᴹ ℚ-ordered
  module A  = Approximation Ap

  obsSpace : Oq.ApproxSpace os ℓa
  obsSpace = record { Carrier = Obs ; approx = Ap }

private variable A B X Y Z : Obj

------------------------------------------------------------------------
-- The relation

infix 4 _≈ᵁᵠ[_]_

_≈ᵁᵠ[_]_ : A ⇒ X ⊛ B → (ℕ → ℚ) → A ⇒ X ⊛ B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≈ᵁᵠ[_]_ {A} {X} {B} f ε g =
  (W : Obj) (E : W ⊛ (X ⊛ B) ⇒ Ω) (m : 𝟙 ⇒ W ⊛ A) {c c′ : ℕ}
  → QB c E → QB c′ m
  → ⟦ (E ∘ T₁ W f) ∘ m ⟧ A.≈[ ε (ctxBudget c c′) ] ⟦ (E ∘ T₁ W g) ∘ m ⟧

ctx-refl : {f : A ⇒ X ⊛ B} → f ≈ᵁᵠ[ (λ _ → 0ℚ) ] f
ctx-refl _ _ _ _ _ = A.≈[]-refl

-- The schedules are explicit, as they are throughout the existing API
-- (`UC.Asymptotic.Contextual.≈ctx-resp`): a sum of two of them is not
-- recoverable from the goal by unification.
ctx-sym : (ε : ℕ → ℚ) {f g : A ⇒ X ⊛ B} → f ≈ᵁᵠ[ ε ] g → g ≈ᵁᵠ[ ε ] f
ctx-sym _ h W E m qE qm = A.≈[]-sym (h W E m qE qm)

ctx-trans : (ε δ : ℕ → ℚ) {f g h : A ⇒ X ⊛ B}
          → f ≈ᵁᵠ[ ε ] g → g ≈ᵁᵠ[ δ ] h
          → f ≈ᵁᵠ[ (λ q → ε q ℚ.+ δ q) ] h
ctx-trans _ _ h k W E m qE qm = A.≈[]-trans (h W E m qE qm) (k W E m qE qm)

ctx-mono : (ε δ : ℕ → ℚ) {f g : A ⇒ X ⊛ B}
         → ((q : ℕ) → ε q ℚ.≤ δ q) → f ≈ᵁᵠ[ ε ] g → f ≈ᵁᵠ[ δ ] g
ctx-mono _ _ le h W E m qE qm = A.≈[]-mono (le _) (h W E m qE qm)

-- The ambient hom equality is observed exactly, `T₁` and the context included.
ctx-resp : (ε : ℕ → ℚ) {f f′ g g′ : A ⇒ X ⊛ B}
         → f ≈ f′ → g ≈ g′ → f ≈ᵁᵠ[ ε ] g → f′ ≈ᵁᵠ[ ε ] g′
ctx-resp _ ef eg h W E m qE qm = Oq.resp₀ obsSpace
  (obs-resp (∘-resp-≈ˡ (∘-resp-≈ʳ (T₁-resp-≈ (Equiv.sym ef)))))
  (obs-resp (∘-resp-≈ˡ (∘-resp-≈ʳ (T₁-resp-≈ eg))))
  (h W E m qE qm)

------------------------------------------------------------------------
-- Absorbing a certified morphism into the test

-- `κ` is what moves in front of the test; everything quantitative about the
-- move is the allowance identity `ctxBudget-simCost`.
ctx-absorb : (ε : ℕ → ℚ) (cs : ℕ) {A B X B′ X′ : Obj}
             {f g : A ⇒ X ⊛ B} {f′ g′ : A ⇒ X′ ⊛ B′}
             (κ : (W : Obj) → W ⊛ (X ⊛ B) ⇒ W ⊛ (X′ ⊛ B′))
           → ((W : Obj) → QB (cs ℕ.⊔ 1) (κ W))
           → ((W : Obj) → T₁ W f′ ≈ κ W ∘ T₁ W f)
           → ((W : Obj) → T₁ W g′ ≈ κ W ∘ T₁ W g)
           → f ≈ᵁᵠ[ ε ] g → f′ ≈ᵁᵠ[ (λ q → ε (simCost q cs)) ] g′
ctx-absorb ε cs {f = f} {g = g} κ qκ stepf stepg h W E m {c} {c′} qE qm =
  Oq.resp₀ obsSpace
    (obs-resp (∘-resp-≈ˡ (Equiv.trans (∘-resp-≈ʳ (stepf W)) sym-assoc)))
    (obs-resp (Equiv.sym (∘-resp-≈ˡ (Equiv.trans (∘-resp-≈ʳ (stepg W)) sym-assoc))))
    (subst (λ k → ⟦ ((E ∘ κ W) ∘ T₁ W f) ∘ m ⟧ A.≈[ ε k ]
                  ⟦ ((E ∘ κ W) ∘ T₁ W g) ∘ m ⟧)
           (ctxBudget-simCost c c′ cs)
           (h W (E ∘ κ W) m (qb-∘ qE (qκ W)) qm))

-- …and at a simulator's action, where `qb-sub` and `qb-T₁` certify the
-- absorbed morphism at `cs ⊔ 1`, the substitution is `simCost _ cs`: the
-- schedule of `UC.Asymptotic.Compose.≤UC^ωᵉ-sub`, derived.
ctx-sub : (ε : ℕ → ℚ) {s : X ⇒ Z} (cs : ℕ) → QB cs s
        → {f g : A ⇒ X ⊛ B} → f ≈ᵁᵠ[ ε ] g
        → (sub s ∘ f) ≈ᵁᵠ[ (λ q → ε (simCost q cs)) ] (sub s ∘ g)
ctx-sub ε {s = s} cs qs h =
  ctx-absorb ε cs (λ W → T₁ W (sub s))
    (λ W → subst (λ k → QB k (T₁ W (sub s)))
             (trans (ℕₚ.⊔-assoc cs 1 1) (cong (cs ℕ.⊔_) (ℕₚ.⊔-idem 1)))
             (qb-T₁ (qb-sub qs)))
    (λ _ → T₁-∘) (λ _ → T₁-∘) h

-- Sequential composition of two witnesses, with the schedule and the composed
-- simulator of `UC.Asymptotic.Compose.≤UC^ωᵉ-trans`: the second comparison is
-- pulled back along the first simulator, so what is added to `ε₁` is `ε₂` read
-- at `simCost _ cs` — not `ε₂` — and the simulator is `s ∘ t`.
at-trans : (ε₁ ε₂ : ℕ → ℚ) {s : Y ⇒ X} {t : Z ⇒ Y} (cs : ℕ) → QB cs s
         → {f : A ⇒ X ⊛ B} {g : A ⇒ Y ⊛ B} {h : A ⇒ Z ⊛ B}
         → f ≈ᵁᵠ[ ε₁ ] (sub s ∘ g) → g ≈ᵁᵠ[ ε₂ ] (sub t ∘ h)
         → f ≈ᵁᵠ[ (λ q → ε₁ q ℚ.+ ε₂ (simCost q cs)) ] (sub (s ∘ t) ∘ h)
at-trans ε₁ ε₂ cs qs e₁ e₂ =
  ctx-trans ε₁ ε₂′ e₁
    (ctx-resp ε₂′ Equiv.refl (Equiv.trans sym-assoc (∘-resp-≈ˡ (Equiv.sym sub-∘)))
              (ctx-sub ε₂ cs qs e₂))
  where
  ε₂′ : ℕ → ℚ
  ε₂′ q = ε₂ (simCost q cs)
