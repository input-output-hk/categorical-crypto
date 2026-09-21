{-# OPTIONS --safe --without-K #-}

-- The query-sensitive contextual comparison, as the admitted agreement of the
-- filtered test presheaf (`docs/quantitative-uc-setup-plan.typ` §7.3).
--
-- The compared morphisms are NOT certified — only the test and the closure
-- are, which is what keeps certified simulators from forcing every compared
-- process to be certified.  The allowance is therefore an index of the
-- RELATION, never of the computation category, and `runᵠ` is `Query.pullᵠ`'s
-- underlying map with no filtered structure on it.
--
-- `_≈ᵁᵠ[ ε ]_` IS `Approx.Filtered._≈ᵃ[_]_` for `Query.Qᵠ` read at the
-- schedule `λ q c′ → ε (ctxBudget q c′)`: `ctx⇒agree`/`agree⇒ctx` differ by
-- the order in which the closure and the test's certificate are taken and by
-- nothing else.  Both substitution principles are then one datum of a filtered
-- map — `absorb-testᵠ` moves a certified morphism in front of the TEST, which
-- is `pullᵠ`'s allowance map, and `absorb-closureᵠ` moves one behind the
-- CLOSURE, which is `pullᵠ⁺`'s control — and `UC.Budget`'s two allowance
-- identities are what makes each of them exact.  `ctx-sub` is the instance at
-- a simulator's action; `UC.Quantitative.Family.≈ctx-ext`/`-pre`/`-dom` are
-- the instances at a continuation, an earlier process and a domain plug.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
import Categories.Category.Monoidal.Reasoning as MonR

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (proj₁)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import CategoricalCrypto.UC.Approximate using (Approximation; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget; ctxBudget; simCost)
open import CategoricalCrypto.UC.Quantitative.Query
  using (absorb-closure; absorb-test; fromBudget; module Fl; module Tests)

import Data.Nat.Properties as ℕₚ
import Data.Rational.Properties as ℚₚ

module CategoricalCrypto.UC.Quantitative.Contextual
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e) (Bg : Budget M qs)
  {Obs : Set os} (Ap : Approximation Obs ℚ-errors ℓa)
  (𝟙 Ω : MonoidalCategory.Obj M)
  (⟦_⟧ : MonoidalCategory._⇒_ M 𝟙 Ω → Obs)
  (obs-resp : {u v : MonoidalCategory._⇒_ M 𝟙 Ω}
            → MonoidalCategory._≈_ M u v → Approximation._≈[_]_ Ap ⟦ u ⟧ 0ℚ ⟦ v ⟧)
  where

open MonoidalCategory M
open Fl
open MonR monoidal
open Budget Bg

module Tᵠ = Tests U (fromBudget Bg) Ap 𝟙 Ω ⟦_⟧ obs-resp

private module A = Approximation Ap

private variable A B X Y Z : Obj

------------------------------------------------------------------------
-- The relation, and the filtered instance it is

infix 4 _≈ᵁᵠ[_]_

_≈ᵁᵠ[_]_ : A ⇒ X ⊗₀ B → (ℕ → ℚ) → A ⇒ X ⊗₀ B → Set (o ⊔ ℓ ⊔ ℓa ⊔ qs)
_≈ᵁᵠ[_]_ {A} {X} {B} f ε g =
  (W : Obj) (E : W ⊗₀ (X ⊗₀ B) ⇒ Ω) (m : 𝟙 ⇒ W ⊗₀ A) {c c′ : ℕ}
  → QB c E → QB c′ m
  → ⟦ (E ∘ id ⊗₁ f) ∘ m ⟧ A.≈[ ε (ctxBudget c c′) ] ⟦ (E ∘ id ⊗₁ g) ∘ m ⟧

-- Two pullbacks of tests agreeing on the ADMITTED ones, at the schedule this
-- layer reads: the test's own allowance in `ctxBudget`'s first leg, the
-- closure's budget in its second.  The bracket a context is written in is not
-- fixed here — `UC.Quantitative.Family._≈ctx[_]_` is the same agreement at
-- `prefixᵒ`, so the two absorptions below serve both.
Agreeᵠ : (ε : ℕ → ℚ) {C D : Obj} (r r′ : Tᵠ.Test D → Tᵠ.Test C) → Set (ℓ ⊔ ℓa ⊔ qs)
Agreeᵠ ε {C} {D} r r′ =
  _≈ᵃ[_]_ {X = Tᵠ.filteredᵠ D} {Y = Tᵠ.filteredᵠ C} r (λ q c′ → ε (ctxBudget q c′)) r′

runᵠ : (W : Obj) {A X B : Obj} → A ⇒ X ⊗₀ B
     → Tᵠ.Test (W ⊗₀ (X ⊗₀ B)) → Tᵠ.Test (W ⊗₀ A)
runᵠ W f E = E ∘ id ⊗₁ f

ctx⇒agree : (ε : ℕ → ℚ) {f g : A ⇒ X ⊗₀ B} → f ≈ᵁᵠ[ ε ] g
          → (W : Obj) → Agreeᵠ ε (runᵠ W f) (runᵠ W g)
ctx⇒agree _ h W = agree λ qE m _ qm → h W _ m qE qm

agree⇒ctx : (ε : ℕ → ℚ) {f g : A ⇒ X ⊗₀ B}
          → ((W : Obj) → Agreeᵠ ε (runᵠ W f) (runᵠ W g)) → f ≈ᵁᵠ[ ε ] g
agree⇒ctx _ h W E m qE qm = admitted (h W) qE m _ qm

-- Zero error in a test space is the ambient hom equality, observed exactly.
cast₀ : {C : Obj} {E F : C ⇒ Ω} → E ≈ F → E Tᵠ.≈ᵠ[ (λ _ → 0ℚ) ] F
cast₀ eq m _ _ = obs-resp (∘-resp-≈ˡ eq)

bud : {C D : Obj} (c : ℕ) {h : C ⇒ D} → QB c h → Tᵠ.Budgeted C D
bud c {h} q = record { hom = h ; budget = c ; certified = q }

------------------------------------------------------------------------
-- The enrichment kit, levelwise from `Approx.Filtered`

ctx-refl : {f : A ⇒ X ⊗₀ B} → f ≈ᵁᵠ[ (λ _ → 0ℚ) ] f
ctx-refl = agree⇒ctx (λ _ → 0ℚ) λ _ → ≈ᵃ-refl

-- The schedules are explicit, as they are throughout the existing API
-- (`UC.Quantitative.Family.≈ctx-resp`): a sum of two of them is not
-- recoverable from the goal by unification.
ctx-sym : (ε : ℕ → ℚ) {f g : A ⇒ X ⊗₀ B} → f ≈ᵁᵠ[ ε ] g → g ≈ᵁᵠ[ ε ] f
ctx-sym ε h = agree⇒ctx ε λ W → ≈ᵃ-sym (ctx⇒agree ε h W)

ctx-trans : (ε δ : ℕ → ℚ) {f g h : A ⇒ X ⊗₀ B}
          → f ≈ᵁᵠ[ ε ] g → g ≈ᵁᵠ[ δ ] h
          → f ≈ᵁᵠ[ (λ q → ε q ℚ.+ δ q) ] h
ctx-trans ε δ h k =
  agree⇒ctx (λ q → ε q ℚ.+ δ q) λ W → ≈ᵃ-trans (ctx⇒agree ε h W) (ctx⇒agree δ k W)

ctx-mono : (ε δ : ℕ → ℚ) {f g : A ⇒ X ⊗₀ B}
         → ((q : ℕ) → ε q ℚ.≤ δ q) → f ≈ᵁᵠ[ ε ] g → f ≈ᵁᵠ[ δ ] g
ctx-mono ε δ le h = agree⇒ctx δ λ W → ≈ᵃ-mono (λ _ _ → le _) (ctx⇒agree ε h W)

-- The ambient hom equality is observed exactly, the ancilla action and the
-- context included.
ctx-resp : (ε : ℕ → ℚ) {f f′ g g′ : A ⇒ X ⊗₀ B}
         → f ≈ f′ → g ≈ g′ → f ≈ᵁᵠ[ ε ] g → f′ ≈ᵁᵠ[ ε ] g′
ctx-resp ε ef eg h = agree⇒ctx ε λ W →
  ≈ᵃ-resp₀ (λ _ → cast₀ (∘-resp-≈ʳ (refl⟩⊗⟨ Equiv.sym ef)))
           (λ _ → cast₀ (∘-resp-≈ʳ (refl⟩⊗⟨ eg))) (ctx⇒agree ε h W)

------------------------------------------------------------------------
-- The two absorptions, each one datum of a filtered map

-- Moving a certified morphism in front of the TEST is `pullᵠ`'s ALLOWANCE
-- map, and `ctxBudget-simCost` (as `absorb-test`) is what makes the resulting
-- substitution `simCost _ cs` exact rather than a bound.
absorb-testᵠ : (ε : ℕ → ℚ) (cs : ℕ) {C D D′ : Obj}
               {r r′ : Tᵠ.Test D → Tᵠ.Test C} {s s′ : Tᵠ.Test D′ → Tᵠ.Test C}
               {k : D ⇒ D′} → QB (cs ℕ.⊔ 1) k
             → ((E : Tᵠ.Test D′) → s E ≈ r (E ∘ k))
             → ((E : Tᵠ.Test D′) → s′ E ≈ r′ (E ∘ k))
             → Agreeᵠ ε r r′ → Agreeᵠ (λ q → ε (simCost q cs)) s s′
absorb-testᵠ ε cs qk stepr stepr′ h =
  ≈ᵃ-resp₀ (λ E → cast₀ (stepr E)) (λ E → cast₀ (Equiv.sym (stepr′ E)))
    (≈ᵃ-mono (λ q → proj₁ (absorb-test q cs) ε)
             (≈ᵃ-pre (Tᵠ.pullᵠ (bud (cs ℕ.⊔ 1) qk)) h))

-- …and moving one behind the CLOSURE is `pullᵠ⁺`'s CONTROL.  `ctxBudget`
-- GUARDS its closure leg rather than multiplying by it, so only reading the
-- new closure's budget past that guard — which `pullᵠ⁺` does and a budget
-- being an upper bound affords — makes the same substitution exact
-- (`absorb-closure`).  The test may move along a structural `k` at the same
-- time, which is what an absorption that changes the ancilla needs.
absorb-closureᵠ : (ε : ℕ → ℚ) (cs : ℕ) {C C′ D D′ : Obj}
                  {r r′ : Tᵠ.Test D → Tᵠ.Test C} {s s′ : Tᵠ.Test D′ → Tᵠ.Test C′}
                  {k : D ⇒ D′} {t : C′ ⇒ C} → QB 1 k → QB (cs ℕ.⊔ 1) t
                → ((E : Tᵠ.Test D′) → s E ≈ r (E ∘ k) ∘ t)
                → ((E : Tᵠ.Test D′) → s′ E ≈ r′ (E ∘ k) ∘ t)
                → Agreeᵠ ε r r′ → Agreeᵠ (λ q → ε (simCost q cs)) s s′
absorb-closureᵠ ε cs qk qt stepr stepr′ h =
  ≈ᵃ-resp₀ (λ E → cast₀ (stepr E)) (λ E → cast₀ (Equiv.sym (stepr′ E)))
    (≈ᵃ-mono le (≈ᵃ-post (Tᵠ.pullᵠ⁺ (bud (cs ℕ.⊔ 1) qt))
                         (≈ᵃ-pre (Tᵠ.pullᵠ (bud 1 qk)) h)))
  where
  le : (q c′ : ℕ) → ε (ctxBudget (q ℕ.* 1) ((cs ℕ.⊔ 1) ℕ.* (c′ ℕ.⊔ 1)))
                    ℚ.≤ ε (simCost (ctxBudget q c′) cs)
  le q c′ = ℚₚ.≤-trans
    (ℚₚ.≤-reflexive (cong (λ j → ε (ctxBudget j ((cs ℕ.⊔ 1) ℕ.* (c′ ℕ.⊔ 1))))
                          (ℕₚ.*-identityʳ q)))
    (proj₁ (absorb-closure q cs) ε c′)

ctx-absorb : (ε : ℕ → ℚ) (cs : ℕ) {A B X B′ X′ : Obj}
             {f g : A ⇒ X ⊗₀ B} {f′ g′ : A ⇒ X′ ⊗₀ B′}
             (κ : (W : Obj) → W ⊗₀ (X ⊗₀ B) ⇒ W ⊗₀ (X′ ⊗₀ B′))
           → ((W : Obj) → QB (cs ℕ.⊔ 1) (κ W))
           → ((W : Obj) → id ⊗₁ f′ ≈ κ W ∘ id ⊗₁ f)
           → ((W : Obj) → id ⊗₁ g′ ≈ κ W ∘ id ⊗₁ g)
           → f ≈ᵁᵠ[ ε ] g → f′ ≈ᵁᵠ[ (λ q → ε (simCost q cs)) ] g′
ctx-absorb ε cs κ qκ stepf stepg h = agree⇒ctx (λ q → ε (simCost q cs)) λ W →
  absorb-testᵠ ε cs (qκ W) (λ _ → cut (stepf W)) (λ _ → cut (stepg W))
               (ctx⇒agree ε h W)
  where
  cut : {C D : Obj} {E : D ⇒ Ω} {a : C ⇒ D} {k : Obj} {b : k ⇒ D} {c : C ⇒ k}
      → a ≈ b ∘ c → E ∘ a ≈ (E ∘ b) ∘ c
  cut eq = Equiv.trans (∘-resp-≈ʳ eq) sym-assoc

-- …and at a simulator's action, where `qb-sub` and `qb-T₁` certify the
-- absorbed morphism at `cs ⊔ 1`, the substitution is `simCost _ cs`: the
-- schedule of `UC.Quantitative.Family.≤UC^ωᵉ-sub`, derived.
ctx-sub : (ε : ℕ → ℚ) {s : X ⇒ Z} (cs : ℕ) → QB cs s
        → {f g : A ⇒ X ⊗₀ B} → f ≈ᵁᵠ[ ε ] g
        → (s ⊗₁ id ∘ f) ≈ᵁᵠ[ (λ q → ε (simCost q cs)) ] (s ⊗₁ id ∘ g)
ctx-sub ε {s = s} cs qs h =
  ctx-absorb ε cs (λ _ → id ⊗₁ (s ⊗₁ id))
    (λ _ → subst (λ k → QB k (id ⊗₁ (s ⊗₁ id)))
             (trans (ℕₚ.⊔-assoc cs 1 1) (cong (cs ℕ.⊔_) (ℕₚ.⊔-idem 1)))
             (qb-T₁ (qb-sub qs)))
    (λ _ → split₂ʳ) (λ _ → split₂ʳ) h

-- Sequential composition of two witnesses, with the schedule and the composed
-- simulator of `UC.Quantitative.Family.≤UC^ωᵉ-trans`: the second comparison is
-- pulled back along the first simulator, so what is added to `ε₁` is `ε₂` read
-- at `simCost _ cs` — not `ε₂` — and the simulator is `s ∘ t`.
at-trans : (ε₁ ε₂ : ℕ → ℚ) {s : Y ⇒ X} {t : Z ⇒ Y} (cs : ℕ) → QB cs s
         → {f : A ⇒ X ⊗₀ B} {g : A ⇒ Y ⊗₀ B} {h : A ⇒ Z ⊗₀ B}
         → f ≈ᵁᵠ[ ε₁ ] (s ⊗₁ id ∘ g) → g ≈ᵁᵠ[ ε₂ ] (t ⊗₁ id ∘ h)
         → f ≈ᵁᵠ[ (λ q → ε₁ q ℚ.+ ε₂ (simCost q cs)) ] ((s ∘ t) ⊗₁ id ∘ h)
at-trans ε₁ ε₂ cs qs e₁ e₂ =
  ctx-trans ε₁ ε₂′ e₁
    (ctx-resp ε₂′ Equiv.refl (Equiv.trans sym-assoc (∘-resp-≈ˡ (Equiv.sym split₁ʳ)))
              (ctx-sub ε₂ cs qs e₂))
  where
  ε₂′ : ℕ → ℚ
  ε₂′ q = ε₂ (simCost q cs)
