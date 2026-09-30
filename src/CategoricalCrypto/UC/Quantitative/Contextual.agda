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
-- schedule `λ q r′ → ε (value (q · r′))`: `ctx⇒agree`/`agree⇒ctx` differ by the
-- order in which the closure and the test's certificate are taken and by
-- nothing else.  Both substitution principles are then one datum of a filtered
-- map — `absorb-testᵠ` moves a certified morphism in front of the TEST, which
-- is `pullᵠ`'s allowance map, and `absorb-closureᵠ` moves one behind the
-- CLOSURE, which is `pullᵠ`'s control — and `scale-comm`/`scale-·` (as
-- `Query.absorb-test`/`absorb-closure`) are what makes each of them exact.
-- `ctx-sub` is the instance at a simulator's action;
-- `UC.Quantitative.Family.≈ctx-ext`/`-pre`/`-dom` are the instances at a
-- continuation, an earlier process and a domain plug.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Reasoning as MonR

open import Categories.LocallyGraded
open import Categories.LocallyGraded.Monoidal
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive using (ℕ⁺; 1⁺; _·_; scale; scale-unit; value)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import CategoricalCrypto.Approx.Error using (Approximation; ℚ-ordered)
open import CategoricalCrypto.UC.Quantitative.Query
  using (absorb-closure; absorb-test; module Fl; module Tests)

import Data.Nat.Properties as ℕₚ
import Data.Rational.Properties as ℚₚ

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Quantitative.Contextual
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e) (Rg : GradedSubCat Rates.monoidalCategory M qs)
  {Obs : Set os} (Ap : Approximation Obs ℚ-ordered ℓa)
  (𝟙 Ω : MonoidalCategory.Obj M)
  (⟦_⟧ : MonoidalCategory._⇒_ M 𝟙 Ω → Obs)
  (obs-resp : {u v : MonoidalCategory._⇒_ M 𝟙 Ω}
            → MonoidalCategory._≈_ M u v → Approximation._≈[_]_ Ap ⟦ u ⟧ 0ℚ ⟦ v ⟧)
  where

open MonoidalCategory M
open Fl
open MonR monoidal
open GradedSubCat Rg
module L = LocallyGradedCategory L
open GradedMonoidal (monoidalᴸ Rates.braided) using () renaming (_⊗₁_ to _⊗ʰ_)

module Tᵠ = Tests M Rg Ap 𝟙 Ω ⟦_⟧ obs-resp

private module A = Approximation Ap

private variable A B X Y Z : Obj

------------------------------------------------------------------------
-- The relation, and the filtered instance it is

infix 4 _≈ᵁᵠ[_]_

_≈ᵁᵠ[_]_ : A ⇒ X ⊗₀ B → (ℕ → ℚ) → A ⇒ X ⊗₀ B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≈ᵁᵠ[_]_ {A} {X} {B} f ε g =
  (W : Obj) (E : W ⊗₀ (X ⊗₀ B) ⇒ Ω) (m : 𝟙 ⇒ W ⊗₀ A) {c r′ : ℕ⁺}
  → Image forget c E → Image forget r′ m
  → ⟦ (E ∘ id ⊗₁ f) ∘ m ⟧ A.≈[ ε (value (c · r′)) ] ⟦ (E ∘ id ⊗₁ g) ∘ m ⟧

-- Two pullbacks of tests agreeing on the ADMITTED ones, at the schedule this
-- layer reads: the test's own rate scaled by the closure's.  The
-- bracket a context is written in is not fixed here —
-- `UC.Quantitative.Family._≈ctx[_]_` is the same agreement at `prefixᵒ`, so
-- the two absorptions below serve both.
Agreeᵠ : (ε : ℕ → ℚ) {C D : Obj} (r r′ : Tᵠ.Test D → Tᵠ.Test C) → Set (ℓ ⊔ e ⊔ ℓa ⊔ qs)
Agreeᵠ ε {C} {D} r r′ =
  _≈ᵃ[_]_ {X = Tᵠ.filteredᵠ D} {Y = Tᵠ.filteredᵠ C} r (λ q r′ → ε (value (q · r′))) r′

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
-- map, and `scale-comm` (as `absorb-test`) is what makes the resulting
-- substitution `scale _ r` exact rather than a bound.
absorb-testᵠ : (ε : ℕ → ℚ) (r : ℕ⁺) {C D D′ : Obj}
               {φ φ′ : Tᵠ.Test D → Tᵠ.Test C} {ψ ψ′ : Tᵠ.Test D′ → Tᵠ.Test C}
               {k : D ⇒ D′} → Image forget r k
             → ((E : Tᵠ.Test D′) → ψ E ≈ φ (E ∘ k))
             → ((E : Tᵠ.Test D′) → ψ′ E ≈ φ′ (E ∘ k))
             → Agreeᵠ ε φ φ′ → Agreeᵠ (λ q → ε (scale q r)) ψ ψ′
absorb-testᵠ ε r ck stepr stepr′ h =
  ≈ᵃ-resp₀ (λ E → cast₀ (stepr E)) (λ E → cast₀ (Equiv.sym (stepr′ E)))
    (≈ᵃ-mono (λ q → proj₁ (absorb-test q r ε))
             (≈ᵃ-pre (Tᵠ.pullᵠ (r , Tᵠ.certifiedᴴ ck)) h))

-- …and moving one behind the CLOSURE is `pullᵠ`'s CONTROL, which multiplies
-- the closure's rate, and `scale-·` (as `absorb-closure`) makes the same
-- substitution exact.  The test may move along a structural `k` at the same
-- time, which is what an absorption that changes the ancilla needs.
absorb-closureᵠ : (ε : ℕ → ℚ) (r : ℕ⁺) {C C′ D D′ : Obj}
                  {φ φ′ : Tᵠ.Test D → Tᵠ.Test C} {ψ ψ′ : Tᵠ.Test D′ → Tᵠ.Test C′}
                  {k : D ⇒ D′} {t : C′ ⇒ C} → Image forget 1⁺ k → Image forget r t
                → ((E : Tᵠ.Test D′) → ψ E ≈ φ (E ∘ k) ∘ t)
                → ((E : Tᵠ.Test D′) → ψ′ E ≈ φ′ (E ∘ k) ∘ t)
                → Agreeᵠ ε φ φ′ → Agreeᵠ (λ q → ε (scale q r)) ψ ψ′
absorb-closureᵠ ε r ck ct stepr stepr′ h =
  ≈ᵃ-resp₀ (λ E → cast₀ (stepr E)) (λ E → cast₀ (Equiv.sym (stepr′ E)))
    (≈ᵃ-mono le (≈ᵃ-post (Tᵠ.pullᵠ (r , Tᵠ.certifiedᴴ ct))
                         (≈ᵃ-pre (Tᵠ.pullᵠ (1⁺ , Tᵠ.certifiedᴴ ck)) h)))
  where
  le : (q r′ : ℕ⁺) → ε (value (q · 1⁺ · (r′ · r))) ℚ.≤ ε (scale (value (q · r′)) r)
  le q r′ = ℚₚ.≤-trans
    (ℚₚ.≤-reflexive (cong (λ j → ε (scale j (r′ · r))) (scale-unit (value q))))
    (proj₁ (absorb-closure q r ε) r′)

ctx-absorb : (ε : ℕ → ℚ) (r : ℕ⁺) {A B X B′ X′ : Obj}
             {f g : A ⇒ X ⊗₀ B} {f′ g′ : A ⇒ X′ ⊗₀ B′}
             (κ : (W : Obj) → W ⊗₀ (X ⊗₀ B) ⇒ W ⊗₀ (X′ ⊗₀ B′))
           → ((W : Obj) → Image forget r (κ W))
           → ((W : Obj) → id ⊗₁ f′ ≈ κ W ∘ id ⊗₁ f)
           → ((W : Obj) → id ⊗₁ g′ ≈ κ W ∘ id ⊗₁ g)
           → f ≈ᵁᵠ[ ε ] g → f′ ≈ᵁᵠ[ (λ q → ε (scale q r)) ] g′
ctx-absorb ε r κ cκ stepf stepg h = agree⇒ctx (λ q → ε (scale q r)) λ W →
  absorb-testᵠ ε r (cκ W) (λ _ → cut (stepf W)) (λ _ → cut (stepg W))
               (ctx⇒agree ε h W)
  where
  cut : {C D : Obj} {E : D ⇒ Ω} {a : C ⇒ D} {k : Obj} {b : k ⇒ D} {c : C ⇒ k}
      → a ≈ b ∘ c → E ∘ a ≈ (E ∘ b) ∘ c
  cut eq = Equiv.trans (∘-resp-≈ʳ eq) sym-assoc

-- …and at a simulator's action, certified by whiskering the simulator's
-- certificate at rate `1⁺` on both sides, the substitution is `scale _ r`: the
-- schedule of `UC.Quantitative.Family.≈ctx-sub`, derived.
ctx-sub : (ε : ℕ → ℚ) {s : X ⇒ Z} (r : ℕ⁺) → Image forget r s
        → {f g : A ⇒ X ⊗₀ B} → f ≈ᵁᵠ[ ε ] g
        → (s ⊗₁ id ∘ f) ≈ᵁᵠ[ (λ q → ε (scale q r)) ] (s ⊗₁ id ∘ g)
ctx-sub ε r cs h =
  ctx-absorb ε r (λ _ → id ⊗₁ (_ ⊗₁ id))
    (λ _ → L.sub[ ℕₚ.≤-reflexive (trans (ℕₚ.*-identityˡ _) (ℕₚ.*-identityʳ (value r))) ]
               (L.id ⊗ʰ (Tᵠ.certifiedᴴ cs ⊗ʰ L.id))
         , Equiv.refl)
    (λ _ → split₂ʳ) (λ _ → split₂ʳ) h

-- Sequential composition of two witnesses, with the schedule and the composed
-- simulator of `UC.Quantitative.Family.≤UC^ωᵉ-trans`: the second comparison is
-- pulled back along the first simulator, so what is added to `ε₁` is `ε₂` read
-- at `scale _ r` — not `ε₂` — and the simulator is `s ∘ t`.
at-trans : (ε₁ ε₂ : ℕ → ℚ) {s : Y ⇒ X} {t : Z ⇒ Y} (r : ℕ⁺) → Image forget r s
         → {f : A ⇒ X ⊗₀ B} {g : A ⇒ Y ⊗₀ B} {h : A ⇒ Z ⊗₀ B}
         → f ≈ᵁᵠ[ ε₁ ] (s ⊗₁ id ∘ g) → g ≈ᵁᵠ[ ε₂ ] (t ⊗₁ id ∘ h)
         → f ≈ᵁᵠ[ (λ q → ε₁ q ℚ.+ ε₂ (scale q r)) ] ((s ∘ t) ⊗₁ id ∘ h)
at-trans ε₁ ε₂ r cs e₁ e₂ =
  ctx-trans ε₁ ε₂′ e₁
    (ctx-resp ε₂′ Equiv.refl (Equiv.trans sym-assoc (∘-resp-≈ˡ (Equiv.sym split₁ʳ)))
              (ctx-sub ε₂ r cs e₂))
  where
  ε₂′ : ℕ → ℚ
  ε₂′ q = ε₂ (scale q r)
