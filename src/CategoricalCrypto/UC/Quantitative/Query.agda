{-# OPTIONS --safe --without-K #-}

-- The query-sensitive test model as a genuine filtered instance
-- (`docs/quantitative-uc-setup-plan.typ` §7.3).
--
-- Tests are compared through CERTIFIED closures, at a schedule read off the
-- closure's own allowance.  Pulling a test back along a morphism of budget
-- `ch` moves BOTH indices, and both moves are one `qb-∘`: the closure `h ∘ m`
-- costs `ch * c′`, so the schedule is reindexed by `ch *_`, and the test
-- `E ∘ h` costs `q * ch`, so the admitted allowance is reindexed by `_* ch`.
-- That is exactly a `Approx.Filtered` map, error control and allowance map
-- together.
--
-- The base is therefore the BUDGETED morphisms, not `𝒞`: an arbitrary morphism
-- induces no controlled map on bounded tests, and a control has to be
-- determined by the morphism, so the budget is part of the hom and of its
-- equality.  `QueryBounds` is the fragment of `UC.Budget.Budget` this spends —
-- no tensor, in `UC.Environment.Presheaf`'s discipline.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Presheaf using (Presheaf)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; sym; trans)

open import CategoricalCrypto.Approx.Error
  using (OrderedErrorAlgebra; ℚ-ordered; ≈[]-resp₀)
open import CategoricalCrypto.Approx.Schedule using (pointwise; module Reindexing)
open import CategoricalCrypto.UC.Approximate using (Approximation; ℚ-errors)
open import CategoricalCrypto.UC.Budget
  using (Budget; ctxBudget; ctxBudget-closure; ctxBudget-simCost; simCost)

import CategoricalCrypto.Approx.Controlled as Controlledᴹ
import CategoricalCrypto.Approx.Filtered as Filteredᴹ
import CategoricalCrypto.Approx.Space as Spaceᴹ
import Data.Nat.Properties as ℕₚ

module CategoricalCrypto.UC.Quantitative.Query where

-- Schedules in the closure allowance.
Sched = pointwise ℕ ℚ-ordered

private
  module S = Controlledᴹ Sched

open Reindexing {I = ℕ} ℚ-ordered using (reindex; reindex-cong)

------------------------------------------------------------------------
-- The two absorptions of `UC.Budget`, as controls

-- Absorbing a morphism of cost `cs` into the TEST is an exact substitution in
-- the allowance, so the two controls agree in both directions…
absorb-test : (c cs : ℕ)
            → reindex (λ c′ → ctxBudget (c ℕ.* (cs ℕ.⊔ 1)) c′)
              S.≐ᶜ reindex (λ c′ → simCost (ctxBudget c c′) cs)
absorb-test c cs = reindex-cong (λ c′ → ctxBudget-simCost c c′ cs)

-- …and so is absorbing into the CLOSURE, once the closure's certificate is
-- bumped past the leg `ctxBudget` guards (`UC.Budget.ctxBudget-closure`).
absorb-closure : (c cs : ℕ)
               → reindex (λ c′ → ctxBudget c ((cs ℕ.⊔ 1) ℕ.* (c′ ℕ.⊔ 1)))
                 S.≐ᶜ reindex (λ c′ → simCost (ctxBudget c c′) cs)
absorb-closure c cs = reindex-cong (λ c′ → ctxBudget-closure c c′ cs)

record QueryBounds {o ℓ e : Level} (𝒞 : Category o ℓ e) (qs : Level)
                 : Set (o ⊔ ℓ ⊔ e ⊔ suc qs) where
  open Category 𝒞

  field
    QB      : ℕ → {A B : Obj} → A ⇒ B → Set qs
    qb-id   : {A : Obj} → QB 1 (id {A})
    qb-∘    : {A B C : Obj} {c c′ : ℕ} {g : B ⇒ C} {f : A ⇒ B}
            → QB c g → QB c′ f → QB (c ℕ.* c′) (g ∘ f)
    qb-mono : {A B : Obj} {c c′ : ℕ} {f : A ⇒ B} → c ℕ.≤ c′ → QB c f → QB c′ f

fromBudget : {o ℓ e qs : Level} {M : MonoidalCategory o ℓ e}
           → Budget M qs → QueryBounds (MonoidalCategory.U M) qs
fromBudget B = record { QB = QB ; qb-id = qb-id ; qb-∘ = qb-∘ ; qb-mono = qb-mono }
  where open Budget B

module Tests
  {o ℓ e os ℓa qs : Level} (𝒞 : Category o ℓ e) (B : QueryBounds 𝒞 qs)
  {Obs : Set os} (Ap : Approximation Obs ℚ-errors ℓa)
  (𝟙 Ω : Category.Obj 𝒞)
  (⟦_⟧ : Category._⇒_ 𝒞 𝟙 Ω → Obs)
  (obs-resp : {u v : Category._⇒_ 𝒞 𝟙 Ω}
            → Category._≈_ 𝒞 u v → Approximation._≈[_]_ Ap ⟦ u ⟧ 0ℚ ⟦ v ⟧)
  where

  open Category 𝒞
  open QueryBounds B

  private
    module Sp = Spaceᴹ Sched
    module Fl = Filteredᴹ Sched
    module A  = Approximation Ap

  Test Closure : Obj → Set ℓ
  Test C    = C ⇒ Ω
  Closure C = 𝟙 ⇒ C

  ------------------------------------------------------------------------
  -- Tests at a schedule

  infix 4 _≈ᵠ[_]_

  _≈ᵠ[_]_ : {C : Obj} → Test C → (ℕ → ℚ) → Test C → Set (ℓ ⊔ ℓa ⊔ qs)
  _≈ᵠ[_]_ {C} E τ F =
    (m : Closure C) (c′ : ℕ) → QB c′ m → ⟦ E ∘ m ⟧ A.≈[ τ c′ ] ⟦ F ∘ m ⟧

  approxᵠ : (C : Obj)
          → Approximation (Test C) (OrderedErrorAlgebra.errors Sched) (ℓ ⊔ ℓa ⊔ qs)
  approxᵠ C = record
    { _≈[_]_    = _≈ᵠ[_]_
    ; ≈[]-refl  = λ _ _ _ → A.≈[]-refl
    ; ≈[]-sym   = λ h m c′ qb → A.≈[]-sym (h m c′ qb)
    ; ≈[]-trans = λ h k m c′ qb → A.≈[]-trans (h m c′ qb) (k m c′ qb)
    ; ≈[]-mono  = λ le h m c′ qb → A.≈[]-mono (le c′) (h m c′ qb)
    }

  spaceᵠ : Obj → Sp.ApproxSpace ℓ (ℓ ⊔ ℓa ⊔ qs)
  spaceᵠ C = record { Carrier = Test C ; approx = approxᵠ C }

  -- …and the filtration: which allowance admits which test.
  filteredᵠ : Obj → Fl.FilteredSpace ℓ (ℓ ⊔ ℓa ⊔ qs) qs
  filteredᵠ C = record
    { space = spaceᵠ C ; Admit = λ q E → QB q E ; admit-mono = qb-mono }

  ------------------------------------------------------------------------
  -- The budgeted base

  record Budgeted (C D : Obj) : Set (ℓ ⊔ qs) where
    field
      hom       : C ⇒ D
      budget    : ℕ
      certified : QB budget hom

  open Budgeted

  infix 4 _≈ᵇ_

  _≈ᵇ_ : {C D : Obj} → Budgeted C D → Budgeted C D → Set e
  f ≈ᵇ g = (hom f ≈ hom g) × (budget f ≡ budget g)

  -- The budget is in the hom EQUALITY too: two morphisms certified at
  -- different allowances reindex a schedule differently.
  𝒞ᵇ : Category o (ℓ ⊔ qs) e
  𝒞ᵇ = record
    { Obj = Obj
    ; _⇒_ = Budgeted
    ; _≈_ = _≈ᵇ_
    ; id  = record { hom = id ; budget = 1 ; certified = qb-id }
    ; _∘_ = λ g f → record
        { hom = hom g ∘ hom f
        ; budget = budget g ℕ.* budget f
        ; certified = qb-∘ (certified g) (certified f) }
    ; assoc     = λ {_} {_} {_} {_} {f} {g} {h} →
        assoc , ℕₚ.*-assoc (budget h) (budget g) (budget f)
    ; sym-assoc = λ {_} {_} {_} {_} {f} {g} {h} →
        sym-assoc , sym (ℕₚ.*-assoc (budget h) (budget g) (budget f))
    ; identityˡ = λ {_} {_} {f} → identityˡ , ℕₚ.*-identityˡ (budget f)
    ; identityʳ = λ {_} {_} {f} → identityʳ , ℕₚ.*-identityʳ (budget f)
    ; identity² = identity² , ℕₚ.*-identityˡ 1
    ; equiv = record
        { refl  = Equiv.refl , refl
        ; sym   = λ (he , be) → Equiv.sym he , sym be
        ; trans = λ (he₁ , be₁) (he₂ , be₂) → Equiv.trans he₁ he₂ , trans be₁ be₂ }
    ; ∘-resp-≈ = λ (he₁ , be₁) (he₂ , be₂) →
        ∘-resp-≈ he₁ he₂ , cong₂ ℕ._*_ be₁ be₂
    }

  ------------------------------------------------------------------------
  -- Pullback moves both indices, and each move is one `qb-∘`

  pullᵠ : {C D : Obj} → Budgeted C D → Fl.Filtered (filteredᵠ D) (filteredᵠ C)
  pullᵠ h = record
    { underlying = record
        { map     = λ E → E ∘ hom h
        ; control = reindex (λ c′ → budget h ℕ.* c′)
        ; preserves = λ hyp n c″ qbn →
            ≈[]-resp₀ ℚ-ordered Ap (obs-resp assoc) (obs-resp sym-assoc)
              (hyp (hom h ∘ n) (budget h ℕ.* c″) (qb-∘ (certified h) qbn))
        }
    ; allowance = record
        { at = λ q → q ℕ.* budget h ; monotone = ℕₚ.*-monoˡ-≤ (budget h) }
    ; admits = λ qbE → qb-∘ qbE (certified h)
    }

  -- …and at a simulator's action, whose budget `Budget.qb-sub` certifies at
  -- `cs ⊔ 1`, that allowance map IS `simCost _ cs` — the substitution the
  -- existing composition theorems perform (`UC.Asymptotic.Compose`), obtained
  -- here from the filtered structure rather than stated as a UC axiom.
  pull-simCost : {C D : Obj} (h : Budgeted C D) (cs : ℕ) → budget h ≡ cs ℕ.⊔ 1
               → (q : ℕ) → Fl.Allowance.at (Fl.Filtered.allowance (pullᵠ h)) q
                         ≡ simCost q cs
  pull-simCost h cs eq q = cong (q ℕ.*_) eq

  Qᵠ : Presheaf 𝒞ᵇ (Fl.Filt ℓ (ℓ ⊔ ℓa ⊔ qs) qs)
  Qᵠ = record
    { F₀ = filteredᵠ
    ; F₁ = pullᵠ
    ; identity = ( reindex-cong ℕₚ.*-identityˡ
                 , λ _ _ _ _ → obs-resp (∘-resp-≈ˡ identityʳ) ) , ℕₚ.*-identityʳ
    ; homomorphism = λ {_} {_} {_} {f} {g} →
        ( reindex-cong (ℕₚ.*-assoc (budget f) (budget g))
        , λ _ _ _ _ → obs-resp (∘-resp-≈ˡ sym-assoc) )
        , λ q → sym (ℕₚ.*-assoc q (budget f) (budget g))
    ; F-resp-≈ = λ (he , be) → ( reindex-cong (λ c′ → cong (ℕ._* c′) be)
                               , λ _ _ _ _ → obs-resp (∘-resp-≈ˡ (∘-resp-≈ʳ he)) )
                               , λ q → cong (q ℕ.*_) be
    }
