{-# OPTIONS --safe --without-K #-}

-- What the UC layer asks of its ambient category, QUALITATIVELY.
--
-- Two records, deliberately separate: `Grading`, the action of adversary
-- interfaces on processes (an ancilla bypassing a process, a simulator acting
-- on one), and `Observation`, a closed run and an equivalence on what two
-- closed runs show.
--
-- The observation is an EQUIVALENCE and nothing more.  A general UC setup need
-- not support quantitative observations: rational advantage, security
-- parameters and negligible functions belong to a model, so the ε-indexed
-- relation and the ε/2 argument that used to sit here live in
-- `CategoricalCrypto.UC.Approximate`, which also constructs an `Observation`
-- out of one (`Induced.observation`) — that construction is how the intended
-- `Dₚ` model and the asymptotic family both arrive.  Query budgets are the
-- same kind of model datum and live in `CategoricalCrypto.UC.Budget`.
--
-- The grading action does NOT leave: adversary interfaces and simulators are
-- intrinsic to UC, and `_≤UC_` is stated over them (`UC.Emulation`).
--
-- Named `UCBase` rather than `UCSetup` because `CategoricalCrypto.UCSetup` is
-- the inherited record of the same intent and a strictly stronger one — it asks
-- for a monoidal category of grades and a graded Kleisli triple, neither of
-- which the intended model has.  `docs/protocol-rewrite.md` has the map.

open import Categories.Category.Core using (Category)

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Structures using (IsEquivalence)

module CategoricalCrypto.UC.Core where

------------------------------------------------------------------------
-- The grading action

-- `T₁ Y f` runs `f` with an ancilla interface `Y` bypassing it; `sub s` acts on
-- the ancilla alone.  `a⇒` reassociates two nested ancillas, which is all
-- `grade-stable` needs of the action's associativity — hence no second half of
-- the iso.
--
-- `𝟭` is the empty ancilla and `λ⇒`/`λ⇐`/`ρ⇒`/`ρ⇐` attach and drop it.  They
-- carry NO laws, for the same reason `a⇒` carries only the two it does: nothing
-- in the qualitative core needs them.  They are here because a `Budget` must be
-- able to certify them — `Grading` is what a budget is stated over, and
-- `UC.Family.Monoidal` needs a `QB` certificate for each of the four in order
-- to assemble the levelwise grading into a `MonoidalCategory`.
record Grading {o ℓ e} (𝒞 : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category 𝒞

  infixr 8 _⊛_

  field
    _⊛_ : Obj → Obj → Obj
    𝟭   : Obj
    T₁  : (Y : Obj) {A B : Obj} → A ⇒ B → Y ⊛ A ⇒ Y ⊛ B
    sub : {X Y A : Obj} → X ⇒ Y → X ⊛ A ⇒ Y ⊛ A
    a⇒  : {X Y A : Obj} → X ⊛ (Y ⊛ A) ⇒ (X ⊛ Y) ⊛ A
    a⇐  : {X Y A : Obj} → (X ⊛ Y) ⊛ A ⇒ X ⊛ (Y ⊛ A)
    λ⇒  : {A : Obj} → 𝟭 ⊛ A ⇒ A
    λ⇐  : {A : Obj} → A ⇒ 𝟭 ⊛ A
    ρ⇒  : {A : Obj} → A ⊛ 𝟭 ⇒ A
    ρ⇐  : {A : Obj} → A ⇒ A ⊛ 𝟭

    T₁-resp-≈  : {Y A B : Obj} {f g : A ⇒ B} → f ≈ g → T₁ Y f ≈ T₁ Y g
    T₁-id      : {Y A : Obj} → T₁ Y (id {A}) ≈ id
    T₁-∘       : {Y A B C : Obj} {g : B ⇒ C} {f : A ⇒ B}
               → T₁ Y (g ∘ f) ≈ T₁ Y g ∘ T₁ Y f
    sub-resp-≈ : {X Y A : Obj} {s t : X ⇒ Y} → s ≈ t → sub {A = A} s ≈ sub t
    sub-id     : {X A : Obj} → sub {A = A} (id {X}) ≈ id
    sub-∘      : {X Y Z A : Obj} {t : Y ⇒ Z} {s : X ⇒ Y}
               → sub {A = A} (t ∘ s) ≈ sub t ∘ sub s
    a-isoˡ     : {X Y A : Obj} → a⇐ {X} {Y} {A} ∘ a⇒ ≈ id
    a-nat      : {X Y A B : Obj} {f : A ⇒ B}
               → a⇒ ∘ T₁ X (T₁ Y f) ≈ T₁ (X ⊛ Y) f ∘ a⇒

------------------------------------------------------------------------
-- Closed runs and their comparison

record Observation {o ℓ e} (𝒞 : Category o ℓ e) (os ℓs : Level)
                 : Set (o ⊔ ℓ ⊔ e ⊔ suc os ⊔ suc ℓs) where
  open Category 𝒞

  infix 4 _∼_

  field
    𝟙 Ω : Obj
    Obs : Set os
    ⟦_⟧ : 𝟙 ⇒ Ω → Obs

    _∼_             : Obs → Obs → Set ℓs
    ∼-isEquivalence : IsEquivalence _∼_
    ⟦⟧-resp-≈       : {u v : 𝟙 ⇒ Ω} → u ≈ v → ⟦ u ⟧ ∼ ⟦ v ⟧

  open IsEquivalence ∼-isEquivalence public
    using () renaming (refl to ∼-refl; sym to ∼-sym; trans to ∼-trans)

  -- Transporting an agreement along the ambient hom equality at both ends.
  ∼-cast : {u u′ v v′ : 𝟙 ⇒ Ω} → u ≈ u′ → v ≈ v′ → ⟦ u ⟧ ∼ ⟦ v ⟧ → ⟦ u′ ⟧ ∼ ⟦ v′ ⟧
  ∼-cast eu ev h = ∼-trans (∼-sym (⟦⟧-resp-≈ eu)) (∼-trans h (⟦⟧-resp-≈ ev))

------------------------------------------------------------------------

record UCBase (o ℓ e os ℓs : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ os ⊔ ℓs)) where
  field
    𝒞           : Category o ℓ e
    grading     : Grading 𝒞
    observation : Observation 𝒞 os ℓs

  open Category 𝒞 public
  open Grading grading public
  open Observation observation public
