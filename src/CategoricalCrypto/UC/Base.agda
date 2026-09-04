{-# OPTIONS --safe --without-K #-}

-- What the UC layer asks of its ambient category.
--
-- Two records, deliberately separate: `Grading`, the action of adversary
-- interfaces on processes (an ancilla bypassing a process, a simulator acting
-- on one), and `Observation`, a closed run and a quantitative comparison of
-- what two closed runs show.
--
-- `Observation`'s comparison is a RELATION `_≈[ ε ]_` indexed by a rational
-- slack, not a function `adv : Obs → Obs → ℚ`.  The intended instance's
-- observations are `Dₚ Bool`, whose termination mass is a supremum the layer
-- never forms, so an `adv` field would be uninhabited there — see
-- `ProbabilisticLogic.Dp.Advantage`.  The three pseudometric laws the
-- vanishing-advantage layer spends survive as `≈[]-sym`/`≈[]-trans`/
-- `≈[]-mono`, and agreement `_∼_` — closeness at every positive slack — is
-- then an equivalence by the ε/2 argument, derived here once.

open import Categories.Category.Core using (Category)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
  using (*-distribʳ-+; *-identityˡ; *-monoʳ-<-pos; *-zeroʳ; <⇒≤; ≤-reflexive)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

module CategoricalCrypto.UC.Base where

private
  half-pos : {ε : ℚ} → 0ℚ ℚ.< ε → 0ℚ ℚ.< ½ ℚ.* ε
  half-pos {ε} ε>0 = subst (ℚ._< ½ ℚ.* ε) (*-zeroʳ ½) (*-monoʳ-<-pos ½ ε>0)

  half+half : (ε : ℚ) → ½ ℚ.* ε ℚ.+ ½ ℚ.* ε ≡ ε
  half+half ε = trans (sym (*-distribʳ-+ ε ½ ½)) (*-identityˡ ε)

------------------------------------------------------------------------
-- The grading action

-- `T₁ Y f` runs `f` with an ancilla interface `Y` bypassing it; `sub s` acts on
-- the ancilla alone.  `a⇒` reassociates two nested ancillas, which is all
-- `grade-stable` needs of the action's associativity — hence no unitors and no
-- second half of the iso.
record Grading {o ℓ e} (𝒞 : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  open Category 𝒞

  infixr 8 _⊛_

  field
    _⊛_ : Obj → Obj → Obj
    T₁  : (Y : Obj) {A B : Obj} → A ⇒ B → Y ⊛ A ⇒ Y ⊛ B
    sub : {X Y A : Obj} → X ⇒ Y → X ⊛ A ⇒ Y ⊛ A
    a⇒  : {X Y A : Obj} → X ⊛ (Y ⊛ A) ⇒ (X ⊛ Y) ⊛ A
    a⇐  : {X Y A : Obj} → (X ⊛ Y) ⊛ A ⇒ X ⊛ (Y ⊛ A)

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
-- Query budgets

-- The closure properties the indexed family category consumes, and nothing
-- else: this record is PLUMBING, not the definition of a query bound.  A query
-- bound with content is the amortised-potential certificate of
-- `CategoricalCrypto.UC.QueryBound`, whose counting theorem is what forbids the
-- degenerate `QB c f = ⊤`; here `QB` is a parameter, so the laws alone cannot
-- forbid it.
--
-- Where the reference arc asked eleven laws, eight suffice: the tensor law
-- splits into `qb-T₁`/`qb-sub` (the action's two one-sided halves), and the
-- four unitor laws are gone with the unitors — `grade-stable` never needs
-- `unit ⊛ A ≅ A`.
record Budget {o ℓ e} (𝒞 : Category o ℓ e) (G : Grading 𝒞) (qs : Level)
            : Set (o ⊔ ℓ ⊔ e ⊔ suc qs) where
  open Category 𝒞
  open Grading G

  field
    QB        : ℕ → {A B : Obj} → A ⇒ B → Set qs
    qb-id     : {A : Obj} → QB 1 (id {A})
    qb-∘      : {A B C : Obj} {c c′ : ℕ} {g : B ⇒ C} {f : A ⇒ B}
              → QB c g → QB c′ f → QB (c ℕ.* c′) (g ∘ f)
    qb-resp-≈ : {A B : Obj} {c : ℕ} {f g : A ⇒ B} → f ≈ g → QB c f → QB c g
    qb-mono   : {A B : Obj} {c c′ : ℕ} {f : A ⇒ B} → c ℕ.≤ c′ → QB c f → QB c′ f
    -- `_⊔ 1_`, not `c`: the bypassed interface's own downward relay is one
    -- completed event that an activation from above must have deposited for,
    -- so a rate of zero cannot survive the action.  This is the reference
    -- arc's `qb-⊗` at `c ⊔ 1`, the identity leg's budget being 1.
    qb-T₁     : {Y A B : Obj} {c : ℕ} {f : A ⇒ B} → QB c f → QB (c ℕ.⊔ 1) (T₁ Y f)
    qb-sub    : {X Y A : Obj} {c : ℕ} {s : X ⇒ Y} → QB c s → QB (c ℕ.⊔ 1) (sub {A = A} s)
    qb-a⇒     : {X Y A : Obj} → QB 1 (a⇒ {X} {Y} {A})
    qb-a⇐     : {X Y A : Obj} → QB 1 (a⇐ {X} {Y} {A})

-- The budget a context's two legs afford a strategy playing in its place.  The
-- test's own `c` is what bounds crossings into the plugged interface: the
-- closure of a CLOSED context supplies only ancilla and input responses, so the
-- conservative bound is `c` alone.  The product form is kept for the closures
-- that do relay downwards, but GUARDED at `c′ ⊔ 1`, because a closure with no
-- downward port certifies at `QB 0` and an unguarded `c * 0` charges a context
-- that genuinely queries to a strategy that cannot query at all (external theory
-- review, finding 1).  This is `qb-T₁`'s `c ⊔ 1` guard, one level up and for the
-- same reason.  The principled eventual form is a port-specific bound on
-- crossings into the DISTINGUISHED hole rather than a product of two whole-hom
-- budgets; `docs/protocol-rewrite.md` prices it, and it is not built.
ctxBudget : ℕ → ℕ → ℕ
ctxBudget c c′ = c ℕ.* (c′ ℕ.⊔ 1)

------------------------------------------------------------------------
-- Closed runs and their comparison

record Observation {o ℓ e} (𝒞 : Category o ℓ e) (os ℓs : Level)
                 : Set (o ⊔ ℓ ⊔ e ⊔ suc os ⊔ suc ℓs) where
  open Category 𝒞

  infix 4 _≈[_]_ _∼_

  field
    𝟙 Ω : Obj
    Obs : Set os
    ⟦_⟧ : 𝟙 ⇒ Ω → Obs

    _≈[_]_    : Obs → ℚ → Obs → Set ℓs
    ≈[]-refl  : {x : Obs} → x ≈[ 0ℚ ] x
    ≈[]-sym   : {x y : Obs} {ε : ℚ} → x ≈[ ε ] y → y ≈[ ε ] x
    ≈[]-trans : {x y z : Obs} {ε δ : ℚ} → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε ℚ.+ δ ] z
    ≈[]-mono  : {x y : Obs} {ε δ : ℚ} → ε ℚ.≤ δ → x ≈[ ε ] y → x ≈[ δ ] y
    ⟦⟧-resp-≈ : {u v : 𝟙 ⇒ Ω} → u ≈ v → ⟦ u ⟧ ≈[ 0ℚ ] ⟦ v ⟧

  -- Agreement: no positive slack separates the two.  At the family instance
  -- this unfolds to the vanishing-advantage relation.
  _∼_ : Obs → Obs → Set ℓs
  x ∼ y = (ε : ℚ) → 0ℚ ℚ.< ε → x ≈[ ε ] y

  ∼-refl : {x : Obs} → x ∼ x
  ∼-refl _ ε>0 = ≈[]-mono (<⇒≤ ε>0) ≈[]-refl

  ∼-sym : {x y : Obs} → x ∼ y → y ∼ x
  ∼-sym h ε ε>0 = ≈[]-sym (h ε ε>0)

  ∼-trans : {x y z : Obs} → x ∼ y → y ∼ z → x ∼ z
  ∼-trans h k ε ε>0 = ≈[]-mono (≤-reflexive (half+half ε))
    (≈[]-trans (h (½ ℚ.* ε) (half-pos ε>0)) (k (½ ℚ.* ε) (half-pos ε>0)))

  ⟦⟧-resp-∼ : {u v : 𝟙 ⇒ Ω} → u ≈ v → ⟦ u ⟧ ∼ ⟦ v ⟧
  ⟦⟧-resp-∼ eq _ ε>0 = ≈[]-mono (<⇒≤ ε>0) (⟦⟧-resp-≈ eq)

  -- Transporting an agreement along the ambient hom equality at both ends.
  ∼-cast : {u u′ v v′ : 𝟙 ⇒ Ω} → u ≈ u′ → v ≈ v′ → ⟦ u ⟧ ∼ ⟦ v ⟧ → ⟦ u′ ⟧ ∼ ⟦ v′ ⟧
  ∼-cast eu ev h = ∼-trans (∼-sym (⟦⟧-resp-∼ eu)) (∼-trans h (⟦⟧-resp-∼ ev))

-- A one-sided reading of an observation: the mass it has reached within a
-- budget.  `Observation` compares two observations and never values one, which
-- is what keeps it inhabited at `Dₚ` (see the header); a BOUND on a single
-- observation — what an audit-form security statement is — needs exactly this
-- much more, and no more: a budgeted value and the ε-domination that `_≈[ ε ]_`
-- already implies.  At the intended instance `at` is `Pr≤` and `dominate` is the
-- left half of `_≈ₚ[_]_`, so nothing new is assumed.
record Mass {o ℓ e os ℓs} {𝒞 : Category o ℓ e} (O : Observation 𝒞 os ℓs)
          : Set (os ⊔ ℓs) where
  open Observation O

  field
    at       : ℕ → Obs → ℚ
    dominate : {x y : Obs} {ε : ℚ} → x ≈[ ε ] y
             → (n : ℕ) → Σ[ m ∈ ℕ ] at n x ℚ.≤ at m y ℚ.+ ε

------------------------------------------------------------------------

record UCBase (o ℓ e os ℓs : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ os ⊔ ℓs)) where
  field
    𝒞           : Category o ℓ e
    grading     : Grading 𝒞
    observation : Observation 𝒞 os ℓs

  open Category 𝒞 public
  open Grading grading public
  open Observation observation public
