{-# OPTIONS --safe --without-K #-}

-- Admitted elements as a second index
-- (`docs/quantitative-uc-setup-plan.typ` §7.3).
--
-- A distance between tests says nothing about what running them costs, so an
-- allowance-restricted model needs one more datum than `Approx.Controlled`
-- carries: which elements a given allowance admits.  The two indices are
-- independent — an allowance transformation is not determined by an error
-- control — so a filtered map carries its own monotone allowance map.
--
-- Allowances are `ℕ`, the domain the existing resource doctrine already counts
-- in (`UC.Budget.QB`, `ctxBudget`, `simCost`).

open import Categories.Category using (Category)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.Approx.Filtered
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Controlled E
open import CategoricalCrypto.Approx.Space E

private variable c ℓa ℓd : Level

record FilteredSpace (c ℓa ℓd : Level) : Set (suc (c ⊔ ℓa ⊔ ℓd) ⊔ es ⊔ ℓe) where
  field
    space : ApproxSpace c ℓa

  open ApproxSpace space public using (Carrier)

  field
    Admit      : ℕ → Carrier → Set ℓd
    admit-mono : {q q′ : ℕ} {x : Carrier} → q ℕ.≤ q′ → Admit q x → Admit q′ x

record Allowance : Set where
  field
    at       : ℕ → ℕ
    monotone : {q q′ : ℕ} → q ℕ.≤ q′ → at q ℕ.≤ at q′

idᵃ : Allowance
idᵃ = record { at = λ q → q ; monotone = λ le → le }

infixr 9 _∘ᵃ_

_∘ᵃ_ : Allowance → Allowance → Allowance
β ∘ᵃ α = record
  { at = λ q → β.at (α.at q) ; monotone = λ le → β.monotone (α.monotone le) }
  where module α = Allowance α
        module β = Allowance β

record Filtered (X Y : FilteredSpace c ℓa ℓd) : Set (c ⊔ es ⊔ ℓe ⊔ ℓa ⊔ ℓd) where
  private
    module X = FilteredSpace X
    module Y = FilteredSpace Y

  field
    underlying : Controlled X.space Y.space
    allowance  : Allowance

  map = Controlled.map underlying

  field
    admits : {q : ℕ} {x : X.Carrier}
           → X.Admit q x → Y.Admit (Allowance.at allowance q) (map x)

module _ {X Y : FilteredSpace c ℓa ℓd} where

  open Filtered

  infix 4 _≈ᶠ_

  _≈ᶠ_ : Filtered X Y → Filtered X Y → Set (c ⊔ es ⊔ ℓe ⊔ ℓa)
  f ≈ᶠ g = (underlying f ≈ᶜ underlying g)
         × ((q : ℕ) → Allowance.at (allowance f) q ≡ Allowance.at (allowance g) q)

  -- Spelled out rather than lifted through `≈ᶜ-isEquivalence`: that lemma's
  -- spaces arrive as projections of `X`/`Y` and are not inferable here.
  ≈ᶠ-isEquivalence : IsEquivalence _≈ᶠ_
  ≈ᶠ-isEquivalence = record
    { refl  = (((λ _ → ⊑-refl) , λ _ → ⊑-refl) , λ _ → SY.≈[]-refl) , λ _ → refl
    ; sym   = λ (((l , r) , me) , ae) →
        ((r , l) , λ x → SY.≈[]-sym (me x)) , λ q → sym (ae q)
    ; trans = λ (((l₁ , r₁) , me₁) , ae₁) (((l₂ , r₂) , me₂) , ae₂) →
        ( ( (λ ε → ⊑-trans (l₁ ε) (l₂ ε)) , λ ε → ⊑-trans (r₂ ε) (r₁ ε) )
        , λ x → SY.≈[]-mono ⊕-identityˡ (SY.≈[]-trans (me₁ x) (me₂ x)) )
        , λ q → trans (ae₁ q) (ae₂ q)
    }
    where module SY = ApproxSpace (FilteredSpace.space Y)

identityᶠ : {X : FilteredSpace c ℓa ℓd} → Filtered X X
identityᶠ = record { underlying = identityᶜ ; allowance = idᵃ ; admits = λ a → a }

composeᶠ : {X Y Z : FilteredSpace c ℓa ℓd} → Filtered Y Z → Filtered X Y → Filtered X Z
composeᶠ g f = record
  { underlying = composeᶜ (underlying g) (underlying f)
  ; allowance  = allowance g ∘ᵃ allowance f
  ; admits     = λ a → admits g (admits f a)
  }
  where open Filtered

composeᶠ-resp : {X Y Z : FilteredSpace c ℓa ℓd}
                {g g′ : Filtered Y Z} {f f′ : Filtered X Y}
              → g ≈ᶠ g′ → f ≈ᶠ f′ → composeᶠ g f ≈ᶠ composeᶠ g′ f′
composeᶠ-resp {X = X} {Y = Y} {Z = Z} {g = g} {g′ = g′} {f = f} {f′ = f′}
              (ce₁ , ae₁) (ce₂ , ae₂) =
  composeᶜ-resp {X = FilteredSpace.space X} {Y = FilteredSpace.space Y}
                {Z = FilteredSpace.space Z}
                {g = Filtered.underlying g} {g′ = Filtered.underlying g′}
                {f = Filtered.underlying f} {f′ = Filtered.underlying f′} ce₁ ce₂
  , λ q → trans (cong (Allowance.at (Filtered.allowance g)) (ae₂ q))
                (ae₁ (Allowance.at (Filtered.allowance f′) q))

Filt : (c ℓa ℓd : Level)
     → Category (suc (c ⊔ ℓa ⊔ ℓd) ⊔ es ⊔ ℓe) (c ⊔ es ⊔ ℓe ⊔ ℓa ⊔ ℓd) (c ⊔ es ⊔ ℓe ⊔ ℓa)
Filt c ℓa ℓd = record
  { Obj       = FilteredSpace c ℓa ℓd
  ; _⇒_       = Filtered
  ; _≈_       = _≈ᶠ_
  ; id        = identityᶠ
  ; _∘_       = composeᶠ
  -- Each law holds because only the two `at` projections and the underlying
  -- function are compared, and those reduce; the records themselves do not
  -- (a composite control's own law fields are built with `⊑-trans`).
  ; assoc     = λ {_} {_} {_} {D} →
      (((λ _ → ⊑-refl) , λ _ → ⊑-refl)
      , λ _ → ApproxSpace.≈[]-refl (FilteredSpace.space D)) , λ _ → refl
  ; sym-assoc = λ {_} {_} {_} {D} →
      (((λ _ → ⊑-refl) , λ _ → ⊑-refl)
      , λ _ → ApproxSpace.≈[]-refl (FilteredSpace.space D)) , λ _ → refl
  ; identityˡ = λ {_} {B} →
      (((λ _ → ⊑-refl) , λ _ → ⊑-refl)
      , λ _ → ApproxSpace.≈[]-refl (FilteredSpace.space B)) , λ _ → refl
  ; identityʳ = λ {_} {B} →
      (((λ _ → ⊑-refl) , λ _ → ⊑-refl)
      , λ _ → ApproxSpace.≈[]-refl (FilteredSpace.space B)) , λ _ → refl
  ; identity² = λ {A} →
      (((λ _ → ⊑-refl) , λ _ → ⊑-refl)
      , λ _ → ApproxSpace.≈[]-refl (FilteredSpace.space A)) , λ _ → refl
  ; equiv     = λ {A} {B} → ≈ᶠ-isEquivalence {X = A} {Y = B}
  ; ∘-resp-≈  = λ {A} {B} {C} {f} {h} {g} {i} →
      composeᶠ-resp {X = A} {Y = B} {Z = C} {g = f} {g′ = h} {f = g} {f′ = i}
  }
