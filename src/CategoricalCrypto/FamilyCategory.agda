{-# OPTIONS --safe --without-K #-}

-- 𝒞^ω, the security-parameter family category over an axiomatized
-- machine layer: objects are ℕ-indexed channel families, homs carry
-- a polynomial query budget.

open import Level

open import CategoricalCrypto.MachineAxioms

module CategoricalCrypto.FamilyCategory
  {o ℓ e os ℓs qs : Level} (MA : MachineAxioms o ℓ e os ℓs qs) where

open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Product

open import Categories.Category
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Functor.Bifunctor

open MachineAxioms MA
open MonoidalUtilities.Shorthands 𝕄.monoidal

Obj^ω : Set o
Obj^ω = ℕ → 𝕄.Obj

private variable A B : Obj^ω

Δ : 𝕄.Obj → Obj^ω
Δ X _ = X

𝟙^ω : Obj^ω
𝟙^ω = Δ 𝕄.unit

-- downward queries of f are polynomially-bounded
PolyQB : (∀ n → A n 𝕄.⇒ B n) → Set qs
PolyQB f = Σ[ p ∈ (ℕ → ℕ) ] Poly p × ∀ n → QB (p n) (f n)

qb1 : {f : ∀ n → A n 𝕄.⇒ B n} → (∀ n → QB 1 (f n)) → PolyQB f
qb1 w = (λ _ → 1) , poly-const 1 , w

_⇒^ω_ : Obj^ω → Obj^ω → Set (ℓ ⊔ qs)
A ⇒^ω B = Σ (∀ n → A n 𝕄.⇒ B n) PolyQB

_≈^ω_ : (f g : A ⇒^ω B) → Set e
f ≈^ω g = ∀ n → proj₁ f n 𝕄.≈ proj₁ g n

Fam : Category o (ℓ ⊔ qs) e
Fam = record
  { Obj       = Obj^ω
  ; _⇒_       = _⇒^ω_
  ; _≈_       = _≈^ω_
  ; id        = (λ _ → 𝕄.id) , qb1 (λ _ → qb-id)
  ; _∘_       = λ (g , p , Pp , wg) (f , q , Pq , wf) →
      (λ n → g n 𝕄.∘ f n) , (λ n → p n ℕ.* q n) , poly-* Pp Pq , λ n → qb-∘ (wg n) (wf n)
  ; assoc     = λ _ → 𝕄.assoc
  ; sym-assoc = λ _ → 𝕄.sym-assoc
  ; identityˡ = λ _ → 𝕄.identityˡ
  ; identityʳ = λ _ → 𝕄.identityʳ
  ; identity² = λ _ → 𝕄.identity²
  ; equiv     = record
    { refl  = λ _ → 𝕄.Equiv.refl
    ; sym   = λ f≈g n → 𝕄.Equiv.sym (f≈g n)
    ; trans = λ f≈g g≈h n → 𝕄.Equiv.trans (f≈g n) (g≈h n) }
  ; ∘-resp-≈  = λ g≈i f≈h n → 𝕄.∘-resp-≈ (g≈i n) (f≈h n)
  }

-- pointwise tensor product
⊗^ω : Bifunctor Fam Fam Fam
⊗^ω = record
  { F₀           = λ (A , B) n → A n 𝕄.⊗₀ B n
  ; F₁           = λ ((f , p , Pp , wf) , (g , q , Pq , wg)) →
      (λ n → f n 𝕄.⊗₁ g n) , (λ n → p n ℕ.⊔ q n) , poly-⊔ Pp Pq , λ n → qb-⊗ (wf n) (wg n)
  ; identity     = λ _ → 𝕄.⊗.identity
  ; homomorphism = λ _ → 𝕄.⊗.homomorphism
  ; F-resp-≈     = λ (f≈ , g≈) n → 𝕄.⊗.F-resp-≈ (f≈ n , g≈ n)
  }

monoidal^ω : Monoidal Fam
monoidal^ω = record
  { ⊗                    = ⊗^ω
  ; unit                 = 𝟙^ω
  ; unitorˡ              = record
    { from = (λ _ → λ⇒) , qb1 (λ _ → qb-λ⇒) ; to = (λ _ → λ⇐) , qb1 (λ _ → qb-λ⇐)
    ; iso  = record { isoˡ = λ _ → 𝕄.unitorˡ.isoˡ ; isoʳ = λ _ → 𝕄.unitorˡ.isoʳ } }
  ; unitorʳ              = record
    { from = (λ _ → ρ⇒) , qb1 (λ _ → qb-ρ⇒) ; to = (λ _ → ρ⇐) , qb1 (λ _ → qb-ρ⇐)
    ; iso  = record { isoˡ = λ _ → 𝕄.unitorʳ.isoˡ ; isoʳ = λ _ → 𝕄.unitorʳ.isoʳ } }
  ; associator           = record
    { from = (λ _ → α⇒) , qb1 (λ _ → qb-α⇒) ; to = (λ _ → α⇐) , qb1 (λ _ → qb-α⇐)
    ; iso  = record { isoˡ = λ _ → 𝕄.associator.isoˡ ; isoʳ = λ _ → 𝕄.associator.isoʳ } }
  ; unitorˡ-commute-from = λ _ → 𝕄.unitorˡ-commute-from
  ; unitorˡ-commute-to   = λ _ → 𝕄.unitorˡ-commute-to
  ; unitorʳ-commute-from = λ _ → 𝕄.unitorʳ-commute-from
  ; unitorʳ-commute-to   = λ _ → 𝕄.unitorʳ-commute-to
  ; assoc-commute-from   = λ _ → 𝕄.assoc-commute-from
  ; assoc-commute-to     = λ _ → 𝕄.assoc-commute-to
  ; triangle             = λ _ → 𝕄.triangle
  ; pentagon             = λ _ → 𝕄.pentagon
  }

𝒞^ω : MonoidalCategory o (ℓ ⊔ qs) e
𝒞^ω = record { U = Fam ; monoidal = monoidal^ω }

-- Budgeted test families and budgeted closures are ordinary 𝒞^ω-homs
Test^ω : Obj^ω → Set (ℓ ⊔ qs)
Test^ω A = A ⇒^ω Δ Ω

Closure^ω : Obj^ω → Set (ℓ ⊔ qs)
Closure^ω A = 𝟙^ω ⇒^ω A
