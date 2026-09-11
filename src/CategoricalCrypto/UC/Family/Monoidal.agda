{-# OPTIONS --safe --without-K #-}

-- `UCSetup` at `Fam`: the indexed family layer's category of grades, made
-- MONOIDAL, and the inherited metatheory read at it.
--
-- `UC.Family` is built over a `Grading`, which has the two one-sided actions
-- and no bifunctor; `UCSetup` wants a `MonoidalCategory` of grades.  The whole
-- gap is the budget: a `Fam`-hom is a base hom plus a polynomial bound and
-- `_≈^ω_` ignores the bound, so every monoidal LAW is the base's read
-- levelwise and the only content is a `QB` certificate per structural
-- morphism.  `UC.Budget.Budget`'s four unitor fields are what that costs; the
-- bifunctor costs nothing extra, because `f ⊗₁ g` factors as `sub f ∘ T₁ _ g`.
--
-- Built BESIDE `UC.Family`'s statements rather than under them.
-- `UC.Family.absorb` lands in `Em UCBase^ω`'s ancilla-quantified `_≈ℰ_`; the
-- same statement at `ucSetup^ω` would land in `_≈ᵁ_`.  The two agree — that is
-- what `UC.Model.Bridge` proves at the model, and the argument is generic in
-- the base — but the kernel congruence is a `no-eta-equality` record, so
-- re-basing `absorb` in place would change its stated type.

open import Categories.Category.Monoidal using (monoidalHelper)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Functor.Bifunctor using (Bifunctor)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (poly-*; poly-const; poly-⊔)
open import Data.Product.Base using (Σ-syntax; _,_)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.UC.Approximate using (ApproximateObservation; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Grading; Observation; UCBase)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.Standard2 as Std2
import CategoricalCrypto.UC.Core.Standard as Std

module CategoricalCrypto.UC.Family.Monoidal
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (obsᴹ : Observation (MonoidalCategory.U M) os ℓs)
  (qapx : ApproximateObservation obsᴹ ℚ-errors ℓa)
  (bud : Budget (MonoidalCategory.U M) (Std.gradingᵗ M) qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

private module 𝕄 = MonoidalCategory M

open MonR 𝕄.monoidal using (serialize₁₂)

-- The base the family layer is taken over: the standard grading of `M`, which
-- is where the four unitor certificates land.
baseᴹ : UCBase o ℓ e os ℓs
baseᴹ = record { 𝒞 = 𝕄.U ; grading = Std.gradingᵗ M ; observation = obsᴹ }

open import CategoricalCrypto.UC.Family baseᴹ qapx bud Ix κ κ-cofinal public

open Budget bud
private module G = Grading Grading^ω

------------------------------------------------------------------------
-- The bifunctor

-- The product certificate the reference arc asked as a field: `f ⊗₁ g` is
-- `(f ⊗₁ id) ∘ (id ⊗₁ g)`, which the action's two one-sided halves certify.
qb-⊗₁ : {A B C D : 𝕄.Obj} {c c′ : ℕ} {f : 𝕄._⇒_ A B} {g : 𝕄._⇒_ C D}
      → QB c f → QB c′ g → QB ((c ℕ.⊔ 1) ℕ.* (c′ ℕ.⊔ 1)) (𝕄._⊗₁_ f g)
qb-⊗₁ qf qg = qb-resp-≈ (𝕄.Equiv.sym serialize₁₂) (qb-∘ (qb-sub qf) (qb-T₁ qg))

infixr 10 _⊗^ω_

_⊗^ω_ : {A B C D : Obj^ω} → A ⇒^ω B → C ⇒^ω D → (A ⊛ω C) ⇒^ω (B ⊛ω D)
(f , p , Pp , wf) ⊗^ω (g , q , Pq , wg) =
    (λ i → 𝕄._⊗₁_ (f i) (g i))
  , (λ n → (p n ℕ.⊔ 1) ℕ.* (q n ℕ.⊔ 1))
  , poly-* (poly-⊔ Pp (poly-const 1)) (poly-⊔ Pq (poly-const 1))
  , λ i → qb-⊗₁ (wf i) (wg i)

⊗^ω-bifunctor : Bifunctor Fam Fam Fam
⊗^ω-bifunctor = record
  { F₀           = λ (A , B) → A ⊛ω B
  ; F₁           = λ (f , g) → f ⊗^ω g
  ; identity     = λ _ → 𝕄.⊗.identity
  ; homomorphism = λ _ → 𝕄.⊗.homomorphism
  ; F-resp-≈     = λ (ef , eg) i → 𝕄.⊗.F-resp-≈ (ef i , eg i)
  }

------------------------------------------------------------------------
-- …and the monoidal structure it carries

Famᴹ : MonoidalCategory o (ℓ ⊔ qs) e
Famᴹ = record
  { U        = Fam
  ; monoidal = monoidalHelper Fam record
    { ⊗          = ⊗^ω-bifunctor
    ; unit       = G.𝟭
    ; unitorˡ    = record
      { from = G.λ⇒ ; to = G.λ⇐
      ; iso  = record { isoˡ = λ _ → 𝕄.unitorˡ.isoˡ ; isoʳ = λ _ → 𝕄.unitorˡ.isoʳ }
      }
    ; unitorʳ    = record
      { from = G.ρ⇒ ; to = G.ρ⇐
      ; iso  = record { isoˡ = λ _ → 𝕄.unitorʳ.isoˡ ; isoʳ = λ _ → 𝕄.unitorʳ.isoʳ }
      }
    ; associator = record
      { from = G.a⇐ ; to = G.a⇒
      ; iso  = record { isoˡ = λ _ → 𝕄.associator.isoˡ ; isoʳ = λ _ → 𝕄.associator.isoʳ }
      }
    ; unitorˡ-commute = λ _ → 𝕄.unitorˡ-commute-from
    ; unitorʳ-commute = λ _ → 𝕄.unitorʳ-commute-from
    ; assoc-commute   = λ _ → 𝕄.assoc-commute-from
    ; triangle        = λ _ → 𝕄.triangle
    ; pentagon        = λ _ → 𝕄.pentagon
    }
  }

------------------------------------------------------------------------

-- P6 of `docs/stduc-supersession-plan.md`: the four fields of `UCSetup` at
-- `Fam`.  `ℳ` is the curried tensor of `Famᴹ` and `ℰ` is `UC.Environment`'s
-- `Observation → Presheaf` construction at `Observation^ω`, so the whole of
-- `Abstract2.AbstractUC` — `≤UC-refl`, `dummy-complete`, `≤UC-trans`,
-- `UC-compose`, `≈ᵁ⇒≈ℰ` — is available at the asymptotic family.
ucSetup^ω : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetup^ω = Std2.StdUC.StdSetup Famᴹ ℰ^ω
