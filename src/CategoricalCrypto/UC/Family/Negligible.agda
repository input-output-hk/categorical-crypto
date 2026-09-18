{-# OPTIONS --safe --without-K #-}

-- The negligible tier as a SECOND observation on the family category, and the
-- one-way bridge into it (`docs/graded-observation-redesign.md`).
--
-- `UC.Family`'s closing comment records what it does not deliver: an
-- `Observation` whose comparison keeps a negligible error witness, because
-- `Induced` builds one by quantifying an ambient ε away.  It is not a core
-- redesign though — `UC.Core.Observation` asks for an ARBITRARY equivalence
-- (`UC/Core.agda:80-93`), and `UC.Approximate.Local`'s `_∼ᴺ_` is one.  So the
-- whole negligible tier is this instance plus the emulation notions inherited
-- at it, and nothing in the qualitative core moves: `Observation^ω` and
-- `_≈ℰ_` are exactly as they were.
--
-- `_≈ℰⁿ_` implies the new relation at every context by SPECIALIZING its global
-- budget-indexed error to the allowance that context carries — the only
-- allowance either relation ever reads `ε` at.  The converse does not hold and
-- the two are deliberately not identified: a witness chosen per context is
-- weaker than one global bound, and no uniformization theorem closes the gap
-- (`docs/protocol-implementation-review.md` §4).
--
-- The acceptance criteria of review §1 — a one-shot `2⁻ⁿ` difference admitted,
-- a one-shot `1/(n+1)` difference rejected — are theorems about `_∼ᴺ_` at a
-- separating approximation, proved in `UC.Approximate.LocalTests`.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁)
open import Data.Rational using (0ℚ)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.UC.Approximate
  using (ApproximateObservation; Negligible-0; ℚ-errors)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Core using (Observation; UCBase)

import CategoricalCrypto.UC.Core.Standard as Std
import CategoricalCrypto.UC.Environment as Env

module CategoricalCrypto.UC.Family.Negligible
  {o ℓ e os ℓs ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (obsᴹ : Observation (MonoidalCategory.U M) os ℓs)
  (qapx : ApproximateObservation obsᴹ ℚ-errors ℓa)
  (bud : Budget (MonoidalCategory.U M) (Std.gradingᵗ M) qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M obsᴹ qapx bud Ix κ κ-cofinal

open UCBase baseᴹ
open ApproximateObservation qapx

open import CategoricalCrypto.UC.Approximate.Local approx Ix κ public

------------------------------------------------------------------------
-- The instance

Observationᴺ : Observation Fam os ℓa
Observationᴺ = record
  { 𝟙 = Δ 𝟙 ; Ω = Δ Ω ; Obs = Ix → Obs ; ⟦_⟧ = λ u i → ⟦ proj₁ u i ⟧
  ; _∼_ = _∼ᴺ_
  ; ∼-isEquivalence = ∼ᴺ-isEquivalence
  ; ⟦⟧-resp-≈ = λ eq → (λ _ → 0ℚ) , Negligible-0 , λ i → ⟦⟧-resp-≈₀ (eq i)
  }

UCBaseᴺ : UCBase o (ℓ ⊔ qs) e os ℓa
UCBaseᴺ = record
  { 𝒞 = Fam ; grading = Std.gradingᵗ Famᴹ ; observation = Observationᴺ }

-- The relation the tier is FOR, renamed apart from `UC.Family`'s.  The
-- environment metatheory is not renamed alongside: it is
-- `CategoricalCrypto.UC.Environment UCBaseᴺ`, reachable by applying that
-- module, and a second copy of it under ᴺ names would be the parallel API this
-- tier is meant not to be.  The tier's EMULATION ORDER is `Abstract2`'s at
-- `ucSetupᴺ` (`UC.Family.Negligible.Setup`, and the gate in
-- `docs/retirement-negligible-order.md`).
private module N = Env UCBaseᴺ

open N public using () renaming (_≈ℰ_ to _≈ℰᴺ_)

------------------------------------------------------------------------
-- The one-way bridge

-- The homs are EXPLICIT for a measured reason: both relations read them under
-- an application, so no value of one determines them by unification, and left
-- to inference the polynomial each carries is elaborated as a meta — 2m25 s of
-- `Poly` arithmetic against 8 s.
≈ℰⁿ⇒≈ℰᴺ : {A B : Obj^ω} (f g : A ⇒^ω B) → f ≈ℰⁿ g → f ≈ℰᴺ g
≈ℰⁿ⇒≈ℰᴺ f g (ε , neg , bnd) Y Et m =
  (λ n → ε n (ctxQB (qbOf Et) (qbOf m) n)) , neg Y Et m , bnd Y Et m
