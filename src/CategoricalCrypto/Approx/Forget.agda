{-# OPTIONS --safe --without-K #-}

-- The two ways to forget an approximate space to a setoid
-- (`docs/quantitative-uc-setup-plan.typ` §3), and the comparison between them.
--
-- Both keep the carrier and the functions and change only the equality: `F₀`
-- identifies at ZERO error, `F₊` at EVERY POSITIVE error.  `F₊`'s equivalence
-- is `Approximation.∼ᵃ-isEquivalence` — the ε/2 argument, proved once upstream.
--
-- The comparison `forget` is the identity on carriers and is deliberately NOT
-- an isomorphism: a space whose error balls are not closed has points that no
-- positive error separates and zero error does (`Approx.Separating`).  That is
-- why an exact bound must stay in `Approx` rather than be asked to respect
-- `F₊`'s coarser equality.
--
-- The levels are module PARAMETERS, and the relation level is spelled
-- `es ⊔ ℓe ⊔ ℓb`: `∼ᵃ` quantifies over an error and a positivity proof, so only
-- at that shape do the two functors share a target category, which a natural
-- transformation between them requires.  Parameters rather than generalized
-- variables because `⊔` is not invertible — `ℓb` is not recoverable from
-- `es ⊔ ℓe ⊔ ℓb` by unification.  At `ℚ-ordered` both error levels are `0ℓ`.

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation using (NaturalTransformation)

open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.Approx.Forget
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) (c ℓb : Level) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Space E

⟦_⟧₀ ⟦_⟧₊ : ApproxSpace c (es ⊔ ℓe ⊔ ℓb) → Setoid c (es ⊔ ℓe ⊔ ℓb)
⟦ X ⟧₀ = zeroSetoid X
⟦ X ⟧₊ = record
  { Carrier = X.Carrier ; _≈_ = X._∼ᵃ_ ; isEquivalence = X.∼ᵃ-isEquivalence }
  where module X = ApproxSpace X

F₀ F₊ : Functor (Approx c (es ⊔ ℓe ⊔ ℓb)) (Setoids c (es ⊔ ℓe ⊔ ℓb))
F₀ = record
  { F₀ = ⟦_⟧₀
  ; F₁ = λ f → record { to = Nonexpansive.map f ; cong = Nonexpansive.preserves f }
  ; identity     = λ {A} → ApproxSpace.≈[]-refl A
  ; homomorphism = λ {_} {_} {Z} → ApproxSpace.≈[]-refl Z
  ; F-resp-≈     = λ e {x} → e x
  }
F₊ = record
  { F₀ = ⟦_⟧₊
  ; F₁ = λ f → record
      { to = Nonexpansive.map f ; cong = λ h ε pos → Nonexpansive.preserves f (h ε pos) }
  ; identity     = λ {A} → zero⇒positive A (ApproxSpace.≈[]-refl A)
  ; homomorphism = λ {_} {_} {Z} → zero⇒positive Z (ApproxSpace.≈[]-refl Z)
  ; F-resp-≈     = λ {_} {B} e {x} → zero⇒positive B (e x)
  }

forget : NaturalTransformation F₀ F₊
forget = record
  { η = λ X → record { to = λ x → x ; cong = zero⇒positive X }
  ; commute     = λ {_} {Y} _ → zero⇒positive Y (ApproxSpace.≈[]-refl Y)
  ; sym-commute = λ {_} {Y} _ → zero⇒positive Y (ApproxSpace.≈[]-refl Y)
  }
