{-# OPTIONS --safe --without-K --guardedness #-}

-- The extra premise is explicit: stable equality alone is not decidability.
-- A four-point fair coin extracts weak excluded middle from support congruence
-- when functions on empty domains can be identified extensionally.
module ProbabilisticLogic.Dp.Positive.Decidability where

open import Axiom.Extensionality.Propositional
open import Data.Bool.Base
open import Data.Bool.Properties using (not-¬)
open import Data.Empty
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Sum.Properties using (inj₁-injective)
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (Dec; yes; no; decidable-stable; ¬¬-excluded-middle)
open import Relation.Nullary.Negation

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Examples using (half-positive)
open import ProbabilisticLogic.Dp.Positive.Monad
open import ProbabilisticLogic.Dp.Positive.Paths

private variable
  X : Set
  d e : Dₚ X
  x : X

fair : X → X → Dₚ X
wt (fair x y) _ = ½
wt-nn (fair x y) _ = <⇒≤ half-positive
wt-1 (fair x y) = refl
br (fair x y) true = inj₁ x
br (fair x y) false = inj₁ y

fair-left : (x y : X) → Positive (fair x y) x
fair-left x y = hit true half-positive refl

fair-support : {x y z : X} → Positive (fair x y) z → (x ≡ z) ⊎ (y ≡ z)
fair-support (hit true _ eq) = inj₁ (inj₁-injective eq)
fair-support (hit false _ eq) = inj₂ (inj₁-injective eq)
fair-support (delay true _ _ () _)
fair-support (delay false _ _ () _)

module FourPoints (ext : Extensionality 0ℓ 0ℓ) (P : Set) where
  Carrier : Set
  Carrier = (P → Bool) × (¬ P → Bool)

  a b c δ : Carrier
  a = (λ _ → false) , (λ _ → false)
  b = (λ _ → true) , (λ _ → true)
  c = (λ _ → false) , (λ _ → true)
  δ = (λ _ → true) , (λ _ → false)

  private
    agree : (Q : Carrier → ℚ) → Dec P
      → ½ ℚ.* Q a ℚ.+ ½ ℚ.* Q b ≡ ½ ℚ.* Q c ℚ.+ ½ ℚ.* Q δ
    agree Q (yes p) = cong₂ ℚ._+_
      (cong (λ z → ½ ℚ.* Q z) (cong ((λ _ → false) ,_) (ext (λ np → ⊥-elim (np p)))))
      (cong (λ z → ½ ℚ.* Q z) (cong ((λ _ → true) ,_) (ext (λ np → ⊥-elim (np p)))))
    agree Q (no np) = trans (cong₂ ℚ._+_
      (cong (λ z → ½ ℚ.* Q z) (cong (_, (λ _ → false)) (ext (λ p → ⊥-elim (np p)))))
      (cong (λ z → ½ ℚ.* Q z) (cong (_, (λ _ → true)) (ext (λ p → ⊥-elim (np p))))))
      (+-comm (½ ℚ.* Q δ) (½ ℚ.* Q c))

  same-observations : fair a b ≈ₚ fair c δ
  same-observations = exact⇒≈ₚ _ _ λ where
    Q zero → refl
    Q (suc n) → decidable-stable (_ ≟ _)
      (¬¬-map (agree Q) ¬¬-excluded-middle)

  support⇒weak-excluded-middle : Positive (fair c δ) a → (¬ ¬ P) ⊎ (¬ P)
  support⇒weak-excluded-middle path with fair-support path
  ... | inj₁ eq = inj₁ (λ np → not-¬ refl (cong (λ z → proj₂ z np) eq))
  ... | inj₂ eq = inj₂ (λ p → not-¬ refl (cong (λ z → proj₁ z p) eq))

literal-support⇒weak-excluded-middle : Extensionality 0ℓ 0ℓ → LiteralSupportCongruence 0ℓ
  → (P : Set) → (¬ ¬ P) ⊎ (¬ P)
literal-support⇒weak-excluded-middle ext support P =
  FourPoints.support⇒weak-excluded-middle ext P
    (support (FourPoints.same-observations ext P) (fair-left _ _))

literal-support⇒decidable-equality : Extensionality 0ℓ 0ℓ → LiteralSupportCongruence 0ℓ
  → {X : Set} → DecidableEquality X
literal-support⇒decidable-equality ext support x y
  with literal-support⇒weak-excluded-middle ext support (x ≡ y)
... | inj₁ nn = yes (literal-support-congruence⇒stable-equality support nn)
... | inj₂ neq = no neq

module _ (dec : DecidableEquality X) (x : X) where
  private
    indicator : X → ℚ
    indicator y with dec y x
    ... | yes _ = 1ℚ
    ... | no _ = 0ℚ

    indicator-nn : NNF indicator
    indicator-nn y with dec y x
    ... | yes _ = 0≤1ℚ
    ... | no _ = ≤-refl

    indicator-self : 0ℚ ℚ.< indicator x
    indicator-self with dec x x
    ... | yes _ = 0<1ℚ
    ... | no neq = ⊥-elim (neq refl)

    indicator-reflect : ∀ y → 0ℚ ℚ.< indicator y → y ≡ x
    indicator-reflect y pos with dec y x
    ... | yes eq = eq
    ... | no _ = ⊥-elim (<-irrefl refl pos)

  decidable-positive-support : d ≈₊ e → Positive d x → Positive e x
  decidable-positive-support {e = e} eq path =
    let n , pos = proj₁ eq indicator indicator-nn
          (positive-witness indicator indicator-nn path indicator-self)
        y , py , iy = positive-extract n e indicator indicator-nn pos
    in subst (Positive e) (indicator-reflect y iy) py

  decidable-literal-support : d ≈ₚ e → Positive d x → Positive e x
  decidable-literal-support eq = decidable-positive-support (≈ₚ⇒≈₊ eq)

decidable-equality⇒literal-support : (∀ {X : Set} → DecidableEquality X) → LiteralSupportCongruence 0ℓ
decidable-equality⇒literal-support dec {x = x} = decidable-literal-support dec x
