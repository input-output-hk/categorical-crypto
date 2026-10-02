{-# OPTIONS --safe --without-K #-}

-- The category `Approx` of approximate spaces and nonexpansive maps.
--
-- Hom equality is pointwise agreement AT ZERO ERROR, and that is the whole
-- point of the packaging: `resp₀` says a fixed bound survives a zero-error
-- change of either endpoint, so no separate fine equality has to be carried
-- alongside the coarse one, and a functor into `Approx` transports every
-- quantitative bound exactly.

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor

open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Structures

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Space {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E

private variable c ℓa : Level

record ApproxSpace (c ℓa : Level) : Set (suc (c ⊔ ℓa) ⊔ es ⊔ ℓe) where
  field
    Carrier : Set c
    approx  : Approximation Carrier E ℓa

  -- `Approximation` re-exports its error algebra, which the module parameter
  -- already fixes; taking only the relation keeps the two spellings apart.
  open Approximation approx public using (_≈[_]_; ≈[]-refl; ≈[]-sym; ≈[]-trans; ≈[]-mono)

  ≈[]-trans₀ : {x y z : Carrier} → x ≈[ ε₀ ] y → y ≈[ ε₀ ] z → x ≈[ ε₀ ] z
  ≈[]-trans₀ h k = ≈[]-mono ⊕-identityˡ (≈[]-trans h k)

private variable X Y Z : ApproxSpace c ℓa

module _ (X : ApproxSpace c ℓa) where
  open ApproxSpace X

  resp₀ : {x x′ y y′ : Carrier} {ε : Error}
        → x′ ≈[ ε₀ ] x → y ≈[ ε₀ ] y′ → x ≈[ ε ] y → x′ ≈[ ε ] y′
  resp₀ = ≈[]-resp₀ E approx

  zeroSetoid : Setoid c ℓa
  zeroSetoid = record
    { Carrier = Carrier
    ; _≈_ = λ x y → x ≈[ ε₀ ] y
    ; isEquivalence = record { refl = ≈[]-refl ; sym = ≈[]-sym ; trans = ≈[]-trans₀ }
    }

record Nonexpansive (X Y : ApproxSpace c ℓa) : Set (c ⊔ es ⊔ ℓa) where
  private
    module X = ApproxSpace X
    module Y = ApproxSpace Y

  field
    map       : X.Carrier → Y.Carrier
    preserves : {x y : X.Carrier} {ε : Error} → x X.≈[ ε ] y → map x Y.≈[ ε ] map y

module _ {X Y : ApproxSpace c ℓa} where
  private module Y = ApproxSpace Y

  infix 4 _≈map_

  _≈map_ : Nonexpansive X Y → Nonexpansive X Y → Set (c ⊔ ℓa)
  f ≈map g = (x : ApproxSpace.Carrier X)
           → Nonexpansive.map f x Y.≈[ ε₀ ] Nonexpansive.map g x

  ≈map-isEquivalence : IsEquivalence _≈map_
  ≈map-isEquivalence = record
    { refl  = λ _ → Y.≈[]-refl
    ; sym   = λ h x → Y.≈[]-sym (h x)
    ; trans = λ h k x → Y.≈[]-trans₀ (h x) (k x)
    }

identity : Nonexpansive X X
identity = record { map = λ x → x ; preserves = λ h → h }

compose : Nonexpansive Y Z → Nonexpansive X Y → Nonexpansive X Z
compose g f = record
  { map = λ x → map g (map f x) ; preserves = λ h → preserves g (preserves f h) }
  where open Nonexpansive

-- `Carrier` is a projection, so a space is not recoverable from a hom type by
-- unification: here and in every law of `Approx` below it has to be named.
compose-resp : {X Y Z : ApproxSpace c ℓa} {g g′ : Nonexpansive Y Z} {f f′ : Nonexpansive X Y}
             → g ≈map g′ → f ≈map f′ → compose g f ≈map compose g′ f′
compose-resp {Z = Z} {g = g} {f′ = f′} eg ef x =
  Z.≈[]-trans₀ (Nonexpansive.preserves g (ef x)) (eg (Nonexpansive.map f′ x))
  where module Z = ApproxSpace Z

Approx : (c ℓa : Level) → Category (suc (c ⊔ ℓa) ⊔ es ⊔ ℓe) (c ⊔ es ⊔ ℓa) (c ⊔ ℓa)
Approx c ℓa = record
  { Obj       = ApproxSpace c ℓa
  ; _⇒_       = Nonexpansive
  ; _≈_       = _≈map_
  ; id        = identity
  ; _∘_       = compose
  ; assoc     = λ {_} {_} {_} {D} _ → ApproxSpace.≈[]-refl D
  ; sym-assoc = λ {_} {_} {_} {D} _ → ApproxSpace.≈[]-refl D
  ; identityˡ = λ {_} {B} _ → ApproxSpace.≈[]-refl B
  ; identityʳ = λ {_} {B} _ → ApproxSpace.≈[]-refl B
  ; identity² = λ {A} _ → ApproxSpace.≈[]-refl A
  ; equiv     = ≈map-isEquivalence
  -- `compose` reduces to a record of lambdas, so its arguments are not
  -- recoverable either; the outer pair is `f h`, the inner pair `g i`.
  ; ∘-resp-≈  = λ {A} {B} {C} {f} {h} {g} {i} →
      compose-resp {X = A} {Y = B} {Z = C} {g = f} {g′ = h} {f = g} {f′ = i}
  }

F₀ : (c ℓa : Level) → Functor (Approx c ℓa) (Setoids c ℓa)
F₀ c ℓa = record
  { F₀ = zeroSetoid
  ; F₁ = λ f → record { to = Nonexpansive.map f ; cong = Nonexpansive.preserves f }
  ; identity     = λ {A} → ApproxSpace.≈[]-refl A
  ; homomorphism = λ {_} {_} {Z} → ApproxSpace.≈[]-refl Z
  ; F-resp-≈     = λ e {x} → e x
  }
