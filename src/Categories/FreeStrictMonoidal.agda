{-# OPTIONS --safe --without-K #-}

module Categories.FreeStrictMonoidal where

--------------------------------------------------------------------------------
-- The free strict monoidal category on a family of wire-list generators.
--
-- Objects are `List X` and the tensor is `++`.
--
-- NOTE on strictness / no `Monoidal` instance: `++` is only a monoid UP TO
-- propositional equality (`++-assoc` / `++-identityʳ` are not definitional), so
-- a full `Monoidal` instance would need the associator/unitors to be
-- `subst`-transported identities rather than `id`, with the attendant
-- pentagon/triangle bookkeeping — which does not fall out cleanly.  We therefore
-- expose only the `Category`; the strict tensor is available directly as the
-- morphism-former `_⊗ʷ_`.
--------------------------------------------------------------------------------

open import Level
open import Data.List

open import Categories.Category
open import Categories.Category.Helper

module FreeStrictMonoidalHelper {X : Set} (Gen : List X → List X → Set) where
  infixr 9 _∘ʷ_
  infixr 10 _⊗ʷ_
  infix  4 _≈ʷ_

  private variable n m k nl ml nr mr : List X

  data WTerm : List X → List X → Set where
    boxʷ : Gen n m → WTerm n m
    idʷ  : WTerm n n
    _∘ʷ_ : WTerm m k → WTerm n m → WTerm n k
    _⊗ʷ_ : WTerm nl ml → WTerm nr mr → WTerm (nl ++ nr) (ml ++ mr)

  private variable f g h i : WTerm n m

  data _≈ʷ_ : WTerm n m → WTerm n m → Set where
    idˡ      : idʷ ∘ʷ f ≈ʷ f
    idʳ      : f ∘ʷ idʷ ≈ʷ f
    assoc    : (h ∘ʷ g) ∘ʷ f ≈ʷ h ∘ʷ (g ∘ʷ f)
    ∘-resp-≈ : f ≈ʷ h → g ≈ʷ i → f ∘ʷ g ≈ʷ h ∘ʷ i
    reflʷ    : f ≈ʷ f
    symʷ     : f ≈ʷ g → g ≈ʷ f
    transʷ   : f ≈ʷ g → g ≈ʷ h → f ≈ʷ h

  Strict : Category 0ℓ 0ℓ 0ℓ
  Strict = categoryHelper record
    { Obj       = List X
    ; _⇒_       = WTerm
    ; _≈_       = _≈ʷ_
    ; id        = idʷ
    ; _∘_       = _∘ʷ_
    ; assoc     = assoc
    ; identityˡ = idˡ
    ; identityʳ = idʳ
    ; equiv     = record { refl = reflʷ ; sym = symʷ ; trans = transʷ }
    ; ∘-resp-≈  = ∘-resp-≈
    }
