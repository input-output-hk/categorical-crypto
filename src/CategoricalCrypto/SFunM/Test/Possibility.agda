{-# OPTIONS --safe --without-K #-}

-- The generic machine layer at the possibility monad `𝒫` on `Setoids`: the
-- endofunctor, monad and graded monad it gives, a graded monad morphism out of
-- `Maybe`, and possibilistic functionalities (`SFunᵉ` morphisms at `𝒫`, with
-- nondeterminism standing for the adversary's choices; not UC functionalities).

open import categorical-crypto.Prelude hiding (Functor; _>>=_; return)

open import Categories.Category.Core
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
import Categories.Monad as C
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Construction.Kleisli.Ext
open import Categories.Monad.Graded
open import Categories.Monad.Graded.Trivial
open import Categories.Monad.Graded.Uncurried
open import Categories.Monad.Relative
open import Categories.Monad.Discrete
import Categories.Monad.Setoids.Discrete.Morphism as DiscreteMorphism
open import Categories.Monad.Setoids.Maybe

open import Data.List.Base
open import Data.List.Properties
open import Data.List.Relation.Binary.BagAndSetEquality
open import Data.List.Relation.Binary.BagAndSetEquality.Ext
open import Data.List.Relation.Unary.Any
import Data.Maybe.Relation.Binary.Pointwise as Pw

open import Function.Bundles
open import Relation.Binary.Bundles

import CategoricalCrypto.SFunM as SFun
import CategoricalCrypto.SFunM.Monoidal as SFunMonoidal
import CategoricalCrypto.SFunM.Morphism as SFunMorphism
import CategoricalCrypto.SFunM.Properties as SFunProperties
open import ProbabilisticLogic.Distribution.Possibility.Setoids

module CategoricalCrypto.SFunM.Test.Possibility where

𝒫ᵏ : KleisliTriple (Setoids 0ℓ 0ℓ)
𝒫ᵏ = 𝒫-KleisliTriple

Maybeᵏ : KleisliTriple (Setoids 0ℓ 0ℓ)
Maybeᵏ = Maybe-KleisliTriple

𝒫ᴰ Maybeᴰ : DiscreteMonad 0ℓ
𝒫ᴰ     = 𝒫-DiscreteMonad
Maybeᴰ = Maybe-DiscreteMonad

open DiscreteMonad 𝒫ᴰ
open SFun 𝒫ᴰ
open SFunMonoidal 𝒫ᴰ
open SFunProperties 𝒫ᴰ

_ : Category _ _ _
_ = SFunᵉ-Category

_ : Monoidal SFunᵉ-Category
_ = SFunᵉ-Monoidal

_ : Symmetric SFunᵉ-Monoidal
_ = SFunᵉ-Symmetric

_ : MonoidalCategory _ _ _
_ = SFunᵉ-MonoidalCategory

_ : eval (statelessᵉ not) (true ∷ false ∷ []) ≡ (false ∷ true ∷ []) ∷ []
_ = refl

_ : eval (statelessᵉ not ⊗ᵉ statelessᵉ id)
         (inj₁ true ∷ inj₂ true ∷ inj₁ false ∷ [])
  ≡ (inj₁ false ∷ inj₂ true ∷ inj₁ true ∷ []) ∷ []
_ = refl

------------------------------------------------------------------------
-- Abstracting a partial machine to a possibilistic one

fromMaybeᵏ : KleisliTriple⇒ (Setoids 0ℓ 0ℓ) Maybeᵏ 𝒫ᵏ
fromMaybeᵏ = record
  { θ        = λ {S} → record
      { to   = fromMaybe
      ; cong = λ where
          (Pw.just a≈b) → return-cong𝒫 {S = S} a≈b
          Pw.nothing    → Setoid.refl (𝒫ˢ S)
      }
  ; θ-unit   = λ {S} → Setoid.refl (𝒫ˢ S)
  ; θ-extend = λ {_} {S′} f → λ where
      {nothing} → Setoid.refl (𝒫ˢ S′)
      {just a}  → Setoid.reflexive (𝒫ˢ S′) (sym (++-identityʳ (fromMaybe (f ⟨$⟩ a))))
  }

private
  module Mb  = SFun Maybeᴰ
  module MbM = SFunMonoidal Maybeᴰ
  module Θ   = DiscreteMorphism Maybeᵏ 𝒫ᵏ fromMaybeᵏ

open SFunMorphism Maybeᴰ 𝒫ᴰ Θ.θ Θ.θ-cong Θ.θ-return Θ.θ-bind

_ : Functor Mb.SFunᵉ-Category SFunᵉ-Category
_ = SFunᵉ-map

_ : StrongMonoidalFunctor MbM.SFunᵉ-MonoidalCategory SFunᵉ-MonoidalCategory
_ = SFunᵉ-map-monoidal

------------------------------------------------------------------------
-- The `Setoids` payoffs

_ : Endofunctor (Setoids 0ℓ 0ℓ)
_ = RMonad⇒Functor 𝒫ᵏ

_ : C.Monad (Setoids 0ℓ 0ℓ)
_ = Kleisli⇒Monad (Setoids 0ℓ 0ℓ) 𝒫ᵏ

_ : GradedKleisliTriple (Oneᴹ {0ℓ} {0ℓ} {0ℓ}) (Setoids 0ℓ 0ℓ)
_ = ungraded 𝒫ᵏ

_ : GradedMonad (Oneᴹ {0ℓ} {0ℓ} {0ℓ}) (Setoids 0ℓ 0ℓ)
_ = GradedKleisliTriple⇒GradedMonad (ungraded 𝒫ᵏ)

fromMaybeᵍ : GradedMonadMorphism _ _ idF (idF-Monoidal (Oneᴹ {0ℓ} {0ℓ} {0ℓ}))
fromMaybeᵍ = toMonadMorphism (ungraded Maybeᵏ) (ungraded 𝒫ᵏ) idF (idF-Monoidal Oneᴹ)
                             (ungraded-morphism Maybeᵏ 𝒫ᵏ fromMaybeᵏ)

------------------------------------------------------------------------
-- Possibilistic functionalities

private variable Msg : Type

-- A link carries at most one message per round; `nothing` is an idle round.
lossy : Maybe Msg → List (Maybe Msg)
lossy m = m ∷ nothing ∷ []

Lossy : SFunᵉ (Maybe Msg) (Maybe Msg)
Lossy = kleisliᵉ lossy

_ : eval Lossy (just 1 ∷ []) ≡ (just 1 ∷ []) ∷ (nothing ∷ []) ∷ []
_ = refl

Lossy-idempotent : (Lossy {Msg} ∘ᵉ Lossy) ≈ᵉ Lossy
Lossy-idempotent = ≈ᵉ.trans (≈ᵉ.sym (kleisliᵉ-∘ lossy lossy)) (kleisliᵉ-cong step)
  where
  step : (m : Maybe Msg) → (lossy m >>= lossy) ≈ᴹ lossy m
  step m = ∷-cong refl (𝒫.trans (∷-absorb (here refl)) (∷-absorb (here refl)))

Cut : SFunᵉ (Maybe Msg) (Maybe Msg)
Cut = mkᵉ nothing λ where
  (nothing    , m) → (just true , m) ∷ (just false , nothing) ∷ []
  (just true  , m) → return (just true , m)
  (just false , _) → return (just false , nothing)

_ : eval Cut (just 1 ∷ just 2 ∷ [])
  ≡ (just 1 ∷ just 2 ∷ []) ∷ (nothing ∷ nothing ∷ []) ∷ []
_ = refl

Network : SFunᵉ (Maybe Msg ⊎ Maybe Msg) (Maybe Msg ⊎ Maybe Msg)
Network = Lossy ⊗ᵉ Cut

Buffer : SFunᵉ (Msg ⊎ ⊤) (⊤ ⊎ Maybe Msg)
Buffer = mkᵉ [] [ (λ (q , m) → return (q ∷ʳ m , tt)) ∣ (λ where
    ([]    , _) → return ([] , nothing)
    (m ∷ q , _) → (q , just m) ∷ (m ∷ q , nothing) ∷ []) ]ᵏ

_ : eval Buffer (inj₁ 1 ∷ inj₂ tt ∷ [])
  ≡ (inj₁ tt ∷ inj₂ (just 1) ∷ []) ∷ (inj₁ tt ∷ inj₂ nothing ∷ []) ∷ []
_ = refl

CRS : SFunᵉ ⊤ Bool
CRS = mkᵉ nothing λ where
  (just b  , _) → return (just b , b)
  (nothing , _) → do
    b ← true ∷ false ∷ []
    return (just b , b)

_ : eval CRS (tt ∷ tt ∷ []) ≡ (true ∷ true ∷ []) ∷ (false ∷ false ∷ []) ∷ []
_ = refl
