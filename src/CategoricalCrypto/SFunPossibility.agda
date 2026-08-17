{-# OPTIONS --safe --without-K #-}

-- The possibilistic abstraction of the machine world, at the level of the
-- CATEGORY of stateful functions: `supp⊥` post-composed with every step
-- kernel.  Objects, states and control flow are untouched; only the
-- probabilities are forgotten, and a certainly-diverging step becomes the
-- empty set of possible outcomes.
--
-- Since the abstraction touches neither the state space nor the interfaces, it
-- preserves the tensor of `SFunM.Monoidal` on the nose: `SFun-supp` is a
-- strong (indeed strict) monoidal functor, which is what
-- `Standard2.Morphism.StdUCMorphism` asks for.  Two things still stand between
-- that and a `UCSetupMorphism` out of the machine world, neither of them about
-- the tensor: `StdUCMorphism`'s own body does not elaborate at a *concrete*
-- machine category (see `docs/sfun-monoidal-report.md` §6), and the ℰ-leg is
-- caller data that cannot be supplied in general — the abstraction does NOT
-- preserve indistinguishability (`RationalDist.Support`'s `pad-not-perfect` and
-- `close-supp-differs` are the counterexamples).

module CategoricalCrypto.SFunPossibility where

open import categorical-crypto.Prelude hiding (Functor)

open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)

open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunM.Monoidal
open import CategoricalCrypto.SFunM.Morphism
open import CategoricalCrypto.SFunPartial
open import ProbabilisticLogic.Distribution.Possibility
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Support

private variable A B : Type

-- `_≈Mℚ_` mentions only `entries`, so `supp⊥-cong`'s two distributions are not
-- recoverable from the equality proof: they have to be handed to it by name
-- (cf. the pinning convention of `RationalDist.Setoid`).
private
  supp⊥-cong′ : ∀ {ℓ} {X : Type ℓ} {μ ν : Dist⊥ X} → μ ≈Mℚ ν → supp⊥ μ ≈𝒫 supp⊥ ν
  supp⊥-cong′ {μ = μ} {ν} = supp⊥-cong {μ = μ} {ν}

suppᵉ : SFun⊥ A B → SFunᵉ {M = List} A B
suppᵉ = mapᵉ supp⊥ (λ {_ _ x y} → supp⊥-cong′ {μ = x} {y}) supp⊥-return supp⊥-bind

SFun-supp : Functor SFun⊥-Category (SFunᵉ-Category {M = List})
SFun-supp = SFunᵉ-map supp⊥ (λ {_ _ x y} → supp⊥-cong′ {μ = x} {y})
                      supp⊥-return supp⊥-bind

-- Spelling out both machine categories rather than reusing
-- `SFun⊥-MonoidalCategory` keeps Agda from comparing two `Monoidal` record
-- types field by field; see the note in `SFunPartial`.
SFun-supp-monoidal : StrongMonoidalFunctor (SFunᵉ-MonoidalCategory {M = Dist⊥})
                                           (SFunᵉ-MonoidalCategory {M = List})
SFun-supp-monoidal = SFunᵉ-map-monoidal supp⊥ (λ {_ _ x y} → supp⊥-cong′ {μ = x} {y})
                                        supp⊥-return supp⊥-bind
