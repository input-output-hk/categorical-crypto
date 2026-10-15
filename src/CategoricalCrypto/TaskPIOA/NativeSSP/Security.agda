{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.NativeSSP.Security where

open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Categories.Functor.Properties using (EssentiallySurjective)
open import Data.Product.Base

open import CategoricalCrypto.Abstract2.Morphism
import CategoricalCrypto.Standard2.Coverage as Structural
import CategoricalCrypto.TaskPIOA.Setup as S
import CategoricalCrypto.TaskPIOA.NativeSSP.Setup as N
open import CategoricalCrypto.TaskPIOA.NativeSSP.Morphism
open import CategoricalCrypto.UCSetup.Coverage

module Transport = Transfer bridge
module Coverage = Structural.Coverage S.Wiringᴹ N.Wiringᴹ S.ℰ-native N.ℰ-native compiler ν

test-coverage : TestCoverage bridge
test-coverage = epi⇒TestCoverage bridge ν-epi

object-coverage : EssentiallySurjective (StrongMonoidalFunctor.F compiler)
object-coverage W = W , record
  { from = N.Syntax.id ; to = N.Syntax.id
  ; iso = record { isoˡ = N.related-refl W ; isoʳ = N.related-refl W } }

ancilla-coverage : Coverage.AncillaCoverage
ancilla-coverage = Coverage.essentiallySurjective⇒AncillaCoverage object-coverage

preserves-≈ℰ : Transport.Preserves-≈ℰ
preserves-≈ℰ = covered-≈ℰ bridge test-coverage

preserves-≈ᵁ : Transport.Preserves-≈ᵁ
preserves-≈ᵁ = Coverage.covered-≈ᵁ test-coverage ancilla-coverage

preserves-≤UC : Transport.Preserves-≤UC
preserves-≤UC = Coverage.covered-≤UC test-coverage ancilla-coverage

simulator-square : ∀ {A B X Y} (s : S.Syntax.HomTerm Y X)
  (g : S.Syntax.HomTerm A (Y S.Syntax.⊗₀ B))
  → Transport.G (S.UC.sub s S.Syntax.∘ g)
    N.∼ (N.UC.sub (compileContext s) N.Syntax.∘ Transport.G g)
simulator-square = Coverage.sub-image
