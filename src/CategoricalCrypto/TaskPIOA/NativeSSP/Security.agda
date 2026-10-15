{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.NativeSSP.Security where

open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Categories.Functor.Properties using (EssentiallySurjective)
open import Data.Product.Base
open import Function.Bundles using (_⇔_; mk⇔)

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

reflects-≈ℰ : Transport.Reflects-≈ℰ
reflects-≈ℰ = Transport.mono⇒reflects-≈ℰ (λ {A} {x} {y} → ν-mono {A} {x} {y})

reflects-≈ᵁ : ∀ {A B X} {f g : S.Syntax.HomTerm A (X S.Syntax.⊗₀ B)}
  → Transport.G f N.UC.≈ᵁ Transport.G g → f S.UC.≈ᵁ g
reflects-≈ᵁ = Coverage.reflects-≈ᵁ (λ {A} {x} {y} → ν-mono {A} {x} {y})

simulator-representation : ∀ {X Y} (s′ : N.Syntax.HomTerm Y X)
  → Coverage.SimulatorRepresentation s′ (sampleContext s′)
simulator-representation {X} s′ = record { action = λ {A} {B} g →
  N.UC.≈C⇒≈ᵁ {f = N.UC.sub s′ N.Syntax.∘ g}
    {g = N.UC.sub (compileContext (sampleContext s′)) N.Syntax.∘ g}
    (λ x → N.related-sym X (native-context-roundtrip s′ (proj₁ (N.Interpretation.⟦ g ⟧₁ x))) ,
      N.related-refl B (proj₂ (N.Interpretation.⟦ g ⟧₁ x))) }

reflects-≤UC-witness : ∀ {A B X Y}
  {f : S.Syntax.HomTerm A (X S.Syntax.⊗₀ B)}
  {g : S.Syntax.HomTerm A (Y S.Syntax.⊗₀ B)}
  (s′ : N.Syntax.HomTerm Y X)
  → Transport.G f N.UC.≈ᵁ (N.UC.sub s′ N.Syntax.∘ Transport.G g)
  → f S.UC.≤UC g
reflects-≤UC-witness s′ witness = Coverage.reflects-≤UC-witness
  (λ {A} {x} {y} → ν-mono {A} {x} {y})
  s′ witness (sampleContext s′) (simulator-representation s′)

reflects-≤UC : Transport.Reflects-≤UC
reflects-≤UC le = let s′ , witness = N.UC.≤UC⇒dummy le
  in reflects-≤UC-witness s′ witness

≈ᵁ-iff : ∀ {A B X} {f g : S.Syntax.HomTerm A (X S.Syntax.⊗₀ B)}
  → (f S.UC.≈ᵁ g) ⇔ (Transport.G f N.UC.≈ᵁ Transport.G g)
≈ᵁ-iff = mk⇔ preserves-≈ᵁ reflects-≈ᵁ

≤UC-iff : ∀ {A B X Y}
  {f : S.Syntax.HomTerm A (X S.Syntax.⊗₀ B)}
  {g : S.Syntax.HomTerm A (Y S.Syntax.⊗₀ B)}
  → (f S.UC.≤UC g) ⇔ (Transport.G f N.UC.≤UC Transport.G g)
≤UC-iff = mk⇔ preserves-≤UC reflects-≤UC
