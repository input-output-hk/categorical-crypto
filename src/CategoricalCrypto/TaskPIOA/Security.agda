{-# OPTIONS --safe --without-K #-}

-- Native finite contextual trace inclusion and the separate, stronger
-- task-preserving resource slice of the wiring UCSetup.
module CategoricalCrypto.TaskPIOA.Security where

open import Data.Product.Base
open import Data.Unit.Base using (⊤; tt)
import Data.Unit.Polymorphic as Unit
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Product
open import CategoricalCrypto.TaskPIOA.Setup
open import CategoricalCrypto.TaskPIOA.Simulation
open import ProbabilisticLogic.Distribution.RationalDist

open Syntax using (ObjTerm; unit; Var; _⊗₀_; HomTerm)
open Interpretation using (⟦_⟧₁)

-- Comparability fixes only public ports, not private states, hidden actions,
-- or task partitions. Ideal schedules can consequently have different types.
data Comparable : Signature → Signature → Set where
  same-ports : ∀ {I O H K T U f g p q}
    → Comparable (sig I O H T f p) (sig I O K U g q)

sameEnvironment : ∀ {A B} → Comparable A B → Environment A → Environment B
sameEnvironment same-ports E = record
  { signature = signature E ; automaton = automaton E
  ; wiring = record { left = left (wiring E) ; right = right (wiring E)
                    ; boundary-live = boundary-live (wiring E) } }

Contextual : ∀ {A B} → Comparable A B → Automaton A → Automaton B → Set
Contextual same-ports M N = ∀ E ρ → ∃ λ ρ′ → observe M E ρ ≈Mℚ observe N (sameEnvironment same-ports E) ρ′

_≤₀_ : ∀ {S} → Automaton S → Automaton S → Set
M ≤₀ N = Contextual same-ports M N

uniform⇒contextual : ∀ {S} {M N : Automaton S} → Simulation M N → M ≤₀ N
uniform⇒contextual s E ρ = ρ , trace-match
  (product-simulation (wiring E) s (identity-simulation (automaton E))) ρ

Related : (A : ObjTerm) → Values.⟦ A ⟧₀ → Values.⟦ A ⟧₀ → Set
Related unit _ _ = ⊤
Related (Var S) M N = Simulation M N
Related (A ⊗₀ B) (a , b) (a′ , b′) = Related A a a′ × Related B b b′

related-refl : ∀ A x → Related A x x
related-refl unit _ = tt
related-refl (Var S) M = identity-simulation M
related-refl (A ⊗₀ B) (a , b) = related-refl A a , related-refl B b

wiring-preserves : ∀ {A B} (f : HomTerm A B) {x y}
  → Related A x y → Related B (⟦ f ⟧₁ x) (⟦ f ⟧₁ y)
wiring-preserves (Syntax.var (install M)) r = identity-simulation M
wiring-preserves (Syntax.var (connect w)) (s , r) = product-simulation w s r
wiring-preserves Syntax.id r = r
wiring-preserves (f Syntax.∘ g) r = wiring-preserves f (wiring-preserves g r)
wiring-preserves (f Syntax.⊗₁ g) (r , s) = wiring-preserves f r , wiring-preserves g s
wiring-preserves Syntax.λ⇒ (r , s) = s
wiring-preserves Syntax.λ⇐ r = tt , r
wiring-preserves Syntax.ρ⇒ (r , s) = r
wiring-preserves Syntax.ρ⇐ r = r , tt
wiring-preserves Syntax.α⇒ ((r , s) , t) = r , s , t
wiring-preserves Syntax.α⇐ (r , s , t) = (r , s) , t
wiring-preserves (Syntax.σ ⦃ () ⦄)

test-preserves : ∀ {A} (t : Test A) {x y} → Related A x y → evaluate t x ≡ evaluate t y
test-preserves t r = trace-match (wiring-preserves (context t) r) (schedule t) (reward t)

Uniform : ∀ {A B} → HomTerm A B → HomTerm A B → Set
Uniform {B = B} f g = ∀ x → Related B (⟦ f ⟧₁ x) (⟦ g ⟧₁ x)

uniform⇒≈ᵁ : ∀ {A B X} {f g : HomTerm A (X ⊗₀ B)} → Uniform f g → f UC.≈ᵁ g
uniform⇒≈ᵁ {X = X} p W = UC.KE.mk∼ λ {t} (w , x) → test-preserves t
  (wiring-preserves (UC.μ W X) (related-refl W w , p x))

simulation⇒≤UC : ∀ {S} {M N : Automaton S} → Simulation M N → resource M UC.≤UC resource N
simulation⇒≤UC s = UC.≈ᵁ⇒≤UC (uniform⇒≈ᵁ (λ _ → tt , s))

-- The unit leakage slice has no simulator-visible port. Applying the native
-- closing test to ≤UC's dummy simulator erases its unit component. The same
-- precommitted word then witnesses inclusion; there is no ∀E/∃s exchange.
resource-≤UC⇒contextual : ∀ {S} {M N : Automaton S}
  → resource M UC.≤UC resource N → M ≤₀ N
resource-≤UC⇒contextual le E ρ = ρ , λ P →
  UC.KE.run∼ (UC.≈ᵁ⇒≈ℰ (proj₂ (UC.≤UC⇒dummy le)))
    {pull Syntax.λ⇒ (nativeTest E ρ P)} Unit.tt
