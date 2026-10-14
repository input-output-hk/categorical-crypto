{-# OPTIONS --safe --without-K #-}

-- Split input-name embeddings enforce the compatibility condition of §2:
-- output owners and hidden actions are disjoint, shared inputs synchronize.
module CategoricalCrypto.TaskPIOA.Product where

open import Data.Empty
open import Data.List.Base hiding (find; product)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.TaskPIOA.Core
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Product

receive : ∀ {S} (M : Automaton S) → Maybe (Input S) → State M → Dist-ℚ (State M)
receive M nothing q = return-ℚ q
receive M (just i) q = input M i q

module _ {A B J} (w : Wiring A B J) (M : Automaton A) (N : Automaton B) where
  private
    S = productSignature A B J

  product-choose : State M × State N → Task S → Maybe (Local S)
  product-choose (q , r) (inj₁ t) = Maybe.map (leftAction {A} {B}) (choose M q t)
  product-choose (q , r) (inj₂ t) = Maybe.map (rightAction {A} {B}) (choose N r t)

  product-owns : ∀ qr t a → product-choose qr t ≡ just a → taskOf S a ≡ t
  product-owns (q , r) (inj₁ t) a eq with choose M q t in chosen
  ... | nothing = ⊥-elim (nothing≢just eq)
    where
    nothing≢just : ∀ {X : Set} {x : X} → nothing ≡ just x → ⊥
    nothing≢just ()
  ... | just b = trans (cong (taskOf S) (sym (just-injective eq)))
    (trans (left-class A B b) (cong inj₁ (owns M q t b chosen)))
  product-owns (q , r) (inj₂ t) a eq with choose N r t in chosen
  ... | nothing = ⊥-elim (nothing≢just eq)
    where
    nothing≢just : ∀ {X : Set} {x : X} → nothing ≡ just x → ⊥
    nothing≢just ()
  ... | just b = trans (cong (taskOf S) (sym (just-injective eq)))
    (trans (right-class A B b) (cong inj₂ (owns N r t b chosen)))

  product-kernel : Local S → State M × State N → Dist-ℚ (State M × State N)
  product-kernel (inj₁ (inj₁ o)) (q , r) = independent (kernel M (inj₁ o) q)
    (receive N (find (right w) (inj₂ o)) r)
  product-kernel (inj₁ (inj₂ o)) (q , r) = independent
    (receive M (find (left w) (inj₂ o)) q) (kernel N (inj₁ o) r)
  product-kernel (inj₂ (inj₁ h)) (q , r) = independent (kernel M (inj₂ h) q) (return-ℚ r)
  product-kernel (inj₂ (inj₂ h)) (q , r) = independent (return-ℚ q) (kernel N (inj₂ h) r)

  product : Automaton S
  product = record
    { states = states M ⊠ states N
    ; initial = initial M , initial N
    ; input = λ i (q , r) → independent (receive M (find (left w) (inj₁ i)) q)
                                      (receive N (find (right w) (inj₁ i)) r)
    ; choose = product-choose
    ; owns = product-owns
    ; kernel = product-kernel
    }

  synchronized-left : ∀ o i q r → find (right w) (inj₂ o) ≡ just i
    → kernel product (inj₁ (inj₁ o)) (q , r)
      ≡ independent (kernel M (inj₁ o) q) (input N i r)
  synchronized-left o i q r connected rewrite connected = refl

  synchronized-right : ∀ o i q r → find (left w) (inj₂ o) ≡ just i
    → kernel product (inj₁ (inj₂ o)) (q , r)
      ≡ independent (input M i q) (kernel N (inj₁ o) r)
  synchronized-right o i q r connected rewrite connected = refl

-- A joint word retains order, not merely its component projections.
leftSchedule : ∀ {A B : Set} → List (A ⊎ B) → List A
leftSchedule [] = []
leftSchedule (inj₁ a ∷ ρ) = a ∷ leftSchedule ρ
leftSchedule (inj₂ b ∷ ρ) = leftSchedule ρ

rightSchedule : ∀ {A B : Set} → List (A ⊎ B) → List B
rightSchedule [] = []
rightSchedule (inj₁ a ∷ ρ) = rightSchedule ρ
rightSchedule (inj₂ b ∷ ρ) = b ∷ rightSchedule ρ

record Environment (S : Signature) : Set where
  field signature : Signature
        automaton : Automaton signature
        wiring : Wiring S signature empty
open Environment public

observe : ∀ {S} (M : Automaton S) (E : Environment S)
  → Schedule (productSignature S (signature E) empty)
  → Dist-ℚ (List (Output S ⊎ Output (signature E)))
observe M E = traceDist (product (wiring E) M (automaton E))

-- The extra adversarial automaton is not the residual task scheduler.
record AdversarialContext (S : Signature) : Set where
  field adversarySignature : Signature
        adversary : Automaton adversarySignature
        boundary : Finite
        connectAdversary : Wiring S adversarySignature boundary
        environment : Environment (productSignature S adversarySignature boundary)

observe-adversarial : ∀ {S} (M : Automaton S) (C : AdversarialContext S)
  → Schedule (productSignature (productSignature S (AdversarialContext.adversarySignature C)
      (AdversarialContext.boundary C)) (signature (AdversarialContext.environment C)) empty)
  → Dist-ℚ (List ((Output S ⊎ Output (AdversarialContext.adversarySignature C))
      ⊎ Output (signature (AdversarialContext.environment C))))
observe-adversarial M C = observe
  (product (AdversarialContext.connectAdversary C) M (AdversarialContext.adversary C))
  (AdversarialContext.environment C)
