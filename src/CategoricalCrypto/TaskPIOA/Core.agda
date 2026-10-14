{-# OPTIONS --safe --without-K #-}

-- Finite, rational, action-deterministic fragment of Canetti et al. (2006),
-- §2, Definition 1. A schedule is data, never a function of the execution.
module CategoricalCrypto.TaskPIOA.Core where

open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base using (Fin)
open import Data.List.Base hiding (find)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist

infixr 6 _⊕_
infixr 7 _⊠_
data Finite : Set where
  empty one bit : Finite
  fin : ℕ → Finite
  _⊕_ _⊠_ : Finite → Finite → Finite

⟨_⟩ : Finite → Set
⟨ empty ⟩ = ⊥
⟨ one ⟩ = ⊤
⟨ bit ⟩ = Bool
⟨ fin n ⟩ = Fin n
⟨ A ⊕ B ⟩ = ⟨ A ⟩ ⊎ ⟨ B ⟩
⟨ A ⊠ B ⟩ = ⟨ A ⟩ × ⟨ B ⟩

record Signature : Set where
  constructor sig
  field inputs outputs hidden tasks : Finite
        taskOf : ⟨ outputs ⟩ ⊎ ⟨ hidden ⟩ → ⟨ tasks ⟩
        task-inhabited : (t : ⟨ tasks ⟩) → ∃ λ a → taskOf a ≡ t
open Signature public

Local Input Output Task : Signature → Set
Local S = ⟨ outputs S ⟩ ⊎ ⟨ hidden S ⟩
Input S = ⟨ inputs S ⟩
Output S = ⟨ outputs S ⟩
Task S = ⟨ tasks S ⟩

record Automaton (S : Signature) : Set where
  field states : Finite
        initial : ⟨ states ⟩
        input : Input S → ⟨ states ⟩ → Dist-ℚ ⟨ states ⟩
        choose : ⟨ states ⟩ → Task S → Maybe (Local S)
        owns : ∀ q t a → choose q t ≡ just a → taskOf S a ≡ t
        kernel : Local S → ⟨ states ⟩ → Dist-ℚ ⟨ states ⟩
open Automaton public

State : ∀ {S} → Automaton S → Set
State M = ⟨ states M ⟩

Enabled : ∀ {S} (M : Automaton S) → State M → Task S → Local S → Set
Enabled M q t a = choose M q t ≡ just a

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

action-determinism : ∀ {S} (M : Automaton S) q t a b
  → Enabled M q t a → Enabled M q t b → a ≡ b
action-determinism M q t a b p r = just-injective (trans (sym p) r)

Transition : ∀ {S} (M : Automaton S) → State M → Input S ⊎ Local S → Dist-ℚ (State M) → Set
Transition M q (inj₁ i) μ = μ ≈Mℚ input M i q
Transition M q (inj₂ a) μ = (∃ λ t → Enabled M q t a) × (μ ≈Mℚ kernel M a q)

input-enabled : ∀ {S} (M : Automaton S) q i → Transition M q (inj₁ i) (input M i q)
input-enabled M q i P = refl

transition-determinism : ∀ {S} (M : Automaton S) q a μ ν
  → Transition M q a μ → Transition M q a ν → μ ≈Mℚ ν
transition-determinism M q (inj₁ i) μ ν p r P = trans (p P) (sym (r P))
transition-determinism M q (inj₂ a) μ ν p r P = trans (proj₂ p P) (sym (proj₂ r P))

Schedule : Signature → Set
Schedule S = List (Task S)

emit : ∀ {S} → Local S → Maybe (Output S)
emit (inj₁ o) = just o
emit (inj₂ h) = nothing

prepend : ∀ {A : Set} → Maybe A → List A → List A
prepend nothing xs = xs
prepend (just a) xs = a ∷ xs

step : ∀ {S} (M : Automaton S) → State M → Maybe (Local S) → Dist-ℚ (Maybe (Output S) × State M)
step M q nothing = return-ℚ (nothing , q)
step {S} M q (just a) = Dmap (emit {S} a ,_) (kernel M a q)

tick : ∀ {S} (M : Automaton S) → Task S → State M → Dist-ℚ (Maybe (Output S) × State M)
tick M t q = step M q (choose M q t)

runFrom : ∀ {S} (M : Automaton S) → Schedule S → State M → Dist-ℚ (List (Output S))
runFrom M [] q = return-ℚ []
runFrom M (t ∷ ρ) q = tick M t q >>=ᴹ λ (o , q′) → Dmap (prepend o) (runFrom M ρ q′)

traceDist : ∀ {S} → Automaton S → Schedule S → Dist-ℚ (List (Output S))
traceDist M ρ = runFrom M ρ (initial M)

disabled-stutters : ∀ {S} (M : Automaton S) q t ρ → choose M q t ≡ nothing
  → runFrom M (t ∷ ρ) q ≈Mℚ runFrom M ρ q
disabled-stutters M q t ρ disabled rewrite disabled = λ P → trans
  (>>=ᴹ-identityˡ (nothing , q) (λ (o , q′) → Dmap (prepend o) (runFrom M ρ q′)) P)
  (Dmap-id (runFrom M ρ q) P)

-- An embedding names each local input by exactly one global action. Its
-- partial inverse prevents a single synchronized action from firing two
-- input transitions of one component.
record Ports (L G : Finite) : Set where
  field name : ⟨ L ⟩ → ⟨ G ⟩
        find : ⟨ G ⟩ → Maybe ⟨ L ⟩
        complete : ∀ i → find (name i) ≡ just i
        sound : ∀ g i → find g ≡ just i → name i ≡ g
open Ports public

record Wiring (A B : Signature) (boundary : Finite) : Set where
  field left : Ports (inputs A) (boundary ⊕ outputs B)
        right : Ports (inputs B) (boundary ⊕ outputs A)
        boundary-live : ∀ i → (∃ λ a → find left (inj₁ i) ≡ just a)
                            ⊎ (∃ λ b → find right (inj₁ i) ≡ just b)
open Wiring public

leftAction : ∀ {A B : Signature} → Local A → (Output A ⊎ Output B) ⊎ (⟨ hidden A ⟩ ⊎ ⟨ hidden B ⟩)
leftAction (inj₁ o) = inj₁ (inj₁ o)
leftAction (inj₂ h) = inj₂ (inj₁ h)

rightAction : ∀ {A B : Signature} → Local B → (Output A ⊎ Output B) ⊎ (⟨ hidden A ⟩ ⊎ ⟨ hidden B ⟩)
rightAction (inj₁ o) = inj₁ (inj₂ o)
rightAction (inj₂ h) = inj₂ (inj₂ h)

productTask : (A B : Signature)
  → (Output A ⊎ Output B) ⊎ (⟨ hidden A ⟩ ⊎ ⟨ hidden B ⟩) → Task A ⊎ Task B
productTask A B (inj₁ (inj₁ o)) = inj₁ (taskOf A (inj₁ o))
productTask A B (inj₁ (inj₂ o)) = inj₂ (taskOf B (inj₁ o))
productTask A B (inj₂ (inj₁ h)) = inj₁ (taskOf A (inj₂ h))
productTask A B (inj₂ (inj₂ h)) = inj₂ (taskOf B (inj₂ h))

left-class : ∀ A B a → productTask A B (leftAction {A} {B} a) ≡ inj₁ (taskOf A a)
left-class A B (inj₁ o) = refl
left-class A B (inj₂ h) = refl

right-class : ∀ A B a → productTask A B (rightAction {A} {B} a) ≡ inj₂ (taskOf B a)
right-class A B (inj₁ o) = refl
right-class A B (inj₂ h) = refl

productSignature : Signature → Signature → Finite → Signature
productSignature A B J = record
  { inputs = J
  ; outputs = outputs A ⊕ outputs B
  ; hidden = hidden A ⊕ hidden B
  ; tasks = tasks A ⊕ tasks B
  ; taskOf = productTask A B
  ; task-inhabited = λ where
      (inj₁ t) → let a , p = task-inhabited A t in leftAction {A} {B} a , trans (left-class A B a) (cong inj₁ p)
      (inj₂ t) → let a , p = task-inhabited B t in rightAction {A} {B} a , trans (right-class A B a) (cong inj₂ p)
  }
