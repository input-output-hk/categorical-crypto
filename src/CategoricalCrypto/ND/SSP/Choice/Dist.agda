{-# OPTIONS --safe --without-K #-}

-- The laws of `_≈ᵈ_` survive `choose` (`docs/uc-setup-nondeterministic.md`
-- §5.3).  `t ≈ᵏ⁺ t′` is `_≈ᵏ_` after resolving against every queue state, so a
-- law under a `choose` is the law at each pick (`choose-cong`), and
-- `stepwise⁺` lifts step-wise `≈ᵏ⁺` through `⌈_⌉` to `≈ᵈ`.  Pick-ahead lets a
-- choice pass a coin or a call (`coin-choose`, `call-choose`, compiled
-- `coin-choose-ᵈ`, `call-choose-ᵈ`): the pick is read from a queue that no coin
-- or reply feeds, and with the queue empty one side dies before the coin or
-- call and the other after it, which `coin-drop` and `call-dead` equate.  Under
-- a demon that saw the toss this was no law (the leak of the superseded design).

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist using (Dist-ℚ; return-ℚ)
open import ProbabilisticLogic.Distribution.RationalDist.Partial using (kmaybe; >>=ᴹ-const)
open import ProbabilisticLogic.Distribution.RationalDist.Setoid using (>>=ᴹ-congˡ)

open import CategoricalCrypto.ND.SSP.Choice
open import CategoricalCrypto.SSP.Dist
open import CategoricalCrypto.SSP.Dist.Kernel
open import CategoricalCrypto.SSP.Dist.Laws
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol

module CategoricalCrypto.ND.SSP.Choice.Dist where

private variable
  A B : Iface
  S⃗ : List Set
  X Y : Set

infix 4 _≈ᵏ⁺_

record _≈ᵏ⁺_ (t t′ : Calls⁺ A S⃗ (X × Y)) : Set₁ where
  constructor mk≈ᵏ⁺
  field resolve≈ᵏ : (qs : Queues S⃗) → resolve qs t ≈ᵏ resolve qs t′
open _≈ᵏ⁺_ public

choose-cong : {i : Ch Cᴵ⟦ S⃗ ⟧} {k k′ : Q Cᴵ⟦ S⃗ ⟧ i → Calls⁺ A S⃗ (X × Y)}
            → (∀ p → k p ≈ᵏ⁺ k′ p) → choose i k ≈ᵏ⁺ choose i k′
choose-cong {S⃗ = S⃗} {i = i} {k} {k′} h = mk≈ᵏ⁺ go
  where
  go : ∀ qs → resolve qs (choose i k) ≈ᵏ resolve qs (choose i k′)
  go qs with pop S⃗ i qs
  ... | nothing        = ≈ᵏ-refl
  ... | just (p , qs′) = resolve≈ᵏ (h p) qs′

coin-choose : (μ : Dist-ℚ Bool) (i : Ch Cᴵ⟦ S⃗ ⟧) (k : Bool → Q Cᴵ⟦ S⃗ ⟧ i → Calls⁺ A S⃗ (X × Y))
            → coin μ (λ b → choose i (k b)) ≈ᵏ⁺ choose i (λ p → coin μ λ b → k b p)
coin-choose {S⃗ = S⃗} μ i k = mk≈ᵏ⁺ go
  where
  go : ∀ qs → resolve qs (coin μ λ b → choose i (k b)) ≈ᵏ resolve qs (choose i λ p → coin μ λ b → k b p)
  go qs with pop S⃗ i qs
  ... | nothing = coin-drop μ dead
  ... | just _  = ≈ᵏ-refl

-- A call whose every reply dies is dead: no oracle answer is observed.
call-dead : (c : Ch A) (q : Q A c) → _≈ᵏ_ {A = A} {X = X} (call c q λ _ → dead) dead
call-dead c q = mk≈ᵏ λ O s ξ → trans
  (>>=ᴹ-congˡ (O s c q) (kmaybe λ _ → return-ℚ nothing) (λ _ → return-ℚ nothing) (λ where
    (just _) _ → refl
    nothing  _ → refl) ξ)
  (>>=ᴹ-const (O s c q) (return-ℚ nothing) ξ)

call-choose : (c : Ch A) (q : Q A c) (i : Ch Cᴵ⟦ S⃗ ⟧) (k : R A c → Q Cᴵ⟦ S⃗ ⟧ i → Calls⁺ A S⃗ (X × Y))
            → call c q (λ r → choose i (k r)) ≈ᵏ⁺ choose i (λ p → call c q λ r → k r p)
call-choose {S⃗ = S⃗} c q i k = mk≈ᵏ⁺ go
  where
  go : ∀ qs → resolve qs (call c q λ r → choose i (k r)) ≈ᵏ resolve qs (choose i λ p → call c q λ r → k r p)
  go qs with pop S⃗ i qs
  ... | nothing = call-dead c q
  ... | just _  = ≈ᵏ-refl

stepwise⁺ : {P P′ : Protocol⁺ S⃗ A B} (θ : St P → St P′) → θ (init P) ≡ init P′
          → (∀ s c q → mapᶜ⁺ (map₁ θ) (step P s c q) ≈ᵏ⁺ step P′ (θ s) c q) → ⌈ P ⌉ ≈ᵈ ⌈ P′ ⌉
stepwise⁺ {S⃗ = S⃗} {P = P} θ e h = stepwise (map₁ θ) (cong (_, empty S⃗) e) λ where
  (s , qs) (inj₁ i) p → ≈ᶜ⇒≈ᵏ (ret refl)
  (s , qs) (inj₂ c) q →
    ≈ᵏ-trans (≈ᶜ⇒≈ᵏ (resolve-sim {θ = θ} (step P s c q) ≈ᶜ⁺-refl qs)) (resolve≈ᵏ (h s c q) qs)

module _ {St₀ : Set} (s₀ : St₀) (μ : Dist-ℚ Bool) (i : Ch Cᴵ⟦ S⃗ ⟧)
         (k : St₀ → (c : Ch B) → Q B c → Bool → Q Cᴵ⟦ S⃗ ⟧ i → Calls⁺ A S⃗ (St₀ × R B c)) where

  coin-first choice-first : Protocol⁺ S⃗ A B
  coin-first   = record { St = St₀ ; init = s₀ ; step = λ s c q → coin μ λ b → choose i (k s c q b) }
  choice-first = record { St = St₀ ; init = s₀ ; step = λ s c q → choose i λ p → coin μ λ b → k s c q b p }

  coin-choose-ᵈ : ⌈ coin-first ⌉ ≈ᵈ ⌈ choice-first ⌉
  coin-choose-ᵈ = stepwise id refl λ where
    (s , qs) (inj₁ _) _ → ≈ᵏ-refl
    (s , qs) (inj₂ c) q →
      ≈ᵏ-trans (≈ᶜ⇒≈ᵏ (mapᶜ-id (λ _ → refl) _)) (resolve≈ᵏ (coin-choose μ i (k s c q)) qs)

module _ {St₀ : Set} (s₀ : St₀) (i : Ch Cᴵ⟦ S⃗ ⟧) (a : St₀ → (c : Ch B) → Q B c → Ch A)
         (qa : ∀ s c q → Q A (a s c q))
         (k : ∀ s c q → R A (a s c q) → Q Cᴵ⟦ S⃗ ⟧ i → Calls⁺ A S⃗ (St₀ × R B c)) where

  call-first choose-first : Protocol⁺ S⃗ A B
  call-first   = record { St = St₀ ; init = s₀ ; step = λ s c q → call (a s c q) (qa s c q) λ r → choose i (k s c q r) }
  choose-first = record { St = St₀ ; init = s₀ ; step = λ s c q → choose i λ p → call (a s c q) (qa s c q) λ r → k s c q r p }

  call-choose-ᵈ : ⌈ call-first ⌉ ≈ᵈ ⌈ choose-first ⌉
  call-choose-ᵈ = stepwise id refl λ where
    (s , qs) (inj₁ _) _ → ≈ᵏ-refl
    (s , qs) (inj₂ c) q →
      ≈ᵏ-trans (≈ᶜ⇒≈ᵏ (mapᶜ-id (λ _ → refl) _)) (resolve≈ᵏ (call-choose (a s c q) (qa s c q) i (k s c q)) qs)
