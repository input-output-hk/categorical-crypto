{-# OPTIONS --safe --without-K #-}

-- The laws of `choose` at SSP (`docs/uc-setup-nondeterministic.md` §5.1,
-- §3.4).  Steps related by `_≈ᶜ⁺_` compile to equal protocols (`congruence`,
-- row 1), so a choice whose branches agree collapses (`collapse`, row 4), also
-- when they agree only against the callee (`Callee`: two calls in either
-- order, to a protocol on which they commute).  Row 2, `choose` past a coin or
-- a call, is `Choice.Dist`'s `coin-choose-ᵈ`, `call-choose-ᵈ`.  A map π of the
-- picks is a hom-equality after the relabelling wire along π (`permute`,
-- row 3): the simulation maps the queue by π.  At π = not the two orders of a
-- two-way choice are equal after swapping the picks (`Swap.swap-ᵖ`, §3.4);
-- `at`/`at-sub` read a compiled protocol at grade (unitᴵ , S⃗), where that wire
-- is the ND_A simulator id ⊗ ⌈ π ⌉ʳ.  Interfaces under `_⊗ᴵ_` are passed
-- explicitly: unification does not recover them (their `Ch-dec` field).

module CategoricalCrypto.ND.SSP.Laws where

open import Class.DecEq
open import Data.Bool.Base using (Bool; true; false; if_then_else_; not)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Properties using (map-++)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import CategoricalCrypto.ND.Relabel
open import CategoricalCrypto.ND.SSP.Choice
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category
open import CategoricalCrypto.SSP.Protocol.Monoidal

private
  open MonoidalCategory Protᴹ using (module Equiv; module HomReasoning; unitorˡ-commute-to)
  open HomReasoning

  variable
    A B : Iface
    S St₀ : Set
    S⃗ : List Set

------------------------------------------------------------------------
-- Congruence (row 1)
------------------------------------------------------------------------

-- The protocol with choices given by its steps.
steps : St₀ → (St₀ → (c : Ch B) → Q B c → Calls⁺ A S⃗ (St₀ × R B c)) → Protocol⁺ S⃗ A B
steps s₀ k = record { St = _ ; init = s₀ ; step = k }

private
  map-id : {X Y : Set} {t t′ : Calls⁺ A S⃗ (X × Y)} → t ≈ᶜ⁺ t′ → mapᶜ⁺ (map₁ id) t ≈ᶜ⁺ t′
  map-id (ret e)    = ret e
  map-id (call h)   = call λ r → map-id (h r)
  map-id (coin h)   = coin λ b → map-id (h b)
  map-id dead       = dead
  map-id (choose h) = choose λ p → map-id (h p)

congruence : {s₀ : St₀} {k k′ : St₀ → (c : Ch B) → Q B c → Calls⁺ A S⃗ (St₀ × R B c)}
           → (∀ s c q → k s c q ≈ᶜ⁺ k′ s c q) → ⌈ steps {B = B} s₀ k ⌉ ≈ᵖ ⌈ steps {B = B} s₀ k′ ⌉
congruence h = ⌈⌉-resp (EqC.return record { θ = id ; θ-init = refl ; θ-step = λ s c q → map-id (h s c q) })

plain-cong : {X : Set} {t t′ : Calls A X} → t ≈ᶜ t′ → plainᶜ {S⃗ = S⃗} t ≈ᶜ⁺ plainᶜ t′
plain-cong (ret e)  = ret e
plain-cong (call h) = call λ r → plain-cong (h r)
plain-cong (coin h) = coin λ b → plain-cong (h b)
plain-cong dead     = dead

------------------------------------------------------------------------
-- Relabelling the picks
------------------------------------------------------------------------

-- The relabelling of a one-site protocol's picks along π.
pickʳ : (S → S) → S ∷ [] ⇝ S ∷ []
pickʳ {S} π = record { route = route′ ; injective = inj′ }
  where
  route′ : (i : Ch Cᴵ⟦ S ∷ [] ⟧) → Maybe (Σ[ k ∈ Ch Cᴵ⟦ S ∷ [] ⟧ ] (Q Cᴵ⟦ S ∷ [] ⟧ i → Q Cᴵ⟦ S ∷ [] ⟧ k))
  route′ (inj₁ _)  = just (inj₁ tt , π)
  route′ (inj₂ ())
  inj′ : ∀ {i j k} → target (route′ i) ≡ just k → target (route′ j) ≡ just k → i ≡ j
  inj′ {inj₁ _}  {inj₁ _}  _ _ = refl
  inj′ {inj₂ ()}
  inj′ {inj₁ _}  {inj₂ ()}

-- A compiled protocol at grade (unitᴵ , S⃗), and a simulator on the choice
-- factors moved past the grade's unit.
at : (S⃗ : List Set) → Protocol A (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ B) → Protocol A ((unitᴵ ⊗ᴵ Cᴵ⟦ S⃗ ⟧) ⊗ᴵ B)
at {B = B} S⃗ P = ⌜ λᴵ {Cᴵ⟦ S⃗ ⟧} ⌝ ⊗ᵖ wireᵖ {B} ∘ᵖ P

at-sub : (S⃗ T⃗ : List Set) (h : Protocol Cᴵ⟦ T⃗ ⟧ Cᴵ⟦ S⃗ ⟧) (P : Protocol A (Cᴵ⟦ T⃗ ⟧ ⊗ᴵ B))
       → at {B = B} S⃗ (h ⊗ᵖ wireᵖ {B} ∘ᵖ P) ≈ᵖ (wireᵖ {unitᴵ} ⊗ᵖ h) ⊗ᵖ wireᵖ {B} ∘ᵖ at {B = B} T⃗ P
at-sub {B = B} S⃗ T⃗ h P = begin
  λˢ ⊗ᵖ I ∘ᵖ (h ⊗ᵖ I ∘ᵖ P)
    ≈˘⟨ ≲⇒≈ᵖ (∘ᵖ-assoc (λˢ ⊗ᵖ I) (h ⊗ᵖ I) P) ⟩
  (λˢ ⊗ᵖ I ∘ᵖ h ⊗ᵖ I) ∘ᵖ P
    ≈˘⟨ ∘ᵖ-resp-≈ᵖ (≲⇒≈ᵖ (⊗ᵖ-homomorphism λˢ h I I)) (Equiv.refl {x = P}) ⟩
  (λˢ ∘ᵖ h) ⊗ᵖ (I ∘ᵖ I) ∘ᵖ P
    ≈⟨ ∘ᵖ-resp-≈ᵖ (⊗ᵖ-resp-≈ᵖ (unitorˡ-commute-to {f = h}) (Equiv.refl {x = I ∘ᵖ I})) (Equiv.refl {x = P}) ⟩
  (U ⊗ᵖ h ∘ᵖ λᵗ) ⊗ᵖ (I ∘ᵖ I) ∘ᵖ P
    ≈⟨ ∘ᵖ-resp-≈ᵖ (≲⇒≈ᵖ (⊗ᵖ-homomorphism (U ⊗ᵖ h) λᵗ I I)) (Equiv.refl {x = P}) ⟩
  ((U ⊗ᵖ h) ⊗ᵖ I ∘ᵖ λᵗ ⊗ᵖ I) ∘ᵖ P
    ≈⟨ ≲⇒≈ᵖ (∘ᵖ-assoc ((U ⊗ᵖ h) ⊗ᵖ I) (λᵗ ⊗ᵖ I) P) ⟩
  (U ⊗ᵖ h) ⊗ᵖ I ∘ᵖ (λᵗ ⊗ᵖ I ∘ᵖ P) ∎
  where
  I = wireᵖ {B}
  U = wireᵖ {unitᴵ}
  λˢ = ⌜ λᴵ {Cᴵ⟦ S⃗ ⟧} ⌝
  λᵗ = ⌜ λᴵ {Cᴵ⟦ T⃗ ⟧} ⌝

------------------------------------------------------------------------
-- One-site protocols: collapse (row 4), permutation (row 3)
------------------------------------------------------------------------

module _ {A B : Iface} (s₀ : St₀) where

  -- One site, consumed once per activation; the plain step tree at the pick.
  ⟨_⟩ : (S → St₀ → (c : Ch B) → Q B c → Calls A (St₀ × R B c)) → Protocol⁺ (S ∷ []) A B
  ⟨ k ⟩ = steps s₀ λ s c q → choose (inj₁ tt) λ p → plainᶜ (k p s c q)

  collapse : {k : S → St₀ → (c : Ch B) → Q B c → Calls A (St₀ × R B c)}
             {k₀ : St₀ → (c : Ch B) → Q B c → Calls A (St₀ × R B c)}
           → (∀ p s c q → k p s c q ≈ᶜ k₀ s c q) → ⌈ ⟨ k ⟩ ⌉ ≈ᵖ ⌈ ⟨ (λ (_ : S) → k₀) ⟩ ⌉
  collapse h = congruence λ s c q → choose λ p → plain-cong (h p s c q)

  permute : (π : S → S) (k : S → St₀ → (c : Ch B) → Q B c → Calls A (St₀ × R B c))
          → ⌈ ⟨ k ∘ π ⟩ ⌉ ≈ᵖ ⌈ pickʳ π ⌉ʳ ⊗ᵖ wireᵖ {B} ∘ᵖ ⌈ ⟨ k ⟩ ⌉
  permute {S = S} π k = ≲⇒≈ᵖ record
    { θ = θπ ; θ-init = refl
    ; θ-step = λ where
        (s , q , _)     (inj₁ (inj₁ _)) p  → ret (cong (λ z → ((tt , tt) , s , z , tt) , tt) (map-++ π q (p ∷ [])))
        (s , q , _)     (inj₁ (inj₂ ())) _
        (s , [] , _)    (inj₂ c) _         → dead
        (s , p ∷ q , _) (inj₂ c) q′        → go (k (π p) s c q′) q }
    where
    θπ : St₀ × List S × ⊤ → (⊤ × ⊤) × St₀ × List S × ⊤
    θπ (s , q , _) = (tt , tt) , s , List.map π q , tt
    go : {c : Ch B} (t : Calls A (St₀ × R B c)) (q : List S)
       → mapᶜ (map₁ θπ) (resolve {S⃗ = S ∷ []} (q , tt) (plainᶜ t))
         ≈ᶜ serve (⌈ pickʳ π ⌉ʳ ⊗ᵖ wireᵖ {B}) ⌈ ⟨ k ⟩ ⌉ {b = inj₂ c} (λ r → ret ((tt , tt) , r))
                  (resolve {S⃗ = S ∷ []} (List.map π q , tt) (plainᶜ t))
    go (ret _)       q = ret refl
    go (call _ _ k′) q = call λ r → go (k′ r) q
    go (coin _ k′)   q = coin λ b → go (k′ b) q
    go dead          q = dead

  -- The two orders of a two-way choice.
  module Swap (t₀ t₁ : St₀ → (c : Ch B) → Q B c → Calls A (St₀ × R B c)) where
    ab ba : Bool → St₀ → (c : Ch B) → Q B c → Calls A (St₀ × R B c)
    ab b = if b then t₀ else t₁
    ba b = if b then t₁ else t₀

    swap-ᵖ : ⌈ ⟨ ba ⟩ ⌉ ≈ᵖ ⌈ pickʳ not ⌉ʳ ⊗ᵖ wireᵖ {B} ∘ᵖ ⌈ ⟨ ab ⟩ ⌉
    swap-ᵖ = Equiv.trans (congruence λ _ _ _ → choose λ where
                            true  → ≈ᶜ⁺-refl
                            false → ≈ᶜ⁺-refl)
                         (permute not ab)


------------------------------------------------------------------------
-- Collapse against a callee
------------------------------------------------------------------------

module Callee where

  Two : Iface
  Two = record { Ch = Bool ; Q = λ _ → ⊤ ; R = λ _ → ⊤ ; Ch-dec = DecEq-Bool }

  -- One counter per channel: the two calls commute.
  counters : Protocol unitᴵ Two
  counters = record { St = ℕ × ℕ ; init = 0 , 0 ; step = λ where
    (m , n) true  _ → ret ((suc m , n) , tt)
    (m , n) false _ → ret ((m , suc n) , tt) }

  -- Call both channels, the picked one first.
  both : Bool → ⊤ → (c : Ch (Cᴵ ⊤)) → Q (Cᴵ ⊤) c → Calls Two (⊤ × R (Cᴵ ⊤) c)
  both b _ _ _ = call b tt λ _ → call (not b) tt λ _ → ret (tt , tt)

  either-order : ⌈ ⟨_⟩ {A = Two} {B = Cᴵ ⊤} tt both ∘⁺ plain {S⃗ = []} counters ⌉
               ≈ᵖ ⌈ ⟨_⟩ {A = Two} {B = Cᴵ ⊤} tt (λ _ → both true) ∘⁺ plain {S⃗ = []} counters ⌉
  either-order = congruence λ _ _ _ → choose λ where
    true  → ≈ᶜ⁺-refl
    false → ≈ᶜ⁺-refl
