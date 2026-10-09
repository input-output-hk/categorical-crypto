{-# OPTIONS --safe --without-K #-}

-- `Prot`: interfaces and protocols, with the simulation zig-zag as equality.
-- Each law is one simulation, proved by one structural induction on a step
-- tree: the unit laws drop the wire's `⊤` state (brzuska2018 Lemma 2),
-- associativity re-brackets it (Lemma 1) by three mutual inductions along
-- the `graft`/`serve` recursion, and the congruence pairs the two state maps.

open import Categories.Category.Core
open import Categories.Category.EquivClosureHelper

open import Data.Product.Base
open import Data.Unit.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol

module CategoricalCrypto.SSP.Protocol.Category where

private variable
  A B C D : Iface
  Y : Set

module _ (P : Protocol A B) where

  wireᵖ-identityˡ : wireᵖ ∘ᵖ P ≲ᵖ P
  wireᵖ-identityˡ = record
    { θ = proj₂ ; θ-init = refl ; θ-step = λ (_ , s) c q → serve-wire (step P s c q) }
    where
    serve-wire : {c : Ch B} (t : Calls A (St P × R B c))
               → mapᶜ (map₁ proj₂) (serve wireᵖ P (λ r → ret (tt , r)) t) ≈ᶜ t
    serve-wire (ret _)      = ret refl
    serve-wire (call _ _ k) = call λ r → serve-wire (k r)
    serve-wire (coin _ k)   = coin λ b → serve-wire (k b)
    serve-wire dead         = dead

  wireᵖ-identityʳ : P ∘ᵖ wireᵖ ≲ᵖ P
  wireᵖ-identityʳ = record
    { θ = proj₁ ; θ-init = refl ; θ-step = λ (s , _) c q → graft-wire (step P s c q) }
    where
    graft-wire : (t : Calls A (St P × Y)) → mapᶜ (map₁ proj₁) (graft P wireᵖ t tt) ≈ᶜ t
    graft-wire (ret _)      = ret refl
    graft-wire (call _ _ k) = call λ r → graft-wire (k r)
    graft-wire (coin _ k)   = coin λ b → graft-wire (k b)
    graft-wire dead         = dead

module _ (h : Protocol C D) (g : Protocol B C) (f : Protocol A B) where

  ∘ᵖ-assoc : (h ∘ᵖ g) ∘ᵖ f ≲ᵖ h ∘ᵖ (g ∘ᵖ f)
  ∘ᵖ-assoc = record
    { θ = assocʳ′ ; θ-init = refl
    ; θ-step = λ ((s₃ , s₂) , s₁) c q → graft-graft (step h s₃ c q) s₂ s₁ }
    where
    mutual
      graft-graft : (t : Calls C (St h × Y)) (s₂ : St g) (s₁ : St f)
                  → mapᶜ (map₁ assocʳ′) (graft (h ∘ᵖ g) f (graft h g t s₂) s₁)
                    ≈ᶜ graft h (g ∘ᵖ f) t (s₂ , s₁)
      graft-graft (ret _)      s₂ s₁ = ret refl
      graft-graft (call c q k) s₂ s₁ = graft-serve k (step g s₂ c q) s₁
      graft-graft (coin _ k)   s₂ s₁ = coin λ b → graft-graft (k b) s₂ s₁
      graft-graft dead         s₂ s₁ = dead

      graft-serve : {c : Ch C} (k : R C c → Calls C (St h × Y)) (u : Calls B (St g × R C c))
                    (s₁ : St f)
                  → mapᶜ (map₁ assocʳ′) (graft (h ∘ᵖ g) f (serve h g k u) s₁)
                    ≈ᶜ serve h (g ∘ᵖ f) k (graft g f u s₁)
      graft-serve k (ret (s₂ , r))  s₁ = graft-graft (k r) s₂ s₁
      graft-serve k (call b q k′) s₁ = serve-serve k k′ (step f s₁ b q)
      graft-serve k (coin _ k′)   s₁ = coin λ b → graft-serve k (k′ b) s₁
      graft-serve k dead          s₁ = dead

      serve-serve : {c : Ch C} {b : Ch B} (k : R C c → Calls C (St h × Y))
                    (k′ : R B b → Calls B (St g × R C c)) (v : Calls A (St f × R B b))
                  → mapᶜ (map₁ assocʳ′) (serve (h ∘ᵖ g) f (λ r → serve h g k (k′ r)) v)
                    ≈ᶜ serve h (g ∘ᵖ f) k (serve g f k′ v)
      serve-serve k k′ (ret (s₁ , r)) = graft-serve k (k′ r) s₁
      serve-serve k k′ (call _ _ k″)  = call λ r → serve-serve k k′ (k″ r)
      serve-serve k k′ (coin _ k″)    = coin λ b → serve-serve k k′ (k″ b)
      serve-serve k k′ dead           = dead

module _ {f h : Protocol B C} {g i : Protocol A B} (u : f ≲ᵖ h) (v : g ≲ᵖ i) where

  ∘ᵖ-resp-≲ᵖ : f ∘ᵖ g ≲ᵖ h ∘ᵖ i
  ∘ᵖ-resp-≲ᵖ = record
    { θ = map (θ u) (θ v) ; θ-init = cong₂ _,_ (θ-init u) (θ-init v)
    ; θ-step = λ (s₂ , s₁) c q → graft-sim (step f s₂ c q) (θ-step u s₂ c q) s₁ }
    where
    mutual
      graft-sim : (t : Calls B (St f × Y)) {t′ : Calls B (St h × Y)}
                → mapᶜ (map₁ (θ u)) t ≈ᶜ t′ → (s₁ : St g)
                → mapᶜ (map₁ (map (θ u) (θ v))) (graft f g t s₁) ≈ᶜ graft h i t′ (θ v s₁)
      graft-sim (ret _)      (ret refl) s₁ = ret refl
      graft-sim (call b q k) (call e)   s₁ = serve-sim k e (step g s₁ b q) (θ-step v s₁ b q)
      graft-sim (coin _ k)   (coin e)   s₁ = coin λ b → graft-sim (k b) (e b) s₁
      graft-sim dead         dead       s₁ = dead

      serve-sim : {b : Ch B} (k : R B b → Calls B (St f × Y)) {k′ : R B b → Calls B (St h × Y)}
                → (∀ r → mapᶜ (map₁ (θ u)) (k r) ≈ᶜ k′ r)
                → (w : Calls A (St g × R B b)) {w′ : Calls A (St i × R B b)}
                → mapᶜ (map₁ (θ v)) w ≈ᶜ w′
                → mapᶜ (map₁ (map (θ u) (θ v))) (serve f g k w) ≈ᶜ serve h i k′ w′
      serve-sim k e (ret (s₁ , r)) (ret refl) = graft-sim (k r) (e r) s₁
      serve-sim k e (call _ _ k₁)  (call e₁)  = call λ r → serve-sim k e (k₁ r) (e₁ r)
      serve-sim k e (coin _ k₁)    (coin e₁)  = coin λ b → serve-sim k e (k₁ b) (e₁ b)
      serve-sim k e dead           dead       = dead

Prot : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
Prot = categoryHelperᵉ record
  { Obj       = Iface
  ; _⇒_       = Protocol
  ; _≈_       = _≲ᵖ_
  ; id        = wireᵖ
  ; _∘_       = _∘ᵖ_
  ; assoc     = λ {f = f} {g} {h} → ∘ᵖ-assoc h g f
  ; identityˡ = λ {f = f} → wireᵖ-identityˡ f
  ; identityʳ = λ {f = f} → wireᵖ-identityʳ f
  ; ∘-resp-≈  = ∘ᵖ-resp-≲ᵖ
  }

∘ᵖ-resp-≈ᵖ : {f h : Protocol B C} {g i : Protocol A B} → f ≈ᵖ h → g ≈ᵖ i → f ∘ᵖ g ≈ᵖ h ∘ᵖ i
∘ᵖ-resp-≈ᵖ = Category.∘-resp-≈ Prot
