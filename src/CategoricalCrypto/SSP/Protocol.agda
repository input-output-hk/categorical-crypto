{-# OPTIONS --safe --without-K #-}

-- Call trees and protocols over channel-indexed interfaces
-- (`docs/uc-setup-ssp.md` §3.2–3.3).  A step answers one query on the right
-- interface with a finite tree of calls on the left one, rational coins and
-- `dead` (SSP's violated assert, brzuska2018 §3).  `_∘ᵖ_` inlines the lower
-- protocol into the upper one's calls (Def. 4).  `_⊗ᵖ_` serves a query on the
-- factor owning its channel and replies on that channel, so control stays one
-- thread; shared imports (Def. 6) are `(P ⊗ᵖ P′) ∘ᵖ ⌜ ∇ ⌝`.
--
-- The hom equality is the equivalence closure of state simulations, step trees
-- compared by `_≈ᶜ_`: extensional tree equality, which needs no funext.

open import Data.Bool.Base using (Bool)
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (id; _∘_)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Distribution.RationalDist

open import CategoricalCrypto.SSP.Iface

module CategoricalCrypto.SSP.Protocol where

private variable
  A A′ B C D : Iface
  X Y Z : Set

------------------------------------------------------------------------
-- Call trees

data Calls (A : Iface) (X : Set) : Set where
  ret  : X → Calls A X
  call : (c : Ch A) → Q A c → (R A c → Calls A X) → Calls A X
  coin : Dist-ℚ Bool → (Bool → Calls A X) → Calls A X
  dead : Calls A X

mapᶜ : (X → Y) → Calls A X → Calls A Y
mapᶜ f (ret x)      = ret (f x)
mapᶜ f (call c q k) = call c q λ r → mapᶜ f (k r)
mapᶜ f (coin μ k)   = coin μ λ b → mapᶜ f (k b)
mapᶜ f dead         = dead

-- Calls go out through `m`, replies come back through it.
reindex : A ⇒ᴵ A′ → Calls A X → Calls A′ X
reindex m (ret x)      = ret x
reindex m (call c q k) = call (ch m c) (qu m q) λ r → reindex m (k (re m r))
reindex m (coin μ k)   = coin μ λ b → reindex m (k b)
reindex m dead         = dead

infix 4 _≈ᶜ_

data _≈ᶜ_ {A : Iface} {X : Set} : Calls A X → Calls A X → Set where
  ret  : ∀ {x x′} → x ≡ x′ → ret x ≈ᶜ ret x′
  call : ∀ {c q k k′} → (∀ r → k r ≈ᶜ k′ r) → call c q k ≈ᶜ call c q k′
  coin : ∀ {μ k k′} → (∀ b → k b ≈ᶜ k′ b) → coin μ k ≈ᶜ coin μ k′
  dead : dead ≈ᶜ dead

≈ᶜ-refl : {t : Calls A X} → t ≈ᶜ t
≈ᶜ-refl {t = ret _}      = ret refl
≈ᶜ-refl {t = call _ _ _} = call λ _ → ≈ᶜ-refl
≈ᶜ-refl {t = coin _ _}   = coin λ _ → ≈ᶜ-refl
≈ᶜ-refl {t = dead}       = dead

≈ᶜ-sym : {t t′ : Calls A X} → t ≈ᶜ t′ → t′ ≈ᶜ t
≈ᶜ-sym (ret p)  = ret (sym p)
≈ᶜ-sym (call h) = call λ r → ≈ᶜ-sym (h r)
≈ᶜ-sym (coin h) = coin λ b → ≈ᶜ-sym (h b)
≈ᶜ-sym dead     = dead

≈ᶜ-trans : {t t′ t″ : Calls A X} → t ≈ᶜ t′ → t′ ≈ᶜ t″ → t ≈ᶜ t″
≈ᶜ-trans (ret p)  (ret p′)  = ret (trans p p′)
≈ᶜ-trans (call h) (call h′) = call λ r → ≈ᶜ-trans (h r) (h′ r)
≈ᶜ-trans (coin h) (coin h′) = coin λ b → ≈ᶜ-trans (h b) (h′ b)
≈ᶜ-trans dead     dead      = dead

≈ᶜ-isEquivalence : IsEquivalence (_≈ᶜ_ {A} {X})
≈ᶜ-isEquivalence = record { refl = ≈ᶜ-refl ; sym = ≈ᶜ-sym ; trans = ≈ᶜ-trans }

mapᶜ-cong : (f : X → Y) {t t′ : Calls A X} → t ≈ᶜ t′ → mapᶜ f t ≈ᶜ mapᶜ f t′
mapᶜ-cong f (ret p)  = ret (cong f p)
mapᶜ-cong f (call h) = call λ r → mapᶜ-cong f (h r)
mapᶜ-cong f (coin h) = coin λ b → mapᶜ-cong f (h b)
mapᶜ-cong f dead     = dead

mapᶜ-id : {f : X → X} → (∀ x → f x ≡ x) → (t : Calls A X) → mapᶜ f t ≈ᶜ t
mapᶜ-id h (ret x)      = ret (h x)
mapᶜ-id h (call _ _ k) = call λ r → mapᶜ-id h (k r)
mapᶜ-id h (coin _ k)   = coin λ b → mapᶜ-id h (k b)
mapᶜ-id h dead         = dead

mapᶜ-∘ : (f : Y → Z) (g : X → Y) (t : Calls A X) → mapᶜ f (mapᶜ g t) ≈ᶜ mapᶜ (f ∘ g) t
mapᶜ-∘ f g (ret _)      = ret refl
mapᶜ-∘ f g (call _ _ k) = call λ r → mapᶜ-∘ f g (k r)
mapᶜ-∘ f g (coin _ k)   = coin λ b → mapᶜ-∘ f g (k b)
mapᶜ-∘ f g dead         = dead

------------------------------------------------------------------------
-- Protocols

record Protocol (A B : Iface) : Set₁ where
  field St   : Set
        init : St
        step : St → (c : Ch B) → Q B c → Calls A (St × R B c)
open Protocol public

module _ (P₂ : Protocol B C) (P₁ : Protocol A B) where
  mutual
    graft : Calls B (St P₂ × Y) → St P₁ → Calls A ((St P₂ × St P₁) × Y)
    graft (ret (s₂ , y)) s₁ = ret ((s₂ , s₁) , y)
    graft (call b q k)   s₁ = serve k (step P₁ s₁ b q)
    graft (coin μ k)     s₁ = coin μ λ x → graft (k x) s₁
    graft dead           s₁ = dead

    serve : {b : Ch B} → (R B b → Calls B (St P₂ × Y)) → Calls A (St P₁ × R B b)
          → Calls A ((St P₂ × St P₁) × Y)
    serve k (ret (s₁ , r)) = graft (k r) s₁
    serve k (call a q k₁)  = call a q λ r → serve k (k₁ r)
    serve k (coin μ k₁)    = coin μ λ x → serve k (k₁ x)
    serve k dead           = dead

  infixl 9 _∘ᵖ_
  _∘ᵖ_ : Protocol A C
  _∘ᵖ_ = record
    { St   = St P₂ × St P₁
    ; init = init P₂ , init P₁
    ; step = λ (s₂ , s₁) c q → graft (step P₂ s₂ c q) s₁ }

-- `⌜_⌝` is contravariant: it serves `A` by calling `B`.
⌜_⌝ : A ⇒ᴵ B → Protocol B A
⌜ m ⌝ = record { St = ⊤ ; init = tt ; step = λ _ c q → call (ch m c) (qu m q) λ r → ret (tt , re m r) }

wireᵖ : Protocol A A
wireᵖ = ⌜ idᴵ ⌝

infixr 10 _⊗ᵖ_

_⊗ᵖ_ : Protocol A B → Protocol C D → Protocol (A ⊗ᴵ C) (B ⊗ᴵ D)
P ⊗ᵖ P′ = record
  { St   = St P × St P′
  ; init = init P , init P′
  ; step = λ where
      (s , t) (inj₁ b) q → mapᶜ (map₁ (_, t)) (reindex ι₁ (step P s b q))
      (s , t) (inj₂ d) q → mapᶜ (map₁ (s ,_)) (reindex ι₂ (step P′ t d q)) }

------------------------------------------------------------------------
-- Simulations and the hom equality

infix 4 _≲ᵖ_ _≈ᵖ_

record _≲ᵖ_ (P P′ : Protocol A B) : Set where
  field θ      : St P → St P′
        θ-init : θ (init P) ≡ init P′
        θ-step : ∀ s c q → mapᶜ (map₁ θ) (step P s c q) ≈ᶜ step P′ (θ s) c q
open _≲ᵖ_ public

≲ᵖ-refl : {P : Protocol A B} → P ≲ᵖ P
≲ᵖ-refl {P = P} = record
  { θ = id ; θ-init = refl ; θ-step = λ s c q → mapᶜ-id (λ _ → refl) (step P s c q) }

_≈ᵖ_ : Rel (Protocol A B) (suc 0ℓ)
_≈ᵖ_ = EqC.EqClosure _≲ᵖ_

≲⇒≈ᵖ : {P P′ : Protocol A B} → P ≲ᵖ P′ → P ≈ᵖ P′
≲⇒≈ᵖ = EqC.return

Prot-setoid : Iface → Iface → Setoid (suc 0ℓ) (suc 0ℓ)
Prot-setoid A B = EqC.setoid (_≲ᵖ_ {A} {B})
