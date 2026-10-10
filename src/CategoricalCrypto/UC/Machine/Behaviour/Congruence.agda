{-# OPTIONS --safe --without-K --guardedness #-}

-- The machine operations absorbed (`Behaviour.Absorb`): a fixed machine beside
-- or around the hole is simulated by the distinguisher, its `Dₚ` steps unfolded
-- into coins.  With the trace (`Behaviour.Trace`) this makes behavioural
-- equality a congruence of the G construction (maurer2002 Lemma 4(i)): its
-- composite is `trace (α ∘ (f ⊗ g) ∘ γ)` (`Machines.Collapse`) and its tensor
-- `mid ∘ (f ⊗ g) ∘ mid`, each factor absorbed in turn.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Commutative
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (onL-pt; onR-pt; point-⊛)
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Behaviour.Absorb
open import CategoricalCrypto.UC.Machine.Behaviour.Trace
open import CategoricalCrypto.UC.Machine.Run

import Categories.Category.Monoidal.Bundle as Bundle
import Categories.GConstructionMonoidal as GM
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import Relation.Binary.Structures as Structures

module CategoricalCrypto.UC.Machine.Behaviour.Congruence where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MS = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module V = Bundle.SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module 𝔾 = Bundle.MonoidalCategory (𝒢ₚᴹ 0ℓ)
  variable A B C D X Y : Set

open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- Runs of the paired machines, their junctions absorbed

runˢ-⊛ : (S T : MC.State) (k : (MC.obj S × MC.obj T) × X → Dₚ ((MC.obj S × MC.obj T) × Y))
         (d : Strat X Y)
       → runˢ (MC.mk (S MC.⊛ T) k) d
         ≈ₚ (MC.point S tt >>=ₚ λ s → MC.point T tt >>=ₚ λ t → runFromˢ (MC.mk (S MC.⊛ T) k) (s , t) d)
runˢ-⊛ S T k d = bindˣ (point-⊛ S T tt) ⟨≈⟩ >>=ₚ-assoc (MC.point S tt) _ _
             ⟨≈⟩ bindᶠ λ s → >>=ₚ-assoc (MC.point T tt) _ _
             ⟨≈⟩ bindᶠ λ t → >>=ₚ-identityˡ (s , t) _

module _ (f : MC.Machine A B) (g : MC.Machine C D) (t : MC.St f) (s : MC.St g) where

  ⊗-run₁ : (a : A) (k : B ⊎ D → Strat (A ⊎ C) (B ⊎ D))
         → runFromˢ (f ⊗ᵉ g) (t , s) (ask (inj₁ a) k)
           ≈ₚ (MC.step f (t , a) >>=ₚ λ r → runFromˢ (f ⊗ᵉ g) (proj₁ r , s) (k (inj₁ (proj₂ r))))
  ⊗-run₁ a k = bindˣ ( tstep-inj₁ (MC.onL (MC.step f)) (MC.onR (MC.step g)) (t , s) a
                     ⟨≈⟩ bindˣ (onL-pt (MC.step f) t s a)
                     ⟨≈⟩ map-map (MC.step f (t , a)) _ _)
           ⟨≈⟩ bind-map (MC.step f (t , a)) _ _

  ⊗-run₂ : (c : C) (k : B ⊎ D → Strat (A ⊎ C) (B ⊎ D))
         → runFromˢ (f ⊗ᵉ g) (t , s) (ask (inj₂ c) k)
           ≈ₚ (MC.step g (s , c) >>=ₚ λ r → runFromˢ (f ⊗ᵉ g) (t , proj₁ r) (k (inj₂ (proj₂ r))))
  ⊗-run₂ c k = bindˣ ( tstep-inj₂ (MC.onL (MC.step f)) (MC.onR (MC.step g)) (t , s) c
                     ⟨≈⟩ bindˣ (onR-pt (MC.step g) t s c)
                     ⟨≈⟩ map-map (MC.step g (s , c)) _ _)
           ⟨≈⟩ bind-map (MC.step g (s , c)) _ _

-- `_∘ᴹ_` with its seal off, so a run can read the paired state.
infixr 9 _∘ʳ_

_∘ʳ_ : MC.Machine B C → MC.Machine A B → MC.Machine A C
g ∘ʳ f = MC.mk (MC.state g MC.⊛ MC.state f) (V._∘_ (MC.onL (MC.step g)) (MC.onR (MC.step f)))

opaque
  unfolding MC._∘ᴹ_

  ∘ʳ≈∘ᴹ : (g : MC.Machine B C) (f : MC.Machine A B) → (g ∘ʳ f) MS.≈ᴹ (g MC.∘ᴹ f)
  ∘ʳ≈∘ᴹ g f = MS.reflᴹ

∘ʳ-run : (g : MC.Machine B C) (f : MC.Machine A B) (s : MC.St g) (t : MC.St f) (a : A)
         (k : C → Strat A C)
       → runFromˢ (g ∘ʳ f) (s , t) (ask a k)
         ≈ₚ (MC.step f (t , a) >>=ₚ λ r → MC.step g (s , proj₂ r) >>=ₚ λ r′ →
               runFromˢ (g ∘ʳ f) (proj₁ r′ , proj₁ r) (k (proj₂ r′)))
∘ʳ-run g f s t a k =
      bindˣ (bindˣ (onR-pt (MC.step f) s t a) ⟨≈⟩ bind-map (MC.step f (t , a)) _ (MC.onL (MC.step g)))
  ⟨≈⟩ >>=ₚ-assoc (MC.step f (t , a)) _ _
  ⟨≈⟩ bindᶠ λ r → bindˣ (onL-pt (MC.step g) s (proj₁ r) (proj₂ r))
                ⟨≈⟩ bind-map (MC.step g (s , proj₂ r)) _ _

------------------------------------------------------------------------
-- A machine beside the hole

module _ (g : MC.Machine C D) where

  besideˡ : MC.St g → Strat (A ⊎ C) (B ⊎ D) → Bool → ℕ → Strat A B
  besideˡ s (out c)          b n = out c
  besideˡ s (coin μ k)       b n = coin μ λ c → besideˡ s (k c) b n
  besideˡ s (ask (inj₁ a) k) b n = ask a λ y → besideˡ s (k (inj₁ y)) b n
  besideˡ s (ask (inj₂ c) k) b n =
    unfoldˢ n (not b) (MC.step g (s , c)) λ r → besideˡ (proj₁ r) (k (inj₂ (proj₂ r))) b n

  module _ (f : MC.Machine A B) (b : Bool) where
    open Approximation b

    besideˡ-approx : (d : Strat (A ⊎ C) (B ⊎ D)) (t : MC.St f) (s : MC.St g)
                   → Approx (λ n → runFromˢ f t (besideˡ s d b n)) (runFromˢ (f ⊗ᵉ g) (t , s) d)
    besideˡ-approx (out c)          t s = approx-ret c
    besideˡ-approx (coin μ k)       t s = approx-bind (coinₚ μ) λ c → besideˡ-approx (k c) t s
    besideˡ-approx (ask (inj₁ a) k) t s =
      approx-≈ (approx-bind (MC.step f (t , a)) λ r → besideˡ-approx (k (inj₁ (proj₂ r))) (proj₁ r) s)
               (≈sym (⊗-run₁ f g t s a k))
    besideˡ-approx (ask (inj₂ c) k) t s =
      approx-≈ (approx-unfold f t (λ n r → besideˡ (proj₁ r) (k (inj₂ (proj₂ r))) b n)
                              (λ r → runFromˢ (f ⊗ᵉ g) (t , proj₁ r) (k (inj₂ (proj₂ r))))
                              (λ r → besideˡ-approx (k (inj₂ (proj₂ r))) t (proj₁ r))
                              (MC.step g (s , c)))
               (≈sym (⊗-run₂ f g t s c k))

  ⊗ᵉ-absorbˡ : Absorbs {A} {B} (_⊗ᵉ g)
  ⊗ᵉ-absorbˡ = approx⇒absorbs (λ d b n → unfoldˢ n (not b) (MC.point (MC.state g) tt) λ s → besideˡ s d b n)
    λ f d b → let open Approximation b in
      approx-≈ (approx-bind (MC.point (MC.state f) tt) λ t →
                  approx-unfold f t (λ n s → besideˡ s d b n) (λ s → runFromˢ (f ⊗ᵉ g) (t , s) d)
                                (λ s → besideˡ-approx f b d t s) (MC.point (MC.state g) tt))
               (≈sym (runˢ-⊛ (MC.state f) (MC.state g) _ d))

module _ (h : MC.Machine C D) where

  besideʳ : MC.St h → Strat (C ⊎ A) (D ⊎ B) → Bool → ℕ → Strat A B
  besideʳ s (out c)          b n = out c
  besideʳ s (coin μ k)       b n = coin μ λ c → besideʳ s (k c) b n
  besideʳ s (ask (inj₁ c) k) b n =
    unfoldˢ n (not b) (MC.step h (s , c)) λ r → besideʳ (proj₁ r) (k (inj₁ (proj₂ r))) b n
  besideʳ s (ask (inj₂ a) k) b n = ask a λ y → besideʳ s (k (inj₂ y)) b n

  module _ (f : MC.Machine A B) (b : Bool) where
    open Approximation b

    besideʳ-approx : (d : Strat (C ⊎ A) (D ⊎ B)) (t : MC.St f) (s : MC.St h)
                   → Approx (λ n → runFromˢ f t (besideʳ s d b n)) (runFromˢ (h ⊗ᵉ f) (s , t) d)
    besideʳ-approx (out c)          t s = approx-ret c
    besideʳ-approx (coin μ k)       t s = approx-bind (coinₚ μ) λ c → besideʳ-approx (k c) t s
    besideʳ-approx (ask (inj₁ c) k) t s =
      approx-≈ (approx-unfold f t (λ n r → besideʳ (proj₁ r) (k (inj₁ (proj₂ r))) b n)
                              (λ r → runFromˢ (h ⊗ᵉ f) (proj₁ r , t) (k (inj₁ (proj₂ r))))
                              (λ r → besideʳ-approx (k (inj₁ (proj₂ r))) t (proj₁ r))
                              (MC.step h (s , c)))
               (≈sym (⊗-run₁ h f s t c k))
    besideʳ-approx (ask (inj₂ a) k) t s =
      approx-≈ (approx-bind (MC.step f (t , a)) λ r → besideʳ-approx (k (inj₂ (proj₂ r))) (proj₁ r) s)
               (≈sym (⊗-run₂ h f s t a k))

  ⊗ᵉ-absorbʳ : Absorbs {A} {B} (h ⊗ᵉ_)
  ⊗ᵉ-absorbʳ = approx⇒absorbs (λ d b n → unfoldˢ n (not b) (MC.point (MC.state h) tt) λ s → besideʳ s d b n)
    λ f d b → let open Approximation b in
      approx-≈ (approx-bind (MC.point (MC.state f) tt) λ t →
                  approx-unfold f t (λ n s → besideʳ s d b n) (λ s → runFromˢ (h ⊗ᵉ f) (s , t) d)
                                (λ s → besideʳ-approx f b d t s) (MC.point (MC.state h) tt))
               (≈sym (runˢ-⊛ (MC.state h) (MC.state f) _ d
                      ⟨≈⟩ >>=ₚ-swap (MC.point (MC.state h) tt) (MC.point (MC.state f) tt) _))

------------------------------------------------------------------------
-- A machine after or before the hole

module _ (h : MC.Machine B C) where

  after : MC.St h → Strat A C → Bool → ℕ → Strat A B
  after s (out c)    b n = out c
  after s (coin μ k) b n = coin μ λ c → after s (k c) b n
  after s (ask a k)  b n = ask a λ y → unfoldˢ n (not b) (MC.step h (s , y)) λ r → after (proj₁ r) (k (proj₂ r)) b n

  module _ (f : MC.Machine A B) (b : Bool) where
    open Approximation b

    after-approx : (d : Strat A C) (s : MC.St h) (t : MC.St f)
                 → Approx (λ n → runFromˢ f t (after s d b n)) (runFromˢ (h ∘ʳ f) (s , t) d)
    after-approx (out c)    s t = approx-ret c
    after-approx (coin μ k) s t = approx-bind (coinₚ μ) λ c → after-approx (k c) s t
    after-approx (ask a k)  s t =
      approx-≈ (approx-bind (MC.step f (t , a)) λ r →
                  approx-unfold f (proj₁ r) (λ n r′ → after (proj₁ r′) (k (proj₂ r′)) b n)
                                (λ r′ → runFromˢ (h ∘ʳ f) (proj₁ r′ , proj₁ r) (k (proj₂ r′)))
                                (λ r′ → after-approx (k (proj₂ r′)) (proj₁ r′) (proj₁ r))
                                (MC.step h (s , proj₂ r)))
               (≈sym (∘ʳ-run h f s t a k))

  ∘ᴹ-absorbʳ : Absorbs {A} {B} (h MC.∘ᴹ_)
  ∘ᴹ-absorbʳ = absorbs-≈ᴹ (∘ʳ≈∘ᴹ h) (approx⇒absorbs
    (λ d b n → unfoldˢ n (not b) (MC.point (MC.state h) tt) λ s → after s d b n)
    λ f d b → let open Approximation b in
      approx-≈ (approx-bind (MC.point (MC.state f) tt) λ t →
                  approx-unfold f t (λ n s → after s d b n) (λ s → runFromˢ (h ∘ʳ f) (s , t) d)
                                (λ s → after-approx f b d s t) (MC.point (MC.state h) tt))
               (≈sym (runˢ-⊛ (MC.state h) (MC.state f) _ d
                      ⟨≈⟩ >>=ₚ-swap (MC.point (MC.state h) tt) (MC.point (MC.state f) tt) _)))

module _ (h : MC.Machine A B) where

  before : MC.St h → Strat A C → Bool → ℕ → Strat B C
  before s (out c)    b n = out c
  before s (coin μ k) b n = coin μ λ c → before s (k c) b n
  before s (ask a k)  b n = unfoldˢ n (not b) (MC.step h (s , a)) λ r → ask (proj₂ r) λ y → before (proj₁ r) (k y) b n

  module _ (f : MC.Machine B C) (b : Bool) where
    open Approximation b

    before-approx : (d : Strat A C) (t : MC.St f) (s : MC.St h)
                  → Approx (λ n → runFromˢ f t (before s d b n)) (runFromˢ (f ∘ʳ h) (t , s) d)
    before-approx (out c)    t s = approx-ret c
    before-approx (coin μ k) t s = approx-bind (coinₚ μ) λ c → before-approx (k c) t s
    before-approx (ask a k)  t s =
      approx-≈ (approx-unfold f t (λ n r → ask (proj₂ r) λ y → before (proj₁ r) (k y) b n)
                              (λ r → MC.step f (t , proj₂ r) >>=ₚ λ r′ →
                                       runFromˢ (f ∘ʳ h) (proj₁ r′ , proj₁ r) (k (proj₂ r′)))
                              (λ r → approx-bind (MC.step f (t , proj₂ r)) λ r′ →
                                       before-approx (k (proj₂ r′)) (proj₁ r′) (proj₁ r))
                              (MC.step h (s , a)))
               (≈sym (∘ʳ-run f h t s a k))

  ∘ᴹ-absorbˡ : Absorbs {B} {C} (MC._∘ᴹ h)
  ∘ᴹ-absorbˡ = absorbs-≈ᴹ (λ f → ∘ʳ≈∘ᴹ f h) (approx⇒absorbs
    (λ d b n → unfoldˢ n (not b) (MC.point (MC.state h) tt) λ s → before s d b n)
    λ f d b → let open Approximation b in
      approx-≈ (approx-bind (MC.point (MC.state f) tt) λ t →
                  approx-unfold f t (λ n s → before s d b n) (λ s → runFromˢ (f ∘ʳ h) (t , s) d)
                                (λ s → before-approx f b d t s) (MC.point (MC.state h) tt))
               (≈sym (runˢ-⊛ (MC.state f) (MC.state h) _ d)))

------------------------------------------------------------------------
-- The G construction's composite and tensor

-- Every object implicit is passed, as at `UC.Machine.𝒫ᴵ`: inferring one asks
-- Agda to invert a G-hom.
module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set} where

  private
    around : {K : MC.Machine X Y → MC.Machine ((B⁺ ⊎ C⁻) ⊎ (A⁺ ⊎ B⁻)) ((B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺))}
           → Absorbs K
           → Absorbs (λ x → Col.MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                              (Col.W.α {A⁻} {B⁺} {B⁻} {C⁺} MC.∘ᴹ (K x MC.∘ᴹ Col.W.γ {A⁺} {B⁺} {B⁻} {C⁻})))
    around 𝔸 = absorbs-∘ traceᴹ-absorb (absorbs-∘ (∘ᴹ-absorbʳ Col.W.α) (absorbs-∘ (∘ᴹ-absorbˡ Col.W.γ) 𝔸))

  ∘ᴳ-absorbˡ : (g : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
             → Absorbs {B⁺ ⊎ C⁻} {B⁻ ⊎ C⁺} {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺}
                       (λ x → 𝔾._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} x g)
  ∘ᴳ-absorbˡ g =
    absorbs-≈ᴹ (λ x → Col.compose-raw≈∘ᴳ {A⁺} {A⁻} {B⁺} {B⁻} {C⁺} {C⁻} x g) (around (⊗ᵉ-absorbˡ g))

  ∘ᴳ-absorbʳ : (f : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺))
             → Absorbs {A⁺ ⊎ B⁻} {A⁻ ⊎ B⁺} {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺}
                       (λ x → 𝔾._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} f x)
  ∘ᴳ-absorbʳ f =
    absorbs-≈ᴹ (Col.compose-raw≈∘ᴳ {A⁺} {A⁻} {B⁺} {B⁻} {C⁺} {C⁻} f) (around (⊗ᵉ-absorbʳ f))

  composeᴳ-resp-≈ᴿ : {f h : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)} {g i : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)}
                   → f ≈ᴿ h → g ≈ᴿ i
                   → _≈ᴿ_ {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺} (𝔾._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} f g)
                                              (𝔾._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} h i)
  composeᴳ-resp-≈ᴿ {f} {h} {g} {i} f∼h g∼i =
    ≈ᴿ.trans (absorbs⇒resp (∘ᴳ-absorbˡ g) f∼h) (absorbs⇒resp (∘ᴳ-absorbʳ h) g∼i)
    where module ≈ᴿ = Structures.IsEquivalence (≈ᴿ-isEquivalence {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺})

opaque
  unfolding midᴹ GM._⊗₁ᴳ_

  ⊗₁ᴳ-raw : {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ D⁺ D⁻ : Set}
            (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : MC.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
          → (midᴹ {A⁻} {B⁺} {C⁻} {D⁺} MC.∘ᴹ ((f ⊗ᵉ g) MC.∘ᴹ midᴹ {A⁺} {C⁺} {B⁻} {D⁻}))
            MS.≈ᴹ 𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f g
  ⊗₁ᴳ-raw f g = MS.reflᴹ

module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ D⁺ D⁻ : Set} where

  private
    conj : {K : MC.Machine X Y → MC.Machine ((A⁺ ⊎ B⁻) ⊎ (C⁺ ⊎ D⁻)) ((A⁻ ⊎ B⁺) ⊎ (C⁻ ⊎ D⁺))}
         → Absorbs K
         → Absorbs (λ x → midᴹ {A⁻} {B⁺} {C⁻} {D⁺} MC.∘ᴹ (K x MC.∘ᴹ midᴹ {A⁺} {C⁺} {B⁻} {D⁻}))
    conj 𝔸 = absorbs-∘ (∘ᴹ-absorbʳ midᴹ) (absorbs-∘ (∘ᴹ-absorbˡ midᴹ) 𝔸)

  ⊗₁ᴳ-absorbˡ : (g : MC.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
              → Absorbs {A⁺ ⊎ B⁻} {A⁻ ⊎ B⁺} {(A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ D⁻)} {(A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ D⁺)}
                        (λ x → 𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} x g)
  ⊗₁ᴳ-absorbˡ g = absorbs-≈ᴹ (λ x → ⊗₁ᴳ-raw x g) (conj (⊗ᵉ-absorbˡ g))

  ⊗₁ᴳ-absorbʳ : (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
              → Absorbs {C⁺ ⊎ D⁻} {C⁻ ⊎ D⁺} {(A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ D⁻)} {(A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ D⁺)}
                        (λ x → 𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f x)
  ⊗₁ᴳ-absorbʳ f = absorbs-≈ᴹ (⊗₁ᴳ-raw f) (conj (⊗ᵉ-absorbʳ f))

  ⊗₁ᴳ-resp-≈ᴿ : {f h : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)} {g i : MC.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺)}
              → f ≈ᴿ h → g ≈ᴿ i
              → _≈ᴿ_ {(A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ D⁻)} {(A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ D⁺)}
                     (𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f g)
                     (𝔾._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} h i)
  ⊗₁ᴳ-resp-≈ᴿ {f} {h} {g} {i} f∼h g∼i =
    ≈ᴿ.trans (absorbs⇒resp (⊗₁ᴳ-absorbˡ g) f∼h) (absorbs⇒resp (⊗₁ᴳ-absorbʳ h) g∼i)
    where
    module ≈ᴿ = Structures.IsEquivalence
                  (≈ᴿ-isEquivalence {(A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ D⁻)} {(A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ D⁺)})
