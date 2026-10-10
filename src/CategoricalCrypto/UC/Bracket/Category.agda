{-# OPTIONS --safe --without-K --guardedness #-}

-- Well-bracketed machines compose (`docs/uc-setup-ssp.md` §4.2): `g ⊙ f`,
-- `𝒢ₚ`'s composite collapsed to one traced machine (`Machines.Collapse.kᴳ`)
-- and the same hom as `𝒫ᴵ`'s `g ∘ f` (`⊙≈∘`), is well-bracketed (`⊙-W`).
-- Between activations its invariant is `Σ b. I_g (calling c b) × I_f (calling
-- b a)`; inside one, every letter on the loop finds `g` calling on its channel
-- and `f` idle, which is all a legal environment's single open query leaves
-- possible.  `W` reads the step term itself, which `⊙` and `𝒫ᴵ`'s composite do
-- not share, so the category (`UC.Bracket.Monoidal.𝒲ᴹ`) takes its homs up to
-- the hom equality.

open import Categories.Category

open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter.Supp

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Supp
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Bracket.Category where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

private variable A B C : Iface

------------------------------------------------------------------------
-- Composition

infixr 9 _⊙_

_⊙_ : Proc (flat B) (flat C) → Proc (flat A) (flat B) → Proc (flat A) (flat C)
_⊙_ {B = B} g f = Col.MT.traceᴹ _ _ (Σ (Ch B) (Q B) ⊎ Σ (Ch B) (R B)) (MC.mk (Col.Sᴳ g f) (Col.kᴳ g f))

⊙≈∘ : (g : Proc (flat B) (flat C)) (f : Proc (flat A) (flat B))
    → Category._≈_ 𝒫ᴵ {flat A} {flat C} (_⊙_ {B = B} {C = C} {A = A} g f)
        (Category._∘_ 𝒫ᴵ {flat A} {flat B} {flat C} g f)
⊙≈∘ g f = S.⟺ᴹ (Col.collapseᵀ g f) S.○ᴹ Col.compose-raw≈∘ᴳ g f

module _ {g : Proc (flat B) (flat C)} {f : Proc (flat A) (flat B)} (wg : W {B} {C} g) (wf : W {A} {B} f) where

  private
    module G = W wg
    module F = W wf

    I : MC.St g × MC.St f → Phase A C → Set
    I (sg , sf) idle          = G.I sg idle × F.I sf idle
    I _         (serving _)   = ⊥
    I (sg , sf) (calling c a) = Σ[ b ∈ Ch B ] G.I sg (calling c b) × F.I sf (calling b a)

    J : Ch C → (MC.St g × MC.St f) × (Σ (Ch B) (Q B) ⊎ Σ (Ch B) (R B)) → Set
    J c ((sg , sf) , inj₁ (b , _)) = G.I sg (calling c b) × F.I sf idle
    J c ((sg , sf) , inj₂ (b , _)) = G.I sg (calling c b) × F.I sf idle

    -- A factor's legal move, routed by `kᴳ` out of the composite or round its loop.
    route-g : ∀ {c sf} → F.I sf idle → ∀ r → Legal G.I (serving c) r
            → ∀ j → Supp j (returnₚ ((proj₁ r , sf) , Col.outᵍ (proj₂ r))) (Turn (J c) (Legal I (serving c)))
    route-g if (_ , inj₁ _) (_ , call , ig)   = Supp-return _ _ (ig , if)
    route-g if (_ , inj₂ _) (_ , answer , ig) = Supp-return _ _ (idle , answer , ig , if)

    route-f : ∀ {c b sg} → G.I sg (calling c b) → ∀ r → Legal F.I (serving b) r
            → ∀ j → Supp j (returnₚ ((sg , proj₁ r) , Col.outᶠ (proj₂ r))) (Turn (J c) (Legal I (serving c)))
    route-f ig (_ , inj₁ _) (_ , call , if)   = Supp-return _ _ (calling _ _ , call , _ , ig , if)
    route-f ig (_ , inj₂ _) (_ , answer , if) = Supp-return _ _ (ig , if)

    loop : (c : Ch C) → ∀ {sl} → J c sl → ∀ n
         → Supp n (Col.kᴳ g f (proj₁ sl , inj₂ (proj₂ sl))) (Turn (J c) (Legal I (serving c)))
    loop c {(_ , sf) , inj₁ _} (ig , if) n =
      Supp-bind _ n _ _ (Supp-map _ _ (route-f ig) n _ (F.I-step if query n))
    loop c {(sg , _) , inj₂ _} (ig , if) n =
      Supp-bind _ n _ _ (Supp-map _ _ (route-g if) n _ (G.I-step ig return n))

    I-init : ∀ n → Supp n (MC.point (Col.Sᴳ g f) tt) λ s → I s idle
    I-init n = Supp-bind _ n _ _ (Supp-return _ _ (λ i →
      Supp-bind _ i _ _ (Supp-map _ _ (λ _ ig j →
        Supp-bind _ j _ _ (Supp-map _ _ (λ _ if → Supp-return _ _ (ig , if)) j _ (F.I-init j)))
        i _ (G.I-init i))) n)

    I-step : ∀ {s φ x φ′} → I s φ → Opp φ x φ′ → ∀ n
           → Supp n (MC.step (_⊙_ {B = B} {C = C} {A = A} g f) (s , x)) (Legal I φ′)
    I-step {_ , _} {x = inj₂ (c , _)} (ig , if) query =
      Supp-traced {S = Col.Sᴳ g f} {k = Col.kᴳ g f} (loop c) λ n →
        Supp-bind _ n _ _ (Supp-map _ _ (route-g if) n _ (G.I-step ig query n))
    I-step {_ , _} (_ , ig , if) (return {b = c}) =
      Supp-traced {S = Col.Sᴳ g f} {k = Col.kᴳ g f} (loop c) λ n →
        Supp-bind _ n _ _ (Supp-map _ _ (route-f ig) n _ (F.I-step if return n))

  ⊙-W : W {A} {C} (_⊙_ {B = B} {C = C} {A = A} g f)
  ⊙-W = record { I = I ; I-init = I-init ; I-step = I-step }
