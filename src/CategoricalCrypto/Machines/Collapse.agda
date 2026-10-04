{-# OPTIONS --safe --without-K --guardedness #-}

-- A G-composite of two machines as ONE traced machine with a readable step.
--
-- `𝒢ₚ` hands `g ∘ f` over as `trace (α ∘ (g ⊗ᵉ f) ∘ γ)`, two structural legs
-- around the interface tensor.  Both legs are pure — every factor of
-- `Categories.GConstructionTrace`'s `α`/`γ` is an associator or a braiding — so
-- `pure-∘ˡ`/`pure-∘ʳ` fold them into the tensor's own step, and what survives is
-- `kᴳ`: a four-way dispatch sending each letter to the factor that owns it and
-- routing that factor's emission out or around the loop.
--
-- `collapseᵀ` is stated as a trace rather than as `𝒢ₚ`'s `_∘_` on purpose: a
-- consumer's goal names `_∘_` already, so leaving the projection out of the
-- G-construction record to the consumer costs ONE such projection, while a
-- lemma stated with `_∘_` costs the consumer a second one.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
import Categories.GConstruction as GC
import Categories.GConstructionTrace as GT

open import Data.Product.Base
open import Data.Sum.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Pure

import CategoricalCrypto.Machines.Trace.Congruence as TraceCong

module CategoricalCrypto.Machines.Collapse where


module TC  = TraceCong (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

module ℳ   = SymmetricMonoidalCategory (ℳₚ 0ℓ)
module W   = GT ℳ.U ℳ.monoidal (Tracedₚ 0ℓ)
module 𝒢   = Category (𝒢ₚ 0ℓ)

private
  variable P Q X Y : Set

------------------------------------------------------------------------
-- The two structural legs of a G-composite

αᶠ : (P ⊎ Q) ⊎ (X ⊎ Y) → (X ⊎ Q) ⊎ (P ⊎ Y)
αᶠ (inj₁ (inj₁ p)) = inj₂ (inj₁ p)
αᶠ (inj₁ (inj₂ q)) = inj₁ (inj₂ q)
αᶠ (inj₂ (inj₁ r)) = inj₁ (inj₁ r)
αᶠ (inj₂ (inj₂ s)) = inj₂ (inj₂ s)

γᶠ : (P ⊎ Q) ⊎ (X ⊎ Y) → (Y ⊎ Q) ⊎ (P ⊎ X)
γᶠ (inj₁ (inj₁ p)) = inj₂ (inj₁ p)
γᶠ (inj₁ (inj₂ q)) = inj₁ (inj₂ q)
γᶠ (inj₂ (inj₁ r)) = inj₂ (inj₂ r)
γᶠ (inj₂ (inj₂ s)) = inj₁ (inj₁ s)

α-pure : (P Q R N : Set) → W.α MS.≈ᴹ pureᶠ (αᶠ)
α-pure P Q R N =
  ∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (α⇒ᶠ P Q (R ⊎ N)) (⊗ᶠ (idᶠ P) (α⇐ᶠ Q R N)))
                 (⊗ᶠ (idᶠ P) (⊗ᶠ (σᶠ Q R) (idᶠ N))))
             (α⇐ᶠ P (R ⊎ Q) N))
         (⊗ᶠ (σᶠ P (R ⊎ Q)) (idᶠ N)))
     (α⇒ᶠ (R ⊎ Q) P N)
  MS.○ᴹ MS.≲⇒≈ᴹ (T.pureᴹ-cong (K.pureᵏ-cong (λ where
    (inj₁ (inj₁ _)) → refl
    (inj₁ (inj₂ _)) → refl
    (inj₂ (inj₁ _)) → refl
    (inj₂ (inj₂ _)) → refl)))

γ-pure : (P Q R N : Set) → W.γ MS.≈ᴹ pureᶠ (γᶠ)
γ-pure P Q R N =
  ∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (⊗ᶠ (idᶠ (P ⊎ Q)) (σᶠ R N)) (α⇒ᶠ P Q (N ⊎ R)))
                     (⊗ᶠ (idᶠ P) (α⇐ᶠ Q N R)))
                 (⊗ᶠ (idᶠ P) (⊗ᶠ (σᶠ Q N) (idᶠ R))))
             (α⇐ᶠ P (N ⊎ Q) R))
         (⊗ᶠ (σᶠ P (N ⊎ Q)) (idᶠ R)))
     (α⇒ᶠ (N ⊎ Q) P R)
  MS.○ᴹ MS.≲⇒≈ᴹ (T.pureᴹ-cong (K.pureᵏ-cong (λ where
    (inj₁ (inj₁ _)) → refl
    (inj₁ (inj₂ _)) → refl
    (inj₂ (inj₁ _)) → refl
    (inj₂ (inj₂ _)) → refl)))

------------------------------------------------------------------------
-- The collapsed step

-- Where each factor's emission goes: the shared interface `B` re-enters the
-- trace's loop, the outer interfaces `A` and `C` leave.
module _ {A⁻ B⁺ B⁻ C⁺ : Set} where

  outᶠ : A⁻ ⊎ B⁺ → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
  outᶠ (inj₁ a) = inj₁ (inj₁ a)
  outᶠ (inj₂ b) = inj₂ (inj₂ b)

  outᵍ : B⁻ ⊎ C⁺ → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
  outᵍ (inj₁ b) = inj₂ (inj₁ b)
  outᵍ (inj₂ c) = inj₁ (inj₂ c)

module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set}
         (g : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) where

  compose-raw≈∘ᴳ : MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                     (W.α MC.∘ᴹ ((g T.⊗ᵉ f) MC.∘ᴹ W.γ))
                   MS.≈ᴹ 𝒢._∘_ g f
  compose-raw≈∘ᴳ = ℳ.Equiv.sym (GC.composeᴳ-raw ℳ.U ℳ.monoidal (Tracedₚ 0ℓ))

  Sᴳ : MC.State
  Sᴳ = MC.state g MC.⊛ MC.state f

  kᴳ : MC.obj Sᴳ × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺))
     → Dₚ (MC.obj Sᴳ × ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)))
  kᴳ ((sg , sf) , inj₁ (inj₁ a)) =
    MC.step f (sf , inj₁ a) >>=ₚ λ r → returnₚ ((sg , proj₁ r) , outᶠ (proj₂ r))
  kᴳ ((sg , sf) , inj₁ (inj₂ c)) =
    MC.step g (sg , inj₂ c) >>=ₚ λ r → returnₚ ((proj₁ r , sf) , outᵍ (proj₂ r))
  kᴳ ((sg , sf) , inj₂ (inj₁ b)) =
    MC.step f (sf , inj₂ b) >>=ₚ λ r → returnₚ ((sg , proj₁ r) , outᶠ (proj₂ r))
  kᴳ ((sg , sf) , inj₂ (inj₂ b)) =
    MC.step g (sg , inj₁ b) >>=ₚ λ r → returnₚ ((proj₁ r , sf) , outᵍ (proj₂ r))

  private
    â : (B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺) → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
    â = αᶠ

    ĉ : (A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺) → (B⁺ ⊎ C⁻) ⊎ (A⁺ ⊎ B⁻)
    ĉ = γᶠ

    tw : MC.obj Sᴳ × ((B⁺ ⊎ C⁻) ⊎ (A⁺ ⊎ B⁻)) → Dₚ (MC.obj Sᴳ × ((B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺)))
    tw = MC.step (g T.⊗ᵉ f)

    mid : MC.Machine ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)) ((B⁻ ⊎ C⁺) ⊎ (A⁻ ⊎ B⁺))
    mid = MC.mk Sᴳ (tw V.∘ (V.id V.⊗₁ K.pureᵏ ĉ))

    -- The outer factor is activated, on a query from `C` or on an answer from
    -- the inner one; either way its emission is routed by `outᵍ`.
    onLcase : (sg : MC.St g) (sf : MC.St f) (y : B⁺ ⊎ C⁻)
            → (tw ((sg , sf) , inj₁ y) >>=ₚ (V.id V.⊗₁ K.pureᵏ â))
            ≈ₚ (MC.step g (sg , y) >>=ₚ λ r → returnₚ ((proj₁ r , sf) , outᵍ (proj₂ r)))
    onLcase sg sf y =
      bindˣ ( tstep-inj₁ (MC.onL (MC.step g)) (MC.onR (MC.step f)) (sg , sf) y
            ⟨≈⟩ bindˣ (onL-pt (MC.step g) sg sf y)
            ⟨≈⟩ >>=ₚ-assoc (MC.step g (sg , y)) _ _
            ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , sf) , proj₂ r) _))
      ⟨≈⟩ >>=ₚ-assoc (MC.step g (sg , y)) _ _
      ⟨≈⟩ bindᶠ (λ where
            (sg′ , inj₁ b) → >>=ₚ-identityˡ ((sg′ , sf) , inj₁ (inj₁ b)) _
                           ⟨≈⟩ pureᴵ â ((sg′ , sf) , inj₁ (inj₁ b))
            (sg′ , inj₂ c) → >>=ₚ-identityˡ ((sg′ , sf) , inj₁ (inj₂ c)) _
                           ⟨≈⟩ pureᴵ â ((sg′ , sf) , inj₁ (inj₂ c)))

    onRcase : (sg : MC.St g) (sf : MC.St f) (z : A⁺ ⊎ B⁻)
            → (tw ((sg , sf) , inj₂ z) >>=ₚ (V.id V.⊗₁ K.pureᵏ â))
            ≈ₚ (MC.step f (sf , z) >>=ₚ λ r → returnₚ ((sg , proj₁ r) , outᶠ (proj₂ r)))
    onRcase sg sf z =
      bindˣ ( tstep-inj₂ (MC.onL (MC.step g)) (MC.onR (MC.step f)) (sg , sf) z
            ⟨≈⟩ bindˣ (onR-pt (MC.step f) sg sf z)
            ⟨≈⟩ >>=ₚ-assoc (MC.step f (sf , z)) _ _
            ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((sg , proj₁ r) , proj₂ r) _))
      ⟨≈⟩ >>=ₚ-assoc (MC.step f (sf , z)) _ _
      ⟨≈⟩ bindᶠ (λ where
            (sf′ , inj₁ a) → >>=ₚ-identityˡ ((sg , sf′) , inj₂ (inj₁ a)) _
                           ⟨≈⟩ pureᴵ â ((sg , sf′) , inj₂ (inj₁ a))
            (sf′ , inj₂ b) → >>=ₚ-identityˡ ((sg , sf′) , inj₂ (inj₂ b)) _
                           ⟨≈⟩ pureᴵ â ((sg , sf′) , inj₂ (inj₂ b)))

    stepEq : (z : MC.obj Sᴳ × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)))
           → ((V.id V.⊗₁ K.pureᵏ â) V.∘ (tw V.∘ (V.id V.⊗₁ K.pureᵏ ĉ))) z ≈ₚ kᴳ z
    stepEq ((sg , sf) , inj₁ (inj₁ a)) =
      bindˣ ( bindˣ (pureᴵ ĉ ((sg , sf) , inj₁ (inj₁ a)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₂ (inj₁ a)) tw)
      ⟨≈⟩ onRcase sg sf (inj₁ a)
    stepEq ((sg , sf) , inj₁ (inj₂ c)) =
      bindˣ ( bindˣ (pureᴵ ĉ ((sg , sf) , inj₁ (inj₂ c)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₁ (inj₂ c)) tw)
      ⟨≈⟩ onLcase sg sf (inj₂ c)
    stepEq ((sg , sf) , inj₂ (inj₁ b)) =
      bindˣ ( bindˣ (pureᴵ ĉ ((sg , sf) , inj₂ (inj₁ b)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₂ (inj₂ b)) tw)
      ⟨≈⟩ onRcase sg sf (inj₂ b)
    stepEq ((sg , sf) , inj₂ (inj₂ b)) =
      bindˣ ( bindˣ (pureᴵ ĉ ((sg , sf) , inj₂ (inj₂ b)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₁ (inj₁ b)) tw)
      ⟨≈⟩ onLcase sg sf (inj₁ b)

    inner : ((g T.⊗ᵉ f) MC.∘ᴹ W.γ) MS.≈ᴹ mid
    inner = Cat.∘ᴹ-resp-≈ᴹ MS.reflᴹ (γ-pure A⁺ C⁻ B⁻ B⁺)
       MS.○ᴹ MS.≲⇒≈ᴹ (T.pure-∘ʳ (K.pureᵏ ĉ) (g T.⊗ᵉ f))

  -- The body of `𝒢ₚ`'s composite, both legs absorbed.
  outer : (W.α MC.∘ᴹ ((g T.⊗ᵉ f) MC.∘ᴹ W.γ)) MS.≈ᴹ MC.mk Sᴳ kᴳ
  outer = Cat.∘ᴹ-resp-≈ᴹ (α-pure B⁻ C⁺ A⁻ B⁺) inner
     MS.○ᴹ MS.≲⇒≈ᴹ (T.pure-∘ˡ (K.pureᵏ â) mid)
     MS.○ᴹ MS.≲⇒≈ᴹ (MS.mk-cong stepEq)

  -- `𝒢ₚ`'s composite, up to the record projection (see the header).
  collapseᵀ : MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                (W.α MC.∘ᴹ
                  ((g T.⊗ᵉ f) MC.∘ᴹ W.γ))
              MS.≈ᴹ MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (MC.mk Sᴳ kᴳ)
  collapseᵀ = TC.trace-resp-≈ᴹ outer

  collapse≈ : MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (MC.mk Sᴳ kᴳ) MS.≈ᴹ 𝒢._∘_ g f
  collapse≈ = MS.⟺ᴹ collapseᵀ MS.○ᴹ compose-raw≈∘ᴳ
