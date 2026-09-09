{-# OPTIONS --safe --without-K --guardedness #-}

-- A G-composite of two machines as ONE traced machine with a readable step.
--
-- `𝒢ₚ` hands `g ∘ f` over as `trace (α ∘ (g ⊗ᵉ f) ∘ γ)`, two structural legs
-- around the interface tensor.  Both legs are pure — every factor of
-- `Categories.GConstructionTrace`'s `α`/`γ` is an associator or a braiding — so
-- `pure-∘ˡ`/`pure-∘ʳ` fold them into the tensor's own step, and what survives is
-- `kᴳ`: a four-way dispatch sending each letter to the factor that owns it and
-- routing that factor's emission out or around the loop.  Any consumer that has
-- to read a `𝒢ₚ`-composite's step off starts here.
--
-- Everything here stays inside `ℳₚ` and measures 16 s warm.  `collapseᵀ` is
-- stated as a trace rather than as `𝒢ₚ`'s `_∘_` on purpose: a consumer's goal
-- names `_∘_` already, so leaving the projection out of the G-construction
-- record to the consumer costs ONE such projection, while a lemma stated with
-- `_∘_` costs the consumer a second one — measured at 269 s against 704 s
-- (`Protocol.Machine.Compose`) and 282 s against 507 s (`UC.Seam.Adequacy.
-- Wiring`).
-- Composition congruence sits against the same conversion boundary and is
-- isolated in `Collapse.Congruence` (about 10 s), so it is paid only by clients
-- that transport a composite equality.  Opaque machine composition keeps
-- that boundary nominal instead of eta-expanding both composite records.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Monoidal.Distributive as MD
import Categories.GConstructionTrace as GT

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; swap)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map) renaming (swap to ⊎swap)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as TraceCong

module CategoricalCrypto.Machines.Collapse where

module MC  = Core (𝒱ₚ 0ℓ)
module MT  = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
module S   = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
module TC  = TraceCong (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

module Cat = MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
module T   = Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
module V   = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
module ℳ   = SymmetricMonoidalCategory (ℳₚ 0ℓ)
module W   = GT ℳ.U ℳ.monoidal (Tracedₚ 0ℓ)
module D   = MD.MonoidalDistributive (distₚ 0ℓ)
module K   = KD (Dₚ-DiscreteMonad {0ℓ})
module CK  = CE V.U D.cocartesian

private
  variable P Q X Y Z X′ Y′ : Set

------------------------------------------------------------------------
-- The base's structural morphisms, as functions

⊗-pure : (h : X → Y) (p : Z × X) → (V.id V.⊗₁ K.pureᵏ h) p ≈ₚ returnₚ (proj₁ p , h (proj₂ p))
⊗-pure h p = >>=ₚ-identityˡ (proj₁ p) _ ⟨≈⟩ >>=ₚ-identityˡ (h (proj₂ p)) _

-- The state-side mirror: the shape every `_≲_`'s `θ ⊗₁ id` takes at a point.
⊗-pureˡ : (h : X → Y) (p : X × Z) → (K.pureᵏ h V.⊗₁ V.id) p ≈ₚ returnₚ (h (proj₁ p) , proj₂ p)
⊗-pureˡ h p = >>=ₚ-identityˡ (h (proj₁ p)) _ ⟨≈⟩ >>=ₚ-identityˡ (proj₂ p) _

α+⇒-fn : (x : (X ⊎ Y) ⊎ Z) → CK.α+⇒ x ≈ₚ returnₚ (⊎assocʳ x)
α+⇒-fn (inj₁ (inj₁ a)) = push CK.α+⇒ (inj₁ (inj₁ a))
                       ⟨≈⟩ bindˣ (push (K.pureᵏ inj₁) (inj₁ a)) ⟨≈⟩ CK.α+⇒-i₁i₁ a
α+⇒-fn (inj₁ (inj₂ b)) = push CK.α+⇒ (inj₁ (inj₂ b))
                       ⟨≈⟩ bindˣ (push (K.pureᵏ inj₁) (inj₂ b)) ⟨≈⟩ CK.α+⇒-i₁i₂ b
                       ⟨≈⟩ >>=ₚ-identityˡ (inj₁ b) (K.pureᵏ inj₂)
α+⇒-fn (inj₂ c)        = push CK.α+⇒ (inj₂ c) ⟨≈⟩ CK.α+⇒-i₂ c
                       ⟨≈⟩ >>=ₚ-identityˡ (inj₂ c) (K.pureᵏ inj₂)

α+⇐-fn : (x : X ⊎ (Y ⊎ Z)) → CK.α+⇐ x ≈ₚ returnₚ (⊎assocˡ x)
α+⇐-fn (inj₁ a)        = push CK.α+⇐ (inj₁ a) ⟨≈⟩ CK.α+⇐-i₁ a
                       ⟨≈⟩ >>=ₚ-identityˡ (inj₁ a) (K.pureᵏ inj₁)
α+⇐-fn (inj₂ (inj₁ b)) = push CK.α+⇐ (inj₂ (inj₁ b))
                       ⟨≈⟩ bindˣ (push (K.pureᵏ inj₂) (inj₁ b)) ⟨≈⟩ CK.α+⇐-i₂i₁ b
                       ⟨≈⟩ >>=ₚ-identityˡ (inj₂ b) (K.pureᵏ inj₁)
α+⇐-fn (inj₂ (inj₂ c)) = push CK.α+⇐ (inj₂ (inj₂ c))
                       ⟨≈⟩ bindˣ (push (K.pureᵏ inj₂) (inj₂ c)) ⟨≈⟩ CK.α+⇐-i₂i₂ c

+-swap-fn : (x : X ⊎ Y) → D.+-swap x ≈ₚ returnₚ (⊎swap x)
+-swap-fn (inj₁ a) = push D.+-swap (inj₁ a) ⟨≈⟩ CK.+-swap-i₁ a
+-swap-fn (inj₂ b) = push D.+-swap (inj₂ b) ⟨≈⟩ CK.+-swap-i₂ b

+₁-fn : (h : X → Y) (k : Z → X′) (x : X ⊎ Z)
      → (K.pureᵏ h D.+₁ K.pureᵏ k) x ≈ₚ returnₚ (map h k x)
+₁-fn h k (inj₁ a) = push (K.pureᵏ h D.+₁ K.pureᵏ k) (inj₁ a) ⟨≈⟩ D.+₁∘i₁ a
                   ⟨≈⟩ >>=ₚ-identityˡ (h a) (K.pureᵏ inj₁)
+₁-fn h k (inj₂ c) = push (K.pureᵏ h D.+₁ K.pureᵏ k) (inj₂ c) ⟨≈⟩ D.+₁∘i₂ c
                   ⟨≈⟩ >>=ₚ-identityˡ (k c) (K.pureᵏ inj₂)

------------------------------------------------------------------------
-- Machines that are functions

pureᶠ : (X → Y) → MC.Machine X Y
pureᶠ h = T.pureᴹ (K.pureᵏ h)

∘ᶠ : {f : MC.Machine X Y} {g : MC.Machine Y Z} {h : X → Y} {k : Y → Z}
   → f S.≈ᴹ pureᶠ h → g S.≈ᴹ pureᶠ k → (g MC.∘ᴹ f) S.≈ᴹ pureᶠ (k ∘′ h)
∘ᶠ {h = h} {k} e₁ e₂ = Cat.∘ᴹ-resp-≈ᴹ e₂ e₁
                S.○ᴹ S.≲⇒≈ᴹ (T.pureᴹ-∘ (K.pureᵏ k) (K.pureᵏ h))
                S.○ᴹ S.≲⇒≈ᴹ (T.pureᴹ-cong (K.pureᵏ-∘ k h))

⊗ᶠ : {f : MC.Machine X Y} {g : MC.Machine Z X′} {h : X → Y} {k : Z → X′}
   → f S.≈ᴹ pureᶠ h → g S.≈ᴹ pureᶠ k → (f T.⊗ᵉ g) S.≈ᴹ pureᶠ (map h k)
⊗ᶠ {h = h} {k} e₁ e₂ = T.⊗ᵉ-resp-≈ᴹ e₁ e₂
                S.○ᴹ S.≲⇒≈ᴹ (T.⊗ᵉ-pureᴹ (K.pureᵏ h) (K.pureᵏ k))
                S.○ᴹ S.≲⇒≈ᴹ (T.pureᴹ-cong (+₁-fn h k))

idᶠ : (X : Set) → MC.idᴹ {X} S.≈ᴹ pureᶠ (λ x → x)
idᶠ _ = S.≲⇒≈ᴹ˘ T.pureᴹ-id

α⇒ᶠ : (X Y Z : Set) → T.α⇒ᴹ {X} {Y} {Z} S.≈ᴹ pureᶠ ⊎assocʳ
α⇒ᶠ _ _ _ = S.≲⇒≈ᴹ (T.pureᴹ-cong α+⇒-fn)

α⇐ᶠ : (X Y Z : Set) → T.α⇐ᴹ {X} {Y} {Z} S.≈ᴹ pureᶠ ⊎assocˡ
α⇐ᶠ _ _ _ = S.≲⇒≈ᴹ (T.pureᴹ-cong α+⇐-fn)

σᶠ : (X Y : Set) → T.σᴹ {X} {Y} S.≈ᴹ pureᶠ ⊎swap
σᶠ _ _ = S.≲⇒≈ᴹ (T.pureᴹ-cong +-swap-fn)

------------------------------------------------------------------------
-- The two structural legs of a G-composite

-- `α` routes the two loop ends together after the factors have acted, `γ` feeds
-- them in; both are the same six-factor shuffle, `γ` with one braiding in front.
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

α-pure : (P Q R N : Set) → W.α {R} {N} {P} {Q} S.≈ᴹ pureᶠ (αᶠ {P} {Q} {R} {N})
α-pure P Q R N =
  ∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (α⇒ᶠ P Q (R ⊎ N)) (⊗ᶠ (idᶠ P) (α⇐ᶠ Q R N)))
                 (⊗ᶠ (idᶠ P) (⊗ᶠ (σᶠ Q R) (idᶠ N))))
             (α⇐ᶠ P (R ⊎ Q) N))
         (⊗ᶠ (σᶠ P (R ⊎ Q)) (idᶠ N)))
     (α⇒ᶠ (R ⊎ Q) P N)
  S.○ᴹ S.≲⇒≈ᴹ (T.pureᴹ-cong (K.pureᵏ-cong (λ where
    (inj₁ (inj₁ _)) → refl
    (inj₁ (inj₂ _)) → refl
    (inj₂ (inj₁ _)) → refl
    (inj₂ (inj₂ _)) → refl)))

γ-pure : (P Q R N : Set) → W.γ {P} {N} {R} {Q} S.≈ᴹ pureᶠ (γᶠ {P} {Q} {R} {N})
γ-pure P Q R N =
  ∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (∘ᶠ (⊗ᶠ (idᶠ (P ⊎ Q)) (σᶠ R N)) (α⇒ᶠ P Q (N ⊎ R)))
                     (⊗ᶠ (idᶠ P) (α⇐ᶠ Q N R)))
                 (⊗ᶠ (idᶠ P) (⊗ᶠ (σᶠ Q N) (idᶠ R))))
             (α⇐ᶠ P (N ⊎ Q) R))
         (⊗ᶠ (σᶠ P (N ⊎ Q)) (idᶠ R)))
     (α⇒ᶠ (N ⊎ Q) P R)
  S.○ᴹ S.≲⇒≈ᴹ (T.pureᴹ-cong (K.pureᵏ-cong (λ where
    (inj₁ (inj₁ _)) → refl
    (inj₁ (inj₂ _)) → refl
    (inj₂ (inj₁ _)) → refl
    (inj₂ (inj₂ _)) → refl)))

------------------------------------------------------------------------
-- The state actions and the interface tensor, at a point

swp-pt : (p : P) (q : Q) (x : X) → MC.swp ((p , q) , x) ≈ₚ returnₚ ((p , x) , q)
swp-pt p q x =
  bindˣ (>>=ₚ-identityˡ (p , q , x) _ ⟨≈⟩ ⊗-pure swap (p , q , x))
  ⟨≈⟩ >>=ₚ-identityˡ (p , x , q) _

onL-pt : (k : P × X → Dₚ (P × Y)) (p : P) (q : Q) (x : X)
       → MC.onL {Q = Q} k ((p , q) , x)
       ≈ₚ (k (p , x) >>=ₚ λ r → returnₚ ((proj₁ r , q) , proj₂ r))
onL-pt k p q x =
  bindˣ (bindˣ (swp-pt p q x) ⟨≈⟩ >>=ₚ-identityˡ ((p , x) , q) _
         ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ q _))
  ⟨≈⟩ >>=ₚ-assoc (k (p , x)) _ _
  ⟨≈⟩ bindᶠ (λ where (p′ , y) → >>=ₚ-identityˡ ((p′ , y) , q) _ ⟨≈⟩ swp-pt p′ y q)

onR-pt : (k : Q × X → Dₚ (Q × Y)) (p : P) (q : Q) (x : X)
       → MC.onR {P = P} k ((p , q) , x)
       ≈ₚ (k (q , x) >>=ₚ λ r → returnₚ ((p , proj₁ r) , proj₂ r))
onR-pt k p q x =
  bindˣ (>>=ₚ-identityˡ (p , q , x) _ ⟨≈⟩ >>=ₚ-identityˡ p _)
  ⟨≈⟩ >>=ₚ-assoc (k (q , x)) _ _
  ⟨≈⟩ bindᶠ (λ where (q′ , y) → >>=ₚ-identityˡ (p , q′ , y) _)

tstepL : (k : P × X → Dₚ (P × Y)) (l : P × Z → Dₚ (P × X′)) (s : P) (x : X)
       → T.tstep k l (s , inj₁ x)
       ≈ₚ (k (s , x) >>=ₚ λ r → returnₚ (proj₁ r , inj₁ (proj₂ r)))
tstepL k l s x =
  ≈sym (bindˣ (⊗-pure inj₁ (s , x)) ⟨≈⟩ >>=ₚ-identityˡ (s , inj₁ x) (T.tstep k l))
  ⟨≈⟩ T.tstep-i₁ {k = k} {l} (s , x) ⟨≈⟩ bindᶠ (⊗-pure inj₁)

tstepR : (k : P × X → Dₚ (P × Y)) (l : P × Z → Dₚ (P × X′)) (s : P) (x : Z)
       → T.tstep k l (s , inj₂ x)
       ≈ₚ (l (s , x) >>=ₚ λ r → returnₚ (proj₁ r , inj₂ (proj₂ r)))
tstepR k l s x =
  ≈sym (bindˣ (⊗-pure inj₂ (s , x)) ⟨≈⟩ >>=ₚ-identityˡ (s , inj₂ x) (T.tstep k l))
  ⟨≈⟩ T.tstep-i₂ {k = k} {l} (s , x) ⟨≈⟩ bindᶠ (⊗-pure inj₂)

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

  Sᴳ : MC.State
  Sᴳ = MC.state g MC.⊛ MC.state f

  -- One pass of the composite: each letter goes to the factor that owns it.
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
      bindˣ ( tstepL (MC.onL (MC.step g)) (MC.onR (MC.step f)) (sg , sf) y
            ⟨≈⟩ bindˣ (onL-pt (MC.step g) sg sf y)
            ⟨≈⟩ >>=ₚ-assoc (MC.step g (sg , y)) _ _
            ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , sf) , proj₂ r) _))
      ⟨≈⟩ >>=ₚ-assoc (MC.step g (sg , y)) _ _
      ⟨≈⟩ bindᶠ (λ where
            (sg′ , inj₁ b) → >>=ₚ-identityˡ ((sg′ , sf) , inj₁ (inj₁ b)) _
                           ⟨≈⟩ ⊗-pure â ((sg′ , sf) , inj₁ (inj₁ b))
            (sg′ , inj₂ c) → >>=ₚ-identityˡ ((sg′ , sf) , inj₁ (inj₂ c)) _
                           ⟨≈⟩ ⊗-pure â ((sg′ , sf) , inj₁ (inj₂ c)))

    onRcase : (sg : MC.St g) (sf : MC.St f) (z : A⁺ ⊎ B⁻)
            → (tw ((sg , sf) , inj₂ z) >>=ₚ (V.id V.⊗₁ K.pureᵏ â))
            ≈ₚ (MC.step f (sf , z) >>=ₚ λ r → returnₚ ((sg , proj₁ r) , outᶠ (proj₂ r)))
    onRcase sg sf z =
      bindˣ ( tstepR (MC.onL (MC.step g)) (MC.onR (MC.step f)) (sg , sf) z
            ⟨≈⟩ bindˣ (onR-pt (MC.step f) sg sf z)
            ⟨≈⟩ >>=ₚ-assoc (MC.step f (sf , z)) _ _
            ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((sg , proj₁ r) , proj₂ r) _))
      ⟨≈⟩ >>=ₚ-assoc (MC.step f (sf , z)) _ _
      ⟨≈⟩ bindᶠ (λ where
            (sf′ , inj₁ a) → >>=ₚ-identityˡ ((sg , sf′) , inj₂ (inj₁ a)) _
                           ⟨≈⟩ ⊗-pure â ((sg , sf′) , inj₂ (inj₁ a))
            (sf′ , inj₂ b) → >>=ₚ-identityˡ ((sg , sf′) , inj₂ (inj₂ b)) _
                           ⟨≈⟩ ⊗-pure â ((sg , sf′) , inj₂ (inj₂ b)))

    stepEq : (z : MC.obj Sᴳ × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)))
           → ((V.id V.⊗₁ K.pureᵏ â) V.∘ (tw V.∘ (V.id V.⊗₁ K.pureᵏ ĉ))) z ≈ₚ kᴳ z
    stepEq ((sg , sf) , inj₁ (inj₁ a)) =
      bindˣ ( bindˣ (⊗-pure ĉ ((sg , sf) , inj₁ (inj₁ a)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₂ (inj₁ a)) tw)
      ⟨≈⟩ onRcase sg sf (inj₁ a)
    stepEq ((sg , sf) , inj₁ (inj₂ c)) =
      bindˣ ( bindˣ (⊗-pure ĉ ((sg , sf) , inj₁ (inj₂ c)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₁ (inj₂ c)) tw)
      ⟨≈⟩ onLcase sg sf (inj₂ c)
    stepEq ((sg , sf) , inj₂ (inj₁ b)) =
      bindˣ ( bindˣ (⊗-pure ĉ ((sg , sf) , inj₂ (inj₁ b)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₂ (inj₂ b)) tw)
      ⟨≈⟩ onRcase sg sf (inj₂ b)
    stepEq ((sg , sf) , inj₂ (inj₂ b)) =
      bindˣ ( bindˣ (⊗-pure ĉ ((sg , sf) , inj₂ (inj₂ b)))
            ⟨≈⟩ >>=ₚ-identityˡ ((sg , sf) , inj₁ (inj₁ b)) tw)
      ⟨≈⟩ onLcase sg sf (inj₁ b)

    inner : ((g T.⊗ᵉ f) MC.∘ᴹ W.γ {A⁺} {B⁺} {B⁻} {C⁻}) S.≈ᴹ mid
    inner = Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ (γ-pure A⁺ C⁻ B⁻ B⁺)
       S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ʳ (K.pureᵏ ĉ) (g T.⊗ᵉ f))

  -- The machine `𝒢ₚ`'s composite is a trace OF, with both legs absorbed.
  outer : (W.α {A⁻} {B⁺} {B⁻} {C⁺} MC.∘ᴹ
            ((g T.⊗ᵉ f) MC.∘ᴹ W.γ {A⁺} {B⁺} {B⁻} {C⁻}))
          S.≈ᴹ MC.mk Sᴳ kᴳ
  outer = Cat.∘ᴹ-resp-≈ᴹ (α-pure B⁻ C⁺ A⁻ B⁺) inner
     S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ˡ (K.pureᵏ â) mid)
     S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong stepEq)

  -- The same, traced: this is `𝒢ₚ`'s composite, up to the projection out of the
  -- G-construction record that the consumer's own goal already performs (see
  -- the header).
  collapseᵀ : MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                (W.α {A⁻} {B⁺} {B⁻} {C⁺} MC.∘ᴹ
                  ((g T.⊗ᵉ f) MC.∘ᴹ W.γ {A⁺} {B⁺} {B⁻} {C⁻}))
              S.≈ᴹ MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (MC.mk Sᴳ kᴳ)
  collapseᵀ = TC.trace-resp-≈ᴹ {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺} {B⁻ ⊎ B⁺} outer
