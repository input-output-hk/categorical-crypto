{-# OPTIONS --safe --without-K --guardedness #-}

-- The `Kl(Dₚ)` point-level calculus the machine layer reads its steps with:
-- the base's structural morphisms as functions on sums, the machines that ARE
-- functions (`pureᶠ` and its four congruences), and the state actions and the
-- interface tensor evaluated at a point.
--
-- Nothing here mentions a G-composite; `Machines.Collapse` is the one consumer
-- that does, and it is not the only one — `Examples.MerkleDamgard.QueryBound`
-- needs `⊗-pureˡ` alone and pays nothing for the trace.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP
import Categories.Category.Monoidal.Distributive as MD

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; swap)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map) renaming (swap to ⊎swap)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.Machines.Pointwise where

module MC  = Core (𝒱ₚ 0ℓ)
module S   = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

module Cat = MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
module T   = Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
module V   = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
module D   = MD.MonoidalDistributive (distₚ 0ℓ)
module K   = KD (Dₚ-DiscreteMonad {0ℓ})
module KP  = KDP (Dₚ-DiscreteMonad {0ℓ})
module CK  = CE V.U D.cocartesian

private
  variable P Q X Y Z X′ : Set

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

-- …and a simulation out of one: `⊗-pureˡ` above names the shape every `_≲_`'s
-- `θ ⊗₁ id` takes at a point, so a consumer supplies only the three pointwise
-- laws.
simFn : {S T : MC.State} {k : MC.obj S × X → Dₚ (MC.obj S × Y)}
        {k′ : MC.obj T × X → Dₚ (MC.obj T × Y)} (h : MC.obj S → MC.obj T)
      → ((s : MC.obj S) → (returnₚ (h s) >>=ₚ MC.discard T) ≈ₚ MC.discard S s)
      → ((x : V.unit) → (MC.point S x >>=ₚ λ s → returnₚ (h s)) ≈ₚ MC.point T x)
      → ((p : MC.obj S × X) → (k p >>=ₚ λ r → returnₚ (h (proj₁ r) , proj₂ r))
                              ≈ₚ k′ (h (proj₁ p) , proj₂ p))
      → MC.mk S k S.≲ MC.mk T k′
simFn {k′ = k′} h hd hp hs = S.sim (K.pureᵏ h) (KP.structural h) hd hp law
  where
  law : (p : _) → _
  law p = bindᶠ (⊗-pureˡ h) ⟨≈⟩ hs p
    ⟨≈⟩ ≈sym (bindˣ (⊗-pureˡ h p) ⟨≈⟩ >>=ₚ-identityˡ (h (proj₁ p) , proj₂ p) k′)

------------------------------------------------------------------------
-- The state actions and the interface tensor, at a point

-- The state tensor's own point and discard, which is what `UC.Seam.Plug`'s
-- `point-red` reduces at an arbitrary pair of states.
point-⊛ : (S T : MC.State) (x : V.unit)
        → MC.point (S MC.⊛ T) x
        ≈ₚ (MC.point S ttᵛ >>=ₚ λ a → MC.point T x >>=ₚ λ b → returnₚ (a , b))
point-⊛ S T x = >>=ₚ-identityˡ (ttᵛ , x) _

discard-⊛ : (S T : MC.State)
          → ((s : MC.obj S) → MC.discard S s ≈ₚ returnₚ ttᵛ)
          → ((t : MC.obj T) → MC.discard T t ≈ₚ returnₚ ttᵛ)
          → (z : MC.obj (S MC.⊛ T)) → MC.discard (S MC.⊛ T) z ≈ₚ returnₚ ttᵛ
discard-⊛ S T hs ht (a , b) =
  bindˣ ( bindˣ (hs a) ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _
     ⟨≈⟩ bindˣ (ht b) ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _)
  ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

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
