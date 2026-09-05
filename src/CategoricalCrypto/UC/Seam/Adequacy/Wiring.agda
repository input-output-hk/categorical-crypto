{-# OPTIONS --safe --without-K --guardedness #-}

-- The closed G-composite `strategyEnv B d ∘ u` as one machine with a readable
-- step.
--
-- `Adequacy` runs an induction on a `Strat` tree against the composite, so it
-- has to read the composite's step off; the G construction hands the composite
-- over as a trace of `α ∘ (e ⊗ u) ∘ γ`, two structural legs around the
-- interface tensor.  Both legs are pure — every factor of `Categories.
-- GConstructionTrace`'s `α`/`γ` is an associator or a braiding — so
-- `pure-∘ˡ`/`pure-∘ʳ` fold them into the tensor's own step, and what survives is
-- `kᵂ`: the environment's tick, the process's answer, and the environment's
-- answer, dispatched over the traced loop.
--
-- Measured cost: ~240 s warm, ~90% of it `compose-≈ᴹ` alone — projecting `_∘_`
-- out of `𝒢ₚ`'s G-construction record, which any consumer of `𝒫.∘` pays once
-- (`Machines.Base`'s header prices the same record).  Nothing here is on that
-- path: the rest of the module measures under 5 s.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Monoidal.Distributive as MD
import Categories.GConstructionTrace as GT

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; swap)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map) renaming (swap to ⊎swap)
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Seam

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as TraceCong

module CategoricalCrypto.UC.Seam.Adequacy.Wiring where

private
  module MC  = Core (𝒱ₚ 0ℓ)
  module MT  = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module S   = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫   = Category 𝒫ᴵ

  module Cat = MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module T   = Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
  module TC  = TraceCong (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module V   = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module ℳ   = SymmetricMonoidalCategory (ℳₚ 0ℓ)
  module W   = GT ℳ.U ℳ.monoidal (Tracedₚ 0ℓ)
  module D   = MD.MonoidalDistributive (distₚ 0ℓ)
  module K   = KD (Dₚ-DiscreteMonad {0ℓ})
  module CK  = CE V.U D.cocartesian

private
  variable P Q X Y Z X′ Y′ : Set

------------------------------------------------------------------------
-- `Dₚ` shorthands

-- The library's lemmas take their subjects explicitly, so a transparent chain
-- strands them as metas; see `UC.Machine.Run` for the same shorthands.
private
  infixr 5 _⟨≈⟩_

  _⟨≈⟩_ : {d e h : Dₚ X} → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
  _⟨≈⟩_ {d = d} {e} {h} = ≈ₚ-trans d e h

  ≈refl : {d : Dₚ X} → d ≈ₚ d
  ≈refl {d = d} = ≈ₚ-refl d

  ≈sym : {d e : Dₚ X} → d ≈ₚ e → e ≈ₚ d
  ≈sym {d = d} {e} = ≈ₚ-sym d e

  bindᶠ : {d : Dₚ X} {k l : X → Dₚ Y} → ((x : X) → k x ≈ₚ l x) → (d >>=ₚ k) ≈ₚ (d >>=ₚ l)
  bindᶠ {d = d} {k} {l} h = >>=ₚ-cong d d k l ≈refl h

  bindˣ : {d e : Dₚ X} {k : X → Dₚ Y} → d ≈ₚ e → (d >>=ₚ k) ≈ₚ (e >>=ₚ k)
  bindˣ {d = d} {e} {k} h = >>=ₚ-cong d e k k h λ _ → ≈refl

  push : (k : X → Dₚ Y) (x : X) → k x ≈ₚ (returnₚ x >>=ₚ k)
  push k x = ≈sym (>>=ₚ-identityˡ x k)

------------------------------------------------------------------------
-- The base's structural morphisms, as functions

private
  ⊗-pure : (h : X → Y) (p : Z × X) → (V.id V.⊗₁ K.pureᵏ h) p ≈ₚ returnₚ (proj₁ p , h (proj₂ p))
  ⊗-pure h p = >>=ₚ-identityˡ (proj₁ p) _ ⟨≈⟩ >>=ₚ-identityˡ (h (proj₂ p)) _

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

private
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
private
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
-- The collapsed step

module _ (B : Iface) where

  -- Where the environment's two possible emissions go: a query on `B` re-enters
  -- the trace's loop, the verdict leaves on the external interface.
  outE : Neg B ⊎ Bool → (⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)
  outE (inj₁ n) = inj₂ (inj₁ n)
  outE (inj₂ v) = inj₁ (inj₂ v)

  outU : ⊥ ⊎ Pos B → (⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)
  outU (inj₁ e) = ⊥-elim e
  outU (inj₂ p) = inj₂ (inj₂ p)

module _ (B : Iface) (u : Proc unitᴵ B) where

  kᵂ : (EnvSt B × MC.St u) × ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B))
     → Dₚ ((EnvSt B × MC.St u) × ((⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)))
  kᵂ ((se , su) , inj₁ (inj₁ e)) = ⊥-elim e
  kᵂ ((se , su) , inj₁ (inj₂ _)) = stepˢ B (se , inj₂ tt) >>=ₚ λ q → returnₚ ((proj₁ q , su) , outE B (proj₂ q))
  kᵂ ((se , su) , inj₂ (inj₁ n)) = MC.step u (su , inj₂ n) >>=ₚ λ q → returnₚ ((se , proj₁ q) , outU B (proj₂ q))
  kᵂ ((se , su) , inj₂ (inj₂ p)) = stepˢ B (se , inj₁ p) >>=ₚ λ q → returnₚ ((proj₁ q , su) , outE B (proj₂ q))

pairedᴹ : (B : Iface) (d : Strat (Neg B) (Pos B)) (u : Proc unitᴵ B) → Proc unitᴵ Ωᴵ
pairedᴹ B d u = MT.traceᴹ (⊥ ⊎ ⊤) (⊥ ⊎ Bool) (Neg B ⊎ Pos B)
                          (MC.mk (stateˢ B d MC.⊛ MC.state u) (kᵂ B u))

------------------------------------------------------------------------
-- Absorbing both legs into the tensor's step

private
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

private
  module _ (B : Iface) (d : Strat (Neg B) (Pos B)) (u : Proc unitᴵ B) where

    â : (Neg B ⊎ Bool) ⊎ (⊥ ⊎ Pos B) → (⊥ ⊎ Bool) ⊎ (Neg B ⊎ Pos B)
    â = αᶠ

    ĉ : (⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B) → (Pos B ⊎ ⊤) ⊎ (⊥ ⊎ Neg B)
    ĉ = γᶠ

    Se : MC.State
    Se = stateˢ B d MC.⊛ MC.state u

    tw : (EnvSt B × MC.St u) × ((Pos B ⊎ ⊤) ⊎ (⊥ ⊎ Neg B))
       → Dₚ ((EnvSt B × MC.St u) × ((Neg B ⊎ Bool) ⊎ (⊥ ⊎ Pos B)))
    tw = MC.step (strategyEnv B d T.⊗ᵉ u)

    mid : MC.Machine ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B)) ((Neg B ⊎ Bool) ⊎ (⊥ ⊎ Pos B))
    mid = MC.mk Se (tw V.∘ (V.id V.⊗₁ K.pureᵏ ĉ))

    -- The environment is activated, on the verdict interface's tick or on an
    -- answer from `u`; either way its emission is routed by `outE`.
    onLcase : (se : EnvSt B) (su : MC.St u) (y : Pos B ⊎ ⊤)
            → (tw ((se , su) , inj₁ y) >>=ₚ (V.id V.⊗₁ K.pureᵏ â))
            ≈ₚ (stepˢ B (se , y) >>=ₚ λ q → returnₚ ((proj₁ q , su) , outE B (proj₂ q)))
    onLcase se su y =
      bindˣ ( tstepL (MC.onL (stepˢ B)) (MC.onR (MC.step u)) (se , su) y
            ⟨≈⟩ bindˣ (onL-pt (stepˢ B) se su y)
            ⟨≈⟩ >>=ₚ-assoc (stepˢ B (se , y)) _ _
            ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , su) , proj₂ r) _))
      ⟨≈⟩ >>=ₚ-assoc (stepˢ B (se , y)) _ _
      ⟨≈⟩ bindᶠ (λ where
            (se′ , inj₁ n) → >>=ₚ-identityˡ ((se′ , su) , inj₁ (inj₁ n)) _
                           ⟨≈⟩ ⊗-pure â ((se′ , su) , inj₁ (inj₁ n))
            (se′ , inj₂ v) → >>=ₚ-identityˡ ((se′ , su) , inj₁ (inj₂ v)) _
                           ⟨≈⟩ ⊗-pure â ((se′ , su) , inj₁ (inj₂ v)))

    onRcase : (se : EnvSt B) (su : MC.St u) (n : Neg B)
            → (tw ((se , su) , inj₂ (inj₂ n)) >>=ₚ (V.id V.⊗₁ K.pureᵏ â))
            ≈ₚ (MC.step u (su , inj₂ n) >>=ₚ λ q → returnₚ ((se , proj₁ q) , outU B (proj₂ q)))
    onRcase se su n =
      bindˣ ( tstepR (MC.onL (stepˢ B)) (MC.onR (MC.step u)) (se , su) (inj₂ n)
            ⟨≈⟩ bindˣ (onR-pt (MC.step u) se su (inj₂ n))
            ⟨≈⟩ >>=ₚ-assoc (MC.step u (su , inj₂ n)) _ _
            ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((se , proj₁ r) , proj₂ r) _))
      ⟨≈⟩ >>=ₚ-assoc (MC.step u (su , inj₂ n)) _ _
      ⟨≈⟩ bindᶠ (λ where
            (su′ , inj₁ e) → ⊥-elim e
            (su′ , inj₂ p) → >>=ₚ-identityˡ ((se , su′) , inj₂ (inj₂ p)) _
                           ⟨≈⟩ ⊗-pure â ((se , su′) , inj₂ (inj₂ p)))

    stepEq : (z : (EnvSt B × MC.St u) × ((⊥ ⊎ ⊤) ⊎ (Neg B ⊎ Pos B)))
           → ((V.id V.⊗₁ K.pureᵏ â) V.∘ (tw V.∘ (V.id V.⊗₁ K.pureᵏ ĉ))) z ≈ₚ kᵂ B u z
    stepEq ((se , su) , inj₁ (inj₁ e)) = ⊥-elim e
    stepEq ((se , su) , inj₁ (inj₂ _)) =
      bindˣ ( bindˣ (⊗-pure ĉ ((se , su) , inj₁ (inj₂ tt)))
            ⟨≈⟩ >>=ₚ-identityˡ ((se , su) , inj₁ (inj₂ tt)) tw)
      ⟨≈⟩ onLcase se su (inj₂ tt)
    stepEq ((se , su) , inj₂ (inj₁ n)) =
      bindˣ ( bindˣ (⊗-pure ĉ ((se , su) , inj₂ (inj₁ n)))
            ⟨≈⟩ >>=ₚ-identityˡ ((se , su) , inj₂ (inj₂ n)) tw)
      ⟨≈⟩ onRcase se su n
    stepEq ((se , su) , inj₂ (inj₂ p)) =
      bindˣ ( bindˣ (⊗-pure ĉ ((se , su) , inj₂ (inj₂ p)))
            ⟨≈⟩ >>=ₚ-identityˡ ((se , su) , inj₁ (inj₁ p)) tw)
      ⟨≈⟩ onLcase se su (inj₁ p)

    inner : ((strategyEnv B d T.⊗ᵉ u) MC.∘ᴹ W.γ {⊥} {Pos B} {Neg B} {⊤}) S.≈ᴹ mid
    inner = Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ (γ-pure ⊥ ⊤ (Neg B) (Pos B))
       S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ʳ (K.pureᵏ ĉ) (strategyEnv B d T.⊗ᵉ u))

    outer : (W.α {⊥} {Pos B} {Neg B} {Bool} MC.∘ᴹ
              ((strategyEnv B d T.⊗ᵉ u) MC.∘ᴹ W.γ {⊥} {Pos B} {Neg B} {⊤}))
            S.≈ᴹ MC.mk Se (kᵂ B u)
    outer = Cat.∘ᴹ-resp-≈ᴹ (α-pure (Neg B) Bool ⊥ (Pos B)) inner
       S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ˡ (K.pureᵏ â) mid)
       S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong stepEq)

compose-≈ᴹ : (B : Iface) (d : Strat (Neg B) (Pos B)) (u : Proc unitᴵ B)
           → (strategyEnv B d 𝒫.∘ u) S.≈ᴹ pairedᴹ B d u
compose-≈ᴹ B d u =
  TC.trace-resp-≈ᴹ {⊥ ⊎ ⊤} {⊥ ⊎ Bool} {Neg B ⊎ Pos B} (outer B d u)
