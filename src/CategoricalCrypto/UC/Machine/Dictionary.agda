{-# OPTIONS --safe --without-K --guardedness #-}

-- The grading dictionary: `UC.Machine`'s direct relays read as the monoidal
-- spellings of the same processes.  Those readings are the bridge between the
-- pinned relays and the derived grading `UC.Machine.gradingᴹ` — a query-bound
-- certificate is about a relay, the grading's action is `_⊗₁_` with an
-- identity, and `UC.Machine.Grading` carries one to the other through these
-- four zigzags.  Nothing here states a `Monoidal` law's type, which is what
-- makes it affordable (`UC.Machine`'s header prices the alternative).
--
-- Every object implicit is passed explicitly, for the reason
-- `UC.Machine.Grading`'s header gives — and so is every implicit of the
-- borrowed 𝒢-law, for the same one: inferring one asks Agda to invert
-- `_⊗₁ᴳ_`, measured at +83 s for a single law against +10 s pinned.
--
-- Four of the eight fields land, and they are exactly the trace-free four
-- `UC.Machine.Grading`'s own note predicts.  The other four each compare a
-- `𝒫ᴵ`-composite, hence the ⊕-trace, and every 𝒢-law that would discharge one
-- (`associator.isoʳ`, `⊗.homomorphism`, `assoc-commute-to`) spends a trace
-- absorption (`GConstructionEmbedding`'s `absorbˡ`/`absorbʳ`).  Instantiating
-- one of those at the machine layer does not finish: `associator.isoʳ` alone,
-- with every implicit pinned, was still running after 900 s under a 16 GiB
-- heap cap, 12.8 GiB resident.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
  using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Monad.Discrete using (DiscreteMonad)
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MU

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)

open import ProbabilisticLogic.Dp using (Dₚ; returnₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
  using (Dₚ-DiscreteMonad; 𝒱ₚ; 𝒢ₚᴹ; distₚ; 𝒫ₚ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.UC.Machine.Dictionary where

private
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Core (𝒱ₚ 0ℓ)
open MD.MonoidalDistributive (distₚ 0ℓ)
open CE 𝒱.U cocartesian
open DiscreteMonad (Dₚ-DiscreteMonad {0ℓ})
  renaming (_≈ᴹ_ to _≈ᵈ_; module ≈ᴹ to ≈ᵈ)
open Frame (𝒱ₚ 0ℓ)
open KD (Dₚ-DiscreteMonad {0ℓ})
open MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open MU.Shorthands 𝒱.monoidal
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)

open import Categories.Category.Monoidal.Reasoning 𝒱.monoidal

-- The 𝒢-level reassociators, which the base's own `α⇒`/`α⇐` would shadow.
open MU.Shorthands 𝔾.monoidal using () renaming (α⇒ to α⇒ᴳ; α⇐ to α⇐ᴳ)

private
  variable P Q R S V W V′ W′ X : 𝒱.Obj

------------------------------------------------------------------------
-- The base is a Kleisli category: its structural maps are functions

  pure-idᵏ : 𝒱._≈_ (𝒱.id {V}) (pureᵏ (λ v → v))
  pure-idᵏ _ = ≈ᵈ.refl

  swapᵏ : 𝒱._≈_ (+-swap {V} {W}) (pureᵏ Sum.swap)
  swapᵏ (inj₁ _) = ≈ᵈ.refl
  swapᵏ (inj₂ _) = ≈ᵈ.refl

  assocˡᵏ : 𝒱._≈_ (α+⇐ {P} {Q} {R}) (pureᵏ ⊎assocˡ)
  assocˡᵏ (inj₁ _)        = >>=-identityˡ-≈
  assocˡᵏ (inj₂ (inj₁ _)) = >>=-identityˡ-≈
  assocˡᵏ (inj₂ (inj₂ _)) = ≈ᵈ.refl

  assocʳᵏ : 𝒱._≈_ (α+⇒ {P} {Q} {R}) (pureᵏ ⊎assocʳ)
  assocʳᵏ (inj₁ (inj₁ _)) = ≈ᵈ.refl
  assocʳᵏ (inj₁ (inj₂ _)) = >>=-identityˡ-≈
  assocʳᵏ (inj₂ _)        = >>=-identityˡ-≈

  ∘-pureᵏ : {u : 𝒱._⇒_ V W} {v : 𝒱._⇒_ V′ V} {h : V → W} {k : V′ → V}
          → 𝒱._≈_ u (pureᵏ h) → 𝒱._≈_ v (pureᵏ k)
          → 𝒱._≈_ (𝒱._∘_ u v) (pureᵏ (λ x → h (k x)))
  ∘-pureᵏ {h = h} {k} e₁ e₂ = (e₁ ⟩∘⟨ e₂) ○ pureᵏ-∘ h k

  +₁-pureᵏ : {u : 𝒱._⇒_ V W} {v : 𝒱._⇒_ V′ W′} {h : V → W} {k : V′ → W′}
           → 𝒱._≈_ u (pureᵏ h) → 𝒱._≈_ v (pureᵏ k)
           → 𝒱._≈_ (u +₁ v) (pureᵏ (Sum.map h k))
  +₁-pureᵏ {h = h} {k} e₁ e₂ = +₁-cong₂ e₁ e₂ ○ leaves
    where
    leaves : 𝒱._≈_ (pureᵏ h +₁ pureᵏ k) (pureᵏ (Sum.map h k))
    leaves (inj₁ _) = >>=-identityˡ-≈
    leaves (inj₂ _) = >>=-identityˡ-≈

  -- A pure interface relabelling spends two junctions and keeps the state.
  pureᴵ : (h : V → W) (r : X × V)
        → 𝒱._⊗₁_ (𝒱.id {X}) (pureᵏ h) r ≈ᵈ returnₚ (proj₁ r , h (proj₂ r))
  pureᴵ h = pureᵏ-⊗ (λ x → x) h

  swapᴵ : (r : X × (V ⊎ W))
        → 𝒱._⊗₁_ (𝒱.id {X}) +-swap r ≈ᵈ returnₚ (proj₁ r , Sum.swap (proj₂ r))
  swapᴵ {X = X} {V} {W} r = ≈ᵈ.trans (padded r) (pureᴵ Sum.swap r)
    where
    padded : 𝒱._≈_ {X × (V ⊎ W)} {X × (W ⊎ V)}
                   (𝒱._⊗₁_ 𝒱.id +-swap) (𝒱._⊗₁_ 𝒱.id (pureᵏ Sum.swap))
    padded = refl⟩⊗⟨ swapᵏ

  enter-pure : {A : 𝒱.Obj} (h : V → W) (K : X × W → Dₚ A) (x : X) (v : V)
             → (𝒱._⊗₁_ (𝒱.id {X}) (pureᵏ h) (x , v) >>= K) ≈ᵈ K (x , h v)
  enter-pure h K x v = ≈ᵈ.trans (>>=-cong-x (pureᴵ h (x , v))) >>=-identityˡ-≈

  exit-pure : (h : V → W) (x : X) (v : V)
            → (returnₚ (x , v) >>= 𝒱._⊗₁_ (𝒱.id {X}) (pureᵏ h)) ≈ᵈ returnₚ (x , h v)
  exit-pure h x v = ≈ᵈ.trans >>=-identityˡ-≈ (pureᴵ h (x , v))

  -- Entering a `tstep` on one summand runs that arm and retags its answer.
  tstep-inj₁ : {A B C D : 𝒱.Obj} (k : X × A → Dₚ (W × B)) (l : X × C → Dₚ (W × D))
               (x : X) (a : A)
             → tstep k l (x , inj₁ a)
               ≈ᵈ (k (x , a) >>= λ r → returnₚ (proj₁ r , inj₁ (proj₂ r)))
  tstep-inj₁ k l x a =
    ≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈)
      (≈ᵈ.trans (>>=-assoc-≈ (k (x , a)))
        (>>=-cong-f λ r → ≈ᵈ.trans >>=-identityˡ-≈ (pureᵏ-⊗ (λ y → y) inj₁ r)))

  tstep-inj₂ : {A B C D : 𝒱.Obj} (k : X × A → Dₚ (W × B)) (l : X × C → Dₚ (W × D))
               (x : X) (c : C)
             → tstep k l (x , inj₂ c)
               ≈ᵈ (l (x , c) >>= λ r → returnₚ (proj₁ r , inj₂ (proj₂ r)))
  tstep-inj₂ k l x c =
    ≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈)
      (≈ᵈ.trans (>>=-assoc-≈ (l (x , c)))
        (>>=-cong-f λ r → ≈ᵈ.trans >>=-identityˡ-≈ (pureᵏ-⊗ (λ y → y) inj₂ r)))

------------------------------------------------------------------------
-- `mid` and the pure machines it is built from

  -- The interchange the G-tensor conjugates by, as a function on sums.
  midfn : (P ⊎ Q) ⊎ (R ⊎ S) → (P ⊎ R) ⊎ (Q ⊎ S)
  midfn (inj₁ (inj₁ p)) = inj₁ (inj₁ p)
  midfn (inj₁ (inj₂ q)) = inj₂ (inj₁ q)
  midfn (inj₂ (inj₁ r)) = inj₁ (inj₂ r)
  midfn (inj₂ (inj₂ s)) = inj₂ (inj₂ s)

  midᴹ : Machine ((P + Q) + (R + S)) ((P + R) + (Q + S))
  midᴹ = α⇐ᴹ ∘ᴹ ((idᴹ ⊗ᵉ (α⇒ᴹ ∘ᴹ ((σᴹ ⊗ᵉ idᴹ) ∘ᴹ α⇐ᴹ))) ∘ᴹ α⇒ᴹ)

  id-pureᴹ : idᴹ {V} ≈ᴹ pureᴹ (𝒱.id {V})
  id-pureᴹ = ≲⇒≈ᴹ˘ pureᴹ-id

  ∘-pureᴹ : {M : Machine W V′} {N : Machine V W} {u : 𝒱._⇒_ W V′} {v : 𝒱._⇒_ V W}
          → M ≈ᴹ pureᴹ u → N ≈ᴹ pureᴹ v → (M ∘ᴹ N) ≈ᴹ pureᴹ (𝒱._∘_ u v)
  ∘-pureᴹ e₁ e₂ = ∘ᴹ-resp-≈ᴹ e₁ e₂ ○ᴹ ≲⇒≈ᴹ (pureᴹ-∘ _ _)

  ⊗-pureᴹ : {M : Machine V W} {N : Machine V′ W′} {u : 𝒱._⇒_ V W} {v : 𝒱._⇒_ V′ W′}
          → M ≈ᴹ pureᴹ u → N ≈ᴹ pureᴹ v → (M ⊗ᵉ N) ≈ᴹ pureᴹ (u +₁ v)
  ⊗-pureᴹ e₁ e₂ = ⊗ᵉ-resp-≈ᴹ e₁ e₂ ○ᴹ ≲⇒≈ᴹ (⊗ᵉ-pureᴹ _ _)

  -- Every factor of `mid` is a structural machine, hence `pureᴹ`; what it
  -- collapses to is the interchange on sums.
  midᴹ-pure : midᴹ {P} {Q} {R} {S} ≈ᴹ pureᴹ (pureᵏ midfn)
  midᴹ-pure = ∘-pureᴹ reflᴹ (∘-pureᴹ (⊗-pureᴹ id-pureᴹ inner) reflᴹ)
            ○ᴹ ≲⇒≈ᴹ (pureᴹ-cong base)
    where
    inner = ∘-pureᴹ reflᴹ (∘-pureᴹ (⊗-pureᴹ reflᴹ id-pureᴹ) reflᴹ)
    base = ∘-pureᵏ assocˡᵏ
             (∘-pureᵏ (+₁-pureᵏ pure-idᵏ
                        (∘-pureᵏ assocʳᵏ
                          (∘-pureᵏ (+₁-pureᵏ swapᵏ pure-idᵏ) assocˡᵏ)))
                      assocʳᵏ)
         ○ pureᵏ-cong λ where
             (inj₁ (inj₁ _)) → refl
             (inj₁ (inj₂ _)) → refl
             (inj₂ (inj₁ _)) → refl
             (inj₂ (inj₂ _)) → refl

  -- Tensoring with a pure machine keeps the other factor's state.
  ⊗ᵉ-pureˡ : (h : 𝒱._⇒_ V W) (M : Machine V′ W′)
           → (pureᴹ h ⊗ᵉ M) ≲ mk (state M) (tstep (𝒱._⊗₁_ 𝒱.id h) (step M))
  ⊗ᵉ-pureˡ h M = collapseˡ ((refl⟩∘⟨ tstep-cong (onL-str h) 𝒱.Equiv.refl)
                            ○ tstep-sim (⟺ (pad-transport λ⇒ h)) onR-collapseˡ)

  ⊗ᵉ-pureʳ : (M : Machine V W) (h : 𝒱._⇒_ V′ W′)
           → (M ⊗ᵉ pureᴹ h) ≲ mk (state M) (tstep (step M) (𝒱._⊗₁_ 𝒱.id h))
  ⊗ᵉ-pureʳ M h = collapseʳ ((refl⟩∘⟨ tstep-cong 𝒱.Equiv.refl (onRᵍ-id⊗ h))
                            ○ tstep-sim onL-collapseʳ (⟺ (pad-transport ρ⇒ h)))

------------------------------------------------------------------------
-- The ancilla reassociators are the 𝒢-associator

private
  -- The base half of the embedding `⌜ u , v ⌝`: swapping after relabelling each
  -- summand is the copairing that routes each summand to the other side.
  swap-copair : (u : 𝒱._⇒_ V W) (v : 𝒱._⇒_ V′ W′)
              → 𝒱._≈_ (𝒱._∘_ +-swap (u +₁ v)) [ 𝒱._∘_ i₂ u , 𝒱._∘_ i₁ v ]
  swap-copair u v = +-unique₂
    (𝒱.assoc ○ (refl⟩∘⟨ +₁∘i₁) ○ 𝒱.sym-assoc ○ (+-swap-i₁ ⟩∘⟨refl) ○ ⟺ inject₁)
    (𝒱.assoc ○ (refl⟩∘⟨ +₁∘i₂) ○ 𝒱.sym-assoc ○ (+-swap-i₂ ⟩∘⟨refl) ○ ⟺ inject₂)

  -- …and the machine half: an embedding of two pure machines is pure.
  ⌜⌝-pureᴹ : (u : 𝒱._⇒_ V W) (v : 𝒱._⇒_ V′ W′)
           → (σᴹ ∘ᴹ (pureᴹ u ⊗ᵉ pureᴹ v)) ≲ pureᴹ (𝒱._∘_ +-swap (u +₁ v))
  ⌜⌝-pureᴹ u v = ≲-trans (∘ᴹ-resp-≲ ≲-refl (⊗ᵉ-pureᴹ u v)) (pureᴹ-∘ +-swap (u +₁ v))

  -- A wire's step is the copairing of its two relabellings, crossed.
  wireStep-copair : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
                  → 𝒱._≈_ (wireStep {A} {B} up down)
                      (𝒱._⊗₁_ 𝒱.id [ 𝒱._∘_ i₂ (pureᵏ up) , 𝒱._∘_ i₁ (pureᵏ down) ])
  wireStep-copair _ _ (_ , inj₁ _) =
    ≈ᵈ.sym (≈ᵈ.trans >>=-identityˡ-≈
                     (≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈) >>=-identityˡ-≈))
  wireStep-copair _ _ (_ , inj₂ _) =
    ≈ᵈ.sym (≈ᵈ.trans >>=-identityˡ-≈
                     (≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈) >>=-identityˡ-≈))

a⇒-α⇐ : {X Y A : Iface}
      → 𝒫._≈_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A}
          (a⇒ᴵ {X} {Y} {A}) (α⇐ᴳ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
a⇒-α⇐ =
    ≲⇒≈ᴹ (mk-cong (wireStep-copair ⊎assocˡ ⊎assocʳ ○ ⟺ (refl⟩⊗⟨ bridge)))
  ○ᴹ ≲⇒≈ᴹ˘ (⌜⌝-pureᴹ α+⇐ α+⇒)
  where
  bridge = swap-copair α+⇐ α+⇒
         ○ []-cong₂ (refl⟩∘⟨ assocˡᵏ) (refl⟩∘⟨ assocʳᵏ)

a⇐-α⇒ : {X Y A : Iface}
      → 𝒫._≈_ {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)}
          (a⇐ᴵ {X} {Y} {A}) (α⇒ᴳ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
a⇐-α⇒ =
    ≲⇒≈ᴹ (mk-cong (wireStep-copair ⊎assocʳ ⊎assocˡ ○ ⟺ (refl⟩⊗⟨ bridge)))
  ○ᴹ ≲⇒≈ᴹ˘ (⌜⌝-pureᴹ α+⇒ α+⇐)
  where
  bridge = swap-copair α+⇒ α+⇐
         ○ []-cong₂ (refl⟩∘⟨ assocʳᵏ) (refl⟩∘⟨ assocˡᵏ)

------------------------------------------------------------------------
-- The two relays are the 𝒢-tensor with an identity

private
  -- Both relays collapse to the same shape: the conjugation of a `tstep` by the
  -- interchange, which is what `_⊗₁ᴳ_` is once its two `mid`s are absorbed.
  T₁-step : {Y A B : Iface} (f : Proc A B)
          → 𝒱._≈_
              (𝒱._∘_ (𝒱._⊗₁_ 𝒱.id (pureᵏ midfn))
                     (𝒱._∘_ (tstep (𝒱._⊗₁_ 𝒱.id +-swap) (step f))
                            (𝒱._⊗₁_ 𝒱.id (pureᵏ midfn))))
              (step (T₁ᴵ Y {A} {B} f))
  T₁-step f (s , inj₁ (inj₁ y)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ s (inj₁ (inj₁ y))) relabel))
             (exit-pure midfn s (inj₁ (inj₂ y)))
    where
    relabel = ≈ᵈ.trans (tstep-inj₁ _ _ s (inj₁ y))
                       (≈ᵈ.trans (>>=-cong-x (swapᴵ (s , inj₁ y))) >>=-identityˡ-≈)
  T₁-step f (s , inj₂ (inj₁ y)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ s (inj₂ (inj₁ y))) relabel))
             (exit-pure midfn s (inj₁ (inj₁ y)))
    where
    relabel = ≈ᵈ.trans (tstep-inj₁ _ _ s (inj₂ y))
                       (≈ᵈ.trans (>>=-cong-x (swapᴵ (s , inj₂ y))) >>=-identityˡ-≈)
  T₁-step f (s , inj₁ (inj₂ a)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ s (inj₁ (inj₂ a)))
                                   (tstep-inj₂ _ _ s (inj₁ a))))
             (≈ᵈ.trans (>>=-assoc-≈ (step f (s , inj₁ a)))
                       (>>=-cong-f λ where
                          (s′ , inj₁ a′) → exit-pure midfn s′ (inj₂ (inj₁ a′))
                          (s′ , inj₂ b′) → exit-pure midfn s′ (inj₂ (inj₂ b′))))
  T₁-step f (s , inj₂ (inj₂ b)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ s (inj₂ (inj₂ b)))
                                   (tstep-inj₂ _ _ s (inj₂ b))))
             (≈ᵈ.trans (>>=-assoc-≈ (step f (s , inj₂ b)))
                       (>>=-cong-f λ where
                          (s′ , inj₁ a′) → exit-pure midfn s′ (inj₂ (inj₁ a′))
                          (s′ , inj₂ b′) → exit-pure midfn s′ (inj₂ (inj₂ b′))))

  sub-step : {X Y A : Iface} (s : Proc X Y)
           → 𝒱._≈_
               (𝒱._∘_ (𝒱._⊗₁_ 𝒱.id (pureᵏ midfn))
                      (𝒱._∘_ (tstep (step s) (𝒱._⊗₁_ 𝒱.id +-swap))
                             (𝒱._⊗₁_ 𝒱.id (pureᵏ midfn))))
               (step (subᴵ′ {X} {Y} {A} s))
  sub-step s (t , inj₁ (inj₂ a)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ t (inj₁ (inj₂ a))) relabel))
             (exit-pure midfn t (inj₂ (inj₂ a)))
    where
    relabel = ≈ᵈ.trans (tstep-inj₂ _ _ t (inj₁ a))
                       (≈ᵈ.trans (>>=-cong-x (swapᴵ (t , inj₁ a))) >>=-identityˡ-≈)
  sub-step s (t , inj₂ (inj₂ a)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ t (inj₂ (inj₂ a))) relabel))
             (exit-pure midfn t (inj₂ (inj₁ a)))
    where
    relabel = ≈ᵈ.trans (tstep-inj₂ _ _ t (inj₂ a))
                       (≈ᵈ.trans (>>=-cong-x (swapᴵ (t , inj₂ a))) >>=-identityˡ-≈)
  sub-step s (t , inj₁ (inj₁ x)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ t (inj₁ (inj₁ x)))
                                   (tstep-inj₁ _ _ t (inj₁ x))))
             (≈ᵈ.trans (>>=-assoc-≈ (step s (t , inj₁ x)))
                       (>>=-cong-f λ where
                          (t′ , inj₁ x′) → exit-pure midfn t′ (inj₁ (inj₁ x′))
                          (t′ , inj₂ y′) → exit-pure midfn t′ (inj₁ (inj₂ y′))))
  sub-step s (t , inj₂ (inj₁ y)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ t (inj₂ (inj₁ y)))
                                   (tstep-inj₁ _ _ t (inj₂ y))))
             (≈ᵈ.trans (>>=-assoc-≈ (step s (t , inj₂ y)))
                       (>>=-cong-f λ where
                          (t′ , inj₁ x′) → exit-pure midfn t′ (inj₁ (inj₁ x′))
                          (t′ , inj₂ y′) → exit-pure midfn t′ (inj₁ (inj₂ y′))))

T₁-⊗₁ : {Y A B : Iface} (f : Proc A B)
      → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y {A} {B} f)
          (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f)
T₁-⊗₁ {Y} {A} {B} f = ⟺ᴹ
  ( ∘ᴹ-resp-≈ᴹ midᴹ-pure (∘ᴹ-resp-≈ᴹ reflᴹ midᴹ-pure)
  ○ᴹ ≲⇒≈ᴹ (∘ᴹ-resp-≲ ≲-refl (∘ᴹ-resp-≲ (⊗ᵉ-pureˡ +-swap f) ≲-refl))
  ○ᴹ ≲⇒≈ᴹ (∘ᴹ-resp-≲ ≲-refl (pure-∘ʳ (pureᵏ midfn) _))
  ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ (pureᵏ midfn) _)
  ○ᴹ ≲⇒≈ᴹ (mk-cong (T₁-step {Y} {A} {B} f)) )

sub-⊗₁ : {X Y A : Iface} (s : Proc X Y)
       → 𝒫._≈_ {X ⊗ᴵ A} {Y ⊗ᴵ A} (subᴵ′ {X} {Y} {A} s)
           (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ A ⟧ᴵ} s (𝒫.id {A}))
sub-⊗₁ {X} {Y} {A} s = ⟺ᴹ
  ( ∘ᴹ-resp-≈ᴹ midᴹ-pure (∘ᴹ-resp-≈ᴹ reflᴹ midᴹ-pure)
  ○ᴹ ≲⇒≈ᴹ (∘ᴹ-resp-≲ ≲-refl (∘ᴹ-resp-≲ (⊗ᵉ-pureʳ s +-swap) ≲-refl))
  ○ᴹ ≲⇒≈ᴹ (∘ᴹ-resp-≲ ≲-refl (pure-∘ʳ (pureᵏ midfn) _))
  ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ (pureᵏ midfn) _)
  ○ᴹ ≲⇒≈ᴹ (mk-cong (sub-step {X} {Y} {A} s)) )

------------------------------------------------------------------------
-- The trace-free grading laws, as corollaries of the 𝒢-tensor

T₁-resp-≈ᴹ : {Y A B : Iface} {f g : Proc A B}
           → 𝒫._≈_ {A} {B} f g
           → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y {A} {B} f) (T₁ᴵ Y {A} {B} g)
T₁-resp-≈ᴹ {Y} {A} {B} {f} {g} e =
     T₁-⊗₁ {Y} {A} {B} f
  ○ᴹ 𝔾.⊗.F-resp-≈ {⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Y ⟧ᴵ , ⟦ B ⟧ᴵ}
       {𝒫.id {Y} , f} {𝒫.id {Y} , g} (𝔾.Equiv.refl {x = 𝒫.id {Y}} , e)
  ○ᴹ ⟺ᴹ (T₁-⊗₁ {Y} {A} {B} g)

T₁-idᴹ : {Y A : Iface}
       → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ A} (T₁ᴵ Y {A} {A} (𝒫.id {A})) (𝒫.id {Y ⊗ᴵ A})
T₁-idᴹ {Y} {A} =
     T₁-⊗₁ {Y} {A} {A} (𝒫.id {A})
  ○ᴹ 𝔾.⊗.identity {⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ}

sub-resp-≈ᴹ : {X Y A : Iface} {s t : Proc X Y}
            → 𝒫._≈_ {X} {Y} s t
            → 𝒫._≈_ {X ⊗ᴵ A} {Y ⊗ᴵ A} (subᴵ′ {X} {Y} {A} s) (subᴵ′ {X} {Y} {A} t)
sub-resp-≈ᴹ {X} {Y} {A} {s} {t} e =
     sub-⊗₁ {X} {Y} {A} s
  ○ᴹ 𝔾.⊗.F-resp-≈ {⟦ X ⟧ᴵ , ⟦ A ⟧ᴵ} {⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ}
       {s , 𝒫.id {A}} {t , 𝒫.id {A}} (e , 𝔾.Equiv.refl {x = 𝒫.id {A}})
  ○ᴹ ⟺ᴹ (sub-⊗₁ {X} {Y} {A} t)

sub-idᴹ : {X A : Iface}
        → 𝒫._≈_ {X ⊗ᴵ A} {X ⊗ᴵ A} (subᴵ′ {X} {X} {A} (𝒫.id {X})) (𝒫.id {X ⊗ᴵ A})
sub-idᴹ {X} {A} =
     sub-⊗₁ {X} {X} {A} (𝒫.id {X})
  ○ᴹ 𝔾.⊗.identity {⟦ X ⟧ᴵ , ⟦ A ⟧ᴵ}
