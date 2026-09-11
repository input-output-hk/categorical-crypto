{-# OPTIONS --safe --without-K --guardedness #-}

-- An initialization prefix at the seal, and the one process that IS one.
--
-- `Prefixedᵒ A B f g p` says `f` runs as `g` does after `p`: it is
-- `Machines.Sim.Lax`'s lax simulation, re-spelled where the seam's statements
-- live.  Under the seal a hom exposes no machine, so the crossing is
-- `UC.Model.Seal`'s third discipline — the whole development inside the
-- unfolding block, only its consequences exported — exactly as
-- `UC.Seam.Grounding.Dead` crosses with the mass bound.
--
-- `scalar-blindᵒ` is why the notion pays: a hom of the TRIVIAL grade has an
-- empty interface, so it can never be activated, its step equation holds
-- vacuously, and the only trace it leaves on any run it takes part in is its
-- own initialization.  Propagating that through `_∘_`, `sub` and the ancilla
-- tensor puts a trivial-grade simulator in front of the process it acts on, and
-- `prefixedᵒ-obs` — `Dp.Mass.astotal-bind` — removes it again once the
-- initialization is known to terminate almost surely.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (_≈ₚ[_]_; ≈ₚ[]-resp)
open import ProbabilisticLogic.Dp.Mass using (ASTotal; astotal-bind)
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
  using (Dₚ-DiscreteMonad; Elgotₚ; distₚ; 𝒫ₚ; 𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Strategy using (ask; out)
open import CategoricalCrypto.UC.Machine using (Ωᴵ; ⊤ᵛ)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)
open import CategoricalCrypto.UC.Machine.Run.Lax using (run-lax)
open import CategoricalCrypto.UC.Model.Observation using (Obs; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; ifaceᵒ)
open import CategoricalCrypto.UC.Seam.Grounding.Dead using (pointᵒ)

import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP
import CategoricalCrypto.Machines.G.Lax as GLax
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Sim.Lax as Lax
import CategoricalCrypto.UC.Core as UCC
import CategoricalCrypto.UC.Core.Standard as Std

module CategoricalCrypto.UC.Seam.Grounding.Prefix where

private
  module Gᵒ = MonoidalCategory 𝔾ᵒ
  module GL = GLax (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module Gr = UCC.Grading (Std.gradingᵗ 𝔾ᵒ)
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})
  module L  = Lax (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

opaque
  unfolding 𝔾ᵒ ifaceᵒ pointᵒ

  Prefixedᵒ : (A B : Gᵒ.Obj) → Gᵒ._⇒_ A B → Gᵒ._⇒_ A B → Dₚ ⊤ᵛ → Set₁
  Prefixedᵒ A B f g p = L._≈ˡ[_]_ f (λ _ → p) g

  prefixedᵒ-scalar : (A B : Gᵒ.Obj) (f g : Gᵒ._⇒_ A B) (p q : Dₚ ⊤ᵛ) → p ≈ₚ q
                   → Prefixedᵒ A B f g p → Prefixedᵒ A B f g q
  prefixedᵒ-scalar A B f g p q e = L.≈ˡ-resp-scalar (λ _ → e)

  prefixedᵒ-resp-≈ : (A B : Gᵒ.Obj) (f f′ g g′ : Gᵒ._⇒_ A B) (p : Dₚ ⊤ᵛ)
                   → Gᵒ._≈_ f f′ → Gᵒ._≈_ g g′
                   → Prefixedᵒ A B f g p → Prefixedᵒ A B f′ g′ p
  prefixedᵒ-resp-≈ A B f f′ g g′ p e₁ e₂ l =
    L.≈ˡ-congʳ (L.≈ˡ-congˡ (S.⟺ᴹ e₁) l) e₂

  prefixedᵒ-∘ˡ : (A B C : Gᵒ.Obj) (h : Gᵒ._⇒_ B C) (f g : Gᵒ._⇒_ A B) (p : Dₚ ⊤ᵛ)
               → Prefixedᵒ A B f g p → Prefixedᵒ A C (Gᵒ._∘_ h f) (Gᵒ._∘_ h g) p
  prefixedᵒ-∘ˡ A B C h f g p l = L.≈ˡ-resp-scalar (λ _ → >>=ₚ-identityʳ p)
    (GL.∘ᴳ-resp-≈ˡ (L.≈ᴹ⇒≈ˡ S.reflᴹ) l)

  prefixedᵒ-∘ʳ : (A B C : Gᵒ.Obj) (h : Gᵒ._⇒_ A B) (f g : Gᵒ._⇒_ B C) (p : Dₚ ⊤ᵛ)
               → Prefixedᵒ B C f g p → Prefixedᵒ A C (Gᵒ._∘_ f h) (Gᵒ._∘_ g h) p
  prefixedᵒ-∘ʳ A B C h f g p l = L.≈ˡ-resp-scalar (λ x → >>=ₚ-identityˡ x (λ _ → p))
    (GL.∘ᴳ-resp-≈ˡ l (L.≈ᴹ⇒≈ˡ S.reflᴹ))

  prefixedᵒ-⊗ˡ : (X Y A B : Gᵒ.Obj) (f g : Gᵒ._⇒_ X Y) (h : Gᵒ._⇒_ A B) (p : Dₚ ⊤ᵛ)
               → Prefixedᵒ X Y f g p
               → Prefixedᵒ (X Gᵒ.⊗₀ A) (Y Gᵒ.⊗₀ B) (Gᵒ._⊗₁_ f h) (Gᵒ._⊗₁_ g h) p
  prefixedᵒ-⊗ˡ X Y A B f g h p l = L.≈ˡ-resp-scalar (λ x → >>=ₚ-identityˡ x (λ _ → p))
    (GL.⊗₁ᴳ-resp-≈ˡ l (L.≈ᴹ⇒≈ˡ S.reflᴹ))

  prefixedᵒ-⊗ʳ : (A B X Y : Gᵒ.Obj) (h : Gᵒ._⇒_ A B) (f g : Gᵒ._⇒_ X Y) (p : Dₚ ⊤ᵛ)
               → Prefixedᵒ X Y f g p
               → Prefixedᵒ (A Gᵒ.⊗₀ X) (B Gᵒ.⊗₀ Y) (Gᵒ._⊗₁_ h f) (Gᵒ._⊗₁_ h g) p
  prefixedᵒ-⊗ʳ A B X Y h f g p l = L.≈ˡ-resp-scalar (λ _ → >>=ₚ-identityʳ p)
    (GL.⊗₁ᴳ-resp-≈ˡ (L.≈ᴹ⇒≈ˡ S.reflᴹ) l)

  -- The grading's substitution is the tensor's left action, and at this
  -- instance the two spellings convert; its `T₁` does not, so the ancilla
  -- action is taken in the tensor's own vocabulary (`prefixedᵒ-⊗ʳ`, with
  -- `CurriedTensor.Properties.T₁-⊗` at the use site).
  prefixedᵒ-sub : (X Y A : Gᵒ.Obj) (s s′ : Gᵒ._⇒_ X Y) (p : Dₚ ⊤ᵛ)
                → Prefixedᵒ X Y s s′ p
                → Prefixedᵒ (Gr._⊛_ X A) (Gr._⊛_ Y A)
                            (Gr.sub {X} {Y} {A} s) (Gr.sub {X} {Y} {A} s′) p
  prefixedᵒ-sub X Y A s s′ p = prefixedᵒ-⊗ˡ X Y A A s s′ Gᵒ.id p

  -- The base case: the trivial grade carries no message, so a hom of it is
  -- never activated and its step equation is vacuous.
  scalar-blindᵒ : (s : Gᵒ._⇒_ Gᵒ.unit Gᵒ.unit)
                → Prefixedᵒ Gᵒ.unit Gᵒ.unit s Gᵒ.id (pointᵒ Gᵒ.unit Gᵒ.unit s)
  scalar-blindᵒ s = L.≲ˡ⇒≈ˡ record
    { θˡ       = K.pureᵏ (λ _ → ttᵛ)
    ; θˡ-pure  = KP.structural (λ _ → ttᵛ)
    ; θˡ-point = λ _ → ≈sym (>>=ₚ-identityʳ _)
    ; θˡ-step  = λ where (_ , inj₁ x) → ⊥-elim x
                         (_ , inj₂ y) → ⊥-elim y
    }

  -- …and what the seam reads off a prefix: an almost surely terminating one is
  -- invisible to an ε-closed observation.
  prefixedᵒ-obs : (u v : Gᵒ._⇒_ 𝟘ᵒ Ωᵒ) (p : Dₚ ⊤ᵛ) → ASTotal p
                → Prefixedᵒ 𝟘ᵒ Ωᵒ u v p → (ε : ℚ) → 0ℚ ℚ.< ε → Obs u ≈ₚ[ ε ] Obs v
  prefixedᵒ-obs u v p tot l ε ε>0 =
    ≈ₚ[]-resp (≈sym prefix) ≈refl (astotal-bind p (Obs v) tot ε ε>0)
    where
    prefix : Obs u ≈ₚ (p >>=ₚ λ _ → Obs v)
    prefix = runᴹ-resp-≈ᴹ {Ωᴵ} (L.fromˡ l) (ask tt out)
       ⟨≈⟩ run-lax (L.coreˡ l) (ask tt out)
       ⟨≈⟩ bindᶠ (λ _ → runᴹ-resp-≈ᴹ {Ωᴵ} (L.toˡ l) (ask tt out))
