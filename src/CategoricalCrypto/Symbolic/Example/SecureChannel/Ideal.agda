{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Symbolic.Example.SecureChannel.Ideal where

open import Categories.Category.Monoidal.Bundle
open import Categories.FreeMonoidal using (module FreeObjInterp; Mon)
open import Data.Bool.Base
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product
open import Data.Sum.Base
open import Data.Sum.Properties using (inj₁-injective)
open import Data.Unit.Base
open import Function.Base hiding (_∘_; id)
open import Function.Bundles using (mk⇔)
open import Function.Definitions using (Injective)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Reasoning
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚᴹ)
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀
open import CategoricalCrypto.Symbolic.Role Σ₀ using (Atom; void; verdict)
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Protocol
import CategoricalCrypto.Symbolic.Example.SecureChannel.Simulation as Coupling
import CategoricalCrypto.Symbolic.RunFollowing.Supply as Supply
open import CategoricalCrypto.UC.Machine.Dictionary using (sub-⊗₁)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

open FreeObjInterp Mon Atom ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ)
private module G = MonoidalCategory 𝔾ᵒ
private variable Y : ObjTerm

private
  equality : ∀ {X Y} {f g : X G.⇒ Y} → f ≡ g → f G.≈ g
  equality refl = G.Equiv.refl

opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ ⊗ᵒ

  role-factoring : ∀ κ κⁱ → leafᵒ (tt , (tt , tt) , simulated-role) κ G.≈
    (leafᵒ (tt , tt , simulator-role) κ G.⊗₁ G.id) G.∘ leafᵒ (tt , (tt , tt) , ideal-role) κⁱ
  role-factoring κ κⁱ = ≈ᴹ⇒≈ᵒ (C.simulated≈composition S.○ᴹ
    M.∘-resp-≈ (sub-⊗₁ {A = ⟦ wire ⟧ᴵ} C.sim) S.reflᴹ)
    where
    module C = Coupling κ κⁱ
    module M = MonoidalCategory (𝒢ₚᴹ Level.0ℓ)

module Naming (T : HomTerm (Y ⊗₀ ports) (Var verdict)) (m : Closure (Y ⊗₀ Var void)) where
  single composite : HomTerm (Var void) (Var verdict)
  single = (T ∘ id ⊗₁ simulated) ∘ m
  composite = (T ∘ id ⊗₁ (Sym.sub simulator ∘ ideal)) ∘ m

  erase : Occ composite → Occ single ⊎ ⊤
  erase (inj₁ (inj₁ o)) = inj₁ (inj₁ (inj₁ o))
  erase (inj₁ (inj₂ (inj₁ ())))
  erase (inj₁ (inj₂ (inj₂ (inj₁ (inj₁ tt))))) = inj₁ (inj₁ (inj₂ (inj₂ tt)))
  erase (inj₁ (inj₂ (inj₂ (inj₁ (inj₂ ())))))
  erase (inj₁ (inj₂ (inj₂ (inj₂ tt)))) = inj₂ tt
  erase (inj₂ o) = inj₁ (inj₂ o)

  reinsert : Occ single ⊎ ⊤ → Occ composite
  reinsert (inj₁ (inj₁ (inj₁ o))) = inj₁ (inj₁ o)
  reinsert (inj₁ (inj₁ (inj₂ (inj₁ ()))))
  reinsert (inj₁ (inj₁ (inj₂ (inj₂ tt)))) = inj₁ (inj₂ (inj₂ (inj₁ (inj₁ tt))))
  reinsert (inj₁ (inj₂ o)) = inj₂ o
  reinsert (inj₂ tt) = inj₁ (inj₂ (inj₂ (inj₂ tt)))

  reinsert-erase : ∀ o → reinsert (erase o) ≡ o
  reinsert-erase (inj₁ (inj₁ _)) = refl
  reinsert-erase (inj₁ (inj₂ (inj₁ ())))
  reinsert-erase (inj₁ (inj₂ (inj₂ (inj₁ (inj₁ tt))))) = refl
  reinsert-erase (inj₁ (inj₂ (inj₂ (inj₁ (inj₂ ())))))
  reinsert-erase (inj₁ (inj₂ (inj₂ (inj₂ tt)))) = refl
  reinsert-erase (inj₂ _) = refl

  erase-reinsert : ∀ o → erase (reinsert o) ≡ o
  erase-reinsert (inj₁ (inj₁ (inj₁ _))) = refl
  erase-reinsert (inj₁ (inj₁ (inj₂ (inj₁ ()))))
  erase-reinsert (inj₁ (inj₁ (inj₂ (inj₂ tt)))) = refl
  erase-reinsert (inj₁ (inj₂ _)) = refl
  erase-reinsert (inj₂ tt) = refl

  insert : Occ single → Occ composite
  insert = reinsert ∘′ inj₁

  erase-injective : Injective _≡_ _≡_ erase
  erase-injective {o} {o′} e = trans (sym (reinsert-erase o)) (trans (cong reinsert e) (reinsert-erase o′))

  insert-injective : Injective _≡_ _≡_ insert
  insert-injective {o} {o′} e = inj₁-injective
    (trans (sym (erase-reinsert (inj₁ o))) (trans (cong erase e) (erase-reinsert (inj₁ o′))))

  lockstep : ∀ (ι : Occ single → ℕ) (ι′ : Occ composite → ℕ)
    → (∀ o → ι′ (insert o) ≡ ι o) → ⟦ single ⟧[ ι ] G.≈ ⟦ composite ⟧[ ι′ ]
  lockstep ι ι′ agree = G.∘-resp-≈
    (G.∘-resp-≈ (equality (⟦⟧[]-cong T λ o → sym (agree (inj₁ (inj₁ o)))))
      (G.⊗.F-resp-≈ (G.Equiv.refl , resource)))
    (equality (⟦⟧[]-cong m λ o → sym (agree (inj₂ o))))
    where
    resource : leafᵒ (tt , (tt , tt) , simulated-role) (ι (inj₁ (inj₂ (inj₂ tt)))) G.≈
      (leafᵒ (tt , tt , simulator-role) (ι′ (inj₁ (inj₂ (inj₂ (inj₁ (inj₁ tt)))))) G.⊗₁ G.id)
        G.∘ leafᵒ (tt , (tt , tt) , ideal-role) (ι′ (inj₁ (inj₂ (inj₂ (inj₂ tt)))))
    resource = G.Equiv.trans
      (equality (cong (leafᵒ (tt , (tt , tt) , simulated-role)) (sym (agree (inj₁ (inj₂ (inj₂ tt)))))))
      (role-factoring _ _)

  forward : ∀ b → eval single b → eval composite b
  forward b (named ι fresh answer) = named ι′ fresh′ (≈sym (obs-resp (lockstep ι ι′ agree)) ⟨≈⟩ answer)
    where
    spare = suc (Supply.bound single ι)
    extension = Supply.extend spare ι
    ι′ = extension ∘′ erase
    fresh′ : Injective _≡_ _≡_ ι′
    fresh′ e = erase-injective (Supply.extend-injective fresh (Supply.unused single ι) e)
    agree : ∀ o → ι′ (insert o) ≡ ι o
    agree o = cong extension (erase-reinsert (inj₁ o))

  backward : ∀ b → eval composite b → eval single b
  backward b (named ι′ fresh answer) = named (ι′ ∘′ insert) (λ e → insert-injective (fresh e))
    (obs-resp (lockstep (ι′ ∘′ insert) ι′ (λ _ → refl)) ⟨≈⟩ answer)

simulated≈ideal-simulator : simulated Sym.≈ℰ (Sym.sub simulator ∘ ideal)
simulated≈ideal-simulator = Sym.KE.mk∼ λ { {lift (_ , T)} → lift (same λ m b →
  mk⇔ (Naming.forward T m b) (Naming.backward T m b)) }
