{-# OPTIONS --safe --without-K --guardedness #-}

-- Behavioural equality is protocol-rewrite's U-kernel, not its bare kernel
-- (docs/uc-setup-random-systems.md §4.2, §5.3).
--
-- `≈ᵁ⇒≈ᴿ`, the converse of `UC.RandomSystems.Morphism.≈ᴿ⇒≈ᵁ`: on the ancilla
-- `A*` the cup (`UC.Machine.Cup`) hands a strategy's letters to the hole's
-- domain and back, so the test playing the strategy (`UC.Seam.strategyEnv`)
-- observes the strategy's own run (`play-cup`).
--
-- `¬gradeStableᵒ`: without the ancilla a closure hears what the hole says on
-- `A` and can pass none of it on, so `revealᴹ true` and `revealᴹ false` are
-- `≈ℰ`-equal, while a strategy, hence `T₁ A*`, reads the bit.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (simFn)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Cup
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Seal
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Model.Setup as Sᵒ

module CategoricalCrypto.UC.RandomSystems.FullAbstraction where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module G = MonoidalCategory 𝔾ᵒ
  module 𝒫 = Category 𝒫ᴵ
  module Q = MonoidalCongruence congᴿ
  module Ap = AllPositive ℚ-refinement Approximationᴹ
  variable A B X Z : G.Obj

------------------------------------------------------------------------
-- Two processes only an ancilla tells apart

Aʳ Bʳ : Iface
Aʳ = ⊥ ⇿ Bool
Bʳ = ⊥ ⇿ ⊤

-- Whoever closes `A` hears `b` and, `Pos Aʳ` being empty, can answer nothing.
revealᴹ : Bool → Proc Aʳ Bʳ
revealᴹ b = MC.mk MC.Iˢ λ where
  (_ , inj₁ ())
  (s , inj₂ _) → returnₚ (s , inj₁ b)

private
  mutual
    cum-void : {Z : Set} → (Z → ⊥) → (n : ℕ) (d : Dₚ Z) (P : Z → ℚ) → cum n d P ≡ 0ℚ
    cum-void v zero    d P = refl
    cum-void v (suc n) d P =
      trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leaf-void v n (br d true) P))
                         (cong (wt d false ℚ.*_) (leaf-void v n (br d false) P)))
            (node-zero (wt d true) (wt d false))

    leaf-void : {Z : Set} → (Z → ⊥) → (n : ℕ) (x : Z ⊎ Dₚ Z) (P : Z → ℚ) → leafₚ n x P ≡ 0ℚ
    leaf-void v n (inj₁ z)  P = ⊥-elim (v z)
    leaf-void v n (inj₂ d′) P = cum-void v n d′ P

  ≈ₚ-void : {Z : Set} → (Z → ⊥) → (d e : Dₚ Z) → d ≈ₚ e
  ≈ₚ-void v d e = exact⇒≈ₚ d e λ P n → trans (cum-void v n d P) (sym (cum-void v n e P))

-- A closed process at `Bʳ` has nothing to answer with, so the closed loop of
-- either composite never lands.
reveal-∘ : (m : Proc unitᴵ Aʳ)
         → 𝒫._≈_ {unitᴵ} {Bʳ} (𝒫._∘_ {unitᴵ} {Aʳ} {Bʳ} (revealᴹ true) m)
                              (𝒫._∘_ {unitᴵ} {Aʳ} {Bʳ} (revealᴹ false) m)
reveal-∘ m =
       S.⟺ᴹ (Col.compose-raw≈∘ᴳ (revealᴹ true) m) S.○ᴹ Col.collapseᵀ (revealᴹ true) m
  S.○ᴹ S.≲⇒≈ᴹ (simFn id (λ _ → >>=ₚ-identityʳ _) λ _ →
                  ≈ₚ-void (λ { (_ , inj₁ ()) ; (_ , inj₂ ()) }) _ _)
  S.○ᴹ S.⟺ᴹ (Col.collapseᵀ (revealᴹ false) m) S.○ᴹ Col.compose-raw≈∘ᴳ (revealᴹ false) m

private
  tell : Strat (⊥ ⊎ ⊤) (Bool ⊎ ⊥)
  tell = ask (inj₂ tt) λ where
    (inj₁ b) → out b
    (inj₂ ())

  run-reveal : (b : Bool) → runˢ (revealᴹ b) tell ≈ₚ returnₚ b
  run-reveal b = >>=ₚ-identityˡ ttᵛ _ ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , inj₁ b) _

reveal-≉ᴿ : ¬ (revealᴹ true ≈ᴿ revealᴹ false)
reveal-≉ᴿ e =
  let m , le = proj₁ (≈ₚ[]-resp (run-reveal true) (run-reveal false)
                                (e tell ½ (toWitness {a? = 0ℚ <? ½} _))) true 1
  in 1≰½ (≤-trans (≤-reflexive (sym (returnₚ-cum 0 true (indᵇ true))))
          (≤-trans le (≤-trans (+-monoˡ-≤ ½ (returnₚ-cum-≤ m false (indᵇ true) (indᵇ-nn true)))
                               (≤-reflexive (+-identityˡ ½)))))

------------------------------------------------------------------------
-- Across the seal

dualᵒ : G.Obj → G.Obj
dualᵒ X = ifaceᵒ (dualᴵ (objᵒ X))

opaque
  unfolding 𝔾ᵒ sealᵒ congᴿ

  unhomᵒ : X G.⇒ Z → Proc (objᵒ X) (objᵒ Z)
  unhomᵒ f = f

  ∼ᴿ-intro : {f g : X G.⇒ Z} → unhomᵒ f ≈ᴿ unhomᵒ g → f Q.∼ g
  ∼ᴿ-intro e = e

  playᵒ : (X Z : G.Obj) → Strat (Pos (objᵒ X) ⊎ Neg (objᵒ Z)) (Neg (objᵒ X) ⊎ Pos (objᵒ Z))
        → dualᵒ X G.⊗₀ Z G.⇒ Ωᵒ
  playᵒ X Z d = strategyEnv (dualᴵ (objᵒ X) ⊗ᴵ objᵒ Z) d

  cupᵒ : (X : G.Obj) → 𝟘ᵒ G.⇒ dualᵒ X G.⊗₀ X
  cupᵒ X = cupᴵ (objᵒ X)

  play-cup : (X Z : G.Obj) (f : X G.⇒ Z)
             (d : Strat (Pos (objᵒ X) ⊎ Neg (objᵒ Z)) (Neg (objᵒ X) ⊎ Pos (objᵒ Z)))
           → Obs ((playᵒ X Z d G.∘ (G.id G.⊗₁ f)) G.∘ cupᵒ X) ≈ₚ runˢ (unhomᵒ f) d
  play-cup X Z f d =
      runᴹ-resp-≈ᴹ (𝒫.∘-resp-≈ˡ (𝒫.∘-resp-≈ʳ (𝒫.Equiv.sym (T₁-⊗₁ f)))) (ask tt out)
    ⟨≈⟩ runᴹ-resp-≈ᴹ 𝒫.assoc (ask tt out)
    ⟨≈⟩ adequacy (dualᴵ (objᵒ X) ⊗ᴵ objᵒ Z) _ d
    ⟨≈⟩ cup-run f d

  reveal-∘≈ : (t : ifaceᵒ Bʳ G.⇒ Ωᵒ) (m : 𝟘ᵒ G.⇒ ifaceᵒ Aʳ)
            → (t G.∘ procᵒ (revealᴹ true)) G.∘ m G.≈ (t G.∘ procᵒ (revealᴹ false)) G.∘ m
  reveal-∘≈ t m = 𝒫.Equiv.trans 𝒫.assoc (𝒫.Equiv.trans (𝒫.∘-resp-≈ʳ (reveal-∘ m)) 𝒫.sym-assoc)

  reveal-≁ᴿ : ¬ (procᵒ (revealᴹ true) Q.∼ procᵒ (revealᴹ false))
  reveal-≁ᴿ = reveal-≉ᴿ

------------------------------------------------------------------------
-- The U-kernel is behavioural equality

T₁-≈ℰ⇒∼ᴿ : {f g : X G.⇒ Z} → Sᵒ.T₁ (dualᵒ X) f Sᵒ.≈ℰ Sᵒ.T₁ (dualᵒ X) g → f Q.∼ g
T₁-≈ℰ⇒∼ᴿ {X} {Z} {f} {g} e = ∼ᴿ-intro λ d →
  ∼ᴼ-resp (play-cup X Z f d) (play-cup X Z g d) (Sᵒ.KE.run∼ e {playᵒ X Z d} (cupᵒ X))

≈ᵁ⇒≈ᴿ : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → f Sᵒ.≈ᵁ g → f Q.∼ g
≈ᵁ⇒≈ᴿ {A} {X} {B} {f} {g} e =
  T₁-≈ℰ⇒∼ᴿ (Sᵒ.≈ℰ-trans (Sᵒ.≈ℰ-sym (unμ f))
             (Sᵒ.≈ℰ-trans (Sᵒ.≈ℰ-cong-post Sᵒ.α⇒ (e (dualᵒ A))) (unμ g)))
  where
  unμ : (h : A Sᵒ.⇒ Sᵒ.T₀ X B)
      → (Sᵒ.α⇒ Sᵒ.𝒞.∘ Sᵒ.μ (dualᵒ A) X Sᵒ.𝒞.∘ Sᵒ.T₁ (dualᵒ A) h) Sᵒ.≈ℰ Sᵒ.T₁ (dualᵒ A) h
  unμ h = Sᵒ.≈C⇒≈ℰ (Sᵒ.𝒞.cancelˡ Sᵒ.ℐ.associator.isoʳ)

------------------------------------------------------------------------
-- The bare kernel is not

reveal-≈ℰ : procᵒ (revealᴹ true) Sᵒ.≈ℰ procᵒ (revealᴹ false)
reveal-≈ℰ = Sᵒ.KE.mk∼ λ {t} m → Ap.zero⇒positive (≈ₚ⇒≈ₚ[0] (obs-resp (reveal-∘≈ t m)))

¬gradeStableᵒ : ¬ Sᵒ.GradeStable
¬gradeStableᵒ gs = reveal-≁ᴿ (T₁-≈ℰ⇒∼ᴿ (gs (dualᵒ (ifaceᵒ Aʳ)) reveal-≈ℰ))
