{-# OPTIONS --safe --without-K --guardedness #-}

-- PM[wb] (`docs/uc-setup-ssp.md` §4.2): the well-bracketed tests on `𝒲ᴹ`
-- (`ℰᵂ`), `𝒲ᴹ` quotiented by their two-sided ancilla kernel
-- (`Standard2.UKernel`), and the tests descended to the quotient.
--
--     ℰᵂ(A) = 𝒲(A , Ωᴵ) / ≋    t ≋ t′ ⟺ ∀ m : 𝒲(unitᴵ , A). Obsᵂ (t ∘ m) ∼ᵃ Obsᵂ (t′ ∘ m)
--
-- `Obsᵂ` is the model's readout `Obs` through two wires respelling SSP's
-- closed and verdict interfaces as the model's, so a well-bracketed test and
-- closure are observed exactly as protocol-rewrite observes them.  Kernel
-- equality is read off padded closures (`closures⇒∼`), or off agreement under
-- a family of maps every padded closure absorbs (`monitored⇒∼`).

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor
open import Categories.Functor.Presheaf

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UC.Bracket.Monoidal
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Machine hiding (Ωᴵ)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.Iface as Flat
import CategoricalCrypto.Standard2 as Std2
import CategoricalCrypto.Standard2.UKernel as UKernel

module CategoricalCrypto.UC.Bracket.Setup where

private
  module G = MonoidalCategory 𝔾ᵒ

------------------------------------------------------------------------
-- Well-bracketed tests

υʷ : Proc Flat.unitᴵ (flat unitᴵ)
υʷ = wireᴹ (λ ()) λ { (() , _) }

ωʷ : Proc (flat Ωᴵ) (Bool Flat.⇿ ⊤)
ωʷ = wireᴹ proj₂ λ _ → tt , tt

Obsᵂ : MonoidalCategory.U 𝒲ᴹ [ unitᴵ , Ωᴵ ] → Dₚ Bool
Obsᵂ (h , _) = Obs (procᵒ ωʷ G.∘ h G.∘ procᵒ υʷ)

qevaluationᵂ : QEvaluation (MonoidalCategory.U 𝒲ᴹ) 0ℓ 0ℓ
qevaluationᵂ = record
  { J = unitᴵ ; Ω = Ωᴵ ; X = spaceᴹ
  ; eval₀ = record { to = Obsᵂ ; cong = λ e → ≈ₚ⇒≈ₚ[0] (obs-resp (G.∘-resp-≈ʳ (G.∘-resp-≈ˡ e))) }
  }

evaluationᵂ : Evaluation (MonoidalCategory.U 𝒲ᴹ) 0ℓ 0ℓ
evaluationᵂ = qual₊ ℚ-refinement qevaluationᵂ

ℰᵂ : Presheaf (MonoidalCategory.U 𝒲ᴹ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᵂ = Observable.ℰᴼ (Evaluation.observable evaluationᵂ)

-- 𝒲[ℰᵂ]: well-bracketed machines under well-bracketed tests.
module 𝒲ᵂ = Std2.StdUC 𝒲ᴹ ℰᵂ

------------------------------------------------------------------------
-- PM[wb]

private module K = UKernel 𝒲ᴹ ℰᵂ

-- `K.uKernel` at one spelling of its level: its own, `suc 0ℓ ⊔ suc 0ℓ ⊔ suc 0ℓ`,
-- is not syntactically `suc 0ℓ`, and two spellings of one quotient are compared
-- by eta-expanding both records down to their law proofs (`q` exhausts 3 GiB).
uKernelᵂ : MonoidalCongruence 𝒲ᴹ (suc 0ℓ)
uKernelᵂ = K.uKernel

PM[wb]ᴹ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
PM[wb]ᴹ = quotient 𝒲ᴹ uKernelᵂ

-- Every use binds its implicit arguments: left to inference, they are solved by
-- unfolding `K._∼_` down to `ℰᵂ`'s tests (`q` past 90 s).
∼⇒≋ᵂ : {A B : Iface} {f g : MonoidalCategory.U 𝒲ᴹ [ A , B ]} → f K.∼ g
     → Setoids (suc 0ℓ) (suc 0ℓ) [ Functor.₁ ℰᵂ f ≈ Functor.₁ ℰᵂ g ]
∼⇒≋ᵂ {A} {B} {f} {g} e {t} = 𝒲ᵂ.KE.run∼ (K.∼⇒≈ℰ {A} {B} {f} {g} e) {t}

-- A map between the two ancillas of a kernel context.
pad : {Y A B Z : Iface} → A 𝒲ᵂ.⇒ B → (Y ⊗ᴵ A) ⊗ᴵ Z 𝒲ᵂ.⇒ (Y ⊗ᴵ B) ⊗ᴵ Z
pad {Y} {Z = Z} k = (𝒲ᵂ.id {Y} 𝒲ᵂ.⊗₁ k) 𝒲ᵂ.⊗₁ 𝒲ᵂ.id {Z}

pad-resp : {Y A B Z : Iface} {k l : A 𝒲ᵂ.⇒ B} → k 𝒲ᵂ.≈ l → pad {Y} {Z = Z} k 𝒲ᵂ.≈ pad l
pad-resp {Y} {Z = Z} {k} {l} e =
  𝒲ᵂ.⊗.F-resp-≈ {f = 𝒲ᵂ.id {Y} 𝒲ᵂ.⊗₁ k , 𝒲ᵂ.id {Z}} {g = 𝒲ᵂ.id 𝒲ᵂ.⊗₁ l , 𝒲ᵂ.id}
    (𝒲ᵂ.⊗.F-resp-≈ {f = 𝒲ᵂ.id {Y} , k} {g = 𝒲ᵂ.id , l} (G.Equiv.refl , e) , G.Equiv.refl)

pad-∘ : {Y A B C Z : Iface} (k : B 𝒲ᵂ.⇒ C) (l : A 𝒲ᵂ.⇒ B) → pad {Y} {Z = Z} (k 𝒲ᵂ.∘ l) 𝒲ᵂ.≈ pad k 𝒲ᵂ.∘ pad l
pad-∘ {Y} {Z = Z} k l = G.Equiv.trans
  (𝒲ᵂ.⊗.F-resp-≈ {f = 𝒲ᵂ.id {Y} 𝒲ᵂ.⊗₁ (k 𝒲ᵂ.∘ l) , 𝒲ᵂ.id {Z}}
                 {g = (𝒲ᵂ.id 𝒲ᵂ.⊗₁ k) 𝒲ᵂ.∘ (𝒲ᵂ.id 𝒲ᵂ.⊗₁ l) , 𝒲ᵂ.id 𝒲ᵂ.∘ 𝒲ᵂ.id}
    ( G.Equiv.trans (𝒲ᵂ.⊗.F-resp-≈ {f = 𝒲ᵂ.id {Y} , k 𝒲ᵂ.∘ l} {g = 𝒲ᵂ.id 𝒲ᵂ.∘ 𝒲ᵂ.id , k 𝒲ᵂ.∘ l}
                                    (G.Equiv.sym G.identity² , G.Equiv.refl))
                    (𝒲ᵂ.⊗.homomorphism {f = 𝒲ᵂ.id {Y} , l} {g = 𝒲ᵂ.id , k})
    , G.Equiv.sym G.identity²))
  (𝒲ᵂ.⊗.homomorphism {f = 𝒲ᵂ.id {Y} 𝒲ᵂ.⊗₁ l , 𝒲ᵂ.id {Z}} {g = 𝒲ᵂ.id 𝒲ᵂ.⊗₁ k , 𝒲ᵂ.id})

-- `ℰᵂ` reads a test only after a closure, so maps that agree after every padded
-- closure are kernel-equal.
closures⇒∼ : {A B : Iface} {f g : A 𝒲ᵂ.⇒ B}
           → (∀ Y Z (c : unitᴵ 𝒲ᵂ.⇒ (Y ⊗ᴵ A) ⊗ᴵ Z) → pad {Y} {Z = Z} f 𝒲ᵂ.∘ c 𝒲ᵂ.≈ pad g 𝒲ᵂ.∘ c)
           → f K.∼ g
closures⇒∼ {f = f} {g} h Y Z = 𝒲ᵂ.KE.mk∼ λ {t} c →
  Evaluation.read-resp evaluationᵂ {(t 𝒲ᵂ.∘ pad f) 𝒲ᵂ.∘ c} {(t 𝒲ᵂ.∘ pad g) 𝒲ᵂ.∘ c}
    (G.assoc ○ (refl⟩∘⟨ h Y Z c) ○ G.sym-assoc)
  where open G.HomReasoning

-- A family of maps every padded closure absorbs turns agreement under it into
-- kernel equality: each copy is absorbed by the closure below it.
monitored⇒∼ : (E : ∀ {A} → A 𝒲ᵂ.⇒ A)
            → (∀ {Y A Z} (c : unitᴵ 𝒲ᵂ.⇒ (Y ⊗ᴵ A) ⊗ᴵ Z) → pad {Y} {Z = Z} (E {A}) 𝒲ᵂ.∘ c 𝒲ᵂ.≈ c)
            → {A B : Iface} {f g : A 𝒲ᵂ.⇒ B} → E {B} 𝒲ᵂ.∘ f 𝒲ᵂ.∘ E {A} 𝒲ᵂ.≈ E {B} 𝒲ᵂ.∘ g 𝒲ᵂ.∘ E {A} → f K.∼ g
monitored⇒∼ E absorb {A} {B} {f} {g} e = closures⇒∼ chain
  where
  open G.HomReasoning
  mon : A 𝒲ᵂ.⇒ B → A 𝒲ᵂ.⇒ B
  mon k = E {B} 𝒲ᵂ.∘ k 𝒲ᵂ.∘ E {A}
  chain : ∀ Y Z (c : unitᴵ 𝒲ᵂ.⇒ (Y ⊗ᴵ A) ⊗ᴵ Z) → pad {Y} {Z = Z} f 𝒲ᵂ.∘ c 𝒲ᵂ.≈ pad g 𝒲ᵂ.∘ c
  chain Y Z c = begin
    proj₁ (pad f 𝒲ᵂ.∘ c)                                      ≈⟨ refl⟩∘⟨ ⟺ (absorb c) ⟩
    proj₁ (pad f 𝒲ᵂ.∘ pad (E {A}) 𝒲ᵂ.∘ c)                     ≈⟨ ⟺ (absorb (pad f 𝒲ᵂ.∘ pad (E {A}) 𝒲ᵂ.∘ c)) ⟩
    proj₁ (pad (E {B}) 𝒲ᵂ.∘ pad f 𝒲ᵂ.∘ pad (E {A}) 𝒲ᵂ.∘ c)   ≈⟨ ⟺ (unpad f) ⟩
    proj₁ (pad (mon f) 𝒲ᵂ.∘ c)                                ≈⟨ pad-resp {Y} {A} {B} {Z} {mon f} {mon g} e ⟩∘⟨refl ⟩
    proj₁ (pad (mon g) 𝒲ᵂ.∘ c)                                ≈⟨ unpad g ⟩
    proj₁ (pad (E {B}) 𝒲ᵂ.∘ pad g 𝒲ᵂ.∘ pad (E {A}) 𝒲ᵂ.∘ c)   ≈⟨ absorb (pad g 𝒲ᵂ.∘ pad (E {A}) 𝒲ᵂ.∘ c) ⟩
    proj₁ (pad g 𝒲ᵂ.∘ pad (E {A}) 𝒲ᵂ.∘ c)                     ≈⟨ refl⟩∘⟨ absorb c ⟩
    proj₁ (pad g 𝒲ᵂ.∘ c)                                      ∎
    where
    unpad : (k : A 𝒲ᵂ.⇒ B) → proj₁ (pad (mon k) 𝒲ᵂ.∘ c) G.≈ proj₁ (pad (E {B}) 𝒲ᵂ.∘ pad k 𝒲ᵂ.∘ pad (E {A}) 𝒲ᵂ.∘ c)
    unpad k = ((pad-∘ (E {B}) (k 𝒲ᵂ.∘ E {A}) ○ (refl⟩∘⟨ pad-∘ k (E {A}))) ⟩∘⟨refl) ○ G.assoc ○ (refl⟩∘⟨ G.assoc)

ℰ[wb] : Presheaf (MonoidalCategory.U PM[wb]ᴹ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰ[wb] = descend 𝒲ᴹ uKernelᵂ ℰᵂ λ {A} {B} {f} {g} → ∼⇒≋ᵂ {A} {B} {f} {g}

open Std2.StdUC PM[wb]ᴹ ℰ[wb] public

q : UCSetupMorphism 𝒲ᵂ.StdSetup StdSetup
q = StdUCMorphism 𝒲ᴹ PM[wb]ᴹ ℰᵂ ℰ[wb] (quotientF 𝒲ᴹ uKernelᵂ)
      (descendᵛ 𝒲ᴹ uKernelᵂ ℰᵂ λ {A} {B} {f} {g} → ∼⇒≋ᵂ {A} {B} {f} {g})
