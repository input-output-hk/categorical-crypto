{-# OPTIONS --safe --without-K --guardedness #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Interchange.Braided as BI
import Categories.Morphism as Mor

open import Data.List.Base using (List; []; _++_)
open import Data.Product.Base using (_,_)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
import CategoricalCrypto.ND.Grade as Grade
open import CategoricalCrypto.ND.PM.Choice
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.PM.Factor.Read
open import CategoricalCrypto.ND.PM.Read
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.Model.Wire

import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.ND.PM.Choice.Compose where

private
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module P = Category 𝒫ᴵ
  module M = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module N = Grade 𝔾ˢ C
  variable
    A B D E : Iface
    S⃗ T⃗ : List Set

open Mor G.U
open G.HomReasoning

⌈⌉-resp : {p q : Proc⁺ S⃗ A B} → P._≈_ {A} {Cᶠ S⃗ ⊗ᴵ B} p q → ⌈_⌉ {S⃗} {A} {B} p G.≈ ⌈_⌉ {S⃗} {A} {B} q
⌈⌉-resp {S⃗} {A} {B} {p} {q} e = reads⇒≈ {x = ifaceᶠ A} {y = flat S⃗ ⊗ᶠ ifaceᶠ B}
  (reads-resp {x = ifaceᶠ A} {y = flat S⃗ ⊗ᶠ ifaceᶠ B} G.Equiv.refl e (reads-compile {S⃗} {A} {B} p)) (reads-compile {S⃗} {A} {B} q)

⌈⌉-plain : (p : Proc A B) → ⌈_⌉ {[]} {A} {B} (plain {A} {B} p) G.≈ G.unitorˡ.to G.∘ procᵒ p
⌈⌉-plain {A} {B} p = reads⇒≈ {x = ifaceᶠ A} {y = flat [] ⊗ᶠ ifaceᶠ B}
  (reads-compile {[]} {A} {B} (plain {A} {B} p))
  (reads-resp {x = ifaceᶠ A} {y = flat [] ⊗ᶠ ifaceᶠ B} (G.⊗.identity ⟩∘⟨refl ○ G.identityˡ) S.reflᴹ
    (reads-∘ {x = ifaceᶠ A} {y = unitᶠ ⊗ᶠ ifaceᶠ B} {z = flat [] ⊗ᶠ ifaceᶠ B}
      (reads-sub {x = unitᶠ} {y = flat []} {z = ifaceᶠ B} reads-nil)
      (reads-∘ {x = ifaceᶠ A} {y = ifaceᶠ B} {z = unitᶠ ⊗ᶠ ifaceᶠ B} (reads-λ⁻¹ (ifaceᶠ B)) (reads-proc p))))

⌈⌉-∘ : (q : Proc⁺ T⃗ B D) (p : Proc⁺ S⃗ A B)
       → ⌈_⌉ {S⃗ ++ T⃗} {A} {D} (_∘⁺_ {T⃗} {B} {D} {S⃗} {A} q p)
         G.≈ (N.C++.from S⃗ T⃗ G.⊗₁ G.id) G.∘ G.associator.to G.∘ (G.id G.⊗₁ ⌈_⌉ {T⃗} {B} {D} q) G.∘ ⌈_⌉ {S⃗} {A} {B} p
⌈⌉-∘ {T⃗} {B} {D} {S⃗} {A} q p = reads⇒≈ {x = ifaceᶠ A} {y = flat (S⃗ ++ T⃗) ⊗ᶠ ifaceᶠ D}
  (reads-compile {S⃗ ++ T⃗} {A} {D} (_∘⁺_ {T⃗} {B} {D} {S⃗} {A} q p))
  (reads-∘ {x = ifaceᶠ A} {y = (flat S⃗ ⊗ᶠ flat T⃗) ⊗ᶠ ifaceᶠ D} {z = flat (S⃗ ++ T⃗) ⊗ᶠ ifaceᶠ D}
    (reads-sub {x = flat S⃗ ⊗ᶠ flat T⃗} {y = flat (S⃗ ++ T⃗)} {z = ifaceᶠ D} (reads-C++ S⃗ T⃗))
    (reads-∘ {x = ifaceᶠ A} {y = flat S⃗ ⊗ᶠ (flat T⃗ ⊗ᶠ ifaceᶠ D)} {z = (flat S⃗ ⊗ᶠ flat T⃗) ⊗ᶠ ifaceᶠ D}
      (reads-α⁻¹ (flat S⃗) (flat T⃗) (ifaceᶠ D))
      (reads-∘ {x = ifaceᶠ A} {y = flat S⃗ ⊗ᶠ ifaceᶠ B} {z = flat S⃗ ⊗ᶠ (flat T⃗ ⊗ᶠ ifaceᶠ D)}
        (reads-T₁ {x = flat S⃗} {y = ifaceᶠ B} {z = flat T⃗ ⊗ᶠ ifaceᶠ D} (reads-compile {T⃗} {B} {D} q)) (reads-compile {S⃗} {A} {B} p))))

⌈⌉-⊗ : (p : Proc⁺ S⃗ A B) (q : Proc⁺ T⃗ D E)
       → ⌈_⌉ {S⃗ ++ T⃗} {A ⊗ᴵ D} {B ⊗ᴵ E} (_⊗⁺_ {S⃗} {A} {B} {T⃗} {D} {E} p q)
         G.≈ (G.id G.⊗₁ _≅_.from (⊗ᵒ≅ B E)) G.∘ (N.C++.from S⃗ T⃗ G.⊗₁ G.id)
           G.∘ BI.swapInner.from G.braided G.∘ (⌈_⌉ {S⃗} {A} {B} p G.⊗₁ ⌈_⌉ {T⃗} {D} {E} q) G.∘ _≅_.to (⊗ᵒ≅ A D)
⌈⌉-⊗ {S⃗} {A} {B} {T⃗} {D} {E} p q = reads⇒≈ {x = ifaceᶠ (A ⊗ᴵ D)} {y = flat (S⃗ ++ T⃗) ⊗ᶠ ifaceᶠ (B ⊗ᴵ E)}
  (reads-compile {S⃗ ++ T⃗} {A ⊗ᴵ D} {B ⊗ᴵ E} (_⊗⁺_ {S⃗} {A} {B} {T⃗} {D} {E} p q))
  (reads-resp {x = ifaceᶠ (A ⊗ᴵ D)} {y = flat (S⃗ ++ T⃗) ⊗ᶠ ifaceᶠ (B ⊗ᴵ E)} G.Equiv.refl
    (P.identityˡ {A ⊗ᴵ D} {Cᶠ (S⃗ ++ T⃗) ⊗ᴵ (B ⊗ᴵ E)})
    (reads-∘ {x = ifaceᶠ (A ⊗ᴵ D)} {y = flat (S⃗ ++ T⃗) ⊗ᶠ (ifaceᶠ B ⊗ᶠ ifaceᶠ E)} {z = flat (S⃗ ++ T⃗) ⊗ᶠ ifaceᶠ (B ⊗ᴵ E)}
      (reads-resp {x = flat (S⃗ ++ T⃗) ⊗ᶠ (ifaceᶠ B ⊗ᶠ ifaceᶠ E)} {y = flat (S⃗ ++ T⃗) ⊗ᶠ ifaceᶠ (B ⊗ᴵ E)} G.Equiv.refl
        (T₁-⊗₁ {Cᶠ (S⃗ ++ T⃗)} {B ⊗ᴵ E} {B ⊗ᴵ E} (P.id {B ⊗ᴵ E}) S.○ᴹ M.⊗.identity {⟦ Cᶠ (S⃗ ++ T⃗) ⟧ᴵ , ⟦ B ⊗ᴵ E ⟧ᴵ})
        (reads-T₁ {x = flat (S⃗ ++ T⃗)} {y = ifaceᶠ B ⊗ᶠ ifaceᶠ E} {z = ifaceᶠ (B ⊗ᴵ E)} (reads-⊗ᵒ B E)))
      (reads-∘ {x = ifaceᶠ (A ⊗ᴵ D)} {y = (flat S⃗ ⊗ᶠ flat T⃗) ⊗ᶠ (ifaceᶠ B ⊗ᶠ ifaceᶠ E)} {z = flat (S⃗ ++ T⃗) ⊗ᶠ (ifaceᶠ B ⊗ᶠ ifaceᶠ E)}
        (reads-sub {x = flat S⃗ ⊗ᶠ flat T⃗} {y = flat (S⃗ ++ T⃗)} {z = ifaceᶠ B ⊗ᶠ ifaceᶠ E} (reads-C++ S⃗ T⃗))
        (reads-∘ {x = ifaceᶠ (A ⊗ᴵ D)} {y = (flat S⃗ ⊗ᶠ ifaceᶠ B) ⊗ᶠ (flat T⃗ ⊗ᶠ ifaceᶠ E)} {z = (flat S⃗ ⊗ᶠ flat T⃗) ⊗ᶠ (ifaceᶠ B ⊗ᶠ ifaceᶠ E)}
          (reads-swapInner (flat S⃗) (ifaceᶠ B) (flat T⃗) (ifaceᶠ E))
          (reads-resp {x = ifaceᶠ (A ⊗ᴵ D)} {y = (flat S⃗ ⊗ᶠ ifaceᶠ B) ⊗ᶠ (flat T⃗ ⊗ᶠ ifaceᶠ E)} G.Equiv.refl
            (P.identityʳ {A ⊗ᴵ D} {(Cᶠ S⃗ ⊗ᴵ B) ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ E)})
            (reads-∘ {x = ifaceᶠ (A ⊗ᴵ D)} {y = ifaceᶠ A ⊗ᶠ ifaceᶠ D} {z = (flat S⃗ ⊗ᶠ ifaceᶠ B) ⊗ᶠ (flat T⃗ ⊗ᶠ ifaceᶠ E)}
              (reads-⊗ {x = ifaceᶠ A} {y = flat S⃗ ⊗ᶠ ifaceᶠ B} {z = ifaceᶠ D} {w = flat T⃗ ⊗ᶠ ifaceᶠ E}
                (reads-compile {S⃗} {A} {B} p) (reads-compile {T⃗} {D} {E} q)) (reads-⊗ᵒ⁻¹ A D)))))))
