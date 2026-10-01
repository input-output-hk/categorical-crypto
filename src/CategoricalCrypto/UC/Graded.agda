{-# OPTIONS --safe --without-K --guardedness #-}

-- Emulation at a NONTRIVIAL grade, from a machine-level factoring.
--
-- `UC.Seam.Grounded`'s `closedᵒ`/`stageᵒ` read a protocol image at the
-- TRIVIAL grade `𝟘ᴳ`, where every simulator is a scalar, blind to the run.
-- `UC.Model.Seal.gradedᵒ` reads a `Proc A (X ⊗ᴵ B)` as a hom
-- `ifaceᵒ A ⇒ T₀ (ifaceᵒ X) (ifaceᵒ B)` instead, and a simulator in front of it
-- is the relay `subᴵ` composed with it, so a factoring of the real process
-- through the simulator and the ideal one — one machine equality — is an
-- emulation at that grade with no error (`≤UCᵍ`).

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Positive
open import Data.Product.Base
open import Level

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Audit
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Graded
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.Graded where

private
  module M = Category (𝒢ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)

  variable A B C X Y : Iface

Factors : Proc A (X ⊗ᴵ B) → Proc Y X → Proc A (Y ⊗ᴵ B) → Set₁
Factors f s g = 𝒢ₚ 0ℓ [ f ≈ subᴵ s M.∘ g ]

-- `UC.Model.Graded`'s coercion lemmas re-typed into the setup's vocabulary
-- (`sub`, `unitorˡ`, `∘` of `UC.Model.Setup`), which `Model.Graded` cannot
-- open (see its header).
plug-graded : (a : Proc X 𝟭ᴵ) (f : Proc A (X ⊗ᴵ B))
            → unitorˡ.from ∘ (sub (procᵘ a) ∘ gradedᵒ f) ≈ procᵒ (plugᴹ a M.∘ f)
plug-graded = plug-gradedᵒ

-- …and the reading a COMPOSED system needs:
-- `UC.Model.Family.Contextual.Compose._∙ᶠ_` is `ext X k ∘ f`, and `ext` is
-- `α⇐ ∘ id ⊗₁ _` on the nose, so a stage plugged on top of a graded image is
-- again one machine composite.
ext-graded : {P : Iface} (k : Proc B (P ⊗ᴵ C)) (f : Proc A (X ⊗ᴵ B))
           → ext (ifaceᵒ X) (gradedᵒ k) ∘ gradedᵒ f
             ≈ graded₂ᵒ (a⇐ᴵ M.∘ T₁ᴵ X k M.∘ f)
ext-graded k f = Equiv.trans assoc (ext-gradedᵒ k f)

graded₂-∘ : {A′ P : Iface} (f : Proc A′ ((X ⊗ᴵ P) ⊗ᴵ C)) (g : Proc A A′)
          → graded₂ᵒ f ∘ procᵒ g ≈ graded₂ᵒ (f M.∘ g)
graded₂-∘ = graded₂-∘ᵒ

sub-graded₂ : {P : Iface} (s : Proc Y (X ⊗ᴵ P)) (g : Proc A (Y ⊗ᴵ C))
            → sub (gradedᵒ s) ∘ gradedᵒ g ≈ graded₂ᵒ (subᴵ s M.∘ g)
sub-graded₂ = sub-graded₂ᵒ

-- The grade `ifaceᵒ (X ⊗ᴵ P)` one `gradedᵒ` hands out and the grade
-- `ifaceᵒ X ⊗₀ ifaceᵒ P` that `UC.Model.Family.Contextual.Compose._∙ᶠ_`
-- produces are the same object, but the seal keeps them apart even for an
-- export's type (`UC.Model.Seal`'s header), so this wire — the identity
-- process read at the split grade — is the morphism between them.
flatᵍ : {P : Iface} → ifaceᵒ (X ⊗ᴵ P) ⇒ ifaceᵒ X ⊗₀ ifaceᵒ P
flatᵍ = gradedᵒ 𝒫.id

regrade : {P : Iface} (g : Proc A ((X ⊗ᴵ P) ⊗ᴵ C))
        → sub flatᵍ ∘ gradedᵒ g ≈ graded₂ᵒ g
regrade g =
  Equiv.trans (sub-graded₂ 𝒫.id g)
    (≈ᴹ⇒≈ᵍ₂ (𝒫.Equiv.trans
               (𝒫.∘-resp-≈ˡ (𝒫.Equiv.trans (sub-⊗₁ 𝒫.id) 𝔾.⊗.identity))
               𝒫.identityˡ))

emulᵍ : {f : Proc A (X ⊗ᴵ B)} {s : Proc Y X} {g : Proc A (Y ⊗ᴵ B)}
      → Factors f s g → gradedᵒ f ≈ᵁ sub (procᵒ s) ∘ gradedᵒ g
emulᵍ {s = s} {g} e = ≈C⇒≈ᵁ (Equiv.trans (≈ᴹ⇒≈ᵍ e) (Equiv.sym (sub-gradedᵒ s g)))

≤UCᵍ : {f : Proc A (X ⊗ᴵ B)} {s : Proc Y X} {g : Proc A (Y ⊗ᴵ B)}
     → Factors f s g → gradedᵒ f ≤UC gradedᵒ g
≤UCᵍ {s = s} e = dummy-complete (procᵒ s , emulᵍ e)

≤UC[]ᵍ : {f : Proc A (X ⊗ᴵ B)} {s : Proc Y X} {g : Proc A (Y ⊗ᴵ B)}
         {r : ℕ⁺} → QB (value r) s → Factors f s g → gradedᵒ f ≤UC[ r ] gradedᵒ g
≤UC[]ᵍ {s = s} q e = (procᵒ s , qbᵒ q) , emulᵍ e
