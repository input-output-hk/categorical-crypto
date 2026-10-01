{-# OPTIONS --safe --without-K --guardedness #-}

-- The seal's coercions for a NONTRIVIALLY graded process image, exported from
-- inside the block (`UC.Model.Seal`'s third discipline, one export per shape).
-- They are stated in the bundle's own vocabulary rather than in `StdUC`'s,
-- because `unfolding 𝔾ᵒ` in a module that opens `StdUC` is the 12 GiB
-- configuration `UC.Model.Enrichment`'s header records; `UC.Graded` is where
-- they are read as statements about `sub`.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle

open import Level

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.Model.Graded where

private
  module G = MonoidalCategory 𝔾ᵒ
  module M = Category (𝒢ₚ 0ℓ)

opaque
  unfolding gradedᵒ procᵘ

  ≈ᴹ⇒≈ᵍ : {A X B : Iface} {f g : Proc A (X ⊗ᴵ B)}
        → 𝒢ₚ 0ℓ [ f ≈ g ] → gradedᵒ f G.≈ gradedᵒ g
  ≈ᴹ⇒≈ᵍ e = e

  -- The grading's `sub` is the machine layer's own relay: `sub c` is `c ⊗₁ id`
  -- (`CurriedTensor.Properties.sub-⊗`) and `subᴵ` is that tensor read at
  -- interface objects (`UC.Machine.Dictionary.sub-⊗₁`), so a simulator standing
  -- in front of a graded image is one machine composite.
  sub-gradedᵒ : {A B X Y : Iface} (s : Proc X Y) (g : Proc A (X ⊗ᴵ B))
              → ((procᵒ s G.⊗₁ G.id {ifaceᵒ B}) G.∘ gradedᵒ g)
                G.≈ gradedᵒ (M._∘_ (subᴵ {X} {Y} {B} s) g)
  sub-gradedᵒ s g = G.∘-resp-≈ˡ (G.Equiv.sym (sub-⊗₁ s))

  -- The shape a COMPOSED system has; a separate export because the seal hides
  -- the tensor (see `UC.Graded.flatᵍ`).
  graded₂ᵒ : {A X P C : Iface} → Proc A ((X ⊗ᴵ P) ⊗ᴵ C)
           → ifaceᵒ A G.⇒ (ifaceᵒ X G.⊗₀ ifaceᵒ P) G.⊗₀ ifaceᵒ C
  graded₂ᵒ f = f

  ≈ᴹ⇒≈ᵍ₂ : {A X P C : Iface} {f g : Proc A ((X ⊗ᴵ P) ⊗ᴵ C)}
         → 𝒢ₚ 0ℓ [ f ≈ g ] → graded₂ᵒ f G.≈ graded₂ᵒ g
  ≈ᴹ⇒≈ᵍ₂ e = e

  graded₂-∘ᵒ : {A A′ X P C : Iface} (f : Proc A′ ((X ⊗ᴵ P) ⊗ᴵ C)) (g : Proc A A′)
             → (graded₂ᵒ f G.∘ procᵒ g) G.≈ graded₂ᵒ (M._∘_ f g)
  graded₂-∘ᵒ _ _ = G.Equiv.refl

  -- `sub-gradedᵒ` at a simulator whose own codomain is a tensor, which is what
  -- a JOINT simulator for a composed system is (`docs/coin-toss.md` §5).
  sub-graded₂ᵒ : {A X P Y C : Iface} (s : Proc Y (X ⊗ᴵ P)) (g : Proc A (Y ⊗ᴵ C))
               → ((gradedᵒ s G.⊗₁ G.id {ifaceᵒ C}) G.∘ gradedᵒ g)
                 G.≈ graded₂ᵒ (M._∘_ (subᴵ {Y} {X ⊗ᴵ P} {C} s) g)
  sub-graded₂ᵒ s g = G.∘-resp-≈ˡ (G.Equiv.sym (sub-⊗₁ s))

  -- A stage plugged ON TOP of a graded image (see `UC.Graded.ext-graded`): not
  -- derivable outside the seal.
  ext-gradedᵒ : {A B C P X : Iface} (k : Proc B (P ⊗ᴵ C)) (f : Proc A (X ⊗ᴵ B))
              → (G.associator.to G.∘ ((G.id {ifaceᵒ X} G.⊗₁ gradedᵒ k) G.∘ gradedᵒ f))
                G.≈ graded₂ᵒ (M._∘_ (a⇐ᴵ {X} {P} {C}) (M._∘_ (T₁ᴵ X k) f))
  ext-gradedᵒ k f =
    G.∘-resp-≈ (G.Equiv.sym a⇐-α⇐) (G.∘-resp-≈ˡ (G.Equiv.sym (T₁-⊗₁ k)))

  procᵘ-∘ : {X Y : Iface} (a : Proc X 𝟭ᴵ) (s : Proc Y X)
          → procᵘ (M._∘_ a s) G.≈ procᵘ a G.∘ procᵒ s
  procᵘ-∘ _ _ = G.Equiv.refl

  -- The filled grade is the unit, which the unitor deflates (`λ⇒-λᴳ` is that
  -- unitor as a wire): the graded reading of `UC.Seam.Grounded.plug-run`'s
  -- `unprocᵒ-∘`.
  plug-gradedᵒ : {A B X : Iface} (a : Proc X 𝟭ᴵ) (f : Proc A (X ⊗ᴵ B))
               → (G.unitorˡ.from G.∘ ((procᵘ a G.⊗₁ G.id {ifaceᵒ B}) G.∘ gradedᵒ f))
                 G.≈ procᵒ (M._∘_ (plugᴹ a) f)
  plug-gradedᵒ a f =
    G.Equiv.trans (G.∘-resp-≈ (G.Equiv.sym λ⇒-λᴳ) (G.∘-resp-≈ˡ (G.Equiv.sym (sub-⊗₁ a))))
                  G.sym-assoc
