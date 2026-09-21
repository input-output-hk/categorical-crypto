{-# OPTIONS --safe --without-K --guardedness #-}

-- The seal's coercions for a NONTRIVIALLY graded process image.
--
-- `UC.Model.Seal.gradedᵒ` already crosses the seal for the object part: a
-- `Proc A (X ⊗ᴵ B)` — a process with an adversary interface `X` beside its
-- honest one — is a hom `ifaceᵒ A ⇒ ifaceᵒ X ⊗₀ ifaceᵒ B`, i.e. a graded hom at
-- the grade `ifaceᵒ X`.  What was missing is the three facts a UC statement
-- about such a hom needs, none of them derivable outside the block: that
-- `gradedᵒ` respects the machine equality, that the grading's `sub` acting on
-- it is the machine-layer relay `subᴵ` composed with it, and that a process
-- plugged under it leaves one machine composite.
--
-- `graded₂ᵒ` and the four exports around it are the same facts for a stage
-- plugged ON TOP of such a hom, which is what `UC.Asymptotic.Compose._∙ᶠ_`
-- builds: its grade is a tensor, so it needs its own coercion, and composing
-- a closed process under it, a joint simulator in front of it, or a stage over
-- it each leaves one machine composite.
--
-- The two below them are the same exports for an adversary machine FILLING
-- that grade, whose own coercion `procᵘ` is `UC.Model.Enrichment`'s (it is
-- inseparable from its certificate there): `plug-gradedᵒ` is what says the
-- filled grade is a machine composite.
--
-- All ten are `UC.Model.Seal`'s third discipline (export from inside, one
-- export per shape).  The statements are written in the bundle's own vocabulary
-- rather than in `StdUC`'s, because `unfolding 𝔾ᵒ` in a module that opens
-- `StdUC` is the 12 GiB configuration `UC.Model.Enrichment`'s header records;
-- `UC.Graded` is where they are read as statements about `sub`.

open import Categories.Category using (Category; _[_≈_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚ)
open import CategoricalCrypto.UC.Machine using (Proc; T₁ᴵ; a⇒ᴵ; subᴵ′)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁; a⇒-α⇐; sub-⊗₁; λ⇒-λᴳ; 𝟭ᴵ)
open import CategoricalCrypto.UC.Machine.Plug using (plugᴹ)
open import CategoricalCrypto.UC.Model.Enrichment using (procᵘ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; gradedᵒ; ifaceᵒ; procᵒ)

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
                G.≈ gradedᵒ (M._∘_ (subᴵ′ {X} {Y} {B} s) g)
  sub-gradedᵒ s g = G.∘-resp-≈ˡ (G.Equiv.sym (sub-⊗₁ s))

  -- A process plugged UNDER such a hom — a resource installed below a graded
  -- system — leaves one machine composite, which is the `Proc` form
  -- `UC.Model.Dominated.dominatedᵍᵠ` consumes.
  graded-∘ᵒ : {A A′ X B : Iface} (f : Proc A′ (X ⊗ᴵ B)) (g : Proc A A′)
            → (gradedᵒ f G.∘ procᵒ g) G.≈ gradedᵒ (M._∘_ f g)
  graded-∘ᵒ _ _ = G.Equiv.refl

  -- The graded image of a process whose grade is already a tensor, which is the
  -- shape a COMPOSED system has.  A separate export because the seal hides the
  -- tensor and the bracketing is what distinguishes it (`UC.Model.Seal`'s third
  -- discipline: one export per shape).
  graded₂ᵒ : {A X P C : Iface} → Proc A ((X ⊗ᴵ P) ⊗ᴵ C)
           → ifaceᵒ A G.⇒ (ifaceᵒ X G.⊗₀ ifaceᵒ P) G.⊗₀ ifaceᵒ C
  graded₂ᵒ f = f

  ≈ᴹ⇒≈ᵍ₂ : {A X P C : Iface} {f g : Proc A ((X ⊗ᴵ P) ⊗ᴵ C)}
         → 𝒢ₚ 0ℓ [ f ≈ g ] → graded₂ᵒ f G.≈ graded₂ᵒ g
  ≈ᴹ⇒≈ᵍ₂ e = e

  -- `graded-∘ᵒ` at a tensor grade.
  graded₂-∘ᵒ : {A A′ X P C : Iface} (f : Proc A′ ((X ⊗ᴵ P) ⊗ᴵ C)) (g : Proc A A′)
             → (graded₂ᵒ f G.∘ procᵒ g) G.≈ graded₂ᵒ (M._∘_ f g)
  graded₂-∘ᵒ _ _ = G.Equiv.refl

  -- `sub-gradedᵒ` at a simulator whose own codomain is a tensor, which is what
  -- a JOINT simulator for a composed system is (`docs/coin-toss.md` §5).
  sub-graded₂ᵒ : {A X P Y C : Iface} (s : Proc Y (X ⊗ᴵ P)) (g : Proc A (Y ⊗ᴵ C))
               → ((gradedᵒ s G.⊗₁ G.id {ifaceᵒ C}) G.∘ gradedᵒ g)
                 G.≈ graded₂ᵒ (M._∘_ (subᴵ′ {Y} {X ⊗ᴵ P} {C} s) g)
  sub-graded₂ᵒ s g = G.∘-resp-≈ˡ (G.Equiv.sym (sub-⊗₁ s))

  -- …and a stage plugged ON TOP of a graded image, which is what
  -- `UC.Asymptotic.Compose._∙ᶠ_` is: `ext X k ∘ f`, with `ext` read as
  -- `μ ∘ T₁` (`GradedKleisli.μT`) and `μ` as the associator
  -- (`CurriedTensor.Properties.μ-α⇐`).  Both of those are outside the seal;
  -- what is not derivable there is that the result is one machine composite.
  ext-gradedᵒ : {A B C P X : Iface} (k : Proc B (P ⊗ᴵ C)) (f : Proc A (X ⊗ᴵ B))
              → (G.associator.to G.∘ ((G.id {ifaceᵒ X} G.⊗₁ gradedᵒ k) G.∘ gradedᵒ f))
                G.≈ graded₂ᵒ (M._∘_ (a⇒ᴵ {X} {P} {C}) (M._∘_ (T₁ᴵ X k) f))
  ext-gradedᵒ k f =
    G.∘-resp-≈ (G.Equiv.sym a⇒-α⇐) (G.∘-resp-≈ˡ (G.Equiv.sym (T₁-⊗₁ k)))

  -- A simulator in front of an adversary is again an adversary.
  procᵘ-∘ : {X Y : Iface} (a : Proc X 𝟭ᴵ) (s : Proc Y X)
          → procᵘ (M._∘_ a s) G.≈ procᵘ a G.∘ procᵒ s
  procᵘ-∘ _ _ = G.Equiv.refl

  -- …and what is left once it has: the grade is the unit, the unitor deflates
  -- it (`λ⇒-λᴳ` is that unitor as a wire), and the whole is one machine
  -- composite.  This is the graded reading of `UC.Seam.Grounded.plug-run`'s
  -- `unprocᵒ-∘` — with the grade filled rather than absent.
  plug-gradedᵒ : {A B X : Iface} (a : Proc X 𝟭ᴵ) (f : Proc A (X ⊗ᴵ B))
               → (G.unitorˡ.from G.∘ ((procᵘ a G.⊗₁ G.id {ifaceᵒ B}) G.∘ gradedᵒ f))
                 G.≈ procᵒ (M._∘_ (plugᴹ a) f)
  plug-gradedᵒ a f =
    G.Equiv.trans (G.∘-resp-≈ (G.Equiv.sym λ⇒-λᴳ) (G.∘-resp-≈ˡ (G.Equiv.sym (sub-⊗₁ a))))
                  G.sym-assoc
