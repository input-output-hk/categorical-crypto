{-# OPTIONS --safe --without-K --guardedness #-}

-- The seal's coercions for a NONTRIVIALLY graded process image.
--
-- `UC.Model.Seal.gradedᵒ` already crosses the seal for the object part: a
-- `Proc A (X ⊗ᴵ B)` — a process with an adversary interface `X` beside its
-- honest one — is a hom `ifaceᵒ A ⇒ ifaceᵒ X ⊗₀ ifaceᵒ B`, i.e. a graded hom at
-- the grade `ifaceᵒ X`.  What was missing is the two facts a UC statement about
-- such a hom needs, and neither is derivable outside the block: that `gradedᵒ`
-- respects the machine equality, and that the grading's `sub` acting on it is
-- the machine-layer relay `subᴵ` composed with it.
--
-- The three below them are the same exports for an adversary machine FILLING
-- that grade: its codomain is the bundle's unit, which `UC.Machine.Dictionary`
-- names `𝟭ᴵ` on the machine side and the seal hides on the other, so `procᵒ`
-- does not serve and `plug-gradedᵒ` is what says the filled grade is a machine
-- composite.
--
-- All five are `UC.Model.Seal`'s third discipline (export from inside, one
-- export per shape).  The statements are written in the bundle's own vocabulary
-- rather than in `StdUC`'s, because `unfolding 𝔾ᵒ` in a module that opens
-- `StdUC` is the 12 GiB configuration `UC.Model.Enrichment`'s header records;
-- `UC.Graded` is where they are read as statements about `sub`.

open import Categories.Category using (Category; _[_≈_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base using (ℕ)
open import Level using (0ℓ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚ)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Machine using (Proc; subᴵ′)
open import CategoricalCrypto.UC.Machine.Dictionary using (sub-⊗₁; λ⇒-λᴳ; 𝟭ᴵ)
open import CategoricalCrypto.UC.Machine.Plug using (plugᴹ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ; gradedᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.QueryBound using (QB)
open import CategoricalCrypto.UC.QueryBound.Object using (qb-to-image)

module CategoricalCrypto.UC.Model.Graded where

private
  module G = MonoidalCategory 𝔾ᵒ
  module M = Category (𝒢ₚ 0ℓ)

opaque
  unfolding gradedᵒ

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

  -- An adversary machine filling the grade.  Its codomain is the bundle's own
  -- unit, which `UC.Machine.Dictionary.𝟭ᴵ` names on the machine side and the
  -- seal hides — hence a coercion of its own rather than `procᵒ`.
  procᵘ : {X : Iface} → Proc X 𝟭ᴵ → ifaceᵒ X G.⇒ G.unit
  procᵘ a = a

  qbᵘ : {X : Iface} {c : ℕ} {a : Proc X 𝟭ᴵ} → QB c a → Budget.QB budgetᵒ c (procᵘ a)
  qbᵘ {X} = qb-to-image X 𝟭ᴵ

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
