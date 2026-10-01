{-# OPTIONS --safe --without-K --guardedness #-}

-- The machine monoidal bundle behind an `opaque` seal, and the coercions across
-- it.  This is the whole reason a UC setup over `𝒢ₚ` is affordable: measured on
-- `spike-stduc-perf`, `open StdUC` at the TRANSPARENT bundle exhausts 12 GiB in
-- 50 s before any statement exists, and sealed the same text is at the 7 s
-- startup floor.  Four disciplines from that measurement are load-bearing.
--
--   1. ONE spelling of the index: `𝔾ᵒ` is the only name the setup is ever
--      given, and `∣𝔾ᵒ∣` is defined from it.
--   2. The seal is the WHOLE `MonoidalCategory` bundle.  Sealing only the
--      `monoidal` field measured 5.7× WORSE than sealing nothing, and passing a
--      re-assembled `record { U = …; monoidal = … }` OOMs at 8 GiB.
--   3. The coercions are exported from INSIDE the `opaque` block, the only
--      scope in which the seal is transparent, so a consumer needs no
--      `unfolding`.  One is exported per SHAPE: the type of a definition in an
--      `opaque` block is checked with the seal still closed (only its body sees
--      through), so the interface side of each type has to be spelled out.
--   4. The presheaf may be CONCRETE, because `ifaceᵒ` names objects of the seal
--      without breaking it (`UC.Model.Setup`).
--
-- `ifaceᵒ` is `Protocol.Machine.⟦_⟧ᴵ`, so a hom of the seal at interface objects
-- IS a `UC.Machine.Proc`; and `UC.Machine.retᴵ` inverts `⟦_⟧ᴵ` definitionally,
-- so a hom at an ARBITRARY object is one too (`objᵒ`, `untestᵒ`, `unclosᵒ`) —
-- which is what an ℰ-agreement's ancilla quantifier, ranging over every
-- object, needs from statements written at `Iface`.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle

open import Level
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine

module CategoricalCrypto.UC.Model.Seal where

opaque
  𝔾ᵒ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
  𝔾ᵒ = 𝒢ₚᴹ 0ℓ

∣𝔾ᵒ∣ : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
∣𝔾ᵒ∣ = MonoidalCategory.U 𝔾ᵒ

private
  module G = MonoidalCategory 𝔾ᵒ
  module M = Category (𝒢ₚ 0ℓ)

opaque
  unfolding 𝔾ᵒ

  -- The seal itself, as a PROPOSITIONAL equation.  A datum derived from the
  -- whole bundle rather than from a hom of it — its grading, say
  -- (`UC.Model.Enrichment`) — cannot be coerced by retyping, because the
  -- conversion checker meets two `MonoidalCategory` records and eta-expands
  -- both, forming the transparent bundle's law types (the header's 12 GiB).
  -- Transporting along this equation never forms them.
  sealᵒ : 𝔾ᵒ ≡ 𝒢ₚᴹ 0ℓ
  sealᵒ = refl

  ifaceᵒ : Iface → G.Obj
  ifaceᵒ A = ⟦ A ⟧ᴵ

  objᵒ : G.Obj → Iface
  objᵒ X = retᴵ X

  ifaceᵒ-onto : (X : G.Obj) → ifaceᵒ (objᵒ X) ≡ X
  ifaceᵒ-onto _ = refl

  procᵒ : {A B : Iface} → Proc A B → ifaceᵒ A G.⇒ ifaceᵒ B
  procᵒ f = f

  unprocᵒ : {A B : Iface} → ifaceᵒ A G.⇒ ifaceᵒ B → Proc A B
  unprocᵒ f = f

  ≈ᴹ⇒≈ᵒ : {A B : Iface} {f g : Proc A B} → 𝒢ₚ 0ℓ [ f ≈ g ] → procᵒ f G.≈ procᵒ g
  ≈ᴹ⇒≈ᵒ e = e

  ≈ᵒ⇒≈ᴹ : {A B : Iface} {f g : ifaceᵒ A G.⇒ ifaceᵒ B}
        → f G.≈ g → 𝒢ₚ 0ℓ [ unprocᵒ f ≈ unprocᵒ g ]
  ≈ᵒ⇒≈ᴹ e = e

  ⊗ᵒ : (A B : Iface) → ifaceᵒ A G.⊗₀ ifaceᵒ B ≡ ifaceᵒ (A ⊗ᴵ B)
  ⊗ᵒ _ _ = refl

  -- A graded hom: `T₀ X B` is `X ⊗₀ B`, whose tensor the seal hides.
  gradedᵒ : {A X B : Iface} → Proc A (X ⊗ᴵ B) → ifaceᵒ A G.⇒ ifaceᵒ X G.⊗₀ ifaceᵒ B
  gradedᵒ f = f

  -- The two halves of an ancilla context: a test on the ancilla beside a graded
  -- interface, and a closure of the ancilla beside the hole's domain.  Only the
  -- ancilla ranges over arbitrary objects; the rest comes from a statement
  -- written at `Iface`.
  untestᵒ : {P A B : Iface} (X : G.Obj)
          → X G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ A) G.⇒ ifaceᵒ B
          → Proc (objᵒ X ⊗ᴵ (P ⊗ᴵ A)) B
  untestᵒ _ E = E

  unclosᵒ : {A B : Iface} (X : G.Obj)
          → ifaceᵒ A G.⇒ X G.⊗₀ ifaceᵒ B → Proc A (objᵒ X ⊗ᴵ B)
  unclosᵒ _ m = m

  -- `procᵒ` is functorial on the nose; the seal hides that, so both directions
  -- are exported.
  unprocᵒ-∘ : {A B C : Iface} (g : Proc B C) (f : Proc A B)
            → 𝒢ₚ 0ℓ [ unprocᵒ (procᵒ g G.∘ procᵒ f) ≈ M._∘_ g f ]
  unprocᵒ-∘ _ _ = M.Equiv.refl

  -- …the same fact read the other way, which is what a machine-layer
  -- functoriality theorem has to cross to become a factoring INSIDE the seal
  -- (`Protocol.Machine.Compose.morphismCompose`, `UC.Seam.Grounded.factorᵖ`).
  -- Not derivable from `unprocᵒ-∘` outside: that would want `procᵒ ∘ unprocᵒ`.
  procᵒ-∘ : {A B C : Iface} (g : Proc B C) (f : Proc A B)
          → procᵒ (M._∘_ g f) G.≈ procᵒ g G.∘ procᵒ f
  procᵒ-∘ _ _ = G.Equiv.refl
