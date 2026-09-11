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
--      scope in which the seal is transparent.  A consumer then needs no
--      `unfolding`.  The seal hides `_⊗₀_` as well, so the tensor equation
--      below has to be exported too — it is not derivable outside.
--   4. The presheaf may be CONCRETE, because `ifaceᵒ` names objects of the seal
--      without breaking it (`UC.Model.Environment`).
--
-- `ifaceᵒ` is `Protocol.Machine.⟦_⟧ᴵ`, so a hom of the seal at interface
-- objects IS a `UC.Machine.Proc` and its equality IS the machine layer's
-- simulation closure; that is what `unprocᵒ`/`≈ᵒ⇒≈ᴹ` say, and it is what lets
-- the observation reuse the existing closed run verbatim.
--
-- `ifaceᵒ` is also ONTO, and that is the second half of the same fact:
-- `UC.Machine.retᴵ` inverts `⟦_⟧ᴵ` definitionally, so `objᵒ` below is a section
-- and a hom at an ARBITRARY object of the seal is a `Proc` too.  An
-- ℰ-agreement's ancilla quantifier ranges over every object, where the machine
-- layer's statements are written at `Iface` — the asymmetry `UC.Seam.Grounding`'s
-- header records — and `untestᵒ`/`unclosᵒ` are what removes it.  A coercion is
-- exported per SHAPE rather than generically because the type of a definition
-- in an `opaque` block is checked with the seal still closed (only its body
-- sees through), so the interface side of each type has to be spelled out.

open import Categories.Category using (Category; _[_≈_])
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Level using (0ℓ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚ; 𝒢ₚᴹ)
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine using (Proc; retᴵ)

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
  -- whole bundle rather than from a hom of it — a `Budget` for the grading
  -- `gradingᵗ 𝔾ᵒ`, say (`UC.Model.Enrichment`) — cannot be coerced by
  -- retyping, because the conversion checker meets two `Grading` records and
  -- eta-expands both, forming the thirteen law types the transparent grading
  -- is unaffordable at (`UC.Machine`'s header).  Transporting along this
  -- equation never forms them.
  sealᵒ : 𝔾ᵒ ≡ 𝒢ₚᴹ 0ℓ
  sealᵒ = refl

  ifaceᵒ : Iface → G.Obj
  ifaceᵒ A = ⟦ A ⟧ᴵ

  -- …and its section: `Iface` and the bundle's objects are both eta records,
  -- so `retᴵ` is a definitional inverse (`UC.Machine`'s header).
  objᵒ : G.Obj → Iface
  objᵒ X = retᴵ X

  ifaceᵒ-onto : (X : G.Obj) → ifaceᵒ (objᵒ X) ≡ X
  ifaceᵒ-onto _ = refl

  procᵒ : {A B : Iface} → Proc A B → ifaceᵒ A G.⇒ ifaceᵒ B
  procᵒ f = f

  unprocᵒ : {A B : Iface} → ifaceᵒ A G.⇒ ifaceᵒ B → Proc A B
  unprocᵒ f = f

  ≈ᴹ⇒≈ᵒ : {A B : Iface} {f g : Proc A B}
        → 𝒢ₚ 0ℓ [ f ≈ g ] → procᵒ f G.≈ procᵒ g
  ≈ᴹ⇒≈ᵒ e = e

  ≈ᵒ⇒≈ᴹ : {A B : Iface} {f g : ifaceᵒ A G.⇒ ifaceᵒ B}
        → f G.≈ g → 𝒢ₚ 0ℓ [ unprocᵒ f ≈ unprocᵒ g ]
  ≈ᵒ⇒≈ᴹ e = e

  -- The tensor, which the seal also hides: on interface objects it is the
  -- interface tensor layer 0 already defines.
  ⊗ᵒ : (A B : Iface) → ifaceᵒ A G.⊗₀ ifaceᵒ B ≡ ifaceᵒ (A ⊗ᴵ B)
  ⊗ᵒ _ _ = refl

  -- …hence the coercion a graded hom needs: `A ⇒ T₀ X B` is `A ⇒ X ⊗₀ B`, and
  -- the seal hides that tensor, so this is not derivable outside.
  gradedᵒ : {A X B : Iface} → Proc A (X ⊗ᴵ B) → ifaceᵒ A G.⇒ ifaceᵒ X G.⊗₀ ifaceᵒ B
  gradedᵒ f = f

  -- The two halves of an ancilla context, at an ARBITRARY ancilla: a test on
  -- the ancilla beside a graded interface, and a closure of the ancilla beside
  -- the hole's domain.  The ancilla is the quantifier that has to be general;
  -- the grade and the interfaces come from the statement being read, which is
  -- written at `Iface`.
  untestᵒ : {P A B : Iface} (X : G.Obj)
          → X G.⊗₀ (ifaceᵒ P G.⊗₀ ifaceᵒ A) G.⇒ ifaceᵒ B
          → Proc (objᵒ X ⊗ᴵ (P ⊗ᴵ A)) B
  untestᵒ _ E = E

  unclosᵒ : {A B : Iface} (X : G.Obj)
          → ifaceᵒ A G.⇒ X G.⊗₀ ifaceᵒ B → Proc A (objᵒ X ⊗ᴵ B)
  unclosᵒ _ m = m

  -- `procᵒ` is functorial on the nose, and the seal hides that too.  This is
  -- what lets the model's closed run read a COMPOSITE of the seal as the
  -- machine composite it is (`UC.Seam.Grounded.plug-run`).
  unprocᵒ-∘ : {A B C : Iface} (g : Proc B C) (f : Proc A B)
            → 𝒢ₚ 0ℓ [ unprocᵒ (procᵒ g G.∘ procᵒ f) ≈ M._∘_ g f ]
  unprocᵒ-∘ _ _ = M.Equiv.refl
