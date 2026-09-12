{-# OPTIONS --safe --without-K --guardedness #-}

-- Where a simulator goes when it leaves the process, spelled once at the model.
--
-- `Abstract2.Action.regradeEnv W s` is precomposition with `sub (id ⊗₁ s)`, and
-- `run-sub` is that fact in the environment SETOID.  A numerical consumer may
-- not spend it there: that setoid identifies tests only up to `∼ᴼ`, which keeps
-- no exact mass, so no `Pr` bound transports along it
-- (`docs/uc-presheaf-preservation-plan.md` §4.2).  `run-subᵒ` is the same slide
-- at REPRESENTATIVES, where `Abstract2.sub-decomp` proves it and an exact `≈ₚ`
-- does transport.
--
-- `slide⊗` is the ancilla-tensor spelling of the wire that lands in front of
-- the test, which is the vocabulary the prefix machinery speaks
-- (`UC.Seam.Grounded.subPrefixedˢ`) and the one `UC.Seam.Audit.Context` and
-- `UC.Seam.Audit.Prefix` consume.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (T₁-⊗)

open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)
open import CategoricalCrypto.UC.Model.Setup

module CategoricalCrypto.UC.Seam.Slide where

open import CategoricalCrypto.Abstract2.Action StdSetup using (Env; regradeEnv; run)

open HomReasoning

private variable A B C X Y : Channel

-- `run-sub` before the quotient: the simulator leaves the process and becomes
-- the single wire `sub (id ⊗₁ s)` in front of the test.
run-subᵒ : (W : Channel) (s : Y ⇒ X) (g : A ⇒ T₀ Y B) (e : Env (T₀ (W ⊗₀ X) B))
         → run W (sub s ∘ g) e ≈ run W g (regradeEnv W s e)
run-subᵒ W s g e = (refl⟩∘⟨ sub-decomp s g W) ○ sym-assoc

-- …and the ancilla's own action, where that wire is `id ⊗₁ _` and two of them
-- in sequence merge.
slide⊗ : (W : Channel) (h : B ⇒ C) (k : A ⇒ B) → id {W} ⊗₁ h ∘ id ⊗₁ k ≈ T₁ W (h ∘ k)
slide⊗ W h k = (⟺ (T₁-⊗ 𝔾ᵒ W h) ⟩∘⟨ ⟺ (T₁-⊗ 𝔾ᵒ W k)) ○ ⟺ T-homomorphism
