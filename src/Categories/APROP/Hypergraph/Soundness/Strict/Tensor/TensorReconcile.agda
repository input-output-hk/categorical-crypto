{-# OPTIONS --safe --without-K #-}

-- Tensor reconciliation needs a K-block braid, not left-frame separability:
-- see the left-frame obstruction in `ExtractPrefix.Properties`.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorReconcile
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  sig using (⟪⟫-cod-Unique)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig

open Perm using (_↭_)

module Reconcile {A B C D : ObjTerm}
  (f : HomTerm A B) (g : HomTerm C D)
  where
  private
    fg : HomTerm (A ⊗₀ C) (B ⊗₀ D)
    fg = f ⊗₁ g

    module RF = Run ⟪ fg ⟫
    module Hf = Hypergraph ⟪ fg ⟫

  BraidSigˢ : RF.s-finˢ ↭ Hf.cod → Set
  BraidSigˢ cand =
    RF.permuteˢ cand ∘ˢ proj₂ (Run.runˢ ⟪ fg ⟫)
      ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
          (decodePˢ f ⊗ˢ decodePˢ g)

  final-resortˢ
    : (cand : RF.s-finˢ ↭ Hf.cod)
    → RF.permuteˢ (finalPermˢ fg) ≈ˢ RF.permuteˢ cand
  final-resortˢ cand = RF.rigidˢ (⟪⟫-cod-Unique fg) (finalPermˢ fg) cand

  reconcile-from-braid
    : (cand : RF.s-finˢ ↭ Hf.cod) → BraidSigˢ cand → BraidSigˢ (finalPermˢ fg)
  reconcile-from-braid cand braidˢ = ≈-trans (∘-resp (final-resortˢ cand) ≈-refl) braidˢ

  decodePˢ-⊗-from-braid
    : (cand : RF.s-finˢ ↭ Hf.cod) → BraidSigˢ cand
    → decodePˢ fg ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
  decodePˢ-⊗-from-braid cand braidˢ =
    viaˢ (cast-≈̂ {p = ⟪⟫-domL fg} {q = ⟪⟫-codL fg})
         (reconcile-from-braid cand braidˢ)
         (≈̂-sym (cast-≈̂ {p = sym (⟪⟫-domL fg)} {q = sym (⟪⟫-codL fg)}))

