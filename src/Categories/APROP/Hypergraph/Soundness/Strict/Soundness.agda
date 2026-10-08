{-# OPTIONS --safe --without-K #-}

-- Soundness through strictification and the unflatten bridge.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Soundness
  (sig : APROPSignature)
  where

open APROP sig
open FreeMonoidalHelper Symm X using (flatten)

open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flat-rec)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; _≅_; bridge; subst-id-cod)
open import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence sig
  using ( bridge-∘; bridge-⊗; bridge-id-is-id; bridge-λ⇒-is-id; bridge-λ⇐-is-id
        ; ρ⇒-coherence; ρ⇐-coherence; module Worker )

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig
import Categories.APROP.Hypergraph.Soundness.Strict.Embed sig as E
import Categories.APROP.Hypergraph.Soundness.Strict.PartI  sig as PI
import Categories.APROP.Hypergraph.Soundness.Strict.PartII sig as PII
open import Categories.Category

open import Categories.FreeStrictSMC
open import Categories.Morphism.Reasoning FreeMonoidal
open import Data.List.Properties

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

-- The record's (relevant) boundary proofs coerce the generator's
-- `bridge (Agen g)` onto the declared (possibly non-`flatten`-shaped)
-- boundary indices `as`/`bs`.
J-flat : ∀ {as bs} → FlatGen as bs → HomTerm (unflatten as) (unflatten bs)
J-flat (flat-rec {A} {B} oa ob g) =
  subst₂ (λ a b → HomTerm (unflatten a) (unflatten b))
    oa ob (bridge (Agen g))

open Map X _≟X_ FlatGen E.morL J-flat using (mapS; mapS-resp)

embF : ∀ {xs ys} → HomS xs ys → HomTerm (unflatten xs) (unflatten ys)
embF t = E.emb (mapS t)

embF-resp-≈ˢ : ∀ {xs ys} {f g : HomS xs ys} → f ≈ˢ g → embF f ≈Term embF g
embF-resp-≈ˢ e = E.EmbRespFull.emb-resp-≈ˢ (mapS-resp e)

private
  embF-coe : ∀ {a b : List X} (e : a ≡ b) → embF (coe e) ≡ subst-id-cod e
  embF-coe refl = refl

st-roundtrip : ∀ {A B} (f : HomTerm A B) → embF (st f) ≈Term bridge f
st-roundtrip (Agen g)  = ≈-Term-refl
st-roundtrip (id {A})  = ⟺ (bridge-id-is-id A)
st-roundtrip (g ∘ f)   =
  (st-roundtrip g ⟩∘⟨ st-roundtrip f) ○ ⟺ (bridge-∘ g f)
st-roundtrip (f ⊗₁ g)  =
  (refl⟩∘⟨ (⊗-resp-≈ (st-roundtrip f) (st-roundtrip g) ⟩∘⟨refl))
  ○ ⟺ (bridge-⊗ f g)
st-roundtrip (λ⇒ {A})  = ⟺ (bridge-λ⇒-is-id A)
st-roundtrip (λ⇐ {A})  = ⟺ (bridge-λ⇐-is-id A)
st-roundtrip (ρ⇒ {A})  =
  ≡⇒≈Term (embF-coe (++-identityʳ (flatten A))) ○ ρ⇒-coherence A
st-roundtrip (ρ⇐ {A})  =
  ≡⇒≈Term (embF-coe (sym (++-identityʳ (flatten A)))) ○ ρ⇐-coherence A
st-roundtrip (α⇒ {A} {B} {C}) =
  ≡⇒≈Term (embF-coe (++-assoc (flatten A) (flatten B) (flatten C)))
  ○ ⟺ (Worker.work A B C)
st-roundtrip (α⇐ {A} {B} {C}) =
  ≡⇒≈Term (embF-coe (sym (++-assoc (flatten A) (flatten B) (flatten C))))
  ○ ⟺ (Worker.derive-⇐ A B C)
st-roundtrip (σ {A} {B} ⦃ v≤v ⦄) =
  ⟺ (center (⟺ σ∘[f⊗g]≈[g⊗f]∘σ)
     ○ (refl⟩∘⟨ cancelInner (⊗-cancel (_≅_.isoʳ (unflatten-flatten-≈ A))
                                      (_≅_.isoʳ (unflatten-flatten-≈ B)))))

bridge⁻¹
  : ∀ {A B}
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  → HomTerm A B
bridge⁻¹ {A} {B} h =
  _≅_.to (unflatten-flatten-≈ B) ∘ h ∘ _≅_.from (unflatten-flatten-≈ A)

bridge-cancel : ∀ {A B} (f : HomTerm A B) → bridge⁻¹ (bridge f) ≈Term f
bridge-cancel {A} {B} f =
  (refl⟩∘⟨ pullʳ (cancelʳ (_≅_.isoˡ (unflatten-flatten-≈ A))))
  ○ cancelˡ (_≅_.isoˡ (unflatten-flatten-≈ B))

private
  part-Iˢ  = PI.st-≈-decodePˢ
  part-IIˢ = PII.decodePˢ-resp-iso

st-resp-iso : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → st f ≈ˢ st g
st-resp-iso f g iso =
  ≈-trans (part-Iˢ f) (≈-trans (part-IIˢ f g iso) (≈-sym (part-Iˢ g)))

bridge-resp-iso
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → bridge f ≈Term bridge g
bridge-resp-iso f g iso = begin
  bridge f          ≈⟨ st-roundtrip f ⟨
  embF (st f)       ≈⟨ embF-resp-≈ˢ (st-resp-iso f g iso) ⟩
  embF (st g)       ≈⟨ st-roundtrip g ⟩
  bridge g          ∎

soundness-strict : ∀ {A B} {f g : HomTerm A B} → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
soundness-strict {f = f} {g = g} iso = begin
  f                       ≈⟨ bridge-cancel f ⟨
  bridge⁻¹ (bridge f)     ≈⟨ refl⟩∘⟨ (bridge-resp-iso f g iso ⟩∘⟨refl) ⟩
  bridge⁻¹ (bridge g)     ≈⟨ bridge-cancel g ⟩
  g ∎
