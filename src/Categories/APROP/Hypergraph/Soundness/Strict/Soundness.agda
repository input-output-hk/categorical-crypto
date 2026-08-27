{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The BOUNDARY of the strictified pipeline (FlatGen side) and the soundness
-- theorem it assembles:
--
--     soundness-strict : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
--
-- §1 THE BOUNDARY.  `st : HomTerm A B → HomS (flatten A) (flatten B)` is the
-- strictification functor of `Strict.Core` (∘/⊗ are DEFINITIONAL; the
-- structural atoms α/ρ become `coe` casts, λ is invisible because `[] ++ xs`
-- reduces).  Here it is met by
--   * `embF = emb ∘ mapS` — the embedding back into the free SMC, with
--     `embF-resp-≈ˢ` from `Strict.Embed`;
--   * `st-roundtrip : embF (st f) ≈Term bridge f` — by induction on f, with the
--     atomic content supplied by the EXISTING bridge lemmas
--     (`bridge-*-is-id`, `ρ⇒/ρ⇐-coherence`, the α cast worker).
--
-- §2 THE ASSEMBLY.  From
--   * part (I)ˢ   `st-≈-decodePˢ : st h ≈ˢ decodePˢ h`        (Strict.PartI)
--     at the unconditional ⊗-shape `TensorBraid.decodePˢ-⊗-concrete`
--     (its K-block box-braid `KBlockσ` discharged there, ZERO postulates);
--   * part (II)ˢ  `decodePˢ-resp-iso : ⟪f⟫≅ᴴ⟪g⟫ → decodePˢ f ≈ˢ decodePˢ g`
--     (Strict.PartII, unconditional);
--   * §1's `embF-resp-≈ˢ` + `st-roundtrip`, and `bridge-cancel` (the
--     `unflatten-flatten-≈` iso cancellation, whose only home this is),
-- conclude `bridge f ≈Term bridge g`, hence `f ≈Term g`.
--
-- Everything here is concrete; the root `Soundness.agda` only re-exports
-- `soundness-strict` under its final name.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Soundness
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flat-rec; flatten)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; _≅_; bridge; subst-id-cod)
open import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence sig
  using ( bridge-∘; bridge-⊗; bridge-id-is-id; bridge-λ⇒-is-id; bridge-λ⇐-is-id
        ; ρ⇒-coherence; ρ⇐-coherence; derive-⇐; module Worker )

open import Categories.FreeMonoidal using (v≤v)
open import Categories.FreeStrictSMC using (module Map)
open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Embed sig _≟X_ as E
import Categories.APROP.Hypergraph.Soundness.Strict.PartI  sig _≟X_ as PI
import Categories.APROP.Hypergraph.Soundness.Strict.PartII sig _≟X_ as PII
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorBraid sig _≟X_
  as TB

open import Data.List using (List)
open import Data.List.Properties using (++-assoc; ++-identityʳ)

open import Categories.Category using (Category)
-- `inv-uniqueᵀ` used to be hand-rolled here because these opens were missing:
-- the σ chase and the bridge cancellation ARE `center`/`cancelInner`/`pullʳ`
-- at the term-level category.
open import Categories.Morphism.Reasoning FreeMonoidal
  using (center; cancelInner; pullʳ; cancelʳ; cancelˡ)

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

--------------------------------------------------------------------------------
-- The boundary instantiation: FlatGen generators are interpreted by
-- `bridge` of the underlying `Agen`, and the `Map` homomorphism carries
-- the FlatGen-generated strict category into the HomTerm-generated one
-- that `Strict.Embed` embeds.

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


--------------------------------------------------------------------------------
-- The roundtrip: `embF (st f) ≈Term bridge f`.

private
  -- embF of a `coe` is the cod-side transport of `id`
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
-- the α⇐ cast is the α⇒ one transposed — the bridge layer's `derive-⇐`, which is that
-- transposition at an arbitrary object.
st-roundtrip (α⇐ {A} {B} {C}) =
  ≡⇒≈Term (embF-coe (sym (++-assoc (flatten A) (flatten B) (flatten C))))
  ○ ⟺ (derive-⇐ A B C (Worker.work A B C))
st-roundtrip (σ {A} {B} ⦃ v≤v ⦄) =
  ⟺ (center (⟺ σ∘[f⊗g]≈[g⊗f]∘σ)
     ○ (refl⟩∘⟨ cancelInner ⊗-iso-cancel))
  where
    ⊗-iso-cancel = ⊗-cancel (_≅_.isoʳ (unflatten-flatten-≈ A))
                            (_≅_.isoʳ (unflatten-flatten-≈ B))
--------------------------------------------------------------------------------
-- Inverse bridge + cancellation.  This is their only home.

bridge⁻¹
  : ∀ {A B}
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
  → HomTerm A B
bridge⁻¹ {A} {B} h =
  _≅_.to (unflatten-flatten-≈ B) ∘ h ∘ _≅_.from (unflatten-flatten-≈ A)

-- the A-side pair cancels under `to-B ∘ (from-B ∘ _)`, which then cancels too.
bridge-cancel : ∀ {A B} (f : HomTerm A B) → bridge⁻¹ (bridge f) ≈Term f
bridge-cancel {A} {B} f =
  (refl⟩∘⟨ pullʳ (cancelʳ (_≅_.isoˡ (unflatten-flatten-≈ A))))
  ○ cancelˡ (_≅_.isoˡ (unflatten-flatten-≈ B))

--------------------------------------------------------------------------------
-- The strict soundness theorem, from its two halves.

private
  part-Iˢ  = PI.st-≈-decodePˢ TB.decodePˢ-⊗-concrete
  part-IIˢ = PII.decodePˢ-resp-iso

-- the strict core: `st f ≈ˢ st g` from the hypergraph iso
st-resp-iso : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → st f ≈ˢ st g
st-resp-iso f g iso =
  ≈-trans (part-Iˢ f) (≈-trans (part-IIˢ f g iso) (≈-sym (part-Iˢ g)))

-- transported to the free SMC: `bridge f ≈Term bridge g`
bridge-resp-iso
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → bridge f ≈Term bridge g
bridge-resp-iso f g iso = begin
  bridge f          ≈⟨ st-roundtrip f ⟨
  embF (st f)       ≈⟨ embF-resp-≈ˢ (st-resp-iso f g iso) ⟩
  embF (st g)       ≈⟨ st-roundtrip g ⟩
  bridge g          ∎

-- the headline theorem
soundness-strict : ∀ {A B} {f g : HomTerm A B} → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
soundness-strict {f = f} {g = g} iso = begin
  f                       ≈⟨ bridge-cancel f ⟨
  bridge⁻¹ (bridge f)     ≈⟨ refl⟩∘⟨ (bridge-resp-iso f g iso ⟩∘⟨refl) ⟩
  bridge⁻¹ (bridge g)     ≈⟨ bridge-cancel g ⟩
  g ∎
