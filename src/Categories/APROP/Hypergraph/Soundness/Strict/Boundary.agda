{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The BOUNDARY of the strictified pipeline, FlatGen side:
--
--   * `st : HomTerm A B → HomS (flatten A) (flatten B)` — the
--     strictification functor (∘/⊗ are DEFINITIONAL; the structural atoms
--     α/ρ become `coe` casts, λ is invisible because `[] ++ xs` reduces);
--   * `embF = emb ∘ mapS` — the embedding back into the free SMC, with
--     `embF-resp-≈ˢ` from `Strict.Embed`;
--   * `st-roundtrip : embF (st f) ≈Term bridge f` — by induction on f,
--     with the atomic content supplied by the EXISTING bridge lemmas
--     (`bridge-*-is-id`, `ρ⇒/ρ⇐-coherence`, BAFC's α-form worker).
--
-- Together these give the final-assembly reflection: from `st f ≈ˢ st g`
-- conclude `bridge f ≈Term bridge g`, hence `f ≈Term g` by bridge-cancel.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Boundary
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flat; flat-rec; flatten)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using ( unflatten; unflatten-flatten-≈; _≅_; bridge
        ; subst-id-cod; cod-cancel; subst-cod-cons )
open import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence sig
  using ( bridge-∘; bridge-⊗; bridge-id-is-id; bridge-λ⇒-is-id; bridge-λ⇐-is-id
        ; ρ⇒-coherence; ρ⇐-coherence; α⇒-form-list )
import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeAlphaFormCompound
  sig as BAFC

open import Categories.FreeMonoidal using (v≤v)
open import Categories.FreeStrictSMC using (module Map)
open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Embed sig _≟X_ as E

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)

open import Categories.Category using (Category)
-- `elim²ᵀ`/`inv-uniqueᵀ` used to be hand-rolled here because these two opens
-- were missing: they ARE `cancelˡ` and `inv-resp` at the term-level category.
open import Categories.Morphism.Reasoning FreeMonoidal
  using (cancelˡ; center; cancelInner)
open import Categories.Morphism.Reasoning.Ext FreeMonoidal using (inv-resp)

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

  -- the α-form tower is the transported identity
  α-form-cast
    : ∀ xs ys zs
    → α⇒-form-list xs ys zs ≈Term subst-id-cod (++-assoc xs ys zs)
  α-form-cast []       ys zs = ≈-Term-refl
  α-form-cast (x ∷ xs) ys zs =
    ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (α-form-cast xs ys zs))
                 (subst-cod-cons (++-assoc xs ys zs))

  bridge-α⇒-cast
    : ∀ A B C
    → bridge (α⇒ {A} {B} {C})
      ≈Term subst-id-cod (++-assoc (flatten A) (flatten B) (flatten C))
  bridge-α⇒-cast A B C =
    ≈-Term-trans (BAFC.Worker.work A B C)
                 (α-form-cast (flatten A) (flatten B) (flatten C))

st-roundtrip : ∀ {A B} (f : HomTerm A B) → embF (st f) ≈Term bridge f
st-roundtrip (Agen g)  = ≈-Term-refl
st-roundtrip (id {A})  = ≈-Term-sym (bridge-id-is-id A)
st-roundtrip (g ∘ f)   =
  ≈-Term-trans (∘-resp-≈ (st-roundtrip g) (st-roundtrip f))
               (≈-Term-sym (bridge-∘ g f))
st-roundtrip (f ⊗₁ g)  =
  ≈-Term-trans
    (∘-resp-≈ ≈-Term-refl
      (∘-resp-≈ (⊗-resp-≈ (st-roundtrip f) (st-roundtrip g)) ≈-Term-refl))
    (≈-Term-sym (bridge-⊗ f g))
st-roundtrip (λ⇒ {A})  = ≈-Term-sym (bridge-λ⇒-is-id A)
st-roundtrip (λ⇐ {A})  = ≈-Term-sym (bridge-λ⇐-is-id A)
st-roundtrip (ρ⇒ {A})  =
  ≈-Term-trans (≡⇒≈Term (embF-coe (++-identityʳ (flatten A))))
               (ρ⇒-coherence A)
st-roundtrip (ρ⇐ {A})  =
  ≈-Term-trans (≡⇒≈Term (embF-coe (sym (++-identityʳ (flatten A)))))
               (ρ⇐-coherence A)
st-roundtrip (α⇒ {A} {B} {C}) =
  ≈-Term-trans
    (≡⇒≈Term (embF-coe (++-assoc (flatten A) (flatten B) (flatten C))))
    (≈-Term-sym (bridge-α⇒-cast A B C))
st-roundtrip (α⇐ {A} {B} {C}) =
  ≈-Term-trans
    (≡⇒≈Term (embF-coe (sym P)))
    (≈-Term-sym
      (inv-resp
        -- bridge α⇐ ∘ bridge α⇒ ≈ id
        (≈-Term-trans (≈-Term-sym (bridge-∘ (α⇐ {A} {B} {C}) α⇒))
          (≈-Term-trans
            (∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl))
            (bridge-id-is-id _)))
        -- bridge α⇒ ∘ subst-id-cod (sym P) ≈ id
        (≈-Term-trans (∘-resp-≈ (bridge-α⇒-cast A B C) ≈-Term-refl)
          (cod-cancel P))
        ≈-Term-refl))
  where P = ++-assoc (flatten A) (flatten B) (flatten C)
st-roundtrip (σ {A} {B} ⦃ v≤v ⦄) =
  ≈-Term-sym (center (≈-Term-sym σ∘[f⊗g]≈[g⊗f]∘σ)
              ○ (refl⟩∘⟨ cancelInner ⊗-iso-cancel))
  where
    ⊗-iso-cancel = ⊗-cancel (_≅_.isoʳ (unflatten-flatten-≈ A))
                            (_≅_.isoʳ (unflatten-flatten-≈ B))
