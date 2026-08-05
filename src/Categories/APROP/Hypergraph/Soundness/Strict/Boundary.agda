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
  using (unflatten; unflatten-++-≅; unflatten-flatten-≈; _≅_; bridge)
open import Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal sig
  using ( subst-id-cod; cod-as-subst₂; dom-as-subst₂; cod-cancel
        ; subst-cod-cons )
open import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeOps sig
  using (bridge-∘; bridge-⊗)
open import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence sig
  using ( bridge-id-is-id; bridge-λ⇒-is-id; bridge-λ⇐-is-id
        ; ρ⇒-coherence; ρ⇐-coherence; α⇒-form-list )
import Categories.APROP.Hypergraph.Soundness.Discharge.BridgeAlphaFormCompound
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
open import Categories.Morphism.Reasoning SCat using (cancelˡ; elimʳ)

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
-- `coe`: the object-equality coercions the structural atoms become.

coe : ∀ {xs ys : List X} → xs ≡ ys → HomS xs ys
coe p = castˢ refl p idˢ

coe-id≈ : ∀ {xs} (p : xs ≡ xs) → coe p ≈ˢ idˢ
coe-id≈ p = cast-id refl p

coe-uip : ∀ {xs ys} (p q : xs ≡ ys) → coe p ≈ˢ coe q
coe-uip p q = ≡⇒≈ˢ (cast-irrel refl refl p q idˢ)

coe-trans : ∀ {xs ys zs} (p : xs ≡ ys) (q : ys ≡ zs)
          → coe q ∘ˢ coe p ≈ˢ coe (trans p q)
coe-trans refl q = idʳ

coe-cancel : ∀ {xs ys} (p : xs ≡ ys) → coe (sym p) ∘ˢ coe p ≈ˢ idˢ
coe-cancel refl = idˡ

coe-cancelʳ : ∀ {xs ys} (p : xs ≡ ys) → coe p ∘ˢ coe (sym p) ≈ˢ idˢ
coe-cancelʳ refl = idˡ

-- a cast as conjugation by `coe`s
coe-conj
  : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys') (t : HomS xs ys)
  → castˢ p q t ≈ˢ coe q ∘ˢ t ∘ˢ coe (sym p)
coe-conj refl refl t = ≈-sym (≈-trans idˡ idʳ)

-- `(HomS , _≈ˢ_)`'s `Morphism.Reasoning` combinators.  `elim²` IS `cancelˡ`
-- and inverse-uniqueness is `elimʳ` + `cancelˡ`; both stay named here (and
-- `public`) because `DecodeSigma` consumes them under these names.
elim²
  : ∀ {as bs cs} {f : HomS as bs} {f' : HomS bs as} {h : HomS cs as}
  → f' ∘ˢ f ≈ˢ idˢ → f' ∘ˢ (f ∘ˢ h) ≈ˢ h
elim² e = cancelˡ e

inv-uniqueˢ
  : ∀ {as bs} {u : HomS as bs} {v w : HomS bs as}
  → v ∘ˢ u ≈ˢ idˢ → u ∘ˢ w ≈ˢ idˢ → v ≈ˢ w
inv-uniqueˢ e₁ e₂ = ≈-trans (≈-sym (elimʳ e₂)) (cancelˡ e₁)

--------------------------------------------------------------------------------
-- The strictification functor.

st : ∀ {A B} → HomTerm A B → HomS (flatten A) (flatten B)
st (Agen g)         = genˢ (flat g)
st id               = idˢ
st (g ∘ f)          = st g ∘ˢ st f
st (f ⊗₁ g)         = st f ⊗ˢ st g
st λ⇒               = idˢ
st λ⇐               = idˢ
st (ρ⇒ {A})         = coe (++-identityʳ (flatten A))
st (ρ⇐ {A})         = coe (sym (++-identityʳ (flatten A)))
st (α⇒ {A} {B} {C}) = coe (++-assoc (flatten A) (flatten B) (flatten C))
st (α⇐ {A} {B} {C}) = coe (sym (++-assoc (flatten A) (flatten B) (flatten C)))
st (σ {A} {B})      = σˢ (flatten A) (flatten B)

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

  elim²ᵀ
    : ∀ {A B C} {f : HomTerm A B} {f' : HomTerm B A} {h : HomTerm C A}
    → f' ∘ f ≈Term id → f' ∘ (f ∘ h) ≈Term h
  elim²ᵀ e = ≈-Term-trans (≈-Term-sym FM.assoc)
               (≈-Term-trans (∘-resp-≈ e ≈-Term-refl) idˡ)

  inv-uniqueᵀ
    : ∀ {A B} {u : HomTerm A B} {v w : HomTerm B A}
    → v ∘ u ≈Term id → u ∘ w ≈Term id → v ≈Term w
  inv-uniqueᵀ e₁ e₂ =
    ≈-Term-trans (≈-Term-sym idʳ)
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym e₂))
    (≈-Term-trans (≈-Term-sym FM.assoc)
    (≈-Term-trans (∘-resp-≈ e₁ ≈-Term-refl) idˡ)))

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
  (≈-Term-trans (≡⇒≈Term (cod-as-subst₂ (++-identityʳ (flatten A))))
    (ρ⇒-coherence A))
st-roundtrip (ρ⇐ {A})  =
  ≈-Term-trans (≡⇒≈Term (embF-coe (sym (++-identityʳ (flatten A)))))
  (≈-Term-trans (≡⇒≈Term (dom-as-subst₂ (++-identityʳ (flatten A))))
    (ρ⇐-coherence A))
st-roundtrip (α⇒ {A} {B} {C}) =
  ≈-Term-trans
    (≡⇒≈Term (embF-coe (++-assoc (flatten A) (flatten B) (flatten C))))
    (≈-Term-sym (bridge-α⇒-cast A B C))
st-roundtrip (α⇐ {A} {B} {C}) =
  ≈-Term-trans
    (≡⇒≈Term (embF-coe (sym P)))
    (≈-Term-sym
      (inv-uniqueᵀ
        -- bridge α⇐ ∘ bridge α⇒ ≈ id
        (≈-Term-trans (≈-Term-sym (bridge-∘ (α⇐ {A} {B} {C}) α⇒))
          (≈-Term-trans
            (∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl))
            (bridge-id-is-id _)))
        -- bridge α⇒ ∘ subst-id-cod (sym P) ≈ id
        (≈-Term-trans (∘-resp-≈ (bridge-α⇒-cast A B C) ≈-Term-refl)
          (cod-cancel P))))
  where P = ++-assoc (flatten A) (flatten B) (flatten C)
st-roundtrip (σ {A} {B} ⦃ v≤v ⦄) = ≈-Term-sym (begin
  (T ∘ (from-B ⊗₁ from-A)) ∘ (σ ∘ ((to-A ⊗₁ to-B) ∘ F))
    ≈⟨ FM.assoc ⟩
  T ∘ ((from-B ⊗₁ from-A) ∘ (σ ∘ ((to-A ⊗₁ to-B) ∘ F)))
    ≈⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc ⟩
  T ∘ (((from-B ⊗₁ from-A) ∘ σ) ∘ ((to-A ⊗₁ to-B) ∘ F))
    ≈⟨ refl⟩∘⟨ (≈-Term-sym σ∘[f⊗g]≈[g⊗f]∘σ ⟩∘⟨refl) ⟩
  T ∘ ((σ ∘ (from-A ⊗₁ from-B)) ∘ ((to-A ⊗₁ to-B) ∘ F))
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  T ∘ (σ ∘ ((from-A ⊗₁ from-B) ∘ ((to-A ⊗₁ to-B) ∘ F)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elim²ᵀ ⊗-iso-cancel ⟩
  T ∘ (σ ∘ F) ∎)
  where
    a = flatten A ; b = flatten B
    T      = _≅_.to (unflatten-++-≅ b a)
    F      = _≅_.from (unflatten-++-≅ a b)
    from-A = _≅_.from (unflatten-flatten-≈ A)
    from-B = _≅_.from (unflatten-flatten-≈ B)
    to-A   = _≅_.to (unflatten-flatten-≈ A)
    to-B   = _≅_.to (unflatten-flatten-≈ B)

    ⊗-iso-cancel : (from-A ⊗₁ from-B) ∘ (to-A ⊗₁ to-B) ≈Term id
    ⊗-iso-cancel =
      ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
      (≈-Term-trans
        (⊗-resp-≈ (_≅_.isoʳ (unflatten-flatten-≈ A))
                  (_≅_.isoʳ (unflatten-flatten-≈ B)))
        id⊗id≈id)
