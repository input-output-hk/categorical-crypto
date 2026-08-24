{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict SMC instance the strictified soundness pipeline works in:
-- `FreeStrictSMC.Build` over the flat graph generators `FlatGen`, plus the two
-- pieces of the strictification that mention nothing outside it: the object
-- coercions `coe` and the strictification functor `st`.  Kept light (no
-- boundary imports) so the DECODER side depends on it alone; the embedding
-- back into the free SMC (`embF`, `st-roundtrip`) needs `Embed`/`Bridge/*`
-- and lives in `Strict.Soundness`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Core
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; flat; flatten)
open import Categories.FreeStrictSMC using (module Build)
open import Data.List using (List)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open Build X _≟X_ FlatGen public

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
