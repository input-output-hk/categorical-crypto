{-# OPTIONS --safe --without-K #-}

-- Strictification into `FreeStrictSMC.Build` at `FlatGen`.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Core
  (sig : APROPSignature)
  where

open APROP sig

open FreeMonoidalHelper Symm X using (flatten)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; flat)
open import Categories.FreeStrictSMC
open import Data.List.Properties

open Build X _≟X_ FlatGen public

private
  variable
    xs xs' ys ys' : List X

gen-cast
  : ∀ {as as' bs bs'} (p : as ≡ as') (q : bs ≡ bs') (x : FlatGen as bs)
  → castˢ p q (genˢ x) ≡ genˢ (subst₂ FlatGen p q x)
gen-cast refl refl x = refl

coe : xs ≡ ys → HomS xs ys
coe p = castˢ refl p idˢ

coe-id≈ : (p : xs ≡ xs) → coe p ≈ˢ idˢ
coe-id≈ p = cast-id refl p

coe-uip : (p q : xs ≡ ys) → coe p ≈ˢ coe q
coe-uip p q = ≡⇒≈ˢ (cast-irrel refl refl p q idˢ)

coe-cancel : (p : xs ≡ ys) → coe (sym p) ∘ˢ coe p ≈ˢ idˢ
coe-cancel refl = idˡ

coe-cancelʳ : (p : xs ≡ ys) → coe p ∘ˢ coe (sym p) ≈ˢ idˢ
coe-cancelʳ refl = idˡ

coe-conj : (p : xs ≡ xs') (q : ys ≡ ys') (t : HomS xs ys)
         → castˢ p q t ≈ˢ coe q ∘ˢ t ∘ˢ coe (sym p)
coe-conj refl refl t = ≈-sym (≈-trans idˡ idʳ)

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
