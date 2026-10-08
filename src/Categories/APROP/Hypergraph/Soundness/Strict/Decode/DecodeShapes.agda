{-# OPTIONS --safe --without-K #-}

-- Structural atoms translate to literal `hId` graphs, so their runs and
-- final permutations reduce to identity.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes
  (sig : APROPSignature)
  where

open APROP sig

open FreeMonoidalHelper Symm X using (flatten)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪⟫-domL; ⟪⟫-codL)
import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig as DA

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig as PK

open import Data.List.Properties

module Scr (V : Set) (vlab : V → X) where
  open PK.Support V vlab public
  open Restrict V vlab

  open DA using (bswap) public

  refl-trivial
    : ∀ {xs ys : List V} (e : xs ≡ ys)
    → permuteˢ (Perm.↭-reflexive e)
      ≈ˢ castˢ refl (cong (map vlab) e) (idˢ {map vlab xs})
  refl-trivial refl = ≈-refl

  -- The inductive step is `Interchange.BlockSwapComm.shift-symᵛ`.
  permuteˢ-shift-sym-base
    : (v : V) (L : List V)
    → permuteᵛ (Perm.↭-sym (PermProp.shift v [] L))
      ≈ᵛ σᵛ (v ∷ []) [] ⊗ᵛ idᵛ {L}
  permuteˢ-shift-sym-base v L =
    ≈-sym (≈-trans (⊗-resp (σ-unitʳˢ (vlab v ∷ [])) ≈-refl) ⊗-id)

  bswap-σ-base : (R : List V) → permuteᵛ (bswap [] R) ≈ᵛ σᵛ [] R
  bswap-σ-base R =
    ≈-trans (refl-trivial (sym (++-identityʳ R)))
      (≈-sym (≈-trans (σ-unitᵛ R)
                      (≡⇒≈ˢ (castᵛ-cast refl (sym (++-identityʳ R)) idᵛ))))

  BswapSig : Set
  BswapSig = ∀ (L R : List V) → permuteᵛ (bswap L R) ≈ᵛ σᵛ L R

atom-coe
  : ∀ {xs as bs} (p : xs ≡ as) (q : xs ≡ bs) (e : as ≡ bs)
  → castˢ p q (idˢ {xs} ∘ˢ idˢ) ≈ˢ coe e
atom-coe refl q e = ≈-trans (cast-resp refl q idʳ) (coe-uip q e)

module _ {A : ObjTerm} where
  decodePˢ-id : decodePˢ (id {A}) ≈ˢ st (id {A})
  decodePˢ-id = atom-coe (⟪⟫-domL (id {A})) (⟪⟫-codL (id {A})) refl

  decodePˢ-λ⇒ : decodePˢ (λ⇒ {A}) ≈ˢ st (λ⇒ {A})
  decodePˢ-λ⇒ = atom-coe (⟪⟫-domL (λ⇒ {A})) (⟪⟫-codL (λ⇒ {A})) refl

  decodePˢ-λ⇐ : decodePˢ (λ⇐ {A}) ≈ˢ st (λ⇐ {A})
  decodePˢ-λ⇐ = atom-coe (⟪⟫-domL (λ⇐ {A})) (⟪⟫-codL (λ⇐ {A})) refl

  decodePˢ-ρ⇒ : decodePˢ (ρ⇒ {A}) ≈ˢ st (ρ⇒ {A})
  decodePˢ-ρ⇒ =
    atom-coe (⟪⟫-domL (ρ⇒ {A})) (⟪⟫-codL (ρ⇒ {A})) (++-identityʳ (flatten A))

  decodePˢ-ρ⇐ : decodePˢ (ρ⇐ {A}) ≈ˢ st (ρ⇐ {A})
  decodePˢ-ρ⇐ =
    atom-coe (⟪⟫-domL (ρ⇐ {A})) (⟪⟫-codL (ρ⇐ {A}))
             (sym (++-identityʳ (flatten A)))

module _ {A B C : ObjTerm} where
  decodePˢ-α⇒ : decodePˢ (α⇒ {A} {B} {C}) ≈ˢ st (α⇒ {A} {B} {C})
  decodePˢ-α⇒ =
    atom-coe (⟪⟫-domL (α⇒ {A} {B} {C})) (⟪⟫-codL (α⇒ {A} {B} {C}))
             (++-assoc (flatten A) (flatten B) (flatten C))

  decodePˢ-α⇐ : decodePˢ (α⇐ {A} {B} {C}) ≈ˢ st (α⇐ {A} {B} {C})
  decodePˢ-α⇐ =
    atom-coe (⟪⟫-domL (α⇐ {A} {B} {C})) (⟪⟫-codL (α⇐ {A} {B} {C}))
             (sym (++-assoc (flatten A) (flatten B) (flatten C)))

