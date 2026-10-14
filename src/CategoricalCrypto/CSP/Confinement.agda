{-# OPTIONS --safe --without-K --guardedness #-}

-- Constructive slice of DRCongruenceRep.OffersOnly and DRCongruence.Sep
-- at agda-cardano-common 9a40d1de330f376c3a102e7c9f1282f4fa830a7e.
-- Their source modules import classical laws; this slice does not.
module CategoricalCrypto.CSP.Confinement (E B R : Set) where

open import Data.Bool.Base
open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Process E B R

Alpha : Set₁
Alpha = E → Set

Disjoint : Alpha → Alpha → Set
Disjoint α β = ∀ e → α e → β e → ⊥

record OffersOnly (α : Alpha) (p : Tree) : Set where
  coinductive
  field
    now : ∀ {e q} → p ─[ visible (event e) ]→ q → α e
    after : ∀ {l q} → p ─[ l ]→ q → OffersOnly α q

Sep : (E → Bool) → Tree → Tree → Set
Sep sync p q = ∀ {e p′ q′} → sync e ≡ false
             → p ─[ visible (event e) ]→ p′ → q ─[ visible (event e) ]→ q′ → ⊥

sep-from-OffersOnly : ∀ {α β p q sync} → OffersOnly α p → OffersOnly β q
  → (∀ e → sync e ≡ false → α e → β e → ⊥) → Sep sync p q
sep-from-OffersOnly cp cq disjoint {e} outside left right = disjoint e outside
  (OffersOnly.now cp left) (OffersOnly.now cq right)

disjoint-interleaving-separation : ∀ {α β p q} → OffersOnly α p → OffersOnly β q
                                → Disjoint α β → Sep (λ _ → false) p q
disjoint-interleaving-separation cp cq disjoint = sep-from-OffersOnly cp cq (λ e _ → disjoint e)

confined-stop : ∀ α → OffersOnly α stop
OffersOnly.now (confined-stop α) step = ⊥-elim (stop-no-step step)
OffersOnly.after (confined-stop α) step = ⊥-elim (stop-no-step step)

confined-div : ∀ α → OffersOnly α div
OffersOnly.now (confined-div α) (sVis () _)
OffersOnly.after (confined-div α) (sRet ())
OffersOnly.after (confined-div α) (sVis () _)
OffersOnly.after (confined-div α) (sTau () _)
OffersOnly.after (confined-div α) (sSil refl) = confined-div α
