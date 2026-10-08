{-# OPTIONS --safe --without-K #-}

-- Relabelling wiring derivations into strict permutation morphisms.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermRelabel
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig

open import Data.Fin using (Fin)
open import Data.List.Properties.Ext
open import Data.Nat using (ℕ)

module _ {nH nJ : ℕ} (φ : Fin nH → Fin nJ)
         (vJ : Fin nJ → X) (vH : Fin nH → X) (veq : ∀ i → vJ (φ i) ≡ vH i)
         where
  private
    vmap : (as : List (Fin nH)) → map vJ (map φ as) ≡ map vH as
    vmap as = map-∘-cong veq as

  pvv-≈̂
    : ∀ {xs ys : List (Fin nH)} (p : xs Perm.↭ ys)
    → Perm′.permuteˢ (Fin nJ) vJ (PermProp.map⁺ φ p)
      ≈̂ Perm′.permuteˢ (Fin nH) vH p
  pvv-≈̂ {xs} Perm.refl      = idˢ-≈̂ (vmap xs)
  pvv-≈̂ (Perm.prep x p)     =
    ⊗-resp-≈̂ (idˢ-≈̂ (cong (_∷ []) (veq x))) (pvv-≈̂ p)
  pvv-≈̂ (Perm.swap x y p)   =
    ⊗-resp-≈̂ (σ-≈̂ (cong (_∷ []) (veq x)) (cong (_∷ []) (veq y))) (pvv-≈̂ p)
  pvv-≈̂ (Perm.trans p q)    = ∘-resp-≈̂ (pvv-≈̂ q) (pvv-≈̂ p)
