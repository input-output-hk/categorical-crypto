{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The standalone, module-level strict cross-vertex-type relabel `pvv-relabelˢ`:
--
--   castˢ P Q (permuteˢ {Fin nJ} vJ (map⁺ φ p)) ≈ˢ permuteˢ {Fin nH} vH p
--
-- Consumed by BOTH the `∘`-shape (`DecodeComposeAssembly`) and the ⊗-shape
-- (`TensorBraid`/`TensorKBlockFinal`) for the G-/K-block final permutes
-- (`φ = injL / injR / remapP`).
--
-- This is FUNCTORIALITY, not rigidity: stdlib's `map⁺ φ` is structural, so
-- `permuteˢ vJ (map⁺ φ p)` and `permuteˢ vH p` are the SAME wiring term up to
-- the vertex relabelling of their atoms, and the coincidence follows by a
-- four-case induction over `p` in `_≈̂_` (the endpoint bookkeeping is exactly
-- `vmap = map-∘ ⨾ map-cong veq`).  No `permˢ-K`/`eval-↭`/`FinBij` machinery is
-- involved — contrast `IsoTransport.permute-relabel-freeˢ`, where the two
-- derivations are genuinely UNRELATED and rigidity IS the content.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorPVVRelabel
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (map-∘; map-cong)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------

module _ {nH nJ : ℕ} (φ : Fin nH → Fin nJ)
         (vJ : Fin nJ → X) (vH : Fin nH → X) (veq : ∀ i → vJ (φ i) ≡ vH i)
         where
  private
    vmap : (as : List (Fin nH)) → map vJ (map φ as) ≡ map vH as
    vmap as = trans (sym (map-∘ as)) (map-cong veq as)

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

pvv-relabelˢ
  : ∀ {nH nJ : ℕ} (φ : Fin nH → Fin nJ)
      (vJ : Fin nJ → X) (vH : Fin nH → X) (veq : ∀ i → vJ (φ i) ≡ vH i)
      {xs ys : List (Fin nH)} (p : xs Perm.↭ ys)
      (P : map vJ (map φ xs) ≡ map vH xs)
      (Q : map vJ (map φ ys) ≡ map vH ys)
  → castˢ P Q
      (Perm′.permuteˢ (Fin nJ) vJ (PermProp.map⁺ φ p))
    ≈ˢ Perm′.permuteˢ (Fin nH) vH p
pvv-relabelˢ φ vJ vH veq p P Q = ≈̂⇒castˢ (pvv-≈̂ φ vJ vH veq p) P Q
