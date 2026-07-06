{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The standalone, module-level strict cross-vertex-type relabel `pvv-relabelˢ`
-- (a verbatim factor-out of the copy inside `DecodeComposeAssembly.ComposeShape`).
--
--   castˢ P Q (permuteˢ {Fin nJ} vJ (map⁺ φ p)) ≈ˢ permuteˢ {Fin nH} vH p
--
-- It routes a `Fin nJ`-level permute of `map⁺ φ p` onto the `Fin nH`-level
-- permute of `p` via §0 `permuteˢ-X` (both sides) + `permˢ-K-X`, whose
-- evaluated-bijection premise is the `eval-map⁺`/`subst₂-FinBij-∘` chain.
--
-- Pulled out so BOTH the `∘`-shape (`DecodeComposeAssembly`) and the ⊗-shape
-- (`TensorBraid`/`TensorKBlockFinal`) can consume the SAME relabel for the
-- G-/K-block final permutes (`φ = injL / injR`).  ZERO postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorPVVRelabel
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
  using (module Support)
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose sig _≟X_ as DC

open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Properties using (length-map; map-∘; map-cong)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.FinBijSubst using (eval-map⁺)
open import Categories.Hypergraph.ExtractPrefixEvalPhi
  using (≈-fb-of-≡; subst₂-FinBij-∘)
  renaming (cast-irrel to cast-irrel-fb)

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------

open DC using (permuteˢ-X; module XPerm)
open XPerm using (permuteˣ)

private
  permˢ-K-X : Support.PermK X (λ x → x)
  permˢ-K-X = PK.permˢ-K X _≟X_ (λ x → x)

  -- eval-↭ of a two-sided subst₂ derivation is a subst₂ FinBij.
  eval-subst₂-↭
    : ∀ {a} {A : Set a} {xs xs' ys ys' : List A}
        (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
    → eval-↭ (subst₂ Perm._↭_ p q r)
      ≡ subst₂ FinBij (cong length p) (cong length q) (eval-↭ r)
  eval-subst₂-↭ refl refl r = refl

  -- permuteˣ of a two-sided subst₂ derivation = a castˢ of permuteˣ.
  permuteˣ-subst₂
    : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
        (r : xs Perm.↭ ys)
    → permuteˣ (subst₂ Perm._↭_ p q r)
      ≡ castˢ (cong (map (λ x → x)) p) (cong (map (λ x → x)) q) (permuteˣ r)
  permuteˣ-subst₂ refl refl r = refl

pvv-relabelˢ
  : ∀ {nH nJ : ℕ} (φ : Fin nH → Fin nJ)
      (vJ : Fin nJ → X) (vH : Fin nH → X) (veq : ∀ i → vJ (φ i) ≡ vH i)
      {xs ys : List (Fin nH)} (p : xs Perm.↭ ys)
      (P : map vJ (map φ xs) ≡ map vH xs)
      (Q : map vJ (map φ ys) ≡ map vH ys)
  → castˢ P Q
      (Perm′.permuteˢ (Fin nJ) vJ (PermProp.map⁺ φ p))
    ≈ˢ Perm′.permuteˢ (Fin nH) vH p
pvv-relabelˢ {nH} {nJ} φ vJ vH veq {xs} {ys} p P Q =
  ≈-trans
    (cast-resp P Q (≈-sym (permuteˢ-X (Fin nJ) vJ (PermProp.map⁺ φ p))))
    (≈-trans middle (permuteˢ-X (Fin nH) vH p))
  where
    mpJd = DC.mp (Fin nJ) vJ (map φ xs)
    mpJc = DC.mp (Fin nJ) vJ (map φ ys)
    mpHd = DC.mp (Fin nH) vH xs
    mpHc = DC.mp (Fin nH) vH ys
    Xj = permuteˣ (PermProp.map⁺ vJ (PermProp.map⁺ φ p))
    Xh = permuteˣ (PermProp.map⁺ vH p)

    -- evaluated-bijection coincidence (the `pvv-relabel` chain).
    coincide
      : eval-↭ (subst₂ Perm._↭_ P Q (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
        ≈-fb eval-↭ (PermProp.map⁺ vH p)
    coincide =
      ≈-fb-of-≡
        (trans (eval-subst₂-↭ P Q (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
        (trans (cong (subst₂ FinBij (cong length P) (cong length Q))
                     (trans (eval-map⁺ vJ (PermProp.map⁺ φ p))
                            (cong (subst₂ FinBij
                                     (sym (length-map vJ (map φ xs)))
                                     (sym (length-map vJ (map φ ys))))
                                  (eval-map⁺ φ p))))
        (trans (cong (subst₂ FinBij (cong length P) (cong length Q))
                     (subst₂-FinBij-∘
                        (sym (length-map φ xs)) (sym (length-map vJ (map φ xs)))
                        (sym (length-map φ ys)) (sym (length-map vJ (map φ ys)))
                        (eval-↭ p)))
        (trans (subst₂-FinBij-∘
                  (trans (sym (length-map φ xs)) (sym (length-map vJ (map φ xs))))
                  (cong length P)
                  (trans (sym (length-map φ ys)) (sym (length-map vJ (map φ ys))))
                  (cong length Q)
                  (eval-↭ p))
        (trans (cast-irrel-fb
                  (trans (trans (sym (length-map φ xs)) (sym (length-map vJ (map φ xs))))
                         (cong length P))
                  (sym (length-map vH xs))
                  (trans (trans (sym (length-map φ ys)) (sym (length-map vJ (map φ ys))))
                         (cong length Q))
                  (sym (length-map vH ys))
                  (eval-↭ p))
               (sym (eval-map⁺ vH p)))))))

    -- the X-level identification: Xh ≈ castˢ (cong(map id)P)(cong(map id)Q) Xj.
    K-step : Xh ≈ˢ castˢ (cong (map (λ x → x)) P) (cong (map (λ x → x)) Q) Xj
    K-step =
      ≈-trans
        (≈-sym (permˢ-K-X (subst₂ Perm._↭_ P Q (PermProp.map⁺ vJ (PermProp.map⁺ φ p)))
                          (PermProp.map⁺ vH p) coincide))
        (≡⇒≈ˢ (permuteˣ-subst₂ P Q (PermProp.map⁺ vJ (PermProp.map⁺ φ p))))

    middle : castˢ P Q (castˢ mpJd mpJc Xj) ≈ˢ castˢ mpHd mpHc Xh
    middle =
      ≈-trans (≡⇒≈ˢ (cast-fuse mpJd P mpJc Q Xj))
      (≈-trans (≡⇒≈ˢ (cast-irrel (trans mpJd P)
                        (trans (cong (map (λ x → x)) P) mpHd)
                        (trans mpJc Q)
                        (trans (cong (map (λ x → x)) Q) mpHc) Xj))
      (≈-trans (≡⇒≈ˢ (sym (cast-fuse (cong (map (λ x → x)) P) mpHd
                                     (cong (map (λ x → x)) Q) mpHc Xj)))
        (≈-sym (cast-resp mpHd mpHc K-step))))
