{-# OPTIONS --safe --without-K #-}

-- Strict decoding and right-frame separability share generic extraction proofs.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder
  (sig : APROPSignature)
  where

open APROP sig

open import Axiom.UniquenessOfIdentityProofs using (UIP; module Decidable⇒UIP)
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (edge-step; process-edges; process-edges-++)
open import Categories.Combinatorics.ExtractPrefix
open import Categories.Combinatorics.ExtractPrefix.Properties
  using (prefix-++ˡ-perm; extract-prefix-++ˡ; extract-prefix-++ˡ-nothing)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig public
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig as PK

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Properties
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)

module StrictDecoder (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open Perm′ (Fin H.nV) H.vlab public

  vl : Fin H.nV → X
  vl = H.vlab

  uipV : UIP (List (Fin H.nV))
  uipV = Decidable⇒UIP.≡-irrelevant (≡-dec _≟F_)

  rigidˢ : ∀ {xs ys : List (Fin H.nV)} → Unique ys
         → (p q : xs Perm.↭ ys) → permuteˢ p ≈ˢ permuteˢ q
  rigidˢ = PK.perm-rigidˢ (Fin H.nV) _≟F_ H.vlab

  ------------------------------------------------------------------------
  -- Edge steps and runs
  ------------------------------------------------------------------------
  fire-termˢ
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
    → s Perm.↭ H.ein e ++ rest
    → HomS (map vl s) (map vl (H.eout e ++ rest))
  fire-termˢ e s rest perm =
    castˢ refl (sym (map-++ vl (H.eout e) rest))
      ((genˢ (H.elab e) ⊗ˢ idˢ {map vl rest})
        ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ perm))

  step-termˢ
    : (s : List (Fin H.nV)) (e : Fin H.nE)
    → HomS (map vl s) (map vl (edge-step H s e))
  step-termˢ s e with extract-prefix (H.ein e) s
  ... | nothing            = idˢ
  ... | just (rest , perm) = fire-termˢ e s rest perm

  edge-stepˢ
    : (s : List (Fin H.nV)) (e : Fin H.nE)
    → Σ[ s' ∈ List (Fin H.nV) ] HomS (map vl s) (map vl s')
  edge-stepˢ s e = (edge-step H s e , step-termˢ s e)

  run-termˢ
    : (es : List (Fin H.nE)) (s : List (Fin H.nV))
    → HomS (map vl s) (map vl (process-edges H es s))
  run-termˢ []       s = idˢ
  run-termˢ (e ∷ es) s = run-termˢ es (edge-step H s e) ∘ˢ step-termˢ s e

  process-edgesˢ
    : (es : List (Fin H.nE)) (s : List (Fin H.nV))
    → Σ[ s' ∈ List (Fin H.nV) ] HomS (map vl s) (map vl s')
  process-edgesˢ es s = (process-edges H es s , run-termˢ es s)

  pe-stack-++ˢ
    : ∀ (ps rest : List (Fin H.nE)) (s : List (Fin H.nV))
    → proj₁ (process-edgesˢ (ps ++ rest) s)
      ≡ proj₁ (process-edgesˢ rest (proj₁ (process-edgesˢ ps s)))
  pe-stack-++ˢ = process-edges-++ H

  ------------------------------------------------------------------------
  -- Right-frame separability
  ------------------------------------------------------------------------

  ein-disjoint : Fin H.nE → List (Fin H.nV) → Set
  ein-disjoint e R = All (λ k → extract-elem k R ≡ nothing) (H.ein e)

  block-disjoint : List (Fin H.nE) → List (Fin H.nV) → Set
  block-disjoint es R = All (λ e → ein-disjoint e R) es

  stack-sepˢ
    : ∀ es xs R → block-disjoint es R
    → proj₁ (process-edgesˢ es (xs ++ R)) ≡ proj₁ (process-edgesˢ es xs) ++ R
  stack-sepˢ []       xs R _          = refl
  stack-sepˢ (e ∷ es) xs R (de ∷ des) with extract-prefix (H.ein e) xs in eq
  ... | nothing
        rewrite extract-prefix-++ˡ-nothing (H.ein e) xs R de eq
        = stack-sepˢ es xs R des
  ... | just (rest , p)
        rewrite extract-prefix-++ˡ (H.ein e) xs R eq
              | sym (++-assoc (H.eout e) rest R)
        = stack-sepˢ es (H.eout e ++ rest) R des

  open Restrict (Fin H.nV) vl

  firedᵛ
    : (e : Fin H.nE) (rest : List (Fin H.nV)) {xs : List (Fin H.nV)}
    → xs Perm.↭ H.ein e ++ rest → HomV xs (H.eout e ++ rest)
  firedᵛ e rest p = (genˢ (H.elab e) ⊗ᵛ idᵛ {rest}) ∘ᵛ permuteᵛ p

  edge-step-firedᵛ
    : ∀ (e : Fin H.nE) (rest : List (Fin H.nV)) {xs : List (Fin H.nV)}
        (p : xs Perm.↭ H.ein e ++ rest)
    → fire-termˢ e xs rest p ≈ᵛ firedᵛ e rest p
  edge-step-firedᵛ e rest p =
    ≈̂⇒≈ˢ
      (≈̂-trans (cast-≈̂ {p = refl} {q = sym (map-++ vl (H.eout e) rest)})
               (∘-resp-≈̂
                 (≈̂-sym (⊗ᵛ-≈̂ (genˢ (H.elab e)) (idᵛ {rest})))
                 (cast-≈̂ {p = refl} {q = map-++ vl (H.ein e) rest})))

  pe-respᵛ
    : ∀ es {s s'} (E : s ≡ s')
      (E₁ : proj₁ (process-edgesˢ es s) ≡ proj₁ (process-edgesˢ es s'))
    → proj₂ (process-edgesˢ es s') ≡ castᵛ E E₁ (proj₂ (process-edgesˢ es s))
  pe-respᵛ es refl E₁ rewrite uipV E₁ refl = refl

  layer-sepᵛ
    : ∀ (e : Fin H.nE) (R rest : List (Fin H.nV)) {xs : List (Fin H.nV)}
        (p : xs Perm.↭ H.ein e ++ rest)
    → castᵛ refl (sym (++-assoc (H.eout e) rest R))
        (firedᵛ e (rest ++ R)
          (prefix-++ˡ-perm (H.ein e) (PermProp.++⁺ʳ R p)))
      ≈ᵛ firedᵛ e rest p ⊗ᵛ idᵛ {R}
  layer-sepᵛ e R rest {xs} p =
    viâ (castᵛ-≈̂ refl (sym (++-assoc B rest R)) (firedᵛ e (rest ++ R) pbig))
        (∘-resp-≈̂ G-side P-side)
        (≈ˢ⇒≈̂ (⊗id-distᵛ Box_r (permuteᵛ p)))
    where
      A = H.ein e ; B = H.eout e
      G₀ = genˢ (H.elab e)
      Box_r = G₀ ⊗ᵛ idᵛ {rest}
      pbig = prefix-++ˡ-perm A (PermProp.++⁺ʳ R p)

      G-side : (G₀ ⊗ᵛ idᵛ {rest ++ R}) ≈̂ (Box_r ⊗ᵛ idᵛ {R})
      G-side = ≈̂-sym (box-suffix-≈̂ᵛ G₀ rest R)

      P-side : permuteᵛ pbig ≈̂ (permuteᵛ p ⊗ᵛ idᵛ {R})
      P-side =
        ≈̂-trans (≈ˢ⇒≈̂ (≡⇒≈ˢ (permuteˢ-subst (++-assoc A rest R)
                               (PermProp.++⁺ʳ R p))))
        (≈̂-trans (cast-≈̂ {p = refl} {q = cong (map vl) (++-assoc A rest R)})
                 (≈ˢ⇒≈̂ (permuteᵛ-frame R p)))

  term-sepᵛ
    : ∀ es xs R (dis : block-disjoint es R)
      (Q : proj₁ (process-edgesˢ es (xs ++ R))
           ≡ proj₁ (process-edgesˢ es xs) ++ R)
    → castᵛ refl Q (proj₂ (process-edgesˢ es (xs ++ R)))
      ≈ᵛ proj₂ (process-edgesˢ es xs) ⊗ᵛ idᵛ {R}
  term-sepᵛ []       xs R _          Q =
    ≈-trans (cast-idᵛ refl Q) (≈-sym ⊗-idᵛ)
  term-sepᵛ (e ∷ es) xs R (de ∷ des) Q with extract-prefix (H.ein e) xs in eq
  ... | nothing
        rewrite extract-prefix-++ˡ-nothing (H.ein e) xs R de eq
        = ≈̂⇒≈ˢ
            (≈̂-trans (castᵛ-≈̂ refl Q _)
            (≈̂-trans (∘-resp-≈̂ (castᵛ⇒≈̂ refl Q _ (term-sepᵛ es xs R des Q)) ≈̂-refl)
                     (≈ˢ⇒≈̂ (≈-trans idʳ (⊗-respᵛ (≈-sym idʳ) ≈-refl)))))
  ... | just (rest , p)
        rewrite extract-prefix-++ˡ (H.ein e) xs R eq
        = ≈̂⇒≈ˢ
            (≈̂-trans (castᵛ-≈̂ refl Q _)
            (≈̂-trans (∘-resp-≈̂ Aside Bside)
            (≈̂-trans (≈ˢ⇒≈̂ interchangeᵛ)
                     (⊗-resp-≈̂ᵛ
                       (∘-resp-≈̂ ≈̂-refl
                         (≈̂-sym (≈ˢ⇒≈̂ (edge-step-firedᵛ e rest p))))
                       (≈ˢ⇒≈̂ idˡ)))))
        where
          B = H.eout e
          xs₁ = B ++ rest

          E∘ : B ++ (rest ++ R) ≡ xs₁ ++ R
          E∘ = sym (++-assoc B rest R)

          E₁ : proj₁ (process-edgesˢ es (B ++ (rest ++ R)))
               ≡ proj₁ (process-edgesˢ es (xs₁ ++ R))
          E₁ = cong (λ z → proj₁ (process-edgesˢ es z)) E∘

          QIH : proj₁ (process-edgesˢ es (xs₁ ++ R))
                ≡ proj₁ (process-edgesˢ es xs₁) ++ R
          QIH = trans (sym E₁) Q

          Aside : proj₂ (process-edgesˢ es (B ++ (rest ++ R)))
                  ≈̂ (proj₂ (process-edgesˢ es xs₁) ⊗ᵛ idᵛ {R})
          Aside =
            ≈̂-trans
              (≈̂-sym (≈̂-trans (≈ˢ⇒≈̂ (≡⇒≈ˢ (pe-respᵛ es E∘ E₁)))
                              (castᵛ-≈̂ E∘ E₁ _)))
              (castᵛ⇒≈̂ refl QIH _ (term-sepᵛ es xs₁ R des QIH))

          Bside : fire-termˢ e (xs ++ R) (rest ++ R)
                    (prefix-++ˡ-perm (H.ein e) (PermProp.++⁺ʳ R p))
                  ≈̂ (firedᵛ e rest p ⊗ᵛ idᵛ {R})
          Bside =
            ≈̂-trans (≈ˢ⇒≈̂ (edge-step-firedᵛ e (rest ++ R) _))
                    (castᵛ⇒≈̂ refl (sym (++-assoc B rest R)) _
                              (layer-sepᵛ e R rest p))

