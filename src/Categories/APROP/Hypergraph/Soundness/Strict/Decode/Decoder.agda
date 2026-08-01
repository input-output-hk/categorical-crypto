{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The STRICT DECODER + the separability theorem.
--
-- Ports the decoder's `edge-step`/`process-edges` to the presented strict
-- SMC (`FreeStrictSMC`): a fired layer is
--     castˢ ((genˢ (elab e) ⊗ˢ idˢ) ∘ˢ castˢ (permuteˢ perm))
-- — two UIP-trivial `map-++` casts where the non-strict layer pays
-- `unflatten-++-≅` conjugation plus `subst₂` transport — and re-proves the
-- SEPARABILITY theorem (the G-side core of the ⊗-shape lemma):
--
--     process-edgesˢ es (xs ++ R)  ≈ˢ  process-edgesˢ es xs ⊗ˢ idˢ {R}
--
-- (modulo the stack equality), whose non-strict counterpart costs
-- SeparableStack (752 LOC) + the former `BoxKernel` box-suffix machinery.
-- Stack-level lemmas (`extract-prefix-++ˡ` etc.) are term-free and are
-- REUSED from SeparableStack as-is.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix; extract-elem)
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.SeparableStack sig
  using (prefix-++ˡ-perm; extract-prefix-++ˡ; extract-prefix-++ˡ-nothing)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_ public

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; map-++; ≡-dec)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Axiom.UniquenessOfIdentityProofs using (UIP; module Decidable⇒UIP)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

module StrictDecoder (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open Perm′ (Fin H.nV) H.vlab public

  vl : Fin H.nV → X
  vl = H.vlab

  uipV : UIP (List (Fin H.nV))
  uipV = Decidable⇒UIP.≡-irrelevant (≡-dec _≟F_)

  ------------------------------------------------------------------------
  -- The strict decoder.

  edge-stepˢ
    : (s : List (Fin H.nV)) (e : Fin H.nE)
    → Σ[ s' ∈ List (Fin H.nV) ] HomS (map vl s) (map vl s')
  edge-stepˢ s e with extract-prefix (H.ein e) s
  ... | nothing            = (s , idˢ)
  ... | just (rest , perm) =
    ( H.eout e ++ rest
    , castˢ refl (sym (map-++ vl (H.eout e) rest))
        ((genˢ (H.elab e) ⊗ˢ idˢ {map vl rest})
          ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ perm)) )

  process-edgesˢ
    : (es : List (Fin H.nE)) (s : List (Fin H.nV))
    → Σ[ s' ∈ List (Fin H.nV) ] HomS (map vl s) (map vl s')
  process-edgesˢ []       s = (s , idˢ)
  process-edgesˢ (e ∷ es) s =
    let (s'  , t)  = edge-stepˢ s e
        (s'' , t') = process-edgesˢ es s'
    in (s'' , t' ∘ˢ t)

  ------------------------------------------------------------------------
  -- Separability, stack level (the term-free half; same 12-line shape as
  -- the non-strict `process-edges-stack-sep`).

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


  ------------------------------------------------------------------------
  -- Separability, term level — in the `Restrict` layer (F7).
  --
  -- Both statements are about VERTEX stacks, so the only transports are
  -- `castᵛ` (a `List (Fin nV)` equality) and the endpoint bookkeeping the
  -- label-level spelling needed (`map-++ vl xs R`, the `W`/`QIH`
  -- map-distribution proofs, `cast-⊗-frame`, `∘-cast-split`) is gone.

  import Data.List.Relation.Binary.Permutation.Propositional.Properties
    as PermProp

  open Restrict (Fin H.nV) vl
    using ( HomV; idᵛ; _∘ᵛ_; _⊗ᵛ_; castᵛ; _≈ᵛ_; permuteᵛ; permuteᵛ-frame
          ; castᵛ-≈̂; ⊗-respᵛ; ⊗-resp-≈̂ᵛ; ⊗-idᵛ; interchangeᵛ; ⊗id-distᵛ
          ; box-suffix-≈̂ᵛ; cast-idᵛ )

  -- the fired layer, at V level: a box on `ein e` framed by the residual,
  -- after the wiring that exposes `ein e` as a prefix
  firedᵛ
    : (e : Fin H.nE) (rest : List (Fin H.nV)) {xs : List (Fin H.nV)}
    → xs Perm.↭ H.ein e ++ rest → HomV xs (H.eout e ++ rest)
  firedᵛ e rest p = (genˢ (H.elab e) ⊗ᵛ idᵛ {rest}) ∘ᵛ permuteᵛ p

  -- `edge-stepˢ`'s FIRE branch IS `firedᵛ`: its two `map-++` casts are
  -- exactly the ones `_⊗ᵛ_` carries.
  edge-step-firedᵛ
    : ∀ (e : Fin H.nE) (rest : List (Fin H.nV)) {xs : List (Fin H.nV)}
        (p : xs Perm.↭ H.ein e ++ rest)
    → castˢ refl (sym (map-++ vl (H.eout e) rest))
        ((genˢ (H.elab e) ⊗ˢ idˢ {map vl rest})
          ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p))
      ≈ᵛ firedᵛ e rest p
  edge-step-firedᵛ e rest p =
    ≈̂⇒≈ˢ
      (≈̂-trans (cast-≈̂ {p = refl} {q = sym (map-++ vl (H.eout e) rest)})
               (∘-resp-≈̂
                 (≈̂-sym (cast-≈̂ {p = sym (map-++ vl (H.ein e) rest)}
                                {q = sym (map-++ vl (H.eout e) rest)}))
                 (cast-≈̂ {p = refl} {q = map-++ vl (H.ein e) rest})))

  -- `process-edgesˢ` respects propositional stack equality (UIP-trivially)
  pe-respᵛ
    : ∀ es {s s'} (E : s ≡ s')
      (E₁ : proj₁ (process-edgesˢ es s) ≡ proj₁ (process-edgesˢ es s'))
    → proj₂ (process-edgesˢ es s') ≡ castᵛ E E₁ (proj₂ (process-edgesˢ es s))
  pe-respᵛ es refl E₁ rewrite uipV E₁ refl = refl

  -- the fired-layer factorization: the `(rest ++ R)`-side layer is the
  -- `rest`-side layer framed by `idᵛ {R}`
  layer-sepᵛ
    : ∀ (e : Fin H.nE) (R rest : List (Fin H.nV)) {xs : List (Fin H.nV)}
        (p : xs Perm.↭ H.ein e ++ rest)
    → castᵛ refl (sym (++-assoc (H.eout e) rest R))
        (firedᵛ e (rest ++ R)
          (prefix-++ˡ-perm (H.ein e) (PermProp.++⁺ʳ R p)))
      ≈ᵛ firedᵛ e rest p ⊗ᵛ idᵛ {R}
  layer-sepᵛ e R rest {xs} p =
    ≈̂⇒≈ˢ
      (≈̂-trans (castᵛ-≈̂ refl (sym (++-assoc B rest R))
                  (firedᵛ e (rest ++ R) pbig))
      (≈̂-trans (∘-resp-≈̂ G-side P-side)
               (≈̂-sym (≈ˢ⇒≈̂ (⊗id-distᵛ Box_r (permuteᵛ p))))))
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

  -- the SEPARABILITY THEOREM at V level: the stack coherence is a
  -- `List (Fin nV)` equality (`stack-sepˢ` supplies it at the projection)
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
            (≈̂-trans (∘-resp-≈̂ (≈̂-trans (≈̂-sym (castᵛ-≈̂ refl Q _))
                                        (≈ˢ⇒≈̂ (term-sepᵛ es xs R des Q)))
                               ≈̂-refl)
                     (≈ˢ⇒≈̂ (≈-trans idʳ (⊗-respᵛ (≈-sym idʳ) ≈-refl)))))
  ... | just (rest , p)
        rewrite extract-prefix-++ˡ (H.ein e) xs R eq
        = main
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
              (≈̂-trans (≈̂-sym (castᵛ-≈̂ refl QIH _))
                       (≈ˢ⇒≈̂ (term-sepᵛ es xs₁ R des QIH)))

          Bside : castˢ refl (sym (map-++ vl B (rest ++ R)))
                    ((genˢ (H.elab e) ⊗ˢ idˢ {map vl (rest ++ R)})
                      ∘ˢ castˢ refl (map-++ vl (H.ein e) (rest ++ R))
                           (permuteˢ (prefix-++ˡ-perm (H.ein e)
                                        (PermProp.++⁺ʳ R p))))
                  ≈̂ (firedᵛ e rest p ⊗ᵛ idᵛ {R})
          Bside =
            ≈̂-trans (≈ˢ⇒≈̂ (edge-step-firedᵛ e (rest ++ R) _))
            (≈̂-trans (≈̂-sym (castᵛ-≈̂ refl (sym (++-assoc B rest R)) _))
                     (≈ˢ⇒≈̂ (layer-sepᵛ e R rest p)))

          main
            : castᵛ refl Q
                (proj₂ (process-edgesˢ es (B ++ (rest ++ R)))
                  ∘ᵛ castˢ refl (sym (map-++ vl B (rest ++ R)))
                      ((genˢ (H.elab e) ⊗ˢ idˢ {map vl (rest ++ R)})
                        ∘ˢ castˢ refl (map-++ vl (H.ein e) (rest ++ R))
                             (permuteˢ (prefix-++ˡ-perm (H.ein e)
                                          (PermProp.++⁺ʳ R p)))))
              ≈ᵛ (proj₂ (process-edgesˢ es xs₁)
                   ∘ᵛ castˢ refl (sym (map-++ vl B rest))
                       ((genˢ (H.elab e) ⊗ˢ idˢ {map vl rest})
                         ∘ˢ castˢ refl (map-++ vl (H.ein e) rest)
                              (permuteˢ p)))
                 ⊗ᵛ idᵛ {R}
          main =
            ≈̂⇒≈ˢ
              (≈̂-trans (castᵛ-≈̂ refl Q _)
              (≈̂-trans (∘-resp-≈̂ Aside Bside)
              (≈̂-trans (≈ˢ⇒≈̂ interchangeᵛ)
                       (⊗-resp-≈̂ᵛ
                         (∘-resp-≈̂ ≈̂-refl
                           (≈̂-sym (≈ˢ⇒≈̂ (edge-step-firedᵛ e rest p))))
                         (≈ˢ⇒≈̂ idˡ)))))
