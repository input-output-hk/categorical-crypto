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
-- SeparableStack (752 LOC) + the BoxKernel box-suffix machinery.
-- Stack-level lemmas (`extract-prefix-++ˡ` etc.) are term-free and are
-- REUSED from SeparableStack as-is.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decoder
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (extract-prefix; extract-elem)
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.SeparableStack sig _≟X_
  using (prefix-++ˡ-perm; extract-prefix-++ˡ; extract-prefix-++ˡ-nothing)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_ public

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; map-++; ≡-dec)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Axiom.UniquenessOfIdentityProofs using (UIP; module Decidable⇒UIP)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
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
  -- Separability, term level.

  private
    import Data.List.Relation.Binary.Permutation.Propositional.Properties
      as PermProp

    -- (X ∘ˢ Y) ⊗ˢ id  ≈  (X ⊗ˢ id) ∘ˢ (Y ⊗ˢ id)
    ⊗id-dist
      : ∀ {as bs cs ls} (X : HomS bs cs) (Y : HomS as bs)
      → (X ∘ˢ Y) ⊗ˢ idˢ {ls} ≈ˢ (X ⊗ˢ idˢ {ls}) ∘ˢ (Y ⊗ˢ idˢ {ls})
    ⊗id-dist X Y =
      ≈-trans (⊗-resp ≈-refl (≈-sym idˡ)) (≈-sym interchangeˢ)

  -- `process-edgesˢ` respects propositional stack equality (UIP-trivially)
  pe-resp
    : ∀ es {s s'} (E : s ≡ s')
      (E₁ : proj₁ (process-edgesˢ es s) ≡ proj₁ (process-edgesˢ es s'))
    → proj₂ (process-edgesˢ es s')
      ≡ castˢ (cong (map vl) E) (cong (map vl) E₁) (proj₂ (process-edgesˢ es s))
  pe-resp es refl E₁ rewrite uipV E₁ refl = refl

  -- the fired-layer factorization: the (xs ++ R)-side layer is the
  -- xs-side layer framed by idˢ {map vl R}
  layer-sepˢ
    : ∀ (e : Fin H.nE) xs R rest (p : xs Perm.↭ H.ein e ++ rest)
      (W : map vl (H.eout e ++ (rest ++ R))
           ≡ map vl (H.eout e ++ rest) ++ map vl R)
    → castˢ (map-++ vl xs R) W
        (castˢ refl (sym (map-++ vl (H.eout e) (rest ++ R)))
          ((genˢ (H.elab e) ⊗ˢ idˢ {map vl (rest ++ R)})
            ∘ˢ castˢ refl (map-++ vl (H.ein e) (rest ++ R))
                 (permuteˢ (prefix-++ˡ-perm (H.ein e) (PermProp.++⁺ʳ R p)))))
      ≈ˢ (castˢ refl (sym (map-++ vl (H.eout e) rest))
           ((genˢ (H.elab e) ⊗ˢ idˢ {map vl rest})
             ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)))
         ⊗ˢ idˢ {map vl R}
  layer-sepˢ e xs R rest p W = ≈-trans lhs→nf (≈-sym rhs→nf)
    where
      A = H.ein e ; B = H.eout e
      G₀ = genˢ (H.elab e)
      mR = map vl R
      C₂ = cong (_++ mR) (sym (map-++ vl B rest))
      M′ = cong (_++ mR) (map-++ vl A rest)
      Q₁ = map-++ vl (A ++ rest) R
      Xn = (G₀ ⊗ˢ idˢ {map vl rest}) ⊗ˢ idˢ {mR}
      Yn = castˢ refl M′ ((permuteˢ p) ⊗ˢ idˢ {mR})

      NF : HomS (map vl xs ++ mR) (map vl (B ++ rest) ++ mR)
      NF = castˢ refl C₂ Xn ∘ˢ Yn

      rhs→nf
        : (castˢ refl (sym (map-++ vl B rest))
            ((G₀ ⊗ˢ idˢ {map vl rest})
              ∘ˢ castˢ refl (map-++ vl A rest) (permuteˢ p)))
          ⊗ˢ idˢ {mR}
          ≈ˢ NF
      rhs→nf =
        ≈-trans (≡⇒≈ˢ (cast-⊗ˡ refl (sym (map-++ vl B rest)) _))
        (≈-trans (cast-resp refl C₂
          (≈-trans (⊗id-dist (G₀ ⊗ˢ idˢ {map vl rest})
                             (castˢ refl (map-++ vl A rest) (permuteˢ p)))
                   (∘-resp ≈-refl
                     (≡⇒≈ˢ (cast-⊗ˡ refl (map-++ vl A rest) (permuteˢ p))))))
          (∘-cast-split refl refl C₂ Xn Yn))

      lhs→nf
        : castˢ (map-++ vl xs R) W
            (castˢ refl (sym (map-++ vl B (rest ++ R)))
              ((G₀ ⊗ˢ idˢ {map vl (rest ++ R)})
                ∘ˢ castˢ refl (map-++ vl A (rest ++ R))
                     (permuteˢ (prefix-++ˡ-perm A (PermProp.++⁺ʳ R p)))))
          ≈ˢ NF
      lhs→nf =
        ≈-trans (≡⇒≈ˢ (cast-fuse refl (map-++ vl xs R)
                        (sym (map-++ vl B (rest ++ R))) W _))
        (≈-trans (∘-cast-split (map-++ vl xs R) M
                   (trans (sym (map-++ vl B (rest ++ R))) W) _ _)
          (∘-resp G-side P-side))
        where
          M : map vl A ++ map vl (rest ++ R)
              ≡ (map vl A ++ map vl rest) ++ mR
          M = trans (cong (map vl A ++_) (map-++ vl rest R))
                    (sym (++-assoc (map vl A) (map vl rest) mR))

          G-side
            : castˢ M (trans (sym (map-++ vl B (rest ++ R))) W)
                (G₀ ⊗ˢ idˢ {map vl (rest ++ R)})
              ≈ˢ castˢ refl C₂ Xn
          G-side =
            ≈-trans (cast-resp M (trans (sym (map-++ vl B (rest ++ R))) W)
              (≈-trans
                (⊗-resp ≈-refl
                  (≈-sym (cast-id (sym (map-++ vl rest R))
                                  (sym (map-++ vl rest R)))))
                (≈-sym (cast-⊗-frame G₀
                  (sym (map-++ vl rest R)) (sym (map-++ vl rest R))
                  (idˢ {map vl rest ++ mR})
                  (cong (map vl A ++_) (sym (map-++ vl rest R)))
                  (cong (map vl B ++_) (sym (map-++ vl rest R)))))))
            (≈-trans (≡⇒≈ˢ (cast-fuse
                (cong (map vl A ++_) (sym (map-++ vl rest R)))
                M
                (cong (map vl B ++_) (sym (map-++ vl rest R)))
                (trans (sym (map-++ vl B (rest ++ R))) W) _))
            (≈-trans (cast-resp _ _
                (≈-sym (box-suffix-ˢ G₀ (map vl rest) mR)))
            (≈-trans (≡⇒≈ˢ (cast-fuse
                (++-assoc (map vl A) (map vl rest) mR)
                (trans (cong (map vl A ++_) (sym (map-++ vl rest R))) M)
                (++-assoc (map vl B) (map vl rest) mR)
                (trans (cong (map vl B ++_) (sym (map-++ vl rest R)))
                       (trans (sym (map-++ vl B (rest ++ R))) W)) Xn))
              (≡⇒≈ˢ (cast-irrel _ refl _ C₂ Xn)))))

          P-side
            : castˢ (map-++ vl xs R) M
                (castˢ refl (map-++ vl A (rest ++ R))
                  (permuteˢ (prefix-++ˡ-perm A (PermProp.++⁺ʳ R p))))
              ≈ˢ Yn
          P-side =
            ≈-trans (≡⇒≈ˢ (cast-fuse refl (map-++ vl xs R)
                            (map-++ vl A (rest ++ R)) M _))
            (≈-trans (≡⇒≈ˢ (cong (castˢ (map-++ vl xs R)
                                        (trans (map-++ vl A (rest ++ R)) M))
                             (permuteˢ-subst (++-assoc A rest R)
                                             (PermProp.++⁺ʳ R p))))
            (≈-trans (≡⇒≈ˢ (cast-fuse refl (map-++ vl xs R)
                             (cong (map vl) (++-assoc A rest R))
                             (trans (map-++ vl A (rest ++ R)) M)
                             (permuteˢ (PermProp.++⁺ʳ R p))))
            (≈-trans (≡⇒≈ˢ (cast-irrel _ (trans (map-++ vl xs R) refl) _
                             (trans Q₁ M′)
                             (permuteˢ (PermProp.++⁺ʳ R p))))
            (≈-trans (≈-sym (≡⇒≈ˢ (cast-fuse (map-++ vl xs R) refl Q₁ M′
                             (permuteˢ (PermProp.++⁺ʳ R p)))))
              (cast-resp refl M′ (permuteˢ-frame R p))))))

  -- the SEPARABILITY THEOREM, term level
  term-sepˢ
    : ∀ es xs R (dis : block-disjoint es R)
      (Q : map vl (proj₁ (process-edgesˢ es (xs ++ R)))
           ≡ map vl (proj₁ (process-edgesˢ es xs)) ++ map vl R)
    → castˢ (map-++ vl xs R) Q (proj₂ (process-edgesˢ es (xs ++ R)))
      ≈ˢ proj₂ (process-edgesˢ es xs) ⊗ˢ idˢ {map vl R}
  term-sepˢ []       xs R _          Q =
    ≈-trans (cast-id (map-++ vl xs R) Q) (≈-sym ⊗-id)
  term-sepˢ (e ∷ es) xs R (de ∷ des) Q
    with extract-prefix (H.ein e) xs in eq
  ... | nothing
        rewrite extract-prefix-++ˡ-nothing (H.ein e) xs R de eq
        = ≈-trans (∘-cast-split (map-++ vl xs R) (map-++ vl xs R) Q _ idˢ)
            (≈-trans (∘-resp (term-sepˢ es xs R des Q)
                             (cast-id (map-++ vl xs R) (map-++ vl xs R)))
              (≈-trans (∘-resp ≈-refl (≈-sym ⊗-id))
                (≈-trans interchangeˢ
                  (⊗-resp ≈-refl idˡ))))
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

          W : map vl (B ++ (rest ++ R)) ≡ map vl xs₁ ++ map vl R
          W = trans (cong (map vl) E∘) (map-++ vl xs₁ R)

          QIH : map vl (proj₁ (process-edgesˢ es (xs₁ ++ R)))
                ≡ map vl (proj₁ (process-edgesˢ es xs₁)) ++ map vl R
          QIH = trans (sym (cong (map vl) E₁)) Q

          main
            : castˢ (map-++ vl xs R) Q
                (proj₂ (process-edgesˢ es (B ++ (rest ++ R)))
                  ∘ˢ castˢ refl (sym (map-++ vl B (rest ++ R)))
                      ((genˢ (H.elab e) ⊗ˢ idˢ {map vl (rest ++ R)})
                        ∘ˢ castˢ refl (map-++ vl (H.ein e) (rest ++ R))
                             (permuteˢ (prefix-++ˡ-perm (H.ein e)
                                          (PermProp.++⁺ʳ R p)))))
              ≈ˢ (proj₂ (process-edgesˢ es xs₁)
                   ∘ˢ castˢ refl (sym (map-++ vl B rest))
                       ((genˢ (H.elab e) ⊗ˢ idˢ {map vl rest})
                         ∘ˢ castˢ refl (map-++ vl (H.ein e) rest)
                              (permuteˢ p)))
                 ⊗ˢ idˢ {map vl R}
          main =
            ≈-trans (∘-cast-split (map-++ vl xs R) W Q _ _)
            (≈-trans
              (∘-resp
                (≈-trans
                  (≡⇒≈ˢ (cong (castˢ W Q)
                          (pe-resp es (sym E∘) (sym E₁))))
                (≈-trans
                  (≡⇒≈ˢ (cast-fuse (cong (map vl) (sym E∘)) W
                                   (cong (map vl) (sym E₁)) Q _))
                (≈-trans
                  (≡⇒≈ˢ (cast-irrel _ (map-++ vl xs₁ R) _ QIH _))
                  (term-sepˢ es xs₁ R des QIH))))
                (layer-sepˢ e xs R rest p W))
              (≈-trans interchangeˢ
                (⊗-resp ≈-refl idˡ)))
