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
  -- Separability, term level.

  import Data.List.Relation.Binary.Permutation.Propositional.Properties
    as PermProp

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
  -- `_≈̂_` version: both sides reduce (heterogeneously) to a CAST-FREE middle
  -- `mid = (box_rest ⊗ id{R}) ∘ (permuteˢ p ⊗ id{R})`.  `cast-≈̂` peels every
  -- boundary/wiring cast, `∘-resp-≈̂` threads the composite endpoint, and the
  -- residual content is exactly the two ⊗-frame lemmas the kit does not
  -- subsume — `box-suffix-ˢ` (⊗-assoc) on the box and `permuteˢ-frame` on the
  -- wiring.  The kit's general `⊗-resp-≈̂` pushes `id{R}` through the RHS
  -- composite-vs-tensor split.  Sub-lemmas carry full type signatures, which
  -- pin every `cast-≈̂`'s endpoints (the homogeneous-projection discipline).
  layer-sepˢ e xs R rest p W = ≈̂⇒≈ˢ (≈̂-trans lhs (≈̂-sym rhs))
    where
      A = H.ein e ; B = H.eout e
      G₀ = genˢ (H.elab e)
      mR = map vl R
      mAr  = map-++ vl A rest
      mArr = map-++ vl A (rest ++ R)
      mBr  = map-++ vl B rest
      mBrr = map-++ vl B (rest ++ R)
      Box_r = G₀ ⊗ˢ idˢ {map vl rest}
      permp = permuteˢ p
      -- `map-++`-recast of `permp` so it composes with `Box_r` (its raw codomain
      -- `map vl (A ++ rest)` is not definitionally `map vl A ++ map vl rest`)
      Pfac  = castˢ refl mAr permp
      pbig  = permuteˢ (prefix-++ˡ-perm A (PermProp.++⁺ʳ R p))
      mid   = (Box_r ⊗ˢ idˢ {mR}) ∘ˢ (Pfac ⊗ˢ idˢ {mR})

      -- `id{map vl rest ++ mR} ≈̂ id{map vl (rest ++ R)}` (a cast of identities)
      id-bridge : idˢ {map vl rest ++ mR} ≈̂ idˢ {map vl (rest ++ R)}
      id-bridge =
        ≈̂-trans (≈̂-sym (≈ˢ⇒≈̂ (cast-id (map-++ vl rest R)
                                        (map-++ vl rest R))))
                cast-≈̂

      -- the fired box over `rest ++ R` = the `rest`-box framed by id{R}
      G-side : (G₀ ⊗ˢ idˢ {map vl (rest ++ R)}) ≈̂ (Box_r ⊗ˢ idˢ {mR})
      G-side =
        ≈̂-sym (≈̂-trans (≈̂-trans (≈̂-sym cast-≈̂)
                                 (≈ˢ⇒≈̂ (box-suffix-ˢ G₀ (map vl rest) mR)))
                        (⊗-resp-≈̂ ≈̂-refl id-bridge))

      -- the framed wiring = `permuteˢ p` framed by id{R}
      P-side : castˢ refl mArr pbig ≈̂ (Pfac ⊗ˢ idˢ {mR})
      P-side =
        ≈̂-trans (≈ˢ⇒≈̂ (≡⇒≈ˢ (cong (castˢ refl mArr)
                          (permuteˢ-subst (++-assoc A rest R)
                                          (PermProp.++⁺ʳ R p)))))
        (≈̂-trans (cast-≈̂ {p = refl} {q = mArr})
        (≈̂-trans (cast-≈̂ {p = refl} {q = cong (map vl) (++-assoc A rest R)})
        (≈̂-trans (≈̂-sym (cast-≈̂ {p = map-++ vl xs R} {q = map-++ vl (A ++ rest) R}))
        (≈̂-trans (≈ˢ⇒≈̂ (permuteˢ-frame R p))
                 (⊗-resp-≈̂ (≈̂-sym (cast-≈̂ {p = refl} {q = mAr})) ≈̂-refl)))))

      lhs : castˢ (map-++ vl xs R) W
              (castˢ refl (sym mBrr)
                ((G₀ ⊗ˢ idˢ {map vl (rest ++ R)}) ∘ˢ castˢ refl mArr pbig))
            ≈̂ mid
      lhs = ≈̂-trans (cast-≈̂ {p = map-++ vl xs R} {q = W})
                    (≈̂-trans (cast-≈̂ {p = refl} {q = sym mBrr})
                             (∘-resp-≈̂ G-side P-side))

      rhs : (castˢ refl (sym mBr) (Box_r ∘ˢ castˢ refl mAr permp)) ⊗ˢ idˢ {mR}
            ≈̂ mid
      rhs =
        ≈̂-trans (⊗-resp-≈̂ cast-≈̂ ≈̂-refl)
                (≈ˢ⇒≈̂ (⊗id-distˢ Box_r Pfac))

  -- the SEPARABILITY THEOREM, term level
  term-sepˢ
    : ∀ es xs R (dis : block-disjoint es R)
      (Q : map vl (proj₁ (process-edgesˢ es (xs ++ R)))
           ≡ map vl (proj₁ (process-edgesˢ es xs)) ++ map vl R)
    → castˢ (map-++ vl xs R) Q (proj₂ (process-edgesˢ es (xs ++ R)))
      ≈ˢ proj₂ (process-edgesˢ es xs) ⊗ˢ idˢ {map vl R}
  term-sepˢ []       xs R _          Q =
    ≈-trans (cast-id (map-++ vl xs R) Q) (≈-sym ⊗-id)
  term-sepˢ (e ∷ es) xs R (de ∷ des) Q with extract-prefix (H.ein e) xs in eq
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
