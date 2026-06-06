{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Hypergraph isomorphism (TensorRocq §3.2): two hypergraphs are isomorphic
-- when there is a bijection of vertices and a bijection of edges that
-- preserves labels, endpoints, and the ordered boundary.  Defines the
-- relation and proves it is an equivalence; translation soundness lives
-- in `Hypergraph.Soundness`.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Iso where

open import Categories.APROP.Hypergraph.Core

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (map-∘; map-cong; map-id)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst; subst₂)

--------------------------------------------------------------------------------
-- Helpers for shuffling `subst₂` along proof equalities.

private
  -- Two `subst₂` transports with the same target are equal if the
  -- equality proofs are.
  subst₂-≡ : ∀ {A B : Set} {P : A → B → Set} {a a'} {b b'}
           → (p₁ p₂ : a ≡ a') (q₁ q₂ : b ≡ b') (x : P a b)
           → p₁ ≡ p₂ → q₁ ≡ q₂
           → subst₂ P p₁ q₁ x ≡ subst₂ P p₂ q₂ x
  subst₂-≡ _ _ _ _ _ refl refl = refl

  -- `subst₂` along `refl` does nothing.
  subst₂-refl : ∀ {A B : Set} {P : A → B → Set} {a b} (x : P a b)
              → subst₂ P refl refl x ≡ x
  subst₂-refl _ = refl

  -- Inverse: `subst₂ P (sym p) (sym q)` undoes `subst₂ P p q`.
  subst₂-sym-subst₂ : ∀ {A B : Set} {P : A → B → Set} {a a'} {b b'}
                    → (p : a ≡ a') (q : b ≡ b') (x : P a b)
                    → subst₂ P (sym p) (sym q) (subst₂ P p q x) ≡ x
  subst₂-sym-subst₂ refl refl _ = refl

  -- And the other direction.
  subst₂-subst₂-sym : ∀ {A B : Set} {P : A → B → Set} {a a'} {b b'}
                    → (p : a ≡ a') (q : b ≡ b') (x : P a' b')
                    → subst₂ P p q (subst₂ P (sym p) (sym q) x) ≡ x
  subst₂-subst₂-sym refl refl _ = refl

  -- Composition: two nested transports collapse.
  subst₂-trans : ∀ {A B : Set} {P : A → B → Set} {a₁ a₂ a₃} {b₁ b₂ b₃}
               → (p : a₁ ≡ a₂) (p' : a₂ ≡ a₃) (q : b₁ ≡ b₂) (q' : b₂ ≡ b₃)
               → (x : P a₁ b₁)
               → subst₂ P p' q' (subst₂ P p q x)
               ≡ subst₂ P (trans p p') (trans q q') x
  subst₂-trans refl refl refl refl _ = refl

--------------------------------------------------------------------------------
-- The isomorphism relation.

module _ {X : Set} {Gen : List X → List X → Set} where

  record _≅ᴴ_ (G K : Hypergraph Gen) : Set where
    private
      module G = Hypergraph G
      module K = Hypergraph K
    field
      -- Vertex bijection.
      φ      : Fin G.nV → Fin K.nV
      φ⁻¹    : Fin K.nV → Fin G.nV
      φ-left : ∀ i → φ⁻¹ (φ i) ≡ i
      φ-rght : ∀ i → φ (φ⁻¹ i) ≡ i

      -- Edge bijection.
      ψ      : Fin G.nE → Fin K.nE
      ψ⁻¹    : Fin K.nE → Fin G.nE
      ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
      ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e

      -- Vertex labels agree: K.vlab ∘ φ ≗ G.vlab.
      φ-lab  : ∀ i → K.vlab (φ i) ≡ G.vlab i

      -- Edge endpoints: K.ein/eout composed with ψ equal `map φ` of
      -- G.ein/eout.
      ψ-ein  : ∀ e → K.ein  (ψ e) ≡ map φ (G.ein e)
      ψ-eout : ∀ e → K.eout (ψ e) ≡ map φ (G.eout e)

      -- Boundary preserved: K.dom/cod = `map φ` G.dom/cod.
      φ-dom  : K.dom ≡ map φ G.dom
      φ-cod  : K.cod ≡ map φ G.cod

      -- Atom-list equalities at each edge.  Implied by the fields above,
      -- but kept as fields so callers can supply `refl`-ish witnesses.
      atom-ein  : ∀ e → map K.vlab (K.ein  (ψ e)) ≡ map G.vlab (G.ein e)
      atom-eout : ∀ e → map K.vlab (K.eout (ψ e)) ≡ map G.vlab (G.eout e)

      -- Edge labels agree up to `subst₂` along the atom-list equalities.
      ψ-elab : ∀ e → subst₂ Gen (atom-ein e) (atom-eout e) (K.elab (ψ e))
                   ≡ G.elab e

--------------------------------------------------------------------------------
-- Reflexivity.

module _ {X : Set} {Gen : List X → List X → Set} where

  refl-≅ᴴ : (G : Hypergraph Gen) → G ≅ᴴ G
  refl-≅ᴴ G = record
    { φ         = id
    ; φ⁻¹       = id
    ; φ-left    = λ _ → refl
    ; φ-rght    = λ _ → refl
    ; ψ         = id
    ; ψ⁻¹       = id
    ; ψ-left    = λ _ → refl
    ; ψ-rght    = λ _ → refl
    ; φ-lab     = λ _ → refl
    ; ψ-ein     = λ e → sym (map-id (G.ein e))
    ; ψ-eout    = λ e → sym (map-id (G.eout e))
    ; φ-dom     = sym (map-id G.dom)
    ; φ-cod     = sym (map-id G.cod)
    ; atom-ein  = λ _ → refl
    ; atom-eout = λ _ → refl
    ; ψ-elab    = λ _ → refl
    }
    where module G = Hypergraph G

--------------------------------------------------------------------------------
-- Symmetry. Invert the two bijections and flip the transports.

module _ {X : Set} {Gen : List X → List X → Set} where

  sym-≅ᴴ : {G K : Hypergraph Gen} → G ≅ᴴ K → K ≅ᴴ G
  sym-≅ᴴ {G} {K} iso = record
    { φ         = φ⁻¹
    ; φ⁻¹       = φ
    ; φ-left    = φ-rght
    ; φ-rght    = φ-left
    ; ψ         = ψ⁻¹
    ; ψ⁻¹       = ψ
    ; ψ-left    = ψ-rght
    ; ψ-rght    = ψ-left
    ; φ-lab     = λ j → trans (sym (φ-lab (φ⁻¹ j)))
                              (cong K.vlab (φ-rght j))
    ; ψ-ein     = λ e → ein-sym e
    ; ψ-eout    = λ e → eout-sym e
    ; φ-dom     = dom-sym
    ; φ-cod     = cod-sym
    ; atom-ein  = λ e → atom-ein-sym e
    ; atom-eout = λ e → atom-eout-sym e
    ; ψ-elab    = elab-sym
    }
    where
      open _≅ᴴ_ iso
      module G = Hypergraph G
      module K = Hypergraph K

      -- `map (φ⁻¹ ∘ φ) ≗ id`, so `map φ⁻¹ (map φ xs) ≡ xs`.
      map-φ⁻¹φ : (xs : List (Fin G.nV)) → map φ⁻¹ (map φ xs) ≡ xs
      map-φ⁻¹φ xs = trans (sym (map-∘ xs))
                   (trans (map-cong φ-left xs) (map-id xs))

      map-φφ⁻¹ : (ys : List (Fin K.nV)) → map φ (map φ⁻¹ ys) ≡ ys
      map-φφ⁻¹ ys = trans (sym (map-∘ ys))
                   (trans (map-cong φ-rght ys) (map-id ys))

      -- ein equation in the flipped direction (via map-φ⁻¹φ + ψ-rght).
      ein-sym : ∀ e → G.ein (ψ⁻¹ e) ≡ map φ⁻¹ (K.ein e)
      ein-sym e =
        trans (sym (map-φ⁻¹φ (G.ein (ψ⁻¹ e))))
              (cong (map φ⁻¹)
                (trans (sym (ψ-ein (ψ⁻¹ e)))
                       (cong K.ein (ψ-rght e))))

      eout-sym : ∀ e → G.eout (ψ⁻¹ e) ≡ map φ⁻¹ (K.eout e)
      eout-sym e =
        trans (sym (map-φ⁻¹φ (G.eout (ψ⁻¹ e))))
              (cong (map φ⁻¹)
                (trans (sym (ψ-eout (ψ⁻¹ e)))
                       (cong K.eout (ψ-rght e))))

      dom-sym : G.dom ≡ map φ⁻¹ K.dom
      dom-sym = trans (sym (map-φ⁻¹φ G.dom))
                      (sym (cong (map φ⁻¹) φ-dom))

      cod-sym : G.cod ≡ map φ⁻¹ K.cod
      cod-sym = trans (sym (map-φ⁻¹φ G.cod))
                      (sym (cong (map φ⁻¹) φ-cod))

      atom-ein-sym : ∀ e → map G.vlab (G.ein (ψ⁻¹ e)) ≡ map K.vlab (K.ein e)
      atom-ein-sym e =
        trans (sym (atom-ein (ψ⁻¹ e)))
              (cong (λ z → map K.vlab (K.ein z)) (ψ-rght e))

      atom-eout-sym : ∀ e → map G.vlab (G.eout (ψ⁻¹ e)) ≡ map K.vlab (K.eout e)
      atom-eout-sym e =
        trans (sym (atom-eout (ψ⁻¹ e)))
              (cong (λ z → map K.vlab (K.eout z)) (ψ-rght e))

      K-elab-cong : ∀ {e₁ e₂} (eq : e₁ ≡ e₂)
                  → K.elab e₂ ≡ subst₂ Gen
                                  (cong (λ z → map K.vlab (K.ein z)) eq)
                                  (cong (λ z → map K.vlab (K.eout z)) eq)
                                  (K.elab e₁)
      K-elab-cong refl = refl

      elab-sym : ∀ e → subst₂ Gen (atom-ein-sym e) (atom-eout-sym e)
                                  (G.elab (ψ⁻¹ e))
                       ≡ K.elab e
      elab-sym e =
        let
          -- original ψ-elab at (ψ⁻¹ e)
          step₁ : subst₂ Gen (atom-ein (ψ⁻¹ e)) (atom-eout (ψ⁻¹ e))
                    (K.elab (ψ (ψ⁻¹ e)))
                  ≡ G.elab (ψ⁻¹ e)
          step₁ = ψ-elab (ψ⁻¹ e)
          -- invert
          step₂ : K.elab (ψ (ψ⁻¹ e))
                  ≡ subst₂ Gen (sym (atom-ein (ψ⁻¹ e)))
                               (sym (atom-eout (ψ⁻¹ e)))
                               (G.elab (ψ⁻¹ e))
          step₂ = trans (sym (subst₂-sym-subst₂ (atom-ein (ψ⁻¹ e))
                                                 (atom-eout (ψ⁻¹ e))
                                                 (K.elab (ψ (ψ⁻¹ e)))))
                        (cong (subst₂ Gen (sym (atom-ein (ψ⁻¹ e)))
                                           (sym (atom-eout (ψ⁻¹ e)))) step₁)
          -- transport along ψ-rght e to K.elab e
          step₃ : K.elab e
                  ≡ subst₂ Gen (cong (λ z → map K.vlab (K.ein z)) (ψ-rght e))
                                (cong (λ z → map K.vlab (K.eout z)) (ψ-rght e))
                                (K.elab (ψ (ψ⁻¹ e)))
          step₃ = K-elab-cong (ψ-rght e)
          -- combine
          combined : K.elab e
                     ≡ subst₂ Gen (cong (λ z → map K.vlab (K.ein z)) (ψ-rght e))
                                   (cong (λ z → map K.vlab (K.eout z)) (ψ-rght e))
                          (subst₂ Gen (sym (atom-ein (ψ⁻¹ e)))
                                       (sym (atom-eout (ψ⁻¹ e)))
                                       (G.elab (ψ⁻¹ e)))
          combined = trans step₃ (cong (subst₂ Gen _ _) step₂)
          -- collapse the nested subst₂
          collapsed : subst₂ Gen
                        (trans (sym (atom-ein (ψ⁻¹ e)))
                               (cong (λ z → map K.vlab (K.ein z)) (ψ-rght e)))
                        (trans (sym (atom-eout (ψ⁻¹ e)))
                               (cong (λ z → map K.vlab (K.eout z)) (ψ-rght e)))
                        (G.elab (ψ⁻¹ e))
                     ≡ K.elab e
          collapsed = trans (sym (subst₂-trans
                                    (sym (atom-ein (ψ⁻¹ e)))
                                    (cong (λ z → map K.vlab (K.ein z)) (ψ-rght e))
                                    (sym (atom-eout (ψ⁻¹ e)))
                                    (cong (λ z → map K.vlab (K.eout z)) (ψ-rght e))
                                    (G.elab (ψ⁻¹ e))))
                            (sym combined)
        in collapsed

--------------------------------------------------------------------------------
-- Transitivity. Compose the two bijections.

module _ {X : Set} {Gen : List X → List X → Set} where

  trans-≅ᴴ : {G H K : Hypergraph Gen}
           → G ≅ᴴ H → H ≅ᴴ K → G ≅ᴴ K
  trans-≅ᴴ {G} {H} {K} iso₁ iso₂ = record
    { φ         = λ i → φ₂ (φ₁ i)
    ; φ⁻¹       = λ k → φ⁻¹₁ (φ⁻¹₂ k)
    ; φ-left    = λ i → trans (cong φ⁻¹₁ (φ-left₂ (φ₁ i))) (φ-left₁ i)
    ; φ-rght    = λ k → trans (cong φ₂ (φ-rght₁ (φ⁻¹₂ k))) (φ-rght₂ k)
    ; ψ         = λ e → ψ₂ (ψ₁ e)
    ; ψ⁻¹       = λ k → ψ⁻¹₁ (ψ⁻¹₂ k)
    ; ψ-left    = λ e → trans (cong ψ⁻¹₁ (ψ-left₂ (ψ₁ e))) (ψ-left₁ e)
    ; ψ-rght    = λ k → trans (cong ψ₂ (ψ-rght₁ (ψ⁻¹₂ k))) (ψ-rght₂ k)
    ; φ-lab     = λ i → trans (I₂.φ-lab (φ₁ i)) (I₁.φ-lab i)
    ; ψ-ein     = λ e → ein-trans e
    ; ψ-eout    = λ e → eout-trans e
    ; φ-dom     = dom-trans
    ; φ-cod     = cod-trans
    ; atom-ein  = λ e → atom-ein-trans e
    ; atom-eout = λ e → atom-eout-trans e
    ; ψ-elab    = elab-trans
    }
    where
      module I₁ = _≅ᴴ_ iso₁
      module I₂ = _≅ᴴ_ iso₂
      module G = Hypergraph G
      module H = Hypergraph H
      module K = Hypergraph K

      φ₁      = I₁.φ      ; φ⁻¹₁    = I₁.φ⁻¹
      φ-left₁ = I₁.φ-left ; φ-rght₁ = I₁.φ-rght
      ψ₁      = I₁.ψ      ; ψ⁻¹₁    = I₁.ψ⁻¹
      ψ-left₁ = I₁.ψ-left ; ψ-rght₁ = I₁.ψ-rght

      φ₂      = I₂.φ      ; φ⁻¹₂    = I₂.φ⁻¹
      φ-left₂ = I₂.φ-left ; φ-rght₂ = I₂.φ-rght
      ψ₂      = I₂.ψ      ; ψ⁻¹₂    = I₂.ψ⁻¹
      ψ-left₂ = I₂.ψ-left ; ψ-rght₂ = I₂.ψ-rght

      ein-trans : ∀ e → K.ein (ψ₂ (ψ₁ e)) ≡ map (λ i → φ₂ (φ₁ i)) (G.ein e)
      ein-trans e =
        trans (I₂.ψ-ein (ψ₁ e))
        (trans (cong (map φ₂) (I₁.ψ-ein e))
               (sym (map-∘ (G.ein e))))

      eout-trans : ∀ e → K.eout (ψ₂ (ψ₁ e)) ≡ map (λ i → φ₂ (φ₁ i)) (G.eout e)
      eout-trans e =
        trans (I₂.ψ-eout (ψ₁ e))
        (trans (cong (map φ₂) (I₁.ψ-eout e))
               (sym (map-∘ (G.eout e))))

      dom-trans : K.dom ≡ map (λ i → φ₂ (φ₁ i)) G.dom
      dom-trans = trans I₂.φ-dom
                  (trans (cong (map φ₂) I₁.φ-dom)
                         (sym (map-∘ G.dom)))

      cod-trans : K.cod ≡ map (λ i → φ₂ (φ₁ i)) G.cod
      cod-trans = trans I₂.φ-cod
                  (trans (cong (map φ₂) I₁.φ-cod)
                         (sym (map-∘ G.cod)))

      atom-ein-trans : ∀ e →
        map K.vlab (K.ein (ψ₂ (ψ₁ e))) ≡ map G.vlab (G.ein e)
      atom-ein-trans e = trans (I₂.atom-ein (ψ₁ e)) (I₁.atom-ein e)

      atom-eout-trans : ∀ e →
        map K.vlab (K.eout (ψ₂ (ψ₁ e))) ≡ map G.vlab (G.eout e)
      atom-eout-trans e = trans (I₂.atom-eout (ψ₁ e)) (I₁.atom-eout e)

      elab-trans : ∀ e →
        subst₂ Gen (atom-ein-trans e) (atom-eout-trans e)
                   (K.elab (ψ₂ (ψ₁ e)))
        ≡ G.elab e
      elab-trans e =
        let
          step₂ : subst₂ Gen (I₂.atom-ein (ψ₁ e)) (I₂.atom-eout (ψ₁ e))
                             (K.elab (ψ₂ (ψ₁ e)))
                  ≡ H.elab (ψ₁ e)
          step₂ = I₂.ψ-elab (ψ₁ e)

          step₁ : subst₂ Gen (I₁.atom-ein e) (I₁.atom-eout e)
                             (H.elab (ψ₁ e))
                  ≡ G.elab e
          step₁ = I₁.ψ-elab e

          chained : subst₂ Gen (trans (I₂.atom-ein (ψ₁ e)) (I₁.atom-ein e))
                                (trans (I₂.atom-eout (ψ₁ e)) (I₁.atom-eout e))
                                (K.elab (ψ₂ (ψ₁ e)))
                    ≡ G.elab e
          chained = trans
            (sym (subst₂-trans (I₂.atom-ein (ψ₁ e)) (I₁.atom-ein e)
                               (I₂.atom-eout (ψ₁ e)) (I₁.atom-eout e)
                               (K.elab (ψ₂ (ψ₁ e)))))
            (trans (cong (subst₂ Gen (I₁.atom-ein e) (I₁.atom-eout e)) step₂)
                   step₁)
        in chained


--------------------------------------------------------------------------------
-- With the de-indexed `Hypergraph Gen`, the `subst₂`-on-boundary
-- compatibility lemmas the indexed version needed are now definitional
-- `refl` and no longer required.
