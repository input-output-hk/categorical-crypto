{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Hypergraph isomorphism (TensorRocq §3.2): two hypergraphs are isomorphic
-- when there is a bijection of vertices and a bijection of edges that
-- preserves labels, endpoints, and the ordered boundary.  Defines the
-- relation and proves it symmetric and transitive; the main theorem
-- (⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g) lives in `Soundness`.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Model.Iso where

open import Categories.APROP.Hypergraph.Model.Core

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Properties using (map-∘)
open import Data.List.Properties.Ext using (map-∘-id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst₂)
open import Relation.Binary.PropositionalEquality.Properties.Ext
  using (subst₂-sym-flip; subst₂-trans)

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

      -- any `map φ` equation read in the flipped direction, via
      -- `map φ⁻¹ (map φ xs) ≡ xs`.
      flip-map : ∀ {xs ys} → ys ≡ map φ xs → xs ≡ map φ⁻¹ ys
      flip-map {xs} p = trans (sym (map-∘-id φ-left xs)) (sym (cong (map φ⁻¹) p))

      ein-sym : ∀ e → G.ein (ψ⁻¹ e) ≡ map φ⁻¹ (K.ein e)
      ein-sym e = flip-map (trans (sym (cong K.ein (ψ-rght e))) (ψ-ein (ψ⁻¹ e)))

      eout-sym : ∀ e → G.eout (ψ⁻¹ e) ≡ map φ⁻¹ (K.eout e)
      eout-sym e = flip-map (trans (sym (cong K.eout (ψ-rght e))) (ψ-eout (ψ⁻¹ e)))

      dom-sym : G.dom ≡ map φ⁻¹ K.dom
      dom-sym = flip-map φ-dom

      cod-sym : G.cod ≡ map φ⁻¹ K.cod
      cod-sym = flip-map φ-cod

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
      elab-sym e = trans
        (sym (subst₂-trans (sym (atom-ein (ψ⁻¹ e)))
                           (cong (λ z → map K.vlab (K.ein  z)) (ψ-rght e))
                           (sym (atom-eout (ψ⁻¹ e)))
                           (cong (λ z → map K.vlab (K.eout z)) (ψ-rght e))
                           (G.elab (ψ⁻¹ e))))
        (trans (cong (subst₂ Gen _ _)
                     (subst₂-sym-flip (atom-ein (ψ⁻¹ e)) (atom-eout (ψ⁻¹ e))
                                      (ψ-elab (ψ⁻¹ e))))
               (sym (K-elab-cong (ψ-rght e))))

--------------------------------------------------------------------------------
-- Transitivity. Compose the two bijections.

module _ {X : Set} {Gen : List X → List X → Set} where

  trans-≅ᴴ : {G H K : Hypergraph Gen} → G ≅ᴴ H → H ≅ᴴ K → G ≅ᴴ K
  trans-≅ᴴ {G} {H} {K} iso₁ iso₂ = record
    { φ         = λ i → φ₂ (φ₁ i)
    ; φ⁻¹       = λ k → φ⁻¹₁ (φ⁻¹₂ k)
    ; φ-left    = λ i → trans (cong φ⁻¹₁ (I₂.φ-left (φ₁ i))) (I₁.φ-left i)
    ; φ-rght    = λ k → trans (cong φ₂ (I₁.φ-rght (φ⁻¹₂ k))) (I₂.φ-rght k)
    ; ψ         = λ e → ψ₂ (ψ₁ e)
    ; ψ⁻¹       = λ k → ψ⁻¹₁ (ψ⁻¹₂ k)
    ; ψ-left    = λ e → trans (cong ψ⁻¹₁ (I₂.ψ-left (ψ₁ e))) (I₁.ψ-left e)
    ; ψ-rght    = λ k → trans (cong ψ₂ (I₁.ψ-rght (ψ⁻¹₂ k))) (I₂.ψ-rght k)
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

      open I₁ using () renaming (φ to φ₁; φ⁻¹ to φ⁻¹₁; ψ to ψ₁; ψ⁻¹ to ψ⁻¹₁)
      open I₂ using () renaming (φ to φ₂; φ⁻¹ to φ⁻¹₂; ψ to ψ₂; ψ⁻¹ to ψ⁻¹₂)

      -- two `map`-legs (through `φ₂` then `φ₁`) fused into one `map (φ₂ ∘ φ₁)`.
      via₂ : ∀ {xs ys zs} → xs ≡ map φ₂ ys → ys ≡ map φ₁ zs
           → xs ≡ map (λ i → φ₂ (φ₁ i)) zs
      via₂ p q = trans p (trans (cong (map φ₂) q) (sym (map-∘ _)))

      ein-trans : ∀ e → K.ein (ψ₂ (ψ₁ e)) ≡ map (λ i → φ₂ (φ₁ i)) (G.ein e)
      ein-trans e = via₂ (I₂.ψ-ein (ψ₁ e)) (I₁.ψ-ein e)

      eout-trans : ∀ e → K.eout (ψ₂ (ψ₁ e)) ≡ map (λ i → φ₂ (φ₁ i)) (G.eout e)
      eout-trans e = via₂ (I₂.ψ-eout (ψ₁ e)) (I₁.ψ-eout e)

      dom-trans : K.dom ≡ map (λ i → φ₂ (φ₁ i)) G.dom
      dom-trans = via₂ I₂.φ-dom I₁.φ-dom

      cod-trans : K.cod ≡ map (λ i → φ₂ (φ₁ i)) G.cod
      cod-trans = via₂ I₂.φ-cod I₁.φ-cod

      atom-ein-trans : ∀ e → map K.vlab (K.ein (ψ₂ (ψ₁ e))) ≡ map G.vlab (G.ein e)
      atom-ein-trans e = trans (I₂.atom-ein (ψ₁ e)) (I₁.atom-ein e)

      atom-eout-trans : ∀ e →
        map K.vlab (K.eout (ψ₂ (ψ₁ e))) ≡ map G.vlab (G.eout e)
      atom-eout-trans e = trans (I₂.atom-eout (ψ₁ e)) (I₁.atom-eout e)

      elab-trans : ∀ e →
        subst₂ Gen (atom-ein-trans e) (atom-eout-trans e)
                   (K.elab (ψ₂ (ψ₁ e)))
        ≡ G.elab e
      elab-trans e = trans
        (sym (subst₂-trans (I₂.atom-ein  (ψ₁ e)) (I₁.atom-ein  e)
                           (I₂.atom-eout (ψ₁ e)) (I₁.atom-eout e)
                           (K.elab (ψ₂ (ψ₁ e)))))
        (trans (cong (subst₂ Gen (I₁.atom-ein e) (I₁.atom-eout e))
                     (I₂.ψ-elab (ψ₁ e)))
               (I₁.ψ-elab e))
