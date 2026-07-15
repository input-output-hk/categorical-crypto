{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Companion to `Faithfulness`.  Provides the single SMC-coherence fact
-- consumed downstream:
--
--   * `σ-block-self-inverse-direct` : the σ-block self-inverse identity
--     `((id ⊗ (id ⊗ g)) ∘ σ-block) ∘ ((id ⊗ (id ⊗ f)) ∘ σ-block) ≈ id`
--     given `g ∘ f ≈ id`.
--
-- It is proved constructively from two private auxiliary lemmas:
--   * `σ-block-involutive` : σ-block ∘ σ-block ≈ id.
--   * `σ-block-natural₃`   : σ-block commutes past `(id ⊗ (id ⊗ f))`.
--
-- FaithfulnessInductive imports only `σ-block-self-inverse-direct`.
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.FaithfulnessK
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d

open import Categories.PermuteCoherence.Faithfulness d
  using (α⇐-comm)

------------------------------------------------------------------------
-- Two auxiliary σ-block lemmas:
--   * σ-block-involutive : σ-block ∘ σ-block ≈ id.
--   * σ-block-natural₃   : σ-block ∘ (id ⊗ (id ⊗ f)) ≈ (id ⊗ (id ⊗ f)) ∘ σ-block.
--
-- `σ-block-self-inverse-direct` then pushes the inner `(id ⊗ (id ⊗ f))`
-- past `σ-block₂` (naturality), collapses the two σ-blocks (involutivity),
-- and finishes with `g ∘ f ≈ id`.

private
  σ-block-involutive
    : ∀ {A B C : ObjTerm}
    → (α⇒ {A = A} {B = B} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = B} {B = A} {C = C})
        ∘ (α⇒ {A = B} {B = A} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = A} {B = B} {C = C})
      ≈Term id
  σ-block-involutive =
    ≈-Term-trans assoc
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                    (∘-resp-≈ ≈-Term-refl
                      (≈-Term-trans (≈-Term-sym assoc)
                                    (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl))))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                    (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                                (≈-Term-trans (⊗-resp-≈ σ∘σ≈id idˡ)
                                              id⊗id≈id))
                              ≈-Term-refl))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ)
                   α⇒∘α⇐≈id))))))

  σ-block-natural₃
    : ∀ {A B C D : ObjTerm} {f : HomTerm C D}
    → (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
      ≈Term (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
  σ-block-natural₃ {A} {B} {C} {D} {f} =
    let lhs→common
          : (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
            ≈Term α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
        lhs→common =
          ≈-Term-trans assoc
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl α⇐-comm))
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
                         (∘-resp-≈ ≈-Term-refl
                           (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                                       (⊗-resp-≈
                                         (≈-Term-trans (∘-resp-≈ ≈-Term-refl id⊗id≈id) idʳ)
                                         idˡ))
                                     ≈-Term-refl)))))
        rhs→common
          : (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐)
            ≈Term α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
        rhs→common =
          ≈-Term-trans (≈-Term-sym assoc)
          (≈-Term-trans (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl)
          (≈-Term-trans assoc
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
                         (∘-resp-≈ ≈-Term-refl
                           (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                                       (⊗-resp-≈
                                         (≈-Term-trans (∘-resp-≈ id⊗id≈id ≈-Term-refl) idˡ)
                                         idʳ))
                                     ≈-Term-refl)))))
    in ≈-Term-trans lhs→common (≈-Term-sym rhs→common)

-- The constructive discharge.
σ-block-self-inverse-direct
  : ∀ {A B C D} (f : HomTerm C D) (g : HomTerm D C)
  → g ∘ f ≈Term id
  → ((id {A = A} ⊗₁ (id {A = B} ⊗₁ g)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
    ∘
    ((id {A = B} ⊗₁ (id {A = A} ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
    ≈Term id
σ-block-self-inverse-direct {A} {B} {C} {D} f g g∘f≈id =
  ≈-Term-trans assoc
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                  (∘-resp-≈ σ-block-natural₃ ≈-Term-refl))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
  (≈-Term-trans (≈-Term-sym assoc)
  (≈-Term-trans (∘-resp-≈
                  (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                    (⊗-resp-≈ idˡ
                      (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                        (⊗-resp-≈ idˡ g∘f≈id))))
                  σ-block-involutive)
  (≈-Term-trans idʳ
  (≈-Term-trans (⊗-resp-≈ ≈-Term-refl id⊗id≈id)
                 id⊗id≈id)))))))
