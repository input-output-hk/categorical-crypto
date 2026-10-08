{-# OPTIONS --safe --without-K #-}

-- Yang–Baxter coherence from the two hexagons and braiding naturality.

open import Categories.FreeStrictSMC
open import Data.List using (List; []; _∷_)
open import Relation.Binary using (DecidableEquality)

module Categories.FreeStrictSMC.Perm.Braid
  (X : Set) (_≟X_ : DecidableEquality X)
  where

module Generic (mor : List X → List X → Set) where

  open Build X _≟X_ mor

  BraidAt : (a b c : X) → List X → Set
  BraidAt a b c L =
    ((σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {a ∷ L})
        ∘ˢ (idˢ {b ∷ []} ⊗ˢ (σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {L})))
          ∘ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {c ∷ L})
    ≈ˢ
    ((idˢ {c ∷ []} ⊗ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {L}))
        ∘ˢ (σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {b ∷ L}))
          ∘ˢ (idˢ {a ∷ []} ⊗ˢ (σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {L}))

  -- Singleton associators reduce to `refl`, so the hexagon casts vanish.
  private
    braid₀
      : ∀ (a b c : X)
      → (((σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {a ∷ []})
            ∘ˢ (idˢ {b ∷ []} ⊗ˢ σˢ (a ∷ []) (c ∷ [])))
            ∘ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {c ∷ []}))
        ≈ˢ
        (((idˢ {c ∷ []} ⊗ˢ σˢ (a ∷ []) (b ∷ []))
            ∘ˢ (σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {b ∷ []}))
            ∘ˢ (idˢ {a ∷ []} ⊗ˢ σˢ (b ∷ []) (c ∷ [])))
    braid₀ a b c =
      ≈-sym
        (≈-trans assocˢ
        (≈-trans (∘-resp ≈-refl (≈-sym (σ-hexˢ (a ∷ []) (b ∷ []) (c ∷ []))))
        (≈-trans (≈-sym σ-natˢ)
          (∘-resp (σ-hexˢ (b ∷ []) (a ∷ []) (c ∷ [])) ≈-refl))))

  strict-braid : ∀ (a b c : X) (L : List X) → BraidAt a b c L
  strict-braid a b c L =
    ≈-trans (≈-sym expand-L)
      (≈-trans (⊗-resp (braid₀ a b c) ≈-refl) expand-R)
    where
      A = a ∷ [] ; B = b ∷ [] ; C = c ∷ []

      ⊗distₗ
        : ∀ {xs ys zs} (p : HomS ys zs) (q : HomS xs ys)
        → (p ∘ˢ q) ⊗ˢ idˢ {L} ≈ˢ (p ⊗ˢ idˢ {L}) ∘ˢ (q ⊗ˢ idˢ {L})
      ⊗distₗ p q = ≈-sym (≈-trans interchangeˢ (⊗-resp ≈-refl idˡ))

      f1 : (σˢ B C ⊗ˢ idˢ {A}) ⊗ˢ idˢ {L} ≈ˢ σˢ B C ⊗ˢ idˢ {a ∷ L}
      f1 = box-suffix-ˢ (σˢ B C) A L

      f2 : (idˢ {B} ⊗ˢ σˢ A C) ⊗ˢ idˢ {L}
             ≈ˢ idˢ {B} ⊗ˢ (σˢ A C ⊗ˢ idˢ {L})
      f2 = ⊗-assocˢ (idˢ {B}) (σˢ A C) (idˢ {L})

      f3 : (σˢ A B ⊗ˢ idˢ {C}) ⊗ˢ idˢ {L} ≈ˢ σˢ A B ⊗ˢ idˢ {c ∷ L}
      f3 = box-suffix-ˢ (σˢ A B) C L

      expand-L
        : (((σˢ B C ⊗ˢ idˢ {A}) ∘ˢ (idˢ {B} ⊗ˢ σˢ A C))
             ∘ˢ (σˢ A B ⊗ˢ idˢ {C})) ⊗ˢ idˢ {L}
          ≈ˢ
          ((σˢ B C ⊗ˢ idˢ {a ∷ L})
              ∘ˢ (idˢ {B} ⊗ˢ (σˢ A C ⊗ˢ idˢ {L})))
            ∘ˢ (σˢ A B ⊗ˢ idˢ {c ∷ L})
      expand-L =
        ≈-trans (⊗distₗ _ (σˢ A B ⊗ˢ idˢ {C}))
          (∘-resp (≈-trans (⊗distₗ (σˢ B C ⊗ˢ idˢ {A}) (idˢ {B} ⊗ˢ σˢ A C))
                           (∘-resp f1 f2))
                  f3)

      g1 : (idˢ {C} ⊗ˢ σˢ A B) ⊗ˢ idˢ {L}
             ≈ˢ idˢ {C} ⊗ˢ (σˢ A B ⊗ˢ idˢ {L})
      g1 = ⊗-assocˢ (idˢ {C}) (σˢ A B) (idˢ {L})

      g2 : (σˢ A C ⊗ˢ idˢ {B}) ⊗ˢ idˢ {L} ≈ˢ σˢ A C ⊗ˢ idˢ {b ∷ L}
      g2 = box-suffix-ˢ (σˢ A C) B L

      g3 : (idˢ {A} ⊗ˢ σˢ B C) ⊗ˢ idˢ {L}
             ≈ˢ idˢ {A} ⊗ˢ (σˢ B C ⊗ˢ idˢ {L})
      g3 = ⊗-assocˢ (idˢ {A}) (σˢ B C) (idˢ {L})

      expand-R
        : (((idˢ {C} ⊗ˢ σˢ A B) ∘ˢ (σˢ A C ⊗ˢ idˢ {B}))
             ∘ˢ (idˢ {A} ⊗ˢ σˢ B C)) ⊗ˢ idˢ {L}
          ≈ˢ
          ((idˢ {C} ⊗ˢ (σˢ A B ⊗ˢ idˢ {L}))
              ∘ˢ (σˢ A C ⊗ˢ idˢ {b ∷ L}))
            ∘ˢ (idˢ {A} ⊗ˢ (σˢ B C ⊗ˢ idˢ {L}))
      expand-R =
        ≈-trans (⊗distₗ _ (idˢ {A} ⊗ˢ σˢ B C))
          (∘-resp (≈-trans (⊗distₗ (idˢ {C} ⊗ˢ σˢ A B) (σˢ A C ⊗ˢ idˢ {B}))
                           (∘-resp g1 g2))
                  g3)
