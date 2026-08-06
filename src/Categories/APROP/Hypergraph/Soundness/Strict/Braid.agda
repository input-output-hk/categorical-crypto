{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict Yang-Baxter braid `strict-braid` — the KEYSTONE residual of the
-- strictified soundness pipeline (`PermDischarge.Discharge.StrictBraid`).
--
-- The statement is GENERATOR-FREE, so it holds in every `FreeStrictSMC.Build`
-- instance.  We prove it DIRECTLY in `HomS` from the `Build` axioms, without
-- any detour through the non-strict free SMC:
--
--   * the σ-blocks are all SINGLETON swaps `σˢ [x] [y]`, so every associator
--     cast (`++-assoc` on singletons) is `refl` and vanishes definitionally;
--   * the braid `s₁s₂s₁ ≈ s₂s₁s₂` is the classical two-hexagon-plus-naturality
--     derivation — `σ-hexˢ` (split the compound swap), `σ-natˢ` (slide it past
--     the third strand), then `σ-hexˢ` again (split the other compound swap);
--   * the common right tail `M` is carried by `box-suffix-ˢ`/`⊗-assocˢ`
--     (both refl-cast at singleton frames) and an interchange distribution.
--
-- `PermDischarge.Discharge` opens `Build X _≟X_ (λ _ _ → V)`, so it instantiates
-- `Generic.strict-braid` at `mor := (λ _ _ → V)`.
--------------------------------------------------------------------------------

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Braid
  (X : Set) (_≟X_ : DecidableEquality X)
  where

open import Data.List using (List; []; _∷_)
open import Categories.FreeStrictSMC using (module Build)

--------------------------------------------------------------------------------
-- The generic part, over an arbitrary generator family.

module Generic (mor : List X → List X → Set) where

  open Build X _≟X_ mor

  ------------------------------------------------------------------------
  -- The braid statement as a predicate on the tail list.

  BraidAt : (a b c : X) → List X → Set
  BraidAt a b c L =
    ((σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {a ∷ L})
        ∘ˢ (idˢ {b ∷ []} ⊗ˢ (σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {L})))
          ∘ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {c ∷ L})
    ≈ˢ
    ((idˢ {c ∷ []} ⊗ˢ (σˢ (a ∷ []) (b ∷ []) ⊗ˢ idˢ {L}))
        ∘ˢ (σˢ (a ∷ []) (c ∷ []) ⊗ˢ idˢ {b ∷ L}))
          ∘ˢ (idˢ {a ∷ []} ⊗ˢ (σˢ (b ∷ []) (c ∷ []) ⊗ˢ idˢ {L}))

  ------------------------------------------------------------------------
  -- The tail-free braid on three SINGLETON strands `[a] [b] [c]`.
  --
  -- All the associator casts produced by `σ-hexˢ` here are `++-assoc` on
  -- singleton lists, which reduce to `refl`; so `castˢ refl refl` collapses
  -- definitionally and `σ-hexˢ [a] [b] [c]` reads as the plain equation
  --   σˢ ([a]++[b]) [c] ≈ˢ (σˢ [a] [c] ⊗ˢ idˢ) ∘ˢ (idˢ ⊗ˢ σˢ [b] [c]).

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

  ------------------------------------------------------------------------
  -- The keystone: the strict Yang-Baxter braid for every right tail `L`.
  -- Pull `idˢ {L}` out of every factor (`box-suffix-ˢ`/`⊗-assocˢ`, refl-cast
  -- at singleton frames), distribute the tail past the composition
  -- (interchange), and apply `braid₀`.
  --
  -- This is exactly `PermDischarge.Discharge.StrictBraid` once
  -- `mor := (λ _ _ → V)`.
  strict-braid : ∀ (a b c : X) (L : List X) → BraidAt a b c L
  strict-braid a b c L =
    ≈-trans (≈-sym expand-L)
      (≈-trans (⊗-resp (braid₀ a b c) ≈-refl) expand-R)
    where
      A = a ∷ [] ; B = b ∷ [] ; C = c ∷ []

      -- (p ∘ˢ q) ⊗ˢ idˢ {L} distributes over the composition.
      ⊗distₗ
        : ∀ {xs ys zs} (p : HomS ys zs) (q : HomS xs ys)
        → (p ∘ˢ q) ⊗ˢ idˢ {L} ≈ˢ (p ⊗ˢ idˢ {L}) ∘ˢ (q ⊗ˢ idˢ {L})
      ⊗distₗ p q = ≈-sym (≈-trans interchangeˢ (⊗-resp ≈-refl idˡ))

      -- LHS: each factor with `idˢ {L}` factored out equals the tailful factor.
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

      -- RHS: same, mirrored.
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
