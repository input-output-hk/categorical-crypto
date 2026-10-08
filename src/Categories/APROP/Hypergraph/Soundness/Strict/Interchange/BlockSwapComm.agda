{-# OPTIONS --safe --without-K #-}

-- Block-swap coherence for the σ decoder shape.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes sig
  using (module Scr)
open import Categories.Morphism.Reasoning SCat
open import Categories.Morphism.Reasoning.Ext SCat

open import Data.List.Properties

-- The right hexagon follows from the left hexagon by uniqueness of inverses.

σ-hexˢʳ
  : ∀ (a b c : List X)
  → σˢ a (b ++ c)
    ≈ˢ coe (sym (++-assoc b c a))
        ∘ˢ (((idˢ {b} ⊗ˢ σˢ a c)
              ∘ˢ coe (++-assoc b a c) ∘ˢ (σˢ a b ⊗ˢ idˢ {c}))
            ∘ˢ coe (sym (++-assoc a b c)))
σ-hexˢʳ a b c = inv-resp σ-σˢ cancel ≈-refl
  where
    P = ++-assoc a b c
    Q = ++-assoc b c a
    R = ++-assoc b a c

    X₁ = σˢ a b ⊗ˢ idˢ {c}
    X₂ = idˢ {b} ⊗ˢ σˢ a c
    W₁ = σˢ b a ⊗ˢ idˢ {c}
    W₂ = idˢ {b} ⊗ˢ σˢ c a

    L : HomS ((a ++ b) ++ c) (b ++ c ++ a)
    L = X₂ ∘ˢ coe R ∘ˢ X₁

    step-σʳ : W₂ ∘ˢ X₂ ≈ˢ idˢ
    step-σʳ = ≈-trans interchangeˢ (≈-trans (⊗-resp idˡ σ-σˢ) ⊗-id)

    step-σˡ : W₁ ∘ˢ X₁ ≈ˢ idˢ
    step-σˡ = ≈-trans interchangeˢ (≈-trans (⊗-resp σ-σˢ idˡ) ⊗-id)

    u-form : σˢ (b ++ c) a ≈ˢ coe P ∘ˢ (W₁ ∘ˢ ((coe (sym R) ∘ˢ W₂) ∘ˢ coe Q))
    u-form =
      ≈-trans (σ-hexˢ b c a)
      (≈-trans (coe-conj (sym Q) P (W₁ ∘ˢ castˢ refl (sym R) W₂))
      (∘-resp ≈-refl
        (pullʳ (∘-resp (≈-trans (coe-conj refl (sym R) W₂) (∘-resp ≈-refl idʳ))
                       (coe-uip (sym (sym Q)) Q)))))

    M-nest : L ∘ˢ coe (sym P) ≈ˢ X₂ ∘ˢ (coe R ∘ˢ (X₁ ∘ˢ coe (sym P)))
    M-nest = pullʳ assocˢ

    cancel : σˢ (b ++ c) a ∘ˢ (coe (sym Q) ∘ˢ (L ∘ˢ coe (sym P))) ≈ˢ idˢ
    cancel =
      ≈-trans (∘-resp u-form ≈-refl)
      (≈-trans (pullʳ assocˢ)
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (cancelˡ (coe-cancelʳ Q)))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (∘-resp ≈-refl M-nest))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (cancelˡ step-σʳ))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (cancelˡ (coe-cancel R))))
      (≈-trans (∘-resp ≈-refl (cancelˡ step-σˡ))
        (coe-cancelʳ P)))))))))

module _ (V : Set) (vlab : V → X) where

  open Scr V vlab
    using (bswap; permuteˢ-shift-sym-base; bswap-σ-base; BswapSig)
  open Restrict V vlab

  -- Singleton associators reduce as in `Braid.Generic`.
  hexᵛ
    : (v x : V) (R : List V)
    → σᵛ (v ∷ []) (x ∷ R)
      ≈ᵛ (idᵛ {x ∷ []} ⊗ᵛ σᵛ (v ∷ []) R) ∘ᵛ (σᵛ (v ∷ []) (x ∷ []) ⊗ᵛ idᵛ {R})
  hexᵛ v x R = viaˢ (σᵛ-≈̂ (v ∷ []) (x ∷ R)) hex' rhs
    where
      a b c : List X
      a = vlab v ∷ []
      b = vlab x ∷ []
      c = map vlab R

      hex' : σˢ a (b ++ c) ≈ˢ (idˢ {b} ⊗ˢ σˢ a c) ∘ˢ (σˢ a b ⊗ˢ idˢ {c})
      hex' =
        ≈-trans (σ-hexˢʳ a b c)
        (≈-trans (∘-resp (coe-id≈ (sym (++-assoc b c a))) ≈-refl)
        (≈-trans idˡ
        (≈-trans (∘-resp ≈-refl (coe-id≈ (sym (++-assoc a b c))))
        (≈-trans idʳ
          (∘-resp ≈-refl
            (≈-trans (∘-resp (coe-id≈ (++-assoc b a c)) ≈-refl) idˡ))))))

      rhs : (idᵛ {x ∷ []} ⊗ᵛ σᵛ (v ∷ []) R) ∘ᵛ (σᵛ (v ∷ []) (x ∷ []) ⊗ᵛ idᵛ {R})
            ≈̂ (idˢ {b} ⊗ˢ σˢ a c) ∘ˢ (σˢ a b ⊗ˢ idˢ {c})
      rhs = ∘-resp-≈̂ (⊗-resp-≈̂ ≈̂-refl (σᵛ-≈̂ (v ∷ []) R)) ≈̂-refl

  shift-symᵛ
    : (v : V) (R L : List V)
    → permuteᵛ (Perm.↭-sym (PermProp.shift v R L))
      ≈ᵛ castᵛ refl (++-assoc R (v ∷ []) L) (σᵛ (v ∷ []) R ⊗ᵛ idᵛ {L})
  shift-symᵛ v []      L = permuteˢ-shift-sym-base v L
  shift-symᵛ v (x ∷ R) L =
    viâ (∘-resp-≈̂ F1 F2)
        (≈̂-trans (≈ˢ⇒≈̂ interchangeᵛ)
                 (⊗-resp-≈̂ᵛ (≈ˢ⇒≈̂ (≈-sym (hexᵛ v x R))) (≈ˢ⇒≈̂ idˡ)))
        (castᵛ-≈̂ refl (++-assoc (x ∷ R) (v ∷ []) L)
          (σᵛ (v ∷ []) (x ∷ R) ⊗ᵛ idᵛ {L}))
    where
      F1 : idᵛ {x ∷ []} ⊗ᵛ permuteᵛ (Perm.↭-sym (PermProp.shift v R L))
           ≈̂ (idᵛ {x ∷ []} ⊗ᵛ σᵛ (v ∷ []) R) ⊗ᵛ idᵛ {L}
      F1 =
        ≈̂-trans
          (⊗-resp-≈̂ ≈̂-refl
            (≈̂-trans (≈ˢ⇒≈̂ (shift-symᵛ v R L))
                     (castᵛ-≈̂ refl (++-assoc R (v ∷ []) L)
                        (σᵛ (v ∷ []) R ⊗ᵛ idᵛ {L}))))
          (≈̂-sym (⊗-assoc-≈̂ᵛ (idᵛ {x ∷ []}) (σᵛ (v ∷ []) R) (idᵛ {L})))

      F2 : σᵛ (v ∷ []) (x ∷ []) ⊗ᵛ idᵛ {R ++ L}
           ≈̂ (σᵛ (v ∷ []) (x ∷ []) ⊗ᵛ idᵛ {R}) ⊗ᵛ idᵛ {L}
      F2 = ≈̂-sym (box-suffix-≈̂ᵛ (σᵛ (v ∷ []) (x ∷ [])) R L)

  block-swap-comm : BswapSig
  block-swap-comm []      R = bswap-σ-base R
  block-swap-comm (v ∷ L) R = ≈̂⇒≈ˢ (≈̂-trans lhs (≈̂-sym rhs))
    where
      CORE : HomV (v ∷ L ++ R) ((R ++ (v ∷ [])) ++ L)
      CORE = (σᵛ (v ∷ []) R ⊗ᵛ idᵛ {L}) ∘ᵛ (idᵛ {v ∷ []} ⊗ᵛ σᵛ L R)

      lhs : permuteᵛ (bswap (v ∷ L) R) ≈̂ CORE
      lhs =
        ∘-resp-≈̂
          (≈̂-trans (≈ˢ⇒≈̂ (shift-symᵛ v R L))
                   (castᵛ-≈̂ refl (++-assoc R (v ∷ []) L)
                      (σᵛ (v ∷ []) R ⊗ᵛ idᵛ {L})))
          (⊗-resp-≈̂ ≈̂-refl (≈ˢ⇒≈̂ (block-swap-comm L R)))

      rhs : σᵛ (v ∷ L) R ≈̂ CORE
      rhs =
        ≈̂-trans (≈ˢ⇒≈̂ (σ-hexᵛ (v ∷ []) L R))
                (castᵛ-≈̂ refl (++-assoc R (v ∷ []) L) CORE)

  swap-block
    : ∀ (L R Rl : List V)
    → permuteᵛ (PermProp.++⁺ʳ Rl (bswap L R)) ≈ᵛ σᵛ L R ⊗ᵛ idᵛ {Rl}
  swap-block L R Rl =
    ≈-trans (permuteᵛ-frame Rl (bswap L R))
            (⊗-respᵛ (block-swap-comm L R) ≈-refl)
