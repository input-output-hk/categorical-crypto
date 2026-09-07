{-# OPTIONS --safe #-}

-- ============================================================================
-- `_⊗₁_` is a functor for the trace composition `_∘_`:
--
--     (g ∘ f) ⊗₁ (k ∘ h)  ≅ᴹ  (g ⊗₁ k) ∘ (f ⊗₁ h)
--
-- Both sides normalise, in the algebra of `Machine.Reindex`, to
-- `Reindex (Trc (Reindex (Pair (Pair f g) (Pair h k)) _ _)) _ _` — the same
-- four machines, the same trace — and differ only in how the messages are
-- routed.  That difference is a pointwise equation between two composites of
-- channel permutations, closed by `refl`.
-- ============================================================================

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults
open import CategoricalCrypto.Machine.Reindex

module CategoricalCrypto.Machine.Monoidal.Interchange where

open _≅ᴹ_

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ ∘κᵢ

  -- The routing the left-hand side produces.
  Aᴸ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.inType (((A₁ ⊗₀ A₂) ⊗₀ (B₁ ⊗₀ B₂)) ⊗ᵀ ((C₁ ⊗₀ C₂) ⊗₀ (B₁ ⊗₀ B₂)))
     → Channel.inType (((A₁ ⊗₀ B₁ ᵀ) ⊗₀ (B₁ ⊗₀ C₁ ᵀ)) ⊗₀ ((A₂ ⊗₀ B₂ ᵀ) ⊗₀ (B₂ ⊗₀ C₂ ᵀ)))
  Aᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i =
    ⊎ᵢ {A₁ ⊗₀ B₁ ᵀ} {(B₁ ⊗₀ C₁ ᵀ) ᵀ} {A₂ ⊗₀ B₂ ᵀ} {(B₂ ⊗₀ C₂ ᵀ) ᵀ}
       {A₁ ⊗₀ B₁} {C₁ ⊗₀ B₁} {A₂ ⊗₀ B₂} {C₂ ⊗₀ B₂}
       (∘κᵢ {A₁} {B₁} {C₁}) (∘κᵢ {A₂} {B₂} {C₂})
       (πᵢ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂} i)

  Bᴸ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.outType (((A₁ ⊗₀ A₂) ⊗₀ (B₁ ⊗₀ B₂)) ⊗ᵀ ((C₁ ⊗₀ C₂) ⊗₀ (B₁ ⊗₀ B₂)))
     → Channel.outType (((A₁ ⊗₀ B₁ ᵀ) ⊗₀ (B₁ ⊗₀ C₁ ᵀ)) ⊗₀ ((A₂ ⊗₀ B₂ ᵀ) ⊗₀ (B₂ ⊗₀ C₂ ᵀ)))
  Bᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o =
    ⊎ₒ {A₁ ⊗₀ B₁ ᵀ} {(B₁ ⊗₀ C₁ ᵀ) ᵀ} {A₂ ⊗₀ B₂ ᵀ} {(B₂ ⊗₀ C₂ ᵀ) ᵀ}
       {A₁ ⊗₀ B₁} {C₁ ⊗₀ B₁} {A₂ ⊗₀ B₂} {C₂ ⊗₀ B₂}
       (∘κₒ {A₁} {B₁} {C₁}) (∘κₒ {A₂} {B₂} {C₂})
       (πₒ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂} o)

  -- The routing the right-hand side produces.
  Nᵢ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.inType (((A₁ ⊗₀ A₂) ⊗₀ (B₁ ⊗₀ B₂)) ⊗ᵀ ((C₁ ⊗₀ C₂) ⊗₀ (B₁ ⊗₀ B₂)))
     → Channel.inType (((A₁ ⊗₀ B₁ ᵀ) ⊗₀ (A₂ ⊗₀ B₂ ᵀ)) ⊗₀ ((B₁ ⊗₀ C₁ ᵀ) ⊗₀ (B₂ ⊗₀ C₂ ᵀ)))
  Nᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i =
    ⊎ᵢ {A₁ ⊗₀ B₁ ᵀ} {(A₂ ⊗₀ B₂ ᵀ) ᵀ} {B₁ ⊗₀ C₁ ᵀ} {(B₂ ⊗₀ C₂ ᵀ) ᵀ}
       {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂}
       (app (⊗σ {A₁} {B₁} {A₂} {B₂} {In})) (app (⊗σ {B₁} {C₁} {B₂} {C₂} {In}))
       (∘κᵢ {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂} i)

  Nₒ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.outType (((A₁ ⊗₀ A₂) ⊗₀ (B₁ ⊗₀ B₂)) ⊗ᵀ ((C₁ ⊗₀ C₂) ⊗₀ (B₁ ⊗₀ B₂)))
     → Channel.outType (((A₁ ⊗₀ B₁ ᵀ) ⊗₀ (A₂ ⊗₀ B₂ ᵀ)) ⊗₀ ((B₁ ⊗₀ C₁ ᵀ) ⊗₀ (B₂ ⊗₀ C₂ ᵀ)))
  Nₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o =
    ⊎ₒ {A₁ ⊗₀ B₁ ᵀ} {(A₂ ⊗₀ B₂ ᵀ) ᵀ} {B₁ ⊗₀ C₁ ᵀ} {(B₂ ⊗₀ C₂ ᵀ) ᵀ}
       {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂}
       (app (⊗σ {A₁} {B₁} {A₂} {B₂} {Out})) (app (⊗σ {B₁} {C₁} {B₂} {C₂} {Out}))
       (∘κₒ {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂} o)

  Aᴿ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.inType (((A₁ ⊗₀ A₂) ⊗₀ (B₁ ⊗₀ B₂)) ⊗ᵀ ((C₁ ⊗₀ C₂) ⊗₀ (B₁ ⊗₀ B₂)))
     → Channel.inType (((A₁ ⊗₀ B₁ ᵀ) ⊗₀ (B₁ ⊗₀ C₁ ᵀ)) ⊗₀ ((A₂ ⊗₀ B₂ ᵀ) ⊗₀ (B₂ ⊗₀ C₂ ᵀ)))
  Aᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i =
    mid4ᵢ {A₁} {B₁} {A₂} {B₂} {B₁} {C₁} {B₂} {C₂} (Nᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i)

  Bᴿ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.outType (((A₁ ⊗₀ A₂) ⊗₀ (B₁ ⊗₀ B₂)) ⊗ᵀ ((C₁ ⊗₀ C₂) ⊗₀ (B₁ ⊗₀ B₂)))
     → Channel.outType (((A₁ ⊗₀ B₁ ᵀ) ⊗₀ (B₁ ⊗₀ C₁ ᵀ)) ⊗₀ ((A₂ ⊗₀ B₂ ᵀ) ⊗₀ (B₂ ⊗₀ C₂ ᵀ)))
  Bᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o =
    mid4ₒ {A₁} {B₁} {A₂} {B₂} {B₁} {C₁} {B₂} {C₂} (Nₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o)

  -- The outer routing the left-hand side produces, in the two stages the
  -- normalisation actually produces them.
  Mᵢ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.inType ((A₁ ⊗₀ A₂) ⊗ᵀ (C₁ ⊗₀ C₂))
     → Channel.inType (((A₁ ⊗₀ B₁) ⊗ᵀ (C₁ ⊗₀ B₁)) ⊗₀ ((A₂ ⊗₀ B₂) ⊗ᵀ (C₂ ⊗₀ B₂)))
  Mᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i =
    ⊎ᵢ {A₁ ⊗₀ B₁} {C₁ ⊗₀ B₁} {A₂ ⊗₀ B₂} {C₂ ⊗₀ B₂} {A₁} {C₁} {A₂} {C₂}
       (tιᵢ {A₁} {C₁} {B₁}) (tιᵢ {A₂} {C₂} {B₂})
       (app (⊗σ {A₁} {C₁} {A₂} {C₂} {In}) i)

  Mₒ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.outType ((A₁ ⊗₀ A₂) ⊗ᵀ (C₁ ⊗₀ C₂))
     → Channel.outType (((A₁ ⊗₀ B₁) ⊗ᵀ (C₁ ⊗₀ B₁)) ⊗₀ ((A₂ ⊗₀ B₂) ⊗ᵀ (C₂ ⊗₀ B₂)))
  Mₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o =
    ⊎ₒ {A₁ ⊗₀ B₁} {C₁ ⊗₀ B₁} {A₂ ⊗₀ B₂} {C₂ ⊗₀ B₂} {A₁} {C₁} {A₂} {C₂}
       (tιₒ {A₁} {C₁} {B₁}) (tιₒ {A₂} {C₂} {B₂})
       (app (⊗σ {A₁} {C₁} {A₂} {C₂} {Out}) o)

  Lᵢ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.inType ((A₁ ⊗₀ A₂) ⊗ᵀ (C₁ ⊗₀ C₂))
     → Channel.inType (((A₁ ⊗₀ A₂) ⊗₀ (B₁ ⊗₀ B₂)) ⊗ᵀ ((C₁ ⊗₀ C₂) ⊗₀ (B₁ ⊗₀ B₂)))
  Lᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i =
    πᵢ⁻ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂} (Mᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i)

  Lₒ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
     → Channel.outType ((A₁ ⊗₀ A₂) ⊗ᵀ (C₁ ⊗₀ C₂))
     → Channel.outType (((A₁ ⊗₀ A₂) ⊗₀ (B₁ ⊗₀ B₂)) ⊗ᵀ ((C₁ ⊗₀ C₂) ⊗₀ (B₁ ⊗₀ B₂)))
  Lₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o =
    πₒ⁻ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂} (Mₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o)

  -- The two routings agree.  This is the whole message-level content of the
  -- interchange law: the same permutation, reached two ways.
  pt-A : ∀ {A₁ B₁ C₁ A₂ B₂ C₂} i
       → Aᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i ≡ Aᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i
  pt-A (inj₁ (inj₁ (inj₁ _))) = refl
  pt-A (inj₁ (inj₁ (inj₂ _))) = refl
  pt-A (inj₁ (inj₂ (inj₁ _))) = refl
  pt-A (inj₁ (inj₂ (inj₂ _))) = refl
  pt-A (inj₂ (inj₁ (inj₁ _))) = refl
  pt-A (inj₂ (inj₁ (inj₂ _))) = refl
  pt-A (inj₂ (inj₂ (inj₁ _))) = refl
  pt-A (inj₂ (inj₂ (inj₂ _))) = refl

  pt-B : ∀ {A₁ B₁ C₁ A₂ B₂ C₂} o
       → Bᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o ≡ Bᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o
  pt-B (inj₁ (inj₁ (inj₁ _))) = refl
  pt-B (inj₁ (inj₁ (inj₂ _))) = refl
  pt-B (inj₁ (inj₂ (inj₁ _))) = refl
  pt-B (inj₁ (inj₂ (inj₂ _))) = refl
  pt-B (inj₂ (inj₁ (inj₁ _))) = refl
  pt-B (inj₂ (inj₁ (inj₂ _))) = refl
  pt-B (inj₂ (inj₂ (inj₁ _))) = refl
  pt-B (inj₂ (inj₂ (inj₂ _))) = refl

  pt-L : ∀ {A₁ B₁ C₁ A₂ B₂ C₂} i
       → Lᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} i ≡ tιᵢ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂} i
  pt-L (inj₁ (inj₁ _)) = refl
  pt-L (inj₁ (inj₂ _)) = refl
  pt-L (inj₂ (inj₁ _)) = refl
  pt-L (inj₂ (inj₂ _)) = refl

  pt-Lₒ : ∀ {A₁ B₁ C₁ A₂ B₂ C₂} o
        → Lₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} o ≡ tιₒ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂} o
  pt-Lₒ (inj₁ (inj₁ _)) = refl
  pt-Lₒ (inj₁ (inj₂ _)) = refl
  pt-Lₒ (inj₂ (inj₁ _)) = refl
  pt-Lₒ (inj₂ (inj₂ _)) = refl

  -- The left-hand side, normalised.
  norm-L : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
           (f : Machine A₁ B₁) (g : Machine B₁ C₁) (h : Machine A₂ B₂) (k : Machine B₂ C₂)
         → ((g CC.∘ f) ⊗₁ (k CC.∘ h))
           ≅ᴹ Reindex (Trc (Reindex (Pair (Pair f g) (Pair h k)) (Aᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂})))
                      (Lᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Lₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂})
  norm-L {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} f g h k =
    ≅ᴹ-trans (Reindex-resp-≅ᴹ (app (⊗σ {A₁} {C₁} {A₂} {C₂} {In})) (app (⊗σ {A₁} {C₁} {A₂} {C₂} {Out}))
                (Pair-resp-≅ᴹ (∘-Reindex f g) (∘-Reindex h k)))
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (app (⊗σ {A₁} {C₁} {A₂} {C₂} {In})) (app (⊗σ {A₁} {C₁} {A₂} {C₂} {Out}))
                (Pair-Reindex (Trc (Reindex (Pair f g) (∘κᵢ {A₁} {B₁} {C₁}) (∘κₒ {A₁} {B₁} {C₁}))) (Trc (Reindex (Pair h k) (∘κᵢ {A₂} {B₂} {C₂}) (∘κₒ {A₂} {B₂} {C₂})))
                   (tιᵢ {A₁} {C₁} {B₁}) (tιₒ {A₁} {C₁} {B₁})
                   (tιᵢ {A₂} {C₂} {B₂}) (tιₒ {A₂} {C₂} {B₂})))
    (≅ᴹ-trans (Reindex-fuse (Pair (Trc (Reindex (Pair f g) (∘κᵢ {A₁} {B₁} {C₁}) (∘κₒ {A₁} {B₁} {C₁}))) (Trc (Reindex (Pair h k) (∘κᵢ {A₂} {B₂} {C₂}) (∘κₒ {A₂} {B₂} {C₂}))))
                 (⊎ᵢ {A₁ ⊗₀ B₁} {C₁ ⊗₀ B₁} {A₂ ⊗₀ B₂} {C₂ ⊗₀ B₂} {A₁} {C₁} {A₂} {C₂}
            (tιᵢ {A₁} {C₁} {B₁}) (tιᵢ {A₂} {C₂} {B₂})) (⊎ₒ {A₁ ⊗₀ B₁} {C₁ ⊗₀ B₁} {A₂ ⊗₀ B₂} {C₂ ⊗₀ B₂} {A₁} {C₁} {A₂} {C₂}
            (tιₒ {A₁} {C₁} {B₁}) (tιₒ {A₂} {C₂} {B₂})) (app (⊗σ {A₁} {C₁} {A₂} {C₂} {In})) (app (⊗σ {A₁} {C₁} {A₂} {C₂} {Out})))
    (≅ᴹ-trans (Reindex-resp-≅ᴹ (Mᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Mₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Trc-Pair (Reindex (Pair f g) (∘κᵢ {A₁} {B₁} {C₁}) (∘κₒ {A₁} {B₁} {C₁})) (Reindex (Pair h k) (∘κᵢ {A₂} {B₂} {C₂}) (∘κₒ {A₂} {B₂} {C₂}))))
    (≅ᴹ-trans (Reindex-fuse (Trc (Reindex (Pair (Reindex (Pair f g) (∘κᵢ {A₁} {B₁} {C₁}) (∘κₒ {A₁} {B₁} {C₁})) (Reindex (Pair h k) (∘κᵢ {A₂} {B₂} {C₂}) (∘κₒ {A₂} {B₂} {C₂}))) (πᵢ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂}) (πₒ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂})))
                 (πᵢ⁻ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂}) (πₒ⁻ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂}) (Mᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Mₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}))
              (Reindex-resp-≅ᴹ (Lᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Lₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Trc-resp-≅ᴹ inner-L))))))
    where
    inner-L : Reindex (Pair (Reindex (Pair f g) (∘κᵢ {A₁} {B₁} {C₁}) (∘κₒ {A₁} {B₁} {C₁})) (Reindex (Pair h k) (∘κᵢ {A₂} {B₂} {C₂}) (∘κₒ {A₂} {B₂} {C₂}))) (πᵢ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂}) (πₒ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂})
              ≅ᴹ Reindex (Pair (Pair f g) (Pair h k)) (Aᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂})
    inner-L =
      ≅ᴹ-trans (Reindex-resp-≅ᴹ (πᵢ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂}) (πₒ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂})
                  (Pair-Reindex (Pair f g) (Pair h k)
                     (∘κᵢ {A₁} {B₁} {C₁}) (∘κₒ {A₁} {B₁} {C₁})
                     (∘κᵢ {A₂} {B₂} {C₂}) (∘κₒ {A₂} {B₂} {C₂})))
                (Reindex-fuse (Pair (Pair f g) (Pair h k)) (⊎ᵢ {A₁ ⊗₀ B₁ ᵀ} {(B₁ ⊗₀ C₁ ᵀ) ᵀ} {A₂ ⊗₀ B₂ ᵀ} {(B₂ ⊗₀ C₂ ᵀ) ᵀ}
            {A₁ ⊗₀ B₁} {C₁ ⊗₀ B₁} {A₂ ⊗₀ B₂} {C₂ ⊗₀ B₂}
            (∘κᵢ {A₁} {B₁} {C₁}) (∘κᵢ {A₂} {B₂} {C₂})) (⊎ₒ {A₁ ⊗₀ B₁ ᵀ} {(B₁ ⊗₀ C₁ ᵀ) ᵀ} {A₂ ⊗₀ B₂ ᵀ} {(B₂ ⊗₀ C₂ ᵀ) ᵀ}
            {A₁ ⊗₀ B₁} {C₁ ⊗₀ B₁} {A₂ ⊗₀ B₂} {C₂ ⊗₀ B₂}
            (∘κₒ {A₁} {B₁} {C₁}) (∘κₒ {A₂} {B₂} {C₂})) (πᵢ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂}) (πₒ {A₁} {C₁} {B₁} {A₂} {C₂} {B₂}))

  -- The right-hand side, normalised.
  norm-R : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
           (f : Machine A₁ B₁) (g : Machine B₁ C₁) (h : Machine A₂ B₂) (k : Machine B₂ C₂)
         → ((g ⊗₁ k) CC.∘ (f ⊗₁ h))
           ≅ᴹ Reindex (Trc (Reindex (Pair (Pair f g) (Pair h k)) (Aᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}))) (tιᵢ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂}) (tιₒ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂})
  norm-R {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} f g h k =
    ≅ᴹ-trans (∘-Reindex (f ⊗₁ h) (g ⊗₁ k))
             (Reindex-resp-≅ᴹ (tιᵢ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂}) (tιₒ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂}) (Trc-resp-≅ᴹ inner-R))
    where
    inner-R : Reindex (Pair (f ⊗₁ h) (g ⊗₁ k)) (∘κᵢ {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂}) (∘κₒ {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂})
              ≅ᴹ Reindex (Pair (Pair f g) (Pair h k)) (Aᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂})
    inner-R =
      ≅ᴹ-trans (Reindex-resp-≅ᴹ (∘κᵢ {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂}) (∘κₒ {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂})
                  (Pair-Reindex (Pair f h) (Pair g k)
                     (app (⊗σ {A₁} {B₁} {A₂} {B₂} {In}))
                     (app (⊗σ {A₁} {B₁} {A₂} {B₂} {Out}))
                     (app (⊗σ {B₁} {C₁} {B₂} {C₂} {In}))
                     (app (⊗σ {B₁} {C₁} {B₂} {C₂} {Out}))))
      (≅ᴹ-trans (Reindex-fuse (Pair (Pair f h) (Pair g k)) (⊎ᵢ {A₁ ⊗₀ B₁ ᵀ} {(A₂ ⊗₀ B₂ ᵀ) ᵀ} {B₁ ⊗₀ C₁ ᵀ} {(B₂ ⊗₀ C₂ ᵀ) ᵀ}
            {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂}
            (app (⊗σ {A₁} {B₁} {A₂} {B₂} {In})) (app (⊗σ {B₁} {C₁} {B₂} {C₂} {In}))) (⊎ₒ {A₁ ⊗₀ B₁ ᵀ} {(A₂ ⊗₀ B₂ ᵀ) ᵀ} {B₁ ⊗₀ C₁ ᵀ} {(B₂ ⊗₀ C₂ ᵀ) ᵀ}
            {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂}
            (app (⊗σ {A₁} {B₁} {A₂} {B₂} {Out})) (app (⊗σ {B₁} {C₁} {B₂} {C₂} {Out}))) (∘κᵢ {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂}) (∘κₒ {A₁ ⊗₀ A₂} {B₁ ⊗₀ B₂} {C₁ ⊗₀ C₂}))
      (≅ᴹ-trans (Reindex-resp-≅ᴹ (Nᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Nₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Pair-mid4 f h g k))
                (Reindex-fuse (Pair (Pair f g) (Pair h k)) (mid4ᵢ {A₁} {B₁} {A₂} {B₂} {B₁} {C₁} {B₂} {C₂}) (mid4ₒ {A₁} {B₁} {A₂} {B₂} {B₁} {C₁} {B₂} {C₂}) (Nᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Nₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}))))

  -- ══════════════════════════════════════════════════════════════════════
  -- `_⊗₁_` is a functor for the trace composition `_∘_`.
  -- ══════════════════════════════════════════════════════════════════════

  ⊗₁-interchange : ∀ {A₁ B₁ C₁ A₂ B₂ C₂}
                   (f : Machine A₁ B₁) (g : Machine B₁ C₁)
                   (h : Machine A₂ B₂) (k : Machine B₂ C₂)
                 → ((g CC.∘ f) ⊗₁ (k CC.∘ h)) ≅ᴹ ((g ⊗₁ k) CC.∘ (f ⊗₁ h))
  ⊗₁-interchange {A₁} {B₁} {C₁} {A₂} {B₂} {C₂} f g h k =
    ≅ᴹ-trans (norm-L f g h k) (≅ᴹ-trans middle (≅ᴹ-sym (norm-R f g h k)))
    where
    middle : Reindex (Trc (Reindex (Pair (Pair f g) (Pair h k)) (Aᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}))) (Lᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Lₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂})
             ≅ᴹ Reindex (Trc (Reindex (Pair (Pair f g) (Pair h k)) (Aᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}))) (tιᵢ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂}) (tιₒ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂})
    middle =
      ≅ᴹ-trans (Reindex-resp-≅ᴹ (Lᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Lₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂})
                  (Trc-resp-≅ᴹ (Reindex-cong (Pair (Pair f g) (Pair h k)) (Aᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Aᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴸ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂})
                                             pt-A pt-B)))
               (Reindex-cong (Trc (Reindex (Pair (Pair f g) (Pair h k)) (Aᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (Bᴿ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂})))
                             (Lᵢ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (tιᵢ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂}) (Lₒ {A₁} {B₁} {C₁} {A₂} {B₂} {C₂}) (tιₒ {A₁ ⊗₀ A₂} {C₁ ⊗₀ C₂} {B₁ ⊗₀ B₂}) pt-L pt-Lₒ)
