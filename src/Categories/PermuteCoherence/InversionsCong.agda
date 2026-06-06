{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Utility congruence lemmas for the inversion count `inv`.
--
--   * `inv-resp-≈` : `inv` respects pointwise (`≈-fb`) equality.
--   * `inv-id`     : the identity has no inversions.
--
-- Both are proved by induction on the size, closely mirroring
-- `Word.canonW-resp-≈` and `Word.canonW-id`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.InversionsCong where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin; toℕ) renaming (suc to fsuc)
open import Data.Fin.Patterns using (0F)
import Data.Fin.Permutation as P
open P using (remove)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; trans; sym; cong; cong₂)

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _∘-fb_; inv-fb; id-fb; _≈-fb_)
open import Categories.PermuteCoherence.Word
  using (rotate-fb; ∘-fb-cong)
open import Categories.PermuteCoherence.Inversions using (inv)
-- `residual-pw-cong` = `remove 0F` respects pointwise (`≈-fb`) equality.
open import Categories.PermuteCoherence.CanonicalProps using (residual-pw-cong)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The backward maps of pointwise-equal bijections agree.  (Same lemma
-- as `Word.≈ˡ`, kept local so this module stays self-contained.)

≈ˡ : {N M : ℕ} {b b′ : FinBij N M} → b ≈-fb b′ → ∀ j → b P.⟨$⟩ˡ j ≡ b′ P.⟨$⟩ˡ j
≈ˡ {b = b} {b′} eq j =
  trans (sym (P.inverseˡ b′ {b P.⟨$⟩ˡ j}))
        (cong (b′ P.⟨$⟩ˡ_) (trans (sym (eq (b P.⟨$⟩ˡ j))) (P.inverseʳ b {j})))

------------------------------------------------------------------------
-- (1) `inv` respects pointwise equality.
--
-- Mirrors `Word.canonW-resp-≈`: the head datum `b ⟨$⟩ˡ 0F` is determined
-- by `≈ˡ`, so the rotation contribution `toℕ (b ⟨$⟩ˡ 0F)` matches; the
-- residual is `≈-fb` (by `residual-pw-cong` + `∘-fb-cong`), so the
-- recursive `inv`s agree by the IH.  (`≈-fb` is non-injective in the
-- bijection, so every implicit bijection argument is pinned explicitly.)

opaque
  unfolding inv
  inv-resp-≈ : {n : ℕ} {b b′ : FinBij (suc n) (suc n)} → b ≈-fb b′ → inv b ≡ inv b′
  inv-resp-≈ {zero}              eq = refl
  inv-resp-≈ {suc n} {b} {b′} eq =
    cong₂ _+_
      (inv-resp-≈ {b = restb} {b′ = rest′} rest≈)
      (cong toℕ m≡)
    where
    m≡ : b P.⟨$⟩ˡ 0F ≡ b′ P.⟨$⟩ˡ 0F
    m≡ = ≈ˡ {b = b} {b′ = b′} eq 0F

    restb rest′ : FinBij (suc n) (suc n)
    restb = remove 0F (b  ∘-fb inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F)))
    rest′ = remove 0F (b′ ∘-fb inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F)))

    rest≈ : restb ≈-fb rest′
    rest≈ = residual-pw-cong (b  ∘-fb inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F)))
                             (b′ ∘-fb inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F)))
              (∘-fb-cong {g = b} {g′ = b′}
                         {f = inv-fb (rotate-fb (b  P.⟨$⟩ˡ 0F))}
                         {f′ = inv-fb (rotate-fb (b′ P.⟨$⟩ˡ 0F))}
                         eq (λ i → cong (λ z → inv-fb (rotate-fb z) P.⟨$⟩ʳ i) m≡))

------------------------------------------------------------------------
-- (2) The identity has no inversions.
--
-- `id-fb ⟨$⟩ˡ 0F ≡ 0F`, so the rotation contribution `toℕ … ` is `0`;
-- the residual `remove 0F (id-fb ∘-fb inv-fb (rotate-fb 0F))` is
-- pointwise the identity, so `inv-resp-≈` collapses it to `inv id-fb`,
-- which is `0` by the IH.

opaque
  unfolding inv
  inv-id : {n : ℕ} → inv (id-fb {suc n}) ≡ 0
  inv-id {zero}  = refl
  inv-id {suc n} =
    -- inv (id-fb {suc (suc n)})
    --   = inv (remove 0F (id-fb ∘-fb inv-fb (rotate-fb 0F))) + toℕ (id-fb ⟨$⟩ˡ 0F)
    --   = inv restᵢ + 0                                       [id ⟨$⟩ˡ 0F = 0F, toℕ 0F = 0]
    --   = inv (id-fb {suc n}) + 0                             [inv-resp-≈ rest≈]
    --   = 0 + 0 = 0                                           [IH]
    trans (cong (_+ toℕ {suc (suc n)} 0F)
                (trans (inv-resp-≈ {b = restᵢ} {b′ = id-fb {suc n}} rest≈)
                       (inv-id {n})))
          refl
    where
    -- `id-fb ⟨$⟩ˡ 0F` is `0F` definitionally (`rotate-fb 0F = id-fb`).
    restᵢ : FinBij (suc n) (suc n)
    restᵢ = remove 0F (id-fb {suc (suc n)} ∘-fb inv-fb (rotate-fb (id-fb {suc (suc n)} P.⟨$⟩ˡ 0F)))

    -- The residual of the identity (after the trivial rotation) is
    -- pointwise the identity.  `id-fb ∘-fb inv-fb (rotate-fb 0F) ≈ id-fb`
    -- pointwise, and `remove 0F` of a pointwise-identity is the identity
    -- (here directly: every component is `refl`).
    rest≈ : restᵢ ≈-fb id-fb {suc n}
    rest≈ = residual-pw-cong (id-fb {suc (suc n)} ∘-fb inv-fb (rotate-fb (id-fb {suc (suc n)} P.⟨$⟩ˡ 0F)))
                             (id-fb {suc (suc n)})
                             (λ _ → refl)
