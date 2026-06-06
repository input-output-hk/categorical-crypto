{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Shared base for the exchange-condition endgame toward `insert`.
--
-- Lifts L1 (the inversion dichotomy, proved for `invS` in
-- `InversionsDichotomy` and transferred to `inv` via `invS≡inv`) to the
-- clean word-level facts the exchange/Matsumoto development needs:
--   * `Reduced w`     — `w` is a reduced word (length = inversions);
--   * `descent i b`   — `i` is a left descent of `b` (inv drops);
--   * `inv-di`        — every generator is an ascent or a descent;
--   * `canonW-reduced`— `canonW b` is reduced.
------------------------------------------------------------------------

module Categories.PermuteCoherence.ExchangeBase where

open import Data.Nat.Base using (ℕ; suc; _<_)
open import Data.Nat.Properties using (<-cmp; 1+n≢n)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Data.Fin.Base using (Fin; toℕ) renaming (suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List.Base using (length)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)
import Data.Fin.Permutation as P

open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_; _∘-fb_; ∘-fb-congˡ)
open import Categories.PermuteCoherence.Word
  using (Word; canonW; evalW; eval-canonW; genFB)
open import Categories.PermuteCoherence.Inversions using (inv; canonW-length)
open import Categories.PermuteCoherence.InversionsCong using (inv-resp-≈)
open import Categories.PermuteCoherence.InversionsRec using (invS≡inv)
open import Categories.PermuteCoherence.InversionsDichotomy
  using (invS-dichotomy; inj; suc-pos; toℕ-inj; toℕ-suc-pos)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- 1. Reduced words and descents.

-- `w` is reduced: its length equals the inversion count of its value.
Reduced : Word n → Set
Reduced w = length w ≡ inv (evalW w)

-- `i` is a left descent of `b`: post-composing with `genFB i` lowers the
-- inversion count by one.
descent : Fin n → FinBij (suc n) (suc n) → Set
descent i b = suc (inv (genFB i ∘-fb b)) ≡ inv b

-- `descent` depends on its bijection only through `inv`, which respects
-- `≈-fb`, so `descent j` does too.
descent-resp-≈ : {j : Fin (suc n)} {x y : FinBij (suc (suc n)) (suc (suc n))}
               → x ≈-fb y → descent j x → descent j y
descent-resp-≈ {j = j} {x} {y} x≈y dsc =
  trans (cong suc (sym (inv-resp-≈ {b = genFB j ∘-fb x} {b′ = genFB j ∘-fb y}
                          (∘-fb-congˡ (genFB j) {f = x} {f′ = y} x≈y))))
        (trans dsc (inv-resp-≈ {b = x} {b′ = y} x≈y))

------------------------------------------------------------------------
-- 2. Every generator is an ascent or a descent.

private
  -- `b ⟨$⟩ˡ_` is injective (it is the inverse of a bijection).
  ⟨$⟩ˡ-inj : (b : FinBij (suc n) (suc n)) {x y : Fin (suc n)}
           → b P.⟨$⟩ˡ x ≡ b P.⟨$⟩ˡ y → x ≡ y
  ⟨$⟩ˡ-inj b {x} {y} eq =
    trans (sym (P.inverseʳ b)) (trans (cong (b P.⟨$⟩ʳ_) eq) (P.inverseʳ b))

  -- The two swapped value-positions are distinct (their `toℕ`s differ).
  inj≢suc : (i : Fin (suc n)) → ¬ (inj i ≡ suc-pos i)
  inj≢suc i e =
    1+n≢n (sym (trans (sym (toℕ-inj i)) (trans (cong toℕ e) (toℕ-suc-pos i))))

inv-di : (i : Fin (suc n)) (b : FinBij (suc (suc n)) (suc (suc n)))
       → (inv (genFB i ∘-fb b) ≡ suc (inv b)) ⊎ descent i b
inv-di i b with <-cmp (toℕ (b P.⟨$⟩ˡ inj i)) (toℕ (b P.⟨$⟩ˡ suc-pos i))
... | tri< lt _ _ =
  inj₁ (trans (sym (invS≡inv (genFB i ∘-fb b)))
       (trans (proj₁ (invS-dichotomy i b) lt) (cong suc (invS≡inv b))))
... | tri> _ _ gt =
  inj₂ (trans (cong suc (sym (invS≡inv (genFB i ∘-fb b))))
       (trans (proj₂ (invS-dichotomy i b) gt) (invS≡inv b)))
... | tri≈ _ eq _ = ⊥-elim (inj≢suc i (⟨$⟩ˡ-inj b (toℕ-injective eq)))

------------------------------------------------------------------------
-- 3. `canonW b` is reduced.

canonW-reduced : (b : FinBij (suc n) (suc n)) → Reduced (canonW b)
canonW-reduced b = trans (canonW-length b) (sym (inv-resp-≈ (eval-canonW b)))
