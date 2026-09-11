{-# OPTIONS --safe --without-K #-}

-- Preservation of value as arithmetic: what ONE accepted transaction does to
-- `total`, with the hash answered by an arbitrary oracle.
--
-- Two facts, and together they are the whole combinatorial content of the
-- birthday bound at the ledger side:
--
--   `applyTx-total-≤`      value is never created — the sequential validation
--                          pays every output out of a consumed input or a
--                          debited account;
--   `applyTx-total-fresh`  and none is destroyed either, UNLESS the hash keying
--                          the new outputs already keys a live UTxO entry, in
--                          which case `unionNew` swallows the output.
--
-- So a trajectory along which `total` moves has, at the step it moved, an
-- oracle answer colliding with a hash already keying the state; that is the
-- event the random oracle's counting bounds.

open import Class.DecEq

open import Data.Bool.Base using (Bool; true; false; if_then_else_; T)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.Properties using
  ( +-assoc; +-comm; +-identityʳ; +-monoˡ-≤; ≤-refl; ≤-reflexive; ≤-trans
  ; ≡ᵇ⇒≡; ≤ᵇ⇒≤; m+[n∸m]≡n; m≤m+n; n≤1+n; n≤0⇒n≡0; 1+n≰n; module ≤-Reasoning )
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.OracleCall

module CategoricalCrypto.Examples.ChimericLedger.Value (ℓ : ℕ) where

-- As in `ChimericLedger` itself: the pair instance is not upstream.
private instance DecEq-×′ = DecEq-×

open Ledger ℓ

private
  ⊥-just : {A B : Set} {x : A} → nothing ≡ just x → B
  ⊥-just ()

  ⊥-nothing : {A B : Set} {x : A} → just x ≡ nothing → B
  ⊥-nothing ()

  +-swap : ∀ m n p → m + (n + p) ≡ n + (m + p)
  +-swap m n p = trans (sym (+-assoc m n p))
                       (trans (cong (_+ p) (+-comm m n)) (+-assoc n m p))

  -- The balance equation an accepted transaction satisfies: the outputs are
  -- exactly the consumed inputs plus the debited withdrawals.
  shuffle : ∀ vIn bu′ vw ba′ vo → vIn + vw ≡ vo
          → (bu′ + vo) + ba′ ≡ (vIn + bu′) + (vw + ba′)
  shuffle vIn bu′ vw ba′ vo eqv = begin
    (bu′ + vo) + ba′          ≡⟨ cong (λ z → (bu′ + z) + ba′) (sym eqv) ⟩
    (bu′ + (vIn + vw)) + ba′  ≡⟨ cong (_+ ba′) (sym (+-assoc bu′ vIn vw)) ⟩
    ((bu′ + vIn) + vw) + ba′  ≡⟨ cong (λ z → (z + vw) + ba′) (+-comm bu′ vIn) ⟩
    ((vIn + bu′) + vw) + ba′  ≡⟨ +-assoc (vIn + bu′) vw ba′ ⟩
    (vIn + bu′) + (vw + ba′)  ∎
    where open ≡-Reasoning

------------------------------------------------------------------------
-- Spending: the UTxO side
------------------------------------------------------------------------

balance-removeIn : ∀ u i o → lookupU u i ≡ just o
                 → balance u ≡ proj₂ o + balance (removeIn i u)
balance-removeIn []            i o eq = ⊥-just eq
balance-removeIn ((k , v) ∷ m) i o eq with i ≟ k
... | yes _ = cong (_+ balance m) (cong proj₂ (just-injective eq))
... | no  _ = trans (cong (proj₂ v +_) (balance-removeIn m i o eq))
                    (+-swap (proj₂ v) (proj₂ o) (balance (removeIn i m)))

checkIns-balance : ∀ u is v u′ → checkIns u is ≡ just (v , u′)
                 → balance u ≡ v + balance u′
checkIns-balance u []       v u′ eq =
  subst (λ p → balance u ≡ proj₁ p + balance (proj₂ p)) (just-injective eq) refl
checkIns-balance u (i ∷ is) v u′ eq with lookupU u i in eqL
... | nothing = ⊥-just eq
... | just o with checkIns (removeIn i u) is in eqC
...   | nothing = ⊥-just eq
...   | just (v₀ , u₁) =
        subst (λ p → balance u ≡ proj₁ p + balance (proj₂ p)) (just-injective eq)
          (trans (balance-removeIn u i o eqL)
            (trans (cong (proj₂ o +_) (checkIns-balance (removeIn i u) is v₀ u₁ eqC))
                   (sym (+-assoc (proj₂ o) v₀ (balance u₁)))))

------------------------------------------------------------------------
-- Withdrawing: the account side
------------------------------------------------------------------------

acctΣ-subOne : ∀ a x v → T (v ≤ᵇ acctOf a x) → acctΣ a ≡ v + acctΣ (subOne x v a)
acctΣ-subOne []            x v le =
  trans (sym (n≤0⇒n≡0 (≤ᵇ⇒≤ v 0 le))) (sym (+-identityʳ v))
acctΣ-subOne ((y , w) ∷ a) x v le with x ≟ y
... | yes _ = trans (cong (_+ acctΣ a) (sym (m+[n∸m]≡n (≤ᵇ⇒≤ v w le))))
                    (+-assoc v (w ∸ v) (acctΣ a))
... | no  _ = trans (cong (w +_) (acctΣ-subOne a x v le))
                    (+-swap w v (acctΣ (subOne x v a)))

checkWdrls-acctΣ : ∀ a ws a′ → checkWdrls a ws ≡ just a′
                 → acctΣ a ≡ wdrlΣ ws + acctΣ a′
checkWdrls-acctΣ a []             a′ eq = cong acctΣ (just-injective eq)
checkWdrls-acctΣ a ((x , v) ∷ ws) a′ eq with v ≤ᵇ acctOf a x in eqb
... | false = ⊥-just eq
... | true  = trans (acctΣ-subOne a x v (subst T (sym eqb) tt))
                (trans (cong (v +_) (checkWdrls-acctΣ (subOne x v a) ws a′ eq))
                       (sym (+-assoc v (wdrlΣ ws) (acctΣ a′))))

------------------------------------------------------------------------
-- Creating: the outputs a transaction keys by its hash
------------------------------------------------------------------------

balance-outsAt : ∀ h i os → balance (outsAt h i os) ≡ valΣ os
balance-outsAt h i []       = refl
balance-outsAt h i (o ∷ os) = cong (proj₂ o +_) (balance-outsAt h (suc i) os)

balance-insertNew-≤ : ∀ u kv → balance (insertNew u kv) ≤ balance u + proj₂ (proj₂ kv)
balance-insertNew-≤ u (k , v) with is-just (lookupU u k)
... | true  = m≤m+n (balance u) (proj₂ v)
... | false = ≤-reflexive (+-comm (proj₂ v) (balance u))

-- `unionNew` keeps the entry already present, so a union can only lose value.
balance-unionNew-≤ : ∀ u w → balance (unionNew u w) ≤ balance u + balance w
balance-unionNew-≤ u []              = ≤-reflexive (sym (+-identityʳ (balance u)))
balance-unionNew-≤ u (kv@(k , v) ∷ w) = begin
  balance (unionNew (insertNew u kv) w)
    ≤⟨ balance-unionNew-≤ (insertNew u kv) w ⟩
  balance (insertNew u kv) + balance w
    ≤⟨ +-monoˡ-≤ (balance w) (balance-insertNew-≤ u kv) ⟩
  (balance u + proj₂ v) + balance w
    ≡⟨ +-assoc (balance u) (proj₂ v) (balance w) ⟩
  balance u + (proj₂ v + balance w)
    ∎
  where open ≤-Reasoning

-- …and it loses none when the hash keying the new entries is unused.  The
-- index bound is what keeps the induction honest: the entries `outsAt` creates
-- are pairwise distinct, so only the indices not yet inserted must be free.
balance-unionNew-outsAt : ∀ u h i os → (∀ j → i ≤ j → lookupU u (h , j) ≡ nothing)
                        → balance (unionNew u (outsAt h i os)) ≡ balance u + valΣ os
balance-unionNew-outsAt u h i []       fresh = sym (+-identityʳ (balance u))
balance-unionNew-outsAt u h i (o ∷ os) fresh = begin
  balance (unionNew (insertNew u ((h , i) , o)) (outsAt h (suc i) os))
    ≡⟨ cong (λ z → balance (unionNew z (outsAt h (suc i) os))) ins ⟩
  balance (unionNew (((h , i) , o) ∷ u) (outsAt h (suc i) os))
    ≡⟨ balance-unionNew-outsAt (((h , i) , o) ∷ u) h (suc i) os fresh′ ⟩
  (proj₂ o + balance u) + valΣ os
    ≡⟨ +-assoc (proj₂ o) (balance u) (valΣ os) ⟩
  proj₂ o + (balance u + valΣ os)
    ≡⟨ +-swap (proj₂ o) (balance u) (valΣ os) ⟩
  balance u + (proj₂ o + valΣ os)
    ∎
  where
  open ≡-Reasoning

  ins : insertNew u ((h , i) , o) ≡ ((h , i) , o) ∷ u
  ins = cong (λ z → if is-just z then u else ((h , i) , o) ∷ u) (fresh i ≤-refl)

  fresh′ : ∀ j → suc i ≤ j → lookupU (((h , i) , o) ∷ u) (h , j) ≡ nothing
  fresh′ j le with (h , j) ≟ (h , i)
  ... | yes e = ⊥-elim (1+n≰n (subst (suc i ≤_) (cong proj₂ e) le))
  ... | no  _ = fresh j (≤-trans (n≤1+n i) le)

------------------------------------------------------------------------
-- Freshness survives the input side
------------------------------------------------------------------------

private
  lookupU-tail : ∀ k₀ v m k → lookupU ((k₀ , v) ∷ m) k ≡ nothing → lookupU m k ≡ nothing
  lookupU-tail k₀ v m k hyp with k ≟ k₀
  ... | yes _ = ⊥-nothing hyp
  ... | no  _ = hyp

  lookupU-cons : ∀ k₀ v m m′ k → lookupU ((k₀ , v) ∷ m) k ≡ nothing
               → lookupU m′ k ≡ nothing → lookupU ((k₀ , v) ∷ m′) k ≡ nothing
  lookupU-cons k₀ v m m′ k hyp hyp′ with k ≟ k₀
  ... | yes _ = hyp
  ... | no  _ = hyp′

lookupU-removeIn : ∀ u i k → lookupU u k ≡ nothing → lookupU (removeIn i u) k ≡ nothing
lookupU-removeIn []            i k hyp = hyp
lookupU-removeIn ((k₀ , v) ∷ m) i k hyp with i ≟ k₀
... | yes _ = lookupU-tail k₀ v m k hyp
... | no  _ = lookupU-cons k₀ v m (removeIn i m) k hyp
                (lookupU-removeIn m i k (lookupU-tail k₀ v m k hyp))

checkIns-lookupU : ∀ u is v u′ k → checkIns u is ≡ just (v , u′)
                 → lookupU u k ≡ nothing → lookupU u′ k ≡ nothing
checkIns-lookupU u []       v u′ k eq hyp =
  subst (λ p → lookupU (proj₂ p) k ≡ nothing) (just-injective eq) hyp
checkIns-lookupU u (i ∷ is) v u′ k eq hyp with lookupU u i in eqL
... | nothing = ⊥-just eq
... | just o with checkIns (removeIn i u) is in eqC
...   | nothing = ⊥-just eq
...   | just (v₀ , u₁) =
        subst (λ p → lookupU (proj₂ p) k ≡ nothing) (just-injective eq)
          (checkIns-lookupU (removeIn i u) is v₀ u₁ k eqC (lookupU-removeIn u i k hyp))

------------------------------------------------------------------------
-- One step of the ledger
------------------------------------------------------------------------

module _ (ser : Tx → List Bool) where

  open Step ser

  -- The state a step reaches when the oracle answers `h`.
  after : Variant → LState → Tx → Hash → LState
  after vr s tx h = proj₁ (runCall (λ _ → h) (applyTx vr s tx))

  applyTx-total-≤ : ∀ vr s tx h → total (after vr s tx h) ≤ total s
  applyTx-total-≤ vr (u , a) (ins , wds , outs) h
    with checkIns u ins in e₁ | checkWdrls a wds in e₂
  ... | nothing         | _       = ≤-refl
  ... | just (vIn , u′) | nothing = ≤-refl
  ... | just (vIn , u′) | just a′ with (vIn + wdrlΣ wds) ≡ᴺ valΣ outs in eb
  ...   | false = ≤-refl
  ...   | true with consumes vr ins
  ...     | false = ≤-refl
  ...     | true  = begin
              balance (unionNew u′ (outsAt h 0 outs)) + acctΣ a′
                ≤⟨ +-monoˡ-≤ (acctΣ a′) (balance-unionNew-≤ u′ (outsAt h 0 outs)) ⟩
              (balance u′ + balance (outsAt h 0 outs)) + acctΣ a′
                ≡⟨ cong (λ z → (balance u′ + z) + acctΣ a′) (balance-outsAt h 0 outs) ⟩
              (balance u′ + valΣ outs) + acctΣ a′
                ≡⟨ shuffle vIn (balance u′) (wdrlΣ wds) (acctΣ a′) (valΣ outs)
                     (≡ᵇ⇒≡ (vIn + wdrlΣ wds) (valΣ outs) (subst T (sym eb) tt)) ⟩
              (vIn + balance u′) + (wdrlΣ wds + acctΣ a′)
                ≡⟨ cong₂ _+_ (sym (checkIns-balance u ins vIn u′ e₁))
                             (sym (checkWdrls-acctΣ a wds a′ e₂)) ⟩
              balance u + acctΣ a
                ∎
              where open ≤-Reasoning

  applyTx-total-fresh : ∀ vr s tx h → (∀ j → lookupU (proj₁ s) (h , j) ≡ nothing)
                      → total (after vr s tx h) ≡ total s
  applyTx-total-fresh vr (u , a) (ins , wds , outs) h fresh
    with checkIns u ins in e₁ | checkWdrls a wds in e₂
  ... | nothing         | _       = refl
  ... | just (vIn , u′) | nothing = refl
  ... | just (vIn , u′) | just a′ with (vIn + wdrlΣ wds) ≡ᴺ valΣ outs in eb
  ...   | false = refl
  ...   | true with consumes vr ins
  ...     | false = refl
  ...     | true  = begin
              balance (unionNew u′ (outsAt h 0 outs)) + acctΣ a′
                ≡⟨ cong (_+ acctΣ a′)
                     (balance-unionNew-outsAt u′ h 0 outs
                       (λ j _ → checkIns-lookupU u ins vIn u′ (h , j) e₁ (fresh j))) ⟩
              (balance u′ + valΣ outs) + acctΣ a′
                ≡⟨ shuffle vIn (balance u′) (wdrlΣ wds) (acctΣ a′) (valΣ outs)
                     (≡ᵇ⇒≡ (vIn + wdrlΣ wds) (valΣ outs) (subst T (sym eb) tt)) ⟩
              (vIn + balance u′) + (wdrlΣ wds + acctΣ a′)
                ≡⟨ cong₂ _+_ (sym (checkIns-balance u ins vIn u′ e₁))
                             (sym (checkWdrls-acctΣ a wds a′ e₂)) ⟩
              balance u + acctΣ a
                ∎
              where open ≡-Reasoning
