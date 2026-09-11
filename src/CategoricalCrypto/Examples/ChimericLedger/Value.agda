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
--
-- `Shape`/`shape` walk the validation cascade once and hand every later
-- consumer the two-way case with an accepted transaction's data attached.

open import Class.DecEq

open import Data.Bool.Base using (Bool; true; false; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base renaming (_≡ᵇ_ to _≡ᴺ_)
open import Data.Nat.Properties using
  ( +-assoc; +-comm; +-identityʳ; +-monoˡ-≤; ≤-refl; ≤-reflexive; ≤-trans
  ; ≡ᵇ⇒≡; ≤ᵇ⇒≤; m+[n∸m]≡n; m≤m+n; n≤1+n; n≤0⇒n≡0; 1+n≰n; module ≤-Reasoning )
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_)

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
-- Keys and uniqueness
------------------------------------------------------------------------

keysU : Utxo → List TxIn
keysU = map proj₁

-- Each key absent from the rest of the list.  This is what makes `removeIn`
-- remove a KEY rather than one copy of it, and every step of the birthday
-- argument that says "this input is gone now" rests on it.
Uniq : Utxo → Set
Uniq []            = ⊤
Uniq ((k , _) ∷ m) = lookupU m k ≡ nothing × Uniq m

lookupU-just-∈ : ∀ u k o → lookupU u k ≡ just o → k ∈ keysU u
lookupU-just-∈ ((k₀ , v) ∷ m) k o eq with k ≟ k₀
... | yes p = here p
... | no  _ = there (lookupU-just-∈ m k o eq)

∉-lookupU : ∀ u k → ¬ (k ∈ keysU u) → lookupU u k ≡ nothing
∉-lookupU []             k h = refl
∉-lookupU ((k₀ , v) ∷ m) k h with k ≟ k₀
... | yes p = ⊥-elim (h (here p))
... | no  _ = ∉-lookupU m k (λ mem → h (there mem))

private
  -- `removeIn` rebuilds the cons, so the decision has to be re-applied by
  -- hand: a `with` on it abstracts the outer occurrence only.
  lookupU-cons-≢ : ∀ k₀ v m k → k ≢ k₀ → lookupU m k ≡ nothing
                 → lookupU ((k₀ , v) ∷ m) k ≡ nothing
  lookupU-cons-≢ k₀ v m k ne hyp with k ≟ k₀
  ... | yes p = ⊥-elim (ne p)
  ... | no  _ = hyp

uniq-removeIn-lookup : ∀ u k → Uniq u → lookupU (removeIn k u) k ≡ nothing
uniq-removeIn-lookup []             k uq           = refl
uniq-removeIn-lookup ((k₀ , v) ∷ m) k (fst , rest) with k ≟ k₀
... | yes p  = subst (λ z → lookupU m z ≡ nothing) (sym p) fst
... | no  ¬p = lookupU-cons-≢ k₀ v (removeIn k m) k ¬p (uniq-removeIn-lookup m k rest)

uniq-removeIn : ∀ u i → Uniq u → Uniq (removeIn i u)
uniq-removeIn []             i uq           = tt
uniq-removeIn ((k₀ , v) ∷ m) i (fst , rest) with i ≟ k₀
... | yes _ = rest
... | no  _ = lookupU-removeIn m i k₀ fst , uniq-removeIn m i rest

uniq-insertNew : ∀ u kv → Uniq u → Uniq (insertNew u kv)
uniq-insertNew u (k , v) uq with lookupU u k in eq
... | just _  = uq
... | nothing = eq , uq

uniq-unionNew : ∀ u w → Uniq u → Uniq (unionNew u w)
uniq-unionNew u []        uq = uq
uniq-unionNew u (kv ∷ w)  uq = uniq-unionNew (insertNew u kv) w (uniq-insertNew u kv uq)

checkIns-uniq : ∀ u is v u′ → Uniq u → checkIns u is ≡ just (v , u′) → Uniq u′
checkIns-uniq u []       v u′ uq eq =
  subst (λ p → Uniq (proj₂ p)) (just-injective eq) uq
checkIns-uniq u (i ∷ is) v u′ uq eq with lookupU u i in eqL
... | nothing = ⊥-just eq
... | just o with checkIns (removeIn i u) is in eqC
...   | nothing = ⊥-just eq
...   | just (v₀ , u₁) = subst (λ p → Uniq (proj₂ p)) (just-injective eq)
          (checkIns-uniq (removeIn i u) is v₀ u₁ (uniq-removeIn u i uq) eqC)

-- The first input of an accepted transaction is gone from the surviving set.
checkIns-consumed : ∀ u i is v u′ → Uniq u → checkIns u (i ∷ is) ≡ just (v , u′)
                  → lookupU u′ i ≡ nothing
checkIns-consumed u i is v u′ uq eq with lookupU u i in eqL
... | nothing = ⊥-just eq
... | just o with checkIns (removeIn i u) is in eqC
...   | nothing = ⊥-just eq
...   | just (v₀ , u₁) = subst (λ p → lookupU (proj₂ p) i ≡ nothing) (just-injective eq)
          (checkIns-lookupU (removeIn i u) is v₀ u₁ i eqC (uniq-removeIn-lookup u i uq))

-- …and every input of an accepted transaction was live: a transaction one of
-- whose inputs is already spent cannot be accepted again.
checkIns-live : ∀ u is v u′ k → checkIns u is ≡ just (v , u′) → k ∈ is
              → lookupU u k ≡ nothing → ⊥
checkIns-live u (i ∷ is) v u′ k eq mem hyp with lookupU u i in eqL
... | nothing = ⊥-just eq
... | just o with checkIns (removeIn i u) is in eqC
...   | nothing = ⊥-just eq
...   | just (v₀ , u₁) with mem
...     | here p = ⊥-nothing
                     (trans (sym eqL) (subst (λ z → lookupU u z ≡ nothing) p hyp))
...     | there mem′ = checkIns-live (removeIn i u) is v₀ u₁ k eqC mem′
                         (lookupU-removeIn u i k hyp)

keysU-removeIn : ∀ u i k → k ∈ keysU (removeIn i u) → k ∈ keysU u
keysU-removeIn ((k₀ , v) ∷ m) i k mem with i ≟ k₀
... | yes _ = there mem
... | no  _ with mem
...   | here p     = here p
...   | there mem′ = there (keysU-removeIn m i k mem′)

checkIns-keysU : ∀ u is v u′ k → checkIns u is ≡ just (v , u′)
               → k ∈ keysU u′ → k ∈ keysU u
checkIns-keysU u []       v u′ k eq mem =
  subst (λ p → k ∈ keysU (proj₂ p)) (sym (just-injective eq)) mem
checkIns-keysU u (i ∷ is) v u′ k eq mem with lookupU u i in eqL
... | nothing = ⊥-just eq
... | just o with checkIns (removeIn i u) is in eqC
...   | nothing = ⊥-just eq
...   | just (v₀ , u₁) = keysU-removeIn u i k
          (checkIns-keysU (removeIn i u) is v₀ u₁ k eqC
            (subst (λ p → k ∈ keysU (proj₂ p)) (sym (just-injective eq)) mem))

keysU-insertNew : ∀ u kv k → k ∈ keysU (insertNew u kv) → k ∈ keysU u ⊎ k ≡ proj₁ kv
keysU-insertNew u (k₀ , v) k mem with is-just (lookupU u k₀)
... | true  = inj₁ mem
... | false with mem
...   | here p     = inj₂ p
...   | there mem′ = inj₁ mem′

keysU-unionNew-outsAt : ∀ u h i os k → k ∈ keysU (unionNew u (outsAt h i os))
                      → k ∈ keysU u ⊎ proj₁ k ≡ h
keysU-unionNew-outsAt u h i []       k mem = inj₁ mem
keysU-unionNew-outsAt u h i (o ∷ os) k mem
  with keysU-unionNew-outsAt (insertNew u ((h , i) , o)) h (suc i) os k mem
... | inj₂ eq = inj₂ eq
... | inj₁ m₁ with keysU-insertNew u ((h , i) , o) k m₁
...   | inj₁ m₂ = inj₁ m₂
...   | inj₂ p  = inj₂ (cong proj₁ p)

lookupU-insertNew : ∀ u kv k → k ≢ proj₁ kv → lookupU u k ≡ nothing
                  → lookupU (insertNew u kv) k ≡ nothing
lookupU-insertNew u (k₀ , v) k ne hyp with is-just (lookupU u k₀)
... | true  = hyp
... | false with k ≟ k₀
...   | yes p = ⊥-elim (ne p)
...   | no  _ = hyp

lookupU-unionNew-outsAt : ∀ u h i os k → proj₁ k ≢ h → lookupU u k ≡ nothing
                        → lookupU (unionNew u (outsAt h i os)) k ≡ nothing
lookupU-unionNew-outsAt u h i []       k ne hyp = hyp
lookupU-unionNew-outsAt u h i (o ∷ os) k ne hyp =
  lookupU-unionNew-outsAt (insertNew u ((h , i) , o)) h (suc i) os k ne
    (lookupU-insertNew u ((h , i) , o) k (λ p → ne (cong proj₁ p)) hyp)

------------------------------------------------------------------------
-- One step of the ledger
------------------------------------------------------------------------

module _ (ser : Tx → List Bool) where

  open Step ser

  -- The state a step reaches when the oracle answers `h`.
  after : Variant → LState → Tx → Hash → LState
  after vr s tx h = proj₁ (runCall (λ _ → h) (applyTx vr s tx))

  ------------------------------------------------------------------------
  -- The two shapes an activation takes
  --
  -- A `with` on the validation cascade does not reach `applyTx` inside a
  -- constructor argument (the abstraction only rewrites the goal), so the
  -- cascade is walked ONCE here and the equations are `rewrite`n in.  Every
  -- consumer then sees a two-way case with the data an accepted transaction
  -- carries: which UTxO entries survived, which accounts were debited, and —
  -- what makes `inputConsuming` the repair — that inputs were consumed.

  private
    reject-ins : ∀ vr s tx → checkIns (proj₁ s) (proj₁ tx) ≡ nothing
               → applyTx vr s tx ≡ pureᶜ (s , false)
    reject-ins vr (u , a) (ins , wds , outs) e rewrite e = refl

    reject-wds : ∀ vr s tx {vIn u′} → checkIns (proj₁ s) (proj₁ tx) ≡ just (vIn , u′)
               → checkWdrls (proj₂ s) (proj₁ (proj₂ tx)) ≡ nothing
               → applyTx vr s tx ≡ pureᶜ (s , false)
    reject-wds vr (u , a) (ins , wds , outs) e₁ e₂ rewrite e₁ | e₂ = refl

    reject-bal : ∀ vr s tx {vIn u′ a′} → checkIns (proj₁ s) (proj₁ tx) ≡ just (vIn , u′)
               → checkWdrls (proj₂ s) (proj₁ (proj₂ tx)) ≡ just a′
               → ((vIn + wdrlΣ (proj₁ (proj₂ tx))) ≡ᴺ valΣ (proj₂ (proj₂ tx))) ≡ false
               → applyTx vr s tx ≡ pureᶜ (s , false)
    reject-bal vr (u , a) (ins , wds , outs) e₁ e₂ eb rewrite e₁ | e₂ | eb = refl

    reject-con : ∀ vr s tx {vIn u′ a′} → checkIns (proj₁ s) (proj₁ tx) ≡ just (vIn , u′)
               → checkWdrls (proj₂ s) (proj₁ (proj₂ tx)) ≡ just a′
               → ((vIn + wdrlΣ (proj₁ (proj₂ tx))) ≡ᴺ valΣ (proj₂ (proj₂ tx))) ≡ true
               → consumes vr (proj₁ tx) ≡ false
               → applyTx vr s tx ≡ pureᶜ (s , false)
    reject-con vr (u , a) (ins , wds , outs) e₁ e₂ eb ec
      rewrite e₁ | e₂ | eb | ec = refl

    accept-eq : ∀ vr s tx {vIn u′ a′} → checkIns (proj₁ s) (proj₁ tx) ≡ just (vIn , u′)
              → checkWdrls (proj₂ s) (proj₁ (proj₂ tx)) ≡ just a′
              → ((vIn + wdrlΣ (proj₁ (proj₂ tx))) ≡ᴺ valΣ (proj₂ (proj₂ tx))) ≡ true
              → consumes vr (proj₁ tx) ≡ true
              → applyTx vr s tx
                ≡ callᶜ (ser tx)
                    (λ h → (unionNew u′ (outsAt h 0 (proj₂ (proj₂ tx))) , a′) , true)
    accept-eq vr (u , a) (ins , wds , outs) e₁ e₂ eb ec
      rewrite e₁ | e₂ | eb | ec = refl

  data Shape (vr : Variant) (s : LState) (tx : Tx) : Set where
    rejected : applyTx vr s tx ≡ pureᶜ (s , false) → Shape vr s tx
    accepted : (vIn : ℕ) (u′ : Utxo) (a′ : Accts)
             → checkIns (proj₁ s) (proj₁ tx) ≡ just (vIn , u′)
             → checkWdrls (proj₂ s) (proj₁ (proj₂ tx)) ≡ just a′
             → consumes vr (proj₁ tx) ≡ true
             → applyTx vr s tx
               ≡ callᶜ (ser tx)
                   (λ h → (unionNew u′ (outsAt h 0 (proj₂ (proj₂ tx))) , a′) , true)
             → Shape vr s tx

  shape : ∀ vr s tx → Shape vr s tx
  shape vr s@(u , a) tx@(ins , wds , outs) with checkIns u ins in e₁
  ... | nothing = rejected (reject-ins vr s tx e₁)
  ... | just (vIn , u′) with checkWdrls a wds in e₂
  ...   | nothing = rejected (reject-wds vr s tx e₁ e₂)
  ...   | just a′ with (vIn + wdrlΣ wds) ≡ᴺ valΣ outs in eb
  ...     | false = rejected (reject-bal vr s tx e₁ e₂ eb)
  ...     | true with consumes vr ins in ec
  ...       | false = rejected (reject-con vr s tx e₁ e₂ eb ec)
  ...       | true  = accepted vIn u′ a′ e₁ e₂ ec (accept-eq vr s tx e₁ e₂ eb ec)

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
