{-# OPTIONS --safe --without-K #-}

-- What the extracting simulator computes, and the one combinatorial fact the
-- extraction rests on.
--
-- The simulator's log IS the oracle's table, and `extract c` reads the bit of
-- the unique preimage of `c` in it, defaulting to `false` at none or at
-- several.  `Pins c b L` is what makes that reading usable at the opening:
-- EVERY preimage of `c` in `L` starts with `b`.  `pins-extract` establishes it
-- at a duplicate-free answer log — which is why `Uniform.Duplicate.dup` is the
-- binding argument's first flag — and `pins-∷` keeps it across a sample that
-- misses `c`, which is why a hit on an outstanding digest is the second.

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec; head)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_)

module CategoricalCrypto.Examples.ROCommitment.Extraction (k : ℕ) where

open import ProbabilisticLogic.Distribution.Uniform.Duplicate k using (dup; memb)

-- An oracle point carries the committed bit in front of the opening
-- randomness, which is what makes a preimage extractable at all.
Pt Dig : Set
Pt  = Vec Bool (suc k)
Dig = Vec Bool k

Tbl : Set
Tbl = List (Pt × Dig)

answers : Tbl → List Dig
answers = map proj₂

lookupPt : Tbl → Pt → Maybe Dig
lookupPt []            x = nothing
lookupPt ((y , d) ∷ L) x with x ≟ y
... | yes _ = just d
... | no  _ = lookupPt L x

preimages : Dig → Tbl → List Pt
preimages c []            = []
preimages c ((x , d) ∷ L) with d ≟ c
... | yes _ = x ∷ preimages c L
... | no  _ = preimages c L

pick : List Pt → Bool
pick (x ∷ []) = head x
pick _        = false

-- The simulator's reading of a commitment digest: the bit of its unique
-- preimage, `false` at none or at several.
extract : Dig → Tbl → Bool
extract c L = pick (preimages c L)

------------------------------------------------------------------------
-- The extraction is pinned

-- Every preimage of `c` in the table starts with `b`.
Pins : Dig → Bool → Tbl → Set
Pins c b []            = ⊤
Pins c b ((x , d) ∷ L) = (d ≡ c → head x ≡ b) × Pins c b L

private
  ∨-false : (a b : Bool) → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  ∨-false false false _ = refl , refl
  ∨-false false true  e = case e of λ ()
  ∨-false true  _     e = case e of λ ()

  memb-pre : (c : Dig) (L : Tbl) → memb c (answers L) ≡ false → preimages c L ≡ []
  memb-pre c []            _  = refl
  memb-pre c ((x , d) ∷ L) eq with c ≟ d | d ≟ c
  ... | yes _   | _       = case eq of λ ()
  ... | no  c≢d | yes d≡c = ⊥-elim (c≢d (sym d≡c))
  ... | no  _   | no  _   = memb-pre c L eq

  pins-[] : (c : Dig) (b : Bool) (L : Tbl) → preimages c L ≡ [] → Pins c b L
  pins-[] c b []            _  = tt
  pins-[] c b ((x , d) ∷ L) eq with d ≟ c
  ... | yes _  = case eq of λ ()
  ... | no d≢c = (λ d≡c → ⊥-elim (d≢c d≡c)) , pins-[] c b L eq

-- At a duplicate-free answer log the extraction is pinned: `c` has at most one
-- preimage there, so reading its bit reads the bit of every preimage there is.
pins-extract : (c : Dig) (L : Tbl) → dup (answers L) ≡ false → Pins c (extract c L) L
pins-extract c []            _  = tt
pins-extract c ((x , d) ∷ L) nd with ∨-false (memb d (answers L)) (dup (answers L)) nd
pins-extract c ((x , d) ∷ L) nd | mb , dd with d ≟ c
... | no d≢c = (λ d≡c → ⊥-elim (d≢c d≡c)) , pins-extract c L dd
... | yes d≡c = (λ _ → sym eq) , subst (λ b → Pins c b L) (sym eq) (pins-[] c (head x) L pre≡[])
  where
  pre≡[] : preimages c L ≡ []
  pre≡[] = memb-pre c L (subst (λ z → memb z (answers L) ≡ false) d≡c mb)

  eq : pick (x ∷ preimages c L) ≡ head x
  eq = cong (λ z → pick (x ∷ z)) pre≡[]

-- A sample that misses `c` adds no preimage of it.
pins-∷ : (c : Dig) (b : Bool) (x : Pt) (h : Dig) (L : Tbl)
       → ¬ (h ≡ c) → Pins c b L → Pins c b ((x , h) ∷ L)
pins-∷ c b x h L ne p = (λ e → ⊥-elim (ne e)) , p

-- …and what the pin is FOR: a tabulated point whose answer is the commitment
-- digest opens to the extracted bit.
pins-lookup : (c : Dig) (b : Bool) (L : Tbl) (x : Pt) (d : Dig)
            → lookupPt L x ≡ just d → Pins c b L → d ≡ c → head x ≡ b
pins-lookup c b ((y , e) ∷ L) x d hit p d≡c with x ≟ y
... | yes x≡y = trans (cong head x≡y) (proj₁ p (trans (just-injective hit) d≡c))
... | no _    = pins-lookup c b L x d hit (proj₂ p) d≡c
