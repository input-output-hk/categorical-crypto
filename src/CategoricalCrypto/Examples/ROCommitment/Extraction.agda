{-# OPTIONS --safe --without-K #-}

-- The extracting simulator's reading of a commitment digest, and the one
-- combinatorial fact behind it.
--
-- `Pins c b L` is what makes `extract c L` usable at the opening.
-- `pins-extract` establishes it at a duplicate-free answer log, which is why
-- `Uniform.Duplicate.dup` is the binding argument's first flag; `pins-∷` keeps
-- it across a sample that misses `c`, which is why a hit on an outstanding
-- digest is the second.

open import Class.DecEq

open import Data.Bool.Base
open import Data.Bool.Properties using (∨-conicalˡ; ∨-conicalʳ)
open import Data.Empty
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Properties
open import Data.Nat.Base
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; head)
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Negation.Core

module CategoricalCrypto.Examples.ROCommitment.Extraction (k : ℕ) where

open import ProbabilisticLogic.Distribution.Uniform.Duplicate k

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
lookupPt ((y , d) ∷ L) x = case x ≟ y of λ where
  (yes _) → just d
  (no  _) → lookupPt L x

lookup-here : (x : Pt) (d : Dig) (L : Tbl) → lookupPt ((x , d) ∷ L) x ≡ just d
lookup-here x d L with x ≟ x
... | yes _  = refl
... | no  ne = ⊥-elim (ne refl)

lookup-there : (x y : Pt) (d : Dig) (L : Tbl) → x ≢ y
             → lookupPt ((y , d) ∷ L) x ≡ lookupPt L x
lookup-there x y d L ne with x ≟ y
... | yes e = ⊥-elim (ne e)
... | no  _ = refl

preimages : Dig → Tbl → List Pt
preimages c []            = []
preimages c ((x , d) ∷ L) = case c ≟ d of λ where
  (yes _) → x ∷ preimages c L
  (no  _) → preimages c L

pre-hit : (c : Dig) (x : Pt) (L : Tbl) → preimages c ((x , c) ∷ L) ≡ x ∷ preimages c L
pre-hit c x L with c ≟ c
... | yes _  = refl
... | no  ne = ⊥-elim (ne refl)

pick : List Pt → Bool
pick (x ∷ []) = head x
pick _        = false

extract : Dig → Tbl → Bool
extract c L = pick (preimages c L)

------------------------------------------------------------------------
-- The extraction is pinned

Pins : Dig → Bool → Tbl → Set
Pins c b = All λ (x , d) → d ≡ c → head x ≡ b

private
  memb-pre : (c : Dig) (L : Tbl) → memb c (answers L) ≡ false → preimages c L ≡ []
  memb-pre c []            _  = refl
  memb-pre c ((x , d) ∷ L) eq with c ≟ d
  ... | yes _ = case eq of λ ()
  ... | no  _ = memb-pre c L eq

  pins-[] : (c : Dig) (b : Bool) (L : Tbl) → preimages c L ≡ [] → Pins c b L
  pins-[] c b []            _  = []
  pins-[] c b ((x , d) ∷ L) eq with c ≟ d
  ... | yes _  = case eq of λ ()
  ... | no c≢d = (λ d≡c → ⊥-elim (c≢d (sym d≡c))) ∷ pins-[] c b L eq

pins-extract : (c : Dig) (L : Tbl) → dup (answers L) ≡ false → Pins c (extract c L) L
pins-extract c []            _  = []
pins-extract c ((x , d) ∷ L) nd with c ≟ d
... | no c≢d = (λ d≡c → ⊥-elim (c≢d (sym d≡c))) ∷ pins-extract c L (∨-conicalʳ _ (dup (answers L)) nd)
... | yes c≡d = (λ _ → sym eq) ∷ subst (λ b → Pins c b L) (sym eq) (pins-[] c (head x) L pre≡[])
  where
  pre≡[] : preimages c L ≡ []
  pre≡[] = memb-pre c L (subst (λ z → memb z (answers L) ≡ false) (sym c≡d) (∨-conicalˡ _ (dup (answers L)) nd))

  eq : pick (x ∷ preimages c L) ≡ head x
  eq = cong (λ z → pick (x ∷ z)) pre≡[]

pins-∷ : (c : Dig) (b : Bool) (x : Pt) (h : Dig) (L : Tbl)
       → ¬ (h ≡ c) → Pins c b L → Pins c b ((x , h) ∷ L)
pins-∷ c b x h L ne p = (λ e → ⊥-elim (ne e)) ∷ p

pins-lookup : (c : Dig) (b : Bool) (L : Tbl) (x : Pt) (d : Dig)
            → lookupPt L x ≡ just d → Pins c b L → d ≡ c → head x ≡ b
pins-lookup c b ((y , e) ∷ L) x d hit (py ∷ p) d≡c with x ≟ y
... | yes x≡y = trans (cong head x≡y) (py (trans (just-injective hit) d≡c))
... | no _    = pins-lookup c b L x d hit p d≡c
