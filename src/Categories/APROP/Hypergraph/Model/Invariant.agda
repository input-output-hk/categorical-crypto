{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Invariants of APROP-translated hypergraphs.
--
-- The decode pipeline relies on structural properties of the translation
-- that are universal but not captured by the `Hypergraph` record fields
-- alone (`Unique` witnesses for `range n` and `hGen`'s dom, and the
-- `range`/`_++_` split).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Model.Invariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Data.Fin as Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List.Properties using (map-id; map-cong; map-++; map-∘)
open import Data.List.Properties.Ext using (map-∘-cong)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁻)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
import Data.List.Relation.Unary.All                as ListAll
import Data.List.Relation.Unary.All.Properties     as ListAll-Prop
import Data.List.Relation.Unary.AllPairs           as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop

--------------------------------------------------------------------------------
-- injectivity of `_↑ˡ_`/`_↑ʳ_` and element-level disjointness of their images:
-- one home in the stdlib-only `Util.Prune`, re-exported here under the names
-- the decode pipeline uses.  (`Prune` cannot import this module, which is
-- `sig`-parameterised, so only this direction is available.)
open import Categories.APROP.Hypergraph.Util.Prune
  using ()
  renaming (↑ˡ-inj to inject+-inj; ↑ʳ-inj to raise-inj; ↑ˡ-↑ʳ-disjoint to ↑ˡ≢↑ʳ)
  public

-- map `_↑ˡ_` and map `_↑ʳ_` produce disjoint lists: a common `v` would be both
-- an `_↑ˡ n` and an `m ↑ʳ_`, which `↑ˡ≢↑ʳ` refutes.
disj-L-R : ∀ {m n} (xs : List (Fin m)) (ys : List (Fin n))
         → Disjoint (map (_↑ˡ n) xs) (map (m ↑ʳ_) ys)
disj-L-R {m} {n} xs ys (v∈L , v∈R) with ∈-map⁻ (_↑ˡ n) v∈L | ∈-map⁻ (m ↑ʳ_) v∈R
... | vL , _ , v≡L | vR , _ , v≡R = ↑ˡ≢↑ʳ vL vR (trans (sym v≡L) v≡R)

--------------------------------------------------------------------------------
-- Unique witnesses for `range n` and for `hGen`'s dom.
-- `zero ≢ suc _` pointwise (`All.universal`) transported across the `map suc`
-- (`All.Properties.map⁺`) is the head condition; the tail is `suc`-injectivity.

range-Unique : ∀ n → Unique (range n)
range-Unique 0             = AllPairs.[]
range-Unique (suc n)  =
  ListAll-Prop.map⁺ (ListAll.universal (λ _ → λ ()) (range n))
    AllPairs.∷ Uniq-Prop.map⁺ suc-injective (range-Unique n)

hGen-dom-Unique : ∀ {A B : ObjTerm} (f : mor A B) → Unique (Hypergraph.dom (hGen f))
hGen-dom-Unique {A} f = Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _)

--------------------------------------------------------------------------------
-- `range` splits along `_+_`:
--   range (n + m) ≡ map (_↑ˡ m) (range n) ++ map (n ↑ʳ_) (range m)

range-++ : ∀ (n m : ℕ)
         → range (n + m) ≡ map (_↑ˡ m) (range n) ++ map (n ↑ʳ_) (range m)
range-++ zero    m = trans (sym (map-id (range m)))
                           (sym (map-cong (λ _ → refl) (range m)))
range-++ (suc n) m = cong (zero ∷_)
  (trans (cong (map Fin.suc) (range-++ n m))
  (trans (map-++ Fin.suc (map (_↑ˡ m) (range n)) (map (n ↑ʳ_) (range m)))
         (cong₂ _++_
           (trans (map-∘-cong (λ _ → refl) (range n)) (map-∘ (range n)))
           (sym (map-∘ (range m))))))
