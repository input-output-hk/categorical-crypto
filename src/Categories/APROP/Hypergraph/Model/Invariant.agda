{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Invariants of APROP-translated hypergraphs.
--
-- The pruned cospan composition `hComposeP` relies on structural properties
-- of the translation that are universal but not captured by the `Hypergraph`
-- record fields alone (uniqueness / dom≡cod of the identity and swap
-- hypergraphs, `range`-shape of `hId`'s dom, and Fin/cast bridging lemmas).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Model.Invariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
import Data.Fin as Fin
open import Data.Fin.Properties using (suc-injective)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-id; map-cong; map-++; map-∘)
open import Data.List.Properties.Ext using (map-∘-cong)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁻)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
import Data.List.Relation.Unary.All                as ListAll
import Data.List.Relation.Unary.All.Properties     as ListAll-Prop
import Data.List.Relation.Unary.AllPairs           as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)

--------------------------------------------------------------------------------
-- For identity hypergraphs, `dom ≡ cod` as lists (every `hId` branch uses
-- the same Fin-list on both sides).

hId-cod≡dom : ∀ A → Hypergraph.cod (hId A) ≡ Hypergraph.dom (hId A)
hId-cod≡dom unit      = refl
hId-cod≡dom (Var x)   = refl
hId-cod≡dom (A ⊗₀ B)  =
  cong₂ _++_
    (cong (map (_↑ˡ Hypergraph.nV (hId B))) (hId-cod≡dom A))
    (cong (map (Hypergraph.nV (hId A) ↑ʳ_)) (hId-cod≡dom B))

--------------------------------------------------------------------------------
-- `Unique` for identity's dom.  The tensor case needs `map⁺` with `_↑ˡ_` /
-- `_↑ʳ_` injectivity on each side + `++⁺` with disjointness of their images.

-- injectivity of `_↑ˡ_`/`_↑ʳ_` and element-level disjointness of their images:
-- one home in the stdlib-only `Util.Prune`, re-exported here under the names
-- the decode pipeline and `HomTermInvariant` use.  (`Prune` cannot import this
-- module, which is `sig`-parameterised, so only this direction is available.)
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

hId-dom-Unique : ∀ A → Unique (Hypergraph.dom (hId A))
hId-dom-Unique unit     = AllPairs.[]
hId-dom-Unique (Var x)  = ListAll.[] AllPairs.∷ AllPairs.[]
hId-dom-Unique (A ⊗₀ B) =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj (Hypergraph.nV (hId B))) (hId-dom-Unique A))
    (Uniq-Prop.map⁺ (raise-inj   (Hypergraph.nV (hId A))) (hId-dom-Unique B))
    (disj-L-R (Hypergraph.dom (hId A)) (Hypergraph.dom (hId B)))

-- Symmetric version for cod.
hId-cod-Unique : ∀ A → Unique (Hypergraph.cod (hId A))
hId-cod-Unique A = subst Unique (sym (hId-cod≡dom A)) (hId-dom-Unique A)

--------------------------------------------------------------------------------
-- Unique witnesses for `range n` and for `hSwap` / `hGen`.
-- `zero ≢ suc _` pointwise (`All.universal`) transported across the `map suc`
-- (`All.Properties.map⁺`) is the head condition; the tail is `suc`-injectivity.

range-Unique : ∀ n → Unique (range n)
range-Unique 0             = AllPairs.[]
range-Unique (suc n)  =
  ListAll-Prop.map⁺ (ListAll.universal (λ _ → λ ()) (range n))
    AllPairs.∷ Uniq-Prop.map⁺ suc-injective (range-Unique n)

hSwap-dom-Unique : ∀ A B → Unique (Hypergraph.dom (hSwap A B))
hSwap-dom-Unique A B =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _))
    (Uniq-Prop.map⁺ (raise-inj   _) (range-Unique _))
    (disj-L-R (range (length (flatten A))) (range (length (flatten B))))

-- hSwap's cod is dom with the two halves swapped.
hSwap-cod-Unique : ∀ A B → Unique (Hypergraph.cod (hSwap A B))
hSwap-cod-Unique A B =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (raise-inj   _) (range-Unique _))
    (Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _))
    (disj-R-L (range (length (flatten B))) (range (length (flatten A))))
  where
    disj-R-L : ∀ {m n} (ys : List (Fin n)) (xs : List (Fin m))
             → Disjoint (map (m ↑ʳ_) ys) (map (_↑ˡ n) xs)
    disj-R-L ys xs (v∈R , v∈L) = disj-L-R xs ys (v∈L , v∈R)

hGen-dom-Unique : ∀ {A B : ObjTerm} (f : mor A B) → Unique (Hypergraph.dom (hGen f))
hGen-dom-Unique {A} f = Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _)

hGen-cod-Unique : ∀ {A B : ObjTerm} (f : mor A B) → Unique (Hypergraph.cod (hGen f))
hGen-cod-Unique {A} f = Uniq-Prop.map⁺ (raise-inj _) (range-Unique _)

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
