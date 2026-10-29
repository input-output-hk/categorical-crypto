{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Invariants of APROP-translated hypergraphs.
--------------------------------------------------------------------------------

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Model.Invariant (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Util.Prune
  using ()
  renaming (↑ˡ-inj to inject+-inj; ↑ʳ-inj to raise-inj; ↑ˡ-↑ʳ-disjoint to ↑ˡ≢↑ʳ)
  public
open import Data.Fin as Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.List.Relation.Binary.Disjoint.Propositional
open import Data.List.Relation.Unary.Unique.Propositional
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Data.Nat

open APROP sig

disj-L-R : ∀ {m n} (xs : List (Fin m)) (ys : List (Fin n))
         → Disjoint (map (_↑ˡ n) xs) (map (m ↑ʳ_) ys)
disj-L-R {m} {n} xs ys (v∈L , v∈R) with ∈-map⁻ (_↑ˡ n) v∈L | ∈-map⁻ (m ↑ʳ_) v∈R
... | vL , _ , v≡L | vR , _ , v≡R = ↑ˡ≢↑ʳ vL vR (trans (sym v≡L) v≡R)


hGen-dom-Unique : ∀ {A B : ObjTerm} (f : mor A B) → Unique (Hypergraph.dom (hGen f))
hGen-dom-Unique {A} f = Uniq-Prop.map⁺ (inject+-inj _) (Uniq-Prop.allFin⁺ _)
