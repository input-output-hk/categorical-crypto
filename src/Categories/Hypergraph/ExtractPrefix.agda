{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic `extract-elem` / `extract-prefix` over `List (Fin n)`.
--
-- Both `Categories.APROP.Hypergraph.Soundness.Decode` and
-- `Categories.FreeSMC.Steps` re-export from here so they observe the
-- SAME definition (definitional equality), which is required for the
-- `process-edges ≡ process-steps-maybe` correspondence lemma in
-- `Categories.APROP.Hypergraph.Soundness.Discharge.APROPMacLaneFromSMC`.
--
-- Bodies are verbatim copies of the original `Decode.extract-elem` /
-- `Decode.extract-prefix` (which are generic in `Fin n` already; only
-- their location was APROP-specific).
--------------------------------------------------------------------------------

module Categories.Hypergraph.ExtractPrefix where

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)
open import Relation.Nullary.Decidable using (yes; no)

extract-elem
  : ∀ {n} (k : Fin n) (xs : List (Fin n))
  → Maybe (Σ[ rest ∈ List (Fin n) ] xs Perm.↭ k ∷ rest)
extract-elem k []       = nothing
extract-elem k (x ∷ xs) with x ≟ k
... | yes p = just ( xs
                   , subst (λ y → (x ∷ xs) Perm.↭ y ∷ xs) p Perm.refl )
... | no  _ with extract-elem k xs
...               | nothing            = nothing
...               | just (rest , q)    =
                     just ( x ∷ rest
                          , Perm.trans (Perm.prep x q) (Perm.swap x k Perm.refl) )

extract-prefix
  : ∀ {n} (ks xs : List (Fin n))
  → Maybe (Σ[ rest ∈ List (Fin n) ] xs Perm.↭ ks ++ rest)
extract-prefix []       xs = just (xs , Perm.refl)
extract-prefix (k ∷ ks) xs with extract-elem k xs
... | nothing            = nothing
... | just (xs' , p)     with extract-prefix ks xs'
...                         | nothing            = nothing
...                         | just (rest , q)    =
                               just (rest , Perm.trans p (Perm.prep k q))
