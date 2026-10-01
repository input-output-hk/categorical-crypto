{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic `extract-elem` / `extract-prefix` over `List (Fin n)`: the
-- multiset search of the decoder, kept in one signature-free place so that
-- every consumer observes the SAME definition (definitional equality).
--
-- Consumers: `APROP.…Soundness.Decode.Decode` (re-exports both `public`),
-- `APROP.…Soundness.Stack.SeparableStack`, and the φ-naturality proof in
-- `Combinatorics.ExtractPrefixEvalPhi`.
--------------------------------------------------------------------------------

module Categories.Combinatorics.ExtractPrefix where

open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality using (subst)
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
