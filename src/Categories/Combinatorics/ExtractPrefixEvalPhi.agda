{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Injective relabelling preserves the search's returned derivation.
-- Decidable equality on `List (Fin m)` supplies UIP, pinning the second
-- component of its `Maybe` pair as well.
--------------------------------------------------------------------------------

module Categories.Combinatorics.ExtractPrefixEvalPhi where

open import Axiom.UniquenessOfIdentityProofs
open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.List.Properties
open import Data.List.Properties.Ext
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Product.Properties
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Categories.Combinatorics.ExtractPrefix

private
  push-subst-cons
    : ∀ {m} {xs V V' V'' : List (Fin m)} {a : Fin m}
        (A : xs ↭ a ∷ V) (B : V ↭ V') (e : V' ≡ V'')
    → subst (λ z → xs ↭ z) (cong (a ∷_) e) (Perm.trans A (Perm.prep a B))
      ≡ Perm.trans A (Perm.prep a (subst (λ z → V ↭ z) e B))
  push-subst-cons A B refl = refl

module _ {n m : ℕ} (f : Fin n → Fin m)
         (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y) where

  map⁺-subst
    : ∀ {x k : Fin n} (xs : List (Fin n)) (pf : x ≡ k) (pf' : f x ≡ f k)
    → subst (λ y → (f x ∷ map f xs) ↭ y ∷ map f xs) pf' Perm.refl
      ≡ PermProp.map⁺ f (subst (λ y → (x ∷ xs) ↭ y ∷ xs) pf Perm.refl)
  map⁺-subst xs refl pf' rewrite Decidable⇒UIP.≡-irrelevant _≟_ pf' refl = refl

  extract-elem-map⁺
    : ∀ (k : Fin n) (xs rest : List (Fin n)) (p : xs ↭ k ∷ rest)
    → extract-elem k xs ≡ just (rest , p)
    → extract-elem (f k) (map f xs) ≡ just (map f rest , PermProp.map⁺ f p)
  extract-elem-map⁺ k []       rest p ()
  extract-elem-map⁺ k (x ∷ xs) rest p eq with x ≟ k
  extract-elem-map⁺ k (x ∷ xs) rest p eq | yes pf with eq
  ... | refl with f x ≟ f k
  ...   | yes pf' = cong (λ d → just (map f xs , d)) (map⁺-subst xs pf pf')
  ...   | no ¬pf' = ⊥-elim (¬pf' (cong f pf))
  extract-elem-map⁺ k (x ∷ xs) rest p eq | no ¬xk
      with extract-elem k xs in eq-inner
  ... | nothing with eq
  ...   | ()
  extract-elem-map⁺ k (x ∷ xs) rest p eq | no ¬xk
      | just (rest' , p') with eq
  ... | refl with f x ≟ f k
  ...   | yes fxk = ⊥-elim (¬xk (f-inj fxk))
  ...   | no _ rewrite extract-elem-map⁺ k xs rest' p' eq-inner = refl

  extract-prefix-map⁺
    : ∀ (ks xs rest : List (Fin n)) (p : xs ↭ ks ++ rest)
    → extract-prefix ks xs ≡ just (rest , p)
    → extract-prefix (map f ks) (map f xs)
      ≡ just (map f rest ,
              subst (λ z → map f xs ↭ z) (map-++ f ks rest) (PermProp.map⁺ f p))
  extract-prefix-map⁺ []       xs rest p eq with eq
  ... | refl = refl
  extract-prefix-map⁺ (k ∷ ks) xs rest p eq with extract-elem k xs in eq-elem
  ... | nothing with eq
  ...   | ()
  extract-prefix-map⁺ (k ∷ ks) xs rest p eq | just (xs' , p-e)
      with extract-prefix ks xs' in eq-pre
  ...   | nothing with eq
  ...     | ()
  extract-prefix-map⁺ (k ∷ ks) xs rest p eq | just (xs' , p-e)
      | just (rest' , q-pre) with eq
  ...     | refl
            rewrite extract-elem-map⁺ k xs xs' p-e eq-elem
                  | extract-prefix-map⁺ ks xs' rest' q-pre eq-pre =
            cong (λ d → just (map f rest' , d))
              (sym (push-subst-cons (PermProp.map⁺ f p-e) (PermProp.map⁺ f q-pre)
                                    (map-++ f ks rest')))

  extract-prefix-pin
    : ∀ (ks xs rest : List (Fin n))
        (permH : xs ↭ ks ++ rest)
        (permJ : map f xs ↭ map f ks ++ map f rest)
    → extract-prefix ks xs ≡ just (rest , permH)
    → extract-prefix (map f ks) (map f xs) ≡ just (map f rest , permJ)
    → permJ ≡ subst (λ z → map f xs ↭ z) (map-++ f ks rest)
                    (PermProp.map⁺ f permH)
  extract-prefix-pin ks xs rest permH permJ eqH eqJ =
    ,-injectiveʳ-UIP (≡-irrelevant _≟_)
      (just-injective
        (trans (sym eqJ) (extract-prefix-map⁺ ks xs rest permH eqH)))
