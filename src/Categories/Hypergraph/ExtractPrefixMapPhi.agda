{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- φ-naturality of the `extract-elem` / `extract-prefix` search at the
-- DERIVATION level: running the search on an injectively-relabelled input
-- (`map f`) produces exactly the `map⁺ f`-image of the derivation produced on
-- the original input.
--
-- This is the generic, APROP-free core needed to discharge `fire-perm-rel`
-- (the permute/K factor of Lemma 0b): once the two search derivations are
-- related by `map⁺ f`, their evaluated bijections coincide by `eval-map⁺`, and
-- K closes the `≈Term` goal — no `Unique`ness / rigidity needed.
--
-- Lightweight module (only `ExtractPrefix` + stdlib) so it typechecks fast.
--------------------------------------------------------------------------------

module Categories.Hypergraph.ExtractPrefixMapPhi where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.List.Properties using (map-++)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (yes; no)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import Categories.Hypergraph.ExtractPrefix using (extract-elem; extract-prefix)

-- UIP on `Fin` (Hedberg; --without-K-safe via decidable equality).
fin-uip : ∀ {l} {a b : Fin l} (p q : a ≡ b) → p ≡ q
fin-uip {l} = Decidable⇒UIP.≡-irrelevant (_≟_ {l})

module _ {n m : ℕ} (f : Fin n → Fin m)
         (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y) where

  -- `map⁺ f` commutes with the head-relabel `subst _ pf Perm.refl` of
  -- `extract-elem`'s found-at-head branch.
  map⁺-subst
    : ∀ {x k : Fin n} (xs : List (Fin n)) (pf : x ≡ k) (pf' : f x ≡ f k)
    → subst (λ y → (f x ∷ map f xs) ↭ y ∷ map f xs) pf' Perm.refl
      ≡ PermProp.map⁺ f (subst (λ y → (x ∷ xs) ↭ y ∷ xs) pf Perm.refl)
  map⁺-subst xs refl pf' rewrite fin-uip pf' refl = refl

  -- `extract-elem` commutes with `map f` at the derivation level.
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

  -- subst over the codomain of `trans A (prep a B)` pushes into `B`
  -- (refl-pattern on the codomain equality).
  push-subst-cons
    : ∀ {xs V V' V'' : List (Fin m)} {a : Fin m}
        (A : xs ↭ a ∷ V) (B : V ↭ V') (e : V' ≡ V'')
    → subst (λ z → xs ↭ z) (cong (a ∷_) e) (Perm.trans A (Perm.prep a B))
      ≡ Perm.trans A (Perm.prep a (subst (λ z → V ↭ z) e B))
  push-subst-cons A B refl = refl

  -- `extract-prefix` commutes with `map f` at the derivation level (modulo the
  -- `map-++` identification of the residual codomain).
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
