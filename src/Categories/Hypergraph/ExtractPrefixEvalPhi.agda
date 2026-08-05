{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The eval-coincidence behind `fire-perm-rel` (permute factor of Lemma 0b),
-- proved generically (no APROP, fast).
--
-- Given an injective vertex relabel `φ : Fin nH → Fin nJ` and two labellings
-- `vJ`, `vH` with `vJ ∘ φ ≗ vH`, the two `extract-prefix` search permutations
-- (one on the relabelled input) have the SAME evaluated finite bijection after
-- labelling:  `eval-↭ (map⁺ vJ permJ) ≡ eval-↭ (map⁺ vH permH)`.
--
-- Because `length (map g l) = length l` definitionally, the two `eval-↭`s have
-- the same `FinBij` type with no casts; the internal `length-map` casts from
-- `eval-map⁺` collapse via ℕ-UIP.  The search-naturality `extract-prefix-map⁺`
-- supplies `permJ = subst (map-++) (map⁺ φ permH)`, so the result is K-free.
--
-- §1 first proves that search naturality (`extract-prefix-map⁺`): the
-- `extract-elem`/`extract-prefix` search commutes with an injective
-- relabel `map f` at the DERIVATION level.
--------------------------------------------------------------------------------

module Categories.Hypergraph.ExtractPrefixEvalPhi where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-++; length-map; ≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Product.Properties using (,-injectiveʳ-UIP)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import Categories.Hypergraph.ExtractPrefix using (extract-elem; extract-prefix)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)

--------------------------------------------------------------------------------
-- §1.  φ-naturality of the search at the derivation level.

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


--------------------------------------------------------------------------------
-- `eval-map⁺` is imported from the canonical (K-free)
-- `PermuteCoherence.FinBijSubst` (re-exported `public` for downstream
-- consumers that imported it from here).

open import Categories.PermuteCoherence.FinBijSubst
  using ( eval-map⁺; _≈̂-fb_; ≈̂-fb-of-≡; ≈̂-fb-sym; _○-fb_; cast-≈̂-fb
        ; ≈̂-fb⇒≈-fb ) public

-- `eval-↭` of a codomain-`subst` is a `subst₂ FinBij refl (cong length _)`.
eval-subst-cod
  : ∀ {A : Set} {xs ys ys' : List A} (e : ys ≡ ys') (d : xs ↭ ys)
  → eval-↭ (subst (λ z → xs ↭ z) e d)
    ≡ subst₂ FinBij refl (cong length e) (eval-↭ d)
eval-subst-cod refl d = refl

-- `map⁺ h` commutes with a codomain-`subst`.
map⁺-subst-cod
  : ∀ {A C : Set} (h : A → C) {xs ys ys' : List A} (e : ys ≡ ys') (d : xs ↭ ys)
  → PermProp.map⁺ h (subst (λ z → xs ↭ z) e d)
    ≡ subst (λ z → map h xs ↭ z) (cong (map h) e) (PermProp.map⁺ h d)
map⁺-subst-cod h refl d = refl

--------------------------------------------------------------------------------

module _ {nH nJ : ℕ} {X : Set}
         (φ : Fin nH → Fin nJ) (φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y)
         (vJ : Fin nJ → X) (vH : Fin nH → X)
         (veq : ∀ v → vJ (φ v) ≡ vH v) where

  -- UIP on `List (Fin nJ)` (the residual type), via decidable equality.
  private
    listFin-uip : ∀ {x y : List (Fin nJ)} (p q : x ≡ y) → p ≡ q
    listFin-uip = Decidable⇒UIP.≡-irrelevant (≡-dec _≟_)

  -- The eval-coincidence, in the form `fire-perm-rel` consumes (the boundary
  -- list-equalities `dom-eq`/`cod-eq` are supplied; here they come from
  -- `vJ ∘ φ ≗ vH`).  Stated with `subst₂ FinBij` casts because, for a VARIABLE
  -- list, `length (map g l)` is a stuck neutral (NOT definitionally `length l`).
  eval-coincide
    : ∀ (ks xs rest : List (Fin nH))
        (permH : xs ↭ ks ++ rest)
        (permJ : map φ xs ↭ map φ ks ++ map φ rest)
        (dom-eq : map vJ (map φ xs) ≡ map vH xs)
        (cod-eq : map vJ (map φ ks ++ map φ rest) ≡ map vH (ks ++ rest))
    → extract-prefix ks xs ≡ just (rest , permH)
    → extract-prefix (map φ ks) (map φ xs) ≡ just (map φ rest , permJ)
    → subst₂ FinBij (cong length dom-eq) (cong length cod-eq)
        (eval-↭ (PermProp.map⁺ vJ permJ))
      ≈-fb eval-↭ (PermProp.map⁺ vH permH)
  eval-coincide ks xs rest permH permJ dom-eq cod-eq eqH eqJ =
    ≈̂-fb⇒≈-fb
      (cast-≈̂-fb (cong length dom-eq) (cong length cod-eq) _
        ○-fb chainJ
        ○-fb ≈̂-fb-sym (≈̂-fb-of-≡ (eval-map⁺ vH permH) ○-fb cast-≈̂-fb _ _ _))
    where
      mpp = map-++ φ ks rest

      permJ≡ : permJ
             ≡ subst (λ z → map φ xs ↭ z) mpp (PermProp.map⁺ φ permH)
      permJ≡ = ,-injectiveʳ-UIP listFin-uip
                 (just-injective
                   (trans (sym eqJ)
                          (extract-prefix-map⁺ φ φ-inj ks xs rest permH eqH)))

      -- `eval-↭ (map⁺ vJ permJ)` is `eval-↭ permH` up to casts: rewrite `permJ`,
      -- push `map⁺ vJ`/`eval-↭` through the codomain-`subst`, then drop each
      -- `length-map` cast `eval-map⁺` produces.
      chainJ : eval-↭ (PermProp.map⁺ vJ permJ) ≈̂-fb eval-↭ permH
      chainJ =
        ≈̂-fb-of-≡ (cong (λ d → eval-↭ (PermProp.map⁺ vJ d)) permJ≡)
          ○-fb ≈̂-fb-of-≡ (cong eval-↭ (map⁺-subst-cod vJ mpp (PermProp.map⁺ φ permH)))
          ○-fb ≈̂-fb-of-≡ (eval-subst-cod (cong (map vJ) mpp)
                            (PermProp.map⁺ vJ (PermProp.map⁺ φ permH)))
          ○-fb cast-≈̂-fb refl (cong length (cong (map vJ) mpp)) _
          ○-fb ≈̂-fb-of-≡ (eval-map⁺ vJ (PermProp.map⁺ φ permH))
          ○-fb cast-≈̂-fb _ _ _
          ○-fb ≈̂-fb-of-≡ (eval-map⁺ φ permH)
          ○-fb cast-≈̂-fb _ _ _
