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
--------------------------------------------------------------------------------

module Categories.Hypergraph.ExtractPrefixEvalPhi where

open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Fin using (Fin; _≟_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-++; length-map; ≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Product.Properties using (,-injectiveʳ-UIP)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import Categories.Hypergraph.ExtractPrefix using (extract-prefix)
open import Categories.Hypergraph.ExtractPrefixMapPhi using (extract-prefix-map⁺)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; cons-fb; swap-fb; _∘-fb_; ≈-fb-refl)

-- UIP on ℕ (Hedberg).
ℕ-uip : ∀ {a b : ℕ} (p q : a ≡ b) → p ≡ q
ℕ-uip = Decidable⇒UIP.≡-irrelevant _≟ℕ_

-- ≈-fb from ≡.
≈-fb-of-≡ : ∀ {n m} {π ρ : FinBij n m} → π ≡ ρ → π ≈-fb ρ
≈-fb-of-≡ {π = π} refl = ≈-fb-refl {π = π}

--------------------------------------------------------------------------------
-- K-free copies of the `eval-map⁺` / FinBij-`subst₂` algebra (the --with-K
-- `PermuteCoherence.Map` lemmas are J-only here, so re-derived; identical to
-- `IsoTransport` §0d).

subst₂-FinBij-id : ∀ {n m} (e : n ≡ m) → subst₂ FinBij e e id-fb ≡ id-fb
subst₂-FinBij-id refl = refl

cons-cast
  : ∀ {n n' m m'} (ex : n' ≡ n) (ey : m' ≡ m) (π : FinBij n m)
  → cons-fb (subst₂ FinBij (sym ex) (sym ey) π)
    ≡ subst₂ FinBij (sym (cong suc ex)) (sym (cong suc ey)) (cons-fb π)
cons-cast refl refl π = refl

swap-cast
  : ∀ {n n' m m'} (ex : n' ≡ n) (ey : m' ≡ m) (π : FinBij n m)
  → swap-fb m' ∘-fb cons-fb (cons-fb (subst₂ FinBij (sym ex) (sym ey) π))
    ≡ subst₂ FinBij (sym (cong suc (cong suc ex)))
                    (sym (cong suc (cong suc ey)))
                    (swap-fb m ∘-fb cons-fb (cons-fb π))
swap-cast refl refl π = refl

comp-cast
  : ∀ {n n' m m' k k'}
      (ex : n' ≡ n) (ey : m' ≡ m) (ez : k' ≡ k)
      (g : FinBij m k) (f : FinBij n m)
  → subst₂ FinBij (sym ey) (sym ez) g ∘-fb subst₂ FinBij (sym ex) (sym ey) f
    ≡ subst₂ FinBij (sym ex) (sym ez) (g ∘-fb f)
comp-cast refl refl refl g f = refl

eval-map⁺ : ∀ {a c} {A : Set a} {C : Set c}
  (h : A → C) {xs ys : List A} (p : xs Perm.↭ ys)
  → eval-↭ (PermProp.map⁺ h p)
    ≡ subst₂ FinBij (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p)
eval-map⁺ h {xs = xs} Perm.refl = sym (subst₂-FinBij-id (sym (length-map h xs)))
eval-map⁺ h {xs = x ∷ xs} {ys = .x ∷ ys} (Perm.prep x p) =
  trans (cong cons-fb (eval-map⁺ h p))
        (cons-cast (length-map h xs) (length-map h ys) (eval-↭ p))
eval-map⁺ h {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (Perm.swap x y p) =
  trans (cong (λ z → swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb z)) (eval-map⁺ h p))
        (swap-cast (length-map h xs) (length-map h ys) (eval-↭ p))
eval-map⁺ h {xs = xs} {ys = zs} (Perm.trans {ys = ys} p q) =
  trans (cong₂ _∘-fb_ (eval-map⁺ h q) (eval-map⁺ h p))
        (comp-cast (length-map h xs) (length-map h ys) (length-map h zs)
                   (eval-↭ q) (eval-↭ p))

-- A `subst₂ FinBij` whose two index-equalities are loops (`n ≡ n`) is the
-- identity (ℕ-UIP collapses them to `refl`).
cast-loop : ∀ {n m} (e : n ≡ n) (e' : m ≡ m) (π : FinBij n m) → subst₂ FinBij e e' π ≡ π
cast-loop e e' π rewrite ℕ-uip e refl | ℕ-uip e' refl = refl

-- Composition of two `subst₂ FinBij` casts.
subst₂-FinBij-∘
  : ∀ {n n' n'' m m' m''}
      (a : n ≡ n') (a' : n' ≡ n'') (b : m ≡ m') (b' : m' ≡ m'') (π : FinBij n m)
  → subst₂ FinBij a' b' (subst₂ FinBij a b π) ≡ subst₂ FinBij (trans a a') (trans b b') π
subst₂-FinBij-∘ refl refl refl refl π = refl

-- Any two `subst₂ FinBij` casts with the same endpoints agree (ℕ-UIP).
cast-irrel
  : ∀ {n n' m m'} (a a' : n ≡ n') (b b' : m ≡ m') (π : FinBij n m)
  → subst₂ FinBij a b π ≡ subst₂ FinBij a' b' π
cast-irrel a a' b b' π rewrite ℕ-uip a a' | ℕ-uip b b' = refl

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
    ≈-fb-of-≡
      (trans (cong (subst₂ FinBij (cong length dom-eq) (cong length cod-eq)) chainJ)
      (trans (subst₂-FinBij-∘ aJ (cong length dom-eq) bJ (cong length cod-eq) (eval-↭ permH))
      (trans (cast-irrel (trans aJ (cong length dom-eq)) (sym (length-map vH xs))
                         (trans bJ (cong length cod-eq)) (sym (length-map vH (ks ++ rest)))
                         (eval-↭ permH))
             (sym (eval-map⁺ vH permH)))))
    where
      permJ≡ : permJ
             ≡ subst (λ z → map φ xs ↭ z) (map-++ φ ks rest) (PermProp.map⁺ φ permH)
      permJ≡ = ,-injectiveʳ-UIP listFin-uip
                 (just-injective
                   (trans (sym eqJ)
                          (extract-prefix-map⁺ φ φ-inj ks xs rest permH eqH)))

      -- Domain/codomain endpoint equalities for the J-side single `subst₂`.
      aJ : length xs ≡ length (map vJ (map φ xs))
      aJ = trans (sym (length-map φ xs))
                 (sym (length-map vJ (map φ xs)))

      bJ : length (ks ++ rest) ≡ length (map vJ (map φ ks ++ map φ rest))
      bJ = trans (sym (length-map φ (ks ++ rest)))
                 (trans (cong length (map-++ φ ks rest))
                        (sym (length-map vJ (map φ ks ++ map φ rest))))

      -- `eval-↭ (map⁺ vJ permJ)` as a SINGLE `subst₂ FinBij` of `eval-↭ permH`.
      chainJ : eval-↭ (PermProp.map⁺ vJ permJ)
             ≡ subst₂ FinBij aJ bJ (eval-↭ permH)
      chainJ =
        trans (cong (λ d → eval-↭ (PermProp.map⁺ vJ d)) permJ≡)
        (trans (cong eval-↭ (map⁺-subst-cod vJ (map-++ φ ks rest) (PermProp.map⁺ φ permH)))
        (trans (eval-subst-cod (cong (map vJ) (map-++ φ ks rest))
                               (PermProp.map⁺ vJ (PermProp.map⁺ φ permH)))
        (trans (cong (subst₂ FinBij refl (cong length (cong (map vJ) (map-++ φ ks rest))))
                     (eval-map⁺ vJ (PermProp.map⁺ φ permH)))
        (trans (cong (subst₂ FinBij refl (cong length (cong (map vJ) (map-++ φ ks rest))))
                     (cong (subst₂ FinBij (sym (length-map vJ (map φ xs)))
                                          (sym (length-map vJ (map φ (ks ++ rest)))))
                           (eval-map⁺ φ permH)))
        (trans (cong (subst₂ FinBij refl (cong length (cong (map vJ) (map-++ φ ks rest))))
                     (subst₂-FinBij-∘ (sym (length-map φ xs)) (sym (length-map vJ (map φ xs)))
                                      (sym (length-map φ (ks ++ rest)))
                                      (sym (length-map vJ (map φ (ks ++ rest))))
                                      (eval-↭ permH)))
        (trans (subst₂-FinBij-∘
                  (trans (sym (length-map φ xs)) (sym (length-map vJ (map φ xs))))
                  refl
                  (trans (sym (length-map φ (ks ++ rest))) (sym (length-map vJ (map φ (ks ++ rest)))))
                  (cong length (cong (map vJ) (map-++ φ ks rest)))
                  (eval-↭ permH))
               (cast-irrel
                  (trans (trans (sym (length-map φ xs)) (sym (length-map vJ (map φ xs)))) refl)
                  aJ
                  (trans (trans (sym (length-map φ (ks ++ rest))) (sym (length-map vJ (map φ (ks ++ rest)))))
                         (cong length (cong (map vJ) (map-++ φ ks rest))))
                  bJ
                  (eval-↭ permH))))))))
