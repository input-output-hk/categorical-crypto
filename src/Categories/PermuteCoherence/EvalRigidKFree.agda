{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Shared `--without-K` FinBij / `eval-↭` rigidity infrastructure.
--
-- These are the intrinsically K-free, J-only lemmas that *also* live in
-- the `--with-K` modules `Categories.PermuteCoherence.{Rigid,Map}`.
-- Co-infectivity forbids importing those `--with-K` modules into the
-- `--without-K` consumers in `…/Completeness/Discharge/…`, so the helpers
-- were previously re-derived VERBATIM in three of them
-- (`IsoTransport`, `SwapStep`, `DecodeOrdBoundary`).
--
-- This module hosts the UNION of those three inlined copies once, as a
-- `--without-K` leaf depending only on stdlib + `PermuteCoherence.{FinBij,
-- Eval}`.  It is APROP-agnostic (NOT sig-parameterised): every lemma is
-- generic over `FinBij`/`eval-↭`/stdlib lists, so it lives next to
-- `FinBij`/`Eval`, not under `APROP`.
--
-- Contents (the IsoTransport superset):
--   * rigidity:   `All-lookup`, `lookup-injective-unique`,
--                 `lookup-sound`, `eval-rigid`;
--   * `subst Fin`/`lookup` algebra:  `subst-Fin-sym-suc`,
--                 `subst-Fin-sym-zero`, `lookup-map`, `eval-subst₂-↭`,
--                 `subst₂-FinBij-as-subst`, `cast-irr`, `subst-Fin-trans`,
--                 `lookup-subst-list`, `subst-Fin-roundtrip`,
--                 `subst-Fin-roundtrip'`, `subst-Fin-sym-sym`;
--   * `eval-map⁺` + its `subst₂`-on-FinBij algebra:  `subst₂-FinBij-id`,
--                 `cons-cast`, `swap-cast`, `comp-cast`, `eval-map⁺`,
--                 `subst₂-FinBij-≈`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.EvalRigidKFree where

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; cons-fb; swap-fb; _∘-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
import Data.Fin.Permutation as P
open import Data.List using (List; []; _∷_; map; length; lookup)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᵘ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

------------------------------------------------------------------------
-- Rigidity of `eval-↭` on `Unique` codomains (copy of
-- `PermuteCoherence.Rigid.eval-rigid`; structural, no K).
------------------------------------------------------------------------

All-lookup : ∀ {a p} {A : Set a} {Q : A → Set p} {xs : List A}
           → All Q xs → (i : Fin (length xs)) → Q (lookup xs i)
All-lookup (q ∷ _)  zero    = q
All-lookup (_ ∷ qs) (suc i) = All-lookup qs i

lookup-injective-unique
  : ∀ {a} {A : Set a} {xs : List A}
  → Unique xs → (i j : Fin (length xs))
  → lookup xs i ≡ lookup xs j
  → i ≡ j
lookup-injective-unique (_  ∷ᵘ _ ) zero    zero    _  = refl
lookup-injective-unique (x≢ ∷ᵘ _ ) zero    (suc j) eq = ⊥-elim (All-lookup x≢ j eq)
lookup-injective-unique (x≢ ∷ᵘ _ ) (suc i) zero    eq = ⊥-elim (All-lookup x≢ i (sym eq))
lookup-injective-unique (_  ∷ᵘ uq) (suc i) (suc j) eq =
  cong suc (lookup-injective-unique uq i j eq)

lookup-sound
  : ∀ {a} {A : Set a} {xs ys : List A} (p : xs Perm.↭ ys) (i : Fin (length xs))
  → lookup ys (eval-↭ p P.⟨$⟩ʳ i) ≡ lookup xs i
lookup-sound Perm.refl              i                  = refl
lookup-sound (Perm.prep x p)        zero               = refl
lookup-sound (Perm.prep x p)        (suc i)            = lookup-sound p i
lookup-sound (Perm.swap x y p)      zero               = refl
lookup-sound (Perm.swap x y p)      (suc zero)         = refl
lookup-sound (Perm.swap x y p)      (suc (suc i))      = lookup-sound p i
lookup-sound (Perm.trans p q)       i                  =
  trans (lookup-sound q (eval-↭ p P.⟨$⟩ʳ i)) (lookup-sound p i)

-- Rigidity of `eval-↭` on `Unique` codomains: any two derivations into
-- the same `Unique` list evaluate to the same finite bijection.
eval-rigid
  : ∀ {a} {A : Set a} {xs ys : List A} → Unique ys
  → (p q : xs Perm.↭ ys)
  → eval-↭ p ≈-fb eval-↭ q
eval-rigid uniq p q i =
  lookup-injective-unique uniq _ _
    (trans (lookup-sound p i) (sym (lookup-sound q i)))

------------------------------------------------------------------------
-- Extra K-free helpers for the CROSS-iso rigidity (φ-equivariance).
-- All are `refl`-matched on `Fin`/length proofs, so without-K clean.
------------------------------------------------------------------------

-- `subst Fin` along a `sym (cong suc _)` cast commutes with `suc`/`zero`.
subst-Fin-sym-suc
  : ∀ {n m : ℕ} (e : n ≡ m) (i : Fin m)
  → subst Fin (sym (cong suc e)) (suc i) ≡ suc (subst Fin (sym e) i)
subst-Fin-sym-suc refl i = refl

subst-Fin-sym-zero
  : ∀ {n m : ℕ} (e : n ≡ m)
  → subst Fin (sym (cong suc e)) zero ≡ zero
subst-Fin-sym-zero refl = refl

-- `lookup` commutes with `map`, the index transported along `length-map`.
lookup-map
  : ∀ {A B : Set} (g : A → B) (xs : List A)
      (i : Fin (length xs))
  → lookup (map g xs) (subst Fin (sym (length-map g xs)) i) ≡ g (lookup xs i)
lookup-map g (x ∷ xs) zero =
  cong (lookup (map g (x ∷ xs))) (subst-Fin-sym-zero (length-map g xs))
lookup-map g (x ∷ xs) (suc i) =
  trans (cong (lookup (map g (x ∷ xs))) (subst-Fin-sym-suc (length-map g xs) i))
        (lookup-map g xs i)

-- `eval-↭` commutes with `subst₂ _↭_` along list equalities, matched at
-- `refl` (without-K clean).
eval-subst₂-↭
  : ∀ {a} {A : Set a} {xs xs' ys ys' : List A}
      (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
  → eval-↭ (subst₂ Perm._↭_ p q r)
    ≡ subst₂ FinBij (cong length p) (cong length q) (eval-↭ r)
eval-subst₂-↭ refl refl r = refl

-- `subst₂ FinBij` re-expressed as a pair of single `subst Fin`-casts on
-- domain (precompose) and codomain (postcompose), matched at `refl`.
subst₂-FinBij-as-subst
  : ∀ {n n' m m'} (a : n ≡ n') (b : m ≡ m') (π : FinBij n m) (i : Fin n')
  → (subst₂ FinBij a b π) P.⟨$⟩ʳ i
    ≡ subst Fin b (π P.⟨$⟩ʳ subst Fin (sym a) i)
subst₂-FinBij-as-subst refl refl π i = refl

-- ℕ-equality is irrelevant (UIP from decidability), so `subst Fin` does
-- not depend on the *proof* of a length equality, only its endpoints.
cast-irr
  : ∀ {n m : ℕ} (e e' : n ≡ m) (i : Fin n)
  → subst Fin e i ≡ subst Fin e' i
cast-irr e e' i = cong (λ z → subst Fin z i) (ℕ-≡-irrelevant e e')
  where open import Data.Nat.Properties using () renaming (≡-irrelevant to ℕ-≡-irrelevant)

-- Two nested `subst Fin`-casts collapse to a single one (matched at refl).
subst-Fin-trans
  : ∀ {n m k : ℕ} (e : n ≡ m) (e' : m ≡ k) (i : Fin n)
  → subst Fin e' (subst Fin e i) ≡ subst Fin (trans e e') i
subst-Fin-trans refl refl i = refl

-- `lookup` along a list equality: transporting the index by the
-- `cong length`-cast of `e : xs ≡ ys` re-indexes `ys` to agree with `xs`.
lookup-subst-list
  : ∀ {a} {A : Set a} {xs ys : List A} (e : xs ≡ ys) (k : Fin (length xs))
  → lookup ys (subst Fin (cong length e) k) ≡ lookup xs k
lookup-subst-list refl k = refl

-- A `subst Fin` round-trip (cast then inverse cast) is the identity.
subst-Fin-roundtrip
  : ∀ {n m : ℕ} (e : n ≡ m) (i : Fin n)
  → subst Fin (sym e) (subst Fin e i) ≡ i
subst-Fin-roundtrip refl i = refl

-- The other-direction round-trip:  `subst Fin e ∘ subst Fin (sym e) = id`.
subst-Fin-roundtrip'
  : ∀ {n m : ℕ} (e : n ≡ m) (i : Fin m)
  → subst Fin e (subst Fin (sym e) i) ≡ i
subst-Fin-roundtrip' refl i = refl

-- `subst Fin (sym (sym e)) = subst Fin e` (cast-irr, since `sym (sym e)`
-- and `e` have the same endpoints).
subst-Fin-sym-sym
  : ∀ {n m : ℕ} (e : n ≡ m) (i : Fin n)
  → subst Fin (sym (sym e)) i ≡ subst Fin e i
subst-Fin-sym-sym e i = cast-irr (sym (sym e)) e i

------------------------------------------------------------------------
-- `eval-map⁺` and its `subst₂`-on-FinBij algebra (copies of the
-- `--with-K` `PermuteCoherence.Map` lemmas; all J-only, no K).
------------------------------------------------------------------------

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

subst₂-FinBij-≈ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') {π ρ : FinBij n m}
  → π ≈-fb ρ → subst₂ FinBij a b π ≈-fb subst₂ FinBij a b ρ
subst₂-FinBij-≈ refl refl eq = eq
