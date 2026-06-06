{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Cross-iso (φ-equivariance) `subst Fin`/`lookup` cast algebra.
--
-- Originally this `--without-K` leaf hosted `--without-K` copies of the
-- FinBij / `eval-↭` rigidity lemmas that also live in `PermuteCoherence.
-- {Rigid,Map}`, because those were once `--with-K` and could not be
-- imported into the `--without-K` `…/Completeness/Discharge/…` consumers.
--
-- Now that `Rigid` and `Map` are themselves `--without-K`, the shared
-- lemmas (`eval-rigid`, `lookup-sound`, `eval-map⁺`) are imported from
-- there and re-exported `public`.  Only the genuinely-unique cast-algebra
-- lemmas (the `subst Fin` family + `lookup-map`/`lookup-subst-list`/
-- `eval-subst₂-↭`/`subst₂-FinBij-as-subst`) and the `Unique`-lookup
-- injectivity helpers (`Rigid` keeps those `private`) are defined locally.
--
-- Sole consumer: `…/Completeness/Discharge/IsoTransport.agda`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.EvalRigidKFree where

open import Categories.PermuteCoherence.FinBij using (FinBij)
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
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

-- Shared rigidity / map lemmas, now `--without-K` in their home modules.
open import Categories.PermuteCoherence.Rigid public
  using (lookup-sound; eval-rigid)
open import Categories.PermuteCoherence.Map public
  using (eval-map⁺)

------------------------------------------------------------------------
-- `Unique`-codomain injectivity helpers (kept `private` in `Rigid`).
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

------------------------------------------------------------------------
-- `subst Fin` cast algebra for the cross-iso (φ-equivariance) rigidity.
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

-- `eval-↭` commutes with `subst₂ _↭_` along list equalities.
eval-subst₂-↭
  : ∀ {a} {A : Set a} {xs xs' ys ys' : List A}
      (p : xs ≡ xs') (q : ys ≡ ys') (r : xs Perm.↭ ys)
  → eval-↭ (subst₂ Perm._↭_ p q r)
    ≡ subst₂ FinBij (cong length p) (cong length q) (eval-↭ r)
eval-subst₂-↭ refl refl r = refl

-- `subst₂ FinBij` re-expressed as a pair of single `subst Fin`-casts on
-- domain (precompose) and codomain (postcompose).
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
