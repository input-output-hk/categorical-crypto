{-# OPTIONS --safe --without-K #-}

module Categories.PermuteCoherence.FinBijSubst where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using (List; _∷_; length; lookup; map)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.Fin.Permutation as P

open import Data.Product using (Σ-syntax; _,_)
open import Data.Nat.Properties using () renaming (≡-irrelevant to ℕ-≡-irrelevant)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Level using (Level)

private
  variable
    a c : Level
    A : Set a
    C : Set c

-- J-lemmas about subst₂ on FinBij.
subst₂-FinBij-id : ∀ {n m} (e : n ≡ m) → subst₂ FinBij e e id-fb ≡ id-fb
subst₂-FinBij-id refl = refl

cons-fb-subst₂ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') (π : FinBij n m)
  → cons-fb (subst₂ FinBij a b π) ≡ subst₂ FinBij (cong suc a) (cong suc b) (cons-fb π)
cons-fb-subst₂ refl refl π = refl

swap-fb-subst₂ : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') (π : FinBij n m)
  → cons-fb (cons-fb (subst₂ FinBij a b π))
    ≡ subst₂ FinBij (cong (λ z → suc (suc z)) a) (cong (λ z → suc (suc z)) b)
        (cons-fb (cons-fb π))
swap-fb-subst₂ refl refl π = refl

-- subst₂ is proof-irrelevant: it depends only on the proof's value.
-- (Needed to reconcile `length-map h (x∷xs)`'s `cong suc`-shaped proof
-- with the `sym`-shaped proof our recursion produces.)
subst₂-FinBij-irr : ∀ {n m n' m'} (a a' : n ≡ n') (b b' : m ≡ m') (π : FinBij n m)
  → a ≡ a' → b ≡ b' → subst₂ FinBij a b π ≡ subst₂ FinBij a' b' π
subst₂-FinBij-irr a a' b b' π refl refl = refl

sym-cong-suc : ∀ {n m} (e : n ≡ m) → sym (cong suc e) ≡ cong suc (sym e)
sym-cong-suc refl = refl

sym-cong-ss : ∀ {n m} (e : n ≡ m)
  → sym (cong suc (cong suc e)) ≡ cong (λ z → suc (suc z)) (sym e)
sym-cong-ss refl = refl

∘-fb-subst₂ : ∀ {n m k n' m' k'} (a : n ≡ n') (b : m ≡ m') (cc : k ≡ k')
  (g : FinBij m k) (f : FinBij n m)
  → subst₂ FinBij b cc g ∘-fb subst₂ FinBij a b f
    ≡ subst₂ FinBij a cc (g ∘-fb f)
∘-fb-subst₂ refl refl refl g f = refl

swap-gen-subst₂ : ∀ {n n'} (a : n ≡ n')
  → swap-fb n' ≡ subst₂ FinBij (cong (λ z → suc (suc z)) a) (cong (λ z → suc (suc z)) a) (swap-fb n)
swap-gen-subst₂ refl = refl

eval-map⁺ : (h : A → C) {xs ys : List A} (p : xs ↭ ys)
  → eval-↭ (PermProp.map⁺ h p)
    ≡ subst₂ FinBij (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p)
eval-map⁺ h {xs = xs} Perm.refl = sym (subst₂-FinBij-id (sym (length-map h xs)))
eval-map⁺ h {xs = x ∷ xs} {ys = .x ∷ ys} (Perm.prep x p) =
  trans (cong cons-fb (eval-map⁺ h p))
  (trans (cons-fb-subst₂ (sym (length-map h xs)) (sym (length-map h ys)) (eval-↭ p))
         (subst₂-FinBij-irr
            (cong suc (sym (length-map h xs))) (sym (length-map h (x ∷ xs)))
            (cong suc (sym (length-map h ys))) (sym (length-map h (x ∷ ys)))
            (cons-fb (eval-↭ p))
            (sym (sym-cong-suc (length-map h xs)))
            (sym (sym-cong-suc (length-map h ys)))))
eval-map⁺ h {xs = x ∷ x' ∷ xs} {ys = y ∷ y' ∷ ys} (Perm.swap x y p) =
  trans (cong (λ z → swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb z)) (eval-map⁺ h p))
  (trans goal
         (subst₂-FinBij-irr
            (ss aa) (sym (length-map h (x ∷ x' ∷ xs)))
            (ss bb) (sym (length-map h (y ∷ y' ∷ ys)))
            (swap-fb (length ys) ∘-fb cons-fb (cons-fb (eval-↭ p)))
            (sym (sym-cong-ss (length-map h xs)))
            (sym (sym-cong-ss (length-map h ys)))))
  where
    aa = sym (length-map h xs)
    bb = sym (length-map h ys)
    ss : ∀ {n m} → n ≡ m → suc (suc n) ≡ suc (suc m)
    ss = cong (λ z → suc (suc z))
    goal : swap-fb (length (map h ys)) ∘-fb cons-fb (cons-fb (subst₂ FinBij aa bb (eval-↭ p)))
         ≡ subst₂ FinBij (ss aa) (ss bb)
             (swap-fb (length ys) ∘-fb cons-fb (cons-fb (eval-↭ p)))
    goal =
      trans (cong (swap-fb (length (map h ys)) ∘-fb_) (swap-fb-subst₂ aa bb (eval-↭ p)))
      (trans (cong (_∘-fb subst₂ FinBij (ss aa) (ss bb) (cons-fb (cons-fb (eval-↭ p))))
                   (swap-gen-subst₂ bb))
             (∘-fb-subst₂ (ss aa) (ss bb) (ss bb) (swap-fb (length ys)) (cons-fb (cons-fb (eval-↭ p)))))
eval-map⁺ h {xs = xs} {ys = zs} (Perm.trans {ys = ys} p q) =
  trans (cong₂ _∘-fb_ (eval-map⁺ h q) (eval-map⁺ h p))
        (∘-fb-subst₂ (sym (length-map h xs)) (sym (length-map h ys)) (sym (length-map h zs)) (eval-↭ q) (eval-↭ p))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

------------------------------------------------------------------------
-- More generic eval lemmas.

-- eval commutes with subst on the codomain.
eval-subst-cod : {xs : List A} {C D : List A} (eq : C ≡ D) (p : xs ↭ C)
  → eval-↭ (subst (λ z → xs ↭ z) eq p)
    ≡ subst (λ n → FinBij (length xs) n) (cong length eq) (eval-↭ p)
eval-subst-cod refl p = refl

-- `≈-fb` from propositional equality of bijections.
≈-fb-of-≡ : ∀ {n m} {π ρ : FinBij n m} → π ≡ ρ → π ≈-fb ρ
≈-fb-of-≡ refl _ = refl

------------------------------------------------------------------------
-- Heterogeneous, cast-insensitive equality on `FinBij`.
--
-- `_≈̂-fb_` packages the two endpoint equalities so a chain never names them,
-- exactly as `_≈̂_` does for `HomS` in `FreeStrictSMC`: `cast-≈̂-fb` retires the
-- `subst₂ FinBij`-composition/irrelevance nests, `≈̂-fb⇒≈-fb` projects onto the
-- pointwise `_≈-fb_` at equal indices, and `≈̂-fb-app` (below) applies a chain
-- at an index with the CALLER's casts.  The residue is `_≡_`, not `_≈-fb_`:
-- every `FinBij`-level fact in the tree is an `_≡_`, and keeping it so is what
-- makes a chain's middle bijection *inferable* (behind `⟨$⟩ʳ` it is not).

infix 4 _≈̂-fb_
_≈̂-fb_ : ∀ {n m n' m'} → FinBij n m → FinBij n' m' → Set
_≈̂-fb_ {n} {m} {n'} {m'} π ρ =
  Σ[ a ∈ n ≡ n' ] Σ[ b ∈ m ≡ m' ] (subst₂ FinBij a b π ≡ ρ)

≈̂-fb-of-≡ : ∀ {n m} {π ρ : FinBij n m} → π ≡ ρ → π ≈̂-fb ρ
≈̂-fb-of-≡ e = refl , refl , e

≈̂-fb-refl : ∀ {n m} {π : FinBij n m} → π ≈̂-fb π
≈̂-fb-refl = ≈̂-fb-of-≡ refl

≈̂-fb-sym : ∀ {n m n' m'} {π : FinBij n m} {ρ : FinBij n' m'}
         → π ≈̂-fb ρ → ρ ≈̂-fb π
≈̂-fb-sym (refl , refl , e) = refl , refl , sym e

infixr 4 _○-fb_
_○-fb_ : ∀ {n m n' m' n'' m''} {π : FinBij n m} {ρ : FinBij n' m'}
           {τ : FinBij n'' m''}
       → π ≈̂-fb ρ → ρ ≈̂-fb τ → π ≈̂-fb τ
(refl , refl , e₁) ○-fb (refl , refl , e₂) = refl , refl , trans e₁ e₂

-- A cast is heterogeneously equal to its content.
cast-≈̂-fb : ∀ {n m n' m'} (a : n ≡ n') (b : m ≡ m') (π : FinBij n m)
          → subst₂ FinBij a b π ≈̂-fb π
cast-≈̂-fb refl refl π = ≈̂-fb-refl

-- At equal indices the endpoint proofs are `refl` by ℕ-UIP, so the
-- heterogeneous equality projects onto the homogeneous one.
≈̂-fb⇒≈-fb : ∀ {n m} {π ρ : FinBij n m} → π ≈̂-fb ρ → π ≈-fb ρ
≈̂-fb⇒≈-fb {π = π} (a , b , e) =
  ≈-fb-of-≡
    (trans (sym (subst₂-FinBij-irr a refl b refl π
                   (ℕ-≡-irrelevant a refl) (ℕ-≡-irrelevant b refl)))
           e)

------------------------------------------------------------------------
-- `subst Fin` cast algebra for the cross-iso (φ-equivariance) rigidity.
------------------------------------------------------------------------

-- `subst Fin` along a `sym (cong suc _)` cast commutes with `suc`/`zero`.
subst-Fin-sym-suc
  : ∀ {n m : ℕ} (e : n ≡ m) (i : Fin m)
  → subst Fin (sym (cong suc e)) (fsuc i) ≡ fsuc (subst Fin (sym e) i)
subst-Fin-sym-suc refl i = refl

subst-Fin-sym-zero
  : ∀ {n m : ℕ} (e : n ≡ m)
  → subst Fin (sym (cong suc e)) fzero ≡ fzero
subst-Fin-sym-zero refl = refl

-- `lookup` commutes with `map`, the index transported along `length-map`.
lookup-map
  : ∀ {A B : Set} (g : A → B) (xs : List A)
      (i : Fin (length xs))
  → lookup (map g xs) (subst Fin (sym (length-map g xs)) i) ≡ g (lookup xs i)
lookup-map g (x ∷ xs) fzero =
  cong (lookup (map g (x ∷ xs))) (subst-Fin-sym-zero (length-map g xs))
lookup-map g (x ∷ xs) (fsuc i) =
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

-- Two nested `subst Fin`-casts collapse to a single one (matched at refl).
subst-Fin-trans
  : ∀ {n m k : ℕ} (e : n ≡ m) (e' : m ≡ k) (i : Fin n)
  → subst Fin e' (subst Fin e i) ≡ subst Fin (trans e e') i
subst-Fin-trans refl refl i = refl

-- `lookup` across a `map`-relabelling, at an ARBITRARY length cast: if
-- `map g xs ≡ ys` then `lookup ys` factors as `g ∘ lookup xs`.  The cast is a
-- parameter — ℕ-UIP makes its proof irrelevant — so callers never reconcile
-- their own `length` proof with the one `lookup-map` produces.
lookup-relabel
  : ∀ {A B : Set} (g : A → B) {xs : List A} {ys : List B} (e : map g xs ≡ ys)
      (ln : length ys ≡ length xs) (k : Fin (length ys))
  → g (lookup xs (subst Fin ln k)) ≡ lookup ys k
lookup-relabel g {xs} refl ln k =
  trans (sym (lookup-map g xs (subst Fin ln k)))
        (cong (lookup (map g xs))
              (trans (subst-Fin-trans ln (sym (length-map g xs)) k)
                     (cast-irr (trans ln (sym (length-map g xs))) refl k)))

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

-- Applying a heterogeneous equality at an index: the two endpoint casts are
-- the CALLER's, not the ones the `≈̂-fb` proof happens to carry.  This is what
-- lets an index-level chase consume a cast-free `≈̂-fb` chain.
≈̂-fb-app
  : ∀ {n m n' m'} {π : FinBij n m} {ρ : FinBij n' m'}
  → π ≈̂-fb ρ → (a : n ≡ n') (b : m ≡ m') (i : Fin n)
  → subst Fin b (π P.⟨$⟩ʳ i) ≡ ρ P.⟨$⟩ʳ subst Fin a i
≈̂-fb-app {π = π} (a₀ , b₀ , e) a b i =
  trans (cast-irr b b₀ (π P.⟨$⟩ʳ i))
  (trans (cong (λ j → subst Fin b₀ (π P.⟨$⟩ʳ j))
               (sym (trans (subst-Fin-trans a (sym a₀) i)
                           (cast-irr (trans a (sym a₀)) refl i))))
  (trans (sym (subst₂-FinBij-as-subst a₀ b₀ π (subst Fin a i)))
         (cong (λ σ → σ P.⟨$⟩ʳ subst Fin a i) e)))
