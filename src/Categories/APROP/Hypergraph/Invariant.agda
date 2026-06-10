{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Invariants of APROP-translated hypergraphs.
--
-- The pruned `hCompose` relies on structural properties of the translation
-- that are universal but not captured by the `Hypergraph` record fields
-- alone (covering / uniqueness / dom≡cod of the identity and swap
-- hypergraphs, `range`-shape of `hId`'s dom, and Fin/cast bridging lemmas).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Invariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using
  ( splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; splitAt-↑ˡ; splitAt-↑ʳ
  ; cast-is-id; toℕ-cast; toℕ-injective; toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)
open import Relation.Binary.PropositionalEquality as PE using (cong; cong₂)

--------------------------------------------------------------------------------
-- For identity hypergraphs, `dom ≡ cod` as lists (every `hId` branch uses
-- the same Fin-list on both sides).

hId-cod≡dom : ∀ A → Hypergraph.cod (hId A) ≡ Hypergraph.dom (hId A)
hId-cod≡dom unit      = refl
hId-cod≡dom (Var x)   = refl
hId-cod≡dom (A ⊗₀ B)  =
  cong₂ _++_
    (cong (map (_↑ˡ Hypergraph.nV (hId B))) (hId-cod≡dom A))
    (cong (map (Hypergraph.nV (hId A) ↑ʳ_)) (hId-cod≡dom B))

--------------------------------------------------------------------------------
-- `Unique` for identity's dom.  The tensor case needs `map⁺` with inject+ /
-- raise injectivity on each side + `++⁺` with disjointness of their images.

-- injectivity of inject+ and raise.  Public: used by `HomTermInvariant`.
inject+-inj : ∀ {m} (n : ℕ) {i j : Fin m}
            → i ↑ˡ n ≡ j ↑ˡ n → i ≡ j
inject+-inj {m} n {i} {j} eq with
  splitAt-↑ˡ m i n | splitAt-↑ˡ m j n | cong (splitAt m) eq
... | i-red | j-red | split-eq =
  inj₁-inj (trans (sym i-red) (trans split-eq j-red))
  where
    inj₁-inj : ∀ {X Y : Set} {x y : X} → inj₁ {B = Y} x ≡ inj₁ y → x ≡ y
    inj₁-inj refl = refl

raise-inj : ∀ (m : ℕ) {n} {i j : Fin n}
          → m ↑ʳ i ≡ m ↑ʳ j → i ≡ j
raise-inj m {n} {i} {j} eq with
  splitAt-↑ʳ m n i | splitAt-↑ʳ m n j | cong (splitAt m) eq
... | i-red | j-red | split-eq =
  inj₂-inj (trans (sym i-red) (trans split-eq j-red))
  where
    inj₂-inj : ∀ {X Y : Set} {x y : Y} → inj₂ {A = X} x ≡ inj₂ y → x ≡ y
    inj₂-inj refl = refl

-- map inject+ and map raise produce disjoint lists: a common `v` would
-- force `splitAt m v` to be both `inj₁` and `inj₂`.
disj-L-R : ∀ {m n} (xs : List (Fin m)) (ys : List (Fin n))
         → Disjoint (map (_↑ˡ n) xs) (map (m ↑ʳ_) ys)
disj-L-R {m} {n} xs ys {v} (v∈L , v∈R)
  with ∈-map⁻ (_↑ˡ n) v∈L | ∈-map⁻ (m ↑ʳ_) v∈R
... | vL , _ , v≡L | vR , _ , v≡R
  = case-absurd (trans (sym sp-L) sp-R)
  where
    sp-L : splitAt m v ≡ inj₁ vL
    sp-L = trans (cong (splitAt m) v≡L) (splitAt-↑ˡ m vL n)

    sp-R : splitAt m v ≡ inj₂ vR
    sp-R = trans (cong (splitAt m) v≡R) (splitAt-↑ʳ m n vR)

    case-absurd : ∀ {ℓ} {X : Set ℓ} → inj₁ {B = Fin n} vL ≡ inj₂ vR → X
    case-absurd ()

hId-dom-Unique : ∀ A → Unique (Hypergraph.dom (hId A))
hId-dom-Unique unit     = AllPairs.[]
  where import Data.List.Relation.Unary.AllPairs as AllPairs
hId-dom-Unique (Var x)  = All.[] AllPairs.∷ AllPairs.[]
  where
    import Data.List.Relation.Unary.AllPairs as AllPairs
    import Data.List.Relation.Unary.All       as All
hId-dom-Unique (A ⊗₀ B) =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj (Hypergraph.nV (hId B))) (hId-dom-Unique A))
    (Uniq-Prop.map⁺ (raise-inj   (Hypergraph.nV (hId A))) (hId-dom-Unique B))
    (disj-L-R (Hypergraph.dom (hId A)) (Hypergraph.dom (hId B)))

-- Symmetric version for cod.
hId-cod-Unique : ∀ A → Unique (Hypergraph.cod (hId A))
hId-cod-Unique A = subst Unique (sym (hId-cod≡dom A)) (hId-dom-Unique A)

--------------------------------------------------------------------------------
-- Unique witnesses for `range n` and for `hSwap` / `hGen`.

import Data.List.Relation.Unary.All        as ListAll
import Data.List.Relation.Unary.AllPairs   as AllPairs
import Data.Fin                            as Fin
open import Relation.Binary.PropositionalEquality using (_≢_)

private
  all-≢-zero : ∀ {n} (xs : List (Fin n))
             → ListAll.All (Fin.zero {n = n} ≢_) (map Fin.suc xs)
  all-≢-zero []       = ListAll.[]
  all-≢-zero (x ∷ xs) = (λ ()) ListAll.∷ all-≢-zero xs

  fin-suc-inj : ∀ {n} {i j : Fin n} → Fin.suc i ≡ Fin.suc j → i ≡ j
  fin-suc-inj refl = refl

range-Unique : ∀ n → Unique (range n)
range-Unique 0             = AllPairs.[]
range-Unique (suc n)  =
  all-≢-zero (range n)
    AllPairs.∷ Uniq-Prop.map⁺ fin-suc-inj (range-Unique n)

hSwap-dom-Unique : ∀ A B → Unique (Hypergraph.dom (hSwap A B))
hSwap-dom-Unique A B =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _))
    (Uniq-Prop.map⁺ (raise-inj   _) (range-Unique _))
    (disj-L-R (range (length (flatten A))) (range (length (flatten B))))

-- hSwap's cod is dom with the two halves swapped.
hSwap-cod-Unique : ∀ A B → Unique (Hypergraph.cod (hSwap A B))
hSwap-cod-Unique A B =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (raise-inj   _) (range-Unique _))
    (Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _))
    (disj-R-L (range (length (flatten B))) (range (length (flatten A))))
  where
    disj-R-L : ∀ {m n} (ys : List (Fin n)) (xs : List (Fin m))
             → Disjoint (map (m ↑ʳ_) ys) (map (_↑ˡ n) xs)
    disj-R-L ys xs (v∈R , v∈L) = disj-L-R xs ys (v∈L , v∈R)

hGen-dom-Unique : ∀ {A B : ObjTerm} (f : mor A B) → Unique (Hypergraph.dom (hGen f))
hGen-dom-Unique {A} f = Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _)

hGen-cod-Unique : ∀ {A B : ObjTerm} (f : mor A B) → Unique (Hypergraph.cod (hGen f))
hGen-cod-Unique {A} f = Uniq-Prop.map⁺ (raise-inj _) (range-Unique _)

--------------------------------------------------------------------------------
-- `(hId A).nV ≡ length (flatten A)` — propositionally only (the tensor case
-- needs `length-++`).

open import Data.List using (lookup)
open import Data.Fin using (cast)
open import Data.List.Properties using (length-++)
open import Data.Nat.Properties using (+-suc)
open import Data.Sum using ([_,_]′; _⊎_)

hId-nV≡len-flatten : ∀ A → Hypergraph.nV (hId A) ≡ length (flatten A)
hId-nV≡len-flatten unit     = refl
hId-nV≡len-flatten (Var x)  = refl
hId-nV≡len-flatten (A ⊗₀ B) =
  trans (cong₂ _+_ (hId-nV≡len-flatten A) (hId-nV≡len-flatten B))
        (sym (length-++ (flatten A)))

--------------------------------------------------------------------------------
-- For an identity, `vlab` agrees with `lookup (flatten A)` pointwise, via a
-- Fin.cast bridging the `(hId A).nV ≡ length (flatten A)` gap.  Needed by
-- `σ∘σ-sound`.

private
  -- lookup through _++_ via inject+/raise, with a Fin.cast absorbing
  -- `length (xs ++ ys) ≡ length xs + length ys`.
  cast-inj+
    : ∀ {A : Set} (xs ys : List A) (i : Fin (length xs))
    → Fin (length (xs ++ ys))
  cast-inj+ xs ys i = cast (sym (length-++ xs)) (i ↑ˡ length ys)

  cast-rai+
    : ∀ {A : Set} (xs ys : List A) (j : Fin (length ys))
    → Fin (length (xs ++ ys))
  cast-rai+ xs ys j = cast (sym (length-++ xs)) (length xs ↑ʳ j)

  lookup-++-inj
    : ∀ {A : Set} (xs ys : List A) (i : Fin (length xs))
    → lookup (xs ++ ys) (cast-inj+ xs ys i) ≡ lookup xs i
  lookup-++-inj []       ys ()
  lookup-++-inj (x ∷ xs) ys zero    = refl
  lookup-++-inj (x ∷ xs) ys (suc i) = lookup-++-inj xs ys i

  lookup-++-rai
    : ∀ {A : Set} (xs ys : List A) (j : Fin (length ys))
    → lookup (xs ++ ys) (cast-rai+ xs ys j) ≡ lookup ys j
  lookup-++-rai []       ys j = cong (lookup ys) (cast-is-id refl j)
  lookup-++-rai (x ∷ xs) ys j = lookup-++-rai xs ys j

-- Two-variable `cong₂` form (pattern-match both eqs as refl, then
-- `cast-is-id` cancels the residual casts).
cast-inject+-cong₂
  : ∀ {mA mA' mB mB'} (eq-A : mA ≡ mA') (eq-B : mB ≡ mB') (i : Fin mA)
  → cast (cong₂ _+_ eq-A eq-B) (i ↑ˡ mB)
  ≡ cast eq-A i ↑ˡ mB'
cast-inject+-cong₂ refl refl i =
  trans (cast-is-id refl (i ↑ˡ _))
        (cong (_↑ˡ _) (sym (cast-is-id refl i)))

cast-raise-cong₂
  : ∀ {mA mA' mB mB'} (eq-A : mA ≡ mA') (eq-B : mB ≡ mB') (j : Fin mB)
  → cast (cong₂ _+_ eq-A eq-B) (mA ↑ʳ j)
  ≡ mA' ↑ʳ cast eq-B j
cast-raise-cong₂ refl refl j =
  trans (cast-is-id refl (_ ↑ʳ j))
        (cong (_ ↑ʳ_) (sym (cast-is-id refl j)))

-- The main lemma.
hId-vlab-lookup
  : ∀ A (i : Fin (Hypergraph.nV (hId A)))
  → Hypergraph.vlab (hId A) i
  ≡ lookup (flatten A) (cast (hId-nV≡len-flatten A) i)
hId-vlab-lookup unit     ()
hId-vlab-lookup (Var x)  zero = refl
hId-vlab-lookup (A ⊗₀ B) i
  with splitAt (Hypergraph.nV (hId A)) i in eq
... | inj₁ a = trans (hId-vlab-lookup A a) lookup-eq
  where
    open import Data.Fin.Properties using (cast-trans)

    eq-A : Hypergraph.nV (hId A) ≡ length (flatten A)
    eq-A = hId-nV≡len-flatten A

    eq-B : Hypergraph.nV (hId B) ≡ length (flatten B)
    eq-B = hId-nV≡len-flatten B

    eq-++ : length (flatten A) + length (flatten B) ≡ length (flatten A ++ flatten B)
    eq-++ = sym (length-++ (flatten A))

    i≡injL : i ≡ a ↑ˡ Hypergraph.nV (hId B)
    i≡injL = sym (splitAt⁻¹-↑ˡ eq)

    cast-form
      : cast (hId-nV≡len-flatten (A ⊗₀ B)) i
      ≡ cast-inj+ (flatten A) (flatten B) (cast eq-A a)
    cast-form =
      trans (cong (cast _) i≡injL)
      (trans (sym (cast-trans (cong₂ _+_ eq-A eq-B) eq-++ (a ↑ˡ _)))
             (cong (cast eq-++) (cast-inject+-cong₂ eq-A eq-B a)))

    lookup-eq
      : lookup (flatten A) (cast eq-A a)
      ≡ lookup (flatten A ++ flatten B) (cast (hId-nV≡len-flatten (A ⊗₀ B)) i)
    lookup-eq =
      trans (sym (lookup-++-inj (flatten A) (flatten B) _))
            (cong (lookup (flatten A ++ flatten B)) (sym cast-form))
... | inj₂ b = trans (hId-vlab-lookup B b) lookup-eq
  where
    open import Data.Fin.Properties using (cast-trans)

    eq-A : Hypergraph.nV (hId A) ≡ length (flatten A)
    eq-A = hId-nV≡len-flatten A

    eq-B : Hypergraph.nV (hId B) ≡ length (flatten B)
    eq-B = hId-nV≡len-flatten B

    eq-++ : length (flatten A) + length (flatten B) ≡ length (flatten A ++ flatten B)
    eq-++ = sym (length-++ (flatten A))

    i≡raise : i ≡ Hypergraph.nV (hId A) ↑ʳ b
    i≡raise = sym (splitAt⁻¹-↑ʳ eq)

    cast-form
      : cast (hId-nV≡len-flatten (A ⊗₀ B)) i
      ≡ cast-rai+ (flatten A) (flatten B) (cast eq-B b)
    cast-form =
      trans (cong (cast _) i≡raise)
      (trans (sym (cast-trans (cong₂ _+_ eq-A eq-B) eq-++ (_ ↑ʳ b)))
             (cong (cast eq-++) (cast-raise-cong₂ eq-A eq-B b)))

    lookup-eq
      : lookup (flatten B) (cast eq-B b)
      ≡ lookup (flatten A ++ flatten B) (cast (hId-nV≡len-flatten (A ⊗₀ B)) i)
    lookup-eq =
      trans (sym (lookup-++-rai (flatten A) (flatten B) _))
            (cong (lookup (flatten A ++ flatten B)) (sym cast-form))

--------------------------------------------------------------------------------
-- `range` splits along `_+_`:
--   range (n + m) ≡ map (inject+ m) (range n) ++ map (raise n) (range m)

range-++ : ∀ (n m : ℕ)
         → range (n + m) ≡ map (_↑ˡ m) (range n) ++ map (n ↑ʳ_) (range m)
range-++ zero    m = trans (sym (map-id (range m)))
                           (sym (map-cong (λ _ → refl) (range m)))
  where open import Data.List.Properties using (map-id; map-cong)
range-++ (suc n) m = cong (zero ∷_)
  (trans (cong (map Fin.suc) (range-++ n m))
  (trans (map-++ Fin.suc (map (_↑ˡ m) (range n)) (map (n ↑ʳ_) (range m)))
         (cong₂ _++_
           (trans (sym (map-∘ (range n)))
           (trans (map-cong (λ _ → refl) (range n))
                  (map-∘ (range n))))
           (sym (map-∘ (range m))))))
  where
    open import Data.List.Properties using (map-++; map-∘; map-cong)
    import Data.Fin as Fin

--------------------------------------------------------------------------------
-- `(hId A).dom` is exactly `range (hId A).nV`.  Used by `σ∘σ-sound`.

hId-dom≡range : ∀ A → Hypergraph.dom (hId A) ≡ range (Hypergraph.nV (hId A))
hId-dom≡range unit     = refl
hId-dom≡range (Var x)  = refl
hId-dom≡range (A ⊗₀ B) =
  trans (cong₂ _++_
          (cong (map (_↑ˡ Hypergraph.nV (hId B))) (hId-dom≡range A))
          (cong (map (Hypergraph.nV (hId A) ↑ʳ_)) (hId-dom≡range B)))
        (sym (range-++ (Hypergraph.nV (hId A)) (Hypergraph.nV (hId B))))
