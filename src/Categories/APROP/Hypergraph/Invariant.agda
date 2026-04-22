{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Invariants of APROP-translated hypergraphs.
--
-- The canonical pruned `hCompose` (Option A) relies on structural properties
-- of the translation that are universal but not captured by the record
-- fields of `Hypergraph` alone. This module collects them.
--
-- CURRENT CONTENT:
--
--   * `hId-dom-covers A` — the identity hypergraph `hId A` has its `dom`
--     covering every vertex. Needed to show `count-non (hId A).dom ≡ 0`,
--     which lets the pruned `hComposeP (⟪f⟫) (hId B)` have the same vertex
--     count as `⟪f⟫` (key to discharging `idˡ`).
--
--   * `hId-cod-covers A` — the identity's `cod` also covers all vertices
--     (same proof, same structure).
--
--   * `hId-cod≡dom A` — for an identity, dom and cod are the SAME list.
--     Proved by induction on A. Needed for the pruned `idˡ-cod-helper`
--     where we want the G/K-side boundaries to align definitionally
--     after establishing the bijection.
--
--   * `hId-dom-Unique A` — the identity's dom is Unique. Proved by
--     induction on A, combining `map⁺` and `++⁺` on Unique lists.
--
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Invariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Categories.APROP.Hypergraph.Prune
  using (AllIn; count-non; AllIn→count-non-zero)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt)
open import Data.Fin.Properties using
  ( splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; splitAt-inject+; splitAt-raise
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
-- Helper: every vertex of `G + K` is in `map injL G-dom ++ map injR K-dom`
-- provided the two sides individually cover. Phrased generically on lists.

private
  tensor-covers : ∀ {m n : ℕ} (xs : List (Fin m)) (ys : List (Fin n))
                → (∀ i → i ∈ xs) → (∀ j → j ∈ ys)
                → (∀ v → v ∈ map (inject+ n) xs ++ map (raise m) ys)
  tensor-covers {m} {n} xs ys cov-x cov-y v with splitAt m v in eq
  ... | inj₁ i = subst (_∈ _) (splitAt⁻¹-↑ˡ eq)
                       (∈-++⁺ˡ (∈-map⁺ (inject+ n) (cov-x i)))
  ... | inj₂ j = subst (_∈ _) (splitAt⁻¹-↑ʳ eq)
                       (∈-++⁺ʳ (map (inject+ n) xs) (∈-map⁺ (raise m) (cov-y j)))

--------------------------------------------------------------------------------
-- hId's dom (and cod) cover all vertices.

hId-dom-covers : ∀ A → AllIn (Hypergraph.dom (hId A))
hId-cod-covers : ∀ A → AllIn (Hypergraph.cod (hId A))

hId-dom-covers unit      = λ ()
hId-dom-covers (Var x)   = λ { zero → here refl }
hId-dom-covers (A ⊗₀ B) v =
  tensor-covers (Hypergraph.dom (hId A)) (Hypergraph.dom (hId B))
                (hId-dom-covers A) (hId-dom-covers B) v

hId-cod-covers unit      = λ ()
hId-cod-covers (Var x)   = λ { zero → here refl }
hId-cod-covers (A ⊗₀ B) v =
  tensor-covers (Hypergraph.cod (hId A)) (Hypergraph.cod (hId B))
                (hId-cod-covers A) (hId-cod-covers B) v

--------------------------------------------------------------------------------
-- Immediate corollary: `count-non (hId A).dom ≡ 0`. With the pruned
-- `hComposeP`, this means `hComposeP G (hId B)` has the same vertex count
-- as `G` (up to `+-identityʳ`) — the cornerstone of `idˡ`.

hId-count-non-dom : ∀ A → count-non (Hypergraph.dom (hId A)) ≡ 0
hId-count-non-dom A = AllIn→count-non-zero (hId-dom-covers A)

hId-count-non-cod : ∀ A → count-non (Hypergraph.cod (hId A)) ≡ 0
hId-count-non-cod A = AllIn→count-non-zero (hId-cod-covers A)

--------------------------------------------------------------------------------
-- For identity hypergraphs, `dom ≡ cod` as lists (not just as types). This
-- mirrors the categorical fact that `id` is self-dual, and at the level of
-- the `hId` construction it holds because every branch uses the same
-- Fin-list on both sides.

hId-cod≡dom : ∀ A → Hypergraph.cod (hId A) ≡ Hypergraph.dom (hId A)
hId-cod≡dom unit      = refl
hId-cod≡dom (Var x)   = refl
hId-cod≡dom (A ⊗₀ B)  =
  cong₂ _++_
    (cong (map (inject+ (Hypergraph.nV (hId B)))) (hId-cod≡dom A))
    (cong (map (raise  (Hypergraph.nV (hId A)))) (hId-cod≡dom B))

--------------------------------------------------------------------------------
-- `Unique` for identity's dom. Used by `idˡ-cod-helper` to apply
-- `classify-lookup-Unique`.
--
-- The tensor case needs:
--   * map⁺ with inject+ injectivity     (left Unique).
--   * map⁺ with raise   injectivity     (right Unique).
--   * ++⁺ with disjointness of images   (inject+ and raise have disjoint ranges).

-- injectivity of inject+ and raise via splitAt reduction.
-- Public: used by `HomTermInvariant` to prove `⟪_⟫-dom-unique` for
-- `_∘_` and `_⊗₁_`.

inject+-inj : ∀ {m} (n : ℕ) {i j : Fin m}
            → inject+ n i ≡ inject+ n j → i ≡ j
inject+-inj {m} n {i} {j} eq with
  splitAt-inject+ m n i | splitAt-inject+ m n j | cong (splitAt m) eq
... | i-red | j-red | split-eq =
  inj₁-inj (trans (sym i-red) (trans split-eq j-red))
  where
    inj₁-inj : ∀ {X Y : Set} {x y : X} → inj₁ {B = Y} x ≡ inj₁ y → x ≡ y
    inj₁-inj refl = refl

raise-inj : ∀ (m : ℕ) {n} {i j : Fin n}
          → raise m i ≡ raise m j → i ≡ j
raise-inj m {n} {i} {j} eq with
  splitAt-raise m n i | splitAt-raise m n j | cong (splitAt m) eq
... | i-red | j-red | split-eq =
  inj₂-inj (trans (sym i-red) (trans split-eq j-red))
  where
    inj₂-inj : ∀ {X Y : Set} {x y : Y} → inj₂ {A = X} x ≡ inj₂ y → x ≡ y
    inj₂-inj refl = refl

-- map inject+ and map raise produce disjoint lists.
--   If v ∈ map (inject+ n) xs, then v = inject+ n vL for some vL ∈ xs,
--     hence splitAt m v = inj₁ vL.
--   If v ∈ map (raise m)  ys, then v = raise m vR for some vR ∈ ys,
--     hence splitAt m v = inj₂ vR.
--   These two splitAt results are both inj₁ and inj₂, contradiction.
disj-L-R : ∀ {m n} (xs : List (Fin m)) (ys : List (Fin n))
         → Disjoint (map (inject+ n) xs) (map (raise m) ys)
disj-L-R {m} {n} xs ys {v} (v∈L , v∈R)
  with ∈-map⁻ (inject+ n) v∈L | ∈-map⁻ (raise m) v∈R
... | vL , _ , v≡L | vR , _ , v≡R
  = case-absurd (trans (sym sp-L) sp-R)
  where
    -- splitAt m v is forced two different ways.
    sp-L : splitAt m v ≡ inj₁ vL
    sp-L = trans (cong (splitAt m) v≡L) (splitAt-inject+ m n vL)

    sp-R : splitAt m v ≡ inj₂ vR
    sp-R = trans (cong (splitAt m) v≡R) (splitAt-raise m n vR)

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
--
-- `range n = 0 ∷ suc 0 ∷ suc (suc 0) ∷ ...`: these are all distinct Fin
-- values because zero ≢ suc and suc is injective.

import Data.List.Relation.Unary.All        as ListAll
import Data.List.Relation.Unary.AllPairs   as AllPairs
import Data.Fin                            as Fin
open import Relation.Binary.PropositionalEquality using (_≢_)

private
  -- Everything in `map Fin.suc xs` starts with `suc`, hence ≠ zero.
  all-≢-zero : ∀ {n} (xs : List (Fin n))
             → ListAll.All (Fin.zero {n = n} ≢_) (map Fin.suc xs)
  all-≢-zero []       = ListAll.[]
  all-≢-zero (x ∷ xs) = (λ ()) ListAll.∷ all-≢-zero xs

  -- Fin.suc is injective.
  fin-suc-inj : ∀ {n} {i j : Fin n} → Fin.suc i ≡ Fin.suc j → i ≡ j
  fin-suc-inj refl = refl

range-Unique : ∀ n → Unique (range n)
range-Unique 0             = AllPairs.[]
range-Unique (suc n)  =
  all-≢-zero (range n)
    AllPairs.∷ Uniq-Prop.map⁺ fin-suc-inj (range-Unique n)

--------------------------------------------------------------------------------
-- hSwap's dom is Unique. Its dom is
--   `map (inject+ nB) (range nA) ++ map (raise nA) (range nB)`
-- which is Unique via `map⁺` on each side + `++⁺` with disjointness.

hSwap-dom-Unique : ∀ A B → Unique (Hypergraph.dom (hSwap A B))
hSwap-dom-Unique A B =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _))
    (Uniq-Prop.map⁺ (raise-inj   _) (range-Unique _))
    (disj-L-R (range (length (flatten A))) (range (length (flatten B))))

--------------------------------------------------------------------------------
-- hGen's dom is Unique. Dom is `map (inject+ nB) (range nA)`.

hGen-dom-Unique : ∀ {A B : ObjTerm} (f : mor A B) → Unique (Hypergraph.dom (hGen f))
hGen-dom-Unique {A} f = Uniq-Prop.map⁺ (inject+-inj _) (range-Unique _)

--------------------------------------------------------------------------------
-- `range n` covers all of Fin n — needed for `hSwap-dom-covers`.
--
-- Every Fin n value is in the recursive enumeration `0 ∷ suc 0 ∷ suc (suc 0) ∷ ...`.

range-covers : ∀ (n : ℕ) (v : Fin n) → v ∈ range n
range-covers (suc n) zero     = here refl
range-covers (suc n) (suc v)  = there (∈-map⁺ Fin.suc (range-covers n v))

--------------------------------------------------------------------------------
-- hSwap's dom and cod each cover all vertices. Used to show
-- `count-non (hSwap A B).dom ≡ 0`, which is the base requirement for the
-- `σ∘σ` iso (symmetric to `hId-count-non-dom` for `idˡ`).

hSwap-dom-covers : ∀ A B → AllIn (Hypergraph.dom (hSwap A B))
hSwap-dom-covers A B v =
  tensor-covers (range (length (flatten A))) (range (length (flatten B)))
                (range-covers _) (range-covers _) v

hSwap-cod-covers : ∀ A B → AllIn (Hypergraph.cod (hSwap A B))
hSwap-cod-covers A B v
  with splitAt (length (flatten A)) v in eq
-- inj₁ i ⇒ v = inject+ nB i lives in the RIGHT part of cod.
... | inj₁ i = subst (_∈ _) (splitAt⁻¹-↑ˡ eq)
                     (∈-++⁺ʳ (map (raise (length (flatten A))) _)
                             (∈-map⁺ (inject+ (length (flatten B))) (range-covers _ i)))
-- inj₂ j ⇒ v = raise nA j lives in the LEFT part of cod.
... | inj₂ j = subst (_∈ _) (splitAt⁻¹-↑ʳ eq)
                     (∈-++⁺ˡ (∈-map⁺ (raise (length (flatten A))) (range-covers _ j)))

hSwap-count-non-dom : ∀ A B → count-non (Hypergraph.dom (hSwap A B)) ≡ 0
hSwap-count-non-dom A B = AllIn→count-non-zero (hSwap-dom-covers A B)

hSwap-count-non-cod : ∀ A B → count-non (Hypergraph.cod (hSwap A B)) ≡ 0
hSwap-count-non-cod A B = AllIn→count-non-zero (hSwap-cod-covers A B)

-- hSwap has zero edges.
hSwap-nE : ∀ A B → Hypergraph.nE (hSwap A B) ≡ 0
hSwap-nE A B = refl

--------------------------------------------------------------------------------
-- `(hId A).nV` and `length (flatten A)` agree — propositionally only,
-- because in the tensor case `(hId A).nV = (hId A₁).nV + (hId A₂).nV`
-- whereas `length (flatten A) = length (flatten A₁ ++ flatten A₂)` which
-- uses stdlib's `length-++` (propositional).

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
-- For an identity, `vlab` agrees with `lookup (flatten A)` pointwise —
-- via a Fin.cast that bridges the `(hId A).nV ≡ length (flatten A)` gap.
--
-- Needed by `σ∘σ-sound` (and other axioms that relate `hSwap`-structured
-- labelings to `hTensor (hId _)`-structured labelings).

private
  -- Local helpers: lookup through _++_ via inject+/raise, but with a
  -- Fin.cast that absorbs the `length (xs ++ ys) ≡ length xs + length ys`
  -- equality. `cast-inj+` re-expresses `inject+ (length ys) i : Fin (length xs + length ys)`
  -- as an element of `Fin (length (xs ++ ys))`.
  cast-inj+
    : ∀ {A : Set} (xs ys : List A) (i : Fin (length xs))
    → Fin (length (xs ++ ys))
  cast-inj+ xs ys i = cast (sym (length-++ xs)) (inject+ (length ys) i)

  cast-rai+
    : ∀ {A : Set} (xs ys : List A) (j : Fin (length ys))
    → Fin (length (xs ++ ys))
  cast-rai+ xs ys j = cast (sym (length-++ xs)) (raise (length xs) j)

  -- Lookup-through-++ on the inject+ side.
  lookup-++-inj
    : ∀ {A : Set} (xs ys : List A) (i : Fin (length xs))
    → lookup (xs ++ ys) (cast-inj+ xs ys i) ≡ lookup xs i
  lookup-++-inj []       ys ()
  lookup-++-inj (x ∷ xs) ys zero    = refl
  lookup-++-inj (x ∷ xs) ys (suc i) = lookup-++-inj xs ys i

  -- Lookup-through-++ on the raise side.
  lookup-++-rai
    : ∀ {A : Set} (xs ys : List A) (j : Fin (length ys))
    → lookup (xs ++ ys) (cast-rai+ xs ys j) ≡ lookup ys j
  lookup-++-rai []       ys j = cong (lookup ys) (cast-is-id refl j)
  lookup-++-rai (x ∷ xs) ys j = lookup-++-rai xs ys j

-- Cast commutes with `inject+` and `raise` up to toℕ-equality.
-- Public — used by σ∘σ-sound's φ-dom/φ-cod to push casts through
-- `inject+ / raise`.

cast-inject+-comm
  : ∀ {m m'} (eq-m : m ≡ m') (n : ℕ) (i : Fin m)
  → cast (cong (_+ n) eq-m) (inject+ n i) ≡ inject+ n (cast eq-m i)
cast-inject+-comm eq-m n i = toℕ-injective
  (trans (toℕ-cast _ (inject+ n i))
  (trans (toℕ-↑ˡ i n)
  (trans (sym (toℕ-cast eq-m i))
         (sym (toℕ-↑ˡ (cast eq-m i) n)))))

cast-raise-comm
  : ∀ (m : ℕ) {n n'} (eq-n : n ≡ n') (j : Fin n)
  → cast (cong (m +_) eq-n) (raise m j) ≡ raise m (cast eq-n j)
cast-raise-comm m eq-n j = toℕ-injective
  (trans (toℕ-cast _ (raise m j))
  (trans (toℕ-↑ʳ m j)
  (trans (cong (m +_) (sym (toℕ-cast eq-n j)))
         (sym (toℕ-↑ʳ m (cast eq-n j))))))

-- Bridge the two-variable cong₂ with `cast-inject+-comm` above.
-- Pattern-match both eqs as refl to unify the indices, then use
-- `cast-is-id` to cancel the residual `cast _` on each side.
cast-inject+-cong₂
  : ∀ {mA mA' mB mB'} (eq-A : mA ≡ mA') (eq-B : mB ≡ mB') (i : Fin mA)
  → cast (cong₂ _+_ eq-A eq-B) (inject+ mB i)
  ≡ inject+ mB' (cast eq-A i)
cast-inject+-cong₂ refl refl i =
  trans (cast-is-id refl (inject+ _ i))
        (cong (inject+ _) (sym (cast-is-id refl i)))

cast-raise-cong₂
  : ∀ {mA mA' mB mB'} (eq-A : mA ≡ mA') (eq-B : mB ≡ mB') (j : Fin mB)
  → cast (cong₂ _+_ eq-A eq-B) (raise mA j)
  ≡ raise mA' (cast eq-B j)
cast-raise-cong₂ refl refl j =
  trans (cast-is-id refl (raise _ j))
        (cong (raise _) (sym (cast-is-id refl j)))

-- The main lemma. Uses Fin.cast across `hId-nV≡len-flatten A` to bridge
-- the `Fin (hId A).nV` → `Fin (length (flatten A))` gap before looking up.
hId-vlab-lookup
  : ∀ A (i : Fin (Hypergraph.nV (hId A)))
  → Hypergraph.vlab (hId A) i
  ≡ lookup (flatten A) (cast (hId-nV≡len-flatten A) i)
hId-vlab-lookup unit     ()
hId-vlab-lookup (Var x)  zero = refl
hId-vlab-lookup (A ⊗₀ B) i
  with splitAt (Hypergraph.nV (hId A)) i in eq
-- inj₁ a: (hId A).vlab a ≡ lookup (flatten A) ... ≡ lookup (flatten A ++ flatten B) ...
... | inj₁ a = trans (hId-vlab-lookup A a) lookup-eq
  where
    open import Data.Fin.Properties using (cast-trans)

    eq-A : Hypergraph.nV (hId A) ≡ length (flatten A)
    eq-A = hId-nV≡len-flatten A

    eq-B : Hypergraph.nV (hId B) ≡ length (flatten B)
    eq-B = hId-nV≡len-flatten B

    eq-++ : length (flatten A) + length (flatten B) ≡ length (flatten A ++ flatten B)
    eq-++ = sym (length-++ (flatten A))

    i≡injL : i ≡ inject+ (Hypergraph.nV (hId B)) a
    i≡injL = sym (splitAt⁻¹-↑ˡ eq)

    -- Reshape the outer cast using cast-trans + cast-inject+-cong₂.
    cast-form
      : cast (hId-nV≡len-flatten (A ⊗₀ B)) i
      ≡ cast-inj+ (flatten A) (flatten B) (cast eq-A a)
    cast-form =
      trans (cong (cast _) i≡injL)
      (trans (sym (cast-trans (cong₂ _+_ eq-A eq-B) eq-++ (inject+ _ a)))
             (cong (cast eq-++) (cast-inject+-cong₂ eq-A eq-B a)))

    lookup-eq
      : lookup (flatten A) (cast eq-A a)
      ≡ lookup (flatten A ++ flatten B) (cast (hId-nV≡len-flatten (A ⊗₀ B)) i)
    lookup-eq =
      trans (sym (lookup-++-inj (flatten A) (flatten B) _))
            (cong (lookup (flatten A ++ flatten B)) (sym cast-form))
-- inj₂ b: mirror the inj₁ case.
... | inj₂ b = trans (hId-vlab-lookup B b) lookup-eq
  where
    open import Data.Fin.Properties using (cast-trans)

    eq-A : Hypergraph.nV (hId A) ≡ length (flatten A)
    eq-A = hId-nV≡len-flatten A

    eq-B : Hypergraph.nV (hId B) ≡ length (flatten B)
    eq-B = hId-nV≡len-flatten B

    eq-++ : length (flatten A) + length (flatten B) ≡ length (flatten A ++ flatten B)
    eq-++ = sym (length-++ (flatten A))

    i≡raise : i ≡ raise (Hypergraph.nV (hId A)) b
    i≡raise = sym (splitAt⁻¹-↑ʳ eq)

    cast-form
      : cast (hId-nV≡len-flatten (A ⊗₀ B)) i
      ≡ cast-rai+ (flatten A) (flatten B) (cast eq-B b)
    cast-form =
      trans (cong (cast _) i≡raise)
      (trans (sym (cast-trans (cong₂ _+_ eq-A eq-B) eq-++ (raise _ b)))
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
--
-- Used by `hId-dom≡range` for the tensor case, and transitively by any
-- proof that needs to show `(hId (A ⊗₀ B)).dom` is `range`-shaped.

range-++ : ∀ (n m : ℕ)
         → range (n + m) ≡ map (inject+ m) (range n) ++ map (raise n) (range m)
range-++ zero    m = trans (sym (map-id (range m)))
                           (sym (map-cong (λ _ → refl) (range m)))
  where open import Data.List.Properties using (map-id; map-cong)
range-++ (suc n) m = cong (zero ∷_)
  (trans (cong (map Fin.suc) (range-++ n m))
  (trans (map-++ Fin.suc (map (inject+ m) (range n)) (map (raise n) (range m)))
         (cong₂ _++_
           (trans (sym (map-∘ (range n)))
           (trans (map-cong (λ _ → refl) (range n))
                  (map-∘ (range n))))
           (sym (map-∘ (range m))))))
  where
    open import Data.List.Properties using (map-++; map-∘; map-cong)
    import Data.Fin as Fin

--------------------------------------------------------------------------------
-- `(hId A).dom` as a list of Fin is exactly `range (hId A).nV`. Used by
-- `σ∘σ-sound` (and any axiom relating `hSwap`'s `range`-based dom/cod to
-- `hTensor (hId _)`'s structural dom/cod).

hId-dom≡range : ∀ A → Hypergraph.dom (hId A) ≡ range (Hypergraph.nV (hId A))
hId-dom≡range unit     = refl
hId-dom≡range (Var x)  = refl
hId-dom≡range (A ⊗₀ B) =
  trans (cong₂ _++_
          (cong (map (inject+ (Hypergraph.nV (hId B)))) (hId-dom≡range A))
          (cong (map (raise  (Hypergraph.nV (hId A)))) (hId-dom≡range B)))
        (sym (range-++ (Hypergraph.nV (hId A)) (Hypergraph.nV (hId B))))

-- Analogous for cod via the hId-cod≡dom bridge.
hId-cod≡range : ∀ A → Hypergraph.cod (hId A) ≡ range (Hypergraph.nV (hId A))
hId-cod≡range A = trans (hId-cod≡dom A) (hId-dom≡range A)

--------------------------------------------------------------------------------
-- splitAt commutes with `cast` across a `cong₂ _+_` on the indices.
-- Used wherever we need to lift a `splitAt n i` reasoning across a
-- propositional equality `n + m ≡ n' + m'` — notably, σ∘σ's φ-lab chase.

splitAt-cast
  : ∀ {m m' n n'} (eq-m : m ≡ m') (eq-n : n ≡ n') (i : Fin (m + n))
  → splitAt m' (cast (cong₂ _+_ eq-m eq-n) i)
  ≡ [ (λ a → inj₁ (cast eq-m a))
    , (λ b → inj₂ (cast eq-n b))
    ]′ (splitAt m i)
splitAt-cast {m} {m'} {n} {n'} refl refl i
  rewrite cast-is-id (cong₂ _+_ (refl {x = m}) (refl {x = n})) i
        = splitAt-cast-refl i
  where
    -- When both eqs are refl, we just need splitAt m i ≡ ... with cast refl ≡ id.
    splitAt-cast-refl
      : (i : Fin (m + n))
      → splitAt m i
      ≡ [ (λ a → inj₁ (cast (refl {x = m}) a))
        , (λ b → inj₂ (cast (refl {x = n}) b))
        ]′ (splitAt m i)
    splitAt-cast-refl i with splitAt m i
    ... | inj₁ a = cong inj₁ (sym (cast-is-id refl a))
    ... | inj₂ b = cong inj₂ (sym (cast-is-id refl b))

--------------------------------------------------------------------------------
-- `map (cast eq) (range m)` = `range m'` when eq : m ≡ m'.
-- Via refl-pattern + map-cong cast-is-id + map-id.

map-cast-range
  : ∀ {m m'} (eq : m ≡ m') → map (cast eq) (range m) ≡ range m'
map-cast-range refl =
  trans (map-cong (λ i → cast-is-id refl i) (range _))
        (map-id (range _))
  where open import Data.List.Properties using (map-id; map-cong)

-- `length (range n) ≡ n`. Routine induction.

length-range : (n : ℕ) → length (range n) ≡ n
length-range zero    = refl
length-range (suc n) = cong suc
  (trans (length-map Fin.suc (range n)) (length-range n))
  where
    import Data.Fin as Fin
    open import Data.List.Properties using (length-map)

-- `range n ≡ allFin n`. The two enumerations of Fin n are the same
-- list. Enables using stdlib's allFin/tabulate/lookup machinery on
-- `range`-generated lists.

private
  open import Data.List using (allFin)
  import Data.Fin as FinMod
  open import Data.List.Properties using (map-tabulate)

  range≡allFin : ∀ n → range n ≡ allFin n
  range≡allFin zero    = refl
  range≡allFin (suc n) = cong (zero ∷_)
    (trans (cong (map FinMod.suc) (range≡allFin n))
           (map-tabulate (λ i → i) FinMod.suc))

-- Public alias (kept private to avoid polluting the outer namespace
-- with `allFin` / `map-tabulate`; call sites that need this can
-- import it explicitly).
range≡allFin-pub : ∀ n → range n ≡ allFin n
range≡allFin-pub = range≡allFin
  where open import Data.List using (allFin)

-- `toℕ (lookup (range n) j) ≡ toℕ j` via direct induction on range.
-- Needed by σ∘σ-sound's `lookup-cod-*` helpers (bridging the cast
-- between `Fin (length (range n))` and `Fin n`).

open import Data.Fin using (toℕ)

lookup-range
  : ∀ n (j : Fin (length (range n)))
  → toℕ (lookup (range n) j) ≡ toℕ j
lookup-range (suc n) zero    = refl
lookup-range (suc n) (suc j) =
  trans (cong toℕ (lookup-map-Fsuc {xs = range n} j))
  (cong suc
    (trans (lookup-range n (cast (length-map Fin.suc (range n)) j))
           (toℕ-cast _ j)))
  where
    import Data.Fin as Fin
    open import Data.List.Properties using (length-map)

    -- lookup (map suc xs) j = suc (lookup xs (cast _ j)).
    lookup-map-Fsuc
      : ∀ {xs : List (Fin n)} (j : Fin (length (map Fin.suc xs)))
      → lookup (map Fin.suc xs) j
      ≡ Fin.suc (lookup xs (cast (length-map Fin.suc xs) j))
    lookup-map-Fsuc {x ∷ xs} zero    = refl
    lookup-map-Fsuc {x ∷ xs} (suc j) = lookup-map-Fsuc {xs} j
