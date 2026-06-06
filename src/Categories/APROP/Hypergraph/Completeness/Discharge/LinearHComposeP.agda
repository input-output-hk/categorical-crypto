{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- DE-RISKING SPIKE: does the linearity layer port from the UNPRUNED
-- composition `hCompose` to the PRUNED `hComposeP`?
--
-- This module proves, for the pruned cospan composition `hComposeP`:
--
--   (#1) `remapP-injective` : injectivity of the pruned K-side vertex remap
--        `remapP = remap K.dom lookup-cod`.
--   (#4) `Linear-hComposeP`  : `hComposeP` preserves the `Linear` invariant.
--
-- It MIRRORS `Linearity.Linear-hCompose`, replacing the unpruned K-side
-- routing (`injR : Fin K.nV → Fin (G.nV + K.nV)`) by the pruned routing
-- baked into `remapP`:
--   * members of K.dom go to `lookup-cod i ↑ˡ count-non K.dom`  (G-side),
--   * non-members go to `G.nV ↑ʳ j`                            (pruned slot).
--
-- SPIKE FINDINGS — see the report.  In short, the port is MECHANICAL:
--   * `remapP-injective` is `Prune.remap-injective` applied with
--     `Unique K.dom` and `lookup-cod`-injectivity, both bridged from the
--     `count _ _ ≤ 1` bounds the linearity invariant already supplies.
--   * `Linear-hComposeP`'s count-algebra ports essentially verbatim from
--     `Linear-hCompose`; the only genuinely new lemma is
--     `map-remapP-K-dom : map remapP K.dom ≡ map (_↑ˡ count-non) G.cod`,
--     which replaces the unpruned `map remap K.dom ≡ map injL G.cod`.
--
-- No `--safe` because we re-derive a handful of private helpers from
-- `Linearity` (which is `--safe`); there is nothing unsafe here.  No
-- postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.LinearHComposeP
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen)
open import Categories.APROP.Hypergraph.Prune
  using ( count-non; nonMem; classify; remap
        ; remap-inj₁; remap-inj₂; remap-injective
        ; classify-lookup-Unique; classify-inj₁-lookup
        ; lookup-injective-unique)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using ( count; count-++; count-map-↑ˡ
        ; count-map-↑ˡ-mismatch; count-swap
        ; producedList; consumedList; Linear)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; cast; toℕ)
open import Data.Fin.Properties using
  ( _≟_
  ; splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ
  ; toℕ-cast; toℕ-injective)
open import Data.List as List using
  (List; []; _∷_; _++_; length; map; tabulate; concat; lookup)
open import Data.List.Properties using
  ( ++-identityʳ; ++-assoc; map-++
  ; tabulate-cong; map-tabulate; concat-map; concat-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Function as Fun
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _+_)
open import Data.Nat as Nat using ()
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_)

--------------------------------------------------------------------------------
-- Re-derived count / permutation helpers.
--
-- These mirror the `private`-block helpers inside `Linearity` (which are
-- not exported).  Each is self-contained and small.

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.CountCombinatorics sig
  using (count-cons-yes; count-cons-no)
  renaming (↭⇒count to ↭⇒count-≡)

private
  -- `tabulate` over a `Fin (m + n)` index splits as a `++` of the two
  -- halves.  Used by `eout-comp-eq` / `ein-comp-eq` below.
  tabulate-+ : ∀ {m n} {A : Set} (f : Fin (m + n) → A)
             → tabulate f
             ≡ tabulate (λ i → f (i ↑ˡ n)) ++ tabulate (λ j → f (m ↑ʳ j))
  tabulate-+ {m = zero}          f = refl
  tabulate-+ {m = suc m} {n = n} f =
    cong (f zero ∷_) (tabulate-+ {m = m} {n = n} (f Fun.∘ suc))

  count-mono-cons : ∀ {n} (v x : Fin n) (xs : List (Fin n))
                  → count v xs Nat.≤ count v (x ∷ xs)
  count-mono-cons v x xs with v ≟ x
  ... | yes _ = Nat.n≤1+n (count v xs)
  ... | no  _ = Nat.≤-refl

  count-zero-empty : ∀ {n} (xs : List (Fin n))
                   → (∀ v → count v xs ≡ 0)
                   → xs ≡ []
  count-zero-empty []       _   = refl
  count-zero-empty (x ∷ xs) hyp
    with trans (sym (count-cons-yes x xs)) (hyp x)
  ... | ()

  count-pos→split
    : ∀ {n} (v : Fin n) (xs : List (Fin n))
    → 0 Nat.< count v xs
    → Σ[ xs₁ ∈ List (Fin n) ] Σ[ xs₂ ∈ List (Fin n) ] xs ≡ xs₁ ++ v ∷ xs₂
  count-pos→split v []       ()
  count-pos→split v (x ∷ xs) c with v ≟ x
  ... | yes refl = [] , xs , refl
  ... | no  _    with count-pos→split v xs c
  ...               | xs₁ , xs₂ , refl = (x ∷ xs₁) , xs₂ , refl

  count-cancel-cons
    : ∀ {n} (v x : Fin n) (xs ys : List (Fin n))
    → count v (x ∷ xs) ≡ count v (x ∷ ys)
    → count v xs ≡ count v ys
  count-cancel-cons v x xs ys h with v ≟ x
  ... | yes _ = Nat.suc-injective h
  ... | no  _ = h

  count-≡⇒↭
    : ∀ {n} (xs ys : List (Fin n))
    → (∀ v → count v xs ≡ count v ys)
    → xs Perm.↭ ys
  count-≡⇒↭ []       ys hyp
    rewrite count-zero-empty ys (λ k → sym (hyp k)) = Perm.refl
  count-≡⇒↭ (x ∷ xs) ys hyp
    with count-pos→split x ys
           (subst (0 Nat.<_) (trans (sym (count-cons-yes x xs)) (hyp x))
                  (s≤s z≤n))
  ... | ys₁ , ys₂ , refl =
        Perm.trans (Perm.prep x (count-≡⇒↭ xs (ys₁ ++ ys₂) sub-hyp))
                   (Perm.↭-sym (PermProp.shift x ys₁ ys₂))
        where
          sub-hyp : ∀ v → count v xs ≡ count v (ys₁ ++ ys₂)
          sub-hyp v = count-cancel-cons v x xs (ys₁ ++ ys₂)
                        (trans (hyp v)
                               (↭⇒count-≡ (PermProp.shift x ys₁ ys₂) v))

  count-map-resp
    : ∀ {n m} (f : Fin n → Fin m) (xs ys : List (Fin n))
    → (∀ k → count k xs ≡ count k ys)
    → ∀ v → count v (map f xs) ≡ count v (map f ys)
  count-map-resp f xs ys hyp v =
    ↭⇒count-≡ (PermProp.map⁺ f (count-≡⇒↭ xs ys hyp)) v

  -- `cast eq` is injective (it preserves `toℕ`).  Stdlib 2.3 has no
  -- `cast-injective`, so we derive it from `toℕ-cast` + `toℕ-injective`.
  cast-injective : ∀ {m n} (eq : m ≡ n) {i j : Fin m}
                 → cast eq i ≡ cast eq j → i ≡ j
  cast-injective eq {i} {j} ci≡cj =
    toℕ-injective
      (trans (sym (toℕ-cast eq i))
             (trans (cong toℕ ci≡cj) (toℕ-cast eq j)))

--------------------------------------------------------------------------------
-- SPIKE QUESTION #1 — `count _ _ ≤ 1` ⇒ `Unique`.
--
-- `Prune.remap-injective` requires the stdlib `Unique xs` (= `AllPairs
-- _≢_ xs`), but the linearity invariant only hands us `count k xs ≤ 1`.
-- There is NO such bridge anywhere in the codebase, so we build it here.
-- It is a short induction: at the head `x ∷ xs`, `count x (x ∷ xs) ≤ 1`
-- forces `count x xs ≡ 0`, hence `x` differs from every element of `xs`
-- (an `All (x ≢_) xs`); the tail count-bound shrinks to give `Unique xs`.

private
  -- `count x xs ≡ 0` ⇒ `x ≢` every element of `xs`.
  count-zero→All-≢ : ∀ {n} (x : Fin n) (xs : List (Fin n))
                   → count x xs ≡ 0
                   → All.All (x ≢_) xs
  count-zero→All-≢ x []       _ = All.[]
  count-zero→All-≢ x (y ∷ xs) c with x ≟ y
  ... | yes refl = ⊥-elim (case c) where case : suc _ ≡ 0 → ⊥
                                         case ()
  ... | no  x≢y  = x≢y All.∷ count-zero→All-≢ x xs c

count-bnd→Unique : ∀ {n} (xs : List (Fin n))
                 → (∀ v → count v xs Nat.≤ 1)
                 → Unique xs
count-bnd→Unique []       _   = AllPairs.[]
count-bnd→Unique (x ∷ xs) bnd =
  count-zero→All-≢ x xs head-zero AllPairs.∷ count-bnd→Unique xs tail-bnd
  where
    head-zero : count x xs ≡ 0
    head-zero =
      Nat.≤-antisym
        (Nat.s≤s⁻¹ (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes x xs)))
                                (bnd x)))
        z≤n
    tail-bnd : ∀ v → count v xs Nat.≤ 1
    tail-bnd v = Nat.≤-trans (count-mono-cons v x xs) (bnd v)

--------------------------------------------------------------------------------
-- The main construction.  Mirrors `Linearity.Linear-hCompose` /
-- `hCompose-Linear-utils`, with `injR` replaced by the pruned routing.

module _
  (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  (lin-G : Linear G) (lin-K : Linear K)
  where

  private
    module G = Hypergraph G
    module K = Hypergraph K
    open hComposeP-impl G K bdy-eq
      using ( remapP; lookup-cod; dom-cod-len; nV-P; injL )

    G-bal = proj₁ lin-G
    G-bnd = proj₂ lin-G
    K-bal = proj₁ lin-K
    K-bnd = proj₂ lin-K

    G-eb    = concat (tabulate G.eout)
    G-ein-b = concat (tabulate G.ein)
    K-eb    = concat (tabulate K.eout)
    K-ein-b = concat (tabulate K.ein)

    cn = count-non K.dom

  ------------------------------------------------------------------------
  -- Bounds carried over from the linearity invariant (same as in
  -- `hCompose-Linear-utils`).

  K-dom-bnd : ∀ k → count k K.dom Nat.≤ 1
  K-dom-bnd k =
    Nat.≤-trans
      (Nat.≤-trans (Nat.m≤m+n (count k K.dom) _)
                   (Nat.≤-reflexive (sym (count-++ k K.dom K-eb))))
      (K-bnd k)

  G-cod-bnd : ∀ v → count v G.cod Nat.≤ 1
  G-cod-bnd v =
    Nat.≤-trans
      (Nat.≤-trans (Nat.m≤m+n (count v G.cod) _)
                   (Nat.≤-reflexive (sym (count-++ v G.cod G-ein-b))))
      (Nat.≤-trans (Nat.≤-reflexive (sym (G-bal v))) (G-bnd v))

  ------------------------------------------------------------------------
  -- SPIKE QUESTION #1+#2 — `remapP-injective`.

  K-dom-Unique : Unique K.dom
  K-dom-Unique = count-bnd→Unique K.dom K-dom-bnd

  G-cod-Unique : Unique G.cod
  G-cod-Unique = count-bnd→Unique G.cod G-cod-bnd

  -- `lookup-cod` is injective: it is `lookup G.cod` precomposed with the
  -- (injective) `cast`, and `lookup G.cod` is injective on a Unique list.
  lookup-cod-injective
    : ∀ {i j : Fin (length K.dom)} → lookup-cod i ≡ lookup-cod j → i ≡ j
  lookup-cod-injective {i} {j} eq =
    cast-injective dom-cod-len
      (lookup-injective-unique G-cod-Unique
        (cast dom-cod-len i) (cast dom-cod-len j) eq)

  -- (#1)  Injectivity of the pruned K-side vertex remap.
  remapP-injective
    : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective =
    remap-injective K.dom lookup-cod K-dom-Unique lookup-cod-injective

  ------------------------------------------------------------------------
  -- `map remapP K.dom ≡ map (_↑ˡ cn) G.cod`.
  --
  -- This is the pruned analogue of `Linear-hCompose`'s
  -- `map-remap-K-dom : map remap K.dom ≡ map injL G.cod`.  Each member of
  -- K.dom is routed (via `classify-lookup-Unique` + `remap-inj₁`) to
  -- `lookup-cod idx ↑ˡ cn`, and `lookup-cod idx = lookup G.cod (cast … idx)`
  -- walks G.cod in lockstep with K.dom (cast is index-preserving), so the
  -- two mapped lists agree.

  private
    -- length K.dom ≡ length G.cod.
    length-K-dom : length K.dom ≡ length G.cod
    length-K-dom = dom-cod-len

    -- Pointwise: `remapP (lookup K.dom idx) ≡ lookup-cod idx ↑ˡ cn`.
    remapP-on-dom
      : ∀ (idx : Fin (length K.dom))
      → remapP (lookup K.dom idx) ≡ lookup-cod idx ↑ˡ cn
    remapP-on-dom idx =
      remap-inj₁ K.dom lookup-cod (lookup K.dom idx) idx
        (classify-lookup-Unique K.dom K-dom-Unique idx)

    -- List-extensionality: two `map`s agree when their lengths agree and
    -- they agree pointwise (up to `cast` on the index).  Same induction
    -- as `PrunedCompose.lookup-boundary`, but at the list level.
    map-ext-cast
      : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B) (g : C → B)
          (xs : List A) (ys : List C) (len : length xs ≡ length ys)
      → (∀ i → f (lookup xs i) ≡ g (lookup ys (cast len i)))
      → map f xs ≡ map g ys
    map-ext-cast f g []       []       _   _  = refl
    map-ext-cast f g []       (y ∷ ys) ()  _
    map-ext-cast f g (x ∷ xs) []       ()  _
    map-ext-cast f g (x ∷ xs) (y ∷ ys) len pt =
      cong₂ _∷_ (pt zero)
        (map-ext-cast f g xs ys (Nat.suc-injective len) (λ i → pt (suc i)))

  -- `lookup-cod idx = lookup G.cod (cast dom-cod-len idx)` is definitional
  -- and `length-K-dom = dom-cod-len`, so `remapP-on-dom idx` already lands
  -- on `lookup G.cod (cast length-K-dom idx) ↑ˡ cn`, i.e. the pointwise
  -- goal of `map-ext-cast`.
  map-remapP-K-dom : map remapP K.dom ≡ map (_↑ˡ cn) G.cod
  map-remapP-K-dom =
    map-ext-cast remapP (_↑ˡ cn) K.dom G.cod length-K-dom remapP-on-dom

  -- count facts about `map remapP K.dom` consumed by the balance proof.
  count-map-remapP-K-dom-injL
    : ∀ (i : Fin G.nV) → count (i ↑ˡ cn) (map remapP K.dom) ≡ count i G.cod
  count-map-remapP-K-dom-injL i =
    trans (cong (count (i ↑ˡ cn)) map-remapP-K-dom)
          (count-map-↑ˡ cn i G.cod)

  count-map-remapP-K-dom-raise
    : ∀ (j : Fin cn) → count (G.nV ↑ʳ j) (map remapP K.dom) ≡ 0
  count-map-remapP-K-dom-raise j =
    trans (cong (count (G.nV ↑ʳ j)) map-remapP-K-dom)
          (count-map-↑ˡ-mismatch G.nV j G.cod)

  ------------------------------------------------------------------------
  -- `map remapP K-eb ≡ map (G.nV ↑ʳ_) (...)`?  NO — unlike the unpruned
  -- case, K-eb members are NOT generally mapped to a single fixed `↑ʳ`
  -- pattern indexed by the K-vertex itself; they go through the pruned
  -- `nonMem`-index.  But for the BALANCE proof we never need that: we
  -- only push K-balance through `remapP` via `count-map-resp`, which
  -- treats `remapP` as an opaque function.  For the BOUND proof, however,
  -- we DO need to bound `count v (map remapP K-eb)`.  We obtain that
  -- bound directly from K-bound via `count-map-≥-fiber` below.

  private
    -- count v (map f xs) ≥ count k xs whenever f k = v.  (Copied from
    -- `hCompose-Linear-utils`.)
    count-map-≥-fiber
      : ∀ {n m} (f : Fin n → Fin m) (k : Fin n) {v : Fin m}
      → f k ≡ v
      → ∀ (xs : List (Fin n)) → count k xs Nat.≤ count v (map f xs)
    count-map-≥-fiber f k {v} eq []       = z≤n
    count-map-≥-fiber f k {v} eq (x ∷ xs) with k ≟ x
    count-map-≥-fiber f k {v} eq (x ∷ xs) | yes refl with v ≟ f x
    ...                                                  | yes _ = s≤s (count-map-≥-fiber f k eq xs)
    ...                                                  | no  q = ⊥-elim (q (sym eq))
    count-map-≥-fiber f k {v} eq (x ∷ xs) | no  _    with v ≟ f x
    ...                                                  | yes _ = Nat.≤-trans
                                                                    (count-map-≥-fiber f k eq xs)
                                                                    (Nat.n≤1+n _)
    ...                                                  | no  _ = count-map-≥-fiber f k eq xs

    -- count v (map f xs) ≤ count k xs when f is injective and f k = v
    -- (each occurrence of v in `map f xs` has a unique k-preimage).
    count-map-≤-fiber
      : ∀ {n m} (f : Fin n → Fin m)
      → (∀ {a b} → f a ≡ f b → a ≡ b)
      → (k : Fin n) {v : Fin m} → f k ≡ v
      → ∀ (xs : List (Fin n)) → count v (map f xs) Nat.≤ count k xs
    count-map-≤-fiber f f-inj k {v} eq []       = z≤n
    count-map-≤-fiber f f-inj k {v} eq (x ∷ xs) with k ≟ x
    count-map-≤-fiber f f-inj k {v} eq (x ∷ xs) | yes refl with v ≟ f x
    ...                                                        | yes _ = s≤s (count-map-≤-fiber f f-inj k eq xs)
    ...                                                        | no  q = ⊥-elim (q (sym eq))
    count-map-≤-fiber f f-inj k {v} eq (x ∷ xs) | no  k≢x with v ≟ f x
    ...                                                        | yes p = ⊥-elim (k≢x (f-inj (trans eq p)))
    ...                                                        | no  _ = count-map-≤-fiber f f-inj k eq xs

    -- count v (map f xs) ≡ count k xs when f injective and f k = v.
    count-map-fiber
      : ∀ {n m} (f : Fin n → Fin m)
      → (∀ {a b} → f a ≡ f b → a ≡ b)
      → (k : Fin n) {v : Fin m} → f k ≡ v
      → ∀ (xs : List (Fin n)) → count v (map f xs) ≡ count k xs
    count-map-fiber f f-inj k eq xs =
      Nat.≤-antisym (count-map-≤-fiber f f-inj k eq xs)
                    (count-map-≥-fiber f k eq xs)

    -- count v (map f xs) ≡ 0 when every preimage of v in `xs` has count 0
    -- there (so no element of `xs` actually maps to v).  Phrased with a
    -- count-zero hypothesis keyed on preimages, which threads through the
    -- recursion without any `y ≟ x` case-split (avoiding `with`-abstraction
    -- clashes with `count`'s own internal `≟`).
    count-map-no-list-preimage
      : ∀ {n m} (f : Fin n → Fin m) {v : Fin m}
      → ∀ (xs : List (Fin n))
      → (∀ x → f x ≡ v → count x xs ≡ 0)
      → count v (map f xs) ≡ 0
    count-map-no-list-preimage f         []       _      = refl
    count-map-no-list-preimage f {v} (x ∷ xs) zeros with v ≟ f x
    ... | yes p = ⊥-elim (head-absurd (zeros x (sym p)))
      where head-absurd : count x (x ∷ xs) ≡ 0 → ⊥
            head-absurd c0 with trans (sym (count-cons-yes x xs)) c0
            ... | ()
    ... | no  _ = count-map-no-list-preimage f xs
                    (λ y fy≡v → tail-zero y (zeros y fy≡v))
      where
        tail-zero : ∀ y → count y (x ∷ xs) ≡ 0 → count y xs ≡ 0
        tail-zero y c0 =
          Nat.≤-antisym
            (Nat.≤-trans (count-mono-cons y x xs) (Nat.≤-reflexive c0)) z≤n

  ------------------------------------------------------------------------
  -- Structural decompositions of `concat (tabulate eout-c / ein-c)`.
  -- Identical in shape to `Linear-hCompose`, with `remap` → `remapP`.

  open hComposeP-impl G K bdy-eq
    using ( eout-c; ein-c
          ; eout-c-inj₁-red; eout-c-inj₂-red
          ; ein-c-inj₁-red; ein-c-inj₂-red )

  eout-comp-eq
    : concat (tabulate eout-c)
    ≡ map injL G-eb ++ map remapP K-eb
  eout-comp-eq =
    trans (cong concat (tabulate-+ {m = G.nE} {n = K.nE} eout-c))
    (trans (cong concat
              (cong₂ _++_
                 (trans (tabulate-cong eout-c-inj₁-red)
                        (sym (map-tabulate G.eout (map injL))))
                 (trans (tabulate-cong eout-c-inj₂-red)
                        (sym (map-tabulate K.eout (map remapP))))))
    (trans (sym (concat-++ (map (map injL) (tabulate G.eout))
                            (map (map remapP) (tabulate K.eout))))
           (cong₂ _++_ (concat-map (tabulate G.eout))
                       (concat-map (tabulate K.eout)))))

  ein-comp-eq
    : concat (tabulate ein-c)
    ≡ map injL G-ein-b ++ map remapP K-ein-b
  ein-comp-eq =
    trans (cong concat (tabulate-+ {m = G.nE} {n = K.nE} ein-c))
    (trans (cong concat
              (cong₂ _++_
                 (trans (tabulate-cong ein-c-inj₁-red)
                        (sym (map-tabulate G.ein (map injL))))
                 (trans (tabulate-cong ein-c-inj₂-red)
                        (sym (map-tabulate K.ein (map remapP))))))
    (trans (sym (concat-++ (map (map injL) (tabulate G.ein))
                            (map (map remapP) (tabulate K.ein))))
           (cong₂ _++_ (concat-map (tabulate G.ein))
                       (concat-map (tabulate K.ein)))))

  ------------------------------------------------------------------------
  -- The dom/cod of the composite (from `hComposeP`'s record):
  --   dom = map injL G.dom ,  cod = map remapP K.cod.
  --
  -- `producedList (hComposeP G K bdy-eq)`
  --   = (map injL G.dom) ++ concat (tabulate eout-c)
  -- and similarly for consumedList.

  count-prod
    : ∀ v
    → count v (producedList (hComposeP G K bdy-eq))
    ≡ count v (map injL G.dom)
    + count v (map injL G-eb)
    + count v (map remapP K-eb)
  count-prod v =
    trans (count-++ v (map injL G.dom) (concat (tabulate eout-c)))
    (trans (cong (count v (map injL G.dom) Nat.+_)
                 (trans (cong (count v) eout-comp-eq)
                        (count-++ v (map injL G-eb) (map remapP K-eb))))
           (sym (Nat.+-assoc (count v (map injL G.dom)) _ _)))

  count-cons
    : ∀ v
    → count v (consumedList (hComposeP G K bdy-eq))
    ≡ count v (map remapP K.cod)
    + count v (map injL G-ein-b)
    + count v (map remapP K-ein-b)
  count-cons v =
    trans (count-++ v (map remapP K.cod) (concat (tabulate ein-c)))
    (trans (cong (count v (map remapP K.cod) Nat.+_)
                 (trans (cong (count v) ein-comp-eq)
                        (count-++ v (map injL G-ein-b) (map remapP K-ein-b))))
           (sym (Nat.+-assoc (count v (map remapP K.cod)) _ _)))

  ------------------------------------------------------------------------
  -- K-balance pushed through `remapP` (treating remapP opaquely).

  K-bal-via-remapP
    : ∀ v
    → count v (map remapP (K.dom ++ K-eb))
    ≡ count v (map remapP (K.cod ++ K-ein-b))
  K-bal-via-remapP v =
    count-map-resp remapP (K.dom ++ K-eb) (K.cod ++ K-ein-b) K-bal v

  ------------------------------------------------------------------------
  -- The "L-side balance" identity.  For v = injL i it combines G-bal with
  -- the `map-remapP-K-dom` characterisation; for v = raise j both sides
  -- are 0.  Mirrors `Linear-hCompose`'s `αβ≡εη`.

  αβ≡εη
    : ∀ v
    → count v (map injL G.dom) + count v (map injL G-eb)
    ≡ count v (map injL G-ein-b) + count v (map remapP K.dom)
  αβ≡εη v with splitAt G.nV v in eq
  ... | inj₁ i with splitAt⁻¹-↑ˡ {n = cn} eq
  ...           | refl =
                  trans (cong₂ Nat._+_
                          (count-map-↑ˡ cn i G.dom)
                          (count-map-↑ˡ cn i G-eb))
                  (trans (sym (count-++ i G.dom G-eb))
                  (trans (G-bal i)
                  (trans (count-swap i G.cod G-ein-b)
                  (trans (count-++ i G-ein-b G.cod)
                         (cong₂ Nat._+_
                           (sym (count-map-↑ˡ cn i G-ein-b))
                           (sym (count-map-remapP-K-dom-injL i)))))))
  αβ≡εη v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
  ...                | refl =
                       trans (cong₂ Nat._+_
                               (count-map-↑ˡ-mismatch G.nV j G.dom)
                               (count-map-↑ˡ-mismatch G.nV j G-eb))
                       (sym (cong₂ Nat._+_
                               (count-map-↑ˡ-mismatch G.nV j G-ein-b)
                               (count-map-remapP-K-dom-raise j)))

  ------------------------------------------------------------------------
  -- Balance: combining all the pieces.  IDENTICAL algebra to
  -- `Linear-hCompose.balance` (only `remap`→`remapP`).

  balance : ∀ v → count v (producedList (hComposeP G K bdy-eq))
                ≡ count v (consumedList (hComposeP G K bdy-eq))
  balance v =
    trans (count-prod v)
    (trans (cong (Nat._+ γ) (αβ≡εη v))
    (trans (Nat.+-assoc ε η γ)
    (trans (cong (ε Nat.+_)
                 (trans (sym (count-++ v (map remapP K.dom) (map remapP K-eb)))
                 (trans (sym (cong (count v) (map-++ remapP K.dom K-eb)))
                 (trans (K-bal-via-remapP v)
                 (trans (cong (count v) (map-++ remapP K.cod K-ein-b))
                        (count-++ v (map remapP K.cod) (map remapP K-ein-b)))))))
    (trans (sym (Nat.+-assoc ε δ ζ))
    (trans (cong (Nat._+ ζ) (Nat.+-comm ε δ))
           (sym (count-cons v)))))))
    where
      α = count v (map injL G.dom)
      β = count v (map injL G-eb)
      γ = count v (map remapP K-eb)
      δ = count v (map remapP K.cod)
      ε = count v (map injL G-ein-b)
      ζ = count v (map remapP K-ein-b)
      η = count v (map remapP K.dom)

  ------------------------------------------------------------------------
  -- Bound: case-split on `v`.
  --
  -- The produced count of `v` decomposes (count-prod) into the G.dom,
  -- G-eb and (map remapP K-eb) contributions.
  --
  --   * For v = raise j: the G-side terms are 0 and the K-eb term is ≤ 1
  --     (it equals `count k K-eb` for the unique remapP-preimage k, by
  --     injectivity of remapP, and `count k K-eb ≤ 1` by K-bound).
  --   * For v = injL i: the G-side terms sum to `count i (G.dom ++ G-eb)`
  --     ≤ 1 (G-bound), and the K-eb term is *exactly 0*: any preimage
  --     `k ∈ K-eb` with `remapP k ≡ injL i` would have `k ∈ K.dom` (only
  --     K.dom members route to injL slots), giving count ≥ 2 in
  --     `K.dom ++ K-eb`, contradicting K-bound.

  private
    -- Disjointness of `_↑ˡ cn` and `G.nV ↑ʳ_` ranges.
    ↑ˡ-↑ʳ-disjoint : (i : Fin G.nV) (j : Fin cn)
                   → i ↑ˡ cn ≡ G.nV ↑ʳ j → ⊥
    ↑ˡ-↑ʳ-disjoint i j eq
      with splitAt-↑ˡ G.nV i cn | splitAt-↑ʳ G.nV cn j | cong (splitAt G.nV) eq
    ... | i-red | j-red | split-eq =
      case-absurd (trans (sym i-red) (trans split-eq j-red))
      where
        case-absurd : ∀ {Y : Set} {x : Fin G.nV} {y : Fin cn}
                    → inj₁ x ≡ inj₂ y → Y
        case-absurd ()

    K-eb-bnd : ∀ k → count k K-eb Nat.≤ 1
    K-eb-bnd k =
      Nat.≤-trans
        (Nat.≤-trans (Nat.m≤n+m (count k K-eb) (count k K.dom))
                     (Nat.≤-reflexive (sym (count-++ k K.dom K-eb))))
        (K-bnd k)

    -- count (any v) in (map remapP K-eb) ≤ 1, via injectivity of remapP.
    -- Search K-eb for a preimage `k` of v.  If found, the v-count equals
    -- `count k K-eb` (injectivity ⇒ `count-map-fiber`), bounded by K-bound.
    -- If not, the search hands back a direct proof that the v-count is 0,
    -- built inductively (no element of the list maps to v).
    count-remapP-K-eb-≤1 : ∀ v → count v (map remapP K-eb) Nat.≤ 1
    count-remapP-K-eb-≤1 v with search K-eb
      where
        -- Either some element of `xs` is a preimage of v, or every
        -- preimage of v has count 0 in `xs` (i.e. doesn't appear).
        search : (xs : List (Fin K.nV))
               → (Σ[ k ∈ Fin K.nV ] remapP k ≡ v)
               ⊎ (∀ x → remapP x ≡ v → count x xs ≡ 0)
        search []       = inj₂ (λ _ _ → refl)
        search (x ∷ xs) with remapP x ≟ v
        ... | yes p = inj₁ (x , p)
        ... | no  q with search xs
        ...            | inj₁ found = inj₁ found
        ...            | inj₂ none  = inj₂ rec
          where
            rec : ∀ y → remapP y ≡ v → count y (x ∷ xs) ≡ 0
            rec y rpy = trans (count-cons-no y x xs y≢x) (none y rpy)
              where
                -- y ≢ x: else remapP y ≡ remapP x ≡ v contradicts q.
                y≢x : ¬ (y ≡ x)
                y≢x y≡x = q (subst (λ z → remapP z ≡ v) y≡x rpy)
    ... | inj₁ (k , rpk) =
          Nat.≤-trans
            (Nat.≤-reflexive (count-map-fiber remapP remapP-injective k rpk K-eb))
            (K-eb-bnd k)
    ... | inj₂ none =
          Nat.≤-trans
            (Nat.≤-reflexive (count-map-no-list-preimage remapP K-eb none))
            z≤n

    -- If `count k K.dom ≡ 0` then `classify K.dom k` lands in `inj₂`.
    classify-from-count-zero
      : ∀ (k : Fin K.nV) → count k K.dom ≡ 0
      → Σ[ j ∈ Fin cn ] classify K.dom k ≡ inj₂ j
    classify-from-count-zero k c0 with classify K.dom k in cls
    ... | inj₂ j = j , refl
    ... | inj₁ i = ⊥-elim (Nat.<-irrefl refl
                            (subst (0 Nat.<_) c0
                              (lookup-count-pos K.dom i
                                (classify-inj₁-lookup K.dom k i cls))))
      where
        -- `lookup xs i ≡ k` ⇒ `0 < count k xs`.
        lookup-count-pos : ∀ (xs : List (Fin K.nV)) (i : Fin (length xs)) {k}
                         → lookup xs i ≡ k → 0 Nat.< count k xs
        lookup-count-pos (x ∷ xs) zero    {k} eq =
          subst (λ z → 0 Nat.< count k (z ∷ xs)) (sym eq)
            (subst (0 Nat.<_) (sym (count-cons-yes k xs)) (s≤s z≤n))
        lookup-count-pos (x ∷ xs) (suc i) {k} eq =
          Nat.<-≤-trans (lookup-count-pos xs i eq) (count-mono-cons k x xs)

    -- Only K.dom members route to `↑ˡ`-slots (injL): if `remapP k ≡ injL i`
    -- then `count k K.dom > 0`.
    remapP-injL→inDom
      : ∀ (k : Fin K.nV) (i : Fin G.nV)
      → remapP k ≡ injL i → 0 Nat.< count k K.dom
    remapP-injL→inDom k i rpk with count k K.dom in cd
    ... | suc _ = s≤s z≤n
    ... | zero  = ⊥-elim (↑ˡ-↑ʳ-disjoint i j₀ (trans (sym rpk) k-raise))
      where
        cls = classify-from-count-zero k cd
        j₀  = proj₁ cls
        k-raise : remapP k ≡ G.nV ↑ʳ j₀
        k-raise = remap-inj₂ K.dom lookup-cod k j₀ (proj₂ cls)

    -- The K-eb contribution at an injL-slot vanishes.
    count-injL-remapP-K-eb-zero
      : ∀ (i : Fin G.nV) → count (injL i) (map remapP K-eb) ≡ 0
    count-injL-remapP-K-eb-zero i = go K-eb (λ _ p → p)
      where
        K-eb→noDom : ∀ k → 0 Nat.< count k K-eb → count k K.dom ≡ 0
        K-eb→noDom k pos = Nat.≤-antisym le z≤n
          where
            prod-bnd : count k K.dom + count k K-eb Nat.≤ 1
            prod-bnd = subst (Nat._≤ 1) (count-++ k K.dom K-eb) (K-bnd k)
            step : count k K.dom + 1 Nat.≤ 1
            step = Nat.≤-trans (Nat.+-monoʳ-≤ (count k K.dom) pos) prod-bnd
            le : count k K.dom Nat.≤ 0
            le = Nat.+-cancelʳ-≤ 1 (count k K.dom) 0 step
        go : (xs : List (Fin K.nV))
           → (∀ k → 0 Nat.< count k xs → 0 Nat.< count k K-eb)
           → count (injL i) (map remapP xs) ≡ 0
        go []       _   = refl
        go (x ∷ xs) sub with injL i ≟ remapP x
        ... | no  _ = go xs (λ k p → sub k (Nat.≤-trans p (count-mono-cons k x xs)))
        ... | yes p = ⊥-elim (x-in-dom→absurd)
          where
            x∈ : 0 Nat.< count x (x ∷ xs)
            x∈ = subst (0 Nat.<_) (sym (count-cons-yes x xs)) (s≤s z≤n)
            x-in-dom : 0 Nat.< count x K.dom
            x-in-dom = remapP-injL→inDom x i (sym p)
            x-dom-zero : count x K.dom ≡ 0
            x-dom-zero = K-eb→noDom x (sub x x∈)
            x-in-dom→absurd : ⊥
            x-in-dom→absurd =
              Nat.<-irrefl refl (subst (0 Nat.<_) x-dom-zero x-in-dom)

    bound-injL : ∀ (i : Fin G.nV)
               → count (injL i) (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
    bound-injL i =
      subst (Nat._≤ 1)
        (sym (trans (count-prod (i ↑ˡ cn))
              (trans (cong (Nat._+ count (injL i) (map remapP K-eb))
                           (cong₂ Nat._+_
                             (count-map-↑ˡ cn i G.dom)
                             (count-map-↑ˡ cn i G-eb)))
                     (trans (cong (count i G.dom + count i G-eb Nat.+_)
                                  (count-injL-remapP-K-eb-zero i))
                            (trans (Nat.+-identityʳ _)
                                   (sym (count-++ i G.dom G-eb)))))))
        (G-bnd i)

    bound-raise : ∀ (j : Fin cn)
                → count (G.nV ↑ʳ j) (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
    bound-raise j =
      subst (Nat._≤ 1)
        (sym (trans (count-prod (G.nV ↑ʳ j))
              (trans (cong (Nat._+ count (G.nV ↑ʳ j) (map remapP K-eb))
                           (cong₂ Nat._+_
                             (count-map-↑ˡ-mismatch G.nV j G.dom)
                             (count-map-↑ˡ-mismatch G.nV j G-eb)))
                     refl)))
        (count-remapP-K-eb-≤1 (G.nV ↑ʳ j))

  bound : ∀ v → count v (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
  bound v with splitAt G.nV v in eq
  ... | inj₁ i with splitAt⁻¹-↑ˡ {n = cn} eq
  ...           | refl = bound-injL i
  bound v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
  ...                | refl = bound-raise j

  ------------------------------------------------------------------------
  -- (#4)  The pruned composition preserves linearity.

  Linear-hComposeP-internal : Linear (hComposeP G K bdy-eq)
  Linear-hComposeP-internal = balance , bound

--------------------------------------------------------------------------------
-- (#4) public face, in the exact requested form.

Linear-hComposeP
  : (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  → Linear G → Linear K
  → Linear (hComposeP G K bdy-eq)
Linear-hComposeP G K bdy-eq lin-G lin-K =
  Linear-hComposeP-internal G K bdy-eq lin-G lin-K
