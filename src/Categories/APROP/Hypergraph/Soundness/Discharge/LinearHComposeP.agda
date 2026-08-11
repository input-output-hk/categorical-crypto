{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Composition-linearity: the cospan composition `hComposeP` preserves the
-- `Linear` invariant (`Linear-hComposeP`), via injectivity of the K-side
-- vertex remap `remapP = remap K.dom lookup-cod` (`remapP-injective`).
-- The routing baked into `remapP`:
--   * members of K.dom go to `lookup-cod i ↑ˡ count-non K.dom`  (G-side),
--   * non-members go to `G.nV ↑ʳ j`                            (pruned slot).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.LinearHComposeP
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Util.Prune
  using ( count-non; classify; classify-view; is-mem; is-non
        ; remap-inj₁; remap-injective
        ; classify-lookup-Unique
        ; lookup-injective-unique)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using ( count; count-++; count-map-↑ˡ; count-map-inj
        ; count-map-↑ˡ-mismatch; count-swap
        ; producedList; consumedList; Linear; concat-tabulate-blocks)
open import Categories.APROP.Hypergraph.Model.Invariant sig using (↑ˡ≢↑ʳ)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; cast; toℕ)
open import Data.Fin.Properties using
  ( _≟_
  ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ
  ; toℕ-cast; toℕ-injective)
open import Data.List using (List; []; _∷_; _++_; length; map; tabulate; concat; lookup)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.Any using (any?)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (zero; suc; z≤n; _+_)
open import Data.Nat as Nat using ()
import Data.Nat.Properties as Nat
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary.Decidable using (yes; no)

--------------------------------------------------------------------------------
-- Count / permutation helpers.

open import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics sig
  using ( count-cons-yes; ∉→count-zero; count-++-bndˡ; count-++-bndʳ
        ; count-mono-cons; count-map-resp; ∈→count-pos; ++-bnd→disjoint)

private

  -- `cast eq` is injective (preserves `toℕ`).  Stdlib 2.3 lacks
  -- `cast-injective`; derived from `toℕ-cast` + `toℕ-injective`.
  cast-injective : ∀ {m n} (eq : m ≡ n) {i j : Fin m} → cast eq i ≡ cast eq j → i ≡ j
  cast-injective eq {i} {j} ci≡cj =
    toℕ-injective
      (trans (sym (toℕ-cast eq i))
             (trans (cong toℕ ci≡cj) (toℕ-cast eq j)))

  -- `count` over `X ++ C`, where `C` is given as a two-block split `A ++ B`.
  count-split3 : ∀ {n} (v : Fin n) (X : List (Fin n)) {C} (A B : List (Fin n))
               → C ≡ A ++ B → count v (X ++ C) ≡ count v X + count v A + count v B
  count-split3 v X A B refl = trans (count-++ v X (A ++ B))
    (trans (cong (count v X +_) (count-++ v A B)) (sym (Nat.+-assoc (count v X) _ _)))

--------------------------------------------------------------------------------
-- `count _ _ ≤ 1` ⇒ `Unique`.  `Prune.remap-injective` needs `Unique xs`
-- (= `AllPairs _≢_ xs`), but the linearity invariant only supplies
-- `count k xs ≤ 1`.  Short induction: at the head `x ∷ xs`, the bound
-- forces `count x xs ≡ 0`, hence `All (x ≢_) xs`; the tail bound gives
-- `Unique xs`.

private
  -- `count x xs ≡ 0` ⇒ `x ≢` every element of `xs`.
  count-zero→All-≢ : ∀ {n} (x : Fin n) (xs : List (Fin n)) → count x xs ≡ 0 → All.All (x ≢_) xs
  count-zero→All-≢ x []       _ = All.[]
  count-zero→All-≢ x (y ∷ xs) c with x ≟ y
  ... | yes refl = ⊥-elim (case c) where case : suc _ ≡ 0 → ⊥
                                         case ()
  ... | no  x≢y  = x≢y All.∷ count-zero→All-≢ x xs c

count-bnd→Unique : ∀ {n} (xs : List (Fin n)) → (∀ v → count v xs Nat.≤ 1) → Unique xs
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
-- The main construction.

module _
  (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  (lin-G : Linear G) (lin-K : Linear K)
  where

  private
    module G = Hypergraph G
    module K = Hypergraph K
    open hComposeP-impl G K bdy-eq using ( remapP; lookup-cod; dom-cod-len; injL )

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
  -- Bounds carried over from the linearity invariant.

  K-dom-bnd : ∀ k → count k K.dom Nat.≤ 1
  K-dom-bnd k = count-++-bndˡ k K.dom K-eb (K-bnd k)

  G-cod-bnd : ∀ v → count v G.cod Nat.≤ 1
  G-cod-bnd v =
    count-++-bndˡ v G.cod G-ein-b
      (Nat.≤-trans (Nat.≤-reflexive (sym (G-bal v))) (G-bnd v))

  ------------------------------------------------------------------------
  -- `remapP-injective`.

  K-dom-Unique : Unique K.dom
  K-dom-Unique = count-bnd→Unique K.dom K-dom-bnd

  G-cod-Unique : Unique G.cod
  G-cod-Unique = count-bnd→Unique G.cod G-cod-bnd

  -- `lookup-cod` is injective: `lookup G.cod` (injective on a Unique
  -- list) precomposed with the injective `cast`.
  lookup-cod-injective : ∀ {i j : Fin (length K.dom)} → lookup-cod i ≡ lookup-cod j → i ≡ j
  lookup-cod-injective {i} {j} eq =
    cast-injective dom-cod-len
      (lookup-injective-unique G-cod-Unique
        (cast dom-cod-len i) (cast dom-cod-len j) eq)

  -- Injectivity of the pruned K-side vertex remap.
  remapP-injective : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective = remap-injective K.dom lookup-cod K-dom-Unique lookup-cod-injective

  ------------------------------------------------------------------------
  -- `map remapP K.dom ≡ map (_↑ˡ cn) G.cod`.  Each member of K.dom is
  -- routed to `lookup-cod idx ↑ˡ cn`, and `lookup-cod` walks G.cod in
  -- lockstep with K.dom, so the two mapped lists agree.

  private
    -- Pointwise: `remapP (lookup K.dom idx) ≡ lookup-cod idx ↑ˡ cn`.
    remapP-on-dom : ∀ (idx : Fin (length K.dom)) → remapP (lookup K.dom idx) ≡ lookup-cod idx ↑ˡ cn
    remapP-on-dom idx =
      remap-inj₁ K.dom lookup-cod (lookup K.dom idx) idx
        (classify-lookup-Unique K.dom K-dom-Unique idx)

    -- List-extensionality: two `map`s agree when their lengths agree and
    -- they agree pointwise (up to `cast` on the index).
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

  map-remapP-K-dom : map remapP K.dom ≡ map (_↑ˡ cn) G.cod
  map-remapP-K-dom = map-ext-cast remapP (_↑ˡ cn) K.dom G.cod dom-cod-len remapP-on-dom

  -- count facts about `map remapP K.dom` consumed by the balance proof.
  count-map-remapP-K-dom-injL : ∀ (i : Fin G.nV) → count (i ↑ˡ cn) (map remapP K.dom) ≡ count i G.cod
  count-map-remapP-K-dom-injL i = trans (cong (count (i ↑ˡ cn)) map-remapP-K-dom) (count-map-↑ˡ cn i G.cod)

  count-map-remapP-K-dom-raise : ∀ (j : Fin cn) → count (G.nV ↑ʳ j) (map remapP K.dom) ≡ 0
  count-map-remapP-K-dom-raise j =
    trans (cong (count (G.nV ↑ʳ j)) map-remapP-K-dom)
          (count-map-↑ˡ-mismatch G.nV j G.cod)

  ------------------------------------------------------------------------
  -- For BALANCE we only push K-balance through `remapP` via
  -- `count-map-resp` (treating `remapP` opaquely); for BOUND we need to
  -- bound `count v (map remapP K-eb)`, obtained from K-bound via the
  -- fiber lemmas below.

  private
    -- count v (map f xs) ≡ count k xs when f injective and f k = v.  This is
    -- `count-map-inj` with the counted value rewritten along `f k ≡ v`.
    count-map-fiber
      : ∀ {n m} (f : Fin n → Fin m)
      → (∀ {a b} → f a ≡ f b → a ≡ b)
      → (k : Fin n) {v : Fin m} → f k ≡ v
      → ∀ (xs : List (Fin n)) → count v (map f xs) ≡ count k xs
    count-map-fiber f f-inj k {v} eq xs =
      subst (λ w → count w (map f xs) ≡ count k xs) eq (count-map-inj f f-inj k xs)

  ------------------------------------------------------------------------
  -- Structural decompositions of `concat (tabulate eout-c / ein-c)`.

  open hComposeP-impl G K bdy-eq
    using ( eout-c; ein-c
          ; eout-c-inj₁-red; eout-c-inj₂-red
          ; ein-c-inj₁-red; ein-c-inj₂-red )

  eout-comp-eq : concat (tabulate eout-c) ≡ map injL G-eb ++ map remapP K-eb
  eout-comp-eq = concat-tabulate-blocks eout-c G.eout K.eout injL remapP
                   eout-c-inj₁-red eout-c-inj₂-red

  ein-comp-eq : concat (tabulate ein-c) ≡ map injL G-ein-b ++ map remapP K-ein-b
  ein-comp-eq = concat-tabulate-blocks ein-c G.ein K.ein injL remapP
                  ein-c-inj₁-red ein-c-inj₂-red

  ------------------------------------------------------------------------
  -- The dom/cod of the composite (from `hComposeP`'s record):
  --   dom = map injL G.dom ,  cod = map remapP K.cod.

  count-prod
    : ∀ v
    → count v (producedList (hComposeP G K bdy-eq))
    ≡ count v (map injL G.dom)
    + count v (map injL G-eb)
    + count v (map remapP K-eb)
  count-prod v =
    count-split3 v (map injL G.dom) (map injL G-eb) (map remapP K-eb) eout-comp-eq

  count-cons
    : ∀ v
    → count v (consumedList (hComposeP G K bdy-eq))
    ≡ count v (map remapP K.cod)
    + count v (map injL G-ein-b)
    + count v (map remapP K-ein-b)
  count-cons v =
    count-split3 v (map remapP K.cod) (map injL G-ein-b) (map remapP K-ein-b) ein-comp-eq

  ------------------------------------------------------------------------
  -- K-balance pushed through `remapP` (treating remapP opaquely).

  K-bal-via-remapP : ∀ v → count v (map remapP (K.dom ++ K-eb)) ≡ count v (map remapP (K.cod ++ K-ein-b))
  K-bal-via-remapP v = count-map-resp remapP (K.dom ++ K-eb) (K.cod ++ K-ein-b) K-bal v

  ------------------------------------------------------------------------
  -- The "L-side balance" identity.  For v = injL i it combines G-bal with
  -- `map-remapP-K-dom`; for v = raise j both sides are 0.

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
  -- Balance: combining all the pieces.

  balance : ∀ v → count v (producedList (hComposeP G K bdy-eq)) ≡ count v (consumedList (hComposeP G K bdy-eq))
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
      γ = count v (map remapP K-eb)
      δ = count v (map remapP K.cod)
      ε = count v (map injL G-ein-b)
      ζ = count v (map remapP K-ein-b)
      η = count v (map remapP K.dom)

  ------------------------------------------------------------------------
  -- Bound: case-split on `v`.  The produced count decomposes (count-prod)
  -- into the G.dom, G-eb and (map remapP K-eb) contributions.
  --
  --   * For v = raise j: the G-side terms are 0 and the K-eb term is ≤ 1
  --     (it equals `count k K-eb` for the unique remapP-preimage, by
  --     injectivity, bounded by K-bound).
  --   * For v = injL i: the G-side terms sum to ≤ 1 (G-bound), and the
  --     K-eb term is *exactly 0* — any `k ∈ K-eb` with `remapP k ≡ injL i`
  --     would have `k ∈ K.dom` (only K.dom members route to injL slots),
  --     giving count ≥ 2 in `K.dom ++ K-eb`, contradicting K-bound.

  private
    K-eb-bnd : ∀ k → count k K-eb Nat.≤ 1
    K-eb-bnd k = count-++-bndʳ k K.dom K-eb (K-bnd k)

    -- count (any v) in (map remapP K-eb) ≤ 1, via injectivity of remapP.
    -- Decide membership of v in the mapped list: a member has a preimage
    -- `k` (`∈-map⁻`) whose count bounds the v-count; a non-member's count
    -- is 0.
    count-remapP-K-eb-≤1 : ∀ v → count v (map remapP K-eb) Nat.≤ 1
    count-remapP-K-eb-≤1 v with any? (v ≟_) (map remapP K-eb)
    ... | no  v∉ = Nat.≤-trans (Nat.≤-reflexive (∉→count-zero v∉)) z≤n
    ... | yes v∈ with ∈-map⁻ remapP v∈
    ...   | k , _ , v≡rk =
            Nat.≤-trans
              (Nat.≤-reflexive
                (count-map-fiber remapP remapP-injective k (sym v≡rk) K-eb))
              (K-eb-bnd k)

    -- Only K.dom members route to `↑ˡ`-slots (injL).  `Prune.classify-view`
    -- gives both halves in one split: `mem` is the membership witness, whose
    -- count is positive (`∈→count-pos`); `out` reduces `remapP k` to a
    -- `G.nV ↑ʳ_` slot, absurd against `injL i` by `↑ˡ≢↑ʳ`.
    remapP-injL→dom : ∀ (k : Fin K.nV) (i : Fin G.nV) → remapP k ≡ injL i → k ∈ K.dom
    remapP-injL→dom k i rpk with classify K.dom k | classify-view K.dom k
    ... | _ | is-mem k∈ = k∈
    ... | _ | is-non _  = ⊥-elim (↑ˡ≢↑ʳ i _ (sym rpk))

    -- The K-eb contribution at an injL-slot vanishes: a preimage `k`
    -- (`∈-map⁻`) of `injL i` is in K.dom, and K.dom is disjoint from K-eb.
    count-injL-remapP-K-eb-zero : ∀ (i : Fin G.nV) → count (injL i) (map remapP K-eb) ≡ 0
    count-injL-remapP-K-eb-zero i with any? (injL i ≟_) (map remapP K-eb)
    ... | no  i∉ = ∉→count-zero i∉
    ... | yes i∈ with ∈-map⁻ remapP i∈
    ...   | k , k∈ , i≡rk =
            ⊥-elim (++-bnd→disjoint K.dom K-eb (K-bnd k)
                      (remapP-injL→dom k i (sym i≡rk)) k∈)

    bound-injL : ∀ (i : Fin G.nV) → count (injL i) (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
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

    bound-raise : ∀ (j : Fin cn) → count (G.nV ↑ʳ j) (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
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
  -- The pruned composition preserves linearity.

  Linear-hComposeP-internal : Linear (hComposeP G K bdy-eq)
  Linear-hComposeP-internal = balance , bound

--------------------------------------------------------------------------------
-- Public face.

Linear-hComposeP
  : (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  → Linear G → Linear K
  → Linear (hComposeP G K bdy-eq)
Linear-hComposeP G K bdy-eq lin-G lin-K = Linear-hComposeP-internal G K bdy-eq lin-G lin-K
