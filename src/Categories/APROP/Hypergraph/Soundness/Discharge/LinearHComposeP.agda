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
  using ( count-non; classify; classify-view; ClassifyV; is-mem; is-non
        ; remap-inj₁; remap-injective
        ; classify-lookup-Unique
        ; lookup-injective-unique)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using ( count; count-++; count-map-↑ˡ; count-map-inj
        ; count-map-↑ˡ-mismatch; count-swap
        ; producedList; consumedList; Linear; tabulate-+)
open import Categories.APROP.Hypergraph.Model.Invariant sig using (↑ˡ≢↑ʳ)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; cast; toℕ)
open import Data.Fin.Properties using
  ( _≟_
  ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ
  ; toℕ-cast; toℕ-injective)
open import Data.List as List using (List; []; _∷_; _++_; length; map; tabulate; concat; lookup)
open import Data.List.Properties using
  ( map-++
  ; tabulate-cong; map-tabulate; concat-map; concat-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Function as Fun
open import Data.Nat using (zero; suc; s≤s; z≤n; _+_)
open import Data.Nat as Nat using ()
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≢_)

--------------------------------------------------------------------------------
-- Count / permutation helpers.

open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.CountCombinatorics sig
  using ( count-cons-yes; count-cons-no
        ; count-mono-cons; count-map-resp; ∈→count-pos)

private

  -- `cast eq` is injective (preserves `toℕ`).  Stdlib 2.3 lacks
  -- `cast-injective`; derived from `toℕ-cast` + `toℕ-injective`.
  cast-injective : ∀ {m n} (eq : m ≡ n) {i j : Fin m} → cast eq i ≡ cast eq j → i ≡ j
  cast-injective eq {i} {j} ci≡cj =
    toℕ-injective
      (trans (sym (toℕ-cast eq i))
             (trans (cong toℕ ci≡cj) (toℕ-cast eq j)))

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

    -- count v (map f xs) ≡ 0 when no element of `xs` maps to v.  The
    -- count-zero hypothesis is keyed on preimages so it threads through
    -- the recursion without a `y ≟ x` case-split (which would clash with
    -- `count`'s internal `≟`).
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
        tail-zero y c0 = Nat.≤-antisym (Nat.≤-trans (count-mono-cons y x xs) (Nat.≤-reflexive c0)) z≤n

  ------------------------------------------------------------------------
  -- Structural decompositions of `concat (tabulate eout-c / ein-c)`.

  open hComposeP-impl G K bdy-eq
    using ( eout-c; ein-c
          ; eout-c-inj₁-red; eout-c-inj₂-red
          ; ein-c-inj₁-red; ein-c-inj₂-red )

  eout-comp-eq : concat (tabulate eout-c) ≡ map injL G-eb ++ map remapP K-eb
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

  ein-comp-eq : concat (tabulate ein-c) ≡ map injL G-ein-b ++ map remapP K-ein-b
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
    K-eb-bnd k =
      Nat.≤-trans
        (Nat.≤-trans (Nat.m≤n+m (count k K-eb) (count k K.dom))
                     (Nat.≤-reflexive (sym (count-++ k K.dom K-eb))))
        (K-bnd k)

    -- count (any v) in (map remapP K-eb) ≤ 1, via injectivity of remapP.
    -- Search K-eb for a preimage of v: if found the v-count equals
    -- `count k K-eb` (bounded by K-bound); else the v-count is 0.
    count-remapP-K-eb-≤1 : ∀ v → count v (map remapP K-eb) Nat.≤ 1
    count-remapP-K-eb-≤1 v with search K-eb
      where
        -- Either some element of `xs` is a preimage of v, or every
        -- preimage of v has count 0 in `xs`.
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
                y≢x : ¬ (y ≡ x)
                y≢x y≡x = q (subst (λ z → remapP z ≡ v) y≡x rpy)
    ... | inj₁ (k , rpk) =
          Nat.≤-trans
            (Nat.≤-reflexive (count-map-fiber remapP remapP-injective k rpk K-eb))
            (K-eb-bnd k)
    ... | inj₂ none = Nat.≤-trans (Nat.≤-reflexive (count-map-no-list-preimage remapP K-eb none)) z≤n

    -- Only K.dom members route to `↑ˡ`-slots (injL).  `Prune.classify-view`
    -- gives both halves in one split: `mem` is the membership witness, whose
    -- count is positive (`∈→count-pos`); `out` reduces `remapP k` to a
    -- `G.nV ↑ʳ_` slot, absurd against `injL i` by `↑ˡ≢↑ʳ`.
    remapP-injL→inDom : ∀ (k : Fin K.nV) (i : Fin G.nV) → remapP k ≡ injL i → 0 Nat.< count k K.dom
    remapP-injL→inDom k i rpk with classify K.dom k | classify-view K.dom k
    ... | _ | is-mem k∈ = ∈→count-pos k∈
    ... | _ | is-non _  = ⊥-elim (↑ˡ≢↑ʳ i _ (sym rpk))

    -- The K-eb contribution at an injL-slot vanishes.
    count-injL-remapP-K-eb-zero : ∀ (i : Fin G.nV) → count (injL i) (map remapP K-eb) ≡ 0
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
            x-in-dom→absurd = Nat.<-irrefl refl (subst (0 Nat.<_) x-dom-zero x-in-dom)

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
