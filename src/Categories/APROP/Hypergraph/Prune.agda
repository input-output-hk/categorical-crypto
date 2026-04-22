{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Pruning helpers for a canonical `hCompose` (TODO.org Option A).
--
-- Given `xs : List (Fin n)` (typically `K.dom` of the right operand of a
-- cospan composition), we want to identify the Fin values NOT in `xs`.
-- After composition, the positions named in `xs` have been "glued" to the
-- left operand's `cod`, so they become unreferenced and can be pruned.
--
-- This module provides:
--   * `nonMem xs`     — the list of Fin values not in `xs`.
--   * `count-non xs`  — its length (the count of "survivors").
--   * `classify xs v` — cases `v : Fin n` as either a position in `xs`
--                       or a position in `nonMem xs`.
--   * `remap xs f`    — combinator that routes members of `xs` to an
--                       arbitrary target space via `f`, and non-members
--                       to the fresh pruned space of size `count-non xs`.
--
-- The canonical `hCompose` will have vertex count
--   `G.nV + count-non K.dom`
-- and a `remap` that sends each K-vertex to either:
--   * a G-side position (if the vertex was in `K.dom`), via
--     `f i = G.cod[i]` composed with `inject+`, or
--   * a fresh pruned-K-side position (via an index lookup in `nonMem K.dom`).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Prune where

open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt)
open import Data.Fin.Properties using (_≟_; splitAt-inject+; splitAt-raise)
open import Data.List using (List; []; _∷_; length; filter; allFin; lookup; map)
open import Data.List.Properties using (map-cong; map-∘)
open import Data.List.Relation.Unary.Any using (index)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (¬?; yes; no)

--------------------------------------------------------------------------------
-- Non-members of a Fin list.

module _ {n : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-filter⁺; ∈-allFin)
  open import Relation.Nullary.Decidable using (Dec)

  -- The predicate "v is not in xs", as a decidable.
  nonMem? : (xs : List (Fin n)) → (v : Fin n) → Dec (v ∉ xs)
  nonMem? xs v = ¬? (v ∈? xs)

  -- The Fin values not present in `xs`.
  nonMem : List (Fin n) → List (Fin n)
  nonMem xs = filter (nonMem? xs) (allFin n)

  -- Count of Fin values not in `xs`.
  count-non : List (Fin n) → ℕ
  count-non xs = length (nonMem xs)

  -- Classify `v : Fin n` as either a member of `xs` (paired with its index
  -- into `xs`) or a non-member (paired with its index into `nonMem xs`).
  classify : (xs : List (Fin n)) (v : Fin n) → Fin (length xs) ⊎ Fin (count-non xs)
  classify xs v with v ∈? xs
  ... | yes v∈xs = inj₁ (index v∈xs)
  ... | no  v∉xs =
    inj₂ (index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉xs))

  -- Inversion: when classify returns `inj₁ i`, the member slot `i` in
  -- `xs` looks back to `v`.
  classify-inj₁-lookup : (xs : List (Fin n)) (v : Fin n) (i : Fin (length xs))
                       → classify xs v ≡ inj₁ i
                       → lookup xs i ≡ v
  classify-inj₁-lookup xs v i eq with v ∈? xs
  classify-inj₁-lookup xs v .(index v∈xs) refl
    | yes v∈xs = sym (lookup-index v∈xs)

  -- Inversion: when classify returns `inj₂ j`, the non-member slot `j` in
  -- `nonMem xs` looks back to `v`. This is the key lemma used by the
  -- pruned `hCompose` to recover vertex labels from the pruned space.
  classify-inj₂-lookup : (xs : List (Fin n)) (v : Fin n) (j : Fin (count-non xs))
                       → classify xs v ≡ inj₂ j
                       → lookup (nonMem xs) j ≡ v
  classify-inj₂-lookup xs v j eq with v ∈? xs
  classify-inj₂-lookup xs v .(index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉xs)) refl
    | no v∉xs = sym (lookup-index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉xs))

  -- "Dom covers all vertices": every vertex of Fin n is in xs.
  AllIn : List (Fin n) → Set
  AllIn xs = ∀ (v : Fin n) → v ∈ xs

  -- When xs covers everything, nonMem xs is empty — every candidate in
  -- `allFin n` fails the `¬ (v ∈ xs)` filter.
  AllIn→nonMem-[] : ∀ {xs} → AllIn xs → nonMem xs ≡ []
  AllIn→nonMem-[] {xs} all = filter-none all (allFin n)
    where
      open import Data.Empty using (⊥-elim)

      -- If every y in ys is in xs, the ¬? filter drops them all.
      filter-none : (∀ v → v ∈ xs)
                  → (ys : List (Fin n))
                  → filter (λ v → ¬? (v ∈? xs)) ys ≡ []
      filter-none _     []       = refl
      filter-none all-xs (y ∷ ys) with y ∈? xs
      ... | yes _ = filter-none all-xs ys
      ... | no  ¬p = ⊥-elim (¬p (all-xs y))

  -- Hence count-non xs = 0.
  AllIn→count-non-zero : ∀ {xs} → AllIn xs → count-non xs ≡ 0
  AllIn→count-non-zero all = cong length (AllIn→nonMem-[] all)

  -- A pruned index `j` in `nonMem xs` looks up to a Fin value that
  -- really is a non-member of `xs`.
  nonMem-member : (xs : List (Fin n)) (j : Fin (count-non xs))
                → lookup (nonMem xs) j ∉ xs
  nonMem-member xs j =
    proj₂ (∈-filter⁻ (nonMem? xs) {xs = allFin n}
                     (∈-lookup {xs = nonMem xs} j))
    where
      open import Data.List.Membership.Propositional.Properties
        using (∈-filter⁻; ∈-lookup)
      open import Data.Product using (proj₂)

--------------------------------------------------------------------------------
-- Injective maps transport (non-)membership.
--
-- If `φ` is injective and `v ∉ xs`, then `φ v ∉ map φ xs`. Used in the
-- eventual `hComposeP-resp-≅ᴴ` port to lift the K-side iso through the
-- pruned space: `K₂.dom ≡ map φ K₁.dom` means φ carries `nonMem K₁.dom`
-- into `nonMem K₂.dom`.

module _ {m n : ℕ} (φ : Fin m → Fin n)
         (φ-inj : ∀ {x y : Fin m} → φ x ≡ φ y → x ≡ y) where
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Relation.Unary.Any using (here; there)

  ∉-map-injective : ∀ {xs : List (Fin m)} {v : Fin m}
                  → v ∉ xs → φ v ∉ map φ xs
  ∉-map-injective {xs = []}     _    ()
  ∉-map-injective {xs = x ∷ xs} v∉xs (here eq)    = v∉xs (here (φ-inj eq))
  ∉-map-injective {xs = x ∷ xs} v∉xs (there rest) =
    ∉-map-injective (λ v∈xs → v∉xs (there v∈xs)) rest

--------------------------------------------------------------------------------
-- Pruned-space transport.
--
-- If `φ : Fin m → Fin n` is an injection and `ys = map φ xs`, then the
-- non-members of `xs` map into non-members of `ys`, yielding
--   pruneMap : Fin (count-non xs) → Fin (count-non (map φ xs)).
-- The K-side vertex bijection in a ported `hComposeP-resp-≅ᴴ` routes
-- through this without leaving `--safe --without-K`.

module _ {m n : ℕ} (φ : Fin m → Fin n)
         (φ-inj : ∀ {x y : Fin m} → φ x ≡ φ y → x ≡ y) where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n})
    using () renaming (_∈?_ to _∈n?_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-filter⁺; ∈-allFin)

  -- Forward direction of the pruned bijection.
  pruneMap : (xs : List (Fin m)) → Fin (count-non xs)
           → Fin (count-non (map φ xs))
  pruneMap xs j =
    index (∈-filter⁺ (λ u → ¬? (u ∈n? map φ xs))
                     (∈-allFin (φ (lookup (nonMem xs) j)))
                     (∉-map-injective φ φ-inj (nonMem-member xs j)))

--------------------------------------------------------------------------------
-- Remap combinator.
--
-- Given xs ⊂ Fin n and a target map f : Fin (length xs) → Fin m for
-- members of xs, produces Fin n → Fin (m + count-non xs) by routing
-- members to `inject+ (count-non xs) (f i)` and non-members to
-- `raise m j` where j is the non-member's index in `nonMem xs`.

module _ {n m : ℕ} where
  remap : (xs : List (Fin n)) → (Fin (length xs) → Fin m)
        → Fin n → Fin (m + count-non xs)
  remap xs f v = [ (λ i → inject+ (count-non xs) (f i))
                 , (λ j → raise m j)
                 ]′ (classify xs v)

  -- Reduction of `remap` in the `inj₁` (member) case.
  remap-inj₁ : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (v : Fin n) (i : Fin (length xs))
             → classify xs v ≡ inj₁ i
             → remap xs f v ≡ inject+ (count-non xs) (f i)
  remap-inj₁ xs f v i eq with classify xs v
  remap-inj₁ xs f v i refl | inj₁ .i = refl

  -- Reduction of `remap` in the `inj₂` (non-member) case.
  remap-inj₂ : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (v : Fin n) (j : Fin (count-non xs))
             → classify xs v ≡ inj₂ j
             → remap xs f v ≡ raise m j
  remap-inj₂ xs f v j eq with classify xs v
  remap-inj₂ xs f v j refl | inj₂ .j = refl

--------------------------------------------------------------------------------
-- Label preservation.
--
-- The key lemma that makes the pruned `hCompose` work. Given:
--   * xs : List (Fin n)           — positions to prune (e.g., K.dom)
--   * f  : Fin (length xs) → Fin m — target map for member positions
--   * λK : Fin n → X              — labels for the source (K-side)
--   * λG : Fin m → X              — labels for the target (G-side)
--   * pointwise boundary agreement: ∀ i → λK (xs[i]) ≡ λG (f i)
--
-- The "pruned composite labeling" is
--   vlab-c : Fin (m + count-non xs) → X
--   vlab-c = [ λG , λ-non ]′ ∘ splitAt m
-- where λ-non j = λK (lookup (nonMem xs) j) reads back through the pruned
-- index. Then `vlab-c (remap xs f v) ≡ λK v` for every v : Fin n — the
-- pruning preserves K-side labels.

module _ {a} {X : Set a} {n m : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-filter⁺; ∈-allFin)

  remap-vlab : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (λK : Fin n → X) (λG : Fin m → X)
               (bdy : ∀ i → λK (lookup xs i) ≡ λG (f i))
               (v : Fin n)
             → [ λG , (λ j → λK (lookup (nonMem xs) j)) ]′
                  (splitAt m (remap xs f v))
             ≡ λK v
  remap-vlab xs f λK λG bdy v with v ∈? xs
  ... | yes v∈xs =
    -- classify xs v reduces to inj₁ (index v∈xs), so
    -- remap xs f v = inject+ (count-non xs) (f (index v∈xs)).
    trans
      (cong [ λG , (λ k → λK (lookup (nonMem xs) k)) ]′
        (splitAt-inject+ m (count-non xs) (f (index v∈xs))))
      (trans (sym (bdy (index v∈xs)))
             (cong λK (sym (lookup-index v∈xs))))
  ... | no v∉xs =
    -- classify xs v reduces to inj₂ (index v∈nonMem), so
    -- remap xs f v = raise m (index v∈nonMem).
    let v∈nonMem = ∈-filter⁺ (λ u → ¬? (u ∈? xs)) (∈-allFin v) v∉xs in
    trans
      (cong [ λG , (λ k → λK (lookup (nonMem xs) k)) ]′
        (splitAt-raise m (count-non xs) (index v∈nonMem)))
      (cong λK (sym (lookup-index v∈nonMem)))

  -- List-wise version of `remap-vlab`: the labels of any list of K-vertices
  -- agree with the labels obtained by going through `remap` and then the
  -- pruned `vlab-c = [ λG , _ ]′ ∘ splitAt m`.
  map-via-remap : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
                  (λK : Fin n → X) (λG : Fin m → X)
                  (bdy : ∀ i → λK (lookup xs i) ≡ λG (f i))
                  (ys : List (Fin n))
                → map λK ys
                ≡ map ([ λG , (λ j → λK (lookup (nonMem xs) j)) ]′ ∘ splitAt m)
                      (map (remap xs f) ys)
  map-via-remap xs f λK λG bdy ys =
    trans (sym (map-cong (remap-vlab xs f λK λG bdy) ys))
          (map-∘ ys)
