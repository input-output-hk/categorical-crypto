{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Pruning helpers for a canonical `hCompose`.
--
-- Given `xs : List (Fin n)` (typically `K.dom` of the right operand of a
-- cospan composition), identify the Fin values NOT in `xs`.  After
-- composition the positions named in `xs` have been "glued" to the left
-- operand's `cod`, so they become unreferenced and can be pruned.
--
--   * `nonMem xs`     — the Fin values not in `xs`.
--   * `count-non xs`  — its length (the "survivors").
--   * `classify xs v` — cases `v` as a position in `xs` or in `nonMem xs`.
--   * `remap xs f`    — routes members of `xs` to an arbitrary target space
--                       via `f`, non-members to the fresh pruned space of
--                       size `count-non xs`.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Prune where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (_≟_; splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List using (List; []; _∷_; length; filter; allFin; lookup; map)
open import Data.List.Properties using (map-cong; map-∘)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (index)
open import Data.List.Relation.Unary.Any.Properties using (lookup-index)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (¬?; yes; no)

--------------------------------------------------------------------------------
-- Generic list/uniqueness helpers (not Fin-specific).

module _ {ℓ} {A : Set ℓ} where
  -- Apply an `All P xs` witness at a Fin position.
  All-lookup : ∀ {p} {P : A → Set p} {xs : List A}
             → All P xs → (i : Fin (length xs)) → P (lookup xs i)
  All-lookup (p ∷ _)  zero    = p
  All-lookup (_ ∷ ps) (suc i) = All-lookup ps i

  -- Unique lists have injective `lookup`.
  lookup-injective-unique : ∀ {xs : List A}
                          → Unique xs
                          → ∀ (i j : Fin (length xs))
                          → lookup xs i ≡ lookup xs j
                          → i ≡ j
  lookup-injective-unique {xs = _ ∷ _ } (_  AllPairs.∷ _ ) zero    zero    _  = refl
  lookup-injective-unique {xs = _ ∷ _ } (x≢ AllPairs.∷ _ ) zero    (suc j) eq =
    ⊥-elim (All-lookup x≢ j eq)
  lookup-injective-unique {xs = _ ∷ _ } (x≢ AllPairs.∷ _ ) (suc i) zero    eq =
    ⊥-elim (All-lookup x≢ i (sym eq))
  lookup-injective-unique {xs = _ ∷ _ } (_  AllPairs.∷ uq) (suc i) (suc j) eq =
    cong suc (lookup-injective-unique uq i j eq)

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
  nonMem-Unique : (xs : List (Fin n)) → Unique (nonMem xs)
  nonMem-Unique xs =
    Uniq-Prop.filter⁺ (nonMem? xs) (Uniq-Prop.allFin⁺ n)
    where import Data.List.Relation.Unary.Unique.Propositional.Properties
                  as Uniq-Prop

  -- Two ∈-filter⁺ constructions with the same value but different
  -- non-membership proofs produce the same index into nonMem xs (the index
  -- is determined solely by `v`, by uniqueness of lookup).
  index-∈-filter-irrelevant
    : ∀ (xs : List (Fin n)) (v : Fin n)
        (v∉₁ v∉₂ : v ∉ xs)
    → index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉₁)
    ≡ index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉₂)
  index-∈-filter-irrelevant xs v v∉₁ v∉₂ =
    lookup-injective-unique (nonMem-Unique xs) _ _
      (trans (sym (lookup-index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉₁)))
             (lookup-index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉₂)))

  -- `subst` through an equality of lists commutes with `∈-filter⁺`+`index`:
  -- transporting the index across `xs ≡ ys` is the same as reconstructing
  -- the ∈-filter⁺ at `ys` with the transported non-membership proof.
  subst-∈-filter-index
    : ∀ {xs ys : List (Fin n)} (eq : xs ≡ ys) (v : Fin n) (v∉xs : v ∉ xs)
    → subst (λ zs → Fin (count-non zs)) eq
            (index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉xs))
    ≡ index (∈-filter⁺ (nonMem? ys) (∈-allFin v) (subst (v ∉_) eq v∉xs))
  subst-∈-filter-index refl v v∉xs = refl

  -- `lookup (nonMem ys)` at a subst-transported index from
  -- `Fin (count-non xs)` agrees with `lookup (nonMem xs)` at the
  -- original index.
  subst-lookup-nonMem
    : ∀ {xs ys : List (Fin n)} (eq : xs ≡ ys) (j : Fin (count-non xs))
    → lookup (nonMem ys) (subst (λ zs → Fin (count-non zs)) eq j)
    ≡ lookup (nonMem xs) j
  subst-lookup-nonMem refl j = refl

  -- When classify returns inj₁, the scrutinee is in xs.
  classify-inj₁-∈ : ∀ {xs v i}
                  → classify xs v ≡ inj₁ i → v ∈ xs
  classify-inj₁-∈ {xs} {v} eq with v ∈? xs
  classify-inj₁-∈ _ | yes v∈ = v∈
  classify-inj₁-∈ () | no _

  -- For Unique xs, the classify index of `lookup xs j` is `j`.
  classify-lookup-Unique
    : (xs : List (Fin n)) → Unique xs
    → (j : Fin (length xs))
    → classify xs (lookup xs j) ≡ inj₁ j
  classify-lookup-Unique xs unique j
    with lookup xs j ∈? xs
  ... | yes v∈ = cong inj₁
    (lookup-injective-unique unique (index v∈) j (sym (lookup-index v∈)))
  ... | no  v∉ = ⊥-elim (v∉ ∈-lookup-helper)
    where
      open import Data.List.Membership.Propositional.Properties
        using () renaming (∈-lookup to ∈-lookup-std)
      ∈-lookup-helper : lookup xs j ∈ xs
      ∈-lookup-helper = ∈-lookup-std j

  -- Dual to `classify-lookup-Unique`: for `j : Fin (count-non xs)`,
  -- `classify xs (lookup (nonMem xs) j) ≡ inj₂ j`.
  classify-lookup-nonMem
    : (xs : List (Fin n)) (j : Fin (count-non xs))
    → classify xs (lookup (nonMem xs) j) ≡ inj₂ j
  classify-lookup-nonMem xs j
    with lookup (nonMem xs) j ∈? xs
  -- impossible: `lookup (nonMem xs) j` is by construction NOT in xs.
  ... | yes v∈ = ⊥-elim (nonMem-member-helper v∈)
    where
      open import Data.List.Membership.Propositional.Properties
        using (∈-filter⁻; ∈-lookup)
      open import Data.Product using (proj₂)
      nonMem-member-helper : lookup (nonMem xs) j ∈ xs → ⊥
      nonMem-member-helper =
        proj₂ (∈-filter⁻ (nonMem? xs) {xs = allFin n}
                         (∈-lookup {xs = nonMem xs} j))
  ... | no  v∉ = cong inj₂
    (lookup-injective-unique
      (nonMem-Unique xs)
      (index w) j
      (sym (lookup-index w)))
    where
      w : lookup (nonMem xs) j ∈ nonMem xs
      w = ∈-filter⁺ (nonMem? xs) (∈-allFin (lookup (nonMem xs) j)) v∉

--------------------------------------------------------------------------------
-- Remap combinator.  Given `xs ⊂ Fin n` and a target map `f : Fin (length
-- xs) → Fin m`, produces `Fin n → Fin (m + count-non xs)` routing members to
-- `f i ↑ˡ count-non xs` and non-members to `m ↑ʳ j`.

module _ {n m : ℕ} where
  remap : (xs : List (Fin n)) → (Fin (length xs) → Fin m)
        → Fin n → Fin (m + count-non xs)
  remap xs f v = [ (λ i → f i ↑ˡ count-non xs)
                 , (λ j → m ↑ʳ j)
                 ]′ (classify xs v)

  -- Reduction of `remap` in the `inj₁` (member) case.
  remap-inj₁ : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (v : Fin n) (i : Fin (length xs))
             → classify xs v ≡ inj₁ i
             → remap xs f v ≡ f i ↑ˡ count-non xs
  remap-inj₁ xs f v i eq with classify xs v
  remap-inj₁ xs f v i refl | inj₁ .i = refl

  -- Reduction of `remap` in the `inj₂` (non-member) case.
  remap-inj₂ : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (v : Fin n) (j : Fin (count-non xs))
             → classify xs v ≡ inj₂ j
             → remap xs f v ≡ m ↑ʳ j
  remap-inj₂ xs f v j eq with classify xs v
  remap-inj₂ xs f v j refl | inj₂ .j = refl

--------------------------------------------------------------------------------
-- Label preservation — the key lemma that makes the pruned `hCompose` work.
-- Given source/target labelings `λK`/`λG` with pointwise boundary agreement
-- `∀ i → λK (xs[i]) ≡ λG (f i)`, the pruned composite labeling `[ λG , λ-non
-- ]′ ∘ splitAt m` (with `λ-non j = λK (lookup (nonMem xs) j)`) satisfies
-- `vlab-c (remap xs f v) ≡ λK v` for every `v`.

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
    trans
      (cong [ λG , (λ k → λK (lookup (nonMem xs) k)) ]′
        (splitAt-↑ˡ m (f (index v∈xs)) (count-non xs)))
      (trans (sym (bdy (index v∈xs)))
             (cong λK (sym (lookup-index v∈xs))))
  ... | no v∉xs =
    let v∈nonMem = ∈-filter⁺ (λ u → ¬? (u ∈? xs)) (∈-allFin v) v∉xs in
    trans
      (cong [ λG , (λ k → λK (lookup (nonMem xs) k)) ]′
        (splitAt-↑ʳ m (count-non xs) (index v∈nonMem)))
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

--------------------------------------------------------------------------------
-- Global injectivity of `remap xs f`, assuming `Unique xs` and `f`
-- injective.  Members route to `↑ˡ` slots and non-members to `↑ʳ` slots;
-- distinct inputs yield distinct outputs because lookup is injective on
-- `Unique xs` / `nonMem xs`, and the two slot families are disjoint.

module _ {n m : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-allFin)
  open import Data.Sum using (inj₁; inj₂)

  -- `_↑ˡ k` is injective for any fixed `k` (local, to avoid `Invariant`).
  ↑ˡ-inj : ∀ {n} (k : ℕ) {i j : Fin n}
         → i ↑ˡ k ≡ j ↑ˡ k → i ≡ j
  ↑ˡ-inj {n} k {i} {j} eq
    with splitAt-↑ˡ n i k | splitAt-↑ˡ n j k | cong (splitAt n) eq
  ... | i-red | j-red | split-eq =
    inj₁-inj (trans (sym i-red) (trans split-eq j-red))
    where
      inj₁-inj : ∀ {X Y : Set} {x y : X} → inj₁ {B = Y} x ≡ inj₁ y → x ≡ y
      inj₁-inj refl = refl

  ↑ʳ-inj : ∀ (k : ℕ) {n} {i j : Fin n}
         → k ↑ʳ i ≡ k ↑ʳ j → i ≡ j
  ↑ʳ-inj k {n} {i} {j} eq
    with splitAt-↑ʳ k n i | splitAt-↑ʳ k n j | cong (splitAt k) eq
  ... | i-red | j-red | split-eq =
    inj₂-inj (trans (sym i-red) (trans split-eq j-red))
    where
      inj₂-inj : ∀ {X Y : Set} {x y : Y} → inj₂ {A = X} x ≡ inj₂ y → x ≡ y
      inj₂-inj refl = refl

  -- Disjointness of `_↑ˡ k` and `m ↑ʳ_` ranges.
  ↑ˡ-↑ʳ-disjoint : (k : ℕ) (i : Fin m) (j : Fin k)
                 → i ↑ˡ k ≡ m ↑ʳ j → ⊥
  ↑ˡ-↑ʳ-disjoint k i j eq
    with splitAt-↑ˡ m i k | splitAt-↑ʳ m k j | cong (splitAt m) eq
  ... | i-red | j-red | split-eq =
    case-absurd (trans (sym i-red) (trans split-eq j-red))
    where
      case-absurd : ∀ {X Y : Set} {x : X} {y : Y} → inj₁ x ≡ inj₂ y → ⊥
      case-absurd ()

  remap-injective
    : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
    → Unique xs
    → (∀ {i j : Fin (length xs)} → f i ≡ f j → i ≡ j)
    → ∀ {v v' : Fin n} → remap xs f v ≡ remap xs f v' → v ≡ v'
  remap-injective xs f xs-uniq f-inj {v} {v'} eq with v ∈? xs | v' ∈? xs
  ... | yes v∈ | yes v'∈ =
    -- Both members: `↑ˡ-inj` + `f-inj` + `lookup-index`.
    trans (lookup-index v∈)
      (trans (cong (lookup xs) idx-eq) (sym (lookup-index v'∈)))
    where
      f-eq : f (index v∈) ≡ f (index v'∈)
      f-eq = ↑ˡ-inj (count-non xs) eq
      idx-eq : index v∈ ≡ index v'∈
      idx-eq = f-inj f-eq
  ... | yes v∈ | no v'∉ = ⊥-elim (↑ˡ-↑ʳ-disjoint _ _ _ eq)
  ... | no v∉  | yes v'∈ = ⊥-elim (↑ˡ-↑ʳ-disjoint _ _ _ (sym eq))
  ... | no v∉  | no v'∉ =
    -- Both non-members: `↑ʳ-inj` + `lookup-index` on `nonMem` indices.
    trans (lookup-index v∈nonMem)
      (trans (cong (lookup (nonMem xs)) idx-eq) (sym (lookup-index v'∈nonMem)))
    where
      v∈nonMem : v ∈ nonMem xs
      v∈nonMem = ∈-filter⁺ (λ u → ¬? (u ∈? xs)) (∈-allFin v) v∉
      v'∈nonMem : v' ∈ nonMem xs
      v'∈nonMem = ∈-filter⁺ (λ u → ¬? (u ∈? xs)) (∈-allFin v') v'∉
      idx-eq : index v∈nonMem ≡ index v'∈nonMem
      idx-eq = ↑ʳ-inj m eq
