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

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt)
open import Data.Fin.Properties using (_≟_; splitAt-inject+; splitAt-raise)
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

  -- `nonMem xs` has pairwise-distinct entries — it's a filter of `allFin n`.
  nonMem-Unique : (xs : List (Fin n)) → Unique (nonMem xs)
  nonMem-Unique xs =
    Uniq-Prop.filter⁺ (nonMem? xs) (Uniq-Prop.allFin⁺ n)
    where import Data.List.Relation.Unary.Unique.Propositional.Properties
                  as Uniq-Prop

  -- Two ∈-filter⁺ constructions with the same value but different
  -- non-membership proofs produce the same index into nonMem xs.
  -- (By uniqueness of lookup in a Unique list, the index is determined
  -- solely by the value v.)
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

  -- When classify returns inj₂, the scrutinee is not in xs.
  classify-inj₂-∉ : ∀ {xs v j}
                  → classify xs v ≡ inj₂ j → v ∉ xs
  classify-inj₂-∉ {xs} {v} eq v∈ with v ∈? xs
  classify-inj₂-∉ {xs} {v} () _ | yes _
  classify-inj₂-∉ {xs} {v} _  v∈xs | no v∉xs = v∉xs v∈xs

  -- When classify returns inj₁, the scrutinee is in xs.
  classify-inj₁-∈ : ∀ {xs v i}
                  → classify xs v ≡ inj₁ i → v ∈ xs
  classify-inj₁-∈ {xs} {v} eq with v ∈? xs
  classify-inj₁-∈ _ | yes v∈ = v∈
  classify-inj₁-∈ () | no _

  -- For Unique xs, the classify index of `lookup xs j` is `j`.
  -- (The first occurrence of v = lookup xs j in a Unique list xs
  -- is at position j, since v appears only there.)
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
-- `any?` / `∈?` commute with `map` under an injection.
--
-- The decidable membership test is structural on the list — it walks each
-- element and checks `_≟ v`. Under an injection f, `f x ≟ f v` has the
-- same answer as `x ≟ v` (by injectivity in the yes case, vacuously in
-- the no case). So `any? (_≟ f v) (map f xs)` traces the same walk as
-- `any? (_≟ v) xs`, just with every element and the target wrapped in f.
--
-- This lemma is used by `Congruence.hComposeP-resp-≅ᴴ`'s `remapP-comm`,
-- via a `classify`-coherence lemma that reduces to this after some
-- `refl` chasing.

module _ {m n : ℕ}
         (φ : Fin m → Fin n)
         (φ-inj : ∀ {x y : Fin m} → φ x ≡ φ y → x ≡ y)
         where
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Relation.Unary.Any using (here; there)

  -- Inverse of ∉-map-injective: `φ v ∈ map φ xs ⇒ v ∈ xs`.
  -- Dual to `∉-map-injective` (which goes the other way).
  ∈-map-injective⁻ : ∀ {xs : List (Fin m)} {v : Fin m}
                   → φ v ∈ map φ xs → v ∈ xs
  ∈-map-injective⁻ {xs = x ∷ xs} (here eq)    = here (φ-inj eq)
  ∈-map-injective⁻ {xs = x ∷ xs} (there rest) =
    there (∈-map-injective⁻ rest)

  open import Data.Fin using (zero; suc; cast)
  open import Data.List.Properties using (length-map)
  open import Data.List.Membership.Propositional.Properties using (∈-map⁺)

  -- `∈-map⁺ φ` preserves `Any.index` structurally.
  ∈-map⁺-index-cast
    : ∀ {xs : List (Fin m)} {v : Fin m} (v∈xs : v ∈ xs)
    → index (∈-map⁺ φ v∈xs)
    ≡ cast (sym (length-map φ xs)) (index v∈xs)
  ∈-map⁺-index-cast {xs = x ∷ xs} (here refl) = refl
  ∈-map⁺-index-cast {xs = x ∷ xs} (there p)  =
    cong suc (∈-map⁺-index-cast p)

-- Generic lookup-through-map commutation.
module _ {ℓ₁ ℓ₂ : _} {A : Set ℓ₁} {B : Set ℓ₂} where
  open import Data.Fin using (cast)
  open import Data.List.Properties using (length-map)

  lookup-map-cast
    : ∀ (f : A → B) (xs : List A) (i : Fin (length xs))
    → lookup (map f xs) (cast (sym (length-map f xs)) i) ≡ f (lookup xs i)
  lookup-map-cast f (x ∷ xs) zero    = refl
  lookup-map-cast f (x ∷ xs) (suc i) = lookup-map-cast f xs i

  -- Generalization: `lookup ys (cast chain i) ≡ f (lookup xs i)` when
  -- ys ≡ map f xs. Proof by refl-pattern on the equality.
  lookup-≡-map-cast
    : ∀ (f : A → B) {xs : List A} {ys : List B}
        (eq : ys ≡ map f xs)
        (i : Fin (length xs))
    → lookup ys (cast (sym (trans (cong length eq) (length-map f xs))) i)
    ≡ f (lookup xs i)
  lookup-≡-map-cast f {xs = xs} refl i = lookup-map-cast f xs i

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

  -- Key identity: going through pruneMap and then looking up recovers
  -- `φ v` where `v = lookup (nonMem xs) j`. Proved via `lookup-index`
  -- on the `∈-filter⁺` witness inside `pruneMap`.
  lookup-pruneMap : (xs : List (Fin m)) (j : Fin (count-non xs))
                  → lookup (nonMem (map φ xs)) (pruneMap xs j)
                  ≡ φ (lookup (nonMem xs) j)
  lookup-pruneMap xs j =
    sym (lookup-index (∈-filter⁺ (λ u → ¬? (u ∈n? map φ xs))
                                  (∈-allFin (φ (lookup (nonMem xs) j)))
                                  (∉-map-injective φ φ-inj (nonMem-member xs j))))

--------------------------------------------------------------------------------
-- Inverse transport: given a two-sided inverse pair `(φ, φ⁻¹)`, the
-- non-members travel back via `φ⁻¹`. Used for the φ⁻¹ side of the pruned
-- vertex bijection.

module _ {m n : ℕ}
         (φ   : Fin m → Fin n) (φ⁻¹ : Fin n → Fin m)
         (φ-left  : ∀ x → φ⁻¹ (φ x) ≡ x)
         (φ-right : ∀ y → φ (φ⁻¹ y) ≡ y) where
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.Membership.Propositional.Properties using (∈-map⁻)

  -- Injectivity from the left-inverse property.
  φ-inj : ∀ {x y : Fin m} → φ x ≡ φ y → x ≡ y
  φ-inj {x} {y} eq = trans (sym (φ-left x)) (trans (cong φ⁻¹ eq) (φ-left y))

  φ⁻¹-inj : ∀ {x y : Fin n} → φ⁻¹ x ≡ φ⁻¹ y → x ≡ y
  φ⁻¹-inj {x} {y} eq = trans (sym (φ-right x)) (trans (cong φ eq) (φ-right y))

  -- If `φ⁻¹ v ∈ xs` then `v ∈ map φ xs` via `v = φ (φ⁻¹ v)`.
  -- Contrapositive: `v ∉ map φ xs → φ⁻¹ v ∉ xs`.
  private
    ∈-map-via-φ : ∀ {xs : List (Fin m)} {v : Fin n}
                → φ⁻¹ v ∈ xs → v ∈ map φ xs
    ∈-map-via-φ {xs} {v} p =
      subst (_∈ map φ xs) (φ-right v) (∈-map⁺ φ p)
      where open import Data.List.Membership.Propositional.Properties
                       using (∈-map⁺)
            open import Relation.Binary.PropositionalEquality using (subst)

  ∉-map-via-φ : ∀ {xs : List (Fin m)} {v : Fin n}
              → v ∉ map φ xs → φ⁻¹ v ∉ xs
  ∉-map-via-φ v∉ = λ φ⁻¹v∈xs → v∉ (∈-map-via-φ φ⁻¹v∈xs)

  -- Backward direction of the pruned bijection: given k indexing into
  -- nonMem (map φ xs), look up the Fin n value, apply φ⁻¹, and take its
  -- index in nonMem xs.
  open import Data.List.Membership.DecPropositional (_≟_ {n = m})
    using () renaming (_∈?_ to _∈m?_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-filter⁺; ∈-allFin)

  pruneMap⁻¹ : (xs : List (Fin m)) → Fin (count-non (map φ xs))
             → Fin (count-non xs)
  pruneMap⁻¹ xs k =
    index (∈-filter⁺ (λ u → ¬? (u ∈m? xs))
                     (∈-allFin (φ⁻¹ (lookup (nonMem (map φ xs)) k)))
                     (∉-map-via-φ (nonMem-member (map φ xs) k)))

  -- Key identity: going through pruneMap⁻¹ and then looking up recovers
  -- `φ⁻¹` of the chain.
  lookup-pruneMap⁻¹ : (xs : List (Fin m)) (k : Fin (count-non (map φ xs)))
                    → lookup (nonMem xs) (pruneMap⁻¹ xs k)
                    ≡ φ⁻¹ (lookup (nonMem (map φ xs)) k)
  lookup-pruneMap⁻¹ xs k =
    sym (lookup-index (∈-filter⁺ (λ u → ¬? (u ∈m? xs))
                                  (∈-allFin (φ⁻¹ (lookup (nonMem (map φ xs)) k)))
                                  (∉-map-via-φ (nonMem-member (map φ xs) k))))

  -- Shorthand for pruneMap using the derived injectivity.
  pruneMap′ : (xs : List (Fin m)) → Fin (count-non xs)
            → Fin (count-non (map φ xs))
  pruneMap′ = pruneMap φ φ-inj

  lookup-pruneMap′ : (xs : List (Fin m)) (j : Fin (count-non xs))
                   → lookup (nonMem (map φ xs)) (pruneMap′ xs j)
                   ≡ φ (lookup (nonMem xs) j)
  lookup-pruneMap′ = lookup-pruneMap φ φ-inj

  -- Left inverse of pruneMap: `pruneMap⁻¹ ∘ pruneMap ≗ id`.
  pruneMap-left-inverse : (xs : List (Fin m)) (j : Fin (count-non xs))
                        → pruneMap⁻¹ xs (pruneMap′ xs j) ≡ j
  pruneMap-left-inverse xs j =
    lookup-injective-unique (nonMem-Unique xs) _ j eq
    where
      -- lookup (nonMem xs) (pruneMap⁻¹ xs (pruneMap′ xs j))
      -- = φ⁻¹ (lookup (nonMem (map φ xs)) (pruneMap′ xs j))   [lookup-pruneMap⁻¹]
      -- = φ⁻¹ (φ (lookup (nonMem xs) j))                      [lookup-pruneMap′]
      -- = lookup (nonMem xs) j                                [φ-left]
      eq : lookup (nonMem xs) (pruneMap⁻¹ xs (pruneMap′ xs j))
         ≡ lookup (nonMem xs) j
      eq = trans (lookup-pruneMap⁻¹ xs (pruneMap′ xs j))
                 (trans (cong φ⁻¹ (lookup-pruneMap′ xs j))
                        (φ-left (lookup (nonMem xs) j)))

  -- Right inverse: `pruneMap ∘ pruneMap⁻¹ ≗ id`. Symmetric proof.
  pruneMap-right-inverse : (xs : List (Fin m)) (k : Fin (count-non (map φ xs)))
                         → pruneMap′ xs (pruneMap⁻¹ xs k) ≡ k
  pruneMap-right-inverse xs k =
    lookup-injective-unique (nonMem-Unique (map φ xs)) _ k eq
    where
      eq : lookup (nonMem (map φ xs)) (pruneMap′ xs (pruneMap⁻¹ xs k))
         ≡ lookup (nonMem (map φ xs)) k
      eq = trans (lookup-pruneMap′ xs (pruneMap⁻¹ xs k))
                 (trans (cong φ (lookup-pruneMap⁻¹ xs k))
                        (φ-right (lookup (nonMem (map φ xs)) k)))

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
