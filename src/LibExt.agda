{-# OPTIONS --safe --without-K #-}

module LibExt where

open import categorical-crypto.Prelude hiding (take ; _++_ ; _/_)
open import Relation.Binary
open import Categories.Category
open import Categories.Category.Helper
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

-- Arith
import Data.Nat as ℕ
open import Data.Nat.Divisibility using (∣-antisym; ∣-refl)
open import Data.Nat.GCD using (gcd[m,n]∣m; gcd-greatest)
  renaming (gcd to ℕgcd)
open import Data.Integer using (ℤ; +_)
  renaming (_*_ to _*ℤ_; ≢-nonZero to ℤ-≢-nonZero)
open import Data.Integer.GCD using () renaming (gcd to ℤgcd)
import Data.Integer.Properties as ℤP
open import Data.Rational using (ℚ; _/_; ↥_; ↧_; *≡*; 1ℚ)
open import Data.Rational.Properties using (≃⇒≡; ↥-/; ↧-/)

-- Lists
open import Data.List.Base using (_++_; cartesianProduct)
open import Data.List.Properties using (filter-all)
open import Data.List.Membership.Propositional.Properties using
  (∈-∃++; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-cartesianProduct⁺; ∈-cartesianProduct⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_; ↭-refl; ↭-sym; ↭-trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (shift; ∈-resp-↭)

-- Predicates
open import Relation.Unary using (Pred; _∪_; _∩_; ∁; U; _≐_; _⊆_)
open import Relation.Unary using () renaming (_⟨×⟩_ to infixr 6 _⊠_) public
open import Relation.Unary.Properties using (≐-sym)
open import Relation.Nullary.Decidable using (T?)

-- Vec (only used by `take-++`).  Rename `_++_` to avoid clashing with the
-- list `_++_` above; `[]`/`_∷_` are ambiguous with the list versions but
-- Agda's typed-constructor disambiguation handles them.
open import Data.Vec using (Vec; []; _∷_; take) renaming (_++_ to _++ᵛ_)

singleton-≐-rect : ∀ {a b} {A : Set a} {B : Set b} (a : A) (b : B)
                 → ((a , b) ≡_) ≐ ((a ≡_) ⊠ (b ≡_))
singleton-≐-rect a b .proj₁ refl = refl , refl
singleton-≐-rect a b .proj₂ (refl , refl) = refl

------------------------------------------------------------------------
-- Arithmetic: lemmas about ℕ, ℤ and ℚ that are missing from std-lib.

module Arith where
  gcd-self-ℕ : ∀ n → ℕgcd n n ≡ n
  gcd-self-ℕ n = ∣-antisym (gcd[m,n]∣m n n) (gcd-greatest ∣-refl ∣-refl)

  gcd-self-ℤ : ∀ n → ℤgcd (+ n) (+ n) ≡ + n
  gcd-self-ℤ n = cong +_ (gcd-self-ℕ n)

  gcd[+n,+n]≢0 : ∀ n .{{_ : ℕ.NonZero n}} → ℤgcd (+ n) (+ n) ≢ + 0
  gcd[+n,+n]≢0 n@(suc _) eq with () ← trans (sym (gcd-self-ℤ n)) eq

  n/n≡1ℚ : ∀ n .{{_ : ℕ.NonZero n}} → ((+ n) / n) ≡ 1ℚ
  n/n≡1ℚ n@(suc _) = ≃⇒≡ (*≡* eq)
    where
      g = ℤgcd (+ n) (+ n)

      ↥g≡↧g : (↥ ((+ n) / n)) *ℤ g ≡ (↧ ((+ n) / n)) *ℤ g
      ↥g≡↧g = trans (↥-/ (+ n) n) (sym (↧-/ (+ n) n))

      ↥≡↧ : ↥ ((+ n) / n) ≡ ↧ ((+ n) / n)
      ↥≡↧ = ℤP.*-cancelʳ-≡ _ _ g {{ℤ-≢-nonZero (gcd[+n,+n]≢0 n)}} ↥g≡↧g

      eq : (↥ ((+ n) / n)) *ℤ (↧ 1ℚ) ≡ (↥ 1ℚ) *ℤ (↧ ((+ n) / n))
      eq = trans (ℤP.*-identityʳ _) (trans ↥≡↧ (sym (ℤP.*-identityˡ _)))

------------------------------------------------------------------------
-- List helpers: dropping middle elements and traversing cons-lists.

module Lists where
  private variable
    a b p ℓ : Level
    A : Set a
    B : Set b

  -- List cartesian product (alias for std-lib's `cartesianProduct`),
  -- matching standard math notation.
  infixr 5 _×ᴸ_
  _×ᴸ_ : List A → List B → List (A × B)
  _×ᴸ_ = cartesianProduct

  Unique-×ᴸ : {s₁ : List A} {s₂ : List B}
            → Unique s₁ → Unique s₂ → Unique (s₁ ×ᴸ s₂)
  Unique-×ᴸ = UniqueP.cartesianProduct⁺

  All-drop-middle : {P : A → Set p} {y : A} (xs ys : List A)
                  → All P (xs ++ y ∷ ys) → All P (xs ++ ys)
  All-drop-middle []       ys (_ All.∷ a)   = a
  All-drop-middle (x ∷ xs) ys (px All.∷ a)  = px All.∷ All-drop-middle xs ys a

  AllPairs-drop-middle : {R : Rel A ℓ} {y : A} (xs ys : List A)
                       → AllPairs R (xs ++ y ∷ ys) → AllPairs R (xs ++ ys)
  AllPairs-drop-middle []       ys (_ ∷ d) = d
  AllPairs-drop-middle (x ∷ xs) ys (a ∷ d) =
    All-drop-middle xs ys a ∷ AllPairs-drop-middle xs ys d

  ∉-of-distinct-middle : {y : A} (xs ys : List A)
                       → Unique (xs ++ y ∷ ys) → y ∉ˡ (xs ++ ys)
  ∉-of-distinct-middle []       ys (y∉ys ∷ _) y∈           =
    All.lookup y∉ys y∈ refl
  ∉-of-distinct-middle (x ∷ xs) ys (x∉ ∷ _)   (here refl)  =
    All.lookup x∉ (∈-++⁺ʳ xs (here refl)) refl
  ∉-of-distinct-middle (x ∷ xs) ys (_ ∷ d)    (there y∈)   =
    ∉-of-distinct-middle xs ys d y∈

  ∈-tail-≢-head : {b ω : A} {ωs : List A}
                → ω ∈ˡ (b ∷ ωs) → ω ≢ b → ω ∈ˡ ωs
  ∈-tail-≢-head (here refl)  ω≢b = ⊥-elim (ω≢b refl)
  ∈-tail-≢-head (there ω∈ωs) _   = ω∈ωs

  ∈-cons-≐ : (a : A) (xs : List A)
           → (_∈ˡ (a ∷ xs)) ≐ ((a ≡_) ∪ (_∈ˡ xs))
  ∈-cons-≐ a xs = forward , backward
    where
      forward : (_∈ˡ (a ∷ xs)) ⊆ ((a ≡_) ∪ (_∈ˡ xs))
      forward (here ω≡a)   = inj₁ (sym ω≡a)
      forward (there ω∈xs) = inj₂ ω∈xs
      backward : ((a ≡_) ∪ (_∈ˡ xs)) ⊆ (_∈ˡ (a ∷ xs))
      backward (inj₁ a≡ω)   = here (sym a≡ω)
      backward (inj₂ ω∈xs) = there ω∈xs

  -- Membership in the cartesian product as a rectangle predicate equivalence.
  ×ᴸ-≐-rect : (s₁ : List A) (s₂ : List B)
            → (_∈ˡ (s₁ ×ᴸ s₂)) ≐ ((_∈ˡ s₁) ⊠ (_∈ˡ s₂))
  ×ᴸ-≐-rect s₁ s₂ .proj₁ ab∈ = ∈-cartesianProduct⁻ s₁ s₂ ab∈
  ×ᴸ-≐-rect s₁ s₂ .proj₂ (a∈ , b∈) = ∈-cartesianProduct⁺ a∈ b∈

  -- A unique list `t` covering a unique list `s` is a permutation of
  -- `s` followed by the elements of `t` not in `s`.
  partition-↭ : (t s : List A)
              → Unique t → Unique s
              → (∀ {ω} → ω ∈ˡ s → ω ∈ˡ t)
              → ∃ λ extras → t ↭ (s ++ extras)
                           × Unique extras
                           × (∀ {ω} → ω ∈ˡ extras → ω ∉ˡ s)
  partition-↭ t [] t-d _ _ = t , ↭-refl , t-d , λ _ ()
  partition-↭ t (a ∷ s) t-d (a∉s ∷ s-d) s⊆t with ∈-∃++ (s⊆t (here refl))
  ... | t₁ , t₂ , refl =
    extras
    , ↭-trans (shift a t₁ t₂) (Perm.prep a t'↭s++extras)
    , extras-d
    , extras∉a∷s
    where
      t'-d : Unique (t₁ ++ t₂)
      t'-d = AllPairs-drop-middle t₁ t₂ t-d

      a∉t' : a ∉ˡ (t₁ ++ t₂)
      a∉t' = ∉-of-distinct-middle t₁ t₂ t-d

      s⊆t' : ∀ {ω} → ω ∈ˡ s → ω ∈ˡ (t₁ ++ t₂)
      s⊆t' {ω} ω∈s with ∈-++⁻ t₁ (s⊆t (there ω∈s))
      ... | inj₁ ω∈t₁         = ∈-++⁺ˡ ω∈t₁
      ... | inj₂ (here refl)  = ⊥-elim (All.lookup a∉s ω∈s refl)
      ... | inj₂ (there ω∈t₂) = ∈-++⁺ʳ t₁ ω∈t₂

      rec = partition-↭ (t₁ ++ t₂) s t'-d s-d s⊆t'
      extras = proj₁ rec
      t'↭s++extras = proj₁ (proj₂ rec)
      extras-d = proj₁ (proj₂ (proj₂ rec))
      extras∉s = proj₂ (proj₂ (proj₂ rec))

      extras∉a∷s : ∀ {ω} → ω ∈ˡ extras → ω ∉ˡ (a ∷ s)
      extras∉a∷s ω∈ex (here refl)  =
        a∉t' (∈-resp-↭ (↭-sym t'↭s++extras) (∈-++⁺ʳ s ω∈ex))
      extras∉a∷s ω∈ex (there ω∈s) = extras∉s ω∈ex ω∈s

  -- Lemmas that need decidable equality on the carrier.
  module _ {a} {A : Set a} ⦃ deceq-A : DecEq A ⦄ where

    open import Data.List.Membership.DecPropositional (DecEq._≟_ deceq-A) using (_∈?_)

    instance
      ∈ˡ-? : ∀ {s : List A} → (_∈ˡ s) ⁇¹
      ∈ˡ-? {s} = ⁇¹ (_∈? s)

    ∈ˡ-≐-T-∈? : ∀ {s : List A} → (_∈ˡ s) ≐ (T ∘ (λ ω → ⌊ ω ∈? s ⌋))
    ∈ˡ-≐-T-∈? .proj₁ ω∈s = fromWitness ω∈s
    ∈ˡ-≐-T-∈? .proj₂ {ω} ↑ω = toWitness {a? = ω ∈? _} ↑ω

    filterᵇ-self : (s : List A) → filterᵇ (λ ω' → ⌊ ω' ∈? s ⌋) s ≡ s
    filterᵇ-self s = filter-all (T? ∘ (λ ω' → ⌊ ω' ∈? s ⌋))
                                (All.tabulate fromWitness)

------------------------------------------------------------------------
-- Predicate-equivalence helpers built on `Relation.Unary`'s `_≐_` /
-- `_∪_` / `_∩_` / `∁`.

module Predicates where
  private variable
    a p q : Level
    A : Set a

  ∪-∁-LEM : (P : Pred A p) ⦃ P? : P ⁇¹ ⦄ → (P ∪ ∁ P) ≐ U
  proj₁ (∪-∁-LEM P) _ = tt
  proj₂ (∪-∁-LEM P) {x} _ with ¿ P x ¿
  ... | yes Px = inj₁  Px
  ... | no ¬Px = inj₂ ¬Px

  ∩-∁-partition : (B : Pred A p) (P : Pred A q) ⦃ P? : P ⁇¹ ⦄
                → B ≐ (B ∩ P) ∪ (B ∩ ∁ P)
  ∩-∁-partition B P .proj₁ {x} Bx with ¿ P x ¿
  ... | yes Px = inj₁ (Bx ,  Px)
  ... | no ¬Px = inj₂ (Bx , ¬Px)
  ∩-∁-partition B P .proj₂ (inj₁ (Bx , _)) = Bx
  ∩-∁-partition B P .proj₂ (inj₂ (Bx , _)) = Bx

------------------------------------------------------------------------
-- Equivalence and Setoid structure for extensional equality.

IsEquivalence-≗ : ∀ {a b} {A : Set a} {B : Set b} → IsEquivalence (_≗_ {A = A} {B = B})
IsEquivalence-≗ = record
   { refl  = λ _ → refl
   ; sym   = λ x≗y → sym ∘ x≗y
   ; trans = λ i≗j j≗k l → trans (i≗j l) (j≗k l)
   }

≗-setoid : ∀ {a b} {A : Set a} {B : Set b} → Setoid _ _
≗-setoid {A = A} {B} = record
  { Carrier = A → B
  ; _≈_ = _
  ; isEquivalence = IsEquivalence-≗ }

------------------------------------------------------------------------
-- Take on subvector

take-++ : ∀ {m n} {a} {A : Set a} {as : Vec A n} {as' : Vec A m}
  → take n (as ++ᵛ as') ≡ as
take-++ {as = []} = refl
take-++ {as = _ ∷ _} = cong (_ ∷_) take-++

------------------------------------------------------------------------
-- A variant of case that remembers the equality proof

case_of-≡_ : ∀ {ℓ ℓ₁} {A : Set ℓ} {B : Set ℓ₁}
  → (a : A) → ((a' : A) → a ≡ a' → B) → B
case a of-≡ f = f a refl

------------------------------------------------------------------------
-- Pulling back a categorical structure from an isomorphism

module _ {a b b' c c' : Level} (C : Category a b c) where
  module C = Category C

  module _ (hom' : C.Obj → C.Obj → Setoid b' c') (inv : ∀ A B → Inverse (C.hom-setoid {A} {B}) (hom' A B)) where
    module hom' A B = Setoid (hom' A B)
    module inv {A} {B} = Inverse (inv A B)
    open C.HomReasoning using (_⟩∘⟨refl; refl⟩∘⟨_)

    Pullback : Category a b' c'
    Pullback = categoryHelper record
      { Obj = C.Obj
      ; _⇒_ = hom'.Carrier
      ; _≈_ = hom'._≈_ _ _
      ; id = inv.to C.id
      ; _∘_ = λ f g → inv.to (inv.from f C.∘ inv.from g)
      ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → let open C.HomReasoning in inv.to-cong $ begin
        inv.from (inv.to (inv.from h C.∘ inv.from g)) C.∘ inv.from f
          ≈⟨ inv.strictlyInverseʳ _ ⟩∘⟨refl ⟩
        (inv.from h C.∘ inv.from g) C.∘ inv.from f
          ≈⟨ C.assoc ⟩
        inv.from h C.∘ (inv.from g C.∘ inv.from f)
          ≈⟨ refl⟩∘⟨ inv.strictlyInverseʳ _ ⟨
        inv.from h C.∘ inv.from (inv.to (inv.from g C.∘ inv.from f)) ∎
      ; identityˡ = λ {_} {_} {f} → let open SetoidReasoning (hom' _ _) in begin
        inv.to (inv.from (inv.to C.id) C.∘ inv.from f)
          ≈⟨ inv.to-cong (inv.strictlyInverseʳ _ ⟩∘⟨refl) ⟩
        inv.to (C.id C.∘ inv.from f)
          ≈⟨ inv.to-cong C.identityˡ ⟩
        inv.to (inv.from f)
          ≈⟨ inv.strictlyInverseˡ _ ⟩
        f ∎
      ; identityʳ = λ {_} {_} {f} → let open SetoidReasoning (hom' _ _) in begin
        inv.to (inv.from f C.∘ inv.from (inv.to C.id))
          ≈⟨ inv.to-cong (refl⟩∘⟨ inv.strictlyInverseʳ _) ⟩
        inv.to (inv.from f C.∘ C.id)
          ≈⟨ inv.to-cong C.identityʳ ⟩
        inv.to (inv.from f)
          ≈⟨ inv.strictlyInverseˡ _ ⟩
        f ∎
      ; equiv = hom'.isEquivalence _ _
      ; ∘-resp-≈ = λ {_} {_} {_} {f} {g} {h} {i} f≈g h≈i → let open C.HomReasoning in inv.to-cong $ begin
        inv.from f C.∘ inv.from h
          ≈⟨ inv.from-cong f≈g ⟩∘⟨ inv.from-cong h≈i ⟩
        inv.from g C.∘ inv.from i ∎
      }
