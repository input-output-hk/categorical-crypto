{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive closure of `SelfLoopPostulate.B-swap` via a triple-lex
-- measure `(size, total-l, swap-count)`.
--
-- ## Strategy
--
-- The B-swap σ-cascade case in `SigmaCascadeResidual` is:
--
--   p = trans (swap k k' a) (trans (swap k' k b) Y) : (k ∷ k' ∷ rest) ↭ (k ∷ k' ∷ rest)
--
-- σ-involutivity tells us this is equivalent (up to ≈Term on permute)
-- to the σ-cancelled form
--
--   q = trans (prep k (prep k' (trans a b))) Y
--
-- which has IDENTICAL `(size, total-l)` lex measure but STRICTLY
-- SMALLER `swap-count` (decreases by 2: the two `swap` constructors are
-- replaced by `prep` constructors).
--
-- We extend the lex measure to a triple `(size, total-l, swap-count)`,
-- with `swap-count` defined to count `swap` constructors.  The
-- σ-cancellation `swap; swap → prep; prep` decreases `swap-count`
-- strictly while preserving size and total-l.
--
-- ## Why A-swap and B-prep are NOT closed here
--
-- The A-swap and B-prep cases involve σ-naturality across non-σ
-- morphisms.  Their natural rewrites either:
--   * preserve swap-count (e.g., pushing `σ` past `prep` only renames),
--     so swap-count cannot drive recursion;
--   * or require structural induction on the underlying sub-derivation
--     `a` (decomposing its codomain), which `_≪₃_` does not capture.
--
-- These remain in a narrowed residual record `TwoCascadeResidual` with
-- just the two un-closeable cases.
--
-- ## What this file delivers
--
--   * `swap-count` measure with map⁺ preservation.
--   * `_≪₃_` lex order on triples with well-foundedness.
--   * `self-loop-lex3` — lex-Acc recursion on the new triple measure.
--   * `TwoCascadeResidual` — narrowed residual record (A-swap, B-prep only).
--   * `constructive-two-cascade-handler` — normal-form handler closing
--     B-swap constructively, dispatching A-swap and B-prep to the
--     residual.
--   * `module WithTwoResidual` — bundles a `SelfLoopPostulate` from
--     the narrower residual.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `TwoCascadeResidual` record.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure2
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (SelfLoopPostulate)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopTransClosure sig-dec
  using (size; size-map⁺)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure sig-dec
  using ( total-l; total-l-map⁺
        ; dnorm; dnorm-trans; dnorm-permute; dnorm-map⁺
        ; size-dnorm; total-l-dnorm)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-suc; ≤-refl; ≤-trans; +-comm; m≤m+n; m≤n+m; <-trans; +-assoc
        ; +-monoʳ-≤; +-monoˡ-≤; +-monoˡ-<; +-monoʳ-<; +-mono-<; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc; acc; WellFounded)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## `swap-count`: counts `swap` constructors in a derivation.

swap-count : ∀ {a} {A : Set a} {xs ys : List A} → xs Perm.↭ ys → ℕ
swap-count Perm.refl         = 0
swap-count (Perm.prep _ p)   = swap-count p
swap-count (Perm.swap _ _ p) = suc (swap-count p)
swap-count (Perm.trans p q)  = swap-count p + swap-count q

-- `map⁺` preserves `swap-count`.
swap-count-map⁺
  : ∀ {n} (vlab : Fin n → X) {xs ys : List (Fin n)}
      (p : xs Perm.↭ ys)
  → swap-count (PermProp.map⁺ vlab p) ≡ swap-count p
swap-count-map⁺ vlab Perm.refl         = refl
swap-count-map⁺ vlab (Perm.prep _ p)   = swap-count-map⁺ vlab p
swap-count-map⁺ vlab (Perm.swap _ _ p) = cong suc (swap-count-map⁺ vlab p)
swap-count-map⁺ vlab (Perm.trans p q)  =
  cong₂ _+_ (swap-count-map⁺ vlab p) (swap-count-map⁺ vlab q)

-- `dnorm-trans` preserves swap-count.
swap-count-dnorm-trans
  : ∀ {a} {A : Set a} {xs ms ys : List A}
      (p : xs Perm.↭ ms) (q : ms Perm.↭ ys)
  → swap-count (dnorm-trans p q) ≡ swap-count (Perm.trans p q)
swap-count-dnorm-trans Perm.refl         q = refl
swap-count-dnorm-trans (Perm.prep x p)   q = refl
swap-count-dnorm-trans (Perm.swap x y p) q = refl
swap-count-dnorm-trans (Perm.trans p₁ p₂) q
  rewrite swap-count-dnorm-trans p₁ (dnorm-trans p₂ q)
        | swap-count-dnorm-trans p₂ q
        | sym (+-assoc (swap-count p₁) (swap-count p₂) (swap-count q))
  = refl

-- `dnorm` preserves swap-count.
swap-count-dnorm
  : ∀ {a} {A : Set a} {xs ys : List A}
      (p : xs Perm.↭ ys)
  → swap-count (dnorm p) ≡ swap-count p
swap-count-dnorm Perm.refl         = refl
swap-count-dnorm (Perm.prep x p)   = swap-count-dnorm p
swap-count-dnorm (Perm.swap x y p) = cong suc (swap-count-dnorm p)
swap-count-dnorm (Perm.trans p q)
  rewrite swap-count-dnorm-trans (dnorm p) (dnorm q)
        | swap-count-dnorm p
        | swap-count-dnorm q
  = refl

--------------------------------------------------------------------------------
-- ## Triple lex order on (size, total-l, swap-count).

infix 4 _≪₃_
data _≪₃_ : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → Set where
  ≪₃-fst : ∀ {s₁ s₂ l₁ l₂ c₁ c₂} → s₁ < s₂ → (s₁ , l₁ , c₁) ≪₃ (s₂ , l₂ , c₂)
  ≪₃-snd : ∀ {s l₁ l₂ c₁ c₂}     → l₁ < l₂ → (s , l₁ , c₁) ≪₃ (s , l₂ , c₂)
  ≪₃-thd : ∀ {s l c₁ c₂}          → c₁ < c₂ → (s , l , c₁) ≪₃ (s , l , c₂)

-- Well-foundedness via triple Acc descent.
mutual
  ≪₃-Acc
    : ∀ {s l c} → Acc _<_ s → Acc _<_ l → Acc _<_ c
    → Acc _≪₃_ (s , l , c)
  ≪₃-Acc {s} {l} {c} acc-s acc-l acc-c =
    acc (≪₃-Acc-rec acc-s acc-l acc-c)

  ≪₃-Acc-rec
    : ∀ {s l c} → Acc _<_ s → Acc _<_ l → Acc _<_ c
    → ∀ {s' l' c'} → (s' , l' , c') ≪₃ (s , l , c)
    → Acc _≪₃_ (s' , l' , c')
  ≪₃-Acc-rec (acc rs) _      _      (≪₃-fst s'<s) =
    ≪₃-Acc (rs s'<s) (<-wellFounded _) (<-wellFounded _)
  ≪₃-Acc-rec acc-s (acc rl) _      (≪₃-snd l'<l) =
    ≪₃-Acc acc-s (rl l'<l) (<-wellFounded _)
  ≪₃-Acc-rec acc-s acc-l (acc rc) (≪₃-thd c'<c) =
    ≪₃-Acc acc-s acc-l (rc c'<c)

≪₃-wf : WellFounded _≪₃_
≪₃-wf (s , l , c) = ≪₃-Acc (<-wellFounded s) (<-wellFounded l) (<-wellFounded c)

--------------------------------------------------------------------------------
-- ## Triple of measures.

measure : ∀ {a} {A : Set a} {xs ys : List A} → xs Perm.↭ ys → ℕ × ℕ × ℕ
measure p = (size p , total-l p , swap-count p)

-- map⁺ preserves the measure triple (componentwise).
measure-map⁺
  : ∀ {n} (vlab : Fin n → X) {xs ys : List (Fin n)}
      (p : xs Perm.↭ ys)
  → measure (PermProp.map⁺ vlab p) ≡ measure p
measure-map⁺ vlab p
  rewrite size-map⁺ vlab p
        | total-l-map⁺ vlab p
        | swap-count-map⁺ vlab p
  = refl

--------------------------------------------------------------------------------
-- ## Arithmetic helpers.

private
  size-trans-refl-left-< : ∀ n → n < suc (suc n)
  size-trans-refl-left-< n = s≤s (n≤1+n n)

  size-trans-refl-right-< : ∀ n → n < suc (n + 1)
  size-trans-refl-right-< n = s≤s (m≤m+n n 1)

  size-trans-aligned-<
    : ∀ sa sb → suc (sa + sb) < suc (suc sa + suc sb)
  size-trans-aligned-< sa sb
    rewrite +-suc sa sb = s≤s (s≤s (n≤1+n (sa + sb)))

  refl-strip-< : ∀ a b → a + b < a + suc (suc b)
  refl-strip-< zero    b = s≤s (n≤1+n b)
  refl-strip-< (suc a) b = s≤s (refl-strip-< a b)

  +-suc-nonzero : ∀ a b → a + suc b ≡ 0 → ⊥
  +-suc-nonzero zero    b ()
  +-suc-nonzero (suc a) b ()

  -- Used for the B-swap closure swap-count strict decrease.
  -- swap-count(p) = suc (sc-a + suc (sc-b + sc-Y))
  --              = 2 + sc-a + sc-b + sc-Y
  -- swap-count(q) = sc-a + sc-b + sc-Y
  -- Strict less by 2.
  swap-count-bswap-<
    : ∀ sa sb sY
    → sa + sb + sY < suc (sa + suc (sb + sY))
  swap-count-bswap-< sa sb sY
    rewrite +-suc sa (sb + sY)
          | sym (+-assoc sa sb sY)
    = s≤s (n≤1+n (sa + sb + sY))

  -- The size-equality for B-swap rewrite:
  --   size(trans (swap k k' a) (trans (swap k' k b) Y))
  --     = suc ((suc sa) + (suc (suc sb + sY)))
  --     = 4 + sa + sb + sY (via +-suc twice)
  --   size(trans (prep k (prep k' (trans a b))) Y)
  --     = suc (suc (suc (suc (sa + sb))) + sY)
  --     = 4 + sa + sb + sY
  size-bswap-eq
    : ∀ sa sb sY
    → suc (suc (suc (suc (sa + sb))) + sY) ≡ suc (suc sa + suc (suc sb + sY))
  size-bswap-eq sa sb sY
    rewrite +-suc sa (suc (sb + sY))
          | +-suc sa (sb + sY)
          | sym (+-assoc sa sb sY)
    = refl

  -- For prep-fusion (used in A-prep case).
  prep-fusion-size-<
    : ∀ sa sb sY
    → suc (suc (suc (sa + sb)) + sY)
      <
      suc (suc sa + suc (suc sb + sY))
  prep-fusion-size-< sa sb sY
    rewrite +-suc sa (suc sb + sY)
          | +-suc sa (sb + sY)
          | sym (+-assoc sa sb sY)
    = s≤s (s≤s (s≤s (s≤s ≤-refl)))

  +-zero-l-zero : ∀ a b → a + b ≡ 0 → a ≡ 0
  +-zero-l-zero zero    _ _ = refl
  +-zero-l-zero (suc _) _ ()

  +-zero-r-zero : ∀ a b → a + b ≡ 0 → b ≡ 0
  +-zero-r-zero zero    _ eq = eq
  +-zero-r-zero (suc _) _ ()

--------------------------------------------------------------------------------
-- ## σ-block helpers (re-derived locally; private elsewhere).

private
  σ-block-involutive
    : ∀ {A B C : ObjTerm}
    → (α⇒ {A = A} {B = B} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = B} {B = A} {C = C})
        ∘ (α⇒ {A = B} {B = A} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = A} {B = B} {C = C})
      ≈Term id
  σ-block-involutive {A} {B} {C} =
    let σ-AB = σ {A = A} {B = B}
        σ-BA = σ {A = B} {B = A}
        α⇒-ABC = α⇒ {A = A} {B = B} {C = C}
        α⇐-ABC = α⇐ {A = A} {B = B} {C = C}
        α⇒-BAC = α⇒ {A = B} {B = A} {C = C}
        α⇐-BAC = α⇐ {A = B} {B = A} {C = C}
    in begin
         (α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ α⇐-BAC)
           ∘ (α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
           ≈⟨ assoc ⟩
         α⇒-ABC ∘ ((σ-BA ⊗₁ id) ∘ α⇐-BAC)
           ∘ (α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
           ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
         α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ (α⇐-BAC ∘ α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl
                  (≈-Term-trans (≈-Term-sym assoc)
                                (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl))) ⟩
         α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ id ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC
           ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
         α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ ((σ-AB ⊗₁ id) ∘ α⇐-ABC)
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
         α⇒-ABC ∘ ((σ-BA ⊗₁ id) ∘ (σ-AB ⊗₁ id)) ∘ α⇐-ABC
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (≈-Term-trans (⊗-resp-≈ σ∘σ≈id idˡ)
                                          id⊗id≈id))
                         ≈-Term-refl) ⟩
         α⇒-ABC ∘ id ∘ α⇐-ABC
           ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
         α⇒-ABC ∘ α⇐-ABC
           ≈⟨ α⇒∘α⇐≈id ⟩
         id
       ∎

  σ-block-natural₃
    : ∀ {A B C D : ObjTerm} {f : HomTerm C D}
    → (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
      ≈Term (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
  σ-block-natural₃ {A} {B} {C} {D} {f} =
    let lhs→common =
          begin
            (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
              ≈⟨ assoc ⟩
            α⇒ ∘ ((σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
              ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
            α⇒ ∘ (σ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (id ⊗₁ f)))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl α⇐-comm) ⟩
            α⇒ ∘ (σ ⊗₁ id) ∘ (((id ⊗₁ id) ⊗₁ f) ∘ α⇐)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
            α⇒ ∘ ((σ ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ α⇐
              ≈⟨ ∘-resp-≈ ≈-Term-refl
                   (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                              (⊗-resp-≈ (≈-Term-trans (∘-resp-≈ ≈-Term-refl id⊗id≈id) idʳ)
                                        idˡ))
                            ≈-Term-refl) ⟩
            α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
          ∎
        rhs→common =
          begin
            (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
              ≈⟨ ≈-Term-sym assoc ⟩
            ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒) ∘ ((σ ⊗₁ id) ∘ α⇐)
              ≈⟨ ∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl ⟩
            (α⇒ ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ ((σ ⊗₁ id) ∘ α⇐)
              ≈⟨ assoc ⟩
            α⇒ ∘ (((id ⊗₁ id) ⊗₁ f) ∘ ((σ ⊗₁ id) ∘ α⇐))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
            α⇒ ∘ ((((id ⊗₁ id) ⊗₁ f)) ∘ (σ ⊗₁ id)) ∘ α⇐
              ≈⟨ ∘-resp-≈ ≈-Term-refl
                   (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                              (⊗-resp-≈ (≈-Term-trans (∘-resp-≈ id⊗id≈id ≈-Term-refl) idˡ)
                                        idʳ))
                            ≈-Term-refl) ⟩
            α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
          ∎
    in ≈-Term-trans lhs→common (≈-Term-sym rhs→common)
    where
      α⇐-comm
        : ∀ {a b c d e g : ObjTerm}
            {h : HomTerm a d} {i : HomTerm b e} {j : HomTerm c g}
        → α⇐ ∘ (h ⊗₁ (i ⊗₁ j)) ≈Term ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
      α⇐-comm {h = h} {i} {j} = begin
        α⇐ ∘ (h ⊗₁ (i ⊗₁ j))
          ≈⟨ ≈-Term-sym idʳ ⟩
        (α⇐ ∘ (h ⊗₁ (i ⊗₁ j))) ∘ id
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id) ⟩
        (α⇐ ∘ (h ⊗₁ (i ⊗₁ j))) ∘ (α⇒ ∘ α⇐)
          ≈⟨ assoc ⟩
        α⇐ ∘ ((h ⊗₁ (i ⊗₁ j)) ∘ (α⇒ ∘ α⇐))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        α⇐ ∘ ((h ⊗₁ (i ⊗₁ j)) ∘ α⇒) ∘ α⇐
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl) ⟩
        α⇐ ∘ (α⇒ ∘ ((h ⊗₁ i) ⊗₁ j)) ∘ α⇐
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        α⇐ ∘ α⇒ ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
          ≈⟨ ≈-Term-sym assoc ⟩
        (α⇐ ∘ α⇒) ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
          ≈⟨ ∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl ⟩
        id ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
          ≈⟨ idˡ ⟩
        ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
          ∎

--------------------------------------------------------------------------------
-- ## Narrowed residual: A-swap, B-prep plus 3 dead branches.
--
-- B-swap is closed constructively in this file.  Only A-swap and B-prep
-- remain as σ-naturality-blocked residuals.
--
-- The 3 dead-branch fields (dead-prep, dead-prep-prep-aligned,
-- dead-swap-swap-aligned) are residuals only for totality of the handler
-- signature.  They are UNREACHABLE in practice — `self-loop-lex3` catches
-- these patterns BEFORE invoking the handler.  A consumer can construct
-- them via any sound mechanism (e.g., directly via `≪₃-wf`-based
-- recursion) or accept them as the documented "unreachable" portion of
-- the trust surface.

record TwoCascadeResidual : Set where
  field
    -- (A.swap): `p = trans (prep .k a) (trans (swap .k k' b) Y)`.
    A-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' : Fin n} {xs' rest rest' : List (Fin n)}
          (uniq : Unique (k ∷ xs'))
          (a : xs' Perm.↭ (k' ∷ rest))
          (b : rest Perm.↭ rest')
          (Y : (k' ∷ k ∷ rest') Perm.↭ (k ∷ xs'))
          (acc-p
            : let p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let p = Perm.trans (Perm.prep k a)
                        (Perm.trans (Perm.swap k k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ xs') Perm.↭ (k ∷ xs'))
              → let p = Perm.trans (Perm.prep k a)
                          (Perm.trans (Perm.swap k k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let p = Perm.trans (Perm.prep k a)
                    (Perm.trans (Perm.swap k k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- (B.prep): `p = trans (swap .k .k' a) (trans (prep .k' b) Y)`.
    B-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' : Fin n} {rest rest' tail' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ rest')
          (b : (k ∷ rest') Perm.↭ tail')
          (Y : (k' ∷ tail') Perm.↭ (k ∷ k' ∷ rest))
          (acc-p
            : let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' b) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' b) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
              → let p = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' b) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let p = Perm.trans (Perm.swap k k' a)
                    (Perm.trans (Perm.prep k' b) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Dead branch (unreachable in practice): handler's signature
    -- requires it for totality, but `self-loop-lex3` always handles
    -- `trans (prep .k a) (prep .k b)` directly before calling the handler.
    dead-prep-prep-aligned
      : ∀ {n} (vlab : Fin n → X)
          {k : Fin n} {xs' ms' : List (Fin n)}
          (uniq : Unique (k ∷ xs'))
          (a : xs' Perm.↭ ms')
          (b : ms' Perm.↭ xs')
          (acc-p
            : let p = Perm.trans (Perm.prep k a) (Perm.prep k b)
              in Acc _≪₃_ (measure p))
          (norm
            : let p = Perm.trans (Perm.prep k a) (Perm.prep k b)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ xs') Perm.↭ (k ∷ xs'))
              → let p = Perm.trans (Perm.prep k a) (Perm.prep k b)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let p = Perm.trans (Perm.prep k a) (Perm.prep k b)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- Dead branch (unreachable in practice).
    dead-swap-swap-aligned
      : ∀ {n} (vlab : Fin n → X)
          {k k' : Fin n} {rest ms' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a : rest Perm.↭ ms')
          (b : ms' Perm.↭ rest)
          (acc-p
            : let p = Perm.trans (Perm.swap k k' a) (Perm.swap k' k b)
              in Acc _≪₃_ (measure p))
          (norm
            : let p = Perm.trans (Perm.swap k k' a) (Perm.swap k' k b)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
              → let p = Perm.trans (Perm.swap k k' a) (Perm.swap k' k b)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let p = Perm.trans (Perm.swap k k' a) (Perm.swap k' k b)
          in permute (PermProp.map⁺ vlab p) ≈Term id

--------------------------------------------------------------------------------
-- ## Main self-loop recursion with TRIPLE lex Acc.
--
-- The handler signature ONLY takes `trans p₁ p₂` (since this is the
-- only catch-all pattern that needs delegation in `self-loop-lex3`).
-- This avoids the totality cliff of handling all `xs ↭ xs` shapes.

self-loop-lex3
  : ∀ {n} (vlab : Fin n → X) {xs : List (Fin n)}
      (uniq : Unique xs)
      (p : xs Perm.↭ xs)
      (acc-p : Acc _≪₃_ (measure p))
      (normal-form-handler
        : ∀ {xs ms : List (Fin n)} (uniq : Unique xs)
            (p₁ : xs Perm.↭ ms) (p₂ : ms Perm.↭ xs)
            (acc-p : Acc _≪₃_ (measure (Perm.trans p₁ p₂)))
            (norm : total-l (Perm.trans p₁ p₂) ≡ 0)
            (self-rec
              : ∀ (q : xs Perm.↭ xs)
                → measure q ≪₃ measure (Perm.trans p₁ p₂)
                → permute (PermProp.map⁺ vlab q) ≈Term id)
        → permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂)) ≈Term id)
  → permute (PermProp.map⁺ vlab p) ≈Term id

self-loop-lex3 vlab uniq Perm.refl _ _ = ≈-Term-refl

self-loop-lex3 vlab {k ∷ xs} (_ ∷ uniq') (Perm.prep .k p') (acc rs) nfh =
  let sub-< : measure p' ≪₃ measure (Perm.prep k p')
      sub-< = ≪₃-fst {l₁ = total-l p'}
                     {l₂ = total-l p'}
                     {c₁ = swap-count p'}
                     {c₂ = swap-count p'}
                     (≤-refl {x = suc (size p')})
      ih = self-loop-lex3 vlab uniq' p' (rs sub-<) nfh
  in begin
       id ⊗₁ permute (PermProp.map⁺ vlab p')
         ≈⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
       id ⊗₁ id
         ≈⟨ id⊗id≈id ⟩
       id
     ∎

self-loop-lex3 vlab ((k≢k' ∷ _) ∷ _) (Perm.swap k k p') _ _ =
  ⊥-elim (k≢k' refl)

self-loop-lex3 vlab uniq (Perm.trans Perm.refl p₂) (acc rs) nfh =
  let sub-< : measure p₂ ≪₃ measure (Perm.trans Perm.refl p₂)
      sub-< = ≪₃-fst {l₁ = total-l p₂}
                     {l₂ = total-l p₂}
                     {c₁ = swap-count p₂}
                     {c₂ = swap-count p₂}
                     (size-trans-refl-left-< (size p₂))
      ih₂ = self-loop-lex3 vlab uniq p₂ (rs sub-<) nfh
  in begin
       permute (PermProp.map⁺ vlab p₂) ∘ id
         ≈⟨ idʳ ⟩
       permute (PermProp.map⁺ vlab p₂)
         ≈⟨ ih₂ ⟩
       id
     ∎

self-loop-lex3 vlab uniq (Perm.trans p₁ Perm.refl) (acc rs) nfh =
  let sub-< : measure p₁ ≪₃ measure (Perm.trans p₁ Perm.refl)
      sub-< = ≪₃-fst {l₁ = total-l p₁}
                     {l₂ = total-l (Perm.trans p₁ Perm.refl)}
                     {c₁ = swap-count p₁}
                     {c₂ = swap-count (Perm.trans p₁ Perm.refl)}
                     (size-trans-refl-right-< (size p₁))
      ih₁ = self-loop-lex3 vlab uniq p₁ (rs sub-<) nfh
  in begin
       id ∘ permute (PermProp.map⁺ vlab p₁)
         ≈⟨ idˡ ⟩
       permute (PermProp.map⁺ vlab p₁)
         ≈⟨ ih₁ ⟩
       id
     ∎

self-loop-lex3 vlab {k ∷ xs'} (_ ∷ uniq')
              (Perm.trans (Perm.prep .k p₁') (Perm.prep .k p₂')) (acc rs) nfh =
  let sub-< : measure (Perm.trans p₁' p₂')
            ≪₃ measure (Perm.trans (Perm.prep k p₁') (Perm.prep k p₂'))
      sub-< = ≪₃-fst {l₁ = total-l (Perm.trans p₁' p₂')}
                     {l₂ = total-l (Perm.trans (Perm.prep k p₁') (Perm.prep k p₂'))}
                     {c₁ = swap-count (Perm.trans p₁' p₂')}
                     {c₂ = swap-count (Perm.trans (Perm.prep k p₁') (Perm.prep k p₂'))}
                     (size-trans-aligned-< (size p₁') (size p₂'))
      ih = self-loop-lex3 vlab uniq' (Perm.trans p₁' p₂') (rs sub-<) nfh
  in begin
       (id ⊗₁ permute (PermProp.map⁺ vlab p₂'))
         ∘ (id ⊗₁ permute (PermProp.map⁺ vlab p₁'))
         ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
       (id ∘ id) ⊗₁ (permute (PermProp.map⁺ vlab p₂') ∘ permute (PermProp.map⁺ vlab p₁'))
         ≈⟨ ⊗-resp-≈ idˡ ih ⟩
       id ⊗₁ id
         ≈⟨ id⊗id≈id ⟩
       id
     ∎

self-loop-lex3 vlab {k ∷ k' ∷ rest} ((_ ∷ _) ∷ _ ∷ uniq-rest)
              (Perm.trans (Perm.swap .k .k' p₁') (Perm.swap .k' .k p₂')) (acc rs) nfh =
  let f = permute (PermProp.map⁺ vlab p₁')
      g = permute (PermProp.map⁺ vlab p₂')
      sub-< : measure (Perm.trans p₁' p₂')
            ≪₃ measure (Perm.trans (Perm.swap k k' p₁') (Perm.swap k' k p₂'))
      sub-< = ≪₃-fst {l₁ = total-l (Perm.trans p₁' p₂')}
                     {l₂ = total-l (Perm.trans (Perm.swap k k' p₁') (Perm.swap k' k p₂'))}
                     {c₁ = swap-count (Perm.trans p₁' p₂')}
                     {c₂ = swap-count (Perm.trans (Perm.swap k k' p₁') (Perm.swap k' k p₂'))}
                     (size-trans-aligned-< (size p₁') (size p₂'))
      ih = self-loop-lex3 vlab uniq-rest (Perm.trans p₁' p₂') (rs sub-<) nfh
  in begin
       ((id ⊗₁ (id ⊗₁ g)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ assoc ⟩
       (id ⊗₁ (id ⊗₁ g)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
       (id ⊗₁ (id ⊗₁ g))
         ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f)))
         ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ-block-natural₃ ≈-Term-refl) ⟩
       (id ⊗₁ (id ⊗₁ g))
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
         ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
       (id ⊗₁ (id ⊗₁ g))
         ∘ (id ⊗₁ (id ⊗₁ f))
         ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl σ-block-involutive) ⟩
       (id ⊗₁ (id ⊗₁ g)) ∘ (id ⊗₁ (id ⊗₁ f)) ∘ id
         ≈⟨ ∘-resp-≈ ≈-Term-refl idʳ ⟩
       (id ⊗₁ (id ⊗₁ g)) ∘ (id ⊗₁ (id ⊗₁ f))
         ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
       (id ∘ id) ⊗₁ ((id ⊗₁ g) ∘ (id ⊗₁ f))
         ≈⟨ ⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist) ⟩
       id ⊗₁ ((id ∘ id) ⊗₁ (g ∘ f))
         ≈⟨ ⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ih) ⟩
       id ⊗₁ (id ⊗₁ id)
         ≈⟨ ⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩
       id ⊗₁ id
         ≈⟨ id⊗id≈id ⟩
       id
     ∎

self-loop-lex3 vlab ((k≢k ∷ _) ∷ _)
              (Perm.trans (Perm.prep k p₁') (Perm.swap k k p₂')) _ _ =
  ⊥-elim (k≢k refl)

self-loop-lex3 vlab ((k≢k ∷ _) ∷ _)
              (Perm.trans (Perm.swap k k p₁') (Perm.prep k p₂')) _ _ =
  ⊥-elim (k≢k refl)

-- Pattern: `trans p₁ (trans refl p₂')`.
self-loop-lex3 vlab uniq (Perm.trans p₁ (Perm.trans Perm.refl p₂')) (acc rs) nfh =
  let q = Perm.trans p₁ p₂'
      size-< : size q < size (Perm.trans p₁ (Perm.trans Perm.refl p₂'))
      size-< = s≤s (refl-strip-< (size p₁) (size p₂'))
      sub-< : measure q ≪₃ measure (Perm.trans p₁ (Perm.trans Perm.refl p₂'))
      sub-< = ≪₃-fst {l₁ = total-l q}
                     {l₂ = total-l (Perm.trans p₁ (Perm.trans Perm.refl p₂'))}
                     {c₁ = swap-count q}
                     {c₂ = swap-count (Perm.trans p₁ (Perm.trans Perm.refl p₂'))}
                     size-<
      ih = self-loop-lex3 vlab uniq q (rs sub-<) nfh
  in begin
       (permute (PermProp.map⁺ vlab p₂') ∘ id) ∘ permute (PermProp.map⁺ vlab p₁)
         ≈⟨ ∘-resp-≈ idʳ ≈-Term-refl ⟩
       permute (PermProp.map⁺ vlab p₂') ∘ permute (PermProp.map⁺ vlab p₁)
         ≈⟨ ih ⟩
       id
     ∎

-- Catch-all case `trans p₁ p₂`.
self-loop-lex3 {n = n} vlab {xs} uniq (Perm.trans p₁ p₂) (acc rs) nfh =
  case-split (total-l (Perm.trans p₁ p₂)) refl
  where
    case-split : (m : ℕ) → total-l (Perm.trans p₁ p₂) ≡ m
               → permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂)) ≈Term id
    case-split zero    tl-eq =
      nfh uniq p₁ p₂ (acc rs) tl-eq
          (λ q q<p → self-loop-lex3 vlab uniq q (rs q<p) nfh)
    case-split (suc m) tl-eq =
      let size-eq′ = size-dnorm (Perm.trans p₁ p₂)
          tl-dn-zero′ = total-l-dnorm (Perm.trans p₁ p₂)

          -- The dnorm rewrites preserve size and reduce total-l to 0.
          -- We use ≪₃-snd (total-l decreases from positive to 0).
          bare-≪ : (size (Perm.trans p₁ p₂) , 0 , swap-count (dnorm (Perm.trans p₁ p₂)))
                  ≪₃ (size (Perm.trans p₁ p₂) , suc m , swap-count (Perm.trans p₁ p₂))
          bare-≪ = ≪₃-snd (s≤s z≤n)

          step1 : (size (Perm.trans p₁ p₂) , 0 , swap-count (dnorm (Perm.trans p₁ p₂)))
                 ≪₃ (size (Perm.trans p₁ p₂) , total-l (Perm.trans p₁ p₂) , swap-count (Perm.trans p₁ p₂))
          step1 = subst (λ z → (size (Perm.trans p₁ p₂) , 0 , swap-count (dnorm (Perm.trans p₁ p₂)))
                              ≪₃ (size (Perm.trans p₁ p₂) , z , swap-count (Perm.trans p₁ p₂)))
                        (sym tl-eq) bare-≪

          step2 : (size (Perm.trans p₁ p₂) , total-l (dnorm (Perm.trans p₁ p₂)) , swap-count (dnorm (Perm.trans p₁ p₂)))
                 ≪₃ (size (Perm.trans p₁ p₂) , total-l (Perm.trans p₁ p₂) , swap-count (Perm.trans p₁ p₂))
          step2 = subst (λ z → (size (Perm.trans p₁ p₂) , z , swap-count (dnorm (Perm.trans p₁ p₂)))
                              ≪₃ (size (Perm.trans p₁ p₂) , total-l (Perm.trans p₁ p₂) , swap-count (Perm.trans p₁ p₂)))
                        (sym tl-dn-zero′) step1

          sub-≪ : measure (dnorm (Perm.trans p₁ p₂)) ≪₃ measure (Perm.trans p₁ p₂)
          sub-≪ = subst (λ z → (z , total-l (dnorm (Perm.trans p₁ p₂)) , swap-count (dnorm (Perm.trans p₁ p₂)))
                              ≪₃ measure (Perm.trans p₁ p₂))
                        (sym size-eq′) step2

          ih : permute (PermProp.map⁺ vlab (dnorm (Perm.trans p₁ p₂))) ≈Term id
          ih = self-loop-lex3 vlab uniq (dnorm (Perm.trans p₁ p₂)) (rs sub-≪) nfh

          eq : permute (PermProp.map⁺ vlab (dnorm (Perm.trans p₁ p₂)))
             ≡ permute (dnorm (PermProp.map⁺ vlab (Perm.trans p₁ p₂)))
          eq = cong permute (dnorm-map⁺ vlab (Perm.trans p₁ p₂))

          ih-via-eq : permute (dnorm (PermProp.map⁺ vlab (Perm.trans p₁ p₂))) ≈Term id
          ih-via-eq = subst (λ z → z ≈Term id) eq ih
      in begin
           permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂))
             ≈⟨ ≈-Term-sym (dnorm-permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂))) ⟩
           permute (dnorm (PermProp.map⁺ vlab (Perm.trans p₁ p₂)))
             ≈⟨ ih-via-eq ⟩
           id
         ∎

--------------------------------------------------------------------------------
-- ## B-swap closure: rewrite to σ-cancelled form, lex-decrease via
-- swap-count, dispatch via self-rec.
--
-- p = trans (swap k k' a) (trans (swap k' k b) Y)
-- q = trans (prep k (prep k' (trans a b))) Y
-- size(p) = size(q), total-l(p) = total-l(q) = 0,
-- swap-count(p) = swap-count(q) + 2.

module _ {n} (vlab : Fin n → X) where

  -- Stage 1 — σ-collapse:
  -- permute(map⁺ vlab p) ≈Term pY ∘ (id ⊗ (id ⊗ (pb ∘ pa))).
  b-swap-sigma-collapse-to-canonical
    : ∀ {k k' : Fin n} {rest rest' rest_b' : List (Fin n)}
        (a : rest Perm.↭ rest')
        (b : rest' Perm.↭ rest_b')
        (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
    → let p = Perm.trans (Perm.swap k k' a)
                (Perm.trans (Perm.swap k' k b) Y)
          pa = permute (PermProp.map⁺ vlab a)
          pb = permute (PermProp.map⁺ vlab b)
          pY = permute (PermProp.map⁺ vlab Y)
      in permute (PermProp.map⁺ vlab p)
         ≈Term pY ∘ (id ⊗₁ (id ⊗₁ (pb ∘ pa)))
  b-swap-sigma-collapse-to-canonical {k} {k'} {rest} {rest'} {rest_b'} a b Y =
    let pa = permute (PermProp.map⁺ vlab a)
        pb = permute (PermProp.map⁺ vlab b)
        pY = permute (PermProp.map⁺ vlab Y)
    in begin
         (pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
           ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
           ≈⟨ assoc ⟩
         pY ∘ (((id ⊗₁ (id ⊗₁ pb)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
           ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                     ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ (((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ pa)))
                     ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl
                  (∘-resp-≈ σ-block-natural₃ ≈-Term-refl)) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ (((id ⊗₁ (id ⊗₁ pa)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
                     ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ ((id ⊗₁ (id ⊗₁ pa))
                     ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                          ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))))
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl
                  (∘-resp-≈ ≈-Term-refl σ-block-involutive)) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb))
                ∘ ((id ⊗₁ (id ⊗₁ pa)) ∘ id))
           ≈⟨ ∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl idʳ) ⟩
         pY ∘ ((id ⊗₁ (id ⊗₁ pb)) ∘ (id ⊗₁ (id ⊗₁ pa)))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym ⊗-∘-dist) ⟩
         pY ∘ ((id ∘ id) ⊗₁ ((id ⊗₁ pb) ∘ (id ⊗₁ pa)))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist)) ⟩
         pY ∘ (id ⊗₁ ((id ∘ id) ⊗₁ (pb ∘ pa)))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl)) ⟩
         pY ∘ (id ⊗₁ (id ⊗₁ (pb ∘ pa)))
       ∎

  -- Stage 2 — canonical reformulation via dnorm of (trans a b):
  --   permute(map⁺ vlab q')
  --     = pY ∘ (id ⊗ (id ⊗ permute (map⁺ vlab (dnorm (trans a b)))))
  --     ≈Term pY ∘ (id ⊗ (id ⊗ permute (map⁺ vlab (trans a b))))
  --     = pY ∘ (id ⊗ (id ⊗ (pb ∘ pa)))
  -- where q' = trans (prep k (prep k' (dnorm (trans a b)))) Y.
  canonical-form-equals-q'
    : ∀ {k k' : Fin n} {rest rest' rest_b' : List (Fin n)}
        (a : rest Perm.↭ rest')
        (b : rest' Perm.↭ rest_b')
        (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
    → let q' = Perm.trans (Perm.prep k (Perm.prep k' (dnorm (Perm.trans a b)))) Y
          pa = permute (PermProp.map⁺ vlab a)
          pb = permute (PermProp.map⁺ vlab b)
          pY = permute (PermProp.map⁺ vlab Y)
      in pY ∘ (id ⊗₁ (id ⊗₁ (pb ∘ pa)))
         ≈Term permute (PermProp.map⁺ vlab q')
  canonical-form-equals-q' {k} {k'} {rest} {rest'} {rest_b'} a b Y =
    let pa = permute (PermProp.map⁺ vlab a)
        pb = permute (PermProp.map⁺ vlab b)
        pY = permute (PermProp.map⁺ vlab Y)
        -- Goal: pY ∘ (id ⊗ (id ⊗ (pb ∘ pa)))
        --       ≈Term permute (map⁺ vlab (trans (prep k (prep k' (dnorm (trans a b)))) Y))
        -- = permute (map⁺ vlab Y) ∘ (id ⊗ (id ⊗ permute (map⁺ vlab (dnorm (trans a b)))))
        -- = pY ∘ (id ⊗ (id ⊗ permute (dnorm (map⁺ vlab (trans a b)))))  (via dnorm-map⁺)
        -- ≈Term pY ∘ (id ⊗ (id ⊗ (pb ∘ pa)))                              (via dnorm-permute)
        --
        -- We need to bridge the ≡-equality from dnorm-map⁺ with subst,
        -- and then the ≈Term from dnorm-permute.

        -- Step A: dnorm-map⁺ gives us:
        --   map⁺ vlab (dnorm (trans a b)) ≡ dnorm (map⁺ vlab (trans a b))
        m-eq : PermProp.map⁺ vlab (dnorm (Perm.trans a b))
             ≡ dnorm (PermProp.map⁺ vlab (Perm.trans a b))
        m-eq = dnorm-map⁺ vlab (Perm.trans a b)

        -- Step B: permute on both sides via cong permute:
        p-eq : permute (PermProp.map⁺ vlab (dnorm (Perm.trans a b)))
             ≡ permute (dnorm (PermProp.map⁺ vlab (Perm.trans a b)))
        p-eq = cong permute m-eq

        -- Step C: dnorm-permute gives ≈Term:
        d-perm : permute (dnorm (PermProp.map⁺ vlab (Perm.trans a b)))
               ≈Term permute (PermProp.map⁺ vlab (Perm.trans a b))
        d-perm = dnorm-permute (PermProp.map⁺ vlab (Perm.trans a b))

        -- Putting it together:
        --   permute (map⁺ vlab (dnorm (trans a b)))
        --   ≡ permute (dnorm (map⁺ vlab (trans a b)))     (p-eq)
        --   ≈Term permute (map⁺ vlab (trans a b))         (d-perm)
        --   = pb ∘ pa                                      (definitional)
        combined : permute (PermProp.map⁺ vlab (dnorm (Perm.trans a b)))
                 ≈Term pb ∘ pa
        combined = ≈-Term-trans (subst (λ z → z ≈Term permute (PermProp.map⁺ vlab (Perm.trans a b)))
                                       (sym p-eq) d-perm)
                                ≈-Term-refl
    in ≈-Term-sym (∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl combined)))

--------------------------------------------------------------------------------
-- ## Lex-measure decrease for B-swap → σ-cancelled q.
--
-- p = trans (swap k k' a) (trans (swap k' k b) Y)
-- q = trans (prep k (prep k' (trans a b))) Y
--
-- We need: measure q ≪₃ measure p.
-- size(q) = size(p), total-l(q) ≤ total-l(p), swap-count(q) < swap-count(p).
-- Specifically, in normal form (total-l p ≡ 0), total-l(q) ≡ 0 as well.

private
  -- For B-swap, we use the σ-cancelled+dnorm-normalized form:
  --   q' = trans (prep k (prep k' (dnorm (trans P Q)))) Y
  -- which has:
  --   size q' = size p     (since size-dnorm preserves)
  --   total-l q' = 0       (since total-l-dnorm = 0)
  --   swap-count q' < swap-count p (strict, by 2: σ→prep cancellation)

  -- size(p) = size(q')
  size-bswap-q'-eq
    : ∀ {a} {A : Set a} {rest rest' rest_b' : List A} {k k' : A}
        (P : rest Perm.↭ rest')
        (Q : rest' Perm.↭ rest_b')
        (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
    → size (Perm.trans (Perm.swap k k' P) (Perm.trans (Perm.swap k' k Q) Y))
      ≡ size (Perm.trans (Perm.prep k (Perm.prep k' (dnorm (Perm.trans P Q)))) Y)
  size-bswap-q'-eq P Q Y
    rewrite size-dnorm (Perm.trans P Q)
    = sym (size-bswap-eq (size P) (size Q) (size Y))

  -- swap-count(q') < swap-count(p), strictly less by 2.
  swap-count-bswap-q'-strict-<
    : ∀ {a} {A : Set a} {rest rest' rest_b' : List A} {k k' : A}
        (P : rest Perm.↭ rest')
        (Q : rest' Perm.↭ rest_b')
        (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
    → swap-count (Perm.trans (Perm.prep k (Perm.prep k' (dnorm (Perm.trans P Q)))) Y)
      < swap-count (Perm.trans (Perm.swap k k' P) (Perm.trans (Perm.swap k' k Q) Y))
  swap-count-bswap-q'-strict-< P Q Y
    rewrite swap-count-dnorm (Perm.trans P Q)
    = swap-count-bswap-< (swap-count P) (swap-count Q) (swap-count Y)

  -- total-l(q') ≡ 0: by total-l-dnorm + total-l Y ≡ 0.
  total-l-bswap-q'-zero
    : ∀ {a} {A : Set a} {rest rest' rest_b' : List A} {k k' : A}
        (P : rest Perm.↭ rest')
        (Q : rest' Perm.↭ rest_b')
        (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
        (norm-Y : total-l Y ≡ 0)
    → total-l (Perm.trans (Perm.prep k (Perm.prep k' (dnorm (Perm.trans P Q)))) Y) ≡ 0
  total-l-bswap-q'-zero P Q Y tY
    rewrite total-l-dnorm (Perm.trans P Q) | tY = refl

  -- Extract total-l Y is 0 from total-l p = 0.
  total-l-bswap-extract-Y
    : ∀ {a} {A : Set a} {rest rest' rest_b' : List A} {k k' : A}
        (P : rest Perm.↭ rest')
        (Q : rest' Perm.↭ rest_b')
        (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
    → total-l (Perm.trans (Perm.swap k k' P) (Perm.trans (Perm.swap k' k Q) Y)) ≡ 0
    → total-l Y ≡ 0
  total-l-bswap-extract-Y P Q Y eq =
    +-zero-r-zero (total-l Q) (total-l Y)
      (+-zero-r-zero (total-l P) (total-l Q + total-l Y) eq)

--------------------------------------------------------------------------------
-- ## The constructive B-swap closure.

discharge-B-swap-3
  : ∀ {n} (vlab : Fin n → X)
      {k k' : Fin n} {rest rest' rest_b' : List (Fin n)}
      (uniq : Unique (k ∷ k' ∷ rest))
      (a : rest Perm.↭ rest')
      (b : rest' Perm.↭ rest_b')
      (Y : (k ∷ k' ∷ rest_b') Perm.↭ (k ∷ k' ∷ rest))
      (acc-p
        : let p = Perm.trans (Perm.swap k k' a)
                    (Perm.trans (Perm.swap k' k b) Y)
          in Acc _≪₃_ (measure p))
      (norm
        : let p = Perm.trans (Perm.swap k k' a)
                    (Perm.trans (Perm.swap k' k b) Y)
          in total-l p ≡ 0)
      (self-rec
        : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
          → let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.swap k' k b) Y)
            in measure q ≪₃ measure p
          → permute (PermProp.map⁺ vlab q) ≈Term id)
  → let p = Perm.trans (Perm.swap k k' a)
              (Perm.trans (Perm.swap k' k b) Y)
    in permute (PermProp.map⁺ vlab p) ≈Term id
discharge-B-swap-3 vlab {k} {k'} {rest} {rest'} {rest_b'} uniq a b Y acc-p norm self-rec =
  let p = Perm.trans (Perm.swap k k' a)
            (Perm.trans (Perm.swap k' k b) Y)
      q' = Perm.trans (Perm.prep k (Perm.prep k' (dnorm (Perm.trans a b)))) Y

      -- σ-cancellation: permute p ≈Term canonical form ≈Term permute q'.
      collapse-eq : permute (PermProp.map⁺ vlab p)
                  ≈Term permute (PermProp.map⁺ vlab Y)
                          ∘ (id ⊗₁ (id ⊗₁
                              (permute (PermProp.map⁺ vlab b)
                                ∘ permute (PermProp.map⁺ vlab a))))
      collapse-eq = b-swap-sigma-collapse-to-canonical vlab a b Y

      canonical-eq : permute (PermProp.map⁺ vlab Y)
                       ∘ (id ⊗₁ (id ⊗₁
                           (permute (PermProp.map⁺ vlab b)
                             ∘ permute (PermProp.map⁺ vlab a))))
                   ≈Term permute (PermProp.map⁺ vlab q')
      canonical-eq = canonical-form-equals-q' vlab a b Y

      -- Measure decrease: size eq, total-l eq (both 0), swap-count strict less.
      size-eq : size q' ≡ size p
      size-eq = sym (size-bswap-q'-eq a b Y)

      norm-Y : total-l Y ≡ 0
      norm-Y = total-l-bswap-extract-Y a b Y norm

      total-l-q'-zero : total-l q' ≡ 0
      total-l-q'-zero = total-l-bswap-q'-zero a b Y norm-Y

      sc-strict-< : swap-count q' < swap-count p
      sc-strict-< = swap-count-bswap-q'-strict-< a b Y

      -- Build the ≪₃ witness.
      bare-≪ : (size p , 0 , swap-count q') ≪₃ (size p , 0 , swap-count p)
      bare-≪ = ≪₃-thd sc-strict-<

      step1 : (size p , 0 , swap-count q') ≪₃ (size p , total-l p , swap-count p)
      step1 = subst (λ z → (size p , 0 , swap-count q') ≪₃ (size p , z , swap-count p))
                    (sym norm) bare-≪

      step2 : (size p , total-l q' , swap-count q') ≪₃ (size p , total-l p , swap-count p)
      step2 = subst (λ z → (size p , z , swap-count q') ≪₃ (size p , total-l p , swap-count p))
                    (sym total-l-q'-zero) step1

      sub-≪ : measure q' ≪₃ measure p
      sub-≪ = subst (λ z → (z , total-l q' , swap-count q') ≪₃ measure p)
                    (sym size-eq) step2

      -- Recursive call.
      ih : permute (PermProp.map⁺ vlab q') ≈Term id
      ih = self-rec q' sub-≪

  in begin
       permute (PermProp.map⁺ vlab p)
         ≈⟨ collapse-eq ⟩
       permute (PermProp.map⁺ vlab Y)
         ∘ (id ⊗₁ (id ⊗₁ (permute (PermProp.map⁺ vlab b)
                          ∘ permute (PermProp.map⁺ vlab a))))
         ≈⟨ canonical-eq ⟩
       permute (PermProp.map⁺ vlab q')
         ≈⟨ ih ⟩
       id
     ∎

--------------------------------------------------------------------------------
-- ## NormalFormHandler with triple lex measure.
--
-- The handler signature only handles `trans p₁ p₂` (the only catch-all
-- pattern that gets delegated by `self-loop-lex3`).  This avoids
-- needing to handle all `xs ↭ xs` shapes for totality.

NormalFormHandler3 : Set
NormalFormHandler3 =
  ∀ {n} (vlab : Fin n → X) {xs ms : List (Fin n)} (uniq : Unique xs)
      (p₁ : xs Perm.↭ ms) (p₂ : ms Perm.↭ xs)
      (acc-p : Acc _≪₃_ (measure (Perm.trans p₁ p₂)))
      (norm : total-l (Perm.trans p₁ p₂) ≡ 0)
      (self-rec
        : ∀ (q : xs Perm.↭ xs)
          → measure q ≪₃ measure (Perm.trans p₁ p₂)
          → permute (PermProp.map⁺ vlab q) ≈Term id)
    → permute (PermProp.map⁺ vlab (Perm.trans p₁ p₂)) ≈Term id

--------------------------------------------------------------------------------
-- ## Main: constructive handler parameterized over the two-cascade
--    residual.

module WithTwoResidual (tcr : TwoCascadeResidual) where
  open TwoCascadeResidual tcr

  constructive-two-cascade-handler : NormalFormHandler3

  -- The handler now takes p₁ and p₂ separately.  We dispatch on them.

  -- ----- trans refl p₂ -----
  constructive-two-cascade-handler vlab uniq Perm.refl p₂ _ _ self-rec =
    let sub-< : measure p₂ ≪₃ measure (Perm.trans Perm.refl p₂)
        sub-< = ≪₃-fst {l₁ = total-l p₂}
                       {l₂ = total-l p₂}
                       {c₁ = swap-count p₂}
                       {c₂ = swap-count p₂}
                       (s≤s (n≤1+n (size p₂)))
        ih = self-rec p₂ sub-<
    in begin
         permute (PermProp.map⁺ vlab p₂) ∘ id
           ≈⟨ idʳ ⟩
         permute (PermProp.map⁺ vlab p₂)
           ≈⟨ ih ⟩
         id
       ∎

  -- ----- trans p₁ refl -----
  constructive-two-cascade-handler vlab uniq p₁ Perm.refl _ _ self-rec =
    let sub-< : measure p₁ ≪₃ measure (Perm.trans p₁ Perm.refl)
        sub-< = ≪₃-fst {l₁ = total-l p₁}
                       {l₂ = total-l (Perm.trans p₁ Perm.refl)}
                       {c₁ = swap-count p₁}
                       {c₂ = swap-count (Perm.trans p₁ Perm.refl)}
                       (s≤s (m≤m+n (size p₁) 1))
        ih = self-rec p₁ sub-<
    in begin
         id ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ idˡ ⟩
         permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ih ⟩
         id
       ∎

  -- ----- trans (prep .k a) (prep .k b) ----- DEAD BRANCH (handled by
  -- self-loop-lex3 directly before reaching the handler).  Dispatched
  -- to residual field for totality.
  constructive-two-cascade-handler vlab {k ∷ xs'} uniq
      (Perm.prep .k a) (Perm.prep .k b) acc-p norm self-rec =
    dead-prep-prep-aligned vlab uniq a b acc-p norm self-rec

  -- ----- trans (swap k k' a) (swap k' k b) ----- DEAD BRANCH.
  constructive-two-cascade-handler vlab {k ∷ k' ∷ rest} uniq
      (Perm.swap .k .k' a) (Perm.swap .k' .k b) acc-p norm self-rec =
    dead-swap-swap-aligned vlab uniq a b acc-p norm self-rec

  -- ----- trans (prep k _) (swap k k _) ----- impossible by Unique.
  constructive-two-cascade-handler vlab ((k≢k ∷ _) ∷ _)
      (Perm.prep k _) (Perm.swap k k _) _ _ _ =
    ⊥-elim (k≢k refl)

  -- ----- trans (swap k k _) (prep k _) ----- impossible by Unique.
  constructive-two-cascade-handler vlab ((k≢k ∷ _) ∷ _)
      (Perm.swap k k _) (Perm.prep k _) _ _ _ =
    ⊥-elim (k≢k refl)

  -- ----- trans p₁ (trans refl p₂') ----- refl-strip via self-rec.
  constructive-two-cascade-handler vlab uniq
      p₁ (Perm.trans Perm.refl p₂') _ _ self-rec =
    let q = Perm.trans p₁ p₂'
        size-< : size q < size (Perm.trans p₁ (Perm.trans Perm.refl p₂'))
        size-< = s≤s (refl-strip-< (size p₁) (size p₂'))
        sub-< : measure q ≪₃ measure (Perm.trans p₁ (Perm.trans Perm.refl p₂'))
        sub-< = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l (Perm.trans p₁ (Perm.trans Perm.refl p₂'))}
                       {c₁ = swap-count q}
                       {c₂ = swap-count (Perm.trans p₁ (Perm.trans Perm.refl p₂'))}
                       size-<
        ih = self-rec q sub-<
    in begin
         (permute (PermProp.map⁺ vlab p₂') ∘ id) ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ∘-resp-≈ idʳ ≈-Term-refl ⟩
         permute (PermProp.map⁺ vlab p₂') ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ih ⟩
         id
       ∎

  -- =====================================================================
  -- (A.prep-aligned): trans (prep .k a) (trans (prep .k b) Y)
  -- =====================================================================
  constructive-two-cascade-handler vlab {k ∷ xs'} (_ ∷ uniq')
      (Perm.prep .k a) (Perm.trans (Perm.prep .k b) Y) _ _ self-rec =
    let q = Perm.trans (Perm.prep k (Perm.trans a b)) Y
        size-q-< : size q < size (Perm.trans (Perm.prep k a)
                                    (Perm.trans (Perm.prep k b) Y))
        size-q-< = prep-fusion-size-< (size a) (size b) (size Y)
        sub-< : measure q ≪₃ measure (Perm.trans (Perm.prep k a)
                                         (Perm.trans (Perm.prep k b) Y))
        sub-< = ≪₃-fst {l₁ = total-l q}
                       {l₂ = total-l (Perm.trans (Perm.prep k a)
                                         (Perm.trans (Perm.prep k b) Y))}
                       {c₁ = swap-count q}
                       {c₂ = swap-count (Perm.trans (Perm.prep k a)
                                            (Perm.trans (Perm.prep k b) Y))}
                       size-q-<
        ih = self-rec q sub-<
        pa = permute (PermProp.map⁺ vlab a)
        pb = permute (PermProp.map⁺ vlab b)
        pY = permute (PermProp.map⁺ vlab Y)
    in begin
         (pY ∘ (id ⊗₁ pb)) ∘ (id ⊗₁ pa)
           ≈⟨ assoc ⟩
         pY ∘ ((id ⊗₁ pb) ∘ (id ⊗₁ pa))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym ⊗-∘-dist) ⟩
         pY ∘ ((id ∘ id) ⊗₁ (pb ∘ pa))
           ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl) ⟩
         pY ∘ (id ⊗₁ (pb ∘ pa))
           ≈⟨ ih ⟩
         id
       ∎

  -- =====================================================================
  -- (A.swap): trans (prep .k a) (trans (swap k k' b) Y) → residual.
  -- =====================================================================
  constructive-two-cascade-handler vlab {k ∷ xs'} uniq
      (Perm.prep .k a) (Perm.trans (Perm.swap k k' b) Y) acc-p norm self-rec =
    A-swap vlab uniq a b Y acc-p norm self-rec

  -- =====================================================================
  -- (B.prep): trans (swap .k .k' a) (trans (prep k' b) Y) → residual.
  -- =====================================================================
  constructive-two-cascade-handler vlab {k ∷ k' ∷ rest} uniq
      (Perm.swap .k .k' a) (Perm.trans (Perm.prep .k' b) Y) acc-p norm self-rec =
    B-prep vlab uniq a b Y acc-p norm self-rec

  -- =====================================================================
  -- (B.swap): trans (swap .k .k' a) (trans (swap k' k b) Y)
  --           → CLOSED CONSTRUCTIVELY via σ-cancellation + self-rec.
  -- =====================================================================
  constructive-two-cascade-handler vlab {k ∷ k' ∷ rest} uniq
      (Perm.swap .k .k' a) (Perm.trans (Perm.swap .k' .k b) Y) acc-p norm self-rec =
    discharge-B-swap-3 vlab uniq a b Y acc-p norm self-rec

  -- =====================================================================
  -- Impossible: trans (prep _ _) (trans (trans _ _) _) has total-l > 0.
  -- =====================================================================
  constructive-two-cascade-handler vlab uniq
      (Perm.prep _ p') (Perm.trans (Perm.trans p₁ p₂) p₃) _ norm _ =
    ⊥-elim (+-suc-nonzero (total-l p') (total-l p₁ + total-l p₂ + total-l p₃) norm)

  constructive-two-cascade-handler vlab uniq
      (Perm.swap _ _ p') (Perm.trans (Perm.trans p₁ p₂) p₃) _ norm _ =
    ⊥-elim (+-suc-nonzero (total-l p') (total-l p₁ + total-l p₂ + total-l p₃) norm)

  -- ----- trans (trans _ _) _ : impossible (total-l > 0 from trans-trans) -----
  constructive-two-cascade-handler vlab uniq
      (Perm.trans _ _) _ _ () _

--------------------------------------------------------------------------------
-- ## Bundle: with TwoCascadeResidual, obtain SelfLoopPostulate.

  selfLoopPostulate : SelfLoopPostulate
  selfLoopPostulate = record
    { Fin-permute-self-loop-id = λ uniq vlab p →
        self-loop-lex3 vlab uniq p (≪₃-wf (measure p))
          (constructive-two-cascade-handler vlab)
    }

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--   * `swap-count` measure with map⁺ preservation.
--   * `swap-count-dnorm` — dnorm preserves swap-count.
--   * `_≪₃_` lex order on (size, total-l, swap-count) with
--     well-foundedness via three-stage Acc descent.
--   * `self-loop-lex3` — lex-Acc recursion on triple measure.
--   * `discharge-B-swap-3` — CONSTRUCTIVE closure of B-swap via
--     `σ-block-involutive` (σ ∘ σ ≈ id) and `σ-block-natural₃`
--     (re-derived locally), reducing swap-count strictly by 2.
--     The rewrite target uses `dnorm (trans a b)` to keep total-l = 0.
--   * `TwoCascadeResidual` — narrowed residual record with:
--     - `A-swap` (σ-naturality across non-σ morphism)
--     - `B-prep` (σ-naturality across non-σ morphism)
--     - `dead-prep-prep-aligned` (unreachable in practice)
--     - `dead-swap-swap-aligned` (unreachable in practice)
--   * `WithTwoResidual.selfLoopPostulate` — bundles a SelfLoopPostulate.
--
-- ## Discharge status:
--   * B-swap: FULL constructive closure (this file's contribution).
--   * A-swap, B-prep: remain as residual fields (σ-naturality across
--     non-σ-block morphisms doesn't decrease swap-count).
--   * dead-prep-prep-aligned, dead-swap-swap-aligned: residual fields
--     for totality only; `self-loop-lex3` catches these patterns
--     before invoking the handler.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `TwoCascadeResidual` record.
--------------------------------------------------------------------------------
