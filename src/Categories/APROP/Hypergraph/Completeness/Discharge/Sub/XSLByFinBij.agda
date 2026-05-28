{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive discharge of `SelfLoopPostulate.Fin-permute-self-loop-id`
-- via the generic FinBij faithfulness machinery in
-- `Categories.PermuteCoherence.*`.
--
-- For a Fin-level self-loop `p : xs ↭ xs` with `Unique xs`:
--
--   1. The bijection `eval-↭ p` sends each position to one with the
--      same lookup-element (by `lookup-eval-↭`).  With `Unique xs`,
--      this forces the bijection to be `id-fb`
--      (`unique-self-loop-eval-id`).
--
--   2. The X-level mapped bijection `eval-↭ (map⁺ vlab p)` agrees
--      pointwise with `eval-↭ p` (modulo a propositional length cast),
--      so it is also `id-fb`.
--
--   3. Apply the generic `permute-self-loop-id` (from
--      `Categories.PermuteCoherence.Faithfulness`, parameterised by a
--      `FaithfulnessResidual`) to obtain `Fa.permute (map⁺ vlab p)
--      ≈Term id`.
--
--   4. The generic and APROP `permute` coincide pointwise (the two
--      definitions are α-equivalent; `permute-bridge` proves it).
--
-- This module is `--safe --with-K` (matching the other Discharge
-- modules).  No new postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.XSLByFinBij
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (SelfLoopPostulate; module SelfLoopPostulate)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
import Categories.PermuteCoherence.Faithfulness as Faith

open import Categories.Category using (Category)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open import Data.List.Base using (List; []; _∷_; length; lookup; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Empty using (⊥-elim)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

------------------------------------------------------------------------
-- ## 1.  Lookup invariance of `eval-↭`.

private
  app : ∀ {n m} → FinBij n m → Fin n → Fin m
  app π i = π P.⟨$⟩ʳ i

lookup-eval-↭
  : ∀ {a} {A : Set a} {xs ys : List A} (r : xs Perm.↭ ys)
      (i : Fin (length xs))
  → lookup xs i ≡ lookup ys (app (eval-↭ r) i)
lookup-eval-↭ Perm.refl i = refl
lookup-eval-↭ (Perm.prep x p) zero    = refl
lookup-eval-↭ (Perm.prep x p) (suc i) = lookup-eval-↭ p i
lookup-eval-↭ (Perm.swap x y p) 0F            = refl
lookup-eval-↭ (Perm.swap x y p) (suc 0F)      = refl
lookup-eval-↭ (Perm.swap x y p) (suc (suc i)) = lookup-eval-↭ p i
lookup-eval-↭ (Perm.trans p q) i =
  trans (lookup-eval-↭ p i)
        (lookup-eval-↭ q (app (eval-↭ p) i))

------------------------------------------------------------------------
-- ## 2.  Lookup injectivity on `Unique` lists.

private
  lookup-≢-head
    : ∀ {a} {A : Set a} {x : A} {xs : List A}
    → All.All (λ y → x ≢ y) xs
    → (j : Fin (length xs))
    → x ≢ lookup xs j
  lookup-≢-head (px All.∷ _)   zero    = px
  lookup-≢-head (_  All.∷ pxs) (suc j) = lookup-≢-head pxs j

lookup-injective
  : ∀ {a} {A : Set a} (xs : List A)
  → Unique xs
  → (i j : Fin (length xs))
  → lookup xs i ≡ lookup xs j → i ≡ j
lookup-injective [] _ () _ _
lookup-injective (x ∷ xs) (h ∷ uniq) zero    zero    eq = refl
lookup-injective (x ∷ xs) (h ∷ uniq) zero    (suc j) eq =
  ⊥-elim (lookup-≢-head h j eq)
lookup-injective (x ∷ xs) (h ∷ uniq) (suc i) zero    eq =
  ⊥-elim (lookup-≢-head h i (sym eq))
lookup-injective (x ∷ xs) (h ∷ uniq) (suc i) (suc j) eq =
  cong suc (lookup-injective xs uniq i j eq)

------------------------------------------------------------------------
-- ## 3.  Fin-level self-loop bijections on `Unique` lists are id.

unique-self-loop-eval-id
  : ∀ {n} {xs : List (Fin n)}
  → Unique xs
  → (r : xs Perm.↭ xs)
  → eval-↭ r ≈-fb id-fb
unique-self-loop-eval-id {xs = xs} uniq r i =
  sym (lookup-injective xs uniq i (app (eval-↭ r) i) (lookup-eval-↭ r i))

------------------------------------------------------------------------
-- ## 4.  Transport to the mapped list, via lookup on the X-level list.
--
-- We avoid the length-cast quagmire by going directly through
-- `lookup-eval-↭` on `map⁺ vlab r`.  The catch: `lookup (map vlab xs)`
-- at a position is `vlab` applied to `lookup xs` at the cast position,
-- and `vlab` need not be injective.  BUT under `Unique xs` we can
-- side-step injectivity: the cast position must equal itself, by an
-- argument about `eval-↭ (map⁺ vlab r)` purely at the position level.
--
-- Concretely: we prove that `eval-↭ (map⁺ vlab r)` is the same
-- function as `eval-↭ r` (modulo a `subst` over the length equality).

private
  length-map-≡
    : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (xs : List A)
    → length (map f xs) ≡ length xs
  length-map-≡ f []       = refl
  length-map-≡ f (x ∷ xs) = cong suc (length-map-≡ f xs)


------------------------------------------------------------------------
-- The bridge: `eval-↭ (map⁺ vlab r)` agrees with `eval-↭ r` after a
-- `subst` on the length isomorphism.  By structural induction on `r`.

  -- Heterogeneous equality on Fin values across length-equal lists.
  --
  -- The key insight: `eval-↭ (map⁺ vlab r) ⟨$⟩ʳ i`, viewed through the
  -- length isomorphism, computes the same Fin element as
  -- `eval-↭ r ⟨$⟩ʳ (cast i)`.
  --
  -- We avoid all explicit casts by writing the statement as a subst
  -- equality (which Agda can check via `J` after pattern-matching the
  -- equality).

  eval-↭-map⁺-via-subst
    : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X) (r : xs Perm.↭ ys)
    → ∀ (i : Fin (length xs))
    → subst Fin (sym (length-map-≡ vlab ys))
        (app (eval-↭ r) i)
      ≡ app (eval-↭ (PermProp.map⁺ vlab r))
            (subst Fin (sym (length-map-≡ vlab xs)) i)
  eval-↭-map⁺-via-subst vlab (Perm.refl {xs = xs}) i = refl-aux vlab xs i
    where
      -- For `r = refl`, both `eval-↭`s give `id-fb`.  Need:
      --   subst Fin (sym (len-map)) i ≡ subst Fin (sym (len-map)) i.
      refl-aux : ∀ {n} (vlab : Fin n → X) (xs : List (Fin n))
                   (i : Fin (length xs))
               → subst Fin (sym (length-map-≡ vlab xs)) i
                 ≡ subst Fin (sym (length-map-≡ vlab xs)) i
      refl-aux _ _ _ = refl
  eval-↭-map⁺-via-subst vlab (Perm.prep {xs = xs} {ys = ys} x p) zero =
    prep-zero-aux (length-map-≡ vlab xs) (length-map-≡ vlab ys)
                  (eval-↭ (PermProp.map⁺ vlab p))
    where
      prep-zero-aux
        : ∀ {n n' m m'} (e₁ : n ≡ n') (e₂ : m ≡ m')
            (πM : FinBij n m)
        → subst Fin (sym (cong suc e₂)) (zero {n = m'})
          ≡ app (cons-fb πM) (subst Fin (sym (cong suc e₁)) (zero {n = n'}))
      prep-zero-aux refl refl _ = refl
  eval-↭-map⁺-via-subst vlab (Perm.prep {xs = xs} {ys = ys} x p) (suc i) =
    prep-suc-aux (length-map-≡ vlab xs) (length-map-≡ vlab ys)
                 (eval-↭ p) (eval-↭ (PermProp.map⁺ vlab p)) i
                 (eval-↭-map⁺-via-subst vlab p i)
    where
      -- e₁ : length (map vlab xs) ≡ length xs, so n = mapped, n' = orig.
      -- The "Fin-level" π lives on the original sizes: FinBij n' m'.
      -- The "X-level mapped" πM lives on the mapped sizes: FinBij n m.
      prep-suc-aux
        : ∀ {n n' m m'} (e₁ : n ≡ n') (e₂ : m ≡ m')
            (π : FinBij n' m') (πM : FinBij n m)
            (j : Fin n')
        → subst Fin (sym e₂) (π P.⟨$⟩ʳ j)
            ≡ πM P.⟨$⟩ʳ subst Fin (sym e₁) j
        → subst Fin (sym (cong suc e₂)) (suc (π P.⟨$⟩ʳ j))
            ≡ app (cons-fb πM) (subst Fin (sym (cong suc e₁)) (suc j))
      prep-suc-aux refl refl π πM j ih = cong suc ih
  eval-↭-map⁺-via-subst vlab (Perm.swap {xs = xs} {ys = ys} x y p) 0F =
    swap-0F-aux (length-map-≡ vlab xs) (length-map-≡ vlab ys)
                (eval-↭ (PermProp.map⁺ vlab p))
    where
      swap-0F-aux
        : ∀ {n n' m m'} (e₁ : n ≡ n') (e₂ : m ≡ m')
            (πM : FinBij n m)
        → subst Fin (sym (cong suc (cong suc e₂))) (suc (zero {n = m'}))
            ≡ app (swap-fb _ ∘-fb cons-fb (cons-fb πM))
                  (subst Fin (sym (cong suc (cong suc e₁))) (zero {n = suc n'}))
      swap-0F-aux refl refl _ = refl
  eval-↭-map⁺-via-subst vlab (Perm.swap {xs = xs} {ys = ys} x y p) (suc 0F) =
    swap-1F-aux (length-map-≡ vlab xs) (length-map-≡ vlab ys)
                (eval-↭ (PermProp.map⁺ vlab p))
    where
      swap-1F-aux
        : ∀ {n n' m m'} (e₁ : n ≡ n') (e₂ : m ≡ m')
            (πM : FinBij n m)
        → subst Fin (sym (cong suc (cong suc e₂))) (zero {n = suc m'})
            ≡ app (swap-fb _ ∘-fb cons-fb (cons-fb πM))
                  (subst Fin (sym (cong suc (cong suc e₁))) (suc (zero {n = n'})))
      swap-1F-aux refl refl _ = refl
  eval-↭-map⁺-via-subst vlab (Perm.swap {xs = xs} {ys = ys} x y p) (suc (suc i)) =
    swap-ss-aux (length-map-≡ vlab xs) (length-map-≡ vlab ys)
                (eval-↭ p) (eval-↭ (PermProp.map⁺ vlab p)) i
                (eval-↭-map⁺-via-subst vlab p i)
    where
      swap-ss-aux
        : ∀ {n n' m m'} (e₁ : n ≡ n') (e₂ : m ≡ m')
            (π : FinBij n' m') (πM : FinBij n m)
            (j : Fin n')
        → subst Fin (sym e₂) (π P.⟨$⟩ʳ j)
            ≡ πM P.⟨$⟩ʳ subst Fin (sym e₁) j
        → subst Fin (sym (cong suc (cong suc e₂)))
            (suc (suc (π P.⟨$⟩ʳ j)))
          ≡ app (swap-fb _ ∘-fb cons-fb (cons-fb πM))
                (subst Fin (sym (cong suc (cong suc e₁))) (suc (suc j)))
      swap-ss-aux refl refl π πM j ih = cong (λ z → suc (suc z)) ih
  eval-↭-map⁺-via-subst vlab (Perm.trans {xs = xs} {ys = zs} {zs = ys} p q) i =
    -- eval-↭ (trans p q) ⟨$⟩ʳ i = eval-↭ q ⟨$⟩ʳ (eval-↭ p ⟨$⟩ʳ i).
    -- IH on p:
    --   subst (sym e_zs) (eval-↭ p ⟨$⟩ʳ i)
    --     ≡ eval-↭ (map⁺ vlab p) ⟨$⟩ʳ subst (sym e_xs) i
    -- IH on q at (eval-↭ p ⟨$⟩ʳ i):
    --   subst (sym e_ys) (eval-↭ q ⟨$⟩ʳ (eval-↭ p ⟨$⟩ʳ i))
    --     ≡ eval-↭ (map⁺ vlab q) ⟨$⟩ʳ subst (sym e_zs) (eval-↭ p ⟨$⟩ʳ i)
    --     ≡ eval-↭ (map⁺ vlab q) ⟨$⟩ʳ (eval-↭ (map⁺ vlab p) ⟨$⟩ʳ subst (sym e_xs) i)
    let ih-p = eval-↭-map⁺-via-subst vlab p i
        ih-q = eval-↭-map⁺-via-subst vlab q (app (eval-↭ p) i)
    in trans ih-q
             (cong (app (eval-↭ (PermProp.map⁺ vlab q))) ih-p)

-- Bridge to `≈-fb id-fb` on the mapped derivation, for self-loops.

private
  subst-sym-subst : ∀ {a} {A : Set a} {B : A → Set} {x y : A} (e : x ≡ y)
                    (b : B x)
                  → subst B (sym e) (subst B e b) ≡ b
  subst-sym-subst refl b = refl

unique-self-loop-eval-id-mapped
  : ∀ {n} {xs : List (Fin n)} (vlab : Fin n → X)
  → Unique xs
  → (r : xs Perm.↭ xs)
  → eval-↭ (PermProp.map⁺ vlab r) ≈-fb id-fb
unique-self-loop-eval-id-mapped {xs = xs} vlab uniq r i =
  let e   = length-map-≡ vlab xs
      j   = subst Fin e i                                  -- j : Fin (length xs)
      -- i ≡ subst Fin (sym e) j
      i≡  : i ≡ subst Fin (sym e) j
      i≡  = sym (subst-sym-subst e i)
      -- bridge j : subst (sym e) (app (eval-↭ r) j)
      --            ≡ app (eval-↭ (map⁺ vlab r)) (subst (sym e) j)
      bridge = eval-↭-map⁺-via-subst vlab r j
      fin-id = unique-self-loop-eval-id uniq r j   -- app (eval-↭ r) j ≡ j
      -- Compose:
      --   app (eval-↭ (map⁺ vlab r)) (subst (sym e) j)
      --     ≡ subst (sym e) (app (eval-↭ r) j)              (sym bridge)
      --     ≡ subst (sym e) j                                (cong of fin-id)
      --     ≡ i                                              (subst-sym-subst)
      step₁ : app (eval-↭ (PermProp.map⁺ vlab r)) (subst Fin (sym e) j) ≡ i
      step₁ = trans (sym bridge)
                    (trans (cong (subst Fin (sym e)) fin-id)
                           (subst-sym-subst e i))
  in trans (cong (app (eval-↭ (PermProp.map⁺ vlab r))) i≡) step₁

------------------------------------------------------------------------
-- ## 5.  Bridging APROP's `permute` and the generic Faithfulness `permute`.

private
  module Fa = Faith asFreeMonoidalData

unflatten-≡
  : (xs : List X) → Fa.unflatten xs ≡ unflatten xs
unflatten-≡ []       = refl
unflatten-≡ (x ∷ xs) = cong (Var x ⊗₀_) (unflatten-≡ xs)

-- Cast a HomTerm along propositional equalities of its objects.
cast-Hom
  : ∀ {A A' B B' : ObjTerm}
  → A ≡ A' → B ≡ B'
  → HomTerm A B → HomTerm A' B'
cast-Hom refl refl h = h

cast-Hom-id
  : ∀ {A A' : ObjTerm} (e : A ≡ A')
  → cast-Hom e e (id {A}) ≈Term id {A'}
cast-Hom-id refl = ≈-Term-refl

cast-Hom-≈
  : ∀ {A A' B B' : ObjTerm}
      (eA : A ≡ A') (eB : B ≡ B')
      {h₁ h₂ : HomTerm A B}
  → h₁ ≈Term h₂ → cast-Hom eA eB h₁ ≈Term cast-Hom eA eB h₂
cast-Hom-≈ refl refl eq = eq

permute-bridge
  : ∀ {xs ys : List X} (p : xs Perm.↭ ys)
  → cast-Hom (unflatten-≡ xs) (unflatten-≡ ys) (Fa.permute p) ≈Term permute p
permute-bridge {xs} {.xs} Perm.refl = cast-Hom-id (unflatten-≡ xs)
permute-bridge {xs = x ∷ xs} {ys = .x ∷ ys} (Perm.prep _ p) =
  prep-aux x (unflatten-≡ xs) (unflatten-≡ ys)
           (Fa.permute p) (permute p)
           (permute-bridge p)
  where
    prep-aux
      : ∀ (x : X) {A A' B B' : ObjTerm}
          (e₁ : A ≡ A') (e₂ : B ≡ B')
          (f : HomTerm A B) (g : HomTerm A' B')
      → cast-Hom e₁ e₂ f ≈Term g
      → cast-Hom (cong (Var x ⊗₀_) e₁) (cong (Var x ⊗₀_) e₂) (id ⊗₁ f) ≈Term id ⊗₁ g
    prep-aux _ refl refl f g ih = ⊗-resp-≈ ≈-Term-refl ih
permute-bridge {xs = x ∷ y ∷ xs} {ys = .y ∷ .x ∷ ys} (Perm.swap _ _ p) =
  swap-aux x y (unflatten-≡ xs) (unflatten-≡ ys)
           (Fa.permute p) (permute p)
           (permute-bridge p)
  where
    swap-aux
      : ∀ (x y : X) {A A' B B' : ObjTerm}
          (e₁ : A ≡ A') (e₂ : B ≡ B')
          (f : HomTerm A B) (g : HomTerm A' B')
      → cast-Hom e₁ e₂ f ≈Term g
      → cast-Hom (cong (Var x ⊗₀_) (cong (Var y ⊗₀_) e₁))
                 (cong (Var y ⊗₀_) (cong (Var x ⊗₀_) e₂))
                 ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
        ≈Term (id ⊗₁ (id ⊗₁ g)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    swap-aux _ _ refl refl f g ih =
      ∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl ih))
               ≈-Term-refl
permute-bridge (Perm.trans p q) =
  trans-aux (unflatten-≡ _) (unflatten-≡ _) (unflatten-≡ _)
            (Fa.permute p) (Fa.permute q)
            (permute p) (permute q)
            (permute-bridge p) (permute-bridge q)
  where
    trans-aux
      : ∀ {A A' B B' C C' : ObjTerm}
          (eA : A ≡ A') (eB : B ≡ B') (eC : C ≡ C')
          (fp : HomTerm A B) (fq : HomTerm B C)
          (gp : HomTerm A' B') (gq : HomTerm B' C')
      → cast-Hom eA eB fp ≈Term gp
      → cast-Hom eB eC fq ≈Term gq
      → cast-Hom eA eC (fq ∘ fp) ≈Term (gq ∘ gp)
    trans-aux refl refl refl fp fq gp gq ihp ihq = ∘-resp-≈ ihq ihp

------------------------------------------------------------------------
-- ## 6.  Constructive `SelfLoopPostulate` parameterised by the
--        FinBij faithfulness residual.

module WithFaithfulnessResidual (R : Fa.FaithfulnessResidual) where

  -- Access the headline corollary by feeding the residual.
  -- `permute-self-loop-id` is now parameterised by the *narrow*
  -- residual (`TransSelfLoopResidual`); we obtain it from the wide
  -- residual `R` via `Fa.wide⇒narrow`.
  permute-self-loop-id = Fa.permute-self-loop-id (Fa.wide⇒narrow R)

  fin-self-loop-id
    : ∀ {n} {xs : List (Fin n)}
        (uniq : Unique xs)
        (vlab : Fin n → X)
        (r : xs Perm.↭ xs)
    → permute (PermProp.map⁺ vlab r) ≈Term id
  fin-self-loop-id {xs = xs} uniq vlab r =
    let r'      = PermProp.map⁺ vlab r
        e       = unflatten-≡ (map vlab xs)
        eval-id = unique-self-loop-eval-id-mapped vlab uniq r
        -- Fa.permute r' ≈Term id  (in the generic FreeMonoidal).
        x-id    = permute-self-loop-id r' eval-id
        -- Transport via the cast bridge.
        bridge  = permute-bridge {xs = map vlab xs} {ys = map vlab xs} r'
        -- bridge : cast-Hom e e (Fa.permute r') ≈Term permute r'.
    in begin
         permute r'
           ≈⟨ ≈-Term-sym bridge ⟩
         cast-Hom e e (Fa.permute r')
           ≈⟨ cast-Hom-≈ e e x-id ⟩
         cast-Hom e e id
           ≈⟨ cast-Hom-id e ⟩
         id
       ∎

  constructive-self-loop-postulate : SelfLoopPostulate
  constructive-self-loop-postulate = record
    { Fin-permute-self-loop-id =
        λ {n} {xs} uniq vlab r → fin-self-loop-id uniq vlab r
    }
