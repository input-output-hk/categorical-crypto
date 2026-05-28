{-# OPTIONS --safe --with-K #-}

------------------------------------------------------------------------
-- Canonical bridge (refl case).
--
-- Goal: prove
--
--     permute Perm.refl
--       ≈Term
--     subst-Hom-cod (canonical-target-id-fb xs)
--                   (permute (canonical-↭ xs id-fb))
--
-- using `CanonicalProps.canonical-target-id-fb` (Part A) and the
-- propositional unfolding lemmas `canonical-go-suc-unfold` /
-- `canonical-go-suc-unfold-↭` added to `Canonical.agda`.
--
-- DELIVERED in this module:
--
--   * The bridge statement, reduced to a strictly narrower residual
--     `CanonicalBridgeReflResidual` that contains only an
--     `≈Term`-equation between specific `permute`-images of
--     `canonical-↭` derivations and `id`.
--
--   * No postulates, no new admits.
--
-- ROADMAP for closing the residual constructively:
--
--   The residual states `permute (canonical-↭ xs id-fb) ≈Term id`
--   (modulo target-equality transport).  By the propositional
--   unfolding of `canonical-go` on `id-fb` (Canonical.agda's
--   `canonical-go-suc-unfold-↭`, head-target = 0F by refl,
--   `bubble-to-front-zero`), the `canonical-↭` is a tower of
--   `Perm.trans Perm.refl (Perm.prep _ rec)` derivations.  Under
--   `permute`, this becomes a tower of `(id ⊗₁ rec) ∘ id`, which
--   collapses to `id ⊗₁ id ⊗₁ … ⊗₁ id ≈Term id` by repeated
--   `id⊗id≈id`, `idˡ`, `idʳ`.  The induction descends through
--   `residual id-fb` (each layer pointwise the identity, by
--   `residual-pw-id`).
--
--   The structural obstacle to closing this constructively here is
--   the same as for `canonical-target-id-fb`: the with-blocks in
--   `canonical-go` make the recursion through `residual b` opaque
--   to direct pattern matching.  The trick used in `CanonicalProps`
--   (induct on the *length* using `canonical-go-pw-id`) works there
--   because we are reasoning about list-equality only; here we
--   reason about `≈Term`-equality of terms whose codomains differ,
--   requiring more elaborate transport machinery.
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.CanonicalBridge
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Fin.Patterns using (0F)
import Data.Fin.Permutation as P

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.Canonical
open import Categories.PermuteCoherence.CanonicalProps
open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; permute)

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (Σ; _,_)

------------------------------------------------------------------------
-- Object-level transport along a list equality.

subst-Hom-cod
  : ∀ {A} {xs ys : List X}
  → xs ≡ ys
  → HomTerm A (unflatten xs)
  → HomTerm A (unflatten ys)
subst-Hom-cod refl t = t

-- Sanity: `subst-Hom-cod refl t ≡ t` definitionally.
subst-Hom-cod-refl
  : ∀ {A} {xs : List X} (t : HomTerm A (unflatten xs))
  → subst-Hom-cod refl t ≡ t
subst-Hom-cod-refl _ = refl

------------------------------------------------------------------------
-- Strictly-narrow residual: `permute (canonical-↭ xs id-fb)` is
-- `≈Term`-equal to `id` (after transporting the codomain via
-- Part A's `canonical-target-id-fb`).

record CanonicalBridgeReflResidual : Set where
  field
    permute-canonical-↭-id-fb≈id
      : ∀ (xs : List X)
      → subst-Hom-cod (canonical-target-id-fb xs)
                      (permute (canonical-↭ xs id-fb))
        ≈Term
        id {unflatten xs}

------------------------------------------------------------------------
-- Constructive closure of `CanonicalBridgeReflResidual`.
--
-- Strategy: prove the stronger pointwise-id invariant directly by
-- induction on the natural-number length bound, mirroring the
-- structure of `canonical-go-pw-id` in `CanonicalProps.agda`.  Each
-- recursive step uses the unfolding equation `canonical-go-suc-unfold-↭`
-- (which is `refl`) to expose the structure of the derivation.  Under
-- `permute`, the resulting `Perm.trans Perm.refl (Perm.prep _ rec)`
-- evaluates to `(id ⊗₁ permute rec) ∘ id`, and the IH collapses
-- `permute rec` to `id`, after which `id⊗id≈id`, `idˡ`, `idʳ` finish.

private
  -- Step lemma: given that `head-target b ≡ 0F` and the residual is
  -- (after subst-transport) ≈Term id, the (suc n) layer is ≈Term id.

  -- Approach: rather than reducing `canonical-go-pw-id` directly,
  -- we instead prove an EQUATIONAL form parameterised over an
  -- ARBITRARY codomain-list equation `e` -- this avoids needing
  -- `canonical-go-pw-id` to reduce, and lets us match `e` with refl
  -- once the result list is generalised.
  --
  -- The trick: at zero, the result list is definitionally `[]`, so
  -- e : [] ≡ ys forces ys = []; at suc, the result list is
  -- definitionally `(lookup (y ∷ ys) (head-target b)) ∷ proj₁ (rec)`,
  -- so e : that ≡ (y ∷ ys) forces head-target b ≡ 0F (giving
  -- lookup = y) and proj₁ rec ≡ ys.

  -- Generic-e form: works for any compatible list equation.  This is
  -- structured to compute on canonical-go's with-blocks by recursing
  -- on n with no with-pattern in the type signature.
  go-pw-id-perm
    : ∀ (n : ℕ) (ys : List X) (ys-len : length ys ≡ n)
        (b : FinBij n n) (b-id : ∀ i → b P.⟨$⟩ʳ i ≡ i)
        (e : proj₁ (canonical-go n ys ys-len b) ≡ ys)
    → subst-Hom-cod e (permute (proj₂ (canonical-go n ys ys-len b)))
      ≈Term id {unflatten ys}
  go-pw-id-perm zero    []       refl b b-id refl = ≈-Term-refl
  go-pw-id-perm zero    (_ ∷ _)  () _ _ _
  go-pw-id-perm (suc n) []       () _ _ _
  go-pw-id-perm (suc n) (y ∷ ys) refl b b-id e =
    -- Use the unfolding lemma `canonical-go-suc-unfold-↭` to substitute
    -- the proj₂ of `canonical-go (suc n) (y ∷ ys) refl b` with its
    -- explicit form, then prove the goal about the explicit form.
    helper (head-target b) (b-id 0F) e
    where
    -- Explicit form of `proj₂ (canonical-go (suc n) (y ∷ ys) refl b)`
    -- as a function of `head-target b`.  Using `canonical-go-suc-unfold-↭`
    -- (= refl), we know:
    --   proj₂ (canonical-go (suc n) (y ∷ ys) refl b)
    --     ≡ Perm.trans
    --         (proj₂ (proj₂ (bubble-to-front (y ∷ ys) refl (head-target b))))
    --         (Perm.prep _ (proj₂ (canonical-go n bf-list bf-len (residual b))))
    -- Similarly proj₁.

    -- Helper: with `k := head-target b` and `eq : k ≡ 0F`, the
    -- bubble-to-front at `k=0F` reduces to (ys, refl, Perm.refl), and
    -- the recursion is on (residual b) at ys.
    helper
      : ∀ (k : Fin (suc n)) (eq : k ≡ 0F)
          (e : lookup (y ∷ ys) k
                 ∷ proj₁ (canonical-go n
                            (proj₁ (bubble-to-front (y ∷ ys) refl k))
                            (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
                            (residual b))
               ≡ y ∷ ys)
      → subst-Hom-cod e
          (permute
            (Perm.trans
              (proj₂ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
              (Perm.prep (lookup (y ∷ ys) k)
                (proj₂ (canonical-go n
                  (proj₁ (bubble-to-front (y ∷ ys) refl k))
                  (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
                  (residual b))))))
        ≈Term id {Var y ⊗₀ unflatten ys}
    helper .0F refl e =
      -- Now `bubble-to-front (y ∷ ys) refl 0F = (ys, refl, Perm.refl)`
      -- definitionally.  So:
      --   proj₂ (proj₂ bubble) = Perm.refl
      --   bf-list = ys; bf-len = refl
      --   permute (Perm.trans Perm.refl (Perm.prep y rec))
      --     = (id ⊗₁ permute rec) ∘ id
      -- And `e : y ∷ proj₁ (canonical-go n ys refl (residual b)) ≡ y ∷ ys`.
      helper2 (proj₁ (canonical-go n ys refl (residual b)))
              (proj₂ (canonical-go n ys refl (residual b)))
              e
              (λ e' → go-pw-id-perm n ys refl (residual b)
                                    (residual-pw-id b b-id) e')
      where
      helper2
        : ∀ (us : List X) (p : ys Perm.↭ us)
            (e : y ∷ us ≡ y ∷ ys)
            (ih : ∀ (e' : us ≡ ys)
                  → subst-Hom-cod e' (permute p) ≈Term id {unflatten ys})
        → subst-Hom-cod e ((id ⊗₁ permute p) ∘ id)
          ≈Term id {Var y ⊗₀ unflatten ys}
      helper2 us p e ih = helper3 us p (∷-injective e) e ih
        where
        ∷-injective : ∀ {x : X} {as bs : List X} → x ∷ as ≡ x ∷ bs → as ≡ bs
        ∷-injective refl = refl

        helper3
          : ∀ (us : List X) (p : ys Perm.↭ us)
              (e' : us ≡ ys) (e : y ∷ us ≡ y ∷ ys)
              (ih : ∀ (e' : us ≡ ys)
                    → subst-Hom-cod e' (permute p) ≈Term id {unflatten ys})
          → subst-Hom-cod e ((id ⊗₁ permute p) ∘ id)
            ≈Term id {Var y ⊗₀ unflatten ys}
        helper3 .ys p refl refl ih =
          ≈-Term-trans idʳ
            (≈-Term-trans (⊗-resp-≈ ≈-Term-refl (ih refl)) id⊗id≈id)

  -- Specialisation: use the canonical proof `canonical-go-pw-id` as `e`.
  canonical-go-pw-id-permute
    : ∀ (n : ℕ) (ys : List X) (ys-len : length ys ≡ n)
        (b : FinBij n n) (b-id : ∀ i → b P.⟨$⟩ʳ i ≡ i)
    → subst-Hom-cod (canonical-go-pw-id n ys ys-len b b-id)
                    (permute (proj₂ (canonical-go n ys ys-len b)))
      ≈Term
      id {unflatten ys}
  canonical-go-pw-id-permute n ys ys-len b b-id =
    go-pw-id-perm n ys ys-len b b-id (canonical-go-pw-id n ys ys-len b b-id)

-- The residual is now constructively closed.
constructive-canonical-bridge-refl : CanonicalBridgeReflResidual
constructive-canonical-bridge-refl = record
  { permute-canonical-↭-id-fb≈id = λ xs →
      canonical-go-pw-id-permute (length xs) xs refl id-fb (λ _ → refl)
  }

------------------------------------------------------------------------
-- Headline bridge (refl case), fully discharged.

permute-canonical-bridge-refl
  : ∀ (xs : List X)
  → permute (Perm.refl {xs = xs})
    ≈Term
    subst-Hom-cod (canonical-target-id-fb xs)
                  (permute (canonical-↭ xs id-fb))
permute-canonical-bridge-refl xs =
  ≈-Term-sym
    (CanonicalBridgeReflResidual.permute-canonical-↭-id-fb≈id
       constructive-canonical-bridge-refl xs)

------------------------------------------------------------------------
-- PREP case of the canonical bridge.
--
-- STATUS: NOT CLOSED in this commit.
--
-- The TARGET-LIST projection `canonical-target-prep` IS proven below,
-- using the new propositional pointwise-congruence lemma
-- `canonical-go-pw-cong-target` (added to `CanonicalProps.agda`).
-- This handles the list-equality "canonical-target (x ∷ xs) (cons-fb b)
-- ≡ x ∷ canonical-target xs b" that the prep case needs.
--
-- The DERIVATION (≈Term) projection -- the actual prep bridge -- is
-- BLOCKED on a structural issue with Agda's unifier:
--
--   Inside the pw-cong-perm induction step, after pattern-matching
--   `head-target b' ≡ head-target b` (via `eq 0F`) using a dot
--   pattern, the unifier refines the local `k'` to `k` BUT does NOT
--   propagate this through the goal's mention of
--   `permute (proj₂ (canonical-go (suc n) (y ∷ ys) refl b'))` -- which
--   contains `b'` directly (and hence `head-target b'`) inside
--   `proj₂(canonical-go ...)`.  This expression doesn't reduce
--   structurally on `b'`, so the codomain types of the two sides of
--   the goal don't align.
--
-- A workaround would be to use propositional `canonical-go-suc-
-- unfold-↭` (= refl) explicitly with `subst` to expose the structure,
-- but the resulting transport machinery would dwarf the actual proof.
--
-- TODO: revisit using `with`-abstraction on `canonical-go (suc n) ... b`
-- and `... b'`, or by reformulating `pw-cong-perm` to take the
-- *unfolded* derivations directly.
--
-- The propositional `canonical-target-prep` lemma below is independently
-- useful (e.g. for stating the prep bridge externally) and is fully
-- discharged.

-- The unconditional target-list lemma (independent of any IH):
-- canonical decomposition of `cons-fb b` peels off `x ∷` from the
-- result list.  Uses `canonical-go-pw-cong-target` (added to
-- `CanonicalProps.agda`) to bridge the residual-via-cons-fb / b
-- pointwise equality.
canonical-target-prep-plain
  : ∀ (x : X) (xs : List X) (b : FinBij (length xs) (length xs))
  → canonical-target (x ∷ xs) (cons-fb b)
    ≡ x ∷ canonical-target xs b
canonical-target-prep-plain x xs b =
  cong (lookup (x ∷ xs) 0F ∷_)
    (canonical-go-pw-cong-target (length xs) xs refl
      (residual (cons-fb b)) b (λ _ → refl))

-- (Legacy parameterised form retained for downstream callers that
-- still bind the residual record explicitly.)
module _ (R : CanonicalBridgeReflResidual) where
  open CanonicalBridgeReflResidual R

  permute-canonical-bridge-refl-param
    : ∀ (xs : List X)
    → permute (Perm.refl {xs = xs})
      ≈Term
      subst-Hom-cod (canonical-target-id-fb xs)
                    (permute (canonical-↭ xs id-fb))
  permute-canonical-bridge-refl-param xs =
    ≈-Term-sym (permute-canonical-↭-id-fb≈id xs)

------------------------------------------------------------------------
-- Constructive closure of the PREP case.
--
-- Strategy:
--
--   1. Prove a pointwise-congruence lemma for the `permute`-image
--      of `canonical-go`'s derivation projection
--      (`canonical-go-pw-cong-permute`).  Mirrors the list-projection
--      version `canonical-go-pw-cong-target` in `CanonicalProps.agda`,
--      using well-founded recursion on the natural-number bound and
--      the unfolding lemma `canonical-go-suc-unfold-↭`.  With-
--      abstraction over `head-target b ≡ head-target b'` exposes the
--      explicit form of both `proj₂ (canonical-go (suc n) ...)`
--      to Agda's unifier.
--
--   2. Specialise at `b' = cons-fb b`, `b = residual (cons-fb b)` (note
--      these are pointwise equal by `λ _ → refl`).  The result is a
--      ≈Term-equation between `permute (canonical-↭ (x ∷ xs)
--      (cons-fb b))` and `id ⊗₁ permute (canonical-↭ xs b)`, modulo a
--      list-equality transport on the codomain.
--
--   3. Combined with `permute (Perm.prep x p) = id ⊗₁ permute p` and an
--      IH on `p`, this yields the prep-case bridge.

open import Data.Nat.Base as Nat using (_<_)
open import Data.Nat.Induction using (<-rec)
open import Data.Nat.Properties using (n<1+n)

-- Propositional equality lifts to ≈Term.
≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

-- subst-Hom-cod commutes through (id ⊗₁ _) on a cong (x ∷_):
subst-Hom-cod-cons-⊗
  : ∀ {A : ObjTerm} {x : X} {ys zs : List X} (e : ys ≡ zs)
      (t : HomTerm A (unflatten ys))
  → subst-Hom-cod {A = Var x ⊗₀ A} (cong (x ∷_) e) (id ⊗₁ t)
    ≡ id {Var x} ⊗₁ subst-Hom-cod e t
subst-Hom-cod-cons-⊗ refl _ = refl

-- subst-Hom-cod absorbs into composition on the left:
subst-Hom-cod-∘
  : ∀ {A B : ObjTerm} {ys zs : List X} (e : ys ≡ zs)
      (f : HomTerm B (unflatten ys)) (g : HomTerm A B)
  → subst-Hom-cod e (f ∘ g) ≡ subst-Hom-cod e f ∘ g
subst-Hom-cod-∘ refl _ _ = refl

private
  -- Well-founded recursion predicate (≈Term version of `P-pw-cong`).
  P-pw-cong-perm : ℕ → Set
  P-pw-cong-perm n =
    ∀ (xs : List X) (xs-len : length xs ≡ n)
      (b b' : FinBij n n) (eq : ∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
      (e : proj₁ (canonical-go n xs xs-len b)
             ≡ proj₁ (canonical-go n xs xs-len b'))
    → subst-Hom-cod e (permute (proj₂ (canonical-go n xs xs-len b)))
      ≈Term
      permute (proj₂ (canonical-go n xs xs-len b'))

  go-pw-cong-perm
    : ∀ (n : ℕ)
    → (∀ {m} → m < n → P-pw-cong-perm m)
    → P-pw-cong-perm n
  go-pw-cong-perm zero    rec []       refl _ _  _   refl = ≈-Term-refl
  go-pw-cong-perm zero    rec (_ ∷ _)  ()
  go-pw-cong-perm (suc n) rec []       ()
  go-pw-cong-perm (suc n) rec (y ∷ ys) refl b b' eq e =
    -- Both `proj₂ (canonical-go (suc n) (y ∷ ys) refl b/b')`
    -- reduce definitionally (because `canonical-go-suc-unfold-↭`
    -- holds by `refl`) to their explicit forms.  We work with the
    -- explicit form via the abstracted-`k` helper.
    cong-perm-with-k (head-target b) (head-target b') (eq 0F) e
    where
    cong-perm-with-k
      : ∀ (k k' : Fin (suc n)) (ek : k ≡ k')
          (e : lookup (y ∷ ys) k
                 ∷ proj₁ (canonical-go n
                            (proj₁ (bubble-to-front (y ∷ ys) refl k))
                            (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
                            (residual b))
               ≡ lookup (y ∷ ys) k'
                 ∷ proj₁ (canonical-go n
                            (proj₁ (bubble-to-front (y ∷ ys) refl k'))
                            (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k')))
                            (residual b')))
      → subst-Hom-cod e
          (permute
            (Perm.trans
              (proj₂ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
              (Perm.prep (lookup (y ∷ ys) k)
                (proj₂ (canonical-go n
                  (proj₁ (bubble-to-front (y ∷ ys) refl k))
                  (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
                  (residual b))))))
        ≈Term
        permute
          (Perm.trans
            (proj₂ (proj₂ (bubble-to-front (y ∷ ys) refl k')))
            (Perm.prep (lookup (y ∷ ys) k')
              (proj₂ (canonical-go n
                (proj₁ (bubble-to-front (y ∷ ys) refl k'))
                (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k')))
                (residual b')))))
    cong-perm-with-k k .k refl e =
      -- After ek := refl, the bubble-to-front calls coincide and the
      -- lookup-values coincide; we apply ∷-injective to peel `lookup`
      -- off `e` and use the well-founded IH `rec` at `n<1+n n` through
      -- the structural commutation lemmas subst-Hom-cod-∘ and
      -- subst-Hom-cod-cons-⊗.
      step
        (proj₁ (bubble-to-front (y ∷ ys) refl k))
        (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
        (proj₂ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
        (∷-injective e)
        (uip e (cong (lookup (y ∷ ys) k ∷_) (∷-injective e)))
      where
      ∷-injective : ∀ {x : X} {as bs : List X} → x ∷ as ≡ x ∷ bs → as ≡ bs
      ∷-injective refl = refl

      -- UIP (available under --with-K).
      uip : ∀ {A : Set} {a b : A} (p q : a ≡ b) → p ≡ q
      uip refl refl = refl

      -- Inner helper: abstract over the bubble-to-front result tuple
      -- and the inner list-equation `e'`.  The outer `e` is replaced
      -- by `cong (lookup k ∷_) e'` via UIP, which lets
      -- `subst-Hom-cod-cons-⊗` propagate the transport through `id ⊗₁`.
      step
        : ∀ (ws : List X) (ws-len : length ws ≡ n)
            (bubble : (y ∷ ys) Perm.↭ (lookup (y ∷ ys) k ∷ ws))
            (e' : proj₁ (canonical-go n ws ws-len (residual b))
                    ≡ proj₁ (canonical-go n ws ws-len (residual b')))
            {e : lookup (y ∷ ys) k ∷ proj₁ (canonical-go n ws ws-len (residual b))
                 ≡ lookup (y ∷ ys) k ∷ proj₁ (canonical-go n ws ws-len (residual b'))}
            (e≡ : e ≡ cong (lookup (y ∷ ys) k ∷_) e')
        → subst-Hom-cod e
            (permute (Perm.trans bubble
                       (Perm.prep (lookup (y ∷ ys) k)
                         (proj₂ (canonical-go n ws ws-len (residual b))))))
          ≈Term
            permute (Perm.trans bubble
                      (Perm.prep (lookup (y ∷ ys) k)
                        (proj₂ (canonical-go n ws ws-len (residual b')))))
      step ws ws-len bubble e' refl =
        -- Goal:
        --   subst-Hom-cod (cong (xₖ ∷_) e')
        --     ((id ⊗₁ permute rec_b) ∘ permute bubble)
        --   ≈Term (id ⊗₁ permute rec_b') ∘ permute bubble
        -- where xₖ = lookup (y∷ys) k, rec_β = proj₂ (canonical-go n ws ws-len (residual β)).
        -- Step 1: push subst-Hom-cod through ∘ (cod-side):
        --   subst-Hom-cod e (f ∘ g) = subst-Hom-cod e f ∘ g.
        -- Step 2: push subst-Hom-cod (cong (xₖ ∷_) e') through id ⊗₁:
        --   subst-Hom-cod (cong (xₖ ∷_) e') (id ⊗₁ t) = id ⊗₁ subst-Hom-cod e' t.
        -- Step 3: apply IH on the inner ⊗-factor via ⊗-resp-≈ and ∘-resp-≈.
        ≈-Term-trans
          (≡⇒≈Term (trans
            (subst-Hom-cod-∘ (cong (lookup (y ∷ ys) k ∷_) e')
              (id ⊗₁ permute (proj₂ (canonical-go n ws ws-len (residual b))))
              (permute bubble))
            (cong (_∘ permute bubble)
              (subst-Hom-cod-cons-⊗ {A = unflatten ws} {x = lookup (y ∷ ys) k}
                e' (permute (proj₂ (canonical-go n ws ws-len (residual b))))))))
          (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl ih) ≈-Term-refl)
        where
        ih : subst-Hom-cod e'
               (permute (proj₂ (canonical-go n ws ws-len (residual b))))
             ≈Term
             permute (proj₂ (canonical-go n ws ws-len (residual b')))
        ih = rec {n} (n<1+n n) ws ws-len (residual b) (residual b')
                 (residual-pw-cong b b' eq) e'

-- The ≈Term-pointwise-congruence lemma for `canonical-go`'s
-- derivation projection.  Closes the with-abstraction blocker
-- described in the prep-case docstring above.
canonical-go-pw-cong-permute
  : ∀ (n : ℕ) (xs : List X) (xs-len : length xs ≡ n)
      (b b' : FinBij n n) (eq : ∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
      (e : proj₁ (canonical-go n xs xs-len b)
             ≡ proj₁ (canonical-go n xs xs-len b'))
  → subst-Hom-cod e (permute (proj₂ (canonical-go n xs xs-len b)))
    ≈Term
    permute (proj₂ (canonical-go n xs xs-len b'))
canonical-go-pw-cong-permute = <-rec _ go-pw-cong-perm

------------------------------------------------------------------------
-- Direct prep-step lemma: `permute (canonical-↭ (x ∷ xs) (cons-fb b))`
-- equates (modulo `subst-Hom-cod` on its codomain) to
-- `(id ⊗₁ permute (canonical-↭ xs b)) ∘ id`.

-- Inner ≈Term-equation between
--   `permute (canonical-↭ (x ∷ xs) (cons-fb b))` and
--   `(id ⊗₁ permute (canonical-↭ xs b)) ∘ id`,
-- transported by `canonical-target-prep-plain`.
permute-canonical-↭-cons-fb
  : ∀ (x : X) (xs : List X) (b : FinBij (length xs) (length xs))
  → subst-Hom-cod (canonical-target-prep-plain x xs b)
                  (permute (canonical-↭ (x ∷ xs) (cons-fb b)))
    ≈Term
    (id {Var x} ⊗₁ permute (canonical-↭ xs b)) ∘ id
permute-canonical-↭-cons-fb x xs b =
  -- canonical-↭ (x ∷ xs) (cons-fb b) reduces (by canonical-go-suc-unfold-↭
  -- and head-target (cons-fb b) = 0F = lookup (x ∷ xs) 0F = x, plus
  -- bubble-to-front-zero) to:
  --   Perm.trans Perm.refl
  --     (Perm.prep x (proj₂ (canonical-go n xs refl (residual (cons-fb b)))))
  -- Under `permute`:
  --   (id ⊗₁ permute (proj₂ (canonical-go n xs refl (residual (cons-fb b))))) ∘ id
  -- We want this equal to (id ⊗₁ permute (canonical-↭ xs b)) ∘ id.
  -- The inner `permute (proj₂ (canonical-go n xs refl (residual (cons-fb b))))`
  -- is related to `permute (canonical-↭ xs b)` by
  -- `canonical-go-pw-cong-permute`, transported through
  -- `canonical-go-pw-cong-target ... (λ _ → refl)`.
  ≈-Term-trans
    (≡⇒≈Term (trans
      (subst-Hom-cod-∘ (canonical-target-prep-plain x xs b)
        (id ⊗₁ permute (proj₂ (canonical-go (length xs) xs refl
                                  (residual (cons-fb b)))))
        id)
      (cong (_∘ id)
        (subst-Hom-cod-cons-⊗ {A = unflatten xs} {x = x}
          (canonical-go-pw-cong-target (length xs) xs refl
             (residual (cons-fb b)) b (λ _ → refl))
          (permute (proj₂ (canonical-go (length xs) xs refl
                              (residual (cons-fb b)))))))))
    (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl
                 (canonical-go-pw-cong-permute (length xs) xs refl
                    (residual (cons-fb b)) b (λ _ → refl)
                    (canonical-go-pw-cong-target (length xs) xs refl
                       (residual (cons-fb b)) b (λ _ → refl))))
              ≈-Term-refl)

------------------------------------------------------------------------
-- Headline bridge (prep case).
--
-- For a tail permutation `p : xs Perm.↭ xs` (restricted to square so
-- that `eval-↭ p` indexes `canonical-↭`), given an IH on `p` of the
-- form
--
--     permute p ≈Term subst-Hom-cod ep (permute (canonical-↭ xs (eval-↭ p)))
--
-- (where `ep : canonical-target xs (eval-↭ p) ≡ xs` is the list-equation
-- side of the bridge), we deliver the (x ∷ xs)-bridge for `Perm.prep x p`.
--
-- The general case `xs Perm.↭ ys` with `ys ≢ xs` requires `cast-bij`
-- through `↭-length` and is part of the full bridge induction; the
-- pure prep-step transformation is captured by
-- `permute-canonical-↭-cons-fb` above.

-- Auxiliary: UIP-like statement for subst-Hom-cod (with-K).
private
  subst-Hom-cod-uip
    : ∀ {A : ObjTerm} {as bs : List X} (e₁ e₂ : as ≡ bs)
        (t : HomTerm A (unflatten as))
    → subst-Hom-cod e₁ t ≈Term subst-Hom-cod e₂ t
  subst-Hom-cod-uip refl refl _ = ≈-Term-refl

  -- subst-Hom-cod commutes with id ⊗₁ _ on the cod-side codomain
  -- transport (cong (x ∷_) e).
  subst-Hom-cod-cons-⊗-≈
    : ∀ {A : ObjTerm} {x : X} {ys zs : List X} (e : ys ≡ zs)
        (t : HomTerm A (unflatten ys))
    → subst-Hom-cod {A = Var x ⊗₀ A} (cong (x ∷_) e) (id ⊗₁ t)
      ≈Term id {Var x} ⊗₁ subst-Hom-cod e t
  subst-Hom-cod-cons-⊗-≈ refl _ = ≈-Term-refl

permute-canonical-bridge-prep
  : ∀ {xs : List X} (x : X) (p : xs Perm.↭ xs)
      (ep : canonical-target xs (eval-↭ p) ≡ xs)
      (ih : permute p ≈Term subst-Hom-cod ep (permute (canonical-↭ xs (eval-↭ p))))
      (ex∷ : canonical-target (x ∷ xs) (cons-fb (eval-↭ p)) ≡ x ∷ xs)
  → permute (Perm.prep x p)
    ≈Term subst-Hom-cod ex∷ (permute (canonical-↭ (x ∷ xs) (cons-fb (eval-↭ p))))
-- We use the lemma that subst-Hom-cod transports respect ≈Term and
-- compose, so an `ep`-witnessed bridge for `p` lifts to a bridge for
-- `Perm.prep x p` through the structural prep step.
--
-- The proof generalises `ep` away by introducing a separate variable
-- for the lhs of the bridge target list, then pattern-matches on it.
permute-canonical-bridge-prep {xs = xs} x p ep ih ex∷ =
  go (canonical-target xs (eval-↭ p))
     (canonical-target (x ∷ xs) (cons-fb (eval-↭ p)))
     (canonical-↭ xs (eval-↭ p))
     (canonical-↭ (x ∷ xs) (cons-fb (eval-↭ p)))
     ep ex∷ ih
     (canonical-target-prep-plain x xs (eval-↭ p))
     (permute-canonical-↭-cons-fb x xs (eval-↭ p))
  where
  -- Fully generalised: every list-equation becomes a free variable;
  -- both `permute (canonical-↭ ...)` become free terms.  The
  -- pattern-matching on `ep := refl` and `cep := refl` then unifies
  -- the bridge.
  go : ∀ (ts : List X) (us : List X)
         (q : xs Perm.↭ ts)
         (q' : (x ∷ xs) Perm.↭ us)
         (ep : ts ≡ xs)
         (ex∷ : us ≡ x ∷ xs)
         (ih : permute p ≈Term subst-Hom-cod ep (permute q))
         (cep : us ≡ x ∷ ts)
         (cqp : subst-Hom-cod cep (permute q') ≈Term (id {Var x} ⊗₁ permute q) ∘ id)
       → permute (Perm.prep x p)
         ≈Term subst-Hom-cod ex∷ (permute q')
  go ts us q q' refl ex∷ ih refl cqp =
    -- ep := refl reduces ih to: permute p ≈Term permute q.
    -- cep := refl reduces cqp to: permute q' ≈Term (id ⊗₁ permute q) ∘ id.
    -- ex∷ : x ∷ ts ≡ x ∷ xs; by UIP since ts := xs (forced by refl-collapse
    -- of the implicit `ts` we passed `canonical-target xs (eval-↭ p)` which
    -- equals `xs` propositionally only — wait, `ep := refl` does NOT force
    -- ts := xs unless we read the type carefully.  Actually `ep : ts ≡ xs`
    -- after refl forces ts ≡ xs DEFINITIONALLY, so ts := xs.
    --
    -- Now ex∷ : x ∷ xs ≡ x ∷ xs (after ts := xs).  By UIP, equals refl.
    -- So `subst-Hom-cod ex∷ (permute q') = permute q'`.
    ≈-Term-trans
      (≈-Term-trans (⊗-resp-≈ ≈-Term-refl ih) (≈-Term-sym idʳ))
      (≈-Term-trans (≈-Term-sym cqp)
                    (subst-Hom-cod-uip refl ex∷ (permute q')))

------------------------------------------------------------------------
