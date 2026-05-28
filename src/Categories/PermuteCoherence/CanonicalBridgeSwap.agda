{-# OPTIONS --safe --with-K #-}

------------------------------------------------------------------------
-- Canonical bridge: SWAP case.
--
-- Companion module to `Categories.PermuteCoherence.CanonicalBridge`.
-- Carved out into its own module so it can be type-checked
-- independently (the combined file is too memory-heavy on small
-- sandboxes due to repeated normalisation of `canonical-go`).
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.CanonicalBridgeSwap
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
open import Categories.PermuteCoherence.CanonicalBridge d
  using ( subst-Hom-cod
        ; ≡⇒≈Term
        ; subst-Hom-cod-cons-⊗
        ; subst-Hom-cod-∘
        ; canonical-target-prep-plain
        ; canonical-go-pw-cong-permute
        ; permute-canonical-↭-cons-fb
        )

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product.Base using (Σ; _,_)

------------------------------------------------------------------------
-- Step 1: pointwise equation between
-- `residual (swap-fb _ ∘-fb cons-fb (cons-fb b))` and `cons-fb b`.
--
-- At i = 0F: `(swap-fb _ ∘-fb cons-fb (cons-fb b)) ⟨$⟩ʳ 1F` reduces
-- definitionally to 0F (transpose 0F 1F at 1F = 0F), and
-- `remove 0F ⋯` of that is `punchOut {1F} {0F} _ = 0F`.  `cons-fb b
-- ⟨$⟩ʳ 0F = 0F` too.
--
-- At i = suc i': similarly, both sides reduce to `suc (b ⟨$⟩ʳ i')`.
private
  residual-swap-fb-cons-fb-cons-fb-pw
    : ∀ {n} (b : FinBij n n)
    → ∀ i → residual (swap-fb n ∘-fb cons-fb (cons-fb b)) P.⟨$⟩ʳ i
            ≡ cons-fb b P.⟨$⟩ʳ i
  residual-swap-fb-cons-fb-cons-fb-pw {n} b 0F      = refl
  residual-swap-fb-cons-fb-cons-fb-pw {n} b (suc i) = refl

------------------------------------------------------------------------
-- Step 2: target-list lemma.

canonical-target-swap-plain
  : ∀ (x y : X) (xs : List X) (b : FinBij (length xs) (length xs))
  → canonical-target (x ∷ y ∷ xs) (swap-fb _ ∘-fb cons-fb (cons-fb b))
    ≡ y ∷ x ∷ canonical-target xs b
canonical-target-swap-plain x y xs b =
  cong (lookup (x ∷ y ∷ xs) (head-target (swap-fb _ ∘-fb cons-fb (cons-fb b))) ∷_)
    (trans
      (canonical-go-pw-cong-target (suc (length xs)) (x ∷ xs) refl
        (residual (swap-fb _ ∘-fb cons-fb (cons-fb b)))
        (cons-fb b)
        (residual-swap-fb-cons-fb-cons-fb-pw b))
      (canonical-target-prep-plain x xs b))

------------------------------------------------------------------------
-- Step 3: ≈Term structural transformation for the swap-fb composite.

permute-canonical-↭-swap-fb-cons-fb-cons-fb
  : ∀ (x y : X) (xs : List X) (b : FinBij (length xs) (length xs))
  → subst-Hom-cod (canonical-target-swap-plain x y xs b)
                  (permute (canonical-↭ (x ∷ y ∷ xs)
                              (swap-fb _ ∘-fb cons-fb (cons-fb b))))
    ≈Term
    (id {Var y} ⊗₁ (id {Var x} ⊗₁ permute (canonical-↭ xs b)))
      ∘ (((id {Var y} ⊗₁ id {Var x} ⊗₁ id) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ (id {Var x} ⊗₁ id {unflatten (y ∷ xs)}))
permute-canonical-↭-swap-fb-cons-fb-cons-fb x y xs b =
  ≈-Term-trans
    (≡⇒≈Term (trans
      (subst-Hom-cod-∘ (canonical-target-swap-plain x y xs b)
        (id {Var y} ⊗₁ permute (proj₂ (canonical-go (suc (length xs)) (x ∷ xs) refl
                                  (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))))
        (permute bubble))
      (cong (_∘ permute bubble)
        (subst-Hom-cod-cons-⊗ {A = unflatten (x ∷ xs)} {x = y}
          inner-e
          (permute (proj₂ (canonical-go (suc (length xs)) (x ∷ xs) refl
                              (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))))))))
    (≈-Term-trans
      (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl rec-≈) ≈-Term-refl)
      bridge)
  where
  inner-e : proj₁ (canonical-go (suc (length xs)) (x ∷ xs) refl
                     (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))
            ≡ x ∷ canonical-target xs b
  inner-e =
    trans
      (canonical-go-pw-cong-target (suc (length xs)) (x ∷ xs) refl
        (residual (swap-fb _ ∘-fb cons-fb (cons-fb b)))
        (cons-fb b)
        (residual-swap-fb-cons-fb-cons-fb-pw b))
      (canonical-target-prep-plain x xs b)

  bubble : (x ∷ y ∷ xs) Perm.↭ (y ∷ x ∷ xs)
  bubble =
    Perm.trans (Perm.prep x (Perm.refl {xs = y ∷ xs}))
               (Perm.swap x y (Perm.refl {xs = xs}))

  -- UIP-derived equation: subst by composite ≈Term subst by parts.
  subst-Hom-cod-uip
    : ∀ {A : ObjTerm} {as bs : List X} (e₁ e₂ : as ≡ bs)
        (t : HomTerm A (unflatten as))
    → subst-Hom-cod e₁ t ≈Term subst-Hom-cod e₂ t
  subst-Hom-cod-uip refl refl _ = ≈-Term-refl

  rec-≈ : subst-Hom-cod inner-e
            (permute (proj₂ (canonical-go (suc (length xs)) (x ∷ xs) refl
                              (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))))
          ≈Term
          (id {Var x} ⊗₁ permute (canonical-↭ xs b)) ∘ id
  rec-≈ =
    ≈-Term-trans step-A (permute-canonical-↭-cons-fb x xs b)
    where
    pw : ∀ i → residual (swap-fb _ ∘-fb cons-fb (cons-fb b)) P.⟨$⟩ʳ i
              ≡ cons-fb b P.⟨$⟩ʳ i
    pw = residual-swap-fb-cons-fb-cons-fb-pw b

    e-AB : proj₁ (canonical-go (suc (length xs)) (x ∷ xs) refl
                    (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))
            ≡ proj₁ (canonical-go (suc (length xs)) (x ∷ xs) refl (cons-fb b))
    e-AB = canonical-go-pw-cong-target (suc (length xs)) (x ∷ xs) refl
             (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))) (cons-fb b) pw

    step-A
      : subst-Hom-cod inner-e
          (permute (proj₂ (canonical-go (suc (length xs)) (x ∷ xs) refl
                            (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))))
        ≈Term
        subst-Hom-cod (canonical-target-prep-plain x xs b)
          (permute (canonical-↭ (x ∷ xs) (cons-fb b)))
    step-A =
      go inner-e e-AB (canonical-target-prep-plain x xs b)
         (canonical-go-pw-cong-permute (suc (length xs)) (x ∷ xs) refl
            (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))) (cons-fb b) pw e-AB)
      where
      go : (e : proj₁ (canonical-go (suc (length xs)) (x ∷ xs) refl
                        (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))
                ≡ x ∷ canonical-target xs b)
             (e₁ : proj₁ (canonical-go (suc (length xs)) (x ∷ xs) refl
                            (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))
                   ≡ proj₁ (canonical-go (suc (length xs)) (x ∷ xs) refl (cons-fb b)))
             (e₂ : proj₁ (canonical-go (suc (length xs)) (x ∷ xs) refl (cons-fb b))
                   ≡ x ∷ canonical-target xs b)
             (≈A : subst-Hom-cod e₁
                     (permute (proj₂ (canonical-go (suc (length xs)) (x ∷ xs) refl
                                       (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))))
                   ≈Term permute (canonical-↭ (x ∷ xs) (cons-fb b)))
           → subst-Hom-cod e
               (permute (proj₂ (canonical-go (suc (length xs)) (x ∷ xs) refl
                                 (residual (swap-fb _ ∘-fb cons-fb (cons-fb b))))))
             ≈Term subst-Hom-cod e₂ (permute (canonical-↭ (x ∷ xs) (cons-fb b)))
      go e refl refl ≈A =
        ≈-Term-trans (subst-Hom-cod-uip e refl _) ≈A

  bridge : (id {Var y} ⊗₁ ((id {Var x} ⊗₁ permute (canonical-↭ xs b)) ∘ id))
              ∘ permute bubble
           ≈Term
           (id {Var y} ⊗₁ (id {Var x} ⊗₁ permute (canonical-↭ xs b)))
             ∘ (((id {Var y} ⊗₁ id {Var x} ⊗₁ id) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                ∘ (id {Var x} ⊗₁ id {unflatten (y ∷ xs)}))
  bridge = ∘-resp-≈ (⊗-resp-≈ ≈-Term-refl idʳ) ≈-Term-refl

------------------------------------------------------------------------
-- Headline bridge (swap case).

private
  subst-Hom-cod-uip
    : ∀ {A : ObjTerm} {as bs : List X} (e₁ e₂ : as ≡ bs)
        (t : HomTerm A (unflatten as))
    → subst-Hom-cod e₁ t ≈Term subst-Hom-cod e₂ t
  subst-Hom-cod-uip refl refl _ = ≈-Term-refl

permute-canonical-bridge-swap
  : ∀ {xs : List X} (x y : X) (p : xs Perm.↭ xs)
      (ep : canonical-target xs (eval-↭ p) ≡ xs)
      (ih : permute p ≈Term subst-Hom-cod ep (permute (canonical-↭ xs (eval-↭ p))))
      (ex∷ : canonical-target (x ∷ y ∷ xs)
              (swap-fb _ ∘-fb cons-fb (cons-fb (eval-↭ p))) ≡ y ∷ x ∷ xs)
  → permute (Perm.swap x y p)
    ≈Term subst-Hom-cod ex∷
            (permute (canonical-↭ (x ∷ y ∷ xs)
                        (swap-fb _ ∘-fb cons-fb (cons-fb (eval-↭ p)))))
permute-canonical-bridge-swap {xs = xs} x y p ep ih ex∷ =
  go (canonical-target xs (eval-↭ p))
     (canonical-target (x ∷ y ∷ xs)
       (swap-fb _ ∘-fb cons-fb (cons-fb (eval-↭ p))))
     (canonical-↭ xs (eval-↭ p))
     (canonical-↭ (x ∷ y ∷ xs)
       (swap-fb _ ∘-fb cons-fb (cons-fb (eval-↭ p))))
     ep ex∷ ih
     (canonical-target-swap-plain x y xs (eval-↭ p))
     (permute-canonical-↭-swap-fb-cons-fb-cons-fb x y xs (eval-↭ p))
  where
  go : ∀ (ts : List X) (us : List X)
         (q : xs Perm.↭ ts)
         (q' : (x ∷ y ∷ xs) Perm.↭ us)
         (ep : ts ≡ xs)
         (ex∷ : us ≡ y ∷ x ∷ xs)
         (ih : permute p ≈Term subst-Hom-cod ep (permute q))
         (cep : us ≡ y ∷ x ∷ ts)
         (cqp : subst-Hom-cod cep (permute q')
                 ≈Term
                 (id {Var y} ⊗₁ (id {Var x} ⊗₁ permute q))
                   ∘ (((id {Var y} ⊗₁ id {Var x} ⊗₁ id) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
                      ∘ (id {Var x} ⊗₁ id {unflatten (y ∷ xs)})))
       → permute (Perm.swap x y p)
         ≈Term subst-Hom-cod ex∷ (permute q')
  go ts us q q' refl ex∷ ih refl cqp =
    ≈-Term-trans
      lhs-≈
      (≈-Term-trans (≈-Term-sym cqp)
                    (subst-Hom-cod-uip refl ex∷ (permute q')))
    where
    lhs-≈
      : permute (Perm.swap x y p)
        ≈Term
        (id {Var y} ⊗₁ (id {Var x} ⊗₁ permute q))
          ∘ (((id {Var y} ⊗₁ id {Var x} ⊗₁ id) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
             ∘ (id {Var x} ⊗₁ id {unflatten (y ∷ xs)}))
    lhs-≈ =
      ≈-Term-trans
        (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl ih)) ≈-Term-refl)
        struct-≈
      where
      struct-≈
        : (id {Var y} ⊗₁ (id {Var x} ⊗₁ permute q)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
          ≈Term
          (id {Var y} ⊗₁ (id {Var x} ⊗₁ permute q))
            ∘ (((id {Var y} ⊗₁ id {Var x} ⊗₁ id) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
               ∘ (id {Var x} ⊗₁ id {unflatten (y ∷ xs)}))
      struct-≈ =
        ∘-resp-≈ ≈-Term-refl
          (≈-Term-trans
            (≈-Term-trans
              (≈-Term-sym idˡ)
              (∘-resp-≈ id-≈-id⊗id⊗id ≈-Term-refl))
            (≈-Term-trans
              (≈-Term-sym idʳ)
              (∘-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id))))
        where
        id-≈-id⊗id⊗id : id {Var y ⊗₀ Var x ⊗₀ unflatten xs}
                        ≈Term id {Var y} ⊗₁ id {Var x} ⊗₁ id
        id-≈-id⊗id⊗id =
          ≈-Term-trans (≈-Term-sym id⊗id≈id)
                       (⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id))
