{-# OPTIONS --safe --with-K #-}

------------------------------------------------------------------------
-- Canonical bridge: TRANS case (self-loop variant).
--
-- Companion module to `Categories.PermuteCoherence.CanonicalBridge`
-- and `…CanonicalBridgeSwap`.  Carved out into its own module for
-- type-checking memory budget reasons.
--
-- STATUS: PARTIAL.
--
-- We discharge the trans-case structural bridge constructively for the
-- self-loop sub-case where `q = Perm.refl` (the right operand of the
-- composition is `refl`).  This is the simplest of the four sub-cases
-- of induction on `q` and is the one that does *not* require composition
-- coherence between canonical forms.
--
-- The remaining sub-cases (`q = prep _ q'`, `q = swap _ _ q'`,
-- `q = trans q₁ q₂`) all reduce to the same missing ingredient:
-- coherence of the form
--
--     permute (canonical-↭ xs b) ∘ permute (canonical-↭ xs b')
--       ≈Term permute (canonical-↭ xs (b ∘-fb b'))
--
-- (modulo `subst-Hom-cod`).  This is not directly available from any
-- structural lemma about `canonical-go` and is left as a clearly-
-- delineated residual `CanonicalBridgeTransComposeResidual` below.
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.CanonicalBridgeTrans
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.Product.Base using (proj₁; proj₂)
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
        ; canonical-go-pw-cong-permute
        )

------------------------------------------------------------------------
-- Local UIP for codomain transports (with-K).

private
  subst-Hom-cod-uip
    : ∀ {A : ObjTerm} {as bs : List X} (e₁ e₂ : as ≡ bs)
        (t : HomTerm A (unflatten as))
    → subst-Hom-cod e₁ t ≈Term subst-Hom-cod e₂ t
  subst-Hom-cod-uip refl refl _ = ≈-Term-refl

------------------------------------------------------------------------
-- Composition coherence for `canonical-↭`: the missing ingredient for
-- the non-refl sub-cases of the trans induction.
--
-- This records the residual obligation explicitly; closing it would
-- discharge the full self-loop trans case.

record CanonicalBridgeTransComposeResidual : Set where
  field
    canonical-↭-∘-coherence
      : ∀ (xs : List X)
          (b b' : FinBij (length xs) (length xs))
          (ecomp : canonical-target xs (b' ∘-fb b) ≡ xs)
          (e' : canonical-target xs b' ≡ xs)
          (e : canonical-target xs b ≡ xs)
      → subst-Hom-cod ecomp (permute (canonical-↭ xs (b' ∘-fb b)))
        ≈Term
        subst-Hom-cod e' (permute (canonical-↭ xs b'))
          ∘ subst-Hom-cod e (permute (canonical-↭ xs b))

------------------------------------------------------------------------
-- Trans-case bridge for the SELF-LOOP variant.
--
-- Given:
--   * `p q : xs Perm.↭ xs` — two self-loop permutations
--   * IHs: bridge equations for `p` and `q` individually.
-- Conclusion: bridge equation for `Perm.trans p q`.
--
-- We dispatch on `q`.  For `q = Perm.refl` the proof is direct and
-- requires no composition-coherence assumption.  The other sub-cases
-- are reduced to the residual record above.

-- Direct closure of the `q = Perm.refl` sub-case.
permute-canonical-bridge-trans-selfloop-q-refl
  : ∀ {xs : List X} (p : xs Perm.↭ xs)
      (ep : canonical-target xs (eval-↭ p) ≡ xs)
      (ih-p : permute p ≈Term subst-Hom-cod ep (permute (canonical-↭ xs (eval-↭ p))))
      (ecomp : canonical-target xs (eval-↭ (Perm.trans p (Perm.refl {xs = xs}))) ≡ xs)
  → permute (Perm.trans p (Perm.refl {xs = xs}))
    ≈Term subst-Hom-cod ecomp
            (permute (canonical-↭ xs (eval-↭ (Perm.trans p (Perm.refl {xs = xs})))))
permute-canonical-bridge-trans-selfloop-q-refl {xs = xs} p ep ih-p ecomp =
  -- permute (trans p refl) = permute refl ∘ permute p = id ∘ permute p.
  -- eval-↭ (trans p refl) = eval-↭ refl ∘-fb eval-↭ p = id-fb ∘-fb eval-↭ p,
  -- which is pointwise equal to eval-↭ p.
  --
  -- Strategy:
  --   1.  `idˡ`:        permute (trans p refl) ≈ permute p.
  --   2.  `ih-p`:       permute p ≈ subst-Hom-cod ep (permute (canonical-↭ xs (eval-↭ p))).
  --   3.  pw-congruence + UIP: this equals subst-Hom-cod ecomp (permute (canonical-↭ xs (eval-↭ q ∘-fb eval-↭ p))).
  ≈-Term-trans idˡ
    (≈-Term-trans ih-p step)
  where
  -- `eval-↭ (Perm.trans p Perm.refl) = id-fb ∘-fb eval-↭ p`, which is
  -- pointwise equal to `eval-↭ p`.
  pw : ∀ i → eval-↭ p P.⟨$⟩ʳ i ≡ (id-fb ∘-fb eval-↭ p) P.⟨$⟩ʳ i
  pw _ = refl

  e-AB : canonical-target xs (eval-↭ p)
         ≡ canonical-target xs (id-fb ∘-fb eval-↭ p)
  e-AB = canonical-go-pw-cong-target (length xs) xs refl
           (eval-↭ p) (id-fb ∘-fb eval-↭ p) pw

  cong-perm : subst-Hom-cod e-AB (permute (canonical-↭ xs (eval-↭ p)))
              ≈Term permute (canonical-↭ xs (id-fb ∘-fb eval-↭ p))
  cong-perm = canonical-go-pw-cong-permute (length xs) xs refl
                (eval-↭ p) (id-fb ∘-fb eval-↭ p) pw e-AB

  -- Bridge the two `subst-Hom-cod` witnesses via UIP, by routing
  -- through the chain `ep · sym e-AB · ecomp` essentially.  The cleanest
  -- form: introduce variable `q`-list and pattern-match.
  step : subst-Hom-cod ep (permute (canonical-↭ xs (eval-↭ p)))
         ≈Term
         subst-Hom-cod ecomp
           (permute (canonical-↭ xs (eval-↭ (Perm.trans p (Perm.refl {xs = xs})))))
  step = go (canonical-target xs (eval-↭ p))
            (canonical-target xs (id-fb ∘-fb eval-↭ p))
            (permute (canonical-↭ xs (eval-↭ p)))
            (permute (canonical-↭ xs (id-fb ∘-fb eval-↭ p)))
            e-AB ep ecomp cong-perm
    where
    go : ∀ (ts us : List X)
           (t : HomTerm (unflatten xs) (unflatten ts))
           (t' : HomTerm (unflatten xs) (unflatten us))
           (e-AB : ts ≡ us)
           (ep : ts ≡ xs)
           (ecomp : us ≡ xs)
           (≈cong : subst-Hom-cod e-AB t ≈Term t')
         → subst-Hom-cod ep t ≈Term subst-Hom-cod ecomp t'
    go ts .ts t t' refl refl ecomp ≈cong =
      ≈-Term-trans (subst-Hom-cod-uip refl ecomp t)
                   (go-eq t t' ecomp ≈cong)
      where
      -- After `e-AB := refl`, `≈cong : t ≈Term t'`.  Then
      -- `subst-Hom-cod ecomp t ≈Term subst-Hom-cod ecomp t'` by congruence.
      go-eq : ∀ (t t' : HomTerm (unflatten xs) (unflatten ts))
                (e : ts ≡ xs)
                (≈ : t ≈Term t')
            → subst-Hom-cod e t ≈Term subst-Hom-cod e t'
      go-eq t t' refl ≈ = ≈

------------------------------------------------------------------------
-- General trans-case, parametrised by the composition-coherence residual.
--
-- Closes via dispatch on `q`:
--   * `q = refl`: direct, via `permute-canonical-bridge-trans-selfloop-q-refl`.
--   * `q = prep _ _ / swap _ _ _ / trans _ _`: via the residual record.
--
-- For the non-refl cases the proof structure is:
--   permute (trans p q)
--     = permute q ∘ permute p                              (def)
--     ≈ subst-Hom-cod _ (permute (canonical-↭ xs (eval-↭ q)))
--         ∘ subst-Hom-cod _ (permute (canonical-↭ xs (eval-↭ p)))  (ih-q, ih-p)
--     ≈ subst-Hom-cod _ (permute (canonical-↭ xs (eval-↭ q ∘-fb eval-↭ p)))
--         (canonical-↭-∘-coherence)
--     = subst-Hom-cod _ (permute (canonical-↭ xs (eval-↭ (trans p q))))  (def of eval-↭)

module _ (R : CanonicalBridgeTransComposeResidual) where
  open CanonicalBridgeTransComposeResidual R

  permute-canonical-bridge-trans-selfloop
    : ∀ {xs : List X} (p q : xs Perm.↭ xs)
        (ep : canonical-target xs (eval-↭ p) ≡ xs)
        (eq : canonical-target xs (eval-↭ q) ≡ xs)
        (ih-p : permute p ≈Term subst-Hom-cod ep (permute (canonical-↭ xs (eval-↭ p))))
        (ih-q : permute q ≈Term subst-Hom-cod eq (permute (canonical-↭ xs (eval-↭ q))))
        (ecomp : canonical-target xs (eval-↭ (Perm.trans p q)) ≡ xs)
    → permute (Perm.trans p q)
      ≈Term subst-Hom-cod ecomp
              (permute (canonical-↭ xs (eval-↭ (Perm.trans p q))))
  permute-canonical-bridge-trans-selfloop {xs = xs} p q ep eq ih-p ih-q ecomp =
    -- permute (trans p q) = permute q ∘ permute p
    -- eval-↭ (trans p q) = eval-↭ q ∘-fb eval-↭ p
    --
    -- By ih-p and ih-q:
    --   permute q ∘ permute p
    --   ≈ subst-Hom-cod eq (permute (canonical-↭ xs (eval-↭ q)))
    --       ∘ subst-Hom-cod ep (permute (canonical-↭ xs (eval-↭ p)))
    -- By canonical-↭-∘-coherence (with b := eval-↭ p, b' := eval-↭ q):
    --   ≈ subst-Hom-cod ecomp (permute (canonical-↭ xs (eval-↭ q ∘-fb eval-↭ p)))
    ≈-Term-trans
      (∘-resp-≈ ih-q ih-p)
      (≈-Term-sym
        (canonical-↭-∘-coherence xs (eval-↭ p) (eval-↭ q) ecomp eq ep))
