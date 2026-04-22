{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Congruence rules for `hComposeP` (the pruned `hCompose`, Option A).
--
-- Parallel to `Hypergraph.Congruence.hCompose-resp-≅ᴴ`. The existing
-- Congruence proof operates on the unpruned `hCompose`; this module ports
-- the structural piece to the pruned variant so a future Soundness
-- rewrite can use `hComposeP` in its `∘-resp-≈` case and still get a
-- congruence lemma out.
--
-- CURRENT STATUS: vertex + edge bijections with left/right inverse
-- proofs. Full `hComposeP-resp-≅ᴴ` record remaining:
--
--   * φ-lab-P (vertex label preservation): inj₁ case identical to
--     Congruence.φ-lab-C; inj₂ case needs
--       vlab-P₂ (raise G₂.nV (pruneK jK))
--       = K₂.vlab (lookup (nonMem K₂.dom) (pruneK jK))
--       ≡? K₁.vlab (lookup (nonMem K₁.dom) jK)
--     which reduces via `subst` on IK.φ-dom and `lookup-pruneMap`
--     (+ IK.φ-lab).
--
--   * ψ-ein-P / ψ-eout-P (edge endpoint preservation): for the inj₂
--     (K-side) branch, use `map-via-remapP` lifted along pruneK.
--
--   * φ-dom-P / φ-cod-P (boundary preservation): map injL-style for
--     dom (G-side only), map-through-pruneMap for cod.
--
--   * atom-ein-P / atom-eout-P (atom-level equality for ≅ᴴ's
--     derived fields).
--
--   * ψ-elab-P (the big six-step subst₂ chain): longest piece, same
--     shape as the unpruned `ψ-elab-C`, with extra subst through
--     pruneK in the inj₂ case.
--
-- Once assembled, `hComposeP-resp-≅ᴴ : G₁ ≅ᴴ G₂ → K₁ ≅ᴴ K₂
--                                    → hComposeP G₁ K₁ ≅ᴴ hComposeP G₂ K₂`
-- discharges `∘-resp-≈` in a Soundness rewrite using `hComposeP`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.CongruenceP (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.Prune
  using ( count-non; nonMem; pruneMap; pruneMap⁻¹
        ; pruneMap-left-inverse; pruneMap-right-inverse)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP)

open import Data.Fin using (Fin; inject+; raise; splitAt)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-raise;
                                        splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)

--------------------------------------------------------------------------------
-- Vertex bijection for the pruned composite, parametric in two hypergraph
-- isos iG : G₁ ≅ᴴ G₂, iK : K₁ ≅ᴴ K₂.

module _
    {As Bs Cs : List X}
    {G₁ G₂ : Hypergraph FlatGen As Bs}
    {K₁ K₂ : Hypergraph FlatGen Bs Cs}
    (iG : G₁ ≅ᴴ G₂) (iK : K₁ ≅ᴴ K₂) where

  private
    module G₁ = Hypergraph G₁
    module G₂ = Hypergraph G₂
    module K₁ = Hypergraph K₁
    module K₂ = Hypergraph K₂
    module IG = _≅ᴴ_ iG
    module IK = _≅ᴴ_ iK

  -- IK.φ is injective, derivable from IK.φ-left.
  private
    IK-φ-inj : ∀ {x y} → IK.φ x ≡ IK.φ y → x ≡ y
    IK-φ-inj {x} {y} eq =
      trans (sym (IK.φ-left x)) (trans (cong IK.φ⁻¹ eq) (IK.φ-left y))

  -- Pruned K-side bijection: `Fin (count-non K₁.dom) → Fin (count-non K₂.dom)`.
  -- Routes `jK` through `pruneMap` on IK.φ, then `subst`s across
  -- `K₂.dom ≡ map IK.φ K₁.dom`.
  pruneK : Fin (count-non K₁.dom) → Fin (count-non K₂.dom)
  pruneK jK = subst (λ ys → Fin (count-non ys)) (sym IK.φ-dom)
                    (pruneMap IK.φ IK-φ-inj K₁.dom jK)

  pruneK⁻¹ : Fin (count-non K₂.dom) → Fin (count-non K₁.dom)
  pruneK⁻¹ kK =
    pruneMap⁻¹ IK.φ IK.φ⁻¹ IK.φ-left IK.φ-rght K₁.dom
               (subst (λ ys → Fin (count-non ys)) IK.φ-dom kK)

  -- Vertex bijection of the composites.
  φ-P : Fin (G₁.nV + count-non K₁.dom) → Fin (G₂.nV + count-non K₂.dom)
  φ-P i = [ (λ iG → inject+ (count-non K₂.dom) (IG.φ iG))
          , (λ iK → raise G₂.nV (pruneK iK))
          ]′ (splitAt G₁.nV i)

  φ⁻¹-P : Fin (G₂.nV + count-non K₂.dom) → Fin (G₁.nV + count-non K₁.dom)
  φ⁻¹-P j = [ (λ jG → inject+ (count-non K₁.dom) (IG.φ⁻¹ jG))
            , (λ jK → raise G₁.nV (pruneK⁻¹ jK))
            ]′ (splitAt G₂.nV j)

  -- Left inverse of the K-side pruned bijection.
  -- `pruneK⁻¹ (pruneK jK) = pruneMap⁻¹ ... (subst ... (subst ... (pruneMap ... jK)))`
  -- and the two substs cancel via `subst-sym-subst`.
  private
    subst-sym-subst : ∀ {A : Set} {B : A → Set} {a₁ a₂ : A}
                    → (eq : a₁ ≡ a₂) (x : B a₁)
                    → subst B (sym eq) (subst B eq x) ≡ x
    subst-sym-subst refl _ = refl

    subst-subst-sym : ∀ {A : Set} {B : A → Set} {a₁ a₂ : A}
                    → (eq : a₁ ≡ a₂) (x : B a₂)
                    → subst B eq (subst B (sym eq) x) ≡ x
    subst-subst-sym refl _ = refl

  pruneK-left : ∀ jK → pruneK⁻¹ (pruneK jK) ≡ jK
  pruneK-left jK =
    trans (cong (pruneMap⁻¹ IK.φ IK.φ⁻¹ IK.φ-left IK.φ-rght K₁.dom)
                (subst-subst-sym IK.φ-dom
                                  (pruneMap IK.φ IK-φ-inj K₁.dom jK)))
          (pruneMap-left-inverse IK.φ IK.φ⁻¹ IK.φ-left IK.φ-rght K₁.dom jK)

  pruneK-right : ∀ kK → pruneK (pruneK⁻¹ kK) ≡ kK
  pruneK-right kK =
    trans (cong (subst (λ ys → Fin (count-non ys)) (sym IK.φ-dom))
                (pruneMap-right-inverse IK.φ IK.φ⁻¹ IK.φ-left IK.φ-rght
                                         K₁.dom _))
          (subst-sym-subst IK.φ-dom kK)

  -- φ-P / φ⁻¹-P roundtrips. Same structure as the unpruned Congruence,
  -- split on `splitAt G₁.nV i` and use `splitAt-inject+` / `splitAt-raise`
  -- to collapse.
  φ-left-P : ∀ i → φ⁻¹-P (φ-P i) ≡ i
  φ-left-P i with splitAt G₁.nV i in eq
  ... | inj₁ iG rewrite splitAt-inject+ G₂.nV (count-non K₂.dom) (IG.φ iG)
                      | IG.φ-left iG
                    = splitAt⁻¹-↑ˡ eq
  ... | inj₂ jK rewrite splitAt-raise G₂.nV (count-non K₂.dom) (pruneK jK)
                      | pruneK-left jK
                    = splitAt⁻¹-↑ʳ eq

  φ-rght-P : ∀ j → φ-P (φ⁻¹-P j) ≡ j
  φ-rght-P j with splitAt G₂.nV j in eq
  ... | inj₁ jG rewrite splitAt-inject+ G₁.nV (count-non K₁.dom) (IG.φ⁻¹ jG)
                      | IG.φ-rght jG
                    = splitAt⁻¹-↑ˡ eq
  ... | inj₂ kK rewrite splitAt-raise G₁.nV (count-non K₁.dom) (pruneK⁻¹ kK)
                      | pruneK-right kK
                    = splitAt⁻¹-↑ʳ eq

  --------------------------------------------------------------------------------
  -- Edge bijection. Identical structure to the unpruned
  -- `Congruence.hCompose-resp-≅ᴴ`, since `hComposeP` has the same edge
  -- count (G.nE + K.nE) as `hCompose` — pruning only affects vertices.

  ψ-P : Fin (G₁.nE + K₁.nE) → Fin (G₂.nE + K₂.nE)
  ψ-P e = [ (λ eG → inject+ K₂.nE (IG.ψ eG))
          , (λ eK → raise G₂.nE (IK.ψ eK))
          ]′ (splitAt G₁.nE e)

  ψ⁻¹-P : Fin (G₂.nE + K₂.nE) → Fin (G₁.nE + K₁.nE)
  ψ⁻¹-P e = [ (λ eG → inject+ K₁.nE (IG.ψ⁻¹ eG))
            , (λ eK → raise G₁.nE (IK.ψ⁻¹ eK))
            ]′ (splitAt G₂.nE e)

  ψ-left-P : ∀ e → ψ⁻¹-P (ψ-P e) ≡ e
  ψ-left-P e with splitAt G₁.nE e in eq
  ... | inj₁ eG rewrite splitAt-inject+ G₂.nE K₂.nE (IG.ψ eG)
                      | IG.ψ-left eG
                    = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eK rewrite splitAt-raise G₂.nE K₂.nE (IK.ψ eK)
                      | IK.ψ-left eK
                    = splitAt⁻¹-↑ʳ eq

  ψ-rght-P : ∀ e → ψ-P (ψ⁻¹-P e) ≡ e
  ψ-rght-P e with splitAt G₂.nE e in eq
  ... | inj₁ eG rewrite splitAt-inject+ G₁.nE K₁.nE (IG.ψ⁻¹ eG)
                      | IG.ψ-rght eG
                    = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eK rewrite splitAt-raise G₁.nE K₁.nE (IK.ψ⁻¹ eK)
                      | IK.ψ-rght eK
                    = splitAt⁻¹-↑ʳ eq
