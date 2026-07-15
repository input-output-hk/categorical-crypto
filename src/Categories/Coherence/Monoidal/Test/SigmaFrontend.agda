{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Tests for the PUBLIC symmetric solver front-end
-- (`Categories.Coherence.Monoidal.Symmetric`).  Every test states its goal in
-- an ARBITRARY symmetric monoidal category `C`'s own vocabulary (σ landing on
-- the target's braiding) and discharges it with `solveMorσ!` (or the
-- `rewriteMorσ!` family), over a three-generator signature
-- (μ : A⊗A→A, s : A→A, t : B→B).  Machine-checked:
--
--   * `Braiding`   — σ∘σ≈id, as a one-liner and DEEP inside a ⊗/α context.
--   * `Naturality` — σ-naturality through box generators; the headline
--     `σ ∘ (s ⊗ t) ≈ (t ⊗ s) ∘ σ` needs TWO machine-fired slides (one per
--     image block), the single-sided variants isolate each slide.
--   * `Mixed`      — σ moves interleaved with coherence/functoriality.
--   * `Rewrite`    — the shared rewriting layer (`rewriteMorσAuto!`).
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Test.SigmaFrontend where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; zero; suc; [_]; [_,_]; _∷_; [])

open import Data.Fin
open import Data.Vec using (_∷_; [])

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Frontend.Core
open import Categories.Coherence.Monoidal.Frontend.Sigma
open import Categories.Coherence.Monoidal.Sigma
import Categories.Coherence.Monoidal as Coh

------------------------------------------------------------------------
-- The symmetric-morphism tests: over an arbitrary symmetric monoidal `C`
-- with two atoms `A , B` and a three-generator signature:
--
--   0 → μ : A ⊗ A → A     (multi-wire input)
--   1 → s : A → A          (endo on A)
--   2 → t : B → B          (endo on B)

module Morphism {o ℓ e : Level}
                (C : MonoidalCategory o ℓ e)
                (Sym : Symmetric (C .MonoidalCategory.monoidal)) where

  private
    module MC = MonoidalCategory C
    module Sy = Symmetric Sym
  open MC using (_⊗₀_; _⊗₁_; _∘_; id; unit; unitorʳ; associator)

  module _
    (A B : MC.Obj)
    (μᴹ : MC.U [ A ⊗₀ A , A ])
    (sᴹ : MC.U [ A , A ])
    (tᴹ : MC.U [ B , B ])
    -- a rule hypothesis for the shared rewriting layer.
    (invσ : MC.U [ sᴹ ∘ sᴹ ≈ id ])
    where

    module O = FreeMonoidalHelper Symm (Fin 2)
    open O renaming (Var to V) using ()
    open Coh.Symmetric C Sym (A ∷ B ∷ [])
         ( ((V zero O.⊗₀ V zero , V zero) , μᴹ)   -- gen 0 : A⊗A → A ↦ μ
         ∷ ((V zero , V zero)             , sᴹ)   -- gen 1 : A → A ↦ s
         ∷ ((V (suc zero) , V (suc zero)) , tᴹ)   -- gen 2 : B → B ↦ t
         ∷ [] )

    private
      μ' = gen zero
      s' = gen (suc zero)
      t' = gen (suc (suc zero))
      -- σ pinned at atom pairs (the object interpretation is not injective,
      -- so the implicits must be supplied term-side).
      a : O.ObjTerm
      a = O.Var zero
      b : O.ObjTerm
      b = O.Var (suc zero)

    ----------------------------------------------------------------------
    -- Braiding involution: σ∘σ≈id, as a one-liner and deep in context.

    module Braiding where

      test-σσ : MC.U [ Sy.braiding.⇒.η (B , A) ∘ Sy.braiding.⇒.η (A , B) ≈ id ]
      test-σσ = solveMorσ! (S.σ S.∘ S.σ) (S.id {a O.⊗₀ b})

      -- the inverse pair fires DEEP: inside a ⊗-context, with α-recasts around.
      test-σσ-deep
        : MC.U
            [ associator.from ∘ ((Sy.braiding.⇒.η (B , A) ∘ Sy.braiding.⇒.η (A , B)) ⊗₁ id)
            ≈ associator.from ]
      test-σσ-deep = solveMorσ! (S.α⇒ S.∘ ((S.σ S.∘ S.σ) S.⊗₁ S.id)) (S.α⇒ {a} {b} {a})

    ----------------------------------------------------------------------
    -- σ-naturality through box generators: the SLIDES fire.

    module Naturality where

      -- the headline: TWO machine-fired slides (s through the a-image block,
      -- t through the b-image block).
      test-σ-nat : MC.U [ Sy.braiding.⇒.η (A , B) ∘ (sᴹ ⊗₁ tᴹ) ≈ (tᴹ ⊗₁ sᴹ) ∘ Sy.braiding.⇒.η (A , B) ]
      test-σ-nat = solveMorσ! (S.σ S.∘ (s' S.⊗₁ t')) ((t' S.⊗₁ s') S.∘ S.σ)

      -- the single-sided variants (one slide each).
      test-σ-nat-left : MC.U [ Sy.braiding.⇒.η (A , B) ∘ (sᴹ ⊗₁ id) ≈ (id ⊗₁ sᴹ) ∘ Sy.braiding.⇒.η (A , B) ]
      test-σ-nat-left = solveMorσ! (S.σ S.∘ (s' S.⊗₁ S.id)) ((S.id S.⊗₁ s') S.∘ S.σ {a} {b})

      test-σ-nat-right : MC.U [ Sy.braiding.⇒.η (A , B) ∘ (id ⊗₁ tᴹ) ≈ (tᴹ ⊗₁ id) ∘ Sy.braiding.⇒.η (A , B) ]
      test-σ-nat-right = solveMorσ! (S.σ S.∘ (S.id S.⊗₁ t')) ((t' S.⊗₁ S.id) S.∘ S.σ {a})

      -- σ-conjugation: slides + σσ-cancellation combined.
      test-σ-conj : MC.U [ Sy.braiding.⇒.η (A , B) ∘ (sᴹ ⊗₁ tᴹ) ∘ Sy.braiding.⇒.η (B , A) ≈ tᴹ ⊗₁ sᴹ ]
      test-σ-conj = solveMorσ! (S.σ S.∘ (s' S.⊗₁ t') S.∘ S.σ) (t' S.⊗₁ s')

      -- a MULTI-WIRE box slides as one block: μ : A⊗A → A through σ.
      test-σ-nat-μ : MC.U [ Sy.braiding.⇒.η (A , B) ∘ (μᴹ ⊗₁ id) ≈ (id ⊗₁ μᴹ) ∘ Sy.braiding.⇒.η (A ⊗₀ A , B) ]
      test-σ-nat-μ = solveMorσ! (S.σ S.∘ (μ' S.⊗₁ S.id)) ((S.id S.⊗₁ μ') S.∘ S.σ {a O.⊗₀ a} {b})

    ----------------------------------------------------------------------
    -- Mixed goals: σ interleaved with the Mon repertoire.

    module Mixed where

      -- cancellation under functoriality: σσ-conjugated tensor of composites.
      test-mix-∘
        : MC.U
            [ (Sy.braiding.⇒.η (B , A) ∘ Sy.braiding.⇒.η (A , B)) ∘ ((sᴹ ∘ sᴹ) ⊗₁ tᴹ)
            ≈ (sᴹ ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ]
      test-mix-∘ = solveMorσ! ((S.σ S.∘ S.σ) S.∘ ((s' S.∘ s') S.⊗₁ t')) ((s' S.⊗₁ t') S.∘ (s' S.⊗₁ S.id))

      -- σ against the unitors: the inverse σ-pair at (unit, A) cancels under
      -- a right unitor.
      test-mix-unit
        : MC.U
            [ unitorʳ.from ∘ Sy.braiding.⇒.η (unit , A) ∘ Sy.braiding.⇒.η (A , unit)
            ≈ unitorʳ.from ]
      test-mix-unit = solveMorσ! (S.ρ⇒ S.∘ S.σ S.∘ S.σ {a}) (S.ρ⇒)

    ----------------------------------------------------------------------
    -- The shared rewriting layer in the σ front-end: the rule `sᴹ ∘ sᴹ ≈ id`
    -- fires (auto-positioned) in the right factor of a tensor, collapsing the
    -- composite to `id` in context.

    module Rewrite where

      test-rwσ-cancel : MC.U [ tᴹ ⊗₁ (sᴹ ∘ sᴹ) ≈ tᴹ ⊗₁ id ]
      test-rwσ-cancel = rewriteMorσAuto! (t' S.⊗₁ (s' S.∘ s')) (t' S.⊗₁ S.id) (s' S.∘ s') (S.id) invσ

------------------------------------------------------------------------
-- Sound rejection

data Ty : Set where ⋆ : Ty

instance
  DecEq-Ty : DecEq Ty
  DecEq-Ty .DecEq._≟_ ⋆ ⋆ = yes refl

open FreeMonoidalHelper Symm Ty using () renaming (ObjTerm to ObjTermᴵ; Var to Varᴵ)

arityT : Fin 1 → ObjTermᴵ × ObjTermᴵ
arityT zero = Varᴵ ⋆ , Varᴵ ⋆

private module FS = FinSig Symm {Ty} arityT
open FS renaming (gen to genᵗ)

open FrontendS {Ty} GenS
open Decide rankS

private
  infixr 9 _∘ᴵ_
  _∘ᴵ_ : ∀ {A B C} → S.HomTerm B C → S.HomTerm A B → S.HomTerm A C
  _∘ᴵ_ = S._∘_
  s' = genᵗ zero

module Negative where

  -- distinct diagrams stay apart (sanity: every just is a real proof).
  neg-distinct : decide?F (s' ∘ᴵ s') s' ≡ nothing
  neg-distinct = refl

--------------------------------------------------------------------------------
-- WIRE-LEVEL σ-engine tests (driving `Sigma.decideσ?` directly, below the
-- front-end): a concrete signature over ℕ-labelled wires, given as a Fin-5
-- arity table (so DecEq and rank come from `Fin`).  Five generators: three
-- 1-wire boxes (kbox/k2box on wire colour 0 — distinguishable only by the rank
-- tiebreak — and mbox on colour 2) and two 2-wire boxes (wbox/w2box, for the
-- straddle negative).  Machine-checked:
--   (i)   a σσ-cancellation hit (adjacent inverse cross-pair deletes), both
--         at the head and below a box layer;
--   (ii)  disjoint cross-box interchange (the crossing participates in the
--         bubble sort like an ordinary box);
--   (iii) negative cases (distinct boxes; a non-cancelling diagram);
--   (iv)  the naturality slides wired into the driver: b-image
--         and a-image slides (head and deep), slide+cancel combined,
--         wire-level σ-naturality via two slides, and the negative
--         straddling-box case.
--------------------------------------------------------------------------------
module SigmaTests where

  open import Data.Fin
  open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
  open import Data.List

  -- `∅` for the empty wire-list: `pad ∅ …` in the litmus types below would
  -- otherwise clash with Diag's `[]_` prefix constructor at parse time.
  ∅ : List ℕ
  ∅ = []

  -- Fin-indexed signature (cf. Test.Frontend): DecEq and the rank tiebreak come
  -- for free from `Fin`'s `_≟_`/`toℕ`.
  arity2 : Fin 5 → List ℕ × List ℕ
  arity2 zero                         = (0 ∷ []) , (0 ∷ [])
  arity2 (suc zero)                   = (0 ∷ []) , (0 ∷ [])
  arity2 (suc (suc zero))             = (2 ∷ []) , (2 ∷ [])
  arity2 (suc (suc (suc zero)))       = (1 ∷ 0 ∷ []) , (1 ∷ 0 ∷ [])
  arity2 (suc (suc (suc (suc _))))    = (0 ∷ 1 ∷ []) , (0 ∷ 1 ∷ [])

  data Gen2 : List ℕ → List ℕ → Set where
    gen2 : (i : Fin 5) → Gen2 (proj₁ (arity2 i)) (proj₂ (arity2 i))

  -- readable aliases matching the test bodies.
  kbox  = gen2 zero
  k2box = gen2 (suc zero)
  mbox  = gen2 (suc (suc zero))
  wbox  = gen2 (suc (suc (suc zero)))
  w2box = gen2 (suc (suc (suc (suc zero))))

  open import Categories.FreeStrictMonoidal

  private module SG = Sigma Gen2
  open SG
  -- HomTerm composition / `≈Term` / `pad` for the litmus types (not
  -- re-exported through `open SG`, which only publicises the wire-coherence
  -- kit; `castW` is available from `SG`, `pad` and the HomTerm ops are not).
  open FreeMonoidalHelper.Mor Symm ℕ mor
  -- the strict pad / cast operators + `_≈ʷ_` for the strict slide litmus below.
  open FreeStrictMonoidalHelper MorS using (padʷ; castʷᵈ; module Theory)
  open Theory R_σ

  private
    instance
      DecEq-Gen2 : DecEq GenM
      DecEq-Gen2 .DecEq._≟_ (_ , _ , gen2 i) (_ , _ , gen2 j) = case i ≟Fin j of λ where
        (yes refl) → yes refl
        (no ¬p)    → no λ where refl → ¬p refl

    rank2 : GenM → ℕ
    rank2 (_ , _ , gen2 i) = toℕ i

  open SG.Decideσ rank2

  ------------------------------------------------------------------------
  -- (i) σσ-cancellation.
  ------------------------------------------------------------------------
  w01 : List ℕ
  w01 = 0 ∷ 1 ∷ []

  -- cross then its inverse  ≈  id.
  tCancelL tCancelR : WTerm w01 w01
  tCancelL = boxʷ (cross (1 ∷ []) (0 ∷ [])) ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
  tCancelR = idʷ

  testCancel : IsJust (decideσ? tCancelL tCancelR)
  testCancel = tt

  -- the same pair fires below a leading box layer.
  tCancelDeepL tCancelDeepR : WTerm w01 w01
  tCancelDeepL = boxʷ (cross (1 ∷ []) (0 ∷ [])) ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ [])) ∘ʷ (boxʷ (box kbox) ⊗ʷ idʷ)
  tCancelDeepR = boxʷ (box kbox) ⊗ʷ idʷ

  testCancelDeep : IsJust (decideσ? tCancelDeepL tCancelDeepR)
  testCancelDeep = tt

  ------------------------------------------------------------------------
  -- (ii) disjoint cross-box interchange: the crossing (wires 0-1) and the
  -- box (wire 2) commute — decided by the existing bubble sort, with the
  -- crossing as an ordinary layer.
  ------------------------------------------------------------------------
  w012 : List ℕ
  w012 = 0 ∷ 1 ∷ 2 ∷ []

  layerCross : WTerm w012 (1 ∷ 0 ∷ 2 ∷ [])
  layerCross = boxʷ (cross (0 ∷ []) (1 ∷ [])) ⊗ʷ idʷ

  layerBoxPre : WTerm w012 w012
  layerBoxPre = idʷ {0 ∷ 1 ∷ []} ⊗ʷ boxʷ (box mbox)

  layerBoxPost : WTerm (1 ∷ 0 ∷ 2 ∷ []) (1 ∷ 0 ∷ 2 ∷ [])
  layerBoxPost = idʷ {1 ∷ 0 ∷ []} ⊗ʷ boxʷ (box mbox)

  tIntL tIntR : WTerm w012 (1 ∷ 0 ∷ 2 ∷ [])
  tIntL = layerCross ∘ʷ layerBoxPre     -- box (offset 2) first, then cross
  tIntR = layerBoxPost ∘ʷ layerCross    -- cross first, then box

  testInterchange : IsJust (decideσ? tIntL tIntR)
  testInterchange = tt

  ------------------------------------------------------------------------
  -- (iii) negative cases: every `just` is a real proof, and these are
  -- genuinely not decided (distinct generators / non-cancelling pair).
  ------------------------------------------------------------------------
  testNegBoxes : decideσ? (boxʷ (box kbox)) (boxʷ (box k2box)) ≡ nothing
  testNegBoxes = refl

  testNegCancel : decideσ? tCancelL tCancelDeepR ≡ nothing
  testNegCancel = refl

  ------------------------------------------------------------------------
  -- slide litmus: the STRICT clean naturality slide KEY (`slide-cleanˢ`)
  -- instantiates at concrete offsets (kbox slides past `cross [1] [0]` from
  -- its post-cross to its pre-cross position), with all four `++`-assoc index
  -- casts `refl`.
  ------------------------------------------------------------------------
  litSlide
    : padʷ ∅ (1 ∷ ∅) (boxʷ (box kbox))
        ∘ʷ castʷ refl (padʷ ∅ ∅ (boxʷ (cross (1 ∷ ∅) (0 ∷ ∅))))
      ≈ʷ castʷ refl (padʷ ∅ ∅ (boxʷ (cross (1 ∷ ∅) (0 ∷ ∅)))
           ∘ʷ castʷ refl (castʷᵈ (sym refl) (padʷ (1 ∷ ∅) ∅ (boxʷ (box kbox)))))
  litSlide = slide-cleanˢ [] [] (1 ∷ []) [] [] (boxʷ (box kbox)) {refl} {refl} {refl}

  -- a-block mirror: kbox slides through the crossing's a-image (the SUFFIX
  -- of the cross's output) instead of the b-image; same concrete offsets,
  -- all four casts `refl`.
  litSlide-a
    : padʷ (1 ∷ ∅) ∅ (boxʷ (box kbox))
        ∘ʷ castʷ refl (padʷ ∅ ∅ (boxʷ (cross (0 ∷ ∅) (1 ∷ ∅))))
      ≈ʷ castʷ refl (padʷ ∅ ∅ (boxʷ (cross (0 ∷ ∅) (1 ∷ ∅)))
           ∘ʷ castʷ refl (castʷᵈ (sym refl) (padʷ ∅ (1 ∷ ∅) (boxʷ (box kbox)))))
  litSlide-a = slide-cleanˢ-a [] [] (1 ∷ []) [] [] (boxʷ (box kbox)) {refl} {refl} {refl}

  ------------------------------------------------------------------------
  -- (iv) the Diag-level naturality SLIDE, wired into the driver.
  ------------------------------------------------------------------------
  w10 : List ℕ
  w10 = 1 ∷ 0 ∷ []

  -- b-image slide: kbox after the crossing (in the b-image prefix) is the
  -- same as kbox before the crossing (in the b suffix).
  tSlideL tSlideR : WTerm w10 w01
  tSlideL = (boxʷ (box kbox) ⊗ʷ idʷ) ∘ʷ boxʷ (cross (1 ∷ []) (0 ∷ []))
  tSlideR = boxʷ (cross (1 ∷ []) (0 ∷ [])) ∘ʷ (idʷ {1 ∷ []} ⊗ʷ boxʷ (box kbox))

  testSlide : IsJust (decideσ? tSlideL tSlideR)
  testSlide = tt

  -- the same slide fires deep: below a leading k2box layer.
  tSlideDeepL tSlideDeepR : WTerm w10 w01
  tSlideDeepL = tSlideL ∘ʷ (idʷ {1 ∷ []} ⊗ʷ boxʷ (box k2box))
  tSlideDeepR = tSlideR ∘ʷ (idʷ {1 ∷ []} ⊗ʷ boxʷ (box k2box))

  testSlideDeep : IsJust (decideσ? tSlideDeepL tSlideDeepR)
  testSlideDeep = tt

  -- a-image slide + σσ-cancel combined: a box conjugated by an inverse
  -- cross-pair (sitting in the a-image between them) is the bare box.
  tSlideCancelL tSlideCancelR : WTerm w01 w01
  tSlideCancelL = boxʷ (cross (1 ∷ []) (0 ∷ []))
               ∘ʷ (idʷ {1 ∷ []} ⊗ʷ boxʷ (box kbox))
               ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
  tSlideCancelR = boxʷ (box kbox) ⊗ʷ idʷ

  testSlideCancel : IsJust (decideσ? tSlideCancelL tSlideCancelR)
  testSlideCancel = tt

  -- σ-naturality at the wire level: TWO slides (kbox through the a-image,
  -- mbox through the b-image) reconcile box-before-cross with
  -- box-after-cross.
  w02 : List ℕ
  w02 = 0 ∷ 2 ∷ []

  tNatL tNatR : WTerm w02 (2 ∷ 0 ∷ [])
  tNatL = boxʷ (cross (0 ∷ []) (2 ∷ [])) ∘ʷ (boxʷ (box kbox) ⊗ʷ boxʷ (box mbox))
  tNatR = (boxʷ (box mbox) ⊗ʷ boxʷ (box kbox)) ∘ʷ boxʷ (cross (0 ∷ []) (2 ∷ []))

  testSlideNat : IsJust (decideσ? tNatL tNatR)
  testSlideNat = tt

  -- NEGATIVE: a box STRADDLING the two image blocks does not slide (and
  -- the pair is genuinely not decided).
  tStraddleL tStraddleR : WTerm w01 w10
  tStraddleL = boxʷ (box wbox) ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
  tStraddleR = boxʷ (cross (0 ∷ []) (1 ∷ [])) ∘ʷ boxʷ (box w2box)

  testNegStraddle : decideσ? tStraddleL tStraddleR ≡ nothing
  testNegStraddle = refl
