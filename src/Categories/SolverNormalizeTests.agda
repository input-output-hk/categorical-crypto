{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Litmus tests for `Categories.SolverNormalize`: the clean-DiagU swap engine
-- genuinely reorders, on the smallest signature that exercises it.
--
-- Two independent single-wire boxes `fbox` (on wire 0) and `gbox` (on wire 1),
-- presented in NON-canonical order, are reordered by a real `two-box-swap`
-- step into canonical (lower-offset-first) order, with machine-checked `≈Term`
-- soundness witnesses.  The swapped layers are again genuine clean `mk-pad`s
-- (so the sort could fire again).  This exercises BOTH `g-out≈pad` and
-- `g-in≈pad` (collapsed to clean pads via the here-`≈id` reassociators), the
-- `LeftFit` recogniser `leftFit?`, the firing `swapHeadD`, and `normalizeD`.
--------------------------------------------------------------------------------

module Categories.SolverNormalizeTests where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Categories.DiagramRewriteUntyped
open import Categories.FreeMonoidal
open import Categories.SolverNormalize

data Gen : List ℕ → List ℕ → Set where
  fbox : Gen (0 ∷ []) (0 ∷ [])
  gbox : Gen (1 ∷ []) (1 ∷ [])

open Normalize Mon {ℕ} _≟ℕ_ Gen
open Untyped Mon {ℕ} Gen
open FreeMonoidalHelper.Mor Mon ℕ mor
open ≈R

-- the concrete frame: P = mid = r = [], boxes fbox (slot 1) and gbox (slot 2).
-- Its four structural reassociators all reduce to `id` (single-wire blocks).
rFo : Frame.reassocF-out [] [] [] fbox gbox ≈Term id
rFo = ≈-Term-trans idˡ id⊗id≈id
rBo : Frame.reassocB-out [] [] [] fbox gbox ≈Term id
rBo = ≈-Term-trans (∘-resp-≈ id⊗id≈id ≈-Term-refl) idˡ
rFi : Frame.reassocF-in [] [] [] fbox gbox ≈Term id
rFi = ≈-Term-trans idˡ id⊗id≈id
rBi : Frame.reassocB-in [] [] [] fbox gbox ≈Term id
rBi = ≈-Term-trans (∘-resp-≈ id⊗id≈id ≈-Term-refl) idˡ

-- the frame g-layers, re-expressed as genuine clean flat pads (reassocs gone).
g-out≈cp : Frame.g-out [] [] [] fbox gbox ≈Term pad (0 ∷ []) [] (⟦box⟧ gbox)
g-out≈cp = ≈-Term-trans (Frame.g-out≈pad [] [] [] fbox gbox)
  (≈-Term-trans (∘-resp-≈ rBo (∘-resp-≈ ≈-Term-refl rFo)) (≈-Term-trans idˡ idʳ))
g-in≈cp : Frame.g-in [] [] [] fbox gbox ≈Term pad (0 ∷ []) [] (⟦box⟧ gbox)
g-in≈cp = ≈-Term-trans (Frame.g-in≈pad [] [] [] fbox gbox)
  (≈-Term-trans (∘-resp-≈ rBi (∘-resp-≈ ≈-Term-refl rFi)) (≈-Term-trans idˡ idʳ))

-- the two CLEAN orderings (genuine `mk-pad` layers, definitionally wired).
--   cleanB :  fbox first (offset 0), then gbox (offset 1)   -- canonical
--   cleanA :  gbox first (offset 1), then fbox (offset 0)   -- non-canonical
cleanB : Ordering (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
cleanB = ordering _ (mk-pad [] (1 ∷ []) fbox ∷ (mk-pad (0 ∷ []) [] gbox ∷ []))
cleanA : Ordering (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])
cleanA = ordering _ (mk-pad (0 ∷ []) [] gbox ∷ (mk-pad [] (1 ∷ []) fbox ∷ []))

before = Frame.before-O [] [] [] fbox gbox []
after  = Frame.after-O  [] [] [] fbox gbox []

-- the clean orderings equal the frame composites (only the g-layer differs).
cB≈before : ⟦ cleanB ⟧O ≈Term ⟦ before ⟧O
cB≈before = ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym g-out≈cp)) ≈-Term-refl
cA≈after : ⟦ cleanA ⟧O ≈Term ⟦ after ⟧O
cA≈after = ∘-resp-≈ ≈-Term-refl (≈-Term-sym g-in≈cp)

-- THE GENUINE CLEAN REORDER: two clean `mk-pad` layers, swapped, equal in the
-- free monoidal category — via g-out≈pad / two-box-swap / g-in≈pad.  No σ.
clean-reorder : ⟦ cleanB ⟧O ≈Term ⟦ cleanA ⟧O
clean-reorder = ≈-Term-trans cB≈before
                  (≈-Term-trans (Frame.head-swap-sound [] [] [] fbox gbox [])
                    (≈-Term-sym cA≈after))

--------------------------------------------------------------------------------
-- LITMUS (DiagU level): the `LeftFit`-driven, frame-routed swap fires on a
-- pair recognised by reading the boxes/offsets off two DiagU head layers.
--
-- Out-of-order input: gbox (right box, fires FIRST) then fbox (left box,
-- fires SECOND).  We build the `LeftFit` with P = mid = s = [], left box
-- fy = fbox (dom/cod `0∷[]`), right box fx = gbox (dom/cod `1∷[]`).  The fit's
-- offset equations:  px ≡ ay = 0∷[] , sx ≡ [] , py ≡ [] , sy ≡ bx = 1∷[].
-- The provable `LeftFrame.input⇒sorted` swaps the frame's input order
-- (gbox-first) into the sorted order (fbox-first) with a real `two-box-swap`
-- witness — autonomously, with the fit RECOGNISED from the layer data.
--------------------------------------------------------------------------------

-- the recognised fit (offsets are exactly the LeftFit equations, by `refl`).
litFit : LeftFit (0 ∷ []) [] [] (1 ∷ []) gbox fbox
litFit = leftFit [] [] [] refl refl refl refl

open LeftFrame litFit
  using (input-O; sorted-O; input⇒sorted; N₃; f-out-layer; g-in-layer)

-- the empty wired tail from the frame's common output N₃.
litTail : Wired N₃ [] N₃
litTail = []

-- the autonomous frame-routed swap step: input (gbox first) ⇒ sorted
-- (fbox first).  Its witness is `≈-Term-sym head-swap-sound` = `two-box-swap`.
litStep : input-O litTail ⇒W sorted-O litTail
litStep = input⇒sorted litTail

-- it genuinely REORDERS: the sorted head layer is fbox's clean `f-out`
-- (the lower-offset box now fires first) — machine-checked by `refl`.
litReorders : layers (sorted-O litTail)
            ≡ Frame.f-in-layer [] [] [] fbox gbox
            ∷ Frame.g-out-layer [] [] [] fbox gbox ∷ []
litReorders = refl

-- and the input head was gbox's grouped `g-in` (the higher-offset box was
-- firing first) — confirming the pair was out of order.
litInputHead : layers (input-O litTail)
             ≡ g-in-layer ∷ f-out-layer ∷ []
litInputHead = refl

-- the genuine `≈Term` soundness of the autonomous frame-routed swap.
litSound : ⟦ input-O litTail ⟧O ≈Term ⟦ sorted-O litTail ⟧O
litSound = sound litStep

--------------------------------------------------------------------------------
-- LITMUS (DiagU clean-bridge level): exercise the PROVEN `fx-clean⇒g-in`
-- and `diagU-swap-sound` on the concrete `litFit`.  Here P=mid=s=[] so every
-- `++`-assoc index cast `castW (domeq …)` reduces to `castW refl = id` and the
-- frame `f-out`/`g-in` are single-wire pads — the abstract bridge specialises
-- exactly to the concrete clean reorder.  Both witnesses are machine-checked.
--------------------------------------------------------------------------------

-- the concrete clean⇒frame bridge (the casts are `id`; fully reduced).
litBridge :
  ⟦ litTail ⟧W
    ∘ Frame.f-out [] [] [] fbox gbox
    ∘ castW (domeq [] (0 ∷ []) [] (1 ∷ []) [])
    ∘ pad (0 ∷ []) [] (⟦box⟧ gbox)
  ≈Term ⟦ input-O litTail ⟧O ∘ castW (domeq [] (0 ∷ []) [] (1 ∷ []) [])
litBridge = fx-clean⇒g-in litFit litTail

-- the concrete DiagU swap soundness: clean (gbox-first) ⇒ sorted (fbox-first).
litSwapSound :
  ⟦ litTail ⟧W
    ∘ Frame.f-out [] [] [] fbox gbox
    ∘ castW (domeq [] (0 ∷ []) [] (1 ∷ []) [])
    ∘ pad (0 ∷ []) [] (⟦box⟧ gbox)
  ≈Term ⟦ sorted-O litTail ⟧O ∘ castW (domeq [] (0 ∷ []) [] (1 ∷ []) [])
litSwapSound = diagU-swap-sound litFit litTail

-- the casts are genuinely the identity here (P=mid=s=[]) — `refl`-checked.
litCastId : castW (domeq [] (0 ∷ []) [] (1 ∷ []) []) ≡ id
litCastId = refl

--------------------------------------------------------------------------------
-- LITMUS (swapHeadD): the genuine clean DiagU SWAP OUTPUT.  We build the
-- swapped clean DiagU with `swapHeadD-out` on `litFit` (fx = gbox at offset 0
-- as the right box, fy = fbox the left box).  The swapped diagram fires fbox
-- (lower offset) FIRST then gbox — both genuine clean `_▸_∷_⟨_⟩` `pad`-layers,
-- the inter-layer `domeq` absorbed by `substDiagU` (= `id` here).  We
-- machine-check the reorder by `refl` on its layer list and exhibit the
-- compiled `swapHeadD-out-sound` witness.
--------------------------------------------------------------------------------

-- the empty sorted tail at the swapped-output index ((0∷[])++(1∷[])) = 0∷1∷[].
litDSorted : DiagU (0 ∷ 1 ∷ [])
litDSorted = []_ (0 ∷ 1 ∷ [])

-- the SWAPPED clean DiagU: fbox first (offset 0), then gbox.  Built autonomously
-- by `swapHeadD-out`; the `substDiagU` cast reduces to identity here.
litSwapped : DiagU (0 ∷ 1 ∷ [])
litSwapped = swapHeadD-out litFit litDSorted

-- the swap genuinely REORDERED: the swapped DiagU's head layer is fbox at
-- offset 0 (lower-offset box now fires FIRST), then gbox at offset 0 in the
-- grouped tail — machine-checked by `refl` on the layer list.
litSwappedLayers : fromDiagU-ls litSwapped
                 ≡ mk-pad [] (1 ∷ []) fbox
                 ∷ mk-pad (0 ∷ []) [] gbox ∷ []
litSwappedLayers = refl

-- the compiled soundness of the swapped output (the casts are `id` here).
litSwapOutSound :
  castW (substDiagU-out (domeq [] (0 ∷ []) [] (1 ∷ []) [])
          (((0 ∷ []) ++ ([])) ▸ [] ∷ gbox ⟨ litDSorted ⟩))
    ∘ ⟦ litSwapped ⟧
  ≈Term (⟦ litDSorted ⟧ ∘ pad (0 ∷ []) [] (⟦box⟧ gbox))
      ∘ castW (sym (domeq [] (0 ∷ []) [] (1 ∷ []) []))
      ∘ Frame.f-in [] [] [] fbox gbox
litSwapOutSound = swapHeadD-out-sound [] [] [] gbox fbox litDSorted

--------------------------------------------------------------------------------
-- LITMUS (end-to-end DiagU swap): the INPUT clean DiagU (gbox fires FIRST) and
-- the SWAPPED clean DiagU `litSwapped` (fbox fires first) have EQUAL
-- interpretations in the free monoidal category — a genuine, machine-checked
-- `≈Term` between two clean `DiagU`s, built by chaining `diagU-swap-sound` with
-- `swapHeadD-out-sound` (all `++`-assoc casts reduce to `id` here).  This is the
-- concrete witness that the autonomous DiagU swap engine REORDERS soundly.
--------------------------------------------------------------------------------

-- the INPUT clean DiagU: gbox (offset 0, the right box) fires FIRST, then fbox.
litInput : DiagU (0 ∷ 1 ∷ [])
litInput = (0 ∷ []) ▸ [] ∷ gbox ⟨ [] ▸ (1 ∷ []) ∷ fbox ⟨ litDSorted ⟩ ⟩

-- both DiagUs reorder genuinely: input is gbox-first, swapped is fbox-first.
litInputLayers : fromDiagU-ls litInput
               ≡ mk-pad (0 ∷ []) [] gbox
               ∷ mk-pad [] (1 ∷ []) fbox ∷ []
litInputLayers = refl

-- THE END-TO-END SOUNDNESS: ⟦ input (gbox-first) ⟧ ≈ ⟦ swapped (fbox-first) ⟧.
-- All `castW (domeq …)` reduce to `id` (P=mid=s=[]); we feed both compiled
-- halves the SAME empty tail and absorb the residual `∘ id`s by `idʳ`.
litDiagUSwap : ⟦ litInput ⟧ ≈Term ⟦ litSwapped ⟧
litDiagUSwap = begin
  ⟦ litInput ⟧
    ≈⟨ assoc ⟩
  ⟦ litDSorted ⟧ ∘ (Frame.f-out [] [] [] fbox gbox ∘ pad (0 ∷ []) [] (⟦box⟧ gbox))
    ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⟩
  ⟦ litDSorted ⟧ ∘ Frame.f-out [] [] [] fbox gbox ∘ id ∘ pad (0 ∷ []) [] (⟦box⟧ gbox)
    ≈⟨ diagU-swap-sound litFit litTail ⟩
  ⟦ sorted-O litTail ⟧O ∘ id
    ≈⟨ idʳ ⟩
  ⟦ sorted-O litTail ⟧O
    ≈⟨ ≈-Term-sym swapped-as-sorted ⟩
  ⟦ litSwapped ⟧ ∎
  where
    -- ⟦ litSwapped ⟧ ≈ ⟦ sorted-O litTail ⟧O : both are fbox-first-then-gbox;
    -- from `swapHeadD-out-sound` with the `id` casts and `idˡ`/`idʳ` absorbed.
    swapped-as-sorted : ⟦ litSwapped ⟧ ≈Term ⟦ sorted-O litTail ⟧O
    swapped-as-sorted = begin
      ⟦ litSwapped ⟧
        ≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ ⟦ litSwapped ⟧
        ≈⟨ swapHeadD-out-sound [] [] [] gbox fbox litDSorted ⟩
      (⟦ litDSorted ⟧ ∘ pad (0 ∷ []) [] (⟦box⟧ gbox)) ∘ id ∘ Frame.f-in [] [] [] fbox gbox
        ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
      (⟦ litDSorted ⟧ ∘ pad (0 ∷ []) [] (⟦box⟧ gbox)) ∘ Frame.f-in [] [] [] fbox gbox
        ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym g-out≈cp)) ≈-Term-refl ⟩
      (⟦ litDSorted ⟧ ∘ Frame.g-out [] [] [] fbox gbox) ∘ Frame.f-in [] [] [] fbox gbox ∎

--------------------------------------------------------------------------------
-- LITMUS (SortD): the DECIDABLE recogniser `leftFit?` FIRES on the concrete
-- out-of-order head data, and `swapHeadD`/`normalizeD` reorder genuinely.  X = ℕ
-- with `DecidableEquality` `_≟_`.  Out-of-order input: gbox (right box, offset 0
-- domain `1∷[]`) fires FIRST then fbox (left box, offset 0).  `leftFit?` rebuilds
-- the fit by splitting the offset lists; `swapHeadD` returns the swapped clean
-- DiagU (fbox first); all `++`-assoc casts reduce to `id` (P=mid=s=[]).
--------------------------------------------------------------------------------
open SortD

-- the recogniser FIRES on the litmus offsets/boxes — machine-checked `just`.
litLeftFit? : leftFit? (0 ∷ []) [] [] (1 ∷ []) gbox fbox
            ≡ just (leftFit [] [] [] refl refl refl refl)
litLeftFit? = refl

-- it conservatively REJECTS an in-order / non-fitting pair (offsets don't split).
litLeftFit?-no : leftFit? [] [] [] [] fbox gbox ≡ nothing
litLeftFit?-no = refl

-- the firing swap on the recognised fit + empty tail.
litSwapD : HeadSwapD litFit litDSorted
litSwapD = swapHeadD litFit litDSorted

-- `normalizeD` with positive fuel REORDERS: the result is the swapped clean
-- DiagU (fbox, the lower-offset box, now fires FIRST) — machine-checked `refl`
-- on the underlying layer list (fbox-pad first, then gbox-pad).
litNormReorders : fromDiagU-ls (normalizeD 4 litFit litDSorted)
                ≡ mk-pad [] (1 ∷ []) fbox
                ∷ mk-pad (0 ∷ []) [] gbox ∷ []
litNormReorders = refl

-- and the INPUT (fuel 0 / pre-sort) is gbox-first — confirming it was out of order.
litNormInput : fromDiagU-ls (normalizeD 0 litFit litDSorted)
             ≡ mk-pad (0 ∷ []) [] gbox
             ∷ mk-pad [] (1 ∷ []) fbox ∷ []
litNormInput = refl

-- the casts are the identity here, so the soundness witness is the clean
-- `≈Term` between the two DiagUs (gbox-first ⇒ fbox-first), machine-checked.
litNormCastId : proj₁ (normalizeD-sound 4 litFit litDSorted) ≡ refl
litNormCastId = refl

litNormSound : id ∘ ⟦ dInput litFit litDSorted ⟧
             ≈Term ⟦ normalizeD 4 litFit litDSorted ⟧
litNormSound = proj₂ (normalizeD-sound 4 litFit litDSorted)
