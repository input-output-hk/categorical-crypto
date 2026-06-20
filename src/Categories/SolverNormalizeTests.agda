{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Litmus tests for `Categories.SolverNormalize`: the clean-DiagU swap engine
-- genuinely reorders, on the smallest signature that exercises it.
--
-- Two independent single-wire boxes `fbox` (on wire 0) and `gbox` (on wire 1),
-- presented in NON-canonical order, are reordered into canonical
-- (lower-offset-first) order, with machine-checked `≈Term` soundness.  This
-- exercises `g-out≈pad`/`g-in≈pad`, the `LeftFit` recogniser `leftFit?`, the
-- firing `swapHeadD`, and `normalizeD`.
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
rFo = idˡ ○ id⊗id≈id
rBo : Frame.reassocB-out [] [] [] fbox gbox ≈Term id
rBo = id⊗id≈id ⟩∘⟨refl ○ idˡ
rFi : Frame.reassocF-in [] [] [] fbox gbox ≈Term id
rFi = idˡ ○ id⊗id≈id
rBi : Frame.reassocB-in [] [] [] fbox gbox ≈Term id
rBi = id⊗id≈id ⟩∘⟨refl ○ idˡ

-- the frame g-layers, re-expressed as genuine clean flat pads (reassocs gone).
g-out≈cp : Frame.g-out [] [] [] fbox gbox ≈Term pad (0 ∷ []) [] (⟦box⟧ gbox)
g-out≈cp = Frame.g-out≈pad [] [] [] fbox gbox
  ○ (rBo ⟩∘⟨ refl⟩∘⟨ rFo) ○ idˡ ○ idʳ
g-in≈cp : Frame.g-in [] [] [] fbox gbox ≈Term pad (0 ∷ []) [] (⟦box⟧ gbox)
g-in≈cp = Frame.g-in≈pad [] [] [] fbox gbox
  ○ (rBi ⟩∘⟨ refl⟩∘⟨ rFi) ○ idˡ ○ idʳ

-- the two CLEAN orderings:
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
cB≈before = (refl⟩∘⟨ ⟺ g-out≈cp) ⟩∘⟨refl
cA≈after : ⟦ cleanA ⟧O ≈Term ⟦ after ⟧O
cA≈after = refl⟩∘⟨ ⟺ g-in≈cp

-- the clean reorder: the two swapped clean orderings are equal in the free
-- monoidal category, via g-out≈pad / two-box-swap / g-in≈pad.  No σ.
clean-reorder : ⟦ cleanB ⟧O ≈Term ⟦ cleanA ⟧O
clean-reorder = cB≈before
  ○ Frame.head-swap-sound [] [] [] fbox gbox []
  ○ ⟺ cA≈after

--------------------------------------------------------------------------------
-- LITMUS (DiagU level): the `LeftFit`-driven, frame-routed swap fires on a
-- pair recognised from two DiagU head layers.  The fit has P = mid = s = [],
-- left box fy = fbox, right box fx = gbox; `LeftFrame.input⇒sorted` swaps the
-- input order (gbox-first) into the sorted order (fbox-first).
--------------------------------------------------------------------------------

-- the recognised fit (offsets are exactly the LeftFit equations, by `refl`).
litFit : LeftFit (0 ∷ []) [] [] (1 ∷ []) gbox fbox
litFit = leftFit [] [] [] refl refl refl refl

open LeftFrame litFit
  using (input-O; sorted-O; input⇒sorted; N₃; f-out-layer; g-in-layer)

-- the empty wired tail from the frame's common output N₃.
litTail : Wired N₃ [] N₃
litTail = []

-- the frame-routed swap step: input (gbox first) ⇒ sorted (fbox first).
litStep : input-O litTail ⇒W sorted-O litTail
litStep = input⇒sorted litTail

-- the sorted head layer is fbox's clean `f-in` (lower offset fires first).
litReorders : layers (sorted-O litTail)
            ≡ Frame.f-in-layer [] [] [] fbox gbox
            ∷ Frame.g-out-layer [] [] [] fbox gbox ∷ []
litReorders = refl

-- and the input head was gbox's grouped `g-in` (higher offset fired first).
litInputHead : layers (input-O litTail)
             ≡ g-in-layer ∷ f-out-layer ∷ []
litInputHead = refl

litSound : ⟦ input-O litTail ⟧O ≈Term ⟦ sorted-O litTail ⟧O
litSound = sound litStep

--------------------------------------------------------------------------------
-- LITMUS (DiagU clean-bridge level): `fx-clean⇒g-in` and `diagU-swap-sound`
-- on the concrete `litFit`.  Here P=mid=s=[], so every `++`-assoc cast
-- `castW (domeq …)` reduces to `id` and the abstract bridge specialises to the
-- concrete clean reorder.
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
-- LITMUS (swapHeadD): the clean DiagU SWAP OUTPUT built by `swapHeadD-out` on
-- `litFit`.  The swapped diagram fires fbox (lower offset) FIRST then gbox; the
-- inter-layer `domeq` is absorbed by `substDiagU` (= `id` here).
--------------------------------------------------------------------------------

-- the empty sorted tail at the swapped-output index ((0∷[])++(1∷[])) = 0∷1∷[].
litDSorted : DiagU (0 ∷ 1 ∷ [])
litDSorted = []_ (0 ∷ 1 ∷ [])

-- the SWAPPED clean DiagU: fbox first (offset 0), then gbox.
litSwapped : DiagU (0 ∷ 1 ∷ [])
litSwapped = swapHeadD-out litFit litDSorted

-- the swapped DiagU's head layer is fbox at offset 0 (lower offset fires
-- first), then gbox in the grouped tail.
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
-- LITMUS (end-to-end DiagU swap): the INPUT clean DiagU (gbox first) and the
-- SWAPPED clean DiagU `litSwapped` (fbox first) have EQUAL interpretations in
-- the free monoidal category, by chaining `diagU-swap-sound` with
-- `swapHeadD-out-sound` (all `++`-assoc casts reduce to `id` here).
--------------------------------------------------------------------------------

-- the INPUT clean DiagU: gbox (offset 0, the right box) fires FIRST, then fbox.
litInput : DiagU (0 ∷ 1 ∷ [])
litInput = (0 ∷ []) ▸ [] ∷ gbox ⟨ [] ▸ (1 ∷ []) ∷ fbox ⟨ litDSorted ⟩ ⟩

litInputLayers : fromDiagU-ls litInput
               ≡ mk-pad (0 ∷ []) [] gbox
               ∷ mk-pad [] (1 ∷ []) fbox ∷ []
litInputLayers = refl

-- ⟦ input (gbox-first) ⟧ ≈ ⟦ swapped (fbox-first) ⟧.  All `castW (domeq …)`
-- reduce to `id` (P=mid=s=[]); the residual `∘ id`s are absorbed by `idʳ`.
litDiagUSwap : ⟦ litInput ⟧ ≈Term ⟦ litSwapped ⟧
litDiagUSwap = begin
  ⟦ litInput ⟧
    ≈⟨ assoc ⟩
  ⟦ litDSorted ⟧ ∘ (Frame.f-out [] [] [] fbox gbox ∘ pad (0 ∷ []) [] (⟦box⟧ gbox))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ idˡ ⟩
  ⟦ litDSorted ⟧ ∘ Frame.f-out [] [] [] fbox gbox ∘ id ∘ pad (0 ∷ []) [] (⟦box⟧ gbox)
    ≈⟨ diagU-swap-sound litFit litTail ⟩
  ⟦ sorted-O litTail ⟧O ∘ id
    ≈⟨ idʳ ⟩
  ⟦ sorted-O litTail ⟧O
    ≈⟨ swapped-as-sorted ⟨
  ⟦ litSwapped ⟧ ∎
  where
    -- ⟦ litSwapped ⟧ ≈ ⟦ sorted-O litTail ⟧O : both are fbox-first-then-gbox;
    -- from `swapHeadD-out-sound` with the `id` casts and `idˡ`/`idʳ` absorbed.
    swapped-as-sorted : ⟦ litSwapped ⟧ ≈Term ⟦ sorted-O litTail ⟧O
    swapped-as-sorted = begin
      ⟦ litSwapped ⟧
        ≈⟨ idˡ ⟨
      id ∘ ⟦ litSwapped ⟧
        ≈⟨ swapHeadD-out-sound [] [] [] gbox fbox litDSorted ⟩
      (⟦ litDSorted ⟧ ∘ pad (0 ∷ []) [] (⟦box⟧ gbox)) ∘ id ∘ Frame.f-in [] [] [] fbox gbox
        ≈⟨ refl⟩∘⟨ idˡ ⟩
      (⟦ litDSorted ⟧ ∘ pad (0 ∷ []) [] (⟦box⟧ gbox)) ∘ Frame.f-in [] [] [] fbox gbox
        ≈⟨ (refl⟩∘⟨ ⟺ g-out≈cp) ⟩∘⟨refl ⟩
      (⟦ litDSorted ⟧ ∘ Frame.g-out [] [] [] fbox gbox) ∘ Frame.f-in [] [] [] fbox gbox ∎

--------------------------------------------------------------------------------
-- LITMUS (SortD): the DECIDABLE recogniser `leftFit?` FIRES on the concrete
-- out-of-order head data, and `swapHeadD`/`normalizeD` reorder.  X = ℕ with
-- `DecidableEquality` `_≟_`; all `++`-assoc casts reduce to `id` (P=mid=s=[]).
--------------------------------------------------------------------------------
open SortD

-- the recogniser FIRES on the litmus offsets/boxes.
litLeftFit? : leftFit? (0 ∷ []) [] [] (1 ∷ []) gbox fbox
            ≡ just (leftFit [] [] [] refl refl refl refl)
litLeftFit? = refl

-- it conservatively REJECTS an in-order / non-fitting pair.
litLeftFit?-no : leftFit? [] [] [] [] fbox gbox ≡ nothing
litLeftFit?-no = refl

-- the firing swap on the recognised fit + empty tail.
litSwapD : HeadSwapD litFit litDSorted
litSwapD = swapHeadD litFit litDSorted

-- `normalizeD` with positive fuel REORDERS to fbox-first.
litNormReorders : fromDiagU-ls (normalizeD 4 litFit litDSorted)
                ≡ mk-pad [] (1 ∷ []) fbox
                ∷ mk-pad (0 ∷ []) [] gbox ∷ []
litNormReorders = refl

-- and the INPUT (fuel 0 / pre-sort) is gbox-first.
litNormInput : fromDiagU-ls (normalizeD 0 litFit litDSorted)
             ≡ mk-pad (0 ∷ []) [] gbox
             ∷ mk-pad [] (1 ∷ []) fbox ∷ []
litNormInput = refl

-- the casts are the identity here, so the soundness witness is `refl`.
litNormCastId : proj₁ (normalizeD-sound 4 litFit litDSorted) ≡ refl
litNormCastId = refl

litNormSound : id ∘ ⟦ dInput litFit litDSorted ⟧
             ≈Term ⟦ normalizeD 4 litFit litDSorted ⟧
litNormSound = proj₂ (normalizeD-sound 4 litFit litDSorted)
