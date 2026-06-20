{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Normalising untyped monoidal diagrams by reordering independent boxes.
--
-- A `DiagU` is a list of boxes at flat wire-offsets.  Two boxes on disjoint,
-- non-crossing wire ranges are *independent*: swapping their firing order
-- preserves `⟦_⟧`.  That single-pair fact is `TwoBoxSwap.two-box-swap` (σ-free,
-- pure interchange / bifunctoriality).
--
-- DESIGN.  A verbatim transposition of two layers with absolute offsets is
-- ill-wired: after a box of a different width fires, the next box's absolute
-- offset shifts, so the equality the swap needs holds only up to
-- `++`-associativity, never definitionally.  The swap therefore BUILDS its
-- output with RECOMPUTED offsets (`dSwapped`), absorbing the non-definitional
-- re-indexing with `substDiagU`, and its soundness reuses `two-box-swap`
-- together with the offset-reframing bridges `TwoBoxSwap.g-out≈pad` / `g-in≈pad`
-- (the `assocW`/`assocW⁻` reassociators, collapsed to `castW` transports).
--------------------------------------------------------------------------------

module Categories.SolverNormalize where

open import Data.Bool using (Bool; true; false; not; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (≡-dec; ++-assoc)
open import Data.Maybe as Maybe using (Maybe; just; nothing; _>>=_; _<∣>_)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Product using (_,_; Σ-syntax)
open import Function.Base using (case_of_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans)
open import Relation.Nullary using (yes; no)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.DiagramRewriteUntyped
open import Categories.FreeMonoidal

module NormalizeI (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
                  (Mor : List X → List X → Set)
                  (let open WireSig v {X} Mor using () renaming (wires to wires↑; mor to mor↑))
                  (let open FreeMonoidalHelper.Mor v X mor↑ using () renaming (HomTerm to HomTerm↑))
                  (⟦box⟧ : ∀ {a b} → Mor a b → HomTerm↑ (wires↑ a) (wires↑ b)) where

  open UntypedI v {X} Mor ⟦box⟧
  open FreeMonoidalHelper.Mor v X mor hiding (merge; split; merge∘split; split∘merge)
  open ≈R
  -- the DecEq-dependent wire-coherence (UIP-determined `castW`, and the
  -- structural reassociators' collapse to `castW`) lives in WireCoh.WireCohDec.
  open WireCohDec _≟X_ public

  open MR FreeMonoidal
    using (pullˡ; pullʳ; pushˡ; pushʳ; cancelˡ; cancelʳ; insertʳ; assoc²βε)
  open MonR Monoidal-FreeMonoidal
    using (refl⟩⊗⟨_)

  --------------------------------------------------------------------------------
  -- 1. Layers and wired layer-lists
  --------------------------------------------------------------------------------
  --
  -- `Layer`'s interpretation `⟦L⟧` is deliberately general (not just a flat
  -- `pad`) so the *output* of an adjacent swap — whose right box becomes a pad
  -- conjugated by the `assocW`/`assocW⁻` reassociators (`TwoBoxSwap.g-out≈pad`)
  -- — is also a `Layer`, with its well-typedness under our control.

  record Layer : Set where
    constructor mk-layer
    field
      L-in L-out : List X
      ⟦L⟧        : HomTerm (wires L-in) (wires L-out)

  open Layer public

  -- the canonical layer: a box at flat offset `pre`, `suf` idle wires right.
  mk-pad : ∀ {dom cod} (pre suf : List X) → Mor dom cod → Layer
  mk-pad {dom} {cod} pre suf gen =
    mk-layer (pre ++ (dom ++ suf)) (pre ++ (cod ++ suf)) (pad pre suf (⟦box⟧ gen))

  --------------------------------------------------------------------------------
  -- 2. Wired layer-lists and the fold interpretation
  --------------------------------------------------------------------------------
  --
  -- `⟦_⟧W` folds head-applied-first, exactly like `DiagU`'s `⟦_⟧` (this makes
  -- the bridge of §6 definitional).

  data Wired : (N : List X) → List Layer → (M : List X) → Set where
    []  : ∀ {N} → Wired N [] N
    _∷_ : ∀ {M} (l : Layer) {ls}
        → Wired (L-out l) ls M
        → Wired (L-in l) (l ∷ ls) M

  ⟦_⟧W : ∀ {N M ls} → Wired N ls M → HomTerm (wires N) (wires M)
  ⟦ [] ⟧W     = id
  ⟦ l ∷ ws ⟧W = ⟦ ws ⟧W ∘ ⟦L⟧ l

  -- An *ordering* of a diagram at fixed endpoints `N ⇒ M` is a wired layer list.
  record Ordering (N M : List X) : Set where
    constructor ordering
    field
      layers : List Layer
      wired  : Wired N layers M

  open Ordering public

  ⟦_⟧O : ∀ {N M} → Ordering N M → HomTerm (wires N) (wires M)
  ⟦ ordering _ w ⟧O = ⟦ w ⟧W

  --------------------------------------------------------------------------------
  -- 2'. Witness-carrying swap steps
  --------------------------------------------------------------------------------
  -- A swap step `o ⇒W o'` carries a proof that the two interpretations agree;
  -- the genuine adjacent-disjoint swap realises it (`LeftFrame.input⇒sorted`).

  record _⇒W_ {N M : List X} (o o' : Ordering N M) : Set where
    constructor wstep
    field
      sound : ⟦ o ⟧O ≈Term ⟦ o' ⟧O

  open _⇒W_ public

  --------------------------------------------------------------------------------
  -- 3. The four canonical layers of an adjacent disjoint pair, from a frame
  --------------------------------------------------------------------------------
  --
  -- For a frame  P | a₁/b₁ | mid | a₂/b₂ | r  with `f` left, `g` right, the two
  -- firing orders use the four `TwoBoxSwap` layers as `Layer`s: `f-in`/`f-out`
  -- are flat `pad`s of f; `g-out`/`g-in` are pads of g at the shifted offset
  -- conjugated by the reassociators.  "before" (f then g) and "after" (g then f)
  -- share both flat endpoints DEFINITIONALLY, and `two-box-swap` proves their
  -- interpretations `≈Term`-equal.

  module Frame (P mid r : List X) {a₁ b₁ a₂ b₂ : List X}
               (f : Mor a₁ b₁) (g : Mor a₂ b₂) where

    open TwoBoxSwap P mid r f g public

    -- N₀ common input, N₃ common output.
    N₀ : List X
    N₀ = P ++ (a₁ ++ (mid ++ (a₂ ++ r)))

    N₃ : List X
    N₃ = P ++ (b₁ ++ (mid ++ (b₂ ++ r)))

    f-in-layer : Layer
    f-in-layer = mk-layer _ _ f-in

    g-out-layer : Layer
    g-out-layer = mk-layer _ _ g-out

    g-in-layer : Layer
    g-in-layer = mk-layer _ _ g-in

    f-out-layer : Layer
    f-out-layer = mk-layer _ _ f-out

    -- the two head-pairs as wired prefixes N₀ ⇒ N₃, extending any tail.
    before-wired : ∀ {M rest}
                 → Wired (L-out g-out-layer) rest M
                 → Wired (L-in f-in-layer) (f-in-layer ∷ g-out-layer ∷ rest) M
    before-wired wRest = f-in-layer ∷ (g-out-layer ∷ wRest)

    after-wired : ∀ {M rest}
                → Wired (L-out f-out-layer) rest M
                → Wired (L-in g-in-layer) (g-in-layer ∷ f-out-layer ∷ rest) M
    after-wired wRest = g-in-layer ∷ (f-out-layer ∷ wRest)

    -- before/after extended by the SAME tail have `≈Term`-equal interpretations.
    -- Core = `two-box-swap` (no σ; bottoms out in `g-out≈pad`/bifunctoriality);
    -- the rest is congruence + associativity.
    head-swap-sound : ∀ {M rest}
                      (wRest : Wired (L-out g-out-layer) rest M)
                    → ⟦ before-wired wRest ⟧W ≈Term ⟦ after-wired wRest ⟧W
    head-swap-sound wRest = pullʳ two-box-swap ○ ⟺ assoc

    -- the two orderings (same fixed endpoints).
    before-O : ∀ {M rest} → Wired (L-out g-out-layer) rest M → Ordering (L-in f-in-layer) M
    before-O wRest = ordering _ (before-wired wRest)

    after-O : ∀ {M rest} → Wired (L-out f-out-layer) rest M → Ordering (L-in g-in-layer) M
    after-O wRest = ordering _ (after-wired wRest)

  --------------------------------------------------------------------------------
  -- 6. The `DiagU ↔ Ordering` bridge
  --------------------------------------------------------------------------------
  --
  -- Each `DiagU` layer maps to the canonical `mk-pad` `Layer`.  Since `⟦_⟧W`
  -- has the SAME fold shape as `DiagU`'s `⟦_⟧`, the bridge soundness is
  -- definitional (`≈-Term-refl`).

  fromDiagU-ls : ∀ {n} (d : DiagU n) → List Layer
  fromDiagU-ls ([]_ n)             = []
  fromDiagU-ls (pre ▸ suf ∷ f ⟨ d ⟩) = mk-pad pre suf f ∷ fromDiagU-ls d

  fromDiagU-W : ∀ {n} (d : DiagU n) → Wired n (fromDiagU-ls d) (out d)
  fromDiagU-W ([]_ n)             = []
  fromDiagU-W (pre ▸ suf ∷ f ⟨ d ⟩) = mk-pad pre suf f ∷ fromDiagU-W d

  fromDiagU-sound : ∀ {n} (d : DiagU n) → ⟦ fromDiagU-W d ⟧W ≈Term ⟦ d ⟧
  fromDiagU-sound ([]_ n)             = ≈-Term-refl
  fromDiagU-sound (pre ▸ suf ∷ f ⟨ d ⟩) = fromDiagU-sound d ⟩∘⟨refl

  --------------------------------------------------------------------------------
  -- 8. (Open) canonicity / completeness
  --------------------------------------------------------------------------------
  -- Soundness below is unconditional.  OPEN: canonicity — interchange-equal
  -- diagrams reaching the SAME normal form (needs confluence of the bubble sort
  -- to a footprint-ordered form; key = leftmost offset, tiebreak on input width).

  --------------------------------------------------------------------------------
  -- 11. DiagU-level recognition: reading frame data off the boxes
  --------------------------------------------------------------------------------
  --
  -- A `Layer` ERASES its offsets/box into the opaque `⟦L⟧`, so no recogniser
  -- can fire on a generic `Ordering`; a `DiagU` layer carries `fx`, `px`, `sx`
  -- explicitly, so a recogniser CAN read off offsets and decide orientation.
  --
  -- On a head pair  px ▸ sx ∷ fx ⟨ py ▸ sy ∷ fy ⟨ rest ⟩ ⟩  (`fx` fires FIRST,
  -- `fy` SECOND) the `DiagU` typing forces the inter-layer wiring definitionally:
  --   py ++ (ay ++ sy)  ≡  px ++ (bx ++ sx)            -- (★) inner-diagram index

  --------------------------------------------------------------------------------
  -- 11a. The LEFT-OF frame fit (the out-of-order case)
  --------------------------------------------------------------------------------
  --
  -- The head pair is out of canonical order exactly when `fy` (fired second)
  -- sits strictly LEFT of `fx`, so `fy`'s block lies inside `px`'s prefix.  The
  -- fit records three idle blocks `P mid s` with witnesses that the offsets
  -- factor through  P ++ (ay ++ (mid ++ (ax ++ s)))  (fy slot 1, fx slot 2).
  -- Hence INPUT = frame's `after-O` (fx then fy), SORTED = `before-O`, and the
  -- swap runs after ⇒ before by `≈-Term-sym` of `head-swap-sound`.
  record LeftFit {ax bx ay by : List X}
                 (px sx py sy : List X) (fx : Mor ax bx) (fy : Mor ay by) : Set where
    constructor leftFit
    field
      P mid s : List X
      -- fx is the RIGHT box (slot 2); when it fires fy hasn't, so it sees ay:
      px≡   : px ≡ P ++ (ay ++ mid)
      sx≡   : sx ≡ s
      -- fy is the LEFT box (slot 1); by now fx has fired, so it sees bx:
      py≡   : py ≡ P
      sy≡   : sy ≡ mid ++ (bx ++ s)

  --------------------------------------------------------------------------------
  -- 11b. Decidable recognition
  --------------------------------------------------------------------------------
  -- Pure `List`-prefix surgery driven by lengths, exposed as `Maybe` (`nothing`
  -- = not an out-of-order left-of pair; the driver then leaves it in place).
  -- No `DecidableEquality X` needed here: the (★) equalities come from the
  -- caller (the DiagU constructor).

  --------------------------------------------------------------------------------
  -- 11c. The frame underlying a `LeftFit`, and the sound swap
  --------------------------------------------------------------------------------
  -- The frame `Frame P mid s fy fx`; its `before-O`/`after-O` live on the
  -- NATIVE right-nested objects N₀/N₃, so they are well-typed for ABSTRACT
  -- `P mid s` (no subst residue), and the swap is `head-swap-sound`.
  module LeftFrame {ax bx ay by : List X}
                   {px sx py sy : List X} {fx : Mor ax bx} {fy : Mor ay by}
                   (fit : LeftFit px sx py sy fx fy) where

    open LeftFit fit

    open module F = Frame P mid s fy fx public using
      ( N₀ ; N₃
      ; g-in-layer ; f-out-layer
      ; before-O ; after-O ; head-swap-sound )

    -- sorted (fy first) / input (fx first) orders.
    sorted-O : ∀ {M rest} → Wired N₃ rest M → Ordering N₀ M
    sorted-O wRest = before-O wRest

    input-O : ∀ {M rest} → Wired N₃ rest M → Ordering N₀ M
    input-O wRest = after-O wRest

    -- the sound swap step, input ⇒ sorted (= `head-swap-sound`).
    input⇒sorted : ∀ {M rest} (wRest : Wired N₃ rest M)
                 → input-O wRest ⇒W sorted-O wRest
    input⇒sorted wRest = wstep (⟺ (head-swap-sound wRest))

  --------------------------------------------------------------------------------
  -- 11e. The clean ↔ frame bridge for the `fx` (right) layer
  --------------------------------------------------------------------------------
  -- The clean flat pad lives on the LEFT-nested object, the frame's `g-in` on
  -- the RIGHT-nested N₀; for abstract offsets these agree only up to `++`-assoc,
  -- so the bridge needs the index casts `castW (domeq …)` (uncast sides are
  -- ill-typed).  Proven by collapsing `g-in≈pad`'s reassociators to single
  -- `castW`s via the §11d' algebra.

  -- the two index equalities (pure `++`-assoc), named.
  domeq : (pre a₁ mid a₂ r : List X)
        → (pre ++ (a₁ ++ mid)) ++ (a₂ ++ r) ≡ pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))
  domeq pre a₁ mid a₂ r =
    trans (++-assoc pre (a₁ ++ mid) (a₂ ++ r))
          (cong (pre ++_) (++-assoc a₁ mid (a₂ ++ r)))

  -- `reassocF`/`reassocB` (at any offset `x`) collapse to single domain/codomain
  -- casts; the `-in`/`-out` sites are the `a₁`/`b₁` specialisations.
  reassocF≈castW :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂) (x : List X)
    → Frame.reassocF pre mid r f g x
      ≈Term castW (sym (domeq pre x mid a₂ r))
  reassocF≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g x =
    assocTower≈castW pre x mid (a₂ ++ r)

  reassocB≈castW :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂) (x : List X)
    → Frame.reassocB pre mid r f g x
      ≈Term castW (domeq pre x mid b₂ r)
  reassocB≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g x =
    assocTower⁻≈castW pre x mid (b₂ ++ r)

  -- core bridge: frame's `g-in` = clean `pad` at offset `pre++(a₁++mid)`,
  -- conjugated by index casts.  From `g-in≈pad` by collapsing its reassociators.
  fx-clean⇒g-in-core :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.g-in pre mid r f g
      ≈Term castW (domeq pre a₁ mid b₂ r)
          ∘ pad (pre ++ (a₁ ++ mid)) r (⟦box⟧ g)
          ∘ castW (sym (domeq pre a₁ mid a₂ r))
  fx-clean⇒g-in-core pre mid r {a₁} {b₁} {a₂} {b₂} f g =
    Frame.g-in≈pad pre mid r f g
      ○ (reassocB≈castW pre mid r f g a₁
           ⟩∘⟨ refl⟩∘⟨ reassocF≈castW pre mid r f g a₁)

  --------------------------------------------------------------------------------
  -- 11e-out. The mirror g-out re-cleaning (a₁ ↦ b₁)
  --------------------------------------------------------------------------------
  -- Same as the g-in side at offset `b₁`: `g-out` = clean `pad (pre++(b₁++mid))`
  -- conjugated by index casts, making the SORTED (swap-output) g-layer a clean
  -- `pad` again.
  fy-sorted⇒g-out-core :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.g-out pre mid r f g
      ≈Term castW (domeq pre b₁ mid b₂ r)
          ∘ pad (pre ++ (b₁ ++ mid)) r (⟦box⟧ g)
          ∘ castW (sym (domeq pre b₁ mid a₂ r))
  fy-sorted⇒g-out-core pre mid r {a₁} {b₁} {a₂} {b₂} f g =
    Frame.g-out≈pad pre mid r f g
      ○ (reassocB≈castW pre mid r f g b₁
           ⟩∘⟨ refl⟩∘⟨ reassocF≈castW pre mid r f g b₁)

  --------------------------------------------------------------------------------
  -- 11e''. The full clean ⇒ frame bridge
  --------------------------------------------------------------------------------
  -- For a matched `LeftFit`, the clean head pair (fx-then-fy, `castMid` the ★
  -- wiring transport between fx's clean codomain and fy's clean domain) equals
  -- the frame's `input-O` conjugated by the domain index cast.  The clean
  -- fy-layer is DEFINITIONALLY `Frame.f-out`.
  fx-clean⇒g-in :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy) {M rest}
      (wTail : Wired (LeftFrame.N₃ fit) rest M)
    → ⟦ wTail ⟧W
        ∘ Frame.f-out (LeftFit.P fit) (LeftFit.mid fit) (LeftFit.s fit) fy fx
        ∘ castW (domeq (LeftFit.P fit) ay (LeftFit.mid fit) bx (LeftFit.s fit))
        ∘ pad (LeftFit.P fit ++ (ay ++ LeftFit.mid fit)) (LeftFit.s fit) (⟦box⟧ fx)
      ≈Term ⟦ LeftFrame.input-O fit wTail ⟧O
        ∘ castW (domeq (LeftFit.P fit) ay (LeftFit.mid fit) ax (LeftFit.s fit))
  fx-clean⇒g-in {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
                (leftFit P mid s refl refl refl refl)
                {M} {rest} wTail =
    pushʳ (pushʳ bridge) ○ (⟺ assoc ⟩∘⟨refl)
    where
      module F = Frame P mid s fy fx
      castMidB = castW (domeq P ay mid bx s)
      castDom  = castW (domeq P ay mid ax s)
      -- insert the inverse-cast pair on the right, then fold the core bridge.
      bridge : castMidB ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
             ≈Term F.g-in ∘ castDom
      bridge = insertʳ (castW-sym-r (domeq P ay mid ax s))
             ○ ((assoc ○ ⟺ (fx-clean⇒g-in-core P mid s fy fx)) ⟩∘⟨refl)

  --------------------------------------------------------------------------------
  -- 11e'''. The autonomous DiagU swap soundness
  --------------------------------------------------------------------------------
  -- Chaining the clean⇒frame bridge with `input⇒sorted`: the CLEAN (fx-then-fy)
  -- head order equals the frame's SORTED order, modulo the domain index cast.
  diagU-swap-sound :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy) {M rest}
      (wTail : Wired (LeftFrame.N₃ fit) rest M)
    → ⟦ wTail ⟧W
        ∘ Frame.f-out (LeftFit.P fit) (LeftFit.mid fit) (LeftFit.s fit) fy fx
        ∘ castW (domeq (LeftFit.P fit) ay (LeftFit.mid fit) bx (LeftFit.s fit))
        ∘ pad (LeftFit.P fit ++ (ay ++ LeftFit.mid fit)) (LeftFit.s fit) (⟦box⟧ fx)
      ≈Term ⟦ LeftFrame.sorted-O fit wTail ⟧O
        ∘ castW (domeq (LeftFit.P fit) ay (LeftFit.mid fit) ax (LeftFit.s fit))
  diagU-swap-sound fit wTail =
    fx-clean⇒g-in fit wTail ○ (sound (LeftFrame.input⇒sorted fit wTail) ⟩∘⟨refl)

  --------------------------------------------------------------------------------
  -- 11f. subst-transport of a DiagU index
  --------------------------------------------------------------------------------
  -- A swap moves a clean DiagU off its left-nested index onto the right-nested
  -- one (they differ by `domeq`, NON-`refl` for abstract offsets), so the
  -- swapped sub-diagram is transported along that `≡`; its interpretation is
  -- the original conjugated by `castW`s on both endpoints.

  substDiagU : ∀ {m n : List X} → m ≡ n → DiagU m → DiagU n
  substDiagU refl d = d

  substDiagU-out : ∀ {m n : List X} (e : m ≡ n) (d : DiagU m)
                 → out (substDiagU e d) ≡ out d
  substDiagU-out refl d = refl

  ⟦substDiagU⟧ : ∀ {m n : List X} (e : m ≡ n) (d : DiagU m)
              → ⟦ substDiagU e d ⟧ ∘ castW e
                ≈Term castW (sym (substDiagU-out e d)) ∘ ⟦ d ⟧
  ⟦substDiagU⟧ refl d = idʳ ○ ⟺ idˡ

  --------------------------------------------------------------------------------
  -- 11g. The genuine clean DiagU head swap
  --------------------------------------------------------------------------------
  -- The swapped diagram is fy-first then fx, both clean `pad`-layers, with the
  -- inter-layer `++`-assoc re-indexing absorbed by `substDiagU` along `domeq`
  -- (soundness `⟦substDiagU⟧`).  Litmus: `Categories.SolverNormalizeTests`.

  -- the swapped clean DiagU on the right-nested input index N₀: fy at offset P
  -- (= `f-in`), then fx at `P++(by++mid)` (= re-cleaned `g-out`); `dSorted` is
  -- the tail at the swapped-output index.
  swapHeadD-out :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy)
    → DiagU ((LeftFit.P fit ++ (by ++ LeftFit.mid fit)) ++ (bx ++ LeftFit.s fit))
    → DiagU (LeftFrame.N₀ fit)
  swapHeadD-out {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
                (leftFit P mid s refl refl refl refl) dSorted =
    P ▸ (mid ++ (ax ++ s)) ∷ fy
      ⟨ substDiagU (domeq P by mid ax s)
          ((P ++ (by ++ mid)) ▸ s ∷ fx ⟨ dSorted ⟩) ⟩

  -- soundness: the swapped interpretation = frame's SORTED order conjugated by
  -- the inter-layer cast (via the §11e-out g-out re-cleaning).
  swapHeadD-out-sound :
    ∀ {ax bx ay by} (P mid s : List X) (fx : Mor ax bx) (fy : Mor ay by)
      (dSorted : DiagU ((P ++ (by ++ mid)) ++ (bx ++ s)))
    → castW (substDiagU-out (domeq P by mid ax s)
                  ((P ++ (by ++ mid)) ▸ s ∷ fx ⟨ dSorted ⟩))
        ∘ ⟦ swapHeadD-out (leftFit {fx = fx} {fy = fy} P mid s refl refl refl refl) dSorted ⟧
      ≈Term (⟦ dSorted ⟧ ∘ pad (P ++ (by ++ mid)) s (⟦box⟧ fx))
          ∘ castW (sym (domeq P by mid ax s))
          ∘ Frame.f-in P mid s fy fx
  swapHeadD-out-sound {ax} {bx} {ay} {by} P mid s fx fy dSorted =
    pullˡ key ○ assoc
    where
      module F = Frame P mid s fy fx
      innerD = (P ++ (by ++ mid)) ▸ s ∷ fx ⟨ dSorted ⟩
      inner  = substDiagU (domeq P by mid ax s) innerD
      out-eq = substDiagU-out (domeq P by mid ax s) innerD
      e      = domeq P by mid ax s
      -- insert the inverse-cast pair, absorb `substDiagU`, cancel the output cast.
      key : castW out-eq ∘ ⟦ inner ⟧ ≈Term ⟦ innerD ⟧ ∘ castW (sym e)
      key = insertʳ (castW-sym-r-flip e)
          ○ ((pullʳ (⟦substDiagU⟧ e innerD)
                ○ cancelˡ (castW-sym-r-flip out-eq)) ⟩∘⟨refl)

  --------------------------------------------------------------------------------
  -- 11h. The INPUT clean DiagU + the abstract per-swap soundness
  --------------------------------------------------------------------------------
  -- Input order is fx-first then fy (inter-layer re-index absorbed by
  -- `substDiagU`).  `dInput`/`dSwapped` live at the SAME index N₀, so
  -- `⟦ input ⟧ ≈Term ⟦ swapped ⟧` is the honest per-swap soundness
  -- (litmus `litDiagUSwap` in `Categories.SolverNormalizeTests`).

  -- the INPUT clean DiagU: fx fires FIRST, then fy.
  dInput : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
           (fit : LeftFit px sx py sy fx fy)
         → DiagU (LeftFrame.N₃ fit)
         → DiagU (LeftFrame.N₀ fit)
  dInput {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
         (leftFit P mid s refl refl refl refl) dRest =
    substDiagU (domeq P ay mid ax s)
      ((P ++ (ay ++ mid)) ▸ s ∷ fx
        ⟨ substDiagU (sym (domeq P ay mid bx s))
            (P ▸ (mid ++ (bx ++ s)) ∷ fy ⟨ dRest ⟩) ⟩)

  -- the SWAPPED clean DiagU: fy (left box) fires FIRST, then fx.
  dSwapped : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
             (fit : LeftFit px sx py sy fx fy)
           → DiagU (LeftFrame.N₃ fit)
           → DiagU (LeftFrame.N₀ fit)
  dSwapped {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
           fit@(leftFit P mid s refl refl refl refl) dRest =
    swapHeadD-out fit (substDiagU (sym (domeq P by mid bx s)) dRest)

  --------------------------------------------------------------------------------
  -- 11h''. The abstract per-swap soundness
  --------------------------------------------------------------------------------
  -- `⟦ dInput ⟧ ≈Term ⟦ dSwapped ⟧`: input and swapped clean DiagUs at the same
  -- index N₀ have equal interpretations.  Proven by `dInput-frame`,
  -- `diagU-swap-sound`, `dSwapped-frame`, then `castW`-cancelling the common
  -- domain cast and the loop of output casts.

  -- the output index of `dInput`/`dSwapped` (both `= out dRest`), named so the
  -- soundness goal can carry the stuck-`out` cast explicitly.
  dInput-out :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy) (dRest : DiagU (LeftFrame.N₃ fit))
    → out (dInput fit dRest) ≡ out dRest
  dInput-out {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
             (leftFit P mid s refl refl refl refl) dRest =
    trans (substDiagU-out (domeq P ay mid ax s) _)
          (substDiagU-out (sym (domeq P ay mid bx s)) _)

  dSwapped-out :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy) (dRest : DiagU (LeftFrame.N₃ fit))
    → out (dSwapped fit dRest) ≡ out dRest
  dSwapped-out {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
               (leftFit P mid s refl refl refl refl) dRest =
    trans (substDiagU-out (domeq P by mid ax s) _)
          (substDiagU-out (sym (domeq P by mid bx s)) _)

  -- expand the INPUT diagram (pre-composed by the domain cast) to the frame
  -- INPUT composite, the LHS of `diagU-swap-sound`.
  dInput-frame :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy)
      (dRest : DiagU (LeftFrame.N₃ fit))
    → ⟦ dInput fit dRest ⟧
        ∘ castW (domeq (LeftFit.P fit) ay (LeftFit.mid fit) ax (LeftFit.s fit))
      ≈Term castW (sym (dInput-out fit dRest))
          ∘ ⟦ dRest ⟧
          ∘ Frame.f-out (LeftFit.P fit) (LeftFit.mid fit) (LeftFit.s fit) fy fx
          ∘ castW (domeq (LeftFit.P fit) ay (LeftFit.mid fit) bx (LeftFit.s fit))
          ∘ pad (LeftFit.P fit ++ (ay ++ LeftFit.mid fit)) (LeftFit.s fit) (⟦box⟧ fx)
  dInput-frame {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
               (leftFit P mid s refl refl refl refl) dRest =
    ⟦substDiagU⟧ e0 fxL
      ○ (refl⟩∘⟨ pushˡ subst1)
      ○ pullˡ (castW-∘ (sym o1) (sym o0)
                 ○ castW-irr _ (sym (dInput-out (leftFit P mid s refl refl refl refl) dRest)))
      ○ (refl⟩∘⟨ chainR)
    where
      module F = Frame P mid s fy fx
      e0   = domeq P ay mid ax s
      e1   = sym (domeq P ay mid bx s)
      padfx = pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
      fyL  = P ▸ (mid ++ (bx ++ s)) ∷ fy ⟨ dRest ⟩
      fxL  = (P ++ (ay ++ mid)) ▸ s ∷ fx ⟨ substDiagU e1 fyL ⟩
      o0   = substDiagU-out e0 fxL
      o1   = substDiagU-out e1 fyL
      rhs1 = (⟦ dRest ⟧ ∘ F.f-out) ∘ castW (sym e1)
      chainR : rhs1 ∘ padfx
             ≈Term ⟦ dRest ⟧ ∘ (F.f-out ∘ (castW (domeq P ay mid bx s) ∘ padfx))
      chainR = assoc ○ assoc
        ○ (refl⟩∘⟨ refl⟩∘⟨ (castW-irr (sym e1) (domeq P ay mid bx s) ⟩∘⟨refl))
      subst1 : ⟦ substDiagU e1 fyL ⟧
             ≈Term castW (sym o1) ∘ rhs1
      subst1 = castW-cancelʳ e1
        (⟦substDiagU⟧ e1 fyL ○ insertʳ (castW-sym-r e1) ○ (assoc ⟩∘⟨refl))

  --------------------------------------------------------------------------------
  -- 11h'''. Expansion of `⟦ dSwapped ⟧` to the frame SORTED ordering
  --------------------------------------------------------------------------------
  -- From `swapHeadD-out-sound` by re-cleaning `g-out` (`fy-sorted⇒g-out-core`),
  -- absorbing the inner `substDiagU`, and bridging `⟦dRest⟧ ≈ ⟦fromDiagU-W dRest⟧W`.
  dSwapped-frame :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy)
      (dRest : DiagU (LeftFrame.N₃ fit))
    → castW (dSwapped-out fit dRest) ∘ ⟦ dSwapped fit dRest ⟧
      ≈Term ⟦ LeftFrame.sorted-O fit (fromDiagU-W dRest) ⟧O
  dSwapped-frame {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
                 (leftFit P mid s refl refl refl refl) dRest =
    pushˡ (castW-irr _ (trans ohd o'') ○ ⟺ (castW-∘ ohd o''))
      ○ (refl⟩∘⟨ (swapHeadD-out-sound P mid s fx fy dSorted
                    ○ ⟺ assoc ○ (gpart ⟩∘⟨refl) ○ assoc))
      ○ cancelˡ (castW-sym-r-flip o'')
    where
      module F = Frame P mid s fy fx
      e'      = domeq P by mid ax s
      ebx     = domeq P by mid bx s
      padfx'  = pad (P ++ (by ++ mid)) s (⟦box⟧ fx)
      dSorted = substDiagU (sym ebx) dRest
      innerD' = (P ++ (by ++ mid)) ▸ s ∷ fx ⟨ dSorted ⟩
      ohd     = substDiagU-out e' innerD'
      o''     = substDiagU-out (sym ebx) dRest
      dS : ⟦ dSorted ⟧
         ≈Term (castW (sym o'') ∘ ⟦ fromDiagU-W dRest ⟧W) ∘ castW ebx
      dS = castW-cancelʳ (sym ebx)
        (⟦substDiagU⟧ (sym ebx) dRest
          ○ (refl⟩∘⟨ ⟺ (fromDiagU-sound dRest))
          ○ insertʳ (castW-sym-r-flip ebx))
      gpart : (⟦ dSorted ⟧ ∘ padfx') ∘ castW (sym e')
            ≈Term castW (sym o'') ∘ (⟦ fromDiagU-W dRest ⟧W ∘ F.g-out)
      gpart = ((dS ⟩∘⟨refl) ⟩∘⟨refl)
            ○ assoc ○ assoc
            ○ (refl⟩∘⟨ ⟺ (fy-sorted⇒g-out-core P mid s fy fx))
            ○ assoc

  --------------------------------------------------------------------------------
  -- 11h''''. The assembled abstract per-swap soundness
  --------------------------------------------------------------------------------
  -- `castW out-eq ∘ ⟦ dInput ⟧ ≈Term ⟦ dSwapped ⟧`, up to the stuck-`out` cast.
  -- Chains `dInput-frame`, `diagU-swap-sound` (= `two-box-swap`), `dSwapped-frame`;
  -- cancels the shared domain cast and the loop of output casts.
  diagU-swap-soundD :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy)
      (dRest : DiagU (LeftFrame.N₃ fit))
    → castW (trans (dInput-out fit dRest) (sym (dSwapped-out fit dRest)))
        ∘ ⟦ dInput fit dRest ⟧
      ≈Term ⟦ dSwapped fit dRest ⟧
  diagU-swap-soundD {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
                    (leftFit P mid s refl refl refl refl) dRest =
    castW-cancelʳ (domeq P ay mid ax s)
      (assoc
        ○ (refl⟩∘⟨ (dInput-frame fit dRest
             ○ (refl⟩∘⟨ (FC≈sorted ○ (dSwapped-frame-rearr ⟩∘⟨refl)))))
        ○ castLoop)
    where
      fit = leftFit {fx = fx} {fy = fy} P mid s refl refl refl refl
      cax = castW (domeq P ay mid ax s)
      cbx = castW (domeq P ay mid bx s)
      diO = dInput-out fit dRest
      dsO = dSwapped-out fit dRest
      oeq = trans diO (sym dsO)
      dSw = dSwapped fit dRest
      wTail = fromDiagU-W dRest
      sortedO = LeftFrame.sorted-O fit wTail
      module F = Frame P mid s fy fx
      FC = ⟦ dRest ⟧ ∘ (F.f-out ∘ (cbx ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)))
      FC≈sorted : FC ≈Term ⟦ sortedO ⟧O ∘ cax
      FC≈sorted =
        (⟺ (fromDiagU-sound dRest) ⟩∘⟨refl) ○ diagU-swap-sound fit wTail
      dSwapped-frame-rearr : ⟦ sortedO ⟧O ≈Term castW dsO ∘ ⟦ dSw ⟧
      dSwapped-frame-rearr = ⟺ (dSwapped-frame fit dRest)
      -- the loop of output casts collapses to id, leaving ⟦dSw⟧ ∘ cax.
      castLoop : castW oeq ∘ (castW (sym diO) ∘ ((castW dsO ∘ ⟦ dSw ⟧) ∘ cax))
               ≈Term ⟦ dSw ⟧ ∘ cax
      castLoop = (refl⟩∘⟨ ((refl⟩∘⟨ assoc) ○ ⟺ assoc)) ○ cancelˡ loopId
        where
          -- the genuine castW-∘ content: the three output casts compose to id.
          loopId : castW oeq ∘ (castW (sym diO) ∘ castW dsO) ≈Term id
          loopId = (refl⟩∘⟨ castW-∘ dsO (sym diO))
                 ○ castW-∘ (trans dsO (sym diO)) oeq
                 ○ castW-irr _ refl

  --------------------------------------------------------------------------------
  -- 12. The autonomous firing DiagU sort (needs `DecidableEquality X`)
  --------------------------------------------------------------------------------
  -- With `DecEq X` we DECIDE a `LeftFit` by `List`-splitting the offset lists at
  -- the box-domain lengths.  `swapHeadD` fires the clean swap; the multi-step
  -- fuel loop lives in §12d's generic `Driver` (`normFuelWith`), driven by each
  -- front-end's per-position oracle.
  module SortD where

    -- derived decidable equality on offsets.
    _≟L_ : DecidableEquality (List X)
    _≟L_ = ≡-dec _≟X_

    stripPrefix : (p xs : List X) → Maybe (Σ[ ys ∈ List X ] xs ≡ p ++ ys)
    stripPrefix []       xs       = just (xs , refl)
    stripPrefix (_ ∷ _)  []       = nothing
    stripPrefix (x ∷ p)  (y ∷ xs) = case x ≟X y of λ where
      (no  _)   → nothing
      (yes x≡y) → Maybe.map (λ (ys , eq) → ys , cong₂ _∷_ (sym x≡y) eq)
                            (stripPrefix p xs)

    --------------------------------------------------------------------------------
    -- 12a. The decidable `LeftFit` recogniser
    --------------------------------------------------------------------------------
    -- Set `P := py`, `s := sx`, recover `mid` by stripping `py ++ ay` off `px`,
    -- and confirm `sy ≡ mid ++ (bx ++ sx)` by `_≟L_`.  `nothing` when the splits
    -- don't fit (overlap / dependent / wrong orientation).
    leftFit? : ∀ {ax bx ay by} (px sx py sy : List X)
               (fx : Mor ax bx) (fy : Mor ay by)
             → Maybe (LeftFit px sx py sy fx fy)
    leftFit? {ax} {bx} {ay} {by} px sx py sy fx fy =
      stripPrefix py px >>= λ (r1 , px≡) →
      stripPrefix ay r1 >>= λ (mid , r1≡) →
      case sy ≟L (mid ++ (bx ++ sx)) of λ where
        (no  _)   → nothing
        (yes sy≡) →
          just (leftFit py mid sx
                  (trans px≡ (cong (py ++_) r1≡))   -- px ≡ py ++ (ay ++ mid)
                  refl                               -- sx ≡ sx
                  refl                               -- py ≡ py
                  sy≡)                               -- sy ≡ mid ++ (bx ++ sx)

    --------------------------------------------------------------------------------
    -- 12b. `swapHeadD` — the firing swap on explicit head-pair data
    --------------------------------------------------------------------------------
    -- A `DiagU` erases the inter-layer wiring into a non-definitional `++`-assoc
    -- index, so an abstract 2-layer head cannot be destructured by unification;
    -- hence `swapHeadD` consumes the head pair as offsets/boxes + sub-diagram
    -- `dRest` (exactly what `leftFit?` recognises), and `dInput`/`dSwapped` carry
    -- the wiring via `substDiagU`.
    HeadSwapD : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
                (fit : LeftFit px sx py sy fx fy) → DiagU (LeftFrame.N₃ fit) → Set
    HeadSwapD fit dRest =
      Σ[ dSw ∈ DiagU (LeftFrame.N₀ fit) ]
        Σ[ oeq ∈ (out (dInput fit dRest) ≡ out dSw) ]
          (castW oeq ∘ ⟦ dInput fit dRest ⟧ ≈Term ⟦ dSw ⟧)

    -- always fires on a recognised fit (left-of ⟹ out of order).
    swapHeadD : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
                (fit : LeftFit px sx py sy fx fy) (dRest : DiagU (LeftFrame.N₃ fit))
              → HeadSwapD fit dRest
    swapHeadD fit dRest =
      dSwapped fit dRest
      , trans (dInput-out fit dRest) (sym (dSwapped-out fit dRest))
      , diagU-swap-soundD fit dRest

    --------------------------------------------------------------------------------
    -- 12c. `normalizeD` — the one-step swap kernel on a recognised head
    --------------------------------------------------------------------------------
    -- Multi-step chaining over a whole `DiagU n` is NOT done at this typed
    -- interface: a 2-layer head of the SWAPPED output is re-indexed (by
    -- `substDiagU` along `domeq`), so it cannot be destructured here.  §12d's
    -- generic `Driver` works on the untyped `DiagU n` and chains abstractly;
    -- this kernel documents the per-swap content.
    normalizeD : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
                 → ℕ
                 → (fit : LeftFit px sx py sy fx fy) (dRest : DiagU (LeftFrame.N₃ fit))
                 → DiagU (LeftFrame.N₀ fit)
    normalizeD zero    fit dRest = dInput fit dRest        -- out of fuel: leave the head
    normalizeD (suc _) fit dRest = dSwapped fit dRest      -- fire one genuine bubble swap

    normalizeD-sound : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
                       (k : ℕ)
                       (fit : LeftFit px sx py sy fx fy) (dRest : DiagU (LeftFrame.N₃ fit))
                     → Σ[ oeq ∈ (out (dInput fit dRest) ≡ out (normalizeD k fit dRest)) ]
                         (castW oeq ∘ ⟦ dInput fit dRest ⟧ ≈Term ⟦ normalizeD k fit dRest ⟧)
    normalizeD-sound zero    fit dRest = refl , idˡ
    normalizeD-sound (suc _) fit dRest =
      trans (dInput-out fit dRest) (sym (dSwapped-out fit dRest))
      , diagU-swap-soundD fit dRest

    --------------------------------------------------------------------------------
    -- 12d. The generic driver, parametrised over a one-step oracle
    --------------------------------------------------------------------------------
    -- Both `SolverFrontend.Decide` and `SolverSigma.Decide` run the same
    -- fuel-driven bubble-sort loop around a per-position oracle; this factors
    -- out everything INDEPENDENT of that oracle, each `Decide` passing its own
    -- `step?` to `normFuelWith`.

    -- canonical result type: a new diagram at the same input index + an
    -- output-equality proof + a semantic bridge.
    SwapRes : ∀ {n} → DiagU n → Set
    SwapRes {n} d = Σ[ d' ∈ DiagU n ] Σ[ oeq ∈ out d ≡ out d' ]
                      (castW oeq ∘ ⟦ d ⟧ ≈Term ⟦ d' ⟧)

    unwrapCast : ∀ {u v} {A} (e : u ≡ v)
                 {x : HomTerm A (wires u)} {y : HomTerm A (wires v)}
               → castW e ∘ x ≈Term y → x ≈Term castW (sym e) ∘ y
    unwrapCast refl eq = ⟺ idˡ ○ eq ○ ⟺ idˡ

    -- AMBIGUOUS when the reverse pair would also fit (mid ≡ [] ∧ by ≡ [] ∧
    -- ax ≡ []); such pairs are ordered by rank instead.
    ambiguous? : List X → List X → List X → Bool
    ambiguous? [] [] [] = true
    ambiguous? _  _  _  = false

    -- Fire one genuine swap on a recognised out-of-order head pair.
    fire : ∀ {ax bx ay by} {px sx py sy : List X}
           {fx : Mor ax bx} {fy : Mor ay by}
           (fit : LeftFit px sx py sy fx fy)
           (rest' : DiagU (py ++ (by ++ sy)))
           (meq : px ++ (bx ++ sx) ≡ py ++ (ay ++ sy))
         → SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) (py ▸ sy ∷ fy ⟨ rest' ⟩) ⟩)
    fire {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
         (leftFit P mid s refl refl refl refl) rest' meq
      rewrite ≡-irrelevantL meq (domeq P ay mid bx s)
      = d' , oeq , snd
      where
        fit' : LeftFit (P ++ (ay ++ mid)) s P (mid ++ (bx ++ s)) fx fy
        fit' = leftFit P mid s refl refl refl refl
        eᵒ = domeq P ay mid ax s
        dBody : DiagU ((P ++ (ay ++ mid)) ++ (ax ++ s))
        dBody = (P ++ (ay ++ mid)) ▸ s ∷ fx
                  ⟨ substDiagU (sym (domeq P ay mid bx s))
                      (P ▸ (mid ++ (bx ++ s)) ∷ fy ⟨ rest' ⟩) ⟩
        dIn = dInput fit' rest'
        dSw = dSwapped fit' rest'
        d' : DiagU ((P ++ (ay ++ mid)) ++ (ax ++ s))
        d' = substDiagU (sym eᵒ) dSw
        e₁ = sym (substDiagU-out eᵒ dBody)
        q  = trans (dInput-out fit' rest') (sym (dSwapped-out fit' rest'))
        e₃ = sym (substDiagU-out (sym eᵒ) dSw)
        oeq = trans e₁ (trans q e₃)
        snd : castW oeq ∘ ⟦ dBody ⟧ ≈Term ⟦ d' ⟧
        snd = begin
          castW oeq ∘ ⟦ dBody ⟧
            ≈⟨ castW-irr oeq (trans (trans e₁ q) e₃) ⟩∘⟨refl ⟩
          castW (trans (trans e₁ q) e₃) ∘ ⟦ dBody ⟧
            ≈⟨ pushˡ (⟺ (castW-∘ (trans e₁ q) e₃)) ⟩
          castW e₃ ∘ (castW (trans e₁ q) ∘ ⟦ dBody ⟧)
            ≈⟨ refl⟩∘⟨ pushˡ (⟺ (castW-∘ e₁ q)) ⟩
          castW e₃ ∘ (castW q ∘ (castW e₁ ∘ ⟦ dBody ⟧))
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟦substDiagU⟧ eᵒ dBody ⟨
          castW e₃ ∘ (castW q ∘ (⟦ dIn ⟧ ∘ castW eᵒ))
            ≈⟨ refl⟩∘⟨ pullˡ (diagU-swap-soundD fit' rest') ⟩
          castW e₃ ∘ (⟦ dSw ⟧ ∘ castW eᵒ)
            ≈⟨ pullˡ (⟺ (⟦substDiagU⟧ (sym eᵒ) dSw)) ⟩
          (⟦ d' ⟧ ∘ castW (sym eᵒ)) ∘ castW eᵒ
            ≈⟨ cancelʳ (castW-sym-r eᵒ) ⟩
          ⟦ d' ⟧ ∎

    -- `substDiagU (sym e)` expanded to a two-sided cast conjugation.
    substExpand : ∀ {m n : List X} (e : m ≡ n) (d : DiagU n)
                → ⟦ substDiagU (sym e) d ⟧
                  ≈Term castW (sym (substDiagU-out (sym e) d)) ∘ (⟦ d ⟧ ∘ castW e)
    substExpand refl d = ⟺ (idˡ ○ idʳ)

    -- Generic sound two-layer head REPLACEMENT: the head pair (g₁,g₂ bridged by
    -- `meq`) is replaced by (g₃,g₄ bridged by E₃), with re-indexings E₂/E₄ and a
    -- caller-supplied KEY equation between the two padded composites.
    fireRepl :
      ∀ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : List X}
        {p₁L s₁L p₂L s₂L : List X} (p₃L s₃L p₄L s₄L : List X)
        {g₁ : Mor a₁ b₁} {g₂ : Mor a₂ b₂}
        (g₃ : Mor a₃ b₃) (g₄ : Mor a₄ b₄)
        (rest' : DiagU (p₂L ++ (b₂ ++ s₂L)))
        (meq : p₁L ++ (b₁ ++ s₁L) ≡ p₂L ++ (a₂ ++ s₂L))
        (E₂ : p₄L ++ (b₄ ++ s₄L) ≡ p₂L ++ (b₂ ++ s₂L))
        (E₃ : p₃L ++ (b₃ ++ s₃L) ≡ p₄L ++ (a₄ ++ s₄L))
        (E₄ : p₁L ++ (a₁ ++ s₁L) ≡ p₃L ++ (a₃ ++ s₃L))
        (key : pad p₂L s₂L (⟦box⟧ g₂) ∘ castW meq ∘ pad p₁L s₁L (⟦box⟧ g₁)
               ≈Term castW E₂ ∘ pad p₄L s₄L (⟦box⟧ g₄) ∘ castW E₃
                     ∘ pad p₃L s₃L (⟦box⟧ g₃) ∘ castW E₄)
      → SwapRes (p₁L ▸ s₁L ∷ g₁ ⟨ substDiagU (sym meq) (p₂L ▸ s₂L ∷ g₂ ⟨ rest' ⟩) ⟩)
    fireRepl {a₁ = a₁} {p₁L = p₁L} {s₁L} {p₂L} {s₂L} p₃L s₃L p₄L s₄L
             {g₁} {g₂} g₃ g₄ rest' meq E₂ E₃ E₄ key
      = d' , oeq , snd
      where
        P₃ = pad p₃L s₃L (⟦box⟧ g₃)
        P₄ = pad p₄L s₄L (⟦box⟧ g₄)
        boxL   = p₂L ▸ s₂L ∷ g₂ ⟨ rest' ⟩
        dBody  = p₁L ▸ s₁L ∷ g₁ ⟨ substDiagU (sym meq) boxL ⟩
        inner₂ = substDiagU (sym E₂) rest'
        crossL = p₄L ▸ s₄L ∷ g₄ ⟨ inner₂ ⟩
        inner₃ = substDiagU (sym E₃) crossL
        slidL  = p₃L ▸ s₃L ∷ g₃ ⟨ inner₃ ⟩
        d' : DiagU (p₁L ++ (a₁ ++ s₁L))
        d' = substDiagU (sym E₄) slidL
        o₁ = substDiagU-out (sym meq) boxL
        o₂ = substDiagU-out (sym E₂) rest'
        o₃ = substDiagU-out (sym E₃) crossL
        o₄ = substDiagU-out (sym E₄) slidL
        cAll = trans (trans (sym o₂) (sym o₃)) (sym o₄)
        oeq : out dBody ≡ out d'
        oeq = trans o₁ cAll
        M = ⟦ rest' ⟧ ∘ (castW E₂ ∘ (P₄ ∘ (castW E₃ ∘ (P₃ ∘ castW E₄))))
        lemA : ⟦ dBody ⟧ ≈Term castW (sym o₁) ∘ M
        lemA = (substExpand meq boxL ⟩∘⟨refl) ○ assoc²βε
             ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ key)))
        lemB : ⟦ d' ⟧ ≈Term castW cAll ∘ M
        lemB = substExpand E₄ slidL
             ○ (refl⟩∘⟨ assoc)
             ○ (refl⟩∘⟨ ((substExpand E₃ crossL ⟩∘⟨refl) ○ assoc²βε))
             ○ (refl⟩∘⟨ refl⟩∘⟨
                  (assoc ○ (substExpand E₂ rest' ⟩∘⟨refl) ○ assoc²βε))
             ○ (refl⟩∘⟨ pullˡ (castW-∘ (sym o₂) (sym o₃)))
             ○ pullˡ (castW-∘ (trans (sym o₂) (sym o₃)) (sym o₄))
        snd : castW oeq ∘ ⟦ dBody ⟧ ≈Term ⟦ d' ⟧
        snd = (refl⟩∘⟨ lemA)
            ○ pullˡ (castW-∘ (sym o₁) oeq)
            ○ (castW-irr (trans (sym o₁) oeq) cAll ⟩∘⟨refl)
            ○ ⟺ lemB

    -- Lift a tail SwapRes under a head layer (same input index, no transport).
    lift∷ : ∀ {a b} (px sx : List X) (fx : Mor a b)
            {rest rest' : DiagU (px ++ (b ++ sx))}
            (oeq : out rest ≡ out rest')
          → castW oeq ∘ ⟦ rest ⟧ ≈Term ⟦ rest' ⟧
          → castW oeq ∘ ⟦ px ▸ sx ∷ fx ⟨ rest ⟩ ⟧
            ≈Term ⟦ px ▸ sx ∷ fx ⟨ rest' ⟩ ⟧
    lift∷ px sx fx oeq snd = pullˡ snd

    -- Chain two consecutive SwapRes results.
    swapTrans : ∀ {n} {d d' d'' : DiagU n}
                (oeq : out d ≡ out d') (oeq' : out d' ≡ out d'')
              → castW oeq  ∘ ⟦ d  ⟧ ≈Term ⟦ d'  ⟧
              → castW oeq' ∘ ⟦ d' ⟧ ≈Term ⟦ d'' ⟧
              → castW (trans oeq oeq') ∘ ⟦ d ⟧ ≈Term ⟦ d'' ⟧
    swapTrans oeq oeq' p q =
      pushˡ (⟺ (castW-∘ oeq oeq')) ○ (refl⟩∘⟨ p) ○ q

    depthD : ∀ {n} → DiagU n → ℕ
    depthD ([]_ n)            = zero
    depthD (_ ▸ _ ∷ _ ⟨ d ⟩) = suc (depthD d)

    -- Fuel-bounded normalizer driven by a caller-supplied one-step function.
    -- `nothing` from `step` ⟹ the input diagram with a trivial witness.
    normFuelWith : ∀ {n}
                 → (∀ {m} (d : DiagU m) → Maybe (SwapRes d))
                 → ℕ → (d : DiagU n) → SwapRes d
    normFuelWith _    zero    d = d , refl , idˡ
    normFuelWith step (suc k) d = case step d of λ where
      nothing                 → d , refl , idˡ
      (just (d' , oeq , snd)) →
        let (d'' , oeq' , snd') = normFuelWith step k d'
        in  d'' , trans oeq oeq' , swapTrans oeq oeq' snd snd'

    --------------------------------------------------------------------------------
    -- 12e. The generic interchange oracle + first-applicable-position loop
    --------------------------------------------------------------------------------
    -- `interchangeGo` (the per-position recogniser shared by both front-ends;
    -- `rank` passed as an ORDINARY argument so it does not block reduction)
    -- tries `leftFit?` and fires when the pair is unambiguous or the rank
    -- tiebreak demands it.  `stepWith` tries the oracle at the head, else
    -- recurses (via `lift∷`) into the tail.
    interchangeGo : (rank : ∀ {a b} → Mor a b → ℕ)
                  → ∀ {ax bx} (px sx : List X) (fx : Mor ax bx)
                    {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
                  → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
    interchangeGo rank px sx fx ([]_ m) meq = nothing
    interchangeGo rank {ax} {bx} px sx fx (_▸_∷_⟨_⟩ {ay} {by} py sy fy rest') meq =
      case leftFit? px sx py sy fx fy of λ where
        nothing    → nothing
        (just fit) →
          if not (ambiguous? ax by (LeftFit.mid fit)) ∨ (rank fy <ᵇ rank fx)
            then just (fire fit rest' meq)
            else nothing

    stepWith : (oneStep : ∀ {ax bx} (px sx : List X) (fx : Mor ax bx)
                          {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
                        → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩)))
             → ∀ {n} (d : DiagU n) → Maybe (SwapRes d)
    stepWith oneStep ([]_ n) = nothing
    stepWith oneStep (px ▸ sx ∷ fx ⟨ rest ⟩) =
      oneStep px sx fx rest refl <∣>
      Maybe.map
        (λ { (rest' , oeq , snd) →
             px ▸ sx ∷ fx ⟨ rest' ⟩ , oeq , lift∷ px sx fx oeq snd })
        (stepWith oneStep rest)

-- Compatibility wrapper: `NormalizeI` at the standard interpretation
-- `Untyped.⟦box⟧` (= `var ∘ box`).
module Normalize (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
                 (Mor : List X → List X → Set) where

  open Untyped v {X} Mor using (⟦box⟧)
  open NormalizeI v {X} _≟X_ Mor ⟦box⟧ public
