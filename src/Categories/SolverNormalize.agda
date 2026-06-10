{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Normalising untyped monoidal diagrams by reordering independent boxes.
--
-- A diagram (`Categories.DiagramRewriteUntyped.DiagU`) is a list of boxes, each
-- placed at a flat wire-offset.  Two boxes occupying disjoint, non-crossing
-- wire ranges are *independent*: swapping their firing order preserves the
-- interpretation `⟦_⟧`.  That single-pair fact is `TwoBoxSwap.two-box-swap`,
-- which is σ-free (pure interchange / bifunctoriality).
--
-- The deliverable is the clean-DiagU swap engine `SortD` (§12): a decidable
-- recogniser `leftFit?` for an out-of-order independent head pair, the firing
-- swap `swapHeadD` with its per-swap soundness `diagU-swap-soundD` (proven by
-- conjugating `two-box-swap` with the `castW` object-transport algebra of
-- §11d'), and the one-step driver `normalizeD` — plus the `Normalize` wrapper
-- at the standard interpretation.  Everything is unconditional: no module
-- parameters beyond the box signature, no postulates.
--
-- DESIGN.  A verbatim transposition of two layers with absolute offsets is
-- ill-wired: after a box of a different width fires, the next box's absolute
-- offset shifts, so the equality the swap needs holds only up to
-- `++`-associativity, never definitionally.  The swap therefore BUILDS its
-- output with RECOMPUTED offsets (`dSwapped`), absorbing the non-definitional
-- re-indexing with `substDiagU`, and its soundness is discharged by reusing
-- `TwoBoxSwap.two-box-swap` together with the offset-reframing bridges
-- `TwoBoxSwap.g-out≈pad` / `g-in≈pad` (the `assocW`/`assocW⁻` reassociators,
-- collapsed to `castW` transports).
--------------------------------------------------------------------------------

module Categories.SolverNormalize where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (≡-dec; ++-assoc)
open import Data.Maybe as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; Σ; Σ-syntax)
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

  -- UIP on the wire lists, via Hedberg (decidable equality), --without-K.
  private
    ≡-irrelevantL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevantL = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)

  open UntypedI v {X} Mor ⟦box⟧
  open FreeMonoidalHelper v X using (ObjTerm)
  open FreeMonoidalHelper.Mor v X mor
  open ≈R

  -- stock associativity/cancellation combinators (same idiom as
  -- DiagramRewriteUntyped/SolverReflect): plain non-public opens, proofs-only.
  open MR FreeMonoidal
    using (pullˡ; pullʳ; pushˡ; pushʳ; cancelˡ; insertʳ)
  open MonR Monoidal-FreeMonoidal
    using (refl⟩⊗⟨_)

  --------------------------------------------------------------------------------
  -- 1. Layers and wired layer-lists.
  --
  -- A `Layer` records its flat input/output wire-lists `L-in`/`L-out` together
  -- with an arbitrary interpretation `⟦L⟧` — a `HomTerm (wires L-in) (wires
  -- L-out)`.  In the canonical case the interpretation is a genuine flat `pad`
  -- of a box at a flat offset (`mk-pad` below); but the carrier is deliberately
  -- general so that the *output* of an adjacent swap — whose right box becomes a
  -- pad conjugated by the `assocW`/`assocW⁻` reassociators (see
  -- `TwoBoxSwap.g-out≈pad`) — is also expressible as a `Layer`, with its
  -- well-typedness under our control rather than an uninhabitable premise.
  --
  -- Crucially we never transpose `Layer`s verbatim: the swap (§11g) BUILDS the
  -- swapped layers (with recomputed offsets / reframed interpretations) from
  -- scratch.
  --------------------------------------------------------------------------------

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
  -- 2. Wired layer-lists and the fold interpretation.
  --
  -- `Wired N ls M` certifies that the layers `ls`, fired head-first, carry the
  -- flat layout from `N` to `M`: each layer's `L-in` equals the current layout
  -- and its `L-out` is the next layout.  The fold `⟦_⟧W` is head-applied-first,
  -- exactly like `DiagU`'s `⟦_⟧`.
  --------------------------------------------------------------------------------

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
  -- 2'. Witness-carrying swap steps.
  --
  -- A swap step `o ⇒W o'` is an ordering rewrite that already carries a proof
  -- that the two interpretations agree.  Each genuine adjacent-disjoint swap is
  -- realised as such a step by `LeftFrame.input⇒sorted` (§11c), whose soundness
  -- is the single load-bearing lemma (reusing `TwoBoxSwap`).
  --------------------------------------------------------------------------------

  record _⇒W_ {N M : List X} (o o' : Ordering N M) : Set where
    constructor wstep
    field
      sound : ⟦ o ⟧O ≈Term ⟦ o' ⟧O

  open _⇒W_ public

  --------------------------------------------------------------------------------
  -- 3. The four canonical layers of an adjacent disjoint pair, from a frame.
  --
  -- For a frame  P | a₁/b₁ | mid | a₂/b₂ | r  with box `f : Mor a₁ b₁` in the
  -- left slot and `g : Mor a₂ b₂` in the right slot, the two firing orders use
  -- the four `TwoBoxSwap` layers, packaged as `Layer`s:
  --
  --   * `f-in-layer` / `f-out-layer` — genuine flat `pad`s of f (at offset P);
  --   * `g-out-layer` / `g-in-layer` — the g-layers, which are flat `pad`s of g
  --     at the shifted offset conjugated by the structural reassociators
  --     (`TwoBoxSwap.g-out` / `g-in`), expressed as `Layer`s via the general
  --     interpretation field.
  --
  -- "f then g" (the *before* head-pair) = g-out-layer after f-in-layer, whose
  -- composite is `f-first = g-out ∘ f-in`.  "g then f" (the *after* head-pair)
  -- = f-out-layer after g-in-layer, composite `g-first = f-out ∘ g-in`.  The two
  -- head-pairs share both flat endpoints DEFINITIONALLY, and `two-box-swap`
  -- gives their interpretations are `≈Term`-equal.
  --------------------------------------------------------------------------------

  module Frame (P mid r : List X) {a₁ b₁ a₂ b₂ : List X}
               (f : Mor a₁ b₁) (g : Mor a₂ b₂) where

    open TwoBoxSwap P mid r f g public

    -- common input / output (definitional) and the g-out output (= N₃).
    N₀ : List X
    N₀ = P ++ (a₁ ++ (mid ++ (a₂ ++ r)))

    N₃ : List X
    N₃ = P ++ (b₁ ++ (mid ++ (b₂ ++ r)))

    L-out-g : List X
    L-out-g = N₃

    -- the four layers (note the shared definitional endpoints):
    --   N₀  common input ;  N₃  common output
    f-in-layer : Layer
    f-in-layer = mk-layer _ _ f-in

    g-out-layer : Layer
    g-out-layer = mk-layer _ _ g-out

    g-in-layer : Layer
    g-in-layer = mk-layer _ _ g-in

    f-out-layer : Layer
    f-out-layer = mk-layer _ _ f-out

    -- the two head-pairs are wired prefixes from the common input N₀ to the
    -- common output N₃; they extend any tail `Wired N₃ rest M`.
    before-wired : ∀ {M rest}
                 → Wired (L-out g-out-layer) rest M
                 → Wired (L-in f-in-layer) (f-in-layer ∷ g-out-layer ∷ rest) M
    before-wired wRest = f-in-layer ∷ (g-out-layer ∷ wRest)

    after-wired : ∀ {M rest}
                → Wired (L-out f-out-layer) rest M
                → Wired (L-in g-in-layer) (g-in-layer ∷ f-out-layer ∷ rest) M
    after-wired wRest = g-in-layer ∷ (f-out-layer ∷ wRest)

    -- THE LOAD-BEARING SOUNDNESS: the before head-pair and the after head-pair,
    -- extended by the SAME tail, have `≈Term`-equal interpretations.  The
    -- categorical core is exactly `two-box-swap`; the wrapping is congruence
    -- (`∘-resp-≈`) and associativity.  No σ; reuses `TwoBoxSwap.two-box-swap`
    -- (which itself bottoms out in `g-out≈pad` / bifunctoriality).
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
  -- 6. The `DiagU ↔ Ordering` bridge.
  --
  -- Each `DiagU` layer `pre ▸ suf ∷ f ⟨ d ⟩` is the canonical `mk-pad pre suf f`
  -- `Layer` (whose `⟦L⟧` is exactly `pad pre suf (⟦box⟧ f)`); the empty diagram
  -- `[]_ n` becomes the empty `Wired`.  Since `⟦_⟧W` folds head-applied-first
  -- with the SAME shape as `DiagU`'s `⟦_⟧`, the bridge soundness is definitional
  -- (`≈-Term-refl`).  This lets `reflect`'s `DiagU` output feed the `SortD`
  -- engine (§12), and the sorted result feed `SolverCompare`.
  --------------------------------------------------------------------------------

  -- the layer-list underlying a diagram
  fromDiagU-ls : ∀ {n} (d : DiagU n) → List Layer
  fromDiagU-ls ([]_ n)             = []
  fromDiagU-ls (pre ▸ suf ∷ f ⟨ d ⟩) = mk-pad pre suf f ∷ fromDiagU-ls d

  -- the wired layer-list underlying a diagram
  fromDiagU-W : ∀ {n} (d : DiagU n) → Wired n (fromDiagU-ls d) (out d)
  fromDiagU-W ([]_ n)             = []
  fromDiagU-W (pre ▸ suf ∷ f ⟨ d ⟩) = mk-pad pre suf f ∷ fromDiagU-W d

  -- bridge soundness: definitional (head-applied-first fold matches `⟦_⟧`).
  fromDiagU-sound : ∀ {n} (d : DiagU n) → ⟦ fromDiagU-W d ⟧W ≈Term ⟦ d ⟧
  fromDiagU-sound ([]_ n)             = ≈-Term-refl
  fromDiagU-sound (pre ▸ suf ∷ f ⟨ d ⟩) = fromDiagU-sound d ⟩∘⟨refl

  --------------------------------------------------------------------------------
  -- 8. (Open) canonicity / completeness.
  --
  -- Soundness of the swap engine below is unconditional; what remains OPEN is
  -- canonicity: that interchange-equal diagrams reach the SAME normal form (so
  -- that `SolverCompare`'s `_≟DiagU_` decides `≈Term`-equality).  This needs
  -- confluence of the bubble sort to a footprint-ordered normal form (canonical
  -- key = leftmost offset, deterministic tiebreak on the input width).
  --------------------------------------------------------------------------------

  --------------------------------------------------------------------------------
  -- 11. DiagU-level recognition: reading frame data off the boxes.
  --
  -- A `Layer` ERASES its `pre`/`suf`/box into the opaque `⟦L⟧`, so no recogniser
  -- can fire on a generic `Ordering`.  A `DiagU` layer `px ▸ sx ∷ fx ⟨ rest ⟩`
  -- does NOT: it carries the box `fx` (hence its `dom`/`cod`) and the flat
  -- offsets `px sx` explicitly.  So a recogniser CAN read off the offsets and
  -- decide independence/orientation.
  --
  -- We work on a head pair of a `DiagU`, i.e. on the constructor pattern
  --   px ▸ sx ∷ fx ⟨ py ▸ sy ∷ fy ⟨ rest ⟩ ⟩
  -- where `fx : Mor ax bx` fires FIRST and `fy : Mor ay by` SECOND.  The
  -- `DiagU` typing forces the inter-layer wiring DEFINITIONALLY:
  --
  --   py ++ (ay ++ sy)  ≡  px ++ (bx ++ sx)            -- (★)  the index of the
  --                                                    --      inner sub-diagram
  --------------------------------------------------------------------------------

  --------------------------------------------------------------------------------
  -- 11a. The LEFT-OF frame fit (the canonical / out-of-order case).
  --
  -- The head pair is OUT of canonical order exactly when the second box `fy`
  -- sits strictly LEFT of the first box `fx` on the shared wire context — i.e.
  -- after we *swap* them, `fy` (lower offset) comes first.  Equivalently, in
  -- the current `px ▸ sx ∷ fx ⟨ py ▸ sy ∷ fy ⟨…⟩ ⟩`, `fx` lives to the right of
  -- `fy`, so `fy`'s block lies inside `px`'s PREFIX.
  --
  -- We capture "fits a left-of frame with f = fy (left) and g = fx (right)"
  -- as the data of three idle blocks `P mid s` together with the propositional
  -- witnesses that the two layers' offsets factor through the 4-block frame
  --   P ++ (ay ++ (mid ++ (ax ++ s)))            -- fy in slot 1, fx in slot 2.
  --
  -- Concretely, with `fy` the LEFT box (slot 1, dom ay/cod by) and `fx` the
  -- RIGHT box (slot 2, dom ax/cod bx), the frame's two firing orders are:
  --
  --   * "fy then fx"  (canonical, sorted)  = Frame.before-O … fy fx
  --   * "fx then fy"  (the input order)     = Frame.after-O  … fy fx
  --
  -- so the INPUT diagram's head pair is the frame's *after* pair and the sorted
  -- output is the frame's *before* pair — the swap step runs `after ⇒ before`
  -- by `≈-Term-sym` of `head-swap-sound`.
  --
  -- The data witnessing the fit:
  record LeftFit {ax bx ay by : List X}
                 (px sx py sy : List X) (fx : Mor ax bx) (fy : Mor ay by) : Set where
    constructor leftFit
    field
      P mid s : List X
      -- fx (fires FIRST) is the RIGHT box (slot 2).  When it fires fy has NOT
      -- yet fired, so fx sees `ay` (fy's dom) in slot 1:
      px≡   : px ≡ P ++ (ay ++ mid)
      sx≡   : sx ≡ s
      -- fy (fires SECOND) is the LEFT box (slot 1).  By now fx HAS fired, so
      -- fy sees `bx` (fx's cod) in slot 2:
      py≡   : py ≡ P
      sy≡   : sy ≡ mid ++ (bx ++ s)

  --------------------------------------------------------------------------------
  -- 11b. Decidable recognition.
  --
  -- Given the four offset lists and the two boxes, we try to build a `LeftFit`.
  -- This is pure `List`-prefix surgery driven by lengths; we expose it as a
  -- `Maybe`.  (A `nothing` result simply means "not an out-of-order independent
  -- pair in left-of form" — the driver then leaves the pair in place.)
  --
  -- We do NOT need `DecidableEquality X`: the recognised data is reconstructed
  -- from the offset lists themselves, and the equalities (★)-style are supplied
  -- by the caller (the DiagU constructor).
  --------------------------------------------------------------------------------

  --------------------------------------------------------------------------------
  -- 11c. The frame underlying a `LeftFit`, and the FULLY SOUND swap between its
  --      two firing orders.
  --
  -- For a `LeftFit P mid s` with left box `fy` (slot 1, dom ay/cod by) and
  -- right box `fx` (slot 2, dom ax/cod bx), the frame is `Frame P mid s fy fx`.
  -- Its `before-O`/`after-O` orderings live on the frame's NATIVE right-nested
  -- objects (`N₀`/`N₃`), so they are well-typed for ABSTRACT `P mid s`, and the
  -- swap step between them is exactly `Frame.swap-step`, i.e. `two-box-swap`.
  --
  --   * input  order  (fx first, then fy) = `Frame.after-O  P mid s fy fx`
  --   * sorted order  (fy first, then fx) = `Frame.before-O P mid s fy fx`
  --
  -- so the autonomous bubble step runs  after ⇒ before  (= `≈-Term-sym` of the
  -- proven `head-swap-sound`).  This is the genuine per-swap soundness at the
  -- frame level, autonomous in `P mid s` and reusing `two-box-swap`/`g-out≈pad`/
  -- `g-in≈pad` through `head-swap-sound`.
  --------------------------------------------------------------------------------

  -- the wired tail for a frame built from a LeftFit, landing on the frame's
  -- common output `N₃ = P ++ (by ++ (mid ++ (bx ++ s)))`.
  module LeftFrame {ax bx ay by : List X}
                   {px sx py sy : List X} {fx : Mor ax bx} {fy : Mor ay by}
                   (fit : LeftFit px sx py sy fx fy) where

    open LeftFit fit

    -- the frame with fy in the left slot, fx in the right slot.
    open module F = Frame P mid s fy fx public using
      ( N₀ ; N₃ ; L-out-g
      ; f-in-layer ; g-out-layer ; g-in-layer ; f-out-layer
      ; before-O ; after-O ; head-swap-sound )

    -- the sorted (canonical) order: fy fires first.
    sorted-O : ∀ {M rest} → Wired N₃ rest M → Ordering N₀ M
    sorted-O wRest = before-O wRest

    -- the input order: fx fires first.
    input-O : ∀ {M rest} → Wired N₃ rest M → Ordering N₀ M
    input-O wRest = after-O wRest

    -- THE SOUND SWAP STEP, input ⇒ sorted.  Reuses `head-swap-sound`
    -- (= `two-box-swap`).  Endpoints are the frame's native objects, so this
    -- typechecks for ABSTRACT `P mid s` — no `subst`, no reassociator residue.
    input⇒sorted : ∀ {M rest} (wRest : Wired N₃ rest M)
                 → input-O wRest ⇒W sorted-O wRest
    input⇒sorted wRest = wstep (⟺ (head-swap-sound wRest))

  --------------------------------------------------------------------------------
  -- 11d'. THE `castW` OBJECT-TRANSPORT ALGEBRA (the genuine coherence content).
  --
  -- `castW : u ≡ v → HomTerm (wires u) (wires v)` is the `++`-assoc object
  -- transport realised as `subst`-of-`id`.  The structural reassociators
  -- `assocW`/`assocW⁻`/`liftW` (built purely from `id` and `id ⊗₁ -`, α-free)
  -- COLLAPSE to single `castW`s; combined with `castW`-functoriality this lets
  -- the `g-in≈pad` reassociators cancel against the index casts.  All proven by
  -- `J` (pattern-matching the equality to `refl`); no postulates, no holes.
  --------------------------------------------------------------------------------


  -- the object transport: realised as `subst`-of-`id`, so `castW refl = id`.
  castW : ∀ {u v : List X} → u ≡ v → HomTerm (wires u) (wires v)
  castW refl = id

  -- functoriality of `castW` (composition of transports).
  castW-∘ : ∀ {u v w : List X} (e₁ : u ≡ v) (e₂ : v ≡ w)
          → castW e₂ ∘ castW e₁ ≈Term castW (trans e₁ e₂)
  castW-∘ refl refl = idˡ

  -- `castW` is determined by its endpoints (proof-irrelevance via the
  -- Hedberg UIP on wire lists; --without-K).
  castW-irr : ∀ {u v : List X} (e e' : u ≡ v) → castW e ≈Term castW e'
  castW-irr e e' = ≡⇒≈Term (cong castW (≡-irrelevantL e e'))

  -- prepending one wire to a transport.
  castW-∷ : ∀ {x : X} {u v : List X} (e : u ≡ v)
          → id ⊗₁ castW e ≈Term castW (cong (x ∷_) e)
  castW-∷ refl = id⊗id≈id

  -- `liftW p` of a transport is the transport prefixed by `p`.
  liftW-castW : ∀ (p : List X) {u v : List X} (e : u ≡ v)
              → liftW p (castW e) ≈Term castW (cong (p ++_) e)
  liftW-castW []      e = castW-irr e (cong (_++_ []) e)
  liftW-castW (x ∷ p) e =
    (refl⟩⊗⟨ liftW-castW p e) ○ castW-∷ (cong (p ++_) e) ○ castW-irr _ _

  -- the structural +-associator IS the `++`-assoc transport (both α-free).
  assocW-castW : ∀ (p q s : List X)
               → assocW p q s ≈Term castW (sym (++-assoc p q s))
  assocW-castW []      q s = ≈-Term-refl
  assocW-castW (x ∷ p) q s =
    (refl⟩⊗⟨ assocW-castW p q s) ○ castW-∷ (sym (++-assoc p q s)) ○ castW-irr _ _

  assocW⁻-castW : ∀ (p q s : List X)
                → assocW⁻ p q s ≈Term castW (++-assoc p q s)
  assocW⁻-castW []      q s = ≈-Term-refl
  assocW⁻-castW (x ∷ p) q s =
    (refl⟩⊗⟨ assocW⁻-castW p q s) ○ castW-∷ (++-assoc p q s) ○ castW-irr _ _

  -- the frame reassociators are two-level assocW/liftW TOWERS; both directions
  -- collapse to a single `castW` (instantiated four times below, at the frame's
  -- `domeq` indices).
  assocTower≈castW : ∀ (pre c mid t : List X)
                   → assocW pre (c ++ mid) t ∘ liftW pre (assocW c mid t)
                     ≈Term castW (sym (trans (++-assoc pre (c ++ mid) t)
                                             (cong (pre ++_) (++-assoc c mid t))))
  assocTower≈castW pre c mid t =
    (assocW-castW pre (c ++ mid) t
       ⟩∘⟨ (liftW-resp pre (assocW-castW c mid t)
              ○ liftW-castW pre (sym (++-assoc c mid t))))
    ○ castW-∘ _ _ ○ castW-irr _ _

  assocTower⁻≈castW : ∀ (pre c mid t : List X)
                    → liftW pre (assocW⁻ c mid t) ∘ assocW⁻ pre (c ++ mid) t
                      ≈Term castW (trans (++-assoc pre (c ++ mid) t)
                                         (cong (pre ++_) (++-assoc c mid t)))
  assocTower⁻≈castW pre c mid t =
    ((liftW-resp pre (assocW⁻-castW c mid t) ○ liftW-castW pre (++-assoc c mid t))
       ⟩∘⟨ assocW⁻-castW pre (c ++ mid) t)
    ○ castW-∘ _ _

  --------------------------------------------------------------------------------
  -- 11e. The CLEAN ↔ FRAME bridge for the `fx` (right) layer.
  --
  -- The clean flat pad of the right box lives on the LEFT-nested object
  -- `(P ++ (ay ++ mid)) ++ (ax ++ s)`, the frame's `g-in` on the RIGHT-nested
  -- `N₀ = P ++ (ay ++ (mid ++ (ax ++ s)))`; for abstract offsets these are
  -- equal only up to `++`-assoc, so the bridge needs the propositional index
  -- casts `castW (domeq …)` — `_≈Term_` between the uncast sides is ill-typed.
  -- The bridge is PROVEN below: `fx-clean⇒g-in-core` (§11e') collapses
  -- `g-in≈pad`'s reassociators to single `castW`s via the §11d' algebra, and
  -- `fx-clean⇒g-in` (§11e'') assembles the full clean ⇒ frame bridge, from
  -- which the autonomous DiagU swap soundness follows (§11e''').
  --------------------------------------------------------------------------------

  --------------------------------------------------------------------------------
  -- 11e'. THE BRIDGE, PROVEN.  The clean flat `pad` of the right box `g` (at the
  -- LeftFit offset `pre++(a₁++mid)`, suffix `r`) equals the frame's grouped
  -- `g-in`, conjugated by the `++`-assoc object casts.  This is the abstract
  -- analogue of `Litmus.cA≈after`/`g-in≈cp`: there the reassociators reduced to
  -- `id` and the casts to `refl`; here they reduce to single `castW`s that cancel
  -- via the §11d' algebra.  Stated directly at the frame coordinates (the
  -- LeftFit-phrased corollary follows by the offset rewrites, which are `refl`
  -- once the fit's fields are matched).
  --
  -- castdom : wires((pre++(a₁++mid))++(a₂++r)) ⇒ wires N₀     (assoc, domain)
  -- castcod : wires(pre++(a₁++(mid++(b₂++r)))) ⇒ wires((pre++(a₁++mid))++(b₂++r))
  --------------------------------------------------------------------------------

  -- the two index equalities (pure `++`-assoc), named.
  domeq : (pre a₁ mid a₂ r : List X)
        → (pre ++ (a₁ ++ mid)) ++ (a₂ ++ r) ≡ pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))
  domeq pre a₁ mid a₂ r =
    trans (++-assoc pre (a₁ ++ mid) (a₂ ++ r))
          (cong (pre ++_) (++-assoc a₁ mid (a₂ ++ r)))

  -- reassocF-in collapses to the domain cast (its inverse direction).
  reassocF-in≈castW :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.reassocF-in pre mid r f g
      ≈Term castW (sym (domeq pre a₁ mid a₂ r))
  reassocF-in≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g =
    assocTower≈castW pre a₁ mid (a₂ ++ r)

  -- reassocB-in collapses to the codomain cast.
  reassocB-in≈castW :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.reassocB-in pre mid r f g
      ≈Term castW (domeq pre a₁ mid b₂ r)
  reassocB-in≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g =
    assocTower⁻≈castW pre a₁ mid (b₂ ++ r)

  -- round-trip cancellation of inverse casts.
  castW-sym-r : ∀ {u v : List X} (e : u ≡ v) → castW (sym e) ∘ castW e ≈Term id
  castW-sym-r refl = idˡ

  -- the other cancellation order.
  castW-sym-r-flip : ∀ {u v : List X} (e : u ≡ v) → castW e ∘ castW (sym e) ≈Term id
  castW-sym-r-flip refl = idˡ

  -- THE CORE BRIDGE (frame coordinates), PROVEN.  The frame's grouped `g-in`
  -- equals the clean flat `pad` of the right box `g` (at the LeftFit offset
  -- `pre++(a₁++mid)`), conjugated by the `++`-assoc object casts.  Obtained from
  -- `g-in≈pad` by collapsing its reassociators to single `castW`s (§11d').
  fx-clean⇒g-in-core :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.g-in pre mid r f g
      ≈Term castW (domeq pre a₁ mid b₂ r)
          ∘ pad (pre ++ (a₁ ++ mid)) r (⟦box⟧ g)
          ∘ castW (sym (domeq pre a₁ mid a₂ r))
  fx-clean⇒g-in-core pre mid r {a₁} {b₁} {a₂} {b₂} f g =
    Frame.g-in≈pad pre mid r f g
      ○ (reassocB-in≈castW pre mid r f g
           ⟩∘⟨ refl⟩∘⟨ reassocF-in≈castW pre mid r f g)

  --------------------------------------------------------------------------------
  -- 11e-out. THE MIRROR g-out RE-CLEANING.  Exact analogue of the g-in side,
  -- with `a₁ ↦ b₁`: `reassocF-out`/`reassocB-out` are the same `assocW`/`liftW`
  -- towers (at offset `b₁` instead of `a₁`) so they collapse to single `castW`s
  -- by the SAME §11d' algebra, and `g-out≈pad` then gives `g-out` as the clean
  -- flat `pad (pre++(b₁++mid)) r ⟦g⟧` conjugated by the index casts.  This makes
  -- the SORTED (swap-output) g-layer a clean `pad` again, mirroring `g-in`.
  --------------------------------------------------------------------------------

  -- reassocF-out collapses to the (inverse) domain cast at offset b₁.
  reassocF-out≈castW :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.reassocF-out pre mid r f g
      ≈Term castW (sym (domeq pre b₁ mid a₂ r))
  reassocF-out≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g =
    assocTower≈castW pre b₁ mid (a₂ ++ r)

  -- reassocB-out collapses to the codomain cast at offset b₁.
  reassocB-out≈castW :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.reassocB-out pre mid r f g
      ≈Term castW (domeq pre b₁ mid b₂ r)
  reassocB-out≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g =
    assocTower⁻≈castW pre b₁ mid (b₂ ++ r)

  -- THE CORE g-out BRIDGE, PROVEN (mirror of `fx-clean⇒g-in-core`).  The frame's
  -- grouped `g-out` equals the clean flat `pad` of the right box `g` (at the
  -- SORTED offset `pre++(b₁++mid)`), conjugated by the `++`-assoc object casts.
  fy-sorted⇒g-out-core :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.g-out pre mid r f g
      ≈Term castW (domeq pre b₁ mid b₂ r)
          ∘ pad (pre ++ (b₁ ++ mid)) r (⟦box⟧ g)
          ∘ castW (sym (domeq pre b₁ mid a₂ r))
  fy-sorted⇒g-out-core pre mid r {a₁} {b₁} {a₂} {b₂} f g =
    Frame.g-out≈pad pre mid r f g
      ○ (reassocB-out≈castW pre mid r f g
           ⟩∘⟨ refl⟩∘⟨ reassocF-out≈castW pre mid r f g)

  --------------------------------------------------------------------------------
  -- 11e''. THE FULL CLEAN ⇒ FRAME BRIDGE, PROVEN.  For a recognised `LeftFit`
  -- (matched to its `refl` offset witnesses, so `px=P++(ay++mid)`, `sx=s`,
  -- `py=P`, `sy=mid++(bx++s)` definitionally), the CLEAN head pair
  --
  --     ⟦wTail⟧ ∘ f-out ∘ castMid ∘ (pad px sx ⟦fx⟧)
  --
  -- (the genuine flat-`pad` firing order fx-then-fy, with `castMid` the ★ wiring
  -- transport between fx's clean codomain and fy's clean domain) equals the
  -- frame's `input-O` (= `after-O`, gbox-grouped order) conjugated by the domain
  -- index cast `castW domcast`.  This is the abstract, frame-routed analogue of
  -- `Litmus.cA≈after`, PROVEN via `fx-clean⇒g-in-core` + the `castW` algebra.
  --
  -- The clean fy-layer `pad py sy ⟦fy⟧` is DEFINITIONALLY `Frame.f-out`, so it
  -- appears as `Frame.f-out P mid s fy fx` here.
  --------------------------------------------------------------------------------

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
      -- castMidB ∘ pad … ≈ g-in ∘ castDom: insert the inverse-cast pair on the
      -- right, then fold the core bridge.
      bridge : castMidB ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
             ≈Term F.g-in ∘ castDom
      bridge = insertʳ (castW-sym-r (domeq P ay mid ax s))
             ○ ((assoc ○ ⟺ (fx-clean⇒g-in-core P mid s fy fx)) ⟩∘⟨refl)

  --------------------------------------------------------------------------------
  -- 11e'''. THE AUTONOMOUS DiagU SWAP SOUNDNESS, PROVEN.  Chaining the clean⇒
  -- frame bridge with the frame's PROVEN `input⇒sorted` swap step gives: the
  -- CLEAN (fx-then-fy) head order equals — modulo the domain index cast — the
  -- frame's SORTED (fy-then-fx) order.  This is precisely the §11e note's
  -- `≈-Term-trans (fx-clean⇒g-in …) (input⇒sorted …-sound)`, now closed.
  --------------------------------------------------------------------------------

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
  -- 11f. subst-transport of a DiagU index, PROVEN sound.  A swap necessarily
  -- moves a clean DiagU off its left-nested index onto the frame's right-nested
  -- index (they differ by `domeq`, NON-`refl` for abstract offsets), so a real
  -- `DiagU n → DiagU n` transports the swapped sub-diagram along that `≡`.  The
  -- interpretation of a transported DiagU is the original conjugated by `castW`s
  -- on BOTH endpoints, proven by `J` (both casts are `id` on `refl`).
  --------------------------------------------------------------------------------

  -- transport a DiagU along an index equality.
  substDiagU : ∀ {m n : List X} → m ≡ n → DiagU m → DiagU n
  substDiagU refl d = d

  -- the transport preserves the output index.
  substDiagU-out : ∀ {m n : List X} (e : m ≡ n) (d : DiagU m)
                 → out (substDiagU e d) ≡ out d
  substDiagU-out refl d = refl

  -- interpretation commutes with the transport up to a single index cast on each
  -- endpoint:  ⟦ substDiagU e d ⟧ ∘ castW e  ≈  castW (out-cast) ∘ ⟦ d ⟧.
  ⟦substDiagU⟧ : ∀ {m n : List X} (e : m ≡ n) (d : DiagU m)
              → ⟦ substDiagU e d ⟧ ∘ castW e
                ≈Term castW (sym (substDiagU-out e d)) ∘ ⟦ d ⟧
  ⟦substDiagU⟧ refl d = idʳ ○ ⟺ idˡ

  --------------------------------------------------------------------------------
  -- 11g. `swapHeadD` — the genuine clean DiagU head swap.
  --
  -- A clean DiagU head pair recognised as a `LeftFit` is presented as: the two
  -- boxes + offset data of the fit, the (★) inter-layer wiring `≡` (which is
  -- NON-`refl` for abstract offsets, hence supplied), and the sub-diagram `dInner
  -- : DiagU (px++(bx++sx))`.  We build the SWAPPED clean DiagU on the same input
  -- index and prove `⟦ input ⟧ ≈Term ⟦ swapped ⟧`.
  --
  -- The swapped diagram is fy-first (lower offset) then fx, both genuine clean
  -- `pad`-layers (`_▸_∷_⟨_⟩`); the necessary `++`-assoc re-indexing between the
  -- fy and fx layers is absorbed by `substDiagU` along `domeq`, whose soundness
  -- is `⟦substDiagU⟧`.  Soundness chains `diagU-swap-sound` (step 11e''') with the
  -- input/output cast bookkeeping; the litmus
  -- (`Categories.SolverNormalizeTests`) machine-checks one fire.
  --------------------------------------------------------------------------------

  -- the SWAPPED clean DiagU on the frame's right-nested input index N₀.  fy fires
  -- first at offset P (clean pad, = `f-in`), then fx at offset `P++(by++mid)`
  -- (clean pad, = the re-cleaned `g-out`), with the inter-layer `domeq` absorbed
  -- by `substDiagU`.  `dSorted` is the tail at the swapped-output index.
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

  -- SOUNDNESS of the swapped diagram.  Its interpretation equals the frame's
  -- SORTED order (`⟦dSorted⟧ ∘ g-out ∘ f-in`) conjugated by the inter-layer
  -- index cast — exactly the clean re-reading of `before-O` via the §11e-out
  -- g-out re-cleaning, with the `substDiagU` cast absorbed by `⟦substDiagU⟧`.
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
      -- insert the inverse-cast pair on the right, absorb `substDiagU` via
      -- `⟦substDiagU⟧`, cancel the output-cast pair on the left.
      key : castW out-eq ∘ ⟦ inner ⟧ ≈Term ⟦ innerD ⟧ ∘ castW (sym e)
      key = insertʳ (castW-sym-r-flip e)
          ○ ((pullʳ (⟦substDiagU⟧ e innerD)
                ○ cancelˡ (castW-sym-r-flip out-eq)) ⟩∘⟨refl)

  --------------------------------------------------------------------------------
  -- 11h. The INPUT clean DiagU of an out-of-order head pair, and the ABSTRACT
  -- per-swap soundness `⟦ input ⟧ ≈Term ⟦ swapped ⟧`.
  --
  -- For a recognised `LeftFit` the input head order is fx-first (the right box,
  -- higher offset) then fy.  Both are genuine clean `pad`-layers; the inter-layer
  -- `++`-assoc re-index between fx and fy is absorbed by `substDiagU` along
  -- `domeq P ay mid bx s` (soundness `⟦substDiagU⟧`).  `dInput`/`swapHeadD-out`
  -- live at the SAME input index `N₀`, so `⟦ input ⟧ ≈Term ⟦ swapped ⟧` is the
  -- honest per-swap soundness — exercised concretely in
  -- `Categories.SolverNormalizeTests` (`litDiagUSwap`).
  --------------------------------------------------------------------------------

  -- the INPUT clean DiagU: fx (right box) fires FIRST, then fy.
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
  -- 11h''. The ABSTRACT per-swap soundness.  `⟦ dInput ⟧ ≈Term ⟦ dSwapped ⟧`:
  -- the input (fx-first) and swapped (fy-first) clean DiagUs, at the SAME input
  -- index `N₀` and same `out`, have equal interpretations.  Proven by:
  --   (1) `dInput-expand`  : ⟦ dInput ⟧ ∘ castW(e) ≈ castW(oI) ∘ (frame INPUT
  --                          composite ⟦dRest⟧ ∘ f-out ∘ castW… ∘ pad fx)
  --   (2) `diagU-swap-sound`: that frame input composite ≈ frame SORTED composite
  --   (3) `dSwapped-expand`: ⟦ dSwapped ⟧ ∘ castW(e) ≈ castW(oS) ∘ frame SORTED
  --                          composite
  -- then `castW`-cancel the common `e` on the right and the (irrelevant, equal-
  -- endpoint) output casts `oI`/`oS` on the left.  All `castW` algebra.
  --------------------------------------------------------------------------------

  -- the output index of `dInput`/`dSwapped` (both `= out dRest`), namable so the
  -- soundness goal can carry the (stuck-`out`) output cast explicitly.
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

  -- right-cancel an iso `castW e`:  A ∘ castW e ≈ B ∘ castW e  ⟹  A ≈ B.
  castW-cancelʳ : ∀ {u v w : List X} (e : u ≡ v)
                  {A B : HomTerm (wires v) (wires w)}
                → A ∘ castW e ≈Term B ∘ castW e → A ≈Term B
  castW-cancelʳ refl {A} {B} h = ⟺ idʳ ○ h ○ idʳ

  -- expansion of the INPUT diagram, pre-composed by the domain cast `e`, to the
  -- frame INPUT composite (the LHS of `diagU-swap-sound`).  Proven by `J` on the
  -- offset witnesses: the top `substDiagU (domeq …ax…)` cancels `castW e`, and
  -- the inner `substDiagU (sym (domeq …bx…))` re-expresses the fx∘fy clean stack
  -- as `f-out ∘ castW(domeq …bx…) ∘ pad fx` — exactly `diagU-swap-sound`'s LHS.
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
      -- (rhs1 ∘ padfx) ≈ ⟦dRest⟧ ∘ (f-out ∘ (castW(domeq …bx…) ∘ padfx)):
      -- pure reassociation + one castW-irr (sym (sym _) vs _).
      chainR : rhs1 ∘ padfx
             ≈Term ⟦ dRest ⟧ ∘ (F.f-out ∘ (castW (domeq P ay mid bx s) ∘ padfx))
      chainR = assoc ○ assoc
        ○ (refl⟩∘⟨ refl⟩∘⟨ (castW-irr (sym e1) (domeq P ay mid bx s) ⟩∘⟨refl))
      -- ⟦ substDiagU e1 fyL ⟧ ≈ castW(sym o1) ∘ (⟦dRest⟧ ∘ f-out) ∘ castW(sym e1):
      -- absorb the substDiagU, insert the inverse-cast pair on the right.
      subst1 : ⟦ substDiagU e1 fyL ⟧
             ≈Term castW (sym o1) ∘ rhs1
      subst1 = castW-cancelʳ e1
        (⟦substDiagU⟧ e1 fyL ○ insertʳ (castW-sym-r e1) ○ (assoc ⟩∘⟨refl))

  --------------------------------------------------------------------------------
  -- 11h'''. Expansion of `⟦ dSwapped ⟧` to the frame SORTED ordering (the
  -- `before-O`/fy-first composite).  Proven from the PROVEN `swapHeadD-out-sound`
  -- by re-cleaning `g-out` (`fy-sorted⇒g-out-core`), absorbing the inner
  -- `substDiagU` via `⟦substDiagU⟧`, and bridging `⟦dRest⟧ ≈ ⟦fromDiagU-W dRest⟧W`
  -- (`fromDiagU-sound`).  All `castW` algebra; reuses only already-proven lemmas.
  --------------------------------------------------------------------------------
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
      -- ⟦dSorted⟧ ≈ (castW(sym o'') ∘ ⟦fromDiagU-W dRest⟧W) ∘ castW ebx:
      -- absorb the substDiagU, bridge ⟦dRest⟧ to the wired fold, insert the
      -- inverse-cast pair on the right.
      dS : ⟦ dSorted ⟧
         ≈Term (castW (sym o'') ∘ ⟦ fromDiagU-W dRest ⟧W) ∘ castW ebx
      dS = castW-cancelʳ (sym ebx)
        (⟦substDiagU⟧ (sym ebx) dRest
          ○ (refl⟩∘⟨ ⟺ (fromDiagU-sound dRest))
          ○ insertʳ (castW-sym-r-flip ebx))
      -- ⟦dSorted⟧ ∘ padfx' ∘ castW(sym e') ≈ castW(sym o'') ∘ (⟦fromDiagU-W dRest⟧W ∘ g-out):
      -- expand dS, reassociate, fold the re-cleaned g-out.
      gpart : (⟦ dSorted ⟧ ∘ padfx') ∘ castW (sym e')
            ≈Term castW (sym o'') ∘ (⟦ fromDiagU-W dRest ⟧W ∘ F.g-out)
      gpart = ((dS ⟩∘⟨refl) ⟩∘⟨refl)
            ○ assoc ○ assoc
            ○ (refl⟩∘⟨ ⟺ (fy-sorted⇒g-out-core P mid s fy fx))
            ○ assoc

  --------------------------------------------------------------------------------
  -- 11h''''. THE ASSEMBLED ABSTRACT PER-SWAP SOUNDNESS.  `castW out-eq ∘ ⟦ dInput ⟧
  -- ≈Term ⟦ dSwapped ⟧`: the input (fx-first) and swapped (fy-first) clean DiagUs
  -- are equal in the free monoidal category, up to the (stuck-`out`) index cast
  -- `out-eq : out dInput ≡ out dSwapped`.  Chains `dInput-frame`, the PROVEN
  -- `diagU-swap-sound` (= `two-box-swap`), and `dSwapped-frame`; cancels the
  -- shared domain cast and the loop of output casts.  Postulate-free.
  --------------------------------------------------------------------------------
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
      dIn = dInput fit dRest
      dSw = dSwapped fit dRest
      wTail = fromDiagU-W dRest
      sortedO = LeftFrame.sorted-O fit wTail
      module F = Frame P mid s fy fx
      FC = ⟦ dRest ⟧ ∘ (F.f-out ∘ (cbx ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)))
      -- ⟦dRest⟧ ≈ ⟦wTail⟧W, lifted to FC ≈ frame-input-composite, then diagU-swap-sound.
      FC≈sorted : FC ≈Term ⟦ sortedO ⟧O ∘ cax
      FC≈sorted =
        (⟺ (fromDiagU-sound dRest) ⟩∘⟨refl) ○ diagU-swap-sound fit wTail
      -- dSwapped-frame rearranged: ⟦sortedO⟧O ≈ castW dsO ∘ ⟦dSw⟧.
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
  -- 12. THE AUTONOMOUS FIRING DiagU SORT (needs `DecidableEquality X`).
  --
  -- Given `DecEq X` we can DECIDE a `LeftFit` by `List`-splitting the offset
  -- lists at the lengths dictated by the box domains, confirming with the derived
  -- `DecEq (List X)`.  `swapHeadD` then fires the genuine clean DiagU swap
  -- (`dInput`/`dSwapped` + `diagU-swap-soundD`), and `normalizeD` is a fuel-driven
  -- bubble sort whose soundness chains the per-swap `≈Term` witnesses.
  --------------------------------------------------------------------------------
  module SortD where

    -- derived decidable equality on offsets (stdlib, --without-K friendly).
    _≟L_ : DecidableEquality (List X)
    _≟L_ = ≡-dec _≟X_

    -- strip a known prefix `p` off `xs`, returning the remainder with a proof.
    stripPrefix : (p xs : List X) → Maybe (Σ[ ys ∈ List X ] xs ≡ p ++ ys)
    stripPrefix []       xs       = just (xs , refl)
    stripPrefix (_ ∷ _)  []       = nothing
    stripPrefix (x ∷ p)  (y ∷ xs) = case x ≟X y of λ where
      (no  _)   → nothing
      (yes x≡y) → Maybe.map (λ (ys , eq) → ys , cong₂ _∷_ (sym x≡y) eq)
                            (stripPrefix p xs)

    --------------------------------------------------------------------------------
    -- 12a. The decidable `LeftFit` recogniser.
    --
    -- We set `P := py`, `s := sx`, and recover `mid` by stripping the prefix
    -- `py ++ ay` off `px`.  The fit's four equalities are then:
    --   px ≡ py ++ (ay ++ mid)      -- by construction of the strip (returns this)
    --   sx ≡ sx                      -- refl
    --   py ≡ py                      -- refl
    --   sy ≡ mid ++ (bx ++ sx)       -- confirmed by `_≟L_`
    -- Returns `nothing` when the splits don't fit (overlap / dependent / wrong
    -- orientation).
    --------------------------------------------------------------------------------
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
    -- 12b. `swapHeadD` — the firing clean DiagU head swap on explicit head-pair
    -- data.  (A `DiagU` ERASES the inter-layer wiring into a non-definitional
    -- `++`-assoc index, so a 2-layer head of an ABSTRACT `DiagU n` cannot be
    -- destructured by unification — `dInput`/`dSwapped` carry that wiring via
    -- `substDiagU`.  So `swapHeadD` consumes the head pair as the offsets/boxes
    -- plus the sub-diagram `dRest`, exactly the data `leftFit?` recognises.)
    --
    -- On a recognised `LeftFit` it returns the SWAPPED clean DiagU `dSwapped`
    -- together with the genuine `≈Term` soundness `diagU-swap-soundD` (input ⇒
    -- swapped, up to the stuck-`out` index cast `castW oeq`).  `nothing` when the
    -- pair is not an out-of-order independent left-of pair.
    --------------------------------------------------------------------------------
    -- the swap result on a recognised fit + sorted-output tail: the swapped clean
    -- DiagU and the per-swap soundness (up to the stuck-`out` index cast).
    HeadSwapD : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
                (fit : LeftFit px sx py sy fx fy) → DiagU (LeftFrame.N₃ fit) → Set
    HeadSwapD fit dRest =
      Σ[ dSw ∈ DiagU (LeftFrame.N₀ fit) ]
        Σ[ oeq ∈ (out (dInput fit dRest) ≡ out dSw) ]
          (castW oeq ∘ ⟦ dInput fit dRest ⟧ ≈Term ⟦ dSw ⟧)

    -- the firing swap: ALWAYS fires on a recognised fit (left-of ⟹ out of order),
    -- returning the genuine swapped DiagU + `diagU-swap-soundD`.
    swapHeadD : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
                (fit : LeftFit px sx py sy fx fy) (dRest : DiagU (LeftFrame.N₃ fit))
              → HeadSwapD fit dRest
    swapHeadD fit dRest =
      dSwapped fit dRest
      , trans (dInput-out fit dRest) (sym (dSwapped-out fit dRest))
      , diagU-swap-soundD fit dRest

    --------------------------------------------------------------------------------
    -- 12c. `normalizeD` — the one-step swap driver on a recognised DiagU head.
    --
    -- `normalizeD` performs AT MOST ONE swap: on `0` fuel it returns the input
    -- head order unchanged (trivial witness); on positive fuel it fires the
    -- single genuine swap of the recognised head pair.  It is NOT a multi-step
    -- bubble sort: the SWAPPED tail is re-indexed (by `substDiagU` along the
    -- non-definitional `++`-assoc `domeq`), so a 2-layer head of the *output* of
    -- an ABSTRACT step cannot be destructured by unification, and abstract
    -- multi-step recursion is not expressible; chaining of multiple genuine
    -- steps is exercised CONCRETELY in the litmus.  Soundness is the per-swap
    -- `≈Term` (up to the stuck-`out` cast `castW oeq`), unconditional whatever
    -- the fuel.
    --------------------------------------------------------------------------------

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
-- Compatibility wrapper: `NormalizeI` at the standard interpretation
-- `Untyped.⟦box⟧` (= `var ∘ box`).  Old consumers keep working, gaining
-- only the leading variant argument.
--------------------------------------------------------------------------------
module Normalize (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
                 (Mor : List X → List X → Set) where

  open Untyped v {X} Mor using (⟦box⟧)
  open NormalizeI v {X} _≟X_ Mor ⟦box⟧ public
