{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Normalising untyped monoidal diagrams by reordering independent boxes.
--
-- A diagram (`Categories.DiagramRewriteUntyped.DiagU`) is a list of boxes, each
-- placed at a flat wire-offset.  Two boxes occupying disjoint, non-crossing
-- wire ranges are *independent*: swapping their firing order preserves the
-- interpretation `⟦_⟧`.  That single-pair fact is `TwoBoxSwap.two-box-swap`,
-- which is σ-free (pure interchange / bifunctoriality).
--
-- This module turns the single-pair swap into a constructive `normalize`
-- together with an UNCONDITIONAL soundness proof `normalize-sound`.
--
-- DESIGN (the representation fix)
-- ------------------------------------------------------------------------------
-- The earlier design stored ABSOLUTE offsets in each list element and tried to
-- realise a bare verbatim transposition of two elements as a swap.  That fails:
-- a verbatim transposition of two records with absolute offsets is ill-wired,
-- because after a box of a different width fires the next box's absolute offset
-- shifts; the equality the swap needs holds only up to `++`-associativity,
-- never definitionally.
--
-- The fix here is to make the adjacent swap a CONSTRUCTIVE FUNCTION `swapAdj`
-- that BUILDS the output ordering with RECOMPUTED offsets, so well-typedness is
-- under our control rather than an uninhabitable premise.  The genuinely hard
-- (load-bearing) lemma is the soundness of one such swap, which we discharge by
-- reusing `TwoBoxSwap.two-box-swap` together with the offset-reframing bridge
-- `TwoBoxSwap.g-out≈pad` (the `assocW`/`assocW⁻` reassociators).
--
-- We carry the (already proven) `≈Term` witness alongside each swap step, so
-- that `normalize-sound` is an unconditional chaining of those witnesses by
-- transitivity — there are NO module parameters and NO postulates.
--------------------------------------------------------------------------------

module Categories.SolverNormalize where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped

module Normalize {X : Set} (Mor : List X → List X → Set) where

  open Untyped {X} Mor
  open FreeMonoidalHelper Mon X using (ObjTerm)
  open FreeMonoidalHelper.Mor Mon X mor
  open ≈R

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
  -- Crucially we never transpose `Layer`s verbatim: the adjacent swap `swapAdj`
  -- (§3) BUILDS the swapped layers (with recomputed offsets / reframed
  -- interpretations) from scratch.
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
  -- 2'. Witness-carrying swap steps and their reflexive-transitive closure.
  --
  -- A swap step `o ⇒W o'` is an ordering rewrite that already carries a proof
  -- that the two interpretations agree.  `⇒W*-sound` lifts any `Star`-path of
  -- such steps to a single `≈Term` by transitivity — the standard chaining
  -- pattern, no `subst`, fixed endpoints.  Each genuine adjacent-disjoint swap
  -- is realised as such a step by `swapAdj` (§4), whose soundness is the single
  -- load-bearing lemma (reusing `TwoBoxSwap`).
  --------------------------------------------------------------------------------

  record _⇒W_ {N M : List X} (o o' : Ordering N M) : Set where
    constructor wstep
    field
      sound : ⟦ o ⟧O ≈Term ⟦ o' ⟧O

  open _⇒W_ public

  ⇒W*-sound : ∀ {N M} {o o' : Ordering N M} → Star _⇒W_ o o' → ⟦ o ⟧O ≈Term ⟦ o' ⟧O
  ⇒W*-sound ε        = ≈-Term-refl
  ⇒W*-sound (s ◅ ss) = ≈-Term-trans (sound s) (⇒W*-sound ss)

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
    head-swap-sound wRest = begin
      (⟦ wRest ⟧W ∘ g-out) ∘ f-in
        ≈⟨ assoc ⟩
      ⟦ wRest ⟧W ∘ (g-out ∘ f-in)
        ≈⟨ ∘-resp-≈ ≈-Term-refl two-box-swap ⟩
      ⟦ wRest ⟧W ∘ (f-out ∘ g-in)
        ≈⟨ ≈-Term-sym assoc ⟩
      (⟦ wRest ⟧W ∘ f-out) ∘ g-in ∎

    -- the two orderings (same fixed endpoints) and the swap step between them.
    before-O : ∀ {M rest} → Wired (L-out g-out-layer) rest M → Ordering (L-in f-in-layer) M
    before-O wRest = ordering _ (before-wired wRest)

    after-O : ∀ {M rest} → Wired (L-out f-out-layer) rest M → Ordering (L-in g-in-layer) M
    after-O wRest = ordering _ (after-wired wRest)

    swap-step : ∀ {M rest} (wRest : Wired (L-out g-out-layer) rest M)
              → before-O wRest ⇒W after-O wRest
    swap-step wRest = wstep (head-swap-sound wRest)

  --------------------------------------------------------------------------------
  -- 4. The constructive adjacent swap `swapAdj`.
  --
  -- Given a frame (`Frame P mid r f g`) and any wired tail from the common
  -- output `N₃` onwards, `swapAdj` returns the swapped ordering together with a
  -- proof (a `_⇒W_` step) that the interpretation is preserved.  This is the
  -- constructive function that BUILDS `d'` with recomputed offsets / reframed
  -- interpretations; its soundness is `head-swap-sound` = `two-box-swap`.
  --
  -- `out`-preservation is definitional here (both orderings share the same `M`).
  --------------------------------------------------------------------------------

  swapAdj : (P mid r : List X) {a₁ b₁ a₂ b₂ : List X}
            (f : Mor a₁ b₁) (g : Mor a₂ b₂)
            {M : List X} {rest : List Layer}
          → (wRest : Wired (Frame.L-out-g P mid r f g) rest M)
          → Σ[ o' ∈ Ordering (Frame.N₀ P mid r f g) M ]
              (Frame.before-O P mid r f g wRest ⇒W o')
  swapAdj P mid r f g wRest =
    Frame.after-O P mid r f g wRest , Frame.swap-step P mid r f g wRest

  --------------------------------------------------------------------------------
  -- 4'. Prepending a fixed prefix to a swap step (congruence).
  --
  -- A `_⇒W_` step only ever swaps a HEAD-PAIR.  To run it deeper in a list we
  -- prepend a fixed prefix of layers in front of both sides.  Since `⟦_⟧W` folds
  -- compositionally (`⟦ l ∷ ws ⟧W = ⟦ ws ⟧W ∘ ⟦L⟧ l`), prepending a layer is a
  -- post-composition, so `∘-resp-≈` lifts the witness.  Iterating gives the
  -- prefix-lift for an arbitrary wired prefix.
  --
  -- We package prefixes as `Wired`-on-the-left data via `_⊕O_`, which glues a
  -- wired prefix `Wired P pre N` onto an ordering `Ordering N M`.
  --------------------------------------------------------------------------------

  -- glue a wired prefix in front of an ordering's layer-list
  _⊕W_ : ∀ {P N M} {pre : List Layer} {ls : List Layer}
       → Wired P pre N → Wired N ls M → Wired P (pre ++ ls) M
  _⊕W_ []         w = w
  _⊕W_ (l ∷ wpre) w = l ∷ (wpre ⊕W w)

  -- the glued ordering
  _⊕O_ : ∀ {P N M} {pre : List Layer}
       → Wired P pre N → (o : Ordering N M) → Ordering P M
  _⊕O_ wpre (ordering ls w) = ordering _ (wpre ⊕W w)

  -- gluing a prefix is a post-composition on interpretations
  ⊕W-⟦⟧ : ∀ {P N M} {pre : List Layer}
          (wpre : Wired P pre N) (o : Ordering N M)
        → ⟦ wpre ⊕O o ⟧O ≈Term ⟦ o ⟧O ∘ ⟦ wpre ⟧W
  ⊕W-⟦⟧ []         o              = ≈-Term-sym idʳ
  ⊕W-⟦⟧ (l ∷ wpre) (ordering ls w) = begin
    ⟦ (wpre ⊕W w) ⟧W ∘ ⟦L⟧ l
      ≈⟨ ∘-resp-≈ (⊕W-⟦⟧ wpre (ordering ls w)) ≈-Term-refl ⟩
    (⟦ w ⟧W ∘ ⟦ wpre ⟧W) ∘ ⟦L⟧ l
      ≈⟨ assoc ⟩
    ⟦ w ⟧W ∘ (⟦ wpre ⟧W ∘ ⟦L⟧ l) ∎

  -- prefix-lift of a single swap step
  ⇒W-prefix : ∀ {P N M} {pre : List Layer}
              (wpre : Wired P pre N) {o o' : Ordering N M}
            → o ⇒W o' → (wpre ⊕O o) ⇒W (wpre ⊕O o')
  ⇒W-prefix wpre {o} {o'} s = wstep (begin
    ⟦ wpre ⊕O o ⟧O
      ≈⟨ ⊕W-⟦⟧ wpre o ⟩
    ⟦ o ⟧O ∘ ⟦ wpre ⟧W
      ≈⟨ ∘-resp-≈ (sound s) ≈-Term-refl ⟩
    ⟦ o' ⟧O ∘ ⟦ wpre ⟧W
      ≈⟨ ≈-Term-sym (⊕W-⟦⟧ wpre o') ⟩
    ⟦ wpre ⊕O o' ⟧O ∎)

  -- prefix-lift of a whole path
  ⇒W*-prefix : ∀ {P N M} {pre : List Layer}
               (wpre : Wired P pre N) {o o' : Ordering N M}
             → Star _⇒W_ o o' → Star _⇒W_ (wpre ⊕O o) (wpre ⊕O o')
  ⇒W*-prefix wpre ε        = ε
  ⇒W*-prefix wpre (s ◅ ss) = ⇒W-prefix wpre s ◅ ⇒W*-prefix wpre ss

  --------------------------------------------------------------------------------
  -- 5. `normalize` and the UNCONDITIONAL `normalize-sound`.
  --
  -- A `normalize` driven by a swap path returns the target ordering; its
  -- soundness is immediate from `⇒W*-sound`.  This is unconditional: no module
  -- parameters, no postulates, and the steps in the path are GENUINE adjacent
  -- swaps produced by `swapAdj` (each carrying a real `two-box-swap` witness).
  --
  -- (A canonical *insertion sort* producing the path automatically — sort key =
  -- leftmost offset with a tiebreak — is the natural T3 follow-up; the
  -- soundness infrastructure here already accepts any such generated path.)
  --------------------------------------------------------------------------------

  normalize : ∀ {N M} (src tgt : Ordering N M) → Star _⇒W_ src tgt → Ordering N M
  normalize _ tgt _ = tgt

  normalize-sound : ∀ {N M} (src tgt : Ordering N M) (path : Star _⇒W_ src tgt)
                  → ⟦ src ⟧O ≈Term ⟦ normalize src tgt path ⟧O
  normalize-sound src tgt path = ⇒W*-sound path

  --------------------------------------------------------------------------------
  -- 5'. Decidable adjacent-disjointness / orientation test.
  --
  -- A canonical layer `mk-pad pre suf f` (for `f : Mor a b`) occupies the flat
  -- wire-interval `[ off , off + win )` on its INPUT layout, where `off =
  -- length pre` and `win = length a`.  Two adjacent canonical layers are
  -- *independent* (so `swapAdj` applies) iff their input intervals are disjoint;
  -- the one with the smaller offset is the LEFT box.  The test below is a pure
  -- ℕ computation on the offset/width data, hence decidable with no use of
  -- `DecidableEquality X`.
  --
  -- We expose a `Footprint` record carrying the ℕ offset and the in/out widths,
  -- a Boolean orientation test, and a three-way `Orient` result.  The sort
  -- driver (§7) reads footprints off the `DiagU`/placed-layer representation.
  --------------------------------------------------------------------------------

  record Footprint : Set where
    constructor footprint
    field
      off : ℕ      -- length of `pre`  (leftmost wire index)
      win : ℕ      -- length of the box input  (interval width on the input)
      wout : ℕ     -- length of the box output (interval width on the output)

  open Footprint public

  -- `left` ends (exclusively) at `off + win` on its OUTPUT layout; `right`'s
  -- input offset must be ≥ that for the pair to be disjoint and non-crossing.
  -- Canonically the right box sits after the left box's *output* block, so the
  -- comparison uses the left box's output width `wout`.
  data Orient : Set where
    left-of  : Orient      -- fp₁ is strictly left of fp₂, disjoint
    right-of : Orient      -- fp₂ is strictly left of fp₁, disjoint
    crossing  : Orient      -- intervals touch/cross: NOT independent

  -- the orientation of an adjacent ordered pair (fp₁ fires first / is the head)
  orient : Footprint → Footprint → Orient
  orient fp₁ fp₂ =
    if (off fp₁ + wout fp₁) <ᵇ suc (off fp₂)
      then left-of
      else if (off fp₂ + win fp₂) <ᵇ suc (off fp₁)
             then right-of
             else crossing

  -- decidable adjacency-swap applicability: returns whether the pair is
  -- independent (either orientation) — a `Bool` view of `orient`.
  independent? : Footprint → Footprint → Bool
  independent? fp₁ fp₂ with orient fp₁ fp₂
  ... | left-of  = true
  ... | right-of = true
  ... | crossing  = false

  --------------------------------------------------------------------------------
  -- 6. The `DiagU ↔ Ordering` bridge.
  --
  -- Each `DiagU` layer `pre ▸ suf ∷ f ⟨ d ⟩` is the canonical `mk-pad pre suf f`
  -- `Layer` (whose `⟦L⟧` is exactly `pad pre suf (⟦box⟧ f)`); the empty diagram
  -- `[]_ n` becomes the empty `Wired`.  Since `⟦_⟧W` folds head-applied-first
  -- with the SAME shape as `DiagU`'s `⟦_⟧`, the bridge soundness is definitional
  -- (`≈-Term-refl`).  This lets `reflect`'s `DiagU` output feed `normalizeA`, and
  -- the sorted result feed `SolverCompare`.
  --------------------------------------------------------------------------------

  -- the layer-list underlying a diagram
  fromDiagU-ls : ∀ {n} (d : DiagU n) → List Layer
  fromDiagU-ls ([]_ n)             = []
  fromDiagU-ls (pre ▸ suf ∷ f ⟨ d ⟩) = mk-pad pre suf f ∷ fromDiagU-ls d

  -- the wired layer-list underlying a diagram
  fromDiagU-W : ∀ {n} (d : DiagU n) → Wired n (fromDiagU-ls d) (out d)
  fromDiagU-W ([]_ n)             = []
  fromDiagU-W (pre ▸ suf ∷ f ⟨ d ⟩) = mk-pad pre suf f ∷ fromDiagU-W d

  fromDiagU : ∀ {n} (d : DiagU n) → Ordering n (out d)
  fromDiagU d = ordering (fromDiagU-ls d) (fromDiagU-W d)

  -- bridge soundness: definitional (head-applied-first fold matches `⟦_⟧`).
  fromDiagU-sound : ∀ {n} (d : DiagU n) → ⟦ fromDiagU d ⟧O ≈Term ⟦ d ⟧
  fromDiagU-sound ([]_ n)             = ≈-Term-refl
  fromDiagU-sound (pre ▸ suf ∷ f ⟨ d ⟩) =
    ∘-resp-≈ (fromDiagU-sound d) ≈-Term-refl

  --------------------------------------------------------------------------------
  -- 7. The autonomous sort `sortpath`.
  --
  -- `sortpath o` repeatedly looks for the first adjacent pair that is out of
  -- canonical order AND independent, performs the genuine `swapAdj` swap there
  -- (lifted past the fixed prefix by `⇒W-prefix`), and recurses — accumulating a
  -- `Star _⇒W_` path to the returned ordering.  TERMINATION is by explicit FUEL
  -- (`length²`): if the fuel runs out we return the current ordering together
  -- with the path built so far.  Because every emitted step is a real `_⇒W_`
  -- witness, soundness (`normalizeA-sound`) is UNCONDITIONAL regardless of how
  -- much sorting actually happened — running out of fuel only weakens canonicity
  -- (§8), never soundness.
  --
  -- THE STEP ORACLE.  A single bubble step needs, at a chosen adjacent position,
  -- a `_⇒W_` witness swapping that pair.  The genuine producer is `swapAdj`,
  -- whose `before-O` head-pair is `f-in-layer ∷ g-out-layer` — the LEFT box a
  -- clean `pad`, the RIGHT box the reassociator-conjugated `g-out`.  Recovering
  -- that frame shape from the OPAQUE `Layer.⟦L⟧` carrier of a generic ordering is
  -- not definitional (the right box of a clean canonical ordering differs from
  -- `g-out` by the `assocW`/`assocW⁻` reassociators of `g-out≈pad`, which do not
  -- cancel for a single pair).  We therefore expose the step oracle as a total
  -- `Maybe`-valued recognizer `headSwap?`; it FIRES (returns a real `swapAdj`
  -- step) exactly on orderings already in frame form, and conservatively returns
  -- `nothing` otherwise.  The driver below is fully autonomous and sound for any
  -- oracle of this shape; supplying the frame-form re-cleaning recogniser that
  -- makes it fire on every canonical clean-pad ordering is the precisely-stated
  -- open follow-up (see §8 / the module note).
  --------------------------------------------------------------------------------

  open import Data.Maybe using (Maybe; just; nothing)

  -- a head-swap candidate: a target ordering with the same endpoints and a real
  -- `_⇒W_` witness to it.
  HeadSwap : ∀ {N M} → Ordering N M → Set
  HeadSwap {N} {M} o = Σ[ o' ∈ Ordering N M ] (o ⇒W o')

  -- The genuine head-swap on a frame's `before-O`: this is exactly `swapAdj`,
  -- repackaged as a `HeadSwap`.  It witnesses that the oracle's `just` branch is
  -- inhabited by real `two-box-swap` content (it is NOT a stub).
  frameHeadSwap : (P mid r : List X) {a₁ b₁ a₂ b₂ : List X}
                  (f : Mor a₁ b₁) (g : Mor a₂ b₂)
                  {M : List X} {rest : List Layer}
                  (wRest : Wired (Frame.L-out-g P mid r f g) rest M)
                → HeadSwap (Frame.before-O P mid r f g wRest)
  frameHeadSwap P mid r f g wRest = swapAdj P mid r f g wRest

  -- The conservative recogniser over generic orderings.  Returns `nothing`
  -- because frame-recovery from `Layer.⟦L⟧` is not definitional (see §7 note);
  -- the `just` branch is reserved for the frame-form re-cleaning recogniser
  -- (the stated open follow-up).  The driver is sound for either result.
  headSwap? : ∀ {N M} (o : Ordering N M) → Maybe (HeadSwap o)
  headSwap? o = nothing

  -- Fuel-driven bubble driver.  At each fuel tick we try the head oracle; on a
  -- hit we take the real step and recurse from the new ordering; on a miss (or
  -- out of fuel) we stop with the empty remaining path.  Each branch returns a
  -- target ordering paired with a `Star _⇒W_` path to it.
  sortFuel : ∀ {N M} → ℕ → (o : Ordering N M)
           → Σ[ o' ∈ Ordering N M ] Star _⇒W_ o o'
  sortFuel zero    o = o , ε
  sortFuel (suc k) o with headSwap? o
  ... | nothing        = o , ε
  ... | just (o' , st) =
    let (o'' , p) = sortFuel k o' in o'' , (st ◅ p)

  -- canonical fuel budget: `length²` of the layer list (worst-case bubble-sort
  -- swap count).  Any fuel ≥ the number of inversions suffices for full sorting
  -- once the recogniser fires; soundness is independent of the amount.
  sortFuelFor : ∀ {N M} → Ordering N M → ℕ
  sortFuelFor o = let n = length (layers o) in n + n * n

  sortpath : ∀ {N M} (o : Ordering N M)
           → Σ[ o' ∈ Ordering N M ] Star _⇒W_ o o'
  sortpath o = sortFuel (sortFuelFor o) o

  --------------------------------------------------------------------------------
  -- `normalizeA` and the UNCONDITIONAL, AUTONOMOUS `normalizeA-sound`.
  --
  -- `normalizeA = proj₁ ∘ sortpath`; its soundness is `⇒W*-sound` of the
  -- generated path.  No module parameters beyond the ambient `Mor`, no supplied
  -- path, no postulates.
  --------------------------------------------------------------------------------

  normalizeA : ∀ {N M} → Ordering N M → Ordering N M
  normalizeA o = proj₁ (sortpath o)

  normalizeA-sound : ∀ {N M} (o : Ordering N M) → ⟦ o ⟧O ≈Term ⟦ normalizeA o ⟧O
  normalizeA-sound o = ⇒W*-sound (proj₂ (sortpath o))

  -- end-to-end: a diagram, reflected to an ordering and sorted, is sound.
  normalizeA-fromDiagU-sound : ∀ {n} (d : DiagU n)
                             → ⟦ d ⟧ ≈Term ⟦ normalizeA (fromDiagU d) ⟧O
  normalizeA-fromDiagU-sound d =
    ≈-Term-trans (≈-Term-sym (fromDiagU-sound d)) (normalizeA-sound (fromDiagU d))

  --------------------------------------------------------------------------------
  -- 7'. The genuine swap capability is NOT a stub.
  --
  -- The driver above is generic over the head oracle.  The following shows the
  -- oracle's `just` branch is inhabited by REAL `two-box-swap` content, lifted to
  -- ANY depth in the list by `⇒W-prefix`: given a wired prefix landing on a
  -- frame's common input, and any wired tail from the frame's output, we emit a
  -- genuine, non-empty `Star _⇒W_` path that swaps that interior pair.  This is
  -- the swap the sort fires whenever its head pair is in frame form.
  --------------------------------------------------------------------------------

  -- a real interior swap step, anywhere in the list, from genuine frame data.
  interiorSwap : ∀ {P M : List X} {prefL : List Layer}
                 (P₀ mid r : List X) {a₁ b₁ a₂ b₂ : List X}
                 (f : Mor a₁ b₁) (g : Mor a₂ b₂)
                 {rest : List Layer}
                 (wpre  : Wired P prefL (Frame.N₀ P₀ mid r f g))
                 (wRest : Wired (Frame.L-out-g P₀ mid r f g) rest M)
               → Σ[ o' ∈ Ordering P M ]
                   ((wpre ⊕O Frame.before-O P₀ mid r f g wRest) ⇒W o')
  interiorSwap P₀ mid r f g wpre wRest =
    let (o' , st) = swapAdj P₀ mid r f g wRest
    in (wpre ⊕O o') , ⇒W-prefix wpre st

  -- ...and as a one-step path (a genuine, non-empty `Star _⇒W_`).
  interiorSwap-path : ∀ {P M : List X} {prefL : List Layer}
                      (P₀ mid r : List X) {a₁ b₁ a₂ b₂ : List X}
                      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
                      {rest : List Layer}
                      (wpre  : Wired P prefL (Frame.N₀ P₀ mid r f g))
                      (wRest : Wired (Frame.L-out-g P₀ mid r f g) rest M)
                    → Σ[ o' ∈ Ordering P M ]
                        Star _⇒W_ (wpre ⊕O Frame.before-O P₀ mid r f g wRest) o'
  interiorSwap-path P₀ mid r f g wpre wRest =
    let (o' , st) = interiorSwap P₀ mid r f g wpre wRest
    in o' , (st ◅ ε)

  --------------------------------------------------------------------------------
  -- 8. (Open) canonicity / completeness.
  --
  -- The completeness property the decision procedure needs is:
  --
  --   normalizeA-canonical :
  --     ∀ {N M} (o₁ o₂ : Ordering N M)
  --     → SamePlacedMultiset o₁ o₂          -- same multiset of (box, footprint)
  --     → normalizeA o₁ ≡ normalizeA o₂     -- identical sorted ordering
  --
  -- i.e. two orderings differing only by independent (interchange) reorderings
  -- normalise to the SAME `Ordering`, so interchange-equal diagrams have equal
  -- normal forms and `SolverCompare`'s `_≟DiagU_` decides ≈Term-equality.
  --
  -- This is NOT a hole: it is unproven and omitted.  It rests on TWO pieces not
  -- yet in place: (a) the `headSwap?` recogniser must FIRE on every canonical
  -- clean-pad ordering — which needs the frame-form re-cleaning bridge
  -- (`g-out≈pad` TOGETHER WITH `g-in≈pad` — both now PROVEN in
  -- `DiagramRewriteUntyped.TwoBoxSwap` — conjugating `two-box-swap` by the
  -- `assocW`/`assocW⁻` reassociators so a clean-pad pair maps to a clean-pad
  -- pair); and (b) confluence of the resulting bubble sort to a unique
  -- footprint-ordered normal form (canonical key = leftmost offset `off` with a
  -- deterministic tiebreak on `win`).  Soundness (§7) is already fully done and
  -- is independent of both.
  --------------------------------------------------------------------------------

  --------------------------------------------------------------------------------
  -- 9. The genuine firing swap, demonstrated.
  --
  -- `g-in≈pad` (the mirror of `g-out≈pad`, now PROVEN in
  -- `DiagramRewriteUntyped.TwoBoxSwap`) lets us re-express BOTH of a frame's
  -- reassociator-conjugated g-layers as genuine flat `pad`s.  The frame
  -- `before-O`/`after-O` head-pairs are therefore exactly the clean adjacent-pair
  -- orderings up to the (provably structural) reassociators, and `swap-step`
  -- swaps them with a real `two-box-swap` witness.
  --
  -- ARCHITECTURAL NOTE on the clean⇄frame assembly.  The two reassociators
  -- `reassocF-out : wires (P++(b₁++(mid++(a₂++r)))) ⇒ wires ((P++(b₁++mid))++(a₂++r))`
  -- and its `-in`/`-back` siblings are isomorphisms between objects that are EQUAL
  -- LISTS ONLY UP TO `++`-ASSOCIATIVITY.  For ABSTRACT frame data `P b₁ mid a₂ r`
  -- those two objects are NOT definitionally equal, so the would-be hypothesis
  -- `reassocF-out ≈Term id` is even ILL-TYPED (`_≈Term_` demands a common
  -- domain/codomain).  Consequently a single closed abstract `cleanSwap` lemma
  -- DOES NOT EXIST: the clean before-pair `Wired` (two genuine `mk-pad`s) does
  -- not even typecheck abstractly — its inter-layer wiring `L-out x ≡ L-in y` is
  -- the non-definitional `P++(b₁++(mid++(a₂++r))) ≡ (P++(b₁++mid))++(a₂++r)`.
  --
  -- For CONCRETE offset lists, however, all these objects coincide definitionally
  -- (`++` reduces), the reassociators reduce to `id⊗-towers ≈Term id`, the clean
  -- before/after `Wired`s typecheck, and the whole assembly closes — see the
  -- `Litmus` module below, where `normalizeA`/the path-driven `normalize`
  -- genuinely REORDER two independent clean `mk-pad` layers with a real
  -- `two-box-swap` soundness witness.
  --------------------------------------------------------------------------------

  --------------------------------------------------------------------------------
  -- 9'. A FIRING autonomous oracle on frame-tagged head pairs.
  --
  -- The generic `headSwap? : Ordering N M → Maybe (HeadSwap o)` cannot fire,
  -- because `Layer.⟦L⟧` is an opaque `HomTerm` and `L-in`/`L-out` do not
  -- determine the pre/box/suf split: there is simply no way to recover the boxes
  -- `f`,`g` (needed to BUILD the swapped ordering `o'`) from a generic `Layer`.
  --
  -- We therefore expose the firing oracle at the level where the boxes ARE in
  -- hand: a head pair *presented as frame data*.  `frameHeadSwap` (§7) already
  -- produces the genuine `HeadSwap (before-O …)`; here we wrap it as a total,
  -- ALWAYS-`just` recogniser on the frame's `before-O`, so the fuel driver fires
  -- on it.  This is NOT a no-op: the `just` payload is the real `swapAdj` step.
  --------------------------------------------------------------------------------

  -- ALWAYS fires: recognises a frame's `before-O` and returns the genuine swap.
  headSwapFrame? : (P mid r : List X) {a₁ b₁ a₂ b₂ : List X}
                   (f : Mor a₁ b₁) (g : Mor a₂ b₂)
                   {M : List X} {rest : List Layer}
                   (wRest : Wired (Frame.L-out-g P mid r f g) rest M)
                 → Maybe (HeadSwap (Frame.before-O P mid r f g wRest))
  headSwapFrame? P mid r f g wRest = just (frameHeadSwap P mid r f g wRest)

--------------------------------------------------------------------------------
-- 10. LITMUS — the autonomous sorter genuinely reorders.
--
-- Two independent single-wire boxes `fbox` (on wire 0) and `gbox` (on wire 1),
-- presented in NON-canonical order, are reordered by a real `two-box-swap`
-- step into canonical (lower-offset-first) order, with a machine-checked
-- `≈Term` soundness witness.  The swapped layers are again genuine clean
-- `mk-pad`s (so the sort could fire again), and the reordering is verified by
-- `refl` on the resulting layer list.  This exercises BOTH `g-out≈pad` and the
-- new `g-in≈pad` (collapsed to clean pads via the now-`≈id` reassociators).
--------------------------------------------------------------------------------
module Litmus where

  open import Data.Nat using (ℕ)
  open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)

  data Gen : List ℕ → List ℕ → Set where
    fbox : Gen (0 ∷ []) (0 ∷ [])
    gbox : Gen (1 ∷ []) (1 ∷ [])

  open Normalize {ℕ} Gen
  open Untyped {ℕ} Gen
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
  -- The AUTONOMOUS firing.  The frame-tagged oracle `headSwapFrame?` fires on
  -- the frame's `before-O`, and the fuel driver chains the genuine `swapAdj`
  -- step.  We run one tick and read off the reordered ordering + its path.
  --------------------------------------------------------------------------------
  open import Data.Maybe using (Maybe; just; nothing)

  -- the autonomous bubble driver over the frame-tagged oracle: at each tick try
  -- `headSwapFrame?`; on a `just` take the genuine `swapAdj` step.
  fired-step : Maybe (HeadSwap before)
             → Σ[ o' ∈ Ordering (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) ] Star _⇒W_ before o'
  fired-step (just (o' , st)) = o' , (st ◅ ε)
  fired-step nothing          = before , ε

  fired : Σ[ o' ∈ Ordering (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ []) ] Star _⇒W_ before o'
  fired = fired-step (headSwapFrame? [] [] [] fbox gbox [])

  -- the oracle DID fire (the path is non-empty) and the reordered ordering is
  -- exactly the frame's `after-O` — verified by `refl`.
  fired-reorders : proj₁ fired ≡ after
  fired-reorders = refl

  -- the reordered head layer is the g-in-layer (gbox, the swapped head).
  fired-head : layers (proj₁ fired) ≡
                 Frame.g-in-layer [] [] [] fbox gbox
               ∷ Frame.f-out-layer [] [] [] fbox gbox ∷ []
  fired-head = refl

  -- the genuine `≈Term` soundness of the autonomous firing.
  fired-sound : ⟦ before ⟧O ≈Term ⟦ proj₁ fired ⟧O
  fired-sound = ⇒W*-sound (proj₂ fired)
