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
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open import Data.List.Properties using (≡-dec)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped

module Normalize {X : Set} (_≟X_ : DecidableEquality X)
                 (Mor : List X → List X → Set) where

  -- UIP on the wire lists, via Hedberg (decidable equality), --without-K.
  private
    ≡-irrelevantL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevantL = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)

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
  -- 11. AUTONOMOUS DiagU-level recognition: reading frame data off the boxes.
  --
  -- The blocker for the generic `headSwap? : Ordering N M → Maybe (HeadSwap o)`
  -- is that a `Layer` ERASES its `pre`/`suf`/box into the opaque `⟦L⟧`.  A
  -- `DiagU` layer `px ▸ sx ∷ fx ⟨ rest ⟩` does NOT: it carries the box `fx`
  -- (hence its `dom`/`cod`) and the flat offsets `px sx` explicitly.  So a
  -- recogniser CAN read off the footprint and decide independence/orientation.
  --
  -- We work on a head pair of a `DiagU`, i.e. on the constructor pattern
  --   px ▸ sx ∷ fx ⟨ py ▸ sy ∷ fy ⟨ rest ⟩ ⟩
  -- where `fx : Mor ax bx` fires FIRST and `fy : Mor ay by` SECOND.  The
  -- `DiagU` typing forces the inter-layer wiring DEFINITIONALLY:
  --
  --   py ++ (ay ++ sy)  ≡  px ++ (bx ++ sx)            -- (★)  the index of the
  --                                                    --      inner sub-diagram
  --------------------------------------------------------------------------------

  open import Data.Nat.Properties using (_≟_)

  -- Footprint of a single DiagU head layer, read directly off `pre`/box.
  fpHead : ∀ {a b} (pre suf : List X) → Mor a b → Footprint
  fpHead {a} {b} pre suf f = footprint (length pre) (length a) (length b)

  -- The canonical key for the sort: a layer's leftmost wire index `length pre`.
  keyHead : ∀ {a b} (pre suf : List X) → Mor a b → ℕ
  keyHead pre suf f = length pre

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
  -- by the caller (the DiagU constructor) — see `recogLeft-from-wiring`.
  --------------------------------------------------------------------------------

  -- The orientation decision purely on footprints (reuses §5' `orient`).
  headOrient : ∀ {ax bx ay by} (px sx py sy : List X)
               (fx : Mor ax bx) (fy : Mor ay by) → Orient
  headOrient {ax} {bx} {ay} {by} px sx py sy fx fy =
    orient (fpHead px sx fx) (fpHead py sy fy)

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
    input⇒sorted wRest = wstep (≈-Term-sym (head-swap-sound wRest))

  --------------------------------------------------------------------------------
  -- 11d. The CLEAN ↔ FRAME bridge for the `fy` (left) layer — PROVEN clean.
  --
  -- For a `LeftFit`, the SECOND DiagU layer `pad py sy ⟦fy⟧` (fy fires second)
  -- equals the frame's `f-out` layer DEFINITIONALLY once we rewrite `py≡P` and
  -- `sy≡mid++(bx++s)`:  `f-out = pad P (mid ++ (bx ++ s)) ⟦fy⟧`.  No reassociator
  -- residue on the fy side — it is a genuine clean flat `pad`.  We record this
  -- as a `≡` of layers (after the offset rewrites) to confirm the fit is exact.
  --------------------------------------------------------------------------------

  fy-layer≡f-out : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
                   (fit : LeftFit px sx py sy fx fy)
                 → mk-pad (LeftFit.P fit) (LeftFit.mid fit ++ (bx ++ LeftFit.s fit)) fy
                   ≡ LeftFrame.f-out-layer fit
  fy-layer≡f-out fit = refl

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

  open import Data.List.Properties using (++-assoc)

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
  castW-irr e e' rewrite ≡-irrelevantL e e' = ≈-Term-refl

  -- prepending one wire to a transport.
  castW-∷ : ∀ {x : X} {u v : List X} (e : u ≡ v)
          → id ⊗₁ castW e ≈Term castW (cong (x ∷_) e)
  castW-∷ refl = id⊗id≈id

  -- `liftW p` of a transport is the transport prefixed by `p`.
  liftW-castW : ∀ (p : List X) {u v : List X} (e : u ≡ v)
              → liftW p (castW e) ≈Term castW (cong (p ++_) e)
  liftW-castW []      e = castW-irr e (cong (_++_ []) e)
  liftW-castW (x ∷ p) e = begin
    id ⊗₁ liftW p (castW e)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (liftW-castW p e) ⟩
    id ⊗₁ castW (cong (p ++_) e)
      ≈⟨ castW-∷ (cong (p ++_) e) ⟩
    castW (cong (x ∷_) (cong (p ++_) e))
      ≈⟨ castW-irr _ _ ⟩
    castW (cong ((x ∷ p) ++_) e) ∎

  -- the structural +-associator IS the `++`-assoc transport (both α-free).
  assocW-castW : ∀ (p q s : List X)
               → assocW p q s ≈Term castW (sym (++-assoc p q s))
  assocW-castW []      q s = ≈-Term-refl
  assocW-castW (x ∷ p) q s = begin
    id ⊗₁ assocW p q s
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (assocW-castW p q s) ⟩
    id ⊗₁ castW (sym (++-assoc p q s))
      ≈⟨ castW-∷ (sym (++-assoc p q s)) ⟩
    castW (cong (x ∷_) (sym (++-assoc p q s)))
      ≈⟨ castW-irr _ _ ⟩
    castW (sym (++-assoc (x ∷ p) q s)) ∎

  assocW⁻-castW : ∀ (p q s : List X)
                → assocW⁻ p q s ≈Term castW (++-assoc p q s)
  assocW⁻-castW []      q s = ≈-Term-refl
  assocW⁻-castW (x ∷ p) q s = begin
    id ⊗₁ assocW⁻ p q s
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (assocW⁻-castW p q s) ⟩
    id ⊗₁ castW (++-assoc p q s)
      ≈⟨ castW-∷ (++-assoc p q s) ⟩
    castW (cong (x ∷_) (++-assoc p q s))
      ≈⟨ castW-irr _ _ ⟩
    castW (++-assoc (x ∷ p) q s) ∎

  --------------------------------------------------------------------------------
  -- 11e. (ISOLATED, Tier-3 residual) The CLEAN ↔ FRAME bridge for the `fx`
  --      (right) layer, and the DiagU index transport.
  --
  -- The FIRST DiagU layer `pad px sx ⟦fx⟧` (fx fires first) is, after the
  -- `LeftFit` rewrites `px≡P++(ay++mid)`, `sx≡s`, the genuine clean flat pad
  --   pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
  -- on the object  (P ++ (ay ++ mid)) ++ (ax ++ s).  The frame's `g-in` layer is
  -- the SAME box in grouped form, on the right-nested object
  --   N₀ = P ++ (ay ++ (mid ++ (ax ++ s)))
  -- and `Frame.g-in≈pad` (PROVEN in DiagramRewriteUntyped) relates them by the
  -- structural reassociators `reassocF-in`/`reassocB-in`:
  --
  --   g-in ≈Term reassocB-in ∘ pad (P++(ay++mid)) s (⟦box⟧ fx) ∘ reassocF-in.
  --
  -- The two objects differ by `++`-associativity ONLY; for ABSTRACT `P ay mid
  -- ax s` they are not definitionally equal, so the clean fx pad and `g-in` do
  -- not have a common (dom,cod) and `_≈Term_` between them is ILL-TYPED.  The
  -- bridge therefore requires a propositional index transport along
  --   ++-assoc : (P++(ay++mid)) ++ (ax++s) ≡ P ++ ((ay++mid) ++ (ax++s))   …etc.
  -- composed with the structural reassociators `reassocF-in`/`reassocB-in`
  -- (which the reassociators precisely realise as morphisms).  Collapsing the
  -- transport+reassociators to the identity is the single remaining surgery.
  --
  -- THE INDEX-CAST OBSTRUCTION (precise).  A DiagU built with the `LeftFit`
  -- offsets has OUTER index `px ++ (ax ++ sx) = (P ++ (ay ++ mid)) ++ (ax ++ s)`
  -- (left-nested at the top split), whereas the frame's `input-O` has domain
  -- `N₀ = P ++ (ay ++ (mid ++ (ax ++ s)))` (right-nested).  For ABSTRACT lists
  -- these are EQUAL only up to `++-assoc`, hence `⟦ fromDiagU … ⟧O` and
  -- `⟦ input-O … ⟧O` do NOT share a domain and `_≈Term_` between them is
  -- literally ILL-TYPED.  So the bridge needs a propositional object cast
  --   castₒ : (P++(ay++mid))++(ax++s) ≡ N₀                 (from ++-assoc)
  -- on the domain (and a matching one on the codomain), realised as the
  -- structural reassociators of `g-in≈pad`.
  --
  -- The PRECISE residual lemma (exact type), stated but NOT proven here so the
  -- module stays postulate-free and `--safe`.  Writing `n₀ = px ++ (ax ++ sx)`
  -- for the DiagU index and `castW : ∀ {u v} → u ≡ v → HomTerm (wires u)
  -- (wires v)` (= `≡⇒≈Term`-style object reshaper, e.g. `subst` of `id`):
  --
  --   fx-clean⇒g-in :
  --     ∀ {ax bx ay by} {px sx py sy}
  --       {fx : Mor ax bx} {fy : Mor ay by}
  --       (fit : LeftFit px sx py sy fx fy)
  --       {M rest} {d : DiagU (px ++ (bx ++ sx))}
  --       (wTail : Wired (LeftFrame.N₃ fit) rest M)
  --       (idx : py ++ (ay ++ sy) ≡ px ++ (bx ++ sx))      -- the DiagU wiring ★
  --     → castW (codcast …) ∘ ⟦ fromDiagU (px ▸ sx ∷ fx ⟨ py ▸ sy ∷ fy ⟨ d ⟩ ⟩) ⟧O
  --       ≈Term  ⟦ LeftFrame.input-O fit wTail ⟧O ∘ castW (domcast …)
  --
  -- where `domcast : px++(ax++sx) ≡ N₀` and `codcast : out … ≡ M` are the
  -- `++-assoc` index transports.  It is the EXACT abstract analogue of the
  -- `Litmus`'s `cA≈after`/`cB≈before` (discharged CONCRETELY below, where the
  -- reassociators reduce to `id` and the casts are `refl`).  Once it is in hand,
  -- the autonomous DiagU swap is `≈-Term-trans (fx-clean⇒g-in …) (input⇒sorted
  -- …)`, and the bubble sort + its soundness follow by chaining exactly as
  -- `normalizeA`/`normalizeA-sound` already do for the `_⇒W_` driver.  The frame
  -- side (`LeftFrame.input⇒sorted`) is PROVEN and exercised in the DiagU litmus
  -- below; only this clean⇄grouped index cast remains.

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
  reassocF-in≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g = begin
    assocW pre (a₁ ++ mid) (a₂ ++ r) ∘ liftW pre (assocW a₁ mid (a₂ ++ r))
      ≈⟨ ∘-resp-≈ (assocW-castW pre (a₁ ++ mid) (a₂ ++ r))
                  (≈-Term-trans (liftW-resp pre (assocW-castW a₁ mid (a₂ ++ r)))
                                (liftW-castW pre (sym (++-assoc a₁ mid (a₂ ++ r))))) ⟩
    castW (sym (++-assoc pre (a₁ ++ mid) (a₂ ++ r)))
      ∘ castW (cong (pre ++_) (sym (++-assoc a₁ mid (a₂ ++ r))))
      ≈⟨ castW-∘ _ _ ⟩
    castW (trans (cong (pre ++_) (sym (++-assoc a₁ mid (a₂ ++ r))))
                 (sym (++-assoc pre (a₁ ++ mid) (a₂ ++ r))))
      ≈⟨ castW-irr _ _ ⟩
    castW (sym (domeq pre a₁ mid a₂ r)) ∎

  -- reassocB-in collapses to the codomain cast.
  reassocB-in≈castW :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.reassocB-in pre mid r f g
      ≈Term castW (domeq pre a₁ mid b₂ r)
  reassocB-in≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g = begin
    liftW pre (assocW⁻ a₁ mid (b₂ ++ r)) ∘ assocW⁻ pre (a₁ ++ mid) (b₂ ++ r)
      ≈⟨ ∘-resp-≈ (≈-Term-trans (liftW-resp pre (assocW⁻-castW a₁ mid (b₂ ++ r)))
                                (liftW-castW pre (++-assoc a₁ mid (b₂ ++ r))))
                  (assocW⁻-castW pre (a₁ ++ mid) (b₂ ++ r)) ⟩
    castW (cong (pre ++_) (++-assoc a₁ mid (b₂ ++ r)))
      ∘ castW (++-assoc pre (a₁ ++ mid) (b₂ ++ r))
      ≈⟨ castW-∘ _ _ ⟩
    castW (trans (++-assoc pre (a₁ ++ mid) (b₂ ++ r))
                 (cong (pre ++_) (++-assoc a₁ mid (b₂ ++ r))))
      ≈⟨ castW-irr _ _ ⟩
    castW (domeq pre a₁ mid b₂ r) ∎

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
  fx-clean⇒g-in-core pre mid r {a₁} {b₁} {a₂} {b₂} f g = begin
    Frame.g-in pre mid r f g
      ≈⟨ Frame.g-in≈pad pre mid r f g ⟩
    Frame.reassocB-in pre mid r f g
      ∘ pad (pre ++ (a₁ ++ mid)) r (⟦box⟧ g)
      ∘ Frame.reassocF-in pre mid r f g
      ≈⟨ ∘-resp-≈ (reassocB-in≈castW pre mid r f g)
           (∘-resp-≈ ≈-Term-refl (reassocF-in≈castW pre mid r f g)) ⟩
    castW (domeq pre a₁ mid b₂ r)
      ∘ pad (pre ++ (a₁ ++ mid)) r (⟦box⟧ g)
      ∘ castW (sym (domeq pre a₁ mid a₂ r)) ∎

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
  reassocF-out≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g = begin
    assocW pre (b₁ ++ mid) (a₂ ++ r) ∘ liftW pre (assocW b₁ mid (a₂ ++ r))
      ≈⟨ ∘-resp-≈ (assocW-castW pre (b₁ ++ mid) (a₂ ++ r))
                  (≈-Term-trans (liftW-resp pre (assocW-castW b₁ mid (a₂ ++ r)))
                                (liftW-castW pre (sym (++-assoc b₁ mid (a₂ ++ r))))) ⟩
    castW (sym (++-assoc pre (b₁ ++ mid) (a₂ ++ r)))
      ∘ castW (cong (pre ++_) (sym (++-assoc b₁ mid (a₂ ++ r))))
      ≈⟨ castW-∘ _ _ ⟩
    castW (trans (cong (pre ++_) (sym (++-assoc b₁ mid (a₂ ++ r))))
                 (sym (++-assoc pre (b₁ ++ mid) (a₂ ++ r))))
      ≈⟨ castW-irr _ _ ⟩
    castW (sym (domeq pre b₁ mid a₂ r)) ∎

  -- reassocB-out collapses to the codomain cast at offset b₁.
  reassocB-out≈castW :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.reassocB-out pre mid r f g
      ≈Term castW (domeq pre b₁ mid b₂ r)
  reassocB-out≈castW pre mid r {a₁} {b₁} {a₂} {b₂} f g = begin
    liftW pre (assocW⁻ b₁ mid (b₂ ++ r)) ∘ assocW⁻ pre (b₁ ++ mid) (b₂ ++ r)
      ≈⟨ ∘-resp-≈ (≈-Term-trans (liftW-resp pre (assocW⁻-castW b₁ mid (b₂ ++ r)))
                                (liftW-castW pre (++-assoc b₁ mid (b₂ ++ r))))
                  (assocW⁻-castW pre (b₁ ++ mid) (b₂ ++ r)) ⟩
    castW (cong (pre ++_) (++-assoc b₁ mid (b₂ ++ r)))
      ∘ castW (++-assoc pre (b₁ ++ mid) (b₂ ++ r))
      ≈⟨ castW-∘ _ _ ⟩
    castW (trans (++-assoc pre (b₁ ++ mid) (b₂ ++ r))
                 (cong (pre ++_) (++-assoc b₁ mid (b₂ ++ r))))
      ≈⟨ castW-irr _ _ ⟩
    castW (domeq pre b₁ mid b₂ r) ∎

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
  fy-sorted⇒g-out-core pre mid r {a₁} {b₁} {a₂} {b₂} f g = begin
    Frame.g-out pre mid r f g
      ≈⟨ Frame.g-out≈pad pre mid r f g ⟩
    Frame.reassocB-out pre mid r f g
      ∘ pad (pre ++ (b₁ ++ mid)) r (⟦box⟧ g)
      ∘ Frame.reassocF-out pre mid r f g
      ≈⟨ ∘-resp-≈ (reassocB-out≈castW pre mid r f g)
           (∘-resp-≈ ≈-Term-refl (reassocF-out≈castW pre mid r f g)) ⟩
    castW (domeq pre b₁ mid b₂ r)
      ∘ pad (pre ++ (b₁ ++ mid)) r (⟦box⟧ g)
      ∘ castW (sym (domeq pre b₁ mid a₂ r)) ∎

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
  -- The clean fy-layer `pad py sy ⟦fy⟧` is DEFINITIONALLY `Frame.f-out`
  -- (`fy-layer≡f-out`), so it appears as `Frame.f-out P mid s fy fx` here.
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
                {M} {rest} wTail = begin
    ⟦ wTail ⟧W ∘ F.f-out ∘ castMidB ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl bridge) ⟩
    ⟦ wTail ⟧W ∘ F.f-out ∘ (F.g-in ∘ castDom)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    ⟦ wTail ⟧W ∘ (F.f-out ∘ F.g-in) ∘ castDom
      ≈⟨ ≈-Term-sym assoc ⟩
    (⟦ wTail ⟧W ∘ (F.f-out ∘ F.g-in)) ∘ castDom
      ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
    ((⟦ wTail ⟧W ∘ F.f-out) ∘ F.g-in) ∘ castDom ∎
    where
      module F = Frame P mid s fy fx
      castMidB = castW (domeq P ay mid bx s)
      castDom  = castW (domeq P ay mid ax s)
      -- g-in ∘ castDom ≈ castMidB ∘ pad …  (the core bridge + cast cancel)
      bridge : castMidB ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
             ≈Term F.g-in ∘ castDom
      bridge = begin
        castMidB ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
          ≈⟨ ≈-Term-sym idʳ ⟩
        (castMidB ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)) ∘ id
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym (castW-sym-r (domeq P ay mid ax s))) ⟩
        (castMidB ∘ pad (P ++ (ay ++ mid)) s (⟦box⟧ fx))
          ∘ (castW (sym (domeq P ay mid ax s)) ∘ castDom)
          ≈⟨ assoc ⟩
        castMidB ∘ (pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
          ∘ (castW (sym (domeq P ay mid ax s)) ∘ castDom))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        castMidB ∘ ((pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
          ∘ castW (sym (domeq P ay mid ax s))) ∘ castDom)
          ≈⟨ ≈-Term-sym assoc ⟩
        (castMidB ∘ (pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
          ∘ castW (sym (domeq P ay mid ax s)))) ∘ castDom
          ≈⟨ ∘-resp-≈ (≈-Term-sym (fx-clean⇒g-in-core P mid s fy fx)) ≈-Term-refl ⟩
        F.g-in ∘ castDom ∎

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
    ≈-Term-trans (fx-clean⇒g-in fit wTail)
      (∘-resp-≈ (sound (LeftFrame.input⇒sorted fit wTail)) ≈-Term-refl)

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
  ⟦substDiagU⟧ refl d = ≈-Term-trans idʳ (≈-Term-sym idˡ)

  -- prepending a clean DiagU layer post-composes its `pad` onto `⟦_⟧`.
  ⟦cons⟧ : ∀ {a b} (pre suf : List X) (f : Mor a b)
           (d : DiagU (pre ++ (b ++ suf)))
         → ⟦ pre ▸ suf ∷ f ⟨ d ⟩ ⟧ ≈Term ⟦ d ⟧ ∘ pad pre suf (⟦box⟧ f)
  ⟦cons⟧ pre suf f d = ≈-Term-refl

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
  -- input/output cast bookkeeping; the litmus (§ below) machine-checks one fire.
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
  swapHeadD-out-sound {ax} {bx} {ay} {by} P mid s fx fy dSorted = begin
    castW out-eq ∘ (⟦ inner ⟧ ∘ F.f-in)
      ≈⟨ ≈-Term-sym assoc ⟩
    (castW out-eq ∘ ⟦ inner ⟧) ∘ F.f-in
      ≈⟨ ∘-resp-≈ key ≈-Term-refl ⟩
    (⟦ innerD ⟧ ∘ castW (sym e)) ∘ F.f-in
      ≈⟨ assoc ⟩
    ⟦ innerD ⟧ ∘ (castW (sym e) ∘ F.f-in) ∎
    where
      module F = Frame P mid s fy fx
      innerD = (P ++ (by ++ mid)) ▸ s ∷ fx ⟨ dSorted ⟩
      inner  = substDiagU (domeq P by mid ax s) innerD
      out-eq = substDiagU-out (domeq P by mid ax s) innerD
      e      = domeq P by mid ax s
      -- castW e ∘ castW (sym e) ≈ id  (the other cancellation order).
      cancel-r : castW e ∘ castW (sym e) ≈Term id
      cancel-r = ≈-Term-trans (∘-resp-≈ (castW-irr e (sym (sym e))) ≈-Term-refl)
                              (castW-sym-r (sym e))
      cancel-out : castW out-eq ∘ castW (sym out-eq) ≈Term id
      cancel-out = ≈-Term-trans (∘-resp-≈ (castW-irr out-eq (sym (sym out-eq))) ≈-Term-refl)
                                (castW-sym-r (sym out-eq))
      key : castW out-eq ∘ ⟦ inner ⟧ ≈Term ⟦ innerD ⟧ ∘ castW (sym e)
      key = begin
        castW out-eq ∘ ⟦ inner ⟧
          ≈⟨ ≈-Term-sym idʳ ⟩
        (castW out-eq ∘ ⟦ inner ⟧) ∘ id
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym cancel-r) ⟩
        (castW out-eq ∘ ⟦ inner ⟧) ∘ (castW e ∘ castW (sym e))
          ≈⟨ ≈-Term-sym assoc ⟩
        ((castW out-eq ∘ ⟦ inner ⟧) ∘ castW e) ∘ castW (sym e)
          ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
        (castW out-eq ∘ (⟦ inner ⟧ ∘ castW e)) ∘ (castW (sym e))
          ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (⟦substDiagU⟧ e innerD)) ≈-Term-refl ⟩
        (castW out-eq ∘ (castW (sym out-eq) ∘ ⟦ innerD ⟧)) ∘ castW (sym e)
          ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
        ((castW out-eq ∘ castW (sym out-eq)) ∘ ⟦ innerD ⟧) ∘ castW (sym e)
          ≈⟨ ∘-resp-≈ (∘-resp-≈ cancel-out ≈-Term-refl) ≈-Term-refl ⟩
        (id ∘ ⟦ innerD ⟧) ∘ castW (sym e)
          ≈⟨ ∘-resp-≈ idˡ ≈-Term-refl ⟩
        ⟦ innerD ⟧ ∘ castW (sym e) ∎

  --------------------------------------------------------------------------------
  -- 11h. The INPUT clean DiagU of an out-of-order head pair, and the ABSTRACT
  -- per-swap soundness `⟦ input ⟧ ≈Term ⟦ swapped ⟧`.
  --
  -- For a recognised `LeftFit` the input head order is fx-first (the right box,
  -- higher offset) then fy.  Both are genuine clean `pad`-layers; the inter-layer
  -- `++`-assoc re-index between fx and fy is absorbed by `substDiagU` along
  -- `domeq P ay mid bx s` (soundness `⟦substDiagU⟧`).  `dInput`/`swapHeadD-out`
  -- live at the SAME input index `N₀`, so `⟦ input ⟧ ≈Term ⟦ swapped ⟧` is the
  -- honest per-swap soundness — the abstract analogue of `Litmus.litDiagUSwap`.
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
           (leftFit P mid s refl refl refl refl) dRest =
    P ▸ (mid ++ (ax ++ s)) ∷ fy
      ⟨ substDiagU (domeq P by mid ax s)
          ((P ++ (by ++ mid)) ▸ s ∷ fx
            ⟨ substDiagU (sym (domeq P by mid bx s)) dRest ⟩) ⟩

  -- ABSTRACT per-swap soundness: the input (fx-first) and swapped (fy-first)
  -- clean DiagUs share endpoints `wires N₀ → wires (out dRest)` and have equal
  -- interpretations in the free monoidal category.  Proven by chaining the
  -- already-PROVEN `swapHeadD-out-sound` (swapped side) and `diagU-swap-sound`
  -- (input ⇒ sorted, = `two-box-swap`) with the `castW`/`⟦substDiagU⟧` algebra.
  dSwapped-is-out :
    ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
      (fit : LeftFit px sx py sy fx fy)
      (dRest : DiagU (LeftFrame.N₃ fit))
    → dSwapped fit dRest
      ≡ swapHeadD-out fit
          (substDiagU (sym (domeq (LeftFit.P fit) by (LeftFit.mid fit) bx (LeftFit.s fit))) dRest)
  dSwapped-is-out (leftFit P mid s refl refl refl refl) dRest = refl

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
  castW-cancelʳ refl {A} {B} h =
    ≈-Term-trans (≈-Term-sym idʳ) (≈-Term-trans h idʳ)

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
               (leftFit P mid s refl refl refl refl) dRest = begin
    ⟦ substDiagU e0 fxL ⟧ ∘ castW e0
      ≈⟨ ⟦substDiagU⟧ e0 fxL ⟩
    castW (sym o0) ∘ ⟦ fxL ⟧
      ≈⟨ ∘-resp-≈ ≈-Term-refl refl-bridge ⟩
    castW (sym o0) ∘ (⟦ substDiagU e1 fyL ⟧ ∘ padfx)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ subst1 ≈-Term-refl) ⟩
    castW (sym o0) ∘ ((castW (sym o1) ∘ rhs1) ∘ padfx)
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    castW (sym o0) ∘ (castW (sym o1) ∘ (rhs1 ∘ padfx))
      ≈⟨ ≈-Term-sym assoc ⟩
    (castW (sym o0) ∘ castW (sym o1)) ∘ (rhs1 ∘ padfx)
      ≈⟨ ∘-resp-≈ (≈-Term-trans (castW-∘ (sym o1) (sym o0))
                     (castW-irr _ (sym (dInput-out (leftFit P mid s refl refl refl refl) dRest))))
                  ≈-Term-refl ⟩
    castW (sym (dInput-out (leftFit P mid s refl refl refl refl) dRest)) ∘ (rhs1 ∘ padfx)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (chainR) ⟩
    castW (sym (dInput-out (leftFit P mid s refl refl refl refl) dRest))
      ∘ (⟦ dRest ⟧ ∘ (F.f-out ∘ (castW (domeq P ay mid bx s) ∘ padfx))) ∎
    where
      module F = Frame P mid s fy fx
      e0   = domeq P ay mid ax s
      e1   = sym (domeq P ay mid bx s)
      padfx = pad (P ++ (ay ++ mid)) s (⟦box⟧ fx)
      fyL  = P ▸ (mid ++ (bx ++ s)) ∷ fy ⟨ dRest ⟩
      fxL  = (P ++ (ay ++ mid)) ▸ s ∷ fx ⟨ substDiagU e1 fyL ⟩
      o0   = substDiagU-out e0 fxL
      o1   = substDiagU-out e1 fyL
      refl-bridge : ⟦ fxL ⟧ ≈Term ⟦ substDiagU e1 fyL ⟧ ∘ padfx
      refl-bridge = ≈-Term-refl
      rhs1 = (⟦ dRest ⟧ ∘ F.f-out) ∘ castW (sym e1)
      -- (rhs1 ∘ padfx) ≈ ⟦dRest⟧ ∘ (f-out ∘ (castW(domeq …bx…) ∘ padfx))
      chainR : rhs1 ∘ padfx
             ≈Term ⟦ dRest ⟧ ∘ (F.f-out ∘ (castW (domeq P ay mid bx s) ∘ padfx))
      chainR = begin
        ((⟦ dRest ⟧ ∘ F.f-out) ∘ castW (sym e1)) ∘ padfx
          ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
        (⟦ dRest ⟧ ∘ (F.f-out ∘ castW (sym e1))) ∘ padfx
          ≈⟨ assoc ⟩
        ⟦ dRest ⟧ ∘ ((F.f-out ∘ castW (sym e1)) ∘ padfx)
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        ⟦ dRest ⟧ ∘ (F.f-out ∘ (castW (sym e1) ∘ padfx))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (castW-irr (sym e1) (domeq P ay mid bx s)) ≈-Term-refl)) ⟩
        ⟦ dRest ⟧ ∘ (F.f-out ∘ (castW (domeq P ay mid bx s) ∘ padfx)) ∎
      -- ⟦ substDiagU e1 fyL ⟧ ≈ castW(sym o1) ∘ (⟦dRest⟧ ∘ f-out) ∘ castW(sym e1)
      subst1 : ⟦ substDiagU e1 fyL ⟧
             ≈Term castW (sym o1) ∘ rhs1
      subst1 = castW-cancelʳ e1 (begin
        ⟦ substDiagU e1 fyL ⟧ ∘ castW e1
          ≈⟨ ⟦substDiagU⟧ e1 fyL ⟩
        castW (sym o1) ∘ ⟦ fyL ⟧
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym idʳ) ⟩
        castW (sym o1) ∘ ((⟦ dRest ⟧ ∘ F.f-out) ∘ id)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym (castW-sym-r e1))) ⟩
        castW (sym o1) ∘ ((⟦ dRest ⟧ ∘ F.f-out) ∘ (castW (sym e1) ∘ castW e1))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        castW (sym o1) ∘ (((⟦ dRest ⟧ ∘ F.f-out) ∘ castW (sym e1)) ∘ castW e1)
          ≈⟨ ≈-Term-sym assoc ⟩
        (castW (sym o1) ∘ ((⟦ dRest ⟧ ∘ F.f-out) ∘ castW (sym e1))) ∘ castW e1 ∎)

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
                 (leftFit P mid s refl refl refl refl) dRest = begin
    castW (dSwapped-out (leftFit {fx = fx} {fy = fy} P mid s refl refl refl refl) dRest)
      ∘ ⟦ dSwapped (leftFit {fx = fx} {fy = fy} P mid s refl refl refl refl) dRest ⟧
      ≈⟨ ∘-resp-≈ (castW-irr _ (trans ohd o'')) ≈-Term-refl ⟩
    castW (trans ohd o'') ∘ ⟦ swapHeadD-out (leftFit {fx = fx} {fy = fy} P mid s refl refl refl refl) dSorted ⟧
      ≈⟨ ∘-resp-≈ (≈-Term-sym (castW-∘ ohd o'')) ≈-Term-refl ⟩
    (castW o'' ∘ castW ohd) ∘ ⟦ swapHeadD-out (leftFit {fx = fx} {fy = fy} P mid s refl refl refl refl) dSorted ⟧
      ≈⟨ assoc ⟩
    castW o'' ∘ (castW ohd ∘ ⟦ swapHeadD-out (leftFit {fx = fx} {fy = fy} P mid s refl refl refl refl) dSorted ⟧)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (swapHeadD-out-sound P mid s fx fy dSorted) ⟩
    castW o'' ∘ ((⟦ dSorted ⟧ ∘ padfx') ∘ castW (sym e') ∘ F.f-in)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    castW o'' ∘ (((⟦ dSorted ⟧ ∘ padfx') ∘ castW (sym e')) ∘ F.f-in)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ gpart ≈-Term-refl) ⟩
    castW o'' ∘ ((castW (sym o'') ∘ (⟦ fromDiagU-W dRest ⟧W ∘ F.g-out)) ∘ F.f-in)
      ≈⟨ collapse ⟩
    (⟦ fromDiagU-W dRest ⟧W ∘ F.g-out) ∘ F.f-in ∎
    where
      module F = Frame P mid s fy fx
      e'      = domeq P by mid ax s
      ebx     = domeq P by mid bx s
      padfx'  = pad (P ++ (by ++ mid)) s (⟦box⟧ fx)
      dSorted = substDiagU (sym ebx) dRest
      innerD' = (P ++ (by ++ mid)) ▸ s ∷ fx ⟨ dSorted ⟩
      ohd     = substDiagU-out e' innerD'
      o''     = substDiagU-out (sym ebx) dRest
      collapse : castW o'' ∘ ((castW (sym o'') ∘ (⟦ fromDiagU-W dRest ⟧W ∘ F.g-out)) ∘ F.f-in)
               ≈Term (⟦ fromDiagU-W dRest ⟧W ∘ F.g-out) ∘ F.f-in
      collapse = begin
        castW o'' ∘ ((castW (sym o'') ∘ G) ∘ F.f-in)
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        castW o'' ∘ (castW (sym o'') ∘ (G ∘ F.f-in))
          ≈⟨ ≈-Term-sym assoc ⟩
        (castW o'' ∘ castW (sym o'')) ∘ (G ∘ F.f-in)
          ≈⟨ ∘-resp-≈ (castW-sym-r-flip o'') ≈-Term-refl ⟩
        id ∘ (G ∘ F.f-in)
          ≈⟨ idˡ ⟩
        G ∘ F.f-in ∎
        where G = ⟦ fromDiagU-W dRest ⟧W ∘ F.g-out

      -- ⟦dSorted⟧ ≈ (castW(sym o'') ∘ ⟦dRest⟧) ∘ castW ebx
      dS : ⟦ dSorted ⟧ ≈Term (castW (sym o'') ∘ ⟦ dRest ⟧) ∘ castW ebx
      dS = castW-cancelʳ (sym ebx) (begin
        ⟦ dSorted ⟧ ∘ castW (sym ebx)
          ≈⟨ ⟦substDiagU⟧ (sym ebx) dRest ⟩
        castW (sym o'') ∘ ⟦ dRest ⟧
          ≈⟨ ≈-Term-sym idʳ ⟩
        (castW (sym o'') ∘ ⟦ dRest ⟧) ∘ id
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym (castW-sym-r-flip ebx)) ⟩
        (castW (sym o'') ∘ ⟦ dRest ⟧) ∘ (castW ebx ∘ castW (sym ebx))
          ≈⟨ ≈-Term-sym assoc ⟩
        ((castW (sym o'') ∘ ⟦ dRest ⟧) ∘ castW ebx) ∘ castW (sym ebx) ∎)
      frd : castW (sym o'') ∘ ⟦ dRest ⟧
          ≈Term castW (sym o'') ∘ ⟦ fromDiagU-W dRest ⟧W
      frd = ∘-resp-≈ ≈-Term-refl (≈-Term-sym (fromDiagU-sound dRest))
      -- ⟦dSorted⟧ ∘ padfx' ∘ castW(sym e') ≈ castW(sym o'') ∘ (⟦fromDiagU-W dRest⟧W ∘ g-out)
      gpart : (⟦ dSorted ⟧ ∘ padfx') ∘ castW (sym e')
            ≈Term castW (sym o'') ∘ (⟦ fromDiagU-W dRest ⟧W ∘ F.g-out)
      gpart = begin
        (⟦ dSorted ⟧ ∘ padfx') ∘ castW (sym e')
          ≈⟨ ∘-resp-≈ (∘-resp-≈ dS ≈-Term-refl) ≈-Term-refl ⟩
        (((castW (sym o'') ∘ ⟦ dRest ⟧) ∘ castW ebx) ∘ padfx') ∘ castW (sym e')
          ≈⟨ ∘-resp-≈ (∘-resp-≈ (∘-resp-≈ frd ≈-Term-refl) ≈-Term-refl) ≈-Term-refl ⟩
        (((castW (sym o'') ∘ ⟦ fromDiagU-W dRest ⟧W) ∘ castW ebx) ∘ padfx') ∘ castW (sym e')
          ≈⟨ assoc ⟩
        ((castW (sym o'') ∘ ⟦ fromDiagU-W dRest ⟧W) ∘ castW ebx) ∘ (padfx' ∘ castW (sym e'))
          ≈⟨ assoc ⟩
        (castW (sym o'') ∘ ⟦ fromDiagU-W dRest ⟧W)
          ∘ (castW ebx ∘ (padfx' ∘ castW (sym e')))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym (fy-sorted⇒g-out-core P mid s fy fx)) ⟩
        (castW (sym o'') ∘ ⟦ fromDiagU-W dRest ⟧W) ∘ F.g-out
          ≈⟨ assoc ⟩
        castW (sym o'') ∘ (⟦ fromDiagU-W dRest ⟧W ∘ F.g-out) ∎

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
    castW-cancelʳ (domeq P ay mid ax s) (begin
      (castW oeq ∘ ⟦ dIn ⟧) ∘ cax
        ≈⟨ assoc ⟩
      castW oeq ∘ (⟦ dIn ⟧ ∘ cax)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (dInput-frame fit dRest) ⟩
      castW oeq ∘ (castW (sym diO) ∘ FC)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl FC≈sorted) ⟩
      castW oeq ∘ (castW (sym diO) ∘ (⟦ sortedO ⟧O ∘ cax))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ dSwapped-frame-rearr ≈-Term-refl)) ⟩
      castW oeq ∘ (castW (sym diO) ∘ ((castW dsO ∘ ⟦ dSw ⟧) ∘ cax))
        ≈⟨ castLoop ⟩
      ⟦ dSw ⟧ ∘ cax ∎)
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
      FC≈sorted = ≈-Term-trans
        (∘-resp-≈ (≈-Term-sym (fromDiagU-sound dRest)) ≈-Term-refl)
        (diagU-swap-sound fit wTail)
      -- dSwapped-frame rearranged: ⟦sortedO⟧O ≈ castW dsO ∘ ⟦dSw⟧.
      dSwapped-frame-rearr : ⟦ sortedO ⟧O ≈Term castW dsO ∘ ⟦ dSw ⟧
      dSwapped-frame-rearr = ≈-Term-sym (dSwapped-frame fit dRest)
      -- the loop of output casts collapses to id, leaving ⟦dSw⟧ ∘ cax.
      castLoop : castW oeq ∘ (castW (sym diO) ∘ ((castW dsO ∘ ⟦ dSw ⟧) ∘ cax))
               ≈Term ⟦ dSw ⟧ ∘ cax
      castLoop = begin
        castW oeq ∘ (castW (sym diO) ∘ ((castW dsO ∘ ⟦ dSw ⟧) ∘ cax))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
        castW oeq ∘ (castW (sym diO) ∘ (castW dsO ∘ (⟦ dSw ⟧ ∘ cax)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        castW oeq ∘ ((castW (sym diO) ∘ castW dsO) ∘ (⟦ dSw ⟧ ∘ cax))
          ≈⟨ ≈-Term-sym assoc ⟩
        (castW oeq ∘ (castW (sym diO) ∘ castW dsO)) ∘ (⟦ dSw ⟧ ∘ cax)
          ≈⟨ ∘-resp-≈ loopId ≈-Term-refl ⟩
        id ∘ (⟦ dSw ⟧ ∘ cax)
          ≈⟨ idˡ ⟩
        ⟦ dSw ⟧ ∘ cax ∎
        where
          loopId : castW oeq ∘ (castW (sym diO) ∘ castW dsO) ≈Term id
          loopId = begin
            castW oeq ∘ (castW (sym diO) ∘ castW dsO)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (castW-∘ dsO (sym diO)) ⟩
            castW oeq ∘ castW (trans dsO (sym diO))
              ≈⟨ castW-∘ (trans dsO (sym diO)) oeq ⟩
            castW (trans (trans dsO (sym diO)) oeq)
              ≈⟨ castW-irr _ refl ⟩
            id ∎

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
    stripPrefix (x ∷ p)  (y ∷ xs) with x ≟X y
    ... | no  _    = nothing
    ... | yes refl with stripPrefix p xs
    ...   | nothing            = nothing
    ...   | just (ys , refl)   = just (ys , refl)

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
    leftFit? {ax} {bx} {ay} {by} px sx py sy fx fy
      with stripPrefix py px
    ... | nothing            = nothing
    ... | just (r1 , px≡)    with stripPrefix ay r1
    ...   | nothing             = nothing
    ...   | just (mid , r1≡)    with sy ≟L (mid ++ (bx ++ sx))
    ...     | no  _             = nothing
    ...     | yes sy≡           =
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

    -- recognise-then-swap on explicit head-pair data: tries `leftFit?`, and on a
    -- hit returns the firing `swapHeadD`.  This is the autonomous DiagU head step.
    recogSwapD : ∀ {ax bx ay by} (px sx py sy : List X)
                 (fx : Mor ax bx) (fy : Mor ay by)
               → Maybe (Σ[ fit ∈ LeftFit px sx py sy fx fy ]
                          ((dRest : DiagU (LeftFrame.N₃ fit)) → HeadSwapD fit dRest))
    recogSwapD px sx py sy fx fy with leftFit? px sx py sy fx fy
    ... | nothing  = nothing
    ... | just fit = just (fit , swapHeadD fit)

    --------------------------------------------------------------------------------
    -- 12c. `normalizeD` — fuel-driven bubble step on a recognised DiagU head.
    --
    -- `normalizeD` reduces a head pair to canonical (lower-offset-first) order by
    -- the genuine `swapHeadD` swap; the fuel argument bounds the number of bubble
    -- steps (`length² ≥ inversions`), and on `0` fuel / a non-recognised head it
    -- returns the input unchanged with the trivial witness.  Because the SWAPPED
    -- tail is re-indexed (by `substDiagU` along the non-definitional `++`-assoc
    -- `domeq`), a 2-layer head of the *output* of an ABSTRACT step cannot be
    -- destructured by unification, so abstract multi-step recursion is not
    -- expressible; the chaining of multiple genuine steps is exercised CONCRETELY
    -- in the litmus.  Soundness is the per-swap `≈Term` (up to the stuck-`out`
    -- cast `castW oeq`), unconditional whatever the fuel.
    --------------------------------------------------------------------------------

    -- a normalized diagram with its per-swap soundness witness.
    NormD : ∀ {ax bx ay by} {px sx py sy} {fx : Mor ax bx} {fy : Mor ay by}
            (fit : LeftFit px sx py sy fx fy) → DiagU (LeftFrame.N₃ fit) → Set
    NormD fit dRest = HeadSwapD fit dRest

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
  open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
  open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)

  data Gen : List ℕ → List ℕ → Set where
    fbox : Gen (0 ∷ []) (0 ∷ [])
    gbox : Gen (1 ∷ []) (1 ∷ [])

  open Normalize {ℕ} _≟ℕ_ Gen
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
    using (input-O; sorted-O; input⇒sorted; N₀; N₃; f-out-layer; g-in-layer)

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
  -- LITMUS (DiagU clean-bridge level): exercise the now-PROVEN `fx-clean⇒g-in`
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

  -- the recognised fit (= the hand-written `litFit`).
  litFitD : LeftFit (0 ∷ []) [] [] (1 ∷ []) gbox fbox
  litFitD = leftFit [] [] [] refl refl refl refl

  -- the firing swap on the recognised fit + empty tail.
  litSwapD : HeadSwapD litFitD litDSorted
  litSwapD = swapHeadD litFitD litDSorted

  -- `normalizeD` with positive fuel REORDERS: the result is the swapped clean
  -- DiagU (fbox, the lower-offset box, now fires FIRST) — machine-checked `refl`
  -- on the underlying layer list (fbox-pad first, then gbox-pad).
  litNormReorders : fromDiagU-ls (normalizeD 4 litFitD litDSorted)
                  ≡ mk-pad [] (1 ∷ []) fbox
                  ∷ mk-pad (0 ∷ []) [] gbox ∷ []
  litNormReorders = refl

  -- and the INPUT (fuel 0 / pre-sort) is gbox-first — confirming it was out of order.
  litNormInput : fromDiagU-ls (normalizeD 0 litFitD litDSorted)
               ≡ mk-pad (0 ∷ []) [] gbox
               ∷ mk-pad [] (1 ∷ []) fbox ∷ []
  litNormInput = refl

  -- the casts are the identity here, so the soundness witness is the clean
  -- `≈Term` between the two DiagUs (gbox-first ⇒ fbox-first), machine-checked.
  litNormCastId : proj₁ (normalizeD-sound 4 litFitD litDSorted) ≡ refl
  litNormCastId = refl

  litNormSound : id ∘ ⟦ dInput litFitD litDSorted ⟧
               ≈Term ⟦ normalizeD 4 litFitD litDSorted ⟧
  litNormSound = proj₂ (normalizeD-sound 4 litFitD litDSorted)
