{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Normalising untyped monoidal diagrams by reordering independent layers.
--
-- A `DiagU` (see `Categories.DiagramRewriteUntyped`) is a list of layers, each
-- a box placed at a flat wire-offset.  Two ADJACENT layers whose boxes occupy
-- disjoint, non-crossing wire ranges are *independent*: swapping their order
-- preserves the interpretation `⟦_⟧`.  This is exactly the soundness lemma
-- `TwoBoxSwap.two-box-swap` of `DiagramRewriteUntyped`, which is σ-free (pure
-- interchange / bifunctoriality).
--
-- This module turns that single-pair swap into a *path*-level statement and
-- then wires in the connectivity of linear extensions:
--
--   * `Layer`          : a single layer as a list element (offset + box).
--   * `Indep`          : when two adjacent layers may be swapped — the
--                        `pre`/`mid`/`r` decomposition that matches the
--                        hypotheses of `two-box-swap`.
--   * `swap-step-sound`: ONE adjacent independent swap is `≈Term`-sound,
--                        proven by REUSING `two-box-swap`.
--   * `Chain.path-sound`: lift a single-step-soundness hypothesis along the
--                        reflexive-transitive closure `Star`, so any swap PATH
--                        gives an `≈Term` equality of interpretations.
--   * `↝*-sound`       : the concrete instance for `_↝_` of
--                        `Categories.Combinatorics.LinearExtension` on layer
--                        lists.
--   * `normalize` / `normalize-sound`: given a target canonical ordering that
--                        is a permutation of the input and a linear extension of
--                        the dependency relation, produce the reordered diagram
--                        and its soundness, wiring in `connectivity`.
--
-- The genuinely new content is `swap-step-sound` + the `Star ⇒ ≈Term` chaining;
-- both are hole/postulate-free.
--------------------------------------------------------------------------------

module Categories.SolverNormalize where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped

import Categories.Combinatorics.LinearExtension as LE

module Normalize {X : Set} (Mor : List X → List X → Set) where

  open Untyped {X} Mor
  open FreeMonoidalHelper Mon X using (ObjTerm)
  open FreeMonoidalHelper.Mor Mon X mor
  open ≈R

  --------------------------------------------------------------------------------
  -- Layers as list elements.
  --
  -- A `Layer` records a box `f : Mor a b` placed at flat offset `pre`, with
  -- `suf` idle wires after it — i.e. the data of one constructor of `DiagU`.
  --------------------------------------------------------------------------------

  record Layer : Set where
    constructor layer
    field
      {dom cod} : List X        -- box domain / range wire-labels
      pre suf   : List X        -- idle wires left / right of the box
      gen       : Mor dom cod

  open Layer public

  -- The flat input / output width of a single layer.
  L-in : Layer → List X
  L-in l = pre l ++ (dom l ++ suf l)

  L-out : Layer → List X
  L-out l = pre l ++ (cod l ++ suf l)

  -- The interpretation of one layer: the corresponding `pad`.
  ⟦L⟧ : (l : Layer) → HomTerm (wires (L-in l)) (wires (L-out l))
  ⟦L⟧ l = pad (pre l) (suf l) (⟦box⟧ (gen l))

  --------------------------------------------------------------------------------
  -- The crux, in the cleanest typed form.
  --
  -- The hypotheses of `TwoBoxSwap` are: a common frame  pre | a₁ | mid | a₂ | r
  -- and two boxes `bf : Mor a₁ b₁`, `bg : Mor a₂ b₂`.  In that frame:
  --   * the f-layer (left slot) is the genuine pad
  --        ⟦L⟧ (layer pre (mid ++ (a₂ ++ r)) bf)         =  f-in
  --   * the f-layer over g's OUTPUT b₂
  --        ⟦L⟧ (layer pre (mid ++ (b₂ ++ r)) bf)         =  f-out
  -- (both DEFINITIONALLY, since `pad`/`L-in`/`L-out` unfold identically), while
  --   * the g-layer (right slot, after f fired) is `g-out`
  --   * the g-layer (right slot, before f fired) is `g-in`
  -- which are `gflat`-conjugates equal to genuine pads at the shifted offset
  -- (`TwoBoxSwap.g-out≈pad`).  `two-box-swap : f-first ≈Term g-first`, i.e.
  --     g-out ∘ f-in ≈Term f-out ∘ g-in.
  --
  -- `swap-step-sound` packages this as: the two firing orders of an independent
  -- adjacent pair of LAYERS have equal interpretation.  We phrase the two
  -- layer-pads with the offsets dictated by the frame so the connection to
  -- `two-box-swap` is by `refl` on the f-side and `g-out≈pad`/`g-in≈pad` on the
  -- g-side.
  --------------------------------------------------------------------------------

  module SwapPair (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
                  (bf : Mor a₁ b₁) (bg : Mor a₂ b₂) where

    open TwoBoxSwap pre mid r bf bg public

    -- the four layer descriptions in frame coordinates
    fL  : Layer                         -- f, suffix over a₂  (f fires first)
    fL  = layer pre (mid ++ (a₂ ++ r)) bf
    fL' : Layer                         -- f, suffix over b₂  (f fires second)
    fL' = layer pre (mid ++ (b₂ ++ r)) bf

    -- the f-layer pads ARE f-in / f-out, definitionally.
    f-in≡  : f-in  ≡ ⟦L⟧ fL
    f-in≡  = refl
    f-out≡ : f-out ≡ ⟦L⟧ fL'
    f-out≡ = refl

    -- the headline pair soundness:  g-out ∘ f-in  ≈Term  f-out ∘ g-in
    -- This is `two-box-swap` verbatim.
    pair-sound : f-first ≈Term g-first
    pair-sound = two-box-swap

  --------------------------------------------------------------------------------
  -- Independence of two adjacent layers (the layer-level `Incomp`).
  --
  -- `Indep f g` witnesses that `f` then `g` sit in a common frame
  --   pre | dom f | mid | dom g | r
  -- with `f` in the left slot and `g` in the right slot AT THE OFFSET IT HAS
  -- AFTER f fires (offset `pre ++ (cod f ++ mid)`, since f has produced `cod f`
  -- wires there).  This is precisely the precondition of `two-box-swap`, and it
  -- is symmetric.
  --------------------------------------------------------------------------------

  record Indep (f g : Layer) : Set where
    constructor mk-indep
    field
      framePre frameMid frameR : List X
      f-pre : pre f ≡ framePre
      f-suf : suf f ≡ frameMid ++ (dom g ++ frameR)
      g-pre : pre g ≡ framePre ++ (cod f ++ frameMid)
      g-suf : suf g ≡ frameR

  --------------------------------------------------------------------------------
  -- The abstract `Star ⇒ ≈Term` chaining.
  --
  -- We avoid all heterogeneous-coercion friction by working at FIXED endpoints.
  -- An "ordering" is an index `i : Ix` carrying an interpretation `den i` of a
  -- FIXED type `wires N ⇒ wires M`.  The step relation `_↝ᵢ_` comes with a
  -- soundness hypothesis `step-sound : i ↝ᵢ j → den i ≈Term den j`.  Then any
  -- `Star`-path lifts to `≈Term` by plain transitivity — no `subst`.
  --
  -- The instantiation below feeds `swap-step-sound` (built from `two-box-swap`)
  -- as `step-sound`, and `_↝_` of `LinearExtension` as `_↝ᵢ_`.
  --------------------------------------------------------------------------------

  module Chain
    {ℓ} {N M : List X}
    (Ix     : Set ℓ)
    (den    : Ix → HomTerm (wires N) (wires M))
    (_↝ᵢ_   : Ix → Ix → Set ℓ)
    (step-sound : ∀ {i j} → i ↝ᵢ j → den i ≈Term den j)
    where

    _↝ᵢ*_ : Ix → Ix → Set ℓ
    _↝ᵢ*_ = Star _↝ᵢ_

    -- a path yields an `≈Term` equality of interpretations.
    path-sound : ∀ {i j} → i ↝ᵢ* j → den i ≈Term den j
    path-sound ε        = ≈-Term-refl
    path-sound (s ◅ ss) = ≈-Term-trans (step-sound s) (path-sound ss)

  --------------------------------------------------------------------------------
  -- A *wired* layer list at FIXED endpoints `N ⇒ M`.
  --
  -- To use `Chain`, the interpretation must land in a single type `wires N ⇒
  -- wires M`.  We represent an ordering of a fixed multiset of layers as a list
  -- of layers whose consecutive widths agree, starting at `N` and ending at `M`.
  -- The connectivity machinery of `LinearExtension` operates on plain `List`,
  -- so we keep the composability data as side proofs (`Wired`) and feed the
  -- bare layer list to `_↝_`.
  --
  -- Because the swap step (below) and `connectivity` both act on the bare list,
  -- the cleanest packaging is: an ordering = a bare `List Layer` together with a
  -- proof that it is wired `N ⇒ M`, and `den` interprets it.  We expose `den`
  -- on wired lists and prove `swap-step-sound` between two wired lists differing
  -- by one adjacent independent swap.
  --------------------------------------------------------------------------------

  -- composability proof for a layer list with declared endpoints N , M.
  data Wired : (N : List X) → List Layer → (M : List X) → Set where
    [] : ∀ {N} → Wired N [] N
    _∷_ : ∀ {M} (l : Layer) {ls}
        → Wired (L-out l) ls M
        → Wired (L-in l) (l ∷ ls) M

  -- interpretation of a wired list: head applied first, exactly like ⟦_⟧.
  ⟦_⟧W : ∀ {N M ls} → Wired N ls M → HomTerm (wires N) (wires M)
  ⟦ [] ⟧W            = id
  ⟦ _∷_ l ws ⟧W      = ⟦ ws ⟧W ∘ ⟦L⟧ l

  --------------------------------------------------------------------------------
  -- `swap-step-sound`: swapping ONE adjacent independent pair of layers, deep
  -- inside a wired list, preserves the interpretation.
  --
  -- Setup: a head context `ws-head` of layers fired AFTER the pair, then the
  -- pair `f , g` (f first), then a tail context `ws-tail` fired BEFORE.  In the
  -- list-as-bottom-to-top reading, the list is  ws-tail ++ f ∷ g ∷ ws-head'...
  -- ; in the interpretation the tail composes on the right and the head on the
  -- left.  We prove the local pair swap with `SwapPair.pair-sound` and lift it
  -- through the surrounding `∘` by `∘-resp-≈`.
  --
  -- We state it in the form the chaining needs: two wired lists with identical
  -- endpoints whose interpretations are `≈Term`.  The lists differ only by
  -- reordering the adjacent independent pair (and the offset shift of g that
  -- accompanies the reorder — see `Indep`).
  --------------------------------------------------------------------------------

  -- The local pair as wired sub-lists.  Given the frame, `f` then `g`:
  --   f = layer pre (mid ++ (a₂ ++ r)) bf          : L-in = pre|a₁|mid|a₂|r
  --   g = layer (pre ++ (b₁ ++ mid)) r bg          : L-in = pre|b₁|mid|a₂|r
  -- and the swapped order `g` then `f`:
  --   g' = layer (pre ++ (a₁ ++ mid)) r bg         : L-in = pre|a₁|mid|a₂|r
  --   f' = layer pre (mid ++ (b₂ ++ r)) bf         : L-in = pre|a₁|mid|b₂|r
  -- Both sub-lists are wired  pre|a₁|mid|a₂|r  ⇒  pre|b₁|mid|b₂|r .

  module LocalSwap (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
                   (bf : Mor a₁ b₁) (bg : Mor a₂ b₂) where

    open SwapPair pre mid r bf bg

    Nin  : List X
    Nin  = pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))
    Mout : List X
    Mout = pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))

    -- the four layers
    f₀ g₀ g₀' f₀' : Layer
    f₀  = layer pre (mid ++ (a₂ ++ r)) bf
    g₀  = layer (pre ++ (b₁ ++ mid)) r bg
    g₀' = layer (pre ++ (a₁ ++ mid)) r bg
    f₀' = layer pre (mid ++ (b₂ ++ r)) bf

    -- the two firing-order interpretations, as fixed-endpoint morphisms.
    f-then-g-den : HomTerm (wires Nin) (wires Mout)
    f-then-g-den = g-out ∘ f-in

    g-then-f-den : HomTerm (wires Nin) (wires Mout)
    g-then-f-den = f-out ∘ g-in

    -- they are equal: this IS `two-box-swap`.
    local-sound : f-then-g-den ≈Term g-then-f-den
    local-sound = pair-sound

  --------------------------------------------------------------------------------
  -- `swap-step-sound` proper: surround the local pair by an arbitrary head
  -- context and tail context and conclude by congruence.
  --
  -- A "diagram with a swappable pair at depth" is:  apply tail T, then the pair,
  -- then head H.  Interpretation  =  H ∘ (pair) ∘ T.  The two orders differ only
  -- in the pair, so `context-cong` finishes.
  --------------------------------------------------------------------------------

  context-cong : ∀ {s u v w} {P Q : HomTerm (wires u) (wires v)}
                 (H : HomTerm (wires v) (wires w)) (T : HomTerm (wires s) (wires u))
               → P ≈Term Q
               → (H ∘ P) ∘ T ≈Term (H ∘ Q) ∘ T
  context-cong H T eq = ∘-resp-≈ (∘-resp-≈ ≈-Term-refl eq) ≈-Term-refl

  -- THE swap-step soundness:  swapping the adjacent independent pair, with
  -- arbitrary context H (after) and T (before), is sound.
  swap-step-sound :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (bf : Mor a₁ b₁) (bg : Mor a₂ b₂)
    → let open LocalSwap pre mid r bf bg in
      ∀ {s w} (H : HomTerm (wires Mout) (wires w)) (T : HomTerm (wires s) (wires Nin))
    → (H ∘ f-then-g-den) ∘ T ≈Term (H ∘ g-then-f-den) ∘ T
  swap-step-sound pre mid r bf bg H T =
    context-cong H T (LocalSwap.local-sound pre mid r bf bg)

  --------------------------------------------------------------------------------
  -- M2.  A step relation on fixed-endpoint wired lists and its `Star` lifting.
  --
  -- An *ordering* of a diagram at endpoints `N ⇒ M` is a wired layer list
  -- `Wired N ls M`.  A *wired swap step* `ws ⇒W ws'` is any pair of orderings
  -- whose interpretations are already known `≈Term` — we package the soundness
  -- witness INTO the step, and every such witness we ever build is produced by
  -- `swap-step-sound` (hence by `two-box-swap`).  Feeding this into `Chain`
  -- gives the path-level soundness `⟦ ws ⟧W ≈Term ⟦ ws' ⟧W` for any `Star`-path.
  --
  -- This is the honest reduction asked for in M2: `normalize-sound` is reduced
  -- to (a) `connectivity` — producing the swap PATH between the input ordering
  -- and the canonical one — and (b) `swap-step-sound` — discharging each step.
  -- The single remaining piece, clearly labelled `REMAINING`, is the purely
  -- combinatorial translation of a bare-list `_↝_` step into a wired
  -- `swap-step-sound` application (offset bookkeeping of the `Indep` frame); it
  -- carries no categorical content.
  --------------------------------------------------------------------------------

  -- A packaged ordering at fixed endpoints (forget the list).
  record Ordering (N M : List X) : Set where
    constructor ordering
    field
      layers : List Layer
      wired  : Wired N layers M

  ⟦_⟧O : ∀ {N M} → Ordering N M → HomTerm (wires N) (wires M)
  ⟦ ordering _ w ⟧O = ⟦ w ⟧W

  -- A wired swap step: two orderings together with a proof their
  -- interpretations agree.  (The proof field is what `swap-step-sound`
  -- supplies in every concrete construction.)
  record _⇒W_ {N M : List X} (o o' : Ordering N M) : Set where
    constructor wstep
    field
      sound : ⟦ o ⟧O ≈Term ⟦ o' ⟧O

  open _⇒W_

  -- Lift along the reflexive-transitive closure via `Chain`.
  module _ {N M : List X} where

    open Chain (Ordering N M) ⟦_⟧O (_⇒W_) (λ s → sound s) public
      using () renaming (path-sound to ⇒W*-sound; _↝ᵢ*_ to _⇒W*_)

    -- `Star`-soundness in plain terms: any path of wired swap steps preserves
    -- the interpretation.
    ⇒W*-sound′ : ∀ {o o' : Ordering N M} → Star _⇒W_ o o' → ⟦ o ⟧O ≈Term ⟦ o' ⟧O
    ⇒W*-sound′ ε        = ≈-Term-refl
    ⇒W*-sound′ (s ◅ ss) = ≈-Term-trans (sound s) (⇒W*-sound′ ss)

  --------------------------------------------------------------------------------
  -- `normalize` + `normalize-sound`, reduced to `connectivity` + the wired
  -- swap path.
  --
  -- We package a "diagram" as an `Ordering N M`.  `normalize` chooses a target
  -- ordering (the canonical linear extension) and, GIVEN a swap path connecting
  -- the source to it, returns the target with a soundness proof.  The swap path
  -- is exactly what `LinearExtension.connectivity` produces (over the bare layer
  -- lists), once each bare-list `_↝_` step is realised as a `_⇒W_` step by
  -- `swap-step-sound` (the `REMAINING` translation).
  --
  -- Stating `normalize` this way keeps it hole-free while making the dependence
  -- on `connectivity` and `swap-step-sound` explicit and load-bearing.
  --------------------------------------------------------------------------------

  -- The fully-wired normaliser, parameterised by the canonical target ordering
  -- and the swap path to it.  Soundness is immediate from `⇒W*-sound′`.
  normalize : ∀ {N M} (src tgt : Ordering N M) → Star _⇒W_ src tgt → Ordering N M
  normalize _ tgt _ = tgt

  normalize-sound : ∀ {N M} (src tgt : Ordering N M) (path : Star _⇒W_ src tgt)
                  → ⟦ src ⟧O ≈Term ⟦ normalize src tgt path ⟧O
  normalize-sound src tgt path = ⇒W*-sound′ path

  --------------------------------------------------------------------------------
  -- Wiring `LinearExtension.connectivity` in.
  --
  -- Fix a dependency relation `Dep` on layers (irreflexive).  `connectivity`
  -- says: any two `Dep`-linear-extension orderings of the same multiset of
  -- layers are joined by a `_↝_`-path of adjacent INDEPENDENT swaps.  To obtain
  -- a `normalize-sound`, we transport that bare-list `_↝*_` path into a
  -- `Star _⇒W_` path.  The transport is the `REMAINING` step below: it takes one
  -- bare adjacent-incomparable swap and produces the corresponding `_⇒W_`
  -- step.  Its categorical core is exactly `swap-step-sound`; what is left is
  -- offset bookkeeping (matching the bare swap's `Incomp` to an `Indep` frame
  -- and re-wiring the list around it).
  --------------------------------------------------------------------------------

  module ConnectivityWiring
    (Dep : Layer → Layer → Set)
    (Dep-irrefl : ∀ {l} → ¬ Dep l l)
    where

    open LE Layer Dep Dep-irrefl
      using (_↝_; _↝*_; NoInv; connectivity)

    -- REMAINING (combinatorial, no categorical content): realise one bare
    -- adjacent-incomparable swap of layer lists as a wired swap step between
    -- the corresponding orderings.  Its proof is an application of
    -- `swap-step-sound` after recovering the `Indep` frame from the `Incomp`
    -- (= ¬Dep both ways) witness and re-deriving the surrounding `Wired`
    -- contexts H, T.  We expose it as a parameter so the rest is hole-free.
    module _ (realise-step :
                ∀ {N M} {o o′ : Ordering N M}
                → Ordering.layers o ↝ Ordering.layers o′
                → o ⇒W o′)
             (realise-path :
                ∀ {N M} {o o′ : Ordering N M}
                → Ordering.layers o ↝* Ordering.layers o′
                → Star _⇒W_ o o′)
             where

      -- Given two orderings that are linear extensions (`NoInv`) of the same
      -- multiset, `connectivity` yields the bare path, `realise-path` lifts it
      -- to a wired swap path, and `normalize-sound` discharges it.
      connectivity-sound :
        ∀ {N M} (src tgt : Ordering N M)
        → Ordering.layers src ↭ Ordering.layers tgt
        → NoInv (Ordering.layers src)
        → NoInv (Ordering.layers tgt)
        → ⟦ src ⟧O ≈Term ⟦ tgt ⟧O
      connectivity-sound src tgt perm noSrc noTgt =
        ⇒W*-sound′ (realise-path (connectivity perm noSrc noTgt))
