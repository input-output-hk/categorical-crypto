{-# OPTIONS --safe --without-K #-}

module Categories.DiagramRewriteUntyped where

--------------------------------------------------------------------------------
-- Untyped normal form for free monoidal-category diagrams with morphism generators
--------------------------------------------------------------------------------
--
-- A diagram is a list of boxes; ⟦_⟧ reflects it into a HomTerm of the free
-- monoidal category over flat "n-wire" objects, and a head-swap exchanges two
-- adjacent boxes in disjoint, non-crossing wire ranges with a soundness proof.
--
-- KEY POINT: the swap only moves a box past a non-interacting neighbour, so
-- soundness is pure bifunctoriality / interchange (⊗-∘-dist, id⊗id≈id) plus
-- hand-discharged merge/split coherence — and never touches the braiding σ.

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (refl)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Category using (Category)
open import Categories.FreeMonoidal
open import Categories.WireCoh using (module WireCoh)

--------------------------------------------------------------------------------
-- WireSig: the wire-level signature
--------------------------------------------------------------------------------
-- Split out so callers can type a custom `⟦box⟧` before instantiating the
-- engine, breaking the chicken-and-egg between `mor` and the interpretation.
module WireSig (v : Variant) {X : Set} (Mor : List X → List X → Set) where

  open FreeMonoidalHelper v X using (ObjTerm)
  open FreeMonoidalHelper v X public using (wires)

  data mor : ObjTerm → ObjTerm → Set where
    box : ∀ {a b} → Mor a b → mor (wires a) (wires b)

  -- merge/split re-exported at this engine's `mor` so ⟦box⟧ interpretations
  -- can be built from them (e.g. the σ-conjugated block braiding of SolverSigma).
  open FreeMonoidalHelper.Mor v X mor public using (merge; split)

--------------------------------------------------------------------------------
-- The engine, parametric in the variant `v` (Mon or Symm) and in the
-- interpretation `⟦box⟧` of a diagram-layer generator into the wire-level
-- free category.  Every proof below uses only the Mon-fragment axioms, so
-- the whole development typechecks at abstract `v`.  (The telescope opens
-- are `renaming`-isolated: re-opening `WireSig` publicly in the body would
-- otherwise make `wires`/`mor` ambiguous at use sites.)
--------------------------------------------------------------------------------
module UntypedI (v : Variant) {X : Set} (Mor : List X → List X → Set)
                (let open WireSig v {X} Mor using () renaming (wires to wires↑; mor to mor↑))
                (let open FreeMonoidalHelper.Mor v X mor↑ using () renaming (HomTerm to HomTerm↑))
                (⟦box⟧ : ∀ {a b} → Mor a b → HomTerm↑ (wires↑ a) (wires↑ b)) where

  open WireSig v {X} Mor public
  open FreeMonoidalHelper v X using (ObjTerm; _⊗₀_; Var)
  -- merge/split/merge∘split/split∘merge are re-exported via `WireSig` (the
  -- first two) and the dedicated public open below, so hide them here to
  -- avoid an (identical-definition) ambiguity with that re-export.
  open FreeMonoidalHelper.Mor v X mor hiding (merge; split; merge∘split; split∘merge)

  -- equational reasoning for the (homogeneous) _≈Term_: since
  -- FreeMonoidal's _≈_ IS _≈Term_ definitionally, agda-categories' stock
  -- HomReasoning applies directly.  It also provides refl⟩∘⟨_, _⟩∘⟨refl,
  -- _⟩∘⟨_ (= ∘-resp-≈), ⟺ (= sym) and _○_ (= trans).  The display step
  -- _≈⟨⟩_ is a local shim (the stock module only has the _≡⟨⟩_ spelling).
  module ≈R where
    open Category.HomReasoning FreeMonoidal public
    infixr 2 _≈⟨⟩_
    _≈⟨⟩_ : ∀ {A B} (f : HomTerm A B) {g} → f IsRelatedTo g → f IsRelatedTo g
    _ ≈⟨⟩ x = x

  -- stock associativity/cancellation combinators on FreeMonoidal
  -- (pullˡ/pullʳ/center/cancel…), and ⊗-step
  -- combinators on Monoidal-FreeMonoidal (refl⟩⊗⟨_ etc.).  Plain `open`
  -- (not public): these are for the proofs in this file only.
  open MR FreeMonoidal
    using (pullˡ; pullʳ; center;
           cancelInner; insertInner; introʳ;
           assoc²εβ)
  open MonR Monoidal-FreeMonoidal
    using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; serialize₁₂; merge₂ˡ)

  open ≈R

  -- The id-tensored fusion combinators (`id⊗-∘`, `id⊗-∘3`, `id⊗-cancel`) and
  -- the flat-shift wire-frame algebra (`rpad`, `liftW`, `pad` and their
  -- functoriality lemmas `liftW-resp`/`liftW-∘`/`liftW-id`,
  -- `rpad-resp`/`rpad-id`/`rpad-∘`, `pad-resp`/`pad-id`/`pad-∘`) are generic in
  -- the generator family — only merge/split and the monoidal structure appear —
  -- so they live in `FreeMonoidalHelper.Mor` and are re-exported by the open
  -- above.  (`merge`/`split` themselves come via `WireSig`.)

  --------------------------------------------------------------------------------
  -- Diagrams: a list of layers.  Each layer is a box `f : Mor a b` placed
  -- at offset `pre`, with `suf` idle wires after it.  The diagram is
  -- indexed by its input wire-list; consing a layer in front turns a
  -- diagram of input width `pre ++ (b ++ suf)` into one of input width
  -- `pre ++ (a ++ suf)`.  The list is read left-to-right = bottom-to-top:
  -- the head layer is applied first.
  --------------------------------------------------------------------------------
  infixr 5 _▸_∷_⟨_⟩
  data DiagU : List X → Set where
    []_     : (n : List X) → DiagU n
    _▸_∷_⟨_⟩ : ∀ {a b} (pre : List X) (suf : List X) (f : Mor a b)
             → DiagU (pre ++ (b ++ suf)) → DiagU (pre ++ (a ++ suf))

  -- output width of a diagram
  out : ∀ {n} → DiagU n → List X
  out ([]_ n)        = n
  out (pre ▸ suf ∷ f ⟨ d ⟩) = out d

  -- interpretation into the free monoidal category: head applied first.
  ⟦_⟧ : ∀ {n} (d : DiagU n) → HomTerm (wires n) (wires (out d))
  ⟦ []_ n ⟧             = id {wires n}
  ⟦ pre ▸ suf ∷ f ⟨ d ⟩ ⟧ = ⟦ d ⟧ ∘ pad pre suf (⟦box⟧ f)

  --------------------------------------------------------------------------------
  -- The soundness kernel: pure disjoint interchange.  Two boxes living in
  -- disjoint blocks of a four-block tensor commute past each other.  This
  -- uses ONLY bifunctoriality (⊗-∘-dist), id⊗id≈id and unit laws — no σ.
  --------------------------------------------------------------------------------
  module _ {M R : ObjTerm} where
    -- a box `x : A ⇒ A'` in block 1 and a box `y : C ⇒ C'` in block 3,
    -- everything else idle.  (4-block layout A ⊗ M ⊗ C ⊗ R.)
    blk : ∀ {A A' C C'} → HomTerm A A' → HomTerm C C'
        → HomTerm (A ⊗₀ M ⊗₀ C ⊗₀ R) (A' ⊗₀ M ⊗₀ C' ⊗₀ R)
    blk x y = x ⊗₁ id ⊗₁ y ⊗₁ id

    -- idle-block functoriality: blk (g∘f) (g'∘f') ≈ blk g g' ∘ blk f f'
    blk-∘ : ∀ {A B A2 C D C2} (g : HomTerm B A2) (f : HomTerm A B)
              (g' : HomTerm D C2) (f' : HomTerm C D)
          → blk (g ∘ f) (g' ∘ f') ≈Term blk g g' ∘ blk f f'
    blk-∘ g f g' f' = begin
      (g ∘ f) ⊗₁ (id ⊗₁ ((g' ∘ f') ⊗₁ id))
        ≈⟨ refl⟩⊗⟨ ((⟺ idˡ) ⟩⊗⟨ (refl⟩⊗⟨ (⟺ idˡ))) ⟩
      (g ∘ f) ⊗₁ ((id ∘ id) ⊗₁ ((g' ∘ f') ⊗₁ (id ∘ id)))
        ≈⟨ refl⟩⊗⟨ (refl⟩⊗⟨ ⊗-∘-dist) ⟩
      (g ∘ f) ⊗₁ ((id ∘ id) ⊗₁ ((g' ⊗₁ id) ∘ (f' ⊗₁ id)))
        ≈⟨ refl⟩⊗⟨ ⊗-∘-dist ⟩
      (g ∘ f) ⊗₁ ((id ⊗₁ (g' ⊗₁ id)) ∘ (id ⊗₁ (f' ⊗₁ id)))
        ≈⟨ ⊗-∘-dist ⟩
      blk g g' ∘ blk f f' ∎

    -- the interchange itself: blk f id ∘ blk id g ≈ blk id g ∘ blk f id
    -- (boxes in disjoint blocks commute), via blk-∘ both ways through the
    -- common diagonal blk f g.
    blk-swap : ∀ {A A' C C'} (f : HomTerm A A') (g : HomTerm C C')
             → blk f id ∘ blk id g ≈Term blk id g ∘ blk f id
    blk-swap f g = begin
      blk f id ∘ blk id g
        ≈⟨ blk-∘ f id id g ⟨
      blk (f ∘ id) (id ∘ g)
        ≈⟨ idʳ ⟩⊗⟨ (refl⟩⊗⟨ (idˡ ⟩⊗⟨refl)) ⟩
      blk f g
        ≈⟨ (⟺ idˡ) ⟩⊗⟨ (refl⟩⊗⟨ ((⟺ idʳ) ⟩⊗⟨refl)) ⟩
      blk (id ∘ f) (g ∘ id)
        ≈⟨ blk-∘ id f g id ⟩
      blk id g ∘ blk f id ∎

  --------------------------------------------------------------------------------
  -- merge / split are mutually inverse (pure coherence).  Generic in the
  -- generator family, so re-exported from `FreeMonoidalHelper.Mor`.
  --------------------------------------------------------------------------------
  open FreeMonoidalHelper.Mor v X mor public using (merge∘split; split∘merge)

  --------------------------------------------------------------------------------
  -- Bridging the flat `pad` to the grouped `blk` form.
  --
  -- The flat layer  pad pre suf g : wires (pre ++ (a ++ suf)) ⇒ wires (pre ++ (b ++ suf))
  -- equals, up to the structural prefix-flatteners `pflat`/`punflat` below,
  -- the prefix-lifted right-pad  underP pre (rpad suf g)  (`padP-bridge`).
  -- We package the conjugation so that consecutive layers' flatteners cancel.
  --
  -- We use the two-block (binary) special case of interchange, which is
  -- exactly bifunctoriality, to slide a box past a disjoint neighbour at
  -- the flat level.
  --------------------------------------------------------------------------------

  -- prefix machinery (internal scaffolding for the flat-level bridge).
  private
   -- right-nested prefix of `pre` wires attached to an object Y
   pfx : List X → ObjTerm → ObjTerm
   pfx []      Y = Y
   pfx (x ∷ p) Y = Var x ⊗₀ pfx p Y

   ------------------------------------------------------------------------------
   -- Prefix lifting: an equation between two morphisms over an object Y is
   -- preserved by prefixing `p` idle wires (id ⊗₁ … ).
   ------------------------------------------------------------------------------
   -- map a morphism through the prefix of p idle wires
   underP : ∀ {A B} (p : List X) → HomTerm A B → HomTerm (pfx p A) (pfx p B)
   underP []      h = h
   underP (x ∷ p) h = id ⊗₁ underP p h

   underP-resp : ∀ {A B} (p : List X) {h k : HomTerm A B} → h ≈Term k → underP p h ≈Term underP p k
   underP-resp []      eq = eq
   underP-resp (x ∷ p) eq = refl⟩⊗⟨ underP-resp p eq

   underP-id : ∀ {A} (p : List X) → underP p (id {A}) ≈Term id
   underP-id []      = ≈-Term-refl
   underP-id (x ∷ p) = (refl⟩⊗⟨ underP-id p) ○ id⊗id≈id

   underP-∘ : ∀ {A B C} (p : List X) (g : HomTerm B C) (f : HomTerm A B)
            → underP p (g ∘ f) ≈Term underP p g ∘ underP p f
   underP-∘ []      g f = ≈-Term-refl
   underP-∘ (x ∷ p) g f = (refl⟩⊗⟨ underP-∘ p g f) ○ (⟺ (id⊗-∘ _ _))

  --------------------------------------------------------------------------------
  -- Grouped diagrams and the sound head-swap.
  --
  -- A *grouped* layer records, with wire-label-list offsets, where a box sits:
  --   pre   : idle wires to the left of the working region
  --   mid   : idle wires between the two interacting slots
  --   r     : idle wires to the right
  -- plus the box itself.  We describe two adjacent layers `f` (left slot)
  -- and `g` (right slot) over a *common* 4-block frame
  --     pfx pre (wires Af  ⊗₀  wires mid  ⊗₀  wires Cg  ⊗₀  wires r)
  -- and exhibit the head-swap together with its soundness.
  --
  -- The two head layers are:
  --   layer-f  = underP pre (blk ⟦f⟧ id)     -- box f in the left slot
  --   layer-g  = underP pre (blk id ⟦g⟧)     -- box g in the right slot
  -- "f then g"  = layer-g ∘ layer-f ;  the head-swap returns "g then f".
  --------------------------------------------------------------------------------

  module HeadSwap (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
                  (f : Mor a₁ b₁) (g : Mor a₂ b₂) where

    -- left / right slots use ⟦box⟧ for the boxes and id elsewhere.
    private
      layer-f : (c : List X)
              → HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires c ⊗₀ wires r))
                        (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires c ⊗₀ wires r))
      layer-f c = underP pre (blk {M = wires mid} {R = wires r} (⟦box⟧ f) (id {wires c}))

      layer-g : (x : List X)
              → HomTerm (pfx pre (wires x ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                        (pfx pre (wires x ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
      layer-g x = underP pre (blk {M = wires mid} {R = wires r} (id {wires x}) (⟦box⟧ g))

      layer-f-in  = layer-f a₂
      layer-f-out = layer-f b₂
      layer-g-in  = layer-g a₁
      layer-g-out = layer-g b₁

    -- "f then g":  apply f (left slot), then g (right slot)
    f-then-g : HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                       (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
    f-then-g = layer-g-out ∘ layer-f-in

    -- "g then f": the swapped diagram (g first, then f)
    g-then-f : HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                       (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
    g-then-f = layer-f-out ∘ layer-g-in

    -- SOUNDNESS of the head-swap: the two orders are equal in the free
    -- monoidal category.  Pure bifunctoriality — NO braiding σ.
    swap-sound : f-then-g ≈Term g-then-f
    swap-sound = begin
      underP pre (blk (id {wires b₁}) (⟦box⟧ g)) ∘ underP pre (blk (⟦box⟧ f) (id {wires a₂}))
        ≈⟨ underP-∘ pre _ _ ⟨
      underP pre (blk (id {wires b₁}) (⟦box⟧ g) ∘ blk (⟦box⟧ f) (id {wires a₂}))
        ≈⟨ underP-resp pre (⟺ (blk-swap (⟦box⟧ f) (⟦box⟧ g))) ⟩
      underP pre (blk (⟦box⟧ f) (id {wires b₂}) ∘ blk (id {wires a₁}) (⟦box⟧ g))
        ≈⟨ underP-∘ pre _ _ ⟩
      underP pre (blk (⟦box⟧ f) (id {wires b₂})) ∘ underP pre (blk (id {wires a₁}) (⟦box⟧ g)) ∎

  --------------------------------------------------------------------------------
  -- The bridge: from the grouped `HeadSwap.swap-sound` to the FLAT `pad`
  -- interpretation used by ⟦_⟧.
  --
  -- We build a global flattener `gflat` taking the grouped 4-block frame
  --   pfx pre (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d)
  -- to the flat object  wires (pre ++ (x ++ (m ++ (c ++ d)))) , together with
  -- its inverse `gunflat`.  Each flat layer (`pad`) then equals the
  -- corresponding grouped block (`underP pre (blk … …)`) conjugated by the
  -- global flatteners; conjugation by an iso preserves ≈Term, and the
  -- inter-layer flatteners + the ++-associativity reassoc telescope to the
  -- identity, so `swap-sound` transports to the flat orders.
  --------------------------------------------------------------------------------

  -- inner / prefix / global flatteners (internal scaffolding for the bridge).
  private
   -- Inner flattener for the 3-block suffix  wires m ⊗₀ wires c ⊗₀ wires d
   --   → wires (m ++ (c ++ d)).
   sflat : (m c : List X) {d : List X}
         → HomTerm (wires m ⊗₀ wires c ⊗₀ wires d) (wires (m ++ (c ++ d)))
   sflat m c {d} = merge m ∘ (id ⊗₁ merge c {d})

   sunflat : (m c : List X) {d : List X}
           → HomTerm (wires (m ++ (c ++ d))) (wires m ⊗₀ wires c ⊗₀ wires d)
   sunflat m c {d} = (id ⊗₁ split c {d}) ∘ split m

   sflat∘sunflat : ∀ (m c : List X) {d} → sflat m c {d} ∘ sunflat m c ≈Term id
   sflat∘sunflat m c {d} = cancelInner (id⊗-cancel (merge∘split c)) ○ merge∘split m

   sunflat∘sflat : ∀ (m c : List X) {d} → sunflat m c {d} ∘ sflat m c ≈Term id
   sunflat∘sflat m c {d} = cancelInner (split∘merge m) ○ id⊗-cancel (split∘merge c)

   -- Inner 4-block flattener:  wires x ⊗₀ (suffix 3-block)  →  wires (x ++ (m ++ (c ++ d))).
   iflat : (x m c : List X) {d : List X}
         → HomTerm (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d)
                   (wires (x ++ (m ++ (c ++ d))))
   iflat x m c {d} = merge x ∘ (id ⊗₁ sflat m c {d})

   iunflat : (x m c : List X) {d : List X}
           → HomTerm (wires (x ++ (m ++ (c ++ d))))
                     (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d)
   iunflat x m c {d} = (id ⊗₁ sunflat m c {d}) ∘ split x

   -- prefix flattener: reshape a right-nested prefix of `pre` wires sitting
   -- on top of an already-flat tail `wires n` into the flat `wires (pre ++ n)`.
   -- (Definitionally an identity on objects via `(x ∷ p) ++ n = x ∷ (p ++ n)`,
   -- but it must be threaded through ⊗₁ to retype.)
   pflat : (pre : List X) {n : List X} → HomTerm (pfx pre (wires n)) (wires (pre ++ n))
   pflat []      = id
   pflat (x ∷ p) = id ⊗₁ pflat p

   punflat : (pre : List X) {n : List X} → HomTerm (wires (pre ++ n)) (pfx pre (wires n))
   punflat []      = id
   punflat (x ∷ p) = id ⊗₁ punflat p

   punflat∘pflat : ∀ (pre : List X) {n} → punflat pre {n} ∘ pflat pre ≈Term id
   punflat∘pflat []      = idˡ
   punflat∘pflat (x ∷ p) = id⊗-cancel (punflat∘pflat p)

   iunflat∘iflat : ∀ (x m c : List X) {d} → iunflat x m c {d} ∘ iflat x m c ≈Term id
   iunflat∘iflat x m c {d} = cancelInner (split∘merge x) ○ id⊗-cancel (sunflat∘sflat m c)

   -- Global flattener: grouped 4-block frame  →  flat wires object.
   gflat : (pre x m c : List X) {d : List X}
         → HomTerm (pfx pre (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d))
                   (wires (pre ++ (x ++ (m ++ (c ++ d)))))
   gflat pre x m c {d} = pflat pre ∘ underP pre (iflat x m c {d})

   gunflat : (pre x m c : List X) {d : List X}
           → HomTerm (wires (pre ++ (x ++ (m ++ (c ++ d)))))
                     (pfx pre (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d))
   gunflat pre x m c {d} = underP pre (iunflat x m c {d}) ∘ punflat pre

   gunflat∘gflat : ∀ (pre x m c : List X) {d}
                 → gunflat pre x m c {d} ∘ gflat pre x m c ≈Term id
   gunflat∘gflat pre x m c {d} =
     cancelInner (punflat∘pflat pre)
       ○ (⟺ (underP-∘ pre _ _))
       ○ underP-resp pre (iunflat∘iflat x m c)
       ○ underP-id pre

   --------------------------------------------------------------------------------
   -- Core bridge (pre = 0): the flat `rpad` of a left-block box equals the
   -- grouped block conjugated by the inner flatteners.
   --
   -- A box `h : wires a ⇒ wires b` placed in block 1 of the 4-block frame
   -- (everything else idle) flattens to  rpad (m ++ (c ++ d)) h.
   --------------------------------------------------------------------------------

   -- the f-side block at pre = 0:  h ⊗₁ id ⊗₁ id ⊗₁ id
   -- iflat b ∘ (h ⊗₁ idsuffix) ∘ iunflat a  ≈  rpad (m ++ (c ++ d)) h
   rpad-iconj : ∀ {a b} (m c : List X) {d : List X} (h : HomTerm (wires a) (wires b))
              → iflat b m c {d} ∘ (h ⊗₁ id {wires m ⊗₀ wires c ⊗₀ wires d}) ∘ iunflat a m c
                ≈Term rpad (m ++ (c ++ d)) h
   rpad-iconj {a} {b} m c {d} h = pullʳ ((refl⟩∘⟨ pullˡ step₁) ○ pullˡ step₂)
     where
       -- slide the box past the (un)flattener: pure bifunctoriality
       step₁ : (h ⊗₁ id) ∘ (id ⊗₁ sunflat m c {d}) ≈Term h ⊗₁ sunflat m c {d}
       step₁ = ⟺ serialize₁₂
       step₂ : (id ⊗₁ sflat m c {d}) ∘ (h ⊗₁ sunflat m c {d}) ≈Term h ⊗₁ id
       step₂ = merge₂ˡ ○ (refl⟩⊗⟨ sflat∘sunflat m c)

   -- blk with the idle box on the right is the box left-tensored with a
   -- single idle block over the whole suffix.
   blk-left-id : ∀ {m c d : List X} {a b} (h : HomTerm (wires a) (wires b))
               → blk {M = wires m} {R = wires d} h (id {wires c})
                 ≈Term h ⊗₁ id {wires m ⊗₀ wires c ⊗₀ wires d}
   blk-left-id {m} {c} {d} h = refl⟩⊗⟨ ((refl⟩⊗⟨ id⊗id≈id) ○ id⊗id≈id)

  --------------------------------------------------------------------------------
  -- Lemmas about liftW (the function itself is re-exported from FreeMonoidalHelper.Mor).
  --------------------------------------------------------------------------------

  -- the flat shift equals the merge/split conjugation.
  liftW-merge : ∀ (p : List X) {u v} (W : HomTerm (wires u) (wires v))
              → liftW p W ≈Term merge p {v} ∘ (id {wires p} ⊗₁ W) ∘ split p {u}
  liftW-merge []      W =
    introʳ λ⇒∘λ⇐≈id ○ pullˡ (⟺ λ⇒∘id⊗f≈f∘λ⇒) ○ assoc
  liftW-merge (x ∷ p) {u} {v} W =
    (refl⟩⊗⟨ liftW-merge p W)
      ○ (⟺ (id⊗-∘3 (merge p) (id ⊗₁ W) (split p)))
      ○ reassoc-suc
    where
      -- insert α⇒∘α⇐ = id in the middle and reassociate to expose
      -- merge (suc p) = id⊗₁merge p ∘ α⇒ and split (suc p) = α⇐ ∘ id⊗₁split p.
      reassoc-suc :
          id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ W) ∘ id ⊗₁ split p)
        ≈Term (id ⊗₁ merge p ∘ α⇒) ∘ id ⊗₁ W ∘ (α⇐ ∘ id ⊗₁ split p)
      reassoc-suc = begin
        id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ W) ∘ id ⊗₁ split p)
          ≈⟨ refl⟩∘⟨ insertInner α⇒∘α⇐≈id ⟩
        id ⊗₁ merge p ∘ ((id ⊗₁ (id ⊗₁ W) ∘ α⇒) ∘ (α⇐ ∘ id ⊗₁ split p))
          ≈⟨ refl⟩∘⟨ ((⟺ α-comm) ○ (refl⟩∘⟨ (id⊗id≈id ⟩⊗⟨refl))) ⟩∘⟨refl ⟩
        id ⊗₁ merge p ∘ ((α⇒ ∘ id ⊗₁ W) ∘ (α⇐ ∘ id ⊗₁ split p))
          ≈⟨ center ≈-Term-refl ⟨
        (id ⊗₁ merge p ∘ α⇒) ∘ id ⊗₁ W ∘ (α⇐ ∘ id ⊗₁ split p) ∎

  -- `pad` is literally the wire-shift of `rpad` — definitional.
  pad≡liftW : ∀ {a b} (pre suf : List X) (g : HomTerm (wires a) (wires b))
            → pad pre suf g ≈Term liftW pre (rpad suf g)
  pad≡liftW pre suf g = ≈-Term-refl

  -- The `castW` object-transport algebra and the structural ++-associators
  -- `assocW`/`assocW⁻` (⟦box⟧-free wire coherence) live in WireCoh.
  open WireCoh v X mor public

  -- pflat-conjugation of a prefix-lifted wire morphism is its flat shift.
  private
   pflatconj : ∀ (pre : List X) {u v} (Y : HomTerm (wires u) (wires v))
             → pflat pre {v} ∘ underP pre Y ∘ punflat pre {u} ≈Term liftW pre Y
   pflatconj []      Y = idˡ ○ idʳ
   pflatconj (x ∷ p) {u} {v} Y =
    id⊗-∘3 (pflat p) (underP p Y) (punflat p) ○ (refl⟩⊗⟨ pflatconj p Y)

  -- pad as a conjugation by the prefix-flattener of a prefix-lifted rpad.
  private
   padP-bridge : ∀ {a b} (pre suf : List X) (h : HomTerm (wires a) (wires b))
               → pad pre suf h
                 ≈Term pflat pre ∘ underP pre (rpad suf h) ∘ punflat pre
   padP-bridge []      suf h = ⟺ (idˡ ○ idʳ)
   padP-bridge (x ∷ p) suf h =
    (refl⟩⊗⟨ padP-bridge p suf h)
      ○ (⟺ (id⊗-∘3 (pflat p) (underP p (rpad suf h)) (punflat p)))

  --------------------------------------------------------------------------------
  -- Generic conjugation collapse: gflat ∘ underP pre X ∘ gunflat folds the
  -- three prefix-lifts into one and exposes the inner-flattener conjugation.
  --------------------------------------------------------------------------------
  private
   gconj : ∀ (pre x m c x' c' : List X) {d}
             (X : HomTerm (wires x' ⊗₀ wires m ⊗₀ wires c' ⊗₀ wires d)
                          (wires x  ⊗₀ wires m ⊗₀ wires c  ⊗₀ wires d))
         → gflat pre x m c {d} ∘ underP pre X ∘ gunflat pre x' m c' {d}
           ≈Term pflat pre
               ∘ underP pre (iflat x m c {d} ∘ X ∘ iunflat x' m c' {d})
               ∘ punflat pre
   gconj pre x m c x' c' {d} X = begin
     (pflat pre ∘ underP pre (iflat x m c))
       ∘ underP pre X
       ∘ (underP pre (iunflat x' m c') ∘ punflat pre)
       ≈⟨ center (⟺ (underP-∘ pre _ _)) ⟩
     pflat pre ∘ (underP pre (iflat x m c ∘ X)
       ∘ (underP pre (iunflat x' m c') ∘ punflat pre))
       ≈⟨ refl⟩∘⟨ pullˡ (⟺ (underP-∘ pre _ _)) ⟩
     pflat pre ∘ (underP pre ((iflat x m c ∘ X) ∘ iunflat x' m c') ∘ punflat pre)
       ≈⟨ refl⟩∘⟨ underP-resp pre assoc ⟩∘⟨refl ⟩
     pflat pre ∘ (underP pre (iflat x m c ∘ (X ∘ iunflat x' m c')) ∘ punflat pre) ∎

   -- Bridge-f: the flat pad of f equals the grouped f-block conjugated by gflat.
   bridge-f : ∀ (pre m c r : List X) {a b : List X} (h : HomTerm (wires a) (wires b))
            → pad pre (m ++ (c ++ r)) h
              ≈Term gflat pre b m c {r}
                  ∘ underP pre (blk {M = wires m} {R = wires r} h (id {wires c}))
                  ∘ gunflat pre a m c {r}
   bridge-f pre m c r {a} {b} h = begin
     pad pre (m ++ (c ++ r)) h
       ≈⟨ padP-bridge pre (m ++ (c ++ r)) h ⟩
     pflat pre ∘ underP pre (rpad (m ++ (c ++ r)) h) ∘ punflat pre
       ≈⟨ refl⟩∘⟨ underP-resp pre (⟺ core) ⟩∘⟨refl ⟩
     pflat pre ∘ underP pre (iflat b m c ∘ (blk h (id {wires c})) ∘ iunflat a m c) ∘ punflat pre
       ≈⟨ gconj pre b m c a c h-block ⟨
     gflat pre b m c ∘ underP pre (blk h (id {wires c})) ∘ gunflat pre a m c ∎
     where
       h-block : HomTerm (wires a ⊗₀ wires m ⊗₀ wires c ⊗₀ wires r)
                         (wires b ⊗₀ wires m ⊗₀ wires c ⊗₀ wires r)
       h-block = blk {M = wires m} {R = wires r} h (id {wires c})
       core : iflat b m c {r} ∘ (blk h (id {wires c})) ∘ iunflat a m c
              ≈Term rpad (m ++ (c ++ r)) h
       core = (refl⟩∘⟨ blk-left-id h ⟩∘⟨refl) ○ rpad-iconj m c h

   -- The g-core: the right-block box, conjugated by the inner flatteners,
   -- is the double flat-shift of g's right-pad.  (g in block 3 / slot c.)
   gcore : ∀ (x m : List X) {a b d : List X} (g : HomTerm (wires a) (wires b))
         → iflat x m b {d} ∘ (blk {M = wires m} {R = wires d} (id {wires x}) g) ∘ iunflat x m a {d}
           ≈Term liftW x (liftW m (rpad d g))
   gcore x m {a} {b} {d} g = begin
     iflat x m b ∘ (blk (id {wires x}) g) ∘ iunflat x m a
       ≈⟨⟩  -- blk id g = id ⊗₁ (id ⊗₁ (g ⊗₁ id)) = id ⊗₁ Bg, definitionally
     (merge x ∘ (id ⊗₁ sflat m b)) ∘ (id ⊗₁ Bg) ∘ ((id ⊗₁ sunflat m a) ∘ split x)
       ≈⟨ center (id⊗-∘ (sflat m b) Bg) ⟩
     merge x ∘ (id ⊗₁ (sflat m b ∘ Bg) ∘ ((id ⊗₁ sunflat m a) ∘ split x))
       ≈⟨ refl⟩∘⟨ pullˡ (id⊗-∘ (sflat m b ∘ Bg) (sunflat m a)) ⟩
     merge x ∘ (id ⊗₁ ((sflat m b ∘ Bg) ∘ sunflat m a) ∘ split x)
       ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ (assoc ○ innerY)) ⟩∘⟨refl ⟩
     merge x ∘ (id ⊗₁ liftW m (rpad d g) ∘ split x)
       ≈⟨ ⟺ (liftW-merge _ _) ⟩
     liftW x (liftW m (rpad d g)) ∎
     where
       Bg : HomTerm (wires m ⊗₀ wires a ⊗₀ wires d) (wires m ⊗₀ wires b ⊗₀ wires d)
       Bg = id {wires m} ⊗₁ (g ⊗₁ id {wires d})
       -- inner collapse: sflat m b ∘ Bg ∘ sunflat m a ≈ liftW m (rpad d g)
       innerY : sflat m b ∘ Bg ∘ sunflat m a ≈Term liftW m (rpad d g)
       innerY = begin
         (merge m ∘ (id ⊗₁ merge b)) ∘ Bg ∘ ((id ⊗₁ split a) ∘ split m)
           ≈⟨ center (id⊗-∘ (merge b) (g ⊗₁ id)) ⟩
         merge m ∘ (id ⊗₁ (merge b ∘ g ⊗₁ id) ∘ ((id ⊗₁ split a) ∘ split m))
           ≈⟨ refl⟩∘⟨ pullˡ (id⊗-∘ (merge b ∘ g ⊗₁ id) (split a)) ⟩
         merge m ∘ (id ⊗₁ ((merge b ∘ g ⊗₁ id) ∘ split a) ∘ split m)
           ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ assoc) ⟩∘⟨refl ⟩
         merge m ∘ (id ⊗₁ (merge b ∘ (g ⊗₁ id) ∘ split a) ∘ split m)
           ≈⟨ ⟺ (liftW-merge _ _) ⟩
         liftW m (rpad d g) ∎

   -- Bridge-g (to the liftW form): the grouped right-block g-layer, conjugated
   -- by gflat, equals the double flat-shift of g's right-pad.
   bridge-g : ∀ (pre x m r : List X) {a b : List X} (g : HomTerm (wires a) (wires b))
            → gflat pre x m b {r}
                ∘ underP pre (blk {M = wires m} {R = wires r} (id {wires x}) g)
                ∘ gunflat pre x m a {r}
              ≈Term liftW pre (liftW x (liftW m (rpad r g)))
   bridge-g pre x m r {a} {b} g = begin
     gflat pre x m b ∘ underP pre (blk (id {wires x}) g) ∘ gunflat pre x m a
       ≈⟨ gconj pre x m b x a (blk (id {wires x}) g) ⟩
     pflat pre ∘ underP pre (iflat x m b ∘ (blk (id {wires x}) g) ∘ iunflat x m a) ∘ punflat pre
       ≈⟨ refl⟩∘⟨ underP-resp pre (gcore x m g) ⟩∘⟨refl ⟩
     pflat pre ∘ underP pre (liftW x (liftW m (rpad r g))) ∘ punflat pre
       ≈⟨ pflatconj pre (liftW x (liftW m (rpad r g))) ⟩
     liftW pre (liftW x (liftW m (rpad r g))) ∎

  -- rpad commutes with the prefix id⊗₁: rpad rt (id⊗₁ h) ≈ id⊗₁ (rpad rt h).
  rpad-id⊗ : ∀ (rt : List X) (x : X) {u v} (h : HomTerm (wires u) (wires v))
           → rpad rt (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ rpad rt h
  rpad-id⊗ rt x {u} {v} h =
    reB
    ○ refl⟩∘⟨ (midα ⟩∘⟨refl)
    ○ refl⟩∘⟨ (id⊗-∘ (h ⊗₁ id) (split u))
    ○ id⊗-∘ (merge v) ((h ⊗₁ id) ∘ split u)
    where
      midα : α⇒ ∘ ((id {Var x} ⊗₁ h) ⊗₁ id) ∘ α⇐
           ≈Term id {Var x} ⊗₁ (h ⊗₁ id)
      midα = α-conj (id {Var x}) h id
      reB : (id {Var x} ⊗₁ merge v {rt} ∘ α⇒)
              ∘ ((id {Var x} ⊗₁ h) ⊗₁ id {wires rt})
              ∘ (α⇐ ∘ id {Var x} ⊗₁ split u {rt})
          ≈Term id {Var x} ⊗₁ merge v {rt}
              ∘ ((α⇒ ∘ ((id {Var x} ⊗₁ h) ⊗₁ id {wires rt}) ∘ α⇐)
                 ∘ id {Var x} ⊗₁ split u {rt})
      reB = assoc ○ (refl⟩∘⟨ assoc²εβ)

  -- The double flat-shift equals the flat shift at the summed offset,
  -- conjugated by structural ++-associativity isos `assocW` (defined by plain id ⊗₁ recursion).
  private
   liftW-reassoc : ∀ (pre x m : List X) {u v} (W : HomTerm (wires u) (wires v))
                → liftW pre (liftW x (liftW m W))
                  ≈Term (liftW pre (assocW⁻ x m v) ∘ assocW⁻ pre (x ++ m) v)
                      ∘ liftW (pre ++ (x ++ m)) W
                      ∘ (assocW pre (x ++ m) u ∘ liftW pre (assocW x m u))
   liftW-reassoc pre x m {u} {v} W = begin
     liftW pre (liftW x (liftW m W))
       ≈⟨ liftW-resp pre (liftW-assoc' x m W) ⟩
     liftW pre (assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u)
       ≈⟨ liftW-∘ pre _ _ ⟩
     liftW pre (assocW⁻ x m v) ∘ liftW pre (liftW (x ++ m) W ∘ assocW x m u)
       ≈⟨ refl⟩∘⟨ liftW-∘ pre _ _ ⟩
     liftW pre (assocW⁻ x m v) ∘ liftW pre (liftW (x ++ m) W) ∘ liftW pre (assocW x m u)
       ≈⟨ refl⟩∘⟨ liftW-assoc' pre (x ++ m) W ⟩∘⟨refl ⟩
     liftW pre (assocW⁻ x m v)
       ∘ (assocW⁻ pre (x ++ m) v ∘ liftW (pre ++ (x ++ m)) W ∘ assocW pre (x ++ m) u)
       ∘ liftW pre (assocW x m u)
       ≈⟨ (refl⟩∘⟨ (((⟺ assoc) ⟩∘⟨refl) ○ assoc)) ○ (⟺ (center ≈-Term-refl)) ⟩
     (liftW pre (assocW⁻ x m v) ∘ assocW⁻ pre (x ++ m) v)
       ∘ liftW (pre ++ (x ++ m)) W
       ∘ (assocW pre (x ++ m) u ∘ liftW pre (assocW x m u)) ∎

  --------------------------------------------------------------------------------
  -- THE BRIDGE THEOREM.  Two adjacent, disjoint, non-crossing boxes commute
  -- under the FLAT `pad` interpretation used by ⟦_⟧.
  --
  -- We work in a frame  pre | a₁/b₁ | mid | a₂/b₂ | r  of flat wires.  The two
  -- orders are:
  --   f-first:  apply f at offset `pre`  (suffix mid+(a₂+r)), then g at offset
  --             `pre ++ (b₁ ++ mid)`  (suffix r) — the g-layer being a genuine
  --             flat pad bridged across the ++-associativity gap by the
  --             structural iso `reassoc` (built by plain id ⊗₁ recursion via assocW).
  --   g-first:  apply g at offset `pre ++ (a₁ ++ mid)`, then f at offset `pre`.
  -- Both orders have the SAME flat domain and codomain and are EQUAL.
  --
  -- The proof reuses `HeadSwap.swap-sound` verbatim, conjugated by the global
  -- flatteners `gflat`/`gunflat` (which cancel between the two layers).  No σ.
  --------------------------------------------------------------------------------
  module TwoBoxSwap (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
                    (f : Mor a₁ b₁) (g : Mor a₂ b₂) where

    open HeadSwap pre mid r f g

    -- ---- flat f-layers (genuine `pad`s) ----
    f-in : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))))
                   (wires (pre ++ (b₁ ++ (mid ++ (a₂ ++ r)))))
    f-in = pad pre (mid ++ (a₂ ++ r)) (⟦box⟧ f)

    f-out : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (b₂ ++ r)))))
                    (wires (pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))))
    f-out = pad pre (mid ++ (b₂ ++ r)) (⟦box⟧ f)

    -- ---- flat g-layers, as `gflat`-conjugates of the grouped block ----
    -- (Each equals a genuine flat `pad` of g at the shifted offset, conjugated
    --  by the structural reassoc iso — see `g-out≈pad` / `g-in≈pad` below.)
    -- the structural reassoc isos at a given box offset (exposed so the
    -- normalizer can collapse them to single `castW`s at both offsets a₁/b₁
    -- with one offset-parametrised lemma each — see SolverNormalize §11d').
    reassocF : (x : List X)
             → HomTerm (wires (pre ++ (x ++ (mid ++ (a₂ ++ r)))))
                       (wires ((pre ++ (x ++ mid)) ++ (a₂ ++ r)))
    reassocF x = assocW pre (x ++ mid) (a₂ ++ r) ∘ liftW pre (assocW x mid (a₂ ++ r))

    reassocB : (x : List X)
             → HomTerm (wires ((pre ++ (x ++ mid)) ++ (b₂ ++ r)))
                       (wires (pre ++ (x ++ (mid ++ (b₂ ++ r)))))
    reassocB x = liftW pre (assocW⁻ x mid (b₂ ++ r)) ∘ assocW⁻ pre (x ++ mid) (b₂ ++ r)

    private
      gLayer : (x : List X)
             → HomTerm (wires (pre ++ (x ++ (mid ++ (a₂ ++ r)))))
                       (wires (pre ++ (x ++ (mid ++ (b₂ ++ r)))))
      gLayer x = gflat pre x mid b₂ {r}
                   ∘ underP pre (blk {M = wires mid} {R = wires r} (id {wires x}) (⟦box⟧ g))
                   ∘ gunflat pre x mid a₂ {r}

      gLayer≈pad : (x : List X)
                 → gLayer x
                   ≈Term reassocB x ∘ pad (pre ++ (x ++ mid)) r (⟦box⟧ g) ∘ reassocF x
      gLayer≈pad x = begin
        gLayer x
          ≈⟨ bridge-g pre x mid r (⟦box⟧ g) ⟩
        liftW pre (liftW x (liftW mid (rpad r (⟦box⟧ g))))
          ≈⟨ liftW-reassoc pre x mid (rpad r (⟦box⟧ g)) ⟩
        reassocB x ∘ liftW (pre ++ (x ++ mid)) (rpad r (⟦box⟧ g)) ∘ reassocF x
          ≈⟨ refl⟩∘⟨ (⟺ (pad≡liftW (pre ++ (x ++ mid)) r (⟦box⟧ g))) ⟩∘⟨refl ⟩
        reassocB x ∘ pad (pre ++ (x ++ mid)) r (⟦box⟧ g) ∘ reassocF x ∎

    g-out        = gLayer b₁
    g-in         = gLayer a₁
    reassocF-out = reassocF b₁
    reassocB-out = reassocB b₁
    reassocF-in  = reassocF a₁
    reassocB-in  = reassocB a₁
    g-out≈pad    = gLayer≈pad b₁
    g-in≈pad     = gLayer≈pad a₁

    -- f-first composite and g-first composite share dom & cod.
    f-first : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))))
                      (wires (pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))))
    f-first = g-out ∘ f-in

    g-first : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))))
                      (wires (pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))))
    g-first = f-out ∘ g-in

    private
      -- shared collapse for f-first≈ / g-first≈: two conjugated layers whose
      -- inner flattener pair cancels (U₁ ∘ G₂ ≈ id).
      conj-cancel : ∀ {A B C D F G : ObjTerm}
                      {G₁ : HomTerm F G} {L₁ : HomTerm C F} {U₁ : HomTerm D C}
                      {G₂ : HomTerm C D} {L₂ : HomTerm B C} {U₂ : HomTerm A B}
                  → U₁ ∘ G₂ ≈Term id
                  → (G₁ ∘ L₁ ∘ U₁) ∘ (G₂ ∘ L₂ ∘ U₂) ≈Term G₁ ∘ (L₁ ∘ L₂) ∘ U₂
      conj-cancel inv = assoc ○ (refl⟩∘⟨ (cancelInner inv ○ (⟺ assoc)))

      -- Each flat composite equals the grouped composite conjugated by ONE pair
      -- of global flatteners (the inner pair cancels).
      f-first≈ : f-first ≈Term gflat pre b₁ mid b₂ {r} ∘ f-then-g ∘ gunflat pre a₁ mid a₂ {r}
      f-first≈ =
        (refl⟩∘⟨ bridge-f pre mid a₂ r (⟦box⟧ f))
          ○ conj-cancel (gunflat∘gflat pre b₁ mid a₂)

      g-first≈ : g-first ≈Term gflat pre b₁ mid b₂ {r} ∘ g-then-f ∘ gunflat pre a₁ mid a₂ {r}
      g-first≈ =
        (bridge-f pre mid b₂ r (⟦box⟧ f) ⟩∘⟨refl)
          ○ conj-cancel (gunflat∘gflat pre a₁ mid b₂)

    -- THE THEOREM: the two flat orders are equal.  Reuses HeadSwap.swap-sound,
    -- conjugated by gflat/gunflat.  No braiding σ anywhere.
    two-box-swap : f-first ≈Term g-first
    two-box-swap = begin
      f-first
        ≈⟨ f-first≈ ⟩
      gflat pre b₁ mid b₂ ∘ f-then-g ∘ gunflat pre a₁ mid a₂
        ≈⟨ refl⟩∘⟨ swap-sound ⟩∘⟨refl ⟩
      gflat pre b₁ mid b₂ ∘ g-then-f ∘ gunflat pre a₁ mid a₂
        ≈⟨ g-first≈ ⟨
      g-first ∎

--------------------------------------------------------------------------------
-- Compatibility wrapper: the engine at the standard interpretation
-- `⟦box⟧ f = var (box f)` (each generator becomes an opaque wire-level
-- generator).  Old consumers keep working, gaining only the leading `v`
-- argument (instantiated at `Mon`).
--------------------------------------------------------------------------------
module Untyped (v : Variant) {X : Set} (Mor : List X → List X → Set) where

  open WireSig v {X} Mor
  open FreeMonoidalHelper.Mor v X mor using (HomTerm; var)

  ⟦box⟧ : ∀ {a b} → Mor a b → HomTerm (wires a) (wires b)
  ⟦box⟧ f = var (box f)

  open UntypedI v {X} Mor ⟦box⟧ public
