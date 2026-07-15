{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Disjoint interchange for flat monoidal diagrams: the sound wire-morphism head-swap.
--------------------------------------------------------------------------------
--
-- Two wire-typed morphisms living in disjoint, non-crossing wire ranges commute
-- past each other under the flat `pad` interpretation.  This is a theorem of the
-- ⟦_⟧ᵇ-free structural wire theory alone: it is engine-independent, mentioning
-- neither the diagram type `Diag` nor the box signature — the "boxes" are just
-- arbitrary wire-typed HomTerms `F`/`G`.  The proof is pure bifunctoriality /
-- interchange (⊗-∘-dist, id⊗id≈id) plus the ⟦_⟧ᵇ-free wire coherence of
-- `WireCoh` — NO braiding σ.  It depends only on `WireCoherence`.
--
-- Structure:
--   * `blk`/`blk-swap`     the interchange kernel on a 4-block tensor;
--   * `HeadSwap`           the grouped (prefix-lifted) head-swap + soundness;
--   * the `gflat`/`gunflat` bridge from the grouped form to the flat `pad`s;
--   * `TwoBoxSwap`         `two-box-swap`: the two flat firing orders are equal.
--
-- Consumed by `Normalize` (via `Frame`), instantiated at the box interpretation
-- `⟦_⟧ᵇ`, to justify reordering independent boxes; the diagram type `Diag`
-- and the engine live in `Diagram`.

module Categories.Coherence.Monoidal.Interchange where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Category
open import Categories.Coherence.Monoidal.WireCoherence
open import Categories.FreeMonoidal

module Interchange (v : Variant) (X : Set)
                   (mor : FreeMonoidalHelper.ObjTerm v X → FreeMonoidalHelper.ObjTerm v X → Set)
                   where

  open FreeMonoidalHelper v X
  open FreeMonoidalHelper.Mor v X mor
  open WireCoh v X mor

  open Category.HomReasoning FreeMonoidal
  open MR FreeMonoidal
  open MonR Monoidal-FreeMonoidal using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; serialize₁₂; serialize₂₁; merge₂ˡ)

  --------------------------------------------------------------------------------
  -- The soundness kernel: pure disjoint interchange.  Two boxes living in
  -- disjoint blocks of a four-block tensor commute past each other.  This
  -- uses ONLY bifunctoriality (⊗-∘-dist), id⊗id≈id and unit laws — no σ.
  --------------------------------------------------------------------------------
  private variable A A' B C C' : ObjTerm
  private module _ {M R : ObjTerm} where
    -- a box `x : A ⇒ A'` in block 1 and a box `y : C ⇒ C'` in block 3,
    -- everything else idle.  (4-block layout A ⊗ M ⊗ C ⊗ R.)
    blk : HomTerm A A' → HomTerm C C' → HomTerm (A ⊗₀ M ⊗₀ C ⊗₀ R) (A' ⊗₀ M ⊗₀ C' ⊗₀ R)
    blk x y = x ⊗₁ id ⊗₁ y ⊗₁ id

    -- the interchange itself: blk f id ∘ blk id g ≈ blk id g ∘ blk f id
    -- (boxes in disjoint blocks commute).  With the idle blocks collapsed
    -- (`id⊗id≈id`), `blk f id = f ⊗₁ id` and `blk id g = id ⊗₁ Gᵣ` (`Gᵣ` the
    -- right-block box in blocks 2-4), so both orders are `f ⊗₁ Gᵣ` by binary
    -- interchange (`serialize₁₂` / `serialize₂₁`) — no `blk-∘` needed.
    blk-swap : (f : HomTerm A A') (g : HomTerm C C') → blk f id ∘ blk id g ≈Term blk id g ∘ blk f id
    blk-swap f g = begin
      blk f id ∘ blk id g
        ≈⟨ (refl⟩⊗⟨ ((refl⟩⊗⟨ id⊗id≈id) ○ id⊗id≈id)) ⟩∘⟨refl ⟩
      (f ⊗₁ id) ∘ blk id g
        ≈⟨ ⟺ serialize₁₂ ⟩
      f ⊗₁ Gᵣ
        ≈⟨ serialize₂₁ ⟩
      blk id g ∘ (f ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ (⟺ ((refl⟩⊗⟨ id⊗id≈id) ○ id⊗id≈id))) ⟩
      blk id g ∘ blk f id ∎
      where
        Gᵣ = id ⊗₁ (g ⊗₁ id)

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

   -- map a morphism through the prefix of p idle wires
   underP : (p : List X) → HomTerm A B → HomTerm (pfx p A) (pfx p B)
   underP []      h = h
   underP (x ∷ p) h = id ⊗₁ underP p h

   underP-resp : (p : List X) {h k : HomTerm A B} → h ≈Term k → underP p h ≈Term underP p k
   underP-resp []      eq = eq
   underP-resp (x ∷ p) eq = refl⟩⊗⟨ underP-resp p eq

   underP-id : (p : List X) → underP p (id {A}) ≈Term id
   underP-id []      = ≈-Term-refl
   underP-id (x ∷ p) = (refl⟩⊗⟨ underP-id p) ○ id⊗id≈id

   underP-∘ : (p : List X) (g : HomTerm B C) (f : HomTerm A B)
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
                  (F : HomTerm (wires a₁) (wires b₁)) (G : HomTerm (wires a₂) (wires b₂)) where

    -- left / right slots hold the wire morphisms F / G and id elsewhere.
    private
      layer-f : (c : List X)
              → HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires c ⊗₀ wires r))
                        (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires c ⊗₀ wires r))
      layer-f c = underP pre (blk F (id))

      layer-g : (x : List X)
              → HomTerm (pfx pre (wires x ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                        (pfx pre (wires x ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
      layer-g x = underP pre (blk (id) G)

      layer-f-in  = layer-f a₂
      layer-f-out = layer-f b₂
      layer-g-in  = layer-g a₁
      layer-g-out = layer-g b₁

    f-then-g : HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                       (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
    f-then-g = layer-g-out ∘ layer-f-in

    g-then-f : HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                       (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
    g-then-f = layer-f-out ∘ layer-g-in

    -- SOUNDNESS of the head-swap: the two orders are equal in the free
    -- monoidal category.  Pure bifunctoriality — NO braiding σ.
    swap-sound : f-then-g ≈Term g-then-f
    swap-sound = begin
      underP pre (blk (id) G) ∘ underP pre (blk F (id))
        ≈⟨ underP-∘ pre _ _ ⟨
      underP pre (blk (id) G ∘ blk F (id))
        ≈⟨ underP-resp pre (⟺ (blk-swap F G)) ⟩
      underP pre (blk F (id) ∘ blk (id) G)
        ≈⟨ underP-∘ pre _ _ ⟩
      underP pre (blk F (id)) ∘ underP pre (blk (id) G) ∎

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
   sflat m c {d} = merge m ∘ (id ⊗₁ merge c)

   sunflat : (m c : List X) {d : List X}
           → HomTerm (wires (m ++ (c ++ d))) (wires m ⊗₀ wires c ⊗₀ wires d)
   sunflat m c {d} = (id ⊗₁ split c) ∘ split m

   sflat∘sunflat : ∀ (m c : List X) {d} → sflat m c {d} ∘ sunflat m c ≈Term id
   sflat∘sunflat m c {d} = cancelInner (id⊗-cancel (merge∘split c)) ○ merge∘split m

   sunflat∘sflat : ∀ (m c : List X) {d} → sunflat m c {d} ∘ sflat m c ≈Term id
   sunflat∘sflat m c {d} = cancelInner (split∘merge m) ○ id⊗-cancel (split∘merge c)

   -- Inner 4-block flattener:  wires x ⊗₀ (suffix 3-block)  →  wires (x ++ (m ++ (c ++ d))).
   iflat : (x m c : List X) {d : List X}
         → HomTerm (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d)
                   (wires (x ++ (m ++ (c ++ d))))
   iflat x m c {d} = merge x ∘ (id ⊗₁ sflat m c)

   iunflat : (x m c : List X) {d : List X}
           → HomTerm (wires (x ++ (m ++ (c ++ d))))
                     (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d)
   iunflat x m c {d} = (id ⊗₁ sunflat m c) ∘ split x

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
   gflat pre x m c {d} = pflat pre ∘ underP pre (iflat x m c)

   gunflat : (pre x m c : List X) {d : List X}
           → HomTerm (wires (pre ++ (x ++ (m ++ (c ++ d)))))
                     (pfx pre (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d))
   gunflat pre x m c {d} = underP pre (iunflat x m c) ∘ punflat pre

   gunflat∘gflat : ∀ (pre x m c : List X) {d} → gunflat pre x m c {d} ∘ gflat pre x m c ≈Term id
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

   -- a block-1 box (everything else idle), flattened, is its suffix flat-shift.
   rpad-iconj : ∀ {a b} (m c : List X) {d : List X} (h : HomTerm (wires a) (wires b))
              → iflat b m c ∘ (h ⊗₁ id) ∘ iunflat a m c
                ≈Term rpad (m ++ (c ++ d)) h
   rpad-iconj {a} {b} m c {d} h = pullʳ ((refl⟩∘⟨ pullˡ step₁) ○ pullˡ step₂)
     where
       step₁ : (h ⊗₁ id) ∘ (id ⊗₁ sunflat m c) ≈Term h ⊗₁ sunflat m c
       step₁ = ⟺ serialize₁₂
       step₂ : (id ⊗₁ sflat m c) ∘ (h ⊗₁ sunflat m c) ≈Term h ⊗₁ id
       step₂ = merge₂ˡ ○ (refl⟩⊗⟨ sflat∘sunflat m c)

   blk-left-id : ∀ {m c d : List X} {a b} (h : HomTerm (wires a) (wires b))
               → blk h (id)
                 ≈Term h ⊗₁ id {wires m ⊗₀ wires c ⊗₀ wires d}
   blk-left-id {m} {c} {d} h = refl⟩⊗⟨ ((refl⟩⊗⟨ id⊗id≈id) ○ id⊗id≈id)

   -- pflat-conjugation of a prefix-lifted wire morphism is its flat shift.
   pflatconj : ∀ (pre : List X) {u v} (Y : HomTerm (wires u) (wires v))
             → pflat pre ∘ underP pre Y ∘ punflat pre ≈Term liftW pre Y
   pflatconj []      Y = idˡ ○ idʳ
   pflatconj (x ∷ p) {u} {v} Y = id⊗-∘3 (pflat p) (underP p Y) (punflat p) ○ (refl⟩⊗⟨ pflatconj p Y)

   -- pad as a conjugation by the prefix-flattener of a prefix-lifted rpad.
   padP-bridge : ∀ {a b} (pre suf : List X) (h : HomTerm (wires a) (wires b))
               → pad pre suf h
                 ≈Term pflat pre ∘ underP pre (rpad suf h) ∘ punflat pre
   padP-bridge pre suf h = ⟺ (pflatconj pre (rpad suf h))

  --------------------------------------------------------------------------------
  -- Generic conjugation collapse: gflat ∘ underP pre X ∘ gunflat folds the
  -- three prefix-lifts into one and exposes the inner-flattener conjugation.
  --------------------------------------------------------------------------------
  private
   gconj : ∀ (pre x m c x' c' : List X) {d}
             (X : HomTerm (wires x' ⊗₀ wires m ⊗₀ wires c' ⊗₀ wires d)
                          (wires x  ⊗₀ wires m ⊗₀ wires c  ⊗₀ wires d))
         → gflat pre x m c ∘ underP pre X ∘ gunflat pre x' m c'
           ≈Term pflat pre
               ∘ underP pre (iflat x m c ∘ X ∘ iunflat x' m c')
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
              ≈Term gflat pre b m c
                  ∘ underP pre (blk h (id))
                  ∘ gunflat pre a m c
   bridge-f pre m c r {a} {b} h = begin
     pad pre (m ++ (c ++ r)) h
       ≈⟨ padP-bridge pre (m ++ (c ++ r)) h ⟩
     pflat pre ∘ underP pre (rpad (m ++ (c ++ r)) h) ∘ punflat pre
       ≈⟨ refl⟩∘⟨ underP-resp pre (⟺ core) ⟩∘⟨refl ⟩
     pflat pre ∘ underP pre (iflat b m c ∘ (blk h (id)) ∘ iunflat a m c) ∘ punflat pre
       ≈⟨ gconj pre b m c a c h-block ⟨
     gflat pre b m c ∘ underP pre (blk h (id)) ∘ gunflat pre a m c ∎
     where
       h-block : HomTerm (wires a ⊗₀ wires m ⊗₀ wires c ⊗₀ wires r)
                         (wires b ⊗₀ wires m ⊗₀ wires c ⊗₀ wires r)
       h-block = blk h (id)
       core : iflat b m c ∘ (blk h (id)) ∘ iunflat a m c ≈Term rpad (m ++ (c ++ r)) h
       core = (refl⟩∘⟨ blk-left-id h ⟩∘⟨refl) ○ rpad-iconj m c h

   -- Generic conjugation-by-flatteners = liftW: a box `M` flanked by the
   -- prefix-idle morphisms `A` (after) and `B` (before), all wrapped in
   -- `merge p`/`split p`, collapses to `liftW p` of the inner composite
   -- `A ∘ M ∘ B` once that composite is shown to be a wire morphism `W'`.
   -- (Used at the x-level and the m-level of `gcore` below.)
   liftW-merge-conj : ∀ (p : List X) {u v : List X} {V W : ObjTerm}
       (A : HomTerm V (wires v)) (M : HomTerm W V) (B : HomTerm (wires u) W)
       (W' : HomTerm (wires u) (wires v))
     → A ∘ M ∘ B ≈Term W'
     → (merge p ∘ (id ⊗₁ A)) ∘ (id ⊗₁ M) ∘ ((id ⊗₁ B) ∘ split p)
       ≈Term liftW p W'
   liftW-merge-conj p A M B W' hyp = begin
     (merge p ∘ (id ⊗₁ A)) ∘ (id ⊗₁ M) ∘ ((id ⊗₁ B) ∘ split p)
       ≈⟨ center (id⊗-∘ A M) ⟩
     merge p ∘ (id ⊗₁ (A ∘ M) ∘ ((id ⊗₁ B) ∘ split p))
       ≈⟨ refl⟩∘⟨ pullˡ (id⊗-∘ (A ∘ M) B) ⟩
     merge p ∘ (id ⊗₁ ((A ∘ M) ∘ B) ∘ split p)
       ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ (assoc ○ hyp)) ⟩∘⟨refl ⟩
     merge p ∘ (id ⊗₁ W' ∘ split p)
       ≈⟨ ⟺ (liftW-merge p W') ⟩
     liftW p W' ∎

   -- The g-core: the right-block box, conjugated by the inner flatteners,
   -- is the double flat-shift of g's right-pad.  (g in block 3 / slot c.)
   gcore : ∀ (x m : List X) {a b d : List X} (g : HomTerm (wires a) (wires b))
         → iflat x m b ∘ (blk id g) ∘ iunflat x m a ≈Term liftW x (liftW m (rpad d g))
   gcore x m {a} {b} {d} g =
     -- blk id g = id ⊗₁ (id ⊗₁ (g ⊗₁ id)) = id ⊗₁ Bg, definitionally; the
     -- inner collapse `innerY : sflat m b ∘ Bg ∘ sunflat m a ≈ liftW m (rpad d g)`
     -- is itself a `liftW-merge-conj` (at the m-level, inner `rpad d g`).
     liftW-merge-conj x (sflat m b) Bg (sunflat m a) (liftW m (rpad d g)) innerY
     where
       Bg : HomTerm (wires m ⊗₀ wires a ⊗₀ wires d) (wires m ⊗₀ wires b ⊗₀ wires d)
       Bg = id ⊗₁ (g ⊗₁ id)
       innerY : sflat m b ∘ Bg ∘ sunflat m a ≈Term liftW m (rpad d g)
       innerY = liftW-merge-conj m (merge b) (g ⊗₁ id) (split a) (rpad d g) ≈-Term-refl

   -- Bridge-g (to the liftW form): the grouped right-block g-layer, conjugated
   -- by gflat, equals the double flat-shift of g's right-pad.
   bridge-g : ∀ (pre x m r : List X) {a b : List X} (g : HomTerm (wires a) (wires b))
            → gflat pre x m b ∘ underP pre (blk id g) ∘ gunflat pre x m a
              ≈Term liftW pre (liftW x (liftW m (rpad r g)))
   bridge-g pre x m r {a} {b} g = begin
     gflat pre x m b ∘ underP pre (blk (id) g) ∘ gunflat pre x m a
       ≈⟨ gconj pre x m b x a (blk (id) g) ⟩
     pflat pre ∘ underP pre (iflat x m b ∘ (blk (id) g) ∘ iunflat x m a) ∘ punflat pre
       ≈⟨ refl⟩∘⟨ underP-resp pre (gcore x m g) ⟩∘⟨refl ⟩
     pflat pre ∘ underP pre (liftW x (liftW m (rpad r g))) ∘ punflat pre
       ≈⟨ pflatconj pre (liftW x (liftW m (rpad r g))) ⟩
     liftW pre (liftW x (liftW m (rpad r g))) ∎

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
       ≈⟨ liftW-resp pre (liftW-assoc x m W) ⟩
     liftW pre (assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u)
       ≈⟨ liftW-∘ pre _ _ ⟩
     liftW pre (assocW⁻ x m v) ∘ liftW pre (liftW (x ++ m) W ∘ assocW x m u)
       ≈⟨ refl⟩∘⟨ liftW-∘ pre _ _ ⟩
     liftW pre (assocW⁻ x m v) ∘ liftW pre (liftW (x ++ m) W) ∘ liftW pre (assocW x m u)
       ≈⟨ refl⟩∘⟨ liftW-assoc pre (x ++ m) W ⟩∘⟨refl ⟩
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
                    (F : HomTerm (wires a₁) (wires b₁)) (G : HomTerm (wires a₂) (wires b₂)) where

    open HeadSwap pre mid r F G

    -- ---- flat f-layers (genuine `pad`s) ----
    f-in : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))))
                   (wires (pre ++ (b₁ ++ (mid ++ (a₂ ++ r)))))
    f-in = pad pre (mid ++ (a₂ ++ r)) F

    f-out : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (b₂ ++ r)))))
                    (wires (pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))))
    f-out = pad pre (mid ++ (b₂ ++ r)) F

    -- ---- flat g-layers, as `gflat`-conjugates of the grouped block ----
    -- (Each equals a genuine flat `pad` of g at the shifted offset, conjugated
    --  by the structural reassoc iso — see `gLayer≈pad` below.)
    -- the structural reassoc isos at a given box offset (exposed so the
    -- normalizer can collapse them to single `castW`s at both offsets a₁/b₁
    -- with one offset-parametrised lemma each — see Normalize's
    -- `reassocF≈castW` / `reassocB≈castW`).
    reassocF : (x : List X)
             → HomTerm (wires (pre ++ (x ++ (mid ++ (a₂ ++ r)))))
                       (wires ((pre ++ (x ++ mid)) ++ (a₂ ++ r)))
    reassocF x = assocW pre (x ++ mid) (a₂ ++ r) ∘ liftW pre (assocW x mid (a₂ ++ r))

    reassocB : (x : List X)
             → HomTerm (wires ((pre ++ (x ++ mid)) ++ (b₂ ++ r)))
                       (wires (pre ++ (x ++ (mid ++ (b₂ ++ r)))))
    reassocB x = liftW pre (assocW⁻ x mid (b₂ ++ r)) ∘ assocW⁻ pre (x ++ mid) (b₂ ++ r)

    gLayer : (x : List X)
           → HomTerm (wires (pre ++ (x ++ (mid ++ (a₂ ++ r)))))
                     (wires (pre ++ (x ++ (mid ++ (b₂ ++ r)))))
    gLayer x = gflat pre x mid b₂ ∘ underP pre (blk id G) ∘ gunflat pre x mid a₂

    gLayer≈pad : (x : List X) → gLayer x ≈Term reassocB x ∘ pad (pre ++ (x ++ mid)) r G ∘ reassocF x
    gLayer≈pad x = begin
        gLayer x
          ≈⟨ bridge-g pre x mid r G ⟩
        liftW pre (liftW x (liftW mid (rpad r G)))
          ≈⟨ liftW-reassoc pre x mid (rpad r G) ⟩
        reassocB x ∘ liftW (pre ++ (x ++ mid)) (rpad r G) ∘ reassocF x
          ≈⟨ refl⟩∘⟨ (⟺ (pad≡liftW (pre ++ (x ++ mid)) r G)) ⟩∘⟨refl ⟩
        reassocB x ∘ pad (pre ++ (x ++ mid)) r G ∘ reassocF x ∎

    g-out        = gLayer b₁
    g-in         = gLayer a₁

    private
      -- f-first composite and g-first composite share dom & cod; both are the
      -- dom/cod of the public `two-box-swap`, which unfolds them transparently.
      f-first : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))))
                        (wires (pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))))
      f-first = g-out ∘ f-in

      g-first : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))))
                        (wires (pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))))
      g-first = f-out ∘ g-in

      -- shared collapse for f-first≈ / g-first≈: two conjugated layers whose
      -- inner flattener pair cancels (U₁ ∘ G₂ ≈ id).
      layers-cancel : ∀ {A B C D F G : ObjTerm}
                      {G₁ : HomTerm F G} {L₁ : HomTerm C F} {U₁ : HomTerm D C}
                      {G₂ : HomTerm C D} {L₂ : HomTerm B C} {U₂ : HomTerm A B}
                  → U₁ ∘ G₂ ≈Term id
                  → (G₁ ∘ L₁ ∘ U₁) ∘ (G₂ ∘ L₂ ∘ U₂) ≈Term G₁ ∘ (L₁ ∘ L₂) ∘ U₂
      layers-cancel inv = assoc ○ (refl⟩∘⟨ (cancelInner inv ○ (⟺ assoc)))

      -- Each flat composite equals the grouped composite conjugated by ONE pair
      -- of global flatteners (the inner pair cancels).
      f-first≈ : f-first ≈Term gflat pre b₁ mid b₂ ∘ f-then-g ∘ gunflat pre a₁ mid a₂
      f-first≈ = (refl⟩∘⟨ bridge-f pre mid a₂ r F) ○ layers-cancel (gunflat∘gflat pre b₁ mid a₂)

      g-first≈ : g-first ≈Term gflat pre b₁ mid b₂ ∘ g-then-f ∘ gunflat pre a₁ mid a₂
      g-first≈ = (bridge-f pre mid b₂ r F ⟩∘⟨refl) ○ layers-cancel (gunflat∘gflat pre a₁ mid b₂)

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
