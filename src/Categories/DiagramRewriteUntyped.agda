{-# OPTIONS --safe --without-K #-}

module Categories.DiagramRewriteUntyped where

--------------------------------------------------------------------------------
-- An *untyped* normal form for free monoidal-category diagrams with
-- morphism generators.
--
-- A diagram is a list of boxes, each box carrying `List X` wire-label
-- offsets (prefix/suffix) and `List X` domain/range wire-labels.  We give:
--   * an interpretation ⟦_⟧ reflecting such a list into a HomTerm of the
--     free monoidal category, where the objects are flat "n-wire" objects
--     wires n;
--   * a head-swap that exchanges two adjacent boxes occupying *disjoint*,
--     non-crossing wire ranges, together with a soundness proof
--     ⟦ d ⟧ ≈Term ⟦ swap d ⟧.
--
-- KEY POINT (confirmed below): because the swap only moves a box past a
-- non-interacting neighbour, the soundness proof is *pure
-- bifunctoriality / interchange* — the M-content (⊗-∘-dist, id⊗id≈id)
-- plus structural reassociation discharged by hand from the merge/split
-- coherence lemmas — and never touches the braiding σ.
--------------------------------------------------------------------------------

open import Data.List using (List; []; _∷_; _++_)

open import Categories.Category using (Category)
import Categories.Morphism.Reasoning as MR
import Categories.Category.Monoidal.Reasoning as MonR

open import Categories.FreeMonoidal

--------------------------------------------------------------------------------
-- The wire-level signature, split out so that callers can TYPE a custom
-- `⟦box⟧` interpretation of the diagram-layer generators BEFORE
-- instantiating the engine (`UntypedI`) — breaking the chicken-and-egg
-- between the generator datatype `mor` and the interpretation parameter.
--------------------------------------------------------------------------------
module WireSig (v : Variant) {X : Set} (Mor : List X → List X → Set) where

  open FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var)

  -- the parallel wires named by a list of labels, right-nested
  wires : List X → ObjTerm
  wires []       = unit
  wires (x ∷ xs) = Var x ⊗₀ wires xs

  -- morphisms of the free monoidal category over the generators:
  -- a box `f : Mor a b` is a generator HomTerm (wires a) (wires b).
  data mor : ObjTerm → ObjTerm → Set where
    box : ∀ {a b} → Mor a b → mor (wires a) (wires b)

  --------------------------------------------------------------------------------
  -- Structural merge / split isos between `wires a ⊗₀ wires suf` and the
  -- flat `wires (a ++ suf)`.  Defined by recursion on `a`; only λ/α
  -- coherence morphisms appear, so all their laws are pure coherence.
  -- They are ⟦box⟧-INDEPENDENT, so they live here (not in `UntypedI`):
  -- callers can use them to BUILD a custom `⟦box⟧` (e.g. the σ-conjugated
  -- block braiding of `Categories.SolverSigma`) before instantiating the
  -- engine.  (The `FreeMonoidalHelper.Mor` open is `using`-scoped and not
  -- public, so WireSig's export surface grows by exactly merge/split.)
  --------------------------------------------------------------------------------
  private
    open module MorW = FreeMonoidalHelper.Mor v X mor
      using (HomTerm; id; _∘_; _⊗₁_; λ⇒; λ⇐; α⇒; α⇐)

  merge : (a : List X) {suf : List X} → HomTerm (wires a ⊗₀ wires suf) (wires (a ++ suf))
  merge []      = λ⇒
  merge (x ∷ a) = id ⊗₁ merge a ∘ α⇒

  split : (a : List X) {suf : List X} → HomTerm (wires (a ++ suf)) (wires a ⊗₀ wires suf)
  split []      = λ⇐
  split (x ∷ a) = α⇐ ∘ id ⊗₁ split a

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
  open FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor v X mor

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
  -- (pullˡ/pullʳ/pushˡ/pushʳ/center/cancel…/elim…), and ⊗-step
  -- combinators on Monoidal-FreeMonoidal (refl⟩⊗⟨_ etc.).  Plain `open`
  -- (not public): these are for the proofs in this file only.
  open MR FreeMonoidal
    using (pullˡ; pullʳ; pushˡ; pushʳ; center; center⁻¹;
           cancelˡ; cancelʳ; cancelInner; insertInner; elimˡ; elimʳ; introˡ; introʳ)
  open MonR Monoidal-FreeMonoidal
    using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; ⊗-distrib-over-∘;
           serialize₁₂; serialize₂₁; split₁ˡ; split₁ʳ; split₂ˡ; split₂ʳ)

  open ≈R

  -- fuse two id-tensored factors:  id⊗₁P ∘ id⊗₁Q ≈ id⊗₁(P∘Q)
  id⊗-∘ : ∀ {Z} {A B C} (P : HomTerm B C) (Q : HomTerm A B)
        → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ≈Term id {Z} ⊗₁ (P ∘ Q)
  id⊗-∘ P Q = (⟺ ⊗-∘-dist) ○ (idˡ ⟩⊗⟨refl)

  -- collapse three id-tensored factors:  id⊗₁P ∘ id⊗₁Q ∘ id⊗₁R ≈ id⊗₁(P∘Q∘R)
  id⊗-∘3 : ∀ {Z} {A B C D} (P : HomTerm C D) (Q : HomTerm B C) (R : HomTerm A B)
         → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ∘ id {Z} ⊗₁ R ≈Term id {Z} ⊗₁ (P ∘ Q ∘ R)
  id⊗-∘3 {Z} P Q R = (refl⟩∘⟨ id⊗-∘ Q R) ○ id⊗-∘ P (Q ∘ R)

  -- cancel two id-tensored mutually-inverse factors outright
  id⊗-cancel : ∀ {Z} {A B} {P : HomTerm B A} {Q : HomTerm A B}
             → P ∘ Q ≈Term id → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ≈Term id
  id⊗-cancel {P = P} {Q} PQ = id⊗-∘ P Q ○ (refl⟩⊗⟨ PQ) ○ id⊗id≈id

  -- (merge / split now live in `WireSig` — re-exported by the public open
  -- above — so that ⟦box⟧ interpretations can be built from them.)

  -- right-pad a morphism g : wires a ⇒ wires b by `suf` idle wires
  rpad : ∀ {a b} (suf : List X) → HomTerm (wires a) (wires b) → HomTerm (wires (a ++ suf)) (wires (b ++ suf))
  rpad {a} {b} suf g = merge b ∘ (g ⊗₁ id {wires suf}) ∘ split a

  -- full padding: `pre` idle wires, the box, then `suf` idle wires.
  pad : ∀ {a b} (pre : List X) (suf : List X) → HomTerm (wires a) (wires b)
      → HomTerm (wires (pre ++ (a ++ suf))) (wires (pre ++ (b ++ suf)))
  pad []      suf g = rpad suf g
  pad (x ∷ p) suf g = id ⊗₁ pad p suf g

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
  -- disjoint blocks of a five-block tensor commute past each other.  This
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
  -- merge / split are mutually inverse (pure coherence: the α-pair cancels
  -- in the middle, and the id-tensored recursive pair cancels by IH).
  --------------------------------------------------------------------------------
  merge∘split : ∀ (a : List X) {suf} → merge a {suf} ∘ split a ≈Term id
  merge∘split []      = λ⇒∘λ⇐≈id
  merge∘split (x ∷ a) = cancelInner α⇒∘α⇐≈id ○ id⊗-cancel (merge∘split a)

  split∘merge : ∀ (a : List X) {suf} → split a {suf} ∘ merge a ≈Term id
  split∘merge []      = λ⇐∘λ⇒≈id
  split∘merge (x ∷ a) = cancelInner (id⊗-cancel (split∘merge a)) ○ α⇐∘α⇒≈id

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

  -- right-nested prefix of `pre` wires attached to an object Y
  pfx : List X → ObjTerm → ObjTerm
  pfx []      Y = Y
  pfx (x ∷ p) Y = Var x ⊗₀ pfx p Y

  --------------------------------------------------------------------------------
  -- Prefix lifting: an equation between two morphisms over an object Y is
  -- preserved by prefixing `p` idle wires (id ⊗₁ … ).
  --------------------------------------------------------------------------------
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
    layer-f-in : HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                         (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
    layer-f-in = underP pre (blk {M = wires mid} {R = wires r} (⟦box⟧ f) (id {wires a₂}))

    layer-f-out : HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
                          (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
    layer-f-out = underP pre (blk {M = wires mid} {R = wires r} (⟦box⟧ f) (id {wires b₂}))

    layer-g-in : HomTerm (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                         (pfx pre (wires a₁ ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
    layer-g-in = underP pre (blk {M = wires mid} {R = wires r} (id {wires a₁}) (⟦box⟧ g))

    layer-g-out : HomTerm (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires a₂ ⊗₀ wires r))
                          (pfx pre (wires b₁ ⊗₀ wires mid ⊗₀ wires b₂ ⊗₀ wires r))
    layer-g-out = underP pre (blk {M = wires mid} {R = wires r} (id {wires b₁}) (⟦box⟧ g))

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

  -- `blk` for the (M = wires m, R = wires d) frame used by the bridge.
  -- We re-introduce the 4-block box at the flat level by conjugation.

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
      step₁ = (⟺ ⊗-distrib-over-∘) ○ (idʳ ⟩⊗⟨ idˡ)
      step₂ : (id ⊗₁ sflat m c {d}) ∘ (h ⊗₁ sunflat m c {d}) ≈Term h ⊗₁ id
      step₂ = (⟺ ⊗-distrib-over-∘) ○ (idˡ ⟩⊗⟨ sflat∘sunflat m c)

  -- blk with the idle box on the right is the box left-tensored with a
  -- single idle block over the whole suffix.
  blk-left-id : ∀ {m c d : List X} {a b} (h : HomTerm (wires a) (wires b))
              → blk {M = wires m} {R = wires d} h (id {wires c})
                ≈Term h ⊗₁ id {wires m ⊗₀ wires c ⊗₀ wires d}
  blk-left-id {m} {c} {d} h = refl⟩⊗⟨ ((refl⟩⊗⟨ id⊗id≈id) ○ id⊗id≈id)

  -- (id⊗-∘ / id⊗-∘3 / id⊗-cancel live next to ≈R at the top of `UntypedI`.)

  --------------------------------------------------------------------------------
  -- `liftW p W` : prepend `p` idle wires to a flat morphism W on `wires u`.
  -- This is the flat shift, recursing exactly like `pad`.  In fact
  -- `pad pre suf g = liftW pre (rpad suf g)` *definitionally*.
  --------------------------------------------------------------------------------
  liftW : (p : List X) {u v : List X} → HomTerm (wires u) (wires v)
        → HomTerm (wires (p ++ u)) (wires (p ++ v))
  liftW []      W = W
  liftW (x ∷ p) W = id ⊗₁ liftW p W

  -- Lemma A: the flat shift equals the merge/split conjugation.
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

  -- `pad` is literally the wire-shift of `rpad`.
  pad≡liftW : ∀ {a b} (pre suf : List X) (g : HomTerm (wires a) (wires b))
            → pad pre suf g ≈Term liftW pre (rpad suf g)
  pad≡liftW []      suf g = ≈-Term-refl
  pad≡liftW (x ∷ p) suf g = refl⟩⊗⟨ pad≡liftW p suf g

  --------------------------------------------------------------------------------
  -- Structural ++-associativity iso on flat wire objects, built from
  -- merge/split (NOT propositional subst).  Used to bridge the gap between
  -- f's codomain  wires (pre ++ (b₁ ++ (mid ++ (a₂ ++ r))))  and g's domain
  -- written as a flat pad at offset  pre ++ (b₁ ++ mid).
  --------------------------------------------------------------------------------
  -- defined by recursion on p: at each `∷` both indices grow by one label,
  -- so it is an id-reshape threaded through ⊗₁ (base case is genuinely id
  -- since [] ++ (q ++ s) = q ++ s = ([] ++ q) ++ s definitionally).
  assocW : (p q s : List X) → HomTerm (wires (p ++ (q ++ s))) (wires ((p ++ q) ++ s))
  assocW []      q s = id
  assocW (x ∷ p) q s = id ⊗₁ assocW p q s

  assocW⁻ : (p q s : List X) → HomTerm (wires ((p ++ q) ++ s)) (wires (p ++ (q ++ s)))
  assocW⁻ []      q s = id
  assocW⁻ (x ∷ p) q s = id ⊗₁ assocW⁻ p q s

  -- pflat-conjugation of a prefix-lifted wire morphism is its flat shift.
  pflatconj : ∀ (pre : List X) {u v} (Y : HomTerm (wires u) (wires v))
            → pflat pre {v} ∘ underP pre Y ∘ punflat pre {u} ≈Term liftW pre Y
  pflatconj []      Y = idˡ ○ idʳ
  pflatconj (x ∷ p) {u} {v} Y =
    id⊗-∘3 (pflat p) (underP p Y) (punflat p) ○ (refl⟩⊗⟨ pflatconj p Y)

  -- Lemma B: lifting by (x+m) vs lifting by x then m, bridged by assocW.
  liftW-assoc : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
              → liftW (x ++ m) W ∘ assocW x m u
                ≈Term assocW x m v ∘ liftW x (liftW m W)
  liftW-assoc []       m W = idʳ ○ (⟺ idˡ)
  liftW-assoc (y ∷ x) m {u} {v} W =
    id⊗-∘ _ _ ○ (refl⟩⊗⟨ liftW-assoc x m W) ○ (⟺ (id⊗-∘ _ _))

  -- pad as a conjugation by the prefix-flattener of a prefix-lifted rpad.
  padP-bridge : ∀ {a b} (pre suf : List X) (h : HomTerm (wires a) (wires b))
              → pad pre suf h
                ≈Term pflat pre ∘ underP pre (rpad suf h) ∘ punflat pre
  padP-bridge []      suf h = ⟺ (idˡ ○ idʳ)
  padP-bridge (x ∷ p) suf h =
    (refl⟩⊗⟨ padP-bridge p suf h)
      ○ (⟺ (id⊗-∘3 (pflat p) (underP p (rpad suf h)) (punflat p)))

  assocW⁻∘assocW : ∀ (p q s : List X) → assocW⁻ p q s ∘ assocW p q s ≈Term id
  assocW⁻∘assocW []      q s = idˡ
  assocW⁻∘assocW (x ∷ p) q s = id⊗-cancel (assocW⁻∘assocW p q s)

  --------------------------------------------------------------------------------
  -- Generic conjugation collapse: gflat ∘ underP pre X ∘ gunflat folds the
  -- three prefix-lifts into one and exposes the inner-flattener conjugation.
  --------------------------------------------------------------------------------
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

  -- merge-conjugation of a wire morphism is its flat shift (liftW), stated
  -- in the convenient direction.
  merge-shift : ∀ (p : List X) {u v} (W : HomTerm (wires u) (wires v))
              → merge p {v} ∘ (id {wires p} ⊗₁ W) ∘ split p {u} ≈Term liftW p W
  merge-shift p W = ⟺ (liftW-merge p W)

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
      ≈⟨ merge-shift x (liftW m (rpad d g)) ⟩
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
          ≈⟨ merge-shift m (rpad d g) ⟩
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

  -- liftW p respects ≈ and ∘ (functoriality of the flat shift).
  liftW-resp : ∀ (p : List X) {u v} {P Q : HomTerm (wires u) (wires v)}
             → P ≈Term Q → liftW p P ≈Term liftW p Q
  liftW-resp []      eq = eq
  liftW-resp (x ∷ p) eq = refl⟩⊗⟨ liftW-resp p eq

  liftW-∘ : ∀ (p : List X) {u v w} (P : HomTerm (wires v) (wires w)) (Q : HomTerm (wires u) (wires v))
          → liftW p (P ∘ Q) ≈Term liftW p P ∘ liftW p Q
  liftW-∘ []      P Q = ≈-Term-refl
  liftW-∘ (x ∷ p) P Q = (refl⟩⊗⟨ liftW-∘ p P Q) ○ (⟺ (id⊗-∘ _ _))

  -- rearranged Lemma B (both directions of conjugation made explicit).
  liftW-assoc' : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
               → liftW x (liftW m W)
                 ≈Term assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u
  liftW-assoc' x m {u} {v} W =
    introˡ (assocW⁻∘assocW x m v) ○ pullʳ (⟺ (liftW-assoc x m W))

  -- The double flat-shift equals the flat shift at the summed offset,
  -- conjugated by structural ++-associativity isos `assocW` (merge/split-built).
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
  --             structural iso `reassoc` (built from merge/split via assocW).
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
    g-out : HomTerm (wires (pre ++ (b₁ ++ (mid ++ (a₂ ++ r)))))
                    (wires (pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))))
    g-out = gflat pre b₁ mid b₂ {r}
              ∘ underP pre (blk {M = wires mid} {R = wires r} (id {wires b₁}) (⟦box⟧ g))
              ∘ gunflat pre b₁ mid a₂ {r}

    g-in : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))))
                   (wires (pre ++ (a₁ ++ (mid ++ (b₂ ++ r)))))
    g-in = gflat pre a₁ mid b₂ {r}
             ∘ underP pre (blk {M = wires mid} {R = wires r} (id {wires a₁}) (⟦box⟧ g))
             ∘ gunflat pre a₁ mid a₂ {r}

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

    -- Corollary: the g-out layer IS a genuine flat `pad` of g at the shifted
    -- offset  pre ++ (b₁ ++ mid) , conjugated by the structural ++-associativity
    -- reassoc isos (built from merge/split via assocW).  This realises the
    -- "g-layer = pad (pre ++ (b₁ ++ mid)) r ⟦g⟧ ∘ reassoc" reading of the bridge.
    reassocF-out : HomTerm (wires (pre ++ (b₁ ++ (mid ++ (a₂ ++ r)))))
                           (wires ((pre ++ (b₁ ++ mid)) ++ (a₂ ++ r)))
    reassocF-out = assocW pre (b₁ ++ mid) (a₂ ++ r) ∘ liftW pre (assocW b₁ mid (a₂ ++ r))

    reassocB-out : HomTerm (wires ((pre ++ (b₁ ++ mid)) ++ (b₂ ++ r)))
                           (wires (pre ++ (b₁ ++ (mid ++ (b₂ ++ r)))))
    reassocB-out = liftW pre (assocW⁻ b₁ mid (b₂ ++ r)) ∘ assocW⁻ pre (b₁ ++ mid) (b₂ ++ r)

    g-out≈pad : g-out
              ≈Term reassocB-out ∘ pad (pre ++ (b₁ ++ mid)) r (⟦box⟧ g) ∘ reassocF-out
    g-out≈pad = begin
      g-out
        ≈⟨ bridge-g pre b₁ mid r (⟦box⟧ g) ⟩
      liftW pre (liftW b₁ (liftW mid (rpad r (⟦box⟧ g))))
        ≈⟨ liftW-reassoc pre b₁ mid (rpad r (⟦box⟧ g)) ⟩
      reassocB-out ∘ liftW (pre ++ (b₁ ++ mid)) (rpad r (⟦box⟧ g)) ∘ reassocF-out
        ≈⟨ refl⟩∘⟨ (⟺ (pad≡liftW (pre ++ (b₁ ++ mid)) r (⟦box⟧ g))) ⟩∘⟨refl ⟩
      reassocB-out ∘ pad (pre ++ (b₁ ++ mid)) r (⟦box⟧ g) ∘ reassocF-out ∎

    -- The MIRROR of `g-out≈pad` for the `g-in` layer: `g-in` sits in the
    -- *dom* (a₁) frame rather than the *cod* (b₁) frame, so the reassociators
    -- use `a₁` in place of `b₁`.  Proven by the SAME machinery (`bridge-g` /
    -- `liftW-reassoc` / `pad≡liftW`), mirrored to the a₁-side.
    reassocF-in : HomTerm (wires (pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))))
                          (wires ((pre ++ (a₁ ++ mid)) ++ (a₂ ++ r)))
    reassocF-in = assocW pre (a₁ ++ mid) (a₂ ++ r) ∘ liftW pre (assocW a₁ mid (a₂ ++ r))

    reassocB-in : HomTerm (wires ((pre ++ (a₁ ++ mid)) ++ (b₂ ++ r)))
                          (wires (pre ++ (a₁ ++ (mid ++ (b₂ ++ r)))))
    reassocB-in = liftW pre (assocW⁻ a₁ mid (b₂ ++ r)) ∘ assocW⁻ pre (a₁ ++ mid) (b₂ ++ r)

    g-in≈pad : g-in
             ≈Term reassocB-in ∘ pad (pre ++ (a₁ ++ mid)) r (⟦box⟧ g) ∘ reassocF-in
    g-in≈pad = begin
      g-in
        ≈⟨ bridge-g pre a₁ mid r (⟦box⟧ g) ⟩
      liftW pre (liftW a₁ (liftW mid (rpad r (⟦box⟧ g))))
        ≈⟨ liftW-reassoc pre a₁ mid (rpad r (⟦box⟧ g)) ⟩
      reassocB-in ∘ liftW (pre ++ (a₁ ++ mid)) (rpad r (⟦box⟧ g)) ∘ reassocF-in
        ≈⟨ refl⟩∘⟨ (⟺ (pad≡liftW (pre ++ (a₁ ++ mid)) r (⟦box⟧ g))) ⟩∘⟨refl ⟩
      reassocB-in ∘ pad (pre ++ (a₁ ++ mid)) r (⟦box⟧ g) ∘ reassocF-in ∎

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
