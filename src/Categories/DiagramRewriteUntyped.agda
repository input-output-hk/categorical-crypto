{-# OPTIONS --safe --without-K #-}

module Categories.DiagramRewriteUntyped where

--------------------------------------------------------------------------------
-- An *untyped* normal form for free monoidal-category diagrams with
-- morphism generators.
--
-- A diagram is a list of boxes, each box carrying plain ℕ wire-offsets
-- and ℕ domain/range wire-counts.  We give:
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

open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.FreeMonoidal

module Untyped {X : Set} (Mor : List X → List X → Set) where

  open FreeMonoidalHelper Mon X using (ObjTerm; unit; _⊗₀_; Var)

  -- the parallel wires named by a list of labels, right-nested
  wires : List X → ObjTerm
  wires []       = unit
  wires (x ∷ xs) = Var x ⊗₀ wires xs

  -- morphisms of the free monoidal category over the generators:
  -- a box `f : Mor a b` is a generator HomTerm (wires a) (wires b).
  data mor : ObjTerm → ObjTerm → Set where
    box : ∀ {a b} → Mor a b → mor (wires a) (wires b)

  open FreeMonoidalHelper.Mor Mon X mor

  -- minimal equational reasoning for the index-heterogeneous _≈Term_
  module ≈R where
    infix  3 _∎
    infixr 2 step-≈ step-≈˘ _≈⟨⟩_
    infix  1 begin_
    begin_ : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → f ≈Term g
    begin x = x
    _≈⟨⟩_ : ∀ {A B} (f : HomTerm A B) {g} → f ≈Term g → f ≈Term g
    _ ≈⟨⟩ x = x
    step-≈ : ∀ {A B} (f : HomTerm A B) {g h} → g ≈Term h → f ≈Term g → f ≈Term h
    step-≈ _ gh fg = ≈-Term-trans fg gh
    step-≈˘ : ∀ {A B} (f : HomTerm A B) {g h} → g ≈Term h → g ≈Term f → f ≈Term h
    step-≈˘ _ gh gf = ≈-Term-trans (≈-Term-sym gf) gh
    _∎ : ∀ {A B} (f : HomTerm A B) → f ≈Term f
    _ ∎ = ≈-Term-refl
    syntax step-≈  f gh fg = f ≈⟨ fg ⟩ gh
    syntax step-≈˘ f gh gf = f ≈⟨ gf ⟨ gh

  ⟦box⟧ : ∀ {a b} → Mor a b → HomTerm (wires a) (wires b)
  ⟦box⟧ f = var (box f)

  idW : (n : List X) → HomTerm (wires n) (wires n)
  idW n = id

  --------------------------------------------------------------------------------
  -- Structural merge / split isos between `wires a ⊗₀ wires suf` and the
  -- flat `wires (a + suf)`.  Defined by recursion on `a`; only λ/α
  -- coherence morphisms appear, so all their laws are pure coherence.
  --------------------------------------------------------------------------------

  merge : (a : List X) {suf : List X} → HomTerm (wires a ⊗₀ wires suf) (wires (a ++ suf))
  merge []       = λ⇒
  merge (x ∷ a) = id ⊗₁ merge a ∘ α⇒

  split : (a : List X) {suf : List X} → HomTerm (wires (a ++ suf)) (wires a ⊗₀ wires suf)
  split []       = λ⇐
  split (x ∷ a) = α⇐ ∘ id ⊗₁ split a

  -- right-pad a morphism g : wires a ⇒ wires b by `suf` idle wires
  rpad : ∀ {a b} (suf : List X) → HomTerm (wires a) (wires b) → HomTerm (wires (a ++ suf)) (wires (b ++ suf))
  rpad {a} {b} suf g = merge b ∘ (g ⊗₁ idW suf) ∘ split a

  -- full padding: `pre` idle wires, the box, then `suf` idle wires.
  pad : ∀ {a b} (pre : List X) (suf : List X) → HomTerm (wires a) (wires b)
      → HomTerm (wires (pre ++ (a ++ suf))) (wires (pre ++ (b ++ suf)))
  pad []      suf g = rpad suf g
  pad (x ∷ p) suf g = id ⊗₁ pad p suf g

  --------------------------------------------------------------------------------
  -- Diagrams: a list of layers.  Each layer is a box `f : Mor a b` placed
  -- at offset `pre`, with `suf` idle wires after it.  The diagram is
  -- indexed by its input wire-count; consing a layer in front turns a
  -- diagram of input width `pre + (b + suf)` into one of input width
  -- `pre + (a + suf)`.  The list is read left-to-right = bottom-to-top:
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
  ⟦ []_ n ⟧             = idW n
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

    open ≈R

    -- idle-block functoriality: blk (g∘f) (g'∘f') ≈ blk g g' ∘ blk f f'
    blk-∘ : ∀ {A B A2 C D C2} (g : HomTerm B A2) (f : HomTerm A B)
              (g' : HomTerm D C2) (f' : HomTerm C D)
          → blk (g ∘ f) (g' ∘ f') ≈Term blk g g' ∘ blk f f'
    blk-∘ g f g' f' = begin
      (g ∘ f) ⊗₁ (id ⊗₁ ((g' ∘ f') ⊗₁ id))
        ≈⟨ idsplit ⟩
      (g ∘ f) ⊗₁ ((id ∘ id) ⊗₁ ((g' ∘ f') ⊗₁ (id ∘ id)))
        ≈⟨ ⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl ⊗-∘-dist) ⟩
      (g ∘ f) ⊗₁ ((id ∘ id) ⊗₁ ((g' ⊗₁ id) ∘ (f' ⊗₁ id)))
        ≈⟨ ⊗-resp-≈ ≈-Term-refl ⊗-∘-dist ⟩
      (g ∘ f) ⊗₁ ((id ⊗₁ (g' ⊗₁ id)) ∘ (id ⊗₁ (f' ⊗₁ id)))
        ≈⟨ ⊗-∘-dist ⟩
      blk g g' ∘ blk f f' ∎
      where
        idsplit : (g ∘ f) ⊗₁ (id ⊗₁ ((g' ∘ f') ⊗₁ id))
                ≈Term (g ∘ f) ⊗₁ ((id ∘ id) ⊗₁ ((g' ∘ f') ⊗₁ (id ∘ id)))
        idsplit = ⊗-resp-≈ ≈-Term-refl
                  (⊗-resp-≈ (≈-Term-sym idˡ)
                  (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)))

    -- the interchange itself: blk f id ∘ blk id g ≈ blk id g ∘ blk f id
    -- (boxes in disjoint blocks commute), via blk-∘ both ways through the
    -- common diagonal blk f g.
    blk-swap : ∀ {A A' C C'} (f : HomTerm A A') (g : HomTerm C C')
             → blk f id ∘ blk id g ≈Term blk id g ∘ blk f id
    blk-swap f g = begin
      blk f id ∘ blk id g
        ≈⟨ blk-∘ f id id g ⟨
      blk (f ∘ id) (id ∘ g)
        ≈⟨ ⊗-resp-≈ idʳ (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl)) ⟩
      blk f g
        ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ (≈-Term-sym idʳ) ≈-Term-refl)) ⟩
      blk (id ∘ f) (g ∘ id)
        ≈⟨ blk-∘ id f g id ⟩
      blk id g ∘ blk f id ∎

  --------------------------------------------------------------------------------
  -- merge / split are mutually inverse (pure coherence, proven by hand).
  --------------------------------------------------------------------------------
  open ≈R

  merge∘split : ∀ (a : List X) {suf} → merge a {suf} ∘ split a ≈Term id
  merge∘split []       = λ⇒∘λ⇐≈id
  merge∘split (x ∷ a) = begin
    (id ⊗₁ merge a ∘ α⇒) ∘ (α⇐ ∘ id ⊗₁ split a)
      ≈⟨ assoc ⟩
    id ⊗₁ merge a ∘ (α⇒ ∘ (α⇐ ∘ id ⊗₁ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    id ⊗₁ merge a ∘ ((α⇒ ∘ α⇐) ∘ id ⊗₁ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒∘α⇐≈id ≈-Term-refl) ⟩
    id ⊗₁ merge a ∘ (id ∘ id ⊗₁ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    id ⊗₁ merge a ∘ id ⊗₁ split a
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (merge a ∘ split a)
      ≈⟨ ⊗-resp-≈ idˡ (merge∘split a) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  split∘merge : ∀ (a : List X) {suf} → split a {suf} ∘ merge a ≈Term id
  split∘merge []       = λ⇐∘λ⇒≈id
  split∘merge (x ∷ a) = begin
    (α⇐ ∘ id ⊗₁ split a) ∘ (id ⊗₁ merge a ∘ α⇒)
      ≈⟨ assoc ⟩
    α⇐ ∘ (id ⊗₁ split a ∘ (id ⊗₁ merge a ∘ α⇒))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    α⇐ ∘ ((id ⊗₁ split a ∘ id ⊗₁ merge a) ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
    α⇐ ∘ ((id ∘ id) ⊗₁ (split a ∘ merge a) ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idˡ (split∘merge a)) ≈-Term-refl) ⟩
    α⇐ ∘ (id ⊗₁ id ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
    α⇐ ∘ (id ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    α⇐ ∘ α⇒
      ≈⟨ α⇐∘α⇒≈id ⟩
    id ∎

  --------------------------------------------------------------------------------
  -- Bridging the flat `pad` to the grouped `blk` form.
  --
  -- The flat layer  pad pre suf g : wires(pre+(a+suf)) ⇒ wires(pre+(b+suf))
  -- equals, up to the structural merge/split isos, the grouped block
  --   blk{wires pre}{unit}{wires suf} g id    (here M = unit, the 4th box id)
  -- post/pre-composed with flatteners.  We package the conjugation so that
  -- consecutive layers' flatteners cancel.
  --
  -- We use the two-block (binary) special case of interchange, which is
  -- exactly bifunctoriality, to slide a box past a disjoint neighbour at
  -- the flat level.
  --------------------------------------------------------------------------------

  -- right-nested prefix of `pre` wires attached to an object Y
  pfx : List X → ObjTerm → ObjTerm
  pfx []      Y = Y
  pfx (x ∷ p) Y = Var x ⊗₀ pfx p Y

  -- A box placed at offset `pre` with `suf` idle wires, but kept in the
  -- grouped object  pfx pre (wires a ⊗₀ wires suf).  Definitionally this
  -- is id-tensoring on the prefix; it needs no arithmetic.
  gpad : ∀ {a b} (pre suf : List X) → HomTerm (wires a) (wires b)
       → HomTerm (pfx pre (wires a ⊗₀ wires suf)) (pfx pre (wires b ⊗₀ wires suf))
  gpad []      suf g = g ⊗₁ id
  gpad (x ∷ p) suf g = id ⊗₁ gpad p suf g

  -- flatten the grouped layer object to the flat wire object
  flat : (pre : List X) {a suf : List X}
       → HomTerm (pfx pre (wires a ⊗₀ wires suf)) (wires (pre ++ (a ++ suf)))
  flat []      {a} = merge a
  flat (x ∷ p) {a} = id ⊗₁ flat p

  unflat : (pre : List X) {a suf : List X}
         → HomTerm (wires (pre ++ (a ++ suf))) (pfx pre (wires a ⊗₀ wires suf))
  unflat []      {a} = split a
  unflat (x ∷ p) {a} = id ⊗₁ unflat p

  flat∘unflat : ∀ (pre : List X) {a suf} → flat pre {a} {suf} ∘ unflat pre ≈Term id
  flat∘unflat []      = merge∘split _
  flat∘unflat (x ∷ p) = begin
    id ⊗₁ flat p ∘ id ⊗₁ unflat p
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (flat p ∘ unflat p)
      ≈⟨ ⊗-resp-≈ idˡ (flat∘unflat p) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  unflat∘flat : ∀ (pre : List X) {a suf} → unflat pre {a} {suf} ∘ flat pre ≈Term id
  unflat∘flat []      = split∘merge _
  unflat∘flat (x ∷ p) = begin
    id ⊗₁ unflat p ∘ id ⊗₁ flat p
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (unflat p ∘ flat p)
      ≈⟨ ⊗-resp-≈ idˡ (unflat∘flat p) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  -- the flat pad equals the conjugated grouped pad
  pad≈ : ∀ {a b} (pre suf : List X) (g : HomTerm (wires a) (wires b))
       → pad pre suf g ≈Term flat pre ∘ gpad pre suf g ∘ unflat pre
  pad≈ []      suf g = ≈-Term-refl
  pad≈ (x ∷ p) suf g = begin
    id ⊗₁ pad p suf g
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (pad≈ p suf g) ⟩
    id ⊗₁ (flat p ∘ gpad p suf g ∘ unflat p)
      ≈⟨ ≈-Term-sym (⊗-resp-≈ idˡ ≈-Term-refl) ⟩
    (id ∘ id) ⊗₁ (flat p ∘ gpad p suf g ∘ unflat p)
      ≈⟨ ⊗-∘-dist ⟩
    id ⊗₁ flat p ∘ id ⊗₁ (gpad p suf g ∘ unflat p)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym (⊗-resp-≈ idˡ ≈-Term-refl)) ⟩
    id ⊗₁ flat p ∘ (id ∘ id) ⊗₁ (gpad p suf g ∘ unflat p)
      ≈⟨ ∘-resp-≈ ≈-Term-refl ⊗-∘-dist ⟩
    id ⊗₁ flat p ∘ id ⊗₁ gpad p suf g ∘ id ⊗₁ unflat p ∎

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
  underP-resp (x ∷ p) eq = ⊗-resp-≈ ≈-Term-refl (underP-resp p eq)

  underP-id : ∀ {A} (p : List X) → underP p (id {A}) ≈Term id
  underP-id []      = ≈-Term-refl
  underP-id (x ∷ p) = begin
    id ⊗₁ underP p id
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (underP-id p) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  underP-∘ : ∀ {A B C} (p : List X) (g : HomTerm B C) (f : HomTerm A B)
           → underP p (g ∘ f) ≈Term underP p g ∘ underP p f
  underP-∘ []      g f = ≈-Term-refl
  underP-∘ (x ∷ p) g f = begin
    id ⊗₁ underP p (g ∘ f)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (underP-∘ p g f) ⟩
    id ⊗₁ (underP p g ∘ underP p f)
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
    (id ∘ id) ⊗₁ (underP p g ∘ underP p f)
      ≈⟨ ⊗-∘-dist ⟩
    id ⊗₁ underP p g ∘ id ⊗₁ underP p f ∎

  --------------------------------------------------------------------------------
  -- Grouped diagrams and the sound head-swap.
  --
  -- A *grouped* layer records, with plain-ℕ offsets, where a box sits:
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
        ≈⟨ underP-resp pre (≈-Term-sym (blk-swap (⟦box⟧ f) (⟦box⟧ g))) ⟩
      underP pre (blk (⟦box⟧ f) (id {wires b₂}) ∘ blk (id {wires a₁}) (⟦box⟧ g))
        ≈⟨ underP-∘ pre _ _ ⟩
      underP pre (blk (⟦box⟧ f) (id {wires b₂})) ∘ underP pre (blk (id {wires a₁}) (⟦box⟧ g)) ∎

  --------------------------------------------------------------------------------
  -- The bridge: from the grouped `HeadSwap.swap-sound` to the FLAT `pad`
  -- interpretation used by ⟦_⟧.
  --
  -- We build a global flattener `gflat` taking the grouped 4-block frame
  --   pfx pre (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d)
  -- to the flat object  wires (pre + (x + (m + (c + d)))) , together with
  -- its inverse `gunflat`.  Each flat layer (`pad`) then equals the
  -- corresponding grouped block (`underP pre (blk … …)`) conjugated by the
  -- global flatteners; conjugation by an iso preserves ≈Term, and the
  -- inter-layer flatteners + the +-associativity reassoc telescope to the
  -- identity, so `swap-sound` transports to the flat orders.
  --------------------------------------------------------------------------------

  -- `blk` for the (M = wires m, R = wires d) frame used by the bridge.
  -- We re-introduce the 4-block box at the flat level by conjugation.

  -- Inner flattener for the 3-block suffix  wires m ⊗₀ wires c ⊗₀ wires d
  --   → wires (m + (c + d)).
  sflat : (m c : List X) {d : List X}
        → HomTerm (wires m ⊗₀ wires c ⊗₀ wires d) (wires (m ++ (c ++ d)))
  sflat m c {d} = merge m ∘ (id ⊗₁ merge c {d})

  sunflat : (m c : List X) {d : List X}
          → HomTerm (wires (m ++ (c ++ d))) (wires m ⊗₀ wires c ⊗₀ wires d)
  sunflat m c {d} = (id ⊗₁ split c {d}) ∘ split m

  sflat∘sunflat : ∀ (m c : List X) {d} → sflat m c {d} ∘ sunflat m c ≈Term id
  sflat∘sunflat m c {d} = begin
    (merge m ∘ (id ⊗₁ merge c)) ∘ ((id ⊗₁ split c) ∘ split m)
      ≈⟨ assoc ⟩
    merge m ∘ ((id ⊗₁ merge c) ∘ ((id ⊗₁ split c) ∘ split m))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    merge m ∘ (((id ⊗₁ merge c) ∘ (id ⊗₁ split c)) ∘ split m)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
    merge m ∘ (((id ∘ id) ⊗₁ (merge c ∘ split c)) ∘ split m)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idˡ (merge∘split c)) ≈-Term-refl) ⟩
    merge m ∘ ((id ⊗₁ id) ∘ split m)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
    merge m ∘ (id ∘ split m)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    merge m ∘ split m
      ≈⟨ merge∘split m ⟩
    id ∎

  sunflat∘sflat : ∀ (m c : List X) {d} → sunflat m c {d} ∘ sflat m c ≈Term id
  sunflat∘sflat m c {d} = begin
    ((id ⊗₁ split c) ∘ split m) ∘ (merge m ∘ (id ⊗₁ merge c))
      ≈⟨ assoc ⟩
    (id ⊗₁ split c) ∘ (split m ∘ (merge m ∘ (id ⊗₁ merge c)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    (id ⊗₁ split c) ∘ ((split m ∘ merge m) ∘ (id ⊗₁ merge c))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge m) ≈-Term-refl) ⟩
    (id ⊗₁ split c) ∘ (id ∘ (id ⊗₁ merge c))
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    (id ⊗₁ split c) ∘ (id ⊗₁ merge c)
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (split c ∘ merge c)
      ≈⟨ ⊗-resp-≈ idˡ (split∘merge c) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  -- Inner 4-block flattener:  wires x ⊗₀ (suffix 3-block)  →  wires (x + (m+(c+d))).
  iflat : (x m c : List X) {d : List X}
        → HomTerm (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d)
                  (wires (x ++ (m ++ (c ++ d))))
  iflat x m c {d} = merge x ∘ (id ⊗₁ sflat m c {d})

  iunflat : (x m c : List X) {d : List X}
          → HomTerm (wires (x ++ (m ++ (c ++ d))))
                    (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d)
  iunflat x m c {d} = (id ⊗₁ sunflat m c {d}) ∘ split x

  iflat∘iunflat : ∀ (x m c : List X) {d} → iflat x m c {d} ∘ iunflat x m c ≈Term id
  iflat∘iunflat x m c {d} = begin
    (merge x ∘ (id ⊗₁ sflat m c)) ∘ ((id ⊗₁ sunflat m c) ∘ split x)
      ≈⟨ assoc ⟩
    merge x ∘ ((id ⊗₁ sflat m c) ∘ ((id ⊗₁ sunflat m c) ∘ split x))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    merge x ∘ (((id ⊗₁ sflat m c) ∘ (id ⊗₁ sunflat m c)) ∘ split x)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
    merge x ∘ (((id ∘ id) ⊗₁ (sflat m c ∘ sunflat m c)) ∘ split x)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idˡ (sflat∘sunflat m c)) ≈-Term-refl) ⟩
    merge x ∘ ((id ⊗₁ id) ∘ split x)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
    merge x ∘ (id ∘ split x)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    merge x ∘ split x
      ≈⟨ merge∘split x ⟩
    id ∎

  -- prefix flattener: reshape a right-nested prefix of `pre` wires sitting
  -- on top of an already-flat tail `wires n` into the flat `wires (pre+n)`.
  -- (Definitionally an identity on objects via `suc p + n = suc (p+n)`,
  -- but it must be threaded through ⊗₁ to retype.)
  pflat : (pre : List X) {n : List X} → HomTerm (pfx pre (wires n)) (wires (pre ++ n))
  pflat []      = id
  pflat (x ∷ p) = id ⊗₁ pflat p

  punflat : (pre : List X) {n : List X} → HomTerm (wires (pre ++ n)) (pfx pre (wires n))
  punflat []      = id
  punflat (x ∷ p) = id ⊗₁ punflat p

  pflat∘punflat : ∀ (pre : List X) {n} → pflat pre {n} ∘ punflat pre ≈Term id
  pflat∘punflat []      = idˡ
  pflat∘punflat (x ∷ p) = begin
    id ⊗₁ pflat p ∘ id ⊗₁ punflat p
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (pflat p ∘ punflat p)
      ≈⟨ ⊗-resp-≈ idˡ (pflat∘punflat p) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  punflat∘pflat : ∀ (pre : List X) {n} → punflat pre {n} ∘ pflat pre ≈Term id
  punflat∘pflat []      = idˡ
  punflat∘pflat (x ∷ p) = begin
    id ⊗₁ punflat p ∘ id ⊗₁ pflat p
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (punflat p ∘ pflat p)
      ≈⟨ ⊗-resp-≈ idˡ (punflat∘pflat p) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  iunflat∘iflat : ∀ (x m c : List X) {d} → iunflat x m c {d} ∘ iflat x m c ≈Term id
  iunflat∘iflat x m c {d} = begin
    ((id ⊗₁ sunflat m c) ∘ split x) ∘ (merge x ∘ (id ⊗₁ sflat m c))
      ≈⟨ assoc ⟩
    (id ⊗₁ sunflat m c) ∘ (split x ∘ (merge x ∘ (id ⊗₁ sflat m c)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    (id ⊗₁ sunflat m c) ∘ ((split x ∘ merge x) ∘ (id ⊗₁ sflat m c))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge x) ≈-Term-refl) ⟩
    (id ⊗₁ sunflat m c) ∘ (id ∘ (id ⊗₁ sflat m c))
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    (id ⊗₁ sunflat m c) ∘ (id ⊗₁ sflat m c)
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (sunflat m c ∘ sflat m c)
      ≈⟨ ⊗-resp-≈ idˡ (sunflat∘sflat m c) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  -- Global flattener: grouped 4-block frame  →  flat wires object.
  gflat : (pre x m c : List X) {d : List X}
        → HomTerm (pfx pre (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d))
                  (wires (pre ++ (x ++ (m ++ (c ++ d)))))
  gflat pre x m c {d} = pflat pre ∘ underP pre (iflat x m c {d})

  gunflat : (pre x m c : List X) {d : List X}
          → HomTerm (wires (pre ++ (x ++ (m ++ (c ++ d)))))
                    (pfx pre (wires x ⊗₀ wires m ⊗₀ wires c ⊗₀ wires d))
  gunflat pre x m c {d} = underP pre (iunflat x m c {d}) ∘ punflat pre

  gflat∘gunflat : ∀ (pre x m c : List X) {d}
                → gflat pre x m c {d} ∘ gunflat pre x m c ≈Term id
  gflat∘gunflat pre x m c {d} = begin
    (pflat pre ∘ underP pre (iflat x m c)) ∘ (underP pre (iunflat x m c) ∘ punflat pre)
      ≈⟨ assoc ⟩
    pflat pre ∘ (underP pre (iflat x m c) ∘ (underP pre (iunflat x m c) ∘ punflat pre))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    pflat pre ∘ ((underP pre (iflat x m c) ∘ underP pre (iunflat x m c)) ∘ punflat pre)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym (underP-∘ pre _ _)) ≈-Term-refl) ⟩
    pflat pre ∘ (underP pre (iflat x m c ∘ iunflat x m c) ∘ punflat pre)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (underP-resp pre (iflat∘iunflat x m c)) ≈-Term-refl) ⟩
    pflat pre ∘ (underP pre id ∘ punflat pre)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (underP-id pre) ≈-Term-refl) ⟩
    pflat pre ∘ (id ∘ punflat pre)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    pflat pre ∘ punflat pre
      ≈⟨ pflat∘punflat pre ⟩
    id ∎

  gunflat∘gflat : ∀ (pre x m c : List X) {d}
                → gunflat pre x m c {d} ∘ gflat pre x m c ≈Term id
  gunflat∘gflat pre x m c {d} = begin
    (underP pre (iunflat x m c) ∘ punflat pre) ∘ (pflat pre ∘ underP pre (iflat x m c))
      ≈⟨ assoc ⟩
    underP pre (iunflat x m c) ∘ (punflat pre ∘ (pflat pre ∘ underP pre (iflat x m c)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    underP pre (iunflat x m c) ∘ ((punflat pre ∘ pflat pre) ∘ underP pre (iflat x m c))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (punflat∘pflat pre) ≈-Term-refl) ⟩
    underP pre (iunflat x m c) ∘ (id ∘ underP pre (iflat x m c))
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    underP pre (iunflat x m c) ∘ underP pre (iflat x m c)
      ≈⟨ ≈-Term-sym (underP-∘ pre _ _) ⟩
    underP pre (iunflat x m c ∘ iflat x m c)
      ≈⟨ underP-resp pre (iunflat∘iflat x m c) ⟩
    underP pre id
      ≈⟨ underP-id pre ⟩
    id ∎

  --------------------------------------------------------------------------------
  -- Core bridge (pre = 0): the flat `rpad` of a left-block box equals the
  -- grouped block conjugated by the inner flatteners.
  --
  -- A box `h : wires a ⇒ wires b` placed in block 1 of the 4-block frame
  -- (everything else idle) flattens to  rpad (m+(c+d)) h.
  --------------------------------------------------------------------------------

  -- the f-side block at pre = 0:  h ⊗₁ id ⊗₁ id ⊗₁ id
  -- iflat b ∘ (h ⊗₁ idsuffix) ∘ iunflat a  ≈  rpad (m+(c+d)) h
  rpad-iconj : ∀ {a b} (m c : List X) {d : List X} (h : HomTerm (wires a) (wires b))
             → iflat b m c {d} ∘ (h ⊗₁ id {wires m ⊗₀ wires c ⊗₀ wires d}) ∘ iunflat a m c
               ≈Term rpad (m ++ (c ++ d)) h
  rpad-iconj {a} {b} m c {d} h = begin
    (merge b ∘ (id ⊗₁ sflat m c)) ∘ (h ⊗₁ id) ∘ ((id ⊗₁ sunflat m c) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    (merge b ∘ (id ⊗₁ sflat m c)) ∘ (((h ⊗₁ id) ∘ (id ⊗₁ sunflat m c)) ∘ split a)
      ≈⟨ assoc ⟩
    merge b ∘ ((id ⊗₁ sflat m c) ∘ (((h ⊗₁ id) ∘ (id ⊗₁ sunflat m c)) ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    merge b ∘ (((id ⊗₁ sflat m c) ∘ ((h ⊗₁ id) ∘ (id ⊗₁ sunflat m c))) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl) ⟩
    merge b ∘ ((((id ⊗₁ sflat m c) ∘ (h ⊗₁ id)) ∘ (id ⊗₁ sunflat m c)) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ≈-Term-refl) ⟩
    merge b ∘ ((((id ∘ h) ⊗₁ (sflat m c ∘ id)) ∘ (id ⊗₁ sunflat m c)) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ (⊗-resp-≈ idˡ idʳ) ≈-Term-refl) ≈-Term-refl) ⟩
    merge b ∘ (((h ⊗₁ sflat m c) ∘ (id ⊗₁ sunflat m c)) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
    merge b ∘ (((h ∘ id) ⊗₁ (sflat m c ∘ sunflat m c)) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idʳ (sflat∘sunflat m c)) ≈-Term-refl) ⟩
    merge b ∘ ((h ⊗₁ id) ∘ split a)
      ≈⟨ ≈-Term-sym assoc ⟩
    (merge b ∘ (h ⊗₁ id)) ∘ split a
      ≈⟨ assoc ⟩
    merge b ∘ ((h ⊗₁ id) ∘ split a) ∎

  -- blk with the idle box on the right is the box left-tensored with a
  -- single idle block over the whole suffix.
  blk-left-id : ∀ {m c d : List X} {a b} (h : HomTerm (wires a) (wires b))
              → blk {M = wires m} {R = wires d} h (id {wires c})
                ≈Term h ⊗₁ id {wires m ⊗₀ wires c ⊗₀ wires d}
  blk-left-id {m} {c} {d} h = ⊗-resp-≈ ≈-Term-refl
    (≈-Term-trans (⊗-resp-≈ ≈-Term-refl id⊗id≈id) id⊗id≈id)

  -- collapse three id-tensored factors:  id⊗₁P ∘ id⊗₁Q ∘ id⊗₁R ≈ id⊗₁(P∘Q∘R)
  id⊗-∘3 : ∀ {Z} {A B C D} (P : HomTerm C D) (Q : HomTerm B C) (R : HomTerm A B)
         → id {Z} ⊗₁ P ∘ id {Z} ⊗₁ Q ∘ id {Z} ⊗₁ R ≈Term id {Z} ⊗₁ (P ∘ Q ∘ R)
  id⊗-∘3 {Z} P Q R = begin
    id ⊗₁ P ∘ (id ⊗₁ Q ∘ id ⊗₁ R)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym ⊗-∘-dist) ⟩
    id ⊗₁ P ∘ (id ∘ id) ⊗₁ (Q ∘ R)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ≈-Term-refl) ⟩
    id ⊗₁ P ∘ id ⊗₁ (Q ∘ R)
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (P ∘ (Q ∘ R))
      ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
    id ⊗₁ (P ∘ Q ∘ R) ∎

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
  liftW-merge []      W = begin
    W
      ≈⟨ ≈-Term-sym idʳ ⟩
    W ∘ id
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym λ⇒∘λ⇐≈id) ⟩
    W ∘ (λ⇒ ∘ λ⇐)
      ≈⟨ ≈-Term-sym assoc ⟩
    (W ∘ λ⇒) ∘ λ⇐
      ≈⟨ ∘-resp-≈ (≈-Term-sym λ⇒∘id⊗f≈f∘λ⇒) ≈-Term-refl ⟩
    (λ⇒ ∘ id ⊗₁ W) ∘ λ⇐
      ≈⟨ assoc ⟩
    λ⇒ ∘ (id ⊗₁ W ∘ λ⇐) ∎
  liftW-merge (x ∷ p) {u} {v} W = begin
    id ⊗₁ liftW p W
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (liftW-merge p W) ⟩
    id ⊗₁ (merge p ∘ (id ⊗₁ W) ∘ split p)
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
    (id ∘ id) ⊗₁ (merge p ∘ (id ⊗₁ W) ∘ split p)
      ≈⟨ ⊗-∘-dist ⟩
    id ⊗₁ merge p ∘ id ⊗₁ ((id ⊗₁ W) ∘ split p)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⟩
    id ⊗₁ merge p ∘ (id ∘ id) ⊗₁ ((id ⊗₁ W) ∘ split p)
      ≈⟨ ∘-resp-≈ ≈-Term-refl ⊗-∘-dist ⟩
    id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ W) ∘ id ⊗₁ split p)
      ≈⟨ reassoc-suc ⟩
    (id ⊗₁ merge p ∘ α⇒) ∘ id ⊗₁ W ∘ (α⇐ ∘ id ⊗₁ split p) ∎
    where
      open ≈R
      -- insert α⇒∘α⇐ = id in the middle and reassociate to expose
      -- merge (suc p) = id⊗₁merge p ∘ α⇒ and split (suc p) = α⇐ ∘ id⊗₁split p.
      reassoc-suc :
          id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ W) ∘ id ⊗₁ split p)
        ≈Term (id ⊗₁ merge p ∘ α⇒) ∘ id ⊗₁ W ∘ (α⇐ ∘ id ⊗₁ split p)
      reassoc-suc = begin
        id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ W) ∘ id ⊗₁ split p)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym idʳ) ≈-Term-refl) ⟩
        id ⊗₁ merge p ∘ ((id ⊗₁ (id ⊗₁ W) ∘ id) ∘ id ⊗₁ split p)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id)) ≈-Term-refl) ⟩
        id ⊗₁ merge p ∘ ((id ⊗₁ (id ⊗₁ W) ∘ (α⇒ ∘ α⇐)) ∘ id ⊗₁ split p)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl) ⟩
        id ⊗₁ merge p ∘ (((id ⊗₁ (id ⊗₁ W) ∘ α⇒) ∘ α⇐) ∘ id ⊗₁ split p)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl) ≈-Term-refl) ⟩
        id ⊗₁ merge p ∘ (((α⇒ ∘ (id ⊗₁ id) ⊗₁ W) ∘ α⇐) ∘ id ⊗₁ split p)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ assoc ≈-Term-refl) ⟩
        id ⊗₁ merge p ∘ ((α⇒ ∘ ((id ⊗₁ id) ⊗₁ W ∘ α⇐)) ∘ id ⊗₁ split p)
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        id ⊗₁ merge p ∘ (α⇒ ∘ (((id ⊗₁ id) ⊗₁ W ∘ α⇐) ∘ id ⊗₁ split p))
          ≈⟨ ≈-Term-sym assoc ⟩
        (id ⊗₁ merge p ∘ α⇒) ∘ (((id ⊗₁ id) ⊗₁ W ∘ α⇐) ∘ id ⊗₁ split p)
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        (id ⊗₁ merge p ∘ α⇒) ∘ ((id ⊗₁ id) ⊗₁ W ∘ (α⇐ ∘ id ⊗₁ split p))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ id⊗id≈id ≈-Term-refl) ≈-Term-refl) ⟩
        (id ⊗₁ merge p ∘ α⇒) ∘ (id ⊗₁ W ∘ (α⇐ ∘ id ⊗₁ split p)) ∎

  -- `pad` is literally the wire-shift of `rpad`.
  pad≡liftW : ∀ {a b} (pre suf : List X) (g : HomTerm (wires a) (wires b))
            → pad pre suf g ≈Term liftW pre (rpad suf g)
  pad≡liftW []      suf g = ≈-Term-refl
  pad≡liftW (x ∷ p) suf g = ⊗-resp-≈ ≈-Term-refl (pad≡liftW p suf g)

  --------------------------------------------------------------------------------
  -- Structural +-associativity iso on flat wire objects, built from
  -- merge/split (NOT propositional subst).  Used to bridge the gap between
  -- f's codomain  wires (pre + (b₁ + (mid + (a₂+r))))  and g's domain
  -- written as a flat pad at offset  pre + (b₁ + mid).
  --------------------------------------------------------------------------------
  -- defined by recursion on p: at each `suc` both indices grow by one `suc`,
  -- so it is an id-reshape threaded through ⊗₁ (base case is genuinely id
  -- since 0+(q+s) = q+s = (0+q)+s definitionally).
  assocW : (p q s : List X) → HomTerm (wires (p ++ (q ++ s))) (wires ((p ++ q) ++ s))
  assocW []      q s = id
  assocW (x ∷ p) q s = id ⊗₁ assocW p q s

  assocW⁻ : (p q s : List X) → HomTerm (wires ((p ++ q) ++ s)) (wires (p ++ (q ++ s)))
  assocW⁻ []      q s = id
  assocW⁻ (x ∷ p) q s = id ⊗₁ assocW⁻ p q s

  assocW∘assocW⁻ : ∀ (p q s : List X) → assocW p q s ∘ assocW⁻ p q s ≈Term id
  assocW∘assocW⁻ []      q s = idˡ
  assocW∘assocW⁻ (x ∷ p) q s = begin
    id ⊗₁ assocW p q s ∘ id ⊗₁ assocW⁻ p q s
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (assocW p q s ∘ assocW⁻ p q s)
      ≈⟨ ⊗-resp-≈ idˡ (assocW∘assocW⁻ p q s) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  -- pflat-conjugation of a prefix-lifted wire morphism is its flat shift.
  pflatconj : ∀ (pre : List X) {u v} (Y : HomTerm (wires u) (wires v))
            → pflat pre {v} ∘ underP pre Y ∘ punflat pre {u} ≈Term liftW pre Y
  pflatconj []      Y = begin
    id ∘ Y ∘ id
      ≈⟨ idˡ ⟩
    Y ∘ id
      ≈⟨ idʳ ⟩
    Y ∎
  pflatconj (x ∷ p) {u} {v} Y = begin
    id ⊗₁ pflat p ∘ id ⊗₁ underP p Y ∘ id ⊗₁ punflat p
      ≈⟨ id⊗-∘3 (pflat p) (underP p Y) (punflat p) ⟩
    id ⊗₁ (pflat p ∘ underP p Y ∘ punflat p)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (pflatconj p Y) ⟩
    id ⊗₁ liftW p Y ∎

  -- Lemma B: lifting by (x+m) vs lifting by x then m, bridged by assocW.
  liftW-assoc : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
              → liftW (x ++ m) W ∘ assocW x m u
                ≈Term assocW x m v ∘ liftW x (liftW m W)
  liftW-assoc []       m W = ≈-Term-trans idʳ (≈-Term-sym idˡ)
  liftW-assoc (y ∷ x) m {u} {v} W = begin
    id ⊗₁ liftW (x ++ m) W ∘ id ⊗₁ assocW x m u
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (liftW (x ++ m) W ∘ assocW x m u)
      ≈⟨ ⊗-resp-≈ idˡ (liftW-assoc x m W) ⟩
    id ⊗₁ (assocW x m v ∘ liftW x (liftW m W))
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
    (id ∘ id) ⊗₁ (assocW x m v ∘ liftW x (liftW m W))
      ≈⟨ ⊗-∘-dist ⟩
    id ⊗₁ assocW x m v ∘ id ⊗₁ liftW x (liftW m W) ∎

  -- pad as a conjugation by the prefix-flattener of a prefix-lifted rpad.
  padP-bridge : ∀ {a b} (pre suf : List X) (h : HomTerm (wires a) (wires b))
              → pad pre suf h
                ≈Term pflat pre ∘ underP pre (rpad suf h) ∘ punflat pre
  padP-bridge []      suf h = begin
    rpad suf h
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ rpad suf h
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym idʳ) ⟩
    id ∘ rpad suf h ∘ id ∎
  padP-bridge (x ∷ p) suf h = begin
    id ⊗₁ pad p suf h
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (padP-bridge p suf h) ⟩
    id ⊗₁ (pflat p ∘ underP p (rpad suf h) ∘ punflat p)
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
    (id ∘ id) ⊗₁ (pflat p ∘ underP p (rpad suf h) ∘ punflat p)
      ≈⟨ ⊗-∘-dist ⟩
    id ⊗₁ pflat p ∘ id ⊗₁ (underP p (rpad suf h) ∘ punflat p)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⟩
    id ⊗₁ pflat p ∘ (id ∘ id) ⊗₁ (underP p (rpad suf h) ∘ punflat p)
      ≈⟨ ∘-resp-≈ ≈-Term-refl ⊗-∘-dist ⟩
    id ⊗₁ pflat p ∘ id ⊗₁ underP p (rpad suf h) ∘ id ⊗₁ punflat p ∎

  assocW⁻∘assocW : ∀ (p q s : List X) → assocW⁻ p q s ∘ assocW p q s ≈Term id
  assocW⁻∘assocW []      q s = idˡ
  assocW⁻∘assocW (x ∷ p) q s = begin
    id ⊗₁ assocW⁻ p q s ∘ id ⊗₁ assocW p q s
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (assocW⁻ p q s ∘ assocW p q s)
      ≈⟨ ⊗-resp-≈ idˡ (assocW⁻∘assocW p q s) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

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
      ≈⟨ assoc ⟩
    pflat pre ∘ (underP pre (iflat x m c)
      ∘ (underP pre X ∘ (underP pre (iunflat x' m c') ∘ punflat pre)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
    pflat pre ∘ (underP pre (iflat x m c)
      ∘ ((underP pre X ∘ underP pre (iunflat x' m c')) ∘ punflat pre))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    pflat pre ∘ ((underP pre (iflat x m c)
      ∘ (underP pre X ∘ underP pre (iunflat x' m c'))) ∘ punflat pre)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym (underP-∘ pre _ _))) ≈-Term-refl) ⟩
    pflat pre ∘ ((underP pre (iflat x m c)
      ∘ underP pre (X ∘ iunflat x' m c')) ∘ punflat pre)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym (underP-∘ pre _ _)) ≈-Term-refl) ⟩
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
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (underP-resp pre (≈-Term-sym core)) ≈-Term-refl) ⟩
    pflat pre ∘ underP pre (iflat b m c ∘ (blk h (id {wires c})) ∘ iunflat a m c) ∘ punflat pre
      ≈⟨ ≈-Term-sym (gconj pre b m c a c h-block) ⟩
    gflat pre b m c ∘ underP pre (blk h (id {wires c})) ∘ gunflat pre a m c ∎
    where
      h-block : HomTerm (wires a ⊗₀ wires m ⊗₀ wires c ⊗₀ wires r)
                        (wires b ⊗₀ wires m ⊗₀ wires c ⊗₀ wires r)
      h-block = blk {M = wires m} {R = wires r} h (id {wires c})
      core : iflat b m c {r} ∘ (blk h (id {wires c})) ∘ iunflat a m c
             ≈Term rpad (m ++ (c ++ r)) h
      core = begin
        iflat b m c ∘ (blk h (id {wires c})) ∘ iunflat a m c
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (blk-left-id h) ≈-Term-refl) ⟩
        iflat b m c ∘ (h ⊗₁ id) ∘ iunflat a m c
          ≈⟨ rpad-iconj m c h ⟩
        rpad (m ++ (c ++ r)) h ∎

  -- merge-conjugation of a wire morphism is its flat shift (liftW), stated
  -- in the convenient direction.
  merge-shift : ∀ (p : List X) {u v} (W : HomTerm (wires u) (wires v))
              → merge p {v} ∘ (id {wires p} ⊗₁ W) ∘ split p {u} ≈Term liftW p W
  merge-shift p W = ≈-Term-sym (liftW-merge p W)

  -- The g-core: the right-block box, conjugated by the inner flatteners,
  -- is the double flat-shift of g's right-pad.  (g in block 3 / slot c.)
  gcore : ∀ (x m : List X) {a b d : List X} (g : HomTerm (wires a) (wires b))
        → iflat x m b {d} ∘ (blk {M = wires m} {R = wires d} (id {wires x}) g) ∘ iunflat x m a {d}
          ≈Term liftW x (liftW m (rpad d g))
  gcore x m {a} {b} {d} g = begin
    iflat x m b ∘ (blk (id {wires x}) g) ∘ iunflat x m a
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ blk≈ ≈-Term-refl) ⟩
    (merge x ∘ (id ⊗₁ sflat m b)) ∘ (id ⊗₁ Bg) ∘ ((id ⊗₁ sunflat m a) ∘ split x)
      ≈⟨ regroup ⟩
    merge x ∘ ((id ⊗₁ sflat m b) ∘ (id ⊗₁ Bg) ∘ (id ⊗₁ sunflat m a)) ∘ split x
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (id⊗-∘3 (sflat m b) Bg (sunflat m a)) ≈-Term-refl) ⟩
    merge x ∘ (id ⊗₁ (sflat m b ∘ Bg ∘ sunflat m a)) ∘ split x
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl innerY) ≈-Term-refl) ⟩
    merge x ∘ (id ⊗₁ liftW m (rpad d g)) ∘ split x
      ≈⟨ merge-shift x (liftW m (rpad d g)) ⟩
    liftW x (liftW m (rpad d g)) ∎
    where
      open ≈R
      Bg : HomTerm (wires m ⊗₀ wires a ⊗₀ wires d) (wires m ⊗₀ wires b ⊗₀ wires d)
      Bg = id {wires m} ⊗₁ (g ⊗₁ id {wires d})
      -- blk id g = id ⊗₁ (id ⊗₁ (g ⊗₁ id)) = id ⊗₁ Bg
      blk≈ : blk {M = wires m} {R = wires d} (id {wires x}) g ≈Term id {wires x} ⊗₁ Bg
      blk≈ = ≈-Term-refl
      -- bracket bookkeeping helpers (pure associativity)
      regroup :
          (merge x ∘ (id ⊗₁ sflat m b)) ∘ (id ⊗₁ Bg) ∘ ((id ⊗₁ sunflat m a) ∘ split x)
        ≈Term merge x ∘ ((id ⊗₁ sflat m b) ∘ (id ⊗₁ Bg) ∘ (id ⊗₁ sunflat m a)) ∘ split x
      regroup = begin
        (merge x ∘ (id ⊗₁ sflat m b)) ∘ (id ⊗₁ Bg) ∘ ((id ⊗₁ sunflat m a) ∘ split x)
          ≈⟨ assoc ⟩
        merge x ∘ ((id ⊗₁ sflat m b) ∘ ((id ⊗₁ Bg) ∘ ((id ⊗₁ sunflat m a) ∘ split x)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
        merge x ∘ ((id ⊗₁ sflat m b) ∘ (((id ⊗₁ Bg) ∘ (id ⊗₁ sunflat m a)) ∘ split x))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        merge x ∘ (((id ⊗₁ sflat m b) ∘ ((id ⊗₁ Bg) ∘ (id ⊗₁ sunflat m a))) ∘ split x) ∎
      regroupY :
          (merge m ∘ (id ⊗₁ merge b)) ∘ Bg ∘ ((id ⊗₁ split a) ∘ split m)
        ≈Term merge m ∘ ((id ⊗₁ merge b) ∘ Bg ∘ (id ⊗₁ split a)) ∘ split m
      regroupY = begin
        (merge m ∘ (id ⊗₁ merge b)) ∘ Bg ∘ ((id ⊗₁ split a) ∘ split m)
          ≈⟨ assoc ⟩
        merge m ∘ ((id ⊗₁ merge b) ∘ (Bg ∘ ((id ⊗₁ split a) ∘ split m)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
        merge m ∘ ((id ⊗₁ merge b) ∘ ((Bg ∘ (id ⊗₁ split a)) ∘ split m))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        merge m ∘ (((id ⊗₁ merge b) ∘ (Bg ∘ (id ⊗₁ split a))) ∘ split m) ∎
      -- inner collapse: sflat m b ∘ Bg ∘ sunflat m a ≈ liftW m (rpad d g)
      innerY : sflat m b ∘ Bg ∘ sunflat m a ≈Term liftW m (rpad d g)
      innerY = begin
        (merge m ∘ (id ⊗₁ merge b)) ∘ Bg ∘ ((id ⊗₁ split a) ∘ split m)
          ≈⟨ regroupY ⟩
        merge m ∘ ((id ⊗₁ merge b) ∘ Bg ∘ (id ⊗₁ split a)) ∘ split m
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (id⊗-∘3 (merge b) (g ⊗₁ id) (split a)) ≈-Term-refl) ⟩
        merge m ∘ (id ⊗₁ (merge b ∘ (g ⊗₁ id) ∘ split a)) ∘ split m
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
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (underP-resp pre (gcore x m g)) ≈-Term-refl) ⟩
    pflat pre ∘ underP pre (liftW x (liftW m (rpad r g))) ∘ punflat pre
      ≈⟨ pflatconj pre (liftW x (liftW m (rpad r g))) ⟩
    liftW pre (liftW x (liftW m (rpad r g))) ∎

  -- liftW p respects ≈ and ∘ (functoriality of the flat shift).
  liftW-resp : ∀ (p : List X) {u v} {P Q : HomTerm (wires u) (wires v)}
             → P ≈Term Q → liftW p P ≈Term liftW p Q
  liftW-resp []      eq = eq
  liftW-resp (x ∷ p) eq = ⊗-resp-≈ ≈-Term-refl (liftW-resp p eq)

  liftW-∘ : ∀ (p : List X) {u v w} (P : HomTerm (wires v) (wires w)) (Q : HomTerm (wires u) (wires v))
          → liftW p (P ∘ Q) ≈Term liftW p P ∘ liftW p Q
  liftW-∘ []      P Q = ≈-Term-refl
  liftW-∘ (x ∷ p) P Q = begin
    id ⊗₁ liftW p (P ∘ Q)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (liftW-∘ p P Q) ⟩
    id ⊗₁ (liftW p P ∘ liftW p Q)
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
    (id ∘ id) ⊗₁ (liftW p P ∘ liftW p Q)
      ≈⟨ ⊗-∘-dist ⟩
    id ⊗₁ liftW p P ∘ id ⊗₁ liftW p Q ∎

  -- rearranged Lemma B (both directions of conjugation made explicit).
  liftW-assoc' : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
               → liftW x (liftW m W)
                 ≈Term assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u
  liftW-assoc' x m {u} {v} W = begin
    liftW x (liftW m W)
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ liftW x (liftW m W)
      ≈⟨ ∘-resp-≈ (≈-Term-sym (assocW⁻∘assocW x m v)) ≈-Term-refl ⟩
    (assocW⁻ x m v ∘ assocW x m v) ∘ liftW x (liftW m W)
      ≈⟨ assoc ⟩
    assocW⁻ x m v ∘ (assocW x m v ∘ liftW x (liftW m W))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym (liftW-assoc x m W)) ⟩
    assocW⁻ x m v ∘ (liftW (x ++ m) W ∘ assocW x m u) ∎

  -- The double flat-shift equals the flat shift at the summed offset,
  -- conjugated by structural +-associativity isos `assocW` (merge/split-built).
  gpad-reassoc : ∀ (pre x m : List X) {u v} (W : HomTerm (wires u) (wires v))
               → liftW pre (liftW x (liftW m W))
                 ≈Term (liftW pre (assocW⁻ x m v) ∘ assocW⁻ pre (x ++ m) v)
                     ∘ liftW (pre ++ (x ++ m)) W
                     ∘ (assocW pre (x ++ m) u ∘ liftW pre (assocW x m u))
  gpad-reassoc pre x m {u} {v} W = begin
    liftW pre (liftW x (liftW m W))
      ≈⟨ liftW-resp pre (liftW-assoc' x m W) ⟩
    liftW pre (assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u)
      ≈⟨ liftW-∘ pre _ _ ⟩
    liftW pre (assocW⁻ x m v) ∘ liftW pre (liftW (x ++ m) W ∘ assocW x m u)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (liftW-∘ pre _ _) ⟩
    liftW pre (assocW⁻ x m v) ∘ liftW pre (liftW (x ++ m) W) ∘ liftW pre (assocW x m u)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (liftW-assoc' pre (x ++ m) W) ≈-Term-refl) ⟩
    liftW pre (assocW⁻ x m v)
      ∘ (assocW⁻ pre (x ++ m) v ∘ liftW (pre ++ (x ++ m)) W ∘ assocW pre (x ++ m) u)
      ∘ liftW pre (assocW x m u)
      ≈⟨ regroupG ⟩
    (liftW pre (assocW⁻ x m v) ∘ assocW⁻ pre (x ++ m) v)
      ∘ liftW (pre ++ (x ++ m)) W
      ∘ (assocW pre (x ++ m) u ∘ liftW pre (assocW x m u)) ∎
    where
      open ≈R
      A1 = liftW pre (assocW⁻ x m v)
      A2 = assocW⁻ pre (x ++ m) v
      WW = liftW (pre ++ (x ++ m)) W
      B2 = assocW pre (x ++ m) u
      B1 = liftW pre (assocW x m u)
      regroupG : A1 ∘ (A2 ∘ WW ∘ B2) ∘ B1
               ≈Term (A1 ∘ A2) ∘ WW ∘ (B2 ∘ B1)
      regroupG = begin
        A1 ∘ (A2 ∘ WW ∘ B2) ∘ B1
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl) ⟩
        A1 ∘ ((A2 ∘ WW) ∘ B2) ∘ B1
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        A1 ∘ ((A2 ∘ WW) ∘ (B2 ∘ B1))
          ≈⟨ ≈-Term-sym assoc ⟩
        (A1 ∘ (A2 ∘ WW)) ∘ (B2 ∘ B1)
          ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
        ((A1 ∘ A2) ∘ WW) ∘ (B2 ∘ B1)
          ≈⟨ assoc ⟩
        (A1 ∘ A2) ∘ (WW ∘ (B2 ∘ B1)) ∎

  --------------------------------------------------------------------------------
  -- THE BRIDGE THEOREM.  Two adjacent, disjoint, non-crossing boxes commute
  -- under the FLAT `pad` interpretation used by ⟦_⟧.
  --
  -- We work in a frame  pre | a₁/b₁ | mid | a₂/b₂ | r  of flat wires.  The two
  -- orders are:
  --   f-first:  apply f at offset `pre`  (suffix mid+(a₂+r)), then g at offset
  --             `pre+(b₁+mid)`  (suffix r) — the g-layer being a genuine flat
  --             pad bridged across the +-associativity gap by the structural
  --             iso `reassoc` (built from merge/split via assocW).
  --   g-first:  apply g at offset `pre+(a₁+mid)`, then f at offset `pre`.
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

    -- Each flat composite equals the grouped composite conjugated by ONE pair
    -- of global flatteners (the inner pair cancels).
    f-first≈ : f-first ≈Term gflat pre b₁ mid b₂ {r} ∘ f-then-g ∘ gunflat pre a₁ mid a₂ {r}
    f-first≈ = begin
      g-out ∘ f-in
        ≈⟨ ∘-resp-≈ ≈-Term-refl (bridge-f pre mid a₂ r (⟦box⟧ f)) ⟩
      (gflat pre b₁ mid b₂ ∘ Lg-out ∘ gunflat pre b₁ mid a₂)
        ∘ (gflat pre b₁ mid a₂ ∘ Lf-in ∘ gunflat pre a₁ mid a₂)
        ≈⟨ cancel-mid ⟩
      gflat pre b₁ mid b₂ ∘ (Lg-out ∘ Lf-in) ∘ gunflat pre a₁ mid a₂ ∎
      where
        Lf-in  = underP pre (blk {M = wires mid} {R = wires r} (⟦box⟧ f) (id {wires a₂}))
        Lg-out = underP pre (blk {M = wires mid} {R = wires r} (id {wires b₁}) (⟦box⟧ g))
        cancel-mid :
            (gflat pre b₁ mid b₂ ∘ Lg-out ∘ gunflat pre b₁ mid a₂)
              ∘ (gflat pre b₁ mid a₂ ∘ Lf-in ∘ gunflat pre a₁ mid a₂)
          ≈Term gflat pre b₁ mid b₂ ∘ (Lg-out ∘ Lf-in) ∘ gunflat pre a₁ mid a₂
        cancel-mid = begin
          (gflat pre b₁ mid b₂ ∘ Lg-out ∘ gunflat pre b₁ mid a₂)
            ∘ (gflat pre b₁ mid a₂ ∘ Lf-in ∘ gunflat pre a₁ mid a₂)
            ≈⟨ assoc ⟩
          gflat pre b₁ mid b₂ ∘ ((Lg-out ∘ gunflat pre b₁ mid a₂)
            ∘ (gflat pre b₁ mid a₂ ∘ Lf-in ∘ gunflat pre a₁ mid a₂))
            ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
          gflat pre b₁ mid b₂ ∘ (Lg-out ∘ (gunflat pre b₁ mid a₂
            ∘ (gflat pre b₁ mid a₂ ∘ Lf-in ∘ gunflat pre a₁ mid a₂)))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
          gflat pre b₁ mid b₂ ∘ (Lg-out ∘ ((gunflat pre b₁ mid a₂
            ∘ gflat pre b₁ mid a₂) ∘ (Lf-in ∘ gunflat pre a₁ mid a₂)))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (gunflat∘gflat pre b₁ mid a₂) ≈-Term-refl)) ⟩
          gflat pre b₁ mid b₂ ∘ (Lg-out ∘ (id ∘ (Lf-in ∘ gunflat pre a₁ mid a₂)))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
          gflat pre b₁ mid b₂ ∘ (Lg-out ∘ (Lf-in ∘ gunflat pre a₁ mid a₂))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
          gflat pre b₁ mid b₂ ∘ ((Lg-out ∘ Lf-in) ∘ gunflat pre a₁ mid a₂) ∎

    g-first≈ : g-first ≈Term gflat pre b₁ mid b₂ {r} ∘ g-then-f ∘ gunflat pre a₁ mid a₂ {r}
    g-first≈ = begin
      f-out ∘ g-in
        ≈⟨ ∘-resp-≈ (bridge-f pre mid b₂ r (⟦box⟧ f)) ≈-Term-refl ⟩
      (gflat pre b₁ mid b₂ ∘ Lf-out ∘ gunflat pre a₁ mid b₂)
        ∘ (gflat pre a₁ mid b₂ ∘ Lg-in ∘ gunflat pre a₁ mid a₂)
        ≈⟨ cancel-mid ⟩
      gflat pre b₁ mid b₂ ∘ (Lf-out ∘ Lg-in) ∘ gunflat pre a₁ mid a₂ ∎
      where
        Lf-out = underP pre (blk {M = wires mid} {R = wires r} (⟦box⟧ f) (id {wires b₂}))
        Lg-in  = underP pre (blk {M = wires mid} {R = wires r} (id {wires a₁}) (⟦box⟧ g))
        cancel-mid :
            (gflat pre b₁ mid b₂ ∘ Lf-out ∘ gunflat pre a₁ mid b₂)
              ∘ (gflat pre a₁ mid b₂ ∘ Lg-in ∘ gunflat pre a₁ mid a₂)
          ≈Term gflat pre b₁ mid b₂ ∘ (Lf-out ∘ Lg-in) ∘ gunflat pre a₁ mid a₂
        cancel-mid = begin
          (gflat pre b₁ mid b₂ ∘ Lf-out ∘ gunflat pre a₁ mid b₂)
            ∘ (gflat pre a₁ mid b₂ ∘ Lg-in ∘ gunflat pre a₁ mid a₂)
            ≈⟨ assoc ⟩
          gflat pre b₁ mid b₂ ∘ ((Lf-out ∘ gunflat pre a₁ mid b₂)
            ∘ (gflat pre a₁ mid b₂ ∘ Lg-in ∘ gunflat pre a₁ mid a₂))
            ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
          gflat pre b₁ mid b₂ ∘ (Lf-out ∘ (gunflat pre a₁ mid b₂
            ∘ (gflat pre a₁ mid b₂ ∘ Lg-in ∘ gunflat pre a₁ mid a₂)))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
          gflat pre b₁ mid b₂ ∘ (Lf-out ∘ ((gunflat pre a₁ mid b₂
            ∘ gflat pre a₁ mid b₂) ∘ (Lg-in ∘ gunflat pre a₁ mid a₂)))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (gunflat∘gflat pre a₁ mid b₂) ≈-Term-refl)) ⟩
          gflat pre b₁ mid b₂ ∘ (Lf-out ∘ (id ∘ (Lg-in ∘ gunflat pre a₁ mid a₂)))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
          gflat pre b₁ mid b₂ ∘ (Lf-out ∘ (Lg-in ∘ gunflat pre a₁ mid a₂))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
          gflat pre b₁ mid b₂ ∘ ((Lf-out ∘ Lg-in) ∘ gunflat pre a₁ mid a₂) ∎

    -- THE THEOREM: the two flat orders are equal.  Reuses HeadSwap.swap-sound,
    -- conjugated by gflat/gunflat.  No braiding σ anywhere.
    two-box-swap : f-first ≈Term g-first
    two-box-swap = begin
      f-first
        ≈⟨ f-first≈ ⟩
      gflat pre b₁ mid b₂ ∘ f-then-g ∘ gunflat pre a₁ mid a₂
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ swap-sound ≈-Term-refl) ⟩
      gflat pre b₁ mid b₂ ∘ g-then-f ∘ gunflat pre a₁ mid a₂
        ≈⟨ ≈-Term-sym g-first≈ ⟩
      g-first ∎

    -- Corollary: the g-out layer IS a genuine flat `pad` of g at the shifted
    -- offset  pre + (b₁ + mid) , conjugated by the structural +-associativity
    -- reassoc isos (built from merge/split via assocW).  This realises the
    -- "g-layer = pad (pre+(b₁+mid)) r ⟦g⟧ ∘ reassoc" reading of the bridge.
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
        ≈⟨ gpad-reassoc pre b₁ mid (rpad r (⟦box⟧ g)) ⟩
      reassocB-out ∘ liftW (pre ++ (b₁ ++ mid)) (rpad r (⟦box⟧ g)) ∘ reassocF-out
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym (pad≡liftW (pre ++ (b₁ ++ mid)) r (⟦box⟧ g))) ≈-Term-refl) ⟩
      reassocB-out ∘ pad (pre ++ (b₁ ++ mid)) r (⟦box⟧ g) ∘ reassocF-out ∎

    -- The MIRROR of `g-out≈pad` for the `g-in` layer: `g-in` sits in the
    -- *dom* (a₁) frame rather than the *cod* (b₁) frame, so the reassociators
    -- use `a₁` in place of `b₁`.  Proven by the SAME machinery (`bridge-g` /
    -- `gpad-reassoc` / `pad≡liftW`), mirrored to the a₁-side.
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
        ≈⟨ gpad-reassoc pre a₁ mid (rpad r (⟦box⟧ g)) ⟩
      reassocB-in ∘ liftW (pre ++ (a₁ ++ mid)) (rpad r (⟦box⟧ g)) ∘ reassocF-in
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym (pad≡liftW (pre ++ (a₁ ++ mid)) r (⟦box⟧ g))) ≈-Term-refl) ⟩
      reassocB-in ∘ pad (pre ++ (a₁ ++ mid)) r (⟦box⟧ g) ∘ reassocF-in ∎

--------------------------------------------------------------------------------
-- Sanity check: the generalization genuinely subsumes the old single-object
-- case.  Instantiating `X = ⊤` recovers wire-count-typed boxes (the wire
-- counts are now `List ⊤`, i.e. unary ℕ), and `two-box-swap` still holds with
-- exactly the same statement and proof — still σ-free.
--------------------------------------------------------------------------------
private
  module SingleObjectExample (Mor : List ⊤ → List ⊤ → Set) where
    open Untyped {⊤} Mor

    -- the headline result transports verbatim to the ⊤-instance: for any two
    -- disjoint boxes, the two flat orders are equal (`f-first ≈Term g-first`),
    -- still proven σ-free by the same `TwoBoxSwap.two-box-swap`.  The type is
    -- inferred (it is exactly `f-first ≈Term g-first` of the ⊤-instance).
    swap⊤ : ∀ (pre mid r : List ⊤) {a₁ b₁ a₂ b₂ : List ⊤}
              (f : Mor a₁ b₁) (g : Mor a₂ b₂) → _
    swap⊤ pre mid r f g = TwoBoxSwap.two-box-swap pre mid r f g
