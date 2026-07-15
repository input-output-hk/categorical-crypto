{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.Diagram where

--------------------------------------------------------------------------------
-- Normal form for free monoidal-category diagrams with morphism generators
--------------------------------------------------------------------------------
--
-- The wire-level signature (`WireSig`/`WireEngine`) and the diagram type `Diag`
-- — a list of boxes placed at wire-offsets — together with its interpretation
-- `⟦_⟧` into a HomTerm of the free monoidal category over flat "n-wire" objects.
--
-- `Diag` is indexed by its input and output wire-lists. A diagram is
-- only ever pattern-matched at a variable endpoint (≥ 1 of its two indices is a
-- variable): recognisers generalize a composite index through an explicit
-- equality (`meq`) and refl-match it later.  The `[]_` constructor's diagonal
-- index (input = output) makes this discipline mandatory.
--
-- The ⟦_⟧ᵇ-free wire coherence (`castW`/`assocW`/`liftW-merge`/…) lives in
-- `WireCoherence` (re-exported here through `DiagramI`); the sound disjoint
-- head-swap of two adjacent boxes lives in `Interchange`
-- (`TwoBoxSwap.two-box-swap`), instantiated at ⟦_⟧ᵇ by `Normalize`.
--
-- The native syntactic step relation `_⤳D_` (`DClosure`) is the rewrite closure
-- of an engine-supplied primitive-step family; a normalizer emits its witnesses
-- and the semantics enters only through `⤳D-sound`.

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)

open import Categories.Category
open import Categories.Coherence.Monoidal.WireCoherence
open import Categories.FreeMonoidal

--------------------------------------------------------------------------------
-- WireSig: the wire-level signature
--------------------------------------------------------------------------------

module WireSig (v : Variant) {X : Set} (Mor : List X → List X → Set) where

  open FreeMonoidalHelper v X using (ObjTerm)
  open FreeMonoidalHelper v X public using (wires)

  data mor : ObjTerm → ObjTerm → Set where
    box : ∀ {a b} → Mor a b → mor (wires a) (wires b)

-- The wire-level engine instance: a generator family `Mor` together with its
-- interpretation `⟦_⟧ᵇ` into the flat free category.
record WireEngine (v : Variant) {X : Set} : Set₁ where
  field Mor : List X → List X → Set

  open WireSig v {X} Mor
  open FreeMonoidalHelper.Mor v X mor

  -- the ᵇ (box) superscript keeps the name distinct from the diagram
  -- interpretation `⟦_⟧`, which every consumer has unqualified in the same
  -- scope (`DiagramI`'s cons clause uses both in one equation).
  field ⟦_⟧ᵇ : ∀ {a b} → Mor a b → HomTerm (wires a) (wires b)

--------------------------------------------------------------------------------
-- The engine, parametric in the variant `v` and the interpretation `⟦_⟧ᵇ`.
--------------------------------------------------------------------------------
module DiagramI {v : Variant} {X : Set} (E : WireEngine v) where

  open WireEngine E
  open WireSig v {X} Mor public
  open FreeMonoidalHelper.Mor v X mor

  module ≈R = Category.HomReasoning FreeMonoidal; open ≈R

  --------------------------------------------------------------------------------
  -- Diagrams: a list of layers.  Each layer is a box `f : Mor a b` placed
  -- at offset `pre`, with `suf` idle wires after it. Consing a layer in front
  -- turns a diagram of input width `pre ++ (b ++ suf)` into one of input width
  -- `pre ++ (a ++ suf)`, leaving the output index untouched.
  --------------------------------------------------------------------------------
  infixr 5 _▸_∷_⟨_⟩
  data Diag : List X → List X → Set where
    []_     : (n : List X) → Diag n n
    _▸_∷_⟨_⟩ : ∀ {a b m} (pre : List X) (suf : List X) (f : Mor a b)
             → Diag (pre ++ (b ++ suf)) m → Diag (pre ++ (a ++ suf)) m

  -- interpretation into the free monoidal category
  ⟦_⟧ : ∀ {n m} (d : Diag n m) → HomTerm (wires n) (wires m)
  ⟦ []_ n ⟧              = id
  ⟦ pre ▸ suf ∷ f ⟨ d ⟩ ⟧ = ⟦ d ⟧ ∘ pad pre suf (⟦ f ⟧ᵇ)

  open WireCoh v X mor public

  --------------------------------------------------------------------------------
  -- Transport of a diagram along a propositional equality of an endpoint index.
  --------------------------------------------------------------------------------

  substDiag : ∀ {m n k : List X} → m ≡ n → Diag m k → Diag n k
  substDiag refl d = d

  substDiagᵒ : ∀ {n k k' : List X} → k ≡ k' → Diag n k → Diag n k'
  substDiagᵒ refl d = d

  -- Both soundness lemmas read the transported diagram off as the original,
  -- conjugated by a single `castW` on the transported side: input transports
  -- pre-compose the inverse cast, codomain transports post-compose the cast.
  ⟦substDiag⟧ : ∀ {m n k : List X} (e : m ≡ n) (d : Diag m k)
    → ⟦ substDiag e d ⟧ ≈Term ⟦ d ⟧ ∘ castW (sym e)
  ⟦substDiag⟧ refl d = ⟺ idʳ

  ⟦substDiagᵒ⟧ : ∀ {n k k' : List X} (e : k ≡ k') (d : Diag n k)
    → ⟦ substDiagᵒ e d ⟧ ≈Term castW e ∘ ⟦ d ⟧
  ⟦substDiagᵒ⟧ refl d = ⟺ idˡ

  --------------------------------------------------------------------------------
  -- The native syntactic step relation `_⤳D_`: the rewrite-reachability
  -- relation (reflexive-transitive congruence closure, no symmetry) of an
  -- engine-supplied primitive-step family `Prim`.
  --
  -- The OPEN canonicity question (do interchange-equal diagrams reach the
  -- same normal form?) is precisely CONFLUENCE of this relation — a purely
  -- syntactic property of the relation itself.
  --------------------------------------------------------------------------------
  module DClosure (Prim : ∀ {n k} → Diag n k → Diag n k → Set) where

    infix 4 _⤳D_
    data _⤳D_ : ∀ {n k} → Diag n k → Diag n k → Set where
      prim   : ∀ {n k} {d d' : Diag n k} → Prim d d' → d ⤳D d'
      reflᴰ  : ∀ {n k} {d : Diag n k} → d ⤳D d
      transᴰ : ∀ {n k} {d d' d'' : Diag n k} → d ⤳D d' → d' ⤳D d'' → d ⤳D d''
      consᴰ  : ∀ {a b k} {pre suf : List X} {f : Mor a b}
               {rest rest' : Diag (pre ++ (b ++ suf)) k}
             → rest ⤳D rest'
             → (pre ▸ suf ∷ f ⟨ rest ⟩) ⤳D (pre ▸ suf ∷ f ⟨ rest' ⟩)

    ⤳D-sound : (prim-sound : ∀ {n k} {d d' : Diag n k}
                           → Prim d d' → ⟦ d ⟧ ≈Term ⟦ d' ⟧)
             → ∀ {n k} {d d' : Diag n k} → d ⤳D d' → ⟦ d ⟧ ≈Term ⟦ d' ⟧
    ⤳D-sound ps (prim p)     = ps p
    ⤳D-sound ps reflᴰ        = ≈-Term-refl
    ⤳D-sound ps (transᴰ p q) = ⤳D-sound ps p ○ ⤳D-sound ps q
    ⤳D-sound ps (consᴰ p)    = ⤳D-sound ps p ⟩∘⟨refl

stdEngine : (v : Variant) {X : Set} (Mor : List X → List X → Set) → WireEngine v
stdEngine v {X} Mor = record { Mor = Mor ; ⟦_⟧ᵇ = var ∘′ box }
  where
    open WireSig v {X} Mor
    open FreeMonoidalHelper.Mor v X mor
