{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.Diagram where

--------------------------------------------------------------------------------
-- Untyped normal form for free monoidal-category diagrams with morphism generators
--------------------------------------------------------------------------------
--
-- The wire-level signature (`WireSig`/`WireEngine`) and the diagram type `DiagU`
-- — a list of boxes placed at wire-offsets — together with its interpretation
-- `⟦_⟧` into a HomTerm of the free monoidal category over flat "n-wire" objects.
--
-- `DiagU` is indexed by BOTH its input and output wire-lists, so the codomain
-- is carried structurally rather than computed by a function.  A diagram is
-- only ever pattern-matched at a variable endpoint (≥ 1 of its two indices is a
-- variable): recognisers generalize a composite index through an explicit
-- equality (`meq`) and refl-match it later.  The `[]_` constructor's diagonal
-- index (input = output) makes this discipline mandatory — never case on a
-- diagram whose BOTH endpoints are `++`-composites.
--
-- The ⟦box⟧-free wire coherence (`castW`/`assocW`/`liftW-merge`/…) lives in
-- `WireCoherence` (re-exported here through `UntypedI`); the sound disjoint
-- head-swap of two adjacent boxes lives in `Interchange`
-- (`TwoBoxSwap.two-box-swap`), instantiated at ⟦box⟧ by `Normalize`.
--
-- The native syntactic step relation `_≈D_` (`DClosure`) is the rewrite closure
-- of an engine-supplied primitive-step family; a normalizer emits its witnesses
-- and the semantics enters only through `≈D-sound`.

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

  open FreeMonoidalHelper.Mor v X mor public using (merge; split; merge∘split; split∘merge)

-- The wire-level engine instance: a generator family `Mor` together with its
-- interpretation `⟦box⟧` into the flat free category.
record WireEngine (v : Variant) {X : Set} : Set₁ where
  field Mor : List X → List X → Set

  open WireSig v {X} Mor
  open FreeMonoidalHelper.Mor v X mor using (HomTerm)

  field ⟦box⟧ : ∀ {a b} → Mor a b → HomTerm (wires a) (wires b)

--------------------------------------------------------------------------------
-- The engine, parametric in the variant `v` and the interpretation `⟦box⟧`.
--------------------------------------------------------------------------------
module UntypedI {v : Variant} {X : Set} (E : WireEngine v {X}) where

  open WireEngine E
  open WireSig v {X} Mor public

  -- `WireSig` already re-exports the merge/split kit publicly, so hide those
  -- four names here to avoid the ambiguity of importing them twice.
  open FreeMonoidalHelper.Mor v X mor hiding (merge; split; merge∘split; split∘merge)

  -- `≈R` bundles the free-monoidal equational-reasoning combinators; it is
  -- re-exported through `UntypedI` for the consumers (`Normalize`) to open.
  module ≈R where
    open Category.HomReasoning FreeMonoidal public

  --------------------------------------------------------------------------------
  -- Diagrams: a list of layers.  Each layer is a box `f : Mor a b` placed
  -- at offset `pre`, with `suf` idle wires after it.  The diagram is
  -- indexed by both its input AND output wire-lists; consing a layer in front
  -- turns a diagram of input width `pre ++ (b ++ suf)` into one of input width
  -- `pre ++ (a ++ suf)`, leaving the output index `m` untouched.  The list is
  -- read left-to-right = bottom-to-top: the head layer is applied first.
  --------------------------------------------------------------------------------
  infixr 5 _▸_∷_⟨_⟩
  data DiagU : List X → List X → Set where
    []_     : (n : List X) → DiagU n n
    _▸_∷_⟨_⟩ : ∀ {a b m} (pre : List X) (suf : List X) (f : Mor a b)
             → DiagU (pre ++ (b ++ suf)) m → DiagU (pre ++ (a ++ suf)) m

  -- interpretation into the free monoidal category
  ⟦_⟧ : ∀ {n m} (d : DiagU n m) → HomTerm (wires n) (wires m)
  ⟦ []_ n ⟧              = id
  ⟦ pre ▸ suf ∷ f ⟨ d ⟩ ⟧ = ⟦ d ⟧ ∘ pad pre suf (⟦box⟧ f)

  -- All ⟦box⟧-free wire coherence — the `castW` object-transport algebra, the
  -- structural ++-associators `assocW`/`assocW⁻`, and the flat-shift lemmas
  -- `liftW-merge`/`pad≡liftW` — lives in WireCoh; re-export it here so the
  -- consumers see those names through `UntypedI`/`Untyped` unchanged.
  open WireCoh v X mor public

  --------------------------------------------------------------------------------
  -- Transport of a diagram along a propositional equality of an endpoint index.
  -- Pure Diagram-level `castW`-transport (no reflection engine, no DecEq): a
  -- reindexed diagram's interpretation is the original conjugated by a single
  -- `castW` on the transported side.
  --------------------------------------------------------------------------------

  -- input-side transport, ONE-cast soundness.
  substDiagU : ∀ {m n k : List X} → m ≡ n → DiagU m k → DiagU n k
  substDiagU refl d = d

  ⟦substDiagU⟧ : ∀ {m n k : List X} (e : m ≡ n) (d : DiagU m k)
    → ⟦ substDiagU e d ⟧ ∘ castW e ≈Term ⟦ d ⟧
  ⟦substDiagU⟧ refl d = idʳ
    where open ≈R

  -- codomain-side transport, mirror soundness.
  substDiagUᵒ : ∀ {n k k' : List X} → k ≡ k' → DiagU n k → DiagU n k'
  substDiagUᵒ refl d = d

  ⟦substDiagUᵒ⟧ : ∀ {n k k' : List X} (e : k ≡ k') (d : DiagU n k)
    → castW e ∘ ⟦ d ⟧ ≈Term ⟦ substDiagUᵒ e d ⟧
  ⟦substDiagUᵒ⟧ refl d = idˡ
    where open ≈R

  -- A `substDiagU` input-transport conjugates its interpretation by a single
  -- `castW` on the transported side (the re-oriented `⟦substDiagU⟧`); the
  -- reflect/normalize soundness proofs apply it wherever a re-indexing wrapper
  -- appears.
  substDiagU-conj : ∀ {m n k : List X} (e : m ≡ n) (d : DiagU m k)
                  → ⟦ substDiagU e d ⟧ ≈Term ⟦ d ⟧ ∘ castW (sym e)
  substDiagU-conj refl d = ⟺ idʳ
    where open ≈R

  --------------------------------------------------------------------------------
  -- The native syntactic step relation `_≈D_`: the reflexive-transitive
  -- congruence closure of an engine-supplied primitive-step family `Prim`.
  -- A normalizer emits `_≈D_` witnesses (a syntactic rewrite trace); the
  -- semantics enters exactly once, through `≈D-sound`.
  --
  -- The relation is DIRECTED: there is no symmetry constructor.  It is really
  -- the rewrite-reachability relation `⤳*` of the step family, and the OPEN
  -- canonicity question (do interchange-equal diagrams reach the same normal
  -- form?) is precisely CONFLUENCE of this relation — a purely syntactic
  -- property of the relation itself.  The closure is
  -- DecEq-free, so it lives here in `UntypedI` alongside the diagram type.
  --------------------------------------------------------------------------------
  module DClosure (Prim : ∀ {n k} → DiagU n k → DiagU n k → Set) where
    open ≈R

    infix 4 _≈D_
    data _≈D_ : ∀ {n k} → DiagU n k → DiagU n k → Set where
      prim   : ∀ {n k} {d d' : DiagU n k} → Prim d d' → d ≈D d'
      reflᴰ  : ∀ {n k} {d : DiagU n k} → d ≈D d
      transᴰ : ∀ {n k} {d d' d'' : DiagU n k} → d ≈D d' → d' ≈D d'' → d ≈D d''
      consᴰ  : ∀ {a b k} {pre suf : List X} {f : Mor a b}
               {rest rest' : DiagU (pre ++ (b ++ suf)) k}
             → rest ≈D rest'
             → (pre ▸ suf ∷ f ⟨ rest ⟩) ≈D (pre ▸ suf ∷ f ⟨ rest' ⟩)

    -- THE soundness result: one induction interprets a whole rewrite trace.
    ≈D-sound : (prim-sound : ∀ {n k} {d d' : DiagU n k}
                           → Prim d d' → ⟦ d ⟧ ≈Term ⟦ d' ⟧)
             → ∀ {n k} {d d' : DiagU n k} → d ≈D d' → ⟦ d ⟧ ≈Term ⟦ d' ⟧
    ≈D-sound ps (prim p)     = ps p
    ≈D-sound ps reflᴰ        = ≈-Term-refl
    ≈D-sound ps (transᴰ p q) = ≈D-sound ps p ○ ≈D-sound ps q
    ≈D-sound ps (consᴰ p)    = ≈D-sound ps p ⟩∘⟨refl

--------------------------------------------------------------------------------
-- The engine at the standard interpretation `⟦box⟧ f = var (box f)`: each
-- generator becomes an opaque wire-level generator.
--------------------------------------------------------------------------------
module Untyped (v : Variant) {X : Set} (Mor : List X → List X → Set) where

  open WireSig v {X} Mor
  open FreeMonoidalHelper.Mor v X mor

  ⟦box⟧ : ∀ {a b} → Mor a b → HomTerm (wires a) (wires b)
  ⟦box⟧ f = var (box f)

  open UntypedI (record { Mor = Mor ; ⟦box⟧ = ⟦box⟧ }) public
