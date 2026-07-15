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
open import Data.List.Properties

open import Categories.Category
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR
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

  --------------------------------------------------------------------------------
  -- `Diag` combinators
  --------------------------------------------------------------------------------

  infixr 9 _∘ᵈ_
  _∘ᵈ_ : ∀ {n m k} → Diag n m → Diag m k → Diag n k
  ([]_ _)               ∘ᵈ d₂ = d₂
  (pre ▸ suf ∷ f ⟨ d ⟩) ∘ᵈ d₂ = pre ▸ suf ∷ f ⟨ d ∘ᵈ d₂ ⟩

  -- Prefix-shift: prepend `lt` idle wires to every layer (offset pre ↦ lt++pre).
  -- Definitionally  ⟦ shiftL lt d ⟧  is  liftW lt ⟦ d ⟧  up to the associativity
  -- reindexing absorbed by `substDiag`; the output index is threaded as `lt ++ m`.
  shiftL : ∀ {n m} (lt : List X) → Diag n m → Diag (lt ++ n) (lt ++ m)
  shiftL lt ([]_ n) = []_ (lt ++ n)
  shiftL lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    substDiag (++-assoc lt pre (a ++ suf))
      ((lt ++ pre) ▸ suf ∷ f ⟨ substDiag (sym (++-assoc lt pre (b ++ suf))) (shiftL lt d) ⟩)

  reassoc++ : ∀ (p a s r : List X) → (p ++ (a ++ s)) ++ r ≡ p ++ (a ++ (s ++ r))
  reassoc++ p a s r = trans (++-assoc p (a ++ s) r) (cong (p ++_) (++-assoc a s r))

  -- Suffix-shift: append `rt` idle wires (suffix suf ↦ suf++rt).
  shiftR : ∀ {n m} (rt : List X) → Diag n m → Diag (n ++ rt) (m ++ rt)
  shiftR rt ([]_ n) = []_ (n ++ rt)
  shiftR rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    substDiag (sym (reassoc++ pre a suf rt))
      (pre ▸ (suf ++ rt) ∷ f ⟨ substDiag (reassoc++ pre b suf rt) (shiftR rt d) ⟩)

  infixr 10 _⊗ᵈ_
  _⊗ᵈ_ : ∀ {nl ml nr mr} → Diag nl ml → Diag nr mr → Diag (nl ++ nr) (ml ++ mr)
  _⊗ᵈ_ {nl} {ml} {nr} {mr} dl dr = shiftR nr dl ∘ᵈ shiftL ml dr

  -- the raw single-box layer; its endpoints carry trailing `++ []`s.
  boxLayer : ∀ {a b} → Mor a b → Diag (a ++ []) (b ++ [])
  boxLayer {a} {b} g = [] ▸ [] ∷ g ⟨ []_ (b ++ []) ⟩

  -- the single-box diagram
  boxD : ∀ {a b} → Mor a b → Diag a b
  boxD {a} {b} g = substDiag (++-identityʳ a) (substDiagᵒ (++-identityʳ b) (boxLayer g))

  --------------------------------------------------------------------------------
  -- Soundness of the pure builders: each `⟦ builder … ⟧` equals the
  -- corresponding structural composite.
  --------------------------------------------------------------------------------
  module DiagSound ⦃ _ : DecEq X ⦄ where
    open FreeMonoidalHelper v X using (_⊗₀_)
    open MR FreeMonoidal
    open MonR Monoidal-FreeMonoidal using (_⟩⊗⟨_; serialize₂₁)
    open WireCohDec

    ∘ᵈ-sound : ∀ {n m k} (d₁ : Diag n m) (d₂ : Diag m k) → ⟦ d₁ ∘ᵈ d₂ ⟧ ≈Term ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧
    ∘ᵈ-sound ([]_ _) d₂ = ⟺ idʳ
    ∘ᵈ-sound (pre ▸ suf ∷ f ⟨ d ⟩) d₂ = (∘ᵈ-sound d d₂ ⟩∘⟨refl) ○ assoc

    boxSound : ∀ {a b} (g : Mor a b) → ⟦ boxD g ⟧ ≈Term ⟦ g ⟧ᵇ
    boxSound {a} {b} g = begin
      ⟦ boxD g ⟧
        ≈⟨ ⟦substDiag⟧ (++-identityʳ a) (substDiagᵒ (++-identityʳ b) (boxLayer g)) ⟩
      ⟦ substDiagᵒ (++-identityʳ b) (boxLayer g) ⟧ ∘ castW (sym (++-identityʳ a))
        ≈⟨ ⟦substDiagᵒ⟧ (++-identityʳ b) (boxLayer g) ⟩∘⟨refl ⟩
      (castW (++-identityʳ b) ∘ ⟦ boxLayer g ⟧) ∘ castW (sym (++-identityʳ a))
        ≈⟨ (refl⟩∘⟨ idˡ) ⟩∘⟨refl ⟩
      (castW (++-identityʳ b) ∘ merge b ∘ rest) ∘ castW (sym (++-identityʳ a))
        ≈⟨ (⟺ assoc) ⟩∘⟨refl ⟩
      ((castW (++-identityʳ b) ∘ merge b) ∘ rest) ∘ castW (sym (++-identityʳ a))
        ≈⟨ assoc ⟩
      (castW (++-identityʳ b) ∘ merge b) ∘ (rest ∘ castW (sym (++-identityʳ a)))
        ≈⟨ (merge-ρ b) ⟩∘⟨ assoc ⟩
      ρ⇒ ∘ ((⟦ g ⟧ᵇ ⊗₁ id) ∘ (split a ∘ castW (sym (++-identityʳ a))))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (split-ρ a)) ⟩
      ρ⇒ ∘ ((⟦ g ⟧ᵇ ⊗₁ id) ∘ ρ⇐)
        ≈⟨ pullˡ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩
      (⟦ g ⟧ᵇ ∘ ρ⇒) ∘ ρ⇐
        ≈⟨ cancelʳ ρ⇒∘ρ⇐≈id ⟩
      ⟦ g ⟧ᵇ ∎
      where
        rest : HomTerm (wires (a ++ [])) (wires b ⊗₀ wires [])
        rest = (⟦ g ⟧ᵇ ⊗₁ id) ∘ split a

    --------------------------------------------------------------------------------
    -- Soundness of the offset shifts `shiftL` / `shiftR`.
    --------------------------------------------------------------------------------

    liftW-pad : ∀ {a b} (lt pre suf : List X) (g : HomTerm (wires a) (wires b))
              → liftW lt (pad pre suf g)
                ≈Term (castW (++-assoc lt pre (b ++ suf)) ∘ pad (lt ++ pre) suf g)
                        ∘ castW (sym (++-assoc lt pre (a ++ suf)))
    liftW-pad lt pre suf g = conj-toSandwich (liftW-fuse lt pre (rpad suf g)) ○ ⟺ assoc

    -- The output index is now `lt ++ m` structurally, so the statement is
    -- cast-free; the two `substDiag` wrappers are peeled by `⟦substDiag⟧`.
    shiftL-sound : ∀ {n m} (lt : List X) (d : Diag n m) → ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
    shiftL-sound lt ([]_ _) = ⟺ (liftW-id lt)
    shiftL-sound lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = begin
      ⟦ substDiag E1 LAYER ⟧
        ≈⟨ ⟦substDiag⟧ E1 LAYER ⟩
      (⟦ subst2 ⟧ ∘ pf) ∘ castW (sym E1)
        ≈⟨ (subst2≈ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((liftW lt ⟦ d ⟧ ∘ castW Eb) ∘ pf) ∘ castW (sym E1)
        ≈⟨ (assoc ⟩∘⟨refl) ○ assoc ⟩
      liftW lt ⟦ d ⟧ ∘ ((castW Eb ∘ pf) ∘ castW (sym E1))
        ≈⟨ refl⟩∘⟨ ⟺ (liftW-pad lt pre suf g) ⟩
      liftW lt ⟦ d ⟧ ∘ liftW lt (pad pre suf g)
        ≈⟨ ⟺ (liftW-∘ lt ⟦ d ⟧ (pad pre suf g)) ⟩
      liftW lt (⟦ d ⟧ ∘ pad pre suf g) ∎
      where
        g  = ⟦ f ⟧ᵇ
        Eb = ++-assoc lt pre (b ++ suf)
        E1 = ++-assoc lt pre (a ++ suf)
        E2 = sym Eb
        d' = shiftL lt d
        subst2 = substDiag E2 d'
        pf = pad (lt ++ pre) suf g
        LAYER = (lt ++ pre) ▸ suf ∷ f ⟨ subst2 ⟩
        -- the inner shift folds through its `substDiag` to `liftW lt ⟦d⟧`.
        subst2≈ : ⟦ subst2 ⟧ ≈Term liftW lt ⟦ d ⟧ ∘ castW Eb
        subst2≈ = ⟦substDiag⟧ E2 d' ○ (shiftL-sound lt d ⟩∘⟨ castW-irr (sym E2) Eb)

    -- rpad / pad relation (suffix analogue of `liftW-pad`): a conjugation chain
    -- over the bi-action laws, all at `R = rpad suf g`.  `rpad-liftW rt pre R`
    -- slides the outer `rpad rt` past the `pad pre suf g = liftW pre R` prefix;
    -- `liftW-conj pre (rpad-rpad suf rt g)` fuses the two suffix pads underneath;
    -- `conj-irr` bridges the composite cast indices to the `reassoc++` forms.
    rpad-pad : ∀ {a b} (pre suf rt : List X) (g : HomTerm (wires a) (wires b))
               → rpad rt (pad pre suf g)
                 ≈Term (castW (sym (reassoc++ pre b suf rt)) ∘ pad pre (suf ++ rt) g)
                         ∘ castW (reassoc++ pre a suf rt)
    rpad-pad pre suf rt g =
      conj-toSandwich
        (conj-irr (conj-trans (rpad-liftW rt pre R) (liftW-conj pre (rpad-rpad suf rt g))))
        ○ ⟺ assoc
      where R = rpad suf g

    shiftR-sound : ∀ {n m} (rt : List X) (d : Diag n m) → ⟦ shiftR rt d ⟧ ≈Term rpad rt ⟦ d ⟧
    shiftR-sound rt ([]_ _) = ⟺ (rpad-id rt)
    shiftR-sound rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = begin
      ⟦ substDiag (sym E1) LAYER ⟧
        ≈⟨ ⟦substDiag⟧ (sym E1) LAYER ⟩
      (⟦ subst2 ⟧ ∘ padR) ∘ castW (sym (sym E1))
        ≈⟨ refl⟩∘⟨ castW-irr (sym (sym E1)) E1 ⟩
      (⟦ subst2 ⟧ ∘ padR) ∘ castW E1
        ≈⟨ (subst2≈ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((rpad rt ⟦ d ⟧ ∘ castW (sym E2)) ∘ padR) ∘ castW E1
        ≈⟨ (assoc ⟩∘⟨refl) ○ assoc ⟩
      rpad rt ⟦ d ⟧ ∘ ((castW (sym E2) ∘ padR) ∘ castW E1)
        ≈⟨ refl⟩∘⟨ ⟺ (rpad-pad pre suf rt g) ⟩
      rpad rt ⟦ d ⟧ ∘ rpad rt (pad pre suf g)
        ≈⟨ ⟺ (rpad-∘ rt ⟦ d ⟧ (pad pre suf g)) ⟩
      rpad rt (⟦ d ⟧ ∘ pad pre suf g) ∎
      where
        g  = ⟦ f ⟧ᵇ
        E1 = reassoc++ pre a suf rt
        E2 = reassoc++ pre b suf rt
        d' = shiftR rt d
        subst2 = substDiag E2 d'
        padR = pad pre (suf ++ rt) g
        LAYER = pre ▸ (suf ++ rt) ∷ f ⟨ subst2 ⟩
        -- the inner shift folds through its `substDiag` to `rpad rt ⟦d⟧`.
        subst2≈ : ⟦ subst2 ⟧ ≈Term rpad rt ⟦ d ⟧ ∘ castW (sym E2)
        subst2≈ = ⟦substDiag⟧ E2 d' ○ (shiftR-sound rt d ⟩∘⟨refl)

    ⊗ᵈ-sound : ∀ {nl ml nr mr} (dl : Diag nl ml) (dr : Diag nr mr)
             → ⟦ dl ⊗ᵈ dr ⟧ ≈Term merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl
    ⊗ᵈ-sound {nl} {ml} {nr} {mr} dl dr = begin
      ⟦ shiftR nr dl ∘ᵈ shiftL ml dr ⟧
        ≈⟨ ∘ᵈ-sound (shiftR nr dl) (shiftL ml dr) ⟩
      ⟦ shiftL ml dr ⟧ ∘ ⟦ shiftR nr dl ⟧
        ≈⟨ shiftL-sound ml dr ⟩∘⟨ shiftR-sound nr dl ⟩
      liftW ml ⟦ dr ⟧ ∘ rpad nr ⟦ dl ⟧
        ≈⟨ liftW-merge ml ⟦ dr ⟧ ⟩∘⟨refl ⟩
      (merge ml ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split ml)
        ∘ (merge ml ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
        ≈⟨ collapse ⟩
      merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl ∎
      where
        -- the central bifunctoriality collapse.
        collapse : (merge ml ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split ml) ∘ (merge ml ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
                   ≈Term merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl
        collapse = begin
          (merge ml ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split ml) ∘ (merge ml ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
            ≈⟨ center (cancelʳ (split∘merge ml)) ⟩
          merge ml ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ ((⟦ dl ⟧ ⊗₁ id) ∘ split nl))
            ≈⟨ refl⟩∘⟨ pullˡ (⟺ serialize₂₁) ⟩
          merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl ∎

stdEngine : (v : Variant) {X : Set} (Mor : List X → List X → Set) → WireEngine v
stdEngine v {X} Mor = record { Mor = Mor ; ⟦_⟧ᵇ = var ∘′ box }
  where
    open WireSig v {X} Mor
    open FreeMonoidalHelper.Mor v X mor
