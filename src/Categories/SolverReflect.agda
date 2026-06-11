{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A reflection  HomTerm → DiagU  with soundness, for the untyped free
-- monoidal diagram normal form of `Categories.DiagramRewriteUntyped`.
--
-- We work in the layered-composite wire fragment (M1): morphisms whose
-- source and target are already `wires`-shaped flat objects, built from
--   id, _∘_, var (box _), _⊗₁_,
-- captured by the inductive `WTerm n m` with embedding
-- `embed : WTerm n m → HomTerm (wires n) (wires m)`.  We define, all under
-- `--safe` and fully postulate-free / hole-free:
--   * `_∘ᵈ_`        : sequential composition (append) of diagrams, with
--                     soundness `∘ᵈ-sound : ⟦ d₁ ∘ᵈ d₂ ⟧ ≈ ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧`
--                     (codomain reindexed).  This is the `_∘_` case.
--   * `shiftL` / `shiftR` : prefix / suffix idle-wire shifts on diagrams
--                     (the offset-bookkeeping building blocks for `tensorD`),
--                     with their `out` computed and soundness proven
--                     (`shiftL-sound` / `shiftR-sound`).
--   * `tensorD`     : horizontal tensor of diagrams (the `_⊗₁_` case), with
--                     `out-tensorD` and `tensorD-sound`.
--   * `reflect`     : WTerm n m → DiagU n  with `out-reflect : out (reflect t) ≡ m`.
--   * `reflect-sound`: ⟦ reflect t ⟧ ≈ embed t (codomain reindexed), proven by
--                     induction on all four constructors.  The single box-leaf
--                     right-unitor coherence (`merge a {[]} ≈ ρ⇒`) is isolated
--                     as the statement `BoxSound` and discharged in-file by
--                     `boxSound` (a Kelly unit-coherence derivation), which
--                     `reflect-sound` uses directly.
--------------------------------------------------------------------------------

module Categories.SolverReflect where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ≡-dec)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

import Categories.Category.Monoidal.Properties as MonProps
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.DiagramRewriteUntyped
open import Categories.FreeMonoidal

module ReflectI (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
                (Mor : List X → List X → Set)
                (let open WireSig v {X} Mor using () renaming (wires to wires↑; mor to mor↑))
                (let open FreeMonoidalHelper.Mor v X mor↑ using () renaming (HomTerm to HomTerm↑))
                (⟦box⟧ : ∀ {a b} → Mor a b → HomTerm↑ (wires↑ a) (wires↑ b)) where

  -- UIP on the wire lists, via Hedberg (decidable equality), --without-K.
  private
    ≡-irrelevant : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevant = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)

  open UntypedI v {X} Mor ⟦box⟧
  open FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor v X mor
  open ≈R

  -- stock associativity/cancellation combinators (same idiom as
  -- DiagramRewriteUntyped): plain non-public opens, proofs-only.
  open MR FreeMonoidal
    using (pullˡ; pullʳ; center; center⁻¹;
           cancelˡ; cancelʳ; cancelInner; introʳ)
  open MonR Monoidal-FreeMonoidal
    using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; serialize₁₂; serialize₂₁; split₁ʳ)

  -- Mac Lane / Kelly unit coherence laws, instantiated at the *free* monoidal
  -- category over `mor`.  Its `_≈_`/`α⇒`/`ρ⇒`/`_⊗₁_` coincide definitionally
  -- with our `_≈Term_`/α⇒/ρ⇒/_⊗₁_, so these land as `≈Term` equalities.
  module K = MonProps.Kelly's Monoidal-FreeMonoidal

  -- coherence₃ : λ⇒ ≈Term ρ⇒  at  unit ⊗₀ unit
  λ⇒≈ρ⇒ : λ⇒ {unit} ≈Term ρ⇒ {unit}
  λ⇒≈ρ⇒ = K.coherence₃

  -- coherence₂ : id ⊗₁ ρ⇒ ∘ α⇒ ≈Term ρ⇒  at  (X ⊗₀ Y) ⊗₀ unit
  idρ∘α≈ρ : ∀ {A B} → id {A} ⊗₁ ρ⇒ {B} ∘ α⇒ ≈Term ρ⇒
  idρ∘α≈ρ = K.coherence₂

  -- coherence-inv₃ : λ⇐ ≈Term ρ⇐  at  unit
  λ⇐≈ρ⇐ : λ⇐ {unit} ≈Term ρ⇐ {unit}
  λ⇐≈ρ⇐ = K.coherence-inv₃

  -- coherence-inv₂ : α⇐ ∘ id ⊗₁ ρ⇐ ≈Term ρ⇐  (inverse of coherence₂)
  α⇐∘idρ⇐≈ρ⇐ : ∀ {A B} → α⇐ ∘ id {A} ⊗₁ ρ⇐ {B} ≈Term ρ⇐
  α⇐∘idρ⇐≈ρ⇐ = K.coherence-inv₂

  -- coherence₁ : λ⇒ ∘ α⇒ ≈Term λ⇒ ⊗₁ id  at  (unit ⊗₀ A) ⊗₀ B
  λ⇒∘α⇒≈λ⇒⊗id : ∀ {A B} → λ⇒ {A ⊗₀ B} ∘ α⇒ {unit} {A} {B} ≈Term λ⇒ ⊗₁ id
  λ⇒∘α⇒≈λ⇒⊗id = K.coherence₁

  --------------------------------------------------------------------------------
  -- M1 fragment: the wire-typed terms.
  --------------------------------------------------------------------------------
  infixr 9 _∘ʷ_
  infixr 10 _⊗ʷ_
  data WTerm : List X → List X → Set where
    boxʷ : ∀ {a b} → Mor a b → WTerm a b
    idʷ  : ∀ {n} → WTerm n n
    _∘ʷ_ : ∀ {n m k} → WTerm m k → WTerm n m → WTerm n k
    _⊗ʷ_ : ∀ {nl ml nr mr} → WTerm nl ml → WTerm nr mr → WTerm (nl ++ nr) (ml ++ mr)

  embed : ∀ {n m} → WTerm n m → HomTerm (wires n) (wires m)
  embed (boxʷ g)  = ⟦box⟧ g
  embed idʷ       = id
  embed (g ∘ʷ f)  = embed g ∘ embed f
  -- the wire-grouping bridge `merge ∘ (— ⊗₁ —) ∘ split` makes the tensor of two
  -- flat morphisms flat again.
  embed (_⊗ʷ_ {nl} {ml} {nr} {mr} s t) =
    merge ml {mr} ∘ (embed s ⊗₁ embed t) ∘ split nl {nr}

  --------------------------------------------------------------------------------
  -- Combinator 1:  sequential composition / append of diagrams.
  --
  -- Recursion on the first-applied diagram d₁ : DiagU m.  We cons each of
  -- its layers, then attach d₂ : DiagU (out d₁) at the empty tail.  The
  -- result is a DiagU m whose output is out d₂.
  --------------------------------------------------------------------------------
  infixr 9 _∘ᵈ_
  _∘ᵈ_ : ∀ {m} (d₁ : DiagU m) → DiagU (out d₁) → DiagU m
  ([]_ m)               ∘ᵈ d₂ = d₂
  (pre ▸ suf ∷ f ⟨ d ⟩) ∘ᵈ d₂ = pre ▸ suf ∷ f ⟨ d ∘ᵈ d₂ ⟩

  out-∘ᵈ : ∀ {m} (d₁ : DiagU m) (d₂ : DiagU (out d₁)) → out (d₁ ∘ᵈ d₂) ≡ out d₂
  out-∘ᵈ ([]_ m)               d₂ = refl
  out-∘ᵈ (pre ▸ suf ∷ f ⟨ d ⟩) d₂ = out-∘ᵈ d d₂

  --------------------------------------------------------------------------------
  -- The coercion vocabulary: retype a HomTerm along a propositional equality
  -- of its codomain (`coeC`) / domain (`coeD`) wire list.  The other end is
  -- an ARBITRARY object (the merge/split steps below need bracketed tensors
  -- of wires, not flat ones), so these two cover every coercion in the file.
  --------------------------------------------------------------------------------
  coeC : ∀ {A} {p q : List X} → p ≡ q → HomTerm A (wires p) → HomTerm A (wires q)
  coeC refl h = h

  coeD : ∀ {B} {p q : List X} → p ≡ q → HomTerm (wires p) B → HomTerm (wires q) B
  coeD refl h = h

  -- congruence.
  coeC-resp : ∀ {A p q} (e : p ≡ q) {h h' : HomTerm A (wires p)}
            → h ≈Term h' → coeC e h ≈Term coeC e h'
  coeC-resp refl eq = eq

  coeD-resp : ∀ {B p q} (e : p ≡ q) {h h' : HomTerm (wires p) B}
            → h ≈Term h' → coeD e h ≈Term coeD e h'
  coeD-resp refl eq = eq

  -- recast along a propositionally-equal index (UIP on the wire lists).
  coeC-castU : ∀ {A p q} (e e' : p ≡ q) (h : HomTerm A (wires p))
             → coeC e h ≈Term coeC e' h
  coeC-castU e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl

  coeD-castU : ∀ {B p q} (e e' : p ≡ q) (h : HomTerm (wires p) B)
             → coeD e h ≈Term coeD e' h
  coeD-castU e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl

  -- collapse two stacked coercions.
  coeC-trans : ∀ {A p q s} (e1 : p ≡ q) (e2 : q ≡ s) (h : HomTerm A (wires p))
             → coeC e2 (coeC e1 h) ≈Term coeC (trans e1 e2) h
  coeC-trans refl refl h = ≈-Term-refl

  coeD-trans : ∀ {B p q s} (e1 : p ≡ q) (e2 : q ≡ s) (h : HomTerm (wires p) B)
             → coeD e2 (coeD e1 h) ≈Term coeD (trans e1 e2) h
  coeD-trans refl refl h = ≈-Term-refl

  -- coeC and coeD commute (independent ends).
  coe-comm : ∀ {p q p' q'} (e1 : p' ≡ q') (e2 : p ≡ q) (h : HomTerm (wires p') (wires p))
           → coeC e2 (coeD e1 h) ≈Term coeD e1 (coeC e2 h)
  coe-comm refl refl h = ≈-Term-refl

  -- push coeC through `∘` onto the left (codomain) factor.
  coeC-∘ˡ : ∀ {A R p q} (e : p ≡ q) (h : HomTerm R (wires p)) (j : HomTerm A R)
          → coeC e (h ∘ j) ≈Term coeC e h ∘ j
  coeC-∘ˡ refl h j = ≈-Term-refl

  -- push coeD through `∘` onto the right (domain) factor.
  coeD-∘ʳ : ∀ {B R p q} (e : p ≡ q) (h : HomTerm R B) (j : HomTerm (wires p) R)
          → coeD e (h ∘ j) ≈Term h ∘ coeD e j
  coeD-∘ʳ refl h j = ≈-Term-refl

  -- retype the middle object of a composite (the two transports cancel).
  mid-retype : ∀ {A B p q} (e : p ≡ q) (h : HomTerm (wires p) B) (j : HomTerm A (wires p))
             → h ∘ j ≈Term coeD e h ∘ coeC e j
  mid-retype refl h j = ≈-Term-refl

  -- push a coercion along `cong (x ∷_)` under the prefix `id {Var x} ⊗₁ _`.
  coeC-id⊗ : ∀ {R} (x : X) {p q : List X} (e : p ≡ q) (h : HomTerm R (wires p))
           → coeC (cong (x ∷_) e) (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ coeC e h
  coeC-id⊗ x refl h = ≈-Term-refl

  coeD-id⊗ : ∀ {R} (x : X) {p q : List X} (e : p ≡ q) (h : HomTerm (wires p) R)
           → coeD (cong (x ∷_) e) (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ coeD e h
  coeD-id⊗ x refl h = ≈-Term-refl

  -- invert a coercion equation:  h ≈ coe eq k  ⇒  coe (sym eq) h ≈ k.
  coeC-invert : ∀ {A p q} (eq : p ≡ q) (h : HomTerm A (wires q)) (k : HomTerm A (wires p))
              → h ≈Term coeC eq k → coeC (sym eq) h ≈Term k
  coeC-invert refl h k e = e

  coeD-invert : ∀ {B p q} (eq : p ≡ q) (h : HomTerm (wires q) B) (k : HomTerm (wires p) B)
              → h ≈Term coeD eq k → coeD (sym eq) h ≈Term k
  coeD-invert refl h k e = e

  -- Soundness of append:  ⟦ d₁ ∘ᵈ d₂ ⟧ ≈ ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧ (codomain coerced).
  ∘ᵈ-sound : ∀ {m} (d₁ : DiagU m) (d₂ : DiagU (out d₁))
           → coeC (out-∘ᵈ d₁ d₂) ⟦ d₁ ∘ᵈ d₂ ⟧ ≈Term ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧
  ∘ᵈ-sound ([]_ m) d₂ = ⟺ idʳ
  ∘ᵈ-sound (pre ▸ suf ∷ f ⟨ d ⟩) d₂ = begin
    coeC (out-∘ᵈ d d₂) (⟦ d ∘ᵈ d₂ ⟧ ∘ pad pre suf (⟦box⟧ f))
      ≈⟨ coeC-∘ˡ (out-∘ᵈ d d₂) ⟦ d ∘ᵈ d₂ ⟧ (pad pre suf (⟦box⟧ f)) ⟩
    coeC (out-∘ᵈ d d₂) ⟦ d ∘ᵈ d₂ ⟧ ∘ pad pre suf (⟦box⟧ f)
      ≈⟨ (∘ᵈ-sound d d₂) ⟩∘⟨refl ⟩
    (⟦ d₂ ⟧ ∘ ⟦ d ⟧) ∘ pad pre suf (⟦box⟧ f)
      ≈⟨ assoc ⟩
    ⟦ d₂ ⟧ ∘ (⟦ d ⟧ ∘ pad pre suf (⟦box⟧ f)) ∎

  --------------------------------------------------------------------------------
  -- Reindexing a diagram along a propositional equality of its input index.
  -- For `refl` it is the identity, and `⟦_⟧` transports definitionally.
  --------------------------------------------------------------------------------
  reidx : ∀ {n n'} → n ≡ n' → DiagU n → DiagU n'
  reidx refl d = d

  out-reidx : ∀ {n n'} (eq : n ≡ n') (d : DiagU n) → out (reidx eq d) ≡ out d
  out-reidx refl d = refl

  -- transport lemma: reindexing only retypes the interpretation via the coes.
  ⟦reidx⟧ : ∀ {n n'} (eq : n ≡ n') (d : DiagU n)
          → ⟦ reidx eq d ⟧ ≈Term coeD eq (coeC (sym (out-reidx eq d)) ⟦ d ⟧)
  ⟦reidx⟧ refl d = ≈-Term-refl

  --------------------------------------------------------------------------------
  -- Generic coe-transport folds.  The soundness proofs below repeatedly
  -- shuffle stacked coeC/coeD coercions around a `reidx` (or an already-
  -- proven coeC equation); each such shuffle is one of the three shapes
  -- here, proven once by matching the reidx equality to refl and
  -- discharging the residual loop equalities by UIP (`≡-irrelevant`).
  --------------------------------------------------------------------------------

  -- fold shape: the outer coeD undoes the reidx, leaving a single codomain
  -- retype of the un-reindexed diagram.
  fold-reidx : ∀ {p q r} (E : p ≡ q) (M : q ≡ p) (d : DiagU p)
               (B : out (reidx E d) ≡ r) (T : out d ≡ r)
             → coeD M (coeC B ⟦ reidx E d ⟧) ≈Term coeC T ⟦ d ⟧
  fold-reidx refl M d B T rewrite ≡-irrelevant M refl | ≡-irrelevant B T = ≈-Term-refl

  -- expand shape: push the codomain retype of a reidx'd diagram inside,
  -- exposing the reidx equality as a domain coercion.
  reidx-expand : ∀ {p q r} (E : p ≡ q) (L : DiagU p)
                 (O : out (reidx E L) ≡ r) (B : out L ≡ r)
               → coeC O ⟦ reidx E L ⟧ ≈Term coeD E (coeC B ⟦ L ⟧)
  reidx-expand refl L O B rewrite ≡-irrelevant O B = ≈-Term-refl

  -- re-route a codomain coercion through an already-proven coeC equation
  -- (the call prefix of the `∘ᵈ-sound` / `tensorD-sound` consumers).
  coeC-fold : ∀ {A p q r} (E : p ≡ q) (B : q ≡ r) (O : p ≡ r)
              {h : HomTerm A (wires p)} {k : HomTerm A (wires q)}
            → coeC E h ≈Term k → coeC O h ≈Term coeC B k
  coeC-fold refl refl O eq rewrite ≡-irrelevant O refl = eq

  --------------------------------------------------------------------------------
  -- Combinator 2:  horizontal tensor of diagrams.
  --
  -- We build the tensor as  (left factor padded with `l` idle suffix wires)
  --                  ∘ᵈ    (right factor padded with `n` idle prefix wires),
  -- mirroring  Ef ⊗₁ Eg = (Ef ⊗₁ id) ∘ (id ⊗₁ Eg).  Each padding is a
  -- per-layer offset shift on the diagram.
  --------------------------------------------------------------------------------

  -- Prefix-shift: prepend `lt` idle wires to every layer (offset pre ↦ lt++pre).
  -- Definitionally  ⟦ shiftL lt d ⟧  is  liftW lt ⟦ d ⟧  up to the associativity
  -- reindexing absorbed by `reidx`.
  shiftL : ∀ {n} (lt : List X) → DiagU n → DiagU (lt ++ n)
  shiftL lt ([]_ n) = []_ (lt ++ n)
  shiftL {._} lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    reidx (++-assoc lt pre (a ++ suf))
      ((lt ++ pre) ▸ suf ∷ f ⟨ reidx (sym (++-assoc lt pre (b ++ suf))) (shiftL lt d) ⟩)

  -- Suffix-shift: append `rt` idle wires (suffix suf ↦ suf++rt).

  -- associativity:  (p ++ (a ++ s)) ++ r  ≡  p ++ (a ++ (s ++ r))
  reassoc++ : ∀ (p a s r : List X) → (p ++ (a ++ s)) ++ r ≡ p ++ (a ++ (s ++ r))
  reassoc++ p a s r = trans (++-assoc p (a ++ s) r) (cong (p ++_) (++-assoc a s r))

  shiftR : ∀ {n} (rt : List X) → DiagU n → DiagU (n ++ rt)
  shiftR rt ([]_ n) = []_ (n ++ rt)
  shiftR {._} rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    reidx (sym (reassoc++ pre a suf rt))
      (pre ▸ (suf ++ rt) ∷ f ⟨ reidx (reassoc++ pre b suf rt) (shiftR rt d) ⟩)

  --------------------------------------------------------------------------------
  -- out of the shifts.
  --------------------------------------------------------------------------------
  out-shiftL : ∀ {n} (lt : List X) (d : DiagU n) → out (shiftL lt d) ≡ lt ++ out d
  out-shiftL lt ([]_ n) = refl
  out-shiftL lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    trans (out-reidx (++-assoc lt pre (a ++ suf)) _)
          (trans (out-reidx (sym (++-assoc lt pre (b ++ suf))) (shiftL lt d))
                 (out-shiftL lt d))

  out-shiftR : ∀ {n} (rt : List X) (d : DiagU n) → out (shiftR rt d) ≡ out d ++ rt
  out-shiftR rt ([]_ n) = refl
  out-shiftR rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    trans (out-reidx (sym (reassoc++ pre a suf rt)) _)
          (trans (out-reidx (reassoc++ pre b suf rt) (shiftR rt d))
                 (out-shiftR rt d))

  --------------------------------------------------------------------------------
  -- Horizontal tensor of diagrams (the `_⊗₁_` combinator).
  --
  --   tensorD dl dr  places `dl`'s layers in the left wire-block (suffix-padded
  --   by the right input wires `nr` via `shiftR`) and `dr`'s layers in the
  --   right block (prefix-padded by the left OUTPUT wires `out dl` via
  --   `shiftL`), composed sequentially.  Result lives over `nl ++ nr` with
  --   output `out dl ++ out dr`.
  --------------------------------------------------------------------------------
  tensorD : ∀ {nl nr} (dl : DiagU nl) (dr : DiagU nr) → DiagU (nl ++ nr)
  tensorD {nl} {nr} dl dr =
    shiftR nr dl ∘ᵈ reidx (sym (out-shiftR nr dl)) (shiftL (out dl) dr)

  out-tensorD : ∀ {nl nr} (dl : DiagU nl) (dr : DiagU nr)
              → out (tensorD dl dr) ≡ out dl ++ out dr
  out-tensorD {nl} {nr} dl dr =
    trans (out-∘ᵈ (shiftR nr dl) (reidx (sym (out-shiftR nr dl)) (shiftL (out dl) dr)))
          (trans (out-reidx (sym (out-shiftR nr dl)) (shiftL (out dl) dr))
                 (out-shiftL (out dl) dr))

  --------------------------------------------------------------------------------
  -- Reflection of the wire fragment into DiagU (M1).
  --
  --   id     →  empty diagram      [] _
  --   g ∘ f  →  reflect f ∘ᵈ reflect g   (f applied first)
  --   box g  →  single-box layer (see `boxD` below)
  --
  -- Soundness:  ⟦ reflect t ⟧ ≈Term embed t  (up to the structural ++[] reindex
  -- on the box leaf).  The id / ∘ cases are discharged purely by `∘ᵈ-sound`.
  --
  -- The single box `g : Mor a b` is placed with empty offsets; its layer has
  -- domain index  [] ++ (a ++ [])  =  a ++ []  (note the trailing []), so the
  -- leaf carries a `++-identityʳ` reindex.  The remaining right-unitor
  -- coherence on this leaf is discharged below by `boxSound`.
  --------------------------------------------------------------------------------

  -- single-box diagram, living over  a ++ []  (trailing idle empty suffix).
  boxD : ∀ {a b} → Mor a b → DiagU (a ++ [])
  boxD {a} {b} g = [] ▸ [] ∷ g ⟨ []_ (b ++ []) ⟩

  out-boxD : ∀ {a b} (g : Mor a b) → out (boxD g) ≡ b ++ []
  out-boxD g = refl

  --------------------------------------------------------------------------------
  -- reflect on the id / ∘ fragment.  We track `out` definitionally by
  -- recursing so that the composite's output is exactly the source's.  The
  -- composition case feeds `reflect g : DiagU m` into the tail of
  -- `reflect f : DiagU n`, which requires `out (reflect f) ≡ m`; we make this
  -- definitional by carrying the output as the diagram index everywhere.
  --------------------------------------------------------------------------------
  -- output of reflect, computed structurally (id ↦ n, ∘ ↦ output of g).
  reflect : ∀ {n m} → WTerm n m → DiagU n
  out-reflect : ∀ {n m} (t : WTerm n m) → out (reflect t) ≡ m

  reflect idʷ        = []_ _
  reflect (g ∘ʷ f)   = reflect f ∘ᵈ reidx (sym (out-reflect f)) (reflect g)
  reflect (boxʷ g)   = reidx (++-identityʳ _) (boxD g)
  reflect (s ⊗ʷ t)   = tensorD (reflect s) (reflect t)

  out-reflect idʷ        = refl
  out-reflect (g ∘ʷ f)   =
    trans (out-∘ᵈ (reflect f) (reidx (sym (out-reflect f)) (reflect g)))
          (trans (out-reidx (sym (out-reflect f)) (reflect g)) (out-reflect g))
  out-reflect (boxʷ {a} {b} g) =
    trans (out-reidx (++-identityʳ a) (boxD g))
          (trans (out-boxD g) (++-identityʳ b))
  out-reflect (_⊗ʷ_ {nl} {ml} {nr} {mr} s t) =
    trans (out-tensorD (reflect s) (reflect t))
          (cong₂ _++_ (out-reflect s) (out-reflect t))

  --------------------------------------------------------------------------------
  -- Box-leaf soundness:  ⟦ boxD g ⟧, transported across the structural
  --   a ++ [] ≡ a   and   b ++ [] ≡ b   reindices, equals ⟦box⟧ g.
  --
  -- ⟦ boxD g ⟧ = id ∘ rpad [] (⟦box⟧ g)
  --            = id ∘ (merge b {[]} ∘ (⟦box⟧ g ⊗₁ id{unit}) ∘ split a {[]}).
  -- The empty-suffix merge/split are the (transported) right-unitor iso, so
  -- this collapses to ⟦box⟧ g.  This last collapse is the pure right-unitor
  -- coherence  merge a {[]} ≈ ρ⇒  (up to a++[]≡a).  We isolate it as the
  -- SINGLE obligation `BoxSound`, discharged below by `boxSound`.
  --------------------------------------------------------------------------------
  -- Box-leaf soundness obligation, isolated as a hypothesis: it is the pure
  -- right-unitor coherence  merge a {[]} ≈ ρ⇒  up to a++[]≡a — box-free
  -- coherence, and so independent of the reflection logic below.  It is
  -- discharged in-file by `boxSound` via an explicit Kelly derivation.
  BoxSound : Set
  BoxSound = ∀ {a b} (g : Mor a b)
           → coeD (++-identityʳ a) (coeC (++-identityʳ b) ⟦ boxD g ⟧)
             ≈Term ⟦box⟧ g

  --------------------------------------------------------------------------------
  -- TASK A: discharge `BoxSound`.
  --
  -- The single obligation is the right-unitor coherence  merge a {[]} ≈ ρ⇒
  -- (and its inverse  split a {[]} ≈ ρ⇐), both up to the structural a++[]≡a
  -- reindex.  We prove these by induction on `a`, bottoming out in the two
  -- Mac Lane / Kelly unit coherence laws (`λ⇒≈ρ⇒` = coherence₃ and
  -- `idρ∘α≈ρ` = coherence₂) imported above.  `boxSound` then collapses the
  -- box-leaf conjugation  ρ⇒ ∘ (g ⊗₁ id) ∘ ρ⇐  to  ⟦box⟧ g  by right-unitor
  -- naturality.  No new postulates / holes.
  --------------------------------------------------------------------------------

  -- the right-unitor coherence on the flat merge:  merge a {[]} ≈ ρ⇒ (retyped).
  merge-ρ : (a : List X) → coeC {wires a ⊗₀ unit} (++-identityʳ a) (merge a {[]})
                          ≈Term ρ⇒ {wires a}
  merge-ρ []      = λ⇒≈ρ⇒
  merge-ρ (x ∷ a) = begin
    coeC (++-identityʳ (x ∷ a)) (id {Var x} ⊗₁ merge a ∘ α⇒)
      ≈⟨ coeC-∘ˡ (cong (x ∷_) (++-identityʳ a)) (id ⊗₁ merge a) α⇒ ⟩
    coeC (cong (x ∷_) (++-identityʳ a)) (id {Var x} ⊗₁ merge a) ∘ α⇒
      ≈⟨ (coeC-id⊗ x (++-identityʳ a) (merge a)) ⟩∘⟨refl ⟩
    id {Var x} ⊗₁ coeC (++-identityʳ a) (merge a) ∘ α⇒
      ≈⟨ (refl⟩⊗⟨ (merge-ρ a)) ⟩∘⟨refl ⟩
    id {Var x} ⊗₁ ρ⇒ {wires a} ∘ α⇒
      ≈⟨ idρ∘α≈ρ ⟩
    ρ⇒ ∎

  -- the right-unitor coherence on the flat split:  split a {[]} ≈ ρ⇐ (retyped).
  split-ρ : (a : List X) → coeD {wires a ⊗₀ unit} (++-identityʳ a) (split a {[]})
                          ≈Term ρ⇐ {wires a}
  split-ρ []      = λ⇐≈ρ⇐
  split-ρ (x ∷ a) = begin
    coeD (++-identityʳ (x ∷ a)) (α⇐ ∘ id {Var x} ⊗₁ split a)
      ≈⟨ coeD-∘ʳ (cong (x ∷_) (++-identityʳ a)) α⇐ (id ⊗₁ split a) ⟩
    α⇐ ∘ coeD (cong (x ∷_) (++-identityʳ a)) (id {Var x} ⊗₁ split a)
      ≈⟨ refl⟩∘⟨ (coeD-id⊗ x (++-identityʳ a) (split a)) ⟩
    α⇐ ∘ id {Var x} ⊗₁ coeD (++-identityʳ a) (split a)
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ (split-ρ a)) ⟩
    α⇐ ∘ id {Var x} ⊗₁ ρ⇐ {wires a}
      ≈⟨ α⇐∘idρ⇐≈ρ⇐ ⟩
    ρ⇐ ∎
  --------------------------------------------------------------------------------
  -- `boxSound : BoxSound`.  The box-leaf right-unitor coherence, discharged.
  --
  --   ⟦ boxD g ⟧ = id ∘ (merge b {[]} ∘ (⟦box⟧ g ⊗₁ id) ∘ split a {[]})
  -- and the two structural coercions reduce merge b {[]} / split a {[]} to
  -- ρ⇒ / ρ⇐ (by `merge-ρ` / `split-ρ`); the conjugation
  --   ρ⇒ ∘ (⟦box⟧ g ⊗₁ id) ∘ ρ⇐  ≈  ⟦box⟧ g
  -- collapses by right-unitor naturality `ρ⇒∘f⊗id≈f∘ρ⇒` and `ρ⇒∘ρ⇐≈id`.
  --------------------------------------------------------------------------------

  boxSound : BoxSound
  boxSound {a} {b} g = begin
    coeD (++-identityʳ a) (coeC (++-identityʳ b) ⟦ boxD g ⟧)
      ≈⟨ coeD-resp (++-identityʳ a) (coeC-resp (++-identityʳ b) idˡ) ⟩
    coeD (++-identityʳ a) (coeC (++-identityʳ b) body)
      ≈⟨ coeD-resp (++-identityʳ a) (coeC-∘ˡ (++-identityʳ b) (merge b) rest) ⟩
    coeD (++-identityʳ a) (coeC (++-identityʳ b) (merge b {[]}) ∘ rest)
      ≈⟨ coeD-∘ʳ (++-identityʳ a) (coeC (++-identityʳ b) (merge b {[]})) rest ⟩
    coeC (++-identityʳ b) (merge b {[]}) ∘ coeD (++-identityʳ a) rest
      ≈⟨ (merge-ρ b) ⟩∘⟨ (coeD-∘ʳ (++-identityʳ a) (⟦box⟧ g ⊗₁ id) (split a {[]})) ⟩
    ρ⇒ ∘ ((⟦box⟧ g ⊗₁ id) ∘ coeD (++-identityʳ a) (split a {[]}))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (split-ρ a)) ⟩
    ρ⇒ ∘ ((⟦box⟧ g ⊗₁ id) ∘ ρ⇐)
      ≈⟨ pullˡ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩
    (⟦box⟧ g ∘ ρ⇒) ∘ ρ⇐
      ≈⟨ cancelʳ ρ⇒∘ρ⇐≈id ⟩
    ⟦box⟧ g ∎
    where
      rest : HomTerm (wires (a ++ [])) (wires b ⊗₀ wires [])
      rest = (⟦box⟧ g ⊗₁ id {wires []}) ∘ split a {[]}
      body : HomTerm (wires (a ++ [])) (wires (b ++ []))
      body = merge b {[]} ∘ rest

  --------------------------------------------------------------------------------
  -- TASK 1: soundness of the offset shifts `shiftL` / `shiftR`.
  --
  --   shiftL lt d  is  liftW lt ⟦ d ⟧  up to the +-associativity reindexing
  --   absorbed by the `reidx` wrappers, and analogously for `shiftR`.  We state
  --   them in the codomain-reindexed form (mirroring `∘ᵈ-sound`):
  --     coeC (out-shiftL lt d) ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
  --     coeC (out-shiftR rt d) ⟦ shiftR rt d ⟧ ≈Term rpad rt ⟦ d ⟧
  --   where `rpad` is the suffix flat-shift (from DiagramRewriteUntyped).
  --------------------------------------------------------------------------------

  -- (`liftW-id` now lives in UntypedI; available via the open above.)

  -- `liftW lt (pad pre suf g)` is the wider `pad (lt ++ pre) suf g`, up to the
  -- +-associativity reindex on its endpoints.  This is the layer-level content
  -- of `shiftL`'s `reidx` wrappers.  Proven by induction on `lt`, mirroring
  -- `shiftL`'s own recursion.
  liftW-pad : ∀ {a b} (lt pre suf : List X) (g : HomTerm (wires a) (wires b))
            → liftW lt (pad pre suf g)
              ≈Term coeD (++-assoc lt pre (a ++ suf))
                      (coeC (++-assoc lt pre (b ++ suf))
                        (pad (lt ++ pre) suf g))
  liftW-pad []      pre suf g = ≈-Term-refl
  liftW-pad {a} {b} (x ∷ lt) pre suf g = begin
    id ⊗₁ liftW lt (pad pre suf g)
      ≈⟨ refl⟩⊗⟨ (liftW-pad lt pre suf g) ⟩
    id {Var x} ⊗₁ coeD (++-assoc lt pre (a ++ suf))
                    (coeC (++-assoc lt pre (b ++ suf)) (pad (lt ++ pre) suf g))
      ≈⟨ ⟺ (coeD-id⊗ x (++-assoc lt pre (a ++ suf)) _) ⟩
    coeD (cong (x ∷_) (++-assoc lt pre (a ++ suf)))
      (id {Var x} ⊗₁ coeC (++-assoc lt pre (b ++ suf)) (pad (lt ++ pre) suf g))
      ≈⟨ coeD-resp _ (⟺ (coeC-id⊗ x (++-assoc lt pre (b ++ suf)) _)) ⟩
    coeD (cong (x ∷_) (++-assoc lt pre (a ++ suf)))
      (coeC (cong (x ∷_) (++-assoc lt pre (b ++ suf))) (id {Var x} ⊗₁ pad (lt ++ pre) suf g))
      ≈⟨ coeD-castU (cong (x ∷_) (++-assoc lt pre (a ++ suf))) (++-assoc (x ∷ lt) pre (a ++ suf)) _ ⟩
    coeD (++-assoc (x ∷ lt) pre (a ++ suf))
      (coeC (cong (x ∷_) (++-assoc lt pre (b ++ suf))) (id {Var x} ⊗₁ pad (lt ++ pre) suf g))
      ≈⟨ coeD-resp _ (coeC-castU (cong (x ∷_) (++-assoc lt pre (b ++ suf))) (++-assoc (x ∷ lt) pre (b ++ suf)) _) ⟩
    coeD (++-assoc (x ∷ lt) pre (a ++ suf))
      (coeC (++-assoc (x ∷ lt) pre (b ++ suf)) (id {Var x} ⊗₁ pad (lt ++ pre) suf g)) ∎

  -- shiftL soundness.
  shiftL-sound : ∀ {n} (lt : List X) (d : DiagU n)
               → coeC (out-shiftL lt d) ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
  shiftL-sound lt ([]_ n) = ⟺ (liftW-id lt)
  shiftL-sound lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = goal
    where
      g = ⟦box⟧ f
      E1 : (lt ++ pre) ++ (a ++ suf) ≡ lt ++ (pre ++ (a ++ suf))
      E1 = ++-assoc lt pre (a ++ suf)
      E2 : lt ++ (pre ++ (b ++ suf)) ≡ (lt ++ pre) ++ (b ++ suf)
      E2 = sym (++-assoc lt pre (b ++ suf))
      d' = shiftL lt d
      LAYER : DiagU ((lt ++ pre) ++ (a ++ suf))
      LAYER = (lt ++ pre) ▸ suf ∷ f ⟨ reidx E2 d' ⟩
      -- the inner shifted layer (before the outer E1 reindex).
      ⟦LAYER⟧ : HomTerm (wires ((lt ++ pre) ++ (a ++ suf))) (wires (out (reidx E2 d')))
      ⟦LAYER⟧ = ⟦ reidx E2 d' ⟧ ∘ pad (lt ++ pre) suf g

      OUTcons : out (shiftL lt (pre ▸ suf ∷ f ⟨ d ⟩)) ≡ lt ++ out (pre ▸ suf ∷ f ⟨ d ⟩)
      OUTcons = out-shiftL lt (pre ▸ suf ∷ f ⟨ d ⟩)

      -- bridge equality used to retype the codomain.
      eBridge : out (reidx E2 d') ≡ lt ++ out d
      eBridge = trans (out-reidx E2 d') (out-shiftL lt d)

      goal : coeC OUTcons ⟦ reidx E1 ((lt ++ pre) ▸ suf ∷ f ⟨ reidx E2 d' ⟩) ⟧
             ≈Term liftW lt (⟦ d ⟧ ∘ pad pre suf g)
      goal = begin
        coeC OUTcons ⟦ reidx E1 LAYER ⟧
          ≈⟨ reidx-expand E1 LAYER OUTcons eBridge ⟩
        coeD E1 (coeC eBridge ⟦LAYER⟧)
          ≈⟨ coeD-resp E1 (coeC-∘ˡ eBridge ⟦ reidx E2 d' ⟧ (pad (lt ++ pre) suf g)) ⟩
        coeD E1 (coeC eBridge ⟦ reidx E2 d' ⟧ ∘ pad (lt ++ pre) suf g)
          ≈⟨ coeD-∘ʳ E1 (coeC eBridge ⟦ reidx E2 d' ⟧) (pad (lt ++ pre) suf g) ⟩
        coeC eBridge ⟦ reidx E2 d' ⟧ ∘ coeD E1 (pad (lt ++ pre) suf g)
          ≈⟨ mid-retype eM (coeC eBridge ⟦ reidx E2 d' ⟧) (coeD E1 (pad (lt ++ pre) suf g)) ⟩
        coeD eM (coeC eBridge ⟦ reidx E2 d' ⟧) ∘ coeC eM (coeD E1 (pad (lt ++ pre) suf g))
          ≈⟨ tailFold ⟩∘⟨ padFold ⟩
        liftW lt ⟦ d ⟧ ∘ liftW lt (pad pre suf g)
          ≈⟨ ⟺ (liftW-∘ lt ⟦ d ⟧ (pad pre suf g)) ⟩
        liftW lt (⟦ d ⟧ ∘ pad pre suf g) ∎
        where
          -- middle-object retype eq:  (lt++pre)++(b++suf) ≡ lt++(pre++(b++suf)).
          eM : (lt ++ pre) ++ (b ++ suf) ≡ lt ++ (pre ++ (b ++ suf))
          eM = ++-assoc lt pre (b ++ suf)
          -- the tail folds (reidx-fold + recursion) to liftW lt ⟦d⟧.
          tailFold : coeD eM (coeC eBridge ⟦ reidx E2 d' ⟧) ≈Term liftW lt ⟦ d ⟧
          tailFold = fold-reidx E2 eM d' eBridge (out-shiftL lt d) ○ shiftL-sound lt d
          padFold : coeC eM (coeD E1 (pad (lt ++ pre) suf g)) ≈Term liftW lt (pad pre suf g)
          padFold = begin
            coeC eM (coeD E1 (pad (lt ++ pre) suf g))
              ≈⟨ coe-comm E1 eM (pad (lt ++ pre) suf g) ⟩
            coeD E1 (coeC eM (pad (lt ++ pre) suf g))
              ≈⟨ ⟺ (liftW-pad lt pre suf g) ⟩
            liftW lt (pad pre suf g) ∎

  --------------------------------------------------------------------------------
  -- The suffix flat-shift `rpad` lemma family, and its soundness for `shiftR`.
  -- (`rpad-resp` / `rpad-id` / `rpad-∘` now live in UntypedI.)
  --------------------------------------------------------------------------------

  -- `merge` associativity (built from `coherence₁` and α-naturality):
  --   merge p {q++r} ∘ (id ⊗₁ merge q {r}) ∘ α⇒
  --     ≈ coeC (++-assoc p q r) (merge (p++q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))
  merge-assoc : ∀ (p q r : List X)
              → merge p {q ++ r} ∘ (id {wires p} ⊗₁ merge q {r}) ∘ α⇒
                ≈Term coeC (++-assoc p q r) (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))
  merge-assoc []      q r = begin
    λ⇒ ∘ (id {unit} ⊗₁ merge q {r}) ∘ α⇒
      ≈⟨ pullˡ λ⇒∘id⊗f≈f∘λ⇒ ⟩
    (merge q {r} ∘ λ⇒) ∘ α⇒
      ≈⟨ pullʳ λ⇒∘α⇒≈λ⇒⊗id ⟩
    merge q {r} ∘ (λ⇒ ⊗₁ id) ∎
  merge-assoc (x ∷ p) q r = begin
    -- LHS = merge(x∷p){q++r} ∘ (id{wires(x∷p)} ⊗ merge q) ∘ α⇒
    (id {Var x} ⊗₁ merge p {q ++ r} ∘ α⇒ {Var x} {wires p} {wires (q ++ r)})
      ∘ (id {Var x ⊗₀ wires p} ⊗₁ merge q {r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
      ≈⟨ refl⟩∘⟨ (((⟺ id⊗id≈id) ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
    (id {Var x} ⊗₁ merge p {q ++ r} ∘ α⇒ {Var x} {wires p} {wires (q ++ r)})
      ∘ ((id {Var x} ⊗₁ id {wires p}) ⊗₁ merge q {r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
      ≈⟨ center α-comm ⟩
    id ⊗₁ merge p ∘ ((id ⊗₁ (id ⊗₁ merge q) ∘ α⇒) ∘ α⇒)
      ≈⟨ ⟺ assoc ⟩
    (id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ merge q) ∘ α⇒)) ∘ α⇒
      ≈⟨ (pullˡ (id⊗-∘ (merge p {q ++ r}) (id ⊗₁ merge q {r}))) ⟩∘⟨refl ⟩
    ((id ⊗₁ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) )
       ∘ α⇒ {Var x} {wires p} {wires q ⊗₀ wires r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
      ≈⟨ pent ⟩
    (id {Var x} ⊗₁ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) ∘ id {Var x} ⊗₁ α⇒ {wires p} {wires q} {wires r}) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
      ≈⟨ (id⊗-∘ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) (α⇒ {wires p} {wires q} {wires r})) ⟩∘⟨refl ⟩
    (id {Var x} ⊗₁ ((merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) ∘ α⇒ {wires p} {wires q} {wires r})) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
      ≈⟨ (refl⟩⊗⟨ (assoc ○ (merge-assoc p q r))) ⟩∘⟨refl ⟩
    (id ⊗₁ coeC (++-assoc p q r) (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})))
      ∘ (α⇒ ∘ α⇒ ⊗₁ id)
      ≈⟨ (⟺ (coeC-id⊗ x (++-assoc p q r) _)) ⟩∘⟨refl ⟩
    coeC (cong (x ∷_) (++-assoc p q r)) (id ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id)))
      ∘ (α⇒ ∘ α⇒ ⊗₁ id)
      ≈⟨ ⟺ (coeC-∘ˡ (cong (x ∷_) (++-assoc p q r)) _ (α⇒ ∘ α⇒ ⊗₁ id)) ⟩
    coeC (cong (x ∷_) (++-assoc p q r))
      ((id ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id))
      ≈⟨ coeC-resp _ tailRHS ⟩
    coeC (cong (x ∷_) (++-assoc p q r))
      (((id ⊗₁ merge (p ++ q) {r}) ∘ α⇒) ∘ ((id ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r}))
      ≈⟨ coeC-castU (cong (x ∷_) (++-assoc p q r)) (++-assoc (x ∷ p) q r) _ ⟩
    coeC (++-assoc (x ∷ p) q r)
      (((id ⊗₁ merge (p ++ q) {r}) ∘ α⇒) ∘ ((id ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r})) ∎
    where
      -- pentagon rebracketing of the two trailing associators:
      --   (X ∘ α⇒) ∘ α⇒  ≈  (X ∘ id⊗α⇒) ∘ (α⇒ ∘ α⇒⊗id)
      -- where X = id ⊗ (…).  Uses `pentagon`.
      pent : ∀ {B} {X : HomTerm (Var x ⊗₀ (wires p ⊗₀ (wires q ⊗₀ wires r))) B}
           → (X ∘ α⇒ {Var x} {wires p} {wires q ⊗₀ wires r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
             ≈Term (X ∘ id {Var x} ⊗₁ α⇒ {wires p} {wires q} {wires r})
                   ∘ (α⇒ {Var x} {wires p ⊗₀ wires q} {wires r} ∘ α⇒ {Var x} {wires p} {wires q} ⊗₁ id {wires r})
      pent {X = X} = pullʳ (⟺ pentagon) ○ ⟺ assoc
      -- expand the RHS tail (id⊗(merge(p++q) ∘ (merge p ⊗ id))) ∘ (α⇒ ∘ α⇒⊗id)
      -- into the cons-merge form  (id⊗merge(p++q) ∘ α⇒) ∘ ((id⊗merge p ∘ α⇒)⊗id).
      tailRHS : (id {Var x} ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})))
                  ∘ (α⇒ {Var x} {wires p ⊗₀ wires q} {wires r}
                     ∘ α⇒ {Var x} {wires p} {wires q} ⊗₁ id {wires r})
              ≈Term ((id {Var x} ⊗₁ merge (p ++ q) {r}) ∘ α⇒)
                    ∘ ((id {Var x} ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r})
      tailRHS = begin
        (id ⊗₁ (merge (p ++ q) ∘ (merge p ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
          ≈⟨ (⟺ (id⊗-∘ (merge (p ++ q) {r}) (merge p {q} ⊗₁ id))) ⟩∘⟨refl ⟩
        (id ⊗₁ merge (p ++ q) ∘ id ⊗₁ (merge p ⊗₁ id)) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
          ≈⟨ center (⟺ α-comm) ⟩
        id ⊗₁ merge (p ++ q) ∘ ((α⇒ ∘ (id ⊗₁ merge p) ⊗₁ id) ∘ α⇒ ⊗₁ id)
          ≈⟨ refl⟩∘⟨ pullʳ (⟺ split₁ʳ) ⟩
        id ⊗₁ merge (p ++ q) ∘ (α⇒ ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id))
          ≈⟨ ⟺ assoc ⟩
        (id ⊗₁ merge (p ++ q) ∘ α⇒) ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id) ∎

  -- `split` associativity (dual of `merge-assoc`, via `coherence-inv₁` + α):
  --   α⇐ ∘ (id ⊗₁ split q {r}) ∘ split p {q++r}
  --     ≈ coeD (++-assoc p q r) ((split p {q} ⊗₁ id) ∘ split (p++q) {r})
  -- proven uniformly (no induction) by inverting `merge-assoc`: both
  -- split-assoc-LHS and merge-assoc-LHS are mutually-inverse isos, as are
  -- the two RHSs, so the equation transports across inversion.
  split-assoc : ∀ (p q r : List X)
              → α⇐ ∘ (id {wires p} ⊗₁ split q {r}) ∘ split p {q ++ r}
                ≈Term coeD (++-assoc p q r) ((split p {q} ⊗₁ id {wires r}) ∘ split (p ++ q) {r})
  split-assoc p q r = inv-resp fi-f g-gi (merge-assoc p q r)
    where
      e = ++-assoc p q r
      mL : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires (p ++ (q ++ r)))
      mL = merge p {q ++ r} ∘ (id {wires p} ⊗₁ merge q {r}) ∘ α⇒
      fi : HomTerm (wires (p ++ (q ++ r))) ((wires p ⊗₀ wires q) ⊗₀ wires r)
      fi = α⇐ ∘ (id {wires p} ⊗₁ split q {r}) ∘ split p {q ++ r}
      mR : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires ((p ++ q) ++ r))
      mR = merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})
      giU : HomTerm (wires ((p ++ q) ++ r)) ((wires p ⊗₀ wires q) ⊗₀ wires r)
      giU = (split p {q} ⊗₁ id {wires r}) ∘ split (p ++ q) {r}
      -- generic inverse-respects-≈.
      inv-resp : ∀ {A B} {f : HomTerm A B} {g : HomTerm A B}
                   {fi gi : HomTerm B A}
               → fi ∘ f ≈Term id → g ∘ gi ≈Term id → f ≈Term g → fi ≈Term gi
      inv-resp {f = f} {g} {fi} {gi} fif ggi f≈g =
        introʳ ggi ○ (refl⟩∘⟨ ((⟺ f≈g) ⟩∘⟨refl)) ○ cancelˡ fif
      -- fi ∘ mL ≈ id  (mutual inverses, cancelling split∘merge and α⇐∘α⇒).
      fi-f : fi ∘ mL ≈Term id
      fi-f = begin
        (α⇐ ∘ (id ⊗₁ split q) ∘ split p) ∘ (merge p ∘ (id ⊗₁ merge q) ∘ α⇒)
          ≈⟨ center (cancelʳ (split∘merge p)) ⟩
        α⇐ ∘ ((id ⊗₁ split q) ∘ ((id ⊗₁ merge q) ∘ α⇒))
          ≈⟨ refl⟩∘⟨ cancelˡ (id⊗-cancel (split∘merge q)) ⟩
        α⇐ ∘ α⇒
          ≈⟨ α⇐∘α⇒≈id ⟩
        id ∎
      -- (coeC e mR) ∘ (coeD e giU) ≈ id  via mR ∘ giU ≈ id and coercion cancel.
      g-gi : coeC e mR ∘ coeD e giU ≈Term id
      g-gi = coe-cancel e mR giU mR-giU
        where
          coe-cancel : ∀ {p' q'} (eq : p' ≡ q')
                         (M : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires p'))
                         (N : HomTerm (wires p') ((wires p ⊗₀ wires q) ⊗₀ wires r))
                     → M ∘ N ≈Term id → coeC eq M ∘ coeD eq N ≈Term id
          coe-cancel refl M N eq = eq
          mR-giU : mR ∘ giU ≈Term id
          mR-giU =
            cancelInner ((⟺ ⊗-∘-dist) ○ ((merge∘split p) ⟩⊗⟨ idˡ) ○ id⊗id≈id)
              ○ merge∘split (p ++ q)

  -- `rpad` suffix-fusion:  rpad rt (rpad suf g) is the wider rpad (suf++rt) g,
  -- up to +-associativity reindex on its endpoints.  This is the base case of
  -- the suffix shift / pad relation.  Assembled from `merge-assoc`/`split-assoc`.
  rpad-fuse : ∀ {a b} (suf rt : List X) (g : HomTerm (wires a) (wires b))
            → rpad rt (rpad suf g)
              ≈Term coeD (sym (++-assoc a suf rt))
                      (coeC (sym (++-assoc b suf rt)) (rpad (suf ++ rt) g))
  rpad-fuse {a} {b} suf rt g = begin
    merge (b ++ suf) {rt} ∘ ((merge b {suf} ∘ (g ⊗₁ id {wires suf}) ∘ split a {suf}) ⊗₁ id {wires rt}) ∘ split (a ++ suf) {rt}
      ≈⟨ refl⟩∘⟨ ((refl⟩⊗⟨ (⟺ idˡ)) ⟩∘⟨refl) ⟩
    merge (b ++ suf) ∘ ((merge b ∘ ((g ⊗₁ id) ∘ split a)) ⊗₁ (id ∘ id)) ∘ split (a ++ suf)
      ≈⟨ refl⟩∘⟨ (⊗-∘-dist ⟩∘⟨refl) ⟩
    merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ∘ split a) ⊗₁ id) ∘ split (a ++ suf)
      ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (refl⟩⊗⟨ (⟺ idˡ))) ⟩∘⟨refl) ⟩
    merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ∘ split a) ⊗₁ (id ∘ id)) ∘ split (a ++ suf)
      ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ ⊗-∘-dist) ⟩∘⟨refl) ⟩
    merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
      ≈⟨ regroup5 ⟩
    (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt}) ∘ (split a ⊗₁ id ∘ split (a ++ suf))
      ≈⟨ mergeStep ⟩∘⟨ (refl⟩∘⟨ splitStep) ⟩
    coeC (sym (++-assoc b suf rt)) (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
      ∘ ((g ⊗₁ id) ⊗₁ id)
      ∘ coeD (sym (++-assoc a suf rt)) (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})
      ≈⟨ pull-coe ⟩
    coeD (sym (++-assoc a suf rt))
      (coeC (sym (++-assoc b suf rt))
        ((merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
          ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
          ∘ (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})))
      ≈⟨ coeD-resp (sym (++-assoc a suf rt)) (coeC-resp (sym (++-assoc b suf rt)) core) ⟩
    coeD (sym (++-assoc a suf rt))
      (coeC (sym (++-assoc b suf rt)) (rpad (suf ++ rt) g)) ∎
    where
      -- mergeStep:  merge(b++suf)∘(merge b⊗id) ≈ coeC(sym e_b)(merge b{suf++rt}∘(id⊗merge suf)∘α⇒)
      mergeStep : merge (b ++ suf) {rt} ∘ (merge b {suf} ⊗₁ id {wires rt})
                ≈Term coeC (sym (++-assoc b suf rt)) (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
      mergeStep = ⟺ (coeC-invert (++-assoc b suf rt) _ _ (merge-assoc b suf rt))
      -- splitStep:  (split a⊗id)∘split(a++suf) ≈ coeD(sym e_a)(α⇐∘(id⊗split suf)∘split a{suf++rt})
      splitStep : (split a {suf} ⊗₁ id {wires rt}) ∘ split (a ++ suf) {rt}
                ≈Term coeD (sym (++-assoc a suf rt)) (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})
      splitStep = ⟺ (coeD-invert (++-assoc a suf rt) _ _ (split-assoc a suf rt))
      -- bookkeeping regroup of the 5-fold composite.
      regroup5 : merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
               ≈Term (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt}) ∘ (split a ⊗₁ id ∘ split (a ++ suf))
      regroup5 = center⁻¹ ≈-Term-refl assoc
      -- pull the coeC / coeD coercions out of the composite to the ends.
      pull-coe :
          coeC (sym (++-assoc b suf rt)) (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
            ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
            ∘ coeD (sym (++-assoc a suf rt)) (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})
        ≈Term coeD (sym (++-assoc a suf rt))
                (coeC (sym (++-assoc b suf rt))
                  ((merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
                    ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
                    ∘ (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})))
      pull-coe = pull (sym (++-assoc b suf rt)) (sym (++-assoc a suf rt)) _ _ _
        where
          pull : ∀ {pb qb pa qa} {C D : ObjTerm}
                   (eb : pb ≡ qb) (ea : pa ≡ qa)
                   (L : HomTerm C (wires pb))
                   (Mid : HomTerm D C)
                   (Rt : HomTerm (wires pa) D)
               → coeC eb L ∘ Mid ∘ coeD ea Rt
                 ≈Term coeD ea (coeC eb (L ∘ Mid ∘ Rt))
          pull refl refl L Mid Rt = ≈-Term-refl
      -- the core box-conjugation collapse (pure bifunctoriality + α + iso).
      core : (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
               ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
               ∘ (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})
             ≈Term rpad (suf ++ rt) g
      core = begin
        (merge b ∘ (id ⊗₁ merge suf) ∘ α⇒) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split suf) ∘ split a)
          ≈⟨ coreRegroup ⟩
        merge b ∘ ((id ⊗₁ merge suf) ∘ (α⇒ ∘ ((g ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ split suf)) ∘ split a
          ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (midα ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
        merge b ∘ ((id ⊗₁ merge suf) ∘ (g ⊗₁ (id {wires suf} ⊗₁ id {wires rt})) ∘ (id ⊗₁ split suf)) ∘ split a
          ≈⟨ refl⟩∘⟨ (midColl ⟩∘⟨refl) ⟩
        merge b ∘ (g ⊗₁ id {wires (suf ++ rt)}) ∘ split a ∎
        where
          -- both sides equal the fully right-associated 7-fold composite.
          m1 = merge b {suf ++ rt}
          m2 = id {wires b} ⊗₁ merge suf {rt}
          m3 = α⇒ {wires b} {wires suf} {wires rt}
          m4 = (g ⊗₁ id {wires suf}) ⊗₁ id {wires rt}
          m5 = α⇐ {wires a} {wires suf} {wires rt}
          m6 = id {wires a} ⊗₁ split suf {rt}
          m7 = split a {suf ++ rt}
          rNF = m1 ∘ (m2 ∘ (m3 ∘ (m4 ∘ (m5 ∘ (m6 ∘ m7)))))
          coreRegroup :
              (merge b ∘ (id ⊗₁ merge suf) ∘ α⇒) ∘ ((g ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split suf) ∘ split a)
            ≈Term merge b ∘ ((id ⊗₁ merge suf) ∘ (α⇒ ∘ ((g ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ split suf)) ∘ split a
          coreRegroup = (lhsNF ○ (⟺ rhsNF))
            where
              lhsNF : (m1 ∘ m2 ∘ m3) ∘ (m4 ∘ (m5 ∘ m6 ∘ m7)) ≈Term rNF
              lhsNF = assoc ○ (refl⟩∘⟨ assoc)
              rhsNF : m1 ∘ ((m2 ∘ (m3 ∘ (m4 ∘ m5)) ∘ m6) ∘ m7) ≈Term rNF
              rhsNF = refl⟩∘⟨ pullʳ (assoc ○ pullʳ assoc)
          -- α⇒ ∘ ((g⊗id)⊗id) ∘ α⇐ ≈ g⊗(id⊗id)
          midα : α⇒ ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt}) ∘ α⇐
               ≈Term g ⊗₁ (id {wires suf} ⊗₁ id {wires rt})
          midα = pullˡ α-comm ○ cancelʳ α⇒∘α⇐≈id
          -- (id⊗merge suf) ∘ (g⊗(id⊗id)) ∘ (id⊗split suf) ≈ g ⊗ id{suf++rt}
          midColl : (id {wires b} ⊗₁ merge suf {rt}) ∘ (g ⊗₁ (id {wires suf} ⊗₁ id {wires rt})) ∘ (id {wires a} ⊗₁ split suf {rt})
                  ≈Term g ⊗₁ id {wires (suf ++ rt)}
          midColl = begin
            (id ⊗₁ merge suf) ∘ (g ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ split suf)
              ≈⟨ refl⟩∘⟨ ((refl⟩⊗⟨ id⊗id≈id) ⟩∘⟨refl) ⟩
            (id ⊗₁ merge suf) ∘ (g ⊗₁ id) ∘ (id ⊗₁ split suf)
              ≈⟨ refl⟩∘⟨ (⟺ serialize₁₂) ⟩
            (id ⊗₁ merge suf) ∘ (g ⊗₁ split suf)
              ≈⟨ ⟺ ⊗-∘-dist ⟩
            (id ∘ g) ⊗₁ (merge suf {rt} ∘ split suf {rt})
              ≈⟨ idˡ ⟩⊗⟨ (merge∘split suf) ⟩
            g ⊗₁ id ∎

  -- (`rpad-id⊗` now lives in UntypedI.)

  -- rpad / pad relation (suffix analogue of liftW-pad), by induction on pre.
  rpad-pad : ∀ {a b} (pre suf rt : List X) (g : HomTerm (wires a) (wires b))
             → rpad rt (pad pre suf g)
               ≈Term coeD (sym (reassoc++ pre a suf rt))
                       (coeC (sym (reassoc++ pre b suf rt)) (pad pre (suf ++ rt) g))
  rpad-pad {a} {b} []      suf rt g = begin
    rpad rt (rpad suf g)
      ≈⟨ rpad-fuse suf rt g ⟩
    coeD (sym (++-assoc a suf rt)) (coeC (sym (++-assoc b suf rt)) (rpad (suf ++ rt) g))
      ≈⟨ coeD-castU (sym (++-assoc a suf rt)) (sym (reassoc++ [] a suf rt)) _ ⟩
    coeD (sym (reassoc++ [] a suf rt)) (coeC (sym (++-assoc b suf rt)) (rpad (suf ++ rt) g))
      ≈⟨ coeD-resp _ (coeC-castU (sym (++-assoc b suf rt)) (sym (reassoc++ [] b suf rt)) _) ⟩
    coeD (sym (reassoc++ [] a suf rt)) (coeC (sym (reassoc++ [] b suf rt)) (rpad (suf ++ rt) g)) ∎
  rpad-pad {a} {b} (x ∷ p) suf rt g = begin
    rpad rt (id {Var x} ⊗₁ pad p suf g)
      ≈⟨ rpad-id⊗ rt x (pad p suf g) ⟩
    id {Var x} ⊗₁ rpad rt (pad p suf g)
      ≈⟨ refl⟩⊗⟨ (rpad-pad p suf rt g) ⟩
    id {Var x} ⊗₁ coeD (sym (reassoc++ p a suf rt)) (coeC (sym (reassoc++ p b suf rt)) (pad p (suf ++ rt) g))
      ≈⟨ ⟺ (coeD-id⊗ x (sym (reassoc++ p a suf rt)) _) ⟩
    coeD (cong (x ∷_) (sym (reassoc++ p a suf rt))) (id {Var x} ⊗₁ coeC (sym (reassoc++ p b suf rt)) (pad p (suf ++ rt) g))
      ≈⟨ coeD-resp _ (⟺ (coeC-id⊗ x (sym (reassoc++ p b suf rt)) _)) ⟩
    coeD (cong (x ∷_) (sym (reassoc++ p a suf rt)))
      (coeC (cong (x ∷_) (sym (reassoc++ p b suf rt))) (id {Var x} ⊗₁ pad p (suf ++ rt) g))
      ≈⟨ coeD-castU (cong (x ∷_) (sym (reassoc++ p a suf rt))) (sym (reassoc++ (x ∷ p) a suf rt)) _ ⟩
    coeD (sym (reassoc++ (x ∷ p) a suf rt))
      (coeC (cong (x ∷_) (sym (reassoc++ p b suf rt))) (id {Var x} ⊗₁ pad p (suf ++ rt) g))
      ≈⟨ coeD-resp _ (coeC-castU (cong (x ∷_) (sym (reassoc++ p b suf rt))) (sym (reassoc++ (x ∷ p) b suf rt)) _) ⟩
    coeD (sym (reassoc++ (x ∷ p) a suf rt))
      (coeC (sym (reassoc++ (x ∷ p) b suf rt)) (id {Var x} ⊗₁ pad p (suf ++ rt) g)) ∎

  -- shiftR soundness:  coeC (out-shiftR rt d) ⟦ shiftR rt d ⟧ ≈ rpad rt ⟦ d ⟧.
  shiftR-sound : ∀ {n} (rt : List X) (d : DiagU n)
               → coeC (out-shiftR rt d) ⟦ shiftR rt d ⟧ ≈Term rpad rt ⟦ d ⟧
  shiftR-sound rt ([]_ n) = ⟺ (rpad-id rt)
  shiftR-sound rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = goal
    where
      g = ⟦box⟧ f
      E1 : (pre ++ (a ++ suf)) ++ rt ≡ pre ++ (a ++ (suf ++ rt))
      E1 = reassoc++ pre a suf rt
      E2 : (pre ++ (b ++ suf)) ++ rt ≡ pre ++ (b ++ (suf ++ rt))
      E2 = reassoc++ pre b suf rt
      d' = shiftR rt d
      LAYER : DiagU (pre ++ (a ++ (suf ++ rt)))
      LAYER = pre ▸ (suf ++ rt) ∷ f ⟨ reidx E2 d' ⟩
      ⟦LAYER⟧ : HomTerm (wires (pre ++ (a ++ (suf ++ rt)))) (wires (out (reidx E2 d')))
      ⟦LAYER⟧ = ⟦ reidx E2 d' ⟧ ∘ pad pre (suf ++ rt) g
      OUTcons : out (shiftR rt (pre ▸ suf ∷ f ⟨ d ⟩)) ≡ out (pre ▸ suf ∷ f ⟨ d ⟩) ++ rt
      OUTcons = out-shiftR rt (pre ▸ suf ∷ f ⟨ d ⟩)
      eBridge : out (reidx E2 d') ≡ out d ++ rt
      eBridge = trans (out-reidx E2 d') (out-shiftR rt d)
      -- middle-object retype eq:  (pre++(b++suf))++rt ≡ pre++(b++(suf++rt)).
      eM : (pre ++ (b ++ suf)) ++ rt ≡ pre ++ (b ++ (suf ++ rt))
      eM = reassoc++ pre b suf rt
      goal : coeC OUTcons ⟦ reidx (sym E1) ((pre ▸ (suf ++ rt) ∷ f ⟨ reidx E2 d' ⟩)) ⟧
             ≈Term rpad rt (⟦ d ⟧ ∘ pad pre suf g)
      goal = begin
        coeC OUTcons ⟦ reidx (sym E1) LAYER ⟧
          ≈⟨ reidx-expand (sym E1) LAYER OUTcons eBridge ⟩
        coeD (sym E1) (coeC eBridge ⟦LAYER⟧)
          ≈⟨ coeD-resp (sym E1) (coeC-∘ˡ eBridge ⟦ reidx E2 d' ⟧ (pad pre (suf ++ rt) g)) ⟩
        coeD (sym E1) (coeC eBridge ⟦ reidx E2 d' ⟧ ∘ pad pre (suf ++ rt) g)
          ≈⟨ coeD-∘ʳ (sym E1) (coeC eBridge ⟦ reidx E2 d' ⟧) (pad pre (suf ++ rt) g) ⟩
        coeC eBridge ⟦ reidx E2 d' ⟧ ∘ coeD (sym E1) (pad pre (suf ++ rt) g)
          ≈⟨ mid-retype eMrev (coeC eBridge ⟦ reidx E2 d' ⟧) (coeD (sym E1) (pad pre (suf ++ rt) g)) ⟩
        coeD eMrev (coeC eBridge ⟦ reidx E2 d' ⟧) ∘ coeC eMrev (coeD (sym E1) (pad pre (suf ++ rt) g))
          ≈⟨ tailFold ⟩∘⟨ padFold ⟩
        rpad rt ⟦ d ⟧ ∘ rpad rt (pad pre suf g)
          ≈⟨ ⟺ (rpad-∘ rt ⟦ d ⟧ (pad pre suf g)) ⟩
        rpad rt (⟦ d ⟧ ∘ pad pre suf g) ∎
        where
          -- middle retype eq:  out(reidx E2 d') = out d ++ rt side
          --  domain of left factor = pre++(b++(suf++rt)); we retype it to
          --  (pre++(b++suf))++rt to match rpad rt ⟦d⟧ domain.
          eMrev : pre ++ (b ++ (suf ++ rt)) ≡ (pre ++ (b ++ suf)) ++ rt
          eMrev = sym eM
          tailFold : coeD eMrev (coeC eBridge ⟦ reidx E2 d' ⟧) ≈Term rpad rt ⟦ d ⟧
          tailFold = fold-reidx E2 eMrev d' eBridge (out-shiftR rt d) ○ shiftR-sound rt d
          padFold : coeC eMrev (coeD (sym E1) (pad pre (suf ++ rt) g)) ≈Term rpad rt (pad pre suf g)
          padFold = begin
            coeC eMrev (coeD (sym E1) (pad pre (suf ++ rt) g))
              ≈⟨ coe-comm (sym E1) eMrev (pad pre (suf ++ rt) g) ⟩
            coeD (sym E1) (coeC eMrev (pad pre (suf ++ rt) g))
              ≈⟨ ⟺ (rpad-pad pre suf rt g) ⟩
            rpad rt (pad pre suf g) ∎

  --------------------------------------------------------------------------------
  -- tensorD soundness (pure bifunctoriality, no σ):
  --   coeC (out-tensorD dl dr) ⟦ tensorD dl dr ⟧
  --     ≈ merge (out dl) ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl
  -- the wire-grouping bridge between `wires nl ⊗₀ wires nr` and `wires (nl++nr)`.
  --------------------------------------------------------------------------------
  tensorD-sound : ∀ {nl nr} (dl : DiagU nl) (dr : DiagU nr)
                → coeC (out-tensorD dl dr) ⟦ tensorD dl dr ⟧
                  ≈Term merge (out dl) {out dr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr}
  tensorD-sound {nl} {nr} dl dr = begin
    coeC (out-tensorD dl dr) ⟦ shiftR nr dl ∘ᵈ d2 ⟧
      ≈⟨ coeC-fold (out-∘ᵈ (shiftR nr dl) d2) eBr (out-tensorD dl dr) (∘ᵈ-sound (shiftR nr dl) d2) ⟩
    coeC eBr (⟦ d2 ⟧ ∘ ⟦ shiftR nr dl ⟧)
      ≈⟨ coeC-∘ˡ eBr ⟦ d2 ⟧ ⟦ shiftR nr dl ⟧ ⟩
    coeC eBr ⟦ d2 ⟧ ∘ ⟦ shiftR nr dl ⟧
      ≈⟨ mid-retype eSR (coeC eBr ⟦ d2 ⟧) ⟦ shiftR nr dl ⟧ ⟩
    coeD eSR (coeC eBr ⟦ d2 ⟧) ∘ coeC eSR ⟦ shiftR nr dl ⟧
      ≈⟨ d2Fold ⟩∘⟨ shiftRfold ⟩
    (merge (out dl) {out dr} ∘ (id {wires (out dl)} ⊗₁ ⟦ dr ⟧) ∘ split (out dl) {nr})
      ∘ (merge (out dl) {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr})
      ≈⟨ collapse ⟩
    merge (out dl) {out dr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr} ∎
    where
      d2 = reidx (sym (out-shiftR nr dl)) (shiftL (out dl) dr)
      eSR : out (shiftR nr dl) ≡ out dl ++ nr
      eSR = out-shiftR nr dl
      eR2 : out (reidx (sym (out-shiftR nr dl)) (shiftL (out dl) dr)) ≡ out (shiftL (out dl) dr)
      eR2 = out-reidx (sym (out-shiftR nr dl)) (shiftL (out dl) dr)
      -- bridge:  out d2 ≡ out dl ++ out dr.
      eBr : out d2 ≡ out dl ++ out dr
      eBr = trans eR2 (out-shiftL (out dl) dr)
      -- ⟦ shiftR nr dl ⟧, codomain-retyped, folds to rpad nr ⟦dl⟧.
      shiftRfold : coeC eSR ⟦ shiftR nr dl ⟧
                 ≈Term merge (out dl) {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr}
      shiftRfold = shiftR-sound nr dl
      -- coeD eSR (coeC eBr ⟦ d2 ⟧) folds to liftW (out dl) ⟦dr⟧ = bridge form.
      d2Fold : coeD eSR (coeC eBr ⟦ d2 ⟧)
             ≈Term merge (out dl) {out dr} ∘ (id {wires (out dl)} ⊗₁ ⟦ dr ⟧) ∘ split (out dl) {nr}
      d2Fold = fold-reidx (sym eSR) eSR (shiftL (out dl) dr) eBr (out-shiftL (out dl) dr)
               ○ shiftL-sound (out dl) dr
               ○ liftW-merge (out dl) ⟦ dr ⟧
      -- the central bifunctoriality collapse.
      collapse :
          (merge (out dl) {out dr} ∘ (id {wires (out dl)} ⊗₁ ⟦ dr ⟧) ∘ split (out dl) {nr})
            ∘ (merge (out dl) {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr})
        ≈Term merge (out dl) {out dr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr}
      collapse = begin
        (merge (out dl) ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split (out dl)) ∘ (merge (out dl) ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
          ≈⟨ center (cancelʳ (split∘merge (out dl))) ⟩
        merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ ((⟦ dl ⟧ ⊗₁ id) ∘ split nl))
          ≈⟨ refl⟩∘⟨ pullˡ (⟺ serialize₂₁) ⟩
        merge (out dl) ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl ∎

  --   coeC (out-reflect t) ⟦ reflect t ⟧  ≈Term  embed t
  -- i.e. the reflected diagram, with its codomain reindexed to match, equals
  -- the original wire-fragment morphism.
  --------------------------------------------------------------------------------
  reflect-sound : ∀ {n m} (t : WTerm n m)
                → coeC (out-reflect t) ⟦ reflect t ⟧ ≈Term embed t
  reflect-sound idʷ = ≈-Term-refl
  reflect-sound (_∘ʷ_ {n} {m} {k} g f) = goal
    where
      -- abbreviations
      df = reflect f
      dg = reflect g
      ef = out-reflect f                -- out df ≡ m
      dg' = reidx (sym ef) dg           -- DiagU (out df)
      -- step 1: push coeC through ∘ᵈ-sound.
      goal : coeC (out-reflect (g ∘ʷ f)) ⟦ df ∘ᵈ dg' ⟧ ≈Term embed g ∘ embed f
      goal = begin
        coeC (out-reflect (g ∘ʷ f)) ⟦ df ∘ᵈ dg' ⟧
          ≈⟨ coeC-fold (out-∘ᵈ df dg') eg-bridge (out-reflect (g ∘ʷ f)) (∘ᵈ-sound df dg') ⟩
        coeC eg-bridge (⟦ dg' ⟧ ∘ ⟦ df ⟧)
          ≈⟨ coeC-∘ˡ eg-bridge ⟦ dg' ⟧ ⟦ df ⟧ ⟩
        coeC eg-bridge ⟦ dg' ⟧ ∘ ⟦ df ⟧
          ≈⟨ mid-retype ef (coeC eg-bridge ⟦ dg' ⟧) ⟦ df ⟧ ⟩
        coeD ef (coeC eg-bridge ⟦ dg' ⟧) ∘ coeC ef ⟦ df ⟧
          ≈⟨ dg'-sound ⟩∘⟨ df-sound ⟩
        embed g ∘ embed f ∎
        where
          -- bridge:  out dg' ≡ k   (out dg' = out (reidx (sym ef) dg) ≡ out dg ≡ k)
          eg-bridge : out dg' ≡ k
          eg-bridge = trans (out-reidx (sym ef) dg) (out-reflect g)
          dg'-sound : coeD ef (coeC eg-bridge ⟦ dg' ⟧) ≈Term embed g
          dg'-sound = fold-reidx (sym ef) ef dg eg-bridge (out-reflect g) ○ reflect-sound g
          df-sound : coeC ef ⟦ df ⟧ ≈Term embed f
          df-sound = reflect-sound f
  reflect-sound (boxʷ {a} {b} g) =
    reidx-expand (++-identityʳ a) (boxD g) (out-reflect (boxʷ g)) (++-identityʳ b)
    ○ boxSound g
  reflect-sound (_⊗ʷ_ {nl} {ml} {nr} {mr} s t) = goal
    where
      ds = reflect s
      dt = reflect t
      es : out ds ≡ ml
      es = out-reflect s
      et : out dt ≡ mr
      et = out-reflect t
      goal : coeC (out-reflect (s ⊗ʷ t)) ⟦ tensorD ds dt ⟧
             ≈Term merge ml {mr} ∘ (embed s ⊗₁ embed t) ∘ split nl {nr}
      goal = begin
        coeC (out-reflect (s ⊗ʷ t)) ⟦ tensorD ds dt ⟧
          ≈⟨ coeC-fold (out-tensorD ds dt) (cong₂ _++_ es et) (out-reflect (s ⊗ʷ t)) (tensorD-sound ds dt) ⟩
        coeC (cong₂ _++_ es et) (merge (out ds) {out dt} ∘ (⟦ ds ⟧ ⊗₁ ⟦ dt ⟧) ∘ split nl {nr})
          ≈⟨ tensorBridge es et ⟩
        merge ml {mr} ∘ ((coeC es ⟦ ds ⟧ ⊗₁ coeC et ⟦ dt ⟧)) ∘ split nl {nr}
          ≈⟨ refl⟩∘⟨ (((reflect-sound s) ⟩⊗⟨ (reflect-sound t)) ⟩∘⟨refl) ⟩
        merge ml {mr} ∘ (embed s ⊗₁ embed t) ∘ split nl {nr} ∎
        where
          -- transport the merge-bridge along  out ds ≡ ml,  out dt ≡ mr.
          tensorBridge : ∀ {ml' mr'} (es : out ds ≡ ml') (et : out dt ≡ mr')
                       → coeC (cong₂ _++_ es et)
                           (merge (out ds) {out dt} ∘ (⟦ ds ⟧ ⊗₁ ⟦ dt ⟧) ∘ split nl {nr})
                         ≈Term merge ml' {mr'} ∘ ((coeC es ⟦ ds ⟧ ⊗₁ coeC et ⟦ dt ⟧)) ∘ split nl {nr}
          tensorBridge refl refl = ≈-Term-refl

--------------------------------------------------------------------------------
-- Compatibility wrapper: `ReflectI` at the standard interpretation
-- `Untyped.⟦box⟧` (= `var ∘ box`).  Old consumers keep working, gaining
-- only the leading variant argument.
--------------------------------------------------------------------------------
module Reflect (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
               (Mor : List X → List X → Set) where

  open Untyped v {X} Mor using (⟦box⟧)
  open ReflectI v {X} _≟X_ Mor ⟦box⟧ public
