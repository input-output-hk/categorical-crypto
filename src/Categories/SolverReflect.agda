{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A reflection  HomTerm → DiagU  with soundness, for the untyped free
-- monoidal diagram normal form of `Categories.DiagramRewriteUntyped`.
--
-- We work in the layered-composite wire fragment (M1): morphisms whose
-- source and target are already `wires`-shaped flat objects, built from
--   id, _∘_, var (box _),
-- captured by the inductive `WTerm n m` with embedding
-- `embed : WTerm n m → HomTerm (wires n) (wires m)`.  We define, all under
-- `--safe` and fully postulate-free / hole-free:
--   * `_∘ᵈ_`        : sequential composition (append) of diagrams, with
--                     soundness `∘ᵈ-sound : ⟦ d₁ ∘ᵈ d₂ ⟧ ≈ ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧`
--                     (codomain reindexed).  This is the `_∘_` case.
--   * `shiftL` / `shiftR` : prefix / suffix idle-wire shifts on diagrams
--                     (the offset-bookkeeping building blocks for a `tensorD`),
--                     with their `out` computed; soundness of these shifts and
--                     the full `tensorD`/`_⊗₁_` case are NOT included here.
--   * `reflect`     : WTerm n m → DiagU n  with `out-reflect : out (reflect t) ≡ m`.
--   * `reflect-sound`: ⟦ reflect t ⟧ ≈ embed t (codomain reindexed), proven by
--                     induction.  The single box-leaf right-unitor coherence
--                     (`merge a {[]} ≈ ρ⇒`, forbidden as a `--safe` postulate)
--                     is taken as the explicit hypothesis `BoxSound`; the id/∘
--                     structural logic is fully discharged.
--------------------------------------------------------------------------------

module Categories.SolverReflect where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ≡-dec)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped
import Categories.Category.Monoidal.Properties as MonProps

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

  -- coherence-inv₁ : α⇐ ∘ λ⇐ ≈Term λ⇐ ⊗₁ id  (inverse of coherence₁)
  α⇐∘λ⇐≈λ⇐⊗id : ∀ {A B} → α⇐ {unit} {A} {B} ∘ λ⇐ {A ⊗₀ B} ≈Term λ⇐ ⊗₁ id
  α⇐∘λ⇐≈λ⇐⊗id = K.coherence-inv₁

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

  -- Coerce a HomTerm along a propositional equality of its codomain index.
  coeCod' : ∀ {n p q} → p ≡ q → HomTerm (wires n) (wires p) → HomTerm (wires n) (wires q)
  coeCod' refl h = h

  coeCod'-∘ : ∀ {n p q r} (eq : p ≡ q) (h : HomTerm (wires r) (wires p))
                (k : HomTerm (wires n) (wires r))
            → coeCod' eq (h ∘ k) ≈Term coeCod' eq h ∘ k
  coeCod'-∘ refl h k = ≈-Term-refl

  -- Soundness of append:  ⟦ d₁ ∘ᵈ d₂ ⟧ ≈ ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧ (codomain coerced).
  ∘ᵈ-sound : ∀ {m} (d₁ : DiagU m) (d₂ : DiagU (out d₁))
           → coeCod' (out-∘ᵈ d₁ d₂) ⟦ d₁ ∘ᵈ d₂ ⟧ ≈Term ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧
  ∘ᵈ-sound ([]_ m) d₂ = ≈-Term-sym idʳ
  ∘ᵈ-sound (pre ▸ suf ∷ f ⟨ d ⟩) d₂ = begin
    coeCod' (out-∘ᵈ d d₂) (⟦ d ∘ᵈ d₂ ⟧ ∘ pad pre suf (⟦box⟧ f))
      ≈⟨ coeCod'-∘ (out-∘ᵈ d d₂) ⟦ d ∘ᵈ d₂ ⟧ (pad pre suf (⟦box⟧ f)) ⟩
    coeCod' (out-∘ᵈ d d₂) ⟦ d ∘ᵈ d₂ ⟧ ∘ pad pre suf (⟦box⟧ f)
      ≈⟨ ∘-resp-≈ (∘ᵈ-sound d d₂) ≈-Term-refl ⟩
    (⟦ d₂ ⟧ ∘ ⟦ d ⟧) ∘ pad pre suf (⟦box⟧ f)
      ≈⟨ assoc ⟩
    ⟦ d₂ ⟧ ∘ (⟦ d ⟧ ∘ pad pre suf (⟦box⟧ f)) ∎

  --------------------------------------------------------------------------------
  -- Reindexing a diagram along a propositional equality of its input index.
  -- For `refl` it is the identity, and `⟦_⟧` transports definitionally.
  --------------------------------------------------------------------------------
  coeDom : ∀ {a b p} → a ≡ b → HomTerm (wires a) (wires p) → HomTerm (wires b) (wires p)
  coeDom refl h = h

  reidx : ∀ {n n'} → n ≡ n' → DiagU n → DiagU n'
  reidx refl d = d

  out-reidx : ∀ {n n'} (eq : n ≡ n') (d : DiagU n) → out (reidx eq d) ≡ out d
  out-reidx refl d = refl

  -- transport lemma: reindexing only retypes the interpretation via the coes.
  ⟦reidx⟧ : ∀ {n n'} (eq : n ≡ n') (d : DiagU n)
          → ⟦ reidx eq d ⟧ ≈Term coeDom eq (coeCod' (sym (out-reidx eq d)) ⟦ d ⟧)
  ⟦reidx⟧ refl d = ≈-Term-refl

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
  open import Relation.Binary.PropositionalEquality using (trans)

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
  -- leaf carries a `++-identityʳ` reindex.  See the report for the remaining
  -- right-unitor coherence needed to fully discharge `⟦boxD⟧`.
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
  -- Transport algebra for coeDom / coeCod'.
  --------------------------------------------------------------------------------
  coeCod'-resp : ∀ {n p q} (eq : p ≡ q) {h h' : HomTerm (wires n) (wires p)}
               → h ≈Term h' → coeCod' eq h ≈Term coeCod' eq h'
  coeCod'-resp refl e = e

  coeDom-resp : ∀ {a b p} (eq : a ≡ b) {h h' : HomTerm (wires a) (wires p)}
              → h ≈Term h' → coeDom eq h ≈Term coeDom eq h'
  coeDom-resp refl e = e

  -- collapse two stacked codomain coercions.
  coeCod'-trans : ∀ {n p q s} (e1 : p ≡ q) (e2 : q ≡ s) (h : HomTerm (wires n) (wires p))
                → coeCod' e2 (coeCod' e1 h) ≈Term coeCod' (trans e1 e2) h
  coeCod'-trans refl refl h = ≈-Term-refl

  -- coeCod' and coeDom commute (independent ends).
  coe-comm : ∀ {a b p q} (e1 : a ≡ b) (e2 : p ≡ q) (h : HomTerm (wires a) (wires p))
           → coeCod' e2 (coeDom e1 h) ≈Term coeDom e1 (coeCod' e2 h)
  coe-comm refl refl h = ≈-Term-refl

  --------------------------------------------------------------------------------
  -- Box-leaf soundness:  ⟦ boxD g ⟧, transported across the structural
  --   a ++ [] ≡ a   and   b ++ [] ≡ b   reindices, equals ⟦box⟧ g.
  --
  -- ⟦ boxD g ⟧ = id ∘ rpad [] (⟦box⟧ g)
  --            = id ∘ (merge b {[]} ∘ (⟦box⟧ g ⊗₁ id{unit}) ∘ split a {[]}).
  -- The empty-suffix merge/split are the (transported) right-unitor iso, so
  -- this collapses to ⟦box⟧ g.  This last collapse is the pure right-unitor
  -- coherence  merge a {[]} ≈ ρ⇒  (up to a++[]≡a); see report.  We isolate it
  -- as the SINGLE remaining obligation `boxD-sound`.
  --------------------------------------------------------------------------------
  -- Box-leaf soundness obligation, isolated as a hypothesis (it is the pure
  -- right-unitor coherence  merge a {[]} ≈ ρ⇒  up to a++[]≡a — discharged
  -- by `Categories.MonoidalCoherence.Solver.solveM` on the box-free subgoal,
  -- or by an explicit Kelly derivation; both are box-free coherence and so
  -- are independent of the reflection logic below).  See report.
  BoxSound : Set
  BoxSound = ∀ {a b} (g : Mor a b)
           → coeDom (++-identityʳ a) (coeCod' (++-identityʳ b) ⟦ boxD g ⟧)
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

  -- codomain coercion with ARBITRARY domain object (the merge step's domain
  -- `(Var x ⊗₀ wires a) ⊗₀ unit` is not `wires`-shaped), driven by a List eq.
  coeC : ∀ {A} {p q : List X} → p ≡ q → HomTerm A (wires p) → HomTerm A (wires q)
  coeC refl h = h

  coeC-resp : ∀ {A} {p q} (e : p ≡ q) {h h' : HomTerm A (wires p)}
            → h ≈Term h' → coeC e h ≈Term coeC e h'
  coeC-resp refl eq = eq

  -- coeC over `cong (x ∷_) e` factors through `∘` (right factor untouched).
  coeC-∘ : ∀ {A R} (x : X) {p q : List X} (e : p ≡ q)
             (h : HomTerm R (Var x ⊗₀ wires p)) (j : HomTerm A R)
         → coeC (cong (x ∷_) e) (h ∘ j) ≈Term coeC (cong (x ∷_) e) h ∘ j
  coeC-∘ x refl h j = ≈-Term-refl

  -- coeC over `cong (x ∷_) e` pushes under the right factor of  id ⊗₁ _ .
  coeC-id⊗ : ∀ {R} (x : X) {p q : List X} (e : p ≡ q)
               (h : HomTerm R (wires p))
           → coeC (cong (x ∷_) e) (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ coeC e h
  coeC-id⊗ x refl h = ≈-Term-refl

  -- the right-unitor coherence on the flat merge:  merge a {[]} ≈ ρ⇒ (retyped).
  merge-ρ : (a : List X) → coeC {wires a ⊗₀ unit} (++-identityʳ a) (merge a {[]})
                          ≈Term ρ⇒ {wires a}
  merge-ρ []      = λ⇒≈ρ⇒
  merge-ρ (x ∷ a) = begin
    coeC (++-identityʳ (x ∷ a)) (id {Var x} ⊗₁ merge a ∘ α⇒)
      ≈⟨ coeC-∘ x (++-identityʳ a) (id ⊗₁ merge a) α⇒ ⟩
    coeC (cong (x ∷_) (++-identityʳ a)) (id {Var x} ⊗₁ merge a) ∘ α⇒
      ≈⟨ ∘-resp-≈ (coeC-id⊗ x (++-identityʳ a) (merge a)) ≈-Term-refl ⟩
    id {Var x} ⊗₁ coeC (++-identityʳ a) (merge a) ∘ α⇒
      ≈⟨ ∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (merge-ρ a)) ≈-Term-refl ⟩
    id {Var x} ⊗₁ ρ⇒ {wires a} ∘ α⇒
      ≈⟨ idρ∘α≈ρ ⟩
    ρ⇒ ∎

  -- domain coercion with ARBITRARY codomain object, driven by a List eq.
  coeD : ∀ {B} {p q : List X} → p ≡ q → HomTerm (wires p) B → HomTerm (wires q) B
  coeD refl h = h

  coeD-∘ : ∀ {B R} (x : X) {p q : List X} (e : p ≡ q)
             (h : HomTerm R B) (j : HomTerm (Var x ⊗₀ wires p) R)
         → coeD (cong (x ∷_) e) (h ∘ j) ≈Term h ∘ coeD (cong (x ∷_) e) j
  coeD-∘ x refl h j = ≈-Term-refl

  coeD-id⊗ : ∀ {R} (x : X) {p q : List X} (e : p ≡ q)
               (h : HomTerm (wires p) R)
           → coeD (cong (x ∷_) e) (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ coeD e h
  coeD-id⊗ x refl h = ≈-Term-refl

  -- the right-unitor coherence on the flat split:  split a {[]} ≈ ρ⇐ (retyped).
  split-ρ : (a : List X) → coeD {wires a ⊗₀ unit} (++-identityʳ a) (split a {[]})
                          ≈Term ρ⇐ {wires a}
  split-ρ []      = λ⇐≈ρ⇐
  split-ρ (x ∷ a) = begin
    coeD (++-identityʳ (x ∷ a)) (α⇐ ∘ id {Var x} ⊗₁ split a)
      ≈⟨ coeD-∘ x (++-identityʳ a) α⇐ (id ⊗₁ split a) ⟩
    α⇐ ∘ coeD (cong (x ∷_) (++-identityʳ a)) (id {Var x} ⊗₁ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (coeD-id⊗ x (++-identityʳ a) (split a)) ⟩
    α⇐ ∘ id {Var x} ⊗₁ coeD (++-identityʳ a) (split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl (split-ρ a)) ⟩
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

  -- coeCod' (codomain `wires`) agrees with the arbitrary-domain coeC.
  coeCod'≈coeC : ∀ {n p q} (e : p ≡ q) (h : HomTerm (wires n) (wires p))
               → coeCod' e h ≈Term coeC e h
  coeCod'≈coeC refl h = ≈-Term-refl

  -- coeDom (domain `wires`) agrees with the arbitrary-codomain coeD.
  coeDom≈coeD : ∀ {p q r} (e : p ≡ q) (h : HomTerm (wires p) (wires r))
              → coeDom e h ≈Term coeD e h
  coeDom≈coeD refl h = ≈-Term-refl

  -- push coeC through `∘` onto the left (codomain) factor (any inner equality).
  coeC-∘ˡ : ∀ {A R p q} (e : p ≡ q) (h : HomTerm R (wires p)) (j : HomTerm A R)
          → coeC e (h ∘ j) ≈Term coeC e h ∘ j
  coeC-∘ˡ refl h j = ≈-Term-refl

  -- push coeD through `∘` onto the right (domain) factor (any inner equality).
  coeD-∘ʳ : ∀ {B R p q} (e : p ≡ q) (h : HomTerm R B) (j : HomTerm (wires p) R)
          → coeD e (h ∘ j) ≈Term h ∘ coeD e j
  coeD-∘ʳ refl h j = ≈-Term-refl

  boxSound : BoxSound
  boxSound {a} {b} g = begin
    coeDom (++-identityʳ a) (coeCod' (++-identityʳ b) ⟦ boxD g ⟧)
      ≈⟨ coeDom≈coeD (++-identityʳ a) _ ⟩
    coeD (++-identityʳ a) (coeCod' (++-identityʳ b) ⟦ boxD g ⟧)
      ≈⟨ coeD-resp (++-identityʳ a) (coeCod'≈coeC (++-identityʳ b) ⟦ boxD g ⟧) ⟩
    coeD (++-identityʳ a) (coeC (++-identityʳ b) ⟦ boxD g ⟧)
      ≈⟨ coeD-resp (++-identityʳ a) (coeC-resp (++-identityʳ b) idˡ) ⟩
    coeD (++-identityʳ a) (coeC (++-identityʳ b) body)
      ≈⟨ coeD-resp (++-identityʳ a) (coeC-∘ˡ (++-identityʳ b) (merge b) rest) ⟩
    coeD (++-identityʳ a) (coeC (++-identityʳ b) (merge b {[]}) ∘ rest)
      ≈⟨ coeD-∘ʳ (++-identityʳ a) (coeC (++-identityʳ b) (merge b {[]})) rest ⟩
    coeC (++-identityʳ b) (merge b {[]}) ∘ coeD (++-identityʳ a) rest
      ≈⟨ ∘-resp-≈ (merge-ρ b) (coeD-∘ʳ (++-identityʳ a) (⟦box⟧ g ⊗₁ id) (split a {[]})) ⟩
    ρ⇒ ∘ ((⟦box⟧ g ⊗₁ id) ∘ coeD (++-identityʳ a) (split a {[]}))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (split-ρ a)) ⟩
    ρ⇒ ∘ ((⟦box⟧ g ⊗₁ id) ∘ ρ⇐)
      ≈⟨ ≈-Term-sym assoc ⟩
    (ρ⇒ ∘ (⟦box⟧ g ⊗₁ id)) ∘ ρ⇐
      ≈⟨ ∘-resp-≈ ρ⇒∘f⊗id≈f∘ρ⇒ ≈-Term-refl ⟩
    (⟦box⟧ g ∘ ρ⇒) ∘ ρ⇐
      ≈⟨ assoc ⟩
    ⟦box⟧ g ∘ (ρ⇒ ∘ ρ⇐)
      ≈⟨ ∘-resp-≈ ≈-Term-refl ρ⇒∘ρ⇐≈id ⟩
    ⟦box⟧ g ∘ id
      ≈⟨ idʳ ⟩
    ⟦box⟧ g ∎
    where
      rest : HomTerm (wires (a ++ [])) (wires b ⊗₀ wires [])
      rest = (⟦box⟧ g ⊗₁ id {wires []}) ∘ split a {[]}
      body : HomTerm (wires (a ++ [])) (wires (b ++ []))
      body = merge b {[]} ∘ rest
      coeD-resp : ∀ {B p q} (e : p ≡ q) {h h' : HomTerm (wires p) B}
                → h ≈Term h' → coeD e h ≈Term coeD e h'
      coeD-resp refl eq = eq

  --------------------------------------------------------------------------------
  -- TASK 1: soundness of the offset shifts `shiftL` / `shiftR`.
  --
  --   shiftL lt d  is  liftW lt ⟦ d ⟧  up to the +-associativity reindexing
  --   absorbed by the `reidx` wrappers, and analogously for `shiftR`.  We state
  --   them in the codomain-reindexed form (mirroring `∘ᵈ-sound`):
  --     coeCod' (out-shiftL lt d) ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
  --     coeCod' (out-shiftR rt d) ⟦ shiftR rt d ⟧ ≈Term rliftW rt ⟦ d ⟧
  --   where `rliftW` is the suffix flat-shift (defined below).
  --------------------------------------------------------------------------------

  -- liftW of an identity is an identity (functoriality, unit).
  liftW-id : ∀ (p : List X) {u} → liftW p (id {wires u}) ≈Term id
  liftW-id []      = ≈-Term-refl
  liftW-id (x ∷ p) = begin
    id ⊗₁ liftW p id
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (liftW-id p) ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  -- push coeDom through `∘` onto the right (domain) factor (codomain `wires`).
  coeDom-∘ : ∀ {a b r p} (eq : a ≡ b) (h : HomTerm (wires r) (wires p))
               (k : HomTerm (wires a) (wires r))
           → coeDom eq (h ∘ k) ≈Term h ∘ coeDom eq k
  coeDom-∘ refl h k = ≈-Term-refl

  -- coeDom / coeCod' commute with the prefix `id {Var x} ⊗₁ _` along `cong (x ∷_)`.
  coeDom-id⊗ʷ : ∀ (x : X) {p q r} (e : p ≡ q) (h : HomTerm (wires p) (wires r))
              → coeDom (cong (x ∷_) e) (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ coeDom e h
  coeDom-id⊗ʷ x refl h = ≈-Term-refl

  coeCod'-id⊗ʷ : ∀ (x : X) {r p q} (e : p ≡ q) (h : HomTerm (wires r) (wires p))
               → coeCod' (cong (x ∷_) e) (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ coeCod' e h
  coeCod'-id⊗ʷ x refl h = ≈-Term-refl

  -- recast a coeDom / coeCod' along a propositionally-equal index (UIP).
  coeDom-castU : ∀ {p q r} (e e' : p ≡ q) (h : HomTerm (wires p) (wires r))
               → coeDom e h ≈Term coeDom e' h
  coeDom-castU e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
  coeCod'-castU : ∀ {r p q} (e e' : p ≡ q) (h : HomTerm (wires r) (wires p))
                → coeCod' e h ≈Term coeCod' e' h
  coeCod'-castU e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl

  -- `liftW lt (pad pre suf g)` is the wider `pad (lt ++ pre) suf g`, up to the
  -- +-associativity reindex on its endpoints.  This is the layer-level content
  -- of `shiftL`'s `reidx` wrappers.  Proven by induction on `lt`, mirroring
  -- `shiftL`'s own recursion.
  liftW-pad : ∀ {a b} (lt pre suf : List X) (g : HomTerm (wires a) (wires b))
            → liftW lt (pad pre suf g)
              ≈Term coeDom (++-assoc lt pre (a ++ suf))
                      (coeCod' (++-assoc lt pre (b ++ suf))
                        (pad (lt ++ pre) suf g))
  liftW-pad []      pre suf g = ≈-Term-refl
  liftW-pad {a} {b} (x ∷ lt) pre suf g = begin
    id ⊗₁ liftW lt (pad pre suf g)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (liftW-pad lt pre suf g) ⟩
    id {Var x} ⊗₁ coeDom (++-assoc lt pre (a ++ suf))
                    (coeCod' (++-assoc lt pre (b ++ suf)) (pad (lt ++ pre) suf g))
      ≈⟨ ≈-Term-sym (coeDom-id⊗ʷ x (++-assoc lt pre (a ++ suf)) _) ⟩
    coeDom (cong (x ∷_) (++-assoc lt pre (a ++ suf)))
      (id {Var x} ⊗₁ coeCod' (++-assoc lt pre (b ++ suf)) (pad (lt ++ pre) suf g))
      ≈⟨ coeDom-resp _ (≈-Term-sym (coeCod'-id⊗ʷ x (++-assoc lt pre (b ++ suf)) _)) ⟩
    coeDom (cong (x ∷_) (++-assoc lt pre (a ++ suf)))
      (coeCod' (cong (x ∷_) (++-assoc lt pre (b ++ suf))) (id {Var x} ⊗₁ pad (lt ++ pre) suf g))
      ≈⟨ coeDom-castU (cong (x ∷_) (++-assoc lt pre (a ++ suf))) (++-assoc (x ∷ lt) pre (a ++ suf)) _ ⟩
    coeDom (++-assoc (x ∷ lt) pre (a ++ suf))
      (coeCod' (cong (x ∷_) (++-assoc lt pre (b ++ suf))) (id {Var x} ⊗₁ pad (lt ++ pre) suf g))
      ≈⟨ coeDom-resp _ (coeCod'-castU (cong (x ∷_) (++-assoc lt pre (b ++ suf))) (++-assoc (x ∷ lt) pre (b ++ suf)) _) ⟩
    coeDom (++-assoc (x ∷ lt) pre (a ++ suf))
      (coeCod' (++-assoc (x ∷ lt) pre (b ++ suf)) (id {Var x} ⊗₁ pad (lt ++ pre) suf g)) ∎

  -- shiftL soundness.
  shiftL-sound : ∀ {n} (lt : List X) (d : DiagU n)
               → coeCod' (out-shiftL lt d) ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
  shiftL-sound lt ([]_ n) = ≈-Term-sym (liftW-id lt)
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
      -- out (reidx E2 d') ≡ out d'
      eR : out (reidx E2 d') ≡ out d'
      eR = out-reidx E2 d'
      -- the inner shifted layer (before the outer E1 reindex).
      ⟦LAYER⟧ : HomTerm (wires ((lt ++ pre) ++ (a ++ suf))) (wires (out (reidx E2 d')))
      ⟦LAYER⟧ = ⟦ reidx E2 d' ⟧ ∘ pad (lt ++ pre) suf g

      OUTcons : out (shiftL lt (pre ▸ suf ∷ f ⟨ d ⟩)) ≡ lt ++ out (pre ▸ suf ∷ f ⟨ d ⟩)
      OUTcons = out-shiftL lt (pre ▸ suf ∷ f ⟨ d ⟩)

      -- bridge equality used to retype the codomain.
      eBridge : out (reidx E2 d') ≡ lt ++ out d
      eBridge = trans (out-reidx E2 d') (out-shiftL lt d)

      goal : coeCod' OUTcons ⟦ reidx E1 ((lt ++ pre) ▸ suf ∷ f ⟨ reidx E2 d' ⟩) ⟧
             ≈Term liftW lt (⟦ d ⟧ ∘ pad pre suf g)
      goal = begin
        coeCod' OUTcons ⟦ reidx E1 LAYER ⟧
          ≈⟨ coeCod'-resp OUTcons (⟦reidx⟧ E1 LAYER) ⟩
        coeCod' OUTcons (coeDom E1 (coeCod' (sym (out-reidx E1 LAYER)) ⟦LAYER⟧))
          ≈⟨ coe-comm E1 OUTcons _ ⟩
        coeDom E1 (coeCod' OUTcons (coeCod' (sym (out-reidx E1 LAYER)) ⟦LAYER⟧))
          ≈⟨ coeDom-resp E1 (coeCod'-trans (sym (out-reidx E1 LAYER)) OUTcons ⟦LAYER⟧) ⟩
        coeDom E1 (coeCod' (trans (sym (out-reidx E1 LAYER)) OUTcons) ⟦LAYER⟧)
          ≈⟨ coeDom-resp E1 (coeCod'-castB (trans (sym (out-reidx E1 LAYER)) OUTcons) eBridge ⟦LAYER⟧) ⟩
        coeDom E1 (coeCod' eBridge ⟦LAYER⟧)
          ≈⟨ coeDom-resp E1 (coeCod'-∘ eBridge ⟦ reidx E2 d' ⟧ (pad (lt ++ pre) suf g)) ⟩
        coeDom E1 (coeCod' eBridge ⟦ reidx E2 d' ⟧ ∘ pad (lt ++ pre) suf g)
          ≈⟨ coeDom-∘ E1 (coeCod' eBridge ⟦ reidx E2 d' ⟧) (pad (lt ++ pre) suf g) ⟩
        coeCod' eBridge ⟦ reidx E2 d' ⟧ ∘ coeDom E1 (pad (lt ++ pre) suf g)
          ≈⟨ mid-retype eM (coeCod' eBridge ⟦ reidx E2 d' ⟧) (coeDom E1 (pad (lt ++ pre) suf g)) ⟩
        coeDom eM (coeCod' eBridge ⟦ reidx E2 d' ⟧) ∘ coeCod' eM (coeDom E1 (pad (lt ++ pre) suf g))
          ≈⟨ ∘-resp-≈ tailFold padFold ⟩
        liftW lt ⟦ d ⟧ ∘ liftW lt (pad pre suf g)
          ≈⟨ ≈-Term-sym (liftW-∘ lt ⟦ d ⟧ (pad pre suf g)) ⟩
        liftW lt (⟦ d ⟧ ∘ pad pre suf g) ∎
        where
          -- middle-object retype eq:  (lt++pre)++(b++suf) ≡ lt++(pre++(b++suf)).
          eM : (lt ++ pre) ++ (b ++ suf) ≡ lt ++ (pre ++ (b ++ suf))
          eM = ++-assoc lt pre (b ++ suf)
          coeCod'-castB : ∀ {N P Q} (e e' : P ≡ Q) (h : HomTerm (wires N) (wires P))
                        → coeCod' e h ≈Term coeCod' e' h
          coeCod'-castB e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
          coeDom-castB : ∀ {P r} (e e' : P ≡ P) (h : HomTerm (wires P) (wires r))
                       → coeDom e h ≈Term coeDom e' h
          coeDom-castB e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
          coeDom-trans2 : ∀ {p q s r} (e1 : p ≡ q) (e2 : q ≡ s) (h : HomTerm (wires p) (wires r))
                        → coeDom e2 (coeDom e1 h) ≈Term coeDom (trans e1 e2) h
          coeDom-trans2 refl refl h = ≈-Term-refl
          -- retype the middle object of a composite (transports cancel).
          mid-retype : ∀ {N P Q R} (eq : P ≡ Q) (h : HomTerm (wires P) (wires R))
                         (j : HomTerm (wires N) (wires P))
                     → h ∘ j ≈Term coeDom eq h ∘ coeCod' eq j
          mid-retype refl h j = ≈-Term-refl
          -- the tail folds (via reidx-transport + recursion + cancellation of
          -- the eM/E2 coercions) to liftW lt ⟦d⟧.
          tailFold : coeDom eM (coeCod' eBridge ⟦ reidx E2 d' ⟧) ≈Term liftW lt ⟦ d ⟧
          tailFold = begin
            coeDom eM (coeCod' eBridge ⟦ reidx E2 d' ⟧)
              ≈⟨ coeDom-resp eM (coeCod'-resp eBridge (⟦reidx⟧ E2 d')) ⟩
            coeDom eM (coeCod' eBridge (coeDom E2 (coeCod' (sym eR) ⟦ d' ⟧)))
              ≈⟨ coeDom-resp eM (coe-comm E2 eBridge _) ⟩
            coeDom eM (coeDom E2 (coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧)))
              ≈⟨ coeDom-trans2 E2 eM (coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧)) ⟩
            coeDom (trans E2 eM) (coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧))
              ≈⟨ coeDom-castB (trans E2 eM) refl (coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧)) ⟩
            coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧)
              ≈⟨ coeCod'-trans (sym eR) eBridge ⟦ d' ⟧ ⟩
            coeCod' (trans (sym eR) eBridge) ⟦ d' ⟧
              ≈⟨ coeCod'-castB (trans (sym eR) eBridge) (out-shiftL lt d) ⟦ d' ⟧ ⟩
            coeCod' (out-shiftL lt d) ⟦ d' ⟧
              ≈⟨ shiftL-sound lt d ⟩
            liftW lt ⟦ d ⟧ ∎
          padFold : coeCod' eM (coeDom E1 (pad (lt ++ pre) suf g)) ≈Term liftW lt (pad pre suf g)
          padFold = begin
            coeCod' eM (coeDom E1 (pad (lt ++ pre) suf g))
              ≈⟨ coe-comm E1 eM (pad (lt ++ pre) suf g) ⟩
            coeDom E1 (coeCod' eM (pad (lt ++ pre) suf g))
              ≈⟨ ≈-Term-sym (liftW-pad lt pre suf g) ⟩
            liftW lt (pad pre suf g) ∎

  --------------------------------------------------------------------------------
  -- Suffix shift `rliftW` (:= rpad) and its soundness for `shiftR`.
  --------------------------------------------------------------------------------

  -- the suffix flat-shift is exactly `rpad` (append rt idle wires on the right).
  rliftW : (rt : List X) {u v : List X} → HomTerm (wires u) (wires v)
         → HomTerm (wires (u ++ rt)) (wires (v ++ rt))
  rliftW rt {u} {v} W = rpad {u} {v} rt W

  rliftW-resp : ∀ (rt : List X) {u v} {P Q : HomTerm (wires u) (wires v)}
              → P ≈Term Q → rliftW rt P ≈Term rliftW rt Q
  rliftW-resp rt eq = ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ eq ≈-Term-refl) ≈-Term-refl)

  rliftW-id : ∀ (rt : List X) {u} → rliftW rt (id {wires u}) ≈Term id
  rliftW-id rt {u} = begin
    merge u {rt} ∘ (id {wires u} ⊗₁ id {wires rt}) ∘ split u {rt}
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
    merge u {rt} ∘ (id ∘ split u {rt})
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    merge u {rt} ∘ split u {rt}
      ≈⟨ merge∘split u ⟩
    id ∎

  rliftW-∘ : ∀ (rt : List X) {u v w} (P : HomTerm (wires v) (wires w)) (Q : HomTerm (wires u) (wires v))
           → rliftW rt (P ∘ Q) ≈Term rliftW rt P ∘ rliftW rt Q
  rliftW-∘ rt {u} {v} {w} P Q = begin
    merge w ∘ ((P ∘ Q) ⊗₁ id) ∘ split u
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ≈-Term-refl) ⟩
    merge w ∘ ((P ∘ Q) ⊗₁ (id ∘ id)) ∘ split u
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ⊗-∘-dist ≈-Term-refl) ⟩
    merge w ∘ ((P ⊗₁ id ∘ Q ⊗₁ id)) ∘ split u
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-trans (≈-Term-sym idˡ) (∘-resp-≈ (≈-Term-sym (split∘merge v)) ≈-Term-refl))) ≈-Term-refl) ⟩
    merge w ∘ ((P ⊗₁ id ∘ ((split v ∘ merge v) ∘ Q ⊗₁ id))) ∘ split u
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl assoc) ≈-Term-refl) ⟩
    merge w ∘ ((P ⊗₁ id ∘ (split v ∘ (merge v ∘ Q ⊗₁ id)))) ∘ split u
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl) ⟩
    merge w ∘ (((P ⊗₁ id ∘ split v) ∘ (merge v ∘ Q ⊗₁ id))) ∘ split u
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    merge w ∘ ((P ⊗₁ id ∘ split v) ∘ ((merge v ∘ Q ⊗₁ id) ∘ split u))
      ≈⟨ ≈-Term-sym assoc ⟩
    (merge w ∘ (P ⊗₁ id ∘ split v)) ∘ ((merge v ∘ Q ⊗₁ id) ∘ split u)
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    (merge w ∘ (P ⊗₁ id ∘ split v)) ∘ (merge v ∘ (Q ⊗₁ id ∘ split u)) ∎

  -- coeCod' / coeDom respect for ARBITRARY (non-wires) domain / codomain
  -- objects (needed for the merge-associativity coherences, whose ends are
  -- bracketed tensors of wires, not flat).
  coeCA : ∀ {A} {p q : List X} → p ≡ q → HomTerm A (wires p) → HomTerm A (wires q)
  coeCA refl h = h
  coeCA-resp : ∀ {A} {p q} (e : p ≡ q) {h h' : HomTerm A (wires p)}
             → h ≈Term h' → coeCA e h ≈Term coeCA e h'
  coeCA-resp refl eq = eq
  coeCA-∘ : ∀ {A R} {p q} (e : p ≡ q) (h : HomTerm R (wires p)) (j : HomTerm A R)
          → coeCA e (h ∘ j) ≈Term coeCA e h ∘ j
  coeCA-∘ refl h j = ≈-Term-refl
  -- coeCA on a flat (wires-domain) morphism coincides with coeCod'.
  coeCA≈coeCod' : ∀ {N p q} (e : p ≡ q) (h : HomTerm (wires N) (wires p))
                → coeCA e h ≈Term coeCod' e h
  coeCA≈coeCod' refl h = ≈-Term-refl

  -- `merge` associativity (built from `coherence₁` and α-naturality):
  --   merge p {q++r} ∘ (id ⊗₁ merge q {r}) ∘ α⇒
  --     ≈ coeCA (++-assoc p q r) (merge (p++q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))
  merge-assoc : ∀ (p q r : List X)
              → merge p {q ++ r} ∘ (id {wires p} ⊗₁ merge q {r}) ∘ α⇒
                ≈Term coeCA (++-assoc p q r) (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))
  merge-assoc []      q r = begin
    λ⇒ ∘ (id {unit} ⊗₁ merge q {r}) ∘ α⇒
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl ≈-Term-refl) ⟩
    λ⇒ ∘ ((id {unit} ⊗₁ merge q {r}) ∘ α⇒)
      ≈⟨ ≈-Term-sym assoc ⟩
    (λ⇒ ∘ (id {unit} ⊗₁ merge q {r})) ∘ α⇒
      ≈⟨ ∘-resp-≈ λ⇒∘id⊗f≈f∘λ⇒ ≈-Term-refl ⟩
    (merge q {r} ∘ λ⇒) ∘ α⇒
      ≈⟨ assoc ⟩
    merge q {r} ∘ (λ⇒ ∘ α⇒)
      ≈⟨ ∘-resp-≈ ≈-Term-refl λ⇒∘α⇒≈λ⇒⊗id ⟩
    merge q {r} ∘ (λ⇒ ⊗₁ id) ∎
  merge-assoc (x ∷ p) q r = begin
    -- LHS = merge(x∷p){q++r} ∘ (id{wires(x∷p)} ⊗ merge q) ∘ α⇒
    (id {Var x} ⊗₁ merge p {q ++ r} ∘ α⇒ {Var x} {wires p} {wires (q ++ r)})
      ∘ (id {Var x ⊗₀ wires p} ⊗₁ merge q {r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ (≈-Term-sym id⊗id≈id) ≈-Term-refl) ≈-Term-refl) ⟩
    (id {Var x} ⊗₁ merge p {q ++ r} ∘ α⇒ {Var x} {wires p} {wires (q ++ r)})
      ∘ ((id {Var x} ⊗₁ id {wires p}) ⊗₁ merge q {r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
      ≈⟨ ≈-Term-refl ⟩
    (id ⊗₁ merge p ∘ α⇒ {Var x} {wires p} {wires (q ++ r)})
      ∘ (((id ⊗₁ id) ⊗₁ merge q) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r})
      ≈⟨ ≈-Term-sym assoc ⟩
    ((id ⊗₁ merge p ∘ α⇒) ∘ ((id ⊗₁ id) ⊗₁ merge q)) ∘ α⇒
      ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
    (id ⊗₁ merge p ∘ (α⇒ ∘ (id ⊗₁ id) ⊗₁ merge q)) ∘ α⇒
      ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl α-comm) ≈-Term-refl ⟩
    (id ⊗₁ merge p ∘ (id ⊗₁ (id ⊗₁ merge q) ∘ α⇒)) ∘ α⇒
      ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
    ((id ⊗₁ merge p ∘ id ⊗₁ (id ⊗₁ merge q)) ∘ α⇒) ∘ α⇒
      ≈⟨ ∘-resp-≈ (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ≈-Term-refl ⟩
    (((id ∘ id) ⊗₁ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r}))) ∘ α⇒) ∘ α⇒
      ≈⟨ ∘-resp-≈ (∘-resp-≈ (⊗-resp-≈ idˡ ≈-Term-refl) ≈-Term-refl) ≈-Term-refl ⟩
    ((id ⊗₁ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) )
       ∘ α⇒ {Var x} {wires p} {wires q ⊗₀ wires r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
      ≈⟨ pent ⟩
    (id {Var x} ⊗₁ (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) ∘ id {Var x} ⊗₁ α⇒ {wires p} {wires q} {wires r}) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
      ≈⟨ ∘-resp-≈ (id⊗-fuse (merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) (α⇒ {wires p} {wires q} {wires r})) ≈-Term-refl ⟩
    (id {Var x} ⊗₁ ((merge p {q ++ r} ∘ (id ⊗₁ merge q {r})) ∘ α⇒ {wires p} {wires q} {wires r})) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
      ≈⟨ ∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (≈-Term-trans assoc (merge-assoc p q r))) ≈-Term-refl ⟩
    (id ⊗₁ coeCA (++-assoc p q r) (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})))
      ∘ (α⇒ ∘ α⇒ ⊗₁ id)
      ≈⟨ ∘-resp-≈ (push-id⊗-coeCA x (++-assoc p q r) _) ≈-Term-refl ⟩
    coeCA (cong (x ∷_) (++-assoc p q r)) (id ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id)))
      ∘ (α⇒ ∘ α⇒ ⊗₁ id)
      ≈⟨ ≈-Term-sym (coeCA-∘ (cong (x ∷_) (++-assoc p q r)) _ (α⇒ ∘ α⇒ ⊗₁ id)) ⟩
    coeCA (cong (x ∷_) (++-assoc p q r))
      ((id ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id))
      ≈⟨ coeCA-resp _ tailRHS ⟩
    coeCA (cong (x ∷_) (++-assoc p q r))
      (((id ⊗₁ merge (p ++ q) {r}) ∘ α⇒) ∘ ((id ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r}))
      ≈⟨ coeCA-cast (cong (x ∷_) (++-assoc p q r)) (++-assoc (x ∷ p) q r) _ ⟩
    coeCA (++-assoc (x ∷ p) q r)
      (((id ⊗₁ merge (p ++ q) {r}) ∘ α⇒) ∘ ((id ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r})) ∎
    where
      push-id⊗-coeCA : ∀ {R} (x : X) {p' q'} (e : p' ≡ q') (h : HomTerm R (wires p'))
                     → id {Var x} ⊗₁ coeCA e h ≈Term coeCA (cong (x ∷_) e) (id {Var x} ⊗₁ h)
      push-id⊗-coeCA x refl h = ≈-Term-refl
      -- fuse two prefixed-id tensors:  id⊗A ∘ id⊗B ≈ id⊗(A∘B).
      id⊗-fuse : ∀ {Z A B C} (A' : HomTerm B C) (B' : HomTerm A B)
               → id {Z} ⊗₁ A' ∘ id {Z} ⊗₁ B' ≈Term id {Z} ⊗₁ (A' ∘ B')
      id⊗-fuse A' B' = begin
        id ⊗₁ A' ∘ id ⊗₁ B'
          ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
        (id ∘ id) ⊗₁ (A' ∘ B')
          ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
        id ⊗₁ (A' ∘ B') ∎
      coeCA-cast : ∀ {A} {p' q'} (e e' : p' ≡ q') (h : HomTerm A (wires p'))
                 → coeCA e h ≈Term coeCA e' h
      coeCA-cast e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
      -- pentagon rebracketing of the two trailing associators:
      --   (X ∘ α⇒) ∘ α⇒  ≈  (X ∘ id⊗α⇒) ∘ (α⇒ ∘ α⇒⊗id)
      -- where X = id ⊗ (…).  Uses `pentagon`.
      pent : ∀ {B} {X : HomTerm (Var x ⊗₀ (wires p ⊗₀ (wires q ⊗₀ wires r))) B}
           → (X ∘ α⇒ {Var x} {wires p} {wires q ⊗₀ wires r}) ∘ α⇒ {Var x ⊗₀ wires p} {wires q} {wires r}
             ≈Term (X ∘ id {Var x} ⊗₁ α⇒ {wires p} {wires q} {wires r})
                   ∘ (α⇒ {Var x} {wires p ⊗₀ wires q} {wires r} ∘ α⇒ {Var x} {wires p} {wires q} ⊗₁ id {wires r})
      pent {X = X} = begin
        (X ∘ α⇒) ∘ α⇒
          ≈⟨ assoc ⟩
        X ∘ (α⇒ ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym pentagon) ⟩
        X ∘ (id ⊗₁ α⇒ ∘ α⇒ ∘ α⇒ ⊗₁ id)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        X ∘ ((id ⊗₁ α⇒ ∘ α⇒) ∘ α⇒ ⊗₁ id)
          ≈⟨ ≈-Term-sym assoc ⟩
        (X ∘ (id ⊗₁ α⇒ ∘ α⇒)) ∘ α⇒ ⊗₁ id
          ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
        ((X ∘ id ⊗₁ α⇒) ∘ α⇒) ∘ α⇒ ⊗₁ id
          ≈⟨ assoc ⟩
        (X ∘ id ⊗₁ α⇒) ∘ (α⇒ ∘ α⇒ ⊗₁ id) ∎
      -- expand the RHS tail (id⊗(merge(p++q) ∘ (merge p ⊗ id))) ∘ (α⇒ ∘ α⇒⊗id)
      -- into the cons-merge form  (id⊗merge(p++q) ∘ α⇒) ∘ ((id⊗merge p ∘ α⇒)⊗id).
      tailRHS : (id {Var x} ⊗₁ (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})))
                  ∘ (α⇒ {Var x} {wires p ⊗₀ wires q} {wires r}
                     ∘ α⇒ {Var x} {wires p} {wires q} ⊗₁ id {wires r})
              ≈Term ((id {Var x} ⊗₁ merge (p ++ q) {r}) ∘ α⇒)
                    ∘ ((id {Var x} ⊗₁ merge p {q} ∘ α⇒) ⊗₁ id {wires r})
      tailRHS = begin
        (id ⊗₁ (merge (p ++ q) ∘ (merge p ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
          ≈⟨ ∘-resp-≈ (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ≈-Term-refl ⟩
        ((id ∘ id) ⊗₁ (merge (p ++ q) ∘ (merge p ⊗₁ id))) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
          ≈⟨ ∘-resp-≈ ⊗-∘-dist ≈-Term-refl ⟩
        (id ⊗₁ merge (p ++ q) ∘ id ⊗₁ (merge p ⊗₁ id)) ∘ (α⇒ ∘ α⇒ ⊗₁ id)
          ≈⟨ assoc ⟩
        id ⊗₁ merge (p ++ q) ∘ (id ⊗₁ (merge p ⊗₁ id) ∘ (α⇒ ∘ α⇒ ⊗₁ id))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        id ⊗₁ merge (p ++ q) ∘ ((id ⊗₁ (merge p ⊗₁ id) ∘ α⇒) ∘ α⇒ ⊗₁ id)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl) ⟩
        id ⊗₁ merge (p ++ q) ∘ ((α⇒ ∘ (id ⊗₁ merge p) ⊗₁ id) ∘ α⇒ ⊗₁ id)
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        id ⊗₁ merge (p ++ q) ∘ (α⇒ ∘ ((id ⊗₁ merge p) ⊗₁ id ∘ α⇒ ⊗₁ id))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym ⊗-∘-dist)) ⟩
        id ⊗₁ merge (p ++ q) ∘ (α⇒ ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ (id ∘ id)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl idˡ)) ⟩
        id ⊗₁ merge (p ++ q) ∘ (α⇒ ∘ ((id ⊗₁ merge p ∘ α⇒) ⊗₁ id))
          ≈⟨ ≈-Term-sym assoc ⟩
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
      inv-resp {f = f} {g} {fi} {gi} fif ggi f≈g = begin
        fi
          ≈⟨ ≈-Term-sym idʳ ⟩
        fi ∘ id
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym ggi) ⟩
        fi ∘ (g ∘ gi)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym f≈g) ≈-Term-refl) ⟩
        fi ∘ (f ∘ gi)
          ≈⟨ ≈-Term-sym assoc ⟩
        (fi ∘ f) ∘ gi
          ≈⟨ ∘-resp-≈ fif ≈-Term-refl ⟩
        id ∘ gi
          ≈⟨ idˡ ⟩
        gi ∎
      -- fi ∘ mL ≈ id  (mutual inverses, cancelling split∘merge and α⇐∘α⇒).
      fi-f : fi ∘ mL ≈Term id
      fi-f = begin
        (α⇐ ∘ (id ⊗₁ split q) ∘ split p) ∘ (merge p ∘ (id ⊗₁ merge q) ∘ α⇒)
          ≈⟨ assoc ⟩
        α⇐ ∘ (((id ⊗₁ split q) ∘ split p) ∘ (merge p ∘ (id ⊗₁ merge q) ∘ α⇒))
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        α⇐ ∘ ((id ⊗₁ split q) ∘ (split p ∘ (merge p ∘ (id ⊗₁ merge q) ∘ α⇒)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
        α⇐ ∘ ((id ⊗₁ split q) ∘ ((split p ∘ merge p) ∘ ((id ⊗₁ merge q) ∘ α⇒)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge p) ≈-Term-refl)) ⟩
        α⇐ ∘ ((id ⊗₁ split q) ∘ (id ∘ ((id ⊗₁ merge q) ∘ α⇒)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
        α⇐ ∘ ((id ⊗₁ split q) ∘ ((id ⊗₁ merge q) ∘ α⇒))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        α⇐ ∘ (((id ⊗₁ split q) ∘ (id ⊗₁ merge q)) ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
        α⇐ ∘ (((id ∘ id) ⊗₁ (split q ∘ merge q)) ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idˡ (split∘merge q)) ≈-Term-refl) ⟩
        α⇐ ∘ ((id ⊗₁ id) ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
        α⇐ ∘ (id ∘ α⇒)
          ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
        α⇐ ∘ α⇒
          ≈⟨ α⇐∘α⇒≈id ⟩
        id ∎
      -- (coeCA e mR) ∘ (coeD e giU) ≈ id  via mR ∘ giU ≈ id and coercion cancel.
      g-gi : coeCA e mR ∘ coeD e giU ≈Term id
      g-gi = coe-cancel e mR giU mR-giU
        where
          coe-cancel : ∀ {p' q'} (eq : p' ≡ q')
                         (M : HomTerm ((wires p ⊗₀ wires q) ⊗₀ wires r) (wires p'))
                         (N : HomTerm (wires p') ((wires p ⊗₀ wires q) ⊗₀ wires r))
                     → M ∘ N ≈Term id → coeCA eq M ∘ coeD eq N ≈Term id
          coe-cancel refl M N eq = eq
          mR-giU : mR ∘ giU ≈Term id
          mR-giU = begin
            (merge (p ++ q) ∘ (merge p ⊗₁ id)) ∘ ((split p ⊗₁ id) ∘ split (p ++ q))
              ≈⟨ assoc ⟩
            merge (p ++ q) ∘ ((merge p ⊗₁ id) ∘ ((split p ⊗₁ id) ∘ split (p ++ q)))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
            merge (p ++ q) ∘ (((merge p ⊗₁ id) ∘ (split p ⊗₁ id)) ∘ split (p ++ q))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
            merge (p ++ q) ∘ (((merge p ∘ split p) ⊗₁ (id ∘ id)) ∘ split (p ++ q))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ (merge∘split p) idˡ) ≈-Term-refl) ⟩
            merge (p ++ q) ∘ ((id ⊗₁ id) ∘ split (p ++ q))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
            merge (p ++ q) ∘ (id ∘ split (p ++ q))
              ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
            merge (p ++ q) ∘ split (p ++ q)
              ≈⟨ merge∘split (p ++ q) ⟩
            id ∎

  -- invert a coeCA equation:  h ≈ coeCA eq k  ⇒  coeCA (sym eq) h ≈ k.
  coeCA-invert : ∀ {A p q} (eq : p ≡ q) (h : HomTerm A (wires q)) (k : HomTerm A (wires p))
               → h ≈Term coeCA eq k → coeCA (sym eq) h ≈Term k
  coeCA-invert refl h k e = e
  coeD-invert : ∀ {B p q} (eq : p ≡ q) (h : HomTerm (wires q) B) (k : HomTerm (wires p) B)
              → h ≈Term coeD eq k → coeD (sym eq) h ≈Term k
  coeD-invert refl h k e = e

  -- `rpad` suffix-fusion:  rpad rt (rpad suf g) is the wider rpad (suf++rt) g,
  -- up to +-associativity reindex on its endpoints.  This is the base case of
  -- the suffix shift / pad relation.  Assembled from `merge-assoc`/`split-assoc`.
  rpad-fuse : ∀ {a b} (suf rt : List X) (g : HomTerm (wires a) (wires b))
            → rpad rt (rpad suf g)
              ≈Term coeD (sym (++-assoc a suf rt))
                      (coeCA (sym (++-assoc b suf rt)) (rpad (suf ++ rt) g))
  rpad-fuse {a} {b} suf rt g = begin
    merge (b ++ suf) {rt} ∘ ((merge b {suf} ∘ (g ⊗₁ id {wires suf}) ∘ split a {suf}) ⊗₁ id {wires rt}) ∘ split (a ++ suf) {rt}
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ≈-Term-refl) ⟩
    merge (b ++ suf) ∘ ((merge b ∘ ((g ⊗₁ id) ∘ split a)) ⊗₁ (id ∘ id)) ∘ split (a ++ suf)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ⊗-∘-dist ≈-Term-refl) ⟩
    merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ∘ split a) ⊗₁ id) ∘ split (a ++ suf)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ))) ≈-Term-refl) ⟩
    merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ∘ split a) ⊗₁ (id ∘ id)) ∘ split (a ++ suf)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl ⊗-∘-dist) ≈-Term-refl) ⟩
    merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
      ≈⟨ regroup5 ⟩
    (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt}) ∘ (split a ⊗₁ id ∘ split (a ++ suf))
      ≈⟨ ∘-resp-≈ mergeStep (∘-resp-≈ ≈-Term-refl splitStep) ⟩
    coeCA (sym (++-assoc b suf rt)) (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
      ∘ ((g ⊗₁ id) ⊗₁ id)
      ∘ coeD (sym (++-assoc a suf rt)) (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})
      ≈⟨ pull-coe ⟩
    coeD (sym (++-assoc a suf rt))
      (coeCA (sym (++-assoc b suf rt))
        ((merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
          ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
          ∘ (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})))
      ≈⟨ coeD-resp2 (sym (++-assoc a suf rt)) (coeCA-resp (sym (++-assoc b suf rt)) core) ⟩
    coeD (sym (++-assoc a suf rt))
      (coeCA (sym (++-assoc b suf rt)) (rpad (suf ++ rt) g)) ∎
    where
      -- mergeStep:  merge(b++suf)∘(merge b⊗id) ≈ coeCA(sym e_b)(merge b{suf++rt}∘(id⊗merge suf)∘α⇒)
      mergeStep : merge (b ++ suf) {rt} ∘ (merge b {suf} ⊗₁ id {wires rt})
                ≈Term coeCA (sym (++-assoc b suf rt)) (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
      mergeStep = ≈-Term-sym (coeCA-invert (++-assoc b suf rt) _ _ (merge-assoc b suf rt))
      -- splitStep:  (split a⊗id)∘split(a++suf) ≈ coeD(sym e_a)(α⇐∘(id⊗split suf)∘split a{suf++rt})
      splitStep : (split a {suf} ⊗₁ id {wires rt}) ∘ split (a ++ suf) {rt}
                ≈Term coeD (sym (++-assoc a suf rt)) (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})
      splitStep = ≈-Term-sym (coeD-invert (++-assoc a suf rt) _ _ (split-assoc a suf rt))
      coeD-resp2 : ∀ {B p q} (eq : p ≡ q) {h h' : HomTerm (wires p) B}
                 → h ≈Term h' → coeD eq h ≈Term coeD eq h'
      coeD-resp2 refl e = e
      -- bookkeeping regroup of the 5-fold composite.
      regroup5 : merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
               ≈Term (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt}) ∘ (split a ⊗₁ id ∘ split (a ++ suf))
      regroup5 = begin
        merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
          ≈⟨ ≈-Term-sym assoc ⟩
        (merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id))) ∘ split (a ++ suf)
          ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
        ((merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
          ≈⟨ assoc ⟩
        (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ (((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id) ∘ split (a ++ suf))
          ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
        (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id ∘ (split a ⊗₁ id ∘ split (a ++ suf))) ∎
      -- pull the coeCA / coeD coercions out of the composite to the ends.
      pull-coe :
          coeCA (sym (++-assoc b suf rt)) (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
            ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
            ∘ coeD (sym (++-assoc a suf rt)) (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})
        ≈Term coeD (sym (++-assoc a suf rt))
                (coeCA (sym (++-assoc b suf rt))
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
               → coeCA eb L ∘ Mid ∘ coeD ea Rt
                 ≈Term coeD ea (coeCA eb (L ∘ Mid ∘ Rt))
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
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl (∘-resp-≈ midα ≈-Term-refl)) ≈-Term-refl) ⟩
        merge b ∘ ((id ⊗₁ merge suf) ∘ (g ⊗₁ (id {wires suf} ⊗₁ id {wires rt})) ∘ (id ⊗₁ split suf)) ∘ split a
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ midColl ≈-Term-refl) ⟩
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
          coreRegroup = ≈-Term-trans lhsNF (≈-Term-sym rhsNF)
            where
              lhsNF : (m1 ∘ m2 ∘ m3) ∘ (m4 ∘ (m5 ∘ m6 ∘ m7)) ≈Term rNF
              lhsNF = begin
                (m1 ∘ (m2 ∘ m3)) ∘ (m4 ∘ (m5 ∘ (m6 ∘ m7)))
                  ≈⟨ assoc ⟩
                m1 ∘ ((m2 ∘ m3) ∘ (m4 ∘ (m5 ∘ (m6 ∘ m7))))
                  ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
                m1 ∘ (m2 ∘ (m3 ∘ (m4 ∘ (m5 ∘ (m6 ∘ m7))))) ∎
              rhsNF : m1 ∘ ((m2 ∘ (m3 ∘ (m4 ∘ m5)) ∘ m6) ∘ m7) ≈Term rNF
              rhsNF = begin
                m1 ∘ ((m2 ∘ ((m3 ∘ (m4 ∘ m5)) ∘ m6)) ∘ m7)
                  ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
                m1 ∘ (m2 ∘ (((m3 ∘ (m4 ∘ m5)) ∘ m6) ∘ m7))
                  ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
                m1 ∘ (m2 ∘ ((m3 ∘ (m4 ∘ m5)) ∘ (m6 ∘ m7)))
                  ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
                m1 ∘ (m2 ∘ (m3 ∘ ((m4 ∘ m5) ∘ (m6 ∘ m7))))
                  ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc)) ⟩
                m1 ∘ (m2 ∘ (m3 ∘ (m4 ∘ (m5 ∘ (m6 ∘ m7))))) ∎
          -- α⇒ ∘ ((g⊗id)⊗id) ∘ α⇐ ≈ g⊗(id⊗id)
          midα : α⇒ ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt}) ∘ α⇐
               ≈Term g ⊗₁ (id {wires suf} ⊗₁ id {wires rt})
          midα = begin
            α⇒ ∘ ((g ⊗₁ id) ⊗₁ id) ∘ α⇐
              ≈⟨ ≈-Term-sym assoc ⟩
            (α⇒ ∘ (g ⊗₁ id) ⊗₁ id) ∘ α⇐
              ≈⟨ ∘-resp-≈ α-comm ≈-Term-refl ⟩
            (g ⊗₁ (id ⊗₁ id) ∘ α⇒) ∘ α⇐
              ≈⟨ assoc ⟩
            g ⊗₁ (id ⊗₁ id) ∘ (α⇒ ∘ α⇐)
              ≈⟨ ∘-resp-≈ ≈-Term-refl α⇒∘α⇐≈id ⟩
            g ⊗₁ (id ⊗₁ id) ∘ id
              ≈⟨ idʳ ⟩
            g ⊗₁ (id ⊗₁ id) ∎
          -- (id⊗merge suf) ∘ (g⊗(id⊗id)) ∘ (id⊗split suf) ≈ g ⊗ id{suf++rt}
          midColl : (id {wires b} ⊗₁ merge suf {rt}) ∘ (g ⊗₁ (id {wires suf} ⊗₁ id {wires rt})) ∘ (id {wires a} ⊗₁ split suf {rt})
                  ≈Term g ⊗₁ id {wires (suf ++ rt)}
          midColl = begin
            (id ⊗₁ merge suf) ∘ (g ⊗₁ (id ⊗₁ id)) ∘ (id ⊗₁ split suf)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym ⊗-∘-dist) ⟩
            (id ⊗₁ merge suf) ∘ ((g ∘ id) ⊗₁ ((id ⊗₁ id) ∘ split suf))
              ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
            (id ∘ (g ∘ id)) ⊗₁ (merge suf ∘ ((id ⊗₁ id) ∘ split suf))
              ≈⟨ ⊗-resp-≈ (≈-Term-trans idˡ idʳ) (∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl)) ⟩
            g ⊗₁ (merge suf ∘ (id ∘ split suf))
              ≈⟨ ⊗-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
            g ⊗₁ (merge suf {rt} ∘ split suf {rt})
              ≈⟨ ⊗-resp-≈ ≈-Term-refl (merge∘split suf) ⟩
            g ⊗₁ id ∎

  -- rliftW commutes with the prefix `id {Var x} ⊗₁ _` (no coercion needed):
  --   merge(x∷v)∘((id⊗h)⊗id)∘split(x∷u)  ≈  id ⊗ (merge v ∘ (h⊗id) ∘ split u).
  rliftW-id⊗ : ∀ (rt : List X) (x : X) {u v} (h : HomTerm (wires u) (wires v))
             → rliftW rt (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ rliftW rt h
  rliftW-id⊗ rt x {u} {v} h = begin
    (id {Var x} ⊗₁ merge v {rt} ∘ α⇒) ∘ ((id {Var x} ⊗₁ h) ⊗₁ id {wires rt}) ∘ (α⇐ ∘ id {Var x} ⊗₁ split u {rt})
      ≈⟨ reB ⟩
    id {Var x} ⊗₁ merge v {rt} ∘ ((α⇒ ∘ ((id {Var x} ⊗₁ h) ⊗₁ id {wires rt}) ∘ α⇐) ∘ id {Var x} ⊗₁ split u {rt})
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ midα ≈-Term-refl) ⟩
    id {Var x} ⊗₁ merge v {rt} ∘ ((id {Var x} ⊗₁ (h ⊗₁ id {wires rt})) ∘ id {Var x} ⊗₁ split u {rt})
      ≈⟨ ∘-resp-≈ ≈-Term-refl (id⊗-fuse (h ⊗₁ id {wires rt}) (split u {rt})) ⟩
    id {Var x} ⊗₁ merge v {rt} ∘ id {Var x} ⊗₁ ((h ⊗₁ id {wires rt}) ∘ split u {rt})
      ≈⟨ id⊗-fuse (merge v {rt}) ((h ⊗₁ id {wires rt}) ∘ split u {rt}) ⟩
    id {Var x} ⊗₁ (merge v {rt} ∘ ((h ⊗₁ id {wires rt}) ∘ split u {rt})) ∎
    where
      id⊗-fuse : ∀ {Z A B C} (A' : HomTerm B C) (B' : HomTerm A B)
               → id {Z} ⊗₁ A' ∘ id {Z} ⊗₁ B' ≈Term id {Z} ⊗₁ (A' ∘ B')
      id⊗-fuse A' B' = ≈-Term-trans (≈-Term-sym ⊗-∘-dist) (⊗-resp-≈ idˡ ≈-Term-refl)
      -- α⇒ ∘ ((id⊗h)⊗id) ∘ α⇐ ≈ id ⊗ (h⊗id).
      midα : α⇒ ∘ ((id {Var x} ⊗₁ h) ⊗₁ id {wires rt}) ∘ α⇐
           ≈Term id {Var x} ⊗₁ (h ⊗₁ id {wires rt})
      midα = begin
        α⇒ ∘ ((id ⊗₁ h) ⊗₁ id) ∘ α⇐
          ≈⟨ ≈-Term-sym assoc ⟩
        (α⇒ ∘ (id ⊗₁ h) ⊗₁ id) ∘ α⇐
          ≈⟨ ∘-resp-≈ α-comm ≈-Term-refl ⟩
        (id ⊗₁ (h ⊗₁ id) ∘ α⇒) ∘ α⇐
          ≈⟨ assoc ⟩
        id ⊗₁ (h ⊗₁ id) ∘ (α⇒ ∘ α⇐)
          ≈⟨ ∘-resp-≈ ≈-Term-refl α⇒∘α⇐≈id ⟩
        id ⊗₁ (h ⊗₁ id) ∘ id
          ≈⟨ idʳ ⟩
        id ⊗₁ (h ⊗₁ id) ∎
      reB : (id {Var x} ⊗₁ merge v {rt} ∘ α⇒) ∘ ((id {Var x} ⊗₁ h) ⊗₁ id {wires rt}) ∘ (α⇐ ∘ id {Var x} ⊗₁ split u {rt})
          ≈Term id {Var x} ⊗₁ merge v {rt} ∘ ((α⇒ ∘ ((id {Var x} ⊗₁ h) ⊗₁ id {wires rt}) ∘ α⇐) ∘ id {Var x} ⊗₁ split u {rt})
      reB = begin
        (id ⊗₁ merge v ∘ α⇒) ∘ ((id ⊗₁ h) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ split u)
          ≈⟨ assoc ⟩
        id ⊗₁ merge v ∘ (α⇒ ∘ (((id ⊗₁ h) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ split u)))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        id ⊗₁ merge v ∘ ((α⇒ ∘ ((id ⊗₁ h) ⊗₁ id)) ∘ (α⇐ ∘ id ⊗₁ split u))
          ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
        id ⊗₁ merge v ∘ (((α⇒ ∘ ((id ⊗₁ h) ⊗₁ id)) ∘ α⇐) ∘ id ⊗₁ split u)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ assoc ≈-Term-refl) ⟩
        id ⊗₁ merge v ∘ ((α⇒ ∘ ((id ⊗₁ h) ⊗₁ id) ∘ α⇐) ∘ id ⊗₁ split u) ∎

  -- rliftW / pad relation (suffix analogue of liftW-pad), by induction on pre.
  rliftW-pad : ∀ {a b} (pre suf rt : List X) (g : HomTerm (wires a) (wires b))
             → rliftW rt (pad pre suf g)
               ≈Term coeD (sym (reassoc++ pre a suf rt))
                       (coeCA (sym (reassoc++ pre b suf rt)) (pad pre (suf ++ rt) g))
  rliftW-pad {a} {b} []      suf rt g = begin
    rliftW rt (rpad suf g)
      ≈⟨ rpad-fuse suf rt g ⟩
    coeD (sym (++-assoc a suf rt)) (coeCA (sym (++-assoc b suf rt)) (rpad (suf ++ rt) g))
      ≈⟨ castD (sym (++-assoc a suf rt)) (sym (reassoc++ [] a suf rt)) _ ⟩
    coeD (sym (reassoc++ [] a suf rt)) (coeCA (sym (++-assoc b suf rt)) (rpad (suf ++ rt) g))
      ≈⟨ castD-resp _ (castCA (sym (++-assoc b suf rt)) (sym (reassoc++ [] b suf rt)) _) ⟩
    coeD (sym (reassoc++ [] a suf rt)) (coeCA (sym (reassoc++ [] b suf rt)) (rpad (suf ++ rt) g)) ∎
    where
      castD : ∀ {B p q} (e e' : p ≡ q) (h : HomTerm (wires p) B) → coeD e h ≈Term coeD e' h
      castD e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
      castCA : ∀ {A p q} (e e' : p ≡ q) (h : HomTerm A (wires p)) → coeCA e h ≈Term coeCA e' h
      castCA e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
      castD-resp : ∀ {B p q} (e : p ≡ q) {h h' : HomTerm (wires p) B} → h ≈Term h' → coeD e h ≈Term coeD e h'
      castD-resp refl e = e
  rliftW-pad {a} {b} (x ∷ p) suf rt g = begin
    rliftW rt (id {Var x} ⊗₁ pad p suf g)
      ≈⟨ rliftW-id⊗ rt x (pad p suf g) ⟩
    id {Var x} ⊗₁ rliftW rt (pad p suf g)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (rliftW-pad p suf rt g) ⟩
    id {Var x} ⊗₁ coeD (sym (reassoc++ p a suf rt)) (coeCA (sym (reassoc++ p b suf rt)) (pad p (suf ++ rt) g))
      ≈⟨ ≈-Term-sym (push-id⊗-coeD x (sym (reassoc++ p a suf rt)) _) ⟩
    coeD (cong (x ∷_) (sym (reassoc++ p a suf rt))) (id {Var x} ⊗₁ coeCA (sym (reassoc++ p b suf rt)) (pad p (suf ++ rt) g))
      ≈⟨ coeD-resp3 _ (≈-Term-sym (push-id⊗-coeCA2 x (sym (reassoc++ p b suf rt)) _)) ⟩
    coeD (cong (x ∷_) (sym (reassoc++ p a suf rt)))
      (coeCA (cong (x ∷_) (sym (reassoc++ p b suf rt))) (id {Var x} ⊗₁ pad p (suf ++ rt) g))
      ≈⟨ coeD-castE (cong (x ∷_) (sym (reassoc++ p a suf rt))) (sym (reassoc++ (x ∷ p) a suf rt)) _ ⟩
    coeD (sym (reassoc++ (x ∷ p) a suf rt))
      (coeCA (cong (x ∷_) (sym (reassoc++ p b suf rt))) (id {Var x} ⊗₁ pad p (suf ++ rt) g))
      ≈⟨ coeD-resp3 _ (coeCA-castE (cong (x ∷_) (sym (reassoc++ p b suf rt))) (sym (reassoc++ (x ∷ p) b suf rt)) _) ⟩
    coeD (sym (reassoc++ (x ∷ p) a suf rt))
      (coeCA (sym (reassoc++ (x ∷ p) b suf rt)) (id {Var x} ⊗₁ pad p (suf ++ rt) g)) ∎
    where
      push-id⊗-coeD : ∀ (x : X) {p' q' B} (e : p' ≡ q') (h : HomTerm (wires p') B)
                    → coeD (cong (x ∷_) e) (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ coeD e h
      push-id⊗-coeD x refl h = ≈-Term-refl
      push-id⊗-coeCA2 : ∀ (x : X) {R p' q'} (e : p' ≡ q') (h : HomTerm R (wires p'))
                      → coeCA (cong (x ∷_) e) (id {Var x} ⊗₁ h) ≈Term id {Var x} ⊗₁ coeCA e h
      push-id⊗-coeCA2 x refl h = ≈-Term-refl
      coeD-resp3 : ∀ {p' q' B} (e : p' ≡ q') {h h' : HomTerm (wires p') B}
                 → h ≈Term h' → coeD e h ≈Term coeD e h'
      coeD-resp3 refl e = e
      coeD-castE : ∀ {p' q' B} (e e' : p' ≡ q') (h : HomTerm (wires p') B)
                 → coeD e h ≈Term coeD e' h
      coeD-castE e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
      coeCA-castE : ∀ {A p' q'} (e e' : p' ≡ q') (h : HomTerm A (wires p'))
                  → coeCA e h ≈Term coeCA e' h
      coeCA-castE e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl

  -- shiftR soundness:  coeCod' (out-shiftR rt d) ⟦ shiftR rt d ⟧ ≈ rliftW rt ⟦ d ⟧.
  shiftR-sound : ∀ {n} (rt : List X) (d : DiagU n)
               → coeCod' (out-shiftR rt d) ⟦ shiftR rt d ⟧ ≈Term rliftW rt ⟦ d ⟧
  shiftR-sound rt ([]_ n) = ≈-Term-sym (rliftW-id rt)
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
      eR : out (reidx E2 d') ≡ out d'
      eR = out-reidx E2 d'
      ⟦LAYER⟧ : HomTerm (wires (pre ++ (a ++ (suf ++ rt)))) (wires (out (reidx E2 d')))
      ⟦LAYER⟧ = ⟦ reidx E2 d' ⟧ ∘ pad pre (suf ++ rt) g
      OUTcons : out (shiftR rt (pre ▸ suf ∷ f ⟨ d ⟩)) ≡ out (pre ▸ suf ∷ f ⟨ d ⟩) ++ rt
      OUTcons = out-shiftR rt (pre ▸ suf ∷ f ⟨ d ⟩)
      eBridge : out (reidx E2 d') ≡ out d ++ rt
      eBridge = trans (out-reidx E2 d') (out-shiftR rt d)
      -- middle-object retype eq:  (pre++(b++suf))++rt ≡ pre++(b++(suf++rt)).
      eM : (pre ++ (b ++ suf)) ++ rt ≡ pre ++ (b ++ (suf ++ rt))
      eM = reassoc++ pre b suf rt
      goal : coeCod' OUTcons ⟦ reidx (sym E1) ((pre ▸ (suf ++ rt) ∷ f ⟨ reidx E2 d' ⟩)) ⟧
             ≈Term rliftW rt (⟦ d ⟧ ∘ pad pre suf g)
      goal = begin
        coeCod' OUTcons ⟦ reidx (sym E1) LAYER ⟧
          ≈⟨ coeCod'-resp OUTcons (⟦reidx⟧ (sym E1) LAYER) ⟩
        coeCod' OUTcons (coeDom (sym E1) (coeCod' (sym (out-reidx (sym E1) LAYER)) ⟦LAYER⟧))
          ≈⟨ coe-comm (sym E1) OUTcons _ ⟩
        coeDom (sym E1) (coeCod' OUTcons (coeCod' (sym (out-reidx (sym E1) LAYER)) ⟦LAYER⟧))
          ≈⟨ coeDom-resp (sym E1) (coeCod'-trans (sym (out-reidx (sym E1) LAYER)) OUTcons ⟦LAYER⟧) ⟩
        coeDom (sym E1) (coeCod' (trans (sym (out-reidx (sym E1) LAYER)) OUTcons) ⟦LAYER⟧)
          ≈⟨ coeDom-resp (sym E1) (coeCod'-castR (trans (sym (out-reidx (sym E1) LAYER)) OUTcons) eBridge ⟦LAYER⟧) ⟩
        coeDom (sym E1) (coeCod' eBridge ⟦LAYER⟧)
          ≈⟨ coeDom-resp (sym E1) (coeCod'-∘ eBridge ⟦ reidx E2 d' ⟧ (pad pre (suf ++ rt) g)) ⟩
        coeDom (sym E1) (coeCod' eBridge ⟦ reidx E2 d' ⟧ ∘ pad pre (suf ++ rt) g)
          ≈⟨ coeDom-∘R (sym E1) (coeCod' eBridge ⟦ reidx E2 d' ⟧) (pad pre (suf ++ rt) g) ⟩
        coeCod' eBridge ⟦ reidx E2 d' ⟧ ∘ coeDom (sym E1) (pad pre (suf ++ rt) g)
          ≈⟨ mid-retype eMrev (coeCod' eBridge ⟦ reidx E2 d' ⟧) (coeDom (sym E1) (pad pre (suf ++ rt) g)) ⟩
        coeDom eMrev (coeCod' eBridge ⟦ reidx E2 d' ⟧) ∘ coeCod' eMrev (coeDom (sym E1) (pad pre (suf ++ rt) g))
          ≈⟨ ∘-resp-≈ tailFold padFold ⟩
        rliftW rt ⟦ d ⟧ ∘ rliftW rt (pad pre suf g)
          ≈⟨ ≈-Term-sym (rliftW-∘ rt ⟦ d ⟧ (pad pre suf g)) ⟩
        rliftW rt (⟦ d ⟧ ∘ pad pre suf g) ∎
        where
          -- middle retype eq:  out(reidx E2 d') = out d ++ rt side
          --  domain of left factor = pre++(b++(suf++rt)); we retype it to
          --  (pre++(b++suf))++rt to match rliftW rt ⟦d⟧ domain.
          eMrev : pre ++ (b ++ (suf ++ rt)) ≡ (pre ++ (b ++ suf)) ++ rt
          eMrev = sym eM
          coeCod'-castR : ∀ {N P Q} (e e' : P ≡ Q) (h : HomTerm (wires N) (wires P))
                        → coeCod' e h ≈Term coeCod' e' h
          coeCod'-castR e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
          coeDom-∘R : ∀ {a' b' r p} (eq : a' ≡ b') (h : HomTerm (wires r) (wires p))
                        (k : HomTerm (wires a') (wires r))
                    → coeDom eq (h ∘ k) ≈Term h ∘ coeDom eq k
          coeDom-∘R refl h k = ≈-Term-refl
          mid-retype : ∀ {N P Q R} (eq : P ≡ Q) (h : HomTerm (wires P) (wires R))
                         (j : HomTerm (wires N) (wires P))
                     → h ∘ j ≈Term coeDom eq h ∘ coeCod' eq j
          mid-retype refl h j = ≈-Term-refl
          coeDom-trans2 : ∀ {p q s r} (e1 : p ≡ q) (e2 : q ≡ s) (h : HomTerm (wires p) (wires r))
                        → coeDom e2 (coeDom e1 h) ≈Term coeDom (trans e1 e2) h
          coeDom-trans2 refl refl h = ≈-Term-refl
          coeDom-castR : ∀ {P r} (e e' : P ≡ P) (h : HomTerm (wires P) (wires r))
                       → coeDom e h ≈Term coeDom e' h
          coeDom-castR e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
          tailFold : coeDom eMrev (coeCod' eBridge ⟦ reidx E2 d' ⟧) ≈Term rliftW rt ⟦ d ⟧
          tailFold = begin
            coeDom eMrev (coeCod' eBridge ⟦ reidx E2 d' ⟧)
              ≈⟨ coeDom-resp eMrev (coeCod'-resp eBridge (⟦reidx⟧ E2 d')) ⟩
            coeDom eMrev (coeCod' eBridge (coeDom E2 (coeCod' (sym eR) ⟦ d' ⟧)))
              ≈⟨ coeDom-resp eMrev (coe-comm E2 eBridge _) ⟩
            coeDom eMrev (coeDom E2 (coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧)))
              ≈⟨ coeDom-trans2 E2 eMrev (coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧)) ⟩
            coeDom (trans E2 eMrev) (coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧))
              ≈⟨ coeDom-castR (trans E2 eMrev) refl (coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧)) ⟩
            coeCod' eBridge (coeCod' (sym eR) ⟦ d' ⟧)
              ≈⟨ coeCod'-trans (sym eR) eBridge ⟦ d' ⟧ ⟩
            coeCod' (trans (sym eR) eBridge) ⟦ d' ⟧
              ≈⟨ coeCod'-castR (trans (sym eR) eBridge) (out-shiftR rt d) ⟦ d' ⟧ ⟩
            coeCod' (out-shiftR rt d) ⟦ d' ⟧
              ≈⟨ shiftR-sound rt d ⟩
            rliftW rt ⟦ d ⟧ ∎
          padFold : coeCod' eMrev (coeDom (sym E1) (pad pre (suf ++ rt) g)) ≈Term rliftW rt (pad pre suf g)
          padFold = begin
            coeCod' eMrev (coeDom (sym E1) (pad pre (suf ++ rt) g))
              ≈⟨ swap eMrev (sym E1) (pad pre (suf ++ rt) g) ⟩
            coeD (sym E1) (coeCA eMrev (pad pre (suf ++ rt) g))
              ≈⟨ ≈-Term-sym (rliftW-pad pre suf rt g) ⟩
            rliftW rt (pad pre suf g) ∎
            where
              -- coeCod' (codomain) and coeDom (domain) are coeCA / coeD and commute.
              swap : ∀ {p q p' q'} (ec : p ≡ q) (ed : p' ≡ q')
                       (h : HomTerm (wires p') (wires p))
                   → coeCod' ec (coeDom ed h) ≈Term coeD ed (coeCA ec h)
              swap refl refl h = ≈-Term-refl

  --------------------------------------------------------------------------------
  -- tensorD soundness (pure bifunctoriality, no σ):
  --   coeCod' (out-tensorD dl dr) ⟦ tensorD dl dr ⟧
  --     ≈ merge (out dl) ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl
  -- the wire-grouping bridge between `wires nl ⊗₀ wires nr` and `wires (nl++nr)`.
  --------------------------------------------------------------------------------
  tensorD-sound : ∀ {nl nr} (dl : DiagU nl) (dr : DiagU nr)
                → coeCod' (out-tensorD dl dr) ⟦ tensorD dl dr ⟧
                  ≈Term merge (out dl) {out dr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr}
  tensorD-sound {nl} {nr} dl dr = begin
    coeCod' (out-tensorD dl dr) ⟦ shiftR nr dl ∘ᵈ d2 ⟧
      ≈⟨ coeCod'-uipT (out-tensorD dl dr) (trans (out-∘ᵈ (shiftR nr dl) d2) eBr) ⟦ shiftR nr dl ∘ᵈ d2 ⟧ ⟩
    coeCod' (trans (out-∘ᵈ (shiftR nr dl) d2) eBr) ⟦ shiftR nr dl ∘ᵈ d2 ⟧
      ≈⟨ ≈-Term-sym (coeCod'-trans (out-∘ᵈ (shiftR nr dl) d2) eBr ⟦ shiftR nr dl ∘ᵈ d2 ⟧) ⟩
    coeCod' eBr (coeCod' (out-∘ᵈ (shiftR nr dl) d2) ⟦ shiftR nr dl ∘ᵈ d2 ⟧)
      ≈⟨ coeCod'-resp eBr (∘ᵈ-sound (shiftR nr dl) d2) ⟩
    coeCod' eBr (⟦ d2 ⟧ ∘ ⟦ shiftR nr dl ⟧)
      ≈⟨ coeCod'-∘ eBr ⟦ d2 ⟧ ⟦ shiftR nr dl ⟧ ⟩
    coeCod' eBr ⟦ d2 ⟧ ∘ ⟦ shiftR nr dl ⟧
      ≈⟨ mid-retype eSR (coeCod' eBr ⟦ d2 ⟧) ⟦ shiftR nr dl ⟧ ⟩
    coeDom eSR (coeCod' eBr ⟦ d2 ⟧) ∘ coeCod' eSR ⟦ shiftR nr dl ⟧
      ≈⟨ ∘-resp-≈ d2Fold shiftRfold ⟩
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
      coeCod'-uipT : ∀ {N P} (e e' : P ≡ out dl ++ out dr) (h : HomTerm (wires N) (wires P))
                   → coeCod' e h ≈Term coeCod' e' h
      coeCod'-uipT e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
      -- retype the middle object `out (shiftR nr dl)` ≡ `out dl ++ nr`.
      mid-retype : ∀ {N P Q R} (eq : P ≡ Q) (h : HomTerm (wires P) (wires R))
                     (j : HomTerm (wires N) (wires P))
                 → h ∘ j ≈Term coeDom eq h ∘ coeCod' eq j
      mid-retype refl h j = ≈-Term-refl
      -- ⟦ shiftR nr dl ⟧, codomain-retyped, folds to rliftW nr ⟦dl⟧.
      shiftRfold : coeCod' eSR ⟦ shiftR nr dl ⟧
                 ≈Term merge (out dl) {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr}
      shiftRfold = shiftR-sound nr dl
      -- coeDom eSR (coeCod' eBr ⟦ d2 ⟧) folds to liftW (out dl) ⟦dr⟧ = bridge form.
      d2Fold : coeDom eSR (coeCod' eBr ⟦ d2 ⟧)
             ≈Term merge (out dl) {out dr} ∘ (id {wires (out dl)} ⊗₁ ⟦ dr ⟧) ∘ split (out dl) {nr}
      d2Fold = begin
        coeDom eSR (coeCod' eBr ⟦ d2 ⟧)
          ≈⟨ coeDom-resp eSR (coeCod'-resp eBr (⟦reidx⟧ (sym (out-shiftR nr dl)) (shiftL (out dl) dr))) ⟩
        coeDom eSR (coeCod' eBr (coeDom (sym eSR) (coeCod' (sym eR2) ⟦ shiftL (out dl) dr ⟧)))
          ≈⟨ coeDom-resp eSR (coe-comm (sym eSR) eBr _) ⟩
        coeDom eSR (coeDom (sym eSR) (coeCod' eBr (coeCod' (sym eR2) ⟦ shiftL (out dl) dr ⟧)))
          ≈⟨ coeDom-trans2T (sym eSR) eSR (coeCod' eBr (coeCod' (sym eR2) ⟦ shiftL (out dl) dr ⟧)) ⟩
        coeDom (trans (sym eSR) eSR) (coeCod' eBr (coeCod' (sym eR2) ⟦ shiftL (out dl) dr ⟧))
          ≈⟨ coeDom-castT (trans (sym eSR) eSR) refl (coeCod' eBr (coeCod' (sym eR2) ⟦ shiftL (out dl) dr ⟧)) ⟩
        coeCod' eBr (coeCod' (sym eR2) ⟦ shiftL (out dl) dr ⟧)
          ≈⟨ coeCod'-trans (sym eR2) eBr ⟦ shiftL (out dl) dr ⟧ ⟩
        coeCod' (trans (sym eR2) eBr) ⟦ shiftL (out dl) dr ⟧
          ≈⟨ coeCod'-castT (trans (sym eR2) eBr) (out-shiftL (out dl) dr) ⟦ shiftL (out dl) dr ⟧ ⟩
        coeCod' (out-shiftL (out dl) dr) ⟦ shiftL (out dl) dr ⟧
          ≈⟨ shiftL-sound (out dl) dr ⟩
        liftW (out dl) ⟦ dr ⟧
          ≈⟨ liftW-merge (out dl) ⟦ dr ⟧ ⟩
        merge (out dl) {out dr} ∘ (id {wires (out dl)} ⊗₁ ⟦ dr ⟧) ∘ split (out dl) {nr} ∎
        where
          coeCod'-castT : ∀ {N P Q} (e e' : P ≡ Q) (h : HomTerm (wires N) (wires P))
                        → coeCod' e h ≈Term coeCod' e' h
          coeCod'-castT e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
          coeDom-trans2T : ∀ {p q s r} (e1 : p ≡ q) (e2 : q ≡ s) (h : HomTerm (wires p) (wires r))
                         → coeDom e2 (coeDom e1 h) ≈Term coeDom (trans e1 e2) h
          coeDom-trans2T refl refl h = ≈-Term-refl
          coeDom-castT : ∀ {P r} (e e' : P ≡ P) (h : HomTerm (wires P) (wires r))
                       → coeDom e h ≈Term coeDom e' h
          coeDom-castT e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
      -- the central bifunctoriality collapse.
      collapse :
          (merge (out dl) {out dr} ∘ (id {wires (out dl)} ⊗₁ ⟦ dr ⟧) ∘ split (out dl) {nr})
            ∘ (merge (out dl) {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr})
        ≈Term merge (out dl) {out dr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr}
      collapse = begin
        (merge (out dl) ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split (out dl)) ∘ (merge (out dl) ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
          ≈⟨ regroupT ⟩
        merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ (split (out dl) ∘ merge (out dl)) ∘ (⟦ dl ⟧ ⊗₁ id)) ∘ split nl
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge (out dl)) ≈-Term-refl)) ≈-Term-refl) ⟩
        merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ (id ∘ (⟦ dl ⟧ ⊗₁ id))) ∘ split nl
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl idˡ) ≈-Term-refl) ⟩
        merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ (⟦ dl ⟧ ⊗₁ id)) ∘ split nl
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
        merge (out dl) ∘ ((id ∘ ⟦ dl ⟧) ⊗₁ (⟦ dr ⟧ ∘ id)) ∘ split nl
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idˡ idʳ) ≈-Term-refl) ⟩
        merge (out dl) ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl ∎
        where
          regroupT :
              (merge (out dl) ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split (out dl)) ∘ (merge (out dl) ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
            ≈Term merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ (split (out dl) ∘ merge (out dl)) ∘ (⟦ dl ⟧ ⊗₁ id)) ∘ split nl
          regroupT = begin
            (merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ split (out dl))) ∘ (merge (out dl) ∘ ((⟦ dl ⟧ ⊗₁ id) ∘ split nl))
              ≈⟨ assoc ⟩
            merge (out dl) ∘ (((id ⊗₁ ⟦ dr ⟧) ∘ split (out dl)) ∘ (merge (out dl) ∘ ((⟦ dl ⟧ ⊗₁ id) ∘ split nl)))
              ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
            merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ (split (out dl) ∘ (merge (out dl) ∘ ((⟦ dl ⟧ ⊗₁ id) ∘ split nl))))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
            merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ ((split (out dl) ∘ merge (out dl)) ∘ ((⟦ dl ⟧ ⊗₁ id) ∘ split nl)))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
            merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ (((split (out dl) ∘ merge (out dl)) ∘ (⟦ dl ⟧ ⊗₁ id)) ∘ split nl))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
            merge (out dl) ∘ (((id ⊗₁ ⟦ dr ⟧) ∘ ((split (out dl) ∘ merge (out dl)) ∘ (⟦ dl ⟧ ⊗₁ id))) ∘ split nl)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl) ⟩
            merge (out dl) ∘ ((((id ⊗₁ ⟦ dr ⟧) ∘ (split (out dl) ∘ merge (out dl))) ∘ (⟦ dl ⟧ ⊗₁ id)) ∘ split nl)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ assoc ≈-Term-refl) ⟩
            merge (out dl) ∘ (((id ⊗₁ ⟦ dr ⟧) ∘ (split (out dl) ∘ merge (out dl)) ∘ (⟦ dl ⟧ ⊗₁ id)) ∘ split nl)
              ≈⟨ ≈-Term-sym assoc ⟩
            (merge (out dl) ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ (split (out dl) ∘ merge (out dl)) ∘ (⟦ dl ⟧ ⊗₁ id))) ∘ split nl
              ≈⟨ assoc ⟩
            merge (out dl) ∘ (((id ⊗₁ ⟦ dr ⟧) ∘ (split (out dl) ∘ merge (out dl)) ∘ (⟦ dl ⟧ ⊗₁ id)) ∘ split nl) ∎

  --   coeCod' (out-reflect t) ⟦ reflect t ⟧  ≈Term  embed t
  -- i.e. the reflected diagram, with its codomain reindexed to match, equals
  -- the original wire-fragment morphism.
  --------------------------------------------------------------------------------
  reflect-sound : BoxSound → ∀ {n m} (t : WTerm n m)
                → coeCod' (out-reflect t) ⟦ reflect t ⟧ ≈Term embed t
  reflect-sound bs idʷ = ≈-Term-refl
  reflect-sound bs (_∘ʷ_ {n} {m} {k} g f) = goal
    where
      -- abbreviations
      df = reflect f
      dg = reflect g
      ef = out-reflect f                -- out df ≡ m
      dg' = reidx (sym ef) dg           -- DiagU (out df)
      eg' = out-reidx (sym ef) dg       -- out dg' ≡ out dg
      -- step 1: push coeCod' through ∘ᵈ-sound.
      goal : coeCod' (out-reflect (g ∘ʷ f)) ⟦ df ∘ᵈ dg' ⟧ ≈Term embed g ∘ embed f
      goal = begin
        coeCod' (out-reflect (g ∘ʷ f)) ⟦ df ∘ᵈ dg' ⟧
          ≈⟨ coeCod'-uip (out-reflect (g ∘ʷ f)) (trans (out-∘ᵈ df dg') eg-bridge) ⟦ df ∘ᵈ dg' ⟧ ⟩
        coeCod' (trans (out-∘ᵈ df dg') eg-bridge) ⟦ df ∘ᵈ dg' ⟧
          ≈⟨ ≈-Term-sym (coeCod'-trans (out-∘ᵈ df dg') eg-bridge ⟦ df ∘ᵈ dg' ⟧) ⟩
        coeCod' eg-bridge (coeCod' (out-∘ᵈ df dg') ⟦ df ∘ᵈ dg' ⟧)
          ≈⟨ coeCod'-resp eg-bridge (∘ᵈ-sound df dg') ⟩
        coeCod' eg-bridge (⟦ dg' ⟧ ∘ ⟦ df ⟧)
          ≈⟨ coeCod'-∘ eg-bridge ⟦ dg' ⟧ ⟦ df ⟧ ⟩
        coeCod' eg-bridge ⟦ dg' ⟧ ∘ ⟦ df ⟧
          ≈⟨ mid-retype ef (coeCod' eg-bridge ⟦ dg' ⟧) ⟦ df ⟧ ⟩
        coeDom ef (coeCod' eg-bridge ⟦ dg' ⟧) ∘ coeCod' ef ⟦ df ⟧
          ≈⟨ ∘-resp-≈ dg'-sound df-sound ⟩
        embed g ∘ embed f ∎
        where
          -- bridge:  out dg' ≡ k   (out dg' = out (reidx (sym ef) dg) ≡ out dg ≡ k)
          eg-bridge : out dg' ≡ k
          eg-bridge = trans (out-reidx (sym ef) dg) (out-reflect g)
          -- any two codomain coercions with the same source & target agree (UIP).
          coeCod'-uip : ∀ {N P} (e e' : P ≡ k) (h : HomTerm (wires N) (wires P))
                      → coeCod' e h ≈Term coeCod' e' h
          coeCod'-uip e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
          -- retype the middle object of a composite (transports cancel).
          mid-retype : ∀ {N P Q} (eq : P ≡ Q) (h : HomTerm (wires P) (wires k))
                         (j : HomTerm (wires N) (wires P))
                     → h ∘ j ≈Term coeDom eq h ∘ coeCod' eq j
          mid-retype refl h j = ≈-Term-refl
          dg'-sound : coeDom ef (coeCod' eg-bridge ⟦ dg' ⟧) ≈Term embed g
          dg'-sound = begin
            coeDom ef (coeCod' eg-bridge ⟦ dg' ⟧)
              ≈⟨ coeDom-resp ef (coeCod'-resp eg-bridge (⟦reidx⟧ (sym ef) dg)) ⟩
            coeDom ef (coeCod' eg-bridge (coeDom (sym ef) (coeCod' (sym eg') ⟦ dg ⟧)))
              ≈⟨ coeDom-resp ef (coe-comm (sym ef) eg-bridge (coeCod' (sym eg') ⟦ dg ⟧)) ⟩
            coeDom ef (coeDom (sym ef) (coeCod' eg-bridge (coeCod' (sym eg') ⟦ dg ⟧)))
              ≈⟨ coeDom-trans (sym ef) ef (coeCod' eg-bridge (coeCod' (sym eg') ⟦ dg ⟧)) ⟩
            coeDom (trans (sym ef) ef) (coeCod' eg-bridge (coeCod' (sym eg') ⟦ dg ⟧))
              ≈⟨ coeDom-cast (trans (sym ef) ef) refl (coeCod' eg-bridge (coeCod' (sym eg') ⟦ dg ⟧)) ⟩
            coeCod' eg-bridge (coeCod' (sym eg') ⟦ dg ⟧)
              ≈⟨ coeCod'-trans (sym eg') eg-bridge ⟦ dg ⟧ ⟩
            coeCod' (trans (sym eg') eg-bridge) ⟦ dg ⟧
              ≈⟨ coeCod'-cast (trans (sym eg') eg-bridge) (out-reflect g) ⟦ dg ⟧ ⟩
            coeCod' (out-reflect g) ⟦ dg ⟧
              ≈⟨ reflect-sound bs g ⟩
            embed g ∎
            where
              coeCod'-cast : ∀ {N P} (e e' : P ≡ k) (h : HomTerm (wires N) (wires P))
                           → coeCod' e h ≈Term coeCod' e' h
              coeCod'-cast e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
              -- collapse two stacked domain coercions.
              coeDom-trans : ∀ {a b c p} (e1 : a ≡ b) (e2 : b ≡ c) (h : HomTerm (wires a) (wires p))
                           → coeDom e2 (coeDom e1 h) ≈Term coeDom (trans e1 e2) h
              coeDom-trans refl refl h = ≈-Term-refl
              -- recast a domain coe along a propositionally-equal (UIP) eq.
              coeDom-cast : ∀ {N} (e e' : m ≡ m) (h : HomTerm (wires m) (wires N))
                          → coeDom e h ≈Term coeDom e' h
              coeDom-cast e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
          df-sound : coeCod' ef ⟦ df ⟧ ≈Term embed f
          df-sound = reflect-sound bs f
  reflect-sound bs (boxʷ {a} {b} g) = goal
    where
      goal : coeCod' (out-reflect (boxʷ g)) ⟦ reflect (boxʷ g) ⟧ ≈Term ⟦box⟧ g
      goal = begin
        coeCod' (out-reflect (boxʷ g)) ⟦ reidx (++-identityʳ a) (boxD g) ⟧
          ≈⟨ coeCod'-resp _ (⟦reidx⟧ (++-identityʳ a) (boxD g)) ⟩
        coeCod' (out-reflect (boxʷ g))
          (coeDom (++-identityʳ a) (coeCod' (sym (out-reidx (++-identityʳ a) (boxD g))) ⟦ boxD g ⟧))
          ≈⟨ coe-comm (++-identityʳ a) (out-reflect (boxʷ g)) _ ⟩
        coeDom (++-identityʳ a)
          (coeCod' (out-reflect (boxʷ g)) (coeCod' (sym (out-reidx (++-identityʳ a) (boxD g))) ⟦ boxD g ⟧))
          ≈⟨ coeDom-resp (++-identityʳ a) (coeCod'-trans (sym (out-reidx (++-identityʳ a) (boxD g))) (out-reflect (boxʷ g)) ⟦ boxD g ⟧) ⟩
        coeDom (++-identityʳ a) (coeCod' (trans (sym (out-reidx (++-identityʳ a) (boxD g))) (out-reflect (boxʷ g))) ⟦ boxD g ⟧)
          ≈⟨ coeDom-resp (++-identityʳ a) (coeCod'-cast2 (trans (sym (out-reidx (++-identityʳ a) (boxD g))) (out-reflect (boxʷ g))) (++-identityʳ b) ⟦ boxD g ⟧) ⟩
        coeDom (++-identityʳ a) (coeCod' (++-identityʳ b) ⟦ boxD g ⟧)
          ≈⟨ bs g ⟩
        ⟦box⟧ g ∎
        where
          coeCod'-cast2 : ∀ {N P Q} (e e' : P ≡ Q) (h : HomTerm (wires N) (wires P))
                        → coeCod' e h ≈Term coeCod' e' h
          coeCod'-cast2 e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
  reflect-sound bs (_⊗ʷ_ {nl} {ml} {nr} {mr} s t) = goal
    where
      ds = reflect s
      dt = reflect t
      es : out ds ≡ ml
      es = out-reflect s
      et : out dt ≡ mr
      et = out-reflect t
      goal : coeCod' (out-reflect (s ⊗ʷ t)) ⟦ tensorD ds dt ⟧
             ≈Term merge ml {mr} ∘ (embed s ⊗₁ embed t) ∘ split nl {nr}
      goal = begin
        coeCod' (out-reflect (s ⊗ʷ t)) ⟦ tensorD ds dt ⟧
          ≈⟨ coeCod'-uipG (out-reflect (s ⊗ʷ t)) (trans (out-tensorD ds dt) (cong₂ _++_ es et)) ⟦ tensorD ds dt ⟧ ⟩
        coeCod' (trans (out-tensorD ds dt) (cong₂ _++_ es et)) ⟦ tensorD ds dt ⟧
          ≈⟨ ≈-Term-sym (coeCod'-trans (out-tensorD ds dt) (cong₂ _++_ es et) ⟦ tensorD ds dt ⟧) ⟩
        coeCod' (cong₂ _++_ es et) (coeCod' (out-tensorD ds dt) ⟦ tensorD ds dt ⟧)
          ≈⟨ coeCod'-resp (cong₂ _++_ es et) (tensorD-sound ds dt) ⟩
        coeCod' (cong₂ _++_ es et) (merge (out ds) {out dt} ∘ (⟦ ds ⟧ ⊗₁ ⟦ dt ⟧) ∘ split nl {nr})
          ≈⟨ tensorBridge es et ⟩
        merge ml {mr} ∘ ((coeCod' es ⟦ ds ⟧ ⊗₁ coeCod' et ⟦ dt ⟧)) ∘ split nl {nr}
          ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ (reflect-sound bs s) (reflect-sound bs t)) ≈-Term-refl) ⟩
        merge ml {mr} ∘ (embed s ⊗₁ embed t) ∘ split nl {nr} ∎
        where
          coeCod'-uipG : ∀ {N P} (e e' : P ≡ ml ++ mr) (h : HomTerm (wires N) (wires P))
                       → coeCod' e h ≈Term coeCod' e' h
          coeCod'-uipG e e' h rewrite ≡-irrelevant e e' = ≈-Term-refl
          -- transport the merge-bridge along  out ds ≡ ml,  out dt ≡ mr.
          tensorBridge : ∀ {ml' mr'} (es : out ds ≡ ml') (et : out dt ≡ mr')
                       → coeCod' (cong₂ _++_ es et)
                           (merge (out ds) {out dt} ∘ (⟦ ds ⟧ ⊗₁ ⟦ dt ⟧) ∘ split nl {nr})
                         ≈Term merge ml' {mr'} ∘ ((coeCod' es ⟦ ds ⟧ ⊗₁ coeCod' et ⟦ dt ⟧)) ∘ split nl {nr}
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
