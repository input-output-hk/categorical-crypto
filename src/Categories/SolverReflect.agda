{-# OPTIONS --safe #-}

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
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

-- UIP, available since this development is --safe *with* K.
≡-irrelevant : ∀ {a} {A : Set a} {x y : A} (e e' : x ≡ y) → e ≡ e'
≡-irrelevant refl refl = refl

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped
import Categories.Category.Monoidal.Properties as MonProps

module Reflect {X : Set} (Mor : List X → List X → Set) where

  open Untyped {X} Mor
  open FreeMonoidalHelper Mon X using (ObjTerm; unit; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor Mon X mor
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

  --------------------------------------------------------------------------------
  -- M1 fragment: the wire-typed terms.
  --------------------------------------------------------------------------------
  infixr 9 _∘ʷ_
  data WTerm : List X → List X → Set where
    boxʷ : ∀ {a b} → Mor a b → WTerm a b
    idʷ  : ∀ {n} → WTerm n n
    _∘ʷ_ : ∀ {n m k} → WTerm m k → WTerm n m → WTerm n k

  embed : ∀ {n m} → WTerm n m → HomTerm (wires n) (wires m)
  embed (boxʷ g)  = ⟦box⟧ g
  embed idʷ       = id
  embed (g ∘ʷ f)  = embed g ∘ embed f

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

  out-reflect idʷ        = refl
  out-reflect (g ∘ʷ f)   =
    trans (out-∘ᵈ (reflect f) (reidx (sym (out-reflect f)) (reflect g)))
          (trans (out-reidx (sym (out-reflect f)) (reflect g)) (out-reflect g))
  out-reflect (boxʷ {a} {b} g) =
    trans (out-reidx (++-identityʳ a) (boxD g))
          (trans (out-boxD g) (++-identityʳ b))

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
  -- THE SOUNDNESS THEOREM (M1).
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
          coeCod'-uip refl refl h = ≈-Term-refl
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
              coeCod'-cast refl refl h = ≈-Term-refl
              -- collapse two stacked domain coercions.
              coeDom-trans : ∀ {a b c p} (e1 : a ≡ b) (e2 : b ≡ c) (h : HomTerm (wires a) (wires p))
                           → coeDom e2 (coeDom e1 h) ≈Term coeDom (trans e1 e2) h
              coeDom-trans refl refl h = ≈-Term-refl
              -- recast a domain coe along a propositionally-equal (UIP) eq.
              coeDom-cast : ∀ {N} (e e' : m ≡ m) (h : HomTerm (wires m) (wires N))
                          → coeDom e h ≈Term coeDom e' h
              coeDom-cast refl refl h = ≈-Term-refl
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
