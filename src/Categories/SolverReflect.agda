{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A reflection  HomTerm → DiagU  with soundness, for the untyped free
-- monoidal diagram normal form of `Categories.DiagramRewriteUntyped`.
--
-- We work in the layered-composite wire fragment (M1): morphisms whose
-- source and target are already `wires`-shaped flat objects, built from
--   id, _∘_, var (box _), _⊗₁_,
-- captured by the inductive `WTerm n m` with embedding
-- `embed : WTerm n m → HomTerm (wires n) (wires m)`.
--------------------------------------------------------------------------------

module Categories.SolverReflect where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.DiagramRewriteUntyped
open import Categories.FreeMonoidal
open import Categories.SolverCompare using (module SolverCompareI)
open import Categories.SolverNormalize using (module NormalizeI)

module ReflectI (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
                (Mor : List X → List X → Set)
                (let open WireSig v {X} Mor using () renaming (wires to wires↑; mor to mor↑))
                (let open FreeMonoidalHelper.Mor v X mor↑ using () renaming (HomTerm to HomTerm↑))
                (⟦box⟧ : ∀ {a b} → Mor a b → HomTerm↑ (wires↑ a) (wires↑ b)) where

  open UntypedI v {X} Mor ⟦box⟧
  open FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor v X mor hiding (merge; split; merge∘split; split∘merge)
  open ≈R

  -- `castW-irr` is UIP on wire lists via Hedberg.
  open NormalizeI v {X} _≟X_ Mor ⟦box⟧
    using (substDiagU; substDiagU-out; ⟦substDiagU⟧; castW-irr)

  open MR FreeMonoidal
    using (pullˡ; pullʳ; center; center⁻¹; cancelʳ)
  open MonR Monoidal-FreeMonoidal
    using (refl⟩⊗⟨_; _⟩⊗⟨_; serialize₁₂; serialize₂₁)

  -- The merge/split coherence family (`merge-ρ`/`split-ρ`/`merge-assoc`/
  -- `split-assoc`, ⟦box⟧-free wire coherence) lives in WireCoh.WireCohDec; the
  -- soundness proofs below (`boxSound`, `rpad-fuse`, …) reach it from here, and
  -- `merge-ρ`/`merge-assoc` are re-exported `public` for the F-side transfer in
  -- SolverFrontendCore.  (`split-ρ`/`split-assoc` are internal here.)  Not the
  -- full WireCohDec re-exported `public`: NormalizeI already does that, so a
  -- second public path would name-clash for openers of both Reflect and Normalize.
  open WireCohDec _≟X_ public using (merge-ρ; merge-assoc)
  open WireCohDec _≟X_ using (split-ρ; split-assoc)

  --------------------------------------------------------------------------------
  -- M1 fragment: the wire-typed terms
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

  -- Coerce a HomTerm along a propositional equality of its codomain index.
  -- Re-introduced for downstream consumers (e.g. `Categories.SolverMor`, which
  -- bridges this against `SolverCompare`'s `coeW`); a `subst`/refl-match identity.
  coeCod' : ∀ {n p q} → p ≡ q → HomTerm (wires n) (wires p) → HomTerm (wires n) (wires q)
  coeCod' refl h = h

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
  -- The castW algebra kit (`⟦box⟧`-free wire coherence) lives in
  -- WireCoh.WireCohDec; brought into scope here for the soundness proofs below.
  --   castWˡ-irr / castWʳ-irr  : irrelevance (UIP) for the two sides
  --   castW-id⊗ˡ / castW-id⊗ʳ  : push castW through `id ⊗₁ _`
  --   castWˡ-invert / castWʳ-invert : cancel a castW against a proven equation
  --   mid-retype                : cancel a castW pair inserted in the middle
  -- Not re-exported `public`: `NormalizeI` already re-exports `WireCohDec` so
  -- a public re-export here would name-clash for modules opening both.  The
  -- engine-specific `substDiagU-fold / substDiagU-expand / castWˡ-fold`
  -- transport folds stay below (they need `substDiagU`).
  --------------------------------------------------------------------------------
  open WireCohDec _≟X_
    using (castWˡ-irr; castWʳ-irr; mid-retype; castW-id⊗ˡ; castW-id⊗ʳ;
           castWˡ-invert; castWʳ-invert)

  -- Soundness of append:  ⟦ d₁ ∘ᵈ d₂ ⟧ ≈ ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧ (codomain coerced).
  ∘ᵈ-sound : ∀ {m} (d₁ : DiagU m) (d₂ : DiagU (out d₁))
           → castW (out-∘ᵈ d₁ d₂) ∘ ⟦ d₁ ∘ᵈ d₂ ⟧ ≈Term ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧
  ∘ᵈ-sound ([]_ m) d₂ = idˡ ○ ⟺ idʳ
  ∘ᵈ-sound (pre ▸ suf ∷ f ⟨ d ⟩) d₂ = pullˡ (∘ᵈ-sound d d₂) ○ assoc

  --------------------------------------------------------------------------------
  -- Generic castW/substDiagU transport folds.  The soundness proofs below
  -- repeatedly shuffle stacked castW coercions around a `substDiagU`
  -- (or an already-proven castWˡ equation); each such shuffle is one of the
  -- three shapes here, proven once by matching the substDiagU equality to refl
  -- and discharging the residual loop equalities by `castW-irr`.
  --------------------------------------------------------------------------------

  -- fold shape: the outer domain coercion undoes the substDiagU, leaving a
  -- single codomain retype of the un-reindexed diagram.
  substDiagU-fold : ∀ {p q r} (E : p ≡ q) (M : q ≡ p) (d : DiagU p)
                    (B : out (substDiagU E d) ≡ r) (T : out d ≡ r)
                  → (castW B ∘ ⟦ substDiagU E d ⟧) ∘ castW (sym M) ≈Term castW T ∘ ⟦ d ⟧
  substDiagU-fold refl M d B T =
    (refl⟩∘⟨ castW-irr (sym M) refl) ○ idʳ ○ (castW-irr B T ⟩∘⟨refl)

  -- expand shape: push the codomain retype of a substDiagU'd diagram inside,
  -- exposing the substDiagU equality as a domain coercion.
  substDiagU-expand : ∀ {p q r} (E : p ≡ q) (L : DiagU p)
                      (O : out (substDiagU E L) ≡ r) (B : out L ≡ r)
                    → castW O ∘ ⟦ substDiagU E L ⟧ ≈Term (castW B ∘ ⟦ L ⟧) ∘ castW (sym E)
  substDiagU-expand refl L O B =
    (castW-irr O B ⟩∘⟨refl) ○ ⟺ idʳ

  -- re-route a codomain coercion through an already-proven castWˡ equation
  -- (the call prefix of the `∘ᵈ-sound` / `tensorD-sound` consumers).
  castWˡ-fold : ∀ {A p q r} (E : p ≡ q) (B : q ≡ r) (O : p ≡ r)
                {h : HomTerm A (wires p)} {k : HomTerm A (wires q)}
              → castW E ∘ h ≈Term k → castW O ∘ h ≈Term castW B ∘ k
  castWˡ-fold E B O eq =
    (castW-irr O (trans E B) ⟩∘⟨refl) ○ (⟺ (castW-∘ E B) ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ eq)

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
  -- reindexing absorbed by `substDiagU`.
  shiftL : ∀ {n} (lt : List X) → DiagU n → DiagU (lt ++ n)
  shiftL lt ([]_ n) = []_ (lt ++ n)
  shiftL {._} lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    substDiagU (++-assoc lt pre (a ++ suf))
      ((lt ++ pre) ▸ suf ∷ f ⟨ substDiagU (sym (++-assoc lt pre (b ++ suf))) (shiftL lt d) ⟩)

  -- Suffix-shift: append `rt` idle wires (suffix suf ↦ suf++rt).

  -- associativity:  (p ++ (a ++ s)) ++ r  ≡  p ++ (a ++ (s ++ r))
  reassoc++ : ∀ (p a s r : List X) → (p ++ (a ++ s)) ++ r ≡ p ++ (a ++ (s ++ r))
  reassoc++ p a s r = trans (++-assoc p (a ++ s) r) (cong (p ++_) (++-assoc a s r))

  shiftR : ∀ {n} (rt : List X) → DiagU n → DiagU (n ++ rt)
  shiftR rt ([]_ n) = []_ (n ++ rt)
  shiftR {._} rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    substDiagU (sym (reassoc++ pre a suf rt))
      (pre ▸ (suf ++ rt) ∷ f ⟨ substDiagU (reassoc++ pre b suf rt) (shiftR rt d) ⟩)

  --------------------------------------------------------------------------------
  -- out of the shifts.
  --------------------------------------------------------------------------------
  out-shiftL : ∀ {n} (lt : List X) (d : DiagU n) → out (shiftL lt d) ≡ lt ++ out d
  out-shiftL lt ([]_ n) = refl
  out-shiftL lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    trans (substDiagU-out (++-assoc lt pre (a ++ suf)) _)
          (trans (substDiagU-out (sym (++-assoc lt pre (b ++ suf))) (shiftL lt d))
                 (out-shiftL lt d))

  out-shiftR : ∀ {n} (rt : List X) (d : DiagU n) → out (shiftR rt d) ≡ out d ++ rt
  out-shiftR rt ([]_ n) = refl
  out-shiftR rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    trans (substDiagU-out (sym (reassoc++ pre a suf rt)) _)
          (trans (substDiagU-out (reassoc++ pre b suf rt) (shiftR rt d))
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
    shiftR nr dl ∘ᵈ substDiagU (sym (out-shiftR nr dl)) (shiftL (out dl) dr)

  out-tensorD : ∀ {nl nr} (dl : DiagU nl) (dr : DiagU nr)
              → out (tensorD dl dr) ≡ out dl ++ out dr
  out-tensorD {nl} {nr} dl dr =
    trans (out-∘ᵈ (shiftR nr dl) (substDiagU (sym (out-shiftR nr dl)) (shiftL (out dl) dr)))
          (trans (substDiagU-out (sym (out-shiftR nr dl)) (shiftL (out dl) dr))
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
  reflect (g ∘ʷ f)   = reflect f ∘ᵈ substDiagU (sym (out-reflect f)) (reflect g)
  reflect (boxʷ g)   = substDiagU (++-identityʳ _) (boxD g)
  reflect (s ⊗ʷ t)   = tensorD (reflect s) (reflect t)

  out-reflect idʷ        = refl
  out-reflect (g ∘ʷ f)   =
    trans (out-∘ᵈ (reflect f) (substDiagU (sym (out-reflect f)) (reflect g)))
          (trans (substDiagU-out (sym (out-reflect f)) (reflect g)) (out-reflect g))
  out-reflect (boxʷ {a} {b} g) =
    trans (substDiagU-out (++-identityʳ a) (boxD g))
          (++-identityʳ b)
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
  -- Box-leaf soundness obligation, named as a statement: it is the pure
  -- right-unitor coherence  merge a {[]} ≈ ρ⇒  up to a++[]≡a — box-free
  -- coherence, and so independent of the reflection logic below.  It is
  -- discharged in-file by `boxSound` via an explicit Kelly derivation (not a
  -- hypothesis: nothing downstream takes it as a parameter).
  BoxSound : Set
  BoxSound = ∀ {a b} (g : Mor a b)
           → (castW (++-identityʳ b) ∘ ⟦ boxD g ⟧) ∘ castW (sym (++-identityʳ a))
             ≈Term ⟦box⟧ g

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
    (castW (++-identityʳ b) ∘ ⟦ boxD g ⟧) ∘ castW (sym (++-identityʳ a))
      ≈⟨ (refl⟩∘⟨ idˡ) ⟩∘⟨refl ⟩
    (castW (++-identityʳ b) ∘ body) ∘ castW (sym (++-identityʳ a))
      ≈⟨ (⟺ assoc) ⟩∘⟨refl ⟩
    ((castW (++-identityʳ b) ∘ merge b {[]}) ∘ rest) ∘ castW (sym (++-identityʳ a))
      ≈⟨ assoc ⟩
    (castW (++-identityʳ b) ∘ merge b {[]}) ∘ (rest ∘ castW (sym (++-identityʳ a)))
      ≈⟨ (merge-ρ b) ⟩∘⟨ assoc ⟩
    ρ⇒ ∘ ((⟦box⟧ g ⊗₁ id) ∘ (split a {[]} ∘ castW (sym (++-identityʳ a))))
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
  -- Soundness of the offset shifts `shiftL` / `shiftR`.
  --
  --   shiftL lt d  is  liftW lt ⟦ d ⟧  up to the +-associativity reindexing
  --   absorbed by the `substDiagU` wrappers, and analogously for `shiftR`.  We state
  --   them in the codomain-reindexed form (mirroring `∘ᵈ-sound`):
  --     castW (out-shiftL lt d) ∘ ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
  --     castW (out-shiftR rt d) ∘ ⟦ shiftR rt d ⟧ ≈Term rpad rt ⟦ d ⟧
  --   where `rpad` is the suffix flat-shift (from DiagramRewriteUntyped).
  --------------------------------------------------------------------------------

  -- `liftW lt (pad pre suf g)` is the wider `pad (lt ++ pre) suf g`, up to the
  -- +-associativity reindex on its endpoints.  This is the layer-level content
  -- of `shiftL`'s `substDiagU` wrappers.  Proven by induction on `lt`, mirroring
  -- `shiftL`'s own recursion.
  liftW-pad : ∀ {a b} (lt pre suf : List X) (g : HomTerm (wires a) (wires b))
            → liftW lt (pad pre suf g)
              ≈Term (castW (++-assoc lt pre (b ++ suf)) ∘ pad (lt ++ pre) suf g)
                      ∘ castW (sym (++-assoc lt pre (a ++ suf)))
  liftW-pad []      pre suf g = ⟺ idˡ ○ ⟺ idʳ
  liftW-pad {a} {b} (x ∷ lt) pre suf g = begin
    id ⊗₁ liftW lt (pad pre suf g)
      ≈⟨ refl⟩⊗⟨ (liftW-pad lt pre suf g) ⟩
    id {Var x} ⊗₁ ((castW (++-assoc lt pre (b ++ suf)) ∘ pad (lt ++ pre) suf g)
                    ∘ castW (sym (++-assoc lt pre (a ++ suf))))
      ≈⟨ ⟺ (castW-id⊗ʳ x (++-assoc lt pre (a ++ suf)) _) ⟩
    (id {Var x} ⊗₁ (castW (++-assoc lt pre (b ++ suf)) ∘ pad (lt ++ pre) suf g))
      ∘ castW (sym (cong (x ∷_) (++-assoc lt pre (a ++ suf))))
      ≈⟨ (⟺ (castW-id⊗ˡ x (++-assoc lt pre (b ++ suf)) _)) ⟩∘⟨refl ⟩
    (castW (cong (x ∷_) (++-assoc lt pre (b ++ suf))) ∘ (id {Var x} ⊗₁ pad (lt ++ pre) suf g))
      ∘ castW (sym (cong (x ∷_) (++-assoc lt pre (a ++ suf))))
      ≈⟨ castWʳ-irr (cong (x ∷_) (++-assoc lt pre (a ++ suf))) (++-assoc (x ∷ lt) pre (a ++ suf)) _ ⟩
    (castW (cong (x ∷_) (++-assoc lt pre (b ++ suf))) ∘ (id {Var x} ⊗₁ pad (lt ++ pre) suf g))
      ∘ castW (sym (++-assoc (x ∷ lt) pre (a ++ suf)))
      ≈⟨ (castWˡ-irr (cong (x ∷_) (++-assoc lt pre (b ++ suf))) (++-assoc (x ∷ lt) pre (b ++ suf)) _) ⟩∘⟨refl ⟩
    (castW (++-assoc (x ∷ lt) pre (b ++ suf)) ∘ (id {Var x} ⊗₁ pad (lt ++ pre) suf g))
      ∘ castW (sym (++-assoc (x ∷ lt) pre (a ++ suf))) ∎

  -- shiftL soundness.
  shiftL-sound : ∀ {n} (lt : List X) (d : DiagU n)
               → castW (out-shiftL lt d) ∘ ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
  shiftL-sound lt ([]_ n) = idˡ ○ ⟺ (liftW-id lt)
  shiftL-sound lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = goal
    where
      g = ⟦box⟧ f
      E1 : (lt ++ pre) ++ (a ++ suf) ≡ lt ++ (pre ++ (a ++ suf))
      E1 = ++-assoc lt pre (a ++ suf)
      E2 : lt ++ (pre ++ (b ++ suf)) ≡ (lt ++ pre) ++ (b ++ suf)
      E2 = sym (++-assoc lt pre (b ++ suf))
      d' = shiftL lt d
      LAYER : DiagU ((lt ++ pre) ++ (a ++ suf))
      LAYER = (lt ++ pre) ▸ suf ∷ f ⟨ substDiagU E2 d' ⟩
      -- the inner shifted layer (before the outer E1 reindex).
      ⟦LAYER⟧ : HomTerm (wires ((lt ++ pre) ++ (a ++ suf))) (wires (out (substDiagU E2 d')))
      ⟦LAYER⟧ = ⟦ substDiagU E2 d' ⟧ ∘ pad (lt ++ pre) suf g

      OUTcons : out (shiftL lt (pre ▸ suf ∷ f ⟨ d ⟩)) ≡ lt ++ out (pre ▸ suf ∷ f ⟨ d ⟩)
      OUTcons = out-shiftL lt (pre ▸ suf ∷ f ⟨ d ⟩)

      -- bridge equality used to retype the codomain.
      eBridge : out (substDiagU E2 d') ≡ lt ++ out d
      eBridge = trans (substDiagU-out E2 d') (out-shiftL lt d)

      goal : castW OUTcons ∘ ⟦ substDiagU E1 ((lt ++ pre) ▸ suf ∷ f ⟨ substDiagU E2 d' ⟩) ⟧
             ≈Term liftW lt (⟦ d ⟧ ∘ pad pre suf g)
      goal = begin
        castW OUTcons ∘ ⟦ substDiagU E1 LAYER ⟧
          ≈⟨ substDiagU-expand E1 LAYER OUTcons eBridge ⟩
        (castW eBridge ∘ ⟦LAYER⟧) ∘ castW (sym E1)
          ≈⟨ (⟺ assoc) ⟩∘⟨refl ⟩
        ((castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) ∘ pad (lt ++ pre) suf g) ∘ castW (sym E1)
          ≈⟨ assoc ⟩
        (castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) ∘ (pad (lt ++ pre) suf g ∘ castW (sym E1))
          ≈⟨ mid-retype eM (castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) (pad (lt ++ pre) suf g ∘ castW (sym E1)) ⟩
        ((castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) ∘ castW (sym eM))
          ∘ (castW eM ∘ (pad (lt ++ pre) suf g ∘ castW (sym E1)))
          ≈⟨ tailFold ⟩∘⟨ padFold ⟩
        liftW lt ⟦ d ⟧ ∘ liftW lt (pad pre suf g)
          ≈⟨ ⟺ (liftW-∘ lt ⟦ d ⟧ (pad pre suf g)) ⟩
        liftW lt (⟦ d ⟧ ∘ pad pre suf g) ∎
        where
          -- middle-object retype eq:  (lt++pre)++(b++suf) ≡ lt++(pre++(b++suf)).
          eM : (lt ++ pre) ++ (b ++ suf) ≡ lt ++ (pre ++ (b ++ suf))
          eM = ++-assoc lt pre (b ++ suf)
          -- the tail folds (substDiagU-fold + recursion) to liftW lt ⟦d⟧.
          tailFold : (castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) ∘ castW (sym eM) ≈Term liftW lt ⟦ d ⟧
          tailFold = substDiagU-fold E2 eM d' eBridge (out-shiftL lt d) ○ shiftL-sound lt d
          padFold : castW eM ∘ (pad (lt ++ pre) suf g ∘ castW (sym E1)) ≈Term liftW lt (pad pre suf g)
          padFold = begin
            castW eM ∘ (pad (lt ++ pre) suf g ∘ castW (sym E1))
              ≈⟨ ⟺ assoc ⟩
            (castW eM ∘ pad (lt ++ pre) suf g) ∘ castW (sym E1)
              ≈⟨ ⟺ (liftW-pad lt pre suf g) ⟩
            liftW lt (pad pre suf g) ∎

  --------------------------------------------------------------------------------
  -- The suffix flat-shift `rpad` lemma family, and its soundness for `shiftR`.
  -- Built on the merge/split `merge-assoc`/`split-assoc` coherence (now in
  -- WireCoh.WireCohDec, re-exported into scope above).
  --------------------------------------------------------------------------------

  -- `rpad` suffix-fusion:  rpad rt (rpad suf g) is the wider rpad (suf++rt) g,
  -- up to +-associativity reindex on its endpoints.  This is the base case of
  -- the suffix shift / pad relation.  Assembled from `merge-assoc`/`split-assoc`.
  rpad-fuse : ∀ {a b} (suf rt : List X) (g : HomTerm (wires a) (wires b))
            → rpad rt (rpad suf g)
              ≈Term (castW (sym (++-assoc b suf rt)) ∘ rpad (suf ++ rt) g)
                      ∘ castW (sym (sym (++-assoc a suf rt)))
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
    (castW (sym (++-assoc b suf rt)) ∘ (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒))
      ∘ ((g ⊗₁ id) ⊗₁ id)
      ∘ ((α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt}) ∘ castW (sym (sym (++-assoc a suf rt))))
      ≈⟨ pull-coe ⟩
    (castW (sym (++-assoc b suf rt)) ∘
        ((merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
          ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
          ∘ (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})))
      ∘ castW (sym (sym (++-assoc a suf rt)))
      ≈⟨ (refl⟩∘⟨ core) ⟩∘⟨refl ⟩
    (castW (sym (++-assoc b suf rt)) ∘ rpad (suf ++ rt) g)
      ∘ castW (sym (sym (++-assoc a suf rt))) ∎
    where
      -- mergeStep:  merge(b++suf)∘(merge b⊗id) ≈ castW(sym e_b) ∘ (merge b{suf++rt}∘(id⊗merge suf)∘α⇒)
      mergeStep : merge (b ++ suf) {rt} ∘ (merge b {suf} ⊗₁ id {wires rt})
                ≈Term castW (sym (++-assoc b suf rt)) ∘ (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
      mergeStep = ⟺ (castWˡ-invert (++-assoc b suf rt) _ _ (merge-assoc b suf rt))
      -- splitStep:  (split a⊗id)∘split(a++suf) ≈ (α⇐∘(id⊗split suf)∘split a{suf++rt}) ∘ castW(sym(sym e_a))
      splitStep : (split a {suf} ⊗₁ id {wires rt}) ∘ split (a ++ suf) {rt}
                ≈Term (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt}) ∘ castW (sym (sym (++-assoc a suf rt)))
      splitStep = ⟺ (castWʳ-invert (++-assoc a suf rt) _ _ (split-assoc a suf rt))
      -- bookkeeping regroup of the 5-fold composite.
      regroup5 : merge (b ++ suf) ∘ (merge b ⊗₁ id ∘ ((g ⊗₁ id) ⊗₁ id ∘ split a ⊗₁ id)) ∘ split (a ++ suf)
               ≈Term (merge (b ++ suf) ∘ merge b ⊗₁ id) ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt}) ∘ (split a ⊗₁ id ∘ split (a ++ suf))
      regroup5 = center⁻¹ ≈-Term-refl assoc
      -- pull the castW coercions out of the composite to the ends.
      pull-coe :
          (castW (sym (++-assoc b suf rt)) ∘ (merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒))
            ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
            ∘ ((α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt}) ∘ castW (sym (sym (++-assoc a suf rt))))
        ≈Term (castW (sym (++-assoc b suf rt)) ∘
                  ((merge b {suf ++ rt} ∘ (id {wires b} ⊗₁ merge suf {rt}) ∘ α⇒)
                    ∘ ((g ⊗₁ id {wires suf}) ⊗₁ id {wires rt})
                    ∘ (α⇐ ∘ (id {wires a} ⊗₁ split suf {rt}) ∘ split a {suf ++ rt})))
              ∘ castW (sym (sym (++-assoc a suf rt)))
      pull-coe = pull (sym (++-assoc b suf rt)) (sym (sym (++-assoc a suf rt))) _ _ _
        where
          pull : ∀ {pb qb pa qa} {C D : ObjTerm}
                   (eb : pb ≡ qb) (ea : pa ≡ qa)
                   (L : HomTerm C (wires pb))
                   (Mid : HomTerm D C)
                   (Rt : HomTerm (wires qa) D)
               → (castW eb ∘ L) ∘ Mid ∘ (Rt ∘ castW ea)
                 ≈Term (castW eb ∘ (L ∘ Mid ∘ Rt)) ∘ castW ea
          pull refl refl L Mid Rt =
            (idˡ ⟩∘⟨ (refl⟩∘⟨ idʳ)) ○ ⟺ (idʳ ○ idˡ)
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
          midα = α-conj g (id {wires suf}) (id {wires rt})
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

  -- rpad / pad relation (suffix analogue of liftW-pad), by induction on pre.
  rpad-pad : ∀ {a b} (pre suf rt : List X) (g : HomTerm (wires a) (wires b))
             → rpad rt (pad pre suf g)
               ≈Term (castW (sym (reassoc++ pre b suf rt)) ∘ pad pre (suf ++ rt) g)
                       ∘ castW (sym (sym (reassoc++ pre a suf rt)))
  rpad-pad {a} {b} []      suf rt g = begin
    rpad rt (rpad suf g)
      ≈⟨ rpad-fuse suf rt g ⟩
    (castW (sym (++-assoc b suf rt)) ∘ rpad (suf ++ rt) g) ∘ castW (sym (sym (++-assoc a suf rt)))
      ≈⟨ castWʳ-irr (sym (++-assoc a suf rt)) (sym (reassoc++ [] a suf rt)) _ ⟩
    (castW (sym (++-assoc b suf rt)) ∘ rpad (suf ++ rt) g) ∘ castW (sym (sym (reassoc++ [] a suf rt)))
      ≈⟨ (castWˡ-irr (sym (++-assoc b suf rt)) (sym (reassoc++ [] b suf rt)) _) ⟩∘⟨refl ⟩
    (castW (sym (reassoc++ [] b suf rt)) ∘ rpad (suf ++ rt) g) ∘ castW (sym (sym (reassoc++ [] a suf rt))) ∎
  rpad-pad {a} {b} (x ∷ p) suf rt g = begin
    rpad rt (id {Var x} ⊗₁ pad p suf g)
      ≈⟨ rpad-id⊗ rt x (pad p suf g) ⟩
    id {Var x} ⊗₁ rpad rt (pad p suf g)
      ≈⟨ refl⟩⊗⟨ (rpad-pad p suf rt g) ⟩
    id {Var x} ⊗₁ ((castW (sym (reassoc++ p b suf rt)) ∘ pad p (suf ++ rt) g)
                    ∘ castW (sym (sym (reassoc++ p a suf rt))))
      ≈⟨ ⟺ (castW-id⊗ʳ x (sym (reassoc++ p a suf rt)) _) ⟩
    (id {Var x} ⊗₁ (castW (sym (reassoc++ p b suf rt)) ∘ pad p (suf ++ rt) g))
      ∘ castW (sym (cong (x ∷_) (sym (reassoc++ p a suf rt))))
      ≈⟨ (⟺ (castW-id⊗ˡ x (sym (reassoc++ p b suf rt)) _)) ⟩∘⟨refl ⟩
    (castW (cong (x ∷_) (sym (reassoc++ p b suf rt))) ∘ (id {Var x} ⊗₁ pad p (suf ++ rt) g))
      ∘ castW (sym (cong (x ∷_) (sym (reassoc++ p a suf rt))))
      ≈⟨ castWʳ-irr (cong (x ∷_) (sym (reassoc++ p a suf rt))) (sym (reassoc++ (x ∷ p) a suf rt)) _ ⟩
    (castW (cong (x ∷_) (sym (reassoc++ p b suf rt))) ∘ (id {Var x} ⊗₁ pad p (suf ++ rt) g))
      ∘ castW (sym (sym (reassoc++ (x ∷ p) a suf rt)))
      ≈⟨ (castWˡ-irr (cong (x ∷_) (sym (reassoc++ p b suf rt))) (sym (reassoc++ (x ∷ p) b suf rt)) _) ⟩∘⟨refl ⟩
    (castW (sym (reassoc++ (x ∷ p) b suf rt)) ∘ (id {Var x} ⊗₁ pad p (suf ++ rt) g))
      ∘ castW (sym (sym (reassoc++ (x ∷ p) a suf rt))) ∎

  -- shiftR soundness:  castW (out-shiftR rt d) ∘ ⟦ shiftR rt d ⟧ ≈ rpad rt ⟦ d ⟧.
  shiftR-sound : ∀ {n} (rt : List X) (d : DiagU n)
               → castW (out-shiftR rt d) ∘ ⟦ shiftR rt d ⟧ ≈Term rpad rt ⟦ d ⟧
  shiftR-sound rt ([]_ n) = idˡ ○ ⟺ (rpad-id rt)
  shiftR-sound rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = goal
    where
      g = ⟦box⟧ f
      E1 : (pre ++ (a ++ suf)) ++ rt ≡ pre ++ (a ++ (suf ++ rt))
      E1 = reassoc++ pre a suf rt
      E2 : (pre ++ (b ++ suf)) ++ rt ≡ pre ++ (b ++ (suf ++ rt))
      E2 = reassoc++ pre b suf rt
      d' = shiftR rt d
      LAYER : DiagU (pre ++ (a ++ (suf ++ rt)))
      LAYER = pre ▸ (suf ++ rt) ∷ f ⟨ substDiagU E2 d' ⟩
      ⟦LAYER⟧ : HomTerm (wires (pre ++ (a ++ (suf ++ rt)))) (wires (out (substDiagU E2 d')))
      ⟦LAYER⟧ = ⟦ substDiagU E2 d' ⟧ ∘ pad pre (suf ++ rt) g
      OUTcons : out (shiftR rt (pre ▸ suf ∷ f ⟨ d ⟩)) ≡ out (pre ▸ suf ∷ f ⟨ d ⟩) ++ rt
      OUTcons = out-shiftR rt (pre ▸ suf ∷ f ⟨ d ⟩)
      eBridge : out (substDiagU E2 d') ≡ out d ++ rt
      eBridge = trans (substDiagU-out E2 d') (out-shiftR rt d)
      -- middle-object retype eq:  (pre++(b++suf))++rt ≡ pre++(b++(suf++rt)).
      eM : (pre ++ (b ++ suf)) ++ rt ≡ pre ++ (b ++ (suf ++ rt))
      eM = reassoc++ pre b suf rt
      goal : castW OUTcons ∘ ⟦ substDiagU (sym E1) ((pre ▸ (suf ++ rt) ∷ f ⟨ substDiagU E2 d' ⟩)) ⟧
             ≈Term rpad rt (⟦ d ⟧ ∘ pad pre suf g)
      goal = begin
        castW OUTcons ∘ ⟦ substDiagU (sym E1) LAYER ⟧
          ≈⟨ substDiagU-expand (sym E1) LAYER OUTcons eBridge ⟩
        (castW eBridge ∘ ⟦LAYER⟧) ∘ castW (sym (sym E1))
          ≈⟨ (⟺ assoc) ⟩∘⟨refl ⟩
        ((castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) ∘ pad pre (suf ++ rt) g) ∘ castW (sym (sym E1))
          ≈⟨ assoc ⟩
        (castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) ∘ (pad pre (suf ++ rt) g ∘ castW (sym (sym E1)))
          ≈⟨ mid-retype eMrev (castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) (pad pre (suf ++ rt) g ∘ castW (sym (sym E1))) ⟩
        ((castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) ∘ castW (sym eMrev))
          ∘ (castW eMrev ∘ (pad pre (suf ++ rt) g ∘ castW (sym (sym E1))))
          ≈⟨ tailFold ⟩∘⟨ padFold ⟩
        rpad rt ⟦ d ⟧ ∘ rpad rt (pad pre suf g)
          ≈⟨ ⟺ (rpad-∘ rt ⟦ d ⟧ (pad pre suf g)) ⟩
        rpad rt (⟦ d ⟧ ∘ pad pre suf g) ∎
        where
          -- middle retype eq:  out(substDiagU E2 d') = out d ++ rt side
          --  domain of left factor = pre++(b++(suf++rt)); we retype it to
          --  (pre++(b++suf))++rt to match rpad rt ⟦d⟧ domain.
          eMrev : pre ++ (b ++ (suf ++ rt)) ≡ (pre ++ (b ++ suf)) ++ rt
          eMrev = sym eM
          tailFold : (castW eBridge ∘ ⟦ substDiagU E2 d' ⟧) ∘ castW (sym eMrev) ≈Term rpad rt ⟦ d ⟧
          tailFold = substDiagU-fold E2 eMrev d' eBridge (out-shiftR rt d) ○ shiftR-sound rt d
          padFold : castW eMrev ∘ (pad pre (suf ++ rt) g ∘ castW (sym (sym E1))) ≈Term rpad rt (pad pre suf g)
          padFold = begin
            castW eMrev ∘ (pad pre (suf ++ rt) g ∘ castW (sym (sym E1)))
              ≈⟨ ⟺ assoc ⟩
            (castW eMrev ∘ pad pre (suf ++ rt) g) ∘ castW (sym (sym E1))
              ≈⟨ ⟺ (rpad-pad pre suf rt g) ⟩
            rpad rt (pad pre suf g) ∎

  --------------------------------------------------------------------------------
  -- tensorD soundness (pure bifunctoriality, no σ):
  --   castW (out-tensorD dl dr) ∘ ⟦ tensorD dl dr ⟧
  --     ≈ merge (out dl) ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl
  -- the wire-grouping bridge between `wires nl ⊗₀ wires nr` and `wires (nl++nr)`.
  --------------------------------------------------------------------------------
  tensorD-sound : ∀ {nl nr} (dl : DiagU nl) (dr : DiagU nr)
                → castW (out-tensorD dl dr) ∘ ⟦ tensorD dl dr ⟧
                  ≈Term merge (out dl) {out dr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr}
  tensorD-sound {nl} {nr} dl dr = begin
    castW (out-tensorD dl dr) ∘ ⟦ shiftR nr dl ∘ᵈ d2 ⟧
      ≈⟨ castWˡ-fold (out-∘ᵈ (shiftR nr dl) d2) eBr (out-tensorD dl dr) (∘ᵈ-sound (shiftR nr dl) d2) ⟩
    castW eBr ∘ (⟦ d2 ⟧ ∘ ⟦ shiftR nr dl ⟧)
      ≈⟨ ⟺ assoc ⟩
    (castW eBr ∘ ⟦ d2 ⟧) ∘ ⟦ shiftR nr dl ⟧
      ≈⟨ mid-retype eSR (castW eBr ∘ ⟦ d2 ⟧) ⟦ shiftR nr dl ⟧ ⟩
    ((castW eBr ∘ ⟦ d2 ⟧) ∘ castW (sym eSR)) ∘ (castW eSR ∘ ⟦ shiftR nr dl ⟧)
      ≈⟨ d2Fold ⟩∘⟨ shiftRfold ⟩
    (merge (out dl) {out dr} ∘ (id {wires (out dl)} ⊗₁ ⟦ dr ⟧) ∘ split (out dl) {nr})
      ∘ (merge (out dl) {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr})
      ≈⟨ collapse ⟩
    merge (out dl) {out dr} ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl {nr} ∎
    where
      d2 = substDiagU (sym (out-shiftR nr dl)) (shiftL (out dl) dr)
      eSR : out (shiftR nr dl) ≡ out dl ++ nr
      eSR = out-shiftR nr dl
      eR2 : out (substDiagU (sym (out-shiftR nr dl)) (shiftL (out dl) dr)) ≡ out (shiftL (out dl) dr)
      eR2 = substDiagU-out (sym (out-shiftR nr dl)) (shiftL (out dl) dr)
      -- bridge:  out d2 ≡ out dl ++ out dr.
      eBr : out d2 ≡ out dl ++ out dr
      eBr = trans eR2 (out-shiftL (out dl) dr)
      -- ⟦ shiftR nr dl ⟧, codomain-retyped, folds to rpad nr ⟦dl⟧.
      shiftRfold : castW eSR ∘ ⟦ shiftR nr dl ⟧
                 ≈Term merge (out dl) {nr} ∘ (⟦ dl ⟧ ⊗₁ id {wires nr}) ∘ split nl {nr}
      shiftRfold = shiftR-sound nr dl
      -- (castW eBr ∘ ⟦ d2 ⟧) ∘ castW (sym eSR) folds to liftW (out dl) ⟦dr⟧ = bridge form.
      d2Fold : (castW eBr ∘ ⟦ d2 ⟧) ∘ castW (sym eSR)
             ≈Term merge (out dl) {out dr} ∘ (id {wires (out dl)} ⊗₁ ⟦ dr ⟧) ∘ split (out dl) {nr}
      d2Fold = substDiagU-fold (sym eSR) eSR (shiftL (out dl) dr) eBr (out-shiftL (out dl) dr)
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

  --------------------------------------------------------------------------------
  -- THE REFLECTION SOUNDNESS THEOREM.
  --
  --   castW (out-reflect t) ∘ ⟦ reflect t ⟧  ≈Term  embed t
  --
  -- i.e. the reflected diagram, with its codomain reindexed to match, equals
  -- the original wire-fragment morphism.
  --------------------------------------------------------------------------------
  reflect-sound : ∀ {n m} (t : WTerm n m)
                → castW (out-reflect t) ∘ ⟦ reflect t ⟧ ≈Term embed t
  reflect-sound idʷ = idˡ
  reflect-sound (_∘ʷ_ {n} {m} {k} g f) = goal
    where
      -- abbreviations
      df = reflect f
      dg = reflect g
      ef = out-reflect f                -- out df ≡ m
      dg' = substDiagU (sym ef) dg           -- DiagU (out df)
      -- step 1: push castW through ∘ᵈ-sound.
      goal : castW (out-reflect (g ∘ʷ f)) ∘ ⟦ df ∘ᵈ dg' ⟧ ≈Term embed g ∘ embed f
      goal = begin
        castW (out-reflect (g ∘ʷ f)) ∘ ⟦ df ∘ᵈ dg' ⟧
          ≈⟨ castWˡ-fold (out-∘ᵈ df dg') eg-bridge (out-reflect (g ∘ʷ f)) (∘ᵈ-sound df dg') ⟩
        castW eg-bridge ∘ (⟦ dg' ⟧ ∘ ⟦ df ⟧)
          ≈⟨ ⟺ assoc ⟩
        (castW eg-bridge ∘ ⟦ dg' ⟧) ∘ ⟦ df ⟧
          ≈⟨ mid-retype ef (castW eg-bridge ∘ ⟦ dg' ⟧) ⟦ df ⟧ ⟩
        ((castW eg-bridge ∘ ⟦ dg' ⟧) ∘ castW (sym ef)) ∘ (castW ef ∘ ⟦ df ⟧)
          ≈⟨ dg'-sound ⟩∘⟨ df-sound ⟩
        embed g ∘ embed f ∎
        where
          -- bridge:  out dg' ≡ k   (out dg' = out (substDiagU (sym ef) dg) ≡ out dg ≡ k)
          eg-bridge : out dg' ≡ k
          eg-bridge = trans (substDiagU-out (sym ef) dg) (out-reflect g)
          dg'-sound : (castW eg-bridge ∘ ⟦ dg' ⟧) ∘ castW (sym ef) ≈Term embed g
          dg'-sound = substDiagU-fold (sym ef) ef dg eg-bridge (out-reflect g) ○ reflect-sound g
          df-sound : castW ef ∘ ⟦ df ⟧ ≈Term embed f
          df-sound = reflect-sound f
  reflect-sound (boxʷ {a} {b} g) =
    substDiagU-expand (++-identityʳ a) (boxD g) (out-reflect (boxʷ g)) (++-identityʳ b)
    ○ boxSound g
  reflect-sound (_⊗ʷ_ {nl} {ml} {nr} {mr} s t) = goal
    where
      ds = reflect s
      dt = reflect t
      es : out ds ≡ ml
      es = out-reflect s
      et : out dt ≡ mr
      et = out-reflect t
      goal : castW (out-reflect (s ⊗ʷ t)) ∘ ⟦ tensorD ds dt ⟧
             ≈Term merge ml {mr} ∘ (embed s ⊗₁ embed t) ∘ split nl {nr}
      goal = begin
        castW (out-reflect (s ⊗ʷ t)) ∘ ⟦ tensorD ds dt ⟧
          ≈⟨ castWˡ-fold (out-tensorD ds dt) (cong₂ _++_ es et) (out-reflect (s ⊗ʷ t)) (tensorD-sound ds dt) ⟩
        castW (cong₂ _++_ es et) ∘ (merge (out ds) {out dt} ∘ (⟦ ds ⟧ ⊗₁ ⟦ dt ⟧) ∘ split nl {nr})
          ≈⟨ tensorBridge es et ⟩
        merge ml {mr} ∘ (((castW es ∘ ⟦ ds ⟧) ⊗₁ (castW et ∘ ⟦ dt ⟧))) ∘ split nl {nr}
          ≈⟨ refl⟩∘⟨ (((reflect-sound s) ⟩⊗⟨ (reflect-sound t)) ⟩∘⟨refl) ⟩
        merge ml {mr} ∘ (embed s ⊗₁ embed t) ∘ split nl {nr} ∎
        where
          -- transport the merge-bridge along  out ds ≡ ml,  out dt ≡ mr.
          tensorBridge : ∀ {ml' mr'} (es : out ds ≡ ml') (et : out dt ≡ mr')
                       → castW (cong₂ _++_ es et)
                           ∘ (merge (out ds) {out dt} ∘ (⟦ ds ⟧ ⊗₁ ⟦ dt ⟧) ∘ split nl {nr})
                         ≈Term merge ml' {mr'} ∘ (((castW es ∘ ⟦ ds ⟧) ⊗₁ (castW et ∘ ⟦ dt ⟧))) ∘ split nl {nr}
          tensorBridge refl refl = idˡ ○ (refl⟩∘⟨ ((⟺ idˡ ⟩⊗⟨ ⟺ idˡ) ⟩∘⟨refl))

  ------------------------------------------------------------------------
  -- `coeCod'` form of `reflect-sound`, for downstream consumers such as
  -- `Categories.SolverMor`.  `reflect-sound` states the codomain coercion as
  -- `castW _ ∘ _`; this bridges it to the `coeCod'` form via `castW refl = id`.
  ------------------------------------------------------------------------
  coeCod'∘ : ∀ {n p q} (e : p ≡ q) (h : HomTerm (wires n) (wires p))
           → coeCod' e h ≈Term castW e ∘ h
  coeCod'∘ refl h = ⟺ idˡ

  reflect-sound-coeCod' : ∀ {n m} (t : WTerm n m)
                        → coeCod' (out-reflect t) ⟦ reflect t ⟧ ≈Term embed t
  reflect-sound-coeCod' t = coeCod'∘ (out-reflect t) ⟦ reflect t ⟧ ○ reflect-sound t

--------------------------------------------------------------------------------
-- Compatibility wrapper: `ReflectI` at the standard interpretation
-- `Untyped.⟦box⟧` (= `var ∘ box`).  Old consumers keep working, gaining
-- only the leading variant argument.
--------------------------------------------------------------------------------
module Reflect (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
               (Mor : List X → List X → Set) where

  open Untyped v {X} Mor using (⟦box⟧)
  open ReflectI v {X} _≟X_ Mor ⟦box⟧ public

--------------------------------------------------------------------------------
-- `DecideCore`: the shared wire-level DECISION ASSEMBLY.
--
-- Both front-ends' `decide?W`/`decideσ?` are byte-identical given a normalizer
-- `norm : ∀ {n} (d : DiagU n) → SwapRes d`: reflect both sides to `DiagU`,
-- normalize each, decide normal-form equality, and chain the reflect-soundness
-- witnesses through the bridge.  `norm` is passed as an ordinary FUNCTION
-- argument so the per-variant oracle (interchange / σσ-cancel / slides) stays in
-- each front-end's scope while the assembly lives here once.
--------------------------------------------------------------------------------
module DecideCore
  (v : Variant) {X : Set} (_≟X_ : DecidableEquality X)
  (Mor : List X → List X → Set)
  (let open WireSig v {X} Mor using () renaming (wires to wires↑; mor to mor↑))
  (let open FreeMonoidalHelper.Mor v X mor↑ using () renaming (HomTerm to HomTerm↑))
  (⟦box⟧ : ∀ {a b} → Mor a b → HomTerm↑ (wires↑ a) (wires↑ b))
  where

  open UntypedI v {X} Mor ⟦box⟧
  open FreeMonoidalHelper.Mor v X mor hiding (merge; split; merge∘split; split∘merge)
  open ≈R
  open ReflectI v {X} _≟X_ Mor ⟦box⟧
    using (WTerm; embed; reflect; out-reflect; reflect-sound)
  open NormalizeI v {X} _≟X_ Mor ⟦box⟧
    using (castW-irr; module SortD)
  open SortD using (SwapRes; unwrapCast)

  private
    open MR FreeMonoidal using (pullˡ)
    module SCmp = SolverCompareI v {X} _≟X_ Mor ⟦box⟧

  -- the caller supplies decidable equality on the Σ-packaged generators (used
  -- only to build `_≟DiagU_`) and a normalizer.
  module Decide
    (_≟Mor_ : DecidableEquality SCmp.Gen)
    (norm : ∀ {n} (d : DiagU n) → SwapRes d)
    where

    open SCmp.Decide _≟Mor_ using (_≈NF_; _≟DiagU_; ≈NF⇒≡)

    decideW : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decideW {n} {m} f g with norm (reflect f) | norm (reflect g)
    ... | (df' , oeqf , sndf) | (dg' , oeqg , sndg) with df' ≟DiagU dg'
    ...   | no  _  = nothing
    ...   | yes eq = just (chain (≈NF⇒≡ eq))
      where
        half : ∀ (t : WTerm n m) (d' : DiagU n) (oeq : out (reflect t) ≡ out d')
             → castW oeq ∘ ⟦ reflect t ⟧ ≈Term ⟦ d' ⟧
             → embed t ≈Term castW (trans (sym oeq) (out-reflect t)) ∘ ⟦ d' ⟧
        half t d' oeq snd =
          ⟺ (reflect-sound t)
          ○ (refl⟩∘⟨ unwrapCast oeq snd)
          ○ pullˡ (castW-∘ (sym oeq) (out-reflect t))

        chain : df' ≡ dg' → embed f ≈Term embed g
        chain deq = begin
          embed f
            ≈⟨ half f df' oeqf sndf ⟩
          castW (trans (sym oeqf) (out-reflect f)) ∘ ⟦ df' ⟧
            ≈⟨ step deq ⟩
          castW (trans (sym oeqg) (out-reflect g)) ∘ ⟦ dg' ⟧
            ≈⟨ half g dg' oeqg sndg ⟨
          embed g ∎
          where
            step : df' ≡ dg'
                 → castW (trans (sym oeqf) (out-reflect f)) ∘ ⟦ df' ⟧
                   ≈Term castW (trans (sym oeqg) (out-reflect g)) ∘ ⟦ dg' ⟧
            step refl = castW-irr _ _ ⟩∘⟨refl
