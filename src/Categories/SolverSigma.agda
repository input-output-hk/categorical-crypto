{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-EXTENSION of the wire-level solver: block crossings as TRANSPARENT
-- generators.
--
-- The variant-/⟦box⟧-parametric engine (`UntypedI`/`ReflectI`/`NormalizeI`/
-- `SolverCompareI`) is instantiated at `v = Symm` over the extended generator
-- family
--
--     data MorS : List X → List X → Set where
--       box   : Mor a b → MorS a b
--       cross : (a b : List X) → MorS (a ++ b) (b ++ a)
--
-- with the crossing interpreted as the GENUINE block braiding of the free
-- symmetric monoidal category, conjugated to flat wire coordinates:
--
--     ⟦box⟧S (cross a b) = merge b {a} ∘ σ ∘ split a {b}
--
-- STAGE A (this module, complete):
--   * `σσ-block`  : the block involution  ⟦cross b a⟧ ∘ ⟦cross a b⟧ ≈ id
--                   (split∘merge cancellation + the σ∘σ≈id axiom — NO
--                   σ-naturality);
--   * `pad-∘`/`pad-id`/`pad-resp` : pad functoriality, lifting it to padded
--                   layers (`pad-σσ`);
--   * `Decide.normσ` : the fuel-driven normalizer interleaving the existing
--                   disjoint-interchange bubble sort (crosses are ordinary
--                   boxes for interchange) with the NEW σσ-CANCEL move that
--                   deletes an adjacent inverse cross-pair;
--   * `Decide.decideσ?` : the decision entry mirroring the front-end's
--                   `decide?W` (reflect → normσ → ≟DiagU → chain), with
--                   `DecidableEquality` on the extended generators derived
--                   from the caller's `_≟G_` (no-K style, via first-order
--                   projection functions — never a refl-match at a forced
--                   `++`-composite index).
--
-- RANK CONVENTION: the interchange tiebreak for ambiguous (scalar-like)
-- pairs needs a rank on the extended generators.  Crosses get rank 0 and
-- boxes get `suc ∘ rank` of the caller's rank — crossings sort below all
-- boxes among mutually-fitting pairs, and the caller's relative order on
-- boxes is preserved.
--
-- STAGE B (the naturality-slide CORE):
--   * `slide-core` : the block-level slide — a box firing inside the
--     b-block AFTER the crossing equals the box firing BEFORE the crossing
--     at its pre-cross position.  ONE σ-naturality axiom instance; stated
--     for an ARBITRARY block update `h : wires b ⇒ wires b'`, fully
--     cast-free.  (`slide-core-a` is the a-block mirror.)
--   * `slide-pad` : the same under an arbitrary `pad pq sq` frame — still
--     cast-free (grouped coordinates).
--   * the re-cleaning of the two grouped box-layers into genuine clean
--     DiagU pads (`slide-clean`/`slide-clean-a`) — this is where the
--     `++`-assoc castW tax lives (`rpad-rpad`, `rpad-liftW`, `liftW-fuse`).
--
-- STAGE C (the DiagU-level slide, WIRED into the driver):
--   * `Decide.fireRepl` : a generic sound two-layer head REPLACEMENT,
--     justified by a caller-supplied key equation between the two padded
--     two-layer composites (pure `substDiagU`/`castW` algebra around it);
--   * `Decide.goSlideB`/`Decide.goSlideA` : the slide recognisers — pure
--     `stripPrefix` list surgery exhibiting the second-layer box inside
--     the crossing's b-image (resp. a-image) block — instantiating the
--     key with `slide-clean-box` (resp. `slide-clean-box-a`);
--   * `Decide.stepσ?` now tries, in order: σσ-cancel, b-image slide,
--     a-image slide, disjoint interchange.  Each slide strictly decreases
--     the number of (cross-before-box) inversions, so the existing
--     depth³-ish fuel still over-approximates; termination stays trivial
--     by fuel.
--
-- Hole-free, postulate-free, --safe --without-K.
--------------------------------------------------------------------------------

module Categories.SolverSigma where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Bool using (Bool; true; false; not; _∨_; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ≡-dec)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<ᵇ_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.DiagramRewriteUntyped using (module WireSig; module UntypedI)
open import Categories.FreeMonoidal
open import Categories.SolverCompare using (module SolverCompareI)
open import Categories.SolverNormalize using (module NormalizeI)
open import Categories.SolverReflect using (module ReflectI)

module Sigma {X : Set} (_≟X_ : DecidableEquality X)
             (Mor : List X → List X → Set) where

  -- `Symm ≤ Symm` for instance search, so σ needs no explicit ⦃ v≤v ⦄.
  private instance
    S≤S : Symm ≤ Symm
    S≤S = v≤v

  -- UIP on the wire lists, via Hedberg (decidable equality), --without-K.
  private
    ≡-irrelevantL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevantL = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)

  ------------------------------------------------------------------------
  -- The extended generator family: boxes + transparent block crossings.
  ------------------------------------------------------------------------
  data MorS : List X → List X → Set where
    box   : ∀ {a b} → Mor a b → MorS a b
    cross : (a b : List X) → MorS (a ++ b) (b ++ a)

  -- the wire signature at MorS: `wires`, the wire-level generator datatype
  -- `mor` (whose `box` wraps a MorS), and the ⟦box⟧-independent merge/split.
  -- Qualified (`WS.`) here — `open UntypedI` below re-exports the same
  -- WireSig surface publicly, and a second anonymous open would be
  -- ambiguous (module application is name-generative).
  private module WS = WireSig Symm {X} MorS
  open FreeMonoidalHelper Symm X using (ObjTerm; unit; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor Symm X WS.mor

  ------------------------------------------------------------------------
  -- The interpretation: boxes stay opaque generators; a crossing is the
  -- block braiding conjugated to flat wire coordinates.
  ------------------------------------------------------------------------
  ⟦box⟧S : ∀ {a b} → MorS a b → HomTerm (WS.wires a) (WS.wires b)
  ⟦box⟧S (box f)     = var (WS.box (box f))
  ⟦box⟧S (cross a b) = WS.merge b {a} ∘ σ ∘ WS.split a {b}

  -- the full diagram engine at (Symm, MorS, ⟦box⟧S), re-exported.
  open UntypedI Symm {X} MorS ⟦box⟧S public
  open ≈R

  -- stock associativity/cancellation combinators (same idiom as
  -- DiagramRewriteUntyped/SolverReflect): plain non-public opens,
  -- proofs-only.
  open MR FreeMonoidal
    using (pullˡ; pullʳ; pushˡ; cancelˡ; cancelʳ; cancelInner; insertInner;
           elimʳ; introˡ; assoc²βε)
  open MonR Monoidal-FreeMonoidal
    using (refl⟩⊗⟨_; _⟩⊗⟨refl; _⟩⊗⟨_; split₁ʳ)

  -- the reflection stack (and its rpad/coercion lemma families), re-exported.
  open ReflectI Symm {X} _≟X_ MorS ⟦box⟧S public

  ------------------------------------------------------------------------
  -- STAGE A1: the block involution.  σ-naturality is NOT needed — only
  -- split∘merge cancellation, σ∘σ≈id, and assoc/id algebra.
  ------------------------------------------------------------------------
  σσ-block : ∀ (a b : List X)
           → ⟦box⟧S (cross b a) ∘ ⟦box⟧S (cross a b) ≈Term id
  σσ-block a b = begin
    (merge a ∘ σ ∘ split b) ∘ (merge b ∘ σ ∘ split a)
      ≈⟨ pullʳ (cancelInner (split∘merge b)) ⟩
    merge a ∘ (σ ∘ (σ ∘ split a))
      ≈⟨ refl⟩∘⟨ cancelˡ σ∘σ≈id ⟩
    merge a ∘ split a
      ≈⟨ merge∘split a ⟩
    id ∎

  ------------------------------------------------------------------------
  -- STAGE A2: pad functoriality (missing from the engine), and the lift
  -- of the involution to padded layers.
  ------------------------------------------------------------------------

  -- (`rpad-resp` / `rpad-id` / `rpad-∘` come from ReflectI above.)
  pad-resp : ∀ {a b} (pre suf : List X) {g g' : HomTerm (wires a) (wires b)}
           → g ≈Term g' → pad pre suf g ≈Term pad pre suf g'
  pad-resp []      suf eq = rpad-resp suf eq
  pad-resp (x ∷ p) suf eq = refl⟩⊗⟨ pad-resp p suf eq

  pad-id : ∀ {a} (pre suf : List X) → pad pre suf (id {wires a}) ≈Term id
  pad-id []      suf = rpad-id suf
  pad-id (x ∷ p) suf = (refl⟩⊗⟨ pad-id p suf) ○ id⊗id≈id

  pad-∘ : ∀ {a b c} (pre suf : List X)
            (g : HomTerm (wires b) (wires c)) (f : HomTerm (wires a) (wires b))
        → pad pre suf (g ∘ f) ≈Term pad pre suf g ∘ pad pre suf f
  pad-∘ []      suf g f = rpad-∘ suf g f
  pad-∘ (x ∷ p) suf g f = (refl⟩⊗⟨ pad-∘ p suf g f) ○ ⟺ (id⊗-∘ _ _)

  -- the padded involution: an adjacent inverse cross-pair at the SAME
  -- offsets is the identity.
  pad-σσ : ∀ (pre suf a b : List X)
         → pad pre suf (⟦box⟧S (cross b a)) ∘ pad pre suf (⟦box⟧S (cross a b))
           ≈Term id
  pad-σσ pre suf a b = begin
    pad pre suf (⟦box⟧S (cross b a)) ∘ pad pre suf (⟦box⟧S (cross a b))
      ≈⟨ pad-∘ pre suf (⟦box⟧S (cross b a)) (⟦box⟧S (cross a b)) ⟨
    pad pre suf (⟦box⟧S (cross b a) ∘ ⟦box⟧S (cross a b))
      ≈⟨ pad-resp pre suf (σσ-block a b) ⟩
    pad pre suf id
      ≈⟨ pad-id pre suf ⟩
    id ∎

  ------------------------------------------------------------------------
  -- The normalize / compare stack at (Symm, MorS, ⟦box⟧S).
  ------------------------------------------------------------------------
  -- castW / castW-∘ / castW-∷ / castW-sym-r now come from the UntypedI open
  -- above (they moved into the engine); only the DecEq-dependent algebra and
  -- the swap machinery still come from NormalizeI.
  open NormalizeI Symm {X} _≟X_ MorS ⟦box⟧S using
    ( castW-irr
    ; substDiagU; substDiagU-out; ⟦substDiagU⟧
    ; LeftFit; leftFit
    ; dInput; dSwapped; dInput-out; dSwapped-out; diagU-swap-soundD; domeq
    ; assocW-castW; assocW⁻-castW; liftW-castW
    ; module SortD )
  open SortD using (leftFit?; stripPrefix; SwapRes; fire; ambiguous?; lift∷; swapTrans; depthD; normFuelWith; unwrapCast)

  private module SCmp = SolverCompareI Symm {X} _≟X_ MorS ⟦box⟧S

  -- the caller-facing generator triples (on the UNDERLYING `Mor`).
  GenM : Set
  GenM = Σ[ a ∈ List X ] Σ[ b ∈ List X ] Mor a b

  ------------------------------------------------------------------------
  -- STAGE B: the naturality-slide CORE.
  --
  -- The slide configuration: a box fires AFTER a crossing, inside the
  -- b-block of its image; sliding it BEFORE the crossing moves it to its
  -- pre-cross position and updates the crossing's b-block (c ↦ d).  The
  -- categorical content is ONE instance of the braiding-naturality axiom
  -- σ∘[f⊗g]≈[g⊗f]∘σ at the pair (id_{wires a}, the-block-update); we
  -- state it for an ARBITRARY block update `h : wires b ⇒ wires b'` (the
  -- DiagU instance is `h = pad p₁ s₁ ⟦f⟧` with b = p₁ ++ (c ++ s₁)),
  -- which keeps the BLOCK-level statement and its `pad pq sq` lift fully
  -- CAST-FREE.  The `++`-assoc castW tax appears only in the final
  -- re-cleaning of the two grouped box-layers into genuine clean DiagU
  -- pads (`slide-clean` below).
  ------------------------------------------------------------------------

  -- THE BLOCK SLIDE: the box (update h, inside the b-block) fires after
  -- the crossing  ≈  it fires before the crossing at the pre-cross
  -- position.  ONE σ-naturality instance + split/merge cancellation.
  slide-core : ∀ (a : List X) {b b' : List X} (h : HomTerm (wires b) (wires b'))
             → ⟦box⟧S (cross a b') ∘ liftW a h
               ≈Term rpad a h ∘ ⟦box⟧S (cross a b)
  slide-core a {b} {b'} h = begin
    (merge b' ∘ σ ∘ split a) ∘ liftW a h
      ≈⟨ refl⟩∘⟨ liftW-merge a h ⟩
    (merge b' ∘ σ ∘ split a) ∘ (merge a ∘ (id ⊗₁ h) ∘ split a)
      ≈⟨ pullʳ (cancelInner (split∘merge a)) ⟩
    merge b' ∘ (σ ∘ ((id ⊗₁ h) ∘ split a))
      ≈⟨ refl⟩∘⟨ pullˡ σ∘[f⊗g]≈[g⊗f]∘σ ⟩
    merge b' ∘ (((h ⊗₁ id) ∘ σ) ∘ split a)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    merge b' ∘ ((h ⊗₁ id) ∘ (σ ∘ split a))
      ≈⟨ refl⟩∘⟨ insertInner (split∘merge b) ⟩
    merge b' ∘ (((h ⊗₁ id) ∘ split b) ∘ (merge b ∘ (σ ∘ split a)))
      ≈⟨ assoc ⟨
    (merge b' ∘ (h ⊗₁ id) ∘ split b) ∘ (merge b ∘ σ ∘ split a) ∎

  -- the symmetric a-block case (update g : wires a ⇒ wires a').
  slide-core-a : ∀ (b : List X) {a a' : List X} (g : HomTerm (wires a) (wires a'))
               → ⟦box⟧S (cross a' b) ∘ rpad b g
                 ≈Term liftW b g ∘ ⟦box⟧S (cross a b)
  slide-core-a b {a} {a'} g = begin
    (merge b ∘ σ ∘ split a') ∘ (merge a' ∘ (g ⊗₁ id) ∘ split a)
      ≈⟨ pullʳ (cancelInner (split∘merge a')) ⟩
    merge b ∘ (σ ∘ ((g ⊗₁ id) ∘ split a))
      ≈⟨ refl⟩∘⟨ pullˡ σ∘[f⊗g]≈[g⊗f]∘σ ⟩
    merge b ∘ (((id ⊗₁ g) ∘ σ) ∘ split a)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    merge b ∘ ((id ⊗₁ g) ∘ (σ ∘ split a))
      ≈⟨ refl⟩∘⟨ insertInner (split∘merge b) ⟩
    merge b ∘ (((id ⊗₁ g) ∘ split b) ∘ (merge b ∘ (σ ∘ split a)))
      ≈⟨ assoc ⟨
    (merge b ∘ (id ⊗₁ g) ∘ split b) ∘ (merge b ∘ σ ∘ split a)
      ≈⟨ liftW-merge b g ⟩∘⟨refl ⟨
    liftW b g ∘ (merge b ∘ σ ∘ split a) ∎

  -- THE PADDED SLIDE (grouped coordinates): the same equation under an
  -- arbitrary `pad pq sq` frame — still fully cast-free, via the Stage-A
  -- pad functoriality.
  slide-pad : ∀ (pq sq a : List X) {b b'} (h : HomTerm (wires b) (wires b'))
            → pad pq sq (⟦box⟧S (cross a b')) ∘ pad pq sq (liftW a h)
              ≈Term pad pq sq (rpad a h) ∘ pad pq sq (⟦box⟧S (cross a b))
  slide-pad pq sq a {b} {b'} h = begin
    pad pq sq (⟦box⟧S (cross a b')) ∘ pad pq sq (liftW a h)
      ≈⟨ pad-∘ pq sq (⟦box⟧S (cross a b')) (liftW a h) ⟨
    pad pq sq (⟦box⟧S (cross a b') ∘ liftW a h)
      ≈⟨ pad-resp pq sq (slide-core a h) ⟩
    pad pq sq (rpad a h ∘ ⟦box⟧S (cross a b))
      ≈⟨ pad-∘ pq sq (rpad a h) (⟦box⟧S (cross a b)) ⟩
    pad pq sq (rpad a h) ∘ pad pq sq (⟦box⟧S (cross a b)) ∎

  ------------------------------------------------------------------------
  -- STAGE B, re-cleaning: the two GROUPED box-layers of the slide
  -- (`pad pq sq (rpad a h)` / `pad pq sq (liftW a h)` with the concrete
  -- block update `h = pad p₁ s₁ G`) re-expressed as genuine clean DiagU
  -- pads at the composite offsets, conjugated by `++`-assoc index casts.
  -- This is where the castW tax lives.  The interface is the SANDWICH
  -- relation `Sand eC eD Y Z` (= Y ≈ castW eC ∘ Z ∘ castW eD), with the
  -- J-style combinators below; the two genuinely new coherence lemmas are
  -- `rpad-liftW` (suffix-pad past a prefix-lift, by induction on the
  -- prefix + α-naturality) and `rpad-rpad` (suffix-pad fusion, ReflectI's
  -- `rpad-fuse` recast from coeC/coeD into the castW sandwich).
  ------------------------------------------------------------------------

  -- the conjugation-by-index-casts relation.
  Sand : ∀ {p q w t : List X} (eC : t ≡ q) (eD : p ≡ w)
       → HomTerm (wires p) (wires q) → HomTerm (wires w) (wires t) → Set
  Sand eC eD Y Z = Y ≈Term castW eC ∘ Z ∘ castW eD

  private
    sand-trans : ∀ {p q w t w' t'}
                 {Y : HomTerm (wires p) (wires q)}
                 {Z : HomTerm (wires w) (wires t)}
                 {V : HomTerm (wires w') (wires t')}
                 {eC : t ≡ q} {eD : p ≡ w} {fC : t' ≡ t} {fD : w ≡ w'}
               → Sand eC eD Y Z → Sand fC fD Z V
               → Sand (trans fC eC) (trans eD fD) Y V
    sand-trans {eC = refl} {refl} {refl} {refl} hy hz = hy ○ idˡ ○ idʳ ○ hz

    sand-flip : ∀ {p q w t}
                {Y : HomTerm (wires p) (wires q)}
                {Z : HomTerm (wires w) (wires t)}
                {eC : t ≡ q} {eD : p ≡ w}
              → Sand eC eD Y Z → Sand (sym eC) (sym eD) Z Y
    sand-flip {eC = refl} {refl} hy = ⟺ (hy ○ idˡ ○ idʳ) ○ ⟺ (idˡ ○ idʳ)

    sand-irr : ∀ {p q w t}
               {Y : HomTerm (wires p) (wires q)}
               {Z : HomTerm (wires w) (wires t)}
               {eC eC' : t ≡ q} {eD eD' : p ≡ w}
             → Sand eC eD Y Z → Sand eC' eD' Y Z
    sand-irr {eC = eC} {eC'} {eD} {eD'} s =
      s ○ (castW-irr eC eC' ⟩∘⟨ refl⟩∘⟨ castW-irr eD eD')

    sand-≈ˡ : ∀ {p q w t}
              {Y' Y : HomTerm (wires p) (wires q)}
              {Z : HomTerm (wires w) (wires t)}
              {eC : t ≡ q} {eD : p ≡ w}
            → Y' ≈Term Y → Sand eC eD Y Z → Sand eC eD Y' Z
    sand-≈ˡ e s = e ○ s

    sand-mid : ∀ {p q w t}
               {Y : HomTerm (wires p) (wires q)}
               {Z Z' : HomTerm (wires w) (wires t)}
               {eC : t ≡ q} {eD : p ≡ w}
             → Sand eC eD Y Z → Z ≈Term Z' → Sand eC eD Y Z'
    sand-mid s e = s ○ (refl⟩∘⟨ (e ⟩∘⟨refl))

    -- the sandwich-cancellation used by both clean slides: flip the
    -- sandwich onto the left factor, then cancel the inverse cast pair
    -- `castW (sym eD) ∘ castW eD` against the caller's cast.
    sand-cancel : ∀ {p q w t} {A : ObjTerm}
                  {Y : HomTerm (wires p) (wires q)}
                  {Z : HomTerm (wires w) (wires t)}
                  {eC : t ≡ q} (eD : p ≡ w) (C : HomTerm A (wires p))
                → Sand eC eD Y Z
                → Z ∘ (castW eD ∘ C) ≈Term castW (sym eC) ∘ (Y ∘ C)
    sand-cancel eD C s =
      (sand-flip s ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ cancelInner (castW-sym-r eD))

    -- prefix-lift of a sandwich.
    liftW-sand : ∀ (p : List X) {pp q w t}
                 {Y : HomTerm (wires pp) (wires q)}
                 {Z : HomTerm (wires w) (wires t)}
                 {eC : t ≡ q} {eD : pp ≡ w}
               → Sand eC eD Y Z
               → Sand (cong (p ++_) eC) (cong (p ++_) eD) (liftW p Y) (liftW p Z)
    liftW-sand p {Y = Y} {Z = Z} {eC = eC} {eD = eD} s = begin
      liftW p Y
        ≈⟨ liftW-resp p s ⟩
      liftW p (castW eC ∘ Z ∘ castW eD)
        ≈⟨ liftW-∘ p (castW eC) (Z ∘ castW eD) ⟩
      liftW p (castW eC) ∘ liftW p (Z ∘ castW eD)
        ≈⟨ liftW-castW p eC ⟩∘⟨ liftW-∘ p Z (castW eD) ⟩
      castW (cong (p ++_) eC) ∘ (liftW p Z ∘ liftW p (castW eD))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ liftW-castW p eD ⟩
      castW (cong (p ++_) eC) ∘ (liftW p Z ∘ castW (cong (p ++_) eD)) ∎

    -- prefix-lift fusion, as a sandwich (assocW towers collapse to castW).
    liftW-fuse : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
               → Sand (++-assoc x m v) (sym (++-assoc x m u))
                      (liftW x (liftW m W)) (liftW (x ++ m) W)
    liftW-fuse x m {u} {v} W = begin
      liftW x (liftW m W)
        ≈⟨ liftW-assoc' x m W ⟩
      assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u
        ≈⟨ assocW⁻-castW x m v ⟩∘⟨ refl⟩∘⟨ assocW-castW x m u ⟩
      castW (++-assoc x m v) ∘ liftW (x ++ m) W ∘ castW (sym (++-assoc x m u)) ∎

    -- a suffix-pad slides under a single prefix wire (α-naturality).
    rpad-⊗-peel : ∀ (sq : List X) (x : X) {n n'} (V : HomTerm (wires n) (wires n'))
                → rpad sq (id {Var x} ⊗₁ V) ≈Term id {Var x} ⊗₁ rpad sq V
    rpad-⊗-peel sq x {n} {n'} V = begin
      (id ⊗₁ merge n' ∘ α⇒) ∘ ((id ⊗₁ V) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ split n)
        ≈⟨ pullʳ (pullˡ α-comm) ⟩
      id ⊗₁ merge n' ∘ ((id ⊗₁ (V ⊗₁ id) ∘ α⇒) ∘ (α⇐ ∘ id ⊗₁ split n))
        ≈⟨ refl⟩∘⟨ cancelInner α⇒∘α⇐≈id ⟩
      id ⊗₁ merge n' ∘ (id ⊗₁ (V ⊗₁ id) ∘ id ⊗₁ split n)
        ≈⟨ id⊗-∘3 (merge n') (V ⊗₁ id) (split n) ⟩
      id ⊗₁ (merge n' ∘ (V ⊗₁ id) ∘ split n) ∎

    -- NEW COHERENCE 1: a suffix-pad past a prefix-lift.
    rpad-liftW : ∀ (sq p : List X) {u v} (W : HomTerm (wires u) (wires v))
               → Sand (sym (++-assoc p v sq)) (++-assoc p u sq)
                      (rpad sq (liftW p W)) (liftW p (rpad sq W))
    rpad-liftW sq [] {u} {v} W = ⟺ (idˡ ○ idʳ)
    rpad-liftW sq (x ∷ p) {u} {v} W = begin
      rpad sq (liftW (x ∷ p) W)
        ≈⟨ rpad-⊗-peel sq x (liftW p W) ⟩
      id ⊗₁ rpad sq (liftW p W)
        ≈⟨ refl⟩⊗⟨ rpad-liftW sq p W ⟩
      id ⊗₁ (castW (sym (++-assoc p v sq)) ∘ liftW p (rpad sq W) ∘ castW (++-assoc p u sq))
        ≈⟨ id⊗-∘3 _ _ _ ⟨
      id ⊗₁ castW (sym (++-assoc p v sq))
        ∘ id ⊗₁ liftW p (rpad sq W)
        ∘ id ⊗₁ castW (++-assoc p u sq)
        ≈⟨ castW-∷ (sym (++-assoc p v sq)) ⟩∘⟨ refl⟩∘⟨ castW-∷ (++-assoc p u sq) ⟩
      castW (cong (x ∷_) (sym (++-assoc p v sq)))
        ∘ liftW (x ∷ p) (rpad sq W)
        ∘ castW (cong (x ∷_) (++-assoc p u sq))
        ≈⟨ castW-irr _ _ ⟩∘⟨ refl⟩∘⟨ castW-irr _ _ ⟩
      castW (sym (++-assoc (x ∷ p) v sq))
        ∘ liftW (x ∷ p) (rpad sq W)
        ∘ castW (++-assoc (x ∷ p) u sq) ∎

    -- coeC / coeD (ReflectI's arbitrary-other-end coercions) are castWs.
    coeC-as-castW : ∀ {A} {p q : List X} (e : p ≡ q) (h : HomTerm A (wires p))
                  → coeC e h ≈Term castW e ∘ h
    coeC-as-castW refl h = ⟺ idˡ

    coeD-as-castW : ∀ {B} {p q : List X} (e : p ≡ q) (h : HomTerm (wires p) B)
                  → coeD e h ≈Term h ∘ castW (sym e)
    coeD-as-castW refl h = ⟺ idʳ

    -- NEW COHERENCE 2: suffix-pad fusion — ReflectI's `rpad-fuse`, recast
    -- from coeC/coeD form into the castW sandwich.
    rpad-rpad : ∀ (s sq : List X) {u v} (W : HomTerm (wires u) (wires v))
              → Sand (sym (++-assoc v s sq)) (++-assoc u s sq)
                     (rpad sq (rpad s W)) (rpad (s ++ sq) W)
    rpad-rpad s sq {u} {v} W = begin
      rpad sq (rpad s W)
        ≈⟨ rpad-fuse s sq W ⟩
      coeD (sym (++-assoc u s sq)) (coeC (sym (++-assoc v s sq)) (rpad (s ++ sq) W))
        ≈⟨ coeD-as-castW (sym (++-assoc u s sq)) _ ⟩
      coeC (sym (++-assoc v s sq)) (rpad (s ++ sq) W) ∘ castW (sym (sym (++-assoc u s sq)))
        ≈⟨ coeC-as-castW (sym (++-assoc v s sq)) _ ⟩∘⟨ castW-irr _ (++-assoc u s sq) ⟩
      (castW (sym (++-assoc v s sq)) ∘ rpad (s ++ sq) W) ∘ castW (++-assoc u s sq)
        ≈⟨ assoc ⟩
      castW (sym (++-assoc v s sq)) ∘ rpad (s ++ sq) W ∘ castW (++-assoc u s sq) ∎

  ------------------------------------------------------------------------
  -- THE TWO RE-CLEANINGS.  With the concrete block update `h = pad p₁ s₁
  -- G` (G generic — the DiagU instance is `G = ⟦box⟧S (box f)`), the two
  -- grouped box-layers of the slide are genuine clean DiagU pads at the
  -- composite offsets, conjugated by `++`-assoc casts.  Stated with the
  -- index equalities ∀-quantified (any proofs work, by Hedberg UIP).
  ------------------------------------------------------------------------

  -- the SLID box layer (box before the crossing, at offset pq++(a++p₁)).
  padBoxSlid : ∀ (pq sq a p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
               (eC : (pq ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sq))
                   ≡ pq ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sq))
               (eD : pq ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sq)
                   ≡ (pq ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sq)))
             → pad pq sq (liftW a (pad p₁ s₁ G))
               ≈Term castW eC ∘ pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G ∘ castW eD
  padBoxSlid pq sq a p₁ s₁ {u} {v} G eC eD = sand-irr SF
    where
      R = rpad (s₁ ++ sq) G
      S4 = rpad-rpad s₁ sq G
      S3 = sand-≈ˡ (rpad-resp sq (pad≡liftW p₁ s₁ G)) (rpad-liftW sq p₁ (rpad s₁ G))
      S3' = sand-trans S3 (liftW-sand p₁ S4)
      S2 = rpad-liftW sq a (pad p₁ s₁ G)
      S2' = sand-trans S2 (liftW-sand a S3')
      S2'' = sand-trans S2' (liftW-fuse a p₁ R)
      S1 = sand-≈ˡ (pad≡liftW pq sq (liftW a (pad p₁ s₁ G))) (liftW-sand pq S2'')
      S0 = sand-trans S1 (liftW-fuse pq (a ++ p₁) R)
      SF = sand-mid S0 (⟺ (pad≡liftW (pq ++ (a ++ p₁)) (s₁ ++ sq) G))

  -- the INPUT-order box layer (box after the crossing, inside the b-image
  -- at offset pq++p₁).
  padBoxIn : ∀ (pq sq a p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
             (eC : (pq ++ p₁) ++ (v ++ (s₁ ++ (a ++ sq)))
                 ≡ pq ++ (((p₁ ++ (v ++ s₁)) ++ a) ++ sq))
             (eD : pq ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sq)
                 ≡ (pq ++ p₁) ++ (u ++ (s₁ ++ (a ++ sq))))
           → pad pq sq (rpad a (pad p₁ s₁ G))
             ≈Term castW eC ∘ pad (pq ++ p₁) (s₁ ++ (a ++ sq)) G ∘ castW eD
  padBoxIn pq sq a p₁ s₁ {u} {v} G eC eD = sand-irr TF
    where
      R = rpad (s₁ ++ (a ++ sq)) G
      T4 = rpad-rpad s₁ (a ++ sq) G
      T3 = sand-≈ˡ (rpad-resp (a ++ sq) (pad≡liftW p₁ s₁ G))
                   (rpad-liftW (a ++ sq) p₁ (rpad s₁ G))
      T3' = sand-trans T3 (liftW-sand p₁ T4)
      T2 = rpad-rpad a sq (pad p₁ s₁ G)
      T2' = sand-trans T2 T3'
      T1 = sand-≈ˡ (pad≡liftW pq sq (rpad a (pad p₁ s₁ G))) (liftW-sand pq T2')
      T0 = sand-trans T1 (liftW-fuse pq p₁ R)
      TF = sand-mid T0 (⟺ (pad≡liftW (pq ++ p₁) (s₁ ++ (a ++ sq)) G))

  ------------------------------------------------------------------------
  -- THE ASSEMBLED CLEAN SLIDE.  Both box-layers are genuine clean DiagU
  -- pads; the four index casts are exactly the ones forced by the
  -- `++`-assoc gaps (any proofs of those equalities work).  The input
  -- order (crossing first, then the box inside its b-image) equals the
  -- slid order (box first at its pre-cross position, then the crossing
  -- with the updated b-block u ↦ v).
  ------------------------------------------------------------------------
  slide-clean :
    ∀ (pq sq a p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
      (e₁ : pq ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (u ++ (s₁ ++ (a ++ sq))))
      (e₂ : pq ++ (((p₁ ++ (v ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (v ++ (s₁ ++ (a ++ sq))))
      (e₃ : (pq ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sq))
          ≡ pq ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sq))
      (e₄ : pq ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sq)
          ≡ (pq ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sq)))
    → pad (pq ++ p₁) (s₁ ++ (a ++ sq)) G
        ∘ castW e₁
        ∘ pad pq sq (⟦box⟧S (cross a (p₁ ++ (u ++ s₁))))
      ≈Term castW e₂
        ∘ pad pq sq (⟦box⟧S (cross a (p₁ ++ (v ++ s₁))))
        ∘ castW e₃
        ∘ pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G
        ∘ castW e₄
  slide-clean pq sq a p₁ s₁ {u} {v} G e₁ e₂ e₃ e₄ = begin
    padIn ∘ (castW e₁ ∘ Cab)
      ≈⟨ sand-cancel e₁ Cab (padBoxIn pq sq a p₁ s₁ G (sym e₂) e₁) ⟩
    castW (sym (sym e₂)) ∘ (Gβ ∘ Cab)
      ≈⟨ castW-irr _ e₂ ⟩∘⟨ ⟺ (slide-pad pq sq a hᵇ) ⟩
    castW e₂ ∘ (Cab' ∘ Gα)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ padBoxSlid pq sq a p₁ s₁ G e₃ e₄ ⟩
    castW e₂ ∘ (Cab' ∘ (castW e₃ ∘ padSlid ∘ castW e₄)) ∎
    where
      hᵇ      = pad p₁ s₁ G
      Cab     = pad pq sq (⟦box⟧S (cross a (p₁ ++ (u ++ s₁))))
      Cab'    = pad pq sq (⟦box⟧S (cross a (p₁ ++ (v ++ s₁))))
      padIn   = pad (pq ++ p₁) (s₁ ++ (a ++ sq)) G
      padSlid = pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G
      Gβ      = pad pq sq (rpad a hᵇ)
      Gα      = pad pq sq (liftW a hᵇ)

  -- the DiagU instance: the block update is a genuine BOX `f : Mor c d`
  -- (`G = ⟦box⟧S (box f)`), i.e. the input order `cross a (p₁++(c++s₁))`
  -- then `box f` at offset pq++p₁ slides to `box f` at offset
  -- pq++(a++p₁) then `cross a (p₁++(d++s₁))`.
  slide-clean-box :
    ∀ (pq sq a p₁ s₁ : List X) {c d} (f : Mor c d)
      (e₁ : pq ++ (((p₁ ++ (c ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (c ++ (s₁ ++ (a ++ sq))))
      (e₂ : pq ++ (((p₁ ++ (d ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (d ++ (s₁ ++ (a ++ sq))))
      (e₃ : (pq ++ (a ++ p₁)) ++ (d ++ (s₁ ++ sq))
          ≡ pq ++ ((a ++ (p₁ ++ (d ++ s₁))) ++ sq))
      (e₄ : pq ++ ((a ++ (p₁ ++ (c ++ s₁))) ++ sq)
          ≡ (pq ++ (a ++ p₁)) ++ (c ++ (s₁ ++ sq)))
    → pad (pq ++ p₁) (s₁ ++ (a ++ sq)) (⟦box⟧S (box f))
        ∘ castW e₁
        ∘ pad pq sq (⟦box⟧S (cross a (p₁ ++ (c ++ s₁))))
      ≈Term castW e₂
        ∘ pad pq sq (⟦box⟧S (cross a (p₁ ++ (d ++ s₁))))
        ∘ castW e₃
        ∘ pad (pq ++ (a ++ p₁)) (s₁ ++ sq) (⟦box⟧S (box f))
        ∘ castW e₄
  slide-clean-box pq sq a p₁ s₁ f = slide-clean pq sq a p₁ s₁ (⟦box⟧S (box f))

  ------------------------------------------------------------------------
  -- THE a-BLOCK MIRROR.  The same slide for a box living inside the
  -- crossing's a-image block (the SUFFIX of the cross's output; the
  -- PREFIX of its input).  The core is `slide-core-a`; the two grouped
  -- box-layers re-clean through the SAME two lemmas with the roles of
  -- `padBoxIn`/`padBoxSlid` swapped (the input-order layer is now the
  -- prefix-lift `liftW b`, the slid layer the suffix-pad `rpad b`).
  ------------------------------------------------------------------------

  -- the padded a-block slide (mirror of `slide-pad`).
  slide-pad-a : ∀ (pq sq b : List X) {a a'} (g : HomTerm (wires a) (wires a'))
              → pad pq sq (⟦box⟧S (cross a' b)) ∘ pad pq sq (rpad b g)
                ≈Term pad pq sq (liftW b g) ∘ pad pq sq (⟦box⟧S (cross a b))
  slide-pad-a pq sq b {a} {a'} g = begin
    pad pq sq (⟦box⟧S (cross a' b)) ∘ pad pq sq (rpad b g)
      ≈⟨ pad-∘ pq sq (⟦box⟧S (cross a' b)) (rpad b g) ⟨
    pad pq sq (⟦box⟧S (cross a' b) ∘ rpad b g)
      ≈⟨ pad-resp pq sq (slide-core-a b g) ⟩
    pad pq sq (liftW b g ∘ ⟦box⟧S (cross a b))
      ≈⟨ pad-∘ pq sq (liftW b g) (⟦box⟧S (cross a b)) ⟩
    pad pq sq (liftW b g) ∘ pad pq sq (⟦box⟧S (cross a b)) ∎

  -- the assembled clean a-block slide.  The input order (crossing first,
  -- then the box inside its a-image) equals the slid order (box first at
  -- its pre-cross position — the a-block is the PREFIX of the cross's
  -- input — then the crossing with the updated a-block u ↦ v).
  slide-clean-a :
    ∀ (pq sq b p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
      (e₁ : pq ++ ((b ++ (p₁ ++ (u ++ s₁))) ++ sq)
          ≡ (pq ++ (b ++ p₁)) ++ (u ++ (s₁ ++ sq)))
      (e₂ : pq ++ ((b ++ (p₁ ++ (v ++ s₁))) ++ sq)
          ≡ (pq ++ (b ++ p₁)) ++ (v ++ (s₁ ++ sq)))
      (e₃ : (pq ++ p₁) ++ (v ++ (s₁ ++ (b ++ sq)))
          ≡ pq ++ (((p₁ ++ (v ++ s₁)) ++ b) ++ sq))
      (e₄ : pq ++ (((p₁ ++ (u ++ s₁)) ++ b) ++ sq)
          ≡ (pq ++ p₁) ++ (u ++ (s₁ ++ (b ++ sq))))
    → pad (pq ++ (b ++ p₁)) (s₁ ++ sq) G
        ∘ castW e₁
        ∘ pad pq sq (⟦box⟧S (cross (p₁ ++ (u ++ s₁)) b))
      ≈Term castW e₂
        ∘ pad pq sq (⟦box⟧S (cross (p₁ ++ (v ++ s₁)) b))
        ∘ castW e₃
        ∘ pad (pq ++ p₁) (s₁ ++ (b ++ sq)) G
        ∘ castW e₄
  slide-clean-a pq sq b p₁ s₁ {u} {v} G e₁ e₂ e₃ e₄ = begin
    padIn ∘ (castW e₁ ∘ Cab)
      ≈⟨ sand-cancel e₁ Cab (padBoxSlid pq sq b p₁ s₁ G (sym e₂) e₁) ⟩
    castW (sym (sym e₂)) ∘ (Gλ ∘ Cab)
      ≈⟨ castW-irr _ e₂ ⟩∘⟨ ⟺ (slide-pad-a pq sq b hₐ) ⟩
    castW e₂ ∘ (Cab' ∘ Gρ)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ padBoxIn pq sq b p₁ s₁ G e₃ e₄ ⟩
    castW e₂ ∘ (Cab' ∘ (castW e₃ ∘ padSlid ∘ castW e₄)) ∎
    where
      hₐ      = pad p₁ s₁ G
      Cab     = pad pq sq (⟦box⟧S (cross (p₁ ++ (u ++ s₁)) b))
      Cab'    = pad pq sq (⟦box⟧S (cross (p₁ ++ (v ++ s₁)) b))
      padIn   = pad (pq ++ (b ++ p₁)) (s₁ ++ sq) G
      padSlid = pad (pq ++ p₁) (s₁ ++ (b ++ sq)) G
      Gρ      = pad pq sq (rpad b hₐ)
      Gλ      = pad pq sq (liftW b hₐ)

  -- the DiagU instance of the a-block slide.
  slide-clean-box-a :
    ∀ (pq sq b p₁ s₁ : List X) {c d} (f : Mor c d)
      (e₁ : pq ++ ((b ++ (p₁ ++ (c ++ s₁))) ++ sq)
          ≡ (pq ++ (b ++ p₁)) ++ (c ++ (s₁ ++ sq)))
      (e₂ : pq ++ ((b ++ (p₁ ++ (d ++ s₁))) ++ sq)
          ≡ (pq ++ (b ++ p₁)) ++ (d ++ (s₁ ++ sq)))
      (e₃ : (pq ++ p₁) ++ (d ++ (s₁ ++ (b ++ sq)))
          ≡ pq ++ (((p₁ ++ (d ++ s₁)) ++ b) ++ sq))
      (e₄ : pq ++ (((p₁ ++ (c ++ s₁)) ++ b) ++ sq)
          ≡ (pq ++ p₁) ++ (c ++ (s₁ ++ (b ++ sq))))
    → pad (pq ++ (b ++ p₁)) (s₁ ++ sq) (⟦box⟧S (box f))
        ∘ castW e₁
        ∘ pad pq sq (⟦box⟧S (cross (p₁ ++ (c ++ s₁)) b))
      ≈Term castW e₂
        ∘ pad pq sq (⟦box⟧S (cross (p₁ ++ (d ++ s₁)) b))
        ∘ castW e₃
        ∘ pad (pq ++ p₁) (s₁ ++ (b ++ sq)) (⟦box⟧S (box f))
        ∘ castW e₄
  slide-clean-box-a pq sq b p₁ s₁ f = slide-clean-a pq sq b p₁ s₁ (⟦box⟧S (box f))

  ------------------------------------------------------------------------
  -- The decision module.  Parameters mirror the front-end's `Decide`: a
  -- decidable equality on the underlying generator triples and a rank
  -- tiebreak for ambiguous (mutually-fitting, scalar-like) pairs.
  ------------------------------------------------------------------------
  module Decide
    (_≟G_ : DecidableEquality GenM)
    (rank : GenM → ℕ)
    where

    private
      _≟L_ : DecidableEquality (List X)
      _≟L_ = ≡-dec _≟X_

    ------------------------------------------------------------------------
    -- Decidable equality on the EXTENDED generator triples, no-K style:
    -- the negative cases go through first-order projection functions
    -- (`tagS`/`boxPay`/`crossPay`), never a refl-match at the forced
    -- `++`-composite indices of `cross`.
    ------------------------------------------------------------------------

    private
      tagS : SCmp.Gen → Bool
      tagS (_ , _ , box _)     = true
      tagS (_ , _ , cross _ _) = false

      boxPay : SCmp.Gen → Maybe GenM
      boxPay (a , b , box f)     = just (a , b , f)
      boxPay (_ , _ , cross _ _) = nothing

      crossPay : SCmp.Gen → Maybe (List X × List X)
      crossPay (_ , _ , box _)     = nothing
      crossPay (_ , _ , cross a b) = just (a , b)

      true≢false : true ≡ false → ⊥
      true≢false ()

    _≟GS_ : DecidableEquality SCmp.Gen
    (a , b , box f) ≟GS (a' , b' , box g) = case (a , b , f) ≟G (a' , b' , g) of λ where
      (yes refl) → yes refl
      (no ¬p)    → no λ e → ¬p (just-injective (cong boxPay e))
    (a , b , box f)     ≟GS (_ , _ , cross c d) = no λ e → true≢false (cong tagS e)
    (_ , _ , cross a b) ≟GS (a' , b' , box g)   = no λ e → true≢false (sym (cong tagS e))
    (_ , _ , cross a b) ≟GS (_ , _ , cross c d) = case a ≟L c of λ where
      (no ¬p)    → no λ e → ¬p (cong proj₁ (just-injective (cong crossPay e)))
      (yes refl) → case b ≟L d of λ where
        (yes refl) → yes refl
        (no ¬q)    → no λ e → ¬q (cong proj₂ (just-injective (cong crossPay e)))

    open SCmp.Decide _≟GS_ using (_≈NF_; _≟DiagU_; ≈NF⇒≡)

    -- RANK: crosses sort below all boxes among ambiguous pairs; the
    -- caller's relative order on boxes is preserved.
    rankS : ∀ {a b} → MorS a b → ℕ
    rankS (box {a} {b} f) = suc (rank (a , b , f))
    rankS (cross _ _)     = zero

    ------------------------------------------------------------------------
    -- The one-step oracle: σσ-CANCEL first, then naturality slides, then
    -- disjoint interchange.
    -- `SwapRes`, `fire`, `ambiguous?`, `lift∷`, `swapTrans`, `depthD`,
    -- and `normFuelWith` come from NormalizeI.SortD (§12d) above.
    ------------------------------------------------------------------------

    private
      -- THE σσ-CANCEL FIRE.  On a recognised adjacent inverse cross-pair
      -- (same pre/suf, blocks reversed) BOTH layers are removed; the tail
      -- lives at the SAME input index, so no diagram transport is needed
      -- and the soundness is `pad-σσ` + assoc/id algebra.
      fireσ : ∀ (px sx a b : List X)
              (rest' : DiagU (px ++ ((a ++ b) ++ sx)))
            → SwapRes (px ▸ sx ∷ cross a b ⟨ px ▸ sx ∷ cross b a ⟨ rest' ⟩ ⟩)
      fireσ px sx a b rest' =
        rest' , refl , (idˡ ○ assoc ○ elimʳ (pad-σσ px sx a b))

      -- the σσ recogniser at the generalized inner index: fires exactly
      -- when the head layer is `cross a b` at (px,sx) and the next layer
      -- is `cross b a` at the SAME (px,sx).
      goσ : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
            {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
          → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      goσ px sx (box f)     rest meq = nothing
      goσ px sx (cross a b) ([]_ m) meq = nothing
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ {ay} {by} py sy (box f) rest') meq = nothing
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq
        with px ≟L py | sx ≟L sy | c ≟L b | d ≟L a
      ... | yes refl | yes refl | yes refl | yes refl
            rewrite ≡-irrelevantL meq refl = just (fireσ px sx a b rest')
      ... | no _  | _     | _     | _     = nothing
      ... | yes _ | no _  | _     | _     = nothing
      ... | yes _ | yes _ | no _  | _     = nothing
      ... | yes _ | yes _ | yes _ | no _  = nothing

      ------------------------------------------------------------------
      -- THE NATURALITY-SLIDE FIRE.  `fireRepl` is a generic sound
      -- two-layer head REPLACEMENT: the recognised head pair (g₁ fires,
      -- then g₂, inter-layer index bridged by `meq`) is replaced by the
      -- pair (g₃ then g₄, bridged by E₃), with the outer/inner
      -- re-indexings E₄/E₂ and a caller-supplied KEY equation between
      -- the two padded two-layer composites.  Soundness is pure
      -- `substDiagU`/`castW` algebra around the key; the slide
      -- instantiates the key with `slide-clean-box` (b-image block) or
      -- `slide-clean-box-a` (a-image block) at the discovered offsets.
      ------------------------------------------------------------------

      -- `substDiagU (sym e)` expanded to a two-sided cast conjugation.
      substExpand : ∀ {m n : List X} (e : m ≡ n) (d : DiagU n)
                  → ⟦ substDiagU (sym e) d ⟧
                    ≈Term castW (sym (substDiagU-out (sym e) d)) ∘ (⟦ d ⟧ ∘ castW e)
      substExpand refl d = ⟺ (idˡ ○ idʳ)

      -- `++`-assoc rebracketings for the slide's four index gaps.
      eq₁ : ∀ (pq p₁ x s₁ a sq : List X)
          → pq ++ (((p₁ ++ (x ++ s₁)) ++ a) ++ sq)
            ≡ (pq ++ p₁) ++ (x ++ (s₁ ++ (a ++ sq)))
      eq₁ pq p₁ x s₁ a sq =
        trans (cong (pq ++_)
                (trans (++-assoc (p₁ ++ (x ++ s₁)) a sq)
                  (trans (++-assoc p₁ (x ++ s₁) (a ++ sq))
                    (cong (p₁ ++_) (++-assoc x s₁ (a ++ sq))))))
              (sym (++-assoc pq p₁ (x ++ (s₁ ++ (a ++ sq)))))

      eq₃ : ∀ (pq a p₁ x s₁ sq : List X)
          → (pq ++ (a ++ p₁)) ++ (x ++ (s₁ ++ sq))
            ≡ pq ++ ((a ++ (p₁ ++ (x ++ s₁))) ++ sq)
      eq₃ pq a p₁ x s₁ sq =
        trans (++-assoc pq (a ++ p₁) (x ++ (s₁ ++ sq)))
          (trans (cong (pq ++_) (++-assoc a p₁ (x ++ (s₁ ++ sq))))
            (sym (cong (pq ++_)
              (trans (++-assoc a (p₁ ++ (x ++ s₁)) sq)
                (cong (a ++_)
                  (trans (++-assoc p₁ (x ++ s₁) sq)
                    (cong (p₁ ++_) (++-assoc x s₁ sq))))))))

      fireRepl :
        ∀ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : List X}
          {p₁L s₁L p₂L s₂L : List X} (p₃L s₃L p₄L s₄L : List X)
          {g₁ : MorS a₁ b₁} {g₂ : MorS a₂ b₂}
          (g₃ : MorS a₃ b₃) (g₄ : MorS a₄ b₄)
          (rest' : DiagU (p₂L ++ (b₂ ++ s₂L)))
          (meq : p₁L ++ (b₁ ++ s₁L) ≡ p₂L ++ (a₂ ++ s₂L))
          (E₂ : p₄L ++ (b₄ ++ s₄L) ≡ p₂L ++ (b₂ ++ s₂L))
          (E₃ : p₃L ++ (b₃ ++ s₃L) ≡ p₄L ++ (a₄ ++ s₄L))
          (E₄ : p₁L ++ (a₁ ++ s₁L) ≡ p₃L ++ (a₃ ++ s₃L))
          (key : pad p₂L s₂L (⟦box⟧S g₂) ∘ castW meq ∘ pad p₁L s₁L (⟦box⟧S g₁)
                 ≈Term castW E₂ ∘ pad p₄L s₄L (⟦box⟧S g₄) ∘ castW E₃
                       ∘ pad p₃L s₃L (⟦box⟧S g₃) ∘ castW E₄)
        → SwapRes (p₁L ▸ s₁L ∷ g₁ ⟨ substDiagU (sym meq) (p₂L ▸ s₂L ∷ g₂ ⟨ rest' ⟩) ⟩)
      fireRepl {a₁ = a₁} {p₁L = p₁L} {s₁L} {p₂L} {s₂L} p₃L s₃L p₄L s₄L
               {g₁} {g₂} g₃ g₄ rest' meq E₂ E₃ E₄ key
        = d' , oeq , snd
        where
          P₁ = pad p₁L s₁L (⟦box⟧S g₁)
          P₂ = pad p₂L s₂L (⟦box⟧S g₂)
          P₃ = pad p₃L s₃L (⟦box⟧S g₃)
          P₄ = pad p₄L s₄L (⟦box⟧S g₄)
          boxL   = p₂L ▸ s₂L ∷ g₂ ⟨ rest' ⟩
          dBody  = p₁L ▸ s₁L ∷ g₁ ⟨ substDiagU (sym meq) boxL ⟩
          inner₂ = substDiagU (sym E₂) rest'
          crossL = p₄L ▸ s₄L ∷ g₄ ⟨ inner₂ ⟩
          inner₃ = substDiagU (sym E₃) crossL
          slidL  = p₃L ▸ s₃L ∷ g₃ ⟨ inner₃ ⟩
          d' : DiagU (p₁L ++ (a₁ ++ s₁L))
          d' = substDiagU (sym E₄) slidL
          o₁ = substDiagU-out (sym meq) boxL
          o₂ = substDiagU-out (sym E₂) rest'
          o₃ = substDiagU-out (sym E₃) crossL
          o₄ = substDiagU-out (sym E₄) slidL
          cAll = trans (trans (sym o₂) (sym o₃)) (sym o₄)
          oeq : out dBody ≡ out d'
          oeq = trans o₁ cAll
          M = ⟦ rest' ⟧ ∘ (castW E₂ ∘ (P₄ ∘ (castW E₃ ∘ (P₃ ∘ castW E₄))))
          -- peel the substDiagU casts off ⟦ dBody ⟧, then fire the key.
          lemA : ⟦ dBody ⟧ ≈Term castW (sym o₁) ∘ M
          lemA = (substExpand meq boxL ⟩∘⟨refl) ○ assoc²βε
               ○ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ key)))
          -- peel the three substDiagU casts off ⟦ d' ⟧ and fuse them.
          lemB : ⟦ d' ⟧ ≈Term castW cAll ∘ M
          lemB = substExpand E₄ slidL
               ○ (refl⟩∘⟨ assoc)
               ○ (refl⟩∘⟨ ((substExpand E₃ crossL ⟩∘⟨refl) ○ assoc²βε))
               ○ (refl⟩∘⟨ refl⟩∘⟨
                    (assoc ○ (substExpand E₂ rest' ⟩∘⟨refl) ○ assoc²βε))
               ○ (refl⟩∘⟨ pullˡ (castW-∘ (sym o₂) (sym o₃)))
               ○ pullˡ (castW-∘ (trans (sym o₂) (sym o₃)) (sym o₄))
          snd : castW oeq ∘ ⟦ dBody ⟧ ≈Term ⟦ d' ⟧
          snd = (refl⟩∘⟨ lemA)
              ○ pullˡ (castW-∘ (sym o₁) oeq)
              ○ (castW-irr (trans (sym o₁) oeq) cAll ⟩∘⟨refl)
              ○ ⟺ lemB

      -- the b-IMAGE slide recogniser: head `cross a b` at (px,sx), second
      -- layer a box exhibited inside the crossing's b-image block
      -- (py = px ++ p₁ with b = p₁ ++ (u ++ s₁) and sy = s₁ ++ (a ++ sx)).
      -- On a hit the box slides BEFORE the crossing, to its pre-cross
      -- offset px ++ (a ++ p₁); the crossing's b-block updates u ↦ v.
      goSlideB : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
                 {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
               → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      goSlideB px sx (box f)     rest meq = nothing
      goSlideB px sx (cross a b) ([]_ m) meq = nothing
      goSlideB px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq = nothing
      goSlideB px sx (cross a b) (_▸_∷_⟨_⟩ {u} {v} py sy (box f) rest') meq
        with stripPrefix px py
      ... | nothing = nothing
      ... | just (p₁ , refl) with stripPrefix p₁ b
      ...   | nothing = nothing
      ...   | just (r₁ , refl) with stripPrefix u r₁
      ...     | nothing = nothing
      ...     | just (s₁ , refl) with sy ≟L (s₁ ++ (a ++ sx))
      ...       | no _ = nothing
      ...       | yes refl =
                  just (fireRepl (px ++ (a ++ p₁)) (s₁ ++ sx) px sx
                          (box f) (cross a (p₁ ++ (v ++ s₁)))
                          rest' meq
                          (eq₁ px p₁ v s₁ a sx)
                          (eq₃ px a p₁ v s₁ sx)
                          (sym (eq₃ px a p₁ u s₁ sx))
                          (slide-clean-box px sx a p₁ s₁ f meq
                            (eq₁ px p₁ v s₁ a sx)
                            (eq₃ px a p₁ v s₁ sx)
                            (sym (eq₃ px a p₁ u s₁ sx))))

      -- the a-IMAGE slide recogniser: head `cross a b` at (px,sx), second
      -- layer a box exhibited inside the crossing's a-image block
      -- (py = px ++ (b ++ p₁) with a = p₁ ++ (u ++ s₁) and sy = s₁ ++ sx).
      -- On a hit the box slides BEFORE the crossing, to its pre-cross
      -- offset px ++ p₁; the crossing's a-block updates u ↦ v.
      goSlideA : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
                 {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
               → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      goSlideA px sx (box f)     rest meq = nothing
      goSlideA px sx (cross a b) ([]_ m) meq = nothing
      goSlideA px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq = nothing
      goSlideA px sx (cross a b) (_▸_∷_⟨_⟩ {u} {v} py sy (box f) rest') meq
        with stripPrefix px py
      ... | nothing = nothing
      ... | just (r₀ , refl) with stripPrefix b r₀
      ...   | nothing = nothing
      ...   | just (p₁ , refl) with stripPrefix p₁ a
      ...     | nothing = nothing
      ...     | just (r₂ , refl) with stripPrefix u r₂
      ...       | nothing = nothing
      ...       | just (s₁ , refl) with sy ≟L (s₁ ++ sx)
      ...         | no _ = nothing
      ...         | yes refl =
                    just (fireRepl (px ++ p₁) (s₁ ++ (b ++ sx)) px sx
                            (box f) (cross (p₁ ++ (v ++ s₁)) b)
                            rest' meq
                            (sym (eq₃ px b p₁ v s₁ sx))
                            (sym (eq₁ px p₁ v s₁ b sx))
                            (eq₁ px p₁ u s₁ b sx)
                            (slide-clean-box-a px sx b p₁ s₁ f meq
                              (sym (eq₃ px b p₁ v s₁ sx))
                              (sym (eq₁ px p₁ v s₁ b sx))
                              (eq₁ px p₁ u s₁ b sx)))

      -- the interchange recogniser at the generalized inner index.
      goSwap : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
               {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
             → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      goSwap px sx fx ([]_ m) meq = nothing
      goSwap {ax} {bx} px sx fx (_▸_∷_⟨_⟩ {ay} {by} py sy fy rest') meq =
        case leftFit? px sx py sy fx fy of λ where
          nothing    → nothing
          (just fit) →
            if not (ambiguous? ax by (LeftFit.mid fit)) ∨ (rankS fy <ᵇ rankS fx)
              then just (fire fit rest' meq)
              else nothing

      -- the combined per-position oracle: σσ-cancel first, then the two
      -- naturality slides (b-image, then a-image), then interchange.
      go : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
           {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
         → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      go px sx fx rest meq =
        goσ      px sx fx rest meq <∣>
        goSlideB px sx fx rest meq <∣>
        goSlideA px sx fx rest meq <∣>
        goSwap   px sx fx rest meq

    -- one cancel-or-swap at the FIRST applicable position.
    stepσ? : ∀ {n} (d : DiagU n) → Maybe (SwapRes d)
    stepσ? ([]_ n) = nothing
    stepσ? (px ▸ sx ∷ fx ⟨ rest ⟩) =
      go px sx fx rest refl <∣>
      Data.Maybe.map
        (λ { (rest' , oeq , snd) →
             px ▸ sx ∷ fx ⟨ rest' ⟩ , oeq , lift∷ px sx fx oeq snd })
        (stepσ? rest)

    -- budget: a cancellation shrinks the diagram (so at most depth/2 of
    -- them); within a phase every move is monotone — an interchange swap
    -- removes one layer inversion and a slide removes one
    -- (cross-before-box) inversion while updating the cross's block — so
    -- each phase needs at most depth² moves.  depth³ + depth² + depth + 1
    -- over-approximates the total.  (Degenerate scalar-arity boxes at a
    -- block edge can make a slide and an interchange oscillate; the fuel
    -- then runs out and the pair is left undecided — soundness is
    -- unconditional whatever the fuel.)
    normσ : ∀ {n} (d : DiagU n) → SwapRes d
    normσ d = normFuelWith stepσ? (suc (k * k * k + k * k + k)) d
      where k = depthD d

    ------------------------------------------------------------------------
    -- The decision entry, mirroring the front-end's `decide?W`:
    -- reflect → normσ → ≟DiagU → chain the soundness witnesses.
    ------------------------------------------------------------------------
    decideσ? : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decideσ? {n} {m} f g with normσ (reflect f) | normσ (reflect g)
    ... | (df' , oeqf , sndf) | (dg' , oeqg , sndg) with df' ≟DiagU dg'
    ...   | no  _  = nothing
    ...   | yes eq = just (chain (≈NF⇒≡ eq))
      where
        half : ∀ (t : WTerm n m) (d' : DiagU n) (oeq : out (reflect t) ≡ out d')
             → castW oeq ∘ ⟦ reflect t ⟧ ≈Term ⟦ d' ⟧
             → embed t ≈Term castW (trans (sym oeq) (out-reflect t)) ∘ ⟦ d' ⟧
        half t d' oeq snd =
          ⟺ (reflect-sound t)
          ○ coeC-as-castW (out-reflect t) ⟦ reflect t ⟧
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

    -- the computing hit-witness (normalizes to ⊤ exactly on a hit).
    IsJust : ∀ {a} {A : Set a} → Maybe A → Set
    IsJust (just _) = ⊤
    IsJust nothing  = ⊥

    private
      extract : ∀ {a} {A : Set a} (x : Maybe A) → IsJust x → A
      extract (just a) _ = a

    -- reference-style entry point.
    solveσ! : ∀ {n m} (f g : WTerm n m)
              {hit : IsJust (decideσ? f g)} → embed f ≈Term embed g
    solveσ! f g {hit} = extract (decideσ? f g) hit

--------------------------------------------------------------------------------
-- TESTS: a concrete signature over ℕ-labelled wires.  Five generators:
-- three 1-wire boxes (kbox/k2box on wire colour 0 — distinguishable only by
-- `_≟G2_`/rank — and mbox on colour 2) and two 2-wire boxes (wbox/w2box,
-- for the straddle negative).  Machine-checked:
--   (i)   a σσ-cancellation hit (adjacent inverse cross-pair deletes), both
--         at the head and below a box layer;
--   (ii)  disjoint cross-box interchange (the crossing participates in the
--         bubble sort like an ordinary box);
--   (iii) negative cases (distinct boxes; a non-cancelling diagram);
--   (iv)  the Stage-B/C naturality slides wired into the driver: b-image
--         and a-image slides (head and deep), slide+cancel combined,
--         wire-level σ-naturality via two slides, and the negative
--         straddling-box case.
--------------------------------------------------------------------------------
module SigmaTests where

  open import Data.Nat using (ℕ)
  open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)

  data Gen2 : List ℕ → List ℕ → Set where
    kbox  : Gen2 (0 ∷ []) (0 ∷ [])
    k2box : Gen2 (0 ∷ []) (0 ∷ [])
    mbox  : Gen2 (2 ∷ []) (2 ∷ [])
    wbox  : Gen2 (1 ∷ 0 ∷ []) (1 ∷ 0 ∷ [])   -- 2-wire boxes, for the
    w2box : Gen2 (0 ∷ 1 ∷ []) (0 ∷ 1 ∷ [])   -- straddle negative

  open Sigma _≟ℕ_ Gen2

  private
    _≟G2_ : DecidableEquality GenM
    (_ , _ , kbox)  ≟G2 (_ , _ , kbox)  = yes refl
    (_ , _ , kbox)  ≟G2 (_ , _ , k2box) = no λ ()
    (_ , _ , kbox)  ≟G2 (_ , _ , mbox)  = no λ ()
    (_ , _ , kbox)  ≟G2 (_ , _ , wbox)  = no λ ()
    (_ , _ , kbox)  ≟G2 (_ , _ , w2box) = no λ ()
    (_ , _ , k2box) ≟G2 (_ , _ , kbox)  = no λ ()
    (_ , _ , k2box) ≟G2 (_ , _ , k2box) = yes refl
    (_ , _ , k2box) ≟G2 (_ , _ , mbox)  = no λ ()
    (_ , _ , k2box) ≟G2 (_ , _ , wbox)  = no λ ()
    (_ , _ , k2box) ≟G2 (_ , _ , w2box) = no λ ()
    (_ , _ , mbox)  ≟G2 (_ , _ , kbox)  = no λ ()
    (_ , _ , mbox)  ≟G2 (_ , _ , k2box) = no λ ()
    (_ , _ , mbox)  ≟G2 (_ , _ , mbox)  = yes refl
    (_ , _ , mbox)  ≟G2 (_ , _ , wbox)  = no λ ()
    (_ , _ , mbox)  ≟G2 (_ , _ , w2box) = no λ ()
    (_ , _ , wbox)  ≟G2 (_ , _ , kbox)  = no λ ()
    (_ , _ , wbox)  ≟G2 (_ , _ , k2box) = no λ ()
    (_ , _ , wbox)  ≟G2 (_ , _ , mbox)  = no λ ()
    (_ , _ , wbox)  ≟G2 (_ , _ , wbox)  = yes refl
    (_ , _ , wbox)  ≟G2 (_ , _ , w2box) = no λ ()
    (_ , _ , w2box) ≟G2 (_ , _ , kbox)  = no λ ()
    (_ , _ , w2box) ≟G2 (_ , _ , k2box) = no λ ()
    (_ , _ , w2box) ≟G2 (_ , _ , mbox)  = no λ ()
    (_ , _ , w2box) ≟G2 (_ , _ , wbox)  = no λ ()
    (_ , _ , w2box) ≟G2 (_ , _ , w2box) = yes refl

    rank2 : GenM → ℕ
    rank2 (_ , _ , kbox)  = 0
    rank2 (_ , _ , k2box) = 1
    rank2 (_ , _ , mbox)  = 2
    rank2 (_ , _ , wbox)  = 3
    rank2 (_ , _ , w2box) = 4

  open Decide _≟G2_ rank2

  ------------------------------------------------------------------------
  -- (i) σσ-cancellation.
  ------------------------------------------------------------------------
  w01 : List ℕ
  w01 = 0 ∷ 1 ∷ []

  -- cross then its inverse  ≈  id.
  tCancelL tCancelR : WTerm w01 w01
  tCancelL = boxʷ (cross (1 ∷ []) (0 ∷ [])) ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
  tCancelR = idʷ

  testCancel : IsJust (decideσ? tCancelL tCancelR)
  testCancel = tt

  -- the same pair fires below a leading box layer.
  tCancelDeepL tCancelDeepR : WTerm w01 w01
  tCancelDeepL = boxʷ (cross (1 ∷ []) (0 ∷ []))
              ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
              ∘ʷ (boxʷ (box kbox) ⊗ʷ idʷ {1 ∷ []})
  tCancelDeepR = boxʷ (box kbox) ⊗ʷ idʷ {1 ∷ []}

  testCancelDeep : IsJust (decideσ? tCancelDeepL tCancelDeepR)
  testCancelDeep = tt

  ------------------------------------------------------------------------
  -- (ii) disjoint cross-box interchange: the crossing (wires 0-1) and the
  -- box (wire 2) commute — decided by the existing bubble sort, with the
  -- crossing as an ordinary layer.
  ------------------------------------------------------------------------
  w012 : List ℕ
  w012 = 0 ∷ 1 ∷ 2 ∷ []

  layerCross : WTerm w012 (1 ∷ 0 ∷ 2 ∷ [])
  layerCross = boxʷ (cross (0 ∷ []) (1 ∷ [])) ⊗ʷ idʷ {2 ∷ []}

  layerBoxPre : WTerm w012 w012
  layerBoxPre = idʷ {0 ∷ 1 ∷ []} ⊗ʷ boxʷ (box mbox)

  layerBoxPost : WTerm (1 ∷ 0 ∷ 2 ∷ []) (1 ∷ 0 ∷ 2 ∷ [])
  layerBoxPost = idʷ {1 ∷ 0 ∷ []} ⊗ʷ boxʷ (box mbox)

  tIntL tIntR : WTerm w012 (1 ∷ 0 ∷ 2 ∷ [])
  tIntL = layerCross ∘ʷ layerBoxPre     -- box (offset 2) first, then cross
  tIntR = layerBoxPost ∘ʷ layerCross    -- cross first, then box

  testInterchange : IsJust (decideσ? tIntL tIntR)
  testInterchange = tt

  ------------------------------------------------------------------------
  -- (iii) negative cases: every `just` is a real proof, and these are
  -- genuinely not decided (distinct generators / non-cancelling pair).
  ------------------------------------------------------------------------
  testNegBoxes : decideσ? (boxʷ (box kbox)) (boxʷ (box k2box)) ≡ nothing
  testNegBoxes = refl

  testNegCancel : decideσ? tCancelL tCancelDeepR ≡ nothing
  testNegCancel = refl

  ------------------------------------------------------------------------
  -- Stage-B litmus: the clean naturality slide instantiates at concrete
  -- offsets (kbox slides past `cross [1] [0]` from its post-cross to its
  -- pre-cross position), with all four `++`-assoc index casts `refl`.
  ------------------------------------------------------------------------
  litSlide : _
  litSlide = slide-clean-box [] [] (1 ∷ []) [] [] kbox refl refl refl refl

  ------------------------------------------------------------------------
  -- (iv) the DiagU-level naturality SLIDE, wired into the driver.
  ------------------------------------------------------------------------
  w10 : List ℕ
  w10 = 1 ∷ 0 ∷ []

  -- b-image slide: kbox after the crossing (in the b-image prefix) is the
  -- same as kbox before the crossing (in the b suffix).
  tSlideL tSlideR : WTerm w10 w01
  tSlideL = (boxʷ (box kbox) ⊗ʷ idʷ {1 ∷ []}) ∘ʷ boxʷ (cross (1 ∷ []) (0 ∷ []))
  tSlideR = boxʷ (cross (1 ∷ []) (0 ∷ [])) ∘ʷ (idʷ {1 ∷ []} ⊗ʷ boxʷ (box kbox))

  testSlide : IsJust (decideσ? tSlideL tSlideR)
  testSlide = tt

  -- the same slide fires deep: below a leading k2box layer.
  tSlideDeepL tSlideDeepR : WTerm w10 w01
  tSlideDeepL = tSlideL ∘ʷ (idʷ {1 ∷ []} ⊗ʷ boxʷ (box k2box))
  tSlideDeepR = tSlideR ∘ʷ (idʷ {1 ∷ []} ⊗ʷ boxʷ (box k2box))

  testSlideDeep : IsJust (decideσ? tSlideDeepL tSlideDeepR)
  testSlideDeep = tt

  -- a-image slide + σσ-cancel combined: a box conjugated by an inverse
  -- cross-pair (sitting in the a-image between them) is the bare box.
  tSlideCancelL tSlideCancelR : WTerm w01 w01
  tSlideCancelL = boxʷ (cross (1 ∷ []) (0 ∷ []))
               ∘ʷ (idʷ {1 ∷ []} ⊗ʷ boxʷ (box kbox))
               ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
  tSlideCancelR = boxʷ (box kbox) ⊗ʷ idʷ {1 ∷ []}

  testSlideCancel : IsJust (decideσ? tSlideCancelL tSlideCancelR)
  testSlideCancel = tt

  -- σ-naturality at the wire level: TWO slides (kbox through the a-image,
  -- mbox through the b-image) reconcile box-before-cross with
  -- box-after-cross.
  w02 : List ℕ
  w02 = 0 ∷ 2 ∷ []

  tNatL tNatR : WTerm w02 (2 ∷ 0 ∷ [])
  tNatL = boxʷ (cross (0 ∷ []) (2 ∷ [])) ∘ʷ (boxʷ (box kbox) ⊗ʷ boxʷ (box mbox))
  tNatR = (boxʷ (box mbox) ⊗ʷ boxʷ (box kbox)) ∘ʷ boxʷ (cross (0 ∷ []) (2 ∷ []))

  testSlideNat : IsJust (decideσ? tNatL tNatR)
  testSlideNat = tt

  -- NEGATIVE: a box STRADDLING the two image blocks does not slide (and
  -- the pair is genuinely not decided).
  tStraddleL tStraddleR : WTerm w01 w10
  tStraddleL = boxʷ (box wbox) ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
  tStraddleR = boxʷ (cross (0 ∷ []) (1 ∷ [])) ∘ʷ boxʷ (box w2box)

  testNegStraddle : decideσ? tStraddleL tStraddleR ≡ nothing
  testNegStraddle = refl
