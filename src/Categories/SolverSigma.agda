{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-extension of the wire-level solver: block crossings as transparent
-- generators (boxes + `cross a b : MorS (a ++ b) (b ++ a)`), with the crossing
-- interpreted as the block braiding conjugated to flat wire coordinates:
--
--     ⟦box⟧S (cross a b) = merge b {a} ∘ σ ∘ split a {b}
--
-- The block involution `⟦cross b a⟧ ∘ ⟦cross a b⟧ ≈ id` needs NO σ-naturality
-- (only split∘merge cancellation + σ∘σ≈id); the naturality slide uses ONE
-- σ-naturality instance.  The `++`-assoc castW tax lives entirely in the final
-- re-cleaning of the two grouped box-layers into clean DiagU pads
-- (`slide-clean`/`slide-clean-a`).
--
-- RANK CONVENTION: the interchange tiebreak for ambiguous (scalar-like) pairs
-- ranks crosses at 0 and boxes at `suc ∘ rank` of the caller's rank, so
-- crossings sort below all boxes and the caller's box order is preserved.
--------------------------------------------------------------------------------

module Categories.SolverSigma where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
import Data.List.Properties.Ext as ListExt
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.DiagramRewriteUntyped using (module WireSig; module UntypedI)
open import Categories.FreeMonoidal
open import Categories.SolverCompare using (module SolverCompareI)
open import Categories.SolverFrontendCore using (module MaybeHit)
open import Categories.SolverNormalize using (module NormalizeI)
open import Categories.SolverReflect using (module ReflectI; module DecideCore)

module Sigma {X : Set} (_≟X_ : DecidableEquality X)
             (Mor : List X → List X → Set) where

  -- UIP on the wire lists, via Hedberg (decidable equality), --without-K.
  private
    ≡-irrelevantL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevantL = ListExt.≡-irrelevant _≟X_

  ------------------------------------------------------------------------
  -- Extended generator family: boxes + transparent block crossings
  ------------------------------------------------------------------------
  data MorS : List X → List X → Set where
    box   : ∀ {a b} → Mor a b → MorS a b
    cross : (a b : List X) → MorS (a ++ b) (b ++ a)

  -- Qualified (`WS.`) here — `open UntypedI` below re-exports the same WireSig
  -- surface publicly, and a second anonymous open would be ambiguous (module
  -- application is name-generative).
  private module WS = WireSig Symm {X} MorS
  open FreeMonoidalHelper Symm X using (ObjTerm)
  open FreeMonoidalHelper.Mor Symm X WS.mor hiding (merge; split; merge∘split; split∘merge)

  ------------------------------------------------------------------------
  -- Interpretation: boxes opaque; a crossing is the conjugated braiding
  ------------------------------------------------------------------------
  ⟦box⟧S : ∀ {a b} → MorS a b → HomTerm (WS.wires a) (WS.wires b)
  ⟦box⟧S (box f)     = var (WS.box (box f))
  ⟦box⟧S (cross a b) = WS.merge b {a} ∘ σ ∘ WS.split a {b}

  open UntypedI Symm {X} MorS ⟦box⟧S public
  open ≈R

  open MR FreeMonoidal
    using (pullˡ; pullʳ; cancelˡ; cancelInner; insertInner; elimʳ)
  open MonR Monoidal-FreeMonoidal
    using (refl⟩⊗⟨_)

  open ReflectI Symm {X} _≟X_ MorS ⟦box⟧S public

  ------------------------------------------------------------------------
  -- Block involution (no σ-naturality: split∘merge + σ∘σ≈id only)
  ------------------------------------------------------------------------
  private
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
  -- Padded involution (inverse cross-pair at the same offsets = id)
  ------------------------------------------------------------------------
  private
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
  -- Normalize / compare stack
  ------------------------------------------------------------------------
  open NormalizeI Symm {X} _≟X_ MorS ⟦box⟧S using
    ( castW-irr
    ; substDiagU
    ; assocW-castW; assocW⁻-castW; liftW-castW
    ; module SortD )
  open SortD using (_≟L_; stripPrefix; SwapRes; depthD; normFuelWith; interchangeGo; stepWith; fireRepl)

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
  private
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
  private
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
  private
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

  private
    -- the conjugation-by-index-casts relation.
    Sand : ∀ {p q w t : List X} (eC : t ≡ q) (eD : p ≡ w)
         → HomTerm (wires p) (wires q) → HomTerm (wires w) (wires t) → Set
    Sand eC eD Y Z = Y ≈Term castW eC ∘ Z ∘ castW eD

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

    -- NEW COHERENCE 1: a suffix-pad past a prefix-lift.
    rpad-liftW : ∀ (sq p : List X) {u v} (W : HomTerm (wires u) (wires v))
               → Sand (sym (++-assoc p v sq)) (++-assoc p u sq)
                      (rpad sq (liftW p W)) (liftW p (rpad sq W))
    rpad-liftW sq [] {u} {v} W = ⟺ (idˡ ○ idʳ)
    rpad-liftW sq (x ∷ p) {u} {v} W = begin
      rpad sq (liftW (x ∷ p) W)
        ≈⟨ rpad-id⊗ sq x (liftW p W) ⟩
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

    -- NEW COHERENCE 2: suffix-pad fusion — ReflectI's `rpad-fuse` is already in
    -- the castW sandwich form; we only reassociate and normalise the trailing
    -- `castW (sym (sym _))` to `castW _` (UIP via `castW-irr`).
    rpad-rpad : ∀ (s sq : List X) {u v} (W : HomTerm (wires u) (wires v))
              → Sand (sym (++-assoc v s sq)) (++-assoc u s sq)
                     (rpad sq (rpad s W)) (rpad (s ++ sq) W)
    rpad-rpad s sq {u} {v} W = begin
      rpad sq (rpad s W)
        ≈⟨ rpad-fuse s sq W ⟩
      (castW (sym (++-assoc v s sq)) ∘ rpad (s ++ sq) W) ∘ castW (sym (sym (++-assoc u s sq)))
        ≈⟨ assoc ⟩
      castW (sym (++-assoc v s sq)) ∘ rpad (s ++ sq) W ∘ castW (sym (sym (++-assoc u s sq)))
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ castW-irr (sym (sym (++-assoc u s sq))) (++-assoc u s sq) ⟩
      castW (sym (++-assoc v s sq)) ∘ rpad (s ++ sq) W ∘ castW (++-assoc u s sq) ∎

  ------------------------------------------------------------------------
  -- THE TWO RE-CLEANINGS.  With the concrete block update `h = pad p₁ s₁
  -- G` (G generic — the DiagU instance is `G = ⟦box⟧S (box f)`), the two
  -- grouped box-layers of the slide are genuine clean DiagU pads at the
  -- composite offsets, conjugated by `++`-assoc casts.  Stated with the
  -- index equalities ∀-quantified (any proofs work, by Hedberg UIP).
  ------------------------------------------------------------------------

  -- the SLID box layer (box before the crossing, at offset pq++(a++p₁)).
  private
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
  private
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

  ------------------------------------------------------------------------
  -- THE a-BLOCK MIRROR.  The same slide for a box living inside the
  -- crossing's a-image block (the SUFFIX of the cross's output; the
  -- PREFIX of its input).  The core is `slide-core-a`; the two grouped
  -- box-layers re-clean through the SAME two lemmas with the roles of
  -- `padBoxIn`/`padBoxSlid` swapped (the input-order layer is the
  -- prefix-lift `liftW b`, the slid layer the suffix-pad `rpad b`).
  ------------------------------------------------------------------------

  -- the padded a-block slide (mirror of `slide-pad`).
  private
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
  private
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

  ------------------------------------------------------------------------
  -- The decision module.  Parameters mirror the front-end's `Decide`: a
  -- decidable equality on the underlying generator triples and a rank
  -- tiebreak for ambiguous (mutually-fitting, scalar-like) pairs.
  ------------------------------------------------------------------------
  module Decide
    (_≟G_ : DecidableEquality GenM)
    (rank : GenM → ℕ)
    where

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

    -- RANK: crosses sort below all boxes among ambiguous pairs; the
    -- caller's relative order on boxes is preserved.
    rankS : ∀ {a b} → MorS a b → ℕ
    rankS (box {a} {b} f) = suc (rank (a , b , f))
    rankS (cross _ _)     = zero

    ------------------------------------------------------------------------
    -- The one-step oracle: σσ-CANCEL first, then naturality slides, then
    -- disjoint interchange.
    -- `SwapRes`, `depthD`, `normFuelWith`, `interchangeGo`, `stepWith`
    -- come from NormalizeI.SortD (§12d) above.
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
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ py sy (box f) rest') meq = nothing
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq
        with px ≟L py | sx ≟L sy | c ≟L b | d ≟L a
      ... | yes refl | yes refl | yes refl | yes refl
            rewrite ≡-irrelevantL meq refl = just (fireσ px sx a b rest')
      ... | _ | _ | _ | _ = nothing

      ------------------------------------------------------------------
      -- THE NATURALITY-SLIDE FIRE.  `fireRepl` (from SortD §12d) is a
      -- generic sound two-layer head REPLACEMENT: the recognised head
      -- pair (g₁ then g₂, bridged by `meq`) is replaced by (g₃ then g₄,
      -- bridged by E₃), with re-indexings E₄/E₂ and a caller-supplied
      -- KEY equation; `substExpand` likewise from SortD.  The slide
      -- instantiates the key with `slide-clean` (b-image, G = ⟦box⟧S (box f))
      -- or `slide-clean-a` (a-image) at the discovered offsets.
      ------------------------------------------------------------------

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
                          -- DiagU instance: G = ⟦box⟧S (box f)
                          (slide-clean px sx a p₁ s₁ (⟦box⟧S (box f)) meq
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
                            -- DiagU instance: G = ⟦box⟧S (box f)
                            (slide-clean-a px sx b p₁ s₁ (⟦box⟧S (box f)) meq
                              (sym (eq₃ px b p₁ v s₁ sx))
                              (sym (eq₁ px p₁ v s₁ b sx))
                              (eq₁ px p₁ u s₁ b sx)))

      -- the combined per-position oracle: σσ-cancel first, then the two
      -- naturality slides (b-image, then a-image), then disjoint interchange
      -- (the generic `interchangeGo` at the σ-rank, from SortD §12e).
      go : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
           {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
         → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      go px sx fx rest meq =
        goσ           px sx fx rest meq <∣>
        goSlideB      px sx fx rest meq <∣>
        goSlideA      px sx fx rest meq <∣>
        interchangeGo rankS px sx fx rest meq

    -- one cancel-or-swap at the FIRST applicable position (the generic loop
    -- from SortD §12e at the σ oracle).
    stepσ? : ∀ {n} (d : DiagU n) → Maybe (SwapRes d)
    stepσ? = stepWith go

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
    -- The decision entry: the shared `DecideCore` assembly at `normσ`
    -- (reflect → normσ → ≟DiagU → chain the soundness witnesses).
    ------------------------------------------------------------------------
    private module DC = DecideCore Symm {X} _≟X_ MorS ⟦box⟧S
    open DC.Decide _≟GS_ normσ public using () renaming (decideW to decideσ?)

    -- the computing hit-witness (normalizes to ⊤ exactly on a hit; the shared
    -- definition from `MaybeHit`); relied on by the `SigmaTests` witnesses below.
    open MaybeHit public using (IsJust)

--------------------------------------------------------------------------------
-- TESTS: a concrete signature over ℕ-labelled wires, given as a Fin-5 arity
-- table (so DecEq and rank come from `Fin`).  Five generators: three 1-wire
-- boxes (kbox/k2box on wire colour 0 — distinguishable only by the rank
-- tiebreak — and mbox on colour 2) and two 2-wire boxes (wbox/w2box, for the
-- straddle negative).  Machine-checked:
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

  open import Data.Fin using (Fin; zero; suc; toℕ)
  open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
  open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)

  -- Fin-indexed signature (cf. SolverFrontendTests): decidable equality and the rank
  -- tiebreak come for free from `Fin`'s `_≟_`/`toℕ`, instead of a quadratic
  -- hand-rolled table.  Five 1-/2-wire endo-boxes:
  --   0 kbox, 1 k2box  — distinct scalars on colour 0 (need the rank tiebreak)
  --   2 mbox           — endo on colour 2
  --   3 wbox, 4 w2box  — 2-wire boxes, for the straddle negative
  arity2 : Fin 5 → List ℕ × List ℕ
  arity2 zero                         = (0 ∷ []) , (0 ∷ [])
  arity2 (suc zero)                   = (0 ∷ []) , (0 ∷ [])
  arity2 (suc (suc zero))             = (2 ∷ []) , (2 ∷ [])
  arity2 (suc (suc (suc zero)))       = (1 ∷ 0 ∷ []) , (1 ∷ 0 ∷ [])
  arity2 (suc (suc (suc (suc _))))    = (0 ∷ 1 ∷ []) , (0 ∷ 1 ∷ [])

  data Gen2 : List ℕ → List ℕ → Set where
    gen2 : (i : Fin 5) → Gen2 (proj₁ (arity2 i)) (proj₂ (arity2 i))

  -- readable aliases matching the test bodies.
  kbox  = gen2 zero
  k2box = gen2 (suc zero)
  mbox  = gen2 (suc (suc zero))
  wbox  = gen2 (suc (suc (suc zero)))
  w2box = gen2 (suc (suc (suc (suc zero))))

  open Sigma _≟ℕ_ Gen2

  private
    _≟G2_ : DecidableEquality GenM
    (_ , _ , gen2 i) ≟G2 (_ , _ , gen2 j) = case i ≟Fin j of λ where
      (yes refl) → yes refl
      (no ¬p)    → no λ where refl → ¬p refl

    rank2 : GenM → ℕ
    rank2 (_ , _ , gen2 i) = toℕ i

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
  -- DiagU instance: G = ⟦box⟧S (box kbox)
  litSlide : _
  litSlide = slide-clean [] [] (1 ∷ []) [] [] (⟦box⟧S (box kbox)) refl refl refl refl

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
