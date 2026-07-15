{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-extension of the wire-level solver: block crossings as transparent
-- generators (boxes + `cross a b : MorS (a ++ b) (b ++ a)`), with the crossing
-- interpreted as the block braiding conjugated to flat wire coordinates:
--
--     ⟦ cross a b ⟧ᵇˢ = merge b {a} ∘ σ ∘ split a {b}
--
-- The block involution `⟦cross b a⟧ ∘ ⟦cross a b⟧ ≈ id` needs NO σ-naturality
-- (only split∘merge cancellation + σ∘σ≈id); the naturality slide uses ONE
-- σ-naturality instance.  The `++`-assoc castW tax lives entirely in the final
-- re-cleaning of the two grouped box-layers into clean Diag pads
-- (`slide-clean`/`slide-clean-a`).
--
-- RANK CONVENTION: the interchange tiebreak for ambiguous (scalar-like) pairs
-- ranks crosses at 0 and boxes at `suc ∘ rank` of the caller's rank, so
-- crossings sort below all boxes and the caller's box order is preserved.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Sigma where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)

open import Data.List.Properties
import Data.List.Properties.Ext as ListExt
open import Data.Maybe.Properties

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Compare
open import Categories.Coherence.Monoidal.Normalize
open import Categories.Coherence.Monoidal.Reflect

module Sigma {X : Set} ⦃ _ : DecEq X ⦄ (Mor : List X → List X → Set) where

  ------------------------------------------------------------------------
  -- Extended generator family: boxes + transparent block crossings
  ------------------------------------------------------------------------
  data MorS : List X → List X → Set where
    box   : ∀ {a b} → Mor a b → MorS a b
    cross : (a b : List X) → MorS (a ++ b) (b ++ a)

  private module WS = WireSig Symm MorS
  open FreeMonoidalHelper.Mor Symm X WS.mor

  ------------------------------------------------------------------------
  -- Interpretation: boxes opaque; a crossing is the conjugated braiding
  ------------------------------------------------------------------------
  ⟦_⟧ᵇˢ : ∀ {a b} → MorS a b → HomTerm (WS.wires a) (WS.wires b)
  ⟦ box f ⟧ᵇˢ     = var (WS.box (box f))
  ⟦ cross a b ⟧ᵇˢ = merge b ∘ σ ∘ split a

  -- the σ-engine instance, shared by the wire-level modules below.
  ES : WireEngine Symm
  ES = record { Mor = MorS ; ⟦_⟧ᵇ = ⟦_⟧ᵇˢ }

  open DiagramI ES public
  open ≈R

  open MR FreeMonoidal
  open MonR Monoidal-FreeMonoidal using (refl⟩⊗⟨_)

  open ReflectI ES public

  -- block involution (no σ-naturality: split∘merge + σ∘σ≈id only).
  private
    σσ-block : ∀ (a b : List X) → ⟦ cross b a ⟧ᵇˢ ∘ ⟦ cross a b ⟧ᵇˢ ≈Term id
    σσ-block a b = begin
      (merge a ∘ σ ∘ split b) ∘ (merge b ∘ σ ∘ split a)
        ≈⟨ pullʳ (cancelInner (split∘merge b)) ⟩
      merge a ∘ (σ ∘ (σ ∘ split a))
        ≈⟨ refl⟩∘⟨ cancelˡ σ∘σ≈id ⟩
      merge a ∘ split a
        ≈⟨ merge∘split a ⟩
      id ∎

  -- padded involution (inverse cross-pair at the same offsets = id).
  private
    pad-σσ : ∀ (pre suf a b : List X)
           → pad pre suf (⟦ cross b a ⟧ᵇˢ) ∘ pad pre suf (⟦ cross a b ⟧ᵇˢ)
             ≈Term id
    pad-σσ pre suf a b = begin
      pad pre suf (⟦ cross b a ⟧ᵇˢ) ∘ pad pre suf (⟦ cross a b ⟧ᵇˢ)
        ≈⟨ pad-∘ pre suf (⟦ cross b a ⟧ᵇˢ) (⟦ cross a b ⟧ᵇˢ) ⟨
      pad pre suf (⟦ cross b a ⟧ᵇˢ ∘ ⟦ cross a b ⟧ᵇˢ)
        ≈⟨ pad-resp pre suf (σσ-block a b) ⟩
      pad pre suf id
        ≈⟨ pad-id pre suf ⟩
      id ∎

  ------------------------------------------------------------------------
  -- Normalize / compare stack
  ------------------------------------------------------------------------
  open NormalizeI ES
  open SortD

  private module SCmp = CompareI ES

  GenM : Set
  GenM = Σ[ a ∈ List X ] Σ[ b ∈ List X ] Mor a b

  ------------------------------------------------------------------------
  -- The naturality-slide CORE — a box after the crossing ≈ the box
  -- before it (pre-cross position).  ONE instance of braiding naturality
  -- σ∘[f⊗g]≈[g⊗f]∘σ + split/merge cancellation.  Stated for an ARBITRARY block
  -- update `h`, which keeps the block-level statement and its `pad` lift CAST-FREE.
  ------------------------------------------------------------------------
  private
    slide-core : ∀ (a : List X) {b b' : List X} (h : HomTerm (wires b) (wires b'))
               → ⟦ cross a b' ⟧ᵇˢ ∘ liftW a h
                 ≈Term rpad a h ∘ ⟦ cross a b ⟧ᵇˢ
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
                 → ⟦ cross a' b ⟧ᵇˢ ∘ rpad b g
                   ≈Term liftW b g ∘ ⟦ cross a b ⟧ᵇˢ
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

  -- pad transport of a composite equation: a `slide-core`-shaped equality of
  -- composites lifts through a common `pad pq sq` frame (the b/a-block slides
  -- below are its two instances).
  private
    pad-∘-resp : ∀ (pq sq : List X) {a b b' c}
      {P  : HomTerm (wires b) (wires c)} {Q : HomTerm (wires a) (wires b)}
      {P' : HomTerm (wires b') (wires c)} {Q' : HomTerm (wires a) (wires b')}
      → P ∘ Q ≈Term P' ∘ Q'
      → pad pq sq P ∘ pad pq sq Q ≈Term pad pq sq P' ∘ pad pq sq Q'
    pad-∘-resp pq sq {P = P} {Q} {P'} {Q'} eq =
      ⟺ (pad-∘ pq sq P Q) ○ pad-resp pq sq eq ○ pad-∘ pq sq P' Q'

  -- THE PADDED SLIDE (grouped coordinates): the same equation under an
  -- arbitrary `pad pq sq` frame — still fully cast-free, via the `pad-∘` /
  -- `pad-resp` functoriality.
  private
    slide-pad : ∀ (pq sq a : List X) {b b'} (h : HomTerm (wires b) (wires b'))
      → pad pq sq (⟦ cross a b' ⟧ᵇˢ) ∘ pad pq sq (liftW a h)
        ≈Term pad pq sq (rpad a h) ∘ pad pq sq (⟦ cross a b ⟧ᵇˢ)
    slide-pad pq sq a h = pad-∘-resp pq sq (slide-core a h)

  ------------------------------------------------------------------------
  -- Re-cleaning: the two grouped box-layers as clean Diag pads.
  ------------------------------------------------------------------------
  -- Re-expressing the slide's grouped layers as genuine clean Diag pads
  -- at the composite offsets is where the castW tax lives. The interface
  -- is the `isConjugate eC eD Y Z` relation (Y is Z retyped on both ends by
  -- the casts `castW eC`/`castW eD`).  The relation, its engine-generic
  -- combinators, and the three pad-fusion laws the re-cleanings chain below
  -- (`rpad-liftW`/`rpad-rpad`/`liftW-fuse`) all live in `WireCoh.WireCohDec`
  -- (re-exported through `NormalizeI`'s `public` open); nothing σ-specific is
  -- needed here.

  ------------------------------------------------------------------------
  -- THE TWO RE-CLEANINGS (concrete block update `h = pad p₁ s₁ G`).
  ------------------------------------------------------------------------
  -- The index equalities are ∀-quantified — any proofs work, by Hedberg UIP.

  -- the SLID box layer (box before the crossing, at offset pq++(a++p₁)).
  private
    padBoxSlid : ∀ (pq sq a p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
                 (eC : (pq ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sq))
                     ≡ pq ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sq))
                 (eD : pq ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sq)
                     ≡ (pq ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sq)))
               → pad pq sq (liftW a (pad p₁ s₁ G))
                 ≈Term castW eC ∘ pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G ∘ castW eD
    padBoxSlid pq sq a p₁ s₁ {u} {v} G eC eD = conj-toSandwich (conj-irr SF)
     where
       R = rpad (s₁ ++ sq) G
       S4 = rpad-rpad s₁ sq G
       S3 = conj-≈ˡ (rpad-resp sq (pad≡liftW p₁ s₁ G)) (rpad-liftW sq p₁ (rpad s₁ G))
       S3' = conj-trans S3 (liftW-conj p₁ S4)
       S2 = rpad-liftW sq a (pad p₁ s₁ G)
       S2' = conj-trans S2 (liftW-conj a S3')
       S2'' = conj-trans S2' (liftW-fuse a p₁ R)
       S1 = conj-≈ˡ (pad≡liftW pq sq (liftW a (pad p₁ s₁ G))) (liftW-conj pq S2'')
       S0 = conj-trans S1 (liftW-fuse pq (a ++ p₁) R)
       SF = conj-mid S0 (⟺ (pad≡liftW (pq ++ (a ++ p₁)) (s₁ ++ sq) G))

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
    padBoxIn pq sq a p₁ s₁ {u} {v} G eC eD = conj-toSandwich (conj-irr TF)
     where
       R = rpad (s₁ ++ (a ++ sq)) G
       T4 = rpad-rpad s₁ (a ++ sq) G
       T3 = conj-≈ˡ (rpad-resp (a ++ sq) (pad≡liftW p₁ s₁ G))
                    (rpad-liftW (a ++ sq) p₁ (rpad s₁ G))
       T3' = conj-trans T3 (liftW-conj p₁ T4)
       T2 = rpad-rpad a sq (pad p₁ s₁ G)
       T2' = conj-trans T2 T3'
       T1 = conj-≈ˡ (pad≡liftW pq sq (rpad a (pad p₁ s₁ G))) (liftW-conj pq T2')
       T0 = conj-trans T1 (liftW-fuse pq p₁ R)
       TF = conj-mid T0 (⟺ (pad≡liftW (pq ++ p₁) (s₁ ++ (a ++ sq)) G))

  -- The assembled clean slide (input order ≈ slid order, both clean pads).
  -- The four index casts are exactly those forced by the `++`-assoc gaps.
  slide-clean :
    ∀ (pq sq a p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
      {e₁ : pq ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (u ++ (s₁ ++ (a ++ sq)))}
      {e₂ : pq ++ (((p₁ ++ (v ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (v ++ (s₁ ++ (a ++ sq)))}
      {e₃ : (pq ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sq))
          ≡ pq ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sq)}
      {e₄ : pq ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sq)
          ≡ (pq ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sq))}
    → pad (pq ++ p₁) (s₁ ++ (a ++ sq)) G
        ∘ castW e₁
        ∘ pad pq sq (⟦ cross a (p₁ ++ (u ++ s₁)) ⟧ᵇˢ)
      ≈Term castW e₂
        ∘ pad pq sq (⟦ cross a (p₁ ++ (v ++ s₁)) ⟧ᵇˢ)
        ∘ castW e₃
        ∘ pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G
        ∘ castW e₄
  slide-clean pq sq a p₁ s₁ {u} {v} G {e₁} {e₂} {e₃} {e₄} = begin
    padIn ∘ (castW e₁ ∘ Cab)
      ≈⟨ conj-cancel e₁ Cab (conj-fromSandwich (padBoxIn pq sq a p₁ s₁ G (sym e₂) e₁)) ⟩
    castW (sym (sym e₂)) ∘ (Gβ ∘ Cab)
      ≈⟨ castW-irr _ e₂ ⟩∘⟨ ⟺ (slide-pad pq sq a hᵇ) ⟩
    castW e₂ ∘ (Cab' ∘ Gα)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ padBoxSlid pq sq a p₁ s₁ G e₃ e₄ ⟩
    castW e₂ ∘ (Cab' ∘ (castW e₃ ∘ padSlid ∘ castW e₄)) ∎
    where
      hᵇ      = pad p₁ s₁ G
      Cab     = pad pq sq (⟦ cross a (p₁ ++ (u ++ s₁)) ⟧ᵇˢ)
      Cab'    = pad pq sq (⟦ cross a (p₁ ++ (v ++ s₁)) ⟧ᵇˢ)
      padIn   = pad (pq ++ p₁) (s₁ ++ (a ++ sq)) G
      padSlid = pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G
      Gβ      = pad pq sq (rpad a hᵇ)
      Gα      = pad pq sq (liftW a hᵇ)

  -- The a-block mirror (box inside the crossing's a-image block): same slide
  -- via `slide-core-a`; the two layers re-clean through the SAME lemmas with
  -- the input-order/slid roles swapped (prefix-lift `liftW b` vs suffix-pad `rpad b`).

  -- the padded a-block slide (mirror of `slide-pad`).
  private
    slide-pad-a : ∀ (pq sq b : List X) {a a'} (g : HomTerm (wires a) (wires a'))
                → pad pq sq (⟦ cross a' b ⟧ᵇˢ) ∘ pad pq sq (rpad b g)
                  ≈Term pad pq sq (liftW b g) ∘ pad pq sq (⟦ cross a b ⟧ᵇˢ)
    slide-pad-a pq sq b g = pad-∘-resp pq sq (slide-core-a b g)

  -- the assembled clean a-block slide.  The input order (crossing first,
  -- then the box inside its a-image) equals the slid order (box first at
  -- its pre-cross position — the a-block is the PREFIX of the cross's
  -- input — then the crossing with the updated a-block u ↦ v).
  slide-clean-a :
   ∀ (pq sq b p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
     {e₁ : pq ++ ((b ++ (p₁ ++ (u ++ s₁))) ++ sq)
         ≡ (pq ++ (b ++ p₁)) ++ (u ++ (s₁ ++ sq))}
     {e₂ : pq ++ ((b ++ (p₁ ++ (v ++ s₁))) ++ sq)
         ≡ (pq ++ (b ++ p₁)) ++ (v ++ (s₁ ++ sq))}
     {e₃ : (pq ++ p₁) ++ (v ++ (s₁ ++ (b ++ sq)))
         ≡ pq ++ (((p₁ ++ (v ++ s₁)) ++ b) ++ sq)}
     {e₄ : pq ++ (((p₁ ++ (u ++ s₁)) ++ b) ++ sq)
         ≡ (pq ++ p₁) ++ (u ++ (s₁ ++ (b ++ sq)))}
   → pad (pq ++ (b ++ p₁)) (s₁ ++ sq) G
       ∘ castW e₁
       ∘ pad pq sq (⟦ cross (p₁ ++ (u ++ s₁)) b ⟧ᵇˢ)
     ≈Term castW e₂
       ∘ pad pq sq (⟦ cross (p₁ ++ (v ++ s₁)) b ⟧ᵇˢ)
       ∘ castW e₃
       ∘ pad (pq ++ p₁) (s₁ ++ (b ++ sq)) G
       ∘ castW e₄
  slide-clean-a pq sq b p₁ s₁ {u} {v} G {e₁} {e₂} {e₃} {e₄} = begin
   padIn ∘ (castW e₁ ∘ Cab)
     ≈⟨ conj-cancel e₁ Cab (conj-fromSandwich (padBoxSlid pq sq b p₁ s₁ G (sym e₂) e₁)) ⟩
   castW (sym (sym e₂)) ∘ (Gλ ∘ Cab)
     ≈⟨ castW-irr _ e₂ ⟩∘⟨ ⟺ (slide-pad-a pq sq b hₐ) ⟩
   castW e₂ ∘ (Cab' ∘ Gρ)
     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ padBoxIn pq sq b p₁ s₁ G e₃ e₄ ⟩
   castW e₂ ∘ (Cab' ∘ (castW e₃ ∘ padSlid ∘ castW e₄)) ∎
   where
     hₐ      = pad p₁ s₁ G
     Cab     = pad pq sq (⟦ cross (p₁ ++ (u ++ s₁)) b ⟧ᵇˢ)
     Cab'    = pad pq sq (⟦ cross (p₁ ++ (v ++ s₁)) b ⟧ᵇˢ)
     padIn   = pad (pq ++ (b ++ p₁)) (s₁ ++ sq) G
     padSlid = pad (pq ++ p₁) (s₁ ++ (b ++ sq)) G
     Gρ      = pad pq sq (rpad b hₐ)
     Gλ      = pad pq sq (liftW b hₐ)

  ------------------------------------------------------------------------
  -- The decision module.  Parameters mirror the front-end's `Decide`: a
  -- decidable equality on the underlying generator triples and
  -- a rank tiebreak for ambiguous (mutually-fitting, scalar-like) pairs.
  ------------------------------------------------------------------------
  module Decideσ ⦃ _ : DecEq GenM ⦄ (rank : GenM → ℕ) where

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

    instance
      DecEq-GenS : DecEq SCmp.Gen
      DecEq-GenS ._≟_ (a , b , box f) (a' , b' , box g) = case (a , b , f) ≟ (a' , b' , g) of λ where
        (yes refl) → yes refl
        (no ¬p)    → no λ e → ¬p (just-injective (cong boxPay e))
      DecEq-GenS ._≟_ (_ , _ , box _)     (_ , _ , cross _ _) = no λ e → true≢false (cong tagS e)
      DecEq-GenS ._≟_ (_ , _ , cross _ _) (_ , _ , box _)     = no λ e → true≢false (sym (cong tagS e))
      DecEq-GenS ._≟_ (_ , _ , cross a b) (_ , _ , cross c d) = case a ≟ c of λ where
        (no ¬p)    → no λ e → ¬p (cong proj₁ (just-injective (cong crossPay e)))
        (yes refl) → case b ≟ d of λ where
          (yes refl) → yes refl
          (no ¬q)    → no λ e → ¬q (cong proj₂ (just-injective (cong crossPay e)))

    -- RANK: crosses sort below all boxes among ambiguous pairs; the
    -- caller's relative order on boxes is preserved.
    rankS : ∀ {a b} → MorS a b → ℕ
    rankS (box {a} {b} f) = suc (rank (a , b , f))
    rankS (cross _ _)     = zero

    ------------------------------------------------------------------------
    -- The one-step oracle: σσ-CANCEL first, then naturality slides, then
    -- disjoint interchange, emitting `PrimSigma` steps.  The generic traversal
    -- `stepWith`, the fuel loop `normFuelWith` and the closure `_⤳D_` come from
    -- `SortD.Steps PrimSigma`; `depthD` and `interchangeGo` from `SortD`.
    ------------------------------------------------------------------------

    private
      -- `++`-assoc rebracketings for the slides' index gaps, shared by the
      -- slide constructors' `replD` RHS and their `prim-sound` clauses.
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

      -- The σ engine's PRIMITIVE STEP family: σσ-cancellation, the two
      -- naturality slides (as `replD` replacements at the discovered offsets),
      -- and the shared disjoint interchange embedded via `swap-step`.  Every
      -- recogniser `meq` is kept ABSTRACT (so no per-fire UIP rewrite runs on
      -- the firing path); the reconciliation lands in
      -- `prim-sound`.  `{u}`/`{v}` on the slides are inferred from the box `f`.
      data PrimSigma : ∀ {n k} → Diag n k → Diag n k → Set where
        σσ-step : ∀ {k} (px sx a b : List X)
                  (rest' : Diag (px ++ ((a ++ b) ++ sx)) k)
                  (meq : px ++ ((b ++ a) ++ sx) ≡ px ++ ((b ++ a) ++ sx))
                → PrimSigma
                    (px ▸ sx ∷ cross a b
                       ⟨ substDiag (sym meq) (px ▸ sx ∷ cross b a ⟨ rest' ⟩) ⟩)
                    rest'
        slideB-step : ∀ {k} (px sx a p₁ s₁ : List X) {u v} (f : Mor u v)
                      (rest' : Diag ((px ++ p₁) ++ (v ++ (s₁ ++ (a ++ sx)))) k)
                      (meq : px ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sx)
                           ≡ (px ++ p₁) ++ (u ++ (s₁ ++ (a ++ sx))))
                    → PrimSigma
                        (px ▸ sx ∷ cross a (p₁ ++ (u ++ s₁))
                           ⟨ substDiag (sym meq)
                               ((px ++ p₁) ▸ (s₁ ++ (a ++ sx)) ∷ box f ⟨ rest' ⟩) ⟩)
                        (replD (px ++ (a ++ p₁)) (s₁ ++ sx) px sx
                               (box f) (cross a (p₁ ++ (v ++ s₁))) rest'
                               (eq₁ px p₁ v s₁ a sx) (eq₃ px a p₁ v s₁ sx)
                               (sym (eq₃ px a p₁ u s₁ sx)))
        slideA-step : ∀ {k} (px sx b p₁ s₁ : List X) {u v} (f : Mor u v)
                      (rest' : Diag ((px ++ (b ++ p₁)) ++ (v ++ (s₁ ++ sx))) k)
                      (meq : px ++ ((b ++ (p₁ ++ (u ++ s₁))) ++ sx)
                           ≡ (px ++ (b ++ p₁)) ++ (u ++ (s₁ ++ sx)))
                    → PrimSigma
                        (px ▸ sx ∷ cross (p₁ ++ (u ++ s₁)) b
                           ⟨ substDiag (sym meq)
                               ((px ++ (b ++ p₁)) ▸ (s₁ ++ sx) ∷ box f ⟨ rest' ⟩) ⟩)
                        (replD (px ++ p₁) (s₁ ++ (b ++ sx)) px sx
                               (box f) (cross (p₁ ++ (v ++ s₁)) b) rest'
                               (sym (eq₃ px b p₁ v s₁ sx)) (sym (eq₁ px p₁ v s₁ b sx))
                               (eq₁ px p₁ u s₁ b sx))
        swap-step : ∀ {n k} {d d' : Diag n k} → PrimSwap d d' → PrimSigma d d'

      open Steps PrimSigma

      -- soundness of each primitive step.  σσ: the abstract-`meq` bridge is
      -- `substDiag-irr` (`substDiag refl` reduces), then
      -- `assoc ○ elimʳ (pad-σσ …)`.  Slides: `replD-sound` at the KEY
      -- `slide-clean`/`slide-clean-a` (which carry the meq/domeq reconciliation).
      prim-sound : ∀ {n k} {d d' : Diag n k} → PrimSigma d d' → ⟦ d ⟧ ≈Term ⟦ d' ⟧
      prim-sound (σσ-step px sx a b rest' meq) =
        (substDiag-irr (sym meq) refl (px ▸ sx ∷ cross b a ⟨ rest' ⟩) ⟩∘⟨refl)
          ○ (assoc ○ elimʳ (pad-σσ px sx a b))
      prim-sound (slideB-step px sx a p₁ s₁ f _ _) =
        replD-sound
          (slide-clean px sx a p₁ s₁ (⟦ box f ⟧ᵇˢ))
      prim-sound (slideA-step px sx b p₁ s₁ f _ _) =
        replD-sound
          (slide-clean-a px sx b p₁ s₁ (⟦ box f ⟧ᵇˢ))
      prim-sound (swap-step p) = prim-swap-sound p

      -- the σσ recogniser at the generalized inner index: fires exactly
      -- when the head layer is `cross a b` at (px,sx) and the next layer
      -- is `cross b a` at the SAME (px,sx).
      goσ : ∀ {ax bx k} (px sx : List X) (fx : MorS ax bx)
            {m : List X} (rest : Diag m k) (meq : px ++ (bx ++ sx) ≡ m)
          → Maybe (Σ[ d' ∈ Diag (px ++ (ax ++ sx)) k ]
                    PrimSigma (px ▸ sx ∷ fx ⟨ substDiag (sym meq) rest ⟩) d')
      goσ px sx (box f)     rest meq = nothing
      goσ px sx (cross a b) ([]_ m) meq = nothing
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ py sy (box f) rest') meq = nothing
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq
        with px ≟ py | sx ≟ sy | c ≟ b | d ≟ a
      ... | yes refl | yes refl | yes refl | yes refl =
              just (rest' , σσ-step px sx a b rest' meq)
      ... | _ | _ | _ | _ = nothing

      -- the b-IMAGE slide recogniser: head `cross a b` at (px,sx), second
      -- layer a box exhibited inside the crossing's b-image block
      -- (py = px ++ p₁ with b = p₁ ++ (u ++ s₁) and sy = s₁ ++ (a ++ sx)).
      -- On a hit the box slides BEFORE the crossing, to its pre-cross
      -- offset px ++ (a ++ p₁); the crossing's b-block updates u ↦ v.
      goSlideB : ∀ {ax bx k} (px sx : List X) (fx : MorS ax bx)
                 {m : List X} (rest : Diag m k) (meq : px ++ (bx ++ sx) ≡ m)
               → Maybe (Σ[ d' ∈ Diag (px ++ (ax ++ sx)) k ]
                         PrimSigma (px ▸ sx ∷ fx ⟨ substDiag (sym meq) rest ⟩) d')
      goSlideB px sx (box f)     rest meq = nothing
      goSlideB px sx (cross a b) ([]_ m) meq = nothing
      goSlideB px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq = nothing
      goSlideB px sx (cross a b) (_▸_∷_⟨_⟩ {u} {v} py sy (box f) rest') meq
        with ListExt.stripPrefix _≟_ px py
      ... | nothing = nothing
      ... | just (p₁ , refl) with ListExt.stripPrefix _≟_ p₁ b
      ...   | nothing = nothing
      ...   | just (r₁ , refl) with ListExt.stripPrefix _≟_ u r₁
      ...     | nothing = nothing
      ...     | just (s₁ , refl) with sy ≟ (s₁ ++ (a ++ sx))
      ...       | no _ = nothing
      ...       | yes refl = just (_ , slideB-step px sx a p₁ s₁ f rest' meq)

      -- the a-IMAGE slide recogniser: head `cross a b` at (px,sx), second
      -- layer a box exhibited inside the crossing's a-image block
      -- (py = px ++ (b ++ p₁) with a = p₁ ++ (u ++ s₁) and sy = s₁ ++ sx).
      -- On a hit the box slides BEFORE the crossing, to its pre-cross
      -- offset px ++ p₁; the crossing's a-block updates u ↦ v.
      goSlideA : ∀ {ax bx k} (px sx : List X) (fx : MorS ax bx)
                 {m : List X} (rest : Diag m k) (meq : px ++ (bx ++ sx) ≡ m)
               → Maybe (Σ[ d' ∈ Diag (px ++ (ax ++ sx)) k ]
                         PrimSigma (px ▸ sx ∷ fx ⟨ substDiag (sym meq) rest ⟩) d')
      goSlideA px sx (box f)     rest meq = nothing
      goSlideA px sx (cross a b) ([]_ m) meq = nothing
      goSlideA px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq = nothing
      goSlideA px sx (cross a b) (_▸_∷_⟨_⟩ {u} {v} py sy (box f) rest') meq
        with ListExt.stripPrefix _≟_ px py
      ... | nothing = nothing
      ... | just (r₀ , refl) with ListExt.stripPrefix _≟_ b r₀
      ...   | nothing = nothing
      ...   | just (p₁ , refl) with ListExt.stripPrefix _≟_ p₁ a
      ...     | nothing = nothing
      ...     | just (r₂ , refl) with ListExt.stripPrefix _≟_ u r₂
      ...       | nothing = nothing
      ...       | just (s₁ , refl) with sy ≟ (s₁ ++ sx)
      ...         | no _ = nothing
      ...         | yes refl = just (_ , slideA-step px sx b p₁ s₁ f rest' meq)

      -- the combined per-position oracle: σσ-cancel first, then the two
      -- naturality slides (b-image, then a-image), then disjoint interchange
      -- (the generic `interchangeGo` at the σ-rank, its `PrimSwap` step
      -- embedded into `PrimSigma` via `swap-step`).
      go : ∀ {ax bx k} (px sx : List X) (fx : MorS ax bx)
           {m : List X} (rest : Diag m k) (meq : px ++ (bx ++ sx) ≡ m)
         → Maybe (Σ[ d' ∈ Diag (px ++ (ax ++ sx)) k ]
                   PrimSigma (px ▸ sx ∷ fx ⟨ substDiag (sym meq) rest ⟩) d')
      go px sx fx rest meq =
        goσ      px sx fx rest meq <∣>
        goSlideB px sx fx rest meq <∣>
        goSlideA px sx fx rest meq <∣>
        (case interchangeGo rankS px sx fx rest meq of λ where
           nothing         → nothing
           (just (d' , p)) → just (d' , swap-step p))

      -- one cancel-or-swap at the FIRST applicable position (the generic loop
      -- from SortD.Steps at the σ oracle).
      stepσ? : ∀ {n m} (d : Diag n m) → Maybe (Σ[ d' ∈ Diag n m ] (d ⤳D d'))
      stepσ? = stepWith go

    normσ : ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (⟦ d ⟧ ≈Term ⟦ d' ⟧)
    normσ = normSound prim-sound stepσ? (λ k → suc (k * k * k +ℕ k * k +ℕ k))

    ------------------------------------------------------------------------
    -- The decision entry: the shared `DecideCore` assembly at `normσ`
    -- (reflect → normσ → ≟Diag → chain the soundness witnesses).
    ------------------------------------------------------------------------
    private module DC = DecideCore ES
    open DC.Decide normσ public using () renaming (decideW to decideσ?)

    open import Data.Maybe.Ext public using (IsJust)
