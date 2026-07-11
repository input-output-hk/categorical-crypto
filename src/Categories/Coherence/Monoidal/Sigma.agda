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

open import Categories.Category
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal
open import Categories.FreeStrictMonoidal
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

  -- `v≤v` is a non-`instance` constructor in `Categories.FreeMonoidal` (a
  -- global `v≤v` instance would clash with the APROP cone's own local
  -- `Symm ≤ v` instances).  This engine only ever works at the `Symm`
  -- variant, so it supplies the `Symm ≤ Symm` witness for the free `σ`
  -- locally and privately (kept out of importers that thread it as a param).
  private instance Symm≤Symm : Symm ≤ Symm
                   Symm≤Symm = v≤v

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

  -- Normalize / compare stack
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

  ------------------------------------------------------------------------
  -- The strict engine relation R_σ (block-level, un-padded) and its ONE-TIME
  -- embed-soundness (reusing the surviving σσ-block / slide-core kernel).
  ------------------------------------------------------------------------
  open FreeStrictMonoidalHelper MorS
    using ( padʷ; castʷᵈ; module Theory
          ; ∘ʷ-castʷ-l; ∘ʷ-castʷᵈ-l′; castʷ-castʷᵈ; castʷ-symʳ; castʷᵈ-irr )

  data R_σ : ∀ {n m} → WTerm n m → WTerm n m → Set where
    σσ     : ∀ (a b : List X) → R_σ (boxʷ (cross b a) ∘ʷ boxʷ (cross a b)) idʷ
    slideB : ∀ (a : List X) {b b' : List X} (h : WTerm b b')
           → R_σ (boxʷ (cross a b') ∘ʷ (idʷ {n = a} ⊗ʷ h))
                 ((h ⊗ʷ idʷ {n = a}) ∘ʷ boxʷ (cross a b))
    -- derivable from `slideB` + `σσ` (insert σσ, slide, cancel); kept as an
    -- axiom for the direct one-instance proof.
    slideA : ∀ (b : List X) {a a' : List X} (g : WTerm a a')
           → R_σ (boxʷ (cross a' b) ∘ʷ (g ⊗ʷ idʷ {n = b}))
                 ((idʷ {n = b} ⊗ʷ g) ∘ʷ boxʷ (cross a b))

  -- embed-soundness: `σσ` is `σσ-block`; the slides are `slide-core`/`slide-core-a`
  -- with `embed (idʷ a ⊗ʷ h) ≈ liftW a (embed h)` (via `liftW-merge`) and
  -- `embed (h ⊗ʷ idʷ a) ≡ rpad a (embed h)` (definitional).
  R_σ-sound : ∀ {n m} {f g : WTerm n m} → R_σ f g → embed f ≈Term embed g
  R_σ-sound (σσ a b)     = σσ-block a b
  R_σ-sound (slideB a h) = (refl⟩∘⟨ ⟺ (liftW-merge a (embed h))) ○ slide-core a (embed h)
  R_σ-sound (slideA b g) = slide-core-a b (embed g) ○ (liftW-merge b (embed g) ⟩∘⟨refl)

  ------------------------------------------------------------------------
  -- The strict slide KEYs consumed by `replD-soundˢ`.  In `Theory R_σ`'s
  -- `_≈ʷ_`: the axiom-derived slide (`pad-∘ˢ`/`pad-respˢ`/`axiom`), re-cleaned
  -- into clean strict `padʷ`s by the two padded-box regroupings `pad-absorbLˢ`
  -- (prefix) / `pad-absorbRˢ` (suffix) from `FreeStrictMonoidal`, with the four
  -- `++`-assoc casts reconciled to `replD`'s offsets by Hedberg irrelevance.
  ------------------------------------------------------------------------
  private module T = Theory R_σ
  open T
  private module Rˢ = Category.HomReasoning T.StrictR
  open Rˢ using () renaming (begin_ to beginˢ_; _∎ to _∎ˢ)
  open Rˢ using () renaming (step-≈-⟩ to libˢ-≈; step-≈-⟨ to libˢ-≈˘)
  infixr 2 stepˢ-≈ stepˢ-≈˘
  stepˢ-≈  = libˢ-≈
  stepˢ-≈˘ = libˢ-≈˘
  syntax stepˢ-≈  f gh fg = f ≈ˢ⟨ fg ⟩ gh
  syntax stepˢ-≈˘ f gh gf = f ≈ˢ⟨ gf ⟨ gh

  ------------------------------------------------------------------------
  -- Shared re-cleaning assembly: the `pad-∘ˢ`/`pad-respˢ`/`pad-absorb*ˢ`
  -- calc chain is identical for both slide KEYs (it never inspects the
  -- `cross`); only the three padded-box regroupings (`absorbR`/`raw`/
  -- `absorbL`) differ.  Abstracting over those endpoints factors the chain.
  ------------------------------------------------------------------------
  private
    slide-assembleˢ :
      ∀ {cun cum cvn cvm pin pim psn psm : List X}
        {padIn : WTerm pin pim} {Cu : WTerm cun cum} {Cv : WTerm cvn cvm}
        {Gα : WTerm cun cvn} {Gβ : WTerm cum cvm} {padSlid : WTerm psn psm}
        (meq : cum ≡ pin) (E₂ : cvm ≡ pim) (E₃ : psm ≡ cvn) (E₄ : cun ≡ psn)
      → castʷ E₂ Gβ ≈ʷ castʷᵈ (sym meq) padIn
      → Cv ∘ʷ Gα ≈ʷ Gβ ∘ʷ Cu
      → Gα ≈ʷ castʷ E₃ (castʷᵈ (sym E₄) padSlid)
      → padIn ∘ʷ castʷ meq Cu
        ≈ʷ castʷ E₂ (Cv ∘ʷ castʷ E₃ (castʷᵈ (sym E₄) padSlid))
    slide-assembleˢ {padIn = padIn} {Cu} {Cv} {Gα} {Gβ} {padSlid}
                    meq E₂ E₃ E₄ absorbR raw absorbL = beginˢ
      padIn ∘ʷ castʷ meq Cu
        ≈ˢ⟨ ≡→≈ʷ (sym (∘ʷ-castʷᵈ-l′ meq padIn Cu)) ⟩
      castʷᵈ (sym meq) padIn ∘ʷ Cu
        ≈ˢ⟨ T.∘-resp-≈ (symʷ absorbR) reflʷ ⟩
      castʷ E₂ Gβ ∘ʷ Cu
        ≈ˢ⟨ ≡→≈ʷ (∘ʷ-castʷ-l E₂ Gβ Cu) ⟩
      castʷ E₂ (Gβ ∘ʷ Cu)
        ≈ˢ⟨ castʷ-resp E₂ (symʷ raw) ⟩
      castʷ E₂ (Cv ∘ʷ Gα)
        ≈ˢ⟨ castʷ-resp E₂ (T.∘-resp-≈ reflʷ absorbL) ⟩
      castʷ E₂ (Cv ∘ʷ castʷ E₃ (castʷᵈ (sym E₄) padSlid)) ∎ˢ

  slide-cleanˢ :
    ∀ (px sx a p₁ s₁ : List X) {u v} (G : WTerm u v)
      {meq : px ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sx) ≡ (px ++ p₁) ++ (u ++ (s₁ ++ (a ++ sx)))}
      {E₂ : px ++ (((p₁ ++ (v ++ s₁)) ++ a) ++ sx) ≡ (px ++ p₁) ++ (v ++ (s₁ ++ (a ++ sx)))}
      {E₃ : (px ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sx)) ≡ px ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sx)}
      {E₄ : px ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sx) ≡ (px ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sx))}
    → padʷ (px ++ p₁) (s₁ ++ (a ++ sx)) G
        ∘ʷ castʷ meq (padʷ px sx (boxʷ (cross a (p₁ ++ (u ++ s₁)))))
      ≈ʷ castʷ E₂ (padʷ px sx (boxʷ (cross a (p₁ ++ (v ++ s₁))))
           ∘ʷ castʷ E₃ (castʷᵈ (sym E₄) (padʷ (px ++ (a ++ p₁)) (s₁ ++ sx) G)))
  slide-cleanˢ px sx a p₁ s₁ {u} {v} G {meq} {E₂} {E₃} {E₄} =
    slide-assembleˢ meq E₂ E₃ E₄ absorbR raw absorbL
    where
      Cu = padʷ px sx (boxʷ (cross a (p₁ ++ (u ++ s₁))))
      Cv = padʷ px sx (boxʷ (cross a (p₁ ++ (v ++ s₁))))
      padIn = padʷ (px ++ p₁) (s₁ ++ (a ++ sx)) G
      padSlid = padʷ (px ++ (a ++ p₁)) (s₁ ++ sx) G
      Gα = padʷ px sx (idʷ {n = a} ⊗ʷ padʷ p₁ s₁ G)
      Gβ = padʷ px sx (padʷ p₁ s₁ G ⊗ʷ idʷ {n = a})
      raw : Cv ∘ʷ Gα ≈ʷ Gβ ∘ʷ Cu
      raw = transʷ (symʷ (pad-∘ˢ px sx (boxʷ (cross a (p₁ ++ (v ++ s₁)))) (idʷ {n = a} ⊗ʷ padʷ p₁ s₁ G)))
              (transʷ (pad-respˢ px sx (axiom (slideB a (padʷ p₁ s₁ G))))
                (pad-∘ˢ px sx (padʷ p₁ s₁ G ⊗ʷ idʷ {n = a}) (boxʷ (cross a (p₁ ++ (u ++ s₁))))))
      absorbL : Gα ≈ʷ castʷ E₃ (castʷᵈ (sym E₄) padSlid)
      absorbL = transʷ (pad-absorbLˢ px sx a p₁ s₁ G (sym E₄) E₃)
                       (≡→≈ʷ (sym (castʷ-castʷᵈ (sym E₄) E₃ padSlid)))
      absorbR : castʷ E₂ Gβ ≈ʷ castʷᵈ (sym meq) padIn
      absorbR = transʷ (castʷ-resp E₂ (pad-absorbRˢ px sx a p₁ s₁ G (sym meq) (sym E₂)))
                  (transʷ (≡→≈ʷ (castʷ-castʷᵈ (sym meq) E₂ (castʷ (sym E₂) padIn)))
                    (castʷᵈ-resp (sym meq) (≡→≈ʷ (castʷ-symʳ E₂ padIn))))

  slide-cleanˢ-a :
    ∀ (px sx b p₁ s₁ : List X) {u v} (G : WTerm u v)
      {meq : px ++ ((b ++ (p₁ ++ (u ++ s₁))) ++ sx) ≡ (px ++ (b ++ p₁)) ++ (u ++ (s₁ ++ sx))}
      {E₂ : px ++ ((b ++ (p₁ ++ (v ++ s₁))) ++ sx) ≡ (px ++ (b ++ p₁)) ++ (v ++ (s₁ ++ sx))}
      {E₃ : (px ++ p₁) ++ (v ++ (s₁ ++ (b ++ sx))) ≡ px ++ (((p₁ ++ (v ++ s₁)) ++ b) ++ sx)}
      {E₄ : px ++ (((p₁ ++ (u ++ s₁)) ++ b) ++ sx) ≡ (px ++ p₁) ++ (u ++ (s₁ ++ (b ++ sx)))}
    → padʷ (px ++ (b ++ p₁)) (s₁ ++ sx) G
        ∘ʷ castʷ meq (padʷ px sx (boxʷ (cross (p₁ ++ (u ++ s₁)) b)))
      ≈ʷ castʷ E₂ (padʷ px sx (boxʷ (cross (p₁ ++ (v ++ s₁)) b))
           ∘ʷ castʷ E₃ (castʷᵈ (sym E₄) (padʷ (px ++ p₁) (s₁ ++ (b ++ sx)) G)))
  slide-cleanˢ-a px sx b p₁ s₁ {u} {v} G {meq} {E₂} {E₃} {E₄} =
    slide-assembleˢ meq E₂ E₃ E₄ absorbR raw absorbL
    where
      Cu = padʷ px sx (boxʷ (cross (p₁ ++ (u ++ s₁)) b))
      Cv = padʷ px sx (boxʷ (cross (p₁ ++ (v ++ s₁)) b))
      padIn = padʷ (px ++ (b ++ p₁)) (s₁ ++ sx) G
      padSlid = padʷ (px ++ p₁) (s₁ ++ (b ++ sx)) G
      Gα = padʷ px sx (padʷ p₁ s₁ G ⊗ʷ idʷ {n = b})
      Gβ = padʷ px sx (idʷ {n = b} ⊗ʷ padʷ p₁ s₁ G)
      raw : Cv ∘ʷ Gα ≈ʷ Gβ ∘ʷ Cu
      raw = transʷ (symʷ (pad-∘ˢ px sx (boxʷ (cross (p₁ ++ (v ++ s₁)) b)) (padʷ p₁ s₁ G ⊗ʷ idʷ {n = b})))
              (transʷ (pad-respˢ px sx (axiom (slideA b (padʷ p₁ s₁ G))))
                (pad-∘ˢ px sx (idʷ {n = b} ⊗ʷ padʷ p₁ s₁ G) (boxʷ (cross (p₁ ++ (u ++ s₁)) b))))
      absorbL : Gα ≈ʷ castʷ E₃ (castʷᵈ (sym E₄) padSlid)
      absorbL = transʷ (pad-absorbRˢ px sx b p₁ s₁ G (sym E₄) E₃)
                       (≡→≈ʷ (sym (castʷ-castʷᵈ (sym E₄) E₃ padSlid)))
      absorbR : castʷ E₂ Gβ ≈ʷ castʷᵈ (sym meq) padIn
      absorbR = transʷ (castʷ-resp E₂ (pad-absorbLˢ px sx b p₁ s₁ G (sym meq) (sym E₂)))
                  (transʷ (≡→≈ʷ (castʷ-castʷᵈ (sym meq) E₂ (castʷ (sym E₂) padIn)))
                    (castʷᵈ-resp (sym meq) (≡→≈ʷ (castʷ-symʳ E₂ padIn))))


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

      -- STRICT soundness of each primitive step, in `Theory R_σ`'s `_≈ʷ_` on the
      -- cast-free `⟦_⟧ˢ`.  σσ: the endo-`meq` collapses propositionally
      -- (`⟦substDiag⟧ˢ` + `castʷᵈ-irr` at `refl`), then `pad-∘ˢ`/`pad-respˢ (axiom
      -- (σσ …))`/`pad-idˢ` + `idʳ`.  Slides: `replD-soundˢ` at the strict KEY
      -- `slide-cleanˢ`/`slide-cleanˢ-a`.  `swap-step`: the `R`-generic
      -- `prim-swap-soundˢ`.
      prim-soundˢ : ∀ {n k} {d d' : Diag n k} → PrimSigma d d' → ⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ
      prim-soundˢ (σσ-step px sx a b rest' meq) = beginˢ
        ⟦ px ▸ sx ∷ cross a b ⟨ substDiag (sym meq) SL ⟩ ⟧ˢ
          ≈ˢ⟨ T.∘-resp-≈ (transʷ (≡→≈ʷ (⟦substDiag⟧ˢ (sym meq) SL))
                            (≡→≈ʷ (castʷᵈ-irr (sym meq) refl ⟦ SL ⟧ˢ))) reflʷ ⟩
        (⟦ rest' ⟧ˢ ∘ʷ padʷ px sx (boxʷ (cross b a))) ∘ʷ padʷ px sx (boxʷ (cross a b))
          ≈ˢ⟨ T.assoc ⟩
        ⟦ rest' ⟧ˢ ∘ʷ (padʷ px sx (boxʷ (cross b a)) ∘ʷ padʷ px sx (boxʷ (cross a b)))
          ≈ˢ⟨ T.∘-resp-≈ reflʷ (symʷ (pad-∘ˢ px sx (boxʷ (cross b a)) (boxʷ (cross a b)))) ⟩
        ⟦ rest' ⟧ˢ ∘ʷ padʷ px sx (boxʷ (cross b a) ∘ʷ boxʷ (cross a b))
          ≈ˢ⟨ T.∘-resp-≈ reflʷ (pad-respˢ px sx (axiom (σσ a b))) ⟩
        ⟦ rest' ⟧ˢ ∘ʷ padʷ px sx idʷ
          ≈ˢ⟨ T.∘-resp-≈ reflʷ (pad-idˢ px sx) ⟩
        ⟦ rest' ⟧ˢ ∘ʷ idʷ
          ≈ˢ⟨ T.idʳ ⟩
        ⟦ rest' ⟧ˢ ∎ˢ
        where SL = px ▸ sx ∷ cross b a ⟨ rest' ⟩
      prim-soundˢ (slideB-step px sx a p₁ s₁ {u} {v} f _ meq) =
        replD-soundˢ R_σ (slide-cleanˢ px sx a p₁ s₁ (boxʷ (box f))
          {meq} {eq₁ px p₁ v s₁ a sx} {eq₃ px a p₁ v s₁ sx} {sym (eq₃ px a p₁ u s₁ sx)})
      prim-soundˢ (slideA-step px sx b p₁ s₁ {u} {v} f _ meq) =
        replD-soundˢ R_σ (slide-cleanˢ-a px sx b p₁ s₁ (boxʷ (box f))
          {meq} {sym (eq₃ px b p₁ v s₁ sx)} {sym (eq₁ px p₁ v s₁ b sx)} {eq₁ px p₁ u s₁ b sx})
      prim-soundˢ (swap-step p) = prim-swap-soundˢ R_σ p

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
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq with px ≟ py | sx ≟ sy | c ≟ b | d ≟ a
      ... | yes refl | yes refl | yes refl | yes refl = just (rest' , σσ-step px sx a b rest' meq)
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
      goSlideB px sx (cross a b) (_▸_∷_⟨_⟩ {u} {v} py sy (box f) rest') meq =
        case ListExt.stripPrefix _≟_ px py of λ where
          nothing → nothing
          (just (p₁ , refl)) → case ListExt.stripPrefix _≟_ p₁ b of λ where
            nothing → nothing
            (just (r₁ , refl)) → case ListExt.stripPrefix _≟_ u r₁ of λ where
              nothing → nothing
              (just (s₁ , refl)) → case sy ≟ (s₁ ++ (a ++ sx)) of λ where
                (no _)     → nothing
                (yes refl) → just (_ , slideB-step px sx a p₁ s₁ f rest' meq)

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
      goSlideA px sx (cross a b) (_▸_∷_⟨_⟩ {u} {v} py sy (box f) rest') meq =
        case ListExt.stripPrefix _≟_ px py of λ where
          nothing → nothing
          (just (r₀ , refl)) → case ListExt.stripPrefix _≟_ b r₀ of λ where
            nothing → nothing
            (just (p₁ , refl)) → case ListExt.stripPrefix _≟_ p₁ a of λ where
              nothing → nothing
              (just (r₂ , refl)) → case ListExt.stripPrefix _≟_ u r₂ of λ where
                nothing → nothing
                (just (s₁ , refl)) → case sy ≟ (s₁ ++ sx) of λ where
                  (no _)     → nothing
                  (yes refl) → just (_ , slideA-step px sx b p₁ s₁ f rest' meq)

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

    normσ : ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ)
    normσ = normSoundˢ R_σ prim-soundˢ stepσ? (λ k → suc (k * k * k +ℕ k * k +ℕ k))

    ------------------------------------------------------------------------
    -- The decision entry: the shared STRICT `DecideCore` assembly at `normσ`
    -- (reflect → normσ → ≟Diag → chain the `⟦_⟧ˢ`-level witnesses through
    -- `embed-resp-≈ R_σ R_σ-sound` once).
    ------------------------------------------------------------------------
    private module DC = DecideCore ES
    open DC.Decide R_σ R_σ-sound normσ public using () renaming (decideW to decideσ?)

    open import Data.Maybe.Ext public using (IsJust)
