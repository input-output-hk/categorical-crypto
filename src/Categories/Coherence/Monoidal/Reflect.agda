{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A reflection  HomTerm → Diag  with soundness, for the free
-- monoidal-diagram normal form of `Categories.Coherence.Monoidal.Diagram`.
--
-- We work in the layered-composite wire fragment (M1): morphisms whose
-- source and target are already `wires`-shaped flat objects, built from
--   id, _∘_, var (box _), _⊗₁_,
-- captured by the inductive `WTerm n m` with embedding
-- `embed : WTerm n m → HomTerm (wires n) (wires m)`.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Reflect where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties using (++-assoc; ++-identityʳ)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal
open import Categories.FreeStrictMonoidal
open import Categories.Coherence.Monoidal.Compare
open import Categories.Coherence.Monoidal.Normalize

module ReflectI {v : Variant} {X : Set} (E : WireEngine v) ⦃ _ : DecEq X ⦄ where

  open WireEngine E
  open DiagramI E
  open FreeMonoidalHelper v X using (ObjTerm; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor v X mor
  open ≈R

  open MonR Monoidal-FreeMonoidal using (_⟩⊗⟨_)

  --------------------------------------------------------------------------------
  -- M1 fragment: the wire-typed strict terms.
  --------------------------------------------------------------------------------
  -- `WTerm`/`boxʷ`/`idʷ`/`_∘ʷ_`/`_⊗ʷ_` are the free strict monoidal category on
  -- the wire generators `Mor`.
  open FreeStrictMonoidalHelper Mor public using (WTerm; boxʷ; idʷ; _∘ʷ_; _⊗ʷ_)

  embed : ∀ {n m} → WTerm n m → HomTerm (wires n) (wires m)
  embed (boxʷ g)  = ⟦ g ⟧ᵇ
  embed idʷ       = id
  embed (g ∘ʷ f)  = embed g ∘ embed f
  embed (_⊗ʷ_ {nl} {ml} s t) = merge ml ∘ (embed s ⊗₁ embed t) ∘ split nl

  --------------------------------------------------------------------------------
  -- Reflection of the wire fragment into Diag (M1).
  --
  --   id     →  empty diagram
  --   g ∘ f  →  reflect f ∘ᵈ reflect g
  --   box g  →  single-box layer
  --------------------------------------------------------------------------------

  reflect : ∀ {n m} → WTerm n m → Diag n m
  reflect idʷ      = []_ _
  reflect (g ∘ʷ f) = reflect f ∘ᵈ reflect g
  reflect (boxʷ g) = boxD g
  reflect (s ⊗ʷ t) = reflect s ⊗ᵈ reflect t

  --------------------------------------------------------------------------------
  -- Extra structure for the strict layer: the `embed`/cast interaction and the
  -- ONE-TIME functor
  -- soundness `embed-resp-≈` (where the merge/split content is paid, once per
  -- `_≈ʷ_` axiom).
  --------------------------------------------------------------------------------
  open MR FreeMonoidal
  open WireCohDec
  open MonR Monoidal-FreeMonoidal using (_⟩⊗⟨refl; refl⟩⊗⟨_; split₁ˡ)
  open FreeStrictMonoidalHelper Mor public using (castʷ)
  open FreeStrictMonoidalHelper Mor
    using (castʷᵈ; padʷ; module Theory)

  -- `embed` intertwines the strict term transports with the wire cast `castW`
  -- (refl-matched).  Public so `Frontend/Core`'s `reflectF`/`cast-half` reuse
  -- them (through its `open ReflectI E`) instead of a private duplicate.
  embed-castʷ : ∀ {n m m'} (e : m ≡ m') (t : WTerm n m)
              → embed (castʷ e t) ≈Term castW e ∘ embed t
  embed-castʷ refl t = ⟺ idˡ

  embed-castʷᵈ : ∀ {n n' m} (e : n ≡ n') (t : WTerm n m)
               → embed (castʷᵈ e t) ≈Term embed t ∘ castW (sym e)
  embed-castʷᵈ refl t = ⟺ idʳ

  --------------------------------------------------------------------------------
  -- The STRICT reflection soundness `⟦ reflect t ⟧ˢ ≈ʷ t` (any engine relation
  -- `R`), via the CAST-FREE `DiagSoundˢ` builders.  The decision core consumes
  -- this, applying `embed-resp-≈` once.
  --------------------------------------------------------------------------------
  module _ (R : ∀ {n m} → WTerm n m → WTerm n m → Set) where
    open Theory R
    open DiagSoundˢ R

    reflect-soundˢ : ∀ {n m} (t : WTerm n m) → ⟦ reflect t ⟧ˢ ≈ʷ t
    reflect-soundˢ idʷ      = reflʷ
    reflect-soundˢ (g ∘ʷ f) =
      transʷ (∘ᵈ-soundˢ (reflect f) (reflect g)) (∘-resp-≈ (reflect-soundˢ g) (reflect-soundˢ f))
    reflect-soundˢ (boxʷ g) = boxSoundˢ g
    reflect-soundˢ (s ⊗ʷ t) =
      transʷ (⊗ᵈ-soundˢ (reflect s) (reflect t)) (⊗-resp-≈ʷ (reflect-soundˢ s) (reflect-soundˢ t))

  --------------------------------------------------------------------------------
  -- `embed-resp-≈`: the free-strict-monoidal functor soundness.  Given the
  -- engine's own soundness `R-sound`, `embed` sends `_≈ʷ_` to `_≈Term_`.  Every
  -- merge/split fact is paid HERE, once per axiom: `inter` = bifunctoriality
  -- collapse, `id⊗id` = `merge∘split`, `unitˡ` = λ-coherence, `unitʳ` =
  -- `merge-ρ`/`split-ρ`, `⊗-assoc` = `merge-assoc`/`split-assoc` glued by
  -- `α-conj`.  Downstream soundness is then a corollary (`embed-resp-≈` of a
  -- strict `DiagSoundˢ` lemma).
  --------------------------------------------------------------------------------
  module _ (R : ∀ {n m} → WTerm n m → WTerm n m → Set)
           (R-sound : ∀ {n m} {f g : WTerm n m} → R f g → embed f ≈Term embed g) where
    open Theory R

    embed-resp-≈ : ∀ {n m} {f g : WTerm n m} → f ≈ʷ g → embed f ≈Term embed g
    embed-resp-≈ idˡ            = idˡ
    embed-resp-≈ idʳ            = idʳ
    embed-resp-≈ assoc          = assoc
    embed-resp-≈ (∘-resp-≈ p q) = embed-resp-≈ p ⟩∘⟨ embed-resp-≈ q
    embed-resp-≈ reflʷ          = ≈-Term-refl
    embed-resp-≈ (symʷ p)       = ⟺ (embed-resp-≈ p)
    embed-resp-≈ (transʷ p q)   = embed-resp-≈ p ○ embed-resp-≈ q
    embed-resp-≈ (⊗-resp-≈ʷ p q) =
      refl⟩∘⟨ ((embed-resp-≈ p ⟩⊗⟨ embed-resp-≈ q) ⟩∘⟨refl)
    embed-resp-≈ (axiom r)      = R-sound r
    -- id⊗id : the flat merge/split of identities collapses.
    embed-resp-≈ id⊗id =
      (refl⟩∘⟨ ((id⊗id≈id ⟩∘⟨refl) ○ idˡ)) ○ merge∘split _
    -- unitˡ : merge [] = λ⇒, split [] = λ⇐; λ-naturality + cancellation.
    embed-resp-≈ (unitˡ f) = pullˡ λ⇒∘id⊗f≈f∘λ⇒ ○ cancelʳ λ⇒∘λ⇐≈id
    -- inter : the bifunctoriality collapse (mirror of `DiagSound.⊗ᵈ-sound`).
    embed-resp-≈ (inter {ml = ml} {nr = nr} {g = g} {f = f} {g' = g'} {f' = f'}) = ⟺ (begin
      (merge _ ∘ (embed g ⊗₁ embed g') ∘ split ml)
        ∘ (merge ml ∘ (embed f ⊗₁ embed f') ∘ split _)
        ≈⟨ center (cancelʳ (split∘merge ml)) ⟩
      merge _ ∘ ((embed g ⊗₁ embed g') ∘ ((embed f ⊗₁ embed f') ∘ split _))
        ≈⟨ refl⟩∘⟨ pullˡ (⟺ ⊗-∘-dist) ⟩
      merge _ ∘ ((embed g ∘ embed f) ⊗₁ (embed g' ∘ embed f')) ∘ split _ ∎)
    -- unitʳ : merge/split right-unitor coherence (mirror of `boxSound`).
    embed-resp-≈ (unitʳ {n} {m} f) = begin
      embed (castʷᵈ eN (castʷ eM (f ⊗ʷ idʷ {n = []})))
        ≈⟨ embed-castʷᵈ eN (castʷ eM (f ⊗ʷ idʷ {n = []})) ⟩
      embed (castʷ eM (f ⊗ʷ idʷ {n = []})) ∘ castW (sym eN)
        ≈⟨ embed-castʷ eM (f ⊗ʷ idʷ {n = []}) ⟩∘⟨refl ⟩
      (castW eM ∘ (merge m ∘ (embed f ⊗₁ id) ∘ split n)) ∘ castW (sym eN)
        ≈⟨ (⟺ assoc) ⟩∘⟨refl ⟩
      ((castW eM ∘ merge m) ∘ ((embed f ⊗₁ id) ∘ split n)) ∘ castW (sym eN)
        ≈⟨ assoc ⟩
      (castW eM ∘ merge m) ∘ (((embed f ⊗₁ id) ∘ split n) ∘ castW (sym eN))
        ≈⟨ merge-ρ m ⟩∘⟨ assoc ⟩
      ρ⇒ ∘ ((embed f ⊗₁ id) ∘ (split n ∘ castW (sym eN)))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ split-ρ n) ⟩
      ρ⇒ ∘ ((embed f ⊗₁ id) ∘ ρ⇐)
        ≈⟨ pullˡ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩
      (embed f ∘ ρ⇒) ∘ ρ⇐
        ≈⟨ cancelʳ ρ⇒∘ρ⇐≈id ⟩
      embed f ∎
      where eN = ++-identityʳ n ; eM = ++-identityʳ m
    -- ⊗-assoc : the merge/split monoidal-coherence.  The codomain half is
    -- `merge-assoc`, the domain half `split-assoc`; they sandwich the box block
    -- `((F ⊗₁ G) ⊗₁ H)` between `α⇒`/`α⇐`, collapsed by `α-conj`.  `Hmove`
    -- shifts `H` from the split side onto the box block; `midCollapse` reglues
    -- the inner `(g ⊗ h)` merge/split.
    embed-resp-≈ (⊗-assoc {n₁} {m₁} {n₂} {m₂} {n₃} {m₃} f g h) = begin
      embed (castʷᵈ eN (castʷ eM ((f ⊗ʷ g) ⊗ʷ h)))
        ≈⟨ embed-castʷᵈ eN (castʷ eM ((f ⊗ʷ g) ⊗ʷ h)) ⟩
      embed (castʷ eM ((f ⊗ʷ g) ⊗ʷ h)) ∘ castW (sym eN)
        ≈⟨ embed-castʷ eM ((f ⊗ʷ g) ⊗ʷ h) ⟩∘⟨refl ⟩
      (castW eM ∘ (merge (m₁ ++ m₂) ∘ ((INL ⊗₁ H) ∘ split (n₁ ++ n₂)))) ∘ castW (sym eN)
        ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (inl-exp ⟩∘⟨refl))) ⟩∘⟨refl ⟩
      (castW eM ∘ (merge (m₁ ++ m₂) ∘
        (((merge m₁ ⊗₁ id) ∘ (((F ⊗₁ G) ⊗₁ id) ∘ (split n₁ ⊗₁ H))) ∘ split (n₁ ++ n₂)))) ∘ castW (sym eN)
        ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ ((refl⟩∘⟨ Hmove) ⟩∘⟨refl))) ⟩∘⟨refl ⟩
      (castW eM ∘ (merge (m₁ ++ m₂) ∘
        (((merge m₁ ⊗₁ id) ∘ (((F ⊗₁ G) ⊗₁ H) ∘ (split n₁ ⊗₁ id))) ∘ split (n₁ ++ n₂)))) ∘ castW (sym eN)
        ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ assoc)) ⟩∘⟨refl ⟩
      (castW eM ∘ (merge (m₁ ++ m₂) ∘
        ((merge m₁ ⊗₁ id) ∘ ((((F ⊗₁ G) ⊗₁ H) ∘ (split n₁ ⊗₁ id)) ∘ split (n₁ ++ n₂))))) ∘ castW (sym eN)
        ≈⟨ (refl⟩∘⟨ (⟺ assoc)) ⟩∘⟨refl ⟩
      (castW eM ∘ ((merge (m₁ ++ m₂) ∘ (merge m₁ ⊗₁ id)) ∘
        ((((F ⊗₁ G) ⊗₁ H) ∘ (split n₁ ⊗₁ id)) ∘ split (n₁ ++ n₂)))) ∘ castW (sym eN)
        ≈⟨ (⟺ assoc) ⟩∘⟨refl ⟩
      ((castW eM ∘ (merge (m₁ ++ m₂) ∘ (merge m₁ ⊗₁ id))) ∘
        ((((F ⊗₁ G) ⊗₁ H) ∘ (split n₁ ⊗₁ id)) ∘ split (n₁ ++ n₂))) ∘ castW (sym eN)
        ≈⟨ assoc ⟩
      (castW eM ∘ (merge (m₁ ++ m₂) ∘ (merge m₁ ⊗₁ id))) ∘
        (((((F ⊗₁ G) ⊗₁ H) ∘ (split n₁ ⊗₁ id)) ∘ split (n₁ ++ n₂)) ∘ castW (sym eN))
        ≈⟨ cod ⟩∘⟨ (assoc ○ assoc ○ (refl⟩∘⟨ ⟺ assoc)) ⟩
      (merge m₁ ∘ ((id ⊗₁ merge m₂) ∘ α⇒)) ∘
        (((F ⊗₁ G) ⊗₁ H) ∘ (((split n₁ ⊗₁ id) ∘ split (n₁ ++ n₂)) ∘ castW (sym eN)))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ dom) ⟩
      (merge m₁ ∘ ((id ⊗₁ merge m₂) ∘ α⇒)) ∘
        (((F ⊗₁ G) ⊗₁ H) ∘ (α⇐ ∘ ((id ⊗₁ split n₂) ∘ split n₁)))
        ≈⟨ assoc ○ (refl⟩∘⟨ assoc)
             ○ (refl⟩∘⟨ (refl⟩∘⟨ ((refl⟩∘⟨ ⟺ assoc) ○ ⟺ assoc))) ⟩
      merge m₁ ∘ ((id ⊗₁ merge m₂) ∘
        ((α⇒ ∘ (((F ⊗₁ G) ⊗₁ H) ∘ α⇐)) ∘ ((id ⊗₁ split n₂) ∘ split n₁)))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (α-conj F G H ⟩∘⟨refl)) ⟩
      merge m₁ ∘ ((id ⊗₁ merge m₂) ∘
        ((F ⊗₁ (G ⊗₁ H)) ∘ ((id ⊗₁ split n₂) ∘ split n₁)))
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ ⟺ assoc) ○ ⟺ assoc ○ (midCollapse ⟩∘⟨refl)) ⟩
      merge m₁ ∘ ((F ⊗₁ (merge m₂ ∘ (G ⊗₁ H) ∘ split n₂)) ∘ split n₁) ∎
      where
        eM = ++-assoc m₁ m₂ m₃ ; eN = ++-assoc n₁ n₂ n₃
        F = embed f ; G = embed g ; H = embed h
        INL = embed (f ⊗ʷ g)
        -- expand the inner box tower's tensor with `H` (bifunctoriality).
        inl-exp : INL ⊗₁ H ≈Term (merge m₁ ⊗₁ id) ∘ (((F ⊗₁ G) ⊗₁ id) ∘ (split n₁ ⊗₁ H))
        inl-exp = split₁ˡ ○ (refl⟩∘⟨ split₁ˡ)
        -- move `H` from the split side onto the box block.
        Hmove : ((F ⊗₁ G) ⊗₁ id) ∘ (split n₁ ⊗₁ H) ≈Term ((F ⊗₁ G) ⊗₁ H) ∘ (split n₁ ⊗₁ id)
        Hmove = (⟺ ⊗-∘-dist) ○ (refl⟩⊗⟨ (idˡ ○ ⟺ idʳ)) ○ ⊗-∘-dist
        -- codomain half (merge-assoc) and domain half (split-assoc).
        cod : castW eM ∘ (merge (m₁ ++ m₂) ∘ (merge m₁ ⊗₁ id))
            ≈Term merge m₁ ∘ ((id ⊗₁ merge m₂) ∘ α⇒)
        cod = ⟺ (merge-assoc m₁ m₂ m₃)
        dom : ((split n₁ ⊗₁ id) ∘ split (n₁ ++ n₂)) ∘ castW (sym eN)
            ≈Term α⇐ ∘ ((id ⊗₁ split n₂) ∘ split n₁)
        dom = ⟺ (split-assoc n₁ n₂ n₃)
        -- reglue the inner `(g ⊗ h)` merge/split.
        midCollapse : (id ⊗₁ merge m₂) ∘ ((F ⊗₁ (G ⊗₁ H)) ∘ (id ⊗₁ split n₂))
                    ≈Term F ⊗₁ (merge m₂ ∘ (G ⊗₁ H) ∘ split n₂)
        midCollapse = begin
          (id ⊗₁ merge m₂) ∘ ((F ⊗₁ (G ⊗₁ H)) ∘ (id ⊗₁ split n₂))
            ≈⟨ pullˡ (⟺ ⊗-∘-dist) ⟩
          ((id ∘ F) ⊗₁ (merge m₂ ∘ (G ⊗₁ H))) ∘ (id ⊗₁ split n₂)
            ≈⟨ (idˡ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
          (F ⊗₁ (merge m₂ ∘ (G ⊗₁ H))) ∘ (id ⊗₁ split n₂)
            ≈⟨ ⟺ ⊗-∘-dist ⟩
          (F ∘ id) ⊗₁ ((merge m₂ ∘ (G ⊗₁ H)) ∘ split n₂)
            ≈⟨ idʳ ⟩⊗⟨ assoc ⟩
          F ⊗₁ (merge m₂ ∘ (G ⊗₁ H) ∘ split n₂) ∎

--------------------------------------------------------------------------------
-- `DecideCore`: the shared wire-level DECISION ASSEMBLY.
--
-- Both front-ends' `decide?W`/`decideσ?` are byte-identical given a STRICT
-- normalizer `norm : ∀ {n m} (d : Diag n m) → Σ[ d' ] (⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ)`:
-- reflect both sides to `Diag`, normalize each, decide normal-form equality,
-- chain the strict reflect-soundness + normalizer witnesses to `f ≈ʷ g`, and
-- transport to the weak `embed f ≈Term embed g` by ONE `embed-resp-≈`.  `norm`
-- is passed as an ordinary FUNCTION argument so the per-variant oracle
-- (interchange / σσ-cancel / slides) stays in each front-end's scope while the
-- assembly lives here once.
--------------------------------------------------------------------------------
module DecideCore
  {v : Variant} {X : Set} (E : WireEngine v)
  ⦃ _ : DecEq X ⦄
  where

  open WireEngine E
  open DiagramI E
  open FreeMonoidalHelper.Mor v X mor
  open ≈R
  open ReflectI E
  open NormalizeI E
  open SortD
  open MR FreeMonoidal
  open FreeStrictMonoidalHelper Mor using (module Theory)

  module SCmp = CompareI E

  -- the decision core: the caller supplies decidable equality on the
  -- Σ-packaged generators (an instance, used only to build `_≟Diag_`), the
  -- engine relation `R` with its one-time `embed`-soundness `R-sound`, and a
  -- STRICT normalizer emitting `⟦_⟧ˢ`-level witnesses in `Theory R`.  On a hit
  -- the two normal forms are equal (`≈NF⇒≡`), so the strict reflect-soundness +
  -- normalizer witnesses chain to `f ≈ʷ g`, transported to the weak
  -- `embed f ≈Term embed g` by ONE `embed-resp-≈`.
  module Decide
    ⦃ _ : DecEq SCmp.Gen ⦄
    (R : ∀ {n m} → WTerm n m → WTerm n m → Set)
    (R-sound : ∀ {n m} {f g : WTerm n m} → R f g → embed f ≈Term embed g)
    (norm : ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (Theory._≈ʷ_ R ⟦ d ⟧ˢ ⟦ d' ⟧ˢ))
    where

    open SCmp.Decide
    open Theory R

    decideW : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decideW {n} {m} f g with norm (reflect f) | norm (reflect g)
    ... | (df' , sndf) | (dg' , sndg) = case df' ≟Diag dg' of λ where
        (no  _)  → nothing
        (yes eq) → just (embed-resp-≈ R R-sound (chain (≈NF⇒≡ eq)))
      where
        chain : df' ≡ dg' → f ≈ʷ g
        chain refl = transʷ (symʷ (reflect-soundˢ R f))
                       (transʷ sndf (transʷ (symʷ sndg) (reflect-soundˢ R g)))
