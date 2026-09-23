{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A reflection  HomTerm → Diag  with soundness.
--
-- We work in the layered-composite wire fragment: morphisms whose source
-- and target are already `wires`-shaped flat objects, captured by the
-- inductive `WTerm n m` with embedding
-- `embed : WTerm n m → HomTerm (wires n) (wires m)`.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Reflect where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal
open import Categories.FreeStrictMonoidal
open import Categories.Coherence.Monoidal.Compare
open import Categories.Coherence.Monoidal.Normalize

module ReflectI {X : Set} (Mor : List X → List X → Set) ⦃ _ : DecEq X ⦄ where

  open DiagramI Mor
  open FreeMonoidalHelper Mon X using (ObjTerm; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor Mon X mor
  open ≈R

  open MonR Monoidal-FreeMonoidal using (_⟩⊗⟨_)

  -- M1 fragment: the wire-typed strict terms.
  open FreeStrictMonoidalHelper Mor public using (WTerm; boxʷ; idʷ; _∘ʷ_; _⊗ʷ_)

  embed : ∀ {n m} → WTerm n m → HomTerm (wires n) (wires m)
  embed (boxʷ g)  = var (box g)
  embed idʷ       = id
  embed (g ∘ʷ f)  = embed g ∘ embed f
  embed (_⊗ʷ_ {nl} {ml} s t) = merge ml ∘ (embed s ⊗₁ embed t) ∘ split nl

  reflect : ∀ {n m} → WTerm n m → Diag n m
  reflect idʷ      = []_ _
  reflect (g ∘ʷ f) = reflect f ∘ᵈ reflect g
  reflect (boxʷ g) = boxD g
  reflect (s ⊗ʷ t) = reflect s ⊗ᵈ reflect t

  --------------------------------------------------------------------------------
  -- Extra structure for the strict layer: the `embed`/cast interaction and the
  -- functor soundness `embed-resp-≈`.
  --------------------------------------------------------------------------------
  open MR FreeMonoidal
  open WireCohDec
  open MonR Monoidal-FreeMonoidal using (_⟩⊗⟨refl; refl⟩⊗⟨_; split₁ˡ)
  open FreeStrictMonoidalHelper Mor public using (castʷ)
  open FreeStrictMonoidalHelper Mor using (castʷᵈ; padʷ; module Theory)

  -- `embed` intertwines the strict term transports with the wire cast `castW`.
  embed-castʷ : ∀ {n m m'} (e : m ≡ m') (t : WTerm n m) → embed (castʷ e t) ≈Term castW e ∘ embed t
  embed-castʷ refl t = ⟺ idˡ

  embed-castʷᵈ : ∀ {n n' m} (e : n ≡ n') (t : WTerm n m)
               → embed (castʷᵈ e t) ≈Term embed t ∘ castW (sym e)
  embed-castʷᵈ refl t = ⟺ idʳ

  open Theory R⊥
  open DiagSoundˢ

  reflect-soundˢ : ∀ {n m} (t : WTerm n m) → ⟦ reflect t ⟧ˢ ≈ʷ t
  reflect-soundˢ idʷ      = reflʷ
  reflect-soundˢ (g ∘ʷ f) =
    transʷ (∘ᵈ-soundˢ (reflect f) (reflect g)) (∘-resp-≈ (reflect-soundˢ g) (reflect-soundˢ f))
  reflect-soundˢ (boxʷ g) = boxSoundˢ g
  reflect-soundˢ (s ⊗ʷ t) =
    transʷ (⊗ᵈ-soundˢ (reflect s) (reflect t)) (⊗-resp-≈ʷ (reflect-soundˢ s) (reflect-soundˢ t))

  --------------------------------------------------------------------------------
  -- `embed-resp-≈`: the free-strict-monoidal functor soundness — `embed` sends
  -- `_≈ʷ_` to `_≈Term_`.  Every merge/split fact is paid here, once per axiom.
  --------------------------------------------------------------------------------
  embed-resp-≈ : ∀ {n m} {f g : WTerm n m} → f ≈ʷ g → embed f ≈Term embed g
  embed-resp-≈ idˡ            = idˡ
  embed-resp-≈ idʳ            = idʳ
  embed-resp-≈ assoc          = assoc
  embed-resp-≈ (∘-resp-≈ p q) = embed-resp-≈ p ⟩∘⟨ embed-resp-≈ q
  embed-resp-≈ reflʷ          = ≈-Term-refl
  embed-resp-≈ (symʷ p)       = ⟺ (embed-resp-≈ p)
  embed-resp-≈ (transʷ p q)   = embed-resp-≈ p ○ embed-resp-≈ q
  embed-resp-≈ (⊗-resp-≈ʷ p q) = refl⟩∘⟨ ((embed-resp-≈ p ⟩⊗⟨ embed-resp-≈ q) ⟩∘⟨refl)
  embed-resp-≈ (axiom ())
  embed-resp-≈ id⊗id = (refl⟩∘⟨ ((id⊗id≈id ⟩∘⟨refl) ○ idˡ)) ○ merge∘split _
  embed-resp-≈ (unitˡ f) = pullˡ λ⇒∘id⊗f≈f∘λ⇒ ○ cancelʳ λ⇒∘λ⇐≈id
  embed-resp-≈ (inter {ml = ml} {nr = nr} {g = g} {f = f} {g' = g'} {f' = f'}) = ⟺ (begin
    (merge _ ∘ (embed g ⊗₁ embed g') ∘ split ml)
      ∘ (merge ml ∘ (embed f ⊗₁ embed f') ∘ split _)
      ≈⟨ center (cancelʳ (split∘merge ml)) ⟩
    merge _ ∘ ((embed g ⊗₁ embed g') ∘ ((embed f ⊗₁ embed f') ∘ split _))
      ≈⟨ refl⟩∘⟨ pullˡ (⟺ ⊗-∘-dist) ⟩
    merge _ ∘ ((embed g ∘ embed f) ⊗₁ (embed g' ∘ embed f')) ∘ split _ ∎)
  embed-resp-≈ (unitʳ {n} {m} f) = begin
    embed (castʷᵈ eN (castʷ eM (f ⊗ʷ idʷ)))
      ≈⟨ embed-castʷᵈ eN (castʷ eM (f ⊗ʷ idʷ)) ⟩
    embed (castʷ eM (f ⊗ʷ idʷ)) ∘ castW (sym eN)
      ≈⟨ embed-castʷ eM (f ⊗ʷ idʷ) ⟩∘⟨refl ⟩
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
      ≈⟨ ⟺ (merge-assoc m₁ m₂ m₃) ⟩∘⟨ (assoc ○ assoc ○ (refl⟩∘⟨ ⟺ assoc)) ⟩
    (merge m₁ ∘ ((id ⊗₁ merge m₂) ∘ α⇒)) ∘
      (((F ⊗₁ G) ⊗₁ H) ∘ (((split n₁ ⊗₁ id) ∘ split (n₁ ++ n₂)) ∘ castW (sym eN)))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⟺ (split-assoc n₁ n₂ n₃)) ⟩
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
      inl-exp : INL ⊗₁ H ≈Term (merge m₁ ⊗₁ id) ∘ (((F ⊗₁ G) ⊗₁ id) ∘ (split n₁ ⊗₁ H))
      inl-exp = split₁ˡ ○ (refl⟩∘⟨ split₁ˡ)
      Hmove : ((F ⊗₁ G) ⊗₁ id) ∘ (split n₁ ⊗₁ H) ≈Term ((F ⊗₁ G) ⊗₁ H) ∘ (split n₁ ⊗₁ id)
      Hmove = (⟺ ⊗-∘-dist) ○ (refl⟩⊗⟨ (idˡ ○ ⟺ idʳ)) ○ ⊗-∘-dist
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
-- `DecideCore`: the wire-level decision assembly.  Given a normalizer `norm`
-- it reflects both sides to `Diag`, normalizes each, decides normal-form
-- equality and transports a hit to `embed f ≈Term embed g`.
--------------------------------------------------------------------------------
module DecideCore
  {X : Set} (Mor : List X → List X → Set)
  ⦃ _ : DecEq X ⦄
  where

  open DiagramI Mor
  open FreeMonoidalHelper.Mor Mon X mor
  open ≈R
  open ReflectI Mor
  open NormalizeI Mor
  open SortD
  open MR FreeMonoidal
  open FreeStrictMonoidalHelper Mor using (module Theory)

  module SCmp = CompareI Mor

  module Decide
    ⦃ _ : DecEq SCmp.Gen ⦄
    (norm : ∀ {n m} (d : Diag n m)
          → Σ[ d' ∈ Diag n m ] ((Theory._≈ʷ_ R⊥ ⟦ d ⟧ˢ ⟦ d' ⟧ˢ) × NormStatus))
    where

    open SCmp.Decide
    open Theory R⊥

    -- A non-`converged` verdict does not disable the comparison: the
    -- normalization witness is sound wherever the loop stops, so a match
    -- between two cut trajectories is still a real proof.
    decideW : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decideW f g = case norm (reflect f) , norm (reflect g) of λ where
      ((df' , sndf , _) , (dg' , sndg , _)) → case df' ≟Diag dg' of λ where
        (no  _)     → nothing
        (yes refl)  → just (embed-resp-≈
          (transʷ (symʷ (reflect-soundˢ f))
            (transʷ sndf (transʷ (symʷ sndg) (reflect-soundˢ g)))))

    -- Diagnostic: the loop's verdict on one side.  A `nothing` from
    -- `decideW` under a `cycled`/`exhausted` verdict is the normalizer's
    -- non-termination on degenerate signatures, not a genuine
    -- normal-form mismatch (see `Test.Limitations`).
    statusW : ∀ {n m} (f : WTerm n m) → NormStatus
    statusW f = proj₂ (proj₂ (norm (reflect f)))
