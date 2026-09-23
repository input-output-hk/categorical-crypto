{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.Diagram where

--------------------------------------------------------------------------------
-- Normal form for free monoidal-category diagrams with morphism generators
--------------------------------------------------------------------------------
--
-- The wire-level signature and the diagram type `Diag` together with
-- its interpretation `⟦_⟧ˢ` into the free strict monoidal category
-- over flat "n-wire" objects.
--
-- The box-free wire coherence (`castW`/`assocW`/`liftW-merge`/…)
-- lives in `WireCoherence`; `⟦_⟧ˢ` and its builder soundness
-- `DiagSoundˢ` land in the free strict monoidal category.
--
-- The native syntactic step relation `_⤳D_` (`DClosure`) is the rewrite closure
-- of an engine-supplied primitive-step family; a normalizer emits its witnesses
-- and the semantics enters only through the strict `⤳D-soundˢ`.

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)
open import Data.List.Properties
import Data.List.Properties.Ext as ListExt

open import Categories.Category
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR
open import Categories.Coherence.Monoidal.WireCoherence
open import Categories.FreeMonoidal
open import Categories.FreeStrictMonoidal

--------------------------------------------------------------------------------
-- WireSig: the wire-level signature
--------------------------------------------------------------------------------

module WireSig {X : Set} (Mor : List X → List X → Set) where

  open FreeMonoidalHelper Mon X using (ObjTerm)
  open FreeMonoidalHelper Mon X public using (wires)

  data mor : ObjTerm → ObjTerm → Set where
    box : ∀ {a b} → Mor a b → mor (wires a) (wires b)

--------------------------------------------------------------------------------
-- The engine over a wire-level generator family `Mor`.
--------------------------------------------------------------------------------
module DiagramI {X : Set} (Mor : List X → List X → Set) where

  open WireSig {X} Mor public
  open FreeMonoidalHelper.Mor Mon X mor

  module ≈R = Category.HomReasoning FreeMonoidal; open ≈R

  --------------------------------------------------------------------------------
  -- Diagrams: a list of layers.  Each layer is a box `f : Mor a b` placed
  -- at offset `pre`, with `suf` idle wires after it. Consing a layer in front
  -- turns a diagram of input width `pre ++ (b ++ suf)` into one of input width
  -- `pre ++ (a ++ suf)`, leaving the output index untouched.
  --------------------------------------------------------------------------------
  infixr 5 _▸_∷_⟨_⟩
  data Diag : List X → List X → Set where
    []_     : (n : List X) → Diag n n
    _▸_∷_⟨_⟩ : ∀ {a b m} (pre : List X) (suf : List X) (f : Mor a b)
             → Diag (pre ++ (b ++ suf)) m → Diag (pre ++ (a ++ suf)) m

  open WireCoh X mor public

  substDiag : ∀ {m n k : List X} → m ≡ n → Diag m k → Diag n k
  substDiag refl d = d

  substDiagᵒ : ∀ {n k k' : List X} → k ≡ k' → Diag n k → Diag n k'
  substDiagᵒ refl d = d

  --------------------------------------------------------------------------------
  -- The diagram semantics `⟦_⟧ˢ : Diag n m → WTerm n m`, into the free strict
  -- monoidal category over the wire generators `Mor`.
  --------------------------------------------------------------------------------
  open FreeStrictMonoidalHelper Mor

  -- the solver carries no engine axioms of its own, so it runs the strict
  -- theory at the empty engine relation.
  R⊥ : ∀ {n m} → WTerm n m → WTerm n m → Set
  R⊥ _ _ = ⊥

  ⟦_⟧ˢ : ∀ {n m} (d : Diag n m) → WTerm n m
  ⟦ []_ n ⟧ˢ              = idʷ
  ⟦ pre ▸ suf ∷ f ⟨ d ⟩ ⟧ˢ = ⟦ d ⟧ˢ ∘ʷ padʷ pre suf (boxʷ f)

  ⟦substDiag⟧ˢ : ∀ {m n k : List X} (e : m ≡ n) (d : Diag m k)
    → ⟦ substDiag e d ⟧ˢ ≡ castʷᵈ e ⟦ d ⟧ˢ
  ⟦substDiag⟧ˢ refl d = refl

  ⟦substDiagᵒ⟧ˢ : ∀ {n k k' : List X} (e : k ≡ k') (d : Diag n k)
    → ⟦ substDiagᵒ e d ⟧ˢ ≡ castʷ e ⟦ d ⟧ˢ
  ⟦substDiagᵒ⟧ˢ refl d = refl

  --------------------------------------------------------------------------------
  -- The native syntactic step relation `_⤳D_`.
  --------------------------------------------------------------------------------
  module DClosure (Prim : ∀ {n k} → Diag n k → Diag n k → Set) where

    infix 4 _⤳D_
    data _⤳D_ : ∀ {n k} → Diag n k → Diag n k → Set where
      prim   : ∀ {n k} {d d' : Diag n k} → Prim d d' → d ⤳D d'
      reflᴰ  : ∀ {n k} {d : Diag n k} → d ⤳D d
      transᴰ : ∀ {n k} {d d' d'' : Diag n k} → d ⤳D d' → d' ⤳D d'' → d ⤳D d''
      consᴰ  : ∀ {a b k} {pre suf : List X} {f : Mor a b}
               {rest rest' : Diag (pre ++ (b ++ suf)) k}
             → rest ⤳D rest'
             → (pre ▸ suf ∷ f ⟨ rest ⟩) ⤳D (pre ▸ suf ∷ f ⟨ rest' ⟩)

    -- The strict discharge: induction on `⟦_⟧ˢ` in `_≈ʷ_` (the `consᴰ` case is
    -- `∘ʷ`-congruence on the shared pad).  This is what the retargeted
    -- `normSoundˢ` emits; `DecideCore` transports it to `_≈Term_`.
    open Theory R⊥

    ⤳D-soundˢ : (∀ {n k} {d d' : Diag n k} → Prim d d' → ⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ)
              → ∀ {n k} {d d' : Diag n k} → d ⤳D d' → ⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ
    ⤳D-soundˢ ps (prim p)     = ps p
    ⤳D-soundˢ ps reflᴰ        = reflʷ
    ⤳D-soundˢ ps (transᴰ p q) = transʷ (⤳D-soundˢ ps p) (⤳D-soundˢ ps q)
    ⤳D-soundˢ ps (consᴰ p)    = ∘-resp-≈ (⤳D-soundˢ ps p) reflʷ

  --------------------------------------------------------------------------------
  -- `Diag` combinators
  --------------------------------------------------------------------------------

  infixr 9 _∘ᵈ_
  _∘ᵈ_ : ∀ {n m k} → Diag n m → Diag m k → Diag n k
  ([]_ _)               ∘ᵈ d₂ = d₂
  (pre ▸ suf ∷ f ⟨ d ⟩) ∘ᵈ d₂ = pre ▸ suf ∷ f ⟨ d ∘ᵈ d₂ ⟩

  shiftL : ∀ {n m} (lt : List X) → Diag n m → Diag (lt ++ n) (lt ++ m)
  shiftL lt ([]_ n) = []_ (lt ++ n)
  shiftL lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    substDiag (++-assoc lt pre (a ++ suf))
      ((lt ++ pre) ▸ suf ∷ f ⟨ substDiag (sym (++-assoc lt pre (b ++ suf))) (shiftL lt d) ⟩)

  shiftR : ∀ {n m} (rt : List X) → Diag n m → Diag (n ++ rt) (m ++ rt)
  shiftR rt ([]_ n) = []_ (n ++ rt)
  shiftR rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
    substDiag (sym (ListExt.++-assoc-mid pre a suf rt))
      (pre ▸ (suf ++ rt) ∷ f ⟨ substDiag (ListExt.++-assoc-mid pre b suf rt) (shiftR rt d) ⟩)

  infixr 10 _⊗ᵈ_
  _⊗ᵈ_ : ∀ {nl ml nr mr} → Diag nl ml → Diag nr mr → Diag (nl ++ nr) (ml ++ mr)
  _⊗ᵈ_ {nl} {ml} {nr} {mr} dl dr = shiftR nr dl ∘ᵈ shiftL ml dr

  boxLayer : ∀ {a b} → Mor a b → Diag (a ++ []) (b ++ [])
  boxLayer {a} {b} g = [] ▸ [] ∷ g ⟨ []_ (b ++ []) ⟩

  boxD : ∀ {a b} → Mor a b → Diag a b
  boxD {a} {b} g = substDiag (++-identityʳ a) (substDiagᵒ (++-identityʳ b) (boxLayer g))

  --------------------------------------------------------------------------------
  -- Soundness of the pure builders on the cast-free strict semantics `⟦_⟧ˢ`.
  --------------------------------------------------------------------------------
  module DiagSoundˢ ⦃ _ : DecEq X ⦄ where
    open Theory R⊥
    private module Rˢ = Category.HomReasoning StrictR
    open Rˢ using () renaming (begin_ to beginˢ_; _∎ to _∎ˢ)
    open Rˢ using () renaming (step-≈-⟩ to libˢ-≈; step-≈-⟨ to libˢ-≈˘)
    infixr 2 stepˢ-≈ stepˢ-≈˘
    stepˢ-≈  = libˢ-≈
    stepˢ-≈˘ = libˢ-≈˘
    syntax stepˢ-≈  f gh fg = f ≈ˢ⟨ fg ⟩ gh
    syntax stepˢ-≈˘ f gh gf = f ≈ˢ⟨ gf ⟨ gh

    ∘ᵈ-soundˢ : ∀ {n m k} (d₁ : Diag n m) (d₂ : Diag m k) → ⟦ d₁ ∘ᵈ d₂ ⟧ˢ ≈ʷ ⟦ d₂ ⟧ˢ ∘ʷ ⟦ d₁ ⟧ˢ
    ∘ᵈ-soundˢ ([]_ _)              d₂ = symʷ idʳ
    ∘ᵈ-soundˢ (pre ▸ suf ∷ f ⟨ d ⟩) d₂ = transʷ (∘-resp-≈ (∘ᵈ-soundˢ d d₂) reflʷ) assoc

    shiftL-soundˢ : ∀ {n m} (lt : List X) (d : Diag n m) → ⟦ shiftL lt d ⟧ˢ ≈ʷ idʷ ⊗ʷ ⟦ d ⟧ˢ
    shiftL-soundˢ lt ([]_ _) = symʷ id⊗id
    shiftL-soundˢ lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = beginˢ
      ⟦ substDiag E1 LAYER ⟧ˢ
        ≈ˢ⟨ ≡→≈ʷ (⟦substDiag⟧ˢ E1 LAYER) ⟩
      castʷᵈ E1 (⟦ substDiag E2 (shiftL lt d) ⟧ˢ ∘ʷ PL)
        ≈ˢ⟨ castʷᵈ-resp E1 (∘-resp-≈ leftEq (pad-nest lt pre suf g)) ⟩
      castʷᵈ E1 (castʷᵈ E2 (Id ⊗ʷ D) ∘ʷ castʷᵈ (sym E1) (castʷ E2 (Id ⊗ʷ PP)))
        ≈ˢ⟨ ≡→≈ʷ (∘ʷ-cast-cancelˡ E1 E2 (Id ⊗ʷ D) (Id ⊗ʷ PP)) ⟩
      (Id ⊗ʷ D) ∘ʷ (Id ⊗ʷ PP)
        ≈ˢ⟨ split₂ʳ ⟨
      idʷ ⊗ʷ (D ∘ʷ PP) ∎ˢ
      where
        g  = boxʷ f
        E1 = ++-assoc lt pre (a ++ suf)
        E2 = sym (++-assoc lt pre (b ++ suf))
        Id = idʷ
        D  = ⟦ d ⟧ˢ
        PP = padʷ pre suf g
        PL = padʷ (lt ++ pre) suf g
        LAYER = (lt ++ pre) ▸ suf ∷ f ⟨ substDiag E2 (shiftL lt d) ⟩
        leftEq : ⟦ substDiag E2 (shiftL lt d) ⟧ˢ ≈ʷ castʷᵈ E2 (Id ⊗ʷ D)
        leftEq = transʷ (≡→≈ʷ (⟦substDiag⟧ˢ E2 (shiftL lt d)))
                        (castʷᵈ-resp E2 (shiftL-soundˢ lt d))

    shiftR-soundˢ : ∀ {n m} (rt : List X) (d : Diag n m) → ⟦ shiftR rt d ⟧ˢ ≈ʷ ⟦ d ⟧ˢ ⊗ʷ idʷ
    shiftR-soundˢ rt ([]_ _) = symʷ id⊗id
    shiftR-soundˢ rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = beginˢ
      ⟦ substDiag (sym E1) LAYER ⟧ˢ
        ≈ˢ⟨ ≡→≈ʷ (⟦substDiag⟧ˢ (sym E1) LAYER) ⟩
      castʷᵈ (sym E1) (⟦ substDiag E2 (shiftR rt d) ⟧ˢ ∘ʷ padʷ pre (suf ++ rt) g)
        ≈ˢ⟨ castʷᵈ-resp (sym E1) (∘-resp-≈ leftEq (pad-nestR pre suf rt g E1 E2)) ⟩
      castʷᵈ (sym E1) (castʷᵈ E2 A ∘ʷ castʷᵈ E1 (castʷ E2 B))
        ≈ˢ⟨ ≡→≈ʷ (∘ʷ-cast-cancelʳ E1 E2 A B) ⟩
      A ∘ʷ B
        ≈ˢ⟨ split₁ʳ ⟨
      (D ∘ʷ PP) ⊗ʷ idʷ ∎ˢ
      where
        g  = boxʷ f
        E1 = ListExt.++-assoc-mid pre a suf rt
        E2 = ListExt.++-assoc-mid pre b suf rt
        D  = ⟦ d ⟧ˢ
        PP = padʷ pre suf g
        A  = D ⊗ʷ idʷ
        B  = PP ⊗ʷ idʷ
        LAYER = pre ▸ (suf ++ rt) ∷ f ⟨ substDiag E2 (shiftR rt d) ⟩
        leftEq : ⟦ substDiag E2 (shiftR rt d) ⟧ˢ ≈ʷ castʷᵈ E2 A
        leftEq = transʷ (≡→≈ʷ (⟦substDiag⟧ˢ E2 (shiftR rt d)))
                        (castʷᵈ-resp E2 (shiftR-soundˢ rt d))

    ⊗ᵈ-soundˢ : ∀ {nl ml nr mr} (dl : Diag nl ml) (dr : Diag nr mr)
              → ⟦ dl ⊗ᵈ dr ⟧ˢ ≈ʷ ⟦ dl ⟧ˢ ⊗ʷ ⟦ dr ⟧ˢ
    ⊗ᵈ-soundˢ {nl} {ml} {nr} {mr} dl dr =
      transʷ (∘ᵈ-soundˢ (shiftR nr dl) (shiftL ml dr))
        (transʷ (∘-resp-≈ (shiftL-soundˢ ml dr) (shiftR-soundˢ nr dl))
          (symʷ serialize₂₁))

    boxSoundˢ : ∀ {a b} (g : Mor a b) → ⟦ boxD g ⟧ˢ ≈ʷ boxʷ g
    boxSoundˢ {a} {b} g = beginˢ
      ⟦ boxD g ⟧ˢ
        ≈ˢ⟨ ≡→≈ʷ (⟦substDiag⟧ˢ (++-identityʳ a) (substDiagᵒ (++-identityʳ b) (boxLayer g))) ⟩
      castʷᵈ (++-identityʳ a) ⟦ substDiagᵒ (++-identityʳ b) (boxLayer g) ⟧ˢ
        ≈ˢ⟨ castʷᵈ-resp (++-identityʳ a) (≡→≈ʷ (⟦substDiagᵒ⟧ˢ (++-identityʳ b) (boxLayer g))) ⟩
      castʷᵈ (++-identityʳ a) (castʷ (++-identityʳ b) ⟦ boxLayer g ⟧ˢ)
        ≈ˢ⟨ castʷᵈ-resp (++-identityʳ a)
             (castʷ-resp (++-identityʳ b) (transʷ idˡ (unitˡ (boxʷ g ⊗ʷ idʷ)))) ⟩
      castʷᵈ (++-identityʳ a) (castʷ (++-identityʳ b) (boxʷ g ⊗ʷ idʷ))
        ≈ˢ⟨ unitʳ (boxʷ g) ⟩
      boxʷ g ∎ˢ
