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
open import Data.List.Properties

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.Compare
open import Categories.Coherence.Monoidal.Normalize

module ReflectI {v : Variant} {X : Set} (E : WireEngine v) ⦃ _ : DecEq X ⦄ where

  open WireEngine E
  open DiagramI E
  open FreeMonoidalHelper v X using (ObjTerm; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor v X mor
  open ≈R

  open MR FreeMonoidal
  open MonR Monoidal-FreeMonoidal using (_⟩⊗⟨_; serialize₂₁)

  -- Re-exported (`public`) for `Frontend.Core`'s `FBridge`, which only does
  -- `open ReflectI E` and transfers these two to the F-side
  -- (`mergeF-ρ`/`mergeF-assoc`) without separately opening `WireCohDec`.
  open WireCohDec public using (merge-ρ; merge-assoc)
  open WireCohDec        using (castW-irr)

  --------------------------------------------------------------------------------
  -- M1 fragment: the wire-typed terms
  --------------------------------------------------------------------------------
  -- This is the free STRICT monoidal category on the wire generators `Mor`:
  -- objects are `List X`, `⊗` is `++` (strictly associative, strict unit), and
  -- there are no unit/associator coherence morphisms.  It is deliberately NOT
  -- factored through `Categories.FreeStrictMonoidal`: that module's
  -- `Mor.HomTerm` is a NON-strict presentation (it still carries λ/ρ/α/σ
  -- constructors) and rests on postulates (`prefix-remainder`, `⊗-cancelˡ`, …)
  -- with `--safe` disabled, so it neither matches this strict term shape nor
  -- could be imported into this `--safe --without-K` module.  With a single
  -- use site, a shared abstraction is not worth extracting.
  infixr 9 _∘ʷ_
  infixr 10 _⊗ʷ_
  data WTerm : List X → List X → Set where
    boxʷ : ∀ {a b} → Mor a b → WTerm a b
    idʷ  : ∀ {n} → WTerm n n
    _∘ʷ_ : ∀ {n m k} → WTerm m k → WTerm n m → WTerm n k
    _⊗ʷ_ : ∀ {nl ml nr mr} → WTerm nl ml → WTerm nr mr → WTerm (nl ++ nr) (ml ++ mr)

  embed : ∀ {n m} → WTerm n m → HomTerm (wires n) (wires m)
  embed (boxʷ g)  = ⟦ g ⟧ᵇ
  embed idʷ       = id
  embed (g ∘ʷ f)  = embed g ∘ embed f
  embed (_⊗ʷ_ {nl} {ml} s t) = merge ml ∘ (embed s ⊗₁ embed t) ∘ split nl

  -- These are pure `Diag` combinators, so in isolation they could live in
  -- `Diagram`.  They are kept here because they exist only to define `reflect`
  -- and are interleaved with soundness lemmas (`∘ᵈ-sound`, `shiftL-sound`, …)
  -- that rest on the `⦃ DecEq X ⦄`-gated `WireCohDec` layer.  `DiagramI` takes
  -- no `DecEq X` (it re-exports only the DecEq-free `WireCoh`), so relocating
  -- the cluster would either force a `DecEq X` instance onto `DiagramI` and all
  -- its consumers or split the definitions from the proofs that justify them.
  private
    infixr 9 _∘ᵈ_
    _∘ᵈ_ : ∀ {n m k} → Diag n m → Diag m k → Diag n k
    ([]_ _)               ∘ᵈ d₂ = d₂
    (pre ▸ suf ∷ f ⟨ d ⟩) ∘ᵈ d₂ = pre ▸ suf ∷ f ⟨ d ∘ᵈ d₂ ⟩

    open WireCohDec
      using (split-ρ; conj-toSandwich; conj-trans; conj-irr;
             liftW-conj; liftW-fuse; rpad-liftW; rpad-rpad)

    ∘ᵈ-sound : ∀ {n m k} (d₁ : Diag n m) (d₂ : Diag m k) → ⟦ d₁ ∘ᵈ d₂ ⟧ ≈Term ⟦ d₂ ⟧ ∘ ⟦ d₁ ⟧
    ∘ᵈ-sound ([]_ _) d₂ = ⟺ idʳ
    ∘ᵈ-sound (pre ▸ suf ∷ f ⟨ d ⟩) d₂ = (∘ᵈ-sound d d₂ ⟩∘⟨refl) ○ assoc

    -- Prefix-shift: prepend `lt` idle wires to every layer (offset pre ↦ lt++pre).
    -- Definitionally  ⟦ shiftL lt d ⟧  is  liftW lt ⟦ d ⟧  up to the associativity
    -- reindexing absorbed by `substDiag`; the output index is threaded as `lt ++ m`.
    shiftL : ∀ {n m} (lt : List X) → Diag n m → Diag (lt ++ n) (lt ++ m)
    shiftL lt ([]_ n) = []_ (lt ++ n)
    shiftL lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
      substDiag (++-assoc lt pre (a ++ suf))
        ((lt ++ pre) ▸ suf ∷ f ⟨ substDiag (sym (++-assoc lt pre (b ++ suf))) (shiftL lt d) ⟩)

    reassoc++ : ∀ (p a s r : List X) → (p ++ (a ++ s)) ++ r ≡ p ++ (a ++ (s ++ r))
    reassoc++ p a s r = trans (++-assoc p (a ++ s) r) (cong (p ++_) (++-assoc a s r))

    -- Suffix-shift: append `rt` idle wires (suffix suf ↦ suf++rt).
    shiftR : ∀ {n m} (rt : List X) → Diag n m → Diag (n ++ rt) (m ++ rt)
    shiftR rt ([]_ n) = []_ (n ++ rt)
    shiftR rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) =
      substDiag (sym (reassoc++ pre a suf rt))
        (pre ▸ (suf ++ rt) ∷ f ⟨ substDiag (reassoc++ pre b suf rt) (shiftR rt d) ⟩)

    infixr 10 _⊗ᵈ_
    _⊗ᵈ_ : ∀ {nl ml nr mr} → Diag nl ml → Diag nr mr → Diag (nl ++ nr) (ml ++ mr)
    _⊗ᵈ_ {nl} {ml} {nr} {mr} dl dr = shiftR nr dl ∘ᵈ shiftL ml dr

    -- the raw single-box layer; its endpoints carry trailing `++ []`s.
    boxLayer : ∀ {a b} → Mor a b → Diag (a ++ []) (b ++ [])
    boxLayer {a} {b} g = [] ▸ [] ∷ g ⟨ []_ (b ++ []) ⟩

    -- the single-box diagram at CLEAN endpoints: the structural `++-identityʳ`
    -- reindices are absorbed right here, so `reflect` and the soundness
    -- statement see a plain `Diag a b`.
    boxD : ∀ {a b} → Mor a b → Diag a b
    boxD {a} {b} g = substDiag (++-identityʳ a) (substDiagᵒ (++-identityʳ b) (boxLayer g))

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

  private
    --------------------------------------------------------------------------------
    -- Box-leaf soundness (`boxSound`):  ⟦ boxD g ⟧ ≈Term ⟦ g ⟧ᵇ.  The two
    -- `++-identityʳ` transports peel off as `castW`s (`⟦substDiag⟧` /
    -- `⟦substDiagᵒ⟧`); the remainder is `merge-ρ`/`split-ρ` unitor coherence.
    --------------------------------------------------------------------------------

    boxSound : ∀ {a b} (g : Mor a b) → ⟦ boxD g ⟧ ≈Term ⟦ g ⟧ᵇ
    boxSound {a} {b} g = begin
      ⟦ boxD g ⟧
        ≈⟨ ⟦substDiag⟧ (++-identityʳ a) (substDiagᵒ (++-identityʳ b) (boxLayer g)) ⟩
      ⟦ substDiagᵒ (++-identityʳ b) (boxLayer g) ⟧ ∘ castW (sym (++-identityʳ a))
        ≈⟨ ⟦substDiagᵒ⟧ (++-identityʳ b) (boxLayer g) ⟩∘⟨refl ⟩
      (castW (++-identityʳ b) ∘ ⟦ boxLayer g ⟧) ∘ castW (sym (++-identityʳ a))
        ≈⟨ (refl⟩∘⟨ idˡ) ⟩∘⟨refl ⟩
      (castW (++-identityʳ b) ∘ merge b ∘ rest) ∘ castW (sym (++-identityʳ a))
        ≈⟨ (⟺ assoc) ⟩∘⟨refl ⟩
      ((castW (++-identityʳ b) ∘ merge b) ∘ rest) ∘ castW (sym (++-identityʳ a))
        ≈⟨ assoc ⟩
      (castW (++-identityʳ b) ∘ merge b) ∘ (rest ∘ castW (sym (++-identityʳ a)))
        ≈⟨ (merge-ρ b) ⟩∘⟨ assoc ⟩
      ρ⇒ ∘ ((⟦ g ⟧ᵇ ⊗₁ id) ∘ (split a ∘ castW (sym (++-identityʳ a))))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (split-ρ a)) ⟩
      ρ⇒ ∘ ((⟦ g ⟧ᵇ ⊗₁ id) ∘ ρ⇐)
        ≈⟨ pullˡ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩
      (⟦ g ⟧ᵇ ∘ ρ⇒) ∘ ρ⇐
        ≈⟨ cancelʳ ρ⇒∘ρ⇐≈id ⟩
      ⟦ g ⟧ᵇ ∎
      where
        rest : HomTerm (wires (a ++ [])) (wires b ⊗₀ wires [])
        rest = (⟦ g ⟧ᵇ ⊗₁ id) ∘ split a

    --------------------------------------------------------------------------------
    -- Soundness of the offset shifts `shiftL` / `shiftR`.
    --------------------------------------------------------------------------------

    liftW-pad : ∀ {a b} (lt pre suf : List X) (g : HomTerm (wires a) (wires b))
              → liftW lt (pad pre suf g)
                ≈Term (castW (++-assoc lt pre (b ++ suf)) ∘ pad (lt ++ pre) suf g)
                        ∘ castW (sym (++-assoc lt pre (a ++ suf)))
    liftW-pad lt pre suf g = conj-toSandwich (liftW-fuse lt pre (rpad suf g)) ○ ⟺ assoc

    -- The output index is now `lt ++ m` structurally, so the statement is
    -- cast-free; the two `substDiag` wrappers are peeled by `⟦substDiag⟧`.
    shiftL-sound : ∀ {n m} (lt : List X) (d : Diag n m) → ⟦ shiftL lt d ⟧ ≈Term liftW lt ⟦ d ⟧
    shiftL-sound lt ([]_ _) = ⟺ (liftW-id lt)
    shiftL-sound lt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = begin
      ⟦ substDiag E1 LAYER ⟧
        ≈⟨ ⟦substDiag⟧ E1 LAYER ⟩
      (⟦ subst2 ⟧ ∘ pf) ∘ castW (sym E1)
        ≈⟨ (subst2≈ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((liftW lt ⟦ d ⟧ ∘ castW Eb) ∘ pf) ∘ castW (sym E1)
        ≈⟨ (assoc ⟩∘⟨refl) ○ assoc ⟩
      liftW lt ⟦ d ⟧ ∘ ((castW Eb ∘ pf) ∘ castW (sym E1))
        ≈⟨ refl⟩∘⟨ ⟺ (liftW-pad lt pre suf g) ⟩
      liftW lt ⟦ d ⟧ ∘ liftW lt (pad pre suf g)
        ≈⟨ ⟺ (liftW-∘ lt ⟦ d ⟧ (pad pre suf g)) ⟩
      liftW lt (⟦ d ⟧ ∘ pad pre suf g) ∎
      where
        g  = ⟦ f ⟧ᵇ
        Eb = ++-assoc lt pre (b ++ suf)
        E1 = ++-assoc lt pre (a ++ suf)
        E2 = sym Eb
        d' = shiftL lt d
        subst2 = substDiag E2 d'
        pf = pad (lt ++ pre) suf g
        LAYER = (lt ++ pre) ▸ suf ∷ f ⟨ subst2 ⟩
        -- the inner shift folds through its `substDiag` to `liftW lt ⟦d⟧`.
        subst2≈ : ⟦ subst2 ⟧ ≈Term liftW lt ⟦ d ⟧ ∘ castW Eb
        subst2≈ = ⟦substDiag⟧ E2 d' ○ (shiftL-sound lt d ⟩∘⟨ castW-irr (sym E2) Eb)

  --------------------------------------------------------------------------------
  -- The suffix flat-shift `rpad` / `pad` relation and its soundness for `shiftR`.
  --------------------------------------------------------------------------------

  private
    -- rpad / pad relation (suffix analogue of `liftW-pad`): a conjugation chain
    -- over the bi-action laws, all at `R = rpad suf g`.  `rpad-liftW rt pre R`
    -- slides the outer `rpad rt` past the `pad pre suf g = liftW pre R` prefix;
    -- `liftW-conj pre (rpad-rpad suf rt g)` fuses the two suffix pads underneath;
    -- `conj-irr` bridges the composite cast indices to the `reassoc++` forms.
    rpad-pad : ∀ {a b} (pre suf rt : List X) (g : HomTerm (wires a) (wires b))
               → rpad rt (pad pre suf g)
                 ≈Term (castW (sym (reassoc++ pre b suf rt)) ∘ pad pre (suf ++ rt) g)
                         ∘ castW (reassoc++ pre a suf rt)
    rpad-pad pre suf rt g =
      conj-toSandwich
        (conj-irr (conj-trans (rpad-liftW rt pre R) (liftW-conj pre (rpad-rpad suf rt g))))
        ○ ⟺ assoc
      where R = rpad suf g

    shiftR-sound : ∀ {n m} (rt : List X) (d : Diag n m) → ⟦ shiftR rt d ⟧ ≈Term rpad rt ⟦ d ⟧
    shiftR-sound rt ([]_ _) = ⟺ (rpad-id rt)
    shiftR-sound rt (_▸_∷_⟨_⟩ {a} {b} pre suf f d) = begin
      ⟦ substDiag (sym E1) LAYER ⟧
        ≈⟨ ⟦substDiag⟧ (sym E1) LAYER ⟩
      (⟦ subst2 ⟧ ∘ padR) ∘ castW (sym (sym E1))
        ≈⟨ refl⟩∘⟨ castW-irr (sym (sym E1)) E1 ⟩
      (⟦ subst2 ⟧ ∘ padR) ∘ castW E1
        ≈⟨ (subst2≈ ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((rpad rt ⟦ d ⟧ ∘ castW (sym E2)) ∘ padR) ∘ castW E1
        ≈⟨ (assoc ⟩∘⟨refl) ○ assoc ⟩
      rpad rt ⟦ d ⟧ ∘ ((castW (sym E2) ∘ padR) ∘ castW E1)
        ≈⟨ refl⟩∘⟨ ⟺ (rpad-pad pre suf rt g) ⟩
      rpad rt ⟦ d ⟧ ∘ rpad rt (pad pre suf g)
        ≈⟨ ⟺ (rpad-∘ rt ⟦ d ⟧ (pad pre suf g)) ⟩
      rpad rt (⟦ d ⟧ ∘ pad pre suf g) ∎
      where
        g  = ⟦ f ⟧ᵇ
        E1 = reassoc++ pre a suf rt
        E2 = reassoc++ pre b suf rt
        d' = shiftR rt d
        subst2 = substDiag E2 d'
        padR = pad pre (suf ++ rt) g
        LAYER = pre ▸ (suf ++ rt) ∷ f ⟨ subst2 ⟩
        -- the inner shift folds through its `substDiag` to `rpad rt ⟦d⟧`.
        subst2≈ : ⟦ subst2 ⟧ ≈Term rpad rt ⟦ d ⟧ ∘ castW (sym E2)
        subst2≈ = ⟦substDiag⟧ E2 d' ○ (shiftR-sound rt d ⟩∘⟨refl)

    ⊗ᵈ-sound : ∀ {nl ml nr mr} (dl : Diag nl ml) (dr : Diag nr mr)
             → ⟦ dl ⊗ᵈ dr ⟧ ≈Term merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl
    ⊗ᵈ-sound {nl} {ml} {nr} {mr} dl dr = begin
      ⟦ shiftR nr dl ∘ᵈ shiftL ml dr ⟧
        ≈⟨ ∘ᵈ-sound (shiftR nr dl) (shiftL ml dr) ⟩
      ⟦ shiftL ml dr ⟧ ∘ ⟦ shiftR nr dl ⟧
        ≈⟨ shiftL-sound ml dr ⟩∘⟨ shiftR-sound nr dl ⟩
      liftW ml ⟦ dr ⟧ ∘ rpad nr ⟦ dl ⟧
        ≈⟨ liftW-merge ml ⟦ dr ⟧ ⟩∘⟨refl ⟩
      (merge ml ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split ml)
        ∘ (merge ml ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
        ≈⟨ collapse ⟩
      merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl ∎
      where
        -- the central bifunctoriality collapse.
        collapse : (merge ml ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split ml) ∘ (merge ml ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
                   ≈Term merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl
        collapse = begin
          (merge ml ∘ (id ⊗₁ ⟦ dr ⟧) ∘ split ml) ∘ (merge ml ∘ (⟦ dl ⟧ ⊗₁ id) ∘ split nl)
            ≈⟨ center (cancelʳ (split∘merge ml)) ⟩
          merge ml ∘ ((id ⊗₁ ⟦ dr ⟧) ∘ ((⟦ dl ⟧ ⊗₁ id) ∘ split nl))
            ≈⟨ refl⟩∘⟨ pullˡ (⟺ serialize₂₁) ⟩
          merge ml ∘ (⟦ dl ⟧ ⊗₁ ⟦ dr ⟧) ∘ split nl ∎

  --------------------------------------------------------------------------------
  -- THE REFLECTION SOUNDNESS THEOREM.
  --
  --   ⟦ reflect t ⟧  ≈Term  embed t
  --
  -- i.e. the reflected diagram equals the original wire-fragment morphism.
  -- Both endpoints are diagram indices, so the statement is cast-free.
  --------------------------------------------------------------------------------
  reflect-sound : ∀ {n m} (t : WTerm n m) → ⟦ reflect t ⟧ ≈Term embed t
  reflect-sound idʷ = ≈-Term-refl
  reflect-sound (g ∘ʷ f) = ∘ᵈ-sound (reflect f) (reflect g) ○ (reflect-sound g ⟩∘⟨ reflect-sound f)
  reflect-sound (boxʷ g) = boxSound g
  reflect-sound (s ⊗ʷ t) =
    ⊗ᵈ-sound (reflect s) (reflect t) ○ (refl⟩∘⟨ ((reflect-sound s ⟩⊗⟨ reflect-sound t) ⟩∘⟨refl))

--------------------------------------------------------------------------------
-- `DecideCore`: the shared wire-level DECISION ASSEMBLY.
--
-- Both front-ends' `decide?W`/`decideσ?` are byte-identical given a normalizer
-- `norm : ∀ {n m} (d : Diag n m) → Σ[ d' ] (⟦ d ⟧ ≈Term ⟦ d' ⟧)`: reflect both
-- sides to `Diag`, normalize each, decide normal-form equality, and chain the
-- reflect-soundness witnesses through the bridge.  The interface stays SEMANTIC
-- (the syntactic `_⤳D_` trace is discharged by `⤳D-sound` inside each
-- front-end's `norm`).  `norm` is passed as an ordinary FUNCTION
-- argument so the per-variant oracle (interchange / σσ-cancel / slides) stays in
-- each front-end's scope while the assembly lives here once.
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

  module SCmp = CompareI E

  -- the caller supplies decidable equality on the Σ-packaged generators
  -- (an instance, used only to build `_≟Diag_`) and a normalizer.
  module Decide
    ⦃ _ : DecEq SCmp.Gen ⦄
    (norm : ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (⟦ d ⟧ ≈Term ⟦ d' ⟧))
    where

    open SCmp.Decide

    -- reflect both sides, normalize each, decide normal-form equality; on a hit
    -- the two normal forms are equal (`≈NF⇒≡`), so the reflect-soundness and
    -- the normalizer's `≈Term` witnesses chain directly (no output casts).
    decideW : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decideW {n} {m} f g with norm (reflect f) | norm (reflect g)
    ... | (df' , sndf) | (dg' , sndg) = case df' ≟Diag dg' of λ where
        (no  _)  → nothing
        (yes eq) → just (chain (≈NF⇒≡ eq))
      where
        chain : df' ≡ dg' → embed f ≈Term embed g
        chain refl = ⟺ (reflect-sound f) ○ sndf ○ ⟺ sndg ○ reflect-sound g
