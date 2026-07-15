{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Normalising monoidal diagrams (`Diag`) by reordering independent boxes.
--
-- Two boxes on disjoint, non-crossing wire ranges are independent: swapping
-- their firing order preserves `⟦_⟧` (`TwoBoxSwap.two-box-swap` — σ-free
-- interchange / bifunctoriality).
--
-- After a box of different width fires, the next box's absolute offset shifts,
-- so the swap equality holds only up to `++`-associativity.  The swap therefore
-- rebuilds its output with recomputed offsets, absorbing the re-indexing with
-- `substDiag`; soundness reuses `two-box-swap` + the offset-reframing bridge
-- `TwoBoxSwap.gLayer≈pad` (`assocW`/`assocW⁻` reassociators collapsed to `castW`).
--
-- Soundness (every fired swap preserves `⟦_⟧`) is unconditional.  OPEN:
-- canonicity — that interchange-equal diagrams reach the SAME normal form.
-- With the syntactic step relation `_⤳D_` (Diagram.`DClosure`) this is now a
-- purely syntactic statement: CONFLUENCE of `_⤳D_` (the bubble sort's rewrite
-- reachability towards a footprint-ordered form; key = the leftmost offset,
-- tiebreak on input width).
--
-- The module's primary PRODUCT is §3's oracle kit: `interchangeGo` — the
-- one-step disjoint-interchange oracle both front-ends build their normalizers.
-- It pairs with the generic `Steps`
-- module: `stepWith` wraps a per-position PRIMITIVE-step oracle into one `_⤳D_`
-- rewrite (`prim` at the hit, `consᴰ` down the spine) and `normFuelWith` chains
-- a bounded run with `transᴰ`, so a whole normalization is a syntactic rewrite
-- trace.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Normalize where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; _>>=_)

open import Data.Bool hiding (_≟_)
open import Data.List.Properties
import Data.List.Properties.Ext as ListExt
open import Data.Maybe as Maybe
open import Data.Nat hiding (_≟_)

import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.Coherence.Monoidal.Interchange
open import Categories.FreeMonoidal

module NormalizeI {v : Variant} {X : Set} (E : WireEngine v)
                  ⦃ _ : DecEq X ⦄ where

  open WireEngine E
  open DiagramI E
  open Interchange v X mor
  open FreeMonoidalHelper.Mor v X mor
  open ≈R
  open WireCohDec public

  open MR FreeMonoidal

  substDiag-irr : ∀ {m n k} (e e' : m ≡ n) (d : Diag m k)
                 → ⟦ substDiag e d ⟧ ≈Term ⟦ substDiag e' d ⟧
  substDiag-irr e e' d =
    ⟦substDiag⟧ e d ○ (refl⟩∘⟨ castW-irr (sym e) (sym e')) ○ ⟺ (⟦substDiag⟧ e' d)

  --------------------------------------------------------------------------------
  -- 1. Frame of an adjacent disjoint pair: shared endpoints + the swap
  --------------------------------------------------------------------------------
  --
  -- For a frame  P | a₁/b₁ | mid | a₂/b₂ | r  with `f` left, `g` right, the two
  -- firing orders (f-then-g = `g-out ∘ f-in`, g-then-f = `f-out ∘ g-in`) are
  -- `≈Term`-equal by `two-box-swap` (no σ; bottoms out in
  -- `gLayer≈pad`/bifunctoriality).  `swap-clean` (§2 below) reads that swap off
  -- in clean-`pad` coordinates.

  module Frame (P mid r : List X) {a₁ b₁ a₂ b₂ : List X}
               (f : Mor a₁ b₁) (g : Mor a₂ b₂) where

    open TwoBoxSwap P mid r (⟦ f ⟧ᵇ) (⟦ g ⟧ᵇ) public

  --------------------------------------------------------------------------------
  -- 2. The interchange KEY equation, in clean-`pad` coordinates
  --------------------------------------------------------------------------------
  --
  -- A `Diag` layer carries `fx`, `px`, `sx` explicitly, so a recogniser can
  -- read off the offsets and decide orientation.
  --
  -- On a head pair  px ▸ sx ∷ fx ⟨ py ▸ sy ∷ fy ⟨ rest ⟩ ⟩  (`fx` fires FIRST,
  -- `fy` SECOND) the `Diag` typing forces the inter-layer wiring definitionally:
  --   py ++ (ay ++ sy)  ≡  px ++ (bx ++ sx)            -- (★) inner-diagram index

  -- The head pair is out of canonical order exactly when `fy` (fired second)
  -- sits strictly LEFT of `fx`, so `fy`'s block lies inside `px`'s prefix.  The
  -- fit records three idle blocks `P mid s` with witnesses that the offsets
  -- factor through  P ++ (ay ++ (mid ++ (ax ++ s)))  (fy slot 1, fx slot 2).
  -- This section's product is the HomTerm-level KEY `swap-clean` — the
  -- interchange in clean-`pad` coordinates, the Mon sibling of σ's
  -- `slide-clean` — consumed by `replD-sound` in §3.  The Diag-level
  -- re-indexing plumbing is the generic `replD`/`replD-sound` there; §2
  -- supplies only the KEY.
  record LeftFit {ax bx ay by : List X}
                 (px sx py sy : List X) (fx : Mor ax bx) (fy : Mor ay by) : Set where
    constructor leftFit
    field
      P mid s : List X
      -- fx is the RIGHT box (slot 2); when it fires fy hasn't, so it sees ay:
      px≡   : px ≡ P ++ (ay ++ mid)
      sx≡   : sx ≡ s
      -- fy is the LEFT box (slot 1); by now fx has fired, so it sees bx:
      py≡   : py ≡ P
      sy≡   : sy ≡ mid ++ (bx ++ s)

  -- The clean flat pad lives on the LEFT-nested object, the frame's `g-in` on
  -- the RIGHT-nested frame input; for abstract offsets these agree only up to
  -- `++`-assoc,
  -- so the bridge needs the index casts `castW (domeq …)` (uncast sides are
  -- ill-typed).  Proven by collapsing `gLayer≈pad`'s reassociators to single
  -- `castW`s via `reassocF≈castW` / `reassocB≈castW` below.

  -- the two index equalities (pure `++`-assoc), named.
  domeq : (pre a₁ mid a₂ r : List X)
        → (pre ++ (a₁ ++ mid)) ++ (a₂ ++ r) ≡ pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))
  domeq pre a₁ mid a₂ r =
    trans (++-assoc pre (a₁ ++ mid) (a₂ ++ r))
          (cong (pre ++_) (++-assoc a₁ mid (a₂ ++ r)))

  -- `reassocF`/`reassocB` (at any offset `x`) collapse to single domain/codomain
  -- casts; the `-in`/`-out` sites are the `a₁`/`b₁` specialisations.
  reassocF≈castW : ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂) (x : List X)
    → Frame.reassocF pre mid r f g x ≈Term castW (sym (domeq pre x mid a₂ r))
  reassocF≈castW pre mid r {_} {_} {a₂} {_} f g x =
    (refl⟩∘⟨ liftW-castW pre (sym (++-assoc x mid (a₂ ++ r))))
      ○ castW-∘ _ _ ○ castW-irr _ _

  reassocB≈castW : ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂) (x : List X)
    → Frame.reassocB pre mid r f g x ≈Term castW (domeq pre x mid b₂ r)
  reassocB≈castW pre mid r {_} {_} {_} {b₂} f g x =
    (liftW-castW pre (++-assoc x mid (b₂ ++ r)) ⟩∘⟨refl) ○ castW-∘ _ _

  -- core bridge: the g-layer at any box offset `x` = clean `pad (pre++(x++mid))`
  -- conjugated by index casts.  From `gLayer≈pad x` by collapsing its
  -- reassociators.  The g-in / g-out re-cleanings are the `a₁` / `b₁` instances
  -- (`g-in = gLayer a₁`, `g-out = gLayer b₁`).
  gLayer-clean-core : ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂) (x : List X)
    → Frame.gLayer pre mid r f g x
      ≈Term castW (domeq pre x mid b₂ r)
          ∘ pad (pre ++ (x ++ mid)) r (⟦ g ⟧ᵇ)
          ∘ castW (sym (domeq pre x mid a₂ r))
  gLayer-clean-core pre mid r f g x =
    Frame.gLayer≈pad pre mid r f g x
      ○ (reassocB≈castW pre mid r f g x ⟩∘⟨ refl⟩∘⟨ reassocF≈castW pre mid r f g x)

  -- the g-in (input) re-cleaning at offset `a₁`.
  fx-clean⇒g-in-core : ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.g-in pre mid r f g
      ≈Term castW (domeq pre a₁ mid b₂ r)
          ∘ pad (pre ++ (a₁ ++ mid)) r (⟦ g ⟧ᵇ)
          ∘ castW (sym (domeq pre a₁ mid a₂ r))
  fx-clean⇒g-in-core pre mid r {a₁} f g = gLayer-clean-core pre mid r f g a₁

  -- The SORTED (swap-output) g-layer is clean again: the same core at offset `b₁`.
  fy-sorted⇒g-out-core :
    ∀ (pre mid r : List X) {a₁ b₁ a₂ b₂ : List X}
      (f : Mor a₁ b₁) (g : Mor a₂ b₂)
    → Frame.g-out pre mid r f g
      ≈Term castW (domeq pre b₁ mid b₂ r)
          ∘ pad (pre ++ (b₁ ++ mid)) r (⟦ g ⟧ᵇ)
          ∘ castW (sym (domeq pre b₁ mid a₂ r))
  fy-sorted⇒g-out-core pre mid r {_} {b₁} f g = gLayer-clean-core pre mid r f g b₁

  -- The interchange KEY, in clean-`pad` coordinates (the Mon sibling of σ's
  -- `slide-clean`): a matched head pair `fy`-first-then-`fx` on the LEFT-nested
  -- input equals the swapped order (`fx` re-cleaned to `g-out`, then `fy` at
  -- `f-in`) up to the four `++`-assoc index casts.  (i) re-clean the input
  -- `fx`-pad into `g-in` (`fx-clean⇒g-in-core` backwards), (ii) swap the layers
  -- via `two-box-swap`, (iii) re-clean `g-out` forwards (`fy-sorted⇒g-out-core`);
  -- every quantified-vs-canonical cast is reconciled by `castW-irr`.  This IS
  -- `replD-sound`'s KEY at the swap's offsets, consumed by `prim-swap-sound`.
  swap-clean : ∀ (P mid s : List X) {ax bx ay by}
               (fx : Mor ax bx) (fy : Mor ay by)
               {meq : (P ++ (ay ++ mid)) ++ (bx ++ s) ≡ P ++ (ay ++ (mid ++ (bx ++ s)))}
               {E₂ : (P ++ (by ++ mid)) ++ (bx ++ s) ≡ P ++ (by ++ (mid ++ (bx ++ s)))}
               {E₃ : P ++ (by ++ (mid ++ (ax ++ s))) ≡ (P ++ (by ++ mid)) ++ (ax ++ s)}
               {E₄ : (P ++ (ay ++ mid)) ++ (ax ++ s) ≡ P ++ (ay ++ (mid ++ (ax ++ s)))}
             → pad P (mid ++ (bx ++ s)) (⟦ fy ⟧ᵇ)
                 ∘ castW meq ∘ pad (P ++ (ay ++ mid)) s (⟦ fx ⟧ᵇ)
               ≈Term castW E₂ ∘ pad (P ++ (by ++ mid)) s (⟦ fx ⟧ᵇ) ∘ castW E₃
                     ∘ pad P (mid ++ (ax ++ s)) (⟦ fy ⟧ᵇ) ∘ castW E₄
  swap-clean P mid s {ax} {bx} {ay} {by} fx fy {meq} {E₂} {E₃} {E₄} =
      (refl⟩∘⟨ bridge)
        ○ ⟺ assoc
        ○ ((⟺ F.two-box-swap) ⟩∘⟨refl)
        ○ ((gout ⟩∘⟨refl) ⟩∘⟨refl)
        ○ assoc ○ assoc ○ (refl⟩∘⟨ assoc)
    where
      module F = Frame P mid s fy fx
      padfx  = pad (P ++ (ay ++ mid)) s (⟦ fx ⟧ᵇ)
      padfx' = pad (P ++ (by ++ mid)) s (⟦ fx ⟧ᵇ)
      -- (i) the input `fx`-pad, pre-cast by `meq`, is `g-in` pre-cast by `E₄`.
      bridge : castW meq ∘ padfx ≈Term F.g-in ∘ castW E₄
      bridge = (castW-irr meq (domeq P ay mid bx s) ⟩∘⟨refl)
             ○ insertʳ (castW-isoˡ (domeq P ay mid ax s))
             ○ ((assoc ○ ⟺ (fx-clean⇒g-in-core P mid s fy fx)) ⟩∘⟨refl)
             ○ (refl⟩∘⟨ castW-irr (domeq P ay mid ax s) E₄)
      -- (iii) the swapped `g-out` re-cleans to the `E₂`/`E₃`-framed `fx`-pad.
      gout : F.g-out ≈Term castW E₂ ∘ padfx' ∘ castW E₃
      gout = fy-sorted⇒g-out-core P mid s fy fx
           ○ (castW-irr (domeq P by mid bx s) E₂
                ⟩∘⟨ (refl⟩∘⟨ castW-irr (sym (domeq P by mid ax s)) E₃))

  --------------------------------------------------------------------------------
  -- 3. The autonomous firing Diag sort (needs `DecEq X`)
  --------------------------------------------------------------------------------
  -- With `DecEq X` we DECIDE a `LeftFit` by `List`-splitting the offset lists at
  -- the box-domain lengths.  `fire` (below) fires the clean swap; the multi-step
  -- fuel loop is the generic `normFuelWith` (below), driven by each front-end's
  -- per-position oracle.
  module SortD where

    -- Set `P := py`, `s := sx`, recover `mid` by stripping `py ++ ay` off `px`,
    -- and confirm `sy ≡ mid ++ (bx ++ sx)`. `nothing` when the splits don't fit.
    leftFit? : ∀ {ax bx ay by} (px sx py sy : List X)
               (fx : Mor ax bx) (fy : Mor ay by)
             → Maybe (LeftFit px sx py sy fx fy)
    leftFit? {ax} {bx} {ay} {by} px sx py sy fx fy =
      ListExt.stripPrefix _≟_ py px >>= λ (r1 , px≡) →
      ListExt.stripPrefix _≟_ ay r1 >>= λ (mid , r1≡) →
      case sy ≟ (mid ++ (bx ++ sx)) of λ where
        (no  _)   → nothing
        (yes sy≡) →
          just (leftFit py mid sx (trans px≡ (cong (py ++_) r1≡)) refl refl sy≡)

    -- Both `Frontend.Decide` and `Sigma.Decideσ` run the same
    -- fuel-driven bubble-sort loop around a per-position oracle; this factors
    -- out everything INDEPENDENT of that oracle, each `Decide` passing its own
    -- `step?` to `normFuelWith`.

    -- AMBIGUOUS when the reverse pair would also fit (ax ≡ [] ∧ by ≡ [] ∧
    -- mid ≡ []); such pairs are ordered by rank instead.
    ambiguous? : List X → List X → List X → Bool
    ambiguous? [] [] [] = true
    ambiguous? _  _  _  = false

    -- `substDiag (sym e)` expanded to a one-cast conjugation.
    substExpand : ∀ {m n k : List X} (e : m ≡ n) (d : Diag n k)
                → ⟦ substDiag (sym e) d ⟧ ≈Term ⟦ d ⟧ ∘ castW e
    substExpand refl d = ⟺ idʳ

    -- The PURE two-layer head REPLACEMENT: the diagram the recognised
    -- head pair rewrites to — (g₃,g₄ bridged by E₃), re-indexed by E₂/E₄.  No
    -- proof, no KEY; its endpoints are single indices `N₁`/`N₂` (E₄/E₂ carry
    -- the offset factorization), so the construction is oblivious to the input
    -- pair (g₁,g₂,meq) that `replD-sound` bridges from.
    replD :
      ∀ {a₃ b₃ a₄ b₄ : List X} {k N₁ N₂ : List X}
        (p₃L s₃L p₄L s₄L : List X)
        (g₃ : Mor a₃ b₃) (g₄ : Mor a₄ b₄)
        (rest' : Diag N₂ k)
        (E₂ : p₄L ++ (b₄ ++ s₄L) ≡ N₂)
        (E₃ : p₃L ++ (b₃ ++ s₃L) ≡ p₄L ++ (a₄ ++ s₄L))
        (E₄ : N₁ ≡ p₃L ++ (a₃ ++ s₃L))
      → Diag N₁ k
    replD p₃L s₃L p₄L s₄L g₃ g₄ rest' E₂ E₃ E₄ =
      substDiag (sym E₄)
        (p₃L ▸ s₃L ∷ g₃
          ⟨ substDiag (sym E₃)
              (p₄L ▸ s₄L ∷ g₄ ⟨ substDiag (sym E₂) rest' ⟩) ⟩)

    -- Soundness of the replacement: the recognised head pair (g₁,g₂
    -- bridged by `meq`) equals `replD …` given the caller's KEY equation between
    -- the two padded composites.
    replD-sound :
      ∀ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : List X} {k : List X}
        {p₁L s₁L p₂L s₂L : List X} {p₃L s₃L p₄L s₄L : List X}
        {g₁ : Mor a₁ b₁} {g₂ : Mor a₂ b₂}
        {g₃ : Mor a₃ b₃} {g₄ : Mor a₄ b₄}
        {rest' : Diag (p₂L ++ (b₂ ++ s₂L)) k}
        {meq : p₁L ++ (b₁ ++ s₁L) ≡ p₂L ++ (a₂ ++ s₂L)}
        {E₂ : p₄L ++ (b₄ ++ s₄L) ≡ p₂L ++ (b₂ ++ s₂L)}
        {E₃ : p₃L ++ (b₃ ++ s₃L) ≡ p₄L ++ (a₄ ++ s₄L)}
        {E₄ : p₁L ++ (a₁ ++ s₁L) ≡ p₃L ++ (a₃ ++ s₃L)}
        (key : pad p₂L s₂L (⟦ g₂ ⟧ᵇ) ∘ castW meq ∘ pad p₁L s₁L (⟦ g₁ ⟧ᵇ)
               ≈Term castW E₂ ∘ pad p₄L s₄L (⟦ g₄ ⟧ᵇ) ∘ castW E₃
                     ∘ pad p₃L s₃L (⟦ g₃ ⟧ᵇ) ∘ castW E₄)
      → ⟦ p₁L ▸ s₁L ∷ g₁ ⟨ substDiag (sym meq) (p₂L ▸ s₂L ∷ g₂ ⟨ rest' ⟩) ⟩ ⟧
        ≈Term ⟦ replD p₃L s₃L p₄L s₄L g₃ g₄ rest' E₂ E₃ E₄ ⟧
    replD-sound {a₁ = a₁} {p₁L = p₁L} {s₁L} {p₂L} {s₂L} {p₃L} {s₃L} {p₄L} {s₄L}
                {g₁} {g₂} {g₃} {g₄} {rest'} {meq} {E₂} {E₃} {E₄} key
      = lemA ○ ⟺ lemB
      where
        P₃ = pad p₃L s₃L (⟦ g₃ ⟧ᵇ)
        P₄ = pad p₄L s₄L (⟦ g₄ ⟧ᵇ)
        boxL   = p₂L ▸ s₂L ∷ g₂ ⟨ rest' ⟩
        dBody  = p₁L ▸ s₁L ∷ g₁ ⟨ substDiag (sym meq) boxL ⟩
        inner₂ = substDiag (sym E₂) rest'
        crossL = p₄L ▸ s₄L ∷ g₄ ⟨ inner₂ ⟩
        inner₃ = substDiag (sym E₃) crossL
        slidL  = p₃L ▸ s₃L ∷ g₃ ⟨ inner₃ ⟩
        d' = substDiag (sym E₄) slidL
        -- the common right-nested composite the two orders re-clean to.
        M = ⟦ rest' ⟧ ∘ (castW E₂ ∘ (P₄ ∘ (castW E₃ ∘ (P₃ ∘ castW E₄))))
        lemA : ⟦ dBody ⟧ ≈Term M
        lemA = (substExpand meq boxL ⟩∘⟨refl) ○ assoc ○ assoc ○ (refl⟩∘⟨ key)
        lemB : ⟦ d' ⟧ ≈Term M
        lemB = substExpand E₄ slidL
             ○ ((substExpand E₃ crossL ⟩∘⟨refl) ⟩∘⟨refl)
             ○ ((((substExpand E₂ rest' ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl)
             ○ assoc ○ assoc ○ assoc ○ assoc

    -- The Mon engine's PRIMITIVE STEP: the recognised disjoint interchange, as
    -- a syntactic relation on diagrams with the recogniser's `meq` kept
    -- ABSTRACT — the constructor commits to no particular re-indexing proof, so
    -- the per-fire Hedberg exchange `≡-irrelevantL meq (domeq …)` never runs on
    -- the firing path; the meq/domeq reconciliation is folded into the KEY
    -- `swap-clean` by `prim-swap-sound`.  The output is a generic `replD`
    -- two-layer replacement (`fy` at `P`, then `fx` re-cleaned to `P++(by++mid)`).
    data PrimSwap : ∀ {n k} → Diag n k → Diag n k → Set where
      prim-swap :
        ∀ {ax bx ay by k} {fx : Mor ax bx} {fy : Mor ay by}
          (P mid s : List X)
          (rest' : Diag (P ++ (by ++ (mid ++ (bx ++ s)))) k)
          (meq : (P ++ (ay ++ mid)) ++ (bx ++ s) ≡ P ++ (ay ++ (mid ++ (bx ++ s))))
        → PrimSwap
            ((P ++ (ay ++ mid)) ▸ s ∷ fx
               ⟨ substDiag (sym meq) (P ▸ (mid ++ (bx ++ s)) ∷ fy ⟨ rest' ⟩) ⟩)
            (replD P (mid ++ (ax ++ s)) (P ++ (by ++ mid)) s fy fx rest'
                   (domeq P by mid bx s) (sym (domeq P by mid ax s)) (domeq P ay mid ax s))

    -- soundness of the primitive step: `replD-sound` at the interchange KEY
    -- `swap-clean` (which takes the recogniser's abstract `meq` directly, so the
    -- meq/domeq reconciliation folds into it — no separate Hedberg bridge here).
    prim-swap-sound : ∀ {n k} {d d' : Diag n k} → PrimSwap d d' → ⟦ d ⟧ ≈Term ⟦ d' ⟧
    prim-swap-sound (prim-swap {ax} {bx} {ay} {by} {fx = fx} {fy = fy} P mid s rest' meq) =
      replD-sound (swap-clean P mid s fx fy)

    -- Fire one genuine swap on a recognised out-of-order head pair: a SINGLE
    -- constructor application (`meq` abstract, no rewrite, no proof on the
    -- firing path).
    fire : ∀ {ax bx ay by k} {px sx py sy : List X}
           {fx : Mor ax bx} {fy : Mor ay by}
           (fit : LeftFit px sx py sy fx fy)
           (rest' : Diag (py ++ (by ++ sy)) k)
           (meq : px ++ (bx ++ sx) ≡ py ++ (ay ++ sy))
         → Σ[ d' ∈ Diag (px ++ (ax ++ sx)) k ]
             PrimSwap (px ▸ sx ∷ fx ⟨ substDiag (sym meq) (py ▸ sy ∷ fy ⟨ rest' ⟩) ⟩) d'
    fire {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
         (leftFit P mid s refl refl refl refl) rest' meq =
      replD P (mid ++ (ax ++ s)) (P ++ (by ++ mid)) s fy fx rest'
            (domeq P by mid bx s) (sym (domeq P by mid ax s)) (domeq P ay mid ax s)
      , prim-swap P mid s rest' meq

    depthD : ∀ {n m} → Diag n m → ℕ
    depthD ([]_ n)            = zero
    depthD (_ ▸ _ ∷ _ ⟨ d ⟩) = suc (depthD d)

    -- swap an adjacent parallel pair
    interchangeGo : (rank : ∀ {a b} → Mor a b → ℕ)
                  → ∀ {ax bx k} (px sx : List X) (fx : Mor ax bx)
                    {m : List X} (rest : Diag m k) (meq : px ++ (bx ++ sx) ≡ m)
                  → Maybe (Σ[ d' ∈ Diag (px ++ (ax ++ sx)) k ]
                            PrimSwap (px ▸ sx ∷ fx ⟨ substDiag (sym meq) rest ⟩) d')
    interchangeGo rank px sx fx ([]_ m) meq = nothing
    interchangeGo rank {ax} {bx} px sx fx (_▸_∷_⟨_⟩ {ay} {by} py sy fy rest') meq =
      case leftFit? px sx py sy fx fy of λ where
        nothing    → nothing
        (just fit) →
          if not (ambiguous? ax by (LeftFit.mid fit)) ∨ (rank fy <ᵇ rank fx)
            then just (fire fit rest' meq)
            else nothing

    -- The generic traversal + fuel loop, parametrized by the primitive-step
    -- family `Prim`: `stepWith` turns a prim-level per-position oracle into a
    -- single `_⤳D_` rewrite (wrapping `prim` at the hit, `consᴰ` down the
    -- spine); `normFuelWith` chains a bounded run of them with `transᴰ`.  Each
    -- front-end instantiates `Prim` (Mon: `PrimSwap`; σ: `Sigma.PrimSigma`) and
    -- turns the resulting `_⤳D_` trace into a semantic witness with the single
    -- soundness induction `⤳D-sound`.
    module Steps (Prim : ∀ {n k} → Diag n k → Diag n k → Set) where
      open DClosure Prim public

      stepWith : (oneStep : ∀ {ax bx k} (px sx : List X) (fx : Mor ax bx)
                            {m : List X} (rest : Diag m k) (meq : px ++ (bx ++ sx) ≡ m)
                          → Maybe (Σ[ d' ∈ Diag (px ++ (ax ++ sx)) k ]
                                    Prim (px ▸ sx ∷ fx ⟨ substDiag (sym meq) rest ⟩) d'))
               → ∀ {n m} (d : Diag n m) → Maybe (Σ[ d' ∈ Diag n m ] (d ⤳D d'))
      stepWith oneStep ([]_ n) = nothing
      stepWith oneStep (px ▸ sx ∷ fx ⟨ rest ⟩) =
        Maybe.map (λ where (d' , p) → d' , prim p) (oneStep px sx fx rest refl) <∣>
        Maybe.map (λ where (rest' , w) → px ▸ sx ∷ fx ⟨ rest' ⟩ , consᴰ w)
          (stepWith oneStep rest)

      -- `nothing` from `step` (or fuel-out) ⟹ the input with the reflexive
      -- witness; each fired step is chained by `transᴰ`.
      normFuelWith : (∀ {n' m'} (d : Diag n' m') → Maybe (Σ[ d' ∈ Diag n' m' ] (d ⤳D d')))
                   → ℕ → ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (d ⤳D d')
      normFuelWith _    zero    d = d , reflᴰ
      normFuelWith step (suc c) d = case step d of λ where
        nothing         → d , reflᴰ
        (just (d' , w)) →
          let (d'' , w') = normFuelWith step c d'
          in  d'' , transᴰ w w'

      -- The whole normalization as a SEMANTIC witness, shared by both
      -- front-ends: run the `fuel`-bounded loop (budget a polynomial in
      -- `depthD d`) on the per-position `step` oracle, then discharge the
      -- `_⤳D_` trace with `⤳D-sound prim-sound`.
      normSound : (∀ {n k} {d d' : Diag n k} → Prim d d' → ⟦ d ⟧ ≈Term ⟦ d' ⟧)
                → (∀ {n' m'} (d : Diag n' m') → Maybe (Σ[ d' ∈ Diag n' m' ] (d ⤳D d')))
                → (ℕ → ℕ)
                → ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (⟦ d ⟧ ≈Term ⟦ d' ⟧)
      normSound prim-sound step fuel d =
        let (d' , w) = normFuelWith step (fuel (depthD d)) d
        in  d' , ⤳D-sound prim-sound w
