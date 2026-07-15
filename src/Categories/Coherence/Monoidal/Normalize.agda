{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Normalising monoidal diagrams (`Diag`) by reordering independent boxes.
--
-- Two boxes on disjoint, non-crossing wire ranges are independent: swapping
-- their firing order preserves `⟦_⟧` (σ-free interchange / bifunctoriality),
-- read off in clean strict-`padʷ` coordinates by `FreeStrictMonoidal.swap-cleanˢ`.
--
-- After a box of different width fires, the next box's absolute offset shifts,
-- so the swap equality holds only up to `++`-associativity.  The swap therefore
-- rebuilds its output with recomputed offsets, absorbing the re-indexing with
-- `substDiag`; the STRICT soundness `prim-swap-soundˢ` feeds `swap-cleanˢ` to
-- the generic `replD-soundˢ`, so only cheap `castʷ`/`castʷᵈ` transports remain.
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
open import Categories.FreeMonoidal
open import Categories.FreeStrictMonoidal

module NormalizeI {v : Variant} {X : Set} (E : WireEngine v)
                  ⦃ _ : DecEq X ⦄ where

  open WireEngine E
  open DiagramI E
  open FreeMonoidalHelper.Mor v X mor
  open ≈R
  open WireCohDec public

  open MR FreeMonoidal

  -- the strict free-monoidal syntax + the cast algebra the strict soundness
  -- (`replD-soundˢ`) chains; opened NON-publicly so it does not re-export
  -- `castʷ` (which `DecideCore` already gets from `ReflectI`).
  open FreeStrictMonoidalHelper Mor
    using ( WTerm; boxʷ; idʷ; _∘ʷ_; _⊗ʷ_; padʷ; castʷ; castʷᵈ; module Theory
          ; ∘ʷ-castʷᵈ-l; ∘ʷ-castʷᵈ-r; castʷ-castʷᵈ; castʷ-irr )

  --------------------------------------------------------------------------------
  -- 2. The adjacent-disjoint-pair FIT and its index equality
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
  -- The interchange KEY itself is the STRICT `swap-cleanˢ` (in
  -- `FreeStrictMonoidal`), consumed by `prim-swap-soundˢ` in §3; `domeq` (below)
  -- supplies the `++`-assoc offsets it and the `replD` re-indexing carry.
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


  -- the two index equalities (pure `++`-assoc), named.
  domeq : (pre a₁ mid a₂ r : List X)
        → (pre ++ (a₁ ++ mid)) ++ (a₂ ++ r) ≡ pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))
  domeq pre a₁ mid a₂ r =
    trans (++-assoc pre (a₁ ++ mid) (a₂ ++ r))
          (cong (pre ++_) (++-assoc a₁ mid (a₂ ++ r)))

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

    -- The PURE two-layer head REPLACEMENT: the diagram the recognised
    -- head pair rewrites to — (g₃,g₄ bridged by E₃), re-indexed by E₂/E₄.  No
    -- proof, no KEY; its endpoints are single indices `N₁`/`N₂` (E₄/E₂ carry
    -- the offset factorization), so the construction is oblivious to the input
    -- pair (g₁,g₂,meq) that `replD-soundˢ` bridges from.
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

    -- The Mon engine's PRIMITIVE STEP: the recognised disjoint interchange, as
    -- a syntactic relation on diagrams with the recogniser's `meq` kept
    -- ABSTRACT — the constructor commits to no particular re-indexing proof, so
    -- the per-fire Hedberg exchange `≡-irrelevantL meq (domeq …)` never runs on
    -- the firing path; the meq/domeq reconciliation is folded into the KEY
    -- `swap-cleanˢ` by `prim-swap-soundˢ`.  The output is a generic `replD`
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

    --------------------------------------------------------------------------------
    -- The STRICT primitive-step soundness, in `Theory R`'s `_≈ʷ_` on the
    -- cast-free strict semantics `⟦_⟧ˢ`.  `replD-soundˢ` is the strict analogue
    -- of `replD-sound`: the `substDiag` peels are propositional (`⟦substDiag⟧ˢ`),
    -- so only the `castʷ`/`castʷᵈ` algebra remains; `prim-swap-soundˢ` feeds it
    -- the strict interchange KEY `swap-cleanˢ` (from `FreeStrictMonoidal`).
    --------------------------------------------------------------------------------
    module _ (R : ∀ {n m} → WTerm n m → WTerm n m → Set) where
      open Theory R

      replD-soundˢ :
        ∀ {a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : List X} {k : List X}
          {p₁L s₁L p₂L s₂L : List X} {p₃L s₃L p₄L s₄L : List X}
          {g₁ : Mor a₁ b₁} {g₂ : Mor a₂ b₂}
          {g₃ : Mor a₃ b₃} {g₄ : Mor a₄ b₄}
          {rest' : Diag (p₂L ++ (b₂ ++ s₂L)) k}
          {meq : p₁L ++ (b₁ ++ s₁L) ≡ p₂L ++ (a₂ ++ s₂L)}
          {E₂ : p₄L ++ (b₄ ++ s₄L) ≡ p₂L ++ (b₂ ++ s₂L)}
          {E₃ : p₃L ++ (b₃ ++ s₃L) ≡ p₄L ++ (a₄ ++ s₄L)}
          {E₄ : p₁L ++ (a₁ ++ s₁L) ≡ p₃L ++ (a₃ ++ s₃L)}
          (key : padʷ p₂L s₂L (boxʷ g₂) ∘ʷ castʷ meq (padʷ p₁L s₁L (boxʷ g₁))
                 ≈ʷ castʷ E₂ (padʷ p₄L s₄L (boxʷ g₄)
                      ∘ʷ castʷ E₃ (castʷᵈ (sym E₄) (padʷ p₃L s₃L (boxʷ g₃)))))
        → ⟦ p₁L ▸ s₁L ∷ g₁ ⟨ substDiag (sym meq) (p₂L ▸ s₂L ∷ g₂ ⟨ rest' ⟩) ⟩ ⟧ˢ
          ≈ʷ ⟦ replD p₃L s₃L p₄L s₄L g₃ g₄ rest' E₂ E₃ E₄ ⟧ˢ
      replD-soundˢ {p₁L = p₁L} {s₁L} {p₂L} {s₂L} {p₃L} {s₃L} {p₄L} {s₄L}
                   {g₁} {g₂} {g₃} {g₄} {rest'} {meq} {E₂} {E₃} {E₄} key =
        transʷ lemA (transʷ (∘-resp-≈ reflʷ key) (symʷ lemB))
        where
          P₁ = padʷ p₁L s₁L (boxʷ g₁)
          P₂ = padʷ p₂L s₂L (boxʷ g₂)
          P₃ = padʷ p₃L s₃L (boxʷ g₃)
          P₄ = padʷ p₄L s₄L (boxʷ g₄)
          Rest = ⟦ rest' ⟧ˢ
          A    = castʷᵈ (sym E₂) Rest
          boxL = p₂L ▸ s₂L ∷ g₂ ⟨ rest' ⟩
          D₄   = p₄L ▸ s₄L ∷ g₄ ⟨ substDiag (sym E₂) rest' ⟩
          D₃   = p₃L ▸ s₃L ∷ g₃ ⟨ substDiag (sym E₃) D₄ ⟩
          Mid  = castʷ E₂ (P₄ ∘ʷ castʷ E₃ (castʷᵈ (sym E₄) P₃))

          -- LHS: peel the `substDiag (sym meq)`, reconcile `sym (sym meq)`, regroup.
          lemA : ⟦ p₁L ▸ s₁L ∷ g₁ ⟨ substDiag (sym meq) boxL ⟩ ⟧ˢ
               ≈ʷ Rest ∘ʷ (P₂ ∘ʷ castʷ meq P₁)
          lemA = transʷ (≡→≈ʷ (cong (_∘ʷ P₁) (⟦substDiag⟧ˢ (sym meq) boxL)))
                   (transʷ (≡→≈ʷ (∘ʷ-castʷᵈ-l (sym meq) (Rest ∘ʷ P₂) P₁))
                     (transʷ (∘-resp-≈ reflʷ (≡→≈ʷ (castʷ-irr (sym (sym meq)) meq P₁)))
                       assoc))

          -- RHS: peel the three `substDiag`s to the nested-cast form.
          d'≡ : ⟦ substDiag (sym E₄) D₃ ⟧ˢ
              ≡ castʷᵈ (sym E₄) (castʷᵈ (sym E₃) (A ∘ʷ P₄) ∘ʷ P₃)
          d'≡ = trans (⟦substDiag⟧ˢ (sym E₄) D₃)
                  (cong (castʷᵈ (sym E₄))
                    (cong (_∘ʷ P₃)
                      (trans (⟦substDiag⟧ˢ (sym E₃) D₄)
                        (cong (castʷᵈ (sym E₃))
                          (cong (_∘ʷ P₄) (⟦substDiag⟧ˢ (sym E₂) rest'))))))

          reconInner : castʷᵈ (sym E₄) (castʷ (sym (sym E₃)) P₃)
                     ≈ʷ castʷ E₃ (castʷᵈ (sym E₄) P₃)
          reconInner = transʷ (castʷᵈ-resp (sym E₄) (≡→≈ʷ (castʷ-irr (sym (sym E₃)) E₃ P₃)))
                              (symʷ (≡→≈ʷ (castʷ-castʷᵈ (sym E₄) E₃ P₃)))

          recon : castʷ (sym (sym E₂)) (P₄ ∘ʷ castʷᵈ (sym E₄) (castʷ (sym (sym E₃)) P₃))
                ≈ʷ Mid
          recon = transʷ (≡→≈ʷ (castʷ-irr (sym (sym E₂)) E₂ _))
                    (castʷ-resp E₂ (∘-resp-≈ reflʷ reconInner))

          lemB : ⟦ replD p₃L s₃L p₄L s₄L g₃ g₄ rest' E₂ E₃ E₄ ⟧ˢ ≈ʷ Rest ∘ʷ Mid
          lemB = transʷ (≡→≈ʷ d'≡)
                   (transʷ (≡→≈ʷ (cong (castʷᵈ (sym E₄)) (∘ʷ-castʷᵈ-l (sym E₃) (A ∘ʷ P₄) P₃)))
                     (transʷ (≡→≈ʷ (sym (∘ʷ-castʷᵈ-r (sym E₄) (A ∘ʷ P₄) (castʷ (sym (sym E₃)) P₃))))
                       (transʷ assoc
                         (transʷ (≡→≈ʷ (∘ʷ-castʷᵈ-l (sym E₂) Rest
                                          (P₄ ∘ʷ castʷᵈ (sym E₄) (castʷ (sym (sym E₃)) P₃))))
                           (∘-resp-≈ reflʷ recon)))))

      prim-swap-soundˢ : ∀ {n k} {d d' : Diag n k} → PrimSwap d d' → ⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ
      prim-swap-soundˢ (prim-swap {ax} {bx} {ay} {by} {fx = fx} {fy = fy} P mid s rest' meq) =
        replD-soundˢ (swap-cleanˢ P mid s fx fy
          {meq} {domeq P by mid bx s} {sym (domeq P by mid ax s)} {domeq P ay mid ax s})

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

      -- The STRICT normalization witness: same loop, discharged with the strict
      -- `⤳D-soundˢ` in `Theory R`.  This is what the front-ends' `norm`/`normσ`
      -- now emit; `DecideCore` transports it to `_≈Term_` via `embed-resp-≈`.
      module _ (R : ∀ {n m} → WTerm n m → WTerm n m → Set) where
        open Theory R

        normSoundˢ : (∀ {n k} {d d' : Diag n k} → Prim d d' → ⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ)
                   → (∀ {n' m'} (d : Diag n' m') → Maybe (Σ[ d' ∈ Diag n' m' ] (d ⤳D d')))
                   → (ℕ → ℕ)
                   → ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ)
        normSoundˢ prim-sound step fuel d =
          let (d' , w) = normFuelWith step (fuel (depthD d)) d
          in  d' , ⤳D-soundˢ R prim-sound w
