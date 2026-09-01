{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Normalising monoidal diagrams (`Diag`) by reordering independent boxes.
--
-- Two boxes on disjoint, non-crossing wire ranges are independent: swapping
-- their firing order preserves `⟦_⟧`.  Soundness is unconditional; canonicity
-- — that interchange-equal diagrams reach the same normal form — is open.
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

module NormalizeI {X : Set} (Mor : List X → List X → Set)
                  ⦃ _ : DecEq X ⦄ where

  open DiagramI Mor
  open FreeMonoidalHelper.Mor Mon X mor
  open ≈R
  open WireCohDec public

  open MR FreeMonoidal

  open FreeStrictMonoidalHelper Mor

  --------------------------------------------------------------------------------
  -- The adjacent-disjoint-pair fit and its index equality
  --------------------------------------------------------------------------------

  -- A head pair is out of canonical order exactly when `fy` (fired second)
  -- sits strictly left of `fx`, so `fy`'s block lies inside `px`'s prefix.  The
  -- fit records three idle blocks `P mid s` with witnesses that the offsets
  -- factor through  P ++ (ay ++ (mid ++ (ax ++ s)))  (fy slot 1, fx slot 2).
  record LeftFit {ax bx ay by : List X}
                 (px sx py sy : List X) (fx : Mor ax bx) (fy : Mor ay by) : Set where
    constructor leftFit
    field
      P mid s : List X
      -- fx is the right box (slot 2); when it fires fy hasn't, so it sees ay:
      px≡   : px ≡ P ++ (ay ++ mid)
      sx≡   : sx ≡ s
      -- fy is the left box (slot 1); by now fx has fired, so it sees bx:
      py≡   : py ≡ P
      sy≡   : sy ≡ mid ++ (bx ++ s)


  domeq : (pre a₁ mid a₂ r : List X)
        → (pre ++ (a₁ ++ mid)) ++ (a₂ ++ r) ≡ pre ++ (a₁ ++ (mid ++ (a₂ ++ r)))
  domeq pre a₁ mid a₂ r = ListExt.++-assoc-mid pre a₁ mid (a₂ ++ r)

  --------------------------------------------------------------------------------
  -- The autonomous firing Diag sort (needs `DecEq X`)
  --------------------------------------------------------------------------------
  module SortD where

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

    -- Ambiguous when the reverse pair would also fit; such pairs are ordered
    -- by rank instead.
    ambiguous? : List X → List X → List X → Bool
    ambiguous? [] [] [] = true
    ambiguous? _  _  _  = false

    -- The two-layer diagram a recognised head pair rewrites to.  It carries no
    -- proof and its endpoints are single indices, so the construction is
    -- oblivious to the input pair that `replD-soundˢ` bridges from.
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

    -- The Mon engine's primitive step: the recognised disjoint interchange, as
    -- a syntactic relation on diagrams.  The recogniser's `meq` is kept
    -- abstract, so no per-fire Hedberg exchange runs on the firing path.
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
    -- The strict primitive-step soundness, in `_≈ʷ_` on the cast-free strict
    -- semantics `⟦_⟧ˢ`.
    --------------------------------------------------------------------------------
    open Theory R⊥

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

        lemA : ⟦ p₁L ▸ s₁L ∷ g₁ ⟨ substDiag (sym meq) boxL ⟩ ⟧ˢ ≈ʷ Rest ∘ʷ (P₂ ∘ʷ castʷ meq P₁)
        lemA = transʷ (≡→≈ʷ (cong (_∘ʷ P₁) (⟦substDiag⟧ˢ (sym meq) boxL)))
                 (transʷ (≡→≈ʷ (∘ʷ-castʷᵈ-l′ meq (Rest ∘ʷ P₂) P₁)) assoc)

        d'≡ : ⟦ substDiag (sym E₄) D₃ ⟧ˢ ≡ castʷᵈ (sym E₄) (castʷᵈ (sym E₃) (A ∘ʷ P₄) ∘ʷ P₃)
        d'≡ = trans (⟦substDiag⟧ˢ (sym E₄) D₃)
                (cong (castʷᵈ (sym E₄))
                  (cong (_∘ʷ P₃)
                    (trans (⟦substDiag⟧ˢ (sym E₃) D₄)
                      (cong (castʷᵈ (sym E₃))
                        (cong (_∘ʷ P₄) (⟦substDiag⟧ˢ (sym E₂) rest'))))))

        reconInner : castʷᵈ (sym E₄) (castʷ (sym (sym E₃)) P₃) ≈ʷ castʷ E₃ (castʷᵈ (sym E₄) P₃)
        reconInner = transʷ (castʷᵈ-resp (sym E₄) (≡→≈ʷ (castʷ-irr (sym (sym E₃)) E₃ P₃)))
                            (symʷ (≡→≈ʷ (castʷ-castʷᵈ (sym E₄) E₃ P₃)))

        recon : castʷ (sym (sym E₂)) (P₄ ∘ʷ castʷᵈ (sym E₄) (castʷ (sym (sym E₃)) P₃)) ≈ʷ Mid
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
        {meq} {domeq P by mid bx s} {sym (domeq P by mid ax s)})

    -- Fire one genuine swap on a recognised out-of-order head pair.
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
    -- family `Prim`.
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

      -- `nothing` from `step`, and fuel exhaustion, both return the input with
      -- the reflexive witness.
      normFuelWith : (∀ {n' m'} (d : Diag n' m') → Maybe (Σ[ d' ∈ Diag n' m' ] (d ⤳D d')))
                   → ℕ → ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (d ⤳D d')
      normFuelWith _    zero    d = d , reflᴰ
      normFuelWith step (suc c) d = case step d of λ where
        nothing         → d , reflᴰ
        (just (d' , w)) →
          let (d'' , w') = normFuelWith step c d'
          in  d'' , transᴰ w w'

      -- The strict normalization witness: the same loop, discharged with
      -- `⤳D-soundˢ`.
      normSoundˢ : (∀ {n k} {d d' : Diag n k} → Prim d d' → ⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ)
                 → (∀ {n' m'} (d : Diag n' m') → Maybe (Σ[ d' ∈ Diag n' m' ] (d ⤳D d')))
                 → (ℕ → ℕ)
                 → ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (⟦ d ⟧ˢ ≈ʷ ⟦ d' ⟧ˢ)
      normSoundˢ prim-sound step fuel d =
        let (d' , w) = normFuelWith step (fuel (depthD d)) d
        in  d' , ⤳D-soundˢ prim-sound w
