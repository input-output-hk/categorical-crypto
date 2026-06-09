{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Tests for the morphism-variable monoidal-diagram solver, exercised over a
-- GENUINELY NON-TRIVIAL morphism signature: a Frobenius/bialgebra-flavoured kit
-- of named generators with real arities (multiply, unit, comultiply, counit,
-- an endo), over a two-element wire-label set `Ty` with decidable equality.
--
-- The existing litmuses in `SolverNormalize`/`SolveMorSpike` use `Mor _ _ = ⊤`
-- or two single-wire boxes on `ℕ`; here every generator carries a real
-- domain/range arity, so boxes land at non-trivial offsets and the reflect /
-- normalize / decide / transport machinery is driven on real data.
--
-- Hole-free, postulate-free, --safe.  Every test is machine-checked by `refl`
-- on a `Maybe`/layer-list outcome, by `Is-just`, or by an exhibited `≈Term`.
--------------------------------------------------------------------------------

module Categories.SolverTests where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness)
open import Data.Maybe.Relation.Unary.Any using (just)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped
open import Categories.SolverReflect
open import Categories.SolverNormalize
open import Categories.SolverCompare
open import Categories.SolveMorSpike

--------------------------------------------------------------------------------
-- 1. THE SIGNATURE.
--
-- Two wire colours `⋆` and `•`.  `Ty` has a (machine-derivable) decidable
-- equality.  The generators are a Frobenius/bialgebra kit on the colour `⋆`:
--
--   μ : ⋆ ⋆ → ⋆     (multiply)        η : · → ⋆        (unit)
--   δ : ⋆ → ⋆ ⋆     (comultiply)      ε : ⋆ → ·        (counit)
--   s : ⋆ → ⋆       (an endomorphism, for the disjoint-wire interchange)
--   t : • → •       (an endomorphism on the OTHER colour)
--
-- Real arities: `μ` consumes two wires, `δ` produces two, etc.  This is the
-- "genuinely non-trivial morphism signature" the tests are about.
--------------------------------------------------------------------------------
data Ty : Set where
  ⋆ • : Ty

⋆∷ : List Ty
⋆∷ = ⋆ ∷ []

_≟Ty_ : DecidableEquality Ty
⋆ ≟Ty ⋆ = yes refl
⋆ ≟Ty • = no λ ()
• ≟Ty ⋆ = no λ ()
• ≟Ty • = yes refl

data Gen : List Ty → List Ty → Set where
  μ : Gen (⋆ ∷ ⋆ ∷ []) (⋆ ∷ [])     -- multiply
  η : Gen []           (⋆ ∷ [])     -- unit
  δ : Gen (⋆ ∷ [])     (⋆ ∷ ⋆ ∷ []) -- comultiply
  ε : Gen (⋆ ∷ [])     []           -- counit
  s : Gen (⋆ ∷ [])     (⋆ ∷ [])     -- endo on ⋆
  t : Gen (• ∷ [])     (• ∷ [])     -- endo on •

--------------------------------------------------------------------------------
-- Bring the solver components into scope at this signature.
--------------------------------------------------------------------------------
open Untyped {Ty} Gen
open Reflect {Ty} Gen
open Normalize {Ty} Gen
open FreeMonoidalHelper Mon Ty using (ObjTerm; unit; _⊗₀_; Var)
open FreeMonoidalHelper.Mor Mon Ty mor
open ≈R

-- The discharged box-leaf right-unitor coherence: `reflect-sound` takes a
-- `BoxSound`, and `boxSound : BoxSound` is the proven witness in `SolverReflect`.
bs : BoxSound
bs = boxSound

--------------------------------------------------------------------------------
-- 2. REFLECT + SOUNDNESS TESTS.
--
-- For each `WTerm`, `reflect-sound bs t : coeCod' (out-reflect t) ⟦ reflect t ⟧
-- ≈Term embed t` — the reflected diagram, interpreted and codomain-coerced,
-- equals the term's embedding.  We exhibit each witness (the typechecker
-- machine-checks the `≈Term`).  The `_⊗ʷ_` cases put boxes at non-trivial
-- offsets via the merge/split wire-grouping bridge.
--------------------------------------------------------------------------------

-- (a) a single multiply box  μ : ⋆⋆ → ⋆
tμ : WTerm (⋆ ∷ ⋆ ∷ []) (⋆ ∷ [])
tμ = boxʷ μ

reflect-sound-μ : coeCod' (out-reflect tμ) ⟦ reflect tμ ⟧ ≈Term embed tμ
reflect-sound-μ = reflect-sound bs tμ

-- (b) a composite  δ ∘ μ : ⋆⋆ → ⋆ → ⋆⋆   (μ applied first, then δ)
tδμ : WTerm (⋆ ∷ ⋆ ∷ []) (⋆ ∷ ⋆ ∷ [])
tδμ = boxʷ δ ∘ʷ boxʷ μ

reflect-sound-δμ : coeCod' (out-reflect tδμ) ⟦ reflect tδμ ⟧ ≈Term embed tδμ
reflect-sound-δμ = reflect-sound bs tδμ

-- (c) a tensor  μ ⊗ η : ⋆⋆ → ⋆ ⊗ · → ⋆ ⋆   (boxes at non-trivial offsets)
tμ⊗η : WTerm (⋆ ∷ ⋆ ∷ []) (⋆ ∷ ⋆ ∷ [])
tμ⊗η = boxʷ μ ⊗ʷ boxʷ η

reflect-sound-μ⊗η : coeCod' (out-reflect tμ⊗η) ⟦ reflect tμ⊗η ⟧ ≈Term embed tμ⊗η
reflect-sound-μ⊗η = reflect-sound bs tμ⊗η

-- (d) a tensor with idʷ on the right, then s on the left:  (s ⊗ id) — endo box
--     left-tensored with an idle wire (box at offset 0, idle suffix).
ts⊗id : WTerm (⋆ ∷ ⋆ ∷ []) (⋆ ∷ ⋆ ∷ [])
ts⊗id = boxʷ s ⊗ʷ idʷ {⋆ ∷ []}

reflect-sound-s⊗id : coeCod' (out-reflect ts⊗id) ⟦ reflect ts⊗id ⟧ ≈Term embed ts⊗id
reflect-sound-s⊗id = reflect-sound bs ts⊗id

--------------------------------------------------------------------------------
-- 3. THE INTERCHANGE TEST (headline).
--
-- Two genuinely-independent endo boxes on DISJOINT wires: `s : ⋆ → ⋆` on wire 0
-- and `t : • → •` on wire 1 of the 2-wire context `⋆ ∷ • ∷ []`.  The two firing
-- orders commute in the free monoidal category — the genuine morphism-variable
-- interchange on a real signature, σ-free.
--
-- We exercise this in TWO ways:
--   (3a) directly via `TwoBoxSwap.two-box-swap` (an exhibited `≈Term`);
--   (3b) via the autonomous `SortD.normalizeD` engine on the concrete reflected
--        diagrams, machine-checking BOTH the reorder (by `refl` on the layer
--        list) and the soundness (an exhibited `≈Term`).
--------------------------------------------------------------------------------

-- (3a) the raw two-box interchange at the smallest frame (pre = mid = r = []),
--      with the LEFT box `s` (on wire ⋆) and the RIGHT box `t` (on wire •).
--      `two-box-swap : f-first ≈Term g-first`.
module IX = TwoBoxSwap [] [] [] s t

interchange-≈ : IX.f-first ≈Term IX.g-first
interchange-≈ = IX.two-box-swap

-- (3b) the SortD engine.  Out-of-order presentation: the RIGHT box (`t` on
--      wire •, offset ⋆∷[]) fires FIRST, then the LEFT box (`s` on wire ⋆,
--      offset []).  `leftFit?` recognises the out-of-order pair; `swapHeadD`
--      / `normalizeD` reorder it to canonical (lower-offset box `s` first).
--
-- This mirrors the `SolverNormalize.Litmus` SortD test, but with REAL endo
-- generators on a TWO-COLOUR context (s on ⋆, t on •) rather than two ℕ boxes.
open SortD _≟Ty_

-- the empty sorted tail at the swapped-output index  (⋆∷[]) ++ (•∷[]) = ⋆ ∷ • ∷ [].
ixTail : DiagU (⋆ ∷ • ∷ [])
ixTail = []_ (⋆ ∷ • ∷ [])

-- the recogniser FIRES on the out-of-order head data (t at offset ⋆∷[], s at
-- offset []): left box fy = s (dom/cod ⋆∷[]), right box fx = t (dom/cod •∷[]).
-- The fit's offset equations:  px ≡ ay = ⋆∷[], sx ≡ [], py ≡ [], sy ≡ bx = •∷[].
ixLeftFit? : leftFit? (⋆ ∷ []) [] [] (• ∷ []) t s
           ≡ just (leftFit [] [] [] refl refl refl refl)
ixLeftFit? = refl

-- it conservatively REJECTS an in-order / non-fitting pair (offsets don't split).
ixLeftFit?-no : leftFit? [] [] [] [] s t ≡ nothing
ixLeftFit?-no = refl

ixFit : LeftFit (⋆ ∷ []) [] [] (• ∷ []) t s
ixFit = leftFit [] [] [] refl refl refl refl

-- `normalizeD` with positive fuel REORDERS: result fires `s` (the lower-offset
-- box) FIRST, then `t` — machine-checked by `refl` on the underlying layers.
ixNormReorders : fromDiagU-ls (normalizeD 4 ixFit ixTail)
               ≡ mk-pad [] (• ∷ []) s
               ∷ mk-pad (⋆ ∷ []) [] t ∷ []
ixNormReorders = refl

-- and the INPUT (fuel 0 / pre-sort) is `t`-first — confirming it was out of order.
ixNormInput : fromDiagU-ls (normalizeD 0 ixFit ixTail)
            ≡ mk-pad (⋆ ∷ []) [] t
            ∷ mk-pad [] (• ∷ []) s ∷ []
ixNormInput = refl

-- the per-swap soundness cast is the identity here (P = mid = s = []).
ixNormCastId : proj₁ (normalizeD-sound 4 ixFit ixTail) ≡ refl
ixNormCastId = refl

-- THE GENUINE INTERCHANGE SOUNDNESS via the SortD engine: the out-of-order
-- input (t-first) and the reordered output (s-first) have EQUAL interpretations.
ixNormSound : id ∘ ⟦ dInput ixFit ixTail ⟧
            ≈Term ⟦ normalizeD 4 ixFit ixTail ⟧
ixNormSound = proj₂ (normalizeD-sound 4 ixFit ixTail)

--------------------------------------------------------------------------------
-- 4. A small end-to-end `decide?` harness.
--
-- `decide? f g` reflects both flat terms, decides NF equality of the reflected
-- diagrams (`_≟DiagU_`), and on a positive decision returns a proof
-- `embed f ≈Term embed g`, glued from `reflect-sound` on each end and the NF
-- equality in the middle.  This is the inline version of the not-yet-packaged
-- `solveMor` routing (`SolverCompare.Assembly.solveMor?`), specialised to the
-- *reflect-only* normal form (no swap normalization) — exactly enough for the
-- structural positive cases and all negative cases below.
--------------------------------------------------------------------------------
open SolverCompare _≟Ty_ Gen using () renaming (Gen to GenΣ)

-- decidable equality on the generator triple `(a , b , g) : Σ … Gen a b`,
-- needed by `SolverCompare.Decide`.  We decide the boundary lists, then the
-- generator constructor; a `yes` recovers both list-equalities and the box.
_≟Gen_ : DecidableEquality GenΣ
(_ , _ , μ) ≟Gen (_ , _ , μ) = yes refl
(_ , _ , η) ≟Gen (_ , _ , η) = yes refl
(_ , _ , δ) ≟Gen (_ , _ , δ) = yes refl
(_ , _ , ε) ≟Gen (_ , _ , ε) = yes refl
(_ , _ , s) ≟Gen (_ , _ , s) = yes refl
(_ , _ , t) ≟Gen (_ , _ , t) = yes refl
(_ , _ , μ) ≟Gen (_ , _ , η) = no λ ()
(_ , _ , μ) ≟Gen (_ , _ , δ) = no λ ()
(_ , _ , μ) ≟Gen (_ , _ , ε) = no λ ()
(_ , _ , μ) ≟Gen (_ , _ , s) = no λ ()
(_ , _ , μ) ≟Gen (_ , _ , t) = no λ ()
(_ , _ , η) ≟Gen (_ , _ , μ) = no λ ()
(_ , _ , η) ≟Gen (_ , _ , δ) = no λ ()
(_ , _ , η) ≟Gen (_ , _ , ε) = no λ ()
(_ , _ , η) ≟Gen (_ , _ , s) = no λ ()
(_ , _ , η) ≟Gen (_ , _ , t) = no λ ()
(_ , _ , δ) ≟Gen (_ , _ , μ) = no λ ()
(_ , _ , δ) ≟Gen (_ , _ , η) = no λ ()
(_ , _ , δ) ≟Gen (_ , _ , ε) = no λ ()
(_ , _ , δ) ≟Gen (_ , _ , s) = no λ ()
(_ , _ , δ) ≟Gen (_ , _ , t) = no λ ()
(_ , _ , ε) ≟Gen (_ , _ , μ) = no λ ()
(_ , _ , ε) ≟Gen (_ , _ , η) = no λ ()
(_ , _ , ε) ≟Gen (_ , _ , δ) = no λ ()
(_ , _ , ε) ≟Gen (_ , _ , s) = no λ ()
(_ , _ , ε) ≟Gen (_ , _ , t) = no λ ()
(_ , _ , s) ≟Gen (_ , _ , μ) = no λ ()
(_ , _ , s) ≟Gen (_ , _ , η) = no λ ()
(_ , _ , s) ≟Gen (_ , _ , δ) = no λ ()
(_ , _ , s) ≟Gen (_ , _ , ε) = no λ ()
(_ , _ , s) ≟Gen (_ , _ , t) = no λ ()
(_ , _ , t) ≟Gen (_ , _ , μ) = no λ ()
(_ , _ , t) ≟Gen (_ , _ , η) = no λ ()
(_ , _ , t) ≟Gen (_ , _ , δ) = no λ ()
(_ , _ , t) ≟Gen (_ , _ , ε) = no λ ()
(_ , _ , t) ≟Gen (_ , _ , s) = no λ ()

open SolverCompare.Decide _≟Ty_ Gen _≟Gen_
  using (_≈NF_; _≟DiagU_; ≈NF⇒≡)

-- the decide harness: reflect both sides, decide NF equality of the reflected
-- diagrams, and on a hit chain reflect-sound · (≈Term from ≡) · reflect-sound.
decide? : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
decide? f g with reflect f ≟DiagU reflect g
... | no  _  = nothing
... | yes eq = just (chain eq)
  where
    -- the two reflected diagrams are propositionally equal (same width), so
    -- their interpretations (codomain-coerced) coincide.
    chain : reflect f ≈NF reflect g → embed f ≈Term embed g
    chain eq = begin
      embed f
        ≈⟨ reflect-sound bs f ⟨
      coeCod' (out-reflect f) ⟦ reflect f ⟧
        ≈⟨ eq-≈Term (≈NF⇒≡ eq) (out-reflect f) (out-reflect g) ⟩
      coeCod' (out-reflect g) ⟦ reflect g ⟧
        ≈⟨ reflect-sound bs g ⟩
      embed g ∎
      where
        -- equal diagrams (same input width) have ≈Term-equal coerced
        -- interpretations: matching `refl` reduces both `coeCod'` to the same
        -- value once the two codomain witnesses are unified (UIP, by `refl`).
        eq-≈Term : ∀ {n p} {d d' : DiagU n}
                     (e : d ≡ d') (q₁ : out d ≡ p) (q₂ : out d' ≡ p)
                 → coeCod' q₁ ⟦ d ⟧ ≈Term coeCod' q₂ ⟦ d' ⟧
        eq-≈Term refl refl refl = ≈-Term-refl

--------------------------------------------------------------------------------
-- 4'. THE decide? OUTCOMES (machine-checked).
--------------------------------------------------------------------------------

-- POSITIVE structural case: `id ∘ μ` reflects to the same diagram as `μ`
-- (the `id` contributes the empty diagram, absorbed by `∘ᵈ`).  decide? = just,
-- machine-checked by `Is-just`; the exhibited `≈Term` witness is extracted by
-- `to-witness`.
pos-is-just : Is-just (decide? (idʷ ∘ʷ boxʷ μ) (boxʷ μ))
pos-is-just = just _

pos-witness : embed (idʷ ∘ʷ boxʷ μ) ≈Term embed (boxʷ μ)
pos-witness = to-witness pos-is-just

-- the symmetric `μ ∘ id` vs `μ` positive case as well.
pos₂-is-just : Is-just (decide? (boxʷ μ ∘ʷ idʷ) (boxʷ μ))
pos₂-is-just = just _

-- NEGATIVE case: `μ` (multiply, ⋆⋆→⋆) vs `s ∘ μ` reflect to DIFFERENT diagrams
-- (extra `s` layer), so decide? = nothing — machine-checked by `refl`.
negᵢ : decide? (boxʷ μ) (boxʷ s ∘ʷ boxʷ μ) ≡ nothing
negᵢ = refl

-- a second NEGATIVE case at the SAME boundary ⋆ → ⋆⋆: a bare `δ` vs `δ`
-- prefixed by an `s` (different first-applied box) — decide? = nothing.
negᵢ₂ : decide? (boxʷ δ) (boxʷ δ ∘ʷ boxʷ s) ≡ nothing
negᵢ₂ = refl

--------------------------------------------------------------------------------
-- 5. TRANSPORT TEST.
--
-- Instantiate `SolveMorSpike.SolveMor` at the concrete target monoidal category
-- `Sets` (cartesian product as ⊗), with a NON-TRIVIAL generator interpretation
-- `⟦Mor⟧` sending each `Gen` to an actual function between the interpreted wire
-- objects.  The two-box interchange (s on wire ⋆, t on wire •) then transports
-- to a genuine equation `C [ ⟦ f-first ⟧₁ ≈ ⟦ g-first ⟧₁ ]` in `Sets`.
--
-- Object interpretation:  ⋆ ↦ ℕ ,  • ↦ ℕ.  Then a wire object `wires (⋆ ∷ [])`
-- interprets as `ℕ × ⊤`, and each generator's `⟦Mor⟧` is a concrete function.
--------------------------------------------------------------------------------
open import Level using (Level) renaming (zero to ℓ0; suc to ℓsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_×_)
open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Instance.Sets using (module Product)

open Product {ℓ0} using (Sets-Monoidal)
open import Categories.Category.Instance.Sets using (Sets)

-- the target monoidal category: Sets at level 0, with × as ⊗.
SetsMon : MonoidalCategory (ℓsuc ℓ0) ℓ0 ℓ0
SetsMon = record { U = Sets ℓ0 ; monoidal = Sets-Monoidal }

-- object interpretation of the two colours.
⟦_⟧obj₀ : Ty → Set
⟦ ⋆ ⟧obj₀ = ℕ
⟦ • ⟧obj₀ = ℕ

open SolveMor {ℓsuc ℓ0} {ℓ0} {ℓ0} {Ty} Gen SetsMon ⟦_⟧obj₀

-- the wire objects, as concrete Set values (× of ℕ's with a trailing ⊤).
-- ⟦ wires (⋆∷[]) ⟧obj = ℕ × ⊤ ;  ⟦ wires (⋆ ∷ ⋆ ∷ []) ⟧obj = ℕ × (ℕ × ⊤) ; etc.

-- the NON-TRIVIAL generator interpretation: each box is an actual function.
⟦Gen⟧ : ∀ {a b} → Gen a b → SetsMon .MonoidalCategory.U
                            [ ⟦ wires a ⟧obj , ⟦ wires b ⟧obj ]
⟦Gen⟧ μ (x , (y , tt)) = (x + y) , tt          -- multiply = addition
⟦Gen⟧ η tt             = 0 , tt                  -- unit = 0
⟦Gen⟧ δ (x , tt)       = x , (x , tt)            -- comultiply = copy
⟦Gen⟧ ε (x , tt)       = tt                      -- counit = discard
⟦Gen⟧ s (x , tt)       = suc x , tt              -- endo s = successor
⟦Gen⟧ t (x , tt)       = (x * 2) , tt            -- endo t = double

open WithMor ⟦Gen⟧

-- the two-box interchange (s on wire ⋆, t on wire •), transported to Sets:
-- a genuine equation between the two interpreted firing orders.
transport-interchange : SetsMon .MonoidalCategory.U
                          [ ⟦ TwoBoxSwap.f-first [] [] [] s t ⟧₁
                          ≈ ⟦ TwoBoxSwap.g-first [] [] [] s t ⟧₁ ]
transport-interchange = interchange-target s t
