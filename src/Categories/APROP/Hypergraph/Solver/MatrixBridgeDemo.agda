{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- FEASIBILITY SPIKE — NON-IDENTITY VALIDATION of the *generator-code
-- augmented* canonical-labelling `align`.
--
-- The previous spike validated `align` on an `f ⊗ g` shape whose two edges
-- read DISTINCT input wires; there the structural rank-multiset signature
-- already canonicalised the two graphs.  This file validates the GENERALISED
-- tie-break (`MatrixBridge.§2`): the signature now folds a per-edge
-- GENERATOR CODE ahead of the structural rank-multiset, so `align` is correct
-- for the one structurally-tying case the old version could NOT order — two
-- distinct INPUT-FREE generators (e.g. two states `u v : unit → X`).
--
-- §B–§F build a minimal monogamous acyclic hypergraph `H` with TWO
-- input-free edges of DIFFERENT generators (`u : unit → a₀`, `v : unit → a₁`)
-- and a relabelled copy `J` obtained by a KNOWN non-identity permutation:
--
--     π : vertices   0↔1      (swap the two outputs)
--     τ : edges      0↔1      (swap u and v)
--
-- §E first DEMONSTRATES THE STRUCTURAL TIE: the structural-only signatures of
-- the two edges are EQUAL (both `[]`) by `refl` — so structure alone cannot
-- order them.  §F then shows the code-augmented `align H J` recovers the
-- CORRECT non-identity bijection `(π , τ)`, and discharges the `_≅ᴴ_`
-- incidence conditions (`vlab`, `ein`/`eout`, `dom`/`cod`) by `refl` on the
-- concrete instance — NOT through `matIso→hgIso`/soundness (whose postulated
-- fields would mask a wrong `align`).
--
-- §G threads the original σ-naturality `⟪_⟫`-translation through the new
-- `align` (with a faithful `morCode`) to show the end-to-end data flow still
-- assembles a `≅ᴴ` (its preservation fields remain postulated).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.MatrixBridgeDemo where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Categories.APROP using (APROPSignature; module APROP)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

--------------------------------------------------------------------------------
-- §A.  A self-contained signature with TWO input-free generators of
-- DIFFERENT types.  Atoms  X = Fin 2  (a₀, a₁).
--
--   u : unit → a₀     v : unit → a₁
--
-- Both are input-free (`flatten unit = []`), so their structural edge
-- signature is `[]` — they TIE on structure.  The generator code separates
-- them: `morCode u = 0`, `morCode v = 1`.

X₂ : Set
X₂ = Fin 2

open FreeMonoidalHelper Symm X₂ using (ObjTerm; unit; _⊗₀_; Var)

private
  b₀ b₁ : ObjTerm
  b₀ = Var zero
  b₁ = Var (suc zero)

data InMor : ObjTerm → ObjTerm → Set where
  u : InMor unit b₀
  v : InMor unit b₁

_≟-InMor_ : ∀ {A B} → DecidableEquality (InMor A B)
u ≟-InMor u = yes refl
v ≟-InMor v = yes refl

inSig : APROPSignature
inSig = record { X = X₂ ; mor = InMor }

inSigDec : APROPSignatureDec
inSigDec = record
  { sig     = inSig
  ; _≟X_    = _≟F2_
  ; _≟-mor_ = _≟-InMor_
  }
  where open import Data.Fin.Properties using () renaming (_≟_ to _≟F2_)

open import Categories.APROP.Hypergraph.FromAPROP inSig
  using (FlatGen; flat; flatten)
open import Categories.APROP.Hypergraph.Solver.MatrixBridge inSigDec
  using (hg→mat; align; matIso→hgIso; Alignment)
import Categories.APROP.Hypergraph.Solver.MatrixBridge inSigDec as MB
open import Categories.APROP.Hypergraph.Solver.Verify inSigDec using (view)
open import Categories.APROP.Hypergraph.Solver.Verify inSigDec
  using (FlatView)

-- Generator code: distinct generators ↦ distinct ℕ.
morCode : ∀ {A B} → InMor A B → ℕ
morCode u = 0
morCode v = 1

-- Per-edge code, read off the edge's `FlatGen` label via the `FlatView`.
-- (Mirrors how `Verify.agda` extracts the underlying generator.)
ecodeOf : (G : Hypergraph FlatGen) → Fin (Hypergraph.nE G) → ℕ
ecodeOf G e = morCode (FlatView.f (view (Hypergraph.elab G e)))

--------------------------------------------------------------------------------
-- §B.  H — the "reference" hypergraph (two input-free generators u, v).
--
--   vertices : 0:a₀ (out of u)   1:a₁ (out of v)
--   edge 0   : u : unit → a₀   ein []   eout [0]
--   edge 1   : v : unit → a₁   ein []   eout [1]
--   dom []   cod [0,1]

H : Hypergraph FlatGen
H = record
  { nV   = 2
  ; vlab = vlabH
  ; nE   = 2
  ; ein  = einH
  ; eout = eoutH
  ; elab = elabH
  ; dom  = []
  ; cod  = z0 ∷ z1 ∷ []
  }
  where
    z0 z1 : Fin 2
    z0 = zero
    z1 = suc zero

    vlabH : Fin 2 → Fin 2
    vlabH zero       = zero       -- a₀
    vlabH (suc _)    = suc zero   -- a₁

    einH : Fin 2 → List (Fin 2)
    einH _ = []                   -- both edges are input-free

    eoutH : Fin 2 → List (Fin 2)
    eoutH zero    = z0 ∷ []       -- u writes vertex 0
    eoutH (suc _) = z1 ∷ []       -- v writes vertex 1

    elabH : (e : Fin 2)
          → FlatGen (map vlabH (einH e)) (map vlabH (eoutH e))
    elabH zero    = flat u        -- FlatGen [] [zero]
    elabH (suc _) = flat v        -- FlatGen [] [suc zero]

--------------------------------------------------------------------------------
-- §C.  J — H relabelled by  π (vertices) and τ (edges).
--
--   π = 0↦1, 1↦0      τ = 0↦1, 1↦0
--
--     J.cod = map π [0,1] = [1,0]
--     J edge 0 = H edge 1 (v)  ein [] eout [0]
--     J edge 1 = H edge 0 (u)  ein [] eout [1]
--     J.vlab chosen so  J.vlab ∘ π ≗ H.vlab  (vertex 0 of J is v's output a₁).

J : Hypergraph FlatGen
J = record
  { nV   = 2
  ; vlab = vlabJ
  ; nE   = 2
  ; ein  = einJ
  ; eout = eoutJ
  ; elab = elabJ
  ; dom  = []
  ; cod  = w1 ∷ w0 ∷ []          -- = map π [0,1]
  }
  where
    w0 w1 : Fin 2
    w0 = zero
    w1 = suc zero

    vlabJ : Fin 2 → Fin 2
    vlabJ zero       = suc zero   -- J vertex 0 ← v output (a₁)
    vlabJ (suc _)    = zero       -- J vertex 1 ← u output (a₀)

    einJ : Fin 2 → List (Fin 2)
    einJ _ = []

    eoutJ : Fin 2 → List (Fin 2)
    eoutJ zero    = w0 ∷ []       -- J edge 0 = v, writes vertex 0
    eoutJ (suc _) = w1 ∷ []       -- J edge 1 = u, writes vertex 1

    elabJ : (e : Fin 2)
          → FlatGen (map vlabJ (einJ e)) (map vlabJ (eoutJ e))
    elabJ zero    = flat v        -- FlatGen [] [suc zero]
    elabJ (suc _) = flat u        -- FlatGen [] [zero]

--------------------------------------------------------------------------------
-- §D.  The alignment, computed by the REAL code-augmented `align`.
--
-- The codes are extracted from H/J via `ecodeOf` (the generator behind each
-- edge).  Defaults (last four args) are never demanded — every rank is in
-- range — but must be supplied at the target types.

theAlignment : Alignment H J
theAlignment = align H J (ecodeOf H) (ecodeOf J) zero zero zero zero

private
  module H = Hypergraph H
  module J = Hypergraph J
  open Alignment theAlignment

--------------------------------------------------------------------------------
-- §E.  THE STRUCTURAL TIE (the whole point).
--
-- With the canonical vertex order seeded at `H.dom = []`, the STRUCTURAL-ONLY
-- signature of each edge is `sortℕ (map (posIn …) (ein e))`.  Since both
-- edges are input-free (`ein = []`), both structural signatures are `[]` —
-- EQUAL — so structure alone cannot order edge 0 vs edge 1.

private
  -- The structural part of the edge signature: `Canon.edgeSig` minus the code
  -- is exactly the second component.  We compute it at the seed order `H.dom`.
  open import Data.Product using (proj₂)

  structSig : Fin 2 → List ℕ
  structSig e = proj₂ (MB.Canon.edgeSig H (ecodeOf H) H.dom e)

-- Edge 0 and edge 1 of H have the SAME structural signature (both `[]`):
-- structure alone TIES them.  (The OLD `align`, keyed on this alone, could
-- not have ordered them between two differently-laid-out iso graphs.)
struct-tie : structSig zero ≡ structSig (suc zero)
struct-tie = refl

struct-both-empty : structSig zero ≡ [] × structSig (suc zero) ≡ []
struct-both-empty = refl , refl

--------------------------------------------------------------------------------
-- §F.  WITNESS + VALIDATION: the code-augmented `align` recovers `(π , τ)`,
-- and the `_≅ᴴ_` incidence conditions hold by `refl` on the concrete graphs.

-- φ = π  (genuinely NON-identity: φ 0 = 1, φ 1 = 0)
φ-is-π : φ zero ≡ suc zero × φ (suc zero) ≡ zero
φ-is-π = refl , refl

-- ψ = τ  (the genuine edge SWAP: ψ 0 = 1, ψ 1 = 0) — resolved by the code.
ψ-is-τ : ψ zero ≡ suc zero × ψ (suc zero) ≡ zero
ψ-is-τ = refl , refl

-- Vertex labels agree:  vlab J (φ v) ≡ vlab H v  for every vertex.
check-vlab : (vtx : Fin 2) → J.vlab (φ vtx) ≡ H.vlab vtx
check-vlab zero       = refl
check-vlab (suc zero) = refl

-- Edge inputs:  map φ (ein H e) ≡ ein J (ψ e)  (both empty, but checked).
check-ein : (e : Fin 2) → map φ (H.ein e) ≡ J.ein (ψ e)
check-ein zero       = refl
check-ein (suc zero) = refl

-- Edge outputs:  map φ (eout H e) ≡ eout J (ψ e).
check-eout : (e : Fin 2) → map φ (H.eout e) ≡ J.eout (ψ e)
check-eout zero       = refl
check-eout (suc zero) = refl

-- Boundary:  map φ (cod H) ≡ cod J  (dom is empty on both).
check-dom : map φ H.dom ≡ J.dom
check-dom = refl

check-cod : map φ H.cod ≡ J.cod
check-cod = refl

--------------------------------------------------------------------------------
-- §F'.  TEETH.  The recovered `ψ` is the SWAP, not the identity.  Asserting
-- the identity would be REJECTED by Agda; we record the genuine value here so
-- the reader can see the discriminating fact (a wrong claim, e.g.
-- `ψ-wrong : ψ zero ≡ zero ; ψ-wrong = refl`, fails to typecheck).

ψ-not-id : ψ zero ≡ suc zero
ψ-not-id = refl

--------------------------------------------------------------------------------
-- §G.  END-TO-END DATA FLOW on the original σ-naturality `⟪_⟫`-translation,
-- threaded through the new code-augmented `align`.
--
-- Uses the existing three-generator test signature (`f g h`, none input-free,
-- so the structural part already separates them; the code is still supplied
-- faithfully).  Its preservation fields are postulated, as documented; the
-- validating content is §E/§F above.

module σ-section where
  open import Categories.APROP.Hypergraph.Solver.Tests
    using (mySig; mySigDec; MyMor)
  open MyMor

  open import Categories.APROP.Hypergraph.FromAPROP mySig
    using () renaming (FlatGen to FlatGenσ)
  open import Categories.APROP.Hypergraph.Solver.Verify mySigDec
    using () renaming (view to viewσ; FlatView to FlatViewσ)
  open import Categories.APROP.Hypergraph.Solver.MatrixBridge mySigDec
    using () renaming (hg→mat to hg→matσ; align to alignσ-fn;
                       matIso→hgIso to matIso→hgIsoσ; Alignment to Alignmentσ)
  open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
  open import Categories.APROP.Hypergraph.SoundnessFullWired mySigDec
    using (soundness-full-wired)
  module M = APROP mySig
  open M using (HomTerm; _≈Term_; Agen; id; _∘_; _⊗₁_; σ)

  -- Faithful generator code for the three-generator signature.
  morCodeσ : ∀ {A B} → MyMor A B → ℕ
  morCodeσ f = 0
  morCodeσ g = 1
  morCodeσ h = 2

  ecodeOfσ : (G : Hypergraph FlatGenσ) → Fin (Hypergraph.nE G) → ℕ
  ecodeOfσ G e = morCodeσ (FlatViewσ.f (viewσ (Hypergraph.elab G e)))

  private
    aₓ aᵧ a_z : M.ObjTerm
    aₓ = M.Var zero
    aᵧ = M.Var (suc zero)
    a_z = M.Var (suc (suc zero))

    LHS RHS : HomTerm (aₓ M.⊗₀ aᵧ) (a_z M.⊗₀ aᵧ)
    LHS = σ {aᵧ} {a_z} ∘ (Agen f ⊗₁ Agen g)
    RHS = (Agen g ⊗₁ Agen f) ∘ σ {aₓ} {aᵧ}

    Hσ Jσ : Hypergraph FlatGenσ
    Hσ = ⟪ LHS ⟫
    Jσ = ⟪ RHS ⟫

    -- The matrix encodings genuinely compute.
    matHσ = hg→matσ Hσ
    matJσ = hg→matσ Jσ

    alignσ : Alignmentσ Hσ Jσ
    alignσ = alignσ-fn Hσ Jσ (ecodeOfσ Hσ) (ecodeOfσ Jσ) zero zero zero zero

    isoσ : Hσ ≅ᴴ Jσ
    isoσ = matIso→hgIsoσ alignσ

    σ-naturality : LHS ≈Term RHS
    σ-naturality = soundness-full-wired isoσ
