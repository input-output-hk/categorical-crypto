{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- FEASIBILITY SPIKE — NON-IDENTITY VALIDATION of the canonical-labelling
-- `align`.
--
-- The point of this demo is to *prove computationally* that the real `align`
-- (canonical DAG labelling, no search — see `MatrixBridge.§2`) finds the
-- CORRECT bijection on a case where the right answer is a genuine
-- NON-IDENTITY permutation.
--
-- We hand-build a small monogamous acyclic hypergraph `H` (shape `f ⊗ g`:
-- two independent generators on disjoint wires) and a relabelled copy `J`
-- obtained by applying a KNOWN non-identity permutation:
--
--     π : vertices   0↔1 , 2↔3   (swap the two inputs, swap the two outputs)
--     τ : edges      0↔1          (swap f and g)
--
-- `align H J` is asked to recover `(π , τ)` purely from the canonical
-- labellings.  We then DISCHARGE the `_≅ᴴ_` incidence conditions
-- CONCRETELY by `refl` — NOT through `matIso→hgIso`/soundness (whose
-- postulated fields would mask a wrong `align`).  Each `refl` below is a
-- machine-checked witness that `align` produced the right bijection.
--
-- A second section threads the original σ-naturality `⟪_⟫`-translation
-- pipeline through the new `align` to show the end-to-end data flow still
-- assembles a `≅ᴴ` (its preservation fields remain postulated).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.MatrixBridgeDemo where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.APROP using (module APROP)
open import Categories.FreeMonoidal

-- Reuse the concrete signature + generators from the existing test suite.
open import Categories.APROP.Hypergraph.Solver.Tests
  using (mySig; mySigDec)

open APROP mySig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP mySig using (FlatGen; flatten; flat)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Solver.MatrixBridge mySigDec
  using (hg→mat; align; matIso→hgIso; Alignment)

open import Categories.APROP.Hypergraph.Solver.Tests using (MyMor)
open MyMor

--------------------------------------------------------------------------------
-- §A.  Atom codes (X = Fin 3).  a₀ = code 0, a₁ = code 1, a₂ = code 2.

private
  c0 c1 c2 : Fin 3
  c0 = zero
  c1 = suc zero
  c2 = suc (suc zero)

  a₀ a₁ a₂ : ObjTerm
  a₀ = Var c0
  a₁ = Var c1
  a₂ = Var c2

--------------------------------------------------------------------------------
-- §B.  H — the "reference" hypergraph (shape  f ⊗ g).
--
--   vertices : 0:a₀ (in)   1:a₁ (in)   2:a₁ (out of f)   3:a₂ (out of g)
--   edge 0   : f : a₀ → a₁   ein [0]  eout [2]
--   edge 1   : g : a₁ → a₂   ein [1]  eout [3]
--   dom [0,1]   cod [2,3]
--
-- Vertex labels are chosen so that  map vlab (ein/eout e)  reduces *on the
-- nose* to  flatten (src/tgt) , so each `elab` is a bare `flat f`/`flat g`.

H : Hypergraph FlatGen
H = record
  { nV   = 4
  ; vlab = vlabH
  ; nE   = 2
  ; ein  = einH
  ; eout = eoutH
  ; elab = elabH
  ; dom  = v0 ∷ v1 ∷ []
  ; cod  = v2 ∷ v3 ∷ []
  }
  where
    v0 v1 v2 v3 : Fin 4
    v0 = zero
    v1 = suc zero
    v2 = suc (suc zero)
    v3 = suc (suc (suc zero))

    vlabH : Fin 4 → Fin 3
    vlabH zero                      = c0   -- a₀
    vlabH (suc zero)                = c1   -- a₁
    vlabH (suc (suc zero))          = c1   -- a₁
    vlabH (suc (suc (suc _)))       = c2   -- a₂

    einH : Fin 2 → List (Fin 4)
    einH zero       = v0 ∷ []      -- f reads vertex 0
    einH (suc _)    = v1 ∷ []      -- g reads vertex 1

    eoutH : Fin 2 → List (Fin 4)
    eoutH zero      = v2 ∷ []      -- f writes vertex 2
    eoutH (suc _)   = v3 ∷ []      -- g writes vertex 3

    elabH : (e : Fin 2)
          → FlatGen (map vlabH (einH e)) (map vlabH (eoutH e))
    elabH zero    = flat f         -- FlatGen [c0] [c1]
    elabH (suc _) = flat g         -- FlatGen [c1] [c2]

--------------------------------------------------------------------------------
-- §C.  J — H relabelled by  π (vertices) and τ (edges).
--
--   π = 0↦1, 1↦0, 2↦3, 3↦2      τ = 0↦1, 1↦0
--
--   So J's data is H's data pushed forward along π/τ:
--     J.dom  = map π [0,1] = [1,0]      J.cod = map π [2,3] = [3,2]
--     J edge 0  = H edge 1 (g)  ein [0] eout [2]
--     J edge 1  = H edge 0 (f)  ein [1] eout [3]
--     J.vlab    chosen so  J.vlab ∘ π ≗ H.vlab.

J : Hypergraph FlatGen
J = record
  { nV   = 4
  ; vlab = vlabJ
  ; nE   = 2
  ; ein  = einJ
  ; eout = eoutJ
  ; elab = elabJ
  ; dom  = w1 ∷ w0 ∷ []          -- = map π [0,1]
  ; cod  = w3 ∷ w2 ∷ []          -- = map π [2,3]
  }
  where
    w0 w1 w2 w3 : Fin 4
    w0 = zero
    w1 = suc zero
    w2 = suc (suc zero)
    w3 = suc (suc (suc zero))

    -- J.vlab : J.vlab(π v) = H.vlab v.  π: 0↦1,1↦0,2↦3,3↦2.
    vlabJ : Fin 4 → Fin 3
    vlabJ zero                = c1   -- vertex 1 of J  ← H vertex 0 (a₀)? no: see below
    vlabJ (suc zero)          = c0
    vlabJ (suc (suc zero))    = c2
    vlabJ (suc (suc (suc _))) = c1

    einJ : Fin 2 → List (Fin 4)
    einJ zero    = w0 ∷ []      -- J edge 0 = g, reads π(1)=0
    einJ (suc _) = w1 ∷ []      -- J edge 1 = f, reads π(0)=1

    eoutJ : Fin 2 → List (Fin 4)
    eoutJ zero    = w2 ∷ []     -- J edge 0 = g, writes π(3)=2
    eoutJ (suc _) = w3 ∷ []     -- J edge 1 = f, writes π(2)=3

    elabJ : (e : Fin 2)
          → FlatGen (map vlabJ (einJ e)) (map vlabJ (eoutJ e))
    elabJ zero    = flat g         -- FlatGen [c1] [c2]
    elabJ (suc _) = flat f         -- FlatGen [c0] [c1]

--------------------------------------------------------------------------------
-- §D.  The alignment, computed by the REAL canonical-labelling `align`.
--
-- Defaults (last four args) are never demanded — every rank is in range —
-- but must be supplied at the target types.

theAlignment : Alignment H J
theAlignment = align H J zero zero zero zero

private
  module H = Hypergraph H
  module J = Hypergraph J
  open Alignment theAlignment

--------------------------------------------------------------------------------
-- §E.  WITNESS: what `align` computed.  These `refl`s pin the recovered
-- permutation to the KNOWN non-identity answer  (π , τ).

-- φ = π  (genuinely NON-identity: φ 0 = 1, φ 1 = 0, …)
φ-is-π : φ zero ≡ suc zero
       × φ (suc zero) ≡ zero
       × φ (suc (suc zero)) ≡ suc (suc (suc zero))
       × φ (suc (suc (suc zero))) ≡ suc (suc zero)
φ-is-π = refl , refl , refl , refl

-- ψ = τ  (the genuine edge SWAP: ψ 0 = 1, ψ 1 = 0)
ψ-is-τ : ψ zero ≡ suc zero × ψ (suc zero) ≡ zero
ψ-is-τ = refl , refl

--------------------------------------------------------------------------------
-- §F.  VALIDATION — the postponed `_≅ᴴ_` incidence conditions, discharged
-- HERE by `refl` on the concrete instance.  Each holding by `refl` proves
-- that the computed `(φ , ψ)` is the correct hypergraph isomorphism.

-- Vertex labels agree:  vlab J (φ v) ≡ vlab H v  for every vertex.
check-vlab : (v : Fin 4) → J.vlab (φ v) ≡ H.vlab v
check-vlab zero                      = refl
check-vlab (suc zero)                = refl
check-vlab (suc (suc zero))          = refl
check-vlab (suc (suc (suc zero)))    = refl

-- Edge inputs:  map φ (ein H e) ≡ ein J (ψ e).
check-ein : (e : Fin 2) → map φ (H.ein e) ≡ J.ein (ψ e)
check-ein zero    = refl
check-ein (suc zero) = refl

-- Edge outputs:  map φ (eout H e) ≡ eout J (ψ e).
check-eout : (e : Fin 2) → map φ (H.eout e) ≡ J.eout (ψ e)
check-eout zero       = refl
check-eout (suc zero) = refl

-- Boundary:  map φ (dom H) ≡ dom J  and  map φ (cod H) ≡ cod J.
check-dom : map φ H.dom ≡ J.dom
check-dom = refl

check-cod : map φ H.cod ≡ J.cod
check-cod = refl

--------------------------------------------------------------------------------
-- §G.  END-TO-END DATA FLOW on the original σ-naturality `⟪_⟫`-translation.
--
-- This re-exercises the full pipeline ⟪_⟫ → hg→mat → align → matIso→hgIso →
-- soundness with the new canonical `align`.  (Its preservation fields are
-- postulated, as documented; the validating content is §E/§F above.)

open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.SoundnessFullWired mySigDec
  using (soundness-full-wired)

private
  LHS RHS : HomTerm (a₀ ⊗₀ a₁) (a₂ ⊗₀ a₁)
  LHS = σ {a₁} {a₂} ∘ (Agen f ⊗₁ Agen g)
  RHS = (Agen g ⊗₁ Agen f) ∘ σ {a₀} {a₁}

  Hσ Jσ : Hypergraph FlatGen
  Hσ = ⟪ LHS ⟫
  Jσ = ⟪ RHS ⟫

  -- The matrix encodings genuinely compute.
  matHσ = hg→mat Hσ
  matJσ = hg→mat Jσ

  -- Canonical alignment, then assemble the (postulated-preservation) iso,
  -- then soundness to a genuine free-SMC equation.
  alignσ : Alignment Hσ Jσ
  alignσ = align Hσ Jσ zero zero zero zero

  isoσ : Hσ ≅ᴴ Jσ
  isoσ = matIso→hgIso alignσ

  σ-naturality : LHS ≈Term RHS
  σ-naturality = soundness-full-wired isoσ
