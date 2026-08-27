{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The label alphabet (`FlatGen`, `flatten`, `flat`) and the smart
-- hypergraph constructors that the term translation is built from.  The
-- translation `⟪_⟫` itself and its boundary lemmas (`⟪⟫-domL`, `⟪⟫-codL`)
-- live downstream in `Model.Translation`.
--
-- The hypergraph is *un-indexed* — it does not carry its boundary
-- atom-lists in the type; boundary facts are separate propositional
-- lemmas at each constructor.
--
-- Smart constructors:
--   hEmpty      empty hypergraph
--   hVar x      single vertex (for `Var x`)
--   hId A       identity on a flattened object, recursive on A
--   hGen f      single edge for a user generator `mor A B`
--   hTensor     disjoint union, boundary `domL G ++ domL K` /
--                                          `codL G ++ codL K`
--   hSwap A B   braiding
--
-- Cospan composition lives in `PrunedCompose.hComposeP`.
--
-- The benefit of de-indexing: `subst₂ (Hypergraph FlatGen)` never shows
-- up; the ρ/α cases of `⟪_⟫` are plain `hId` calls, with the boundary
-- equations living in the boundary lemmas rather than the type.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Model.FromAPROP (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties as Fin
open import Data.List using (List; []; _∷_; _++_; length; map; lookup)
open import Data.List.Properties
open import Data.List.Properties.Ext using (map-∘-cong)
open import Data.Nat
open import Data.Sum using (inj₁; inj₂; [_,_]′)


--------------------------------------------------------------------------------
-- Flattening an ObjTerm into its list of atoms.

flatten : ObjTerm → List X
flatten unit = []
flatten (A ⊗₀ B) = flatten A ++ flatten B
flatten (Var x) = x ∷ []

-- Edges carry generators whose boundary is already a flat atom list.
--
-- Represented as a RECORD carrying its original `ObjTerm` boundaries plus
-- linking proofs `okA`/`okB`.  This is morally the data type
--
--   data FlatGen : List X → List X → Set where
--     flat : ∀ {A B} → mor A B → FlatGen (flatten A) (flatten B)
--
-- but the record form lets every `elab` construction site BUILD THE RECORD
-- DIRECTLY at its target boundaries (via `retype`, which folds the boundary
-- equality into the `okA`/`okB` field) INSTEAD of wrapping in `subst₂ FlatGen`.
-- The `view`/matching machinery then reads `f`/`A`/`B` by shallow record
-- projection, never forcing the (stacked, tower-deep) boundary equalities to
-- normalise to `refl`.  This kills the quadratic-in-tower-depth
-- `subst₂`-proof-normalisation blowup that the indexed-data form incurred at
-- each `hComposeP` level.
--
-- The boundary proofs are kept *relevant* so the soundness-side strictification
-- (`Strict.Soundness.J-flat`, `DecodeLean.Agen-edge-aux`) can coerce a generator's
-- `unflatten`-bridge onto the record's declared boundaries without needing
-- decidable equality on `X` (which most soundness modules lack).  They are
-- never *normalised* on the solver hot path (only carried as thunks), so the
-- perf win is unaffected.
record FlatGen (As Bs : List X) : Set where
  constructor flat-rec
  field
    {A B} : ObjTerm
    okA   : flatten A ≡ As
    okB   : flatten B ≡ Bs
    f     : mor A B

-- Smart constructor `flat g : FlatGen (flatten A) (flatten B)`.
flat : ∀ {A B} → mor A B → FlatGen (flatten A) (flatten B)
flat g = flat-rec refl refl g

-- Re-type a `FlatGen` along boundary equalities by REBUILDING the record
-- (composing the equalities into the `okA`/`okB` fields).  Behaves exactly
-- like `subst₂ FlatGen p q` (see `retype-≡`) but, crucially, produces a
-- *direct* `flat-rec` — so projecting `A`/`B`/`f` via the `view` machinery
-- never forces the boundary proofs to normalise.  Used at every `elab`
-- construction site (`hTensor`, `hComposeP`, `hGen`) to avoid the quadratic
-- stacked-`subst₂` proof-normalisation cost.
retype : ∀ {As Bs As' Bs'} → As ≡ As' → Bs ≡ Bs'
       → FlatGen As Bs → FlatGen As' Bs'
retype p q (flat-rec oa ob g) = flat-rec (trans oa p) (trans ob q) g

-- `retype` agrees with `subst₂ FlatGen p q` propositionally, so the downstream
-- `subst₂ FlatGen`-shaped reasoning lemmas (`elab-c-inj₁`/`₂`) still apply.
retype-≡ : ∀ {As Bs As' Bs'} (p : As ≡ As') (q : Bs ≡ Bs') (v : FlatGen As Bs)
         → retype p q v ≡ subst₂ FlatGen p q v
retype-≡ refl refl (flat-rec oa ob g) =
  cong₂ (λ a b → flat-rec a b g) (trans-reflʳ oa) (trans-reflʳ ob)

--------------------------------------------------------------------------------
-- Fin-range helpers.

range : (n : ℕ) → List (Fin n)
range zero = []
range (suc n) = zero ∷ map suc (range n)

map-lookup-range : (xs : List X) → map (lookup xs) (range (length xs)) ≡ xs
map-lookup-range [] = refl
map-lookup-range (x ∷ xs) =
  cong (x ∷_)
    (trans (sym (map-∘ (range (length xs))))
           (map-lookup-range xs))

--------------------------------------------------------------------------------
-- Generic helper: mapping through a relabelling `f` preserves a
-- pointwise-stated vertex labeling (instantiated at `_↑ˡ_`, `_↑ʳ_`, `remapP`).

map-via : ∀ {m n : ℕ} {v : Fin m → X} {w : Fin n → X} {f : Fin m → Fin n}
        → (∀ i → w (f i) ≡ v i)
        → (xs : List (Fin m))
        → map v xs ≡ map w (map f xs)
map-via p xs = sym (map-∘-cong p xs)

--------------------------------------------------------------------------------
-- Empty hypergraph: no vertices, no edges, empty boundary.

hEmpty : Hypergraph FlatGen
hEmpty = record
  { nV = 0; vlab = λ (); nE = 0
  ; ein = λ (); eout = λ (); elab = λ ()
  ; dom = []; cod = []
  }

-- Single vertex hypergraph labeled `x`.
hVar : (x : X) → Hypergraph FlatGen
hVar x = record
  { nV = 1; vlab = λ _ → x; nE = 0
  ; ein = λ (); eout = λ (); elab = λ ()
  ; dom = zero ∷ []; cod = zero ∷ []
  }

--------------------------------------------------------------------------------
-- The coproduct edge structure, shared by the two binary composites: the
-- edge index is dispatched by `splitAt G.nE`, G-edges are routed through a
-- left vertex embedding and K-edges through a right one.  `hTensor-impl`
-- instantiates it at `(injL , injR)`, `PrunedCompose.hComposeP-impl` at
-- `(injL , remapP)` — the two differ ONLY in the right vertex map and its
-- label bridge, which are the parameters here.  Both instantiate with
-- `open … public`, so every downstream qualified name
-- (`hTensor-impl.ein-c-inj₁-red`, `hComposeP-impl.elab-c-inj₂`, …) keeps its
-- spelling and, since the label bridges are passed partially applied, its
-- statement.

module CoproductEdges
  (G K : Hypergraph FlatGen)
  (nVc : ℕ) (vlab-c : Fin nVc → X)
  (ιL : Fin (Hypergraph.nV G) → Fin nVc)
  (ιR : Fin (Hypergraph.nV K) → Fin nVc)
  (labL : ∀ (xs : List (Fin (Hypergraph.nV G)))
        → map (Hypergraph.vlab G) xs ≡ map vlab-c (map ιL xs))
  (labR : ∀ (xs : List (Fin (Hypergraph.nV K)))
        → map (Hypergraph.vlab K) xs ≡ map vlab-c (map ιR xs))
  where

  private
    module G = Hypergraph G
    module K = Hypergraph K

  ein-c : Fin (G.nE + K.nE) → List (Fin nVc)
  ein-c e = [ (λ eG → map ιL (G.ein eG))
            , (λ eK → map ιR (K.ein eK))
            ]′ (splitAt G.nE e)

  eout-c : Fin (G.nE + K.nE) → List (Fin nVc)
  eout-c e = [ (λ eG → map ιL (G.eout eG))
             , (λ eK → map ιR (K.eout eK))
             ]′ (splitAt G.nE e)

  elab-c : (e : Fin (G.nE + K.nE))
         → FlatGen (map vlab-c (ein-c e)) (map vlab-c (eout-c e))
  elab-c e with splitAt G.nE e
  ... | inj₁ eG = retype (labL (G.ein eG)) (labL (G.eout eG)) (G.elab eG)
  ... | inj₂ eK = retype (labR (K.ein eK)) (labR (K.eout eK)) (K.elab eK)

  -- `ein-c` / `eout-c` reduce in each branch of the internal `with`.
  ein-c-inj₁-red : ∀ (eG : Fin G.nE) → ein-c (eG ↑ˡ K.nE) ≡ map ιL (G.ein eG)
  ein-c-inj₁-red eG with splitAt G.nE (eG ↑ˡ K.nE) | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)      | refl = refl

  eout-c-inj₁-red : ∀ (eG : Fin G.nE) → eout-c (eG ↑ˡ K.nE) ≡ map ιL (G.eout eG)
  eout-c-inj₁-red eG with splitAt G.nE (eG ↑ˡ K.nE) | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)       | refl = refl

  ein-c-inj₂-red : ∀ (eK : Fin K.nE) → ein-c (G.nE ↑ʳ eK) ≡ map ιR (K.ein eK)
  ein-c-inj₂-red eK with splitAt G.nE (G.nE ↑ʳ eK) | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)      | refl = refl

  eout-c-inj₂-red : ∀ (eK : Fin K.nE) → eout-c (G.nE ↑ʳ eK) ≡ map ιR (K.eout eK)
  eout-c-inj₂-red eK with splitAt G.nE (G.nE ↑ʳ eK) | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)       | refl = refl

  elab-c-inj₁ : ∀ (eG : Fin G.nE)
              → subst₂ FlatGen
                  (cong (map vlab-c) (ein-c-inj₁-red eG))
                  (cong (map vlab-c) (eout-c-inj₁-red eG))
                  (elab-c (eG ↑ˡ K.nE))
              ≡ subst₂ FlatGen (labL (G.ein eG)) (labL (G.eout eG)) (G.elab eG)
  elab-c-inj₁ eG with splitAt G.nE (eG ↑ˡ K.nE) | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)   | refl =
        retype-≡ (labL (G.ein eG)) (labL (G.eout eG)) (G.elab eG)

  elab-c-inj₂ : ∀ (eK : Fin K.nE)
              → subst₂ FlatGen
                  (cong (map vlab-c) (ein-c-inj₂-red eK))
                  (cong (map vlab-c) (eout-c-inj₂-red eK))
                  (elab-c (G.nE ↑ʳ eK))
              ≡ subst₂ FlatGen (labR (K.ein eK)) (labR (K.eout eK)) (K.elab eK)
  elab-c-inj₂ eK with splitAt G.nE (G.nE ↑ʳ eK) | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)   | refl =
        retype-≡ (labR (K.ein eK)) (labR (K.eout eK)) (K.elab eK)

--------------------------------------------------------------------------------
-- Tensor: disjoint union with concatenated boundaries.

module hTensor-impl (G K : Hypergraph FlatGen) where

  private
    module G = Hypergraph G
    module K = Hypergraph K

  injL : Fin G.nV → Fin (G.nV + K.nV)
  injL i = i ↑ˡ K.nV

  injR : Fin K.nV → Fin (G.nV + K.nV)
  injR j = G.nV ↑ʳ j

  vlab-c : Fin (G.nV + K.nV) → X
  vlab-c i = [ G.vlab , K.vlab ]′ (splitAt G.nV i)

  vlab-injL : ∀ i → vlab-c (injL i) ≡ G.vlab i
  vlab-injL i = cong [ G.vlab , K.vlab ]′ (splitAt-↑ˡ G.nV i K.nV)

  vlab-injR : ∀ j → vlab-c (injR j) ≡ K.vlab j
  vlab-injR j = cong [ G.vlab , K.vlab ]′ (splitAt-↑ʳ G.nV K.nV j)

  open CoproductEdges G K (G.nV + K.nV) vlab-c injL injR
         (map-via vlab-injL) (map-via vlab-injR) public

hTensor : Hypergraph FlatGen → Hypergraph FlatGen → Hypergraph FlatGen
hTensor G K = record
  { nV = G.nV + K.nV
  ; vlab = vlab-c
  ; nE = G.nE + K.nE
  ; ein = ein-c
  ; eout = eout-c
  ; elab = elab-c
  ; dom = map injL G.dom ++ map injR K.dom
  ; cod = map injL G.cod ++ map injR K.cod
  }
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hTensor-impl G K

-- Boundary lemmas for hTensor.

module _ (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    open hTensor-impl G K

    hTensor-boundary
      : (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
      → map vlab-c (map injL xs ++ map injR ys)
      ≡ map G.vlab xs ++ map K.vlab ys
    hTensor-boundary xs ys = trans
      (map-++ vlab-c (map injL xs) (map injR ys))
      (cong₂ _++_
        (sym (map-via vlab-injL xs))
        (sym (map-via vlab-injR ys)))

  domL-hTensor : domL (hTensor G K) ≡ domL G ++ domL K
  domL-hTensor = hTensor-boundary G.dom K.dom

  codL-hTensor : codL (hTensor G K) ≡ codL G ++ codL K
  codL-hTensor = hTensor-boundary G.cod K.cod

--------------------------------------------------------------------------------
-- Identity on an ObjTerm: one fresh vertex per atom, no edges.

hId : ObjTerm → Hypergraph FlatGen
hId unit = hEmpty
hId (Var x) = hVar x
hId (A ⊗₀ B) = hTensor (hId A) (hId B)

domL-hId : ∀ A → domL (hId A) ≡ flatten A
domL-hId unit       = refl
domL-hId (Var x)    = refl
domL-hId (A ⊗₀ B)   =
  trans (domL-hTensor (hId A) (hId B))
        (cong₂ _++_ (domL-hId A) (domL-hId B))

codL-hId : ∀ A → codL (hId A) ≡ flatten A
codL-hId unit       = refl
codL-hId (Var x)    = refl
codL-hId (A ⊗₀ B)   =
  trans (codL-hTensor (hId A) (hId B))
        (cong₂ _++_ (codL-hId A) (codL-hId B))

--------------------------------------------------------------------------------
-- Shared interface labeling for `hGen` and `hSwap`: vertices = flatten A ++
-- flatten B, with `vlab-c` the boundary labeling `[ lookup (flatten A) ,
-- lookup (flatten B) ]′ ∘ splitAt nA` and its two reduction lemmas + the
-- left/right `map`-recovery lemmas (parallel to `hTensor-impl`).

module hGenSwap-impl (A B : ObjTerm) where
  nA = length (flatten A)
  nB = length (flatten B)

  vlab-c : Fin (nA + nB) → X
  vlab-c i = [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt nA i)

  vlab-inL : ∀ (i : Fin nA) → vlab-c (i ↑ˡ nB) ≡ lookup (flatten A) i
  vlab-inL i = cong [ lookup (flatten A) , lookup (flatten B) ]′
                    (splitAt-↑ˡ nA i nB)

  vlab-inR : ∀ (i : Fin nB) → vlab-c (nA ↑ʳ i) ≡ lookup (flatten B) i
  vlab-inR i = cong [ lookup (flatten A) , lookup (flatten B) ]′
                    (splitAt-↑ʳ nA nB i)

  lem-L : map vlab-c (map (_↑ˡ nB) (range nA)) ≡ flatten A
  lem-L = trans (map-∘-cong vlab-inL (range nA)) (map-lookup-range (flatten A))

  lem-R : map vlab-c (map (nA ↑ʳ_) (range nB)) ≡ flatten B
  lem-R = trans (map-∘-cong vlab-inR (range nB)) (map-lookup-range (flatten B))

--------------------------------------------------------------------------------
-- Single edge hypergraph for a user generator `mor A B`.

hGen : ∀ {A B} → mor A B → Hypergraph FlatGen
hGen {A} {B} f = record
  { nV = nA + nB
  ; vlab = vlab-c
  ; nE = 1
  ; ein = λ _ → map (_↑ˡ nB) (range nA)
  ; eout = λ _ → map (nA ↑ʳ_) (range nB)
  ; elab = λ _ → retype (sym lem-L) (sym lem-R) (flat f)
  ; dom = map (_↑ˡ nB) (range nA)
  ; cod = map (nA ↑ʳ_) (range nB)
  }
  where open hGenSwap-impl A B

domL-hGen : ∀ {A B} (g : mor A B) → domL (hGen g) ≡ flatten A
domL-hGen {A} {B} _ = lem-L
  where open hGenSwap-impl A B

codL-hGen : ∀ {A B} (g : mor A B) → codL (hGen g) ≡ flatten B
codL-hGen {A} {B} _ = lem-R
  where open hGenSwap-impl A B

--------------------------------------------------------------------------------
-- Symmetry: vertices = flatten A ++ flatten B, no edges, swapped boundary.

hSwap : ObjTerm → ObjTerm → Hypergraph FlatGen
hSwap A B = record
  { nV = nA + nB
  ; vlab = vlab-c
  ; nE = 0
  ; ein = λ (); eout = λ (); elab = λ ()
  ; dom = map (_↑ˡ nB) (range nA) ++ map (nA ↑ʳ_) (range nB)
  ; cod = map (nA ↑ʳ_) (range nB) ++ map (_↑ˡ nB) (range nA)
  }
  where open hGenSwap-impl A B

domL-hSwap : ∀ A B → domL (hSwap A B) ≡ flatten A ++ flatten B
domL-hSwap A B =
  trans (map-++ vlab-c (map (_↑ˡ nB) (range nA)) (map (nA ↑ʳ_) (range nB)))
        (cong₂ _++_ lem-L lem-R)
  where open hGenSwap-impl A B

codL-hSwap : ∀ A B → codL (hSwap A B) ≡ flatten B ++ flatten A
codL-hSwap A B =
  trans (map-++ vlab-c (map (nA ↑ʳ_) (range nB)) (map (_↑ˡ nB) (range nA)))
        (cong₂ _++_ lem-R lem-L)
  where open hGenSwap-impl A B

