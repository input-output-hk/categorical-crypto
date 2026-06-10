{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Translate an APROP term `HomTerm A B` into a labeled hypergraph
-- `Hypergraph FlatGen`.
--
-- The hypergraph is *un-indexed* — it does not carry its boundary
-- atom-lists in the type.  The boundary facts `domL ⟪f⟫ ≡ flatten A`
-- and `codL ⟪f⟫ ≡ flatten B` are exposed as separate propositional
-- lemmas (`⟪⟫-domL`, `⟪⟫-codL`).
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
-- Cospan composition lives in `PrunedCompose.hComposeP` (the unpruned
-- `hCompose` was retired together with the unpruned decoder; see
-- docs/size-reduction-strategies.md, 2026-06-10 addendum).
--
-- The benefit of de-indexing: `subst₂ (Hypergraph FlatGen)` no longer shows
-- up; the ρ/α cases of `⟪_⟫` are plain `hId` calls, with the boundary
-- equations living in the boundary lemmas rather than the type.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.FromAPROP (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties as Fin using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List using (List; []; _∷_; _++_; length; map; lookup)
open import Data.List.Properties using (map-∘; map-++; map-cong; ++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst₂)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Flattening an ObjTerm into its list of atoms.

flatten : ObjTerm → List X
flatten unit = []
flatten (A ⊗₀ B) = flatten A ++ flatten B
flatten (Var x) = x ∷ []

-- Edges carry generators whose boundary is already a flat atom list.
data FlatGen : List X → List X → Set where
  flat : ∀ {A B} → mor A B → FlatGen (flatten A) (flatten B)

--------------------------------------------------------------------------------
-- Fin-range helpers.

range : (n : ℕ) → List (Fin n)
range zero = []
range (suc n) = zero ∷ map suc (range n)

-- `map (lookup xs) (range (length xs)) ≡ xs`.
map-lookup-range : (xs : List X) → map (lookup xs) (range (length xs)) ≡ xs
map-lookup-range [] = refl
map-lookup-range (x ∷ xs) =
  cong (x ∷_)
    (trans (sym (map-∘ (range (length xs))))
           (map-lookup-range xs))

--------------------------------------------------------------------------------
-- Generic helpers: map through inject+/raise preserves a pointwise-stated
-- vertex labeling.

map-via-inj : ∀ {m n : ℕ} {v : Fin m → X} {w : Fin (m + n) → X}
            → (∀ i → w (i ↑ˡ n) ≡ v i)
            → (xs : List (Fin m))
            → map v xs ≡ map w (map (_↑ˡ n) xs)
map-via-inj p xs =
  trans (sym (map-cong p xs)) (map-∘ xs)

map-via-raise : ∀ {m n : ℕ} {v : Fin n → X} {w : Fin (m + n) → X}
              → (∀ i → w (m ↑ʳ i) ≡ v i)
              → (xs : List (Fin n))
              → map v xs ≡ map w (map (m ↑ʳ_) xs)
map-via-raise p xs =
  trans (sym (map-cong p xs)) (map-∘ xs)

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

  ein-c : Fin (G.nE + K.nE) → List (Fin (G.nV + K.nV))
  ein-c e = [ (λ eG → map injL (G.ein eG))
            , (λ eK → map injR (K.ein eK))
            ]′ (splitAt G.nE e)

  eout-c : Fin (G.nE + K.nE) → List (Fin (G.nV + K.nV))
  eout-c e = [ (λ eG → map injL (G.eout eG))
             , (λ eK → map injR (K.eout eK))
             ]′ (splitAt G.nE e)

  elab-c : (e : Fin (G.nE + K.nE))
         → FlatGen (map vlab-c (ein-c e)) (map vlab-c (eout-c e))
  elab-c e with splitAt G.nE e
  ... | inj₁ eG = subst₂ FlatGen
                    (map-via-inj vlab-injL (G.ein eG))
                    (map-via-inj vlab-injL (G.eout eG))
                    (G.elab eG)
  ... | inj₂ eK = subst₂ FlatGen
                    (map-via-raise vlab-injR (K.ein eK))
                    (map-via-raise vlab-injR (K.eout eK))
                    (K.elab eK)

  -- ein-c / eout-c reduce in each branch of the internal `with`.
  ein-c-inj₁-red : ∀ (eG : Fin G.nE)
                 → ein-c (eG ↑ˡ K.nE) ≡ map injL (G.ein eG)
  ein-c-inj₁-red eG with splitAt G.nE (eG ↑ˡ K.nE)
                         | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)      | refl = refl

  eout-c-inj₁-red : ∀ (eG : Fin G.nE)
                  → eout-c (eG ↑ˡ K.nE) ≡ map injL (G.eout eG)
  eout-c-inj₁-red eG with splitAt G.nE (eG ↑ˡ K.nE)
                          | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)       | refl = refl

  ein-c-inj₂-red : ∀ (eK : Fin K.nE)
                 → ein-c (G.nE ↑ʳ eK) ≡ map injR (K.ein eK)
  ein-c-inj₂-red eK with splitAt G.nE (G.nE ↑ʳ eK)
                         | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)      | refl = refl

  eout-c-inj₂-red : ∀ (eK : Fin K.nE)
                  → eout-c (G.nE ↑ʳ eK) ≡ map injR (K.eout eK)
  eout-c-inj₂-red eK with splitAt G.nE (G.nE ↑ʳ eK)
                          | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)       | refl = refl

  elab-c-inj₁ : ∀ (eG : Fin G.nE)
              → subst₂ FlatGen
                  (cong (map vlab-c) (ein-c-inj₁-red eG))
                  (cong (map vlab-c) (eout-c-inj₁-red eG))
                  (elab-c (eG ↑ˡ K.nE))
              ≡ subst₂ FlatGen
                  (map-via-inj vlab-injL (G.ein eG))
                  (map-via-inj vlab-injL (G.eout eG))
                  (G.elab eG)
  elab-c-inj₁ eG with splitAt G.nE (eG ↑ˡ K.nE)
                      | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)   | refl = refl

  elab-c-inj₂ : ∀ (eK : Fin K.nE)
              → subst₂ FlatGen
                  (cong (map vlab-c) (ein-c-inj₂-red eK))
                  (cong (map vlab-c) (eout-c-inj₂-red eK))
                  (elab-c (G.nE ↑ʳ eK))
              ≡ subst₂ FlatGen
                  (map-via-raise vlab-injR (K.ein eK))
                  (map-via-raise vlab-injR (K.eout eK))
                  (K.elab eK)
  elab-c-inj₂ eK with splitAt G.nE (G.nE ↑ʳ eK)
                      | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)   | refl = refl

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

-- Boundary lemmas for hTensor (replacing `boundary-eq`'s type-level role
-- in the indexed version).

module _ (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    open hTensor-impl G K

  private
    hTensor-boundary
      : (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
      → map vlab-c (map injL xs ++ map injR ys)
      ≡ map G.vlab xs ++ map K.vlab ys
    hTensor-boundary xs ys = trans
      (map-++ vlab-c (map injL xs) (map injR ys))
      (cong₂ _++_
        (sym (map-via-inj   vlab-injL xs))
        (sym (map-via-raise vlab-injR ys)))

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
-- Single edge hypergraph for a user generator `mor A B`.

hGen : ∀ {A B} → mor A B → Hypergraph FlatGen
hGen {A} {B} f = record
  { nV = nA + nB
  ; vlab = vlab-c
  ; nE = 1
  ; ein = λ _ → map (_↑ˡ nB) (range nA)
  ; eout = λ _ → map (nA ↑ʳ_) (range nB)
  ; elab = λ _ → subst₂ FlatGen lem-in lem-out (flat f)
  ; dom = map (_↑ˡ nB) (range nA)
  ; cod = map (nA ↑ʳ_) (range nB)
  }
  where
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

    lem-in : flatten A ≡ map vlab-c (map (_↑ˡ nB) (range nA))
    lem-in = sym
      (trans (sym (map-∘ (range nA)))
      (trans (map-cong vlab-inL (range nA))
             (map-lookup-range (flatten A))))

    lem-out : flatten B ≡ map vlab-c (map (nA ↑ʳ_) (range nB))
    lem-out = sym
      (trans (sym (map-∘ (range nB)))
      (trans (map-cong vlab-inR (range nB))
             (map-lookup-range (flatten B))))

domL-hGen : ∀ {A B} (g : mor A B) → domL (hGen g) ≡ flatten A
domL-hGen {A} {B} _ =
  trans (sym (map-∘ (range nA)))
        (trans (map-cong vlab-inL (range nA))
               (map-lookup-range (flatten A)))
  where
    nA = length (flatten A)
    nB = length (flatten B)
    vlab-c : Fin (nA + nB) → X
    vlab-c i = [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt nA i)
    vlab-inL : (i : Fin nA) → vlab-c (i ↑ˡ nB) ≡ lookup (flatten A) i
    vlab-inL i = cong [ lookup (flatten A) , lookup (flatten B) ]′
                       (splitAt-↑ˡ nA i nB)

codL-hGen : ∀ {A B} (g : mor A B) → codL (hGen g) ≡ flatten B
codL-hGen {A} {B} _ =
  trans (sym (map-∘ (range nB)))
        (trans (map-cong vlab-inR (range nB))
               (map-lookup-range (flatten B)))
  where
    nA = length (flatten A)
    nB = length (flatten B)
    vlab-c : Fin (nA + nB) → X
    vlab-c i = [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt nA i)
    vlab-inR : (i : Fin nB) → vlab-c (nA ↑ʳ i) ≡ lookup (flatten B) i
    vlab-inR i = cong [ lookup (flatten A) , lookup (flatten B) ]′
                       (splitAt-↑ʳ nA nB i)

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
  where
    nA = length (flatten A)
    nB = length (flatten B)
    vlab-c : Fin (nA + nB) → X
    vlab-c i = [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt nA i)

domL-hSwap : ∀ A B → domL (hSwap A B) ≡ flatten A ++ flatten B
domL-hSwap A B =
  trans (map-++ vlab-c (map (_↑ˡ nB) (range nA)) (map (nA ↑ʳ_) (range nB)))
        (cong₂ _++_ lem-L lem-R)
  where
    nA = length (flatten A)
    nB = length (flatten B)
    vlab-c : Fin (nA + nB) → X
    vlab-c i = [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt nA i)
    vlab-inL : ∀ (i : Fin nA) → vlab-c (i ↑ˡ nB) ≡ lookup (flatten A) i
    vlab-inL i = cong [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt-↑ˡ nA i nB)
    vlab-inR : ∀ (i : Fin nB) → vlab-c (nA ↑ʳ i) ≡ lookup (flatten B) i
    vlab-inR i = cong [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt-↑ʳ nA nB i)
    lem-L : map vlab-c (map (_↑ˡ nB) (range nA)) ≡ flatten A
    lem-L = trans (sym (map-∘ (range nA)))
                  (trans (map-cong vlab-inL (range nA)) (map-lookup-range (flatten A)))
    lem-R : map vlab-c (map (nA ↑ʳ_) (range nB)) ≡ flatten B
    lem-R = trans (sym (map-∘ (range nB)))
                  (trans (map-cong vlab-inR (range nB)) (map-lookup-range (flatten B)))

codL-hSwap : ∀ A B → codL (hSwap A B) ≡ flatten B ++ flatten A
codL-hSwap A B =
  trans (map-++ vlab-c (map (nA ↑ʳ_) (range nB)) (map (_↑ˡ nB) (range nA)))
        (cong₂ _++_ lem-R lem-L)
  where
    nA = length (flatten A)
    nB = length (flatten B)
    vlab-c : Fin (nA + nB) → X
    vlab-c i = [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt nA i)
    vlab-inL : ∀ (i : Fin nA) → vlab-c (i ↑ˡ nB) ≡ lookup (flatten A) i
    vlab-inL i = cong [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt-↑ˡ nA i nB)
    vlab-inR : ∀ (i : Fin nB) → vlab-c (nA ↑ʳ i) ≡ lookup (flatten B) i
    vlab-inR i = cong [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt-↑ʳ nA nB i)
    lem-L : map vlab-c (map (_↑ˡ nB) (range nA)) ≡ flatten A
    lem-L = trans (sym (map-∘ (range nA)))
                  (trans (map-cong vlab-inL (range nA)) (map-lookup-range (flatten A)))
    lem-R : map vlab-c (map (nA ↑ʳ_) (range nB)) ≡ flatten B
    lem-R = trans (sym (map-∘ (range nB)))
                  (trans (map-cong vlab-inR (range nB)) (map-lookup-range (flatten B)))

