{-# OPTIONS --safe --without-K #-}

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Model.FromAPROP (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.Nat
open import Data.Sum using (inj₁; inj₂; [_,_]′)

open APROP sig

open FreeMonoidalHelper Symm X using (flatten)

-- Rebuilding this record at the required boundaries avoids stacked `subst₂`
-- wrappers: projecting A/B/f need not normalise tower-deep boundary proofs.
-- Keep okA/okB relevant: soundness strictification and `DecodeLean.Agen-edge-aux`
-- use them without decidable equality on X. The solver carries them lazily;
-- `Verify.flatgen-irrel` compares them using UIP-ListX.
record FlatGen (As Bs : List X) : Set where
  constructor flat-rec
  field {A B} : ObjTerm
        okA : flatten A ≡ As
        okB : flatten B ≡ Bs
        f : mor A B

private
  variable
    A B : ObjTerm
    As Bs As' Bs' : List X

flat : mor A B → FlatGen (flatten A) (flatten B)
flat g = flat-rec refl refl g

-- Fold boundary equalities into the record rather than forcing them to refl.
retype : As ≡ As' → Bs ≡ Bs' → FlatGen As Bs → FlatGen As' Bs'
retype p q (flat-rec oa ob g) = flat-rec (trans oa p) (trans ob q) g

retype-≡ : (p : As ≡ As') (q : Bs ≡ Bs') (v : FlatGen As Bs)
         → retype p q v ≡ subst₂ FlatGen p q v
retype-≡ refl refl (flat-rec oa ob g) =
  cong₂ (λ a b → flat-rec a b g) (trans-reflʳ oa) (trans-reflʳ ob)

map-via : ∀ {m n : ℕ} {v : Fin m → X} {w : Fin n → X} {f : Fin m → Fin n}
        → (∀ i → w (f i) ≡ v i)
        → (xs : List (Fin m))
        → map v xs ≡ map w (map f xs)
map-via p xs = sym (map-∘-cong p xs)

--------------------------------------------------------------------------------
-- Binary composites
--------------------------------------------------------------------------------

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
-- Structural and generator graphs
--------------------------------------------------------------------------------

-- Define hId directly on flatten A: nE reduces to 0 and dom to cod even
-- for abstract A. Structural translations can therefore expose these facts
-- by refl, without a parallel induction on A.

hId : ObjTerm → Hypergraph FlatGen
hId A = record
  { nV = length (flatten A); vlab = lookup (flatten A); nE = 0
  ; ein = λ (); eout = λ (); elab = λ ()
  ; dom = allFin (length (flatten A))
  ; cod = allFin (length (flatten A))
  }

domL-hId : ∀ A → domL (hId A) ≡ flatten A
domL-hId A = map-lookup-allFin (flatten A)

codL-hId : ∀ A → codL (hId A) ≡ flatten A
codL-hId A = domL-hId A

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

  Lblk : List (Fin (nA + nB))
  Lblk = map (_↑ˡ nB) (allFin nA)

  Rblk : List (Fin (nA + nB))
  Rblk = map (nA ↑ʳ_) (allFin nB)

  lem-L : map vlab-c Lblk ≡ flatten A
  lem-L = trans (map-∘-cong vlab-inL (allFin nA)) (domL-hId A)

  lem-R : map vlab-c Rblk ≡ flatten B
  lem-R = trans (map-∘-cong vlab-inR (allFin nB)) (domL-hId B)

hGen : mor A B → Hypergraph FlatGen
hGen {A} {B} f = record
  { nV = nA + nB
  ; vlab = vlab-c
  ; nE = 1
  ; ein = λ _ → Lblk
  ; eout = λ _ → Rblk
  ; elab = λ _ → retype (sym lem-L) (sym lem-R) (flat f)
  ; dom = Lblk
  ; cod = Rblk
  }
  where open hGenSwap-impl A B

domL-hGen : (g : mor A B) → domL (hGen g) ≡ flatten A
domL-hGen {A} {B} _ = lem-L
  where open hGenSwap-impl A B

codL-hGen : (g : mor A B) → codL (hGen g) ≡ flatten B
codL-hGen {A} {B} _ = lem-R
  where open hGenSwap-impl A B

hSwap : ObjTerm → ObjTerm → Hypergraph FlatGen
hSwap A B = record
  { nV = nA + nB
  ; vlab = vlab-c
  ; nE = 0
  ; ein = λ (); eout = λ (); elab = λ ()
  ; dom = Lblk ++ Rblk
  ; cod = Rblk ++ Lblk
  }
  where open hGenSwap-impl A B

domL-hSwap : ∀ A B → domL (hSwap A B) ≡ flatten A ++ flatten B
domL-hSwap A B = trans (map-++ vlab-c Lblk Rblk) (cong₂ _++_ lem-L lem-R)
  where open hGenSwap-impl A B

codL-hSwap : ∀ A B → codL (hSwap A B) ≡ flatten B ++ flatten A
codL-hSwap A B = trans (map-++ vlab-c Rblk Lblk) (cong₂ _++_ lem-R lem-L)
  where open hGenSwap-impl A B
