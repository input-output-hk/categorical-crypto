{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- ## Block disjointness at the concrete `hTensor` layout, both sides.
--
-- K-side: the K-edge inputs `C.ein (ψK eK) = map injR (K.ein eK)` are disjoint
-- from any `injL`-block `map injL P` — the side condition
-- `TensorKBlockFinal`'s `disj-kblk` needs at `P = s_G_final`, `e = ψK eK`, and
-- through it the `stack-sepˢ`/`term-sepᵛ` separability of the K-block run on
-- the block-swapped stack.
-- G-side (the mirror `injL∉injRs`/`gblock-disjoint`): the whole G-block's
-- inputs are absent from the `injR` residual `map injR K.dom` — the
-- `stack-sepˢ`/`term-sepᵛ` side condition consumed by `TensorBraid.Braid` and
-- `TensorKBlockFinal`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorKBlock
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
-- Canonical Decoder alias for disambiguating 'open StrictDecoder':
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_ as Dec

open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig using (extract-elem)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
import Data.Fin.Properties as FinP
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality

module KBlockDisjoint (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open hTensor-impl G K using (injL; injR; ein-c-inj₁-red; ein-c-inj₂-red)
  open Dec.StrictDecoder (hTensor G K) using (vl; ein-disjoint; block-disjoint)

  ψK : Fin K.nE → Fin C.nE
  ψK eK = G.nE ↑ʳ eK

  ψG : Fin G.nE → Fin C.nE
  ψG eG = eG ↑ˡ K.nE

  private
    -- `x` is absent from an `f`-block whenever `f` never hits `x`.
    ∉-map : ∀ {m} {f : Fin m → Fin C.nV} {x : Fin C.nV} (P : List (Fin m))
          → (∀ k → f k ≡ x → ⊥) → extract-elem x (map f P) ≡ nothing
    ∉-map []       _  = refl
    ∉-map {f = f} {x} (k ∷ ks) ne with f k FinP.≟ x
    ... | yes p  = ⊥-elim (ne k p)
    ... | no  _  rewrite ∉-map ks ne = refl

    -- an `f`-block avoids `blk` pointwise ⇒ it avoids it as a list.
    all-∉-map
      : ∀ {m} {f : Fin m → Fin C.nV} (blk : List (Fin C.nV))
      → (∀ k → extract-elem (f k) blk ≡ nothing)
      → ∀ (ks : List (Fin m))
      → All (λ k → extract-elem k blk ≡ nothing) (map f ks)
    all-∉-map blk h []       = []
    all-∉-map blk h (k ∷ ks) = h k ∷ all-∉-map blk h ks

  -- the two injections are disjoint (`splitAt` lands in `inj₂` vs `inj₁`).
  injR≢injL : ∀ {j : Fin K.nV} {k : Fin G.nV} → injR j ≡ injL k → ⊥
  injR≢injL {j} {k} eq with trans (sym (splitAt-↑ʳ G.nV K.nV j))
                            (trans (cong (splitAt G.nV) eq)
                                   (splitAt-↑ˡ G.nV k K.nV))
  ... | ()

  -- `injR j` is absent from any `injL`-block, and dually.
  injR∉injLs : ∀ (j : Fin K.nV) (P : List (Fin G.nV)) → extract-elem (injR j) (map injL P) ≡ nothing
  injR∉injLs j P = ∉-map P (λ _ eq → injR≢injL (sym eq))

  injL∉injRs : ∀ (k : Fin G.nV) (Q : List (Fin K.nV)) → extract-elem (injL k) (map injR Q) ≡ nothing
  injL∉injRs k Q = ∉-map Q (λ _ → injR≢injL)

  -- `ein-disjⁱ (ψK eK) (map injL P)` / `ein-disjⁱ (ψG eG) (map injR Q)` at
  -- `H = hTensor G K`: the block's inputs are all on the other side.
  kblock-ein-disjoint
    : ∀ (eK : Fin K.nE) (P : List (Fin G.nV))
    → All (λ k → extract-elem k (map injL P) ≡ nothing) (C.ein (ψK eK))
  kblock-ein-disjoint eK P =
    subst (All (λ k → extract-elem k (map injL P) ≡ nothing))
          (sym (ein-c-inj₂-red eK))
          (all-∉-map (map injL P) (λ j → injR∉injLs j P) (K.ein eK))

  gblock-ein-disjoint : ∀ (eG : Fin G.nE) (Q : List (Fin K.nV)) → ein-disjoint (ψG eG) (map injR Q)
  gblock-ein-disjoint eG Q =
    subst (All (λ k → extract-elem k (map injR Q) ≡ nothing))
          (sym (ein-c-inj₁-red eG))
          (all-∉-map (map injR Q) (λ k → injL∉injRs k Q) (G.ein eG))

  gblk : List (Fin C.nE)
  gblk = map (_↑ˡ K.nE) (range G.nE)

  -- the whole G-block's inputs are absent from the `injR` residual.
  gblock-disjoint : block-disjoint gblk (map injR K.dom)
  gblock-disjoint = all-gblk (range G.nE)
    where
      all-gblk : ∀ (es : List (Fin G.nE)) → block-disjoint (map (_↑ˡ K.nE) es) (map injR K.dom)
      all-gblk []       = []
      all-gblk (e ∷ es) = gblock-ein-disjoint e K.dom ∷ all-gblk es

