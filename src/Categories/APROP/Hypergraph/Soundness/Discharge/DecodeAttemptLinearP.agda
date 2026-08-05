{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Totality of the decoder on the translation `⟪_⟫ₚ`, whose `∘` case uses
-- `hComposeP`.  Three pieces: `decode-attempt-hComposeP` (the `∘` lift),
-- `⟪⟫-LinearP` (the invariant), `decode-attempt-LinearP` (totality), plus
-- the packaged total decoder `decodeP`.
--
-- Pruning removes only vertices, never edges (same `nE`, same Fin order),
-- so every atomic (non-`∘`) decode lemma from `DecodeAttempt` is reused
-- verbatim; only the `∘` machinery is proven here.  No postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig

open import Categories.APROP.Hypergraph.Model.PrunedCompose sig

open import Categories.APROP.Hypergraph.Util.Prune

open import Categories.APROP.Hypergraph.Model.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig

open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig

import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
open Inv
import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig as Lin
open import Categories.APROP.Hypergraph.Soundness.Discharge.LinearHComposeP sig
  using (Linear-hComposeP)
import Categories.APROP.Hypergraph.Soundness.Discharge.LinearHComposeP sig as LP

-- Reused-as-is generic decode lemmas (arbitrary `H`).
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig


open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Nat
open import Data.List
open import Data.List.Properties
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality


--------------------------------------------------------------------------------
-- Per-edge / process-edges liftings for `hComposeP`.  The G-side raise is
-- `injL = _↑ˡ cn`; the K-side remap is `remapP` (whose injectivity needs
-- Linear G + K).

module _
  (G K : Hypergraph FlatGen)
  (bdy-eq : codL G ≡ domL K)
  (lin-G : Lin.Linear G) (lin-K : Lin.Linear K)
  where
  private
    module G = Hypergraph G
    module K = Hypergraph K

  open hComposeP-impl G K bdy-eq


  remapP-injective : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective = LP.remapP-injective G K bdy-eq lin-G lin-K

  cn : ℕ
  cn = count-non K.dom

  -- G-side: per-edge lifting on a pure-L stack `map injL xs`.

  -- The G-side instance of `DecodeAttempt.StackLift`: frame-free, so the
  -- stack former is `map injL` and `fold` is one `map-++`.
  private
    module PureL where
      out : List (Fin G.nV) → List (Fin nV-P)
      out = map injL

      hit : ∀ (e : Fin G.nE) (xs rest : List (Fin G.nV))
              (p : xs Perm.↭ G.ein e ++ rest)
          → extract-prefix (G.ein e) xs ≡ just (rest , p)
          → ∃[ q ] extract-prefix
                     (Hypergraph.ein (hComposeP G K bdy-eq) (e ↑ˡ K.nE)) (out xs)
                   ≡ just (out rest , q)
      hit e xs rest p eq =
        subst (λ ks → ∃[ q ] extract-prefix ks (out xs) ≡ just (out rest , q))
              (sym (ein-c-inj₁-red e))
              (extract-prefix-via-injective-just injL (inject+-inj cn)
                                                  (G.ein e) xs rest p eq)

      miss : ∀ (e : Fin G.nE) (xs : List (Fin G.nV))
           → extract-prefix (G.ein e) xs ≡ nothing
           → extract-prefix
               (Hypergraph.ein (hComposeP G K bdy-eq) (e ↑ˡ K.nE)) (out xs)
             ≡ nothing
      miss e xs eq =
        subst (λ ks → extract-prefix ks (out xs) ≡ nothing)
              (sym (ein-c-inj₁-red e))
              (extract-prefix-via-injective-nothing injL (inject+-inj cn)
                                                     (G.ein e) xs eq)

      fold : ∀ (e : Fin G.nE) (rest : List (Fin G.nV))
           → Hypergraph.eout (hComposeP G K bdy-eq) (e ↑ˡ K.nE) ++ out rest
             ≡ out (G.eout e ++ rest)
      fold e rest =
        trans (cong (_++ out rest) (eout-c-inj₁-red e))
              (sym (map-++ injL (G.eout e) rest))

      open StackLift (hComposeP G K bdy-eq) G (_↑ˡ K.nE) out hit miss fold public

  process-edges-↑ˡ-pure-L
    : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → process-edges (hComposeP G K bdy-eq) (map (_↑ˡ K.nE) es) (map injL xs)
      ≡ map injL (process-edges G es xs)
  process-edges-↑ˡ-pure-L = PureL.process-edges-lift

  --------------------------------------------------------------------
  -- K-side: the frame-free instance of `DecodeAttempt.PermLift` — with no
  -- L-block to commute past, `front` and `fold` are one `map-++` each.

  private
    module ViaRemapP where
      out : List (Fin K.nV) → List (Fin nV-P)
      out = map remapP

      front : ∀ (e : Fin K.nE) (ys rest : List (Fin K.nV))
            → ys Perm.↭ K.ein e ++ rest
            → out ys Perm.↭ map remapP (K.ein e) ++ out rest
      front e ys rest p =
        Perm.↭-trans (PermProp.map⁺ remapP p)
                     (Perm.↭-reflexive (map-++ remapP (K.ein e) rest))

      fold : ∀ (e : Fin K.nE) (rest : List (Fin K.nV))
           → map remapP (K.eout e) ++ out rest Perm.↭ out (K.eout e ++ rest)
      fold e rest = Perm.↭-reflexive (sym (map-++ remapP (K.eout e) rest))

      miss : ∀ (e : Fin K.nE) (ys : List (Fin K.nV))
           → extract-prefix (K.ein e) ys ≡ nothing
           → extract-prefix (map remapP (K.ein e)) (out ys) ≡ nothing
      miss e ys eq =
        extract-prefix-via-injective-nothing remapP remapP-injective
                                              (K.ein e) ys eq

      open PermLift (hComposeP G K bdy-eq) K (G.nE ↑ʳ_) remapP out
             ein-c-inj₂-red eout-c-inj₂-red front fold miss public

  process-edges-↑ʳ-via-remapP
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + cn)))
        (ys : List (Fin K.nV))
    → s Perm.↭ map remapP ys
    → process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) es) s
        Perm.↭ map remapP (process-edges K es ys)
  process-edges-↑ʳ-via-remapP = ViaRemapP.process-edges-lift

--------------------------------------------------------------------------------
-- `decode-attempt-hComposeP`.

decode-attempt-hComposeP
  : (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  → Lin.Linear G → Lin.Linear K
  → process-all-edges G (Hypergraph.dom G) Perm.↭ Hypergraph.cod G
  → process-all-edges K (Hypergraph.dom K) Perm.↭ Hypergraph.cod K
  → process-all-edges (hComposeP G K bdy-eq) (Hypergraph.dom (hComposeP G K bdy-eq))
      Perm.↭ Hypergraph.cod (hComposeP G K bdy-eq)
decode-attempt-hComposeP G K bdy-eq lin-G lin-K perm-G perm-K =
    perm-final
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hComposeP-impl G K bdy-eq
    map-remapP-K-dom = LP.map-remapP-K-dom G K bdy-eq lin-G lin-K
    open Perm.PermutationReasoning

    s_G_final = process-all-edges G G.dom
    s_K_final = process-all-edges K K.dom

    proc = process-all-edges (hComposeP G K bdy-eq) (Hypergraph.dom (hComposeP G K bdy-eq))

    after-G-stack = process-edges (hComposeP G K bdy-eq)
                      (map (_↑ˡ K.nE) (range G.nE))
                      (Hypergraph.dom (hComposeP G K bdy-eq))

    after-G-≡ : after-G-stack ≡ map injL s_G_final
    after-G-≡ = process-edges-↑ˡ-pure-L G K bdy-eq lin-G lin-K (range G.nE) G.dom

    after-G-↭-remap-Kdom : after-G-stack Perm.↭ map remapP K.dom
    after-G-↭-remap-Kdom = begin
      after-G-stack
        ≡⟨ after-G-≡ ⟩
      map injL s_G_final
        ↭⟨ PermProp.map⁺ injL perm-G ⟩
      map injL G.cod
        ≡⟨ sym map-remapP-K-dom ⟩
      map remapP K.dom
        ∎

    K-lift : process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
               Perm.↭ map remapP s_K_final
    K-lift = process-edges-↑ʳ-via-remapP G K bdy-eq lin-G lin-K
              (range K.nE) after-G-stack K.dom after-G-↭-remap-Kdom

    proc-≡ : proc
             ≡ process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
    proc-≡ =
      trans (cong (λ es → process-edges (hComposeP G K bdy-eq) es
                            (Hypergraph.dom (hComposeP G K bdy-eq)))
                  (Inv.range-++ G.nE K.nE))
            (process-edges-++-stack (hComposeP G K bdy-eq)
              (map (_↑ˡ K.nE) (range G.nE))
              (map (G.nE ↑ʳ_) (range K.nE))
              (Hypergraph.dom (hComposeP G K bdy-eq)))

    perm-final : proc Perm.↭ Hypergraph.cod (hComposeP G K bdy-eq)
    perm-final = begin
      proc
        ≡⟨ proc-≡ ⟩
      process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
        ↭⟨ K-lift ⟩
      map remapP s_K_final
        ↭⟨ PermProp.map⁺ remapP perm-K ⟩
      map remapP K.cod
        ∎

--------------------------------------------------------------------------------
-- `⟪⟫-LinearP`.

⟪⟫-LinearP : ∀ {A B} (f : HomTerm A B) → Lin.Linear ⟪ f ⟫ₚ
⟪⟫-LinearP (Agen g)        = Lin.Linear-hGen g
⟪⟫-LinearP (id {A})        = Lin.Linear-hId A
⟪⟫-LinearP (g ∘ f)         =
  Linear-hComposeP ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g)))
    (⟪⟫-LinearP f) (⟪⟫-LinearP g)
⟪⟫-LinearP (f ⊗₁ g)        = Lin.Linear-hTensor ⟪ f ⟫ₚ ⟪ g ⟫ₚ (⟪⟫-LinearP f) (⟪⟫-LinearP g)
⟪⟫-LinearP (λ⇒ {A})        = Lin.Linear-hId A
⟪⟫-LinearP (λ⇐ {A})        = Lin.Linear-hId A
⟪⟫-LinearP (ρ⇒ {A})        = Lin.Linear-hId (A ⊗₀ unit)
⟪⟫-LinearP (ρ⇐ {A})        = Lin.Linear-hId (A ⊗₀ unit)
⟪⟫-LinearP (α⇒ {A}{B}{C})  = Lin.Linear-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-LinearP (α⇐ {A}{B}{C})  = Lin.Linear-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-LinearP (σ {A}{B})      = Lin.Linear-hSwap A B

--------------------------------------------------------------------------------
-- `decode-attempt-LinearP`.

decode-attempt-LinearP
  : ∀ {A B} (f : HomTerm A B)
  → process-all-edges ⟪ f ⟫ₚ (Hypergraph.dom ⟪ f ⟫ₚ) Perm.↭ Hypergraph.cod ⟪ f ⟫ₚ
decode-attempt-LinearP (Agen g)        = decode-attempt-hGen g
decode-attempt-LinearP (id {A})        = decode-attempt-hId A
decode-attempt-LinearP (g ∘ f)         =
  decode-attempt-hComposeP ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g)))
    (⟪⟫-LinearP f) (⟪⟫-LinearP g)
    (decode-attempt-LinearP f) (decode-attempt-LinearP g)
decode-attempt-LinearP (f ⊗₁ g)        =
  decode-attempt-hTensor ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (decode-attempt-LinearP f) (decode-attempt-LinearP g)
decode-attempt-LinearP (λ⇒ {A})        = decode-attempt-hId A
decode-attempt-LinearP (λ⇐ {A})        = decode-attempt-hId A
decode-attempt-LinearP (ρ⇒ {A})        = decode-attempt-hId (A ⊗₀ unit)
decode-attempt-LinearP (ρ⇐ {A})        = decode-attempt-hId (A ⊗₀ unit)
decode-attempt-LinearP (α⇒ {A}{B}{C})  = decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)
decode-attempt-LinearP (α⇐ {A}{B}{C})  = decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)
decode-attempt-LinearP (σ {A}{B})      = decode-attempt-hSwap A B

-- NOTE (weak-decoder demotion, Review-2 F2): the non-strict total decoder
-- `decodeP` (which packaged `proj₁ (decode-attempt-LinearP f)` as a boundary
-- `subst₂ HomTerm`) had zero live consumers — the live pipeline runs entirely
-- through the strict `decodePˢ`.  It has been deleted along with the weak
-- morphism apparatus; only the totality witness `decode-attempt-LinearP`
-- survives (consumed by `Strict/Decode/Decode` — the witness IS the bare
-- permutation `process-all-edges ⟪f⟫ dom ↭ cod`, so no `Maybe`/`≡ just`
-- unwrapping is needed).
