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

  edge-step-↑ˡ-pure-L-just
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
        (rest : List (Fin G.nV)) (p : xs Perm.↭ G.ein eG ++ rest)
    → extract-prefix (G.ein eG) xs ≡ just (rest , p)
    → edge-step (hComposeP G K bdy-eq) (map injL xs) (eG ↑ˡ K.nE)
      ≡ map injL (G.eout eG ++ rest)
  edge-step-↑ˡ-pure-L-just eG xs rest p eq =
      trans reduce-result list-eq
    where
      open ≡-Reasoning
      stack = map injL xs

      eq-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)) stack
                 ≡ just (map injL rest , q)
      eq-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks stack
                              ≡ just (map injL rest , q))
              (sym (ein-c-inj₁-red eG))
              (extract-prefix-via-injective-just injL (inject+-inj cn)
                                                  (G.ein eG) xs rest p eq)

      reduce-result
        : edge-step (hComposeP G K bdy-eq) stack (eG ↑ˡ K.nE)
          ≡ Hypergraph.eout (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)
              ++ map injL rest
      reduce-result =
        edge-step-just (hComposeP G K bdy-eq) stack (eG ↑ˡ K.nE)
                       (proj₂ eq-on-ein-c)

      list-eq : Hypergraph.eout (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)
                  ++ map injL rest
              ≡ map injL (G.eout eG ++ rest)
      list-eq = begin
        Hypergraph.eout (hComposeP G K bdy-eq) (eG ↑ˡ K.nE)
          ++ map injL rest
          ≡⟨ cong (_++ map injL rest) (eout-c-inj₁-red eG) ⟩
        map injL (G.eout eG) ++ map injL rest
          ≡⟨ sym (map-++ injL (G.eout eG) rest) ⟩
        map injL (G.eout eG ++ rest)
          ∎

  edge-step-↑ˡ-pure-L-nothing
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
    → extract-prefix (G.ein eG) xs ≡ nothing
    → edge-step (hComposeP G K bdy-eq) (map injL xs) (eG ↑ˡ K.nE)
      ≡ map injL xs
  edge-step-↑ˡ-pure-L-nothing eG xs eq =
    edge-step-nothing (hComposeP G K bdy-eq) stack (eG ↑ˡ K.nE) nothing-lifted
    where
      stack = map injL xs

      nothing-lifted : extract-prefix
                         (Hypergraph.ein (hComposeP G K bdy-eq) (eG ↑ˡ K.nE))
                         stack ≡ nothing
      nothing-lifted =
        subst (λ ks → extract-prefix ks stack ≡ nothing)
              (sym (ein-c-inj₁-red eG))
              (extract-prefix-via-injective-nothing injL
                                                     (inject+-inj cn)
                                                     (G.ein eG) xs eq)

  edge-step-↑ˡ-pure-L
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
    → edge-step (hComposeP G K bdy-eq) (map injL xs) (eG ↑ˡ K.nE)
      ≡ map injL (edge-step G xs eG)
  edge-step-↑ˡ-pure-L eG xs with extract-prefix (G.ein eG) xs in eq
  ... | just (rest , p) = edge-step-↑ˡ-pure-L-just eG xs rest p eq
  ... | nothing         = edge-step-↑ˡ-pure-L-nothing eG xs eq

  process-edges-↑ˡ-pure-L
    : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → process-edges (hComposeP G K bdy-eq) (map (_↑ˡ K.nE) es) (map injL xs)
      ≡ map injL (process-edges G es xs)
  process-edges-↑ˡ-pure-L []       xs = refl
  process-edges-↑ˡ-pure-L (e ∷ es) xs
    rewrite edge-step-↑ˡ-pure-L e xs =
      process-edges-↑ˡ-pure-L es (edge-step G xs e)

  --------------------------------------------------------------------
  -- K-side: perm-respecting per-edge lifting via remapP.  Input stack
  -- `↭ map remapP ys`; output `↭ map remapP (proj₁ (edge-step K ys eK))`.

  edge-step-↑ʳ-via-remapP
    : ∀ (eK : Fin K.nE)
        (s : List (Fin (G.nV + cn)))
        (ys : List (Fin K.nV))
    → s Perm.↭ map remapP ys
    → edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK)
        Perm.↭ map remapP (edge-step K ys eK)
  edge-step-↑ʳ-via-remapP eK s ys s↭std with extract-prefix (K.ein eK) ys in eq-K
  ... | just (rest , p-K) =
        Perm.↭-trans (Perm.↭-reflexive edge-step-eq) final-perm
    where
      open Perm.PermutationReasoning
      R-pre = map remapP (K.ein eK)
      R-out = map remapP (K.eout eK)
      R-rst = map remapP rest

      s↭shuffled : s Perm.↭ R-pre ++ R-rst
      s↭shuffled = begin
        s
          ↭⟨ s↭std ⟩
        map remapP ys
          ↭⟨ PermProp.map⁺ remapP p-K ⟩
        map remapP (K.ein eK ++ rest)
          ≡⟨ map-++ remapP (K.ein eK) rest ⟩
        R-pre ++ R-rst
          ∎

      extract-step : ∃[ r ] ∃[ p ] extract-prefix R-pre s ≡ just (r , p) × R-rst Perm.↭ r
      extract-step = extract-prefix-↭-residual R-pre s R-rst s↭shuffled

      r = proj₁ extract-step
      r↭ : R-rst Perm.↭ r
      r↭ = proj₂ (proj₂ (proj₂ extract-step))

      extract-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hComposeP G K bdy-eq) (G.nE ↑ʳ eK)) s
                 ≡ just (r , q)
      extract-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks s ≡ just (r , q))
              (sym (ein-c-inj₂-red eK))
              (proj₁ (proj₂ extract-step) ,
               proj₁ (proj₂ (proj₂ extract-step)))

      reduce-result
        : edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK)
          ≡ Hypergraph.eout (hComposeP G K bdy-eq) (G.nE ↑ʳ eK) ++ r
      reduce-result =
        edge-step-just (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK)
                       (proj₂ extract-on-ein-c)

      edge-step-eq
        : edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK) ≡ R-out ++ r
      edge-step-eq =
        subst (λ ks → edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK)
                       ≡ ks ++ r)
              (eout-c-inj₂-red eK)
              reduce-result

      -- `edge-step K ys eK` reduces (via `eq-K`) to `K.eout eK ++ rest`.
      final-perm : R-out ++ r Perm.↭ map remapP (K.eout eK ++ rest)
      final-perm = begin
        R-out ++ r
          ↭⟨ PermProp.++⁺ˡ R-out (Perm.↭-sym r↭) ⟩
        R-out ++ R-rst
          ≡⟨ sym (map-++ remapP (K.eout eK) rest) ⟩
        map remapP (K.eout eK ++ rest)
          ∎

  ... | nothing =
        Perm.↭-trans (Perm.↭-reflexive reduce-to-id) s↭std
    where
      nothing-on-std : extract-prefix (map remapP (K.ein eK)) (map remapP ys) ≡ nothing
      nothing-on-std =
        extract-prefix-via-injective-nothing remapP remapP-injective
                                              (K.ein eK) ys eq-K

      nothing-on-s : extract-prefix (map remapP (K.ein eK)) s ≡ nothing
      nothing-on-s =
        extract-prefix-↭-nothing
          (map remapP (K.ein eK)) (map remapP ys) s
          (Perm.↭-sym s↭std) nothing-on-std

      nothing-on-ein-c
        : extract-prefix
            (Hypergraph.ein (hComposeP G K bdy-eq) (G.nE ↑ʳ eK)) s ≡ nothing
      nothing-on-ein-c =
        subst (λ ks → extract-prefix ks s ≡ nothing)
              (sym (ein-c-inj₂-red eK))
              nothing-on-s

      -- `edge-step K ys eK` reduces (via `eq-K`) to `ys`.
      reduce-to-id : edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK) ≡ s
      reduce-to-id =
        edge-step-nothing (hComposeP G K bdy-eq) s (G.nE ↑ʳ eK) nothing-on-ein-c

  process-edges-↑ʳ-via-remapP
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + cn)))
        (ys : List (Fin K.nV))
    → s Perm.↭ map remapP ys
    → process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) es) s
        Perm.↭ map remapP (process-edges K es ys)
  process-edges-↑ʳ-via-remapP []       s ys s↭std = s↭std
  process-edges-↑ʳ-via-remapP (e ∷ es) s ys s↭std =
    process-edges-↑ʳ-via-remapP es (edge-step (hComposeP G K bdy-eq) s (G.nE ↑ʳ e))
      (edge-step K ys e)
      (edge-step-↑ʳ-via-remapP e s ys s↭std)

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
