{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- FULL CONSTRUCTIVE DISCHARGE of `process-edges-resp-iso-stack`
-- from `CompletenessAssumptions` (`DecodeRespIso.agda` field (b)),
-- using the NEW `Perm.↭` signature (vs. the previously refuted `_≡_`).
--
-- ## Goal
--
-- Given `f, g : HomTerm A B` and an iso `⟪ f ⟫ ≅ᴴ ⟪ g ⟫` at the
-- Translation (pruned) level, show:
--
--     map (Hypergraph.vlab ⟪ f ⟫F)
--         (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
--   Perm.↭
--     map (Hypergraph.vlab ⟪ g ⟫F)
--         (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
--
-- ## Status: FULL DISCHARGE (no postulates).
--
-- The proof is straightforward: both `⟪ f ⟫F` and `⟪ g ⟫F` are Linear
-- (`⟪⟫-Linear`), so `decode-attempt-Linear` proves each
-- `process-all-edges` succeeds with a final stack that is a
-- permutation of the respective `.cod`. Composing with the boundary
-- equation `map vlab .cod ≡ flatten B` (`⟪⟫F-codL`), we obtain:
--
--     map ⟪f⟫F.vlab (final-f) ↭ flatten B
--     map ⟪g⟫F.vlab (final-g) ↭ flatten B
--
-- Hence the two vlab-mapped stacks are permutations of each other
-- via transitivity through `flatten B`.
--
-- This is exactly the multiset-level statement the algorithm
-- guarantees, and it is the strongest list-level invariant derivable
-- from the iso (the corresponding `_≡_` statement was provably false:
-- see `Discharge/Sub/StackListEq.agda` counter-example
-- `Agen φ₁ ⊗ Agen φ₂` vs `σ ∘ (Agen φ₂ ⊗ Agen φ₁) ∘ σ`).
--
-- ## Relationship to `Discharge/StackEq.agda`
--
-- The companion file `Discharge/StackEq.agda` (written for the OLD
-- `_≡_` signature) contains essentially the same constructive
-- multiset proof under the name `stack-↭-from-iso`. With the field
-- signature now returning `Perm.↭`, that proof is the entire
-- discharge - no `StackEqAssumption` sub-postulate is needed.
--
-- This file is the clean repackaging for the corrected field.
--
-- ## Constructive helpers used
--
--   * `decode-attempt-Linear`         (Lin)         — totality of
--                                                     `decode-attempt`
--                                                     on `⟪ f ⟫F`.
--   * `decode-attempt-perm-from-just` (DecodeAttempt) — extract the
--                                                     final-stack
--                                                     `↭ .cod` witness.
--   * `⟪⟫F-codL`                      (FromAPROP)   — `codL ⟪ f ⟫F ≡
--                                                     flatten B`.
--   * `PermProp.map⁺`                 (stdlib)     — `_↭_` is
--                                                     preserved by `map`.
--   * `Perm.↭-reflexive`, `Perm.↭-sym`, `Perm.trans` (stdlib).
--
-- No constructive helpers from `LinearityIso.agda` are used: the iso
-- itself is consumed only to witness it exists; the bridge to a
-- common reference (`flatten B`) is established independently on each
-- side via boundary equations.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.StackPerm
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode-attempt-Linear; decode-attempt-perm-from-just)

open import Data.List using (List; map; length)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

-- For the `eval-↭`-level rigidity lemma exposing the internal structure.
open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; id-fb; _∘-fb_; ≈-fb-trans; ≈-fb-sym)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Soundness
  using (eval-↭-comp)
open import Categories.PermuteCoherence.Rigid using (eval-rigid)
open import Categories.PermuteCoherence.Map
  using (eval-map⁺; subst₂-FinBij-≈; map⁺-↭-reflexive; ≈-fb-of-≡
        ; ∘-fb-cong; ∘-fb-assoc; ≈-fb-resp-≡)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FromAPROPCodUnique sig-dec
  using (⟪_⟫F-cod-unique)

--------------------------------------------------------------------------------
-- ## Section 1: Per-side bridge to `flatten B`.
--
-- For any term `f : HomTerm A B`, the vlab-mapped final stack of
-- `process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)` is a permutation
-- of `flatten B`. Fully constructive.

stack-↭-flatten-B
  : ∀ {A B} (f : HomTerm A B)
  → map (Hypergraph.vlab ⟪ f ⟫F)
        (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
    Perm.↭ flatten B
stack-↭-flatten-B f =
  let dal       = decode-attempt-Linear f
      perm-data = decode-attempt-perm-from-just ⟪ f ⟫F dal
      s_final   = proj₁ perm-data
      eq-proc   = proj₁ (proj₂ (proj₂ perm-data))
      s_↭_cod   = proj₂ (proj₂ (proj₂ perm-data))
      proj-eq : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
              ≡ s_final
      proj-eq = cong proj₁ eq-proc
      vlab-↭ : map (Hypergraph.vlab ⟪ f ⟫F) s_final
               Perm.↭ map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.cod ⟪ f ⟫F)
      vlab-↭ = PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫F) s_↭_cod
  in Perm.trans
       (Perm.↭-reflexive (cong (map (Hypergraph.vlab ⟪ f ⟫F)) proj-eq))
       (Perm.trans vlab-↭ (Perm.↭-reflexive (⟪⟫F-codL f)))

--------------------------------------------------------------------------------
-- ## Section 2: The discharge.
--
-- The top-level function with the exact signature of
-- `CompletenessAssumptions.process-edges-resp-iso-stack`.
--
-- The iso is consumed only for type-correctness; the conclusion
-- follows from each side's bridge to `flatten B` via transitivity.

process-edges-resp-iso-stack
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → map (Hypergraph.vlab ⟪ f ⟫F)
        (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
    Perm.↭
    map (Hypergraph.vlab ⟪ g ⟫F)
        (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
process-edges-resp-iso-stack f g _iso =
  Perm.trans (stack-↭-flatten-B f) (Perm.↭-sym (stack-↭-flatten-B g))

--------------------------------------------------------------------------------
-- ## Section 3: `eval-↭`-level rigidity exposure of `stack-↭-flatten-B`.
--
-- For ANY `perm-f : s₀ ↭ cod ⟪f⟫F` (where `s₀` is the decoder's final
-- stack `proj₁ (process-all-edges …)`), the evaluated bijection of
-- `stack-↭-flatten-B f` agrees with that of
-- `trans (map⁺ vlab perm-f) (↭-reflexive (⟪⟫F-codL f))`.
--
-- This exposes the internal structure of `stack-↭-flatten-B` purely at
-- the `eval-↭` (finite-bijection) level, WITHOUT requiring the caller
-- to know the internal `s_final`/`s↭cod`/`proj-eq` witnesses.  The proof
-- factors the internal reflexive-`proj-eq` bridge into the Fin-level
-- derivation `q = trans (↭-reflexive proj-eq) s↭cod : s₀ ↭ cod`, then
-- uses `eval-rigid` on the `Unique` codomain `cod ⟪f⟫F` to identify
-- `eval q` with `eval perm-f`; the `map vlab` relabel cancels via
-- `eval-map⁺` (the length casts coincide on both sides).

eval-stack-↭-flatten-B-rigid
  : ∀ {A B} (f : HomTerm A B)
      (perm-f : proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
                Perm.↭ Hypergraph.cod ⟪ f ⟫F)
  → eval-↭ (stack-↭-flatten-B f)
    ≈-fb eval-↭ (Perm.trans (PermProp.map⁺ (Hypergraph.vlab ⟪ f ⟫F) perm-f)
                            (Perm.↭-reflexive (⟪⟫F-codL f)))
eval-stack-↭-flatten-B-rigid f perm-f = result
  where
    vlab      = Hypergraph.vlab ⟪ f ⟫F
    cod       = Hypergraph.cod ⟪ f ⟫F
    s₀        = proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
    dal       = decode-attempt-Linear f
    perm-data = decode-attempt-perm-from-just ⟪ f ⟫F dal
    s_final   = proj₁ perm-data
    eq-proc   = proj₁ (proj₂ (proj₂ perm-data))
    s↭cod     = proj₂ (proj₂ (proj₂ perm-data))
    proj-eq : s₀ ≡ s_final
    proj-eq = cong proj₁ eq-proc
    R0 = Perm.↭-reflexive (cong (map vlab) proj-eq)
    M0 = PermProp.map⁺ vlab s↭cod
    RC = Perm.↭-reflexive (⟪⟫F-codL f)

    -- The Fin-level composite derivation s₀ ↭ cod.
    q : s₀ Perm.↭ cod
    q = Perm.trans (Perm.↭-reflexive proj-eq) s↭cod

    -- 1. eval (stack-↭-flatten-B f) = eval (trans R0 (trans M0 RC))
    --    = eval RC ∘-fb (eval M0 ∘-fb eval R0)   (re-associated).
    --    The LHS literally parenthesises as (eval RC ∘-fb eval M0) ∘-fb eval R0.
    assoc-step : eval-↭ (stack-↭-flatten-B f)
            ≈-fb eval-↭ RC ∘-fb (eval-↭ M0 ∘-fb eval-↭ R0)
    assoc-step = ∘-fb-assoc (eval-↭ RC) (eval-↭ M0) (eval-↭ R0)

    -- 2. eval RC ≈ eval RC  (trivial; named for ∘-fb-cong).
    RC≈step : eval-↭ RC ≈-fb eval-↭ RC
    RC≈step = ≈-fb-of-≡ {π = eval-↭ RC} refl

    -- 3. eval M0 ∘-fb eval R0 = eval (trans R0 M0) = eval (map⁺ vlab q)
    --    ≈ eval (map⁺ vlab perm-f)  (eval-rigid on the Unique codomain cod).
    step-map⁺ : eval-↭ M0 ∘-fb eval-↭ R0 ≡ eval-↭ (PermProp.map⁺ vlab q)
    step-map⁺ = cong (λ z → eval-↭ (Perm.trans z M0))
                     (sym (map⁺-↭-reflexive vlab proj-eq))

    -- Core rigidity at the Fin level (Unique codomain cod).
    rigid-core : eval-↭ q ≈-fb eval-↭ perm-f
    rigid-core = eval-rigid (⟪ f ⟫F-cod-unique) q perm-f

    -- inner: transport `subst₂-FinBij-≈ … rigid-core` back along the two
    -- `eval-map⁺` equalities and `step-map⁺` using `≈-fb-resp-≡`.
    inner : eval-↭ M0 ∘-fb eval-↭ R0 ≈-fb eval-↭ (PermProp.map⁺ vlab perm-f)
    inner =
      ≈-fb-resp-≡
        (trans (sym (eval-map⁺ vlab q)) (sym step-map⁺))
        (sym (eval-map⁺ vlab perm-f))
        (subst₂-FinBij-≈ (sym (length-map vlab s₀)) (sym (length-map vlab cod)) rigid-core)

    result : eval-↭ (stack-↭-flatten-B f)
             ≈-fb eval-↭ (Perm.trans (PermProp.map⁺ vlab perm-f) RC)
    result = ≈-fb-trans {π = eval-↭ (stack-↭-flatten-B f)}
                        {ρ = eval-↭ RC ∘-fb (eval-↭ M0 ∘-fb eval-↭ R0)}
                        {σ = eval-↭ RC ∘-fb eval-↭ (PermProp.map⁺ vlab perm-f)}
                        assoc-step
                        (∘-fb-cong {g = eval-↭ RC} {g′ = eval-↭ RC}
                                   {f = eval-↭ M0 ∘-fb eval-↭ R0}
                                   {f′ = eval-↭ (PermProp.map⁺ vlab perm-f)}
                                   RC≈step inner)
