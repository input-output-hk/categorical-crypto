{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Phase 3.5f Step 4 (start) — discharging `decode-attempt-Linear` for
-- translated hypergraphs, plus the derivation of the total `decode`.
--
-- The cospan-form algorithm `decode-attempt` returns a `Maybe` (see
-- `Decode.agda`).  We discharge the `Maybe` for hypergraphs of the
-- form `⟪ f ⟫` by induction on the term `f`.  Each smart-constructor
-- case is a separate lemma.  Status:
--
--   * Constructive (no postulate):
--     - `decode-attempt-hEmpty` : `decode-attempt hEmpty ≡ just _`
--       (concrete lists ⇒ algorithm reduces by `refl`).
--     - `decode-attempt-hVar`   : `decode-attempt (hVar x) ≡ just _`
--       (singleton stack ⇒ algorithm reduces by `refl`).
--     - `decode-attempt-hSwap`  : reduces via `extract-prefix-from-↭`
--       (in `DecodeProperties.agda`) applied to `Perm.++-comm`.
--     - `decode-attempt-hGen`   : `extract-prefix-self` for the single
--       edge step, then `extract-prefix-from-↭` for the final
--       `R ++ [] ↭ R` bridge via `PermProp.++-identityʳ`.
--     - `decode-attempt-hId`    : structural recursion on `A`.
--     - `decode-attempt-subst₂` : `subst₂ refl refl` is the identity.
--
--   * Postulated (still): `hTensor`, `hCompose`.
--     These have non-trivial edge sets that require `extract-prefix`
--     to interact with `injL`/`injR`/`remap`-mapped lists.  Their
--     signatures *now take induction hypotheses* for the sub-
--     hypergraphs (matching the eventual proof shape); the bodies
--     remain postulated pending the disjoint-injection lifting
--     lemmas.
--
-- Composing the per-case lemmas gives a constructive proof of
-- `decode-attempt-Linear f : ∃ t. decode-attempt ⟪ f ⟫ ≡ just t`,
-- from which the total `decode` is defined as the projection.
-- `decode` and `bridge` live here (rather than in `Decoder.agda`) so
-- that `DecodeRoundtrip.agda` can refer to them without going through
-- `Decoder.agda` (avoiding a module cycle).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeAttempt (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; ⟪_⟫; range;
         hEmpty; hVar; hId; hGen; hSwap; hTensor; hCompose)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (decode-attempt)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-self; extract-prefix-from-↭)

open import Categories.Morphism FreeMonoidal using (_≅_)

open import Data.Fin using (_↑ˡ_; _↑ʳ_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; subst₂)

--------------------------------------------------------------------------------
-- Per-case lemmas, one for each smart constructor of `FromAPROP`.
--
-- Statement form: `∃ t. decode-attempt H ≡ just t` for the relevant
-- smart-constructor application `H`.  Inductive cases (hTensor /
-- hCompose) take the witness for the sub-hypergraphs as input.
--
-- The base cases `hEmpty` and `hVar` are *not* postulated — their
-- `dom`/`cod` are concrete enough that the algorithm reduces by `refl`.

decode-attempt-hEmpty
  : Σ[ t ∈ HomTerm (unflatten []) (unflatten []) ]
      decode-attempt hEmpty ≡ just t
decode-attempt-hEmpty = _ , refl

decode-attempt-hVar
  : ∀ (x : X)
  → Σ[ t ∈ HomTerm (unflatten (x ∷ [])) (unflatten (x ∷ [])) ]
      decode-attempt (hVar x) ≡ just t
decode-attempt-hVar x = _ , refl

--------------------------------------------------------------------------------
-- `hSwap A B`: nE = 0, dom = L ++ R, cod = R ++ L (where
-- L = map (_↑ˡ nB) (range nA), R = map (nA ↑ʳ_) (range nB)).
-- `process-all-edges` returns (dom, id) trivially since nE = 0.
-- Then `extract-exact (R ++ L) (L ++ R)` succeeds because
-- (L ++ R) ↭ (R ++ L) by stdlib's `++-comm`, and
-- `extract-prefix-from-↭` discharges the search.

decode-attempt-hSwap
  : ∀ (A B : ObjTerm)
  → Σ[ t ∈ HomTerm (unflatten (flatten A ++ flatten B))
                   (unflatten (flatten B ++ flatten A)) ]
      decode-attempt (hSwap A B) ≡ just t
decode-attempt-hSwap A B
    with extract-prefix-from-↭
           (map (_↑ˡ length (flatten B)) (range (length (flatten A)))
            ++ map (length (flatten A) ↑ʳ_) (range (length (flatten B))))
           (map (length (flatten A) ↑ʳ_) (range (length (flatten B)))
            ++ map (_↑ˡ length (flatten B)) (range (length (flatten A))))
           (PermProp.++-comm
             (map (_↑ˡ length (flatten B)) (range (length (flatten A))))
             (map (length (flatten A) ↑ʳ_) (range (length (flatten B)))))
... | p , eq rewrite eq = _ , refl

--------------------------------------------------------------------------------
-- `hGen g`: nE = 1, ein 0 = dom = L, eout 0 = cod = R (where
-- L = map (_↑ˡ nB) (range nA), R = map (nA ↑ʳ_) (range nB)).
--
-- `process-all-edges` runs the single edge:
--   `edge-step L 0` calls `extract-prefix L L`, which succeeds by
--   `extract-prefix-self`.  After the edge the stack becomes `R ++ []`.
--
-- The final `extract-exact R (R ++ [])` then needs `(R ++ []) ↭ R`,
-- discharged by `PermProp.++-identityʳ` + `extract-prefix-from-↭`.

decode-attempt-hGen
  : ∀ {A B : ObjTerm} (g : mor A B)
  → Σ[ t ∈ HomTerm (unflatten (flatten A)) (unflatten (flatten B)) ]
      decode-attempt (hGen g) ≡ just t
decode-attempt-hGen {A} {B} g
    with extract-prefix-self
           (map (_↑ˡ length (flatten B)) (range (length (flatten A))))
... | _ , eq1 rewrite eq1
    with extract-prefix-from-↭
           (map (length (flatten A) ↑ʳ_) (range (length (flatten B))) ++ [])
           (map (length (flatten A) ↑ʳ_) (range (length (flatten B))))
           (PermProp.++-identityʳ
             (map (length (flatten A) ↑ʳ_) (range (length (flatten B)))))
... | _ , eq2 rewrite eq2 = _ , refl

-- `decode-attempt-hTensor` and `decode-attempt-hCompose` are stated
-- *with* induction hypotheses for the sub-hypergraphs.  This is the
-- API that the eventual constructive proof needs — even though the
-- bodies are still postulated, the IHs are now plumbed through
-- `decode-attempt-Linear` (so a future proof can use them without
-- changing the call sites again).
--
-- The proof shape (sketch):
--   * `process-all-edges` factors via stdlib's
--     `Invariant.range-++ : range (n + m) ≡ map _↑ˡ_ (range n) ++ map _↑ʳ_ (range m)`
--     and a `process-edges-++` decomposition (provable by induction).
--   * Each branch (G's edges then K's) interacts only with one side
--     of the disjoint-injection stack.  This requires lifting lemmas
--     analogous to `extract-prefix-from-↭` but specialised to
--     `extract-prefix (map injL ks) (map injL xs ++ map injR ys)` —
--     the proofs reuse `disj-L-R` (Invariant) to skip the wrong-side
--     prefix and `inject+-inj`/`raise-inj` to thread through the
--     matching side.
--   * The final `extract-exact cod final-stack` succeeds by
--     `extract-exact-self` on the (provably equal) `cod`.

postulate
  decode-attempt-hTensor
    : ∀ {As Bs Cs Ds : List X}
        (G : Hypergraph FlatGen As Bs) (K : Hypergraph FlatGen Cs Ds)
    → (∃[ tG ] decode-attempt G ≡ just tG)
    → (∃[ tK ] decode-attempt K ≡ just tK)
    → Σ[ t ∈ HomTerm (unflatten (As ++ Cs)) (unflatten (Bs ++ Ds)) ]
        decode-attempt (hTensor G K) ≡ just t

  decode-attempt-hCompose
    : ∀ {As Bs Cs : List X}
        (G : Hypergraph FlatGen As Bs) (K : Hypergraph FlatGen Bs Cs)
    → (∃[ tG ] decode-attempt G ≡ just tG)
    → (∃[ tK ] decode-attempt K ≡ just tK)
    → Σ[ t ∈ HomTerm (unflatten As) (unflatten Cs) ]
        decode-attempt (hCompose G K) ≡ just t

--------------------------------------------------------------------------------
-- `subst₂` transport: pure type-level shuffling.  When both equalities
-- are `refl`, `subst₂` is the identity, so the input pair is the output.

decode-attempt-subst₂
  : ∀ {As Bs As' Bs' : List X} (H : Hypergraph FlatGen As Bs)
      (eq-As : As ≡ As') (eq-Bs : Bs ≡ Bs')
  → Σ[ t ∈ HomTerm (unflatten As) (unflatten Bs) ] decode-attempt H ≡ just t
  → Σ[ t' ∈ HomTerm (unflatten As') (unflatten Bs') ]
      decode-attempt (subst₂ (Hypergraph FlatGen) eq-As eq-Bs H) ≡ just t'
decode-attempt-subst₂ H refl refl (t , p) = (t , p)

--------------------------------------------------------------------------------
-- `hId A`: structural recursion on `A`.  `hId unit = hEmpty`,
-- `hId (Var x) = hVar x`, `hId (A ⊗₀ B) = hTensor (hId A) (hId B)`.
-- The first two are constructive base cases; the tensor case
-- delegates to the (still-postulated) `decode-attempt-hTensor`.

decode-attempt-hId
  : ∀ (A : ObjTerm)
  → Σ[ t ∈ HomTerm (unflatten (flatten A)) (unflatten (flatten A)) ]
      decode-attempt (hId A) ≡ just t
decode-attempt-hId unit       = decode-attempt-hEmpty
decode-attempt-hId (Var x)    = decode-attempt-hVar x
decode-attempt-hId (A ⊗₀ B)   =
  decode-attempt-hTensor (hId A) (hId B)
    (decode-attempt-hId A) (decode-attempt-hId B)

--------------------------------------------------------------------------------
-- Constructive proof of `decode-attempt-Linear` for translated
-- hypergraphs, by induction on the term `f`.  This is the function
-- `Decoder.agda` uses to define the total `decode`.
--
-- Each branch unfolds `⟪_⟫` and applies the corresponding per-case
-- lemma above.  The unitor / associator branches (`λ⇒`, `λ⇐`, `ρ⇒`,
-- `ρ⇐`, `α⇒`, `α⇐`) translate via `subst₂` on `hId`, so they go
-- through `decode-attempt-subst₂`.

decode-attempt-Linear
  : ∀ {A B} (f : HomTerm A B)
  → Σ[ t ∈ HomTerm (unflatten (flatten A)) (unflatten (flatten B)) ]
      decode-attempt ⟪ f ⟫ ≡ just t
decode-attempt-Linear (Agen g)  = decode-attempt-hGen g
decode-attempt-Linear (id {A})  = decode-attempt-hId A
decode-attempt-Linear (g ∘ f)   =
  decode-attempt-hCompose ⟪ f ⟫ ⟪ g ⟫
    (decode-attempt-Linear f) (decode-attempt-Linear g)
decode-attempt-Linear (f ⊗₁ g)  =
  decode-attempt-hTensor ⟪ f ⟫ ⟪ g ⟫
    (decode-attempt-Linear f) (decode-attempt-Linear g)
decode-attempt-Linear (λ⇒ {A})  = decode-attempt-hId A
decode-attempt-Linear (λ⇐ {A})  = decode-attempt-hId A
decode-attempt-Linear (ρ⇒ {A})  =
  decode-attempt-subst₂ (hId (A ⊗₀ unit)) refl (++-identityʳ (flatten A))
    (decode-attempt-hId (A ⊗₀ unit))
decode-attempt-Linear (ρ⇐ {A})  =
  decode-attempt-subst₂ (hId (A ⊗₀ unit)) (++-identityʳ (flatten A)) refl
    (decode-attempt-hId (A ⊗₀ unit))
decode-attempt-Linear (α⇒ {A} {B} {C}) =
  decode-attempt-subst₂ (hId ((A ⊗₀ B) ⊗₀ C))
    refl (++-assoc (flatten A) (flatten B) (flatten C))
    (decode-attempt-hId ((A ⊗₀ B) ⊗₀ C))
decode-attempt-Linear (α⇐ {A} {B} {C}) =
  decode-attempt-subst₂ (hId ((A ⊗₀ B) ⊗₀ C))
    (++-assoc (flatten A) (flatten B) (flatten C)) refl
    (decode-attempt-hId ((A ⊗₀ B) ⊗₀ C))
decode-attempt-Linear (σ {A} {B}) = decode-attempt-hSwap A B

--------------------------------------------------------------------------------
-- The total `decode` and the `bridge` it commutes with, derived from
-- `decode-attempt-Linear`.

decode
  : ∀ {A B} (f : HomTerm A B)
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decode f = proj₁ (decode-attempt-Linear f)

-- `bridge`: `f` composed with the unflatten-flatten coherence isos
-- on each side.  When `flatten`/`unflatten` were definitional inverses
-- this would just be `f`; under propositional/iso-only inversion we
-- need the explicit bridge.
bridge
  : ∀ {A B}
  → HomTerm A B
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
bridge {A} {B} f =
  _≅_.from (unflatten-flatten-≈ B) ∘ f ∘ _≅_.to (unflatten-flatten-≈ A)
