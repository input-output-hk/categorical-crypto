{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive discharge of the `AllFire-natural-range` field from
-- `Discharge/Sub/ProcessTermAligned.agda` (Step A in the brief).
--
-- ## Goal
--
--   `AllFire ⟪ f ⟫F (range nE_F) ⟪f⟫F.dom`
--
-- for every term `f : HomTerm A B`.  That is, the *natural* Fin order on
-- the edges of the FromAPROP-translated hypergraph fires correctly when
-- run from the natural starting stack.
--
-- ## Strategy
--
-- Structural induction on `f`.  The 11 constructors fall into three
-- groups:
--
--   * Zero-edge cases (`id`, `λ⇒`, `λ⇐`, `ρ⇒`, `ρ⇐`, `α⇒`, `α⇐`, `σ`):
--     `nE = 0` so `range 0 = []` and `AllFire H [] s = ⊤` is `tt`.
--
--   * Single-edge case (`Agen g`):  `nE = 1`, the one edge's `ein` is
--     equal to `dom`, so `extract-prefix-self` discharges directly.
--
--   * Compositional cases (`g ∘ f`, `f ⊗₁ g`):  Two lifting helpers
--     (`AllFire-via-↑ˡ-on-mixed`, `AllFire-via-↑ʳ-on-perm`, plus
--     hCompose variants) move AllFire on a sub-hypergraph to AllFire on
--     the composite, mirroring the per-edge lifts in `DecodeAttempt`.
--     These use the same machinery (`extract-prefix-↑ˡ-on-mixed-just`,
--     `extract-prefix-via-injective-just`, etc.) but lift to AllFire
--     rather than to a Maybe-success.
--
-- ## Status
--
-- Fully constructive; no postulates, no residual fields.  The hardest
-- piece is the K-side lifting through `remap` for `hCompose`, which
-- requires `Lin.hCompose-Linear-utils.remap-injective` (already proved
-- in `Linearity.agda`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireNatural
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using ( FlatGen; flatten; range; ⟪⟫-domL; ⟪⟫-codL
        ; hEmpty; hVar; hId; hGen; hSwap; hTensor; hCompose
        ; module hTensor-impl; module hCompose-impl)
  renaming (⟪_⟫ to ⟪_⟫F)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-elem; extract-prefix; edge-step; process-edges)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using ( extract-prefix-self
        ; extract-prefix-↑ˡ-on-mixed-just
        ; extract-prefix-↑ʳ-on-mixed-just
        ; extract-prefix-via-injective-just
        ; extract-prefix-↭-residual)
import Categories.APROP.Hypergraph.Invariant sig as Inv
open Inv using (inject+-inj; range-++)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec using (AllFire)

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ; ++-assoc; map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- ## Section 1: A characterisation of `process-edges`-stack under
-- AllFire.
--
-- If `AllFire H (e ∷ es) s` holds, then `proj₁ (process-edges H (e ∷ es)
-- s) ≡ proj₁ (process-edges H es (eout e ++ rest))` where `rest` is the
-- AllFire-residual after `e`.  This is folklore: `edge-step` reduces
-- (by `extract-prefix … ≡ just …`) to `(eout ++ rest, _)`.

AllFire-edge-step-stack
  : (H : Hypergraph FlatGen)
    (e : Fin (Hypergraph.nE H))
    (s : List (Fin (Hypergraph.nV H)))
    (rest : List (Fin (Hypergraph.nV H)))
    (p : s Perm.↭ Hypergraph.ein H e ++ rest)
  → extract-prefix (Hypergraph.ein H e) s ≡ just (rest , p)
  → proj₁ (edge-step H s e) ≡ Hypergraph.eout H e ++ rest
AllFire-edge-step-stack H e s rest p eq with extract-prefix (Hypergraph.ein H e) s
... | just _ = cong (λ x → Hypergraph.eout H e ++ proj₁ x) (just-extract eq)
  where
    just-extract : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
    just-extract refl = refl

-- AllFire is permutation-invariant on the starting stack (only the
-- "extract-prefix outputs" change shape; the success structure is
-- preserved because `extract-prefix-↭-residual` gives a residual
-- permutation).
AllFire-resp-↭
  : (H : Hypergraph FlatGen) (es : List (Fin (Hypergraph.nE H)))
    (s₁ s₂ : List (Fin (Hypergraph.nV H)))
  → s₁ Perm.↭ s₂
  → AllFire H es s₁
  → AllFire H es s₂
AllFire-resp-↭ H []       s₁ s₂ _   _   = tt
AllFire-resp-↭ H (e ∷ es) s₁ s₂ s↭ (rest , p , eq , af) =
  let
    -- Use `extract-prefix-↭-residual` to obtain a successful extract
    -- on `s₂` with a residual `rest'` that permutes from `rest`.
    step = extract-prefix-↭-residual (Hypergraph.ein H e) s₂ rest
                                       (Perm.↭-trans (Perm.↭-sym s↭) p)
    rest' = proj₁ step
    p₂    = proj₁ (proj₂ step)
    eq₂   = proj₁ (proj₂ (proj₂ step))
    rest↭rest' = proj₂ (proj₂ (proj₂ step))

    -- Lift the recursive AllFire to the new residual.
    af₂   = AllFire-resp-↭ H es (Hypergraph.eout H e ++ rest)
                                  (Hypergraph.eout H e ++ rest')
                                  (PermProp.++⁺ˡ (Hypergraph.eout H e) rest↭rest')
                                  af
  in rest' , p₂ , eq₂ , af₂

--------------------------------------------------------------------------------
-- ## Section 2: Helper — AllFire on `map (_↑ˡ K.nE) es` for `hTensor`.
--
-- Given `AllFire G es-G xs-G`, we lift to AllFire on the corresponding
-- G-edges in `hTensor G K`, starting from `map injL xs-G ++ map injR ys`.
--
-- The proof is a direct induction on `es-G`.  Each step uses
-- `extract-prefix-↑ˡ-on-mixed-just` to lift the G-side success, and
-- bridges the resulting "extract" output to the form Agda expects via
-- `subst` against `ein-c-inj₁-red`.

module _ (G K : Hypergraph FlatGen) where

  private
    module G = Hypergraph G
    module K = Hypergraph K
    module hT-impl = hTensor-impl G K

  -- Lifted edge-step shape on the G-side:
  -- `eout-c (eG ↑ˡ K.nE) ++ (map injL rest-G ++ map injR ys)`
  -- ≡ `map injL (G.eout eG ++ rest-G) ++ map injR ys`.
  -- Lifted directly from `DecodeAttempt.edge-step-↑ˡ-on-mixed-just`'s
  -- `list-eq`, but kept inline so we don't depend on the module.

  AllFire-hTensor-G-step
    : ∀ (eG : Fin G.nE)
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
        (rest-G : List (Fin G.nV))
        (p-G : xs-G Perm.↭ G.ein eG ++ rest-G)
    → extract-prefix (G.ein eG) xs-G ≡ just (rest-G , p-G)
    → Σ[ rest' ∈ List (Fin (G.nV + K.nV)) ]
      Σ[ p' ∈
          (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
          Perm.↭
          (Hypergraph.ein (hTensor G K) (eG ↑ˡ K.nE) ++ rest')
        ]
        extract-prefix (Hypergraph.ein (hTensor G K) (eG ↑ˡ K.nE))
                       (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
        ≡ just (rest' , p')
      × (Hypergraph.eout (hTensor G K) (eG ↑ˡ K.nE) ++ rest')
          ≡ (map (_↑ˡ K.nV) (G.eout eG ++ rest-G) ++ map (G.nV ↑ʳ_) ys)
  AllFire-hTensor-G-step eG xs-G ys rest-G p-G eq =
      _ , _ , extract-eq , out-eq
    where
      stack = map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys
      lifted-rest = map (_↑ˡ K.nV) rest-G ++ map (G.nV ↑ʳ_) ys

      -- Lift G's extract-prefix success to the mixed stack.
      extract-on-↑ˡ
        : ∃[ q ] extract-prefix (map (_↑ˡ K.nV) (G.ein eG)) stack
                   ≡ just (lifted-rest , q)
      extract-on-↑ˡ =
        extract-prefix-↑ˡ-on-mixed-just K.nV (G.ein eG)
                                          xs-G ys rest-G p-G eq

      -- Transport to the algorithm's actual lookup shape via
      -- `ein-c-inj₁-red`.
      extract-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hTensor G K) (eG ↑ˡ K.nE)) stack
                 ≡ just (lifted-rest , q)
      extract-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks stack
                              ≡ just (lifted-rest , q))
              (sym (hT-impl.ein-c-inj₁-red eG))
              extract-on-↑ˡ

      extract-eq
        : extract-prefix (Hypergraph.ein (hTensor G K) (eG ↑ˡ K.nE)) stack
            ≡ just (lifted-rest , proj₁ extract-on-ein-c)
      extract-eq = proj₂ extract-on-ein-c

      -- Match the eout side: list-eq (lifted from DecodeAttempt).
      out-eq : Hypergraph.eout (hTensor G K) (eG ↑ˡ K.nE) ++ lifted-rest
             ≡ map (_↑ˡ K.nV) (G.eout eG ++ rest-G) ++ map (G.nV ↑ʳ_) ys
      out-eq =
        trans (cong (_++ lifted-rest) (hT-impl.eout-c-inj₁-red eG))
        (trans (sym (++-assoc (map (_↑ˡ K.nV) (G.eout eG))
                               (map (_↑ˡ K.nV) rest-G)
                               (map (G.nV ↑ʳ_) ys)))
               (cong (_++ map (G.nV ↑ʳ_) ys)
                     (sym (map-++ (_↑ˡ K.nV) (G.eout eG) rest-G))))

  -- AllFire-lifting on the G-side: given G's AllFire, conclude
  -- AllFire for the G-block of edges in hTensor.
  --
  -- Note: AllFire's recursion is in terms of `eout ++ rest`.  After one
  -- step, the lifted residual `map injL (G.eout eG ++ rest-G) ++ map
  -- injR ys` exactly matches the form for the recursive call, so the
  -- induction goes through.
  AllFire-↑ˡ-on-mixed
    : ∀ (es : List (Fin G.nE))
        (xs-G : List (Fin G.nV))
        (ys : List (Fin K.nV))
    → AllFire G es xs-G
    → AllFire (hTensor G K)
              (map (_↑ˡ K.nE) es)
              (map (_↑ˡ K.nV) xs-G ++ map (G.nV ↑ʳ_) ys)
  AllFire-↑ˡ-on-mixed []       xs-G ys _  = tt
  AllFire-↑ˡ-on-mixed (e ∷ es) xs-G ys (rest-G , p-G , eq , af-rest)
      with AllFire-hTensor-G-step e xs-G ys rest-G p-G eq
  ... | rest' , p' , extract-eq , out-eq =
        rest'
      , p'
      , extract-eq
      , subst (AllFire (hTensor G K) (map (_↑ˡ K.nE) es))
              (sym out-eq)
              (AllFire-↑ˡ-on-mixed es (G.eout e ++ rest-G) ys af-rest)

--------------------------------------------------------------------------------
-- ## Section 3: Helper — AllFire on `map (G.nE ↑ʳ_) es` for `hTensor`
-- under a permutation invariant on the stack.
--
-- This is the K-side analogue.  Unlike the G-side, K's eouts get
-- *prepended* to the front of the stack (not interleaved with `map
-- injL`), so the standard form is preserved only up to a permutation.
-- The proof structure mirrors `DecodeAttempt.edge-step-↑ʳ-on-perm` and
-- `process-edges-↑ʳ-on-perm`.

  AllFire-hTensor-K-step
    : ∀ (eK : Fin K.nE)
        (s : List (Fin (G.nV + K.nV)))
        (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
        (rest-K : List (Fin K.nV))
        (p-K : ys Perm.↭ K.ein eK ++ rest-K)
    → extract-prefix (K.ein eK) ys ≡ just (rest-K , p-K)
    → s Perm.↭ map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys
    → Σ[ rest' ∈ List (Fin (G.nV + K.nV)) ]
      Σ[ p' ∈
          s Perm.↭ (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK) ++ rest')
        ]
        extract-prefix (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK)) s
        ≡ just (rest' , p')
      × (Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK) ++ rest')
          Perm.↭
        (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) (K.eout eK ++ rest-K))
  AllFire-hTensor-K-step eK s xs ys rest-K p-K eq-K s↭std =
    rest' , p'-final , extract-eq , out-perm
    where
      open Perm.PermutationReasoning
      L     = map (_↑ˡ K.nV)  xs
      R-pre = map (G.nV ↑ʳ_)  (K.ein  eK)
      R-out = map (G.nV ↑ʳ_)  (K.eout eK)
      R-rst = map (G.nV ↑ʳ_)  rest-K

      -- Shuffle s to expose `R-pre` at the front.
      s↭shuffled : s Perm.↭ R-pre ++ (L ++ R-rst)
      s↭shuffled = begin
        s
          ↭⟨ s↭std ⟩
        L ++ map (G.nV ↑ʳ_) ys
          ↭⟨ PermProp.++⁺ˡ L (PermProp.map⁺ (G.nV ↑ʳ_) p-K) ⟩
        L ++ map (G.nV ↑ʳ_) (K.ein eK ++ rest-K)
          ≡⟨ cong (L ++_) (map-++ (G.nV ↑ʳ_) (K.ein eK) rest-K) ⟩
        L ++ (R-pre ++ R-rst)
          ≡⟨ sym (++-assoc L R-pre R-rst) ⟩
        (L ++ R-pre) ++ R-rst
          ↭⟨ PermProp.++⁺ʳ R-rst (PermProp.++-comm L R-pre) ⟩
        (R-pre ++ L) ++ R-rst
          ≡⟨ ++-assoc R-pre L R-rst ⟩
        R-pre ++ (L ++ R-rst)
          ∎

      extract-step
        : ∃[ r ] ∃[ p ] extract-prefix R-pre s ≡ just (r , p)
                       × (L ++ R-rst) Perm.↭ r
      extract-step =
        extract-prefix-↭-residual R-pre s (L ++ R-rst) s↭shuffled

      rest' = proj₁ extract-step
      p-extract = proj₁ (proj₂ extract-step)
      eq-extract = proj₁ (proj₂ (proj₂ extract-step))
      r↭ = proj₂ (proj₂ (proj₂ extract-step))

      -- Lift through `ein-c-inj₂-red`: bundle the perm and the
      -- extract-prefix equation together so a single `subst` carries
      -- both across the change in `ks`.
      extract-bundle
        : Σ[ q ∈ s Perm.↭ (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK) ++ rest') ]
            extract-prefix (Hypergraph.ein (hTensor G K) (G.nE ↑ʳ eK)) s
              ≡ just (rest' , q)
      extract-bundle =
        subst (λ ks → Σ[ q ∈ s Perm.↭ (ks ++ rest') ]
                        extract-prefix ks s ≡ just (rest' , q))
              (sym (hT-impl.ein-c-inj₂-red eK))
              (p-extract , eq-extract)

      p'-final = proj₁ extract-bundle
      extract-eq = proj₂ extract-bundle

      -- Output permutation: eout-c output ++ rest' ↭ L ++ R-out ++ R-rst.
      eout-c-↦-R-out
        : Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK) ≡ R-out
      eout-c-↦-R-out = hT-impl.eout-c-inj₂-red eK

      out-perm
        : (Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK) ++ rest')
          Perm.↭ (L ++ map (G.nV ↑ʳ_) (K.eout eK ++ rest-K))
      out-perm = begin
        Hypergraph.eout (hTensor G K) (G.nE ↑ʳ eK) ++ rest'
          ≡⟨ cong (_++ rest') eout-c-↦-R-out ⟩
        R-out ++ rest'
          ↭⟨ PermProp.++⁺ˡ R-out (Perm.↭-sym r↭) ⟩
        R-out ++ (L ++ R-rst)
          ≡⟨ sym (++-assoc R-out L R-rst) ⟩
        (R-out ++ L) ++ R-rst
          ↭⟨ PermProp.++⁺ʳ R-rst (PermProp.++-comm R-out L) ⟩
        (L ++ R-out) ++ R-rst
          ≡⟨ ++-assoc L R-out R-rst ⟩
        L ++ (R-out ++ R-rst)
          ≡⟨ cong (L ++_) (sym (map-++ (G.nV ↑ʳ_) (K.eout eK) rest-K)) ⟩
        L ++ map (G.nV ↑ʳ_) (K.eout eK ++ rest-K)
          ∎

  AllFire-↑ʳ-on-perm
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + K.nV)))
        (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
    → AllFire K es ys
    → s Perm.↭ map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) ys
    → AllFire (hTensor G K) (map (G.nE ↑ʳ_) es) s
  AllFire-↑ʳ-on-perm []       s xs ys _  _ = tt
  AllFire-↑ʳ-on-perm (e ∷ es) s xs ys (rest-K , p-K , eq , af-rest) s↭std
      with AllFire-hTensor-K-step e s xs ys rest-K p-K eq s↭std
  ... | rest' , p' , extract-eq , out-perm =
        rest'
      , p'
      , extract-eq
      , AllFire-resp-↭ (hTensor G K) (map (G.nE ↑ʳ_) es)
                       (map (_↑ˡ K.nV) xs ++ map (G.nV ↑ʳ_) (K.eout e ++ rest-K))
                       (Hypergraph.eout (hTensor G K) (G.nE ↑ʳ e) ++ rest')
                       (Perm.↭-sym out-perm)
                       (AllFire-↑ʳ-on-perm es _ xs (K.eout e ++ rest-K) af-rest Perm.refl)

--------------------------------------------------------------------------------
-- ## Section 4: AllFire under `_++_`.
--
-- `AllFire H (es1 ++ es2) s` iff `AllFire H es1 s` and `AllFire H es2 s'`
-- where `s'` is the residual stack after `es1`.
--
-- We need the "right-to-left" direction with a refinement: as long as
-- we can produce an AllFire witness on `es2` for the *true* residual
-- (computed by `process-edges`), the conjunction lifts.
--
-- Since `process-edges H (e ∷ es) s = process-edges H es (eout e ++
-- rest)` under AllFire of the head, we don't need a separate
-- `process-edges`-stack characterisation — the induction threads
-- through.

AllFire-++
  : (H : Hypergraph FlatGen)
    (es₁ es₂ : List (Fin (Hypergraph.nE H)))
    (s : List (Fin (Hypergraph.nV H)))
    (af₁ : AllFire H es₁ s)
  → AllFire H es₂ (proj₁ (process-edges H es₁ s))
  → AllFire H (es₁ ++ es₂) s
AllFire-++ H []       es₂ s _  af₂ = af₂
AllFire-++ H (e ∷ es) es₂ s (rest , p , eq , af-rest) af₂ =
    rest , p , eq
  , AllFire-++ H es es₂ (Hypergraph.eout H e ++ rest) af-rest
      (subst (AllFire H es₂) bridge-eq af₂)
  where
    just-extract : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
    just-extract refl = refl

    -- The `proj₁ (process-edges H (e ∷ es) s)` matches
    -- `proj₁ (process-edges H es (eout ++ rest))` after edge-step's
    -- success reduction.
    bridge-eq
      : proj₁ (process-edges H (e ∷ es) s)
      ≡ proj₁ (process-edges H es (Hypergraph.eout H e ++ rest))
    bridge-eq rewrite eq = refl

--------------------------------------------------------------------------------
-- ## Section 5: AllFire under `map` of an injective function.
--
-- Variant for `hCompose`'s K-side: stack `↭ map remap ys`, K-edges
-- lifted to `map (G.nE ↑ʳ_) es`.  Uses `extract-prefix-via-injective-just`
-- with `f = remap` (whose injectivity comes from
-- `Lin.hCompose-Linear-utils.remap-injective`, requiring Linear G + K).

module _
  (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  (lin-G : Lin.Linear G) (lin-K : Lin.Linear K)
  where

  private
    module G = Hypergraph G
    module K = Hypergraph K
  open Lin.hCompose-Linear-utils G K bdy-eq lin-G lin-K

  --------------------------------------------------------------------
  -- G-side: per-edge AllFire lifting on a pure-L stack `map injL xs`.

  AllFire-hCompose-G-step
    : ∀ (eG : Fin G.nE) (xs : List (Fin G.nV))
        (rest : List (Fin G.nV)) (p : xs Perm.↭ G.ein eG ++ rest)
    → extract-prefix (G.ein eG) xs ≡ just (rest , p)
    → Σ[ rest' ∈ List (Fin (G.nV + K.nV)) ]
      Σ[ p' ∈
          (map (_↑ˡ K.nV) xs)
          Perm.↭
          (Hypergraph.ein (hCompose G K bdy-eq) (eG ↑ˡ K.nE) ++ rest')
        ]
        extract-prefix (Hypergraph.ein (hCompose G K bdy-eq) (eG ↑ˡ K.nE))
                       (map (_↑ˡ K.nV) xs)
        ≡ just (rest' , p')
      × (Hypergraph.eout (hCompose G K bdy-eq) (eG ↑ˡ K.nE) ++ rest')
          ≡ (map (_↑ˡ K.nV) (G.eout eG ++ rest))
  AllFire-hCompose-G-step eG xs rest p eq = _ , _ , extract-eq , out-eq
    where
      stack = map (_↑ˡ K.nV) xs

      -- Lift G's extract via `_↑ˡ K.nV` (the L-side injection).
      extract-on-↑ˡ
        : ∃[ q ] extract-prefix (map (_↑ˡ K.nV) (G.ein eG)) stack
                   ≡ just (map (_↑ˡ K.nV) rest , q)
      extract-on-↑ˡ =
        extract-prefix-via-injective-just (_↑ˡ K.nV) (inject+-inj K.nV)
                                            (G.ein eG) xs rest p eq

      extract-on-ein-c
        : ∃[ q ] extract-prefix
                   (Hypergraph.ein (hCompose G K bdy-eq) (eG ↑ˡ K.nE)) stack
                 ≡ just (map (_↑ˡ K.nV) rest , q)
      extract-on-ein-c =
        subst (λ ks → ∃[ q ] extract-prefix ks stack
                              ≡ just (map (_↑ˡ K.nV) rest , q))
              (sym (ein-c-inj₁-red eG))
              extract-on-↑ˡ

      extract-eq
        : extract-prefix (Hypergraph.ein (hCompose G K bdy-eq) (eG ↑ˡ K.nE)) stack
            ≡ just (map (_↑ˡ K.nV) rest , proj₁ extract-on-ein-c)
      extract-eq = proj₂ extract-on-ein-c

      out-eq : Hypergraph.eout (hCompose G K bdy-eq) (eG ↑ˡ K.nE)
                 ++ map (_↑ˡ K.nV) rest
             ≡ map (_↑ˡ K.nV) (G.eout eG ++ rest)
      out-eq =
        trans (cong (_++ map (_↑ˡ K.nV) rest) (eout-c-inj₁-red eG))
              (sym (map-++ (_↑ˡ K.nV) (G.eout eG) rest))

  AllFire-↑ˡ-pure-L
    : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → AllFire G es xs
    → AllFire (hCompose G K bdy-eq)
              (map (_↑ˡ K.nE) es)
              (map (_↑ˡ K.nV) xs)
  AllFire-↑ˡ-pure-L []       xs _  = tt
  AllFire-↑ˡ-pure-L (e ∷ es) xs (rest , p , eq , af-rest)
      with AllFire-hCompose-G-step e xs rest p eq
  ... | rest' , p' , extract-eq , out-eq =
        rest'
      , p'
      , extract-eq
      , subst (AllFire (hCompose G K bdy-eq) (map (_↑ˡ K.nE) es))
              (sym out-eq)
              (AllFire-↑ˡ-pure-L es (G.eout e ++ rest) af-rest)

  --------------------------------------------------------------------
  -- K-side: per-edge AllFire lifting through `remap` with a permutation
  -- invariant on the stack.

  AllFire-hCompose-K-step
    : ∀ (eK : Fin K.nE)
        (s : List (Fin (G.nV + K.nV)))
        (ys : List (Fin K.nV))
        (rest-K : List (Fin K.nV))
        (p-K : ys Perm.↭ K.ein eK ++ rest-K)
    → extract-prefix (K.ein eK) ys ≡ just (rest-K , p-K)
    → s Perm.↭ map remap ys
    → Σ[ rest' ∈ List (Fin (G.nV + K.nV)) ]
      Σ[ p' ∈
          s Perm.↭ (Hypergraph.ein (hCompose G K bdy-eq) (G.nE ↑ʳ eK) ++ rest')
        ]
        extract-prefix (Hypergraph.ein (hCompose G K bdy-eq) (G.nE ↑ʳ eK)) s
        ≡ just (rest' , p')
      × (Hypergraph.eout (hCompose G K bdy-eq) (G.nE ↑ʳ eK) ++ rest')
          Perm.↭
        map remap (K.eout eK ++ rest-K)
  AllFire-hCompose-K-step eK s ys rest-K p-K eq-K s↭std =
    rest' , p'-final , extract-eq , out-perm
    where
      open Perm.PermutationReasoning
      R-pre = map remap (K.ein eK)
      R-out = map remap (K.eout eK)
      R-rst = map remap rest-K

      s↭shuffled : s Perm.↭ R-pre ++ R-rst
      s↭shuffled = begin
        s
          ↭⟨ s↭std ⟩
        map remap ys
          ↭⟨ PermProp.map⁺ remap p-K ⟩
        map remap (K.ein eK ++ rest-K)
          ≡⟨ map-++ remap (K.ein eK) rest-K ⟩
        R-pre ++ R-rst
          ∎

      extract-step
        : ∃[ r ] ∃[ p ] extract-prefix R-pre s ≡ just (r , p) × R-rst Perm.↭ r
      extract-step = extract-prefix-↭-residual R-pre s R-rst s↭shuffled

      rest' = proj₁ extract-step
      p-extract = proj₁ (proj₂ extract-step)
      eq-extract = proj₁ (proj₂ (proj₂ extract-step))
      r↭ = proj₂ (proj₂ (proj₂ extract-step))

      -- Lift through `ein-c-inj₂-red`.
      extract-pair
        : Σ[ q ∈ s Perm.↭ (Hypergraph.ein (hCompose G K bdy-eq) (G.nE ↑ʳ eK) ++ rest') ]
            extract-prefix (Hypergraph.ein (hCompose G K bdy-eq) (G.nE ↑ʳ eK)) s
              ≡ just (rest' , q)
      extract-pair =
        subst (λ ks → Σ[ q ∈ s Perm.↭ (ks ++ rest') ]
                        extract-prefix ks s ≡ just (rest' , q))
              (sym (ein-c-inj₂-red eK))
              (p-extract , eq-extract)

      p'-final = proj₁ extract-pair
      extract-eq = proj₂ extract-pair

      out-perm
        : (Hypergraph.eout (hCompose G K bdy-eq) (G.nE ↑ʳ eK) ++ rest')
          Perm.↭ map remap (K.eout eK ++ rest-K)
      out-perm = begin
        Hypergraph.eout (hCompose G K bdy-eq) (G.nE ↑ʳ eK) ++ rest'
          ≡⟨ cong (_++ rest') (eout-c-inj₂-red eK) ⟩
        R-out ++ rest'
          ↭⟨ PermProp.++⁺ˡ R-out (Perm.↭-sym r↭) ⟩
        R-out ++ R-rst
          ≡⟨ sym (map-++ remap (K.eout eK) rest-K) ⟩
        map remap (K.eout eK ++ rest-K)
          ∎

  AllFire-↑ʳ-via-remap
    : ∀ (es : List (Fin K.nE))
        (s : List (Fin (G.nV + K.nV)))
        (ys : List (Fin K.nV))
    → AllFire K es ys
    → s Perm.↭ map remap ys
    → AllFire (hCompose G K bdy-eq) (map (G.nE ↑ʳ_) es) s
  AllFire-↑ʳ-via-remap []       s ys _ _ = tt
  AllFire-↑ʳ-via-remap (e ∷ es) s ys (rest-K , p-K , eq , af-rest) s↭std
      with AllFire-hCompose-K-step e s ys rest-K p-K eq s↭std
  ... | rest' , p' , extract-eq , out-perm =
        rest'
      , p'
      , extract-eq
      , AllFire-resp-↭ (hCompose G K bdy-eq) (map (G.nE ↑ʳ_) es)
                       (map remap (K.eout e ++ rest-K))
                       (Hypergraph.eout (hCompose G K bdy-eq) (G.nE ↑ʳ e) ++ rest')
                       (Perm.↭-sym out-perm)
                       (AllFire-↑ʳ-via-remap es _ (K.eout e ++ rest-K) af-rest Perm.refl)

--------------------------------------------------------------------------------
-- ## Section 6: process-edges stack characterisations.
--
-- After running the G-side of `range (G.nE + K.nE)` on hTensor, the
-- stack is `map injL (proj₁ (process-edges G (range G.nE) G.dom)) ++
-- map injR K.dom`.  Symmetric for hCompose's pure-L variant.
--
-- These let us thread AllFire through the second block correctly:
-- after the G-block, the stack is in the "standard shape" needed for
-- the K-block's lifting helpers.

  -- Computed final stack for G's natural order.
process-edges-stack-G-of-hTensor
  : (G K : Hypergraph FlatGen)
    (es : List (Fin (Hypergraph.nE G))) (xs : List (Fin (Hypergraph.nV G)))
    (ys : List (Fin (Hypergraph.nV K)))
  → AllFire G es xs
  → proj₁ (process-edges (hTensor G K)
            (map (_↑ˡ Hypergraph.nE K) es)
            (map (_↑ˡ Hypergraph.nV K) xs
              ++ map (Hypergraph.nV G ↑ʳ_) ys))
  ≡ map (_↑ˡ Hypergraph.nV K) (proj₁ (process-edges G es xs))
      ++ map (Hypergraph.nV G ↑ʳ_) ys
process-edges-stack-G-of-hTensor G K []       xs ys _  = refl
process-edges-stack-G-of-hTensor G K (e ∷ es) xs ys (rest , p , eq , af-rest)
    with AllFire-hTensor-G-step G K e xs ys rest p eq
... | rest' , p' , extract-eq , out-eq
    rewrite extract-eq | out-eq
    rewrite AllFire-edge-step-stack G e xs rest p eq
    = process-edges-stack-G-of-hTensor G K es (Hypergraph.eout G e ++ rest) ys af-rest

process-edges-stack-G-of-hCompose
  : (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
    (lin-G : Lin.Linear G) (lin-K : Lin.Linear K)
    (es : List (Fin (Hypergraph.nE G))) (xs : List (Fin (Hypergraph.nV G)))
  → AllFire G es xs
  → proj₁ (process-edges (hCompose G K bdy-eq)
            (map (_↑ˡ Hypergraph.nE K) es)
            (map (_↑ˡ Hypergraph.nV K) xs))
  ≡ map (_↑ˡ Hypergraph.nV K) (proj₁ (process-edges G es xs))
process-edges-stack-G-of-hCompose G K bdy-eq lin-G lin-K []       xs _  = refl
process-edges-stack-G-of-hCompose G K bdy-eq lin-G lin-K (e ∷ es) xs
                                  (rest , p , eq , af-rest)
    with AllFire-hCompose-G-step G K bdy-eq lin-G lin-K e xs rest p eq
... | rest' , p' , extract-eq , out-eq
    rewrite extract-eq | out-eq
    rewrite AllFire-edge-step-stack G e xs rest p eq
    = process-edges-stack-G-of-hCompose G K bdy-eq lin-G lin-K es
        (Hypergraph.eout G e ++ rest) af-rest

--------------------------------------------------------------------------------
-- ## Section 7: Main theorem.
--
-- The natural Fin order on `⟪ f ⟫F`'s edges is AllFire.

AllFire-natural-range
  : ∀ {A B} (f : HomTerm A B)
  → AllFire ⟪ f ⟫F (range (Hypergraph.nE ⟪ f ⟫F))
                    (Hypergraph.dom ⟪ f ⟫F)

-- Agen g: nE = 1, the single edge's ein equals dom by definition.  So
-- AllFire reduces to `extract-prefix-self` on dom.
AllFire-natural-range {A} {B} (Agen g)
    with extract-prefix-self (Hypergraph.dom ⟪ Agen g ⟫F)
... | p , eq = [] , p , eq , tt

AllFire-natural-range (id {A}) = AllFire-natural-range-hId A
  where
    -- hId A has zero edges.  Build the AllFire witness by structural
    -- induction on A, gluing the (trivial) sub-witnesses via
    -- AllFire-↑ˡ-on-mixed + AllFire-↑ʳ-on-perm + AllFire-++.
    AllFire-natural-range-hId
      : ∀ A → AllFire (hId A) (range (Hypergraph.nE (hId A)))
                                (Hypergraph.dom (hId A))
    AllFire-natural-range-hId unit    = tt
    AllFire-natural-range-hId (Var x) = tt
    AllFire-natural-range-hId (A ⊗₀ B) =
      hTensor-glue (hId A) (hId B)
        (AllFire-natural-range-hId A)
        (AllFire-natural-range-hId B)
      where
        -- Inline of the hTensor compositional case (same pattern as
        -- `f ⊗₁ g`'s case below).  Factored locally so the `id` case
        -- compiles without forward reference.
        hTensor-glue
          : (F G : Hypergraph FlatGen)
          → AllFire F (range (Hypergraph.nE F)) (Hypergraph.dom F)
          → AllFire G (range (Hypergraph.nE G)) (Hypergraph.dom G)
          → AllFire (hTensor F G)
                     (range (Hypergraph.nE (hTensor F G)))
                     (Hypergraph.dom (hTensor F G))
        hTensor-glue F G af-F af-G =
            subst (λ es → AllFire (hTensor F G) es
                           (Hypergraph.dom (hTensor F G)))
                  (sym (range-++ (Hypergraph.nE F) (Hypergraph.nE G)))
                  combined-raw
          where
            module F = Hypergraph F
            module G = Hypergraph G

            af-F-lifted = AllFire-↑ˡ-on-mixed F G (range F.nE) F.dom G.dom af-F

            post-F-stack-eq =
              process-edges-stack-G-of-hTensor F G (range F.nE) F.dom G.dom af-F

            af-G-lifted =
              subst (AllFire (hTensor F G) (map (F.nE ↑ʳ_) (range G.nE)))
                    (sym post-F-stack-eq)
                    (AllFire-↑ʳ-on-perm F G (range G.nE)
                      (map (_↑ˡ G.nV) (proj₁ (process-edges F (range F.nE) F.dom))
                        ++ map (F.nV ↑ʳ_) G.dom)
                      (proj₁ (process-edges F (range F.nE) F.dom))
                      G.dom af-G Perm.refl)

            combined-raw =
              AllFire-++ (hTensor F G) (map (_↑ˡ G.nE) (range F.nE))
                                        (map (F.nE ↑ʳ_) (range G.nE))
                                        (map (_↑ˡ G.nV) F.dom ++ map (F.nV ↑ʳ_) G.dom)
                                        af-F-lifted af-G-lifted

-- λ⇒/λ⇐: ⟪ λ⇒ ⟫F = hId A, so reduce to AllFire-natural-range (id).
AllFire-natural-range (λ⇒ {A}) = AllFire-natural-range (id {A})
AllFire-natural-range (λ⇐ {A}) = AllFire-natural-range (id {A})

-- ρ⇒/ρ⇐: ⟪ ρ⇒ ⟫F = hId (A ⊗₀ unit).
AllFire-natural-range (ρ⇒ {A}) = AllFire-natural-range (id {A ⊗₀ unit})
AllFire-natural-range (ρ⇐ {A}) = AllFire-natural-range (id {A ⊗₀ unit})

-- α⇒/α⇐: ⟪ α⇒ ⟫F = hId ((A ⊗₀ B) ⊗₀ C).
AllFire-natural-range (α⇒ {A} {B} {C}) =
    AllFire-natural-range (id {(A ⊗₀ B) ⊗₀ C})
AllFire-natural-range (α⇐ {A} {B} {C}) =
    AllFire-natural-range (id {(A ⊗₀ B) ⊗₀ C})

-- σ: ⟪ σ ⟫F = hSwap A B, which has nE = 0.
AllFire-natural-range (σ {A} {B}) = tt

-- f ⊗₁ g: combine the IHs for f and g via AllFire-↑ˡ-on-mixed and
-- AllFire-↑ʳ-on-perm.
AllFire-natural-range (f ⊗₁ g) =
    subst (AllFire (hTensor ⟪ f ⟫F ⟪ g ⟫F)
                    (range (Hypergraph.nE ⟪ f ⟫F + Hypergraph.nE ⟪ g ⟫F)))
          dom-eq combined
  where
    F = ⟪ f ⟫F
    G = ⟪ g ⟫F
    module F = Hypergraph F
    module G = Hypergraph G

    af-F = AllFire-natural-range f
    af-G = AllFire-natural-range g

    -- Lift af-F to AllFire on hTensor's G-block.
    af-F-lifted
      : AllFire (hTensor F G) (map (_↑ˡ G.nE) (range F.nE))
                 (map (_↑ˡ G.nV) F.dom ++ map (F.nV ↑ʳ_) G.dom)
    af-F-lifted = AllFire-↑ˡ-on-mixed F G (range F.nE) F.dom G.dom af-F

    -- Lift af-G to AllFire on hTensor's K-block, with perm shape via
    -- the residual stack after G-edges.  The K-side helper takes a
    -- perm input, so we need to know the actual stack after F-edges.
    -- By `process-edges-stack-G-of-hTensor` applied with af-F, the
    -- post-F stack equals `map injL post-F-stack ++ map injR G.dom`.
    post-F-stack = proj₁ (process-edges F (range F.nE) F.dom)

    post-F-stack-eq
      : proj₁ (process-edges (hTensor F G)
                (map (_↑ˡ G.nE) (range F.nE))
                (map (_↑ˡ G.nV) F.dom ++ map (F.nV ↑ʳ_) G.dom))
      ≡ map (_↑ˡ G.nV) post-F-stack ++ map (F.nV ↑ʳ_) G.dom
    post-F-stack-eq =
      process-edges-stack-G-of-hTensor F G (range F.nE) F.dom G.dom af-F

    af-G-lifted
      : AllFire (hTensor F G) (map (F.nE ↑ʳ_) (range G.nE))
                 (proj₁ (process-edges (hTensor F G)
                          (map (_↑ˡ G.nE) (range F.nE))
                          (map (_↑ˡ G.nV) F.dom ++ map (F.nV ↑ʳ_) G.dom)))
    af-G-lifted =
      subst (AllFire (hTensor F G) (map (F.nE ↑ʳ_) (range G.nE)))
            (sym post-F-stack-eq)
            (AllFire-↑ʳ-on-perm F G (range G.nE)
              (map (_↑ˡ G.nV) post-F-stack ++ map (F.nV ↑ʳ_) G.dom)
              post-F-stack G.dom af-G Perm.refl)

    -- Glue via AllFire-++.
    combined-raw
      : AllFire (hTensor F G)
                 (map (_↑ˡ G.nE) (range F.nE) ++ map (F.nE ↑ʳ_) (range G.nE))
                 (map (_↑ˡ G.nV) F.dom ++ map (F.nV ↑ʳ_) G.dom)
    combined-raw =
      AllFire-++ (hTensor F G) (map (_↑ˡ G.nE) (range F.nE))
                                (map (F.nE ↑ʳ_) (range G.nE))
                                (map (_↑ˡ G.nV) F.dom ++ map (F.nV ↑ʳ_) G.dom)
                                af-F-lifted af-G-lifted

    -- Rewrite range (F.nE + G.nE) into the concatenated form, AND
    -- rewrite the starting stack: `hTensor (F.dom)` is `map injL F.dom
    -- ++ map injR G.dom` (by definition of hTensor.dom).  But the AllFire
    -- statement is in terms of `Hypergraph.dom ⟪ f ⊗₁ g ⟫F`, which by
    -- defn equals `hTensor (⟪f⟫F) (⟪g⟫F).dom = map injL F.dom ++ map
    -- injR G.dom`.  Equal definitionally; nothing to rewrite for the
    -- stack.
    combined
      : AllFire (hTensor F G)
                 (range (F.nE + G.nE))
                 (Hypergraph.dom (hTensor F G))
    combined =
      subst (λ es → AllFire (hTensor F G) es
                     (Hypergraph.dom (hTensor F G)))
            (sym (range-++ F.nE G.nE))
            combined-raw

    -- dom of `⟪ f ⊗₁ g ⟫F` = dom of `hTensor F G`.
    dom-eq : Hypergraph.dom (hTensor F G)
           ≡ Hypergraph.dom ⟪ f ⊗₁ g ⟫F
    dom-eq = refl

-- g ∘ f: combine the IHs for f and g via AllFire-↑ˡ-pure-L and
-- AllFire-↑ʳ-via-remap.
AllFire-natural-range (g ∘ f) =
    subst (AllFire (hCompose F G bdy-eq')
                    (range (Hypergraph.nE ⟪ f ⟫F + Hypergraph.nE ⟪ g ⟫F)))
          dom-eq combined
  where
    F = ⟪ f ⟫F
    G = ⟪ g ⟫F
    module F = Hypergraph F
    module G = Hypergraph G

    bdy-eq' : codL F ≡ domL G
    bdy-eq' = trans (⟪⟫-codL f) (sym (⟪⟫-domL g))

    lin-F = Lin.⟪⟫-Linear f
    lin-G = Lin.⟪⟫-Linear g

    open Lin.hCompose-Linear-utils F G bdy-eq' lin-F lin-G

    af-F = AllFire-natural-range f
    af-G = AllFire-natural-range g

    -- F-block: lifted via the pure-L injection.
    af-F-lifted
      : AllFire (hCompose F G bdy-eq')
                 (map (_↑ˡ G.nE) (range F.nE))
                 (map (_↑ˡ G.nV) F.dom)
    af-F-lifted = AllFire-↑ˡ-pure-L F G bdy-eq' lin-F lin-G
                                       (range F.nE) F.dom af-F

    -- Post-F stack: `map injL (proj₁ (process-edges F (range F.nE) F.dom))`.
    post-F-stack = proj₁ (process-edges F (range F.nE) F.dom)

    post-F-stack-eq
      : proj₁ (process-edges (hCompose F G bdy-eq')
                (map (_↑ˡ G.nE) (range F.nE))
                (map (_↑ˡ G.nV) F.dom))
      ≡ map (_↑ˡ G.nV) post-F-stack
    post-F-stack-eq =
      process-edges-stack-G-of-hCompose F G bdy-eq' lin-F lin-G
                                          (range F.nE) F.dom af-F

    -- Bridge to K-side: `map injL post-F-stack ↭ map remap G.dom`,
    -- using `post-F-stack ↭ F.cod` (which holds for the natural order
    -- on a translated hypergraph — the `decode-attempt-perm-from-just`
    -- gives this, but we need it without going through `decode-attempt`.
    -- Easier: we have AllFire on `range F.nE`, but the property
    -- `post-F-stack ↭ F.cod` requires `extract-exact F.cod post-F-stack`
    -- to succeed.  That's not a corollary of AllFire alone — it's the
    -- "final-permute" condition.  For `⟪ f ⟫F`, this holds, but it's a
    -- separate fact; we'd need `decode-attempt-Linear`'s output.
    --
    -- Use `decode-attempt-perm-from-just` (from DecodeAttempt) applied
    -- to the IH `decode-attempt-Linear f`.

    -- post-F-stack ↭ F.cod  (from decode-attempt-Linear f).
    post-F-stack-↭-cod : post-F-stack Perm.↭ F.cod
    post-F-stack-↭-cod = decode-perm-helper f
      where
        open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
          using (decode-attempt-Linear; decode-attempt-perm-from-just)
        open import Categories.APROP.Hypergraph.Completeness.Decode sig
          using (process-all-edges)
        decode-perm-helper
          : ∀ {A B} (f : HomTerm A B)
          → proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
            Perm.↭ Hypergraph.cod ⟪ f ⟫F
        decode-perm-helper f =
          let ih = decode-attempt-Linear f
              ext = decode-attempt-perm-from-just ⟪ f ⟫F ih
          in subst (Perm._↭ Hypergraph.cod ⟪ f ⟫F)
                   (cong proj₁ (sym (proj₁ (proj₂ (proj₂ ext)))))
                   (proj₂ (proj₂ (proj₂ ext)))

    bridge-perm
      : map (_↑ˡ G.nV) post-F-stack Perm.↭ map remap G.dom
    bridge-perm =
      Perm.↭-trans
        (PermProp.map⁺ (_↑ˡ G.nV) post-F-stack-↭-cod)
        (Perm.↭-reflexive (sym map-remap-K-dom))

    -- K-block: lifted via remap with the bridge perm.
    af-G-lifted-raw
      : AllFire (hCompose F G bdy-eq')
                 (map (F.nE ↑ʳ_) (range G.nE))
                 (map (_↑ˡ G.nV) post-F-stack)
    af-G-lifted-raw =
      AllFire-↑ʳ-via-remap F G bdy-eq' lin-F lin-G (range G.nE)
                            (map (_↑ˡ G.nV) post-F-stack)
                            G.dom af-G bridge-perm

    af-G-lifted
      : AllFire (hCompose F G bdy-eq')
                 (map (F.nE ↑ʳ_) (range G.nE))
                 (proj₁ (process-edges (hCompose F G bdy-eq')
                          (map (_↑ˡ G.nE) (range F.nE))
                          (map (_↑ˡ G.nV) F.dom)))
    af-G-lifted =
      subst (AllFire (hCompose F G bdy-eq') (map (F.nE ↑ʳ_) (range G.nE)))
            (sym post-F-stack-eq) af-G-lifted-raw

    -- Glue.
    combined-raw
      : AllFire (hCompose F G bdy-eq')
                 (map (_↑ˡ G.nE) (range F.nE) ++ map (F.nE ↑ʳ_) (range G.nE))
                 (map (_↑ˡ G.nV) F.dom)
    combined-raw =
      AllFire-++ (hCompose F G bdy-eq')
                  (map (_↑ˡ G.nE) (range F.nE))
                  (map (F.nE ↑ʳ_) (range G.nE))
                  (map (_↑ˡ G.nV) F.dom)
                  af-F-lifted af-G-lifted

    combined
      : AllFire (hCompose F G bdy-eq')
                 (range (F.nE + G.nE))
                 (Hypergraph.dom (hCompose F G bdy-eq'))
    combined =
      subst (λ es → AllFire (hCompose F G bdy-eq') es
                     (Hypergraph.dom (hCompose F G bdy-eq')))
            (sym (range-++ F.nE G.nE))
            combined-raw

    dom-eq : Hypergraph.dom (hCompose F G bdy-eq')
           ≡ Hypergraph.dom ⟪ g ∘ f ⟫F
    dom-eq = refl
