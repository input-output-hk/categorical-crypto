{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- De-indexed translation `⟪_⟫ : HomTerm A B → Hypergraph FlatGen`.
--
-- The translation no longer carries its boundary in the type; we expose
-- two propositional facts `⟪⟫-domL` / `⟪⟫-codL` separately.  These
-- facts are needed exactly *once*, when bridging from the algorithm's
-- output to the user-facing `HomTerm (unflatten (flatten A))
-- (unflatten (flatten B))` type.  Inside the algorithm and inside the
-- compositional / tensor constructors, no `subst` ever appears.
--
-- Highlights vs. the indexed version:
--   * `⟪ ρ⇒ {A} ⟫` is just `hId (A ⊗₀ unit)` — no `subst₂`!  The
--     boundary equation `flatten A ++ [] ≡ flatten A` is recorded as a
--     companion propositional fact.
--   * `hCompose G K` takes the K↔G boundary agreement as a *runtime
--     proof*, not as a type identity.  Composing `⟪f⟫` and `⟪g⟫` for
--     `f : HomTerm A B`, `g : HomTerm B C` provides the proof from
--     `⟪⟫-codL f` + `⟪⟫-domL g`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.FromAPROP2 (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core2

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties as Fin using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List using (List; []; _∷_; _++_; length; map; lookup)
open import Data.List.Properties
  using (map-∘; map-++; map-cong; ++-identityʳ; ++-assoc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst₂)

--------------------------------------------------------------------------------
-- Atomic flattening (same as FromAPROP).

flatten : ObjTerm → List X
flatten unit = []
flatten (A ⊗₀ B) = flatten A ++ flatten B
flatten (Var x) = x ∷ []

data FlatGen : List X → List X → Set where
  flat : ∀ {A B} → mor A B → FlatGen (flatten A) (flatten B)

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
-- Smart constructors.  None require any `subst` at the type level.

hEmpty : Hypergraph FlatGen
hEmpty = record
  { nV = 0; vlab = λ (); nE = 0
  ; ein = λ (); eout = λ (); elab = λ ()
  ; dom = []; cod = []
  }

hVar : (x : X) → Hypergraph FlatGen
hVar x = record
  { nV = 1; vlab = λ _ → x; nE = 0
  ; ein = λ (); eout = λ (); elab = λ ()
  ; dom = zero ∷ []; cod = zero ∷ []
  }

--------------------------------------------------------------------------------
-- Tensor.  No boundary index to thread; the underlying construction is
-- identical to FromAPROP.hTensor-impl modulo the absent dom-ok/cod-ok.

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

  map-via-inj : (xs : List (Fin G.nV))
              → map G.vlab xs ≡ map vlab-c (map (_↑ˡ K.nV) xs)
  map-via-inj xs = trans (sym (map-cong vlab-injL xs)) (map-∘ xs)

  map-via-raise : ∀ (xs : List (Fin K.nV))
                → map K.vlab xs ≡ map vlab-c (map (G.nV ↑ʳ_) xs)
  map-via-raise xs = trans (sym (map-cong vlab-injR xs)) (map-∘ xs)

  elab-c : (e : Fin (G.nE + K.nE))
         → FlatGen (map vlab-c (ein-c e)) (map vlab-c (eout-c e))
  elab-c e with splitAt G.nE e
  ... | inj₁ eG = subst₂ FlatGen
                    (map-via-inj (G.ein eG))
                    (map-via-inj (G.eout eG))
                    (G.elab eG)
  ... | inj₂ eK = subst₂ FlatGen
                    (map-via-raise (K.ein eK))
                    (map-via-raise (K.eout eK))
                    (K.elab eK)

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

--------------------------------------------------------------------------------
-- Identity hypergraph.

hId : (A : ObjTerm) → Hypergraph FlatGen
hId unit       = hEmpty
hId (Var x)    = hVar x
hId (A ⊗₀ B)   = hTensor (hId A) (hId B)

--------------------------------------------------------------------------------
-- Translation.  THE KEY POINT: ρ⇒/ρ⇐/α⇒/α⇐ are *plain* `hId` calls.
-- No subst₂.  The boundary fact is recorded separately below.
--
-- (Cases for `Agen`, `_∘_`, and `σ` are stubs in this prototype — they
-- require `hGen`, `hCompose`, `hSwap` constructors that are
-- straightforward de-indexed analogs of FromAPROP's; nothing surprising
-- in their de-indexed forms either.  We focus on ρ/α to show the
-- subst-elimination payoff.)

postulate
  -- Stand-ins for hGen / hCompose / hSwap whose de-indexed bodies are
  -- mechanical translations of FromAPROP's.  None of them need any
  -- subst at the type level.
  hGen     : ∀ {A B} → mor A B → Hypergraph FlatGen
  hCompose : (G K : Hypergraph FlatGen) → codL G ≡ domL K → Hypergraph FlatGen
  hSwap    : ObjTerm → ObjTerm → Hypergraph FlatGen

-- The translation, which we declare first in two pieces:
-- (1) the underlying hypergraph,
-- (2) the boundary lemmas (these are needed *for* the hCompose case
--     of (1), so we use a mutual block).

⟪_⟫ : ∀ {A B} → HomTerm A B → Hypergraph FlatGen

postulate
  -- For `g ∘ f`, the boundary proof is `codL ⟪f⟫ ≡ domL ⟪g⟫`,
  -- derivable from `⟪⟫-codL f : codL ⟪f⟫ ≡ flatten B` and
  -- `⟪⟫-domL g : domL ⟪g⟫ ≡ flatten B`.  Omitted from the prototype
  -- (mechanical induction on terms).
  ⟪g∘f⟫-boundary
    : ∀ {A B C} (f : HomTerm A B) (g : HomTerm B C)
    → codL ⟪ f ⟫ ≡ domL ⟪ g ⟫

⟪ Agen f ⟫            = hGen f
⟪ id {A} ⟫            = hId A
⟪ g ∘ f ⟫             = hCompose ⟪ f ⟫ ⟪ g ⟫ (⟪g∘f⟫-boundary f g)
⟪ f ⊗₁ g ⟫            = hTensor ⟪ f ⟫ ⟪ g ⟫
⟪ λ⇒ {A} ⟫            = hId A
⟪ λ⇐ {A} ⟫            = hId A
⟪ ρ⇒ {A} ⟫            = hId (A ⊗₀ unit)
⟪ ρ⇐ {A} ⟫            = hId (A ⊗₀ unit)
⟪ α⇒ {A} {B} {C} ⟫    = hId ((A ⊗₀ B) ⊗₀ C)
⟪ α⇐ {A} {B} {C} ⟫    = hId ((A ⊗₀ B) ⊗₀ C)
⟪ σ {A} {B} ⟫         = hSwap A B

--------------------------------------------------------------------------------
-- Boundary lemmas: relate `domL ⟪f⟫` / `codL ⟪f⟫` to `flatten A` /
-- `flatten B` propositionally.  These take the place of the type-level
-- `dom-ok`/`cod-ok` from the indexed version.  The interesting cases —
-- ρ⇒/ρ⇐/α⇒/α⇐ — are where the propositional equality `flatten A ++ []
-- ≡ flatten A` etc. now lives.  Crucially, these facts are USED ONLY
-- ONCE, when boxing the algorithm's output into the user-facing type
-- `HomTerm (unflatten (flatten A)) (unflatten (flatten B))`.

postulate
  -- Mechanical: needs `map vlab (map injL dom-of-hId-A ++ map injR dom-of-hId-B)
  --                  ≡ flatten A ++ flatten B`.
  -- Proof by `map-++` + the per-side IHs.  Exactly what `boundary-eq`
  -- did in FromAPROP — but *now propositional rather than type-level*.
  ⟪⟫-domL-tensor-hId
    : ∀ A B → domL (hTensor (hId A) (hId B)) ≡ flatten A ++ flatten B
  ⟪⟫-codL-tensor-hId
    : ∀ A B → codL (hTensor (hId A) (hId B)) ≡ flatten A ++ flatten B

⟪⟫-domL-id : ∀ A → domL (hId A) ≡ flatten A
⟪⟫-domL-id unit       = refl
⟪⟫-domL-id (Var x)    = refl
⟪⟫-domL-id (A ⊗₀ B)   = ⟪⟫-domL-tensor-hId A B

⟪⟫-codL-id : ∀ A → codL (hId A) ≡ flatten A
⟪⟫-codL-id unit       = refl
⟪⟫-codL-id (Var x)    = refl
⟪⟫-codL-id (A ⊗₀ B)   = ⟪⟫-codL-tensor-hId A B

--------------------------------------------------------------------------------
-- ρ⇒ / ρ⇐ / α⇒ / α⇐: the boundary facts now ARE the propositional
-- equations that previously required `subst₂ (Hypergraph FlatGen)`.

⟪⟫-domL-ρ⇒ : ∀ A → domL (⟪ ρ⇒ {A} ⟫) ≡ flatten (A ⊗₀ unit)
⟪⟫-domL-ρ⇒ A = ⟪⟫-domL-id (A ⊗₀ unit)

⟪⟫-codL-ρ⇒ : ∀ A → codL (⟪ ρ⇒ {A} ⟫) ≡ flatten A
⟪⟫-codL-ρ⇒ A = trans (⟪⟫-codL-id (A ⊗₀ unit)) (++-identityʳ (flatten A))
  -- ^ The `++-identityʳ` bridge that was previously inside `⟪ ρ⇒ ⟫`
  -- via `subst₂` is now just an extra `trans` step *here*, in a
  -- propositional fact that lives entirely outside the algorithm.

⟪⟫-domL-α⇒ : ∀ A B C → domL (⟪ α⇒ {A} {B} {C} ⟫) ≡ flatten ((A ⊗₀ B) ⊗₀ C)
⟪⟫-domL-α⇒ A B C = ⟪⟫-domL-id ((A ⊗₀ B) ⊗₀ C)

⟪⟫-codL-α⇒ : ∀ A B C → codL (⟪ α⇒ {A} {B} {C} ⟫) ≡ flatten (A ⊗₀ (B ⊗₀ C))
⟪⟫-codL-α⇒ A B C = trans (⟪⟫-codL-id ((A ⊗₀ B) ⊗₀ C))
                          (++-assoc (flatten A) (flatten B) (flatten C))

--------------------------------------------------------------------------------
-- The KEY payoff for the completeness pipeline.
--
-- Imagine we have a `decode-attempt : (H : Hypergraph FlatGen) →
-- Maybe (HomTerm (unflatten (domL H)) (unflatten (codL H)))`.
-- (Building it is mechanical from FromAPROP/Decode.agda.)
--
-- Compare the per-case decode-attempt-Linear obligations *before* and
-- *after* de-indexing for ρ⇒/ρ⇐/α⇒/α⇐:
--
-- BEFORE (FromAPROP-indexed, DecodeAttempt.agda lines 1242-1255):
--
--   decode-attempt-Linear (ρ⇒ {A})  =
--     decode-attempt-subst₂ (hId (A ⊗₀ unit))
--       refl (++-identityʳ (flatten A))
--       (decode-attempt-hId (A ⊗₀ unit))
--   decode-attempt-Linear (ρ⇐ {A})  = ...                  -- (3 lines)
--   decode-attempt-Linear (α⇒ {A}{B}{C}) = ...             -- (3 lines)
--   decode-attempt-Linear (α⇐ {A}{B}{C}) = ...             -- (3 lines)
--
--   plus `decode-attempt-subst₂` itself (~13 lines) and its two
--   private helpers `subst₂-Maybe-of-HomTerm-just` (~10 lines) and
--   `decode-attempt-resp-subst₂` (~8 lines), and `decode-attempt-subst₂-proj₁`
--   (~7 lines) — together ~50 lines just to handle ρ/α boundary
--   equations propagating into the `Maybe` wrapper.
--
-- AFTER (de-indexed):
--
--   -- decode-attempt itself returns a Maybe HomTerm at the *computed*
--   -- domL/codL types.  No subst on H needed since H has no boundary
--   -- index in its type.
--   decode-attempt-Linear (ρ⇒ {A})        = decode-attempt-hId (A ⊗₀ unit)
--   decode-attempt-Linear (ρ⇐ {A})        = decode-attempt-hId (A ⊗₀ unit)
--   decode-attempt-Linear (α⇒ {A}{B}{C})  = decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)
--   decode-attempt-Linear (α⇐ {A}{B}{C})  = decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)
--
-- The user-facing `decode : HomTerm A B → HomTerm (unflatten (flatten A))
-- (unflatten (flatten B))` then applies a *single* `subst` per side
-- using `⟪⟫-domL`/`⟪⟫-codL`.  That subst lives at the top, not
-- propagated through the algorithm.
--
-- Net effect on DecodeAttempt.agda: the entire `decode-attempt-subst₂`
-- machinery (~50 lines) disappears, and ρ/α cases each become a
-- one-liner.
