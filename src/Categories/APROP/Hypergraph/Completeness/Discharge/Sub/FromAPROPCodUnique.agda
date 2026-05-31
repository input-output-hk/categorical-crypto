{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Uniqueness of the codomain (and domain) interface of FromAPROP-translated
-- hypergraphs.
--
-- For every APROP term `f : HomTerm A B`, the FromAPROP translation
-- `⟪ f ⟫F : Hypergraph FlatGen` has a `Unique` codomain vertex-list
-- (`⟪_⟫F-cod-unique`) and a `Unique` domain vertex-list
-- (`⟪_⟫F-dom-unique`).
--
-- This is the FromAPROP (`hCompose`, UNPRUNED composition) analogue of
-- `Categories.APROP.Hypergraph.HomTermInvariant`'s `⟪_⟫-cod-unique` /
-- `⟪_⟫-dom-unique`, which prove the same facts for the Translation
-- (`hComposeP`, pruned composition).
--
-- Proof by structural induction on `f`.  All cases except `_∘_` follow
-- directly from the existing `hX-{dom,cod}-Unique` lemmas in
-- `Invariant.agda` together with `map⁺` / `++⁺`.  The `_∘_` case reduces
-- to showing the FromAPROP `hCompose` positional remap
-- (`hCompose-impl.remap`) injective; this holds because the right
-- operand's `cod` (`gs = ⟪h⟫F.cod`) is `Unique` (an IH).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FromAPROPCodUnique
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using ( FlatGen; flatten; range
        ; hId; hTensor; hGen; hSwap; hCompose
        ; module hCompose-impl )
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Invariant sig
  using ( hId-dom-Unique; hId-cod-Unique
        ; hSwap-dom-Unique; hSwap-cod-Unique
        ; hGen-dom-Unique; hGen-cod-Unique
        ; inject+-inj; raise-inj; disj-L-R )
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.AllPairs as AllPairs
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Data.Nat using (ℕ; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Local Fin-injectivity / disjointness helpers (standalone, so the
-- implicit Fin sizes are always inferable from the arguments).

private
  ↑ˡ-inj′ : ∀ {m} (k : ℕ) {i j : Fin m} → i ↑ˡ k ≡ j ↑ˡ k → i ≡ j
  ↑ˡ-inj′ {m} k {i} {j} eq
    with splitAt-↑ˡ m i k | splitAt-↑ˡ m j k | cong (splitAt m) eq
  ... | i-red | j-red | split-eq = inj₁-inj (trans (sym i-red) (trans split-eq j-red))
    where
      inj₁-inj : ∀ {X Y : Set} {x y : X} → inj₁ {B = Y} x ≡ inj₁ y → x ≡ y
      inj₁-inj refl = refl

  ↑ʳ-inj′ : ∀ (m : ℕ) {n} {i j : Fin n} → m ↑ʳ i ≡ m ↑ʳ j → i ≡ j
  ↑ʳ-inj′ m {n} {i} {j} eq
    with splitAt-↑ʳ m n i | splitAt-↑ʳ m n j | cong (splitAt m) eq
  ... | i-red | j-red | split-eq = inj₂-inj (trans (sym i-red) (trans split-eq j-red))
    where
      inj₂-inj : ∀ {X Y : Set} {x y : Y} → inj₂ {A = X} x ≡ inj₂ y → x ≡ y
      inj₂-inj refl = refl

  ↑ˡ-↑ʳ-disj : ∀ {m} (k : ℕ) (i : Fin m) (j : Fin k) → i ↑ˡ k ≡ m ↑ʳ j → ⊥
  ↑ˡ-↑ʳ-disj {m} k i j eq
    with splitAt-↑ˡ m i k | splitAt-↑ʳ m k j | cong (splitAt m) eq
  ... | i-red | j-red | split-eq = case-absurd (trans (sym i-red) (trans split-eq j-red))
    where
      case-absurd : ∀ {X Y : Set} {x : X} {y : Y} → inj₁ x ≡ inj₂ y → ⊥
      case-absurd ()

--------------------------------------------------------------------------------
-- Injectivity of the FromAPROP positional remap `hCompose-impl.remap'`.
--
-- We work directly with the `remap'`/`injL`/`injR` of a fixed
-- `hCompose-impl G K bdy` so that the conclusion is about the *actual*
-- `hC.remap`, not a structurally-identical copy.

module remap-inj-impl (G K : Hypergraph FlatGen) (bdy : codL G ≡ domL K) where

  module G = Hypergraph G
  module K = Hypergraph K
  open hCompose-impl G K bdy

  -- Head of a Unique list differs from every tail element.
  uniq-head : ∀ {a} {A : Set a} {x : A} {xs : List A}
            → Unique (x ∷ xs) → All (x ≢_) xs
  uniq-head (h AllPairs.∷ _) = h

  uniq-tail : ∀ {a} {A : Set a} {x : A} {xs : List A}
            → Unique (x ∷ xs) → Unique xs
  uniq-tail (_ AllPairs.∷ t) = t

  -- The head image `injL g` is never produced by `remap' ks gs` provided
  -- `g` is absent from `gs`.  (If the recursion ever returns `injL g'`,
  -- then `g' ∈ gs`, so `g' ≢ g`, so `injL g' ≢ injL g`; the `injR` outputs
  -- differ from `injL g` by disjointness.)
  injL≢tail
    : (g : Fin G.nV) (ks : List (Fin K.nV)) (gs : List (Fin G.nV))
    → All (g ≢_) gs
    → ∀ v → remap' ks gs v ≢ injL g
  injL≢tail g []        _          _              v eq =
    ↑ˡ-↑ʳ-disj K.nV g v (sym eq)
  injL≢tail g (_ ∷ _)   []         _              v eq =
    ↑ˡ-↑ʳ-disj K.nV g v (sym eq)
  injL≢tail g (k ∷ ks)  (g' ∷ gs)  (g≢g' ∷ rest)  v eq with v Fin.≟ k
  ... | yes _ = g≢g' (sym (↑ˡ-inj′ K.nV eq))
  ... | no  _ = injL≢tail g ks gs rest v eq

  -- Global injectivity of `remap' ks gs`, given `Unique gs`.
  remap'-inj
    : (ks : List (Fin K.nV)) (gs : List (Fin G.nV))
    → Unique gs
    → ∀ {v v'} → remap' ks gs v ≡ remap' ks gs v' → v ≡ v'
  remap'-inj []        _         _   eq = ↑ʳ-inj′ G.nV eq
  remap'-inj (_ ∷ _)   []        _   eq = ↑ʳ-inj′ G.nV eq
  remap'-inj (k ∷ ks)  (g ∷ gs)  ug  {v} {v'} eq with v Fin.≟ k | v' Fin.≟ k
  ... | yes p | yes q = trans p (sym q)
  ... | yes p | no  _ =
        ⊥-elim (injL≢tail g ks gs (uniq-head ug) v' (sym eq))
  ... | no  _ | yes q =
        ⊥-elim (injL≢tail g ks gs (uniq-head ug) v eq)
  ... | no  _ | no  _ =
        remap'-inj ks gs (uniq-tail ug) eq

  -- Injectivity of the actual `remap = remap' K.dom G.cod`.
  remap-inj
    : Unique G.cod
    → ∀ {v v'} → remap v ≡ remap v' → v ≡ v'
  remap-inj ucod eq = remap'-inj K.dom G.cod ucod eq

--------------------------------------------------------------------------------
-- `⟪ f ⟫F.dom` is Unique for every APROP term.

⟪_⟫F-dom-unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.dom ⟪ f ⟫F)

⟪ Agen g ⟫F-dom-unique = hGen-dom-Unique g
⟪ id {A} ⟫F-dom-unique = hId-dom-Unique A
⟪ g ∘ h ⟫F-dom-unique =
  -- ⟪g ∘ h⟫F = hCompose ⟪h⟫F ⟪g⟫F bdy; dom = map injL ⟪h⟫F.dom.
  Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫F-dom-unique h)
⟪ f ⊗₁ g ⟫F-dom-unique =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫F-dom-unique f))
    (Uniq-Prop.map⁺ (raise-inj   _) (⟪_⟫F-dom-unique g))
    (disj-L-R (Hypergraph.dom ⟪ f ⟫F) (Hypergraph.dom ⟪ g ⟫F))
⟪ λ⇒ {A} ⟫F-dom-unique = hId-dom-Unique A
⟪ λ⇐ {A} ⟫F-dom-unique = hId-dom-Unique A
⟪ ρ⇒ {A} ⟫F-dom-unique = hId-dom-Unique (A ⊗₀ unit)
⟪ ρ⇐ {A} ⟫F-dom-unique = hId-dom-Unique (A ⊗₀ unit)
⟪ α⇒ {A} {B} {C} ⟫F-dom-unique = hId-dom-Unique ((A ⊗₀ B) ⊗₀ C)
⟪ α⇐ {A} {B} {C} ⟫F-dom-unique = hId-dom-Unique ((A ⊗₀ B) ⊗₀ C)
⟪ σ {A} {B} ⟫F-dom-unique = hSwap-dom-Unique A B

--------------------------------------------------------------------------------
-- `⟪ f ⟫F.cod` is Unique for every APROP term.

⟪_⟫F-cod-unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.cod ⟪ f ⟫F)

⟪ Agen g ⟫F-cod-unique = hGen-cod-Unique g
⟪ id {A} ⟫F-cod-unique = hId-cod-Unique A
⟪ g ∘ h ⟫F-cod-unique =
  -- ⟪g ∘ h⟫F = hCompose ⟪h⟫F ⟪g⟫F bdy; cod = map remap ⟪g⟫F.cod
  -- where remap = remap' ⟪g⟫F.dom ⟪h⟫F.cod.  `remap` is injective by
  -- `remap'-inj` (needs Unique ⟪h⟫F.cod, the IH on h).
  Uniq-Prop.map⁺ (RI.remap-inj (⟪_⟫F-cod-unique h)) (⟪_⟫F-cod-unique g)
  where
    bdy = trans (⟪⟫F-codL h) (sym (⟪⟫F-domL g))
    module RI = remap-inj-impl ⟪ h ⟫F ⟪ g ⟫F bdy
⟪ f ⊗₁ g ⟫F-cod-unique =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj _) (⟪_⟫F-cod-unique f))
    (Uniq-Prop.map⁺ (raise-inj   _) (⟪_⟫F-cod-unique g))
    (disj-L-R (Hypergraph.cod ⟪ f ⟫F) (Hypergraph.cod ⟪ g ⟫F))
⟪ λ⇒ {A} ⟫F-cod-unique = hId-cod-Unique A
⟪ λ⇐ {A} ⟫F-cod-unique = hId-cod-Unique A
⟪ ρ⇒ {A} ⟫F-cod-unique = hId-cod-Unique (A ⊗₀ unit)
⟪ ρ⇐ {A} ⟫F-cod-unique = hId-cod-Unique (A ⊗₀ unit)
⟪ α⇒ {A} {B} {C} ⟫F-cod-unique = hId-cod-Unique ((A ⊗₀ B) ⊗₀ C)
⟪ α⇐ {A} {B} {C} ⟫F-cod-unique = hId-cod-Unique ((A ⊗₀ B) ⊗₀ C)
⟪ σ {A} {B} ⟫F-cod-unique = hSwap-cod-Unique A B
