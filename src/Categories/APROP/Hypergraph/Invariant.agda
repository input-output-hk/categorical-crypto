{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Invariants of APROP-translated hypergraphs.
--
-- The canonical pruned `hCompose` (Option A) relies on structural properties
-- of the translation that are universal but not captured by the record
-- fields of `Hypergraph` alone. This module collects them.
--
-- CURRENT CONTENT:
--
--   * `hId-dom-covers A` — the identity hypergraph `hId A` has its `dom`
--     covering every vertex. Needed to show `count-non (hId A).dom ≡ 0`,
--     which lets the pruned `hComposeP (⟪f⟫) (hId B)` have the same vertex
--     count as `⟪f⟫` (key to discharging `idˡ`).
--
--   * `hId-cod-covers A` — the identity's `cod` also covers all vertices
--     (same proof, same structure).
--
--   * `hId-cod≡dom A` — for an identity, dom and cod are the SAME list.
--     Proved by induction on A. Needed for the pruned `idˡ-cod-helper`
--     where we want the G/K-side boundaries to align definitionally
--     after establishing the bijection.
--
--   * `hId-dom-Unique A` — the identity's dom is Unique. Proved by
--     induction on A, combining `map⁺` and `++⁺` on Unique lists.
--
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Invariant (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Categories.APROP.Hypergraph.Prune
  using (AllIn; count-non; AllIn→count-non-zero)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ; splitAt-inject+; splitAt-raise)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Uniq-Prop
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst)

--------------------------------------------------------------------------------
-- Helper: every vertex of `G + K` is in `map injL G-dom ++ map injR K-dom`
-- provided the two sides individually cover. Phrased generically on lists.

private
  tensor-covers : ∀ {m n : ℕ} (xs : List (Fin m)) (ys : List (Fin n))
                → (∀ i → i ∈ xs) → (∀ j → j ∈ ys)
                → (∀ v → v ∈ map (inject+ n) xs ++ map (raise m) ys)
  tensor-covers {m} {n} xs ys cov-x cov-y v with splitAt m v in eq
  ... | inj₁ i = subst (_∈ _) (splitAt⁻¹-↑ˡ eq)
                       (∈-++⁺ˡ (∈-map⁺ (inject+ n) (cov-x i)))
  ... | inj₂ j = subst (_∈ _) (splitAt⁻¹-↑ʳ eq)
                       (∈-++⁺ʳ (map (inject+ n) xs) (∈-map⁺ (raise m) (cov-y j)))

--------------------------------------------------------------------------------
-- hId's dom (and cod) cover all vertices.

hId-dom-covers : ∀ A → AllIn (Hypergraph.dom (hId A))
hId-cod-covers : ∀ A → AllIn (Hypergraph.cod (hId A))

hId-dom-covers unit      = λ ()
hId-dom-covers (Var x)   = λ { zero → here refl }
hId-dom-covers (A ⊗₀ B) v =
  tensor-covers (Hypergraph.dom (hId A)) (Hypergraph.dom (hId B))
                (hId-dom-covers A) (hId-dom-covers B) v

hId-cod-covers unit      = λ ()
hId-cod-covers (Var x)   = λ { zero → here refl }
hId-cod-covers (A ⊗₀ B) v =
  tensor-covers (Hypergraph.cod (hId A)) (Hypergraph.cod (hId B))
                (hId-cod-covers A) (hId-cod-covers B) v

--------------------------------------------------------------------------------
-- Immediate corollary: `count-non (hId A).dom ≡ 0`. With the pruned
-- `hComposeP`, this means `hComposeP G (hId B)` has the same vertex count
-- as `G` (up to `+-identityʳ`) — the cornerstone of `idˡ`.

hId-count-non-dom : ∀ A → count-non (Hypergraph.dom (hId A)) ≡ 0
hId-count-non-dom A = AllIn→count-non-zero (hId-dom-covers A)

hId-count-non-cod : ∀ A → count-non (Hypergraph.cod (hId A)) ≡ 0
hId-count-non-cod A = AllIn→count-non-zero (hId-cod-covers A)

--------------------------------------------------------------------------------
-- For identity hypergraphs, `dom ≡ cod` as lists (not just as types). This
-- mirrors the categorical fact that `id` is self-dual, and at the level of
-- the `hId` construction it holds because every branch uses the same
-- Fin-list on both sides.

hId-cod≡dom : ∀ A → Hypergraph.cod (hId A) ≡ Hypergraph.dom (hId A)
hId-cod≡dom unit      = refl
hId-cod≡dom (Var x)   = refl
hId-cod≡dom (A ⊗₀ B)  =
  cong₂ _++_
    (cong (map (inject+ (Hypergraph.nV (hId B)))) (hId-cod≡dom A))
    (cong (map (raise  (Hypergraph.nV (hId A)))) (hId-cod≡dom B))

--------------------------------------------------------------------------------
-- `Unique` for identity's dom. Used by `idˡ-cod-helper` to apply
-- `classify-lookup-Unique`.
--
-- The tensor case needs:
--   * map⁺ with inject+ injectivity     (left Unique).
--   * map⁺ with raise   injectivity     (right Unique).
--   * ++⁺ with disjointness of images   (inject+ and raise have disjoint ranges).

-- injectivity of inject+ and raise via splitAt reduction.
private
  inject+-inj : ∀ {m} (n : ℕ) {i j : Fin m}
              → inject+ n i ≡ inject+ n j → i ≡ j
  inject+-inj {m} n {i} {j} eq with
    splitAt-inject+ m n i | splitAt-inject+ m n j | cong (splitAt m) eq
  ... | i-red | j-red | split-eq =
    inj₁-inj (trans (sym i-red) (trans split-eq j-red))
    where
      inj₁-inj : ∀ {X Y : Set} {x y : X} → inj₁ {B = Y} x ≡ inj₁ y → x ≡ y
      inj₁-inj refl = refl

  raise-inj : ∀ (m : ℕ) {n} {i j : Fin n}
            → raise m i ≡ raise m j → i ≡ j
  raise-inj m {n} {i} {j} eq with
    splitAt-raise m n i | splitAt-raise m n j | cong (splitAt m) eq
  ... | i-red | j-red | split-eq =
    inj₂-inj (trans (sym i-red) (trans split-eq j-red))
    where
      inj₂-inj : ∀ {X Y : Set} {x y : Y} → inj₂ {A = X} x ≡ inj₂ y → x ≡ y
      inj₂-inj refl = refl

  -- map inject+ and map raise produce disjoint lists.
  --   If v ∈ map (inject+ n) xs, then v = inject+ n vL for some vL ∈ xs,
  --     hence splitAt m v = inj₁ vL.
  --   If v ∈ map (raise m)  ys, then v = raise m vR for some vR ∈ ys,
  --     hence splitAt m v = inj₂ vR.
  --   These two splitAt results are both inj₁ and inj₂, contradiction.
  disj-L-R : ∀ {m n} (xs : List (Fin m)) (ys : List (Fin n))
           → Disjoint (map (inject+ n) xs) (map (raise m) ys)
  disj-L-R {m} {n} xs ys {v} (v∈L , v∈R)
    with ∈-map⁻ (inject+ n) v∈L | ∈-map⁻ (raise m) v∈R
  ... | vL , _ , v≡L | vR , _ , v≡R
    = case-absurd (trans (sym sp-L) sp-R)
    where
      -- splitAt m v is forced two different ways.
      sp-L : splitAt m v ≡ inj₁ vL
      sp-L = trans (cong (splitAt m) v≡L) (splitAt-inject+ m n vL)

      sp-R : splitAt m v ≡ inj₂ vR
      sp-R = trans (cong (splitAt m) v≡R) (splitAt-raise m n vR)

      case-absurd : ∀ {ℓ} {X : Set ℓ} → inj₁ {B = Fin n} vL ≡ inj₂ vR → X
      case-absurd ()

hId-dom-Unique : ∀ A → Unique (Hypergraph.dom (hId A))
hId-dom-Unique unit     = AllPairs.[]
  where import Data.List.Relation.Unary.AllPairs as AllPairs
hId-dom-Unique (Var x)  = All.[] AllPairs.∷ AllPairs.[]
  where
    import Data.List.Relation.Unary.AllPairs as AllPairs
    import Data.List.Relation.Unary.All       as All
hId-dom-Unique (A ⊗₀ B) =
  Uniq-Prop.++⁺
    (Uniq-Prop.map⁺ (inject+-inj (Hypergraph.nV (hId B))) (hId-dom-Unique A))
    (Uniq-Prop.map⁺ (raise-inj   (Hypergraph.nV (hId A))) (hId-dom-Unique B))
    (disj-L-R (Hypergraph.dom (hId A)) (Hypergraph.dom (hId B)))

-- Symmetric version for cod.
hId-cod-Unique : ∀ A → Unique (Hypergraph.cod (hId A))
hId-cod-Unique A = subst Unique (sym (hId-cod≡dom A)) (hId-dom-Unique A)
