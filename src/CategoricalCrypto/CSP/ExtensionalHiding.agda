{-# OPTIONS --safe --without-K --guardedness #-}

-- Exact raw observations are not divergence flooded. The progress rule is an
-- implementation-side invariant; visible steps may reset its natural potential.
-- The enlarged-refusal argument follows HideMonoFD/HideFD at
-- agda-cardano-common 9a40d1de330f376c3a102e7c9f1282f4fa830a7e, ported here
-- to safe, exact-trace semantics without the library's classical accessibility rule.
open import Data.Bool.Base hiding (_<_; _≤_)
module CategoricalCrypto.CSP.ExtensionalHiding (E B : Set) (sync : E → Bool) where

open import Data.Empty
open import Data.List.Base
open import Data.Nat.Base
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.NativeParallel as Parallel
import CategoricalCrypto.CSP.NativeRefinement as Inversion
import CategoricalCrypto.CSP.Process as Core

module O = Operators E B sync
module P = Parallel E B sync
module V = Inversion E B sync
module L = Core E O.Index ⊤
open O
open L
open Tree

private variable
  p q r hp hq t : Tree
  l : Label
  e : E
  xs ys : List Visible
  X : Visible → Set

record RawInclusion (spec impl : Tree) : Set₁ where
  field
    traces : ∀ {xs} → Trace impl xs → Trace spec xs
    failures : ∀ {xs X} → Failure impl xs X → Failure spec xs X
    divergences : ∀ {xs} → Divergence impl xs → Divergence spec xs

module Mask (hide : E → Bool) where
  erase : List Visible → List Visible
  erase [] = []
  erase (event e ∷ xs) with hide e
  ... | true = erase xs
  ... | false = event e ∷ erase xs
  erase (√ tt ∷ xs) = √ tt ∷ erase xs

  -- Return reaches the literal stop, whereas Hide stop is only behaviourally
  -- equal to it. Keeping this case explicit avoids any coinductive equality axiom.
  data Hides : Tree → Tree → Set where
    hidden : Hides p (Hide hide p)
    halted : Hides stop stop

  data SilentSource (p : Tree) : Tree → Set where
    old : p ─[ τ ]→ q → Hides q hq → SilentSource p hq
    concealed : hide e ≡ true → p ─[ visible (event e) ]→ q → Hides q hq → SilentSource p hq

  silent-source : Hides p hp → hp ─[ τ ]→ hq → SilentSource p hq
  silent-source hidden step with P.hide-silent-invert hide step
  ... | P.original move = old move hidden
  ... | P.concealed-event inside move = concealed inside move hidden
  silent-source halted step = ⊥-elim (stop-no-step step)

  event-source : Hides p hp → hp ─[ visible (event e) ]→ hq
    → Σ Tree (λ q → hide e ≡ false × p ─[ visible (event e) ]→ q × Hides q hq)
  event-source hidden step with V.hide-visible-invert hide step
  ... | V.kept outside move = _ , outside , move , hidden
  event-source halted step = ⊥-elim (stop-no-step step)

  return-source : Hides p hp → hp ─[ visible (√ tt) ]→ hq
    → p ─[ visible (√ tt) ]→ stop × Hides stop hq
  return-source hidden step with P.hide-return-invert hide step
  ... | ready , refl = sRet ready , halted
  return-source halted step = ⊥-elim (stop-no-step step)

  erase-hidden : hide e ≡ true → erase (event e ∷ xs) ≡ erase xs
  erase-hidden {e = e} inside rewrite inside = refl

  erase-kept : hide e ≡ false → erase (event e ∷ xs) ≡ event e ∷ erase xs
  erase-kept {e = e} outside rewrite outside = refl

  project : Hides p hp → Executes hp ys t
    → Σ (List Visible) (λ xs → Σ Tree (λ q → Executes p xs q × erase xs ≡ ys × Hides q t))
  project rel done = [] , _ , done , refl , rel
  project rel (silent-step step run) with silent-source rel step
  ... | old move next with project next run
  ... | xs , q , path , eq , end = xs , q , silent-step move path , eq , end
  project rel (silent-step step run) | concealed inside move next with project next run
  ... | xs , q , path , eq , end = event _ ∷ xs , q , visible-step move path , trans (erase-hidden inside) eq , end
  project rel (visible-step {e = event e} step run) with event-source rel step
  ... | q , outside , move , next with project next run
  ... | xs , r , path , eq , end = event e ∷ xs , r , visible-step move path , trans (erase-kept outside) (cong (event e ∷_) eq) , end
  project rel (visible-step {e = √ tt} step run) with return-source rel step
  ... | move , next with project next run
  ... | xs , r , path , eq , end = √ tt ∷ xs , r , visible-step move path , cong (√ tt ∷_) eq , end

  lift-silent : Hides p hp → p ─[ τ ]→ q → Σ Tree (λ hq → hp ─[ τ ]→ hq × Hides q hq)
  lift-silent hidden move = _ , P.hide-silent-step hide move , hidden
  lift-silent halted move = ⊥-elim (stop-no-step move)

  lift-event : Hides p hp → p ─[ visible (event e) ]→ q
    → (hide e ≡ true → Σ Tree (λ hq → hp ─[ τ ]→ hq × Hides q hq))
      × (hide e ≡ false → Σ Tree (λ hq → hp ─[ visible (event e) ]→ hq × Hides q hq))
  lift-event hidden move = (λ inside → _ , P.hide-hidden hide inside move , hidden)
    , (λ outside → _ , P.hide-keep hide outside move , hidden)
  lift-event halted move = ⊥-elim (stop-no-step move)

  lift-return : Hides p hp → p ─[ visible (√ tt) ]→ q
    → Σ Tree (λ hq → hp ─[ visible (√ tt) ]→ hq × Hides q hq)
  lift-return hidden (sRet ready) = stop , P.hide-return hide ready , halted
  lift-return halted move = ⊥-elim (stop-no-step move)

  lift : Hides p hp → Executes p xs q
    → Σ Tree (λ hq → Executes hp (erase xs) hq × Hides q hq)
  lift rel done = _ , done , rel
  lift rel (silent-step move run) with lift-silent rel move
  ... | hp′ , step , next with lift next run
  ... | hq , path , end = hq , silent-step step path , end
  lift rel (visible-step {e = event e} move run) with hide e in eq
  ... | true with proj₁ (lift-event rel move) eq
  ... | hp′ , step , next with lift next run
  ... | hq , path , end = hq , silent-step step path , end
  lift rel (visible-step {e = event e} move run) | false with proj₂ (lift-event rel move) eq
  ... | hp′ , step , next with lift next run
  ... | hq , path , end = hq , visible-step step path , end
  lift rel (visible-step {e = √ tt} move run) with lift-return rel move
  ... | hp′ , step , next with lift next run
  ... | hq , path , end = hq , visible-step step path , end

  Hidden : Visible → Set
  Hidden (event e) = hide e ≡ true
  Hidden (√ tt) = ⊥

  augment : (Visible → Set) → Visible → Set
  augment X e = X e ⊎ Hidden e

  refusal-source : Hides p hp → Refuses hp X → Refuses p (augment X)
  refusal-source {p = p} {X = X} rel ((noτ , no√) , absent) =
    ((λ q move → let _ , step , _ = lift-silent rel move in noτ _ step)
    , (λ _ q move → let _ , step , _ = lift-return rel move in no√ tt _ step))
    , refuse
    where
    refuse : ∀ e → augment X e → ∀ q → ¬ (p ─[ visible e ]→ q)
    refuse (event e) choice q move with hide e in eq
    ... | true = let _ , step , _ = proj₁ (lift-event rel move) eq in noτ _ step
    ... | false with choice
    ... | inj₁ selected = let _ , step , _ = proj₂ (lift-event rel move) eq in absent (event e) selected _ step
    ... | inj₂ inside = false≢true inside
      where
      false≢true : ¬ (false ≡ true)
      false≢true ()
    refuse (√ tt) (inj₁ selected) q move = let _ , step , _ = lift-return rel move in absent (√ tt) selected _ step
    refuse (√ tt) (inj₂ ()) q move

  refusal-lift : Hides p hp → Refuses p (augment X) → Refuses hp X
  refusal-lift {p = p} {hp = hp} {X = X} rel ((noτ , no√) , absent) =
    ((λ q step → silent-absent (silent-source rel step))
    , (λ _ q step → no√ tt stop (proj₁ (return-source rel step)))) , refuse
    where
    silent-absent : SilentSource p t → ⊥
    silent-absent (old move next) = noτ _ move
    silent-absent (concealed inside move next) = absent (event _) (inj₂ inside) _ move
    refuse : ∀ e → X e → ∀ q → ¬ (hp ─[ visible e ]→ q)
    refuse (event e) selected q step = let _ , _ , move , _ = event-source rel step in absent (event e) (inj₁ selected) _ move
    refuse (√ tt) selected q step = absent (√ tt) (inj₁ selected) stop (proj₁ (return-source rel step))

  traces : (∀ {xs} → Trace q xs → Trace p xs)
    → Trace (Hide hide q) ys → Trace (Hide hide p) ys
  traces inclusion (t , run) with project hidden run
  ... | xs , q′ , path , eq , end with inclusion (q′ , path)
  ... | p′ , source with lift hidden source
  ... | hp′ , target , end′ = hp′ , subst (λ ys → Executes _ ys hp′) eq target

  failures : (∀ {xs X} → Failure q xs X → Failure p xs X)
    → Failure (Hide hide q) ys X → Failure (Hide hide p) ys X
  failures inclusion (t , run , refusal) with project hidden run
  ... | xs , q′ , path , eq , end with inclusion (q′ , path , refusal-source end refusal)
  ... | p′ , source , refusal′ with lift hidden source
  ... | hp′ , target , end′ = hp′ , subst (λ ys → Executes _ ys hp′) eq target , refusal-lift end′ refusal′

  Silent : Label → Set
  Silent τ = ⊤
  Silent (visible e) = Hidden e

  record Progress (initial : Tree) : Set₁ where
    field
      Inv : Tree → Set
      starts : Inv initial
      closed : ∀ {p q l} → Inv p → p ─[ l ]→ q → Inv q
      rank : ∀ {p} → Inv p → ℕ
      decreases : ∀ {p q l} (i : Inv p) (step : p ─[ l ]→ q)
        → Silent l → rank (closed i step) < rank i

  module Ranked {initial} (progress : Progress initial) where
    open Progress progress

    no-divergence : ∀ n → ∀ {p hp} (i : Inv p) → rank i ≤ n → Hides p hp → ¬ (Diverges hp)
    no-divergence zero i bound rel d with silent-source rel (Diverges.step d)
    ... | old move next = impossible (decreases i move tt) bound
      where
      impossible : ∀ {m k} → m < k → k ≤ zero → ⊥
      impossible () z≤n
    ... | concealed inside move next = impossible (decreases i move inside) bound
      where
      impossible : ∀ {m k} → m < k → k ≤ zero → ⊥
      impossible () z≤n
    no-divergence (suc n) i bound rel d with silent-source rel (Diverges.step d)
    ... | old move next = no-divergence n (closed i move) (lower (decreases i move tt) bound) next (Diverges.rest d)
      where
      lower : ∀ {m k n} → m < k → k ≤ suc n → m ≤ n
      lower a b = s≤s⁻¹ (≤-trans a b)
    ... | concealed inside move next = no-divergence n (closed i move) (lower (decreases i move inside) bound) next (Diverges.rest d)
      where
      lower : ∀ {m k n} → m < k → k ≤ suc n → m ≤ n
      lower a b = s≤s⁻¹ (≤-trans a b)

    invariant : ∀ {p q xs} → Inv p → Executes p xs q → Inv q
    invariant i done = i
    invariant i (silent-step move run) = invariant (closed i move) run
    invariant i (visible-step move run) = invariant (closed i move) run

    no-exact-divergence : ¬ (Divergence (Hide hide initial) ys)
    no-exact-divergence (t , run , d) with project hidden run
    ... | xs , q , path , eq , end = no-divergence _ (invariant starts path) ≤-refl end d

  ranked-hiding : RawInclusion p q → Progress q → RawInclusion (Hide hide p) (Hide hide q)
  RawInclusion.traces (ranked-hiding inclusion progress) = traces (RawInclusion.traces inclusion)
  RawInclusion.failures (ranked-hiding inclusion progress) = failures (RawInclusion.failures inclusion)
  RawInclusion.divergences (ranked-hiding inclusion progress) d = ⊥-elim (Ranked.no-exact-divergence progress d)
