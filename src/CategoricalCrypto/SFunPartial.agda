{-# OPTIONS --safe --without-K #-}

-- PARTIAL probabilistic stateful functions: `SFunM` instantiated at the
-- sub-probability monad `Dist⊥ = Dist-ℚ ∘ Maybe`.  Because `SFunM` is generic
-- over a commutative setoid monad and `Partial` provides all four instances,
-- the CATEGORY comes for free (`SFun⊥-Category`).
--
-- On top of it we build the iteration operator (`iterFuel`): the (⊎-)TRACE of
-- the monoidal structure, in fuelled form: `iterFuel` is the n-th trace
-- approximant, and a genuinely partial computation is the ω-chain of
-- approximants.  Machine COMPOSITION is NOT an ad-hoc relay loop here — it is
-- the G-construction's composition (a field of `Machine.Probabilistic`'s
-- `Machines`, in a shape the g-construction branch discharges against the real
-- trace).  The full traced-monoidal axioms over the chain semantics
-- (yanking, naturality, …) are future work — with the finite `Dist-ℚ` carrier the untruncated trace of an unbounded
-- a.s.-terminating loop needs lower reals (cf. the expectation model on the
-- probability-theory branch); every BOUNDED loop (all we need for reactive
-- machine composition with per-activation bounds) already lives here.

open import categorical-crypto.Prelude hiding (Stable)

open import Data.List as L using ()
open import Data.Nat using (_≤_)

open import Class.Core
open import Class.Monad
open import Class.Monad.Ext.Setoid

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.RationalDist.Partial

import Relation.Binary.Reasoning.Setoid as RS

open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunM.Monoidal

module CategoricalCrypto.SFunPartial where

private variable
  A A' B B' St X : Type

-- The category of partial probabilistic stateful functions.
SFun⊥ : Type → Type → Type₁
SFun⊥ = SFunᵉ {M = Dist⊥}

SFun⊥-Category : Category _ _ _
SFun⊥-Category = SFunᵉ-Category {M = Dist⊥}

-- Machines run side by side: the tensor is the disjoint union of interfaces
-- and the unit is the empty interface, so `strip⊥` below is the left unitor.
--
-- Both types spell the category out rather than reusing `SFun⊥-Category`:
-- checking a `Monoidal C` against a `Monoidal C′` with `C`, `C′` *different
-- definitions* of the same category makes Agda compare the two record types
-- field by field, which at `Dist⊥` costs >120 s instead of <1 s.
SFun⊥-MonoidalCategory : MonoidalCategory _ _ _
SFun⊥-MonoidalCategory = SFunᵉ-MonoidalCategory {M = Dist⊥}

SFun⊥-Symmetric : Symmetric (SFunᵉ-Monoidal {M = Dist⊥})
SFun⊥-Symmetric = SFunᵉ-Symmetric


-- Total functions embed (pointwise `just`).
embed⊥ : SFunᵉ {M = Dist-ℚ} A B → SFun⊥ A B
embed⊥ f = record
  { State = SFunᵉ.State f
  ; init  = SFunᵉ.init f
  ; fun   = λ sa → Dmap just (SFunᵉ.fun f sa)
  }

-- Binding an embedded computation skips the Maybe layer.
>>=⊥-embed : {A B : Type} (μ : Dist-ℚ A) (k : A → Dist⊥ B)
           → (Dmap just μ >>=⊥ k) ≈Mℚ (μ >>=ᴹ k)
>>=⊥-embed μ k = Dmap->>= just μ (kmaybe k)

-- Dropping an empty (⊥) interface component: the left unitor's underlying map.
open import Data.Sum.Ext using () renaming (unitˡ⇒ to unbot) public

strip⊥ : {A B : Type} → SFun⊥ (⊥ ⊎ A) (⊥ ⊎ B) → SFun⊥ A B
strip⊥ f = record
  { State = SFunᵉ.State f
  ; init  = SFunᵉ.init f
  ; fun   = λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))
                     >>=⊥ λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr))
  }

-- The same construction on a TOTAL functionality.
stripᵉ : SFunᵉ {M = Dist-ℚ} (⊥ ⊎ A) (⊥ ⊎ B) → SFunᵉ {M = Dist-ℚ} A B
stripᵉ f = record
  { State = SFunᵉ.State f
  ; init  = SFunᵉ.init f
  ; fun   = λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))
                     >>=ᴹ λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr))
  }

------------------------------------------------------------------------
-- Trace and strip: `trace` is congruent and commutes with relabelling, and
-- `strip⊥`/`embed⊥` commute with each other up to `_≈ᵉ_`.

-- `_≈ᵉ_`-transitivity and `≡`-to-`_≈ᵉ_`, unfolded per-`xs` to `_≈Mℚ_` (avoids
-- needing the `IsEquivalence` module of `_≈ᵉ_` in scope).
≈ᵉ-trans⊥ : {f g h : SFun⊥ A B}
          → (_≈ᵉ_ {M = Dist⊥}) f g → (_≈ᵉ_ {M = Dist⊥}) g h → (_≈ᵉ_ {M = Dist⊥}) f h
≈ᵉ-trans⊥ {f = f} {g} {h} f≈g g≈h xs =
  Mℚ.trans {i = eval f xs} {j = eval g xs} {k = eval h xs} (f≈g xs) (g≈h xs)

≡→≈ᵉ⊥ : {f g : SFun⊥ A B} → f ≡ g → (_≈ᵉ_ {M = Dist⊥}) f g
≡→≈ᵉ⊥ {f = f} {g} eq xs = Mℚ.reflexive (cong (λ m → eval m xs) eq)

trace-cong⊥ : {f g : St × A → Dist⊥ (St × B)}
            → (∀ sa → f sa ≈Mℚ g sa)
            → (s : St) (xs : List A)
            → trace {M = Dist⊥} f s xs ≈Mℚ trace {M = Dist⊥} g s xs
trace-cong⊥ f≈g s []       = λ P → refl
trace-cong⊥ {f = f} {g} f≈g s (a ∷ as) =
  >>=⊥-cong {μ = f (s , a)} {g (s , a)}
    {λ sb → trace {M = Dist⊥} f (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))}
    {λ sb → trace {M = Dist⊥} g (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))}
    (f≈g (s , a))
    (λ sb → >>=⊥-congʳ (λ bs → return⊥ (proj₂ sb ∷ bs))
              (trace {M = Dist⊥} f (proj₁ sb) as) (trace {M = Dist⊥} g (proj₁ sb) as)
              (trace-cong⊥ f≈g (proj₁ sb) as))

-- `embed⊥` of a stripped total functionality equals the `strip⊥` of its embedding.
strip-embed-swap : (h : SFunᵉ {M = Dist-ℚ} (⊥ ⊎ A) (⊥ ⊎ B))
                 → (_≈ᵉ_ {M = Dist⊥}) (strip⊥ (embed⊥ h)) (embed⊥ (stripᵉ h))
strip-embed-swap h = trace-cong⊥ kern (SFunᵉ.init h)
  where
    kern : ∀ sa → SFunᵉ.fun (strip⊥ (embed⊥ h)) sa ≈Mℚ SFunᵉ.fun (embed⊥ (stripᵉ h)) sa
    kern sa = begin
      SFunᵉ.fun (strip⊥ (embed⊥ h)) sa
        ≈⟨ >>=⊥-embed (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)))
                      (λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr))) ⟩
      (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)) >>=ᴹ (λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr))))
        ≈˘⟨ >>=ᴹ-congˡ (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)))
              (λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr)))
              (λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr)) >>=ᴹ (return-ℚ ∘ just))
              (λ sr → >>=ᴹ-identityˡ (proj₁ sr , unbot (proj₂ sr)) (return-ℚ ∘ just)) ⟩
      (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)) >>=ᴹ
        (λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr)) >>=ᴹ (return-ℚ ∘ just)))
        ≈˘⟨ >>=ᴹ-assoc (SFunᵉ.fun h (proj₁ sa , inj₂ (proj₂ sa)))
              (λ sr → return-ℚ (proj₁ sr , unbot (proj₂ sr))) (return-ℚ ∘ just) ⟩
      SFunᵉ.fun (embed⊥ (stripᵉ h)) sa
        ∎
      where open RS (Mℚ-setoid _)

-- Trace commutes with a per-step input relabelling.
trace-mapin : (g : A → A') (k : St × A' → Dist⊥ (St × B))
              (s : St) (xs : List A)
            → trace {M = Dist⊥} (λ sa → k (proj₁ sa , g (proj₂ sa))) s xs
              ≈Mℚ trace {M = Dist⊥} k s (L.map g xs)
trace-mapin g k s []       = λ P → refl
trace-mapin g k s (a ∷ as) =
  >>=⊥-congˡ (k (s , g a))
    (λ sb → trace {M = Dist⊥} (λ sa → k (proj₁ sa , g (proj₂ sa))) (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs)))
    (λ sb → trace {M = Dist⊥} k (proj₁ sb) (L.map g as) >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs)))
    (λ sb → >>=⊥-congʳ (λ bs → return⊥ (proj₂ sb ∷ bs))
              (trace {M = Dist⊥} (λ sa → k (proj₁ sa , g (proj₂ sa))) (proj₁ sb) as)
              (trace {M = Dist⊥} k (proj₁ sb) (L.map g as))
              (trace-mapin g k (proj₁ sb) as))

-- Trace commutes with a per-step output relabelling (pushed to the end).
trace-mapout : (φ : B → B') (k : St × A → Dist⊥ (St × B))
               (s : St) (xs : List A)
             → trace {M = Dist⊥} (λ sa → k sa >>=⊥ (λ sr → return⊥ (proj₁ sr , φ (proj₂ sr)))) s xs
               ≈Mℚ (trace {M = Dist⊥} k s xs >>=⊥ (λ ys → return⊥ (L.map φ ys)))
trace-mapout φ k s [] = begin
  return⊥ []                    ≈˘⟨ >>=⊥-identityˡ [] post ⟩
  (return⊥ [] >>=⊥ post)        ∎
  where post = λ ys → return⊥ (L.map φ ys)
        open RS (Mℚ-setoid _)
trace-mapout φ k s (a ∷ as) = begin
  ((K >>=⊥ wret) >>=⊥ ContMO)
    ≈⟨ >>=⊥-assoc K wret ContMO ⟩
  (K >>=⊥ (λ sr → wret sr >>=⊥ ContMO))
    ≈⟨ >>=⊥-congˡ K (λ sr → wret sr >>=⊥ ContMO) (λ sr → ContMO (proj₁ sr , φ (proj₂ sr)))
         (λ sr → >>=⊥-identityˡ (proj₁ sr , φ (proj₂ sr)) ContMO) ⟩
  (K >>=⊥ (λ sr → ContMO (proj₁ sr , φ (proj₂ sr))))
    ≈⟨ >>=⊥-congˡ K (λ sr → ContMO (proj₁ sr , φ (proj₂ sr)))
         (λ sr → (Tk (proj₁ sr) >>=⊥ post) >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))
         (λ sr → >>=⊥-congʳ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))
                   (Tm (proj₁ sr)) (Tk (proj₁ sr) >>=⊥ post)
                   (trace-mapout φ k (proj₁ sr) as)) ⟩
  (K >>=⊥ (λ sr → (trace {M = Dist⊥} k (proj₁ sr) as >>=⊥ post) >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))))
    ≈⟨ >>=⊥-congˡ K
         (λ sr → (Tk (proj₁ sr) >>=⊥ post) >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))
         (λ sr → Tk (proj₁ sr) >>=⊥ (λ ys → post ys >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))))
         (λ sr → >>=⊥-assoc (Tk (proj₁ sr)) post (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))) ⟩
  (K >>=⊥ (λ sr → trace {M = Dist⊥} k (proj₁ sr) as >>=⊥ (λ ys → post ys >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))))
    ≈⟨ >>=⊥-congˡ K
         (λ sr → Tk (proj₁ sr) >>=⊥ (λ ys → post ys >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs))))
         (λ sr → Tk (proj₁ sr) >>=⊥ (λ ys → return⊥ (φ (proj₂ sr) ∷ L.map φ ys)))
         (λ sr → >>=⊥-congˡ (Tk (proj₁ sr))
                   (λ ys → post ys >>=⊥ (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))
                   (λ ys → return⊥ (φ (proj₂ sr) ∷ L.map φ ys))
                   (λ ys → >>=⊥-identityˡ (L.map φ ys) (λ bs → return⊥ (φ (proj₂ sr) ∷ bs)))) ⟩
  (K >>=⊥ (λ sr → trace {M = Dist⊥} k (proj₁ sr) as >>=⊥ (λ ys → return⊥ (φ (proj₂ sr) ∷ L.map φ ys))))
    ≈˘⟨ >>=⊥-congˡ K
          (λ sb → Tk (proj₁ sb) >>=⊥ (λ ys → return⊥ (proj₂ sb ∷ ys) >>=⊥ post))
          (λ sb → Tk (proj₁ sb) >>=⊥ (λ ys → return⊥ (φ (proj₂ sb) ∷ L.map φ ys)))
          (λ sb → >>=⊥-congˡ (Tk (proj₁ sb))
                    (λ ys → return⊥ (proj₂ sb ∷ ys) >>=⊥ post)
                    (λ ys → return⊥ (φ (proj₂ sb) ∷ L.map φ ys))
                    (λ ys → >>=⊥-identityˡ (proj₂ sb ∷ ys) post)) ⟩
  (K >>=⊥ (λ sb → trace {M = Dist⊥} k (proj₁ sb) as >>=⊥ (λ ys → return⊥ (proj₂ sb ∷ ys) >>=⊥ post)))
    ≈˘⟨ >>=⊥-congˡ K
          (λ sb → Gk sb >>=⊥ post)
          (λ sb → Tk (proj₁ sb) >>=⊥ (λ ys → return⊥ (proj₂ sb ∷ ys) >>=⊥ post))
          (λ sb → >>=⊥-assoc (Tk (proj₁ sb)) (λ bs → return⊥ (proj₂ sb ∷ bs)) post) ⟩
  (K >>=⊥ (λ sb → (trace {M = Dist⊥} k (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))) >>=⊥ post))
    ≈˘⟨ >>=⊥-assoc K Gk post ⟩
  ((K >>=⊥ Gk) >>=⊥ post)
    ∎
  where
    post   = λ ys → return⊥ (L.map φ ys)
    K      = k (s , a)
    wret   = λ sr → return⊥ (proj₁ sr , φ (proj₂ sr))
    Tm     = λ st → trace {M = Dist⊥} (λ sa → k sa >>=⊥ (λ sr → return⊥ (proj₁ sr , φ (proj₂ sr)))) st as
    Tk     = λ st → trace {M = Dist⊥} k st as
    ContMO = λ sb → Tm (proj₁ sb) >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))
    Gk     = λ sb → trace {M = Dist⊥} k (proj₁ sb) as >>=⊥ (λ bs → return⊥ (proj₂ sb ∷ bs))
    open RS (Mℚ-setoid _)

-- `strip⊥` unfolds to running on `inj₂`-wrapped inputs and `unbot`-ing outputs.
strip-eval : (f : SFun⊥ (⊥ ⊎ A) (⊥ ⊎ B)) (s : SFunᵉ.State f) (xs : List A)
           → trace {M = Dist⊥} (SFunᵉ.fun (strip⊥ f)) s xs
             ≈Mℚ (trace {M = Dist⊥} (SFunᵉ.fun f) s (L.map inj₂ xs) >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
strip-eval f s xs = begin
  trace {M = Dist⊥} (SFunᵉ.fun (strip⊥ f)) s xs
    ≈⟨ trace-mapout unbot (λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))) s xs ⟩
  (trace {M = Dist⊥} (λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))) s xs >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
    ≈⟨ >>=⊥-congʳ (λ ys → return⊥ (L.map unbot ys))
         (trace {M = Dist⊥} (λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))) s xs)
         (trace {M = Dist⊥} (SFunᵉ.fun f) s (L.map inj₂ xs))
         (trace-mapin inj₂ (SFunᵉ.fun f) s xs) ⟩
  (trace {M = Dist⊥} (SFunᵉ.fun f) s (L.map inj₂ xs) >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
    ∎
  where open RS (Mℚ-setoid _)

-- `strip⊥` respects `_≈ᵉ_`.
strip⊥-cong : {f g : SFun⊥ (⊥ ⊎ A) (⊥ ⊎ B)}
            → (_≈ᵉ_ {M = Dist⊥}) f g → (_≈ᵉ_ {M = Dist⊥}) (strip⊥ f) (strip⊥ g)
strip⊥-cong {f = f} {g} f≈g xs = begin
  eval (strip⊥ f) xs
    ≈⟨ strip-eval f (SFunᵉ.init f) xs ⟩
  (eval f (L.map inj₂ xs) >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
    ≈⟨ >>=⊥-congʳ (λ ys → return⊥ (L.map unbot ys))
         (eval f (L.map inj₂ xs)) (eval g (L.map inj₂ xs))
         (f≈g (L.map inj₂ xs)) ⟩
  (eval g (L.map inj₂ xs) >>=⊥ (λ ys → return⊥ (L.map unbot ys)))
    ≈˘⟨ strip-eval g (SFunᵉ.init g) xs ⟩
  eval (strip⊥ g) xs
    ∎
  where open RS (Mℚ-setoid _)


------------------------------------------------------------------------
-- Fuelled iteration (the ⊎-trace approximants).  Elgot-style: the body
-- either exits (`inj₁`) or requests another round (`inj₂`); out of fuel
-- means divergence (`nothing`).

iterFuel : {X B : Type} → ℕ → (X → Dist⊥ (B ⊎ X)) → X → Dist⊥ B
iterGo   : {X B : Type} → ℕ → (X → Dist⊥ (B ⊎ X)) → (B ⊎ X) → Dist⊥ B

iterFuel zero    body x = return-ℚ nothing
iterFuel (suc n) body x = body x >>=⊥ iterGo n body

iterGo n body (inj₁ b) = return⊥ b
iterGo n body (inj₂ x) = iterFuel n body x

------------------------------------------------------------------------
-- The G-composition's execution-formula approximants (GoI token dynamics).
-- Composing `g` and `f` over the shared middle interface `B⁺ ⊎ B⁻`, an
-- internal token bounces between `g` (entered on `B⁺`) and `f` (entered on
-- `B⁻`) until it exits on the external interface `A⁻ ⊎ C⁺`.  `machineAt n` is
-- the `n`-th such approximant (`iterFuel`-bounded); the real `∘ᵍ` (assumed in
-- `Machine.Probabilistic`) is their limit: `∘ᵍ` is the ⊎-trace over the middle
-- interface, whose fuelled approximants ARE these token machines, and the
-- limit of an eventually-constant chain (`Stable n`) is its tail (`machineAt n`).

module GComp {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Type}
  (g : SFun⊥ (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺))
  (f : SFun⊥ (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) where

  private
    module g = SFunᵉ g
    module f = SFunᵉ f

  S : Type
  S = g.State × f.State

  -- internal token: heading into `g` (`inj₁`) resp. `f` (`inj₂`).
  Tok : Type
  Tok = B⁺ ⊎ B⁻

  -- either exit on the external interface, or continue with a token.
  Res : Type
  Res = (S × (A⁻ ⊎ C⁺)) ⊎ (S × Tok)

  -- classify `g`'s output: internal `B⁻` continues into `f`; external `C⁺` exits.
  stepG : f.State → (g.State × (B⁻ ⊎ C⁺)) → Res
  stepG sf (sg , inj₁ b⁻) = inj₂ ((sg , sf) , inj₂ b⁻)
  stepG sf (sg , inj₂ c⁺) = inj₁ ((sg , sf) , inj₂ c⁺)

  -- classify `f`'s output: internal `B⁺` continues into `g`; external `A⁻` exits.
  stepF : g.State → (f.State × (A⁻ ⊎ B⁺)) → Res
  stepF sg (sf , inj₁ a⁻) = inj₁ ((sg , sf) , inj₁ a⁻)
  stepF sg (sf , inj₂ b⁺) = inj₂ ((sg , sf) , inj₁ b⁺)

  -- one bounce of the token loop.
  body : S × Tok → Dist⊥ Res
  body ((sg , sf) , inj₁ b⁺) = g.fun (sg , inj₁ b⁺) >>=⊥ (return⊥ ∘ stepG sf)
  body ((sg , sf) , inj₂ b⁻) = f.fun (sf , inj₂ b⁻) >>=⊥ (return⊥ ∘ stepF sg)

  -- inject an external input, producing the first `Res`.
  enter : S × (A⁺ ⊎ C⁻) → Dist⊥ Res
  enter ((sg , sf) , inj₁ a⁺) = f.fun (sf , inj₁ a⁺) >>=⊥ (return⊥ ∘ stepF sg)
  enter ((sg , sf) , inj₂ c⁻) = g.fun (sg , inj₂ c⁻) >>=⊥ (return⊥ ∘ stepG sf)

  -- run the loop from the first `Res` under `n` units of fuel.
  goRes : ℕ → Res → Dist⊥ (S × (A⁻ ⊎ C⁺))
  goRes n (inj₁ done) = return⊥ done
  goRes n (inj₂ tok)  = iterFuel n body tok

  kernelAt : ℕ → S × (A⁺ ⊎ C⁻) → Dist⊥ (S × (A⁻ ⊎ C⁺))
  kernelAt n (s , m) = enter (s , m) >>=⊥ goRes n

  machineAt : ℕ → SFun⊥ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺)
  machineAt n = record
    { State = S
    ; init  = g.init , f.init
    ; fun   = kernelAt n
    }

  Stable : ℕ → Type
  Stable n = ∀ m s x → n ≤ m → kernelAt m (s , x) ≈Mℚ kernelAt n (s , x)
