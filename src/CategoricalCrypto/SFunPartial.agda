{-# OPTIONS --safe #-}

-- PARTIAL probabilistic stateful functions: `SFunM` instantiated at the
-- sub-probability monad `Dist⊥ = Dist-ℚ ∘ Maybe`.  Because `SFunM` is generic
-- over a commutative setoid monad and `Partial` provides all four instances,
-- the CATEGORY comes for free (`SFun⊥-Category`).
--
-- On top of it we build the iteration operator (`iterFuel`): the (⊎-)TRACE of
-- the monoidal structure, in fuelled form: `iterFuel` is the n-th trace
-- approximant, and a genuinely partial computation is the ω-chain of
-- approximants.  Machine COMPOSITION is NOT an ad-hoc relay loop here — it is
-- the G-construction's composition (postulated in `MerkleDamgard` in a shape
-- the g-construction branch discharges against the real trace).  The full
-- traced-monoidal
-- axioms over the chain semantics (yanking, naturality, …) are future work —
-- with the finite `Dist-ℚ` carrier the untruncated trace of an unbounded
-- a.s.-terminating loop needs lower reals (cf. the expectation model on the
-- probability-theory branch); every BOUNDED loop (all we need for reactive
-- machine composition with per-activation bounds) already lives here.

open import categorical-crypto.Prelude hiding (Stable)

open import Data.Nat using (_≤_)

open import Class.Core
open import Class.Monad
open import Class.Monad.Ext.Setoid

open import Categories.Category.Core using (Category)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.RationalDist.Partial

open import CategoricalCrypto.SFunM

module CategoricalCrypto.SFunPartial where

private variable
  A B : Type
  X : Type

-- The category of partial probabilistic stateful functions.
SFun⊥ : Type → Type → Type₁
SFun⊥ = SFunᵉ {M = Dist⊥}

SFun⊥-Category : Category _ _ _
SFun⊥-Category = SFunᵉ-Category {M = Dist⊥}

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

-- Dropping an empty (⊥) interface component.
unbot : {B : Type} → ⊥ ⊎ B → B
unbot (inj₂ b) = b

strip⊥ : {A B : Type} → SFun⊥ (⊥ ⊎ A) (⊥ ⊎ B) → SFun⊥ A B
strip⊥ f = record
  { State = SFunᵉ.State f
  ; init  = SFunᵉ.init f
  ; fun   = λ sa → SFunᵉ.fun f (proj₁ sa , inj₂ (proj₂ sa))
                     >>=⊥ λ sr → return⊥ (proj₁ sr , unbot (proj₂ sr))
  }

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
-- the `n`-th such approximant (`iterFuel`-bounded); the real `∘ᵍ` (postulated
-- in `MerkleDamgard`) is their limit: `∘ᵍ` is the ⊎-trace over the middle
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
