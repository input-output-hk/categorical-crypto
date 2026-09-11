{-# OPTIONS --safe --without-K #-}

-- Liveness: a protocol whose steps never diverge plays every strategy to a
-- verdict.
--
-- `Protocol.Machine.Total.totalRun-morphism` takes exactly `live`'s conclusion
-- as its side condition, and calls it a side condition because `evalC` sends
-- `dead` to the `nothing` sink and nothing else does.  So the condition is
-- STRUCTURAL — the step trees carry no `dead` — which is what `NoDead` says.
-- `dead` is only ever written by a protocol author: `_>>=ᶜ_`, `graft`, `serve`
-- and `fromCall` propagate it and never create it, so `NoDead` is
-- compositional and a concrete system discharges it by name.

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Ext using (IsJust)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₂)
open import Data.Rational as ℚ using (ℚ; 1ℚ)
open import Data.Rational.Properties
  using (+-identityˡ; +-identityʳ; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (sym)

open import ProbabilisticLogic.Distribution.RationalDist
  using (OnSupport; OnSupport-bind; OnSupport-return)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
  using (E-add; E-const; E-mono-on; maybeℚ)
open import ProbabilisticLogic.Distribution.RationalDist.Partial using (Dist⊥; kmaybe)
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Prelude using (Prᵇ⊥)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.OracleCall using (Call)
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe using (Prᵇ; evalC; run; runFrom)
open import CategoricalCrypto.Strategy using (Strat; ask; coin; out)

module CategoricalCrypto.Protocol.Live where

private variable X : Set
                 A B C : Iface

------------------------------------------------------------------------
-- Dead-free call trees

NoDead : Calls A X → Set
NoDead (ret _)    = ⊤
NoDead (call _ k) = ∀ r → NoDead (k r)
NoDead (coin _ k) = ∀ b → NoDead (k b)
NoDead dead       = ⊥

NoDeadStep : Protocol A B → Set
NoDeadStep {B = B} P = (s : St P) (q : Neg B) → NoDead (step P s q)

-- An oracle call is one query and an answer; there is no way to write `dead`
-- with it, which is why an example built out of `Call` never has to argue.
nodead-fromCall : (c : Call (Neg A) (Pos A) X) → NoDead (fromCall c)
nodead-fromCall (inj₁ _)       = tt
nodead-fromCall (inj₂ (_ , _)) = λ _ → tt

nodead-uniformVec : (n : ℕ) (k : Vec Bool n → Calls A X)
                  → ((v : Vec Bool n) → NoDead (k v)) → NoDead (uniformVec n k)
nodead-uniformVec zero    k h = h []
nodead-uniformVec (suc n) k h b =
  nodead-uniformVec n (λ v → k (b ∷ v)) (λ v → h (b ∷ v))

module _ (P₂ : Protocol B C) (P₁ : Protocol A B) (nd₁ : NoDeadStep P₁) where

  mutual

    nodead-graft : (t : Calls B (St P₂ × Pos C)) → NoDead t → (s₁ : St P₁)
                 → NoDead (graft P₂ P₁ t s₁)
    nodead-graft (ret _)    _  _  = tt
    nodead-graft (call b k) nd s₁ = nodead-serve k nd (step P₁ s₁ b) (nd₁ s₁ b)
    nodead-graft (coin _ k) nd s₁ = λ x → nodead-graft (k x) (nd x) s₁
    nodead-graft dead       nd _  = ⊥-elim nd

    nodead-serve : (k : Pos B → Calls B (St P₂ × Pos C)) → ((r : Pos B) → NoDead (k r))
                 → (t : Calls A (St P₁ × Pos B)) → NoDead t → NoDead (serve P₂ P₁ k t)
    nodead-serve k hk (ret (s₁ , b⁺)) _  = nodead-graft (k b⁺) (hk b⁺) s₁
    nodead-serve k hk (call _ k₁)     nd = λ r → nodead-serve k hk (k₁ r) (nd r)
    nodead-serve k hk (coin _ k₁)     nd = λ x → nodead-serve k hk (k₁ x) (nd x)
    nodead-serve _ _  dead            nd = ⊥-elim nd

  nodead-∘ᵖ : NoDeadStep P₂ → NoDeadStep (P₂ ∘ᵖ P₁)
  nodead-∘ᵖ nd₂ (s₂ , s₁) c = nodead-graft (step P₂ s₂ c) (nd₂ s₂ c) s₁

------------------------------------------------------------------------
-- …and the mass they carry

-- `evalC-support` is the same recursion at a predicate that is VACUOUS on the
-- sink (`Reached P nothing = ⊤`), which is what a safety invariant wants and
-- what a mass statement cannot use.  `IsJust` is the sink's complement.
evalC-just : (t : Calls unitᴵ X) → NoDead t → OnSupport IsJust (evalC t)
evalC-just (ret _)    _  = OnSupport-return tt
evalC-just (call q _) _  = ⊥-elim q
evalC-just (coin μ k) nd = OnSupport-bind μ (λ b → evalC (k b))
                             (All.universal (λ _ → tt) _) (λ b _ → evalC-just (k b) (nd b))
evalC-just dead       nd = ⊥-elim nd

runFrom-just : {B : Iface} (P : Protocol unitᴵ B) → NoDeadStep P → (s : St P)
               (d : Strat (Neg B) (Pos B)) → OnSupport IsJust (runFrom P s d)
runFrom-just _ _  _ (out _)    = OnSupport-return tt
runFrom-just {B} P nd s (ask q k)  =
  OnSupport-bind (evalC (step P s q)) (kmaybe cont) (evalC-just _ (nd s q)) served
  where
  cont : St P × Pos B → Dist⊥ Bool
  cont (s′ , r) = runFrom P s′ (k r)

  served : (x : Maybe (St P × Pos B)) → IsJust x → OnSupport IsJust (kmaybe cont x)
  served (just (s′ , r)) _ = runFrom-just P nd s′ (k r)
runFrom-just P nd s (coin μ k) =
  OnSupport-bind μ (λ b → runFrom P s (k b)) (All.universal (λ _ → tt) _)
                 (λ b _ → runFrom-just P nd s (k b))

-- A run charging only `just` carries mass one across the two verdicts: the two
-- indicators sum to one there, and to zero at the sink.
just-live : (μ : Dist⊥ Bool) → OnSupport IsJust μ
          → 1ℚ ℚ.≤ Prᵇ⊥ true μ ℚ.+ Prᵇ⊥ false μ
just-live μ os =
  ≤-trans (≤-reflexive (sym (E-const μ 1ℚ)))
    (≤-trans (E-mono-on μ (λ _ → 1ℚ) both (All.map (λ {e} → pt (proj₂ e)) os))
             (≤-reflexive (E-add μ (maybeℚ (indᵇ true)) (maybeℚ (indᵇ false)))))
  where
  both : Maybe Bool → ℚ
  both x = maybeℚ (indᵇ true) x ℚ.+ maybeℚ (indᵇ false) x

  pt : (x : Maybe Bool) → IsJust x → 1ℚ ℚ.≤ both x
  pt (just true)  _ = ≤-reflexive (sym (+-identityʳ 1ℚ))
  pt (just false) _ = ≤-reflexive (sym (+-identityˡ 1ℚ))

live : (P : Protocol unitᴵ B) → NoDeadStep P
     → (d : Strat (Neg B) (Pos B)) → 1ℚ ℚ.≤ Prᵇ P true d ℚ.+ Prᵇ P false d
live P nd d = just-live (run P d) (runFrom-just P nd (init P) d)
