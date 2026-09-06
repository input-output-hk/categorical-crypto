{-# OPTIONS --safe --without-K --guardedness #-}

-- Functoriality of the semantics functor: `morphism (P₂ ∘ᵖ P₁)` and
-- `morphism P₂ 𝒢.∘ morphism P₁` are the same hom of `𝒢ₚ`.
--
-- `Machines.Collapse` reduces the right-hand side to ONE traced machine whose
-- pre-trace step `kᴳ` dispatches a letter to the factor that owns it; what is
-- left is that solving that machine's loop within a step is what `_∘ᵖ_`'s
-- `graft`/`serve` do syntactically, which is a structural induction on the two
-- call trees (`ι-graft`/`ι-serve`).
--
-- The simulation runs through a THIRD machine, `machineᶜ`, whose state names
-- exactly the composite's reachable configurations: both factors idle, or both
-- suspended on the call they made.  Neither `_≲_` between the two sides exists
-- on its own.  Forwards, a grafted `wait` holds `serve k₂ ∘ k₁` and the two
-- continuations cannot be recovered from it.  Backwards, the pair
-- `(idle , wait)` — the outer factor idle while the inner one is suspended —
-- is unreachable but would still have to be mapped somewhere, and no target
-- works: on a query from `C` it must behave like an idle composite, on an
-- answer from `A` like a suspended one, and `MSt` is one or the other.
-- `machineᶜ` drops that configuration, and both legs become simulations *out*
-- of it, which is all an `EqClosure` needs.  The intermediate
-- `(wait , idle)` — the outer factor suspended mid-loop — never surfaces:
-- `traceᴹ` solves the loop inside one step.
--
-- Measured cost: 269 s warm, of which everything but `morphism-∘` is 11 s — the
-- rest is projecting `_∘_` out of `𝒢ₚ`'s G-construction record, which is what
-- stating anything about `𝒢ₚ`'s composition costs (`Machines.Collapse`'s header
-- prices the two ways of paying it).

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.Protocol.Machine.Compose where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MT = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module V  = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module E  = Elgotᵏ 0ℓ
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})

module _ {A B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol A B) where

  ------------------------------------------------------------------------
  -- The reachable-configuration machine

  data CSt : Set where
    both : St P₂ → St P₁ → CSt
    susp : (Pos B → Calls B (St P₂ × Pos C))
         → (Pos A → Calls A (St P₁ × Pos B)) → CSt

  stateᶜ : MC.State
  stateᶜ = record
    { obj     = CSt
    ; point   = λ _ → returnₚ (both (init P₂) (init P₁))
    ; discard = λ _ → returnₚ tt
    }

  -- Driving a call tree while keeping the configuration: the two clauses that
  -- park a continuation are where `CSt` is finer than `MSt`.
  mutual
    serveᶜ : (Pos B → Calls B (St P₂ × Pos C)) → Calls A (St P₁ × Pos B)
           → Dₚ (CSt × (Neg A ⊎ Pos C))
    serveᶜ k₂ (ret (s₁ , b⁺)) = graftᶜ (k₂ b⁺) s₁
    serveᶜ k₂ (call a k₁)     = returnₚ (susp k₂ k₁ , inj₁ a)
    serveᶜ k₂ (coin μ k₁)     = coinₚ μ >>=ₚ λ b → serveᶜ k₂ (k₁ b)
    serveᶜ k₂ dead            = botₚ

    graftᶜ : Calls B (St P₂ × Pos C) → St P₁ → Dₚ (CSt × (Neg A ⊎ Pos C))
    graftᶜ (ret (s₂ , c⁺)) s₁ = returnₚ (both s₂ s₁ , inj₂ c⁺)
    graftᶜ (call b k₂)     s₁ = serveᶜ k₂ (step P₁ s₁ b)
    graftᶜ (coin μ k₂)     s₁ = coinₚ μ >>=ₚ λ x → graftᶜ (k₂ x) s₁
    graftᶜ dead            s₁ = botₚ

  stepᶜ : CSt × (Pos A ⊎ Neg C) → Dₚ (CSt × (Neg A ⊎ Pos C))
  stepᶜ (both s₂ s₁ , inj₂ c⁻) = graftᶜ (step P₂ s₂ c⁻) s₁
  stepᶜ (susp k₂ k₁ , inj₁ a⁺) = serveᶜ k₂ (k₁ a⁺)
  stepᶜ (both _  _  , inj₁ _)  = botₚ
  stepᶜ (susp _  _  , inj₂ _)  = botₚ

  machineᶜ : MC.Machine (Pos A ⊎ Neg C) (Neg A ⊎ Pos C)
  machineᶜ = MC.mk stateᶜ stepᶜ

  ------------------------------------------------------------------------
  -- Into the grafted machine

  private
    π : CSt → MSt (P₂ ∘ᵖ P₁)
    π (both s₂ s₁) = idle (s₂ , s₁)
    π (susp k₂ k₁) = wait λ a → serve P₂ P₁ k₂ (k₁ a)

    πpad : CSt × (Neg A ⊎ Pos C) → Dₚ (MSt (P₂ ∘ᵖ P₁) × (Neg A ⊎ Pos C))
    πpad z = returnₚ (π (proj₁ z) , proj₂ z)

    -- The two drives agree, one call node at a time.  `serve`'s own recursion,
    -- so the termination argument is `_∘ᵖ_`'s.
    mutual
      π-serve : (k₂ : Pos B → Calls B (St P₂ × Pos C)) (t : Calls A (St P₁ × Pos B))
              → (serveᶜ k₂ t >>=ₚ πpad) ≈ₚ drive (P₂ ∘ᵖ P₁) (serve P₂ P₁ k₂ t)
      π-serve k₂ (ret (s₁ , b⁺)) = π-graft (k₂ b⁺) s₁
      π-serve k₂ (call a k₁)     = >>=ₚ-identityˡ (susp k₂ k₁ , inj₁ a) πpad
      π-serve k₂ (coin μ k₁)     = >>=ₚ-assoc (coinₚ μ) _ _
                                 ⟨≈⟩ bindᶠ (λ b → π-serve k₂ (k₁ b))
      π-serve k₂ dead            = bot-bind-≈ₚ πpad

      π-graft : (t : Calls B (St P₂ × Pos C)) (s₁ : St P₁)
              → (graftᶜ t s₁ >>=ₚ πpad) ≈ₚ drive (P₂ ∘ᵖ P₁) (graft P₂ P₁ t s₁)
      π-graft (ret (s₂ , c⁺)) s₁ = >>=ₚ-identityˡ (both s₂ s₁ , inj₂ c⁺) πpad
      π-graft (call b k₂)     s₁ = π-serve k₂ (step P₁ s₁ b)
      π-graft (coin μ k₂)     s₁ = >>=ₚ-assoc (coinₚ μ) _ _
                                 ⟨≈⟩ bindᶠ (λ x → π-graft (k₂ x) s₁)
      π-graft dead            s₁ = bot-bind-≈ₚ πpad

    π-step : (z : CSt × (Pos A ⊎ Neg C))
           → (stepᶜ z >>=ₚ (K.pureᵏ π V.⊗₁ V.id))
           ≈ₚ ((K.pureᵏ π V.⊗₁ V.id) z >>=ₚ stepᴹ (P₂ ∘ᵖ P₁))
    π-step (both s₂ s₁ , inj₂ c⁻) =
      bindᶠ (Col.⊗-pureˡ π) ⟨≈⟩ π-graft (step P₂ s₂ c⁻) s₁
      ⟨≈⟩ ≈sym ( bindˣ (Col.⊗-pureˡ π (both s₂ s₁ , inj₂ c⁻))
               ⟨≈⟩ >>=ₚ-identityˡ (idle (s₂ , s₁) , inj₂ c⁻) _)
    π-step (susp k₂ k₁ , inj₁ a⁺) =
      bindᶠ (Col.⊗-pureˡ π) ⟨≈⟩ π-serve k₂ (k₁ a⁺)
      ⟨≈⟩ ≈sym ( bindˣ (Col.⊗-pureˡ π (susp k₂ k₁ , inj₁ a⁺))
               ⟨≈⟩ >>=ₚ-identityˡ (π (susp k₂ k₁) , inj₁ a⁺) _)
    π-step (both s₂ s₁ , inj₁ a⁺) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym ( bindˣ (Col.⊗-pureˡ π (both s₂ s₁ , inj₁ a⁺))
               ⟨≈⟩ >>=ₚ-identityˡ (idle (s₂ , s₁) , inj₁ a⁺) _)
    π-step (susp k₂ k₁ , inj₂ c⁻) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym ( bindˣ (Col.⊗-pureˡ π (susp k₂ k₁ , inj₂ c⁻))
               ⟨≈⟩ >>=ₚ-identityˡ (π (susp k₂ k₁) , inj₂ c⁻) _)

  π-sim : machineᶜ S.≲ morphism (P₂ ∘ᵖ P₁)
  π-sim = S.sim (K.pureᵏ π) (KP.structural π)
                (λ r → >>=ₚ-identityˡ (π r) _)
                (λ _ → >>=ₚ-identityˡ (both (init P₂) (init P₁)) _)
                π-step

  ------------------------------------------------------------------------
  -- Into the G-composite

  private
    Sᴳ : MC.State
    Sᴳ = Col.Sᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C} (morphism P₂) (morphism P₁)

    kᴳ : MC.obj Sᴳ × ((Pos A ⊎ Neg C) ⊎ (Neg B ⊎ Pos B))
       → Dₚ (MC.obj Sᴳ × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B)))
    kᴳ = Col.kᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C} (morphism P₂) (morphism P₁)

    -- The trace's loop, as a `Dp.Iter` body, and its dispatch: exit on the
    -- outer interfaces, iterate on the shared one.
    loop : Body (MC.obj Sᴳ) (Neg B ⊎ Pos B) (Neg A ⊎ Pos C)
    loop (m , l) = kᴳ (m , inj₂ l)

    exit : MC.obj Sᴳ × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B))
         → Dₚ (MC.obj Sᴳ × (Neg A ⊎ Pos C))
    exit = contᵢ loop

    ι : CSt → MC.obj Sᴳ
    ι (both s₂ s₁) = idle s₂ , idle s₁
    ι (susp k₂ k₁) = wait k₂ , wait k₁

    ιpad : CSt × (Neg A ⊎ Pos C) → Dₚ (MC.obj Sᴳ × (Neg A ⊎ Pos C))
    ιpad z = returnₚ (ι (proj₁ z) , proj₂ z)

    -- Solving the loop is grafting.  Each `ret`/`call` clause that hands a
    -- letter to the *other* factor unfolds `iterₚ` once, and the mutual call
    -- lands on the other lemma; the composite's own recursion again.
    mutual
      ι-serve : (k₂ : Pos B → Calls B (St P₂ × Pos C)) (t : Calls A (St P₁ × Pos B))
              → (serveᶜ k₂ t >>=ₚ ιpad)
              ≈ₚ (drive P₁ t >>=ₚ λ r → exit ((wait k₂ , proj₁ r) , Col.outᶠ (proj₂ r)))
      ι-serve k₂ (ret (s₁ , b⁺)) =
        ι-graft (k₂ b⁺) s₁
        ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (idle s₁ , inj₂ b⁺) _
                 ⟨≈⟩ iterₚ-fix loop ((wait k₂ , idle s₁) , inj₂ b⁺)
                 ⟨≈⟩ >>=ₚ-assoc (drive P₂ (k₂ b⁺)) _ _
                 ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , idle s₁) , Col.outᵍ (proj₂ r)) exit))
      ι-serve k₂ (call a k₁) =
        >>=ₚ-identityˡ (susp k₂ k₁ , inj₁ a) ιpad
        ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (wait k₁ , inj₁ a) _)
      ι-serve k₂ (coin μ k₁) =
        >>=ₚ-assoc (coinₚ μ) _ _
        ⟨≈⟩ bindᶠ (λ b → ι-serve k₂ (k₁ b))
        ⟨≈⟩ ≈sym (>>=ₚ-assoc (coinₚ μ) _ _)
      ι-serve k₂ dead = bot-bind-≈ₚ ιpad ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)

      ι-graft : (t : Calls B (St P₂ × Pos C)) (s₁ : St P₁)
              → (graftᶜ t s₁ >>=ₚ ιpad)
              ≈ₚ (drive P₂ t >>=ₚ λ r → exit ((proj₁ r , idle s₁) , Col.outᵍ (proj₂ r)))
      ι-graft (ret (s₂ , c⁺)) s₁ =
        >>=ₚ-identityˡ (both s₂ s₁ , inj₂ c⁺) ιpad
        ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (idle s₂ , inj₂ c⁺) _)
      ι-graft (call b k₂) s₁ =
        ι-serve k₂ (step P₁ s₁ b)
        ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (wait k₂ , inj₁ b) _
                 ⟨≈⟩ iterₚ-fix loop ((wait k₂ , idle s₁) , inj₁ b)
                 ⟨≈⟩ >>=ₚ-assoc (drive P₁ (step P₁ s₁ b)) _ _
                 ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((wait k₂ , proj₁ r) , Col.outᶠ (proj₂ r)) exit))
      ι-graft (coin μ k₂) s₁ =
        >>=ₚ-assoc (coinₚ μ) _ _
        ⟨≈⟩ bindᶠ (λ x → ι-graft (k₂ x) s₁)
        ⟨≈⟩ ≈sym (>>=ₚ-assoc (coinₚ μ) _ _)
      ι-graft dead s₁ = bot-bind-≈ₚ ιpad ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)

    -- `traceStep` at a point: feed the letter in on the external summand, then
    -- dispatch.  `δ⇐-contᵢ` is what identifies the dispatch with `contᵢ`.
    bodyᴹ : Body (MC.obj Sᴳ) (Neg B ⊎ Pos B) (Neg A ⊎ Pos C)
    bodyᴹ = MT.loopBody Sᴳ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) kᴳ

    loop-pt : (w : MC.obj Sᴳ × (Neg B ⊎ Pos B)) → bodyᴹ w ≈ₚ loop w
    loop-pt w = bindˣ (Col.⊗-pure inj₂ w)
              ⟨≈⟩ >>=ₚ-identityˡ (proj₁ w , inj₂ (proj₂ w)) kᴳ

    solve-pt : (w : MC.obj Sᴳ × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B)))
             → MT.solve Sᴳ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) kᴳ w ≈ₚ exit w
    solve-pt w = E.δ⇐-contᵢ bodyᴹ w ⟨≈⟩ cont-pt w
      where
      cont-pt : (w′ : MC.obj Sᴳ × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B)))
              → contᵢ bodyᴹ w′ ≈ₚ exit w′
      cont-pt (_ , inj₁ _) = ≈refl
      cont-pt (m , inj₂ l) = iterₚ-cong bodyᴹ loop loop-pt (m , l)

    trace-pt : (z : MC.obj Sᴳ × (Pos A ⊎ Neg C))
             → MT.traceStep Sᴳ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) kᴳ z
             ≈ₚ (kᴳ (proj₁ z , inj₁ (proj₂ z)) >>=ₚ exit)
    trace-pt z = bindˣ ( bindˣ (Col.⊗-pure inj₁ z)
                       ⟨≈⟩ >>=ₚ-identityˡ (proj₁ z , inj₁ (proj₂ z)) kᴳ)
               ⟨≈⟩ bindᶠ solve-pt

    ι-step : (z : CSt × (Pos A ⊎ Neg C))
           → (stepᶜ z >>=ₚ (K.pureᵏ ι V.⊗₁ V.id))
           ≈ₚ ((K.pureᵏ ι V.⊗₁ V.id) z
                >>=ₚ MT.traceStep Sᴳ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) kᴳ)
    ι-step (both s₂ s₁ , inj₂ c⁻) =
      bindᶠ (Col.⊗-pureˡ ι) ⟨≈⟩ ι-graft (step P₂ s₂ c⁻) s₁
      ⟨≈⟩ ≈sym ( bindˣ (Col.⊗-pureˡ ι (both s₂ s₁ , inj₂ c⁻))
               ⟨≈⟩ >>=ₚ-identityˡ ((idle s₂ , idle s₁) , inj₂ c⁻) _
               ⟨≈⟩ trace-pt ((idle s₂ , idle s₁) , inj₂ c⁻)
               ⟨≈⟩ >>=ₚ-assoc (drive P₂ (step P₂ s₂ c⁻)) _ _
               ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , idle s₁) , Col.outᵍ (proj₂ r)) exit))
    ι-step (susp k₂ k₁ , inj₁ a⁺) =
      bindᶠ (Col.⊗-pureˡ ι) ⟨≈⟩ ι-serve k₂ (k₁ a⁺)
      ⟨≈⟩ ≈sym ( bindˣ (Col.⊗-pureˡ ι (susp k₂ k₁ , inj₁ a⁺))
               ⟨≈⟩ >>=ₚ-identityˡ ((wait k₂ , wait k₁) , inj₁ a⁺) _
               ⟨≈⟩ trace-pt ((wait k₂ , wait k₁) , inj₁ a⁺)
               ⟨≈⟩ >>=ₚ-assoc (drive P₁ (k₁ a⁺)) _ _
               ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((wait k₂ , proj₁ r) , Col.outᶠ (proj₂ r)) exit))
    ι-step (both s₂ s₁ , inj₁ a⁺) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym ( bindˣ (Col.⊗-pureˡ ι (both s₂ s₁ , inj₁ a⁺))
               ⟨≈⟩ >>=ₚ-identityˡ ((idle s₂ , idle s₁) , inj₁ a⁺) _
               ⟨≈⟩ trace-pt ((idle s₂ , idle s₁) , inj₁ a⁺)
               ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ exit)
    ι-step (susp k₂ k₁ , inj₂ c⁻) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym ( bindˣ (Col.⊗-pureˡ ι (susp k₂ k₁ , inj₂ c⁻))
               ⟨≈⟩ >>=ₚ-identityˡ ((wait k₂ , wait k₁) , inj₂ c⁻) _
               ⟨≈⟩ trace-pt ((wait k₂ , wait k₁) , inj₂ c⁻)
               ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ exit)

  ι-sim : machineᶜ S.≲ MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
                                 (MC.mk Sᴳ kᴳ)
  ι-sim = S.sim (K.pureᵏ ι) (KP.structural ι)
                (λ r → >>=ₚ-identityˡ (ι r) _
                     ⟨≈⟩ bindˣ (>>=ₚ-identityˡ tt _ ⟨≈⟩ >>=ₚ-identityˡ tt _)
                     ⟨≈⟩ >>=ₚ-identityˡ (tt , tt) _)
                (λ x → >>=ₚ-identityˡ (both (init P₂) (init P₁)) _
                     ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                              ⟨≈⟩ >>=ₚ-identityˡ (idle (init P₂)) _
                              ⟨≈⟩ >>=ₚ-identityˡ (idle (init P₁)) _))
                ι-step

------------------------------------------------------------------------
-- Functoriality

morphism-∘ : Morphism-∘
morphism-∘ {A} {B} {C} P₂ P₁ =
       S.⟺ᴹ (S.≲⇒≈ᴹ (π-sim P₂ P₁))
  S.○ᴹ S.≲⇒≈ᴹ (ι-sim P₂ P₁)
  S.○ᴹ S.⟺ᴹ (Col.collapseᵀ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C}
                           (morphism P₂) (morphism P₁))
