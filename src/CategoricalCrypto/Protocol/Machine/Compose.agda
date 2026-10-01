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
-- The simulation runs through a THIRD machine, `machineᶜ`, whose state is
-- exactly the composite's reachable configurations: both factors idle, or both
-- suspended on the call they made.  No `_≲_` runs directly between the two
-- sides — a grafted `wait` holds `serve k₂ ∘ k₁`, from which the two
-- continuations cannot be recovered, and the unreachable `(idle , wait)` has no
-- `MSt` image — so both legs are simulations *out of* `machineᶜ`, which is all
-- an `EqClosure` needs (`(wait , idle)` never surfaces: `traceᴹ` solves the
-- loop inside one step).
--
-- The theorem names the G-composition before it is packed into `𝒢ₚ`'s Category
-- record.  This is definitionally the same operation but avoids projecting
-- `_∘_` through the assembled G-construction.  Measured warm cost: 11 s.

open import Categories.Category

open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Level

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
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.Protocol.Machine.Compose where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MT = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

module _ {A B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol A B) where

  ------------------------------------------------------------------------
  -- The reachable-configuration machine

  data CSt : Set where
    both : St P₂ → St P₁ → CSt
    susp : (Pos B → Calls B (St P₂ × Pos C)) → (Pos A → Calls A (St P₁ × Pos B)) → CSt

  stateᶜ : MC.State
  stateᶜ = record { obj = CSt ; point = λ _ → returnₚ (both (init P₂) (init P₁)) }

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

    mutual
      π-serve : (k₂ : Pos B → Calls B (St P₂ × Pos C)) (t : Calls A (St P₁ × Pos B))
              → (serveᶜ k₂ t >>=ₚ Pw.padϕ π) ≈ₚ drive (P₂ ∘ᵖ P₁) (serve P₂ P₁ k₂ t)
      π-serve k₂ (ret (s₁ , b⁺)) = π-graft (k₂ b⁺) s₁
      π-serve k₂ (call a k₁)     = >>=ₚ-identityˡ (susp k₂ k₁ , inj₁ a) (Pw.padϕ π)
      π-serve k₂ (coin μ k₁)     = >>=ₚ-assoc (coinₚ μ) _ _ ⟨≈⟩ bindᶠ (λ b → π-serve k₂ (k₁ b))
      π-serve k₂ dead            = bot-bind-≈ₚ (Pw.padϕ π)

      π-graft : (t : Calls B (St P₂ × Pos C)) (s₁ : St P₁)
              → (graftᶜ t s₁ >>=ₚ Pw.padϕ π) ≈ₚ drive (P₂ ∘ᵖ P₁) (graft P₂ P₁ t s₁)
      π-graft (ret (s₂ , c⁺)) s₁ = >>=ₚ-identityˡ (both s₂ s₁ , inj₂ c⁺) (Pw.padϕ π)
      π-graft (call b k₂)     s₁ = π-serve k₂ (step P₁ s₁ b)
      π-graft (coin μ k₂)     s₁ = >>=ₚ-assoc (coinₚ μ) _ _ ⟨≈⟩ bindᶠ (λ x → π-graft (k₂ x) s₁)
      π-graft dead            s₁ = bot-bind-≈ₚ (Pw.padϕ π)

    π-step : (z : CSt × (Pos A ⊎ Neg C))
           → (stepᶜ z >>=ₚ Pw.padϕ π) ≈ₚ stepᴹ (P₂ ∘ᵖ P₁) (π (proj₁ z) , proj₂ z)
    π-step (both s₂ s₁ , inj₂ c⁻) = π-graft (step P₂ s₂ c⁻) s₁
    π-step (susp k₂ k₁ , inj₁ a⁺) = π-serve k₂ (k₁ a⁺)
    π-step (both _  _  , inj₁ _)  = bot-bind-≈ₚ (Pw.padϕ π)
    π-step (susp _  _  , inj₂ _)  = bot-bind-≈ₚ (Pw.padϕ π)

  π-sim : machineᶜ S.≲ morphism (P₂ ∘ᵖ P₁)
  π-sim = Pw.simFn π (λ _ → >>=ₚ-identityˡ (both (init P₂) (init P₁)) _) π-step

  ------------------------------------------------------------------------
  -- Into the G-composite

  private
    Sᴳ : MC.State
    Sᴳ = Col.Sᴳ {Pos A} {Neg A} (morphism P₂) (morphism P₁)

    kᴳ : MC.obj Sᴳ × ((Pos A ⊎ Neg C) ⊎ (Neg B ⊎ Pos B))
       → Dₚ (MC.obj Sᴳ × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B)))
    kᴳ = Col.kᴳ {Pos A} {Neg A} {Pos B} {Neg B} (morphism P₂) (morphism P₁)

    open Col.Loop (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) Sᴳ kᴳ

    exit : MC.obj Sᴳ × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B)) → Dₚ (MC.obj Sᴳ × (Neg A ⊎ Pos C))
    exit = contᵢ body

    ι : CSt → MC.obj Sᴳ
    ι (both s₂ s₁) = idle s₂ , idle s₁
    ι (susp k₂ k₁) = wait k₂ , wait k₁

    mutual
      ι-serve : (k₂ : Pos B → Calls B (St P₂ × Pos C)) (t : Calls A (St P₁ × Pos B))
              → (serveᶜ k₂ t >>=ₚ Pw.padϕ ι)
              ≈ₚ (drive P₁ t >>=ₚ λ r → exit ((wait k₂ , proj₁ r) , Col.outᶠ (proj₂ r)))
      ι-serve k₂ (ret (s₁ , b⁺)) =
        ι-graft (k₂ b⁺) s₁
        ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (idle s₁ , inj₂ b⁺) _
                 ⟨≈⟩ iterₚ-fix body ((wait k₂ , idle s₁) , inj₂ b⁺)
                 ⟨≈⟩ >>=ₚ-assoc (drive P₂ (k₂ b⁺)) _ _
                 ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , idle s₁) , Col.outᵍ (proj₂ r)) exit))
      ι-serve k₂ (call a k₁) =
        >>=ₚ-identityˡ (susp k₂ k₁ , inj₁ a) (Pw.padϕ ι)
        ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (wait k₁ , inj₁ a) _)
      ι-serve k₂ (coin μ k₁) =
        >>=ₚ-assoc (coinₚ μ) _ _
        ⟨≈⟩ bindᶠ (λ b → ι-serve k₂ (k₁ b))
        ⟨≈⟩ ≈sym (>>=ₚ-assoc (coinₚ μ) _ _)
      ι-serve k₂ dead = bot-bind-≈ₚ (Pw.padϕ ι) ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)

      ι-graft : (t : Calls B (St P₂ × Pos C)) (s₁ : St P₁)
              → (graftᶜ t s₁ >>=ₚ Pw.padϕ ι)
              ≈ₚ (drive P₂ t >>=ₚ λ r → exit ((proj₁ r , idle s₁) , Col.outᵍ (proj₂ r)))
      ι-graft (ret (s₂ , c⁺)) s₁ =
        >>=ₚ-identityˡ (both s₂ s₁ , inj₂ c⁺) (Pw.padϕ ι)
        ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (idle s₂ , inj₂ c⁺) _)
      ι-graft (call b k₂) s₁ =
        ι-serve k₂ (step P₁ s₁ b)
        ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (wait k₂ , inj₁ b) _
                 ⟨≈⟩ iterₚ-fix body ((wait k₂ , idle s₁) , inj₁ b)
                 ⟨≈⟩ >>=ₚ-assoc (drive P₁ (step P₁ s₁ b)) _ _
                 ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((wait k₂ , proj₁ r) , Col.outᶠ (proj₂ r)) exit))
      ι-graft (coin μ k₂) s₁ =
        >>=ₚ-assoc (coinₚ μ) _ _
        ⟨≈⟩ bindᶠ (λ x → ι-graft (k₂ x) s₁)
        ⟨≈⟩ ≈sym (>>=ₚ-assoc (coinₚ μ) _ _)
      ι-graft dead s₁ = bot-bind-≈ₚ (Pw.padϕ ι) ⟨≈⟩ ≈sym (bot-bind-≈ₚ _)

    ι-step : (z : CSt × (Pos A ⊎ Neg C))
           → (stepᶜ z >>=ₚ Pw.padϕ ι)
           ≈ₚ MT.traceStep Sᴳ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) kᴳ
                (ι (proj₁ z) , proj₂ z)
    ι-step (both s₂ s₁ , inj₂ c⁻) =
      ι-graft (step P₂ s₂ c⁻) s₁
      ⟨≈⟩ ≈sym ( step-red (idle s₂ , idle s₁) (inj₂ c⁻)
               ⟨≈⟩ >>=ₚ-assoc (drive P₂ (step P₂ s₂ c⁻)) _ _
               ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , idle s₁) , Col.outᵍ (proj₂ r)) exit))
    ι-step (susp k₂ k₁ , inj₁ a⁺) =
      ι-serve k₂ (k₁ a⁺)
      ⟨≈⟩ ≈sym ( step-red (wait k₂ , wait k₁) (inj₁ a⁺)
               ⟨≈⟩ >>=ₚ-assoc (drive P₁ (k₁ a⁺)) _ _
               ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((wait k₂ , proj₁ r) , Col.outᶠ (proj₂ r)) exit))
    ι-step (both s₂ s₁ , inj₁ a⁺) =
      bot-bind-≈ₚ (Pw.padϕ ι)
      ⟨≈⟩ ≈sym (step-red (idle s₂ , idle s₁) (inj₁ a⁺) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ exit)
    ι-step (susp k₂ k₁ , inj₂ c⁻) =
      bot-bind-≈ₚ (Pw.padϕ ι)
      ⟨≈⟩ ≈sym (step-red (wait k₂ , wait k₁) (inj₂ c⁻) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ exit)

  ι-sim : machineᶜ S.≲ MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B) (MC.mk Sᴳ kᴳ)
  ι-sim = Pw.simFn ι
            (λ x → >>=ₚ-identityˡ (both (init P₂) (init P₁)) _
                 ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (tt , x) _
                          ⟨≈⟩ >>=ₚ-identityˡ (idle (init P₂)) _
                          ⟨≈⟩ >>=ₚ-identityˡ (idle (init P₁)) _))
            ι-step

------------------------------------------------------------------------
-- Functoriality

morphism-∘ : {A B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol A B)
           → morphism (P₂ ∘ᵖ P₁) S.≈ᴹ
             Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
               (Col.W.α {Neg A} {Pos B} {Neg B} Pw.MC.∘ᴹ
                 ((morphism P₂ Pw.T.⊗ᵉ morphism P₁) Pw.MC.∘ᴹ
                   Col.W.γ {Pos A} {Pos B} {Neg B}))
morphism-∘ {A} {B} {C} P₂ P₁ =
       S.⟺ᴹ (S.≲⇒≈ᴹ (π-sim P₂ P₁))
  S.○ᴹ S.≲⇒≈ᴹ (ι-sim P₂ P₁)
  S.○ᴹ S.⟺ᴹ (Col.collapseᵀ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C}
                           (morphism P₂) (morphism P₁))

-- …and at `𝒢`'s own composition.  Every polarity is passed explicitly, for
-- the reason at `UC.Machine.𝒫ᴵ`.
morphismCompose : {A B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol A B)
                → 𝒢ₚ 0ℓ [ morphism (P₂ ∘ᵖ P₁) ≈ 𝒢ₚ 0ℓ [ morphism P₂ ∘ morphism P₁ ] ]
morphismCompose {A} {B} {C} P₂ P₁ =
  morphism-∘ P₂ P₁ S.○ᴹ
  Col.compose-raw≈∘ᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C}
                     (morphism P₂) (morphism P₁)
