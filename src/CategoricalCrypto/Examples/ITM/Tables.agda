{-# OPTIONS --safe --without-K --guardedness #-}

-- Each honest request returns a fresh fair bit. The adversarial request returns
-- a public marker; the simulator recodes the ideal marker and normalizes queries.

module CategoricalCrypto.Examples.ITM.Tables where

open import Categories.Category
open import Categories.FreeMonoidal

open import Data.Bool.Base
open import Data.Fin.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base hiding (map₂)
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base hiding (flip)
open import Level hiding (zero; suc)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.ITM.Run
open import CategoricalCrypto.ITM.Run.Properties
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (simFn; padϕ)
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Machine.Wire.Algebra

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MS = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open FreeMonoidalHelper Mon Pol

Service : Ports
Service = Var ⁺ ⊗₀ Var ⁻

grade-query honest-query : In unit (Service ⊗₀ Service)
grade-query  = inj₂ (inj₁ (inj₂ tt))
honest-query = inj₂ (inj₂ (inj₂ tt))

grade-reply honest-reply : Out unit (Service ⊗₀ Service)
grade-reply  = inj₂ (inj₁ (inj₁ tt))
honest-reply = inj₂ (inj₂ (inj₁ tt))

private
  reply-port : In unit (Service ⊗₀ Service) → Out unit (Service ⊗₀ Service)
  reply-port (inj₁ ())
  reply-port (inj₂ (inj₁ (inj₁ ())))
  reply-port (inj₂ (inj₁ (inj₂ _))) = grade-reply
  reply-port (inj₂ (inj₂ (inj₁ ())))
  reply-port (inj₂ (inj₂ (inj₂ _))) = honest-reply

  honest? : In unit (Service ⊗₀ Service) → Bool
  honest? (inj₁ ())
  honest? (inj₂ (inj₁ (inj₁ ())))
  honest? (inj₂ (inj₁ (inj₂ _))) = false
  honest? (inj₂ (inj₂ (inj₁ ())))
  honest? (inj₂ (inj₂ (inj₂ _))) = true

------------------------------------------------------------------------
-- Protocol tables and their initialized activations
------------------------------------------------------------------------

resource : Bool → Gen unit (Service ⊗₀ Service)
resource marker = record { #Q = 4 ; start = zero ; δ = table }
  where
  table : Fin 4 → In unit (Service ⊗₀ Service) → Sym → Sym
        → Instr (Fin 4) (Out unit (Service ⊗₀ Service))
  table zero                p _ _ = if honest? p then flip (suc zero) (suc (suc zero))
                                    else run (suc (suc (suc zero))) ␣ ∙ ∙ (just marker)
  table (suc zero)          _ _ _ = run (suc (suc (suc zero))) ␣ ∙ ∙ (just false)
  table (suc (suc zero))    _ _ _ = run (suc (suc (suc zero))) ␣ ∙ ∙ (just true)
  table (suc (suc (suc zero))) p _ _ = send (reply-port p) zero

module _ (marker : Bool) where
  private
    M = resource marker

    finish-bit : (b : Bool) (p : In unit (Service ⊗₀ Service)) (w : Bits)
               → activateᵀᴹ M (goto M (if b then suc (suc zero) else suc zero) (load M (blank M) (p , w)))
                 ≈ₚ returnₚ (blank M , reply-port p , b ∷ [])
    finish-bit false p w = activate-run M c (suc (suc (suc zero))) ␣ ∙ ∙ (just false) refl
      ⟨≈⟩ activate-send M (exec M (suc (suc (suc zero))) ␣ ∙ ∙ (just false) c) (reply-port p) zero refl
      where c = goto M (suc zero) (load M (blank M) (p , w))
    finish-bit true p w = activate-run M c (suc (suc (suc zero))) ␣ ∙ ∙ (just true) refl
      ⟨≈⟩ activate-send M (exec M (suc (suc (suc zero))) ␣ ∙ ∙ (just true) c) (reply-port p) zero refl
      where c = goto M (suc (suc zero)) (load M (blank M) (p , w))

  resource-grade : (w : Bits)
                 → runᵀᴹ M (blank M , grade-query , w) ≈ₚ returnₚ (blank M , grade-reply , marker ∷ [])
  resource-grade w = activate-run M c (suc (suc (suc zero))) ␣ ∙ ∙ (just marker) refl
    ⟨≈⟩ activate-send M (exec M (suc (suc (suc zero))) ␣ ∙ ∙ (just marker) c) grade-reply zero refl
    where c = load M (blank M) (grade-query , w)

  resource-honest : (w : Bits)
                  → runᵀᴹ M (blank M , honest-query , w)
                    ≈ₚ mapₚ (λ b → blank M , honest-reply , b ∷ []) (coinₚ uniform-Bool)
  resource-honest w = activate-flip M (load M (blank M) (honest-query , w)) (suc zero) (suc (suc zero)) refl
    ⟨≈⟩ bindᶠ (λ b → finish-bit b honest-query w)

resourceStep : Bool → Pos ⟦ unit ⟧ ⊎ Neg ⟦ Service ⊗₀ Service ⟧
             → Dₚ (Neg ⟦ unit ⟧ ⊎ Pos ⟦ Service ⊗₀ Service ⟧)
resourceStep _      (inj₁ (lift ()))
resourceStep _      (inj₂ (inj₁ (inj₁ (lift ()))))
resourceStep marker (inj₂ (inj₁ (inj₂ _))) = returnₚ (inj₂ (inj₁ (inj₁ (marker ∷ []))))
resourceStep _      (inj₂ (inj₂ (inj₁ (lift ()))))
resourceStep _      (inj₂ (inj₂ (inj₂ _))) = mapₚ (λ b → inj₂ (inj₂ (inj₁ (b ∷ [])))) (coinₚ uniform-Bool)

resourceᴹ : Bool → Proc ⟦ unit ⟧ ⟦ Service ⊗₀ Service ⟧
resourceᴹ marker = MC.mk MC.Iˢ λ (s , x) → mapₚ (s ,_) (resourceStep marker x)

resource-step-law : (marker : Bool) (x : Pos ⟦ unit ⟧ ⊎ Neg ⟦ Service ⊗₀ Service ⟧)
                  → MC.step (runᴾ {unit} {Service ⊗₀ Service} (resource marker)) (blank (resource marker) , x)
                    ≈ₚ mapₚ (blank (resource marker) ,_) (resourceStep marker x)
resource-step-law _      (inj₁ (lift ()))
resource-step-law _      (inj₂ (inj₁ (inj₁ (lift ()))))
resource-step-law marker (inj₂ (inj₁ (inj₂ w))) =
  map-arg (map₂ (encodeᴼ unit (Service ⊗₀ Service))) (resource-grade marker w)
  ⟨≈⟩ >>=ₚ-identityˡ (blank (resource marker) , grade-reply , marker ∷ []) _
  ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (inj₂ (inj₁ (inj₁ (marker ∷ [])))) _)
resource-step-law _      (inj₂ (inj₂ (inj₁ (lift ()))))
resource-step-law marker (inj₂ (inj₂ (inj₂ w))) =
  map-arg (map₂ (encodeᴼ unit (Service ⊗₀ Service))) (resource-honest marker w)
  ⟨≈⟩ map-map (coinₚ uniform-Bool) (λ b → blank (resource marker) , honest-reply , b ∷ [])
                (map₂ (encodeᴼ unit (Service ⊗₀ Service)))
  ⟨≈⟩ ≈sym (map-map (coinₚ uniform-Bool) (λ b → inj₂ (inj₂ (inj₁ (b ∷ [])))) (blank (resource marker) ,_))

resource-correct : (marker : Bool)
                 → resourceᴹ marker MS.≈ᴹ runᴾ {unit} {Service ⊗₀ Service} (resource marker)
resource-correct marker = MS.≲⇒≈ᴹ (simFn (λ _ → blank (resource marker))
  (λ _ → >>=ₚ-identityˡ ttᵛ _)
  (λ (s , x) → bind-map (resourceStep marker x) (s ,_) (padϕ (λ _ → blank (resource marker)))
                ⟨≈⟩ ≈sym (resource-step-law marker x)))

------------------------------------------------------------------------
-- A finite-table adversarial marker simulator
------------------------------------------------------------------------

private
  forward-port : In Service Service → Out Service Service
  forward-port (inj₁ (inj₁ _)) = inj₂ (inj₁ tt)
  forward-port (inj₁ (inj₂ ()))
  forward-port (inj₂ (inj₁ ()))
  forward-port (inj₂ (inj₂ _)) = inj₁ (inj₂ tt)

  response? : In Service Service → Bool
  response? (inj₁ (inj₁ _)) = true
  response? (inj₁ (inj₂ ()))
  response? (inj₂ (inj₁ ()))
  response? (inj₂ (inj₂ _)) = false

simulator : Gen Service Service
simulator = record { #Q = 2 ; start = zero ; δ = table }
  where
  table : Fin 2 → In Service Service → Sym → Sym → Instr (Fin 2) (Out Service Service)
  table zero       p _ _ = if response? p then run (suc zero) ␣ ∙ ∙ (just true)
                          else send (forward-port p) zero
  table (suc zero) p _ _ = send (forward-port p) zero

sim-up : Pos ⟦ Service ⟧ → Pos ⟦ Service ⟧
sim-up (inj₁ _) = inj₁ (true ∷ [])
sim-up (inj₂ (lift ()))

sim-down : Neg ⟦ Service ⟧ → Neg ⟦ Service ⟧
sim-down (inj₁ (lift ()))
sim-down (inj₂ _) = inj₂ []

simulatorᴹ : Proc ⟦ Service ⟧ ⟦ Service ⟧
simulatorᴹ = wireᴹ sim-up sim-down

simulator-step-law : (x : Pos ⟦ Service ⟧ ⊎ Neg ⟦ Service ⟧)
                   → MC.step (runᴾ {Service} {Service} simulator) (blank simulator , x)
                     ≈ₚ returnₚ (blank simulator , Data.Sum.Base.swap (Data.Sum.Base.map sim-up sim-down x))
simulator-step-law (inj₁ (inj₁ w)) =
  map-arg (map₂ (encodeᴼ Service Service))
    (activate-run simulator c (suc zero) ␣ ∙ ∙ (just true) refl
     ⟨≈⟩ activate-send simulator (exec simulator (suc zero) ␣ ∙ ∙ (just true) c) (inj₂ (inj₁ tt)) zero refl)
  ⟨≈⟩ >>=ₚ-identityˡ (blank simulator , inj₂ (inj₁ tt) , true ∷ []) _
  where c = load simulator (blank simulator) (inj₁ (inj₁ tt) , w)
simulator-step-law (inj₁ (inj₂ (lift ())))
simulator-step-law (inj₂ (inj₁ (lift ())))
simulator-step-law (inj₂ (inj₂ w)) =
  map-arg (map₂ (encodeᴼ Service Service)) (runᵀᴹ-send simulator {m = blank simulator} {x = inj₂ (inj₂ tt) , w} refl)
  ⟨≈⟩ >>=ₚ-identityˡ (blank simulator , inj₁ (inj₂ tt) , []) _

simulator-correct : simulatorᴹ MS.≈ᴹ runᴾ {Service} {Service} simulator
simulator-correct = MS.≲⇒≈ᴹ (simFn (λ _ → blank simulator)
  (λ _ → >>=ₚ-identityˡ ttᵛ _)
  λ where
    (_ , inj₁ (inj₁ w)) → >>=ₚ-identityˡ (ttᵛ , inj₂ (inj₁ (true ∷ []))) _ ⟨≈⟩ ≈sym (simulator-step-law (inj₁ (inj₁ w)))
    (_ , inj₁ (inj₂ (lift ())))
    (_ , inj₂ (inj₁ (lift ())))
    (_ , inj₂ (inj₂ w)) → >>=ₚ-identityˡ (ttᵛ , inj₁ (inj₂ [])) _ ⟨≈⟩ ≈sym (simulator-step-law (inj₂ (inj₂ w))))

private
  -- Pin the stateless step before the simulation closure; inferring it through
  -- a G-composite otherwise unfolds the trace while inverting interface sums.
  simulated-step : (s : ⊤ᵛ) (x : Pos ⟦ unit ⟧ ⊎ Neg ⟦ Service ⊗₀ Service ⟧)
                  → mapₚ (map₂ (Data.Sum.Base.map id (Data.Sum.Base.map sim-up id)))
                      (mapₚ (s ,_) (resourceStep false (Data.Sum.Base.map id (Data.Sum.Base.map sim-down id) x)))
                    ≈ₚ mapₚ (s ,_) (resourceStep true x)
  simulated-step _ (inj₁ (lift ()))
  simulated-step _ (inj₂ (inj₁ (inj₁ (lift ()))))
  simulated-step s (inj₂ (inj₁ (inj₂ w))) =
    bindˣ (>>=ₚ-identityˡ (inj₂ (inj₁ (inj₁ (false ∷ [])))) (returnₚ ∘′ (s ,_)))
    ⟨≈⟩ >>=ₚ-identityˡ (s , inj₂ (inj₁ (inj₁ (false ∷ [])))) _
    ⟨≈⟩ ≈sym (>>=ₚ-identityˡ (inj₂ (inj₁ (inj₁ (true ∷ [])))) (returnₚ ∘′ (s ,_)))
  simulated-step _ (inj₂ (inj₂ (inj₁ (lift ()))))
  simulated-step s (inj₂ (inj₂ (inj₂ w))) =
    map-map (mapₚ (λ b → inj₂ (inj₂ (inj₁ (b ∷ [])))) (coinₚ uniform-Bool)) (s ,_) _
    ⟨≈⟩ map-map (coinₚ uniform-Bool) (λ b → inj₂ (inj₂ (inj₁ (b ∷ [])))) _
    ⟨≈⟩ ≈sym (map-map (coinₚ uniform-Bool) (λ b → inj₂ (inj₂ (inj₁ (b ∷ [])))) (s ,_))

simulated-correct : 𝒫._∘_ {⟦ unit ⟧} {⟦ Service ⊗₀ Service ⟧} {⟦ Service ⊗₀ Service ⟧}
                     (subᴵ {A = ⟦ Service ⟧} simulatorᴹ) (resourceᴹ false) MS.≈ᴹ resourceᴹ true
simulated-correct =
  𝒫.∘-resp-≈ˡ {⟦ unit ⟧} {⟦ Service ⊗₀ Service ⟧} {⟦ Service ⊗₀ Service ⟧}
    (sub-wire {A = ⟦ Service ⟧} sim-up sim-down)
  MS.○ᴹ wire-∘ᴹ {⟦ unit ⟧} {⟦ Service ⊗₀ Service ⟧} {⟦ Service ⊗₀ Service ⟧}
    (Data.Sum.Base.map sim-up id) (Data.Sum.Base.map sim-down id) (resourceᴹ false)
  MS.○ᴹ MS.≲⇒≈ᴹ (MS.mk-cong λ (s , x) → simulated-step s x)

tables-correct : 𝒫._∘_ {⟦ unit ⟧} {⟦ Service ⊗₀ Service ⟧} {⟦ Service ⊗₀ Service ⟧}
                  (subᴵ {A = ⟦ Service ⟧} (runᴾ {Service} {Service} simulator))
                  (runᴾ {unit} {Service ⊗₀ Service} (resource false))
                MS.≈ᴹ runᴾ {unit} {Service ⊗₀ Service} (resource true)
tables-correct =
  𝒫.∘-resp-≈ {⟦ unit ⟧} {⟦ Service ⊗₀ Service ⟧} {⟦ Service ⊗₀ Service ⟧}
    {f = subᴵ {A = ⟦ Service ⟧} (runᴾ {Service} {Service} simulator)} {h = subᴵ {A = ⟦ Service ⟧} simulatorᴹ}
    {g = runᴾ {unit} {Service ⊗₀ Service} (resource false)} {i = resourceᴹ false}
    (MS.⟺ᴹ (sub-resp-≈ {⟦ Service ⟧} {⟦ Service ⟧} {⟦ Service ⟧}
      {s = simulatorᴹ} {t = runᴾ {Service} {Service} simulator} simulator-correct))
    (MS.⟺ᴹ (resource-correct false))
  MS.○ᴹ simulated-correct MS.○ᴹ resource-correct true

------------------------------------------------------------------------
-- Closing the initialized resources and querying their public outputs
------------------------------------------------------------------------

emptyᴹ : Proc unitᴵ ⟦ unit ⟧
emptyᴹ = wireᴹ (λ ()) (λ { (lift ()) })

closed-resource : Bool → Proc unitᴵ ⟦ Service ⊗₀ Service ⟧
closed-resource marker = MC.mk MC.Iˢ λ where
  (_ , inj₁ ())
  (_ , inj₂ (inj₁ (inj₁ (lift ()))))
  (s , inj₂ (inj₁ (inj₂ _))) → returnₚ (s , inj₂ (inj₁ (inj₁ (marker ∷ []))))
  (_ , inj₂ (inj₂ (inj₁ (lift ()))))
  (s , inj₂ (inj₂ (inj₂ _))) → mapₚ (λ b → s , inj₂ (inj₂ (inj₁ (b ∷ [])))) (coinₚ uniform-Bool)

closed-correct : (marker : Bool)
               → 𝒫._∘_ {unitᴵ} {⟦ unit ⟧} {⟦ Service ⊗₀ Service ⟧}
                   (runᴾ {unit} {Service ⊗₀ Service} (resource marker)) emptyᴹ MS.≈ᴹ closed-resource marker
closed-correct marker =
  𝒫.∘-resp-≈ {unitᴵ} {⟦ unit ⟧} {⟦ Service ⊗₀ Service ⟧}
    {f = runᴾ {unit} {Service ⊗₀ Service} (resource marker)} {h = resourceᴹ marker} {g = emptyᴹ} {i = emptyᴹ}
    (MS.⟺ᴹ (resource-correct marker)) MS.reflᴹ
  MS.○ᴹ ∘-wireᴹ {unitᴵ} {⟦ unit ⟧} {⟦ Service ⊗₀ Service ⟧}
    (λ ()) (λ { (lift ()) }) (resourceᴹ marker)
  MS.○ᴹ MS.≲⇒≈ᴹ (MS.mk-cong λ where
    (_ , inj₁ ())
    (_ , inj₂ (inj₁ (inj₁ (lift ()))))
    (s , inj₂ (inj₁ (inj₂ w))) →
      bindˣ (>>=ₚ-identityˡ (inj₂ (inj₁ (inj₁ (marker ∷ [])))) _)
      ⟨≈⟩ >>=ₚ-identityˡ (s , inj₂ (inj₁ (inj₁ (marker ∷ [])))) _
    (_ , inj₂ (inj₂ (inj₁ (lift ()))))
    (s , inj₂ (inj₂ (inj₂ w))) →
      map-map (mapₚ (λ b → inj₂ (inj₂ (inj₁ (b ∷ [])))) (coinₚ uniform-Bool)) (s ,_) _
      ⟨≈⟩ map-map (coinₚ uniform-Bool) (λ b → inj₂ (inj₂ (inj₁ (b ∷ [])))) _)

first-bit : Bits → Bool
first-bit [] = false
first-bit (b ∷ _) = b

reply-bit : Pos ⟦ Service ⊗₀ Service ⟧ → Bool
reply-bit (inj₁ (inj₁ w)) = first-bit w
reply-bit (inj₁ (inj₂ (lift ())))
reply-bit (inj₂ (inj₁ w)) = first-bit w
reply-bit (inj₂ (inj₂ (lift ())))

probe : Bool → Strat (Neg ⟦ Service ⊗₀ Service ⟧) (Pos ⟦ Service ⊗₀ Service ⟧)
probe honest = ask (if honest then inj₂ (inj₂ []) else inj₁ (inj₂ [])) (out ∘′ reply-bit)

probe-grade : (marker : Bool) → runᴹ (closed-resource marker) (probe false) ≈ₚ returnₚ marker
probe-grade marker = >>=ₚ-identityˡ ttᵛ _
  ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , inj₂ (inj₁ (inj₁ (marker ∷ [])))) _

probe-honest : (marker : Bool) → runᴹ (closed-resource marker) (probe true) ≈ₚ coinₚ uniform-Bool
probe-honest marker = >>=ₚ-identityˡ ttᵛ _
  ⟨≈⟩ bind-map (coinₚ uniform-Bool) (λ b → ttᵛ , inj₂ (inj₂ (inj₁ (b ∷ [])))) _
  ⟨≈⟩ >>=ₚ-identityʳ (coinₚ uniform-Bool)

double-probe : Strat (Neg ⟦ Service ⊗₀ Service ⟧) (Pos ⟦ Service ⊗₀ Service ⟧)
double-probe = ask (inj₂ (inj₂ [])) λ p →
  ask (inj₂ (inj₂ [])) λ p′ → out (if reply-bit p then reply-bit p′ else not (reply-bit p′))

private
  probe-again : (marker b : Bool)
               → runᴹFrom (closed-resource marker) ttᵛ
                   (ask (inj₂ (inj₂ [])) λ p → out (if b then reply-bit p else not (reply-bit p)))
                 ≈ₚ (coinₚ uniform-Bool >>=ₚ λ b′ → returnₚ (if b then b′ else not b′))
  probe-again marker b = bind-map (coinₚ uniform-Bool) (λ b′ → ttᵛ , inj₂ (inj₂ (inj₁ (b′ ∷ [])))) _

probe-double : (marker : Bool) → runᴹ (closed-resource marker) double-probe
               ≈ₚ (coinₚ uniform-Bool >>=ₚ λ b → coinₚ uniform-Bool >>=ₚ λ b′ → returnₚ (if b then b′ else not b′))
probe-double marker = >>=ₚ-identityˡ ttᵛ _
  ⟨≈⟩ bind-map (coinₚ uniform-Bool) (λ b → ttᵛ , inj₂ (inj₂ (inj₁ (b ∷ [])))) _
  ⟨≈⟩ bindᶠ (probe-again marker)
