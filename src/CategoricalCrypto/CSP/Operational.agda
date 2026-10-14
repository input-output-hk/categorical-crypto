{-# OPTIONS --safe --without-K --guardedness #-}

-- Network completion uses the Par⊤ convention: a nonempty family returns
-- jointly once, and completed experiments have no further transitions.
module CategoricalCrypto.CSP.Operational (Sort : Set) (Payload : Sort → Set) where

open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; yes; no)

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
import CategoricalCrypto.CSP.Process as P

open Interface
open Port
open Boxes renaming (shape to box-shape)
open Component

module Labels (A B : Interface) where
  data Visible : Set where
    event : Event (A ⊗₀ B) → Visible
    √ : Visible

  data Label : Set where
    visible : Visible → Label
    τ : Label
module Execution {A B : Interface} (N : Network A B) where
  open Labels A B public
  open Network N
  open Wiring N

  Box : Set
  Box = ⟨ box-shape components ⟩

  module Local (k : Box) = P (Event (boundary (label components k)))
                             (Branch (label components k)) ⊤

  update : (k : Box) → Local.Tree k → State → State
  update k t q j with index-equality (box-shape components) k j
  ... | yes refl = t
  ... | no _ = q j

  data Configuration : Set where
    running : State → Configuration
    completed : Configuration

  initial-configuration : Configuration
  initial-configuration = running initial-state


  external-name : ⟨ shape (A ⊗₀ B) ⟩ → Name
  external-name = inj₂

  external-sort : ∀ e → name-sort (external-name e) ≡ sort (ports (A ⊗₀ B) e)
  external-sort (inj₁ _) = refl
  external-sort (inj₂ _) = refl

  external-polarity : ⟨ shape (A ⊗₀ B) ⟩ → Polarity
  external-polarity (inj₁ i) = dual (polarity (ports A i))
  external-polarity (inj₂ i) = polarity (ports B i)

  Private : Name → Set
  Private n = ∀ e → ¬ (Connected n (external-name e))

  local-sort : Local components → Sort
  local-sort (k , p) = sort (ports (boundary (label components k)) p)

  class-payload : ∀ {kp n} → Connected (local-wire kp) n → local-sort kp ≡ name-sort n
  class-payload {kp} conn = trans (wire-type kp) (connected-type conn)

  LocalPort : Box → Set
  LocalPort k = ⟨ shape (boundary (label components k)) ⟩

  record Gather (n : Name) (x : Payload (name-sort n)) (q q′ : State) : Set where
    field
      selected : (k : Box) → Maybe (LocalPort k)
      incident : ∀ {k} p → Connected (local-wire (k , p)) n
               → Σ (LocalPort k) (λ r → selected k ≡ just r)
      on-wire : ∀ {k p} → selected k ≡ just p → Connected (local-wire (k , p)) n
      advances : ∀ {k p} (chosen : selected k ≡ just p)
               → Local._─[_]→_ k (q k)
                   (Local.visible (Local.event (p , subst Payload (sym (class-payload (on-wire chosen))) x))) (q′ k)
      absent : ∀ {k} → selected k ≡ nothing → q′ k ≡ q k
      inhabited : Σ Box (λ k → Σ (LocalPort k) (λ p → selected k ≡ just p))

  nonincident-unchanged : ∀ {n x q q′ k} (gather : Gather n x q q′)
    → (∀ p → ¬ (Connected (local-wire (k , p)) n)) → q′ k ≡ q k
  nonincident-unchanged {k = k} gather outside with Gather.selected gather k in chosen
  ... | nothing = Gather.absent gather chosen
  ... | just p = ⊥-elim (outside p (Gather.on-wire gather chosen))

  incident-must-offer : ∀ {n x q q′ k} (gather : Gather n x q q′) p
    → Connected (local-wire (k , p)) n
    → Σ (LocalPort k) (λ r → Σ (Connected (local-wire (k , r)) n)
        (λ conn → Local._─[_]→_ k (q k)
          (Local.visible (Local.event (r , subst Payload (sym (class-payload conn)) x))) (q′ k)))
  incident-must-offer gather p conn with Gather.incident gather p conn
  ... | r , chosen = r , Gather.on-wire gather chosen , Gather.advances gather chosen

  record OutputSupport {n x q q′} (gather : Gather n x q q′) : Set where
    open Gather gather
    field
      provider : Σ Box (λ k → Σ (LocalPort k)
        (λ p → selected k ≡ just p × polarity (ports (boundary (label components k)) p) ≡ output))
      unique-output : ∀ {k p} → selected k ≡ just p
                    → polarity (ports (boundary (label components k)) p) ≡ output → k ≡ proj₁ provider

  record Handshake {n x q q′} (gather : Gather n x q q′) : Set where
    open Gather gather
    field
      output-support : OutputSupport gather
      listener : Σ Box (λ k → Σ (LocalPort k)
        (λ p → selected k ≡ just p × polarity (ports (boundary (label components k)) p) ≡ input
             × k ≢ proj₁ (OutputSupport.provider output-support)))

  data BoundaryCompatible {e x q q′} (gather : Gather (external-name e) x q q′) : Set where
    input-boundary : external-polarity e ≡ input
                  → (∀ {k p} → Gather.selected gather k ≡ just p
                     → polarity (ports (boundary (label components k)) p) ≡ input) → BoundaryCompatible gather
    output-boundary : external-polarity e ≡ output → OutputSupport gather → BoundaryCompatible gather

  AllRet : State → Set
  AllRet q = ∀ k → Local.Tree.force (q k) ≡ Local.ret tt

  infix 4 _─[_]→_
  data _─[_]→_ : Configuration → Label → Configuration → Set where
    internal : ∀ {q k t} → Local._─[_]→_ k (q k) Local.τ t
             → running q ─[ τ ]→ running (update k t q)
    exterior : ∀ {q q′ e} (x : Payload (name-sort (external-name e)))
             → (gather : Gather (external-name e) x q q′) → BoundaryCompatible gather
             → running q ─[ visible (event (e , subst Payload (external-sort e) x)) ]→ running q′
    hidden : ∀ {q q′ n} (x : Payload (name-sort n))
           → (gather : Gather n x q q′) → Private n → Handshake gather
           → running q ─[ τ ]→ running q′
    finish : ∀ {q} → Box → AllRet q → running q ─[ visible √ ]→ completed

  completed-no-step : ∀ {l q} → ¬ (completed ─[ l ]→ q)
  completed-no-step ()

  record Diverges (q : Configuration) : Set where
    coinductive
    field next : Configuration; step : q ─[ τ ]→ next; rest : Diverges next

  completed-not-divergent : ¬ (Diverges completed)
  completed-not-divergent d = completed-no-step (Diverges.step d)

