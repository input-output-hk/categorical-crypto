{-# OPTIONS --safe --without-K --guardedness #-}

open import Data.Nat.Base using (ℕ)
module CategoricalCrypto.Symbolic.Example.SecureChannel.Simulation (κ κⁱ : ℕ) where

open import Categories.Category.Monoidal.Bundle
open import Data.Bool.Base
open import Data.Fin.Base as Fin using ()
open import Data.List.Base
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Polymorphic using () renaming (tt to ttᵛ)
open import Function.Base hiding (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Protocol.Machine as Machine
open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀ using (Var)
open import CategoricalCrypto.Symbolic.Role Σ₀ hiding (Input)
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀ using (runᴿ; ⟦_⟧ᴵ)
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Protocol
open import CategoricalCrypto.UC.Machine using (Proc; subᴵ; initˢ)
open import CategoricalCrypto.UC.Machine.Dictionary using (sub-⊗₁)

open Terms Σ₀
open EqTheory E₀
open Run E₀ hiding (after)
private module M = MonoidalCategory (𝒢ₚᴹ 0ℓ)

sim : Proc ⟦ wire ⟧ᴵ ⟦ wire ⟧ᴵ
sim = runᴿ κ simulator-role
f : Proc ⟦ Var void ⟧ᴵ ⟦ ports ⟧ᴵ
f = runᴿ κⁱ ideal-role
g : Proc ⟦ ports ⟧ᴵ ⟦ ports ⟧ᴵ
g = subᴵ {A = ⟦ wire ⟧ᴵ} sim

module L = Col.Loop (Alphabet pos (Var void) ⊎ Alphabet neg ports)
  (Alphabet neg (Var void) ⊎ Alphabet pos ports)
  (Alphabet neg ports ⊎ Alphabet pos ports) (Col.Sᴳ g f) (Col.kᴳ g f)

ciphertext : Msg
ciphertext = app enc (app (cst 0) [] ∷ name (κ , 0) ∷ name (κ , 1) ∷ [])
error-term : Msg
error-term = app (cst 2) []

data State : Set where
  idle : State
  waiting : Msg → State
  stopped : Config 3 Γˢ → State

left-state : State → Config 3 Γ
left-state idle = init simulated-role
left-state (waiting m) = config pending (name (κ , 0) ∷ ciphertext ∷ nf m ∷ []) 2
left-state (stopped s) = config finished [] (counter s)

right-state : State → Config 3 Γˢ × Config 3 Γⁱ
right-state idle = init simulator-role , init ideal-role
right-state (waiting m) = config pending (ciphertext ∷ []) 2 , config pending (nf m ∷ []) 0
right-state (stopped s) = s , config finished [] 0

Input = Alphabet pos (Var void) ⊎ Alphabet neg ports
Output = Alphabet neg (Var void) ⊎ Alphabet pos ports

act : State × Input → State × Output
act (s , inj₁ ())
act (idle , inj₂ (inj₁ t)) = stopped (config finished [] 0) , inj₂ (inj₂ error-term)
act (idle , inj₂ (inj₂ t)) = waiting t , inj₂ (inj₁ ciphertext)
act (waiting m , inj₂ (inj₁ t)) = stopped (config finished [] 2) , inj₂ (inj₂
  (if does (t ≟E ciphertext) then nf (nf m) else error-term))
act (waiting m , inj₂ (inj₂ t)) = stopped (config pending (ciphertext ∷ []) 2) , inj₂ (inj₂ error-term)
act (stopped s , inj₂ (inj₂ t)) = stopped s , inj₂ (inj₂ error-term)
act (stopped (config Fin.zero [] j) , inj₂ (inj₁ t)) = stopped (config finished [] j) , inj₂ (inj₂ error-term)
act (stopped (config (Fin.suc Fin.zero) (c ∷ []) j) , inj₂ (inj₁ t)) = stopped (config finished [] j) , inj₂ (inj₂ error-term)
act (stopped (config (Fin.suc (Fin.suc Fin.zero)) [] j) , inj₂ (inj₁ t)) = stopped (config finished [] j) , inj₂ (inj₂ error-term)
act (stopped (config (Fin.suc (Fin.suc (Fin.suc ()))) _ _) , _)

left-law : ∀ s i → Data.Product.map left-state (λ x → x) (act (s , i))
  ≡ Data.Product.map₂ (encode (Var void) ports) (step κ simulated-role (left-state s) (decode (Var void) ports i))
left-law s (inj₁ ())
left-law idle (inj₂ (inj₁ t)) = refl
left-law idle (inj₂ (inj₂ t)) = refl
left-law (waiting m) (inj₂ (inj₁ t)) with does (t ≟E ciphertext)
... | true = refl
... | false = refl
left-law (waiting m) (inj₂ (inj₂ t)) = refl
left-law (stopped (config Fin.zero [] j)) (inj₂ (inj₁ t)) = refl
left-law (stopped (config (Fin.suc Fin.zero) (c ∷ []) j)) (inj₂ (inj₁ t)) = refl
left-law (stopped (config (Fin.suc (Fin.suc Fin.zero)) [] j)) (inj₂ (inj₁ t)) = refl
left-law (stopped (config (Fin.suc (Fin.suc (Fin.suc ()))) _ _)) _
left-law (stopped s) (inj₂ (inj₂ t)) = refl

private
  St = Config 3 Γˢ × Config 3 Γⁱ
  Feedback = Alphabet neg ports ⊎ Alphabet pos ports

  three-pass : ∀ (s s₁ s₂ s₃ : St) (i : Input) (x y : Feedback) (o : Output)
    → Col.kᴳ g f (s , inj₁ i) ≈ₚ returnₚ (s₁ , inj₂ x)
    → Col.kᴳ g f (s₁ , inj₂ x) ≈ₚ returnₚ (s₂ , inj₂ y)
    → Col.kᴳ g f (s₂ , inj₂ y) ≈ₚ returnₚ (s₃ , inj₁ o)
    → MC.step L.tracedᴹ (s , i) ≈ₚ returnₚ (s₃ , o)
  three-pass s s₁ s₂ s₃ i x y o e₁ e₂ e₃ = L.step-red s i
    ⟨≈⟩ bindˣ e₁ ⟨≈⟩ >>=ₚ-identityˡ _ _
    ⟨≈⟩ L.loop-pass s₁ x s₂ (inj₂ y) e₂
    ⟨≈⟩ L.loop-pass s₂ y s₃ (inj₁ o) e₃

  first-honest : ∀ sg sf t → Col.kᴳ g f ((sg , sf) , inj₁ (inj₂ (inj₂ t)))
    ≈ₚ returnₚ ((sg , sf) , inj₂ (inj₁ (inj₂ t)))
  first-honest sg sf t = >>=ₚ-identityˡ _ _

  last-honest : ∀ sg sf t → Col.kᴳ g f ((sg , sf) , inj₂ (inj₂ (inj₂ t)))
    ≈ₚ returnₚ ((sg , sf) , inj₁ (inj₂ (inj₂ t)))
  last-honest sg sf t = >>=ₚ-identityˡ _ _

  ideal-pass : ∀ sg sf sf′ i o → step κⁱ ideal-role sf (decode (Var void) ports (inj₂ i)) ≡ (sf′ , o)
    → Col.kᴳ g f ((sg , sf) , inj₂ (inj₁ i))
      ≈ₚ returnₚ ((sg , sf′) , Col.outᶠ (encode (Var void) ports o))
  ideal-pass sg sf sf′ i o e = bindˣ (ret≡ (cong (Data.Product.map₂ (encode (Var void) ports)) e))
    ⟨≈⟩ >>=ₚ-identityˡ _ _

  down-pass : ∀ sg sf sg′ t command → step κ simulator-role sg (there (here refl) ↦ t) ≡ (sg′ , here refl ↦ command)
    → Col.kᴳ g f ((sg , sf) , inj₁ (inj₂ (inj₁ t)))
      ≈ₚ returnₚ ((sg′ , sf) , inj₂ (inj₁ (inj₁ command)))
  down-pass sg sf sg′ t command e = bindˣ
    (map-arg _ (ret≡ (cong (Data.Product.map₂ (encode wire wire)) e)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    ⟨≈⟩ >>=ₚ-identityˡ _ _

  up-pass : ∀ sg sf sg′ t cipher → step κ simulator-role sg (here refl ↦ t) ≡ (sg′ , there (here refl) ↦ cipher)
    → Col.kᴳ g f ((sg , sf) , inj₂ (inj₂ (inj₁ t)))
      ≈ₚ returnₚ ((sg′ , sf) , inj₁ (inj₂ (inj₁ cipher)))
  up-pass sg sf sg′ t cipher e = bindˣ
    (map-arg _ (ret≡ (cong (Data.Product.map₂ (encode wire wire)) e)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    ⟨≈⟩ >>=ₚ-identityˡ _ _

  honest-error : ∀ sg sf sf′ t → step κⁱ ideal-role sf (there (here refl) ↦ t) ≡ (sf′ , there (here refl) ↦ error-term)
    → MC.step L.tracedᴹ ((sg , sf) , inj₂ (inj₂ t)) ≈ₚ returnₚ ((sg , sf′) , inj₂ (inj₂ error-term))
  honest-error sg sf sf′ t e = three-pass (sg , sf) (sg , sf) (sg , sf′) (sg , sf′)
    (inj₂ (inj₂ t)) (inj₁ (inj₂ t)) (inj₂ (inj₂ error-term)) (inj₂ (inj₂ error-term))
    (first-honest sg sf t) (ideal-pass sg sf sf′ (inj₂ t) (there (here refl) ↦ error-term) e) (last-honest sg sf′ error-term)

  adversary : ∀ sg sf sg′ sf′ t command output
    → step κ simulator-role sg (there (here refl) ↦ t) ≡ (sg′ , here refl ↦ command)
    → step κⁱ ideal-role sf (here refl ↦ command) ≡ (sf′ , there (here refl) ↦ output)
    → MC.step L.tracedᴹ ((sg , sf) , inj₂ (inj₁ t)) ≈ₚ returnₚ ((sg′ , sf′) , inj₂ (inj₂ output))
  adversary sg sf sg′ sf′ t command output e₁ e₂ = three-pass (sg , sf) (sg′ , sf) (sg′ , sf′) (sg′ , sf′)
    (inj₂ (inj₁ t)) (inj₁ (inj₁ command)) (inj₂ (inj₂ output)) (inj₂ (inj₂ output))
    (down-pass sg sf sg′ t command e₁) (ideal-pass sg′ sf sf′ (inj₁ command) (there (here refl) ↦ output) e₂)
    (last-honest sg′ sf′ output)

  delivery-command : Msg → Msg → Msg
  delivery-command c t = if does (t ≟E c) then app (cst 0) [] else app (cst 1) []

  simulator-command : ∀ c j t → step κ simulator-role (config pending (c ∷ []) j) (there (here refl) ↦ t)
    ≡ (config finished [] j , here refl ↦ delivery-command c t)
  simulator-command c j t with does (t ≟E c)
  ... | true = refl
  ... | false = refl

  ideal-response : ∀ m t → step κⁱ ideal-role (config pending (nf m ∷ []) 0)
    (here refl ↦ delivery-command ciphertext t)
    ≡ (config finished [] 0 , there (here refl) ↦ (if does (t ≟E ciphertext) then nf (nf m) else error-term))
  ideal-response m t with does (t ≟E ciphertext)
  ... | true = refl
  ... | false = refl

right-law : ∀ s i → MC.step L.tracedᴹ (right-state s , i)
  ≈ₚ returnₚ (Data.Product.map right-state (λ x → x) (act (s , i)))
right-law s (inj₁ ())
right-law idle (inj₂ (inj₁ t)) = adversary (init simulator-role) (init ideal-role)
  (config finished [] 0) (config finished [] 0) t (app (cst 1) []) error-term refl refl
right-law idle (inj₂ (inj₂ t)) = three-pass (init simulator-role , init ideal-role)
  (init simulator-role , init ideal-role) (init simulator-role , config pending (nf t ∷ []) 0)
  (config pending (ciphertext ∷ []) 2 , config pending (nf t ∷ []) 0)
  (inj₂ (inj₂ t)) (inj₁ (inj₂ t)) (inj₂ (inj₁ (app (cst 0) []))) (inj₂ (inj₁ ciphertext))
  (first-honest (init simulator-role) (init ideal-role) t)
  (ideal-pass (init simulator-role) (init ideal-role) (config pending (nf t ∷ []) 0)
    (inj₂ t) (here refl ↦ app (cst 0) []) refl)
  (up-pass (init simulator-role) (config pending (nf t ∷ []) 0) (config pending (ciphertext ∷ []) 2)
    (app (cst 0) []) ciphertext refl)
right-law (waiting m) (inj₂ (inj₁ t)) = adversary
  (config pending (ciphertext ∷ []) 2) (config pending (nf m ∷ []) 0)
  (config finished [] 2) (config finished [] 0) t (delivery-command ciphertext t)
  (if does (t ≟E ciphertext) then nf (nf m) else error-term)
  (simulator-command ciphertext 2 t) (ideal-response m t)
right-law (waiting m) (inj₂ (inj₂ t)) = honest-error (config pending (ciphertext ∷ []) 2)
  (config pending (nf m ∷ []) 0) (config finished [] 0) t refl
right-law (stopped (config Fin.zero [] j)) (inj₂ (inj₁ t)) = adversary (config Fin.zero [] j)
  (config finished [] 0) (config finished [] j) (config finished [] 0) t (app (cst 1) []) error-term refl refl
right-law (stopped (config (Fin.suc Fin.zero) (c ∷ []) j)) (inj₂ (inj₁ t)) = adversary
  (config pending (c ∷ []) j) (config finished [] 0) (config finished [] j) (config finished [] 0)
  t (delivery-command c t) error-term (simulator-command c j t) refl
right-law (stopped (config (Fin.suc (Fin.suc Fin.zero)) [] j)) (inj₂ (inj₁ t)) = adversary
  (config finished [] j) (config finished [] 0) (config finished [] j) (config finished [] 0)
  t (app (cst 1) []) error-term refl refl
right-law (stopped (config (Fin.suc (Fin.suc (Fin.suc ()))) _ _)) _
right-law (stopped s) (inj₂ (inj₂ t)) = honest-error s (config finished [] 0) (config finished [] 0) t refl

apex : MC.Machine Input Output
apex = MC.mk (initˢ State idle) (returnₚ ∘′ act)

left : apex RS.≲[ V.id ∣ V.id ] runᴿ κ simulated-role
left = RS.≲[]-resp-≈ (λ x → ≈sym (pure-idᵏ x)) (λ x → ≈sym (pure-idᵏ x))
  (simFn[] left-state (λ x → x) (λ x → x) (λ _ → >>=ₚ-identityˡ _ _)
    (λ (s , i) → >>=ₚ-identityˡ _ _ ⟨≈⟩ ret≡ (left-law s i)))

right : apex RS.≲[ V.id ∣ V.id ] L.tracedᴹ
right = RS.≲[]-resp-≈ (λ x → ≈sym (pure-idᵏ x)) (λ x → ≈sym (pure-idᵏ x))
  (simFn[] right-state (λ x → x) (λ x → x)
    (λ _ → >>=ₚ-identityˡ _ _ ⟨≈⟩ ≈sym (point-⊛ (MC.state g) (MC.state f) ttᵛ
      ⟨≈⟩ >>=ₚ-identityˡ _ _ ⟨≈⟩ >>=ₚ-identityˡ _ _))
    (λ (s , i) → >>=ₚ-identityˡ _ _ ⟨≈⟩ ≈sym (right-law s i)))

simulated≈trace : runᴿ κ simulated-role S.≈ᴹ L.tracedᴹ
simulated≈trace = RS.relsim⇒≈ᴹ record { apex = apex ; left = left ; right = right }

simulated≈composition : runᴿ κ simulated-role S.≈ᴹ M._∘_ {Machine.⟦ ⟦ Var void ⟧ᴵ ⟧ᴵ}
  {Machine.⟦ ⟦ ports ⟧ᴵ ⟧ᴵ} {Machine.⟦ ⟦ ports ⟧ᴵ ⟧ᴵ} g f
simulated≈composition = simulated≈trace S.○ᴹ S.⟺ᴹ (Col.collapseᵀ g f) S.○ᴹ Col.compose-raw≈∘ᴳ g f
