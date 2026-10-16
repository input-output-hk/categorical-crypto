{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Simulation where

open import Data.Product.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Observation as O
import CategoricalCrypto.Machine.Relational.Wiring as W

private variable A B C D : Channel

-- A script represents only the selected finite interaction. Forward
-- simulation permits the native preparation's other choices and the script's
-- deliberate divergence on an unexpected request.
record _≲ᴿ_ (P Q : Initialized A B) : Set₁ where
  field
    Related : M.Machine.State (machine P) → M.Machine.State (machine Q) → Set
    initial-to : ∀ {s} → initial P s → ∃ λ t → initial Q t × Related s t
    step-to : ∀ {s t i o s′} → Related s t → M.Machine.stepRel (machine P) s i o s′
      → ∃ λ t′ → M.Machine.stepRel (machine Q) t i o t′ × Related s′ t′

module Forward = _≲ᴿ_

reflexive : {P : Initialized A B} → P ≲ᴿ P
reflexive = record
  { Related = _≡_
  ; initial-to = λ p → _ , p , refl
  ; step-to = λ { refl p → _ , p , refl }
  }

transitive : {P Q S : Initialized A B} → P ≲ᴿ Q → Q ≲ᴿ S → P ≲ᴿ S
transitive φ ψ = record
  { Related = λ s u → ∃ λ t → Forward.Related φ s t × Forward.Related ψ t u
  ; initial-to = λ p →
      let t , q , st = Forward.initial-to φ p
          u , r , tu = Forward.initial-to ψ q
      in u , r , t , st , tu
  ; step-to = λ { (t , st , tu) p →
      let t′ , q , st′ = Forward.step-to φ st p
          u′ , r , tu′ = Forward.step-to ψ tu q
      in u′ , r , t′ , st′ , tu′ }
  }

bisimulation : {P Q : Initialized A B} → P ≈ᴿ Q → P ≲ᴿ Q
bisimulation φ = record { Related = Related φ ; initial-to = initial-to φ ; step-to = step-to φ }

modify : (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
  → {P Q : Initialized A B} → P ≲ᴿ Q → W.modify p P ≲ᴿ W.modify p Q
modify p φ = record
  { Related = Forward.Related φ
  ; initial-to = Forward.initial-to φ
  ; step-to = Forward.step-to φ
  }

module _ {P P′ : Initialized A B} {Q Q′ : Initialized C D}
  (φ : P ≲ᴿ P′) (ψ : Q ≲ᴿ Q′) where
  pair-related : M.Machine.State (machine P) × M.Machine.State (machine Q)
    → M.Machine.State (machine P′) × M.Machine.State (machine Q′) → Set
  pair-related s t = Forward.Related φ (proj₁ s) (proj₁ t) × Forward.Related ψ (proj₂ s) (proj₂ t)

  tensor-step : ∀ {s t i o s′} → pair-related s t
    → M.Tensor.CompRel (machine P) (machine Q) s i o s′
    → ∃ λ t′ → M.Tensor.CompRel (machine P′) (machine Q′) t i o t′ × pair-related s′ t′
  tensor-step (rs , rt) (M.Tensor.Step₁ p) =
    let s′ , q , rs′ = Forward.step-to φ rs p
    in (s′ , _) , M.Tensor.Step₁ q , rs′ , rt
  tensor-step (rs , rt) (M.Tensor.Step₂ p) =
    let t′ , q , rt′ = Forward.step-to ψ rt p
    in (_ , t′) , M.Tensor.Step₂ q , rs , rt′

  tensor : (P W.⊗₁ Q) ≲ᴿ (P′ W.⊗₁ Q′)
  tensor = record
    { Related = pair-related
    ; initial-to = λ { (p , q) →
        let s , p′ , rs = Forward.initial-to φ p
            t , q′ , rt = Forward.initial-to ψ q
        in (s , t) , (p′ , q′) , rs , rt }
    ; step-to = tensor-step
    }

module _ {P Q : Initialized (A ⊗₀ C) (B ⊗₀ C)} (φ : P ≲ᴿ Q) where
  trace-step : ∀ {s t i o s′} → Forward.Related φ s t → M.TraceRel (machine P) s i o s′
    → ∃ λ t′ → M.TraceRel (machine Q) t i o t′ × Forward.Related φ s′ t′
  trace-step st M.Trace[ p ] =
    let t′ , q , st′ = Forward.step-to φ st p
    in t′ , M.Trace[ q ] , st′
  trace-step st (p M.Trace∷ₒ ps) =
    let t′ , q , st′ = Forward.step-to φ st p
        t″ , qs , st″ = trace-step st′ ps
    in t″ , q M.Trace∷ₒ qs , st″
  trace-step st (p M.Trace∷ᵢ ps) =
    let t′ , q , st′ = Forward.step-to φ st p
        t″ , qs , st″ = trace-step st′ ps
    in t″ , q M.Trace∷ᵢ qs , st″

  trace : W.trace P ≲ᴿ W.trace Q
  trace = record
    { Related = Forward.Related φ
    ; initial-to = Forward.initial-to φ
    ; step-to = trace-step
    }

compose : {P P′ : Initialized A B} {Q Q′ : Initialized B C}
  → Q ≲ᴿ Q′ → P ≲ᴿ P′ → (Q W.∘ P) ≲ᴿ (Q′ W.∘ P′)
compose ψ φ = trace (modify M.∘σ (tensor φ ψ))

forward : {P Q : Initialized O.J O.Ω} → P ≲ᴿ Q → ∀ {b} → O.eval P b → O.eval Q b
forward φ (s , init , s′ , path) =
  let t , init′ , st = Forward.initial-to φ init
      t′ , path′ , st′ = Forward.step-to φ st path
  in t , init′ , t′ , path′

observe : {p q : Initialized O.J A} {t u : Initialized A O.Ω}
  → t ≲ᴿ u → p ≲ᴿ q → ∀ {b} → O.eval (t W.∘ p) b → O.eval (u W.∘ q) b
observe φ ψ = forward (compose φ ψ)
