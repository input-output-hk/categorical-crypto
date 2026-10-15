{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Wiring where

open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Unit.Base

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational

private variable A B C D : Channel

id : Initialized A A
id = singleton M.id tt

modify : (∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
       → Initialized A B → Initialized C D
modify p P = initialize (M.modifyStepRel p (machine P)) (initial P)

modify-cong : (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
            → {P Q : Initialized A B} → P ≈ᴿ Q → modify p P ≈ᴿ modify p Q
modify-cong p φ = record
  { Related = Related φ
  ; initial-to = initial-to φ
  ; initial-from = initial-from φ
  ; step-to = step-to φ
  ; step-from = step-from φ
  }

infixr 9 _⊗₁_ _∘_

_⊗₁_ : Initialized A B → Initialized C D → Initialized (A ⊗₀ C) (B ⊗₀ D)
P ⊗₁ Q = initialize (machine P M.⊗₁ machine Q) λ s → initial P (proj₁ s) × initial Q (proj₂ s)

module _ {P P′ : Initialized A B} {Q Q′ : Initialized C D}
  (φ : P ≈ᴿ P′) (ψ : Q ≈ᴿ Q′) where

  pair-related : M.Machine.State (machine P) × M.Machine.State (machine Q)
               → M.Machine.State (machine P′) × M.Machine.State (machine Q′) → Set
  pair-related s t = Related φ (proj₁ s) (proj₁ t) × Related ψ (proj₂ s) (proj₂ t)

  tensor-to : ∀ {s t i o s′} → pair-related s t
            → M.Tensor.CompRel (machine P) (machine Q) s i o s′
            → ∃ λ t′ → M.Tensor.CompRel (machine P′) (machine Q′) t i o t′ × pair-related s′ t′
  tensor-to (rs , rt) (M.Tensor.Step₁ p) =
    let s′ , q , rs′ = step-to φ rs p
    in (s′ , _) , M.Tensor.Step₁ q , rs′ , rt
  tensor-to (rs , rt) (M.Tensor.Step₂ p) =
    let t′ , q , rt′ = step-to ψ rt p
    in (_ , t′) , M.Tensor.Step₂ q , rs , rt′

⊗-cong : {P P′ : Initialized A B} {Q Q′ : Initialized C D}
       → P ≈ᴿ P′ → Q ≈ᴿ Q′ → (P ⊗₁ Q) ≈ᴿ (P′ ⊗₁ Q′)
⊗-cong φ ψ = record
  { Related = pair-related φ ψ
  ; initial-to = λ { (p , q) →
      let s , p′ , rs = initial-to φ p
          t , q′ , rt = initial-to ψ q
      in (s , t) , (p′ , q′) , rs , rt }
  ; initial-from = λ { (p′ , q′) →
      let s , p , rs = initial-from φ p′
          t , q , rt = initial-from ψ q′
      in (s , t) , (p , q) , rs , rt }
  ; step-to = tensor-to φ ψ
  ; step-from = tensor-to (≈ᴿ-sym φ) (≈ᴿ-sym ψ)
  }

trace : Initialized (A ⊗₀ C) (B ⊗₀ C) → Initialized A B
trace P = initialize (M.tr (machine P)) (initial P)

module _ {P Q : Initialized (A ⊗₀ C) (B ⊗₀ C)} (φ : P ≈ᴿ Q) where

  trace-to : ∀ {s t i o s′} → Related φ s t → M.TraceRel (machine P) s i o s′
           → ∃ λ t′ → M.TraceRel (machine Q) t i o t′ × Related φ s′ t′
  trace-to st M.Trace[ p ] =
    let t′ , q , st′ = step-to φ st p
    in t′ , M.Trace[ q ] , st′
  trace-to st (p M.Trace∷ₒ ps) =
    let t′ , q , st′ = step-to φ st p
        t″ , qs , st″ = trace-to st′ ps
    in t″ , q M.Trace∷ₒ qs , st″
  trace-to st (p M.Trace∷ᵢ ps) =
    let t′ , q , st′ = step-to φ st p
        t″ , qs , st″ = trace-to st′ ps
    in t″ , q M.Trace∷ᵢ qs , st″

trace-cong : {P Q : Initialized (A ⊗₀ C) (B ⊗₀ C)} → P ≈ᴿ Q → trace P ≈ᴿ trace Q
trace-cong φ = record
  { Related = Related φ
  ; initial-to = initial-to φ
  ; initial-from = initial-from φ
  ; step-to = trace-to φ
  ; step-from = trace-to (≈ᴿ-sym φ)
  }

_∘_ : Initialized B C → Initialized A B → Initialized A C
_∘_ {B = B} Q P = trace {C = B} (modify M.∘σ (P ⊗₁ Q))

∘-cong : {P P′ : Initialized A B} {Q Q′ : Initialized B C}
       → Q ≈ᴿ Q′ → P ≈ᴿ P′ → (Q ∘ P) ≈ᴿ (Q′ ∘ P′)
∘-cong ψ φ = trace-cong (modify-cong M.∘σ (⊗-cong φ ψ))
