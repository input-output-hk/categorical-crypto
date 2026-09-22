{-# OPTIONS --safe #-}

-- ============================================================================
-- Bisimulation of machines.
--
-- `Machine.Iso`'s `_≅ᴹ_` asks for a *bijection* of state spaces.  That is the
-- right notion when two machines are the same construction written two ways,
-- but too strong to compare a system with a simulation of it: a simulator
-- routinely remembers what the system it simulates has already forgotten, so
-- no bijection exists even though no test can tell the two apart.
--
-- `_≈ᴮ_` asks only for a relation between the state spaces that every step
-- respects, and that covers both sides.  `≅ᴹ⇒≈ᴮ` embeds the old notion, so
-- every existing proof still counts.
-- ============================================================================

module CategoricalCrypto.Machine.Bisim where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Iso

private variable A B : Channel

infix 4 _≈ᴮ_

record _≈ᴮ_ (M M' : Machine A B) : Type₁ where
  constructor MkBisim
  open Machine M  renaming (State to S;  stepRel to R)
  open Machine M' renaming (State to S'; stepRel to R')
  field
    ℜ         : S → S' → Type
    totalˡ    : ∀ s  → ∃[ s' ] ℜ s s'
    totalʳ    : ∀ s' → ∃[ s  ] ℜ s s'
    step-to   : ∀ {s s' i o t}  → ℜ s s' → R  s  i o t  → ∃[ t' ] (R' s' i o t' × ℜ t t')
    step-from : ∀ {s s' i o t'} → ℜ s s' → R' s' i o t' → ∃[ t  ] (R  s  i o t  × ℜ t t')

open _≈ᴮ_

-- A state bijection is a bisimulation: relate `s` to `to s`.
≅ᴹ⇒≈ᴮ : {M M' : Machine A B} → M ≅ᴹ M' → M ≈ᴮ M'
≅ᴹ⇒≈ᴮ {M = M} {M'} φ = record
  { ℜ         = λ s s' → _≅ᴹ_.to φ s ≡ s'
  ; totalˡ    = λ s  → _≅ᴹ_.to φ s , refl
  ; totalʳ    = λ s' → _≅ᴹ_.from φ s' , _≅ᴹ_.to∘from φ s'
  ; step-to   = λ { {t = t} refl r → _≅ᴹ_.to φ t , _≅ᴹ_.step-to φ r , refl }
  ; step-from = λ { {s} {t' = t'} refl r →
      _≅ᴹ_.from φ t'
      , subst (λ x → Machine.stepRel M x _ _ (_≅ᴹ_.from φ t'))
              (_≅ᴹ_.from∘to φ s) (_≅ᴹ_.step-from φ r)
      , _≅ᴹ_.to∘from φ t' }
  }

≈ᴮ-refl : {M : Machine A B} → M ≈ᴮ M
≈ᴮ-refl = ≅ᴹ⇒≈ᴮ ≅ᴹ-refl

≈ᴮ-sym : {M M' : Machine A B} → M ≈ᴮ M' → M' ≈ᴮ M
≈ᴮ-sym e = record
  { ℜ         = λ s' s → ℜ e s s'
  ; totalˡ    = totalʳ e
  ; totalʳ    = totalˡ e
  ; step-to   = step-from e
  ; step-from = step-to e
  }

≈ᴮ-trans : {M M' M'' : Machine A B} → M ≈ᴮ M' → M' ≈ᴮ M'' → M ≈ᴮ M''
≈ᴮ-trans e₁ e₂ = record
  { ℜ         = λ s s'' → ∃[ s' ] (ℜ e₁ s s' × ℜ e₂ s' s'')
  ; totalˡ    = λ s → let (s' , r₁) = totalˡ e₁ s
                          (s'' , r₂) = totalˡ e₂ s'
                      in s'' , s' , r₁ , r₂
  ; totalʳ    = λ s'' → let (s' , r₂) = totalʳ e₂ s''
                            (s , r₁)  = totalʳ e₁ s'
                        in s , s' , r₁ , r₂
  ; step-to   = λ { (s' , r₁ , r₂) r →
      let (t' , r' , q₁) = step-to e₁ r₁ r
          (t'' , r'' , q₂) = step-to e₂ r₂ r'
      in t'' , r'' , t' , q₁ , q₂ }
  ; step-from = λ { (s' , r₁ , r₂) r'' →
      let (t' , r' , q₂) = step-from e₂ r₂ r''
          (t , r , q₁)   = step-from e₁ r₁ r'
      in t , r , t' , q₁ , q₂ }
  }

-- ----------------------------------------------------------------------------
-- Congruences.  `_∘_` unfolds to `tr (modifyStepRel ∘σ (_ ⊗₁ _))`, so the
-- three pieces below are exactly what left-congruence of composition needs,
-- and that is what `ℰ-tests` asks of its equality.
-- ----------------------------------------------------------------------------

-- Relabelling messages leaves the state spaces, hence the relation, alone.
modifyStepRel-cong : ∀ {A B C D} (p : ∀ {m} → C ⊗₀ D ᵀ [ m ]⇒[ m ] A ⊗₀ B ᵀ)
                     {M M' : Machine A B}
                   → M ≈ᴮ M' → modifyStepRel p M ≈ᴮ modifyStepRel p M'
modifyStepRel-cong p e = record
  { ℜ         = ℜ e
  ; totalˡ    = totalˡ e
  ; totalʳ    = totalʳ e
  ; step-to   = step-to e
  ; step-from = step-from e
  }

module _ {A B C D} (M₁ : Machine A B) {M₂ M₂' : Machine C D} (e : M₂ ≈ᴮ M₂') where

  private
    inner : Machine (A ⊗₀ B ᵀ) ((C ⊗₀ D ᵀ) ᵀ)
    inner = MkMachine (Tensor.CompRel M₁ M₂)

    inner' : Machine (A ⊗₀ B ᵀ) ((C ⊗₀ D ᵀ) ᵀ)
    inner' = MkMachine (Tensor.CompRel M₁ M₂')

    ℜ⊗ : Machine.State inner → Machine.State inner' → Type
    ℜ⊗ (a , b) (a' , b') = (a ≡ a') × ℜ e b b'

    inner-bisim : inner ≈ᴮ inner'
    inner-bisim = record
      { ℜ         = ℜ⊗
      ; totalˡ    = λ { (a , b) → let (b' , r) = totalˡ e b in (a , b') , refl , r }
      ; totalʳ    = λ { (a' , b') → let (b , r) = totalʳ e b' in (a' , b) , refl , r }
      ; step-to   = λ { {t = t} (refl , rb) (Tensor.Step₁ r) → _ , Tensor.Step₁ r , refl , rb
                      ; (refl , rb) (Tensor.Step₂ r) →
                          let (t' , r' , q) = step-to e rb r in _ , Tensor.Step₂ r' , refl , q }
      ; step-from = λ { (refl , rb) (Tensor.Step₁ r) → _ , Tensor.Step₁ r , refl , rb
                      ; (refl , rb) (Tensor.Step₂ r) →
                          let (t , r' , q) = step-from e rb r in _ , Tensor.Step₂ r' , refl , q }
      }

  ⊗₁-congʳ : (M₁ ⊗₁ M₂) ≈ᴮ (M₁ ⊗₁ M₂')
  ⊗₁-congʳ = modifyStepRel-cong ⊗σ inner-bisim

-- The trace hides internal traffic by *chaining* component steps, so the
-- bisimulation follows the chain.
module _ {A B C} {M M' : Machine (A ⊗₀ C) (B ⊗₀ C)} (e : M ≈ᴮ M') where

  private
    trace-to : ∀ {s s' i o t} → ℜ e s s' → TraceRel M s i o t
             → ∃[ t' ] (TraceRel M' s' i o t' × ℜ e t t')
    trace-to rel Trace[ r ] =
      let (t' , r' , q) = step-to e rel r in t' , Trace[ r' ] , q
    trace-to rel (r Trace∷ₒ rest) =
      let (u' , r' , q)     = step-to e rel r
          (t' , rest' , q') = trace-to q rest
      in t' , (r' Trace∷ₒ rest') , q'
    trace-to rel (r Trace∷ᵢ rest) =
      let (u' , r' , q)     = step-to e rel r
          (t' , rest' , q') = trace-to q rest
      in t' , (r' Trace∷ᵢ rest') , q'

    trace-from : ∀ {s s' i o t'} → ℜ e s s' → TraceRel M' s' i o t'
               → ∃[ t ] (TraceRel M s i o t × ℜ e t t')
    trace-from rel Trace[ r ] =
      let (t , r' , q) = step-from e rel r in t , Trace[ r' ] , q
    trace-from rel (r Trace∷ₒ rest) =
      let (u , r' , q)      = step-from e rel r
          (t , rest' , q')  = trace-from q rest
      in t , (r' Trace∷ₒ rest') , q'
    trace-from rel (r Trace∷ᵢ rest) =
      let (u , r' , q)      = step-from e rel r
          (t , rest' , q')  = trace-from q rest
      in t , (r' Trace∷ᵢ rest') , q'

    raw : MkMachine (TraceRel M) ≈ᴮ MkMachine (TraceRel M')
    raw = record
      { ℜ = ℜ e ; totalˡ = totalˡ e ; totalʳ = totalʳ e
      ; step-to = trace-to ; step-from = trace-from }

  tr-cong : tr M ≈ᴮ tr M'
  tr-cong = modifyStepRel-cong (∣^ˡσ {C = C}) (modifyStepRel-cong (∣ˡσ {B = C}) raw)

-- Left-congruence of composition, which is what `test-map-cong` needs.
∘-congˡ : ∀ {A B C} {M₁ M₁' : Machine B C} (M₂ : Machine A B)
        → M₁ ≈ᴮ M₁' → (M₁ ∘ M₂) ≈ᴮ (M₁' ∘ M₂)
∘-congˡ M₂ e = tr-cong (modifyStepRel-cong ∘σ (⊗₁-congʳ M₂ e))

-- Environment equivalence at the weaker relation, mirroring `Iso`'s `_≅ℰ_`.
_≈ℰᴮ_ : ∀ {A B} → Machine A B → Machine A B → Type₁
_≈ℰᴮ_ {B = B} M M' = (E : ℰ B) → map-ℰ M E ≈ᴮ map-ℰ M' E
