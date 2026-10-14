{-# OPTIONS --safe --without-K --guardedness #-}

-- Constructive event reindexing of Process_Trees and Semantics.LTS at
-- input-output-hk/agda-cardano-common 9a40d1de330f376c3a102e7c9f1282f4fa830a7e.
-- E is the dependent sum of a component's declared ports and their payloads;
-- B is arbitrary, not a finite branching certificate. Return remains visible.
module CategoricalCrypto.CSP.Process (E B R : Set) where

open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

mutual
  data Node : Set where
    ret : R → Node
    sil : Tree → Node
    react : (E → Maybe Tree) → (B → Maybe Tree) → Node

  record Tree : Set where
    coinductive
    constructor ptree
    field force : Node

open Tree

stop : Tree
force stop = react (λ _ → nothing) (λ _ → nothing)

return : R → Tree
force (return r) = ret r

silent : Tree → Tree
force (silent p) = sil p

div : Tree
force div = sil div

menu : (E → Maybe Tree) → (B → Maybe Tree) → Tree
force (menu v b) = react v b

data Visible : Set where
  event : E → Visible
  √ : R → Visible

data Label : Set where
  visible : Visible → Label
  τ : Label

infix 4 _─[_]→_
data _─[_]→_ : Tree → Label → Tree → Set where
  sRet : ∀ {p r} → force p ≡ ret r → p ─[ visible (√ r) ]→ stop
  sSil : ∀ {p q} → force p ≡ sil q → p ─[ τ ]→ q
  sVis : ∀ {p q v b e} → force p ≡ react v b → v e ≡ just q
       → p ─[ visible (event e) ]→ q
  sTau : ∀ {p q v b i} → force p ≡ react v b → b i ≡ just q → p ─[ τ ]→ q

private variable
  p q r : Tree
  l : Label
  e : Visible
  xs : List Visible

record Diverges (p : Tree) : Set where
  coinductive
  field
    next : Tree
    step : p ─[ τ ]→ next
    rest : Diverges next

divergent-div : Diverges div
Diverges.next divergent-div = div
Diverges.step divergent-div = sSil refl
Diverges.rest divergent-div = divergent-div

-- Native stability excludes ret even though √ is a visible label.
Stable : Tree → Set
Stable p = (∀ q → ¬ (p ─[ τ ]→ q)) × (∀ r q → ¬ (p ─[ visible (√ r) ]→ q))

stop-no-step : ¬ (stop ─[ l ]→ q)
stop-no-step (sRet ())
stop-no-step (sSil ())
stop-no-step (sVis refl ())
stop-no-step (sTau refl ())

stable-stop : Stable stop
stable-stop = (λ _ → stop-no-step) , (λ _ _ → stop-no-step)

stop-not-divergent : ¬ (Diverges stop)
stop-not-divergent d = stop-no-step (Diverges.step d)

div-not-stable : ¬ (Stable div)
div-not-stable (noτ , _) = noτ div (sSil refl)

return-not-stable : ∀ x → ¬ (Stable (return x))
return-not-stable x (_ , no√) = no√ x stop (sRet refl)

data Executes : Tree → List Visible → Tree → Set where
  done : Executes p [] p
  silent-step : p ─[ τ ]→ q → Executes q xs r → Executes p xs r
  visible-step : p ─[ visible e ]→ q → Executes q xs r → Executes p (e ∷ xs) r

Trace : Tree → List Visible → Set
Trace p xs = Σ Tree (Executes p xs)

Refuses : Tree → (Visible → Set) → Set
Refuses p refusal = Stable p × (∀ e → refusal e → ∀ q → ¬ (p ─[ visible e ]→ q))

Failure : Tree → List Visible → (Visible → Set) → Set
Failure p xs refusal = Σ Tree (λ q → Executes p xs q × Refuses q refusal)

-- No divergence flooding: this records an infinite silent path AFTER the
-- exact executed trace. Neither traces nor failures are made chaotic afterward.
Divergence : Tree → List Visible → Set
Divergence p xs = Σ Tree (λ q → Executes p xs q × Diverges q)
