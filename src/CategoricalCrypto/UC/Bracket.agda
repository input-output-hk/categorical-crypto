{-# OPTIONS --safe --without-K --guardedness #-}

-- Well-bracketed machines (`docs/uc-setup-ssp.md` §4.2): a machine between
-- flattened channel-indexed interfaces that plays the call/return discipline
-- whenever its environment does.  The environment queries only an idle machine
-- and returns only on the channel of the machine's open call; the machine then
-- calls below or answers on the queried channel.  `W` is CryptHOL's
-- respectfulness (lochbihler2019cc Def. 3) moved to the machine layer, an
-- invariant read on a step's support at every finite depth (`Dp.Supp`), so it
-- needs no coinduction.  Every compiled protocol is well-bracketed
-- (`morphism-W`), and so are the identity (`id-W`) and every relabelling wire
-- whose returns come back on the queried channel (`wire-W`).

open import Categories.Category

open import Class.DecEq
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.SSP.Compile
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Protocol as Flat

module CategoricalCrypto.UC.Bracket where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module T  = Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)

private variable
  A B : Iface
  S : Set

------------------------------------------------------------------------
-- The discipline

data Phase (A B : Iface) : Set where
  idle    : Phase A B
  serving : Ch B → Phase A B
  calling : Ch B → Ch A → Phase A B

-- The environment's legal moves: a query to an idle machine, and the return of
-- its open call, on the called channel.
data Opp {A B : Iface} : Phase A B → Σ (Ch A) (R A) ⊎ Σ (Ch B) (Q B) → Phase A B → Set where
  query  : ∀ {b q}   → Opp idle (inj₂ (b , q)) (serving b)
  return : ∀ {b a r} → Opp (calling b a) (inj₁ (a , r)) (serving b)

-- The machine's: a call below, or the answer on the queried channel.
data Ply {A B : Iface} : Phase A B → Σ (Ch A) (Q A) ⊎ Σ (Ch B) (R B) → Phase A B → Set where
  call   : ∀ {b a q} → Ply (serving b) (inj₁ (a , q)) (calling b a)
  answer : ∀ {b r}   → Ply (serving b) (inj₂ (b , r)) idle

-- A legal move from `φ′` to a state the invariant `I` holds of.
Legal : (S → Phase A B → Set) → Phase A B → S × (Σ (Ch A) (Q A) ⊎ Σ (Ch B) (R B)) → Set
Legal I φ′ (s′ , y) = Σ[ φ″ ∈ Phase _ _ ] Ply φ′ y φ″ × I s′ φ″

record W (f : Proc (flat A) (flat B)) : Set₁ where
  field
    I      : MC.St f → Phase A B → Set
    I-init : ∀ n → Supp n (MC.point (MC.state f) tt) λ s → I s idle
    I-step : ∀ {s φ x φ′} → I s φ → Opp φ x φ′ → ∀ n → Supp n (MC.step f (s , x)) (Legal I φ′)

------------------------------------------------------------------------
-- Compiled protocols

-- A flat step tree that answers only on `b`, and after each call continues
-- well at every return on the called channel.
data Bracketed {A : Iface} {S : Set} (B : Iface) (b : Ch B)
     : Flat.Calls (flat A) (S × Σ (Ch B) (R B)) → Set where
  ret  : ∀ {s r} → Bracketed B b (Flat.ret (s , b , r))
  call : ∀ {a q k} → (∀ r → Bracketed B b (k (a , r))) → Bracketed B b (Flat.call (a , q) k)
  coin : ∀ {μ k} → (∀ x → Bracketed B b (k x)) → Bracketed B b (Flat.coin μ k)
  dead : Bracketed B b Flat.dead

module _ ⦃ _ : DecEq (Ch A) ⦄ where

  toCalls-bracketed : (b : Ch B) (t : Calls A (S × R B b)) → Bracketed B b (toCalls (mapᶜ (map₂ (b ,_)) t))
  toCalls-bracketed b (ret _)      = ret
  toCalls-bracketed b (call _ _ k) =
    call λ r → subst (Bracketed _ b) (sym (reply-refl r _)) (toCalls-bracketed b (k r))
  toCalls-bracketed b (coin _ k)   = coin λ x → toCalls-bracketed b (k x)
  toCalls-bracketed b dead         = dead

  module _ (P : Protocol A B) where

    private
      I : MSt (toProtocol P) → Phase A B → Set
      I (idle _) idle          = ⊤
      I (wait k) (calling b a) = ∀ r → Bracketed B b (k (a , r))
      I _        _             = ⊥

      drive-W : {b : Ch B} {t : Flat.Calls (flat A) (St P × Σ (Ch B) (R B))} → Bracketed B b t
              → ∀ n → Supp n (drive (toProtocol P) t) (Legal I (serving b))
      drive-W ret      = Supp-return _ _ (idle , answer , tt)
      drive-W (call g) = Supp-return _ _ (calling _ _ , call , g)
      drive-W (coin g) = λ n → Supp-bind _ n _ _ (Supp-all _ (λ x i → drive-W (g x) i) n _)
      drive-W dead     = Supp-bot _

      I-step : ∀ {s φ x φ′} → I s φ → Opp φ x φ′ → ∀ n
             → Supp n (stepᴹ (toProtocol P) (s , x)) (Legal I φ′)
      I-step {idle s} _ query  = drive-W (toCalls-bracketed _ (step P s _ _))
      I-step {wait _} g return = drive-W (g _)
      I-step {wait _} () query
      I-step {idle _} () return

    morphism-W : W (morphism (toProtocol P))
    morphism-W = record { I = I ; I-init = Supp-return _ _ tt ; I-step = I-step }

------------------------------------------------------------------------
-- Wires

-- `𝒢ₚ`'s identity is the braiding `σᴹ`, a copycat: it calls on the queried
-- channel and answers with the return.
id-W : W {A} {A} (Category.id 𝒫ᴵ {flat A})
id-W {A} = record { I = I ; I-init = Supp-return _ _ tt ; I-step = I-step }
  where
  I : ⊤ᵛ → Phase A A → Set
  I _ idle          = ⊤
  I _ (serving _)   = ⊥
  I _ (calling b a) = a ≡ b

  I-step : ∀ {s φ x φ′} → I s φ → Opp φ x φ′ → ∀ n → Supp n (MC.step T.σᴹ (s , x)) (Legal I φ′)
  I-step _ query n =
    Supp-bind _ n _ _ (Supp-return _ _ (λ i → Supp-bind _ i _ _
      (Supp-return _ _ (Supp-return _ _ (calling _ _ , call , refl)) i)) n)
  I-step refl return n =
    Supp-bind _ n _ _ (Supp-return _ _ (λ i → Supp-bind _ i _ _
      (Supp-return _ _ (Supp-return _ _ (idle , answer , tt)) i)) n)

-- A relabelling wire is well-bracketed when the return of a call it makes is
-- relabelled onto the channel it was queried on.
module _ {up : Σ (Ch A) (R A) → Σ (Ch B) (R B)} {down : Σ (Ch B) (Q B) → Σ (Ch A) (Q A)}
         (back : ∀ b q r → proj₁ (up (proj₁ (down (b , q)) , r)) ≡ b) where

  private
    I : ⊤ᵛ → Phase A B → Set
    I _ idle          = ⊤
    I _ (serving _)   = ⊥
    I _ (calling b a) = ∀ r → proj₁ (up (a , r)) ≡ b

    I-step : ∀ {s φ x φ′} → I s φ → Opp φ x φ′ → ∀ n → Supp n (wireStep up down (s , x)) (Legal I φ′)
    I-step _ (query {b} {q}) = Supp-return _ _ (calling b _ , call , back b q)
    I-step g (return {r = r}) =
      Supp-return _ _ (idle , subst (λ b → Ply (serving b) (inj₂ (up (_ , r))) idle) (g r) answer , tt)

  wire-W : W (wireᴹ up down)
  wire-W = record { I = I ; I-init = Supp-return _ _ tt ; I-step = I-step }
