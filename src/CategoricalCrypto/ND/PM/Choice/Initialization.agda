{-# OPTIONS --safe --without-K --guardedness #-}

-- Eager PM initialization and the first-activation initialization of `choose`
-- agree only when the selected branch's initialization is total.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
import Data.Unit.Polymorphic.Base as Unit
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Commutative
open import ProbabilisticLogic.Dp.Dominate
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Mass
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (point-⊛)
open import CategoricalCrypto.ND.PM.Choice
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.Wire

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sandwich as Sandwich
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.ND.PM.Choice.Initialization where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MS = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module SW = Sandwich
  module P = Category 𝒫ᴵ
  module Ap = AllPositive ℚ-refinement Approximationᴹ

module Resolution {S : Set} {A B : Iface} (branches : S → Proc⁺ [] A B)
                  (resolver : Proc (Cᶠ (S ∷ [])) 𝟭ᴵ) where
  module O = Online {S} {[]} {A} {B} branches

  chosen : Proc⁺ (S ∷ []) A B
  chosen = choose {S} {[]} {A} {B} branches

  Input : Set
  Input = Pos A ⊎ Neg B

  Output : Set
  Output = Neg A ⊎ Pos B

  inject : Input → O.Input
  inject = Sum.map id inj₂

  discard : Pos (Cᶠ []) ⊎ Pos B → Pos B
  discard (inj₁ ())
  discard (inj₂ b) = b

  erase : Neg A ⊎ (Pos (Cᶠ []) ⊎ Pos B) → Output
  erase = Sum.map id discard

  branch : S → Proc A B
  branch s = MC.mk (MC.state (branches s)) λ (t , i) →
    mapₚ (map₂ erase) (MC.step (branches s) (t , inject i))

  relay : Proc (Cᶠ (S ∷ []) ⊗ᴵ B) B
  relay = SW.sandwichᴹ (subᴵ resolver) (Sum.map id inj₂) (Sum.map id drop⇒ˡ)

  plug-relay : P._≈_ {Cᶠ (S ∷ []) ⊗ᴵ B} {B} (plugᴹ resolver) relay
  plug-relay = wire-∘ᴹ drop⇒ˡ inj₂ (subᴵ resolver)

  module L = Col.Loop Input Output
    (Neg (Cᶠ (S ∷ []) ⊗ᴵ B) ⊎ Pos (Cᶠ (S ∷ []) ⊗ᴵ B))
    (Col.Sᴳ relay chosen) (Col.kᴳ relay chosen)

  machine : Proc A B
  machine = L.tracedᴹ

  plugged : Proc A B
  plugged = P._∘_ {A} {Cᶠ (S ∷ []) ⊗ᴵ B} {B} (plugᴹ resolver) chosen

  plugged-machine : P._≈_ {A} {B} plugged machine
  plugged-machine = P.∘-resp-≈ˡ {A} {Cᶠ (S ∷ []) ⊗ᴵ B} {B} plug-relay
    MS.○ᴹ MS.⟺ᴹ (Col.compose-raw≈∘ᴳ relay chosen)
    MS.○ᴹ Col.collapseᵀ relay chosen

  private
    route : Neg (Cᶠ (S ∷ [])) ⊎ Pos 𝟭ᴵ → Neg (Cᶠ (S ∷ []) ⊗ᴵ B) ⊎ Pos B
    route (inj₁ p) = inj₁ (inj₁ p)
    route (inj₂ ())

    relay-request : (k : MC.St resolver) → MC.step relay (k , inj₁ (inj₁ (inj₁ tt)))
      ≈ₚ mapₚ (map₂ route) (MC.step resolver (k , inj₁ (inj₁ tt)))
    relay-request k = map-fuse (MC.step resolver (k , inj₁ (inj₁ tt))) _ _ _
      (λ where (_ , inj₁ _) → refl ; (_ , inj₂ ()))

    relay-up : (k : MC.St resolver) (b : Pos B) →
      MC.step relay (k , inj₁ (inj₂ b)) ≈ₚ returnₚ (k , inj₂ b)
    relay-up k b = >>=ₚ-identityˡ (k , inj₂ (inj₂ b)) _

    relay-down : (k : MC.St resolver) (b : Neg B) →
      MC.step relay (k , inj₂ b) ≈ₚ returnₚ (k , inj₁ (inj₂ b))
    relay-down k b = >>=ₚ-identityˡ (k , inj₁ (inj₂ b)) _

  finish : (k : MC.St resolver) (s : S) → MC.St (branches s) × (Neg A ⊎ (Pos (Cᶠ []) ⊎ Pos B))
         → MC.St machine × Output
  finish k s (t , o) = (k , O.active s t) , erase o

  resume-picked : Input → MC.St resolver × (Neg (Cᶠ (S ∷ [])) ⊎ Pos 𝟭ᴵ) → Dₚ (MC.St machine × Output)
  resume-picked i (k , inj₁ (inj₁ _ , s)) = MC.point (MC.state (branches s)) Unit.tt >>=ₚ λ t →
    mapₚ (finish k s) (MC.step (branches s) (t , inject i))
  resume-picked i (_ , inj₁ (inj₂ () , _))
  resume-picked i (_ , inj₂ ())

  private
    exit : (k : MC.St resolver) (s : S) (t : MC.St (branches s))
           (o : Neg A ⊎ (Pos (Cᶠ []) ⊎ Pos B)) →
      contᵢ L.body ((k , O.active s t) , Col.outᶠ (O.emit o))
      ≈ₚ returnₚ (finish k s (t , o))
    exit k s t (inj₁ a) = ≈refl
    exit k s t (inj₂ (inj₁ ()))
    exit k s t (inj₂ (inj₂ b)) = L.loop-pass (k , O.active s t) (inj₂ (inj₂ b))
      (k , O.active s t) (inj₁ (inj₂ b))
      (bindˣ (relay-up k b) ⟨≈⟩ >>=ₚ-identityˡ (k , inj₂ b) _)

    run-exit : (k : MC.St resolver) (s : S) (t : MC.St (branches s)) (i : O.Input) →
      (O.run s t i >>=ₚ λ r → returnₚ ((k , proj₁ r) , Col.outᶠ (proj₂ r)) >>=ₚ contᵢ L.body)
      ≈ₚ mapₚ (finish k s) (MC.step (branches s) (t , i))
    run-exit k s t i = bind-map (MC.step (branches s) (t , i)) _ _
      ⟨≈⟩ bindᶠ (λ (t′ , o) → >>=ₚ-identityˡ ((k , O.active s t′) , Col.outᶠ (O.emit o)) _
        ⟨≈⟩ exit k s t′ o)

    pick : (k : MC.St resolver) (i : Input) (s : S) →
      iterₚ L.body ((k , O.wait (inject i)) , inj₁ (inj₁ (inj₁ tt , s)))
      ≈ₚ (MC.point (MC.state (branches s)) Unit.tt >>=ₚ λ t →
        mapₚ (finish k s) (MC.step (branches s) (t , inject i)))
    pick k i s = L.loop-fix (k , O.wait (inject i)) (inj₁ (inj₁ (inj₁ tt , s)))
      ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state (branches s)) Unit.tt >>=ₚ λ t → O.run s t (inject i)) _ _
      ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state (branches s)) Unit.tt) _ _
      ⟨≈⟩ bindᶠ (λ t → run-exit k s t (inject i))

    request : (k : MC.St resolver) (i : Input) →
      iterₚ L.body ((k , O.wait (inject i)) , inj₂ (inj₁ (inj₁ tt)))
      ≈ₚ (MC.step resolver (k , inj₁ (inj₁ tt)) >>=ₚ resume-picked i)
    request k i = L.loop-fix (k , O.wait (inject i)) (inj₂ (inj₁ (inj₁ tt)))
      ⟨≈⟩ >>=ₚ-assoc (MC.step relay (k , inj₁ (inj₁ (inj₁ tt)))) _ _
      ⟨≈⟩ bindˣ (relay-request k)
      ⟨≈⟩ bind-map (MC.step resolver (k , inj₁ (inj₁ tt))) _ _
      ⟨≈⟩ bindᶠ (λ where
        (k′ , inj₁ (inj₁ _ , s)) → >>=ₚ-identityˡ ((k′ , O.wait (inject i)) , inj₂ (inj₁ (inj₁ (inj₁ tt , s)))) _
          ⟨≈⟩ pick k′ i s
        (_ , inj₁ (inj₂ () , _))
        (_ , inj₂ ()))

    ordinary-down : (t : O.State) (b : Neg B) →
      O.step (t , inj₂ (inj₂ b)) ≡ O.feed t (inj₂ (inj₂ b))
    ordinary-down O.fresh b = refl
    ordinary-down (O.wait _) b = refl
    ordinary-down (O.active _ _) b = refl

    enter : (k : MC.St resolver) (t : O.State) (i : Input) →
      MC.step machine ((k , t) , i)
      ≈ₚ (O.feed t (inject i) >>=ₚ λ r →
        returnₚ ((k , proj₁ r) , Col.outᶠ (proj₂ r)) >>=ₚ contᵢ L.body)
    enter k t (inj₁ a) = L.step-red (k , t) (inj₁ a)
      ⟨≈⟩ >>=ₚ-assoc (O.feed t (inj₁ a)) _ _
    enter k t (inj₂ b) = L.step-red (k , t) (inj₂ b)
      ⟨≈⟩ bindˣ (bindˣ (relay-down k b) ⟨≈⟩ >>=ₚ-identityˡ (k , inj₁ (inj₂ b)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((k , t) , inj₂ (inj₁ (inj₂ b))) _
      ⟨≈⟩ L.loop-fix (k , t) (inj₁ (inj₂ b))
      ⟨≈⟩ bindˣ (bindˣ (≡⇒≈ₚ (ordinary-down t b)))
      ⟨≈⟩ >>=ₚ-assoc (O.feed t (inj₂ (inj₂ b))) _ _

  step-active : (k : MC.St resolver) (s : S) (t : MC.St (branches s)) (i : Input) →
    MC.step machine ((k , O.active s t) , i)
    ≈ₚ mapₚ (finish k s) (MC.step (branches s) (t , inject i))
  step-active k s t i = enter k (O.active s t) i ⟨≈⟩ run-exit k s t (inject i)

  step-fresh : (k : MC.St resolver) (i : Input) →
    MC.step machine ((k , O.fresh) , i)
    ≈ₚ (MC.step resolver (k , inj₁ (inj₁ tt)) >>=ₚ resume-picked i)
  step-fresh k i = enter k O.fresh i
    ⟨≈⟩ >>=ₚ-identityˡ (O.wait (inject i) , inj₂ (inj₁ (inj₁ tt))) _
    ⟨≈⟩ >>=ₚ-identityˡ ((k , O.wait (inject i)) , inj₂ (inj₂ (inj₁ (inj₁ tt)))) _
    ⟨≈⟩ request k i

  run-init : (d : Strat Input Output) → runˢ machine d
    ≈ₚ (MC.point (MC.state resolver) Unit.tt >>=ₚ λ k → runFromˢ machine (k , O.fresh) d)
  run-init d = bindˣ (point-⊛ (MC.state relay) (MC.state chosen) Unit.tt)
    ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state resolver) Unit.tt) _ _
    ⟨≈⟩ bindᶠ (λ k → bindˣ (>>=ₚ-identityˡ O.fresh _) ⟨≈⟩ >>=ₚ-identityˡ (k , O.fresh) _)

  run-active : (k : MC.St resolver) (s : S) (t : MC.St (branches s)) (d : Strat Input Output) →
    runFromˢ machine (k , O.active s t) d ≈ₚ runFromˢ (branch s) t d
  run-active k s t (out b) = ≈refl
  run-active k s t (coin μ c) = bindᶠ (λ b → run-active k s t (c b))
  run-active k s t (ask i c) = bindˣ (step-active k s t i)
    ⟨≈⟩ bind-map (MC.step (branches s) (t , inject i)) _ _
    ⟨≈⟩ bindᶠ (λ (t′ , o) → run-active k s t′ (c (erase o)))
    ⟨≈⟩ ≈sym (bind-map (MC.step (branches s) (t , inject i)) _ _)

constant-pick : {S : Set} → S → Proc (Cᶠ (S ∷ [])) 𝟭ᴵ
constant-pick s = MC.mk MC.Iˢ λ where
  (k , inj₁ (inj₁ _)) → returnₚ (k , inj₁ (inj₁ tt , s))
  (_ , inj₁ (inj₂ ()))
  (_ , inj₂ ())

module Constant {S : Set} {A B : Iface} (branches : S → Proc⁺ [] A B) (s : S) where
  module R = Resolution {S} {A} {B} branches (constant-pick s)
  open R using (branch; machine; plugged)

  TotalInitialization : Set
  TotalInitialization = ASTotal (MC.point (MC.state (branches s)) Unit.tt)

  private
    prefix : Strat R.Input R.Output → Dₚ Bool
    prefix d = MC.point (MC.state (branches s)) Unit.tt >>=ₚ λ t → runFromˢ (branch s) t d

    run-fresh : TotalInitialization → (d : Strat R.Input R.Output) →
      runFromˢ machine (Unit.tt , R.O.fresh) d Ap.∼ᵃ prefix d
    run-fresh total (out b) ε pos = ≈ₚ[]-sym (astotal-bind _ (returnₚ b) total ε pos)
    run-fresh total (coin μ c) ε pos = ≈ₚ[]-resp ≈refl
      (≈sym (>>=ₚ-swap (MC.point (MC.state (branches s)) Unit.tt) (coinₚ μ)
        (λ t b → runFromˢ (branch s) t (c b))))
      ( (λ b → dom-bind (indᵇ b) (indᵇ-nn b) (<⇒≤ pos) (coinₚ μ) _ _
          (λ x → proj₁ (run-fresh total (c x) ε pos) b))
      , (λ b → dom-bind (indᵇ b) (indᵇ-nn b) (<⇒≤ pos) (coinₚ μ) _ _
          (λ x → proj₂ (run-fresh total (c x) ε pos) b)))
    run-fresh total (ask i c) ε pos = Ap.zero⇒positive (≈ₚ⇒≈ₚ[0] eq) ε pos
      where
      eq : runFromˢ machine (Unit.tt , R.O.fresh) (ask i c) ≈ₚ prefix (ask i c)
      eq = bindˣ (R.step-fresh Unit.tt i)
        ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (Unit.tt , inj₁ (inj₁ tt , s)) _)
        ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state (branches s)) Unit.tt) _ _
        ⟨≈⟩ bindᶠ (λ t → bind-map (MC.step (branches s) (t , R.inject i)) _ _
          ⟨≈⟩ bindᶠ (λ (t′ , o) → R.run-active Unit.tt s t′ (c (R.erase o)))
          ⟨≈⟩ ≈sym (bind-map (MC.step (branches s) (t , R.inject i)) _ _))

  constant-pick-≈ᴿ : TotalInitialization → plugged ≈ᴿ branch s
  constant-pick-≈ᴿ total d ε pos = ≈ₚ[]-resp
    (≈sym (runˢ-resp-≈ᴹ R.plugged-machine d ⟨≈⟩ R.run-init d ⟨≈⟩ >>=ₚ-identityˡ Unit.tt _))
    ≈refl (run-fresh total d ε pos)
