{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Symbolic.Example.SecureChannel.Security where

open import Categories.Category.Monoidal.Bundle
open import Categories.FreeMonoidal using (module FreeObjInterp; Mon)
open import Data.Bool.Base
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Function.Base hiding (_∘_; id)
open import Function.Bundles using (mk⇔; Equivalence)
open import Function.Definitions using (Injective)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Reasoning
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise
open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀
open import CategoricalCrypto.Symbolic.Role Σ₀ using (Atom; void; verdict; pos; neg)
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Protocol
import CategoricalCrypto.Symbolic.Example.SecureChannel.Relation as Channel
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Ideal using (simulated≈ideal-simulator)
import CategoricalCrypto.Symbolic.RunFollowing.Circuit as Circuits
import CategoricalCrypto.Symbolic.RunFollowing.PairEnc as Worlds
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

open FreeObjInterp Mon Atom ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ)

private module G = MonoidalCategory 𝔾ᵒ
private variable Y : ObjTerm

module ContextRun (T : HomTerm (Y ⊗₀ ports) (Var verdict)) (m : Closure (Y ⊗₀ Var void)) where
  cf cg : HomTerm (Var void) (Var verdict)
  cf = (T ∘ id ⊗₁ smt) ∘ m
  cg = (T ∘ id ⊗₁ simulated) ∘ m

  lockstep : (ι : Occ cf → ℕ) → Injective _≡_ _≡_ ι → ⟦ cf ⟧[ ι ] G.≈ ⟦ cg ⟧[ ι ]
  lockstep ι fresh = G.Equiv.trans (G.Equiv.sym (C.Circuit.correct closed true))
    (G.Equiv.trans (≈ᴹ⇒≈ᵒ (RS.relsim⇒≈ᴹ relation)) (C.Circuit.correct closed false))
    where
    κ = ι (inj₁ (inj₂ (inj₂ tt)))
    module Ch = Channel κ
    module C = Circuits κ
    module W = Worlds κ
    module F = W.F
    module R = C.R
    module P = C.P

    channel-circuit : C.Circuit (Var void) ports (λ b → leafᵒ (tt , (tt , tt) , Ch.role b) κ)
    channel-circuit = record
      { machine = λ b → R.tree-role κ (Ch.role b)
      ; following = F.sandwich-following (λ _ x → x) (λ _ x → x)
          (λ w → Sum.map (R.to-flat w pos (Var void)) (R.to-flat w neg ports))
          (λ w → Sum.map (R.from-flat w neg (Var void)) (R.from-flat w pos ports))
          (λ where b w (inj₁ a) → cong inj₁ (R.to-flat-project b w pos (Var void) a)
                   b w (inj₂ a) → cong inj₂ (R.to-flat-project b w neg ports a))
          (λ where b w (inj₁ a) → cong inj₁ (R.from-flat-project b w neg (Var void) a)
                   b w (inj₂ a) → cong inj₂ (R.from-flat-project b w pos ports a))
          Ch.channel-following
      ; correct = λ b → treeᵒ-resp {x = Var void} {y = ports} tt (tt , tt) (≈ᴹ⇒≈ᵒ
          (sandwich-id (runᴿ κ (Ch.role b)) (λ x → x) (λ x → x) (λ _ → refl) (λ _ → refl))) }

    test : C.Context (Y ⊗₀ ports) (Var verdict) ⟦ T ⟧[ ι ∘′ inj₁ ∘′ inj₁ ]
    test = C.context T (ι ∘′ inj₁ ∘′ inj₁) λ o e → impossible o (fresh e)
      where
      impossible : ∀ o → inj₁ (inj₁ o) ≢ inj₁ (inj₂ (inj₂ tt))
      impossible o ()

    closure : C.Context (Var void) (Y ⊗₀ Var void) ⟦ m ⟧[ ι ∘′ inj₂ ]
    closure = C.context m (ι ∘′ inj₂) λ o e → impossible o (fresh e)
      where
      impossible : ∀ o → inj₂ o ≢ inj₁ (inj₂ (inj₂ tt))
      impossible o ()

    closed : C.Circuit (Var void) (Var verdict) (λ b →
      (⟦ T ⟧[ ι ∘′ inj₁ ∘′ inj₁ ] G.∘ (G.id G.⊗₁ leafᵒ (tt , (tt , tt) , Ch.role b) κ)) G.∘ ⟦ m ⟧[ ι ∘′ inj₂ ])
    closed = C.compose-left (C.compose-right test (C.tensor-right C.id-context channel-circuit)) closure

    input : ∀ w → F.Base (P.inputs (C.object (Var void)) (C.object (Var verdict)))
      → F.Related (P.inputs (C.object (Var void)) (C.object (Var verdict))) w
    input w (inj₁ ())
    input w (inj₂ x) = inj₂ (x , tt)

    output : ∀ w → F.Related (P.outputs (C.object (Var void)) (C.object (Var verdict))) w
      → F.Base (P.outputs (C.object (Var void)) (C.object (Var verdict)))
    output w (inj₁ (() , _))
    output w (inj₂ (x , _)) = inj₂ x

    relation = F.following-relsim
      (F.Related (P.inputs (C.object (Var void)) (C.object (Var verdict))))
      (F.Related (P.outputs (C.object (Var void)) (C.object (Var verdict))))
      (F.project (P.inputs (C.object (Var void)) (C.object (Var verdict))))
      (F.project (P.outputs (C.object (Var void)) (C.object (Var verdict))))
      (C.Circuit.following closed) input
      (λ { b w (inj₁ ()) ; b w (inj₂ _) → refl }) output
      (λ { b w (inj₁ (() , _)) ; b w (inj₂ _) → refl })

smt≈simulated : smt Sym.≈ℰ simulated
smt≈simulated = Sym.KE.mk∼ λ { {lift (_ , T)} → lift (same λ m b → mk⇔ (forward T m b) (backward T m b)) }
  where
  forward : (T : HomTerm (Y ⊗₀ ports) (Var verdict)) (m : Closure (Y ⊗₀ Var void)) (b : Bool)
    → eval ((T ∘ id ⊗₁ smt) ∘ m) b → eval ((T ∘ id ⊗₁ simulated) ∘ m) b
  forward T m b (named ι fresh answer) = named ι fresh (≈sym (obs-resp (ContextRun.lockstep T m ι fresh)) ⟨≈⟩ answer)
  backward : (T : HomTerm (Y ⊗₀ ports) (Var verdict)) (m : Closure (Y ⊗₀ Var void)) (b : Bool)
    → eval ((T ∘ id ⊗₁ simulated) ∘ m) b → eval ((T ∘ id ⊗₁ smt) ∘ m) b
  backward T m b (named ι fresh answer) = named ι fresh (obs-resp (ContextRun.lockstep T m ι fresh) ⟨≈⟩ answer)

smt≤ideal : smt Sym.≤UC ideal
smt≤ideal = Sym.dummy-complete
  (simulator , Sym.≈ᵁ-trans (Equivalence.from ≈ᵁ⇔≈ℰ smt≈simulated)
    (Equivalence.from ≈ᵁ⇔≈ℰ simulated≈ideal-simulator))
