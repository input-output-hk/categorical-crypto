{-# OPTIONS --safe --without-K --guardedness #-}

-- SSP games are dense among well-bracketed closures (`games-dense`): SSP tests
-- that agree on every SSP game agree on every well-bracketed closure.  So
-- compilation carries SSP's tests to PM[wb]'s (`νᵂ`), and is a morphism of
-- setups, `SSP→PM[wb]` (`docs/uc-setup-ssp.md` §6, C7).
--
-- A compiled test over a closure is the oracle machine
-- (`Protocol.Machine.Oracle`), so its readout is the test's call tree run
-- against the closure's steps (`obs-oracle`).  The closure from a state `s`,
-- its steps cut at depth `n`, is an SSP game (`game`).  By induction on the
-- call tree, the depth-`n` readout is at most the game's verdict mass
-- (`below`), and the game's is at most a finite readout (`above`), its depth
-- maxed over the finitely many values a node reaches (`Dp.uniformize`).  The
-- same games serve both tests, and the slack is paid once, against the
-- closure's initial state.  Well-bracketedness is not used: a compiled test
-- checks every reply's channel.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation using (ntHelper)

open import Class.DecEq
open import Data.Bool.Base
open import Data.Empty
open import Data.Nat.Base as ℕ using (ℕ; suc)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties hiding (_≟_)
open import Data.Rational.Properties.Ext
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.RationalDist.Advantage
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Mass using (cum-const-≤)
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.Protocol using () renaming (Calls to Callsᶠ)
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Oracle
open import CategoricalCrypto.SSP.Compile
open import CategoricalCrypto.SSP.Cut
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Monoidal
open import CategoricalCrypto.SSP.Semantics
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Bracket.Monitor
open import CategoricalCrypto.UC.Bracket.Setup
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Machine hiding (Ωᴵ)
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UCSetup.Morphism

import Categories.Morphism as Mor
import CategoricalCrypto.Iface as Flat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.SSP.Setup as SSP

module CategoricalCrypto.SSP.Dense where

private
  module G  = MonoidalCategory 𝔾ᵒ
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫  = Category 𝒫ᴵ

private variable A : Iface

------------------------------------------------------------------------
-- A closure's games, and a compiled test's tree

-- A closure has nothing below it.
e⁺ : ¬ Σ (Ch unitᴵ) (R unitᴵ)
e⁺ (() , _)

e⁻ : ¬ Σ (Ch unitᴵ) (Q unitᴵ)
e⁻ (() , _)

-- An answer on `c′` to a call on `c`.
replyᵍ : {S : Set} {c c′ : Ch A} → Dec (c′ ≡ c) → S → R A c′ → Calls unitᴵ (S × R A c)
replyᵍ (yes refl) s r = ret (s , r)
replyᵍ (no _)     _ _ = dead

module _ (m̂ : Proc (flat unitᴵ) (flat A)) where

  settle : (c : Ch A) → MC.St m̂ × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch A) (R A)) → Calls unitᴵ (MC.St m̂ × R A c)
  settle c (_ , inj₁ x)        = ⊥-elim (e⁻ x)
  settle c (s , inj₂ (c′ , r)) = replyᵍ {A} (_≟_ ⦃ Ch-dec A ⦄ c′ c) s r

  -- The closure from the state `s`, its steps cut at depth `n`.
  game : ℕ → MC.St m̂ → Protocol unitᴵ A
  game n s = record { St = MC.St m̂ ; init = s ; step = λ s′ c q → cutᵏ n (MC.step m̂ (s′ , inj₂ (c , q))) (settle c) }

compiled : {S : Set} → Calls A (S × Bool) → Callsᶠ (flat A) (S × Σ (Ch Ωᴵ) (R Ωᴵ))
compiled {A} t = toCalls ⦃ Ch-dec A ⦄ (mapᶜ (map₂ (tt ,_)) t)

verd : {X : Set} → X × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)) → Bool
verd (_ , inj₁ x)       = ⊥-elim (e⁻ x)
verd (_ , inj₂ (_ , b)) = b

------------------------------------------------------------------------
-- A test's tree against the closure, and against its games

module _ (D : Protocol A Ωᴵ) (m̂ : Proc (flat unitᴵ) (flat A)) (n : ℕ) (s₀ : MC.St m̂)
         (V : Bool → ℚ) (nnV : NNF V) where

  private
    P = toProtocol ⦃ Ch-dec A ⦄ D
    Gm = game {A} m̂ n s₀

    Out : Set
    Out = (MSt P × MC.St m̂) × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ))

    runᵒ : Callsᶠ (flat A) (St D × Σ (Ch Ωᴵ) (R Ωᴵ)) → MC.St m̂ → Dₚ Out
    runᵒ = orun e⁺ e⁻ P m̂

    Vᵛ : Out → ℚ
    Vᵛ y = V (verd y)

    nnVᵛ : NNF Vᵛ
    nnVᵛ y = nnV (verd y)

    Vᵍ : (St D × MC.St m̂) × Bool → ℚ
    Vᵍ p = V (proj₂ p)

    -- The continuation a compiled call waits on (`toCalls`).
    K : {c : Ch A} → (R A c → Calls A (St D × Bool)) → Σ (Ch A) (R A) → Callsᶠ (flat A) (St D × Σ (Ch Ωᴵ) (R Ωᴵ))
    K k = resume A (λ r → mapᶜ (map₂ (tt ,_)) (k r))

    -- The rest of the game after a call.
    rest : {c : Ch A} → (R A c → Calls A (St D × Bool)) → MC.St m̂ × R A c → ℚ
    rest k p = ev (graft D Gm (k (proj₂ p)) (proj₁ p)) Vᵍ

    Above : {c : Ch A} → (R A c → Calls A (St D × Bool))
          → MC.St m̂ × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch A) (R A)) → ℕ → Set
    Above {c} k y i = ev (settle {A} m̂ c y) (rest k) ℚ.≤ cum i (answer e⁺ e⁻ P m̂ (K k) y) Vᵛ

  mutual
    below : (t : Calls A (St D × Bool)) (s : MC.St m̂) → cum n (runᵒ (compiled t) s) Vᵛ ℚ.≤ ev (graft D Gm t s) Vᵍ
    below (ret (sD , b)) s =
      ≤-trans (returnₚ-cum-≤ n ((idle sD , s) , inj₂ (tt , b)) Vᵛ nnVᵛ) (≤-reflexive (sym (ev-ret ((sD , s) , b) Vᵍ)))
    below (call c q k) s =
      ≤-trans (>>=ₚ-boundA n d (answer e⁺ e⁻ P m̂ (K k)) Vᵛ nnVᵛ)
     (≤-trans (cum-mono-P n d (λ y → cum n (answer e⁺ e⁻ P m̂ (K k) y) Vᵛ) (λ y → ev (settle {A} m̂ c y) (rest k))
                          (below-answer k))
              (≤-reflexive (sym (trans (ev-serve D Gm k (cutᵏ n d (settle {A} m̂ c)) Vᵍ) (ev-cutᵏ n d (settle {A} m̂ c) (rest k))))))
      where d = MC.step m̂ (s , inj₂ (c , q))
    below (coin μ k) s =
      ≤-trans (>>=ₚ-boundA n (coinₚ μ) (λ b → runᵒ (compiled (k b)) s) Vᵛ nnVᵛ)
     (≤-trans (coin-≤E μ n (λ b → cum n (runᵒ (compiled (k b)) s) Vᵛ) (λ b → cum-nn n (runᵒ (compiled (k b)) s) Vᵛ nnVᵛ))
     (≤-trans (E-mono μ (λ b → cum n (runᵒ (compiled (k b)) s) Vᵛ) (λ b → ev (graft D Gm (k b) s) Vᵍ) (λ b → below (k b) s))
              (≤-reflexive (sym (ev-coin μ (λ b → graft D Gm (k b) s) Vᵍ)))))
    below dead s = ≤-reflexive (trans (botₚ-cum n Vᵛ) (sym (ev-dead Vᵍ)))

    below-answer : {c : Ch A} (k : R A c → Calls A (St D × Bool))
                   (y : MC.St m̂ × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch A) (R A)))
                 → cum n (answer e⁺ e⁻ P m̂ (K k) y) Vᵛ ℚ.≤ ev (settle {A} m̂ c y) (rest k)
    below-answer k (_  , inj₁ x)        = ⊥-elim (e⁻ x)
    below-answer k (s′ , inj₂ (c′ , r)) = below-reply k (_≟_ ⦃ Ch-dec A ⦄ c′ _) s′ r

    below-reply : {c c′ : Ch A} (k : R A c → Calls A (St D × Bool)) (d : Dec (c′ ≡ c)) (s′ : MC.St m̂) (r : R A c′)
                → cum n (runᵒ (reply {A} ⦃ Ch-dec A ⦄ d r (λ r → compiled (k r))) s′) Vᵛ ℚ.≤ ev (replyᵍ {A} d s′ r) (rest k)
    below-reply k (yes refl) s′ r = ≤-trans (below (k r) s′) (≤-reflexive (sym (ev-ret (s′ , r) (rest k))))
    below-reply k (no _)     s′ r = ≤-reflexive (trans (botₚ-cum n Vᵛ) (sym (ev-dead (rest k))))

  mutual
    above : (t : Calls A (St D × Bool)) (s : MC.St m̂) → Σ[ j ∈ ℕ ] ev (graft D Gm t s) Vᵍ ℚ.≤ cum j (runᵒ (compiled t) s) Vᵛ
    above (ret (sD , b)) s =
      1 , ≤-reflexive (trans (ev-ret ((sD , s) , b) Vᵍ) (sym (returnₚ-cum 0 ((idle sD , s) , inj₂ (tt , b)) Vᵛ)))
    above (call c q k) s =
      let J , sp = uniformize (Above k) (λ y le h → ≤-trans h (cum-mono le (answer e⁺ e⁻ P m̂ (K k) y) Vᵛ nnVᵛ))
                              (above-answer k) n d
      in n ℕ.+ J
       , ≤-trans (≤-reflexive (trans (ev-serve D Gm k (cutᵏ n d (settle {A} m̂ c)) Vᵍ) (ev-cutᵏ n d (settle {A} m̂ c) (rest k))))
         (≤-trans (cum-mono-Supp n d (λ y → ev (settle {A} m̂ c y) (rest k)) (λ y → cum J (answer e⁺ e⁻ P m̂ (K k) y) Vᵛ) sp)
                  (>>=ₚ-boundB n J d (answer e⁺ e⁻ P m̂ (K k)) Vᵛ nnVᵛ))
      where d = MC.step m̂ (s , inj₂ (c , q))
    above (coin μ k) s =
      let j₁ , h₁ = above (k true) s
          j₂ , h₂ = above (k false) s
      in suc (suc (j₁ ℕ.⊔ j₂))
       , ≤-trans (≤-reflexive (ev-coin μ (λ b → graft D Gm (k b) s) Vᵍ))
         (≤-trans (E-mono μ (λ b → ev (graft D Gm (k b) s) Vᵍ) (λ b → cum (j₁ ℕ.⊔ j₂) (runᵒ (compiled (k b)) s) Vᵛ) λ where
                     true  → ≤-trans h₁ (cum-mono (m≤m⊔n j₁ j₂) (runᵒ (compiled (k true)) s) Vᵛ nnVᵛ)
                     false → ≤-trans h₂ (cum-mono (m≤n⊔m j₁ j₂) (runᵒ (compiled (k false)) s) Vᵛ nnVᵛ))
                  (≤-reflexive (sym (coin-bind-cum μ (λ b → runᵒ (compiled (k b)) s) (j₁ ℕ.⊔ j₂) Vᵛ))))
    above dead s = 0 , ≤-reflexive (ev-dead Vᵍ)

    above-answer : {c : Ch A} (k : R A c → Calls A (St D × Bool))
                   (y : MC.St m̂ × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch A) (R A))) → Σ[ i ∈ ℕ ] Above k y i
    above-answer k (_  , inj₁ x)        = ⊥-elim (e⁻ x)
    above-answer k (s′ , inj₂ (c′ , r)) = above-reply k (_≟_ ⦃ Ch-dec A ⦄ c′ _) s′ r

    above-reply : {c c′ : Ch A} (k : R A c → Calls A (St D × Bool)) (d : Dec (c′ ≡ c)) (s′ : MC.St m̂) (r : R A c′)
                → Σ[ i ∈ ℕ ] ev (replyᵍ {A} d s′ r) (rest k) ℚ.≤ cum i (runᵒ (reply {A} ⦃ Ch-dec A ⦄ d r (λ r → compiled (k r))) s′) Vᵛ
    above-reply k (yes refl) s′ r = let j , h = above (k r) s′ in j , ≤-trans (≤-reflexive (ev-ret (s′ , r) (rest k))) h
    above-reply k (no _)     s′ r = 0 , ≤-reflexive (ev-dead (rest k))

------------------------------------------------------------------------
-- Readouts

-- One tick of a closed machine, its verdict.
readoutᴹ : Proc (flat unitᴵ) (flat Ωᴵ) → Dₚ Bool
readoutᴹ M = MC.point (MC.state M) ttᵛ >>=ₚ λ st → mapₚ verd (MC.step M (st , inj₂ (tt , tt)))

-- A closed well-bracketed composite reads as any machine it equals.  Opaque
-- here and below: a readout proof is only ever projected, and transparent its
-- depth witnesses unfold through every step (`dense≼` exhausts 3 GiB).
opaque
  obs-proc : (t : unitᴵ 𝒲ᵂ.⇒ Ωᴵ) (M : Proc (flat unitᴵ) (flat Ωᴵ)) → proj₁ t G.≈ procᵒ M → Obsᵂ t ≈ₚ readoutᴹ M
  obs-proc t M e =
        obs-resp (refl⟩∘⟨ ((e ⟩∘⟨refl) ○ ⟺ (procᵒ-∘ {Flat.unitᴵ} {flat unitᴵ} {flat Ωᴵ} M υʷ)))
    ⟨≈⟩ runᴹ-resp-≈ᴹ (unprocᵒ-∘ {Flat.unitᴵ} {flat Ωᴵ} {Bool Flat.⇿ ⊤} ωʷ X) (ask tt out)
    ⟨≈⟩ runᴹ-resp-≈ᴹ wires (ask tt out)
    ⟨≈⟩ bindᶠ λ st → bind-map (MC.step M (st , inj₂ (tt , tt))) _ _ ⟨≈⟩ bindᶠ verdict
    where
    open G.HomReasoning

    X : Proc Flat.unitᴵ (flat Ωᴵ)
    X = 𝒫._∘_ {Flat.unitᴵ} {flat unitᴵ} {flat Ωᴵ} M υʷ

    υup : Flat.Pos Flat.unitᴵ → Σ (Ch unitᴵ) (R unitᴵ)
    υup ()

    υdown : Σ (Ch unitᴵ) (Q unitᴵ) → Flat.Neg Flat.unitᴵ
    υdown (() , _)

    -- `υʷ`'s relabellings are absurd, so any two are the same wire.
    υ≈ : 𝒫._≈_ {Flat.unitᴵ} {flat unitᴵ} υʷ (wireᴹ υup υdown)
    υ≈ = S.≲⇒≈ᴹ (Pw.simFn (λ s → s) (λ x → >>=ₚ-identityʳ (MC.point MC.Iˢ x)) λ where
                   (_ , inj₁ ())
                   (_ , inj₂ (() , _)))

    i : Data.Empty.⊥ ⊎ ⊤ → Σ (Ch unitᴵ) (R unitᴵ) ⊎ Σ (Ch Ωᴵ) (Q Ωᴵ)
    i x = Sum.map υup (λ x → x) (Sum.map (λ a → a) (λ _ → tt , tt) x)

    o : Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ) → Data.Empty.⊥ ⊎ Bool
    o y = Sum.map (λ a → a) proj₂ (Sum.map υdown (λ x → x) y)

    wires : S._≈ᴹ_ (𝒫._∘_ {Flat.unitᴵ} {flat Ωᴵ} {Bool Flat.⇿ ⊤} ωʷ X) (sandwichᴹ M i o)
    wires =
           𝒫.∘-resp-≈ʳ {Flat.unitᴵ} {flat Ωᴵ} {Bool Flat.⇿ ⊤} {g = ωʷ}
             (𝒫.∘-resp-≈ʳ {Flat.unitᴵ} {flat unitᴵ} {flat Ωᴵ} {g = M} υ≈
              S.○ᴹ ∘-wireᴹ {Flat.unitᴵ} {flat unitᴵ} {flat Ωᴵ} υup υdown M)
      S.○ᴹ wire-∘ᴹ {Flat.unitᴵ} {flat Ωᴵ} {Bool Flat.⇿ ⊤} proj₂ (λ _ → tt , tt)
             (sandwichᴹ M (Sum.map υup (λ x → x)) (Sum.map υdown (λ x → x)))
      S.○ᴹ sandwich-∘ M (Sum.map υup (λ x → x)) (Sum.map υdown (λ x → x))
             (Sum.map (λ a → a) (λ _ → tt , tt)) (Sum.map (λ a → a) proj₂)

    verdict : (y : MC.St M × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ)))
            → resumeᴹ (sandwichᴹ M i o) (λ _ r → returnₚ r) (proj₁ y , o (proj₂ y)) ≈ₚ returnₚ (verd y)
    verdict (_ , inj₁ x) = ⊥-elim (e⁻ x)
    verdict (_ , inj₂ _) = ≈refl

module _ (D : Protocol A Ωᴵ) (m : unitᴵ 𝒲ᵂ.⇒ A) where

  private
    m̂ : Proc (flat unitᴵ) (flat A)
    m̂ = proj₁ (proj₂ m)

    P = toProtocol ⦃ Ch-dec A ⦄ D

  -- The test's call tree run against the closure's steps.
  oracle-run : Dₚ Bool
  oracle-run = MC.point (MC.state m̂) ttᵛ >>=ₚ λ s → mapₚ verd (orun e⁺ e⁻ P m̂ (compiled (step D (init D) tt tt)) s)

  -- The continuations are pinned: left to inference they exhaust 3 GiB.
  opaque
    obs-oracle : Obsᵂ (⟦ D ⟧ᵂ 𝒲ᵂ.∘ m) ≈ₚ oracle-run
    obs-oracle =
          obs-proc (⟦ D ⟧ᵂ 𝒲ᵂ.∘ m) (oracleᴹ e⁺ e⁻ P m̂)
            ( (refl⟩∘⟨ proj₂ (proj₂ (proj₂ m)))
            ○ ⟺ (procᵒ-∘ {flat unitᴵ} {flat A} {flat Ωᴵ} (protᴹ D) m̂)
            ○ ≈ᴹ⇒≈ᵒ {flat unitᴵ} {flat Ωᴵ} (S.⟺ᴹ (oracle≈∘ e⁺ e⁻ P m̂)))
      ⟨≈⟩ bindˣ {k = k} (Pw.point-⊛ (stateᴹ P) (MC.state m̂) ttᵛ ⟨≈⟩ >>=ₚ-identityˡ (idle (init D)) λ a → pt >>=ₚ λ b → returnₚ (a , b))
      ⟨≈⟩ >>=ₚ-assoc pt (λ b → returnₚ (idle (init D) , b)) k
      ⟨≈⟩ bindᶠ (λ s → >>=ₚ-identityˡ (idle (init D) , s) k)
      where
      open G.HomReasoning

      pt : Dₚ (MC.St m̂)
      pt = MC.point (MC.state m̂) ttᵛ

      k : MSt P × MC.St m̂ → Dₚ Bool
      k st = mapₚ verd (stepᴼ e⁺ e⁻ P m̂ (st , inj₂ (tt , tt)))

------------------------------------------------------------------------
-- Density

private
  -- One side of a distance bound.
  ∣-∣≤⇒≤+ : (x y ε : ℚ) → ℚ.∣ x ℚ.- y ∣ ℚ.≤ ε → x ℚ.≤ y ℚ.+ ε
  ∣-∣≤⇒≤+ x y ε h = ≤-trans (≤-reflexive (sym (−-+-cancel x y)))
                    (≤-trans (+-monoˡ-≤ y (≤-trans (p≤∣p∣ (x ℚ.- y)) h)) (≤-reflexive (+-comm ε y)))

module _ {D D′ : Protocol A Ωᴵ} (agree : D SSP.≋ D′) (m : unitᴵ 𝒲ᵂ.⇒ A) (ε : ℚ) (pos : 0ℚ ℚ.< ε) (b : Bool) where

  private
    m̂ : Proc (flat unitᴵ) (flat A)
    m̂ = proj₁ (proj₂ m)

    pt : Dₚ (MC.St m̂)
    pt = MC.point (MC.state m̂) ttᵛ

    readᴰ : Protocol A Ωᴵ → MC.St m̂ → Dₚ Bool
    readᴰ E s = mapₚ verd (orun e⁺ e⁻ (toProtocol ⦃ Ch-dec A ⦄ E) m̂ (compiled (step E (init E) tt tt)) s)

    pr : Protocol A Ωᴵ → ℕ → MC.St m̂ → ℚ
    pr E n s = Prᵇ⊥ b (runᵖ (E ∘ᵖ game {A} m̂ n s))

    pr-ev : (E : Protocol A Ωᴵ) (n : ℕ) (s : MC.St m̂)
          → pr E n s ≡ ev (graft E (game {A} m̂ n s) (step E (init E) tt tt) s) (λ p → indᵇ b (proj₂ p))
    pr-ev E n s = ev-map proj₂ (graft E (game {A} m̂ n s) (step E (init E) tt tt) s) (indᵇ b)

    -- The depth-`n` readout against `D` is below the game's verdict against `D′`.
    below-slack : (n : ℕ) (s : MC.St m̂) → cum n (readᴰ D s) (indᵇ b) ℚ.≤ pr D′ n s ℚ.+ ε
    below-slack n s =
      ≤-trans (mapₚ-≤ n verd _ (indᵇ b) (indᵇ-nn b))
     (≤-trans (below D m̂ n s (indᵇ b) (indᵇ-nn b) (step D (init D) tt tt) s)
     (≤-trans (≤-reflexive (sym (pr-ev D n s)))
              (∣-∣≤⇒≤+ (pr D n s) (pr D′ n s) ε (agree (game {A} m̂ n s) ε pos b))))

    above-read : (n : ℕ) (s : MC.St m̂) → Σ[ i ∈ ℕ ] pr D′ n s ℚ.≤ cum i (readᴰ D′ s) (indᵇ b)
    above-read n s =
      let j , h = above D′ m̂ n s (indᵇ b) (indᵇ-nn b) (step D′ (init D′) tt tt) s
      in suc j , ≤-trans (≤-reflexive (pr-ev D′ n s)) (≤-trans h (≤-reflexive (sym (mapₚ-cum j verd _ (indᵇ b)))))

  dense≼ : Dom (indᵇ b) ε (Obsᵂ (⟦ D ⟧ᵂ 𝒲ᵂ.∘ m)) (Obsᵂ (⟦ D′ ⟧ᵂ 𝒲ᵂ.∘ m))
  dense≼ k =
    let k₁ , le₁ = proj₁ (obs-oracle D m) (indᵇ b) (indᵇ-nn b) k
        J  , sp  = uniformize (λ s i → pr D′ k₁ s ℚ.≤ cum i (readᴰ D′ s) (indᵇ b))
                              (λ s le h → ≤-trans h (cum-mono le (readᴰ D′ s) (indᵇ b) (indᵇ-nn b)))
                              (above-read k₁) k₁ pt
        k₂ , le₂ = proj₂ (obs-oracle D′ m) (indᵇ b) (indᵇ-nn b) (k₁ ℕ.+ J)
    in k₂
     , ≤-trans le₁
       (≤-trans (>>=ₚ-boundA k₁ pt (readᴰ D) (indᵇ b) (indᵇ-nn b))
       (≤-trans (cum-mono-P k₁ pt (λ s → cum k₁ (readᴰ D s) (indᵇ b)) (λ s → pr D′ k₁ s ℚ.+ ε) (below-slack k₁))
       (≤-trans (≤-reflexive (cum-add k₁ pt (pr D′ k₁) (λ _ → ε)))
       (≤-trans (+-mono-≤ (cum-mono-Supp k₁ pt (pr D′ k₁) (λ s → cum J (readᴰ D′ s) (indᵇ b)) sp) (cum-const-≤ k₁ pt (<⇒≤ pos)))
                (+-monoˡ-≤ ε (≤-trans (>>=ₚ-boundB k₁ J pt (readᴰ D′) (indᵇ b) (indᵇ-nn b)) le₂))))))

games-dense : {D D′ : Protocol A Ωᴵ} → D SSP.≋ D′
            → Observable._≋_ (Evaluation.observable evaluationᵂ) ⟦ D ⟧ᵂ ⟦ D′ ⟧ᵂ
games-dense {D = D} {D′ = D′} agree m ε pos = (λ b → dense≼ agree m ε pos b) , (λ b → dense≼ agree˘ m ε pos b)
  where
  agree˘ : D′ SSP.≋ D
  agree˘ G δ pos′ c = ≤-trans (≤-reflexive (advᵇ⊥-sym c (runᵖ (D′ ∘ᵖ G)) (runᵖ (D ∘ᵖ G)))) (agree G δ pos′ c)

------------------------------------------------------------------------
-- The morphism of setups

νᵂ : PresheafMorphism (StrongMonoidalFunctor.F Fᵂ) SSP.ℰᵖ ℰ[wb]
νᵂ = record { ν = ntHelper record
  { η = λ _ → record { to = ⟦_⟧ᵂ ; cong = games-dense }
  ; commute = λ {_} {Y} f {D} → Observable.≈⇒≋ (Evaluation.observable evaluationᵂ) {A = Y}
      {t = ⟦ D ∘ᵖ f ⟧ᵂ} {u = ⟦ D ⟧ᵂ 𝒲ᵂ.∘ ⟦ f ⟧ᵂ} (⟦⟧ᵂ-∘ D f) } }

SSP→PM[wb] : UCSetupMorphism SSP.StdSetup StdSetup
SSP→PM[wb] = StdUCMorphism Protᴹ PM[wb]ᴹ SSP.ℰᵖ ℰ[wb] Fᵂ νᵂ

-- `Fᵂ` is the identity on objects, so `≈ℰ` crossing suffices
-- (`Standard2.Morphism.surjective⇒preserves-≈ᵁ`).
≤UC-transfer : Transfer.Preserves-≈ℰ SSP→PM[wb] → Transfer.Preserves-≤UC SSP→PM[wb]
≤UC-transfer pres = Transfer.transfer⁺ SSP→PM[wb] (surjective⇒preserves-≈ᵁ Protᴹ PM[wb]ᴹ SSP.ℰᵖ ℰ[wb] Fᵂ νᵂ
  (λ A → A , Mor.≅.refl (MonoidalCategory.U PM[wb]ᴹ)) pres)
