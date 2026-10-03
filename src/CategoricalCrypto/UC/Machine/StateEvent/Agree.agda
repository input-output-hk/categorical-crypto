{-# OPTIONS --safe --without-K --guardedness #-}

-- The state-event reading at embedded strategies: the experiment an ordinary
-- strategy embeds to (`UC.Seam.Budget.stratTest`), read against
-- `M ▷ P`, IS the closed run of `M ▷ P` at `flagStrat d`, as `_≈ₚ_`.
--
-- The flag reader over `stratTest B d` and `strategyEnv` at `flagStrat d` are
-- NOT equal machines: once the flag is read, the reader returns to a state
-- whose next tick asks the flag again, while the strategy environment replays
-- its verdict.  So the agreement is proved at the observation, one tick,
-- against `M ▷ P` itself, whose flag port only ever answers with the flag.

open import Categories.Category

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality using (refl)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Run
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Bridge
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Slide
open import CategoricalCrypto.UC.Machine.StateEvent
open import CategoricalCrypto.UC.Machine.StateEvent.Read
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Budget
open import CategoricalCrypto.UC.Machine.Plug

module CategoricalCrypto.UC.Machine.StateEvent.Agree where

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The embedded strategy, below the flag reader

embeds : (B : Iface) (d : Strat (Neg B) (Pos B)) → 𝒫._≈_ (stratTest B d 𝒫.∘ λᴵ⇐) (strategyEnv B d)
embeds B d =
      𝒫.∘-resp-≈ˡ (stratTest-embeds B d)
  S.○ᴹ 𝒫.assoc
  S.○ᴹ 𝒫.∘-resp-≈ʳ (𝒫.∘-resp-≈ʳ (𝒫.Equiv.sym 𝒫.identityʳ) S.○ᴹ unit-cancel 𝒫.id)
  S.○ᴹ 𝒫.identityʳ

-- The closed flagged context at `stratTest`, as the flag reader over the
-- strategy environment.
flag-tower : (B : Iface) (u : Proc unitᴵ (B ⊗ᴵ Ωᴵ)) (d : Strat (Neg B) (Pos B))
      → 𝒫._≈_ ((flagReader B unitᴵ (stratTest B d) 𝒫.∘ T₁ᴵ unitᴵ u) 𝒫.∘ λᴵ⇐ {unitᴵ})
                            (Collapsed.readᴹ B (strategyEnv B d) 𝒫.∘ u)
flag-tower B u d =
     𝒫.assoc
  S.○ᴹ 𝒫.∘-resp-≈ʳ (S.⟺ᴹ (λ-nat u))
  S.○ᴹ 𝒫.sym-assoc
  S.○ᴹ 𝒫.∘-resp-≈ˡ
       ( 𝒫.assoc
    S.○ᴹ 𝒫.∘-resp-≈ʳ ( 𝒫.assoc
                   S.○ᴹ 𝒫.∘-resp-≈ʳ λ-tri
                   S.○ᴹ S.⟺ᴹ (sub-∘ (stratTest B d) λᴵ⇐)
                   S.○ᴹ sub-resp-≈ (embeds B d))
    S.○ᴹ Collapsed.read-collapse B (strategyEnv B d))

------------------------------------------------------------------------
-- One tick of the collapsed composite

module _ {B : Iface} (M : Proc unitᴵ B) (P : StateTest M) (d : Strat (Neg B) (Pos B)) where

  private
    B′ = B ⊗ᴵ Ωᴵ
    u = M ▷ P
    E = strategyEnv B d

  open Collapsed B E
  open Plugged B′ readᴹ u

  private
    SK = FlagSt × EnvSt B
    SU = MC.St M × Bool

    pass : (st : SK × SU) (x : Neg B′ ⊎ Pos B′) → iterₚ body (st , x) ≈ₚ (kᶜ (st , inj₂ x) >>=ₚ contᵢ body)
    pass st x = iterₚ-fix body (st , x) ⟨≈⟩ bindˣ (k-red (st , inj₂ x))

    -- What the environment's emission leads to, once the loop has taken it.
    emit : SU → (FlagSt × EnvSt B) × (Neg B′ ⊎ Bool) → Dₚ Bool
    emit su q = cont ((proj₁ q , su) , outE B′ (proj₂ q))

    -- The flag ask and its answer: two passes, and the answer is the verdict.
    flag-read : (se : EnvSt B) (su : SU)
              → (iterₚ body (((waitF , se) , su) , inj₁ (inj₂ tt)) >>=ₚ verdict)
                ≈ₚ runᴹFrom u su (flagStrat (out false))
    flag-read se (s , f) =
        bindˣ ( pass ((waitF , se) , (s , f)) (inj₁ (inj₂ tt))
            ⟨≈⟩ >>=ₚ-assoc (returnₚ ((s , f) , inj₂ (inj₂ f))) _ (contᵢ body)
            ⟨≈⟩ >>=ₚ-identityˡ ((s , f) , inj₂ (inj₂ f)) _
            ⟨≈⟩ >>=ₚ-identityˡ (((waitF , se) , (s , f)) , inj₂ (inj₂ (inj₂ f))) _
            ⟨≈⟩ pass ((waitF , se) , (s , f)) (inj₂ (inj₂ f))
            ⟨≈⟩ >>=ₚ-assoc (returnₚ ((idle , se) , inj₂ f)) _ (contᵢ body)
            ⟨≈⟩ >>=ₚ-identityˡ ((idle , se) , inj₂ f) _
            ⟨≈⟩ >>=ₚ-identityˡ (((idle , se) , (s , f)) , inj₁ (inj₂ f)) _)
      ⟨≈⟩ >>=ₚ-identityˡ (((idle , se) , (s , f)) , inj₂ f) verdict
      ⟨≈⟩ ≈sym (>>=ₚ-identityˡ ((s , f) , inj₂ (inj₂ f)) _)

  mutual
    -- `Seam.Adequacy.play-run` with the flag reader's post-processing.
    play-run : (su : SU) (e : Strat (Neg B) (Pos B))
             → ((playˢ B e >>=ₚ efOut waitE) >>=ₚ emit su) ≈ₚ runᴹFrom u su (flagStrat e)
    play-run su (out v) =
        >>=ₚ-assoc (returnₚ (play (out v) , inj₂ v)) _ _
      ⟨≈⟩ >>=ₚ-identityˡ (play (out v) , inj₂ v) _
      ⟨≈⟩ >>=ₚ-identityˡ ((waitF , play (out v)) , inj₁ (inj₂ tt)) _
      ⟨≈⟩ flag-read (play (out v)) su
    play-run su (coin μ k) =
        bindˣ (>>=ₚ-assoc (coinₚ μ) (λ c → playˢ B (k c)) _)
      ⟨≈⟩ >>=ₚ-assoc (coinₚ μ) _ _
      ⟨≈⟩ bindᶠ (λ c → play-run su (k c))
    play-run (s , f) (ask q k) =
        >>=ₚ-assoc (returnₚ (susp k , inj₁ q)) _ _
      ⟨≈⟩ >>=ₚ-identityˡ (susp k , inj₁ q) _
      ⟨≈⟩ >>=ₚ-identityˡ ((waitE , susp k) , inj₁ (inj₁ q)) _
      ⟨≈⟩ bindˣ (pass ((waitE , susp k) , (s , f)) (inj₁ (inj₁ q)))
      ⟨≈⟩ bindˣ (>>=ₚ-assoc (MC.step u ((s , f) , inj₂ (inj₁ q))) _ (contᵢ body))
      ⟨≈⟩ >>=ₚ-assoc (MC.step u ((s , f) , inj₂ (inj₁ q))) _ verdict
      ⟨≈⟩ bind-map (MC.step M (s , inj₂ q)) (sample M P f) _
      ⟨≈⟩ bindᶠ (answer k)
      ⟨≈⟩ ≈sym (bind-map (MC.step M (s , inj₂ q)) (sample M P f) _)

    answer : (k : Pos B → Strat (Neg B) (Pos B)) {f : Bool} (r : MC.St M × (⊥ ⊎ Pos B))
           → ((returnₚ ((((waitE , susp k) , proj₁ (sample M P f r))) , outU B′ (proj₂ (sample M P f r)))
               >>=ₚ contᵢ body) >>=ₚ verdict)
             ≈ₚ resumeᴹ u (λ su′ p → runᴹFrom u su′ ([ flagStrat ∘ k , (λ _ → out false) ] p))
                        (sample M P f r)
    answer k (_  , inj₁ ())
    answer k {f} (s′ , inj₂ p) =
        bindˣ (>>=ₚ-identityˡ ((((waitE , susp k) , (s′ , f ∨ P s′))) , inj₂ (inj₂ (inj₁ p))) _)
      ⟨≈⟩ bindˣ (pass ((waitE , susp k) , (s′ , f ∨ P s′)) (inj₂ (inj₁ p)))
      ⟨≈⟩ bindˣ (>>=ₚ-assoc (playˢ B (k p) >>=ₚ efOut waitE) _ (contᵢ body))
      ⟨≈⟩ >>=ₚ-assoc (playˢ B (k p) >>=ₚ efOut waitE) _ verdict
      ⟨≈⟩ bindᶠ (λ q → bindˣ (>>=ₚ-identityˡ ((proj₁ q , (s′ , f ∨ P s′)) , outE B′ (proj₂ q)) (contᵢ body))
                    ⟨≈⟩ cont-red ((proj₁ q , (s′ , f ∨ P s′)) , outE B′ (proj₂ q)))
      ⟨≈⟩ play-run (s′ , f ∨ P s′) (k p)

  flag-adequacy : ⟦ readᴹ 𝒫.∘ u ⟧ᴼ ≈ₚ runᴹ u (flagStrat d)
  flag-adequacy =
      collapse
    ⟨≈⟩ observe
    ⟨≈⟩ bindˣ (point-⊛ (MC.state readᴹ) (MC.state u) ttᵛ
               ⟨≈⟩ bindˣ (point-⊛ (MC.state flagReadᴹ) (MC.state E) ttᵛ
                          ⟨≈⟩ >>=ₚ-identityˡ idle _ ⟨≈⟩ >>=ₚ-identityˡ (play d) _)
               ⟨≈⟩ >>=ₚ-identityˡ (idle , play d) _)
    ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state u) ttᵛ) _ _
    ⟨≈⟩ bindᶠ (λ su → >>=ₚ-identityˡ ((idle , play d) , su) _
                  ⟨≈⟩ bindˣ (k-red (((idle , play d) , su) , inj₁ (inj₂ tt)))
                  ⟨≈⟩ >>=ₚ-assoc (playˢ B d >>=ₚ efOut waitE) _ cont
                  ⟨≈⟩ bindᶠ (λ q → >>=ₚ-identityˡ ((proj₁ q , su) , outE B′ (proj₂ q)) cont)
                  ⟨≈⟩ play-run su d)

------------------------------------------------------------------------
-- Agreement

stateRead-agree : {B : Iface} (M : Proc unitᴵ B) (P : StateTest M) (d : Strat (Neg B) (Pos B))
                → stateRead unitᴵ M P (stratTest B d) (λᴵ⇐ {unitᴵ}) ≈ₚ runᴹ (M ▷ P) (flagStrat d)
stateRead-agree {B} M P d = runᴹ-resp-≈ᴹ (flag-tower B (M ▷ P) d) (ask tt out) ⟨≈⟩ flag-adequacy M P d
