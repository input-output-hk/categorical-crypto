{-# OPTIONS --safe #-}

-- ============================================================================
-- The length-leaking secure channel realizes the message-leaking channel:
--
--     SecureChannel  ≅ᴹ  ((A ⊗₀ B) ⊗ˡ Sim) ∘ LeakyChannel
--
-- The ideal specification is the permissive one, so what this says is that
-- leakage may always be added and the simulator discards what it is given.
-- The converse non-realization is not proved.
--
-- The right-hand side traces out the shared channel, so its steps are two-hop
-- chains.  `Reindex.Post` turns post-composition with a forwarder into a
-- relabelling `Post` of the inner machine (`Xfwd-∘-Post`), after which the two
-- functionalities are compared constructor by constructor with the identity on
-- their common state `List M`.  `msgLength` is not injective, so `Reindex`,
-- which relabels contravariantly, would not do; that is what `Post` is for.
-- ============================================================================

open import CategoricalCrypto.Machine.Reindex
open import CategoricalCrypto.Machine.Reindex.Slide
open import CategoricalCrypto.Machine.Reindex.Post
open import CategoricalCrypto.Machine.Forwarder
open import CategoricalCrypto.Examples.Basic

open import categorical-crypto.Prelude hiding (id; _∘_)
open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Channel.Selection
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Message
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import Tactic.Defaults

module CategoricalCrypto.Examples.Channels (M : Type) (msgLength : M → ℕ) where

module L = LeakyChannel M
module S = SecureChannel M msgLength

open Channel

-- The two functionalities share `A` and `B`; only Eve's port differs.
AB : Channel
AB = L.A ⊗₀ L.B

Cᴸ Cˢ : Channel
Cᴸ = AB ⊗₀ L.E
Cˢ = AB ⊗₀ S.E

-- The simulator: a forwarder on Eve's port.

-- A leaked message becomes its length; a request passes through.
Simᵢ : L.E [ In ]⇒[ In ] S.E
Simᵢ = mk⇒ msgLength

Simₒ : S.E [ Out ]⇒[ Out ] L.E
Simₒ = mk⇒ (λ x → x)

Sim : Machine L.E S.E
Sim = TotalFunctionMachine' Simᵢ Simₒ

-- The right-hand side as a relabelling of the leaky functionality.

opaque
  unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
            ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
            πᵢ ∘κᵢ cdᵢ Xφ cdₒ⁺

  -- The message maps of `AB ⊗ˡ Sim`, as a single crossing forwarder.
  simᶠ : inType Cᴸ → inType Cˢ
  simᶠ = ⊗mapᵢ {AB} {AB} {L.E} {S.E} (λ x → x) msgLength

  simᵍ : outType Cˢ → outType Cᴸ
  simᵍ = ⊗mapₒ {AB} {AB} {L.E} {S.E} (λ x → x) (λ x → x)

  Sim-Xfwd : (AB ⊗ˡ Sim) ≅ᴹ Xfwd simᶠ simᵍ
  Sim-Xfwd = ≅ᴹ-trans (⊗₁-resp-≅ᴹ id-is-Xfwd (tfm'-is-Xfwd Simᵢ Simₒ)) ⊗₁-Xfwd

  -- The relabelling the simulator induces on the functionality's ports.
  uˢ : inType (I ⊗ᵀ Cˢ) → inType (I ⊗ᵀ Cᴸ)
  uˢ = cdᵢ {I} {Cᴸ} {Cˢ} simᵍ

  wˢ : outType (I ⊗ᵀ Cᴸ) → outType (I ⊗ᵀ Cˢ)
  wˢ = cdₒ⁺ {I} {Cᴸ} {Cˢ} simᶠ

  rhs-Post : ((AB ⊗ˡ Sim) CC.∘ L.Functionality) ≅ᴹ Post L.Functionality uˢ wˢ
  rhs-Post = ≅ᴹ-trans (∘-resp-≅ᴹ Sim-Xfwd ≅ᴹ-refl) (Xfwd-∘-Post L.Functionality simᶠ simᵍ)

  -- The state isomorphism proper: `Send` matches `Send`, `Req` matches `Req`.

  -- Forward: a secure step is a leaky step with its leak relabelled.  The
  -- `Selection` indices reduce to `inj` nests here, so the leaky constructor
  -- fits the relabelled indices definitionally.
  secure→leaky : ∀ {s i o s'} → S.WithState s receive i return o newState s'
               → Machine.stepRel (Post L.Functionality uˢ wˢ) s i o s'
  secure→leaky (S.Send {m} {s}) = _ , L.Send {m} {s} , refl
  secure→leaky (S.Req {m} {s})  = _ , L.Req {m} {s} , refl

  -- Backward, at general indices tied by equations: matching the leaky
  -- constructor under `uˢ` directly leaves the unifier stuck.
  leaky→secure : ∀ {s s' i₀ o₀} → L.WithState s receive i₀ return o₀ newState s'
               → (i : inType (I ⊗ᵀ Cˢ)) (o : Maybe (outType (I ⊗ᵀ Cˢ)))
               → i₀ ≡ uˢ i → mapᴹ wˢ o₀ ≡ o
               → S.WithState s receive i return o newState s'
  leaky→secure (L.Send {m} {s}) (inj₂ (inj₁ (inj₁ m'))) o ieq oeq =
    subst₂ (λ x y → S.WithState s receive inj₂ (inj₁ (inj₁ x)) return y newState (s ∷ʳ m))
           (inj₁-inj (inj₁-inj (inj₂-inj ieq))) oeq (S.Send {m} {s})
  leaky→secure (L.Send {m} {s}) (inj₂ (inj₂ _)) o ieq oeq = inj₁≢inj₂ (inj₂-inj ieq)
  leaky→secure (L.Req {m} {s}) (inj₂ (inj₂ _)) o ieq oeq =
    subst (λ y → S.WithState (m ∷ s) receive inj₂ (inj₂ tt) return y newState s)
          oeq (S.Req {m} {s})
  leaky→secure (L.Req {m} {s}) (inj₂ (inj₁ (inj₁ _))) o ieq oeq = inj₁≢inj₂ (sym (inj₂-inj ieq))

  secure≅Post : S.Functionality ≅ᴹ Post L.Functionality uˢ wˢ
  secure≅Post = MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl)
    secure→leaky
    (λ {_} {i} {o} (o₀ , x , e) → leaky→secure x i o refl e)

  secure≅sim∘leaky : S.Functionality ≅ᴹ ((AB ⊗ˡ Sim) CC.∘ L.Functionality)
  secure≅sim∘leaky = ≅ᴹ-trans secure≅Post (≅ᴹ-sym rhs-Post)

-- The UC statement.  `Machine.UC` instantiates the abstract layer at
-- machines, so a state isomorphism is an equality of the category; `≈C⇒≈ᵁ`
-- feeds it to the dummy-adversary theorem, giving that the secure channel
-- realizes the leaky one with `Sim` as the simulator.

import CategoricalCrypto.Machine.UC as UC

secure≤UC-leaky : S.Functionality UC.≤UC L.Functionality
secure≤UC-leaky = UC.dummy-complete (Sim , UC.≈C⇒≈ᵁ secure≅sim∘leaky)
