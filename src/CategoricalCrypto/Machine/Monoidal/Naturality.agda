{-# OPTIONS --safe #-}

-- ============================================================================
-- The Kleisli shuffles `∘ᴷ-fwd` and `⊗ᴷ-fwd` are natural.
--
-- Both shuffles are composites of associators and symmetries
-- (`Machine.Monoidal.Coherence`), so each law is an instance of the naturality
-- of the structural isomorphisms, slid across one factor at a time.
--
-- The bookkeeping was once left to the symmetric coherence solver of
-- `Categories.Coherence.Monoidal`, which is shorter.  It is done by hand here
-- because a transfer argument needs to know what these isomorphisms do to
-- STATES, and a solver proof's state map is buried in a decision procedure
-- that is stuck on abstract channels, whereas every step below has a state map
-- that computes — see the `…-to` laws at the foot of this module.
-- ============================================================================

module CategoricalCrypto.Machine.Monoidal.Naturality where

open import categorical-crypto.Prelude hiding (id; _∘_)

open import Categories.Category

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Core
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Monoidal.Coherence
  using (∘ᴷ-fwd-decomp; ⊗ᴷ-fwd-decomp; mid4-decomp; α-isoˡ; α-isoʳ)
open import CategoricalCrypto.Machine.Monoidal.Associator using (⊗-assoc⃖-natural)
open import CategoricalCrypto.Machine.Monoidal.Braiding using (σ-natural)
open import CategoricalCrypto.Machine.Monoidal.Interchange using (⊗₁-interchange; Aᴸ)
open import CategoricalCrypto.Machine.Monoidal.Braiding using (pt-σLᵢ)
open import CategoricalCrypto.Machine.Monoidal.Associator using (nrᵢ)
open import CategoricalCrypto.Machine.Monoidal.Coherence using (∘-collapse)
open import CategoricalCrypto.Machine.Reindex using (πᵢ; ∘κᵢ)
open import CategoricalCrypto.Machine.Reindex.Slide using (cdᵢ)
open import CategoricalCrypto.Machine.Reindex.Collapse using (cod-routeᵢ)
open import CategoricalCrypto.Machine.Reindex.PairAssoc using (asc3ᵢ)
open import CategoricalCrypto.Machine.Reindex.Post using (Pair-Post)
open import CategoricalCrypto.Machine.Forwarder using (Xφ)
open import CategoricalCrypto.Machine.MonoidalCategory

open Category MachineCategory using (module HomReasoning)
open HomReasoning

-- Naturality of the forward associator, conjugated out of the inverse one.
-- Proved here rather than left to the coherence solver because the transfer
-- argument needs to know what these isomorphisms do to STATES, and a solver
-- proof's state map is buried in a decision procedure that is stuck on
-- abstract channels.  Every step below has a computable state map.
⊗-assoc-natural : ∀ {A A' B B' D D'}
                  (a : Machine A A') (b : Machine B B') (d : Machine D D')
                → ((a ⊗₁ (b ⊗₁ d)) CC.∘ ⊗-assoc)
                  ≅ᴹ (⊗-assoc CC.∘ ((a ⊗₁ b) ⊗₁ d))
⊗-assoc-natural a b d =
  ≅ᴹ-trans (≅ᴹ-sym ∘-identityˡ-≅ᴹ)
  (≅ᴹ-trans (∘-resp-≅ᴹ (≅ᴹ-sym α-isoʳ) ≅ᴹ-refl)
  (≅ᴹ-trans ∘-assoc-≅ᴹ
  (∘-resp-≅ᴹ ≅ᴹ-refl
    (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
    (≅ᴹ-trans (∘-resp-≅ᴹ (≅ᴹ-sym (⊗-assoc⃖-natural a b d)) ≅ᴹ-refl)
    (≅ᴹ-trans ∘-assoc-≅ᴹ
    (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl α-isoˡ)
              ∘-identityʳ-≅ᴹ)))))))

∘ᴷ-fwd-natural : ∀ {C C' E₁ E₁' E₂ E₂'}
                 (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
               → ((c ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ∘ᴷ-fwd)
                 ≅ᴹ (∘ᴷ-fwd CC.∘ ((c ⊗₁ u₂) ⊗₁ u₁))
∘ᴷ-fwd-natural c u₁ u₂ =
  ≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl ∘ᴷ-fwd-decomp)
  (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
  (≅ᴹ-trans (∘-resp-≅ᴹ (≅ᴹ-sym (⊗₁-interchange CC.id c ⊗-symₘ (u₁ ⊗₁ u₂))) ≅ᴹ-refl)
  (≅ᴹ-trans (∘-resp-≅ᴹ (⊗₁-resp-≅ᴹ (≅ᴹ-trans ∘-identityʳ-≅ᴹ (≅ᴹ-sym ∘-identityˡ-≅ᴹ))
                                   (≅ᴹ-sym (σ-natural u₂ u₁)))
                       ≅ᴹ-refl)
  (≅ᴹ-trans (∘-resp-≅ᴹ (⊗₁-interchange c CC.id (u₂ ⊗₁ u₁) ⊗-symₘ) ≅ᴹ-refl)
  (≅ᴹ-trans ∘-assoc-≅ᴹ
  (≅ᴹ-trans (∘-resp-≅ᴹ ≅ᴹ-refl (⊗-assoc-natural c u₂ u₁))
  (≅ᴹ-trans (≅ᴹ-sym ∘-assoc-≅ᴹ)
            (∘-resp-≅ᴹ (≅ᴹ-sym ∘ᴷ-fwd-decomp) ≅ᴹ-refl))))))))

⊗ᴷ-fwd-natural : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
                 (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
                 (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
               → (((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd)
                 ≅ᴹ (⊗ᴷ-fwd CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂)))
⊗ᴷ-fwd-natural {B₁} {B₁'} {E₁} {E₁'} {B₂} {B₂'} {E₂} {E₂'} b₁ u₁ b₂ u₂ = begin
    ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗ᴷ-fwd
  ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-trans ⊗ᴷ-fwd-decomp mid4-decomp) ⟩
    ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ mid4-core
  ≈⟨ mid4-nat ⟩
    mid4-core CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
  ≈⟨ ∘-resp-≅ᴹ (≅ᴹ-sym (≅ᴹ-trans ⊗ᴷ-fwd-decomp mid4-decomp)) ≅ᴹ-refl ⟩
    ⊗ᴷ-fwd CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
  ∎
  where
  -- The inner shuffle of `mid4-core`, and the whole of it.
  Y : ∀ {Q R S} → Machine (Q ⊗₀ (R ⊗₀ S)) (R ⊗₀ (Q ⊗₀ S))
  Y = ⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖)

  mid4-core : ∀ {P Q R S} → Machine ((P ⊗₀ Q) ⊗₀ (R ⊗₀ S)) ((P ⊗₀ R) ⊗₀ (Q ⊗₀ S))
  mid4-core = ⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ Y) CC.∘ ⊗-assoc)

  -- Naturality of the inner shuffle: `α⇒`, then `σ` on the left pair, then
  -- `α⇐`, each carrying the machines across by its own naturality law.
  Y-nat : ((b₂ ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ Y) ≅ᴹ (Y CC.∘ (u₁ ⊗₁ (b₂ ⊗₁ u₂)))
  Y-nat = begin
      (b₂ ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ (⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖))
    ≈⟨ ≅ᴹ-sym ∘-assoc-≅ᴹ ⟩
      ((b₂ ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗-assoc) CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖)
    ≈⟨ ∘-resp-≅ᴹ (⊗-assoc-natural b₂ u₁ u₂) ≅ᴹ-refl ⟩
      (⊗-assoc CC.∘ ((b₂ ⊗₁ u₁) ⊗₁ u₂)) CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖)
    ≈⟨ ∘-assoc-≅ᴹ ⟩
      ⊗-assoc CC.∘ (((b₂ ⊗₁ u₁) ⊗₁ u₂) CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖))
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-assoc-≅ᴹ) ⟩
      ⊗-assoc CC.∘ ((((b₂ ⊗₁ u₁) ⊗₁ u₂) CC.∘ (⊗-symₘ ⊗₁ CC.id)) CC.∘ ⊗-assoc⃖)
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (∘-resp-≅ᴹ σ-block ≅ᴹ-refl) ⟩
      ⊗-assoc CC.∘ (((⊗-symₘ ⊗₁ CC.id) CC.∘ ((u₁ ⊗₁ b₂) ⊗₁ u₂)) CC.∘ ⊗-assoc⃖)
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl ∘-assoc-≅ᴹ ⟩
      ⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ (((u₁ ⊗₁ b₂) ⊗₁ u₂) CC.∘ ⊗-assoc⃖))
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (∘-resp-≅ᴹ ≅ᴹ-refl (⊗-assoc⃖-natural u₁ b₂ u₂)) ⟩
      ⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ (⊗-assoc⃖ CC.∘ (u₁ ⊗₁ (b₂ ⊗₁ u₂))))
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-assoc-≅ᴹ) ⟩
      ⊗-assoc CC.∘ (((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖) CC.∘ (u₁ ⊗₁ (b₂ ⊗₁ u₂)))
    ≈⟨ ≅ᴹ-sym ∘-assoc-≅ᴹ ⟩
      (⊗-assoc CC.∘ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ⊗-assoc⃖)) CC.∘ (u₁ ⊗₁ (b₂ ⊗₁ u₂))
    ∎
    where
    -- `σ ⊗₁ id` carries the pair across: interchange, `σ-natural`, interchange.
    σ-block : (((b₂ ⊗₁ u₁) ⊗₁ u₂) CC.∘ (⊗-symₘ ⊗₁ CC.id))
            ≅ᴹ ((⊗-symₘ ⊗₁ CC.id) CC.∘ ((u₁ ⊗₁ b₂) ⊗₁ u₂))
    σ-block =
      ≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange ⊗-symₘ (b₂ ⊗₁ u₁) CC.id u₂))
      (≅ᴹ-trans (⊗₁-resp-≅ᴹ (≅ᴹ-sym (σ-natural u₁ b₂))
                            (≅ᴹ-trans ∘-identityʳ-≅ᴹ (≅ᴹ-sym ∘-identityˡ-≅ᴹ)))
                (⊗₁-interchange (u₁ ⊗₁ b₂) ⊗-symₘ u₂ CC.id))

  -- `id ⊗₁ Y` carries the outer machine across, by interchange on both sides.
  X-nat : ((b₁ ⊗₁ (b₂ ⊗₁ (u₁ ⊗₁ u₂))) CC.∘ (CC.id ⊗₁ Y))
        ≅ᴹ ((CC.id ⊗₁ Y) CC.∘ (b₁ ⊗₁ (u₁ ⊗₁ (b₂ ⊗₁ u₂))))
  X-nat =
    ≅ᴹ-trans (≅ᴹ-sym (⊗₁-interchange CC.id b₁ Y (b₂ ⊗₁ (u₁ ⊗₁ u₂))))
    (≅ᴹ-trans (⊗₁-resp-≅ᴹ (≅ᴹ-trans ∘-identityʳ-≅ᴹ (≅ᴹ-sym ∘-identityˡ-≅ᴹ)) Y-nat)
              (⊗₁-interchange b₁ CC.id (u₁ ⊗₁ (b₂ ⊗₁ u₂)) Y))

  mid4-nat : (((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ mid4-core)
           ≅ᴹ (mid4-core CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂)))
  mid4-nat = begin
      ((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ (⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ Y) CC.∘ ⊗-assoc))
    ≈⟨ ≅ᴹ-sym ∘-assoc-≅ᴹ ⟩
      (((b₁ ⊗₁ b₂) ⊗₁ (u₁ ⊗₁ u₂)) CC.∘ ⊗-assoc⃖) CC.∘ ((CC.id ⊗₁ Y) CC.∘ ⊗-assoc)
    ≈⟨ ∘-resp-≅ᴹ (⊗-assoc⃖-natural b₁ b₂ (u₁ ⊗₁ u₂)) ≅ᴹ-refl ⟩
      (⊗-assoc⃖ CC.∘ (b₁ ⊗₁ (b₂ ⊗₁ (u₁ ⊗₁ u₂)))) CC.∘ ((CC.id ⊗₁ Y) CC.∘ ⊗-assoc)
    ≈⟨ ∘-assoc-≅ᴹ ⟩
      ⊗-assoc⃖ CC.∘ ((b₁ ⊗₁ (b₂ ⊗₁ (u₁ ⊗₁ u₂))) CC.∘ ((CC.id ⊗₁ Y) CC.∘ ⊗-assoc))
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-assoc-≅ᴹ) ⟩
      ⊗-assoc⃖ CC.∘ (((b₁ ⊗₁ (b₂ ⊗₁ (u₁ ⊗₁ u₂))) CC.∘ (CC.id ⊗₁ Y)) CC.∘ ⊗-assoc)
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (∘-resp-≅ᴹ X-nat ≅ᴹ-refl) ⟩
      ⊗-assoc⃖ CC.∘ (((CC.id ⊗₁ Y) CC.∘ (b₁ ⊗₁ (u₁ ⊗₁ (b₂ ⊗₁ u₂)))) CC.∘ ⊗-assoc)
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl ∘-assoc-≅ᴹ ⟩
      ⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ Y) CC.∘ ((b₁ ⊗₁ (u₁ ⊗₁ (b₂ ⊗₁ u₂))) CC.∘ ⊗-assoc))
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (∘-resp-≅ᴹ ≅ᴹ-refl (⊗-assoc-natural b₁ u₁ (b₂ ⊗₁ u₂))) ⟩
      ⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ Y) CC.∘ (⊗-assoc CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))))
    ≈⟨ ∘-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-assoc-≅ᴹ) ⟩
      ⊗-assoc⃖ CC.∘ (((CC.id ⊗₁ Y) CC.∘ ⊗-assoc) CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂)))
    ≈⟨ ≅ᴹ-sym ∘-assoc-≅ᴹ ⟩
      (⊗-assoc⃖ CC.∘ ((CC.id ⊗₁ Y) CC.∘ ⊗-assoc)) CC.∘ ((b₁ ⊗₁ u₁) ⊗₁ (b₂ ⊗₁ u₂))
    ∎

-- PROBE: the state map of the hand-derived naturality.
opaque
  unfolding destruct-⊗ πᵢ ∘κᵢ cdᵢ Xφ asc3ᵢ cod-routeᵢ Pair-Post
            Aᴸ pt-σLᵢ nrᵢ ∘-collapse

  ∘ᴷ-fwd-natural-to : ∀ {C C' E₁ E₁' E₂ E₂'}
                      (c : Machine C C') (u₁ : Machine E₁ E₁') (u₂ : Machine E₂ E₂')
                    → ∀ sc su₁ su₂
                    → _≅ᴹ_.to (∘ᴷ-fwd-natural c u₁ u₂) (tt , (sc , (su₁ , su₂)))
                      ≡ (((sc , su₂) , su₁) , tt)
  ∘ᴷ-fwd-natural-to c u₁ u₂ sc su₁ su₂ = refl

  ⊗ᴷ-fwd-natural-to : ∀ {B₁ B₁' E₁ E₁' B₂ B₂' E₂ E₂'}
                      (b₁ : Machine B₁ B₁') (u₁ : Machine E₁ E₁')
                      (b₂ : Machine B₂ B₂') (u₂ : Machine E₂ E₂')
                    → ∀ sb₁ su₁ sb₂ su₂
                    → _≅ᴹ_.to (⊗ᴷ-fwd-natural b₁ u₁ b₂ u₂)
                        (tt , ((sb₁ , sb₂) , (su₁ , su₂)))
                      ≡ (((sb₁ , su₁) , (sb₂ , su₂)) , tt)
  ⊗ᴷ-fwd-natural-to b₁ u₁ b₂ u₂ sb₁ su₁ sb₂ su₂ = refl
