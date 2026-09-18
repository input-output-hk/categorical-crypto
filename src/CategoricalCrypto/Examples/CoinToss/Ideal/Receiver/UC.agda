{-# OPTIONS --safe --without-K --guardedness #-}

-- The corrupted-receiver hop at the UC model: the joint simulator's query
-- certificate, and the two sides of `Receiver.Machine.coin-runʰ` read as
-- graded homs.
--
-- `Examples.CoinToss.Ideal.UC` is the corrupted-committer twin, and the three
-- coercions are its: `ext-graded` for the stage on top, `graded₂-∘` for the
-- resource plugged under, `sub-graded₂` for the joint simulator in front.
-- What is new is a FOURTH reading of the same two machines — at the grade
-- `ifaceᵒ (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)` rather than `ifaceᵒ Lkᴵʰ ⊗₀ ifaceᵒ Advᴵᶜʰ` — and
-- the identity that regrades one to the other.  The seal hides the tensor
-- (`UC.Model.Seal`'s third discipline), so the two spellings are two
-- coercions and not one, and `sub-graded₂` at the IDENTITY process is the
-- morphism between them.  That is what lets the domination, which is stated
-- at a grade of the first shape (`UC.Model.Dominated.dominatedᵍ`), be read at
-- the second, which is the shape `UC.Asymptotic.Compose._∙ᶠ_` produces.

open import Data.Bool.Base using (_xor_)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; s≤s; z≤n)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (case_of_; _∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒢ₚ; 𝒢ₚᴹ)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Graded using (ext-graded; graded₂-∘; sub-graded₂)
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; T₁ᴵ; a⇒ᴵ)
open import CategoricalCrypto.UC.Machine.Dictionary using (sub-⊗₁)
open import CategoricalCrypto.UC.Model.Dominated using (qb-gradedᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Graded using (graded₂ᵒ; ≈ᴹ⇒≈ᵍ₂)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound
  using (Ans; Certified; certified⇒QB; forget; qb-idᴹ)

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss.Hiding k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Hybrid k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Machine k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Hiding k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Budget budgetᵒ using (QB)
open HomReasoning

private
  module M = Category (𝒢ₚ 0ℓ)
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The joint simulator spends one call per activation

-- Only `shareᴬʰ` buys a `Lkᴵᶜʰ` message; a hash query is answered from the
-- simulator's own table and the coin's two answers only return, so nothing is
-- owed afterwards and the potential stays at zero.  This is
-- `Examples.CoinToss.Ideal.UC.simJCert`'s shape, at the other corruption.
simJʰCert : Certified 1 simJʰ
simJʰCert = record
  { Φ      = λ _ → 0
  ; pointᵍ = returnₚ (preʲʰ [] , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (preʲʰ [] , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  Aᵍ : ℕ → Set
  Aᵍ = Ans {JStʰ} (λ _ → 0) (Neg Lkᴵᶜʰ) (Pos (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ))

  hashG : Tbl → (Tbl → JStʰ) → Pt → Dₚ (Aᵍ 1)
  hashG t φ x = case lookupPt t x of λ where
    (just d) → returnₚ (inj₂ ((φ t , z≤n) , inj₁ (digᶠ d)))
    nothing  → uniformₚ k >>=ₚ λ h →
                 returnₚ (inj₂ ((φ ((x , h) ∷ t) , z≤n) , inj₁ (digᶠ h)))

  -- The lookup is scrutinized by both sides at once, so it is `rewrite`n once.
  cohHash : (t : Tbl) (φ : Tbl → JStʰ) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
          → mapₚ forget (hashG t φ x) ≈ₚ hashJʰ t φ x
  cohHash t φ x (just d) eq rewrite eq = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohHash t φ x nothing  eq rewrite eq =
    map-bind (uniformₚ k) _ forget ⟨≈⟩ bindᶠ λ _ → >>=ₚ-identityˡ _ (returnₚ ∘′ forget)

  onL : (s : JStʰ) (a : Pos Lkᴵᶜʰ) → Dₚ (Aᵍ 0)
  onL (preʲʰ t)    startᵏʰ    = returnₚ (inj₂ ((midʲʰ t , z≤n) , inj₁ rcptᶠ))
  onL (preʲʰ _)    (coinᵏʰ _) = botₚ
  onL (midʲʰ _)    startᵏʰ    = botₚ
  onL (midʲʰ _)    (coinᵏʰ _) = botₚ
  onL (askʲʰ _ _)  startᵏʰ    = botₚ
  onL (askʲʰ t b₂) (coinᵏʰ c) =
    returnₚ (inj₂ ((endʲʰ t , z≤n) , inj₁ (bitᶠ (c xor b₂))))
  onL (endʲʰ _)    startᵏʰ    = botₚ
  onL (endʲʰ _)    (coinᵏʰ _) = botₚ

  onR : (s : JStʰ) (b : Neg (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ)) → Dₚ (Aᵍ 1)
  onR s (inj₁ (relayᶠ x))   = case s of λ where
    (preʲʰ t)    → hashG t preʲʰ x
    (midʲʰ t)    → hashG t midʲʰ x
    (askʲʰ t b₂) → hashG t (λ u → askʲʰ u b₂) x
    (endʲʰ t)    → hashG t endʲʰ x
  onR s (inj₂ (shareᴬʰ b₂)) = case s of λ where
    (midʲʰ t) → returnₚ (inj₁ ((askʲʰ t b₂ , s≤s z≤n) , sampleᵏʰ))
    _         → botₚ

  cohL : (s : JStʰ) (a : Pos Lkᴵᶜʰ) → mapₚ forget (onL s a) ≈ₚ jStepʰ (s , inj₁ a)
  cohL (preʲʰ _)   startᵏʰ    = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (preʲʰ _)   (coinᵏʰ _) = bot-bind-≈ₚ _
  cohL (midʲʰ _)   startᵏʰ    = bot-bind-≈ₚ _
  cohL (midʲʰ _)   (coinᵏʰ _) = bot-bind-≈ₚ _
  cohL (askʲʰ _ _) startᵏʰ    = bot-bind-≈ₚ _
  cohL (askʲʰ _ _) (coinᵏʰ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (endʲʰ _)   startᵏʰ    = bot-bind-≈ₚ _
  cohL (endʲʰ _)   (coinᵏʰ _) = bot-bind-≈ₚ _

  cohR : (s : JStʰ) (b : Neg (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ))
       → mapₚ forget (onR s b) ≈ₚ jStepʰ (s , inj₂ b)
  cohR (preʲʰ t)    (inj₁ (relayᶠ x))   = cohHash t preʲʰ x _ refl
  cohR (midʲʰ t)    (inj₁ (relayᶠ x))   = cohHash t midʲʰ x _ refl
  cohR (askʲʰ t b₂) (inj₁ (relayᶠ x))   = cohHash t (λ u → askʲʰ u b₂) x _ refl
  cohR (endʲʰ t)    (inj₁ (relayᶠ x))   = cohHash t endʲʰ x _ refl
  cohR (preʲʰ _)    (inj₂ (shareᴬʰ _))  = bot-bind-≈ₚ _
  cohR (midʲʰ _)    (inj₂ (shareᴬʰ _))  = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (askʲʰ _ _)  (inj₂ (shareᴬʰ _))  = bot-bind-≈ₚ _
  cohR (endʲʰ _)    (inj₂ (shareᴬʰ _))  = bot-bind-≈ₚ _

simJʰQB : QB 1 (gradedᵒ simJʰ)
simJʰQB = qb-gradedᵒ (certified⇒QB simJʰCert)

-- The regrading wire is the identity process, read at the split grade.
flatʰ : ifaceᵒ (Lkᴵʰ ⊗ᴵ Advᴵᶜʰ) ⇒ ifaceᵒ Lkᴵʰ ⊗₀ ifaceᵒ Advᴵᶜʰ
flatʰ = gradedᵒ (𝒫.id {Lkᴵʰ ⊗ᴵ Advᴵᶜʰ})

flatʰQB : QB 1 flatʰ
flatʰQB = qb-gradedᵒ qb-idᴹ

------------------------------------------------------------------------
-- The two sides, regraded

-- `sub-graded₂` at the IDENTITY simulator: the grade `ifaceᵒ (X ⊗ᴵ P)` the
-- seal hands a `gradedᵒ` and the grade `ifaceᵒ X ⊗₀ ifaceᵒ P` a composed
-- system carries are the same object, and this is the morphism that says so.
regrade : {C : Iface} (g : Proc unitᴵ ((Lkᴵʰ ⊗ᴵ Advᴵᶜʰ) ⊗ᴵ C))
        → sub flatʰ ∘ gradedᵒ g ≈ graded₂ᵒ g
regrade g =
       sub-graded₂ (𝒫.id {Lkᴵʰ ⊗ᴵ Advᴵᶜʰ}) g
  ○ ≈ᴹ⇒≈ᵍ₂ (𝒫.Equiv.trans
              (𝒫.∘-resp-≈ˡ (𝒫.Equiv.trans (sub-⊗₁ (𝒫.id {Lkᴵʰ ⊗ᴵ Advᴵᶜʰ})) 𝔾.⊗.identity))
              𝒫.identityˡ)

-- …and the hybrid's own reading, which is `Examples.CoinToss.Ideal.UC`'s
-- `coin-hop` split at the machine both sides are compared through.
hyb-flatʰ : sub flatʰ ∘ gradedᵒ hybridᴹʰ
            ≈ (ext (ifaceᵒ Lkᴵʰ) (gradedᵒ tossʰ) ∘ gradedᵒ idealʰ) ∘ procᵒ resource
hyb-flatʰ =
       regrade hybridᴹʰ
  ○ Equiv.sym ( ∘-resp-≈ˡ (ext-graded tossʰ idealʰ)
              ○ graded₂-∘ (M._∘_ a⇒ᴵ (M._∘_ (T₁ᴵ Lkᴵʰ tossʰ) idealʰ)) resource )

idl-flatʰ : sub flatʰ ∘ gradedᵒ idealᴹʰ ≈ sub (gradedᵒ simJʰ) ∘ gradedᵒ Fcoinʰ
idl-flatʰ = regrade idealᴹʰ ○ Equiv.sym (sub-graded₂ simJʰ Fcoinʰ)
