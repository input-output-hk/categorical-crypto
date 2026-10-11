{-# OPTIONS --safe --without-K --guardedness #-}

-- The tester (`Distinguish.Tester`) run against a frame emitter: under every
-- naming the verdict compares the two recipes on the tester's drawn names and
-- the emitter's frame.  The leaves cross the seal by `unprocᵒ-∘`, the loop is
-- `UC.Seam.Plug`'s with one emitter and one tester pass per port, and the
-- passes are an induction on the tester's stage.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Static.Distinguish.Run (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Categories.Category.Monoidal
open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc; fromℕ; inject₁)
open import Data.Fin.Induction using (<-weakInduction)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.Symbolic.Semantics 𝔖 E
open import CategoricalCrypto.Symbolic.Static.Distinguish.Tester 𝔖 E
open import CategoricalCrypto.Symbolic.Static.Emitter 𝔖 E
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.UC.Seam.Plug as Plug

private
  module G = MonoidalCategory 𝔾ᵒ
  module MC = Core (𝒱ₚ 0ℓ)

open Signature 𝔖
open Terms 𝔖
open EqTheory E
open Run E

-- The seal's transports at the two leaves cancel.
private
  tree-∘ : ∀ {X Y Y′ Z} (q : Y ≡ Y′) (g : Y G.⇒ Z) (f : X G.⇒ Y)
         → subst₂ G._⇒_ q refl g G.∘ subst₂ G._⇒_ refl q f ≡ g G.∘ f
  tree-∘ refl _ _ = refl

module _ {Δ Ν : List Sort} (Θ : List Sort) {s₀ : Sort} (ẑ ẑ′ : Rcp (Θ ++ Δ) s₀) (ζs : All (Rcp Ν) Δ) where

  circuit : HomTerm (Var void) (Var verdict)
  circuit = var (ports-free Δ , tt , tester Θ ẑ ẑ′) ∘ Emitter Ν ζs

  -- The verdict of a tester occurrence `κᵀ` against an emitter occurrence `κᵉ`.
  verdictᵀ : ℕ → ℕ → Bool
  verdictᵀ κᵀ κᵉ = does (ẑ ⟨ F ⟩ ≟E ẑ′ ⟨ F ⟩)
    where F = ++⁺ (drawn κᵀ (length Δ + 0) Θ) (frame κᵉ Ν ζs)

  private
    T  = tester Θ ẑ ẑ′
    Em = emitter Ν ζs
    c₀ = length Δ + 0

  module Pass (κᵀ κᵉ : ℕ) where
    K : Proc ⟦ Ports Δ ⟧ᴵ Ωᴵ
    K = runᴿ κᵀ T

    u : Proc unitᴵ ⟦ Ports Δ ⟧ᴵ
    u = runᴿ κᵉ Em

    module P = Plug.Plugged ⟦ Ports Δ ⟧ᴵ K u

    φ : Frame Δ
    φ = frame κᵉ Ν ζs

    Cfgᵀ Cfgᵉ : Set
    Cfgᵀ = Config (suc (length Δ)) (Γᵀ Δ)
    Cfgᵉ = Config 2 (Γᵉ Ν)

    -- A tester step, as the loop carries it on.
    toLoop : Cfgᵉ → Cfgᵀ × Emission (Oᵀ Δ) → MC.obj P.Sᴷ × ((⊥ ⊎ Bool) ⊎ (Alphabet neg (Ports Δ) ⊎ Alphabet pos (Ports Δ)))
    toLoop es X = (proj₁ X , es) , Col.outᵍ (encode (Ports Δ) (Var verdict) (proj₂ X))

    tester-pass : ∀ cfg es (m : Alphabet pos (Ports Δ) ⊎ ⊤) {X} → step κᵀ T cfg (decode (Ports Δ) (Var verdict) m) ≡ X
                → (MC.step K (cfg , m) >>=ₚ λ r → returnₚ ((proj₁ r , es) , Col.outᵍ (proj₂ r))) ≈ₚ returnₚ (toLoop es X)
    tester-pass cfg es m eq = >>=ₚ-identityˡ _ _ ⟨≈⟩ ≡⇒≈ₚ (cong (λ X → returnₚ (toLoop es X)) eq)

    Answers : Cfgᵉ → Set
    Answers es = ∀ {s} (j : s ∈ Δ) q → step κᵉ Em es (port↦ neg j ↦ q) ≡ (ready κᵉ Ν , port↦ pos j ↦ lookup φ j)

    emitter-pass : ∀ cfg es → Answers es → ∀ {s} (j : s ∈ Δ) q
                 → P.kᴷ ((cfg , es) , inj₂ (inj₁ (write neg (Ports Δ) (port↦ neg j) q)))
                 ≈ₚ returnₚ ((cfg , ready κᵉ Ν) , inj₂ (inj₂ (write pos (Ports Δ) (port↦ pos j) (lookup φ j))))
    emitter-pass cfg es ans j q = >>=ₚ-identityˡ _ _ ⟨≈⟩ ≡⇒≈ₚ
      (cong (λ Y → returnₚ ((cfg , proj₁ Y) , Col.outᶠ (encode (Var void) (Ports Δ) (proj₂ Y))))
            (trans (cong (step κᵉ Em es) (decode-query j q)) (ans j q)))

    -- What the closed run makes of the tester at stage `c`.
    Q : Fin (suc (length Δ)) → Set
    Q c = ∀ {Λ} (F : Frame Λ) (ρs : All (Rcp Λ) Δ) es → Answers es → From c (ρs ⟨ F ⟩*) φ
        → P.cont (toLoop es (exec κᵀ (stage Θ ẑ ẑ′ c ρs) F c₀)) ≈ₚ returnₚ (verdictᵀ κᵀ κᵉ)

    finish : Q zero
    finish F ρs es _ a = ≡⇒≈ₚ
      (trans (cong (λ X → P.cont (toLoop es X)) (exec-final Θ ẑ ẑ′ κᵀ ρs F c₀))
      (trans (cong (λ o → P.cont ((config zero [] (length Θ + c₀) , es) , Col.outᵍ o)) (encode-verdict {Δ = Δ} _))
             (cong returnₚ (verdict-≈ Θ ẑ ẑ′ ρs (drawn κᵀ c₀ Θ) F a))))

    descend : ∀ i → Q (inject₁ i) → Q (suc i)
    descend i ih F ρs es ans a =
          ≡⇒≈ₚ (cong (λ o → P.cont ((cfg , es) , Col.outᵍ o)) (encode-query j q))
      ⟨≈⟩ bindˣ ( P.loop-pass (cfg , es) (inj₁ b) (cfg , ready κᵉ Ν) (inj₂ (inj₂ b′)) (emitter-pass cfg es ans j q)
                ⟨≈⟩ P.loop-pass (cfg , ready κᵉ Ν) (inj₂ b′) (proj₁ r) (proj₂ r)
                      (tester-pass cfg (ready κᵉ Ν) (inj₁ b′) answered))
      ⟨≈⟩ P.cont-red r
      ⟨≈⟩ ih (t ∷ R) (refresh j) (ready κᵉ Ν) (later κᵉ Ν ζs)
             (subst (λ R′ → From (inject₁ i) R′ φ) (sym (refresh-⟨⟩ j t R))
                    (From-step {Δ = Δ} i {t = t} {R = R} {φ = φ}
                      (From-canon {Δ = Δ} (suc i) {R = ρs ⟨ F ⟩*} {φ = φ} a) ≈E.refl))
      where
      j  = ∈-lookup {xs = Δ} i
      R  = canon* (ρs ⟨ F ⟩*)
      cfg = config (suc i) R c₀
      q  = canon (lookup ρs j ⟨ F ⟩)
      b  = write neg (Ports Δ) (port↦ neg j) q
      t  = lookup φ j
      b′ = write pos (Ports Δ) (port↦ pos j) t
      X  = exec κᵀ (stage Θ ẑ ẑ′ (inject₁ i) (refresh j)) (t ∷ R) c₀
      r  = toLoop (ready κᵉ Ν) X

      answered : step κᵀ T cfg (decode (Ports Δ) (Var verdict) (inj₁ b′)) ≡ X
      answered = trans (cong (step κᵀ T cfg) (decode-answer j t)) (step-answer Θ ẑ ẑ′ κᵀ i j t R c₀)

    obs : Obs (procᵒ K G.∘ procᵒ u) ≈ₚ returnₚ (verdictᵀ κᵀ κᵉ)
    obs = runᴹ-resp-≈ᴹ {Ωᴵ} (unprocᵒ-∘ {unitᴵ} {⟦ Ports Δ ⟧ᴵ} {Ωᴵ} K u) (ask tt out)
      ⟨≈⟩ P.collapse ⟨≈⟩ P.observe
      ⟨≈⟩ bindˣ (P.point-red ⟨≈⟩ >>=ₚ-identityˡ _ _ ⟨≈⟩ >>=ₚ-identityˡ _ _)
      ⟨≈⟩ >>=ₚ-identityˡ _ _
      ⟨≈⟩ bindˣ (tester-pass (init T) (init Em) (inj₂ tt) (step-tick Θ ẑ ẑ′ κᵀ))
      ⟨≈⟩ >>=ₚ-identityˡ _ _
      ⟨≈⟩ <-weakInduction Q finish descend (fromℕ (length Δ)) _ slots₀ (init Em) (first κᵉ Ν ζs) (From-top _ φ)

  run : (ι : Occ circuit → ℕ) → Obs ⟦ circuit ⟧[ ι ] ≈ₚ returnₚ (verdictᵀ (ι (inj₁ tt)) (ι (inj₂ tt)))
  run ι = ≡⇒≈ₚ (cong Obs (tree-∘ (sym (tree≡ (Ports Δ) (ports-free Δ))) _ _)) ⟨≈⟩ Pass.obs (ι (inj₁ tt)) (ι (inj₂ tt))
