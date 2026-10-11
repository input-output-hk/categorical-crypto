{-# OPTIONS --safe --without-K --guardedness #-}

-- Static equivalence implies the kernel equality of `Sym` on frame emitters.
-- The converse is proved for Σ₀/E₀ in `Static.PairEnc`; it is false in general
-- (docs/uc-setup-symbolic.md §3.7). The same-recipe apex relates entry `j` to
-- entry `j`, and `Static.Relational.relsim⇒≈ℰ` carries it through every test.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Static (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂; map₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function.Construct.Identity using (↔-id)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Pointwise using (module MC)
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise
open import CategoricalCrypto.Symbolic.Deduction 𝔖 E
open import CategoricalCrypto.Symbolic.Fine 𝔖 using (Var)
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.Symbolic.Semantics 𝔖 E using (runᴿ)
open import CategoricalCrypto.Symbolic.Setup 𝔖 E using (module Sym)
open import CategoricalCrypto.Symbolic.Static.Emitter 𝔖 E
open import CategoricalCrypto.Symbolic.Static.Relational 𝔖 E
open import CategoricalCrypto.Symbolic.Static.Same 𝔖 E
open import CategoricalCrypto.UC.Machine using (Proc; initˢ)

open Signature 𝔖
open Terms 𝔖
open EqTheory E
open Run E

private variable
  s  : Sort
  Δ′ : List Sort

------------------------------------------------------------------------
-- The apex of two emitters at one occurrence

module _ {Δ Ν : List Sort} (ζs ζs′ : All (Rcp Ν) Δ) (κ : ℕ) where

  private
    φ = frame κ Ν ζs
    ψ = frame κ Ν ζs′

  open Apex φ ψ

  -- An apex letter on entry `j`'s port.
  portᵃ : (d : Dir) → s ∈ Δ′ → Pair φ ψ s → Alphabetᵃ φ ψ d (Ports Δ′)
  portᵃ pos (here refl) q = inj₁ q
  portᵃ pos (there j)   q = inj₂ (portᵃ pos j q)
  portᵃ neg (here refl) q = inj₁ q
  portᵃ neg (there j)   q = inj₂ (portᵃ neg j q)

  Π-portᵃ : (w : Side) (d : Dir) (j : s ∈ Δ′) (q : Pair φ ψ s)
          → Π φ ψ w d (Ports Δ′) (portᵃ d j q) ≡ portᵐ d j (pick w (Pair.fst q) (Pair.snd q))
  Π-portᵃ w pos (here refl) q = refl
  Π-portᵃ w pos (there j)   q = cong inj₂ (Π-portᵃ w pos j q)
  Π-portᵃ w neg (here refl) q = refl
  Π-portᵃ w neg (there j)   q = cong inj₂ (Π-portᵃ w neg j q)

  data OnPortᵃ (Δ′ : List Sort) : Alphabetᵃ φ ψ neg (Ports Δ′) → Set where
    onportᵃ : (j : s ∈ Δ′) (q : Pair φ ψ s) → OnPortᵃ Δ′ (portᵃ neg j q)

  onportᵃ? : (Δ′ : List Sort) (a : Alphabetᵃ φ ψ neg (Ports Δ′)) → OnPortᵃ Δ′ a
  onportᵃ? (_ ∷ _)  (inj₁ q) = onportᵃ (here refl) q
  onportᵃ? (_ ∷ Δ′) (inj₂ a) with onportᵃ? Δ′ a
  ... | onportᵃ j q = onportᵃ (there j) q
  onportᵃ? []       ()

  answer : (∀ {s} → s ∈ Δ′ → Pair φ ψ s) → Alphabetᵃ φ ψ neg (Ports Δ′) → Alphabetᵃ φ ψ pos (Ports Δ′)
  answer {_ ∷ _} e (inj₁ _) = inj₁ (e (here refl))
  answer {_ ∷ _} e (inj₂ a) = inj₂ (answer (λ j → e (there j)) a)
  answer {[]}    e ()

  answer-port : (e : ∀ {s} → s ∈ Δ′ → Pair φ ψ s) (j : s ∈ Δ′) (q : Pair φ ψ s)
              → answer e (portᵃ neg j q) ≡ portᵃ pos j (e j)
  answer-port e (here refl) q = refl
  answer-port e (there j)   q = cong inj₂ (answer-port (λ j′ → e (there j′)) j q)

  -- Entry `j` of either frame is the recipe `var j`.
  entryᵃ : s ∈ Δ → Pair φ ψ s
  entryᵃ j = pair (lookup φ j) (lookup ψ j) (same (var j) ≈E.refl ≈E.refl)

  emitterᵃ : Proc ⟦ Var void ⟧ᴵᵃ ⟦ Ports Δ ⟧ᴵᵃ
  emitterᵃ = MC.mk (initˢ Bool false) λ where
    (_ , inj₂ a) → returnₚ (true , inj₂ (answer entryᵃ a))

  private
    ζw : Side → All (Rcp Ν) Δ
    ζw w = pick w ζs ζs′

    leg : Bool → Config 2 (Γᵉ Ν)
    leg false = init (emitter Ν ζs)
    leg true  = ready κ Ν

    answers : (w : Side) (b : Bool) (j : s ∈ Δ) (t : Tm s)
            → step κ (emitter Ν (ζw w)) (leg b) (port↦ neg j ↦ t)
            ≡ (ready κ Ν , port↦ pos j ↦ lookup (frame κ Ν (ζw w)) j)
    answers w false = first κ Ν (ζw w)
    answers w true  = later κ Ν (ζw w)

    entryᵃ-pick : (w : Side) (j : s ∈ Δ) → pick w (lookup φ j) (lookup ψ j) ≡ lookup (frame κ Ν (ζw w)) j
    entryᵃ-pick l _ = refl
    entryᵃ-pick r _ = refl

    decode-port : (j : s ∈ Δ) (t : Tm s) → decode (Var void) (Ports Δ) (inj₂ (portᵐ neg j t)) ≡ port↦ neg j ↦ t
    decode-port j t = cong (λ x → _↦_ {x = Var void} {y = Ports Δ} (proj₁ (proj₂ x)) (proj₂ (proj₂ x)))
                           (read-port neg j t)

    law : (w : Side) (b : Bool) (j : s ∈ Δ) (q : Pair φ ψ s)
        → (ready κ Ν , inj₂ (Π φ ψ w pos (Ports Δ) (answer entryᵃ (portᵃ neg j q))))
        ≡ map₂ (encode (Var void) (Ports Δ))
            (step κ (emitter Ν (ζw w)) (leg b) (decode (Var void) (Ports Δ) (inj₂ (Π φ ψ w neg (Ports Δ) (portᵃ neg j q)))))
    law w b j q = begin
        (ready κ Ν , inj₂ (Π φ ψ w pos (Ports Δ) (answer entryᵃ (portᵃ neg j q))))
      ≡⟨ cong (λ a → ready κ Ν , inj₂ (Π φ ψ w pos (Ports Δ) a)) (answer-port entryᵃ j q) ⟩
        (ready κ Ν , inj₂ (Π φ ψ w pos (Ports Δ) (portᵃ pos j (entryᵃ j))))
      ≡⟨ cong (λ a → ready κ Ν , inj₂ a) (trans (Π-portᵃ w pos j (entryᵃ j)) (cong (portᵐ pos j) (entryᵃ-pick w j))) ⟩
        (ready κ Ν , inj₂ (portᵐ pos j (lookup (frame κ Ν (ζw w)) j)))
      ≡⟨ cong (λ a → ready κ Ν , inj₂ a) (sym (write-port pos j _)) ⟩
        map₂ (encode (Var void) (Ports Δ)) (ready κ Ν , port↦ pos j ↦ lookup (frame κ Ν (ζw w)) j)
      ≡⟨ cong (map₂ (encode (Var void) (Ports Δ))) (sym (answers w b j _)) ⟩
        map₂ (encode (Var void) (Ports Δ)) (step κ (emitter Ν (ζw w)) (leg b) (port↦ neg j ↦ _))
      ≡⟨ cong (λ inp → map₂ (encode (Var void) (Ports Δ)) (step κ (emitter Ν (ζw w)) (leg b) inp))
              (sym (trans (cong (λ m → decode (Var void) (Ports Δ) (inj₂ m)) (Π-portᵃ w neg j q))
                          (decode-port j (pick w (Pair.fst q) (Pair.snd q))))) ⟩
        map₂ (encode (Var void) (Ports Δ))
          (step κ (emitter Ν (ζw w)) (leg b) (decode (Var void) (Ports Δ) (inj₂ (Π φ ψ w neg (Ports Δ) (portᵃ neg j q))))) ∎
      where open ≡-Reasoning

  emitter≲ : (w : Side) → emitterᵃ RS.≲[ _ ∣ _ ] runᴿ κ (emitter Ν (ζw w))
  emitter≲ w = simFn[] leg (Πᴵ φ ψ w (Var void) (Ports Δ)) (Πᴼ φ ψ w (Var void) (Ports Δ))
    (λ _ → >>=ₚ-identityˡ false _)
    λ where
      (b , inj₂ a) → case-port b a (onportᵃ? Δ a)
    where
    case-port : (b : Bool) (a : Alphabetᵃ φ ψ neg (Ports Δ)) → OnPortᵃ Δ a
              → (returnₚ (true , inj₂ (answer entryᵃ a)) >>=ₚ λ x → returnₚ (leg (proj₁ x) , Πᴼ φ ψ w (Var void) (Ports Δ) (proj₂ x)))
              ≈ₚ returnₚ (map₂ (encode (Var void) (Ports Δ))
                   (step κ (emitter Ν (ζw w)) (leg b) (decode (Var void) (Ports Δ) (inj₂ (Π φ ψ w neg (Ports Δ) a)))))
    case-port b _ (onportᵃ j q) = >>=ₚ-identityˡ _ _ ⟨≈⟩ ≡⇒≈ₚ (cong returnₚ (law w b j q))

------------------------------------------------------------------------
-- Statically equivalent frames make kernel-equal emitters

≈ₛ⇒≈ℰ : {Δ Ν : List Sort} {ζs ζs′ : All (Rcp Ν) Δ}
      → (∀ κ → frame κ Ν ζs ≈ₛ frame κ Ν ζs′) → Emitter Ν ζs Sym.≈ℰ Emitter Ν ζs′
≈ₛ⇒≈ℰ {Δ} {Ν} {ζs} {ζs′} equiv = relsim⇒≈ℰ (↔-id _) λ ι _ → let κ = ι tt in record
  { φ     = frame κ Ν ζs
  ; ψ     = frame κ Ν ζs′
  ; equiv = equiv κ
  ; held  = λ where
      (inj₁ n∈) → tt , frame-names κ Ν ζs n∈
      (inj₂ n∈) → tt , frame-names κ Ν ζs′ n∈
  ; apex  = Apex.liftᵃ (frame κ Ν ζs) (frame κ Ν ζs′) {Var void} {Ports Δ} tt (ports-free Δ) (emitterᵃ ζs ζs′ κ)
  ; left  = Apex.proc-rel (frame κ Ν ζs) (frame κ Ν ζs′) l {Var void} {Ports Δ} tt (ports-free Δ) (emitter≲ ζs ζs′ κ l)
  ; right = Apex.proc-rel (frame κ Ν ζs) (frame κ Ν ζs′) r {Var void} {Ports Δ} tt (ports-free Δ) (emitter≲ ζs ζs′ κ r)
  }
