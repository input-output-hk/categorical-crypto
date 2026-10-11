{-# OPTIONS --safe --without-K --guardedness #-}

-- Relational simulation through Dolev–Yao circuits.  The apex world
-- interprets every atom at related pairs (`Static.Same`); along the two
-- projections, `HSimᵒ` (`UC.Model.Relational`) holds between the apex and the
-- circuit at every circuit whose leaves draw only names foreign to the frames
-- (`context`).  Two circuits that differ only in a part with such an apex —
-- the part exposes statically equivalent frames and alone holds their names
-- (`Emits`) — are kernel-equal (`relsim⇒≈ℰ`): any test and closure run in
-- lockstep in both worlds.  See docs/uc-setup-symbolic.md §3.5.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Static.Relational (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.FreeMonoidal using (module FreeObjInterp; Mon)
open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Function.Bundles using (_↔_; Inverse; mk⇔)
open import Function.Definitions using (Injective)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Pointwise using (module K)
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise using (module RS)
open import CategoricalCrypto.Symbolic.Deduction 𝔖 E
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖 using (Atom; Role; pos; neg; verdict; void)
open import CategoricalCrypto.Symbolic.Semantics 𝔖 E
open import CategoricalCrypto.Symbolic.Setup 𝔖 E
open import CategoricalCrypto.Symbolic.Static.Same 𝔖 E
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Relational
open import CategoricalCrypto.UC.Model.Seal

open Signature 𝔖
open Terms 𝔖

private
  module G = MonoidalCategory 𝔾ᵒ
  module Φ = FreeObjInterp Mon Atom ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ)

  variable
    A B Y : ObjTerm
    X X₀ X′ X₀′ Z Z₀ Z′ Z₀′ : G.Obj

------------------------------------------------------------------------
-- Transports along object equations

private
  subst-⊗ᵐ : (p : X ≡ X₀) (p′ : X′ ≡ X₀′) (q : Z ≡ Z₀) (q′ : Z′ ≡ Z₀′) {m : Mapᵒ X₀ X₀′} {n : Mapᵒ Z₀ Z₀′}
           → subst₂ Mapᵒ (sym p) (sym p′) m ⊗ᵐ subst₂ Mapᵒ (sym q) (sym q′) n
           ≡ subst₂ Mapᵒ (sym (cong₂ G._⊗₀_ p q)) (sym (cong₂ G._⊗₀_ p′ q′)) (m ⊗ᵐ n)
  subst-⊗ᵐ refl refl refl refl = refl

  subst₂-trans : (p : X ≡ X₀) (p′ : X′ ≡ X₀′) (q : X₀ ≡ Z) (q′ : X₀′ ≡ Z′) {m : Mapᵒ Z Z′}
               → subst₂ Mapᵒ (sym p) (sym p′) (subst₂ Mapᵒ (sym q) (sym q′) m)
               ≡ subst₂ Mapᵒ (sym (trans p q)) (sym (trans p′ q′)) m
  subst₂-trans refl refl refl refl = refl

  HSimᵒ-subst : (p : X ≡ X₀) (p′ : X′ ≡ X₀′) (q : Z ≡ Z₀) (q′ : Z′ ≡ Z₀′)
                {μX : Mapᵒ X₀ X₀′} {μZ : Mapᵒ Z₀ Z₀′} {f : X₀ G.⇒ Z₀} {g : X₀′ G.⇒ Z₀′}
              → HSimᵒ μX μZ f g
              → HSimᵒ (subst₂ Mapᵒ (sym p) (sym p′) μX) (subst₂ Mapᵒ (sym q) (sym q′) μZ)
                      (subst₂ G._⇒_ (sym p) (sym q) f) (subst₂ G._⇒_ (sym p′) (sym q′) g)
  HSimᵒ-subst refl refl refl refl h = h

------------------------------------------------------------------------
-- The apex world of a pair of frames

module Apex {Δ : List Sort} (φ ψ : Frame Δ) where

  atomᴵᵃ : Atom → Iface
  atomᴵᵃ a = alphabetᵃ φ ψ pos a ⇿ alphabetᵃ φ ψ neg a

  private module Aᵒ = FreeObjInterp Mon Atom ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵᵃ)

  ⟦_⟧ᵃ : ObjTerm → G.Obj
  ⟦_⟧ᵃ = Aᵒ.⟦_⟧₀

  ⟦_⟧ᴵᵃ : ObjTerm → Iface
  ⟦ x ⟧ᴵᵃ = Alphabetᵃ φ ψ pos x ⇿ Alphabetᵃ φ ψ neg x

  tree≡ᵃ : (x : ObjTerm) → UnitFree x → ⟦ x ⟧ᵃ ≡ ifaceᵒ ⟦ x ⟧ᴵᵃ
  tree≡ᵃ (x ⊗₀ y) (ux , uy) = trans (cong₂ G._⊗₀_ (tree≡ᵃ x ux) (tree≡ᵃ y uy)) (⊗ᵒ ⟦ x ⟧ᴵᵃ ⟦ y ⟧ᴵᵃ)
  tree≡ᵃ (Var _)  _         = refl

  -- Each world reads the apex letters through its projection.
  μ : Side → (x : ObjTerm) → Mapᵒ ⟦ x ⟧ᵃ Φ.⟦ x ⟧₀
  μ w unit     = idᵐ
  μ w (x ⊗₀ y) = μ w x ⊗ᵐ μ w y
  μ w (Var a)  = ifaceᵐ (π φ ψ w pos a) (π φ ψ w neg a)

  μ-tree : (w : Side) (x : ObjTerm) (ux : UnitFree x)
         → μ w x ≡ subst₂ Mapᵒ (sym (tree≡ᵃ x ux)) (sym (tree≡ x ux)) (ifaceᵐ (Π φ ψ w pos x) (Π φ ψ w neg x))
  μ-tree w (Var _)  _         = refl
  μ-tree w (x ⊗₀ y) (ux , uy) =
    trans (cong₂ _⊗ᵐ_ (μ-tree w x ux) (μ-tree w y uy))
    (trans (subst-⊗ᵐ (tree≡ᵃ x ux) (tree≡ x ux) (tree≡ᵃ y uy) (tree≡ y uy))
    (trans (cong (subst₂ Mapᵒ (sym (cong₂ G._⊗₀_ (tree≡ᵃ x ux) (tree≡ᵃ y uy)))
                              (sym (cong₂ G._⊗₀_ (tree≡ x ux) (tree≡ y uy)))) ifaceᵐ-⊗)
           (subst₂-trans (cong₂ G._⊗₀_ (tree≡ᵃ x ux) (tree≡ᵃ y uy)) (cong₂ G._⊗₀_ (tree≡ x ux) (tree≡ y uy))
                         (⊗ᵒ ⟦ x ⟧ᴵᵃ ⟦ y ⟧ᴵᵃ) (⊗ᵒ ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ))))

  -- An apex process for a single role, read across the seal.
  liftᵃ : {x y : ObjTerm} → UnitFree x → UnitFree y → Proc ⟦ x ⟧ᴵᵃ ⟦ y ⟧ᴵᵃ → ⟦ x ⟧ᵃ G.⇒ ⟦ y ⟧ᵃ
  liftᵃ {x} {y} ux uy q = subst₂ G._⇒_ (sym (tree≡ᵃ x ux)) (sym (tree≡ᵃ y uy)) (procᵒ q)

  proc-rel : (w : Side) {x y : ObjTerm} (ux : UnitFree x) (uy : UnitFree y)
             {q : Proc ⟦ x ⟧ᴵᵃ ⟦ y ⟧ᴵᵃ} {p : Role x y} {κ : ℕ}
           → q RS.≲[ K.pureᵏ (Πᴵ φ ψ w x y) ∣ K.pureᵏ (Πᴼ φ ψ w x y) ] runᴿ κ p
           → HSimᵒ (μ w x) (μ w y) (liftᵃ ux uy q) (leafᵒ (ux , uy , p) κ)
  proc-rel w {x} {y} ux uy s =
    subst₂ (λ m n → HSimᵒ m n _ _) (sym (μ-tree w x ux)) (sym (μ-tree w y uy))
      (HSimᵒ-subst (tree≡ᵃ x ux) (tree≡ x ux) (tree≡ᵃ y uy) (tree≡ y uy)
        (HSimᵒ-proc (Π φ ψ w pos x) (Π φ ψ w neg x) (Π φ ψ w pos y) (Π φ ψ w neg y) s))

  module _ (equiv : φ ≈ₛ ψ) where

    -- An apex related to `h` in both worlds.
    Rel : (A B : ObjTerm) → Φ.⟦ A ⟧₀ G.⇒ Φ.⟦ B ⟧₀ → Set₁
    Rel A B h = Σ[ h′ ∈ ⟦ A ⟧ᵃ G.⇒ ⟦ B ⟧ᵃ ] HSimᵒ (μ l A) (μ l B) h′ h × HSimᵒ (μ r A) (μ r B) h′ h

    private
      closed : Closed Rel
      closed = record
        { P-id = λ {A} → _ , HSimᵒ-id (μ l A) , HSimᵒ-id (μ r A)
        ; P-∘  = λ (_ , gl , gr) (_ , fl , fr) → _ , HSimᵒ-∘ gl fl , HSimᵒ-∘ gr fr
        ; P-⊗  = λ (_ , fl , fr) (_ , gl , gr) → _ , HSimᵒ-⊗ fl gl , HSimᵒ-⊗ fr gr
        ; P-λ⇒ = λ {A} → _ , HSimᵒ-λ⇒ (μ l A) , HSimᵒ-λ⇒ (μ r A)
        ; P-λ⇐ = λ {A} → _ , HSimᵒ-λ⇐ (μ l A) , HSimᵒ-λ⇐ (μ r A)
        ; P-ρ⇒ = λ {A} → _ , HSimᵒ-ρ⇒ (μ l A) , HSimᵒ-ρ⇒ (μ r A)
        ; P-ρ⇐ = λ {A} → _ , HSimᵒ-ρ⇐ (μ l A) , HSimᵒ-ρ⇐ (μ r A)
        ; P-α⇒ = λ {A} {B} {C} → _ , HSimᵒ-α⇒ (μ l A) (μ l B) (μ l C) , HSimᵒ-α⇒ (μ r A) (μ r B) (μ r C)
        ; P-α⇐ = λ {A} {B} {C} → _ , HSimᵒ-α⇐ (μ l A) (μ l B) (μ l C) , HSimᵒ-α⇐ (μ r A) (μ r B) (μ r C)
        ; P-σ  = λ { ⦃ () ⦄ }
        }

    -- A circuit whose occurrences draw foreign names runs alike in both worlds.
    context : (c : HomTerm A B) (ι : Occ c → ℕ) → (∀ o j → Foreign φ ψ (ι o , j)) → Rel A B ⟦ c ⟧[ ι ]
    context = ⟦⟧[]-ind Rel closed (λ κ → ∀ j → Foreign φ ψ (κ , j)) λ (ux , uy , p) κ fresh →
      liftᵃ ux uy (apexᴿ φ ψ equiv fresh p)
      , proc-rel l ux uy (apex≲ φ ψ equiv fresh p l) , proc-rel r ux uy (apex≲ φ ψ equiv fresh p r)

------------------------------------------------------------------------
-- Circuits differing in one part

-- At a naming of `f`'s occurrences: frames the part alone holds, statically
-- equivalent, and an apex of `f` and `g` over them.
record Emits {A B : ObjTerm} (f g : HomTerm A B) (occ : Occ f ↔ Occ g) (ι : Occ f → ℕ) : Set₁ where
  field
    {Δ}   : List Sort
    φ ψ   : Frame Δ
    equiv : φ ≈ₛ ψ
    held  : ∀ {n} → n ∈ names* φ ⊎ n ∈ names* ψ → ∃[ o ] proj₁ n ≡ ι o
    apex  : Apex.⟦_⟧ᵃ φ ψ A G.⇒ Apex.⟦_⟧ᵃ φ ψ B
    left  : HSimᵒ (Apex.μ φ ψ l A) (Apex.μ φ ψ l B) apex ⟦ f ⟧[ ι ]
    right : HSimᵒ (Apex.μ φ ψ r A) (Apex.μ φ ψ r B) apex ⟦ g ⟧[ ι ∘′ Inverse.from occ ]

module _ {A B : ObjTerm} {f g : HomTerm A B} (occ : Occ f ↔ Occ g)
         (emits : (ι : Occ f → ℕ) → Injective _≡_ _≡_ ι → Emits f g occ ι) where

  private
    module occ = Inverse occ

    module Circuit (T : HomTerm (Y ⊗₀ B) (Var verdict)) (m : Closure (Y ⊗₀ A)) where

      cf cg : HomTerm (Var void) (Var verdict)
      cf = (T ∘ id ⊗₁ f) ∘ m
      cg = (T ∘ id ⊗₁ g) ∘ m

      relabel : Occ cg → Occ cf
      relabel (inj₁ (inj₁ o))        = inj₁ (inj₁ o)
      relabel (inj₁ (inj₂ (inj₁ ())))
      relabel (inj₁ (inj₂ (inj₂ o))) = inj₁ (inj₂ (inj₂ (occ.from o)))
      relabel (inj₂ o)               = inj₂ o

      back : Occ cf → Occ cg
      back (inj₁ (inj₁ o))        = inj₁ (inj₁ o)
      back (inj₁ (inj₂ (inj₁ ())))
      back (inj₁ (inj₂ (inj₂ o))) = inj₁ (inj₂ (inj₂ (occ.to o)))
      back (inj₂ o)               = inj₂ o

      back-relabel : ∀ x → back (relabel x) ≡ x
      back-relabel (inj₁ (inj₁ _))        = refl
      back-relabel (inj₁ (inj₂ (inj₁ ())))
      back-relabel (inj₁ (inj₂ (inj₂ o))) = cong (λ z → inj₁ (inj₂ (inj₂ z))) (occ.strictlyInverseˡ o)
      back-relabel (inj₂ _)               = refl

      relabel-back : ∀ x → relabel (back x) ≡ x
      relabel-back (inj₁ (inj₁ _))        = refl
      relabel-back (inj₁ (inj₂ (inj₁ ())))
      relabel-back (inj₁ (inj₂ (inj₂ o))) = cong (λ z → inj₁ (inj₂ (inj₂ z))) (occ.strictlyInverseʳ o)
      relabel-back (inj₂ _)               = refl

      -- The two closed runs are one machine up to the hom equality.
      lockstep : (ι : Occ cf → ℕ) → Injective _≡_ _≡_ ι → ⟦ cf ⟧[ ι ] G.≈ ⟦ cg ⟧[ ι ∘′ relabel ]
      lockstep ι inj = G.Equiv.trans (G.Equiv.sym (ends l closeˡ)) (ends r closeʳ)
        where
        ιf : Occ f → ℕ
        ιf o = ι (inj₁ (inj₂ (inj₂ o)))

        part : ∀ {o o′ : Occ f} → _≡_ {A = Occ cf} (inj₁ (inj₂ (inj₂ o))) (inj₁ (inj₂ (inj₂ o′))) → o ≡ o′
        part refl = refl

        open Emits (emits ιf λ e → part (inj e))

        -- Every other occurrence draws names the frames do not mention.
        fresh : (x : Occ cf) → (∀ {o′} → x ≢ inj₁ (inj₂ (inj₂ o′))) → ∀ j → Foreign φ ψ (ι x , j)
        fresh x out j = (λ n∈ → out (inj (proj₂ (held (inj₁ n∈)))))
                      , (λ n∈ → out (inj (proj₂ (held (inj₂ n∈)))))

        T-rel = Apex.context φ ψ equiv T (λ o → ι (inj₁ (inj₁ o))) λ o → fresh (inj₁ (inj₁ o)) λ ()
        m-rel = Apex.context φ ψ equiv m (λ o → ι (inj₂ o)) λ o → fresh (inj₂ o) λ ()

        apexᶜ : Φ.⟦ Var void ⟧₀ G.⇒ Φ.⟦ Var verdict ⟧₀
        apexᶜ = (proj₁ T-rel G.∘ (G.id G.⊗₁ apex)) G.∘ proj₁ m-rel

        -- The closed apex reads verdicts and ticks as they are.
        ends : (w : Side) {c : Φ.⟦ Var void ⟧₀ G.⇒ Φ.⟦ Var verdict ⟧₀}
             → HSimᵒ (Apex.μ φ ψ w (Var void)) (Apex.μ φ ψ w (Var verdict)) apexᶜ c → apexᶜ G.≈ c
        ends w {c} h = HSimᵒ⇒≈ (subst₂ (λ a b → HSimᵒ a b apexᶜ c)
                                       (ifaceᵐ-id {A = atomᴵ void}) (ifaceᵐ-id {A = atomᴵ verdict}) h)

        closeˡ : HSimᵒ (Apex.μ φ ψ l (Var void)) (Apex.μ φ ψ l (Var verdict)) apexᶜ ⟦ cf ⟧[ ι ]
        closeˡ = HSimᵒ-∘ (HSimᵒ-∘ (proj₁ (proj₂ T-rel)) (HSimᵒ-⊗ (HSimᵒ-id (Apex.μ φ ψ l Y)) left))
                         (proj₁ (proj₂ m-rel))

        closeʳ : HSimᵒ (Apex.μ φ ψ r (Var void)) (Apex.μ φ ψ r (Var verdict)) apexᶜ ⟦ cg ⟧[ ι ∘′ relabel ]
        closeʳ = HSimᵒ-∘ (HSimᵒ-∘ (proj₂ (proj₂ T-rel)) (HSimᵒ-⊗ (HSimᵒ-id (Apex.μ φ ψ r Y)) right))
                         (proj₂ (proj₂ m-rel))

      relabel-inj : Injective _≡_ _≡_ relabel
      relabel-inj {x} {y} e = trans (sym (back-relabel x)) (trans (cong back e) (back-relabel y))

      back-inj : Injective _≡_ _≡_ back
      back-inj {x} {y} e = trans (sym (relabel-back x)) (trans (cong relabel e) (relabel-back y))

  relsim⇒≈ℰ : f Sym.≈ℰ g
  relsim⇒≈ℰ = Sym.KE.mk∼ λ { {lift (_ , T)} → lift (same λ m b → mk⇔ (forth T m b) (backward T m b)) }
    where
    forth : (T : HomTerm (Y ⊗₀ B) (Var verdict)) (m : Closure (Y ⊗₀ A)) (b : Bool)
          → eval ((T ∘ id ⊗₁ f) ∘ m) b → eval ((T ∘ id ⊗₁ g) ∘ m) b
    forth T m b (named ι inj ans) =
      named (ι ∘′ relabel) (λ e → relabel-inj (inj e)) (≈sym (obs-resp (lockstep ι inj)) ⟨≈⟩ ans)
      where open Circuit T m

    backward : (T : HomTerm (Y ⊗₀ B) (Var verdict)) (m : Closure (Y ⊗₀ A)) (b : Bool)
             → eval ((T ∘ id ⊗₁ g) ∘ m) b → eval ((T ∘ id ⊗₁ f) ∘ m) b
    backward T m b (named ι inj ans) =
      named (ι ∘′ back) (λ e → back-inj (inj e))
        (obs-resp (lockstep (ι ∘′ back) (λ e → back-inj (inj e)))
         ⟨≈⟩ ≡⇒≈ₚ (cong Obs (⟦⟧[]-cong cg λ x → cong ι (back-relabel x))) ⟨≈⟩ ans)
      where open Circuit T m
