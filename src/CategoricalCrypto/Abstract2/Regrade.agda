{-# OPTIONS --safe --without-K #-}

-- 𝕊|ι, a UC setup restricted along a lax monoidal functor of grades ι : 𝒥 → ℐ
-- (`docs/uc-setup-nondeterministic.md` §1): 𝕊's computations and tests, and the
-- graded monad precomposed with ι — a graded monad is a lax monoidal functor
-- ℐ → [𝒞, 𝒞] (fujii2016), so this is `Graded.Pullback.pullbackM`.  A protocol
-- of 𝕊|ι at grade X is one of 𝕊 at ι X; only the adversaries, the simulators
-- and the ancillas are cut down to ι's image.  The dual of
-- `Abstract2.WideSubcategory`, which restricts the computations instead.
--
-- `inclusion` = (Id, ι, id, `idᵛ`) reflects ≤UC when ι is full (`restrict-≤UC`)
-- and preserves it when ι is essentially surjective with split comparisons
-- (`Preserves`) or 𝕊 is grade-stable (`unrestrict-≤UC-gs`).  `Between` relates
-- two restrictions.

open import Level

open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal

open import CategoricalCrypto.UCSetup

module CategoricalCrypto.Abstract2.Regrade
  {o ℓ e o′ ℓ′ e′ cs ℓs oⱼ ℓⱼ eⱼ : Level} (𝕊 : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ} (ι : MonoidalFunctor 𝒥 (UCSetup.ℐ 𝕊)) where

open import Data.Product

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Monoidal.Properties
open import Categories.Functor.Presheaf.Morphism
open import Categories.Functor.Properties
import Categories.Morphism as Mor
open import Categories.Morphism.Notation
open import Categories.NaturalTransformation.NaturalIsomorphism.Monoidal

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.UCSetup.Morphism

open AbstractUC 𝕊

private
  module 𝒥 = MonoidalCategory 𝒥
  module ι = MonoidalFunctor ι

  variable
    A B : 𝒞.Obj
    V W : ℐ.Obj
    X Y : 𝒥.Obj

ι₂ : (W X : 𝒥.Obj) → ι.₀ W ⊗₀ ι.₀ X ℐ.⇒ ι.₀ (W 𝒥.⊗₀ X)
ι₂ W X = ι.⊗-homo.η (W , X)

regraded : UCSetup oⱼ ℓⱼ eⱼ o′ ℓ′ e′ cs ℓs
regraded = record { 𝒞 = 𝒞 ; ℐ = 𝒥 ; ℳ = ∘-Monoidal ℳ ι ; ℰ = ℰ }

-- R.T₀ X = T₀ (ι.₀ X), R.sub c = sub (ι.₁ c), R.return = sub ι.ε ∘ return and
-- R.μ W X = sub (ι₂ W X) ∘ μ (ι.₀ W) (ι.₀ X), definitionally (`Regrade.Pin`).
module R = AbstractUC regraded

inclusion : UCSetupMorphism regraded 𝕊
inclusion = record
  { effect = record
    { F = idF ; Φ = ι ; κ = 𝒞.id
    ; isGradedKleisliMorphism = record
      { κ-return = identityˡ
      ; κ-ext = λ _ → identityˡ ○ assoc ○ refl⟩∘⟨ (ext-resp-≈ (⟺ identityˡ) ○ ⟺ identityʳ)
      ; κ-sub = λ _ → id-comm-sym } }
  ; ν = idᵛ ℰ }
  where open 𝒞

private
  across : {u u′ v v′ : A 𝒞.⇒ B} → u 𝒞.≈ u′ → v 𝒞.≈ v′ → u′ ≈ℰ v′ → u ≈ℰ v
  across p q e = ≈ℰ-trans (≈C⇒≈ℰ p) (≈ℰ-trans e (≈ℰ-sym (≈C⇒≈ℰ q)))

  sub-inv : {α : V ℐ.⇒ W} {β : W ℐ.⇒ V} → α ℐ.∘ β ℐ.≈ ℐ.id → sub α 𝒞.∘ sub β 𝒞.≈ 𝒞.id {T₀ W A}
  sub-inv inv = ⟺ sub-homomorphism ○ sub-resp-≈ inv ○ sub-identity
    where open 𝒞

------------------------------------------------------------------------
-- What the inclusion preserves and reflects (§1.3)
------------------------------------------------------------------------

≈ᵁ⇒≈ᵁ|ι : {f g : A 𝒞.⇒ T₀ (ι.₀ X) B} → f ≈ᵁ g → f R.≈ᵁ g
≈ᵁ⇒≈ᵁ|ι e W = across 𝒞.assoc 𝒞.assoc (≈ℰ-cong-post (sub (ι₂ W _)) (e (ι.₀ W)))

restrict-≤UC : Full ι.F → {f : A 𝒞.⇒ T₀ (ι.₀ X) B} {g : A 𝒞.⇒ T₀ (ι.₀ Y) B}
             → f ≤UC g → f R.≤UC g
restrict-≤UC full f≤g =
  let s₀ , e = ≤UC⇒dummy f≤g
      s₀′ , ιs₀′≈s₀ = full s₀
  in R.dummy-complete
       (s₀′ , ≈ᵁ⇒≈ᵁ|ι (≈ᵁ-trans e (≈C⇒≈ᵁ (𝒞.∘-resp-≈ˡ (sub-resp-≈ (ℐ.Equiv.sym ιs₀′≈s₀))))))

-- ι with split comparisons; a strong ι supplies `⊗-homo.⇐`
module Preserves (r : ∀ {W X} → ι.₀ (W 𝒥.⊗₀ X) ℐ.⇒ ι.₀ W ⊗₀ ι.₀ X)
                 (r∘ι₂ : ∀ {W X} → r ℐ.∘ ι₂ W X ℐ.≈ ℐ.id) where

  -- 𝕊's component at an ancilla W that is a retract of an image ancilla ι W′
  ≈ᵁ|ι⇒≈ᵁ-at : {f g : A 𝒞.⇒ T₀ (ι.₀ X) B} → f R.≈ᵁ g
             → {W′ : 𝒥.Obj} {u : ι.₀ W′ ℐ.⇒ W} {u⁻ : W ℐ.⇒ ι.₀ W′} → u ℐ.∘ u⁻ ℐ.≈ ℐ.id
             → μ W (ι.₀ X) 𝒞.∘ T₁ W f ≈ℰ μ W (ι.₀ X) 𝒞.∘ T₁ W g
  ≈ᵁ|ι⇒≈ᵁ-at {X = X} {W = W} {f = f} {g} e {W′} {u} {u⁻} inv =
    across (conj f) (conj g) (≈ℰ-cong-post (sub (u ⊗₁ ℐ.id)) (≈ℰ-cong-pre (sub u⁻)
      (across (cancel f) (cancel g) (≈ℰ-cong-post (sub r) (e W′)))))
    where
      open 𝒞
      cancel : (h : A ⇒ T₀ (ι.₀ X) B)
             → ext (ι.₀ W′) h ≈ sub r ∘ (sub (ι₂ W′ X) ∘ μ (ι.₀ W′) (ι.₀ X)) ∘ T₁ (ι.₀ W′) h
      cancel _ = introˡ (sub-inv r∘ι₂) ○ assoc ○ refl⟩∘⟨ sym-assoc
      conj : (h : A ⇒ T₀ (ι.₀ X) B) → ext W h ≈ sub (u ⊗₁ ℐ.id) ∘ ext (ι.₀ W′) h ∘ sub u⁻
      conj _ = introʳ (sub-inv inv) ○ pullˡ sub-commute₁ ○ assoc

  module _ (surj : EssentiallySurjective ι.F) where

    ≈ᵁ|ι⇒≈ᵁ : {f g : A 𝒞.⇒ T₀ (ι.₀ X) B} → f R.≈ᵁ g → f ≈ᵁ g
    ≈ᵁ|ι⇒≈ᵁ e W = ≈ᵁ|ι⇒≈ᵁ-at e (Mor._≅_.isoʳ (proj₂ (surj W)))

    unrestrict-≤UC : {f : A 𝒞.⇒ T₀ (ι.₀ X) B} {g : A 𝒞.⇒ T₀ (ι.₀ Y) B} → f R.≤UC g → f ≤UC g
    unrestrict-≤UC le = let s₀ , e = R.≤UC⇒dummy le in dummy-complete (ι.₁ s₀ , ≈ᵁ|ι⇒≈ᵁ e)

regraded-gs : GradeStable → R.GradeStable
regraded-gs gs Y = gs (ι.₀ Y)

unrestrict-≤UC-gs : GradeStable → {f : A 𝒞.⇒ T₀ (ι.₀ X) B} {g : A 𝒞.⇒ T₀ (ι.₀ Y) B}
                  → f R.≤UC g → f ≤UC g
unrestrict-≤UC-gs gs le =
  ≤UC-resp-≈ 𝒞.identityˡ 𝒞.identityˡ (Transfer.transfer inclusion (idᵛ-epi {P = ℰ}) gs le)

------------------------------------------------------------------------
-- Between two restrictions (§1.4)
------------------------------------------------------------------------

-- `regraded′` is `Regrade 𝕊 ι′`'s `regraded`, spelled out: a module cannot name
-- its own instance.
module Between {oⱼ′ ℓⱼ′ eⱼ′ : Level} {𝒥′ : MonoidalCategory oⱼ′ ℓⱼ′ eⱼ′}
               (ι′ : MonoidalFunctor 𝒥′ ℐ) (j : MonoidalFunctor 𝒥 𝒥′)
               (θ : Lax.MonoidalNaturalIsomorphism (∘-Monoidal ι′ j) ι) where
  private
    module 𝒥′ = MonoidalCategory 𝒥′
    module ι′ = MonoidalFunctor ι′
    module j = MonoidalFunctor j
    module θ = Lax.MonoidalNaturalIsomorphism θ

  regraded′ : UCSetup oⱼ′ ℓⱼ′ eⱼ′ o′ ℓ′ e′ cs ℓs
  regraded′ = record { 𝒞 = 𝒞 ; ℐ = 𝒥′ ; ℳ = ∘-Monoidal ℳ ι′ ; ℰ = ℰ }

  module R′ = AbstractUC regraded′

  between : UCSetupMorphism regraded regraded′
  between = record
    { effect = record
      { F = idF ; Φ = j ; κ = sub (θ.⇐.η _)
      ; isGradedKleisliMorphism = record
        { κ-return = pullˡ (⟺ sub-homomorphism ○ sub-resp-≈ θ.⇐.ε-compat ○ sub-homomorphism) ○ assoc
        ; κ-ext = ext-law
        ; κ-sub = λ c → ⟺ sub-homomorphism ○ sub-resp-≈ (θ.⇐.commute c) ○ sub-homomorphism } }
    ; ν = idᵛ ℰ }
    where
      open 𝒞
      ext-law : (f : A ⇒ T₀ (ι.₀ Y) B)
              → sub (θ.⇐.η (X 𝒥.⊗₀ Y)) ∘ R.ext X f
                ≈ R′.sub (j.⊗-homo.η (X , Y)) ∘ R′.ext (j.₀ X) (sub (θ.⇐.η Y) ∘ f) ∘ sub (θ.⇐.η X)
      ext-law {Y = Y} {X = X} f = begin
        sub θ⁻ˣʸ ∘ (sub (ι₂ X Y) ∘ μ (ι.₀ X) (ι.₀ Y)) ∘ T₁ (ι.₀ X) f
          ≈⟨ refl⟩∘⟨ assoc ⟩
        sub θ⁻ˣʸ ∘ sub (ι₂ X Y) ∘ ext (ι.₀ X) f
          ≈⟨ pullˡ (⟺ sub-homomorphism) ○ sub-resp-≈ θ.⇐.⊗-homo-compat ⟩∘⟨refl ⟩
        sub ((ι′.₁ j₂ ℐ.∘ ι′₂) ℐ.∘ θ⁻ˣ ⊗₁ θ⁻ʸ) ∘ ext (ι.₀ X) f
          ≈⟨ pushˡ sub-homomorphism ○ refl⟩∘⟨ ⟺ sub-commute ⟩
        sub (ι′.₁ j₂ ℐ.∘ ι′₂) ∘ ext (ι′.₀ (j.₀ X)) (sub θ⁻ʸ ∘ f) ∘ sub θ⁻ˣ
          ≈⟨ pushˡ sub-homomorphism ○ refl⟩∘⟨ (sym-assoc ○ sym-assoc ⟩∘⟨refl) ⟩
        R′.sub j₂ ∘ R′.ext (j.₀ X) (sub θ⁻ʸ ∘ f) ∘ sub θ⁻ˣ ∎
        where
          θ⁻ˣ = θ.⇐.η X
          θ⁻ʸ = θ.⇐.η Y
          θ⁻ˣʸ = θ.⇐.η (X 𝒥.⊗₀ Y)
          j₂ = j.⊗-homo.η (X , Y)
          ι′₂ = ι′.⊗-homo.η (j.₀ X , j.₀ Y)

  module T = Transfer between
  private module B = UCSetupMorphism between

  -- 𝕊|ι's ancillas are, up to θ, among 𝕊|ι′'s
  reflects-≈ᵁ : {f g : A 𝒞.⇒ T₀ (ι.₀ X) B} → T.G f R′.≈ᵁ T.G g → f R.≈ᵁ g
  reflects-≈ᵁ {X = X} {f = f} {g} e W =
    across (back f) (back g) (≈ℰ-cong-post _ (≈ℰ-cong-pre (sub (θ.⇐.η W)) (e (j.₀ W))))
    where
      open 𝒞
      back : (h : A ⇒ T₀ (ι.₀ X) B)
           → R.ext W h ≈ (sub (θ.⇒.η (W 𝒥.⊗₀ X)) ∘ R′.sub (j.⊗-homo.η (W , X)))
                         ∘ R′.ext (j.₀ W) (T.G h) ∘ sub (θ.⇐.η W)
      back h = ⟺ (cancelˡ (sub-inv (θ.iso.isoʳ _))) ○ refl⟩∘⟨ B.κ-ext h ○ sym-assoc

  reflects-≤UC : Full j.F → T.Reflects-≤UC
  reflects-≤UC full {g = g} Gf≤Gg =
    let s′ , e = R′.≤UC⇒dummy Gf≤Gg
        s , js≈s′ = full s′
    in R.dummy-complete (s , reflects-≈ᵁ (R′.≈ᵁ-trans e (R′.≈C⇒≈ᵁ
         (sub-resp-≈ (ι′.F-resp-≈ (𝒥′.Equiv.sym js≈s′)) ⟩∘⟨refl ○ pullˡ (⟺ (B.κ-sub s)) ○ assoc))))
    where open 𝒞

  module _ (r : ∀ {W X} → ι.₀ (W 𝒥.⊗₀ X) ℐ.⇒ ι.₀ W ⊗₀ ι.₀ X)
           (r∘ι₂ : ∀ {W X} → r ℐ.∘ ι₂ W X ℐ.≈ ℐ.id)
           (img : (W′ : 𝒥′.Obj) → Σ[ W ∈ 𝒥.Obj ] ℐ.U [ ι.₀ W ≅ ι′.₀ W′ ]) where
    open Preserves r r∘ι₂

    preserves-≈ᵁ : T.Preserves-≈ᵁ
    preserves-≈ᵁ {X = X} {f = f} {g} e W′ =
      across (fwd f) (fwd g) (≈ℰ-cong-post _ (≈ᵁ|ι⇒≈ᵁ-at e (Mor._≅_.isoʳ (proj₂ (img W′)))))
      where
        open 𝒞
        fwd : (h : A ⇒ T₀ (ι.₀ X) B)
            → R′.ext W′ (T.G h)
              ≈ (sub (ι′.⊗-homo.η (W′ , j.₀ X)) ∘ sub (ℐ.id ⊗₁ θ.⇐.η X)) ∘ ext (ι′.₀ W′) h
        fwd _ = assoc ○ refl⟩∘⟨ sub-commute₂ ○ sym-assoc

    preserves-≤UC : T.Preserves-≤UC
    preserves-≤UC = T.transfer⁺ preserves-≈ᵁ
