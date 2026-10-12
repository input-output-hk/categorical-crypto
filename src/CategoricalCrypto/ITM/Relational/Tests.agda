{-# OPTIONS --safe #-}

module CategoricalCrypto.ITM.Relational.Tests where

open import Categories.FreeMonoidal
open import Categories.Functor
open import Categories.Functor.Monoidal

open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation.Core

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Channel.Core hiding (In; Out) renaming (_⊗₀_ to _⊗ᶜ_)
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.ITM.Relational
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Machine.Initialized
open import CategoricalCrypto.Machine.Iso

import CategoricalCrypto.Machine.UC as Iso

open FreeMonoidal itmData hiding (id; _∘_; _⊗₁_)

P : Ports
P = Var ⁺

private
  q₀ q₁ q₂ q₃ : Fin 4
  q₀ = zero
  q₁ = suc zero
  q₂ = suc (suc zero)
  q₃ = suc (suc (suc zero))

  table : Fin 4 → In P P → Sym → Sym → Instr (Fin 4) (Out P P)
  table zero _ w _ = run q₁ w ∙ ∙ (just false)
  table (suc zero) _ _ _ = send (inj₂ tt) q₀
  table (suc (suc zero)) _ w _ = run q₃ w ∙ ∙ (just true)
  table (suc (suc (suc zero))) _ _ _ = send (inj₂ tt) q₂

zeroStart : Gen P P
zeroStart = record { #Q = 4 ; start = q₀ ; δ = table }

oneStart : Gen P P
oneStart = Uninitialized.Reinitialize.M′ zeroStart q₂

same-table : TM.δ zeroStart ≡ TM.δ oneStart
same-table = refl

uninitialized-images-iso : Uninitialized.leaf {A = P} {B = P} zeroStart
                           ≅ᴹ Uninitialized.leaf {A = P} {B = P} oneStart
uninitialized-images-iso = Uninitialized.reinitialize-iso {A = P} {B = P} zeroStart q₂

private
  C : Channel
  C = Functor.F₀ (StrongMonoidalFunctor.F Uninitialized.F) P

probe : Channel.inType (C ⊗ᵀ C)
probe = construct-⊗ {m = Mode.In} (inj₁ [])

reply : Bool → Channel.outType (C ⊗ᵀ C)
reply b = encodeᴿ P P (inj₂ tt , b ∷ [])

zero-query : Executes (initializedLeaf {A = P} {B = P} zeroStart) ((probe , just (reply false)) ∷ [])
zero-query = blank zeroStart , next ((inj₂ tt , false ∷ []) , step refl (halt refl) , refl) done

one-query : Executes (initializedLeaf {A = P} {B = P} oneStart) ((probe , just (reply true)) ∷ [])
one-query = blank oneStart , next ((inj₂ tt , true ∷ []) , step refl (halt refl) , refl) done

two-zero-replies : Executes (initializedLeaf {A = P} {B = P} zeroStart)
  ((probe , just (reply false)) ∷ (probe , just (reply false)) ∷ [])
two-zero-replies = blank zeroStart ,
  next ((inj₂ tt , false ∷ []) , step refl (halt refl) , refl)
    (next ((inj₂ tt , false ∷ []) , step refl (halt refl) , refl) done)

two-one-replies : Executes (initializedLeaf {A = P} {B = P} oneStart)
  ((probe , just (reply true)) ∷ (probe , just (reply true)) ∷ [])
two-one-replies = blank oneStart ,
  next ((inj₂ tt , true ∷ []) , step refl (halt refl) , refl)
    (next ((inj₂ tt , true ∷ []) , step refl (halt refl) , refl) done)

private
  zero-only : ∀ {x r} → Halts zeroStart (load zeroStart (blank zeroStart) x) r
            → proj₂ (proj₂ r) ≡ false ∷ []
  zero-only (halt ())
  zero-only (step refl (halt refl)) = refl
  zero-only (step refl (step () _))
  zero-only (step refl (toss _ () _))
  zero-only (toss _ () _)

  one-only : ∀ {x r} → Halts oneStart (load oneStart (blank oneStart) x) r
           → proj₂ (proj₂ r) ≡ true ∷ []
  one-only (halt ())
  one-only (step refl (halt refl)) = refl
  one-only (step refl (step () _))
  one-only (step refl (toss _ () _))
  one-only (toss _ () _)

  opaque
    unfolding _⊗ᶜ_ construct-⊗
    output-injective : ∀ {v w} → just (encodeᴿ P P (inj₂ tt , v)) ≡ just (encodeᴿ P P (inj₂ tt , w))
                     → v ≡ w
    output-injective refl = refl

  false≠true : false ∷ [] ≡ true ∷ [] → ⊥
  false≠true ()

zero-rejects-one : ¬ Executes (initializedLeaf {A = P} {B = P} zeroStart) ((probe , just (reply true)) ∷ [])
zero-rejects-one (_ , next ((inj₁ () , _) , _ , _) _)
zero-rejects-one (_ , next ((inj₂ tt , _) , h , eq) _) =
  false≠true (trans (sym (zero-only h)) (sym (output-injective eq)))

one-rejects-zero : ¬ Executes (initializedLeaf {A = P} {B = P} oneStart) ((probe , just (reply false)) ∷ [])
one-rejects-zero (_ , next ((inj₁ () , _) , _ , _) _)
one-rejects-zero (_ , next ((inj₂ tt , _) , h , eq) _) =
  false≠true (trans (output-injective eq) (one-only h))

initialized-traces-differ : ¬ (initializedLeaf {A = P} {B = P} zeroStart
                              ≈ᵗ initializedLeaf {A = P} {B = P} oneStart)
initialized-traces-differ e = one-rejects-zero
  (Equivalence.to (e ((probe , just (reply false)) ∷ [])) zero-query)

no-initialized-iso : ¬ (initializedLeaf {A = P} {B = P} zeroStart
                       ≅ⁱ initializedLeaf {A = P} {B = P} oneStart)
no-initialized-iso φ = initialized-traces-differ (≅ⁱ⇒≈ᵗ φ)

blankLatch : Gen P P
blankLatch = record { #Q = 2 ; start = zero ; δ = latch-table }
  where
  latch-table : Fin 2 → In P P → Sym → Sym → Instr (Fin 2) (Out P P)
  latch-table zero _ ␣ _ = run (suc zero) 𝟏 ∙ ∙ (just false)
  latch-table zero _ 𝟎 _ = run (suc zero) 𝟏 ∙ ∙ (just true)
  latch-table zero _ 𝟏 _ = run (suc zero) 𝟏 ∙ ∙ (just true)
  latch-table (suc zero) _ _ _ = send (inj₂ tt) zero

initialized-memory-evolves : Executes (initializedLeaf {A = P} {B = P} blankLatch)
  ((probe , just (reply false)) ∷ (probe , just (reply true)) ∷ [])
initialized-memory-evolves = (zero , [] ‹ 𝟏 › []) ,
  next ((inj₂ tt , false ∷ []) , step refl (halt refl) , refl)
    (next ((inj₂ tt , true ∷ []) , step refl (halt refl) , refl) done)

private
  module F = StrongMonoidalFunctor Uninitialized.F
  module Transport = Transfer Uninitialized.⇒iso
  module UC = Uninitialized.UC

zero-system one-system : P UC.𝒞.⇒ UC.T₀ unit P
zero-system = UC.λ⇐ UC.∘ var zeroStart
one-system = UC.λ⇐ UC.∘ var oneStart

system-images-iso : F.₁ zero-system ≅ᴹ F.₁ one-system
system-images-iso = ∘-resp-≅ᴹ
  {M₁ = F.₁ (UC.λ⇐ {X = P})} {M₁' = F.₁ (UC.λ⇐ {X = P})}
  {M₂ = Uninitialized.leaf {A = P} {B = P} zeroStart}
  {M₂' = Uninitialized.leaf {A = P} {B = P} oneStart}
  ≅ᴹ-refl uninitialized-images-iso

uninitialized-source-emulation : zero-system UC.≤UC one-system
uninitialized-source-emulation {X′} a =
  UC.≈ᵁ⇒≤UC {A = P} {X = unit} {B = P} {f = zero-system} {g = one-system}
    (Uninitialized.image-iso⇒≈ᵁ {A = P} {X = unit} {B = P}
      {f = zero-system} {g = one-system} system-images-iso) {X′ = X′} a

transported-uninitialized-emulation :
  Iso._≤UC_ {A = C} {X = F.₀ unit} {B = C} {Y = F.₀ unit}
    (Transport.G {X = unit} {A = P} {B = P} zero-system)
    (Transport.G {X = unit} {A = P} {B = P} one-system)
transported-uninitialized-emulation {X′} a =
  Transport.transfer (λ {A} y → Uninitialized.ν-epi {A = A} y) Iso.grade-stable
    {A = P} {B = P} {X = unit} {Y = unit} {f = zero-system} {g = one-system}
    uninitialized-source-emulation {X′ = X′} a
