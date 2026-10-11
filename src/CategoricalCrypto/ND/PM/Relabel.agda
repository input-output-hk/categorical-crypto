{-# OPTIONS --safe --without-K --guardedness #-}

open import Categories.Category.Monoidal.Bundle

open import Data.List.Base using (List; []; _++_)
open import Data.Product.Base using (_,_)

import CategoricalCrypto.ND.A as A
import CategoricalCrypto.ND.Grade as Grade
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.PM.Factor.Read
open import CategoricalCrypto.ND.PM.Read
open import CategoricalCrypto.ND.PM.Relabel.Regroup
open import CategoricalCrypto.ND.PM.Relabel.Wire
open import CategoricalCrypto.ND.Relabel
open import CategoricalCrypto.UC.Model.Symmetric

module CategoricalCrypto.ND.PM.Relabel where

private
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module B = Grade 𝔾ˢ C
  module N = A 𝔾ˢ C
  variable S⃗ T⃗ U⃗ S⃗′ T⃗′ : List Set

⌈_⌉ʳᴾ : S⃗ ⇝ T⃗ → B.C⟦ T⃗ ⟧ G.⇒ B.C⟦ S⃗ ⟧
⌈_⌉ʳᴾ {S⃗} {T⃗} ρ = conjugate (flat T⃗) (flat S⃗) (wireᴾ ρ)

reads-relabel : (ρ : S⃗ ⇝ T⃗) → Reads (flat T⃗) (flat S⃗) ⌈ ρ ⌉ʳᴾ (wireᴾ ρ)
reads-relabel {S⃗} {T⃗} ρ = reads-conjugate (flat T⃗) (flat S⃗) (wireᴾ ρ)

⌈⌉ʳᴾ-id : ⌈ idʳ {S⃗} ⌉ʳᴾ G.≈ G.id
⌈⌉ʳᴾ-id {S⃗} = reads⇒≈ {x = flat S⃗} {y = flat S⃗}
  (reads-resp {x = flat S⃗} {y = flat S⃗} G.Equiv.refl (wireᴾ-id {S⃗}) (reads-relabel {S⃗} {S⃗} (idʳ {S⃗}))) (reads-id (flat S⃗))

⌈⌉ʳᴾ-resp : {ρ ρ′ : S⃗ ⇝ T⃗} → ρ ≈ʳ ρ′ → ⌈ ρ ⌉ʳᴾ G.≈ ⌈ ρ′ ⌉ʳᴾ
⌈⌉ʳᴾ-resp {S⃗} {T⃗} {ρ} {ρ′} e = reads⇒≈ {x = flat T⃗} {y = flat S⃗}
  (reads-resp {x = flat T⃗} {y = flat S⃗} G.Equiv.refl (wireᴾ-resp e) (reads-relabel ρ)) (reads-relabel ρ′)

⌈⌉ʳᴾ-∘ : (ρ′ : T⃗ ⇝ U⃗) (ρ : S⃗ ⇝ T⃗) → ⌈ ρ′ ∘ʳ ρ ⌉ʳᴾ G.≈ ⌈ ρ ⌉ʳᴾ G.∘ ⌈ ρ′ ⌉ʳᴾ
⌈⌉ʳᴾ-∘ {T⃗} {U⃗} {S⃗} ρ′ ρ = reads⇒≈ {x = flat U⃗} {y = flat S⃗}
  (reads-resp {x = flat U⃗} {y = flat S⃗} G.Equiv.refl (wireᴾ-∘ ρ′ ρ) (reads-relabel (ρ′ ∘ʳ ρ)))
  (reads-∘ {x = flat U⃗} {y = flat T⃗} {z = flat S⃗} (reads-relabel ρ) (reads-relabel ρ′))

⌈⌉ʳᴾ-++ : (ρ : S⃗ ⇝ T⃗) (ρ′ : S⃗′ ⇝ T⃗′)
          → ⌈ ρ ++ʳ ρ′ ⌉ʳᴾ G.≈ B.C++.from S⃗ S⃗′ G.∘ (⌈ ρ ⌉ʳᴾ G.⊗₁ ⌈ ρ′ ⌉ʳᴾ) G.∘ B.C++.to T⃗ T⃗′
⌈⌉ʳᴾ-++ {S⃗} {T⃗} {S⃗′} {T⃗′} ρ ρ′ = reads⇒≈ {x = flat (T⃗ ++ T⃗′)} {y = flat (S⃗ ++ S⃗′)}
  (reads-resp {x = flat (T⃗ ++ T⃗′)} {y = flat (S⃗ ++ S⃗′)} G.Equiv.refl (wireᴾ-++ ρ ρ′) (reads-relabel (ρ ++ʳ ρ′)))
  (reads-∘ {x = flat (T⃗ ++ T⃗′)} {y = flat S⃗ ⊗ᶠ flat S⃗′} {z = flat (S⃗ ++ S⃗′)} (reads-C++ S⃗ S⃗′)
    (reads-∘ {x = flat (T⃗ ++ T⃗′)} {y = flat T⃗ ⊗ᶠ flat T⃗′} {z = flat S⃗ ⊗ᶠ flat S⃗′}
      (reads-⊗ {x = flat T⃗} {y = flat S⃗} {z = flat T⃗′} {w = flat S⃗′} (reads-relabel ρ) (reads-relabel ρ′))
      (reads-C++⁻¹ T⃗ T⃗′)))

relabelling : N.Relabelling
relabelling = record
  { ⌈_⌉ = ⌈_⌉ʳᴾ
  ; ⌈⌉-id = λ {S⃗} → ⌈⌉ʳᴾ-id {S⃗}
  ; ⌈⌉-∘ = λ {S⃗} {T⃗} {U⃗} → ⌈⌉ʳᴾ-∘ {T⃗} {U⃗} {S⃗}
  ; ⌈⌉-++ = λ {S⃗} {T⃗} {S⃗′} {T⃗′} → ⌈⌉ʳᴾ-++ {S⃗} {T⃗} {S⃗′} {T⃗′}
  ; unit⇒ = λ S⃗ → unit⇒ʳ S⃗ , reads⇒≈ {x = flat (S⃗ ++ [])} {y = flat S⃗} (reads-relabel (unit⇒ʳ S⃗)) (reads-unit⇒ S⃗)
  ; unit⇐ = λ S⃗ → unit⇐ʳ S⃗ , reads⇒≈ {x = flat S⃗} {y = flat (S⃗ ++ [])} (reads-relabel (unit⇐ʳ S⃗)) (reads-unit⇐ S⃗)
  ; assoc⇒ = λ S⃗ T⃗ U⃗ → assoc⇒ʳ S⃗ T⃗ U⃗ , reads⇒≈ {x = flat ((S⃗ ++ T⃗) ++ U⃗)} {y = flat (S⃗ ++ (T⃗ ++ U⃗))}
      (reads-relabel (assoc⇒ʳ S⃗ T⃗ U⃗)) (reads-assoc⇒ S⃗ T⃗ U⃗)
  ; assoc⇐ = λ S⃗ T⃗ U⃗ → assoc⇐ʳ S⃗ T⃗ U⃗ , reads⇒≈ {x = flat (S⃗ ++ (T⃗ ++ U⃗))} {y = flat ((S⃗ ++ T⃗) ++ U⃗)}
      (reads-relabel (assoc⇐ʳ S⃗ T⃗ U⃗)) (reads-assoc⇐ S⃗ T⃗ U⃗) }
