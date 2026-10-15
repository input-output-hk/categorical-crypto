{-# OPTIONS --safe --without-K #-}

-- Honest graded protocol composition closes at the canonical composite caps.
-- Errors follow absorption order; no associativity or commutativity of ⊕ is used.

open import Categories.Category.Monoidal.Core using (Monoidal)
open import Data.Product.Base
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.UC.Quantitative.Availability.Composition
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.UC.Quantitative E
open import CategoricalCrypto.UC.Quantitative.Availability E

module Serial {o ℓ e o′ ℓ′ e′ c ℓb : Level}
              (S : QUCSetup o ℓ e o′ ℓ′ e′ c ℓb) where

  open Designated S public

  private variable
    A B C′ : 𝒞.Obj
    X Y P R : ℐ.Obj
    εf εu εfs εfa εus εua : Error

  cap-compose : X ℐ.⇒ ℐ.unit → P ℐ.⇒ ℐ.unit → (X ⊗₀ P) ℐ.⇒ ℐ.unit
  cap-compose a c = λ⇒ ℐ.∘ (a ⊗₁ c)

  close-compose : (a : X ℐ.⇒ ℐ.unit) (c : P ℐ.⇒ ℐ.unit)
                  (f : A 𝒞.⇒ T₀ X B) (u : B 𝒞.⇒ T₀ P C′)
                → close (cap-compose a c) (u ∙ f)
                  𝒞.≈ sub λ⇒ 𝒞.∘ (close c u ∙ close a f)
  close-compose a c f u = let open 𝒞 in begin
    sub (λ⇒ ℐ.∘ (a ⊗₁ c)) ∘ (ext _ u ∘ f)
      ≈⟨ ⟺ sub-merge ⟩
    sub λ⇒ ∘ sub (a ⊗₁ c) ∘ ext _ u ∘ f
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    sub λ⇒ ∘ (sub (a ⊗₁ c) ∘ ext _ u) ∘ f
      ≈⟨ refl⟩∘⟨ (⟺ sub-commute) ⟩∘⟨refl ⟩
    sub λ⇒ ∘ (ext ℐ.unit (sub c ∘ u) ∘ sub a) ∘ f
      ≈⟨ refl⟩∘⟨ assoc ⟩
    sub λ⇒ ∘ (close c u ∙ close a f) ∎

  availability-compose : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                          {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                          {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                          {u : B 𝒞.⇒ T₀ P C′} {v : B 𝒞.⇒ T₀ R C′}
                        → Availability εf a b f g → Availability εu c d u v
                        → Availability (εu ⊕ εf) (cap-compose a c) (cap-compose b d)
                            (u ∙ f) (v ∙ g)
  availability-compose {a = a} {b} {c} {d} {f} {g} {u} {v} hf hu =
    ctx-resp (𝒞.Equiv.sym (close-compose a c f u))
             (𝒞.Equiv.sym (close-compose b d g v))
      (ctx-sub λ⇒ (ctx-trans (ctx-pre (close a f) hu) (ctx-ext (close d v) hf)))

  secure-compose : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                    {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                    {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                    {u : B 𝒞.⇒ T₀ P C′} {v : B 𝒞.⇒ T₀ R C′}
                  → SecureAvailable εfs εfa a b f g → SecureAvailable εus εua c d u v
                  → SecureAvailable (εus ⊕ εfs) (εua ⊕ εfa)
                      (cap-compose a c) (cap-compose b d) (u ∙ f) (v ∙ g)
  secure-compose (secure-available (s , hs) ha) (secure-available (t , ht) hb) =
    secure-available ((ℐ.id ⊗₁ t) ℐ.∘ (s ⊗₁ ℐ.id) , at-compose hs ht)
                     (availability-compose ha hb)

  availability-compose-cap : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                              {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                              {ac : (X ⊗₀ P) ℐ.⇒ ℐ.unit} {bd : (Y ⊗₀ R) ℐ.⇒ ℐ.unit}
                              {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                              {u : B 𝒞.⇒ T₀ P C′} {v : B 𝒞.⇒ T₀ R C′}
                            → ac ℐ.≈ cap-compose a c → bd ℐ.≈ cap-compose b d
                            → Availability εf a b f g → Availability εu c d u v
                            → Availability (εu ⊕ εf) ac bd (u ∙ f) (v ∙ g)
  availability-compose-cap {f = f} {g} {u} {v} ac bd hf hu =
    ctx-resp (close-resp-cap (u ∙ f) (ℐ.Equiv.sym ac))
             (close-resp-cap (v ∙ g) (ℐ.Equiv.sym bd)) (availability-compose hf hu)

  secure-compose-cap : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                        {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                        {ac : (X ⊗₀ P) ℐ.⇒ ℐ.unit} {bd : (Y ⊗₀ R) ℐ.⇒ ℐ.unit}
                        {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                        {u : B 𝒞.⇒ T₀ P C′} {v : B 𝒞.⇒ T₀ R C′}
                      → ac ℐ.≈ cap-compose a c → bd ℐ.≈ cap-compose b d
                      → SecureAvailable εfs εfa a b f g → SecureAvailable εus εua c d u v
                      → SecureAvailable (εus ⊕ εfs) (εua ⊕ εfa) ac bd (u ∙ f) (v ∙ g)
  secure-compose-cap ac bd (secure-available (s , hs) ha) (secure-available (t , ht) hb) =
    secure-available ((ℐ.id ⊗₁ t) ℐ.∘ (s ⊗₁ ℐ.id) , at-compose hs ht)
                     (availability-compose-cap ac bd ha hb)

  mode-compose : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                  {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                  {s : Y ℐ.⇒ X} {t : R ℐ.⇒ P}
                → a ℐ.∘ s ℐ.≈ b → c ℐ.∘ t ℐ.≈ d
                → cap-compose a c ℐ.∘ ((ℐ.id ⊗₁ t) ℐ.∘ (s ⊗₁ ℐ.id))
                  ℐ.≈ cap-compose b d
  mode-compose {a = a} {c = c} {s = s} {t = t} hs ht =
    let open ℐ using (_∘_; id; assoc; identityˡ; identityʳ); open ℐ.HomReasoning in begin
    (λ⇒ ∘ (a ⊗₁ c)) ∘ ((id ⊗₁ t) ∘ (s ⊗₁ id))
      ≈⟨ assoc ⟩
    λ⇒ ∘ ((a ⊗₁ c) ∘ ((id ⊗₁ t) ∘ (s ⊗₁ id)))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⟺ ℐ.⊗.homomorphism) ⟩
    λ⇒ ∘ ((a ⊗₁ c) ∘ ((id ∘ s) ⊗₁ (t ∘ id)))
      ≈⟨ refl⟩∘⟨ ⟺ ℐ.⊗.homomorphism ⟩
    λ⇒ ∘ ((a ∘ (id ∘ s)) ⊗₁ (c ∘ (t ∘ id)))
      ≈⟨ refl⟩∘⟨ ℐ.⊗.F-resp-≈ ((refl⟩∘⟨ identityˡ ○ hs) , (refl⟩∘⟨ identityʳ ○ ht)) ⟩
    cap-compose _ _ ∎

module Parallel {o ℓ e o′ ℓ′ e′ c ℓb : Level}
                (S : QUCSetup o ℓ e o′ ℓ′ e′ c ℓb)
                (M : Monoidal (QUCSetup.𝒞 S)) where

  open Serial S public
  private module M = Monoidal M

  private variable
    A B C′ D : 𝒞.Obj
    X Y P R : ℐ.Obj
    ε δ εfs εfa εus εua : Error

  record Pairing : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb) where
    field
      χ : {X P : ℐ.Obj} {B D : 𝒞.Obj}
        → (T₀ X B M.⊗₀ T₀ P D) 𝒞.⇒ T₀ (X ⊗₀ P) (B M.⊗₀ D)
      χ-sub : {B D : 𝒞.Obj} (s : Y ℐ.⇒ X) (t : R ℐ.⇒ P)
            → sub (s ⊗₁ t) 𝒞.∘ χ {B = B} {D = D} 𝒞.≈ χ 𝒞.∘ (sub s M.⊗₁ sub t)

    pair : (A 𝒞.⇒ T₀ X B) → (C′ 𝒞.⇒ T₀ P D)
         → (A M.⊗₀ C′) 𝒞.⇒ T₀ (X ⊗₀ P) (B M.⊗₀ D)
    pair f u = χ 𝒞.∘ (f M.⊗₁ u)

    field
      action-left : {f g : A 𝒞.⇒ T₀ X B} (u : C′ 𝒞.⇒ T₀ P D)
                  → f ≈ᵁ[ ε ] g → pair f u ≈ᵁ[ ε ] pair g u
      action-right : (f : A 𝒞.⇒ T₀ X B) {u v : C′ 𝒞.⇒ T₀ P D}
                   → u ≈ᵁ[ ε ] v → pair f u ≈ᵁ[ ε ] pair f v

  module Laws (K : Pairing) where
    open Pairing K public

    pair-sub : (s : Y ℐ.⇒ X) (t : R ℐ.⇒ P)
               (g : A 𝒞.⇒ T₀ Y B) (v : C′ 𝒞.⇒ T₀ R D)
             → sub (s ⊗₁ t) 𝒞.∘ pair g v
               𝒞.≈ pair (sub s 𝒞.∘ g) (sub t 𝒞.∘ v)
    pair-sub s t g v = let open 𝒞 in begin
      sub (s ⊗₁ t) ∘ (χ ∘ (g M.⊗₁ v))
        ≈⟨ sym-assoc ⟩
      (sub (s ⊗₁ t) ∘ χ) ∘ (g M.⊗₁ v)
        ≈⟨ χ-sub s t ⟩∘⟨refl ⟩
      (χ ∘ (sub s M.⊗₁ sub t)) ∘ (g M.⊗₁ v)
        ≈⟨ assoc ⟩
      χ ∘ ((sub s M.⊗₁ sub t) ∘ (g M.⊗₁ v))
        ≈⟨ refl⟩∘⟨ 𝒞.Equiv.sym M.⊗.homomorphism ⟩
      pair (sub s ∘ g) (sub t ∘ v) ∎

    ctx-parallel : {f g : A 𝒞.⇒ T₀ X B} {u v : C′ 𝒞.⇒ T₀ P D}
                 → f ≈ᵁ[ ε ] g → u ≈ᵁ[ δ ] v → pair f u ≈ᵁ[ ε ⊕ δ ] pair g v
    ctx-parallel {g = g} {u = u} hf hu =
      ctx-trans (action-left u hf) (action-right g hu)

    at-parallel : {s : Y ℐ.⇒ X} {t : R ℐ.⇒ P}
                  {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                  {u : C′ 𝒞.⇒ T₀ P D} {v : C′ 𝒞.⇒ T₀ R D}
                → At s ε f g → At t δ u v → At (s ⊗₁ t) (ε ⊕ δ) (pair f u) (pair g v)
    at-parallel {s = s} {t} {g = g} {v = v} hf hu =
      ctx-resp 𝒞.Equiv.refl (𝒞.Equiv.sym (pair-sub s t g v)) (ctx-parallel hf hu)

    close-parallel : (a : X ℐ.⇒ ℐ.unit) (c : P ℐ.⇒ ℐ.unit)
                     (f : A 𝒞.⇒ T₀ X B) (u : C′ 𝒞.⇒ T₀ P D)
                   → close (cap-compose a c) (pair f u)
                     𝒞.≈ sub λ⇒ 𝒞.∘ pair (close a f) (close c u)
    close-parallel a c f u = let open 𝒞 in begin
      sub (λ⇒ ℐ.∘ (a ⊗₁ c)) ∘ pair f u
        ≈⟨ ⟺ sub-merge ⟩
      sub λ⇒ ∘ sub (a ⊗₁ c) ∘ pair f u
        ≈⟨ refl⟩∘⟨ pair-sub a c f u ⟩
      sub λ⇒ ∘ pair (close a f) (close c u) ∎

    availability-parallel : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                            {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                            {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                            {u : C′ 𝒞.⇒ T₀ P D} {v : C′ 𝒞.⇒ T₀ R D}
                          → Availability ε a b f g → Availability δ c d u v
                          → Availability (ε ⊕ δ) (cap-compose a c) (cap-compose b d)
                              (pair f u) (pair g v)
    availability-parallel {a = a} {b} {c} {d} {f} {g} {u} {v} hf hu =
      ctx-resp (𝒞.Equiv.sym (close-parallel a c f u))
               (𝒞.Equiv.sym (close-parallel b d g v)) (ctx-sub λ⇒ (ctx-parallel hf hu))

    secure-parallel : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                      {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                      {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                      {u : C′ 𝒞.⇒ T₀ P D} {v : C′ 𝒞.⇒ T₀ R D}
                    → SecureAvailable εfs εfa a b f g → SecureAvailable εus εua c d u v
                    → SecureAvailable (εfs ⊕ εus) (εfa ⊕ εua)
                        (cap-compose a c) (cap-compose b d) (pair f u) (pair g v)
    secure-parallel (secure-available (s , hs) ha) (secure-available (t , ht) hb) =
      secure-available (s ⊗₁ t , at-parallel hs ht) (availability-parallel ha hb)

    availability-parallel-cap : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                                {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                                {ac : (X ⊗₀ P) ℐ.⇒ ℐ.unit} {bd : (Y ⊗₀ R) ℐ.⇒ ℐ.unit}
                                {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                                {u : C′ 𝒞.⇒ T₀ P D} {v : C′ 𝒞.⇒ T₀ R D}
                              → ac ℐ.≈ cap-compose a c → bd ℐ.≈ cap-compose b d
                              → Availability ε a b f g → Availability δ c d u v
                              → Availability (ε ⊕ δ) ac bd (pair f u) (pair g v)
    availability-parallel-cap {f = f} {g} {u} {v} ac bd hf hu =
      ctx-resp (close-resp-cap (pair f u) (ℐ.Equiv.sym ac))
               (close-resp-cap (pair g v) (ℐ.Equiv.sym bd)) (availability-parallel hf hu)

    secure-parallel-cap : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                          {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                          {ac : (X ⊗₀ P) ℐ.⇒ ℐ.unit} {bd : (Y ⊗₀ R) ℐ.⇒ ℐ.unit}
                          {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                          {u : C′ 𝒞.⇒ T₀ P D} {v : C′ 𝒞.⇒ T₀ R D}
                        → ac ℐ.≈ cap-compose a c → bd ℐ.≈ cap-compose b d
                        → SecureAvailable εfs εfa a b f g → SecureAvailable εus εua c d u v
                        → SecureAvailable (εfs ⊕ εus) (εfa ⊕ εua) ac bd (pair f u) (pair g v)
    secure-parallel-cap ac bd (secure-available (s , hs) ha) (secure-available (t , ht) hb) =
      secure-available (s ⊗₁ t , at-parallel hs ht) (availability-parallel-cap ac bd ha hb)

    mode-parallel : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                    {c : P ℐ.⇒ ℐ.unit} {d : R ℐ.⇒ ℐ.unit}
                    {s : Y ℐ.⇒ X} {t : R ℐ.⇒ P}
                  → a ℐ.∘ s ℐ.≈ b → c ℐ.∘ t ℐ.≈ d
                  → cap-compose a c ℐ.∘ (s ⊗₁ t) ℐ.≈ cap-compose b d
    mode-parallel hs ht =
      ℐ.Equiv.trans ℐ.assoc
        (ℐ.∘-resp-≈ʳ (ℐ.Equiv.trans (ℐ.Equiv.sym ℐ.⊗.homomorphism) (ℐ.⊗.F-resp-≈ (hs , ht))))
