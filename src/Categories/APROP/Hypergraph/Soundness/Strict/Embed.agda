{-# OPTIONS --safe --without-K #-}

-- Embedding the presented strict SMC into the free SMC via the unflatten laxator.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Embed
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using ( unflatten; unflatten-++-≅
        ; subst-id-dom; subst-id-cod
        ; cast-dc; cod-cancel; dom-cancel )
open import Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal sig
  using (c-iso-assoc-to; c-iso-assoc-from)
import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence sig as BC
open import Categories.Category
open import Categories.Category.Monoidal.Symmetric Monoidal-FreeMonoidal using (Symmetric)
open import Categories.Category.Monoidal.Braided.Properties
  (Symmetric.braided Symmetric-Monoidal)
  using (braiding-coherence-inv)
open import Categories.Category.Monoidal.Reasoning Monoidal-FreeMonoidal
  using (merge₁ʳ; merge₂ʳ; split₁ˡ; split₁ʳ)
open import Categories.FreeStrictSMC
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Morphism.Reasoning FreeMonoidal
open import Data.List.Properties

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

private
  U : List X → ObjTerm
  U = unflatten

  T : ∀ a b → HomTerm (U a ⊗₀ U b) (U (a ++ b))
  T a b = _≅_.to (unflatten-++-≅ a b)

  F : ∀ a b → HomTerm (U (a ++ b)) (U a ⊗₀ U b)
  F a b = _≅_.from (unflatten-++-≅ a b)

morL : List X → List X → Set
morL as bs = HomTerm (U as) (U bs)

open Build X _≟X_ morL public

emb : ∀ {xs ys} → HomS xs ys → HomTerm (U xs) (U ys)
emb idˢ                              = id
emb (g ∘ˢ f)                         = emb g ∘ emb f
emb (_⊗ˢ_ {xs} {ys} {us} {vs} f g)   = T ys vs ∘ (emb f ⊗₁ emb g) ∘ F xs us
emb (genˢ t)                         = t
emb (σˢ xs ys)                       = T ys xs ∘ σ ∘ F xs ys

emb-cast-conj
  : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys') (t : HomS xs ys)
  → emb (castˢ p q t) ≈Term subst-id-cod q ∘ emb t ∘ subst-id-dom p
emb-cast-conj refl refl t = ≈-Term-sym (≈-Term-trans idˡ idʳ)

private
  α-conjE
    : ∀ {A B C A' B' C'} (m : HomTerm A A') (n : HomTerm B B') (k : HomTerm C C')
    → (m ⊗₁ n) ⊗₁ k
      ≈Term α⇐ ∘ (m ⊗₁ (n ⊗₁ k)) ∘ α⇒
  α-conjE m n k = ⟺ (cancelˡ α⇐∘α⇒≈id) ○ (refl⟩∘⟨ α-comm)

⊗-assoc-case
  : ∀ {xs ys us vs ps qs}
      (f : HomS xs ys) (g : HomS us vs) (h : HomS ps qs)
  → emb (castˢ (++-assoc xs us ps) (++-assoc ys vs qs) ((f ⊗ˢ g) ⊗ˢ h))
    ≈Term emb (f ⊗ˢ (g ⊗ˢ h))
⊗-assoc-case {xs} {ys} {us} {vs} {ps} {qs} f g h =
  emb-cast-conj (++-assoc xs us ps) (++-assoc ys vs qs) _ ○ main
  where
    A₁ = ++-assoc xs us ps
    A₂ = ++-assoc ys vs qs
    ef = emb f ; eg = emb g ; eh = emb h
    Sd₁ = subst-id-dom A₁ ; Sc₁ = subst-id-cod A₁
    Sd₂ = subst-id-dom A₂ ; Sc₂ = subst-id-cod A₂
    N   = ef ⊗₁ (eg ⊗₁ eh)

    core : emb ((f ⊗ˢ g) ⊗ˢ h) ≈Term Sd₂ ∘ emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁
    core =
      (refl⟩∘⟨ (split₁ˡ ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ split₁ʳ) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ (α-conjE ef eg eh ⟩∘⟨refl)) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
      ○ ≈-Term-sym FM.assoc
      ○ ≈-Term-sym FM.assoc
      ○ (FM.assoc ⟩∘⟨refl)
      ○ (c-iso-assoc-to ys vs qs ⟩∘⟨refl)
      ○ (refl⟩∘⟨ refl⟩∘⟨ (c-iso-assoc-from xs us ps))
      ○ FM.assoc
      ○ (refl⟩∘⟨ FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl))
      ○ (refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
      ○ (refl⟩∘⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl))
      ○ (refl⟩∘⟨ refl⟩∘⟨ (⊗-resp-≈ (≈-Term-trans idʳ idˡ) FM.assoc ⟩∘⟨refl))
      ○ (refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
      ○ (refl⟩∘⟨ ≈-Term-sym FM.assoc)

    main : Sc₂ ∘ emb ((f ⊗ˢ g) ⊗ˢ h) ∘ Sd₁ ≈Term emb (f ⊗ˢ (g ⊗ˢ h))
    main =
      (refl⟩∘⟨ (core ⟩∘⟨refl))
      ○ (refl⟩∘⟨ pullʳ (cancelʳ (cod-cancel A₁)))
      ○ cancelˡ (cod-cancel A₂)

-- `FR` is `BridgeCoherence.ρ⇒-coh-list` read through `cast-dc`;
-- `TR` follows by uniqueness of inverses.

private
  FR : ∀ a → ρ⇒ ∘ F a [] ≈Term subst-id-dom (sym (++-identityʳ a))
  FR a = ⟺ (BC.ρ⇒-coh-list a) ○ ⟺ (cast-dc (++-identityʳ a))

  TR : ∀ a → T a [] ∘ ρ⇐ ≈Term subst-id-cod (sym (++-identityʳ a))
  TR a =
    ⟺ (cancelˡ (cod-cancel (sym (++-identityʳ a))))
    ○ (refl⟩∘⟨ (⟺ (FR a) ⟩∘⟨refl))
    ○ (refl⟩∘⟨ collapse)
    ○ idʳ
    where
      collapse : (ρ⇒ ∘ F a []) ∘ (T a [] ∘ ρ⇐) ≈Term id
      collapse = cancelInner (_≅_.isoʳ (unflatten-++-≅ a [])) ○ ρ⇒∘ρ⇐≈id

⊗-unitʳ-case
  : ∀ {xs ys} (f : HomS xs ys)
  → emb (castˢ (++-identityʳ xs) (++-identityʳ ys) (f ⊗ˢ idˢ {[]}))
    ≈Term emb f
⊗-unitʳ-case {xs} {ys} f =
  emb-cast-conj (++-identityʳ xs) (++-identityʳ ys) _ ○ main
  where
    ef = emb f
    Sd = subst-id-dom (++-identityʳ xs)
    Sc = subst-id-cod (++-identityʳ ys)

    padE : ef ⊗₁ id {unit} ≈Term ρ⇐ ∘ ef ∘ ρ⇒
    padE = ⟺ (cancelˡ ρ⇐∘ρ⇒≈id) ○ (refl⟩∘⟨ ρ⇒∘f⊗id≈f∘ρ⇒)

    main : Sc ∘ emb (f ⊗ˢ idˢ {[]}) ∘ Sd ≈Term ef
    main =
      (refl⟩∘⟨ ((refl⟩∘⟨ (padE ⟩∘⟨refl)) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ FM.assoc) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ (≈-Term-sym FM.assoc ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ FM.assoc) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((TR ys ⟩∘⟨ (refl⟩∘⟨ FR xs)) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ pullʳ (cancelʳ (dom-cancel (++-identityʳ xs))))
      ○ cancelˡ (cod-cancel (++-identityʳ ys))

-- Reduce both sides of the hexagon to the common normal form
--   N = Sc A₂ ∘ T (zs++xs) ys ∘ ((T zs xs ∘ σ) ⊗ id)
--         ∘ α⇐ ∘ (id ⊗ (σ ∘ F ys zs)) ∘ F xs (ys++zs) ∘ Sc A₁ .

private
  fold⊗ʳ
    : ∀ {A B C D E} {p : HomTerm B C} {q : HomTerm A B} {W : HomTerm E (D ⊗₀ A)}
    → (id {D} ⊗₁ p) ∘ ((id {D} ⊗₁ q) ∘ W) ≈Term (id {D} ⊗₁ (p ∘ q)) ∘ W
  fold⊗ʳ = pullˡ merge₂ʳ

  fold⊗ˡ
    : ∀ {A B C D E} {p : HomTerm B C} {q : HomTerm A B} {W : HomTerm E (A ⊗₀ D)}
    → (p ⊗₁ id {D}) ∘ ((q ⊗₁ id {D}) ∘ W) ≈Term ((p ∘ q) ⊗₁ id {D}) ∘ W
  fold⊗ˡ = pullˡ merge₁ʳ

  σ-split
    : ∀ xs ys zs
    → σ {U (xs ++ ys)} {U zs}
      ≈Term (id ⊗₁ T xs ys) ∘ σ {U xs ⊗₀ U ys} {U zs} ∘ (F xs ys ⊗₁ id)
  σ-split xs ys zs =
    ⟺ (pullˡ (⟺ σ∘[f⊗g]≈[g⊗f]∘σ)
        ○ cancelʳ (⊗-cancel (_≅_.isoˡ (unflatten-++-≅ xs ys)) idˡ))

  L1 : ∀ xs ys zs
     → T zs (xs ++ ys) ∘ (id ⊗₁ T xs ys)
       ≈Term subst-id-cod (++-assoc zs xs ys)
             ∘ T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id) ∘ α⇐
  L1 xs ys zs =
    ⟺ ( (refl⟩∘⟨ c-iso-assoc-to zs xs ys)
      ○ cancelˡ (cod-cancel (++-assoc zs xs ys)) )

  L2 : ∀ xs ys zs
     → (F xs ys ⊗₁ id {U zs}) ∘ F (xs ++ ys) zs
       ≈Term α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
             ∘ subst-id-cod (++-assoc xs ys zs)
  L2 xs ys zs =
    ⟺ ( (refl⟩∘⟨ ⟺ (c-iso-assoc-from xs ys zs))
      ○ cancelˡ α⇐∘α⇒≈id )

  J : ∀ xs ys zs
    → F (xs ++ zs) ys ∘ subst-id-cod (sym (++-assoc xs zs ys)) ∘ T xs (zs ++ ys)
      ≈Term (T xs zs ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ F zs ys)
  J xs ys zs =
    ⟺ ( ⟺ FM.assoc
      ○ (star ⟩∘⟨refl)
      ○ pullʳ (pullʳ (cancelʳ (id⊗-cancel (_≅_.isoˡ (unflatten-++-≅ zs ys))))) )
    where
      star : (T xs zs ⊗₁ id {U ys}) ∘ α⇐
             ≈Term F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys)
                   ∘ T xs (zs ++ ys) ∘ (id ⊗₁ T zs ys)
      star =
        ⟺ (cancelˡ (_≅_.isoʳ (unflatten-++-≅ (xs ++ zs) ys)))
        ○ (refl⟩∘⟨ c-iso-assoc-to xs zs ys)

private
  tidyL : ∀ xs zs → (T zs xs ∘ σ ∘ F xs zs) ∘ T xs zs ≈Term T zs xs ∘ σ
  tidyL xs zs = pullʳ (cancelʳ (_≅_.isoʳ (unflatten-++-≅ xs zs)))

  tidyR : ∀ ys zs → F zs ys ∘ (T zs ys ∘ σ ∘ F ys zs) ≈Term σ ∘ F ys zs
  tidyR ys zs = cancelˡ (_≅_.isoʳ (unflatten-++-≅ zs ys))

  lhs→N
    : ∀ xs ys zs
    → emb (σˢ (xs ++ ys) zs)
      ≈Term subst-id-cod (++-assoc zs xs ys)
            ∘ T (zs ++ xs) ys ∘ ((T zs xs ∘ σ) ⊗₁ id)
            ∘ α⇐ ∘ (id ⊗₁ (σ ∘ F ys zs)) ∘ F xs (ys ++ zs)
            ∘ subst-id-cod (++-assoc xs ys zs)
  lhs→N xs ys zs =
    (refl⟩∘⟨ (σ-split xs ys zs ⟩∘⟨refl))
    ○ (refl⟩∘⟨ ((refl⟩∘⟨ (σ-A⊗B-expand ⟩∘⟨refl)) ⟩∘⟨refl))
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ L2 xs ys zs)
    ○ ≈-Term-sym FM.assoc
    ○ (L1 xs ys zs ⟩∘⟨refl)
    ○ ((refl⟩∘⟨ ≈-Term-sym FM.assoc) ⟩∘⟨refl)
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ cancel-mid-iso α⇐∘α⇒≈id
    ○ (refl⟩∘⟨ FM.assoc) ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ fold⊗ˡ)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ α⇒∘α⇐≈id)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ fold⊗ʳ)

private
  rhs→N
    : ∀ xs ys zs
    → emb (castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
             ((σˢ xs zs ⊗ˢ idˢ {ys})
               ∘ˢ castˢ refl (sym (++-assoc xs zs ys))
                    (idˢ {xs} ⊗ˢ σˢ ys zs)))
      ≈Term subst-id-cod (++-assoc zs xs ys)
            ∘ T (zs ++ xs) ys ∘ ((T zs xs ∘ σ) ⊗₁ id)
            ∘ α⇐ ∘ (id ⊗₁ (σ ∘ F ys zs)) ∘ F xs (ys ++ zs)
            ∘ subst-id-cod (++-assoc xs ys zs)
  rhs→N xs ys zs =
    emb-cast-conj (sym (++-assoc xs ys zs)) (++-assoc zs xs ys) _
    ○ (refl⟩∘⟨ ((refl⟩∘⟨ stepC) ⟩∘⟨refl))
    ○ (refl⟩∘⟨ (refl⟩∘⟨ cast-dc (++-assoc xs ys zs)))
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-sym FM.assoc))
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (J xs ys zs ⟩∘⟨refl))
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ fold⊗ˡ)
    ○ (refl⟩∘⟨ refl⟩∘⟨ (⊗-resp-≈ (tidyL xs zs) ≈-Term-refl ⟩∘⟨refl))
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ fold⊗ʳ)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
         (⊗-resp-≈ ≈-Term-refl (tidyR ys zs) ⟩∘⟨refl))
    where
      stepC
        : emb (castˢ refl (sym (++-assoc xs zs ys)) (idˢ {xs} ⊗ˢ σˢ ys zs))
          ≈Term subst-id-cod (sym (++-assoc xs zs ys))
                ∘ (T xs (zs ++ ys)
                    ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))
      stepC = emb-cast-conj refl (sym (++-assoc xs zs ys)) _ ○ (refl⟩∘⟨ idʳ)

σ-hex-case
  : ∀ xs ys zs
  → emb (σˢ (xs ++ ys) zs)
    ≈Term emb (castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
                 ((σˢ xs zs ⊗ˢ idˢ {ys})
                   ∘ˢ castˢ refl (sym (++-assoc xs zs ys))
                        (idˢ {xs} ⊗ˢ σˢ ys zs)))
σ-hex-case xs ys zs = ≈-Term-trans (lhs→N xs ys zs) (≈-Term-sym (rhs→N xs ys zs))

-- `F [] xs = λ⇐` and `T [] xs = λ⇒` are DEFINITIONAL
-- (`unflatten-++-≅ [] = ≅.sym unitorˡ`), so the case is
-- `braiding-coherence-inv` + the `TR` induction from the `⊗-unitʳˢ` case.

σ-unit-case : ∀ xs → emb (σˢ [] xs) ≈Term emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs}))
σ-unit-case xs = begin
  T xs [] ∘ σ ∘ λ⇐
    ≈⟨ refl⟩∘⟨ braiding-coherence-inv ⟩
  T xs [] ∘ ρ⇐
    ≈⟨ TR xs ⟩
  subst-id-cod (sym (++-identityʳ xs))
    ≈⟨ emb-cast-conj refl (sym (++-identityʳ xs)) _ ○ (refl⟩∘⟨ idˡ) ○ idʳ ⟨
  emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs})) ∎

module EmbRespFull where

  emb-resp-≈ˢ : ∀ {xs ys} {f g : HomS xs ys} → f ≈ˢ g → emb f ≈Term emb g
  emb-resp-≈ˢ ≈-refl           = ≈-Term-refl
  emb-resp-≈ˢ (≈-sym e)        = ≈-Term-sym (emb-resp-≈ˢ e)
  emb-resp-≈ˢ (≈-trans e e')   = ≈-Term-trans (emb-resp-≈ˢ e) (emb-resp-≈ˢ e')
  emb-resp-≈ˢ (∘-resp e e')    = ∘-resp-≈ (emb-resp-≈ˢ e) (emb-resp-≈ˢ e')
  emb-resp-≈ˢ (⊗-resp e e')    = refl⟩∘⟨ (⊗-resp-≈ (emb-resp-≈ˢ e) (emb-resp-≈ˢ e') ⟩∘⟨refl)
  emb-resp-≈ˢ idˡ              = idˡ
  emb-resp-≈ˢ idʳ              = idʳ
  emb-resp-≈ˢ assocˢ           = FM.assoc
  emb-resp-≈ˢ (⊗-id {xs} {us}) =
    (refl⟩∘⟨ (id⊗id≈id ⟩∘⟨refl)) ○ (refl⟩∘⟨ idˡ)
    ○ _≅_.isoˡ (unflatten-++-≅ xs us)
  emb-resp-≈ˢ (interchangeˢ {xs} {ys} {zs} {us} {vs} {ws} {a} {b} {c} {d}) =
    cancel-mid-iso (_≅_.isoʳ (unflatten-++-≅ ys vs))
    ○ (refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl))
  emb-resp-≈ˢ (⊗-assocˢ f g h) = ⊗-assoc-case f g h
  emb-resp-≈ˢ (⊗-unitʳˢ f)     = ⊗-unitʳ-case f
  emb-resp-≈ˢ (σ-natˢ {xs} {ys} {us} {vs} {f} {g}) =
    cancel-mid-iso (_≅_.isoʳ (unflatten-++-≅ ys vs))
    ○ (refl⟩∘⟨ (σ∘[f⊗g]≈[g⊗f]∘σ ⟩∘⟨refl))
    ○ ≈-Term-sym (cancel-mid-iso {M₂ = σ} (_≅_.isoʳ (unflatten-++-≅ us xs)))
  emb-resp-≈ˢ (σ-σˢ {xs} {ys}) =
    cancel-mid-iso (_≅_.isoʳ (unflatten-++-≅ ys xs))
    ○ (refl⟩∘⟨ (σ∘σ≈id ⟩∘⟨refl))
    ○ (refl⟩∘⟨ idˡ)
    ○ _≅_.isoˡ (unflatten-++-≅ xs ys)
  emb-resp-≈ˢ (σ-hexˢ xs ys zs) = σ-hex-case xs ys zs
  emb-resp-≈ˢ (σ-unitˢ xs)      = σ-unit-case xs
