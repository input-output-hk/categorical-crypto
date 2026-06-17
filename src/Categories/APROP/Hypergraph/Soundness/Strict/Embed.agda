{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The BOUNDARY of the strictified pipeline: `emb : HomS → HomTerm` (the
-- embedding of the presented strict SMC back into the non-strict free SMC)
-- and `emb-resp-≈ˢ` — the one-time Mac-Lane payment per strict axiom that
-- replaces the per-site M-tax of the non-strict pipeline.  Generators are
-- arbitrary HomTerms (`morL`); other generator families enter via
-- `FreeStrictSMC.Map` along their interpretation into HomTerms.
--
-- Structure: the cheap cases are proved inline; the three substantial ones
-- (`⊗-assocˢ` — the laxator associativity, `⊗-unitʳˢ`, `σ-hexˢ`) are proved
-- as standalone lemmas and instantiated in `EmbRespFull`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Embed
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal sig
  using ( cancel-mid-iso; c-iso-assoc-to; c-iso-assoc-from
        ; subst-id-dom; subst-id-cod )

open import Categories.FreeStrictSMC using (module Build)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

-- shorthands for the laxator
private
  U : List X → ObjTerm
  U = unflatten

  T : ∀ a b → HomTerm (U a ⊗₀ U b) (U (a ++ b))
  T a b = _≅_.to (unflatten-++-≅ a b)

  F : ∀ a b → HomTerm (U (a ++ b)) (U a ⊗₀ U b)
  F a b = _≅_.from (unflatten-++-≅ a b)

--------------------------------------------------------------------------------
-- The strict side: generators = arbitrary HomTerms between unflattens.

morL : List X → List X → Set
morL as bs = HomTerm (U as) (U bs)

open Build X _≟X_ morL public

--------------------------------------------------------------------------------
-- The embedding.

emb : ∀ {xs ys} → HomS xs ys → HomTerm (U xs) (U ys)
emb idˢ                              = id
emb (g ∘ˢ f)                         = emb g ∘ emb f
emb (_⊗ˢ_ {xs} {ys} {us} {vs} f g)   = T ys vs ∘ (emb f ⊗₁ emb g) ∘ F xs us
emb (genˢ t)                         = t
emb (σˢ xs ys)                       = T ys xs ∘ σ ∘ F xs ys

emb-cast
  : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys') (t : HomS xs ys)
  → emb (castˢ p q t)
    ≡ subst₂ HomTerm (cong U p) (cong U q) (emb t)
emb-cast refl refl t = refl

-- a subst₂ over `cong U` re-expressed as conjugation by transported ids
subst₂-conj
  : ∀ {a b c d} (p : a ≡ b) (q : c ≡ d) (t : HomTerm (U a) (U c))
  → subst₂ HomTerm (cong U p) (cong U q) t
    ≈Term subst-id-cod q ∘ t ∘ subst-id-dom p
subst₂-conj refl refl t = ≈-Term-sym (≈-Term-trans idˡ idʳ)

--------------------------------------------------------------------------------
-- `emb` respects `_≈ˢ_`: the cheap cases, with the three substantial ones
-- taken as parameters (proved standalone below and instantiated at the end).

module EmbResp
  (⊗-assoc-case
    : ∀ {xs ys us vs ps qs}
        (f : HomS xs ys) (g : HomS us vs) (h : HomS ps qs)
    → emb (castˢ (++-assoc xs us ps) (++-assoc ys vs qs) ((f ⊗ˢ g) ⊗ˢ h))
      ≈Term emb (f ⊗ˢ (g ⊗ˢ h)))
  (⊗-unitʳ-case
    : ∀ {xs ys} (f : HomS xs ys)
    → emb (castˢ (++-identityʳ xs) (++-identityʳ ys) (f ⊗ˢ idˢ {[]}))
      ≈Term emb f)
  (σ-hex-case
    : ∀ xs ys zs
    → emb (σˢ (xs ++ ys) zs)
      ≈Term emb (castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
                   ((σˢ xs zs ⊗ˢ idˢ {ys})
                     ∘ˢ castˢ refl (sym (++-assoc xs zs ys))
                          (idˢ {xs} ⊗ˢ σˢ ys zs))))
  (σ-unit-case
    : ∀ xs
    → emb (σˢ [] xs)
      ≈Term emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs})))
  where

  emb-resp-≈ˢ : ∀ {xs ys} {f g : HomS xs ys} → f ≈ˢ g → emb f ≈Term emb g
  emb-resp-≈ˢ ≈-refl           = ≈-Term-refl
  emb-resp-≈ˢ (≈-sym e)        = ≈-Term-sym (emb-resp-≈ˢ e)
  emb-resp-≈ˢ (≈-trans e e')   = ≈-Term-trans (emb-resp-≈ˢ e) (emb-resp-≈ˢ e')
  emb-resp-≈ˢ (∘-resp e e')    = ∘-resp-≈ (emb-resp-≈ˢ e) (emb-resp-≈ˢ e')
  emb-resp-≈ˢ (⊗-resp e e')    =
    refl⟩∘⟨ (⊗-resp-≈ (emb-resp-≈ˢ e) (emb-resp-≈ˢ e') ⟩∘⟨refl)
  emb-resp-≈ˢ idˡ              = idˡ
  emb-resp-≈ˢ idʳ              = idʳ
  emb-resp-≈ˢ assocˢ           = FM.assoc
  -- to ∘ (id ⊗ id) ∘ from  ≈  id
  emb-resp-≈ˢ (⊗-id {xs} {us}) = begin
    T xs us ∘ (id ⊗₁ id) ∘ F xs us
      ≈⟨ refl⟩∘⟨ (id⊗id≈id ⟩∘⟨refl) ⟩
    T xs us ∘ id ∘ F xs us
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    T xs us ∘ F xs us
      ≈⟨ _≅_.isoˡ (unflatten-++-≅ xs us) ⟩
    id ∎
  -- (T∘(a⊗b)∘F) ∘ (T∘(c⊗d)∘F)  ≈  T∘((a∘c)⊗(b∘d))∘F
  emb-resp-≈ˢ (interchangeˢ {xs} {ys} {zs} {us} {vs} {ws} {a} {b} {c} {d}) = begin
    (T zs ws ∘ (emb a ⊗₁ emb b) ∘ F ys vs)
      ∘ (T ys vs ∘ (emb c ⊗₁ emb d) ∘ F xs us)
      ≈⟨ cancel-mid-iso (T zs ws) (emb a ⊗₁ emb b) (F ys vs)
           (T ys vs) (emb c ⊗₁ emb d) (F xs us)
           (_≅_.isoʳ (unflatten-++-≅ ys vs)) ⟩
    T zs ws ∘ (emb a ⊗₁ emb b) ∘ (emb c ⊗₁ emb d) ∘ F xs us
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    T zs ws ∘ ((emb a ⊗₁ emb b) ∘ (emb c ⊗₁ emb d)) ∘ F xs us
      ≈⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl) ⟩
    T zs ws ∘ ((emb a ∘ emb c) ⊗₁ (emb b ∘ emb d)) ∘ F xs us ∎
  emb-resp-≈ˢ (⊗-assocˢ f g h) = ⊗-assoc-case f g h
  emb-resp-≈ˢ (⊗-unitʳˢ f)     = ⊗-unitʳ-case f
  -- (T∘σ∘F) ∘ (T∘(f⊗g)∘F)  ≈  (T∘(g⊗f)∘F) ∘ (T∘σ∘F)
  emb-resp-≈ˢ (σ-natˢ {xs} {ys} {us} {vs} {f} {g}) = begin
    (T vs ys ∘ σ ∘ F ys vs) ∘ (T ys vs ∘ (emb f ⊗₁ emb g) ∘ F xs us)
      ≈⟨ cancel-mid-iso (T vs ys) σ (F ys vs) (T ys vs)
           (emb f ⊗₁ emb g) (F xs us) (_≅_.isoʳ (unflatten-++-≅ ys vs)) ⟩
    T vs ys ∘ σ ∘ (emb f ⊗₁ emb g) ∘ F xs us
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    T vs ys ∘ (σ ∘ (emb f ⊗₁ emb g)) ∘ F xs us
      ≈⟨ refl⟩∘⟨ (σ∘[f⊗g]≈[g⊗f]∘σ ⟩∘⟨refl) ⟩
    T vs ys ∘ ((emb g ⊗₁ emb f) ∘ σ) ∘ F xs us
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    T vs ys ∘ (emb g ⊗₁ emb f) ∘ σ ∘ F xs us
      ≈⟨ ≈-Term-sym (cancel-mid-iso (T vs ys) (emb g ⊗₁ emb f) (F us xs)
           (T us xs) σ (F xs us) (_≅_.isoʳ (unflatten-++-≅ us xs))) ⟩
    (T vs ys ∘ (emb g ⊗₁ emb f) ∘ F us xs) ∘ (T us xs ∘ σ ∘ F xs us) ∎
  -- (T∘σ∘F) ∘ (T∘σ∘F)  ≈  id
  emb-resp-≈ˢ (σ-σˢ {xs} {ys}) = begin
    (T xs ys ∘ σ ∘ F ys xs) ∘ (T ys xs ∘ σ ∘ F xs ys)
      ≈⟨ cancel-mid-iso (T xs ys) σ (F ys xs) (T ys xs) σ (F xs ys)
           (_≅_.isoʳ (unflatten-++-≅ ys xs)) ⟩
    T xs ys ∘ σ ∘ σ ∘ F xs ys
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    T xs ys ∘ (σ ∘ σ) ∘ F xs ys
      ≈⟨ refl⟩∘⟨ (σ∘σ≈id ⟩∘⟨refl) ⟩
    T xs ys ∘ id ∘ F xs ys
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    T xs ys ∘ F xs ys
      ≈⟨ _≅_.isoˡ (unflatten-++-≅ xs ys) ⟩
    id ∎
  emb-resp-≈ˢ (σ-hexˢ xs ys zs) = σ-hex-case xs ys zs
  emb-resp-≈ˢ (σ-unitˢ xs)      = σ-unit-case xs

--------------------------------------------------------------------------------
-- THE CRUX: the `⊗-assocˢ` case — the laxator-associativity payment,
-- made ONCE here instead of per positional site.

private
  cast-cancel : ∀ {a b} (p : a ≡ b) → subst-id-cod p ∘ subst-id-dom p ≈Term id
  cast-cancel refl = idˡ

  -- α-conjugation of a ⊗-pair (the Mac-Lane move, once)
  α-conj
    : ∀ {A B C A' B' C'} (m : HomTerm A A') (n : HomTerm B B') (k : HomTerm C C')
    → (m ⊗₁ n) ⊗₁ k
      ≈Term α⇐ ∘ (m ⊗₁ (n ⊗₁ k)) ∘ α⇒
  α-conj m n k = begin
    (m ⊗₁ n) ⊗₁ k                       ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ ((m ⊗₁ n) ⊗₁ k)                ≈⟨ ≈-Term-sym α⇐∘α⇒≈id ⟩∘⟨refl ⟩
    (α⇐ ∘ α⇒) ∘ ((m ⊗₁ n) ⊗₁ k)        ≈⟨ FM.assoc ⟩
    α⇐ ∘ (α⇒ ∘ ((m ⊗₁ n) ⊗₁ k))        ≈⟨ refl⟩∘⟨ α-comm ⟩
    α⇐ ∘ ((m ⊗₁ (n ⊗₁ k)) ∘ α⇒)        ≈⟨ ≈-Term-sym FM.assoc ⟩
    (α⇐ ∘ (m ⊗₁ (n ⊗₁ k))) ∘ α⇒        ≈⟨ FM.assoc ⟩
    α⇐ ∘ (m ⊗₁ (n ⊗₁ k)) ∘ α⇒          ∎

⊗-assoc-case
  : ∀ {xs ys us vs ps qs}
      (f : HomS xs ys) (g : HomS us vs) (h : HomS ps qs)
  → emb (castˢ (++-assoc xs us ps) (++-assoc ys vs qs) ((f ⊗ˢ g) ⊗ˢ h))
    ≈Term emb (f ⊗ˢ (g ⊗ˢ h))
⊗-assoc-case {xs} {ys} {us} {vs} {ps} {qs} f g h =
  ≈-Term-trans
    (≡⇒≈Term (emb-cast (++-assoc xs us ps) (++-assoc ys vs qs) ((f ⊗ˢ g) ⊗ˢ h)))
    (≈-Term-trans (subst₂-conj (++-assoc xs us ps) (++-assoc ys vs qs) _) main)
  where
    A₁ = ++-assoc xs us ps
    A₂ = ++-assoc ys vs qs
    ef = emb f ; eg = emb g ; eh = emb h
    Sd₁ = subst-id-dom A₁ ; Sc₁ = subst-id-cod A₁
    Sd₂ = subst-id-dom A₂ ; Sc₂ = subst-id-cod A₂
    N   = ef ⊗₁ (eg ⊗₁ eh)

    -- E ≈ Sd₂ ∘ emb (f ⊗ (g ⊗ h)) ∘ Sc₁
    core
      : emb ((f ⊗ˢ g) ⊗ˢ h)
        ≈Term Sd₂ ∘ emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁
    core = begin
      T (ys ++ vs) qs ∘ ((T ys vs ∘ (ef ⊗₁ eg) ∘ F xs us) ⊗₁ eh) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym (≈-Term-trans idˡ idʳ)) ⟩∘⟨refl) ⟩
      T (ys ++ vs) qs ∘ ((T ys vs ∘ (ef ⊗₁ eg) ∘ F xs us) ⊗₁ (id ∘ eh ∘ id)) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ (⊗-∘-dist ⟩∘⟨refl) ⟩
      T (ys ++ vs) qs ∘ ((T ys vs ⊗₁ id) ∘ (((ef ⊗₁ eg) ∘ F xs us) ⊗₁ (eh ∘ id))) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ ⊗-∘-dist) ⟩∘⟨refl) ⟩
      T (ys ++ vs) qs ∘ ((T ys vs ⊗₁ id) ∘ ((ef ⊗₁ eg) ⊗₁ eh) ∘ (F xs us ⊗₁ id)) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (α-conj ef eg eh ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
      T (ys ++ vs) qs ∘ ((T ys vs ⊗₁ id) ∘ (α⇐ ∘ N ∘ α⇒) ∘ (F xs us ⊗₁ id)) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      T (ys ++ vs) qs ∘ (T ys vs ⊗₁ id) ∘ ((α⇐ ∘ N ∘ α⇒) ∘ (F xs us ⊗₁ id)) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
      T (ys ++ vs) qs ∘ (T ys vs ⊗₁ id) ∘ (α⇐ ∘ N ∘ α⇒) ∘ (F xs us ⊗₁ id) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
      T (ys ++ vs) qs ∘ (T ys vs ⊗₁ id) ∘ α⇐ ∘ (N ∘ α⇒) ∘ (F xs us ⊗₁ id) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
      T (ys ++ vs) qs ∘ (T ys vs ⊗₁ id) ∘ α⇐ ∘ N ∘ α⇒ ∘ (F xs us ⊗₁ id) ∘ F (xs ++ us) ps
        ≈⟨ ≈-Term-sym FM.assoc ⟩
      (T (ys ++ vs) qs ∘ (T ys vs ⊗₁ id)) ∘ α⇐ ∘ N ∘ α⇒ ∘ (F xs us ⊗₁ id) ∘ F (xs ++ us) ps
        ≈⟨ ≈-Term-sym FM.assoc ⟩
      ((T (ys ++ vs) qs ∘ (T ys vs ⊗₁ id)) ∘ α⇐) ∘ N ∘ α⇒ ∘ (F xs us ⊗₁ id) ∘ F (xs ++ us) ps
        ≈⟨ FM.assoc ⟩∘⟨refl ⟩
      (T (ys ++ vs) qs ∘ (T ys vs ⊗₁ id) ∘ α⇐) ∘ N ∘ α⇒ ∘ (F xs us ⊗₁ id) ∘ F (xs ++ us) ps
        ≈⟨ c-iso-assoc-to ys vs qs ⟩∘⟨refl ⟩
      (Sd₂ ∘ T ys (vs ++ qs) ∘ (id ⊗₁ T vs qs)) ∘ N ∘ α⇒ ∘ (F xs us ⊗₁ id) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (c-iso-assoc-from xs us ps) ⟩
      (Sd₂ ∘ T ys (vs ++ qs) ∘ (id ⊗₁ T vs qs)) ∘ N ∘ (id ⊗₁ F us ps) ∘ F xs (us ++ ps) ∘ Sc₁
        ≈⟨ FM.assoc ⟩
      Sd₂ ∘ (T ys (vs ++ qs) ∘ (id ⊗₁ T vs qs)) ∘ N ∘ (id ⊗₁ F us ps) ∘ F xs (us ++ ps) ∘ Sc₁
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      Sd₂ ∘ T ys (vs ++ qs) ∘ (id ⊗₁ T vs qs) ∘ N ∘ (id ⊗₁ F us ps) ∘ F xs (us ++ ps) ∘ Sc₁
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc ⟩
      Sd₂ ∘ T ys (vs ++ qs) ∘ ((id ⊗₁ T vs qs) ∘ N) ∘ (id ⊗₁ F us ps) ∘ F xs (us ++ ps) ∘ Sc₁
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl) ⟩
      Sd₂ ∘ T ys (vs ++ qs) ∘ ((id ∘ ef) ⊗₁ (T vs qs ∘ (eg ⊗₁ eh))) ∘ (id ⊗₁ F us ps) ∘ F xs (us ++ ps) ∘ Sc₁
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc ⟩
      Sd₂ ∘ T ys (vs ++ qs) ∘ (((id ∘ ef) ⊗₁ (T vs qs ∘ (eg ⊗₁ eh))) ∘ (id ⊗₁ F us ps)) ∘ F xs (us ++ ps) ∘ Sc₁
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist ⟩∘⟨refl) ⟩
      Sd₂ ∘ T ys (vs ++ qs) ∘ (((id ∘ ef) ∘ id) ⊗₁ ((T vs qs ∘ (eg ⊗₁ eh)) ∘ F us ps)) ∘ F xs (us ++ ps) ∘ Sc₁
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (⊗-resp-≈ (≈-Term-trans idʳ idˡ) FM.assoc ⟩∘⟨refl) ⟩
      Sd₂ ∘ T ys (vs ++ qs) ∘ (ef ⊗₁ (T vs qs ∘ (eg ⊗₁ eh) ∘ F us ps)) ∘ F xs (us ++ ps) ∘ Sc₁
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc ⟩
      Sd₂ ∘ T ys (vs ++ qs) ∘ ((ef ⊗₁ (T vs qs ∘ (eg ⊗₁ eh) ∘ F us ps)) ∘ F xs (us ++ ps)) ∘ Sc₁
        ≈⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc ⟩
      Sd₂ ∘ (T ys (vs ++ qs) ∘ (ef ⊗₁ (T vs qs ∘ (eg ⊗₁ eh) ∘ F us ps)) ∘ F xs (us ++ ps)) ∘ Sc₁ ∎

    main
      : Sc₂ ∘ emb ((f ⊗ˢ g) ⊗ˢ h) ∘ Sd₁
        ≈Term emb (f ⊗ˢ (g ⊗ˢ h))
    main = begin
      Sc₂ ∘ emb ((f ⊗ˢ g) ⊗ˢ h) ∘ Sd₁
        ≈⟨ refl⟩∘⟨ (core ⟩∘⟨refl) ⟩
      Sc₂ ∘ (Sd₂ ∘ emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁) ∘ Sd₁
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      Sc₂ ∘ Sd₂ ∘ (emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁) ∘ Sd₁
        ≈⟨ ≈-Term-sym FM.assoc ⟩
      (Sc₂ ∘ Sd₂) ∘ (emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁) ∘ Sd₁
        ≈⟨ cast-cancel A₂ ⟩∘⟨refl ⟩
      id ∘ (emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁) ∘ Sd₁
        ≈⟨ idˡ ⟩
      (emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁) ∘ Sd₁
        ≈⟨ FM.assoc ⟩
      emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁ ∘ Sd₁
        ≈⟨ refl⟩∘⟨ cast-cancel A₁ ⟩
      emb (f ⊗ˢ (g ⊗ˢ h)) ∘ id
        ≈⟨ idʳ ⟩
      emb (f ⊗ˢ (g ⊗ˢ h)) ∎

--------------------------------------------------------------------------------
-- The `⊗-unitʳˢ` case — the right-unit payment (a small induction on the
-- left block, closed by Kelly's coherence₂/₃).

open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal
  using (module Kelly's)
open Kelly's using (coherence₂; coherence₃)

private
  cast-cancel′ : ∀ {a b} (p : a ≡ b) → subst-id-dom p ∘ subst-id-cod p ≈Term id
  cast-cancel′ refl = idˡ

  -- the ρ-flavoured triangle: α⇒ ∘ ρ⇐ ≈ id ⊗ ρ⇐
  ρ⇐-tri : ∀ {A B} → α⇒ {A} {B} {unit} ∘ ρ⇐ {A ⊗₀ B} ≈Term id ⊗₁ ρ⇐
  ρ⇐-tri {A} {B} = begin
    α⇒ ∘ ρ⇐
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ (α⇒ ∘ ρ⇐)
      ≈⟨ ≈-Term-sym lem ⟩∘⟨refl ⟩
    ((id ⊗₁ ρ⇐) ∘ (id ⊗₁ ρ⇒)) ∘ (α⇒ ∘ ρ⇐)
      ≈⟨ FM.assoc ⟩
    (id ⊗₁ ρ⇐) ∘ ((id ⊗₁ ρ⇒) ∘ (α⇒ ∘ ρ⇐))
      ≈⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc ⟩
    (id ⊗₁ ρ⇐) ∘ (((id ⊗₁ ρ⇒) ∘ α⇒) ∘ ρ⇐)
      ≈⟨ refl⟩∘⟨ (coherence₂ ⟩∘⟨refl) ⟩
    (id ⊗₁ ρ⇐) ∘ (ρ⇒ ∘ ρ⇐)
      ≈⟨ refl⟩∘⟨ ρ⇒∘ρ⇐≈id ⟩
    (id ⊗₁ ρ⇐) ∘ id
      ≈⟨ idʳ ⟩
    id ⊗₁ ρ⇐ ∎
    where
      lem : (id ⊗₁ ρ⇐) ∘ (id ⊗₁ ρ⇒) ≈Term id {A ⊗₀ (B ⊗₀ unit)}
      lem = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
              (≈-Term-trans (⊗-resp-≈ idˡ ρ⇐∘ρ⇒≈id) id⊗id≈id)

  subst-cod-cons
    : ∀ {x : X} {a b} (e : a ≡ b)
    → id {Var x} ⊗₁ subst-id-cod e ≈Term subst-id-cod (cong (x ∷_) e)
  subst-cod-cons refl = id⊗id≈id

  -- T a [] ∘ ρ⇐  collapses to a pure cast
  TR : ∀ a → T a [] ∘ ρ⇐ ≈Term subst-id-cod (sym (++-identityʳ a))
  TR [] = begin
    λ⇒ ∘ ρ⇐    ≈⟨ coherence₃ ⟩∘⟨refl ⟩
    ρ⇒ ∘ ρ⇐    ≈⟨ ρ⇒∘ρ⇐≈id ⟩
    id ∎
  TR (x ∷ a) = begin
    ((id ⊗₁ T a []) ∘ α⇒) ∘ ρ⇐
      ≈⟨ FM.assoc ⟩
    (id ⊗₁ T a []) ∘ (α⇒ ∘ ρ⇐)
      ≈⟨ refl⟩∘⟨ ρ⇐-tri ⟩
    (id ⊗₁ T a []) ∘ (id ⊗₁ ρ⇐)
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (T a [] ∘ ρ⇐)
      ≈⟨ ⊗-resp-≈ idˡ (TR a) ⟩
    id ⊗₁ subst-id-cod (sym (++-identityʳ a))
      ≈⟨ subst-cod-cons (sym (++-identityʳ a)) ⟩
    subst-id-cod (cong (x ∷_) (sym (++-identityʳ a)))
      ≈⟨ ≡⇒≈Term (cong subst-id-cod
           (uipL (cong (x ∷_) (sym (++-identityʳ a)))
                 (sym (++-identityʳ (x ∷ a))))) ⟩
    subst-id-cod (sym (++-identityʳ (x ∷ a))) ∎

  -- its inverse composite, by uniqueness of inverses
  FR : ∀ a → ρ⇒ ∘ F a [] ≈Term subst-id-dom (sym (++-identityʳ a))
  FR a = begin
    ρ⇒ ∘ F a []
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ (ρ⇒ ∘ F a [])
      ≈⟨ ≈-Term-sym (cast-cancel′ (sym (++-identityʳ a))) ⟩∘⟨refl ⟩
    (subst-id-dom (sym (++-identityʳ a)) ∘ subst-id-cod (sym (++-identityʳ a)))
      ∘ (ρ⇒ ∘ F a [])
      ≈⟨ FM.assoc ⟩
    subst-id-dom (sym (++-identityʳ a))
      ∘ (subst-id-cod (sym (++-identityʳ a)) ∘ (ρ⇒ ∘ F a []))
      ≈⟨ refl⟩∘⟨ (≈-Term-sym (TR a) ⟩∘⟨refl) ⟩
    subst-id-dom (sym (++-identityʳ a)) ∘ ((T a [] ∘ ρ⇐) ∘ (ρ⇒ ∘ F a []))
      ≈⟨ refl⟩∘⟨ collapse ⟩
    subst-id-dom (sym (++-identityʳ a)) ∘ id
      ≈⟨ idʳ ⟩
    subst-id-dom (sym (++-identityʳ a)) ∎
    where
      collapse : (T a [] ∘ ρ⇐) ∘ (ρ⇒ ∘ F a []) ≈Term id
      collapse = begin
        (T a [] ∘ ρ⇐) ∘ (ρ⇒ ∘ F a [])
          ≈⟨ FM.assoc ⟩
        T a [] ∘ (ρ⇐ ∘ (ρ⇒ ∘ F a []))
          ≈⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc ⟩
        T a [] ∘ ((ρ⇐ ∘ ρ⇒) ∘ F a [])
          ≈⟨ refl⟩∘⟨ (ρ⇐∘ρ⇒≈id ⟩∘⟨refl) ⟩
        T a [] ∘ (id ∘ F a [])
          ≈⟨ refl⟩∘⟨ idˡ ⟩
        T a [] ∘ F a []
          ≈⟨ _≅_.isoˡ (unflatten-++-≅ a []) ⟩
        id ∎

⊗-unitʳ-case
  : ∀ {xs ys} (f : HomS xs ys)
  → emb (castˢ (++-identityʳ xs) (++-identityʳ ys) (f ⊗ˢ idˢ {[]}))
    ≈Term emb f
⊗-unitʳ-case {xs} {ys} f =
  ≈-Term-trans
    (≡⇒≈Term (emb-cast (++-identityʳ xs) (++-identityʳ ys) (f ⊗ˢ idˢ {[]})))
    (≈-Term-trans (subst₂-conj (++-identityʳ xs) (++-identityʳ ys) _) main)
  where
    ef = emb f
    Sd = subst-id-dom (++-identityʳ xs)
    Sc = subst-id-cod (++-identityʳ ys)

    -- ef ⊗ id_unit ≈ ρ⇐ ∘ ef ∘ ρ⇒
    pad : ef ⊗₁ id {unit} ≈Term ρ⇐ ∘ ef ∘ ρ⇒
    pad = begin
      ef ⊗₁ id
        ≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ (ef ⊗₁ id)
        ≈⟨ ≈-Term-sym ρ⇐∘ρ⇒≈id ⟩∘⟨refl ⟩
      (ρ⇐ ∘ ρ⇒) ∘ (ef ⊗₁ id)
        ≈⟨ FM.assoc ⟩
      ρ⇐ ∘ (ρ⇒ ∘ (ef ⊗₁ id))
        ≈⟨ refl⟩∘⟨ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩
      ρ⇐ ∘ (ef ∘ ρ⇒) ∎

    -- the de-cast'd embedding collapses
    main : Sc ∘ emb (f ⊗ˢ idˢ {[]}) ∘ Sd ≈Term ef
    main = begin
      Sc ∘ (T ys [] ∘ (ef ⊗₁ id) ∘ F xs []) ∘ Sd
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (pad ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
      Sc ∘ (T ys [] ∘ (ρ⇐ ∘ ef ∘ ρ⇒) ∘ F xs []) ∘ Sd
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ FM.assoc) ⟩∘⟨refl) ⟩
      Sc ∘ (T ys [] ∘ ρ⇐ ∘ (ef ∘ ρ⇒) ∘ F xs []) ∘ Sd
        ≈⟨ refl⟩∘⟨ (≈-Term-sym FM.assoc ⟩∘⟨refl) ⟩
      Sc ∘ ((T ys [] ∘ ρ⇐) ∘ (ef ∘ ρ⇒) ∘ F xs []) ∘ Sd
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ FM.assoc) ⟩∘⟨refl) ⟩
      Sc ∘ ((T ys [] ∘ ρ⇐) ∘ ef ∘ (ρ⇒ ∘ F xs [])) ∘ Sd
        ≈⟨ refl⟩∘⟨ ((TR ys ⟩∘⟨ (refl⟩∘⟨ FR xs)) ⟩∘⟨refl) ⟩
      Sc ∘ (subst-id-cod (sym (++-identityʳ ys))
             ∘ ef ∘ subst-id-dom (sym (++-identityʳ xs))) ∘ Sd
        ≈⟨ ≈-Term-sym FM.assoc ⟩
      (Sc ∘ subst-id-cod (sym (++-identityʳ ys))
             ∘ ef ∘ subst-id-dom (sym (++-identityʳ xs))) ∘ Sd
        ≈⟨ (≈-Term-sym FM.assoc) ⟩∘⟨refl ⟩
      ((Sc ∘ subst-id-cod (sym (++-identityʳ ys)))
             ∘ ef ∘ subst-id-dom (sym (++-identityʳ xs))) ∘ Sd
        ≈⟨ (cast-fold (++-identityʳ ys) ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (id ∘ ef ∘ subst-id-dom (sym (++-identityʳ xs))) ∘ Sd
        ≈⟨ idˡ ⟩∘⟨refl ⟩
      (ef ∘ subst-id-dom (sym (++-identityʳ xs))) ∘ Sd
        ≈⟨ FM.assoc ⟩
      ef ∘ (subst-id-dom (sym (++-identityʳ xs)) ∘ Sd)
        ≈⟨ refl⟩∘⟨ cast-fold′ (++-identityʳ xs) ⟩
      ef ∘ id
        ≈⟨ idʳ ⟩
      ef ∎
      where
        cast-fold : ∀ {a b} (p : a ≡ b)
                  → subst-id-cod p ∘ subst-id-cod (sym p) ≈Term id
        cast-fold refl = idˡ
        cast-fold′ : ∀ {a b} (p : a ≡ b)
                   → subst-id-dom (sym p) ∘ subst-id-dom p ≈Term id
        cast-fold′ refl = idˡ

--------------------------------------------------------------------------------
-- The `σ-hexˢ` case — the block-braiding payment.  Strategy: reduce BOTH
-- sides to the common normal form
--   N = Sc A₂ ∘ T (zs++xs) ys ∘ ((T zs xs ∘ σ) ⊗ id)
--         ∘ α⇐ ∘ (id ⊗ (σ ∘ F ys zs)) ∘ F xs (ys++zs) ∘ Sc A₁ .

import Categories.FreeSMC.SigmaBlockHexagon
  asFreeMonoidalData as SBH

private
  cast-dc : ∀ {a b} (p : a ≡ b) → subst-id-dom (sym p) ≈Term subst-id-cod p
  cast-dc refl = ≈-Term-refl

  cast-cd : ∀ {a b} (p : a ≡ b) → subst-id-dom p ≈Term subst-id-cod (sym p)
  cast-cd refl = ≈-Term-refl

  -- fold two right-framed / left-framed tensor factors under a tail W
  fold⊗ʳ
    : ∀ {A B C D E} {p : HomTerm B C} {q : HomTerm A B} {W : HomTerm E (D ⊗₀ A)}
    → (id {D} ⊗₁ p) ∘ ((id {D} ⊗₁ q) ∘ W) ≈Term (id {D} ⊗₁ (p ∘ q)) ∘ W
  fold⊗ʳ = ≈-Term-trans (≈-Term-sym FM.assoc)
             ((≈-Term-trans (≈-Term-sym ⊗-∘-dist) (⊗-resp-≈ idˡ ≈-Term-refl)) ⟩∘⟨refl)

  fold⊗ˡ
    : ∀ {A B C D E} {p : HomTerm B C} {q : HomTerm A B} {W : HomTerm E (A ⊗₀ D)}
    → (p ⊗₁ id {D}) ∘ ((q ⊗₁ id {D}) ∘ W) ≈Term ((p ∘ q) ⊗₁ id {D}) ∘ W
  fold⊗ˡ = ≈-Term-trans (≈-Term-sym FM.assoc)
             ((≈-Term-trans (≈-Term-sym ⊗-∘-dist) (⊗-resp-≈ ≈-Term-refl idˡ)) ⟩∘⟨refl)

  -- σ at a fused block, split through the laxator
  σ-split
    : ∀ xs ys zs
    → σ {U (xs ++ ys)} {U zs}
      ≈Term (id ⊗₁ T xs ys) ∘ σ {U xs ⊗₀ U ys} {U zs} ∘ (F xs ys ⊗₁ id)
  σ-split xs ys zs = begin
    σ
      ≈⟨ ≈-Term-sym idʳ ⟩
    σ ∘ id
      ≈⟨ refl⟩∘⟨ ≈-Term-sym TFid ⟩
    σ ∘ ((T xs ys ⊗₁ id) ∘ (F xs ys ⊗₁ id))
      ≈⟨ ≈-Term-sym FM.assoc ⟩
    (σ ∘ (T xs ys ⊗₁ id)) ∘ (F xs ys ⊗₁ id)
      ≈⟨ σ∘[f⊗g]≈[g⊗f]∘σ ⟩∘⟨refl ⟩
    ((id ⊗₁ T xs ys) ∘ σ) ∘ (F xs ys ⊗₁ id)
      ≈⟨ FM.assoc ⟩
    (id ⊗₁ T xs ys) ∘ σ ∘ (F xs ys ⊗₁ id) ∎
    where
      TFid : (T xs ys ⊗₁ id {U zs}) ∘ (F xs ys ⊗₁ id) ≈Term id
      TFid = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
               (≈-Term-trans (⊗-resp-≈ (_≅_.isoˡ (unflatten-++-≅ xs ys)) idˡ)
                             id⊗id≈id)

  -- L1: the cod-side laxator chain, c-iso-assoc-to re-oriented
  L1 : ∀ xs ys zs
     → T zs (xs ++ ys) ∘ (id ⊗₁ T xs ys)
       ≈Term subst-id-cod (++-assoc zs xs ys)
             ∘ T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id) ∘ α⇐
  L1 xs ys zs = begin
    T zs (xs ++ ys) ∘ (id ⊗₁ T xs ys)
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ (T zs (xs ++ ys) ∘ (id ⊗₁ T xs ys))
      ≈⟨ ≈-Term-sym (cast-cancel (++-assoc zs xs ys)) ⟩∘⟨refl ⟩
    (subst-id-cod (++-assoc zs xs ys) ∘ subst-id-dom (++-assoc zs xs ys))
      ∘ (T zs (xs ++ ys) ∘ (id ⊗₁ T xs ys))
      ≈⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ (subst-id-dom (++-assoc zs xs ys) ∘ (T zs (xs ++ ys) ∘ (id ⊗₁ T xs ys)))
      ≈⟨ refl⟩∘⟨ ≈-Term-sym (c-iso-assoc-to zs xs ys) ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ (T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id) ∘ α⇐) ∎

  -- L2: the dom-side laxator chain, c-iso-assoc-from re-oriented
  L2 : ∀ xs ys zs
     → (F xs ys ⊗₁ id {U zs}) ∘ F (xs ++ ys) zs
       ≈Term α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
             ∘ subst-id-cod (++-assoc xs ys zs)
  L2 xs ys zs = begin
    (F xs ys ⊗₁ id) ∘ F (xs ++ ys) zs
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ ((F xs ys ⊗₁ id) ∘ F (xs ++ ys) zs)
      ≈⟨ ≈-Term-sym α⇐∘α⇒≈id ⟩∘⟨refl ⟩
    (α⇐ ∘ α⇒) ∘ ((F xs ys ⊗₁ id) ∘ F (xs ++ ys) zs)
      ≈⟨ FM.assoc ⟩
    α⇐ ∘ (α⇒ ∘ ((F xs ys ⊗₁ id) ∘ F (xs ++ ys) zs))
      ≈⟨ refl⟩∘⟨ c-iso-assoc-from xs ys zs ⟩
    α⇐ ∘ ((id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
           ∘ subst-id-cod (++-assoc xs ys zs)) ∎

  -- J: the junction between the two σ-frames on the RHS
  J : ∀ xs ys zs
    → F (xs ++ zs) ys ∘ subst-id-cod (sym (++-assoc xs zs ys)) ∘ T xs (zs ++ ys)
      ≈Term (T xs zs ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ F zs ys)
  J xs ys zs = ≈-Term-sym (begin
    (T xs zs ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ F zs ys)
      ≈⟨ ≈-Term-sym FM.assoc ⟩
    ((T xs zs ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ F zs ys)
      ≈⟨ star ⟩∘⟨refl ⟩
    (F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys)
       ∘ T xs (zs ++ ys) ∘ (id ⊗₁ T zs ys)) ∘ (id ⊗₁ F zs ys)
      ≈⟨ FM.assoc ⟩
    F (xs ++ zs) ys ∘ ((subst-id-dom (++-assoc xs zs ys)
       ∘ T xs (zs ++ ys) ∘ (id ⊗₁ T zs ys)) ∘ (id ⊗₁ F zs ys))
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys)
       ∘ ((T xs (zs ++ ys) ∘ (id ⊗₁ T zs ys)) ∘ (id ⊗₁ F zs ys))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys)
       ∘ T xs (zs ++ ys) ∘ ((id ⊗₁ T zs ys) ∘ (id ⊗₁ F zs ys))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ TFfold ⟩
    F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys) ∘ T xs (zs ++ ys) ∘ id
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idʳ ⟩
    F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys) ∘ T xs (zs ++ ys)
      ≈⟨ refl⟩∘⟨ (cast-cd (++-assoc xs zs ys) ⟩∘⟨refl) ⟩
    F (xs ++ zs) ys ∘ subst-id-cod (sym (++-assoc xs zs ys)) ∘ T xs (zs ++ ys) ∎)
    where
      TFfold : (id ⊗₁ T zs ys) ∘ (id ⊗₁ F zs ys) ≈Term id
      TFfold = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                 (≈-Term-trans (⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ zs ys)))
                               id⊗id≈id)

      star : (T xs zs ⊗₁ id {U ys}) ∘ α⇐
             ≈Term F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys)
                   ∘ T xs (zs ++ ys) ∘ (id ⊗₁ T zs ys)
      star = begin
        (T xs zs ⊗₁ id) ∘ α⇐
          ≈⟨ ≈-Term-sym idˡ ⟩
        id ∘ ((T xs zs ⊗₁ id) ∘ α⇐)
          ≈⟨ ≈-Term-sym (_≅_.isoʳ (unflatten-++-≅ (xs ++ zs) ys)) ⟩∘⟨refl ⟩
        (F (xs ++ zs) ys ∘ T (xs ++ zs) ys) ∘ ((T xs zs ⊗₁ id) ∘ α⇐)
          ≈⟨ FM.assoc ⟩
        F (xs ++ zs) ys ∘ (T (xs ++ zs) ys ∘ ((T xs zs ⊗₁ id) ∘ α⇐))
          ≈⟨ refl⟩∘⟨ c-iso-assoc-to xs zs ys ⟩
        F (xs ++ zs) ys ∘ (subst-id-dom (++-assoc xs zs ys)
           ∘ T xs (zs ++ ys) ∘ (id ⊗₁ T zs ys)) ∎

private
  -- α⇒ ∘ (α⇐ ∘ W) ≈ W
  junction : ∀ {A B C D} {W : HomTerm A (B ⊗₀ (C ⊗₀ D))}
           → α⇒ ∘ (α⇐ ∘ W) ≈Term W
  junction = ≈-Term-trans (≈-Term-sym FM.assoc)
               (≈-Term-trans (α⇒∘α⇐≈id ⟩∘⟨refl) idˡ)

  tidyL : ∀ xs zs → (T zs xs ∘ σ ∘ F xs zs) ∘ T xs zs ≈Term T zs xs ∘ σ
  tidyL xs zs = begin
    (T zs xs ∘ σ ∘ F xs zs) ∘ T xs zs
      ≈⟨ FM.assoc ⟩
    T zs xs ∘ ((σ ∘ F xs zs) ∘ T xs zs)
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    T zs xs ∘ (σ ∘ (F xs zs ∘ T xs zs))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ _≅_.isoʳ (unflatten-++-≅ xs zs)) ⟩
    T zs xs ∘ (σ ∘ id)
      ≈⟨ refl⟩∘⟨ idʳ ⟩
    T zs xs ∘ σ ∎

  tidyR : ∀ ys zs → F zs ys ∘ (T zs ys ∘ σ ∘ F ys zs) ≈Term σ ∘ F ys zs
  tidyR ys zs = begin
    F zs ys ∘ (T zs ys ∘ σ ∘ F ys zs)
      ≈⟨ ≈-Term-sym FM.assoc ⟩
    (F zs ys ∘ T zs ys) ∘ (σ ∘ F ys zs)
      ≈⟨ _≅_.isoʳ (unflatten-++-≅ zs ys) ⟩∘⟨refl ⟩
    id ∘ (σ ∘ F ys zs)
      ≈⟨ idˡ ⟩
    σ ∘ F ys zs ∎

  lhs→N
    : ∀ xs ys zs
    → emb (σˢ (xs ++ ys) zs)
      ≈Term subst-id-cod (++-assoc zs xs ys)
            ∘ T (zs ++ xs) ys ∘ ((T zs xs ∘ σ) ⊗₁ id)
            ∘ α⇐ ∘ (id ⊗₁ (σ ∘ F ys zs)) ∘ F xs (ys ++ zs)
            ∘ subst-id-cod (++-assoc xs ys zs)
  lhs→N xs ys zs = begin
    T zs (xs ++ ys) ∘ σ ∘ F (xs ++ ys) zs
      ≈⟨ refl⟩∘⟨ (σ-split xs ys zs ⟩∘⟨refl) ⟩
    T zs (xs ++ ys)
      ∘ ((id ⊗₁ T xs ys) ∘ σ ∘ (F xs ys ⊗₁ id)) ∘ F (xs ++ ys) zs
      ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (SBH.σ-A⊗B-expand ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
    T zs (xs ++ ys)
      ∘ ((id ⊗₁ T xs ys)
          ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒) ∘ (F xs ys ⊗₁ id))
      ∘ F (xs ++ ys) zs
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    T zs (xs ++ ys)
      ∘ (id ⊗₁ T xs ys)
      ∘ (((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒) ∘ (F xs ys ⊗₁ id))
          ∘ F (xs ++ ys) zs)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    T zs (xs ++ ys)
      ∘ (id ⊗₁ T xs ys)
      ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
      ∘ ((F xs ys ⊗₁ id) ∘ F (xs ++ ys) zs)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ L2 xs ys zs ⟩
    T zs (xs ++ ys)
      ∘ (id ⊗₁ T xs ys)
      ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
      ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
          ∘ subst-id-cod (++-assoc xs ys zs))
      ≈⟨ ≈-Term-sym FM.assoc ⟩
    (T zs (xs ++ ys) ∘ (id ⊗₁ T xs ys))
      ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
      ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
          ∘ subst-id-cod (++-assoc xs ys zs))
      ≈⟨ L1 xs ys zs ⟩∘⟨refl ⟩
    (subst-id-cod (++-assoc zs xs ys)
       ∘ T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id) ∘ α⇐)
      ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
      ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
          ∘ subst-id-cod (++-assoc xs ys zs))
      ≈⟨ (refl⟩∘⟨ ≈-Term-sym FM.assoc) ⟩∘⟨refl ⟩
    (subst-id-cod (++-assoc zs xs ys)
       ∘ (T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id)) ∘ α⇐)
      ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
          ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
              ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    (subst-id-cod (++-assoc zs xs ys)
       ∘ (T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id)) ∘ α⇐)
      ∘ (α⇒ ∘ (((σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
          ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
              ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    (subst-id-cod (++-assoc zs xs ys)
       ∘ (T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id)) ∘ α⇐)
      ∘ (α⇒ ∘ (σ ⊗₁ id)
          ∘ ((α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
              ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
                  ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ cancel-mid-iso (subst-id-cod (++-assoc zs xs ys))
           (T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id)) α⇐ α⇒ (σ ⊗₁ id)
           ((α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
             ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
                 ∘ subst-id-cod (++-assoc xs ys zs)))
           α⇐∘α⇒≈id ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ (T (zs ++ xs) ys ∘ (T zs xs ⊗₁ id))
      ∘ (σ ⊗₁ id)
      ∘ ((α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
          ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
              ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ⊗₁ id)
          ∘ (σ ⊗₁ id)
          ∘ ((α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
              ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
                  ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ fold⊗ˡ ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ ((α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
          ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
              ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ α⇐
      ∘ (((id ⊗₁ σ) ∘ α⇒)
          ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
              ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ α⇐
      ∘ (id ⊗₁ σ)
      ∘ (α⇒ ∘ (α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
                ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ junction ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ α⇐
      ∘ (id ⊗₁ σ)
      ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
      ∘ subst-id-cod (++-assoc xs ys zs)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ fold⊗ʳ ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ α⇐
      ∘ (id ⊗₁ (σ ∘ F ys zs))
      ∘ F xs (ys ++ zs)
      ∘ subst-id-cod (++-assoc xs ys zs) ∎

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
  rhs→N xs ys zs = begin
    emb (castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
          ((σˢ xs zs ⊗ˢ idˢ {ys})
            ∘ˢ castˢ refl (sym (++-assoc xs zs ys)) (idˢ {xs} ⊗ˢ σˢ ys zs)))
      ≈⟨ ≡⇒≈Term (emb-cast (sym (++-assoc xs ys zs)) (++-assoc zs xs ys) _) ⟩
    subst₂ HomTerm (cong U (sym (++-assoc xs ys zs))) (cong U (++-assoc zs xs ys))
      (emb ((σˢ xs zs ⊗ˢ idˢ {ys})
             ∘ˢ castˢ refl (sym (++-assoc xs zs ys)) (idˢ {xs} ⊗ˢ σˢ ys zs)))
      ≈⟨ subst₂-conj (sym (++-assoc xs ys zs)) (++-assoc zs xs ys) _ ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ ((T (zs ++ xs) ys ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id) ∘ F (xs ++ zs) ys)
          ∘ emb (castˢ refl (sym (++-assoc xs zs ys)) (idˢ {xs} ⊗ˢ σˢ ys zs)))
      ∘ subst-id-dom (sym (++-assoc xs ys zs))
      ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ stepC) ⟩∘⟨refl) ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ ((T (zs ++ xs) ys ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id) ∘ F (xs ++ zs) ys)
          ∘ (subst-id-cod (sym (++-assoc xs zs ys))
              ∘ (T xs (zs ++ ys)
                  ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))))
      ∘ subst-id-dom (sym (++-assoc xs ys zs))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ cast-dc (++-assoc xs ys zs)) ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ ((T (zs ++ xs) ys ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id) ∘ F (xs ++ zs) ys)
          ∘ (subst-id-cod (sym (++-assoc xs zs ys))
              ∘ (T xs (zs ++ ys)
                  ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))))
      ∘ subst-id-cod (++-assoc xs ys zs)
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ (T (zs ++ xs) ys ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id) ∘ F (xs ++ zs) ys)
      ∘ ((subst-id-cod (sym (++-assoc xs zs ys))
           ∘ (T xs (zs ++ ys)
               ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs)))
          ∘ subst-id-cod (++-assoc xs ys zs))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ (T (zs ++ xs) ys ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id) ∘ F (xs ++ zs) ys)
      ∘ subst-id-cod (sym (++-assoc xs zs ys))
      ∘ ((T xs (zs ++ ys) ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))
          ∘ subst-id-cod (++-assoc xs ys zs))
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id) ∘ F (xs ++ zs) ys)
          ∘ subst-id-cod (sym (++-assoc xs zs ys))
          ∘ ((T xs (zs ++ ys) ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))
              ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id)
      ∘ (F (xs ++ zs) ys
          ∘ subst-id-cod (sym (++-assoc xs zs ys))
          ∘ ((T xs (zs ++ ys) ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))
              ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id)
      ∘ (F (xs ++ zs) ys
          ∘ subst-id-cod (sym (++-assoc xs zs ys))
          ∘ (T xs (zs ++ ys)
              ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))
                  ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id)
      ∘ (F (xs ++ zs) ys
          ∘ subst-id-cod (sym (++-assoc xs zs ys))
          ∘ (T xs (zs ++ ys)
              ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs))
                  ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs)))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-sym FM.assoc) ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id)
      ∘ (F (xs ++ zs) ys
          ∘ ((subst-id-cod (sym (++-assoc xs zs ys)) ∘ T xs (zs ++ ys))
              ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs))
                  ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs)))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id)
      ∘ ((F (xs ++ zs) ys
           ∘ (subst-id-cod (sym (++-assoc xs zs ys)) ∘ T xs (zs ++ ys)))
          ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs))
              ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (J xs ys zs ⟩∘⟨refl) ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id)
      ∘ (((T xs zs ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ F zs ys))
          ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs))
              ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ ∘ F xs zs) ⊗₁ id)
      ∘ (T xs zs ⊗₁ id)
      ∘ ((α⇐ ∘ (id ⊗₁ F zs ys))
          ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs))
              ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ fold⊗ˡ ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ (((T zs xs ∘ σ ∘ F xs zs) ∘ T xs zs) ⊗₁ id)
      ∘ ((α⇐ ∘ (id ⊗₁ F zs ys))
          ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs))
              ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (⊗-resp-≈ (tidyL xs zs) ≈-Term-refl ⟩∘⟨refl) ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ ((α⇐ ∘ (id ⊗₁ F zs ys))
          ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs))
              ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ α⇐
      ∘ ((id ⊗₁ F zs ys)
          ∘ ((id ⊗₁ (T zs ys ∘ σ ∘ F ys zs))
              ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs))))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ fold⊗ʳ ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ α⇐
      ∘ ((id ⊗₁ (F zs ys ∘ (T zs ys ∘ σ ∘ F ys zs)))
          ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs)))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
           (⊗-resp-≈ ≈-Term-refl (tidyR ys zs) ⟩∘⟨refl) ⟩
    subst-id-cod (++-assoc zs xs ys)
      ∘ T (zs ++ xs) ys
      ∘ ((T zs xs ∘ σ) ⊗₁ id)
      ∘ α⇐
      ∘ ((id ⊗₁ (σ ∘ F ys zs))
          ∘ (F xs (ys ++ zs) ∘ subst-id-cod (++-assoc xs ys zs))) ∎
    where
      stepC
        : emb (castˢ refl (sym (++-assoc xs zs ys)) (idˢ {xs} ⊗ˢ σˢ ys zs))
          ≈Term subst-id-cod (sym (++-assoc xs zs ys))
                ∘ (T xs (zs ++ ys)
                    ∘ (id ⊗₁ (T zs ys ∘ σ ∘ F ys zs)) ∘ F xs (ys ++ zs))
      stepC =
        ≈-Term-trans
          (≡⇒≈Term (emb-cast refl (sym (++-assoc xs zs ys)) (idˢ {xs} ⊗ˢ σˢ ys zs)))
          (≈-Term-trans
            (subst₂-conj refl (sym (++-assoc xs zs ys)) _)
            (refl⟩∘⟨ idʳ))

σ-hex-case
  : ∀ xs ys zs
  → emb (σˢ (xs ++ ys) zs)
    ≈Term emb (castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
                 ((σˢ xs zs ⊗ˢ idˢ {ys})
                   ∘ˢ castˢ refl (sym (++-assoc xs zs ys))
                        (idˢ {xs} ⊗ˢ σˢ ys zs)))
σ-hex-case xs ys zs =
  ≈-Term-trans (lhs→N xs ys zs) (≈-Term-sym (rhs→N xs ys zs))

--------------------------------------------------------------------------------
-- The `σ-unitˢ` case — unit braiding collapses to the right-unit cast.
-- `F [] xs = λ⇐` and `T [] xs = λ⇒` are DEFINITIONAL
-- (`unflatten-++-≅ [] = ≅.sym unitorˡ`), so the case is
-- `braiding-coherence-inv` + the `TR` induction from the `⊗-unitʳˢ` case.

open import Categories.Category.Monoidal.Symmetric Monoidal-FreeMonoidal
  using (Symmetric)
open import Categories.Category.Monoidal.Braided.Properties
  (Symmetric.braided Symmetric-Monoidal)
  using (braiding-coherence-inv)

σ-unit-case
  : ∀ xs
  → emb (σˢ [] xs)
    ≈Term emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs}))
σ-unit-case xs = begin
  T xs [] ∘ σ ∘ λ⇐
    ≈⟨ refl⟩∘⟨ braiding-coherence-inv ⟩
  T xs [] ∘ ρ⇐
    ≈⟨ TR xs ⟩
  subst-id-cod (sym (++-identityʳ xs))
    ≈⟨ rhs ⟨
  emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs})) ∎
  where
    rhs : emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs}))
          ≈Term subst-id-cod (sym (++-identityʳ xs))
    rhs =
      ≈-Term-trans
        (≡⇒≈Term (emb-cast refl (sym (++-identityʳ xs)) idˢ))
        (≈-Term-trans (subst₂-conj refl (sym (++-identityʳ xs)) id)
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ) idʳ))

--------------------------------------------------------------------------------
-- All sixteen cases closed.

module EmbRespFull = EmbResp ⊗-assoc-case ⊗-unitʳ-case σ-hex-case σ-unit-case
