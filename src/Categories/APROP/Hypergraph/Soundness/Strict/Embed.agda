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

open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig using (unflatten; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal sig
  using ( cancel-mid-iso; c-iso-assoc-to; c-iso-assoc-from
        ; subst-id-dom; subst-id-cod
        ; cast-dc; cast-cancel′; cod-cancel; dom-cancel
        ; subst-cod-cons )

open import Categories.FreeStrictSMC using (module Build)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst₂)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Morphism.Reasoning FreeMonoidal
  using ( pullˡ; pullʳ; cancelˡ; cancelʳ; cancelInner; elimʳ )

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
  emb-resp-≈ˢ (⊗-resp e e')    = refl⟩∘⟨ (⊗-resp-≈ (emb-resp-≈ˢ e) (emb-resp-≈ˢ e') ⟩∘⟨refl)
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
  -- α-conjugation of a ⊗-pair (the Mac-Lane move, once)
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
    core : emb ((f ⊗ˢ g) ⊗ˢ h) ≈Term Sd₂ ∘ emb (f ⊗ˢ (g ⊗ˢ h)) ∘ Sc₁
    core = begin
      T (ys ++ vs) qs ∘ ((T ys vs ∘ (ef ⊗₁ eg) ∘ F xs us) ⊗₁ eh) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym (≈-Term-trans idˡ idʳ)) ⟩∘⟨refl) ⟩
      T (ys ++ vs) qs ∘ ((T ys vs ∘ (ef ⊗₁ eg) ∘ F xs us) ⊗₁ (id ∘ eh ∘ id)) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ (⊗-∘-dist ⟩∘⟨refl) ⟩
      T (ys ++ vs) qs ∘ ((T ys vs ⊗₁ id) ∘ (((ef ⊗₁ eg) ∘ F xs us) ⊗₁ (eh ∘ id))) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ ⊗-∘-dist) ⟩∘⟨refl) ⟩
      T (ys ++ vs) qs ∘ ((T ys vs ⊗₁ id) ∘ ((ef ⊗₁ eg) ⊗₁ eh) ∘ (F xs us ⊗₁ id)) ∘ F (xs ++ us) ps
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (α-conjE ef eg eh ⟩∘⟨refl)) ⟩∘⟨refl) ⟩
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

    main : Sc₂ ∘ emb ((f ⊗ˢ g) ⊗ˢ h) ∘ Sd₁ ≈Term emb (f ⊗ˢ (g ⊗ˢ h))
    main =
      (refl⟩∘⟨ (core ⟩∘⟨refl))
      ○ (refl⟩∘⟨ pullʳ (cancelʳ (cod-cancel A₁)))
      ○ cancelˡ (cod-cancel A₂)

--------------------------------------------------------------------------------
-- The `⊗-unitʳˢ` case — the right-unit payment (a small induction on the
-- left block, closed by Kelly's coherence₂/₃).

open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal using (module Kelly's)
open Kelly's using (coherence₂; coherence₃)

private
  -- the ρ-flavoured triangle: α⇒ ∘ ρ⇐ ≈ id ⊗ ρ⇐
  ρ⇐-tri : ∀ {A B} → α⇒ {A} {B} {unit} ∘ ρ⇐ {A ⊗₀ B} ≈Term id ⊗₁ ρ⇐
  ρ⇐-tri {A} {B} =
    ⟺ (cancelˡ lem) ○ (refl⟩∘⟨ pullˡ coherence₂) ○ elimʳ ρ⇒∘ρ⇐≈id
    where
      lem : (id ⊗₁ ρ⇐) ∘ (id ⊗₁ ρ⇒) ≈Term id {A ⊗₀ (B ⊗₀ unit)}
      lem = ≈-Term-trans (≈-Term-sym ⊗-∘-dist) (≈-Term-trans (⊗-resp-≈ idˡ ρ⇐∘ρ⇒≈id) id⊗id≈id)

  -- T a [] ∘ ρ⇐  collapses to a pure cast
  TR : ∀ a → T a [] ∘ ρ⇐ ≈Term subst-id-cod (sym (++-identityʳ a))
  TR [] = begin λ⇒ ∘ ρ⇐    ≈⟨ coherence₃ ⟩∘⟨refl ⟩ ρ⇒ ∘ ρ⇐    ≈⟨ ρ⇒∘ρ⇐≈id ⟩ id ∎
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
  FR a =
    ⟺ (cancelˡ (cast-cancel′ (sym (++-identityʳ a))))
    ○ (refl⟩∘⟨ (⟺ (TR a) ⟩∘⟨refl))
    ○ (refl⟩∘⟨ collapse)
    ○ idʳ
    where
      collapse : (T a [] ∘ ρ⇐) ∘ (ρ⇒ ∘ F a []) ≈Term id
      collapse =
        cancelInner ρ⇐∘ρ⇒≈id ○ _≅_.isoˡ (unflatten-++-≅ a [])

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
    padE : ef ⊗₁ id {unit} ≈Term ρ⇐ ∘ ef ∘ ρ⇒
    padE = ⟺ (cancelˡ ρ⇐∘ρ⇒≈id) ○ (refl⟩∘⟨ ρ⇒∘f⊗id≈f∘ρ⇒)

    -- the de-cast'd embedding collapses
    main : Sc ∘ emb (f ⊗ˢ idˢ {[]}) ∘ Sd ≈Term ef
    main =
      -- pad `ef` with the ρ-pair, slide the laxator legs onto it (`TR`/`FR`),
      -- then the two transported-identity pairs cancel.
      (refl⟩∘⟨ ((refl⟩∘⟨ (padE ⟩∘⟨refl)) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ FM.assoc) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ (≈-Term-sym FM.assoc ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((refl⟩∘⟨ FM.assoc) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ ((TR ys ⟩∘⟨ (refl⟩∘⟨ FR xs)) ⟩∘⟨refl))
      ○ (refl⟩∘⟨ pullʳ (cancelʳ (dom-cancel (++-identityʳ xs))))
      ○ cancelˡ (cod-cancel (++-identityʳ ys))

--------------------------------------------------------------------------------
-- The `σ-hexˢ` case — the block-braiding payment.  Strategy: reduce BOTH
-- sides to the common normal form
--   N = Sc A₂ ∘ T (zs++xs) ys ∘ ((T zs xs ∘ σ) ⊗ id)
--         ∘ α⇐ ∘ (id ⊗ (σ ∘ F ys zs)) ∘ F xs (ys++zs) ∘ Sc A₁ .

import Categories.FreeSMC.SigmaBlockHexagon
  asFreeMonoidalData as SBH

private
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
  σ-split xs ys zs =
    ⟺ (pullˡ (⟺ σ∘[f⊗g]≈[g⊗f]∘σ) ○ cancelʳ TFid)
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
  L1 xs ys zs =
    ⟺ ( (refl⟩∘⟨ c-iso-assoc-to zs xs ys)
      ○ cancelˡ (cod-cancel (++-assoc zs xs ys)) )

  -- L2: the dom-side laxator chain, c-iso-assoc-from re-oriented
  L2 : ∀ xs ys zs
     → (F xs ys ⊗₁ id {U zs}) ∘ F (xs ++ ys) zs
       ≈Term α⇐ ∘ (id ⊗₁ F ys zs) ∘ F xs (ys ++ zs)
             ∘ subst-id-cod (++-assoc xs ys zs)
  L2 xs ys zs =
    ⟺ ( (refl⟩∘⟨ ⟺ (c-iso-assoc-from xs ys zs))
      ○ cancelˡ α⇐∘α⇒≈id )

  -- J: the junction between the two σ-frames on the RHS
  J : ∀ xs ys zs
    → F (xs ++ zs) ys ∘ subst-id-cod (sym (++-assoc xs zs ys)) ∘ T xs (zs ++ ys)
      ≈Term (T xs zs ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ F zs ys)
  J xs ys zs =
    ⟺ ( ⟺ FM.assoc
      ○ (star ⟩∘⟨refl)
      ○ pullʳ (pullʳ (cancelʳ TFfold)) )
    where
      TFfold : (id ⊗₁ T zs ys) ∘ (id ⊗₁ F zs ys) ≈Term id
      TFfold = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                 (≈-Term-trans (⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ zs ys)))
                               id⊗id≈id)

      star : (T xs zs ⊗₁ id {U ys}) ∘ α⇐
             ≈Term F (xs ++ zs) ys ∘ subst-id-dom (++-assoc xs zs ys)
                   ∘ T xs (zs ++ ys) ∘ (id ⊗₁ T zs ys)
      star =
        ⟺ (cancelˡ (_≅_.isoʳ (unflatten-++-≅ (xs ++ zs) ys)))
        ○ (refl⟩∘⟨ c-iso-assoc-to xs zs ys)

private
  -- α⇒ ∘ (α⇐ ∘ W) ≈ W
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
    -- phase 1: split σ off the fused block, then expand it by the hexagon
    (refl⟩∘⟨ (σ-split xs ys zs ⟩∘⟨refl))
    ○ (refl⟩∘⟨ ((refl⟩∘⟨ (SBH.σ-A⊗B-expand ⟩∘⟨refl)) ⟩∘⟨refl))
    -- phase 2: reassociate onto the dom-side laxator run, then L2
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ L2 xs ys zs)
    -- phase 3: regroup onto the cod-side laxator run, then L1
    ○ ≈-Term-sym FM.assoc
    ○ (L1 xs ys zs ⟩∘⟨refl)
    -- phase 4: expose the inner α⇐/α⇒ pair and cancel it
    ○ ((refl⟩∘⟨ ≈-Term-sym FM.assoc) ⟩∘⟨refl)
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ cancel-mid-iso _ _ _ _ _ _ α⇐∘α⇒≈id
    -- phase 5: fold the left frame into (T zs xs ∘ σ) ⊗ id
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ fold⊗ˡ)
    -- phase 6: cancel the outer α-pair and fold the right frame
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
    -- phase 1: de-cast the outer cast into a conjugation by transported ids
    ≡⇒≈Term (emb-cast (sym (++-assoc xs ys zs)) (++-assoc zs xs ys) _)
    ○ subst₂-conj (sym (++-assoc xs ys zs)) (++-assoc zs xs ys) _
    -- phase 2: de-cast the inner factor (`stepC`), then merge the dom-side cast
    ○ (refl⟩∘⟨ ((refl⟩∘⟨ stepC) ⟩∘⟨refl))
    ○ (refl⟩∘⟨ (refl⟩∘⟨ cast-dc (++-assoc xs ys zs)))
    -- phase 3: reassociate the two σ-frames into one right-nested spine
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    -- phase 4: regroup the junction between the frames and discharge it by J
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-sym FM.assoc))
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (J xs ys zs ⟩∘⟨refl))
    -- phase 5: fold the left frame and tidy it to (T zs xs ∘ σ) ⊗ id
    ○ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc)
    ○ (refl⟩∘⟨ refl⟩∘⟨ fold⊗ˡ)
    ○ (refl⟩∘⟨ refl⟩∘⟨ (⊗-resp-≈ (tidyL xs zs) ≈-Term-refl ⟩∘⟨refl))
    -- phase 6: fold the right frame and tidy it to id ⊗ (σ ∘ F ys zs)
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
σ-hex-case xs ys zs = ≈-Term-trans (lhs→N xs ys zs) (≈-Term-sym (rhs→N xs ys zs))

--------------------------------------------------------------------------------
-- The `σ-unitˢ` case — unit braiding collapses to the right-unit cast.
-- `F [] xs = λ⇐` and `T [] xs = λ⇒` are DEFINITIONAL
-- (`unflatten-++-≅ [] = ≅.sym unitorˡ`), so the case is
-- `braiding-coherence-inv` + the `TR` induction from the `⊗-unitʳˢ` case.

open import Categories.Category.Monoidal.Symmetric Monoidal-FreeMonoidal using (Symmetric)
open import Categories.Category.Monoidal.Braided.Properties
  (Symmetric.braided Symmetric-Monoidal)
  using (braiding-coherence-inv)

σ-unit-case : ∀ xs → emb (σˢ [] xs) ≈Term emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs}))
σ-unit-case xs = begin
  T xs [] ∘ σ ∘ λ⇐
    ≈⟨ refl⟩∘⟨ braiding-coherence-inv ⟩
  T xs [] ∘ ρ⇐
    ≈⟨ TR xs ⟩
  subst-id-cod (sym (++-identityʳ xs))
    ≈⟨ rhs ⟨
  emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs})) ∎
  where
    rhs : emb (castˢ refl (sym (++-identityʳ xs)) (idˢ {xs})) ≈Term subst-id-cod (sym (++-identityʳ xs))
    rhs =
      ≈-Term-trans
        (≡⇒≈Term (emb-cast refl (sym (++-identityʳ xs)) idˢ))
        (≈-Term-trans (subst₂-conj refl (sym (++-identityʳ xs)) id)
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ) idʳ))

--------------------------------------------------------------------------------
-- All sixteen cases closed.

module EmbRespFull = EmbResp ⊗-assoc-case ⊗-unitʳ-case σ-hex-case σ-unit-case
