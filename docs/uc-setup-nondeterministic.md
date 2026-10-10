# Nondeterministic choice: the scheduler in the grade

Plan, 2026-10-10; replaces the 2026-10-09 plan of the same name (image equality over `Sched → Dist⊥ Bool`,
in git history at `7d722e1f`).  Nothing here is typechecked.  Every claim about a module that does not
exist is a design claim; `[INFERENCE]` marks what was reasoned and not checked.  Line references are to
`uc-setup-landscape` at `cf7c0db0`.  Names are those of `docs/uc-models.typ` (PM, SSP, PM[wb], 𝒲, SSPᵈ,
ND_A, ND_B; §4 there, `sec:nd`, is the mathematical statement this plan implements).

## 0. Summary

(outline; filled below)

## 1. The generic construction: restriction along a monoidal functor of grades

### 1.1 The restricted setup

For a setup 𝕊 = (𝒞, ℐ, ℳ, ℰ) and a lax monoidal functor ι : 𝒥 → ℐ (structure ι_ε : I → ιI,
ι₂ : ιW ⊗ ιX → ι(W ⊗ X)), the **restriction of 𝕊 along ι** is

  𝕊|ι := (𝒞, 𝒥, ℳ ∘ ι, ℰ),

with the graded monad pulled back (`Categories/Monad/Graded/Pullback.agda:32`, `pullbackM = ∘-Monoidal ℳ ι`):
T′_X = T_{ιX}, sub′_c = sub_{ιc}, η′ = sub_{ι_ε} ∘ η, μ′_{W,X} = sub_{ι₂} ∘ μ_{ιW,ιX}.  Computations, tests
and the kernel ≈ℰ are 𝕊's; a protocol of 𝕊|ι at grade X *is* a protocol of 𝕊 at grade ιX.  Only the
adversaries, the simulators and the ancillas are cut down to ι's image.

The standard case is `Std(𝕄, ℰ)|ι` for ι : 𝕄′ → 𝕄: 𝒞 = |𝕄|, ℐ = 𝕄′, T′_X B = ιX ⊗ B, an adversary
a ∈ 𝕄′(X, X′) acts as ιa ⊗ id, and μ′ = (ι₂ ⊗ id) ∘ α⁻¹.  Typical ι: the inclusion of a monoidal
subcategory of grades, not necessarily full (ND_A; efficient simulators) nor wide (the adversary-free
setup of §1.3(e)), or a functor that names structure on grades (ND_B's designated choice factors, §2.2).

### 1.2 The inclusion morphism

`inclusion : UCSetupMorphism (𝕊|ι) 𝕊` is (F = Id, Φ = ι, κ = id, ν = `idᵛ ℰ`).  Its κ-laws are the
pullback's defining equations: κ-sub and κ-return are `pullback-sub`/`pullback-return` (`refl`,
`Pullback.agda:46-50`), κ-ext is `pullback-ext` (`:52`).  The action on protocols is G f = id ∘ f ≈ f, and
ν is Epi and Mono (`Categories/Functor/Presheaf/Morphism.agda:155-159`).

### 1.3 Theorem: what the inclusion preserves and reflects

Let f : A → T_{ιX} B and g : A → T_{ιY} B be protocols of 𝕊|ι; ≈ᵁ|ι and ≤UC|ι are 𝕊|ι's relations.

- **(a) ≈ᵁ ⊆ ≈ᵁ|ι, always.**  𝕊|ι quantifies over the ancillas ιW only, and μ′ = sub_{ι₂} ∘ μ only
  post-composes, which ≈ℰ respects (`≈ℰ-cong-post`).
- **(b) ≈ᵁ|ι ⊆ ≈ᵁ when ι is essentially surjective with split comparisons** (every ι₂ has a retraction;
  a strong ι supplies `⊗-homo.⇐`).  Cancel sub_{ι₂} by sub of the retraction, then move the ancilla
  along φ : ιW′ ≅ W:  prefix_W f = sub_{φ ⊗ id} ∘ prefix_{ιW′} f ∘ sub_{φ⁻¹}, by `sub-commute′` and
  `μ-sub-commute` (`FromMonad.agda:87-91`).  The curried-tensor instance of this conjugation is
  `Standard2/Morphism.agda:82` `conj`, used by `surjective⇒preserves-≈ᵁ` (`:97`).  "W a retract of some
  ιW′" suffices (the same computation with r ∘ s = id).  Under (b) the U-kernels coincide on 𝕊|ι's
  protocols; when ι is bijective on objects and strict (a wide monoidal subcategory) they are literally
  one relation, with no conjugation.
- **(c) Preservation under (b).**  f ≤UC|ι g ⇒ f ≤UC g: the dummy simulator s₀ ∈ 𝒥(Y, X) of the
  hypothesis gives f ≈ᵁ sub_{ιs₀} ∘ g by (b), and `dummy-complete` (`Abstract2.agda:156`) gives the
  simulator a ∘ ιs₀ for each a : ιX → X″.  No `GradeStable`, no Epi.
- **(d) Preservation for every ι when 𝕊 is grade-stable.**  𝕊|ι is then grade-stable (T′_Y = T_{ιY}), and
  f ≈ᵁ|ι g ⇒ f ≈ℰ g ⇒ f ≈ᵁ g by `bridge` (`Abstract2.agda:124`).  This is
  `Transfer.transfer inclusion idᵛ-epi gs` (`Abstract2/Morphism.agda:75`), the route the causal-boxes
  sketch takes.
- **(e) Without (b) or (d) preservation fails.**  Take ι : `Oneᴹ` → ℐ, the unit (`Oneᴹ` is
  `Categories/Monad/Graded/Trivial.agda:24`).  𝕊|ι is the adversary-free setup: one ancilla and one
  simulator, so ≈ᵁ|ι and ≤UC|ι are ≈ℰ on unit-graded protocols.  At PM the reveal pair
  r_true ≈ℰ r_false (`UC/RandomSystems/FullAbstraction.agda:186`) is ≤UC|ι, while r_true ≰UC r_false: a
  simulator I → I has the empty interface, so sub_s ∘ r_false still never sends `true`, and ≈ᵁ ⇒ ≈ᴿ
  separates the two [INFERENCE: that every s : I → I of 𝔾ᵒ is inert].
- **(f) Reflection when ι is full.**  f ≤UC g ⇒ f ≤UC|ι g: take 𝕊's dummy simulator s₀ ∈ ℐ(ιY, ιX), a
  preimage s₀′ with ιs₀′ ≈ s₀, and (a).  No grade stability, κ-mono or ν-mono:
  `Abstract2/Morphism.agda:90` `reflects-≤UC` needs all three because it rebuilds the source U-kernel
  from a ≈ℰ; here (a) gives it directly.
- **(g) Without fullness reflection fails**; ND_A → ND_B is the witness (§4).

So a full, essentially surjective, strong ι changes nothing about ≤UC (ND_B, §2.2); a wide strict non-full
ι preserves and does not reflect (ND_A ⊆ ND_B; efficient simulators); a non-essentially-surjective ι
coarsens ≈ᵁ, and preservation then needs grade stability.

### 1.4 Between two restrictions

For a second ι′ : 𝒥′ → ℐ, a monoidal j : 𝒥 → 𝒥′ and a monoidal natural iso θ : ι′ ∘ j ≅ ι
(`Categories.NaturalTransformation.NaturalIsomorphism.Monoidal`), `between j θ : 𝕊|ι → 𝕊|ι′` is
(Id, j, sub_{θ⁻¹}, `idᵛ ℰ`); its κ-laws are `pullback-∘-return`/`pullback-∘-ext` (`Pullback.agda:90-99`)
plus θ's monoidality.  The theorem carries over with "essential image of ι" in place of "all of ℐ":
the U-kernels agree when ι and ι′ have the same essential image on objects (split comparisons), and
full j reflects.  §4 needs it once, for the way back B → A.

### 1.5 The module

`src/CategoricalCrypto/Abstract2/Regrade.agda`, beside its dual `Abstract2/WideSubcategory.agda`.  It is
generic in the `UCSetup`, not in `Standard2`: ND_A restricts the non-standard ND_B, and the curried
tensor buys nothing (b) needs.  No `Standard2/Regrade.agda`: `Std(𝕄,ℰ)|ι` is the instance
`regraded (StdUC.StdSetup 𝕄 ℰ) ι`.

```agda
{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Abstract2.Regrade
  {o ℓ e o′ ℓ′ e′ cs ℓs oⱼ ℓⱼ eⱼ : Level} (𝕊 : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ} (ι : MonoidalFunctor 𝒥 (UCSetup.ℐ 𝕊)) where
open AbstractUC 𝕊
ι₂ : (W X : 𝒥.Obj) → ι.₀ W ⊗₀ ι.₀ X ℐ.⇒ ι.₀ (W 𝒥.⊗₀ X) ;  ι₂ W X = ι.⊗-homo.η (W , X)

regraded : UCSetup oⱼ ℓⱼ eⱼ o′ ℓ′ e′ cs ℓs                                 -- 𝕊|ι
regraded = record { 𝒞 = 𝒞 ; ℐ = 𝒥 ; ℳ = pullbackM ι ℳ ; ℰ = ℰ }
module R = AbstractUC regraded       -- R.T₀ X = T₀ (ι.₀ X), R.sub c = sub (ι.₁ c): refl

inclusion : UCSetupMorphism regraded 𝕊
inclusion = record { ν = idᵛ ℰ ; effect = record { F = idF ; Φ = ι ; κ = 𝒞.id
  ; isGradedKleisliMorphism = record { κ-return = 𝒞.identityˡ ; κ-sub = λ _ → id-comm-sym
                                     ; κ-ext = λ f → 𝒞.identityˡ ○ pullback-ext ι triple f ○ … } } }

≈ᵁ⇒≈ᵁ|ι : {f g : A 𝒞.⇒ T₀ (ι.₀ X) B} → f ≈ᵁ g → f R.≈ᵁ g                       -- (a)
≈ᵁ⇒≈ᵁ|ι e W = ≈ℰ-cong-post (sub (ι₂ W _)) (e (ι.₀ W))                            -- up to R.μ's spelling

restrict-≤UC : Full ι.F → f ≤UC g → f R.≤UC g                                    -- (f)
restrict-≤UC full f≤g = let s₀ , e = ≤UC⇒dummy f≤g ; s₀′ , s≈ = full s₀
                        in R.dummy-complete (s₀′ , ≈ᵁ⇒≈ᵁ|ι (≈ᵁ-trans e (≈C⇒≈ᵁ (sub-resp-≈ (ℐ.Equiv.sym s≈) ⟩∘⟨refl))))

module Preserves (r : ∀ {W X} → ι.₀ (W 𝒥.⊗₀ X) ℐ.⇒ ι.₀ W ⊗₀ ι.₀ X) (r∘ι₂ : ∀ {W X} → r ℐ.∘ ι₂ W X ℐ.≈ ℐ.id)
                 (surj : EssentiallySurjective ι.F) where                         -- (b), (c)
  ≈ᵁ|ι⇒≈ᵁ : f R.≈ᵁ g → f ≈ᵁ g
  ≈ᵁ|ι⇒≈ᵁ e W = let W′ , φ = surj W in conjugate φ (cancel r∘ι₂ (e W′))
  unrestrict-≤UC : f R.≤UC g → f ≤UC g
  unrestrict-≤UC le = let s₀ , e = R.≤UC⇒dummy le in dummy-complete (ι.₁ s₀ , ≈ᵁ|ι⇒≈ᵁ e)

regraded-gs : GradeStable → R.GradeStable                                       -- (d)
regraded-gs gs Y = gs (ι.₀ Y)
unrestrict-≤UC-gs : GradeStable → f R.≤UC g → f ≤UC g                           -- Transfer.transfer, G f = 𝒞.id ∘ f

module Between (ι′ : MonoidalFunctor 𝒥′ ℐ) (j : MonoidalFunctor 𝒥 𝒥′)
               (θ : MonoidalNaturalIsomorphism (∘-Monoidal ι′ j) ι) where      -- §1.4
  between : UCSetupMorphism regraded (Regrade.regraded 𝕊 ι′)                    -- κ = sub (θ.⇐.η _)

module Trivial where                                                             -- acceptance, §6
  open Preserves ℐ.id ℐ.identity² (λ W → W , ≅.refl)    -- at ι = idF-Monoidal ℐ
  to = restrict-≤UC (λ s → s , ℐ.Equiv.refl) ; from = unrestrict-≤UC
```

`cancel` (post-compose sub r, `sub-homomorphism`, `sub-identity`) and `conjugate` (the identity of (b))
are private.  The `refl`s of `R.T₀`/`R.sub`/`R.return` must survive `FromMonad`'s `triple`: the
causal-boxes plan flags it, and `pullback-*` are stated on `GradedMonad⇒GradedKleisliTriple`, which is
what `UCSetup.triple` is (`FromMonad.agda:36-37`).

### 1.6 Relation to `WideSubcategory`, causal boxes' `regrade`, `Oneᴹ`

| | `Abstract2/WideSubcategory` (𝒞 side) | `Abstract2/Regrade` (ℐ side) |
|---|---|---|
| restricts | computations, to a wide 𝒲 ⊆ 𝒞 closed under `return`, `μ`, `T₁`, `sub` | grades, along any monoidal ι : 𝒥 → ℐ |
| keeps | ℐ; ℳ restricted; tests ℰ′ presented by ν : ℰ′ ⇒ ℰ ∘ ιᵒᵖ | 𝒞 and ℰ; ℳ pulled back |
| inclusion | (ι, Id, id, ν) (`:118`) | (Id, ι, id, `idᵛ`) |
| has fewer | protocols | adversaries, simulators, ancillas |
| ≤UC preserved | `Preserves-≈ℰ` (`unrestrict-≤UC`, `:172`) | ι essentially surjective with split comparisons, or 𝕊 grade-stable |
| ≤UC reflected | `Reflects-≈ℰ` (`restrict-≤UC`, `:158`; free for `fine`) | ι full |
| trivial instance | `Trivial.everything` (`:192`) | ι = `idF-Monoidal ℐ` |

- **Causal boxes** (`docs/uc-setup-causal-boxes.md:417-433`): its `regrade`, planned in
  `UCSetup/Morphism.agda`, is `inclusion`; its "`Transfer.transfer` given target `GradeStable`" is
  (d), and (c) drops the hypothesis whenever ι is essentially surjective — its efficient-simulator
  grading keeps all grades, so (c) applies.  Its step 9 becomes an import of this module.
- **Regrade, then restrict computations.**  `WideSubcategory` over 𝕊|ι asks `W-sub` only at
  `sub (ι.₁ c)`.  The landscape's §3 correction (`W-sub` at every ambient adversary sinks "feasible
  machines") is lifted by first regrading to feasible adversaries.
- **`Oneᴹ`**: `Graded/Trivial.ungraded` reads a Kleisli triple as graded over `Oneᴹ`; restriction along
  the unit `Oneᴹ → ℐ` is (e)'s adversary-free setup, where UC emulation collapses to ≈ℰ.
- Only (b) and (c) use more than laxness of ι; the construction, (a), (d) and (f) are lax.

## 2. Choice factors and model B

### 2.1 Choice factors, and why a grade carries a list of them

- **PM.**  C_S := (1, S), the flat `⊤ ⇿ S` (`Iface.agda:13`): `Pos` = the request, up to the caller;
  `Neg` = the pick, down into the protocol.
- **SSP.**  `Cᴵ S := record { Ch = ⊤ ; Q = const S ; R = const ⊤ ; Ch-dec = DecEq-⊤ }`, whose
  `flat (Cᴵ S) = (⊤ × ⊤) ⇿ (⊤ × S) ≅ ⊤ ⇿ S` (`SSP/Iface.agda:112`): the same PM interface read
  call/return — the pick is the query, ⊤ the reply.
- **n ≥ 0 factors.**  A grade is X ⊗ C_{S₁} ⊗ … ⊗ C_{Sₙ}, one factor per *site*, because
  (⊤⇿S) ⊗ᴵ (⊤⇿S′) = (⊤⊎⊤) ⇿ (S⊎S′) ≇ ⊤ ⇿ (S⊎S′): a merged factor's request does not say which site
  asks, and it lets the environment answer one site with the other's pick (in SSP, `Cᴵ S ⊗ᴵ Cᴵ S′` has
  two channels, `Cᴵ (S ⊎ S′)` one).  A serial composite h ∙ f has grade X ⊗ Y, so site lists
  concatenate; n = 0 is every ordinary grade.

### 2.2 The grades 𝒢_B and the setup ND_B

Objects (X, S⃗) ∈ Ob 𝕄 × List Set, ⌊X, S⃗⌋ := X ⊗ C⟦S⃗⟧ with C⟦[]⟧ = I and C⟦S ∷ S⃗⟧ = C_S ⊗ C⟦S⃗⟧;
(X, S⃗) ⊕ (Y, T⃗) := (X ⊗ Y, S⃗ ++ T⃗), unit (I, []).  𝒢_B has all 𝕄-morphisms between the images.  The
tree already builds such a category: `Categories/Category/Monoidal/Construction/Transport.agda`,
`Restriction.transport` at R = ⊤ (`:183-211`), with ι_B = `transportF` (`:213`, strong, ⊗-homo φ),
given isos

  φ : ⌊X,S⃗⌋ ⊗ ⌊Y,T⃗⌋ ≅ ⌊X ⊗ Y, S⃗ ++ T⃗⌋   (associators, one braiding component σ_{C⟦S⃗⟧,Y}, then
                                             C⟦S⃗⟧ ⊗ C⟦T⃗⟧ ≅ C⟦S⃗ ++ T⃗⟧ by induction on S⃗),   υ : I ≅ I ⊗ I.

**ND_B := Std(𝕄, ℰ)|ι_B** = `regraded (StdUC.StdSetup 𝕄 ℰ) ι_B`.  ι_B is full (R = ⊤), essentially
surjective ((X, []) ↦ X ⊗ I ≅ X) and strong, so by §1.3 (b), (c), (f) ≤UC in ND_B *is* ≤UC in Std(𝕄)
on choice-graded protocols: uc-models' "ND_B is Std(𝕄) itself, with choice factors named", as an
instance of the theorem.  The designation matters only to ND_A (§3).

### 2.3 Where the braiding is needed

- **B: only the components** σ_{C⟦S⃗⟧,Y}, to define φ; `Transport` makes ⊗ᵗ natural by conjugation.  B
  can do without them: with word-shaped grades (lists of ordinary and choice blocks, ⊕ = ++) φ is
  associators only, and B ≃ Std(𝕄) anyway.
- **A: naturality and the hexagon.**  𝒢_A's closure under ⊗ᵗ is
  (u ⊗ ⌈ρ⌉) ⊗ᵗ (u′ ⊗ ⌈ρ′⌉) ≈ (u ⊗ u′) ⊗ ⌈ρ ++ ρ′⌉, naturality of σ against an arbitrary u′ and a
  relabelling; the transported associator being α ⊗ (identity relabelling) is the hexagon.  Without a
  braiding an adversary of a composite could not act on X and Y jointly across C⟦S⃗⟧.
- **SSP has it**: `Protˢ` (`SSP/Protocol/Monoidal.agda:277`), braiding `⌜ swapᴵ ⌝`, naturality
  `⌜⌝-natσ` (`:222`, brzuska2018 Lemma 3).
- **PM does not.**  `Machines/Base.agda` exports symmetry only on the Mealy base (`𝒱ₚ` `:77`, `ℳₚ`
  `:269` via `Bundle.Mealy-Symmetric`); `𝒢ₚᴹ` (`:282`) is `GConstructionMonoidalCategory`
  (`Categories/GConstructionMonoidal.agda:253`), a plain `MonoidalCategory`, and `𝔾ᵒ` seals it
  (`opaque`, `UC/Model/Seal.agda:43`).  `Reverse` (agda-categories 0.3.0,
  `Categories.Category.Monoidal.Construction.Reverse`) only transports a braiding (`Reverse-Braided`
  `:73`, `Reverse-Symmetric` `:92`); the tree applies it to machine-iso's `machine-monoidal-category`
  (`Machine/UC.agda:110`), dropping that category's `machine-symmetric` (`Machine/MonoidalCategory.agda:83`),
  and never to `𝔾ᵒ`.  The G-construction of a traced symmetric category is symmetric (jsv1996), so this is
  a formalisation gap: σᴳ is the embedded base swap, a relabelling wire (`UC/Machine/Wire.agda`), and
  `GConstructionEmbedding`'s `absorbˡ`/`absorbʳ` reduce its naturality to `σᴹ`'s plus a routing
  coherence, built under the seal [INFERENCE: cost unknown; `homomorphismᴳ`'s loop coherence needed a
  split solver, `Categories/GConstructionHomCoherence.agda`].

### 2.4 `choose` and its compilation

**Why a grade and not an effect** (kept): there is no distributive law combining probability and
nondeterminism (varacca2006 §1; zwart2019nogo §1, §3.1, Thms 3.5, 3.12), and the convex powerset monad
(bonchi2022 §4.1–4.2, §5) is not needed: the scheduler is a factor of the grade, `Dist⊥`/`Dₚ` stay the
only effects, and a closed system — no factor left — is read by the ordinary tests with ν = `idᵛ`.  The
leak of the 2026-10-09 design (CE1: a demon in one component saw another's coins, canetti2006taskpioa
abstract, §1) does not arise.

**Syntax, SSP side.**  Kept: the `choose` constructor and its `graft`/`serve`/`mapᶜ`/`reindex` clauses,
shaped like `coin`'s.  New: a site index, since each node compiles to a request on *its* factor.

```agda
-- CategoricalCrypto/ND/SSP/Choice.agda
data Calls⁺ (A : Iface) (S⃗ : List Set) (X : Set) : Set where
  ret ; call ; coin ; dead                                    -- SSP's four (`SSP/Protocol.agda:37-41`)
  choose : (i : Fin (length S⃗)) → (lookup S⃗ i → Calls⁺ A S⃗ X) → Calls⁺ A S⃗ X
record Protocol⁺ (S⃗ : List Set) (A B : Iface) : Set₁        -- `Protocol` with `Calls⁺` steps
-- the old `choose : (n : ℕ) → (Fin (suc n) → Calls A X) → Calls A X` is one site, S = Fin (suc n)
```

Notation: for a family k : S → (step trees over one state), ⟨k⟩ is the one-site protocol stepping by
`choose 0 (λ i → k i …)`, ⟨t⟩ the site-free one stepping by t, and [t₀, t₁] the family on `Fin 2`.

**Compilation, SSP side: pick-ahead.**

```agda
Cᴵ⟦_⟧ : List Set → Iface                        -- unitᴵ ; Cᴵ S ⊗ᴵ Cᴵ⟦ S⃗ ⟧
resolve : Queues S⃗ → Calls⁺ A S⃗ Z → Calls A (Z × Queues S⃗)     -- one FIFO List (lookup S⃗ i) per site
resolve qs (choose i k) with pop i qs
... | just (p , qs′) = resolve qs′ (k p)
... | nothing        = dead                     -- an unanswered request
-- ret, call, coin, dead: structural, threading qs
⌈_⌉ : Protocol⁺ S⃗ A B → A ⇒ T₀ Cᴵ⟦ S⃗ ⟧ B      -- = Protocol A (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ B)
⌈ P ⌉ = record { St = St P × Queues S⃗ ; init = init P , empty ; step = λ where
  (s , qs) (inj₁ i) p → ret ((s , push i p qs) , tt)                 -- a pick arrives on site i
  (s , qs) (inj₂ c) q → mapᶜ regroup (resolve qs (step P s c q)) }
```

- **Why pick-ahead.**  In SSP the grade is exported (T₀ X B = X ⊗ᴵ B: the adversary calls the
  protocol), and a step can neither call its exported side nor suspend (`docs/uc-setup-ssp.md:483-496`,
  pollable state).  So uc-models §4's request cannot be raised inside a step, and the pick must arrive
  before the activation that consumes it.  The same holds in every well-bracketed setup (𝒲, PM[wb]): on
  `flat (Cᴵ S)` the pick is the query.  Only PM proper raises the request online: a machine at grade
  X ⊗ C_S emits ⋆ on C_S⁺ mid-activation and resumes on the pick, the suspended step in its state.  PM
  has no call-tree syntax for that; there, protocols with choices are machines at choice grades.
- **Who sees what.**  The old global demon saw every coin ⊐ PM online sees that and when a site asks
  (the header view of canetti2015suc's router, backes2007rsim's "realistic information"), not the coins
  ⊐ SSP pick-ahead sees activation boundaries only (oblivious within an activation) ⊐ a task schedule
  fixed in advance (canetti2006taskpioa).
- **Not a `StdUCMorphism`.**  ⌈−⌉ changes the grade, so it is no functor Prot⁺ → Prot; it maps into
  graded hom-sets, the Kleisli-valued shape the old plan rejected as its (2b).  None is needed: ND_B has
  no category of its own, protocols with choices are its morphisms at choice grades, `Protocol⁺` is
  syntax and ⌈−⌉ its meaning.  What must hold instead, by structural induction [INFERENCE]: `⌈⌉-resp`
  (step-wise ≈ᶜ ⇒ ≈ᵖ); `⌈⌉-∘`: ⌈g ∘⁺ f⌉ ≈ᵖ sub φ ∘ (⌈g⌉ ∙ ⌈f⌉), for `_∘⁺_` concatenating site lists
  (per-site queues make the two schedules agree); `⌈⌉-⊗` likewise; `⌈⌉-plain`: at S⃗ = [],
  ⌈P⌉ ≈ᵖ λ⇐ ∘ P.  These make `choose` compositional.

### 2.5 What ≤UC in B says

By `dummy-complete`, f ≤UC_B g iff some s₀ : ⌊Y,T⃗⌋ → ⌊X,S⃗⌋ — any morphism — has f ≈ᵁ sub_{s₀} ∘ g.
Real choices (S⃗) are resolved by whoever holds the real grade: the adversary a, answering from its own
state and what it learned on X.  Ideal ones (T⃗) are resolved by the simulator, from what it learns from
a; the environment plays the dummy adversary.  This is UC with adversarial scheduling (canetti2015suc
§2.2: the router delivers a message when the adversary says so).  Refining a choice is emulation: in PM
⟨t₀⟩ ≤UC_B ⟨[t₀, t₁]⟩, s₀ answering every ideal request with 0, invisibly to the environment.

**SSP caveat.**  A call/return simulator runs only when the environment calls the real grade; the ideal
protocol cannot activate it.  So SSP-B resolves ideal choices only on the environment's schedule, and
⟨t₀⟩ ≤UC_B ⟨[t₀, t₁]⟩ fails when ⟨t₀⟩ exports no adversary oracle: s₀ : `Protocol (Cᴵ (Fin 2)) unitᴵ`
serves no channel, the ideal queue stays empty, its `choose` is `dead` [INFERENCE].  SSP-B is Canetti's
model restricted to adversaries that schedule ahead; for more, export a scheduling oracle (ssp.md §5.2,
the old `Schedᴵ` router) or do B in PM (P1–P2, §6).


## 3. Model A: relabellings only

## 4. The morphism A → B, and the way back

## 5. Laws of `choose`, `P ∥ Q`, SSPᵈ

## 6. Work breakdown

## 7. Sources
