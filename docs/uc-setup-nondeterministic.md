# Nondeterministic choice: the scheduler in the grade

Plan, 2026-10-10; replaces the 2026-10-09 plan of the same name (image equality over `Sched → Dist⊥ Bool`,
in git history at `7d722e1f`).  Only the modules §6 marks **built** are typechecked.  Every claim about a
module that does not exist is a design claim; `[INFERENCE]` marks what was reasoned and not checked.
Line references are to `uc-setup-landscape` at `cf7c0db0`.  Names are those of `docs/uc-models.typ` (PM,
SSP, PM[wb], 𝒲, SSPᵈ, ND_A, ND_B; §4 there, `sec:nd`, is the mathematical statement this plan implements).

## 0. Summary

The scheduler of a nondeterministic protocol is a factor of its *grade*, not an effect (landscape
finding 5): each `choose` site is a choice factor C_S = (1, S) of the adversary interface.  Model B lets
every grade morphism touch it — the adversary resolves real choices, the simulator ideal ones (Canetti) —
and model A only relabellings — the environment resolves both (specifications).  Both are restrictions
of one standard setup along a functor of grades, and A → B is the inclusion.

1. **The generic construction** (§1): 𝕊|ι for any setup 𝕊 and lax monoidal ι : 𝒥 → ℐ, with
   `inclusion : 𝕊|ι → 𝕊` = (Id, ι, id, `idᵛ`).  ι essentially surjective with split comparisons ⇒ the same
   U-kernel and ≤UC preserved, no `GradeStable`; 𝕊 grade-stable ⇒ preserved for every ι; otherwise not
   (the unit at PM).  ι full ⇒ reflected, with no other hypothesis.  `Abstract2/Regrade.agda`, the dual
   of `Abstract2/WideSubcategory.agda`; causal boxes' `regrade` is its `inclusion`.
2. **ND_B** (§2) = Std(𝕄)|ι_B over designated grades X ⊗ C_{S₁} ⊗ … ⊗ C_{Sₙ}, n ≥ 0, built by the
   existing `Construction/Transport`; ι_B is full and essentially surjective, so ND_B has Std(𝕄)'s ≤UC.
3. **ND_A** (§3) = ND_B|incl, incl the wide inclusion of the grade morphisms u ⊗ ⌈ρ⌉, ρ a relabelling.
4. **A → B** (§4) is `inclusion` at incl: it preserves ≤UC for all f, g (one U-kernel) and does not
   reflect it.  Undesignation B → A is a section; nothing inverts the inclusion on designated grades.

**Findings against uc-models §4.**  (a) *SSP cannot raise the request* (§2.4): its grade is called,
never calling, and a step cannot suspend.  SSP compiles `choose` *pick-ahead* — picks pushed on
`Cᴵ S`, queued, popped, an empty queue `dead` — and only PM raises the request online, so SSP-B's
simulator resolves ideal choices only when the environment activates it.  (b) *The braiding* (§2.3): B
needs its components at most, A its naturality and hexagon; SSP has one (`Protˢ`), `𝔾ᵒ` exports none,
and neither `Machines/Base` (symmetric only on the Mealy base) nor `Reverse` (it transports, never
creates) supplies one.  (c) *Relabellings are partial injections* (§3.1), for stateless pick routing in
PM.  (d) Under pick-ahead `choose` commutes with coins and calls, and SSPᵈ's laws survive it (§5).

**Kept from the 2026-10-09 plan:** the `choose` constructor (now site-indexed) with its `graft`, `serve`,
`mapᶜ`, `reindex` clauses; the no-go literature (§2.4); `P ∥ Q`'s non-derivability (§5.2).
**Dropped:** `Sched`, `run⁺`, image equality and its Hausdorff version, the five law constructors, CE0/CE1
and their repairs, the routings (2a)/(2b), and the edge SSP → ND with its reflection (R): SSP is ND_B's
site-free part, read by the same tests.

**Decisions for the maintainer:** (1) pick-ahead SSP-B, or B in PM (P1–P2, §6); (2) relabellings as
partial injections; (3) site-indexed `choose`; (4) G1 in `Abstract2/Regrade.agda`, not in
`UCSetup/Morphism.agda` where the causal-boxes plan puts `regrade`.

## 1. The generic construction: restriction along a monoidal functor of grades

### 1.1 The restricted setup

For a setup 𝕊 = (𝒞, ℐ, ℳ, ℰ) and a lax monoidal functor ι : 𝒥 → ℐ (structure ι_ε : I → ιI,
ι₂ : ιW ⊗ ιX → ι(W ⊗ X)), the **restriction of 𝕊 along ι** is

  𝕊|ι := (𝒞, 𝒥, ℳ ∘ ι, ℰ),

with the graded monad pulled back — a graded monad is a lax monoidal functor ℐ → [𝒞, 𝒞] (fujii2016), so this is
precomposition (`Categories/Monad/Graded/Pullback.agda:32`, `pullbackM = ∘-Monoidal ℳ ι`):
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
- **(d) Preservation for every ι when 𝕊 is grade-stable.**  f ≈ᵁ|ι g ⇒ f ≈ℰ g (`≈ᵁ⇒≈ℰ` in 𝕊|ι) ⇒
  f ≈ᵁ g (`bridge`, `Abstract2.agda:124`); 𝕊|ι is grade-stable too (T′_Y = T_{ιY}).  This is
  `Transfer.transfer inclusion idᵛ-epi gs` (`Abstract2/Morphism.agda:75`), the route the causal-boxes
  sketch takes.
- **(e) Without (b) or (d) preservation fails.**  Take ι : `Oneᴹ` → ℐ, the unit (`Oneᴹ` is
  `Categories/Monad/Graded/Trivial.agda:24`).  𝕊|ι is the adversary-free setup: one ancilla and one
  simulator, so for standard 𝕊 (T_I f is f conjugated by λ) ≈ᵁ|ι and ≤UC|ι are ≈ℰ on unit-graded
  protocols.  At PM the reveal pair
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
                                     ; κ-ext = λ f → 𝒞.identityˡ ○ ext-pullback f ○ … } } }

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

`cancel` (post-compose sub r, `sub-homomorphism`, `sub-identity`), `conjugate` (the identity of (b)) and
`ext-pullback` (R.ext W f ≈ sub (ι₂ W _) ∘ ext (ι.₀ W) f) are private.  `Pullback.agda`'s lemmas are
stated for `pullback ι triple`, which round-trips ℳ through `GradedKleisliTriple⇒GradedMonad`;
`regraded`'s triple is `FromMonad (pullbackM ι ℳ)` without the round trip.  So `R.T₀`, `R.sub` and
`R.return` should hold by `refl` directly (`F₀`/`F₁` of `∘-Monoidal`), and `pullback-ext`'s proof is
replayed as `ext-pullback` — the causal-boxes plan's "else one round-trip lemma" [INFERENCE].

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

**Syntax, SSP side** (built, `ND/SSP/Choice.agda`).  Kept: the `choose` constructor and its
`graft`/`serve`/`mapᶜ`/`reindex` clauses, shaped like `coin`'s.  New: a site index, since each node
compiles to a request on *its* factor.

```agda
-- CategoricalCrypto/ND/SSP/Choice.agda
Cᴵ⟦_⟧ : List Set → Iface                        -- unitᴵ ; Cᴵ S ⊗ᴵ Cᴵ⟦ S⃗ ⟧: one factor per site
data Calls⁺ (A : Iface) (S⃗ : List Set) (X : Set) : Set where
  ret ; call ; coin ; dead                                    -- SSP's four (`SSP/Protocol.agda:37-41`)
  choose : (i : Ch Cᴵ⟦ S⃗ ⟧) → (Q Cᴵ⟦ S⃗ ⟧ i → Calls⁺ A S⃗ X) → Calls⁺ A S⃗ X
record Protocol⁺ (S⃗ : List Set) (A B : Iface) : Set₁        -- `Protocol` with `Calls⁺` steps
_∘⁺_ : Protocol⁺ T⃗ B C → Protocol⁺ S⃗ A B → Protocol⁺ (S⃗ ++ T⃗) A C       -- the lower factor's sites first
_⊗⁺_ : Protocol⁺ S⃗ A B → Protocol⁺ T⃗ C D → Protocol⁺ (S⃗ ++ T⃗) (A ⊗ᴵ C) (B ⊗ᴵ D)
-- the old `choose : (n : ℕ) → (Fin (suc n) → Calls A X) → Calls A X` is one site, S = Fin (suc n)
```

Against the pseudocode this section carried before the build: a site is a channel of `Cᴵ⟦ S⃗ ⟧` and its pick a
query there, not `Fin (length S⃗)` with `lookup S⃗ i`, so compiling converts nothing; `_∘⁺_`'s
`graft⁺`/`serve⁺` move each factor's sites into `S⃗ ++ T⃗` along `join` (below), `_⊗⁺_` by `relocate`;
and site lists are explicit arguments of the helpers (`push S⃗`, `pop S⃗`, `join S⃗ T⃗`), since neither
`Cᴵ⟦_⟧` nor `Queues` is injective and Agda cannot infer them.

Notation: for a family k : S → (step trees over one state), ⟨k⟩ is the one-site protocol stepping by
`choose 0 (λ i → k i …)`, ⟨t⟩ the site-free one stepping by t, and [t₀, t₁] the family on `Fin 2`; in PM
the same names denote the machines that request a pick and run accordingly.

**Compilation, SSP side: pick-ahead** (built).

```agda
resolve : Queues S⃗ → Calls⁺ A S⃗ (X × Y) → Calls A ((X × Queues S⃗) × Y)    -- one FIFO List S per site
resolve qs (choose i k) = maybe′ (λ pq → resolve (proj₂ pq) (k (proj₁ pq))) dead (pop S⃗ i qs)
-- ret, call, coin, dead: structural, threading qs into the state; `nothing` is an unanswered request
⌈_⌉ : Protocol⁺ S⃗ A B → Protocol A (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ B)   -- = A ⇒ T₀ Cᴵ⟦ S⃗ ⟧ B; for B = X ⊗ᴵ B′ a wire regrades to (X, S⃗)
⌈ P ⌉ = record { St = St P × Queues S⃗ ; init = init P , empty S⃗ ; step = λ where
  (s , qs) (inj₁ i) p → ret ((s , push S⃗ i p qs) , tt⟦ S⃗ ⟧ i)        -- a pick arrives on site i
  (s , qs) (inj₂ c) q → resolve qs (step P s c q) }
```

`resolve` returns the queues inside the state rather than beside the result, so `⌈_⌉` needs no
`regroup`; `tt⟦ S⃗ ⟧ i` is the reply at site i, ⊤ only up to recursion on `S⃗`.

- **Why pick-ahead.**  In SSP the grade is exported (T₀ X B = X ⊗ᴵ B: the adversary calls the
  protocol), and a step can neither call its exported side nor suspend (`docs/uc-setup-ssp.md:483-496`,
  pollable state).  So uc-models §4's request cannot be raised inside a step, and the pick must arrive
  before the activation that consumes it.  The same holds in every well-bracketed setup (𝒲, PM[wb]): on
  `flat (Cᴵ S)` the pick is the query.  Only PM proper raises the request online: a machine at grade
  X ⊗ C_S emits ⋆ on C_S⁺ mid-activation and resumes on the pick, the suspended step in its state.  PM
  has no call-tree syntax for that; there, protocols with choices are machines at choice grades.
- **Who sees what.**  The old global demon (segala1995 §5.2's perfect information) saw every coin ⊐ PM online sees that and when a site asks
  (the header view of canetti2015suc's router, backes2007rsim's "realistic information"), not the coins
  ⊐ SSP pick-ahead sees activation boundaries only (oblivious within an activation) ⊐ a task schedule
  fixed in advance (canetti2006taskpioa).
- **Not a `StdUCMorphism`.**  ⌈−⌉ changes the grade, so it is no functor Prot⁺ → Prot; it maps into
  graded hom-sets, the Kleisli-valued shape the old plan rejected as its (2b).  None is needed: ND_B has
  no category of its own, protocols with choices are its morphisms at choice grades, `Protocol⁺` is
  syntax and ⌈−⌉ its meaning.  What holds instead, each by one simulation (built, `ND/SSP/Choice.agda`
  and `Choice/Compose.agda`): `⌈⌉-resp` (P ≈⁺ P′ ⇒ ⌈P⌉ ≈ᵖ ⌈P′⌉, ≈⁺ the simulations whose step trees
  agree up to ≈ᶜ⁺, SSP's ≈ᶜ with a `choose` clause); `⌈⌉-plain`: at S⃗ = [], ⌈P⌉ ≈ᵖ λ⇐ ∘ P; `⌈⌉-∘`:
  sub φ⁻¹ ∘ ⌈g ∘⁺ f⌉ ≈ᵖ ⌈g⌉ ∙ ⌈f⌉, with φ = ⌜ `split S⃗ T⃗` ⌝ and φ⁻¹ = ⌜ `join S⃗ T⃗` ⌝ the regrouping
  built from the unitor and associator — φ⁻¹ meets the picks before the queues, which `splitQ` splits
  (per-site queues make the two schedules agree); `⌈⌉-⊗`: sub φ⁻¹ ∘ ⌈P ⊗⁺ P′⌉ ≈ᵖ ⌜ `interchangeᴵ` ⌝ ∘
  (⌈P⌉ ⊗ ⌈P′⌉).  With `split∘join` (φ invertible, through `SSP/Protocol/Wire.agda`'s `⌜⌝-∘`, `⌜⌝-⊗`)
  they take this plan's form, `⌈⌉-∘-split`: ⌈g ∘⁺ f⌉ ≈ᵖ sub φ ∘ (⌈g⌉ ∙ ⌈f⌉), and `⌈⌉-⊗-split`.
  `Choice/Pin.agda` checks by `refl` that these concrete forms are `SSP.Setup`'s `_∙_` and `sub`.

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

### 3.1 Relabellings

A relabelling ρ : S⃗ ⇝ T⃗ is a partial injection τ from the real sites S⃗ to the ideal sites T⃗ with
pick maps r_j : S_j → T_{τ j}.  As a grade morphism ⌈ρ⌉ : C⟦T⃗⟧ → C⟦S⃗⟧ (ideal to real, a simulator's
direction) it is the wire that forwards a pick on a real site j ∈ dom τ to τ j along r_j, absorbs picks
on the other real sites and, in PM, forwards each request of an ideal site i ∈ im τ to τ⁻¹ i.  It never
originates a pick and never answers a request.  Injectivity is what makes PM's routing stateless (one way
back per pick); SSP would accept any partial map, and one class serves both.  In SSP, ⌈ρ⌉ is ⌜ m ⌝ with
m : Cᴵ⟦dom τ⟧ ⇒ᴵ Cᴵ⟦T⃗⟧ (`ch` = τ, `qu` = r), tensored with `ack : Protocol unitᴵ (Cᴵ S)` (state ⊤,
replies tt) on the absorbed sites, up to reordering wires.  Relabellings form a category Alph (lists of
sets; partial injections with fibre maps), monoidal under ++.  uc-models' "a stateless wire that forwards
each request and pulls the pick back along a function S′_j → S_i" is this, made partial.

**Built** (`ND/Relabel.agda`).  `record _⇝_` holds τ and r in one field,
`route : (i : Ch Cᴵ⟦ S⃗ ⟧) → Maybe (Σ[ k ∈ Ch Cᴵ⟦ T⃗ ⟧ ] (Q Cᴵ⟦ S⃗ ⟧ i → Q Cᴵ⟦ T⃗ ⟧ k))`, beside
`injective`; `Alph : Category` compares routes pointwise, fibre maps extensionally (`_≈ʳ_`); `_++ʳ_` routes
a site by the side `split` puts it on and is injective through `split`/`join`.  The wire is `⌈_⌉ʳ` (the
compile keeps `⌈_⌉`), defined directly: forward along the route, or answer `tt`.  Instead of `⌜ m ⌝` over
`Cᴵ⟦dom τ⟧` with reordering wires, `⌈⌉ʳ-factor` shows ⌈ρ⌉ʳ ≈ᵖ ⌜ `relabelᴵ ρ` ⌝ ∘ (wire ⊗ `ack`) ∘ ρ⇐,
where `relabelᴵ ρ : Cᴵ⟦ S⃗ ⟧ ⇒ᴵ Cᴵ⟦ T⃗ ⟧ ⊗ᴵ Cᴵ ⊤` sends every absorbed site to one channel `ack`
answers.  `⌈−⌉ʳ : Functor (Category.op Alph) Prot` (`⌈⌉ʳ-id`, `⌈⌉ʳ-∘`, `⌈⌉ʳ-resp`), and `⌈⌉ʳ-++`:
⌈ρ ++ʳ ρ′⌉ʳ ≈ᵖ φ ∘ (⌈ρ⌉ʳ ⊗ ⌈ρ′⌉ʳ) ∘ φ⁻¹, the monoidality R-⊗ of §3.2 needs.

### 3.2 The grades 𝒢_A and the setup ND_A

𝒢_A := `Restriction.transport` at R f := Σ (u , ρ). f ≈ u ⊗ ⌈ρ⌉, u : X → Y arbitrary: wide in 𝒢_B,
and on the choice part the image of 𝕄 × Alphᵒᵖ (uc-models' 𝓘 × Alphᵒᵖ).  Obligations: R-id, R-∘
(⌈−⌉ functorial), R-⊗ and R-α/λ/ρ (§2.3).  incl : 𝒢_A → 𝒢_B is the identity on objects and strict:
`Restriction.weaken` (R ⊆ R′ ⇒ strict inclusion), a new lemma in `Transport.agda`.

**ND_A := ND_B|incl** = `regraded ND_B incl`; `pullback-∘-*` relate it to Std(𝕄)|(ι_B ∘ incl) if a
direct form is wanted.

### 3.3 What ≤UC in A says

f ≤UC_A g iff f ≈ᵁ sub_{u ⊗ ⌈ρ⌉} ∘ g for some u : Y → X and relabelling ρ (`dummy-complete`).  No 𝒢_A
morphism answers a request or originates a pick, so every request of both worlds is answered by the
environment, on the real grade.  The simulator renames sites, absorbs real sites the ideal lacks, and
leaves ideal sites outside im τ unanswered.  This is environment resolution: the reading for
specifications ("send to A, B, C in any order"), and task-PIOA's inessential choices
(canetti2006taskpioa §1) resolved by the universally quantified environment instead of a schedule fixed
in advance.  An unanswered request blocks one side only, so sites must match through τ:
⟨t⟩ ≰UC_A ⟨[t, t]⟩ (the ideal site is never answered), and A has no idempotence (§5.1).

### 3.4 Order independence

For one site and π : S ≃ S, ⌈⟨k ∘ π⟩⌉ ≈ᵖ sub_{id ⊗ ⌈π⌉} ∘ ⌈⟨k⟩⌉: the simulation maps the queue by π
[INFERENCE].  This is a hom-equality after a relabelling.  At π = swap, ⟨[t_AB, t_BA]⟩ and
⟨[t_BA, t_AB]⟩ ("A then B" against "B then A") emulate each other in A, with the swap of the two picks
as simulator (uc-models §4); hence in B (§4) and, by `UC-compose`, in every context.  "The order does not
matter" is the stronger, grade-preserving ⌈⟨k⟩⌉ ≈ᵖ ⌈⟨const k₀⟩⌉.  As in the old plan's `OrderSpec`, it
is a statement about the composite with the actual callee, since calls on different channels do not
commute for an order-sensitive importer.  It is proved per reachable state (ssp.md §4.3's technique).

## 4. The morphism A → B, and the way back

**A → B is §1's `inclusion`** for 𝕊 = ND_B and ι = incl: (Id, incl, id, `idᵛ`).  incl is bijective on
objects and strict, so §1.3(b) holds with φ = id: ≈ᵁ_A is literally ≈ᵁ_B (the same grade objects, hence
the same ancillas, prefix contexts and tests — uc-models' proof idea).  By (c), **f ≤UC_A g ⇒ f ≤UC_B g
for all f, g graded in 𝒢_A**, with the same dummy simulator u ⊗ ⌈ρ⌉; composed with B → Std(𝕄)
(`composeᵁ`) it reaches Std(𝕄).  Every A-proof — order independence, refinements by relabelling — is a
B-proof with the same simulator, and this one edge is what relates the two models.  §1.3(d) is neither
needed nor available (PM is not grade-stable; SSP is not known to be).

**It does not reflect** (incl is not full, §1.3(g)).  Witnesses: (i) *flattening*: ⟨λ i → choose 0 (k i)⟩,
two picks from one site per activation, against the one-site protocol on S × S stepping by the pair.
They are B-equivalent through a simulator that buffers two real picks and passes the pair (or splits
one), and not A-related, since a relabelling forwards one pick per pick, statelessly [INFERENCE; PM and
SSP alike].  (ii) In PM, ⟨t₀⟩ ≤UC_B ⟨[t₀, t₁]⟩ (§2.5) while ⟨t₀⟩ ≰UC_A ⟨[t₀, t₁]⟩ (§3.3).

**The way back.**

- **Nothing inverts the inclusion on designated grades.**  A morphism B → A fixing them would carry
  B-simulators to A-simulators (κ-sub), and witness (i)'s simulator is no relabelling [INFERENCE].
- **Undesignation is a morphism B → A.**  Φ_u : 𝒢_B → 𝒢_A, (X, S⃗) ↦ (⌊X,S⃗⌋, []), u ↦ u ⊗ ⌈id_[]⌉, is a
  functor (between site-free grades every morphism is in R) and strong (comparison φ).  With ND_A in its
  direct form Std(𝕄)|(ι_B ∘ incl), it is `between Φ_u θ` (§1.4), θ the unitor ⌊X,S⃗⌋ ⊗ I ≅ ⌊X,S⃗⌋.  ι_A ∘ Φ_u and ι_B have the
  same essential image (all of 𝕄) and Φ_u is full, so it preserves and reflects ≤UC.  B embeds into A as
  A's site-free part: B → A → B ≅ id, while A → B → A forgets the designation, sending A-emulation to
  B-emulation inside A.  B is a retract of A, not conversely.
- **Choice-free specifications.**  On grades with S⃗ = [], 𝒢_A and 𝒢_B have the same homs
  (u ⊗ ⌈id_[]⌉ = u up to ρ), so A-, B- and Std(𝕄)-emulation coincide between site-free protocols; the
  models differ as soon as either side has a site.
- **`Factorization`** (`UCSetup/Morphism.agda:101`) adds nothing: both morphisms have ν = `idᵛ`, Epi
  and Mono, so the image setup is the source itself.

## 5. Laws of `choose`, `P ∥ Q`, SSPᵈ

### 5.1 Hom-equalities and emulations

A law relates two compiled protocols.  It is a hom-equality only when the sites agree, an A-emulation
when a relabelling relates them, and a B-emulation otherwise.  The old plan's five law constructors of
`≈ᶜ` are gone: `Calls⁺` carries SSP's `≈ᶜ` with a congruence clause for `choose`, and laws are theorems
about ⌈−⌉.

| law | after ⌈−⌉ | A | B, PM | B, SSP |
|---|---|---|---|---|
| congruence: `k i ≈ᶜ k′ i` ⇒ `choose i k ≈ᶜ choose i k′` | ≈ᵖ (`resolve` pointwise) | ✓ | ✓ | ✓ |
| `choose` past `coin` or `call` in one step | ≈ᵈ, hence ≈ᵁ: the pick precedes the activation | ✓ | no syntax | ✓ |
| permutation `k ∘ π`; commutativity `[t₀,t₁] ~ [t₁,t₀]` | ≈ᵖ after the relabelling ⌈π⌉ | mutual | mutual | mutual |
| collapse: ∀ i. k i ≈ k₀ ⇒ ⟨k⟩ ~ ⟨const k₀⟩ (same site) | ≈ᵖ | ✓ | ✓ | ✓ |
| idempotence ⟨const t⟩ ~ ⟨t⟩ (one site against none) | grades differ | ✗ both ways | ⟨t⟩ ≤ ⟨const t⟩ only | ✗ |
| flattening: two picks against one pair-pick | grades differ | ✗ | mutual | mutual |

- Row 2 is new.  Under the old global demon `coin-unit` and choose/coin commutation were non-laws (a
  demon saw the toss: CE0, CE1); under pick-ahead `choose` reads the queue, which no coin or reply
  feeds.  With a pick queued the two trees are ≈ᶜ; with none, one dies after the coin or call and the
  other before it: `coin-drop` (the coin half is built, `coin-choose-ᵈ`, §5.3), and a "`dead` absorbs
  a call" square [INFERENCE].  In PM a request's position within an activation is observable, so the
  row holds there only for requests raised on every branch [INFERENCE].
- Idempotence: in A an unanswered site hangs one side only; in PM-B the simulator answers the ideal's
  request invisibly (⟨t⟩ ≤ ⟨const t⟩) but cannot raise the real one's; in SSP-B the simulator is never
  activated, and the real side dies on an empty queue.  Flattening's B rows and both idempotence
  verdicts are [INFERENCE].

### 5.2 `P ∥ Q` (kept)

`P ∥ Q` is not derivable from `choose` and `_⊗ᵖ_`.  (1) `(P ⊗ᵖ Q) ∘ᵖ ⌜ ∇ ⌝` is already caller-scheduled
interleaving: each query is atomic, and no `choose` is involved.  (2) `_⊗ᵖ_` dispatches on the queried
channel and has no fork, so interleaving inside one activation is no composite, and a `choose` over
protocols picks one per activation.  (3) What is definable is the tree shuffle
`_∥ᶜ_ : Calls⁺ A S⃗ X → Calls⁺ A S⃗ Y → Calls⁺ A (Bool ∷ S⃗) (X × Y)` (old plan §4.4, lexicographic
termination), whose call/call clause is a `choose` on its own interleaving site.  Compiled, the
adversary (B) or the environment (A) schedules the interleaving.  Commutativity up to `mapᶜ swap` is
the relabelling `not` on that site, so it holds both ways in A.  Associativity re-encodes a three-way
interleaving across two sites, which needs a buffering simulator: B only [INFERENCE].

### 5.3 SSPᵈ

Compiled protocols are SSP protocols, so `≈ᵈ` (`SSP/Dist.agda:37`), `congᵈ` (`:54`) and the laws of
`SSP/Dist/Laws.agda` (`coins-comm`, `coin-drop`, `coin-flip`, `coin-xor`, `stepwise`, `defer`) apply to
them unchanged; `Calls⁺` needs no `≈ᵈ` of its own.  The laws also survive `choose` in the source.
`resolve qs` is pointwise in the continuation and turns `choose` into a read of the queue, which no coin
feeds, so a law under `choose` is the law at each pick.  Built (`ND/SSP/Choice/Dist.agda`): t ≈ᵏ⁺ t′ is
`resolve qs t ≈ᵏ resolve qs t′` at every queue state, `choose-cong` the law at each pick, `stepwise⁺`
lifts step-wise ≈ᵏ⁺ through ⌈−⌉ to ≈ᵈ, and `coin-choose`/`coin-choose-ᵈ` is §5.1's row 2 for coins.
`defer` moves a draw past a choice, since ρ acts on `St P` and the queues ride along [INFERENCE].  ND
over SSPᵈ is `regraded (StdUC.StdSetup Protᵈ ℰᵈ) ι_B`.  Its braiding descends from `Protˢ` (⌜ swapᴵ ⌝'s
laws are ≈ᵖ, hence ≈ᵈ), but `Construction/Quotient` exports only the monoidal structure: one small
lemma.

## 6. Work breakdown

Every module is `--safe --without-K` and checked alone by `pagda` (house rules: `timeout`, `-M3G`, empty
warning gate, escape-hatch baseline unchanged, a commit per green step); the root closure is the
integrator's.  Paths are under `src/`.

| # | module | delivers | acceptance |
|---|---|---|---|
| G1 | `CategoricalCrypto/Abstract2/Regrade.agda` | §1.5: `regraded`, `inclusion`, `≈ᵁ⇒≈ᵁ\|ι`, `restrict-≤UC`, `Preserves`, `regraded-gs`, `unrestrict-≤UC-gs`, `Between` | at ι = `idF-Monoidal ℐ`, `inclusion`'s `F`, `Φ`, `κ`, `ν.η` are `idᵁ 𝕊`'s by `refl` (`Abstract2/Regrade/Pin.agda`); `Trivial.to`/`from` |
| G2 | `Categories/Category/Monoidal/Construction/Transport.agda` | `Restriction.weaken` | importers (`UC/Bracket/*`) re-checked |
| G3 (opt.) | `CategoricalCrypto/Examples/RegradeUnit.agda` | §1.3(e) at PM | `r_true` ≤UC\|ι `r_false`, `¬ (r_true ≤UC r_false)` |
| B1 | `CategoricalCrypto/ND/Grade.agda` | over a `SymmetricMonoidalCategory` and `C : Set → Obj`: `Grade`, `⌊_⌋`, φ, υ, `𝒢B`, `ιB`, `NDB`, ≤UC_B ⇔ ≤UC (G1) | instantiated at `Protˢ`, `Cᴵ` |
| B2 | `CategoricalCrypto/ND/SSP/Choice.agda` | §2.4: `Calls⁺`, `Protocol⁺`, the `choose` clauses, `_∘⁺_`, `Queues`, `resolve`, `⌈_⌉`, `⌈⌉-resp`, `⌈⌉-plain`, `⌈⌉-∘`, `⌈⌉-⊗` | a two-site composite pinned by `refl` — **built**: `ND/SSP/Choice.agda` (syntax, `⌈_⌉`, `⌈⌉-resp`, `⌈⌉-plain`), `Choice/Compose.agda` (`⌈⌉-∘`, `⌈⌉-⊗` with φ⁻¹ on the left; `split∘join`, then `⌈⌉-∘-split`, `⌈⌉-⊗-split` in §2.4's form), `Choice/Pin.agda` (`veto ∘⁺ pick`: site order, FIFO, an empty queue `dead`; the concrete forms are `_∙_` and `sub` by `refl`), `Choice/Dist.agda` (§5.3, optional), `SSP/Protocol/Wire.agda` (`⌜⌝-∘`, `⌜⌝-⊗`, `interchangeᴵ`) |
| A1 | `CategoricalCrypto/ND/Relabel.agda` | §3.1: `Alph`, `++`, the SSP wires `⌈ρ⌉` (`⌜ m ⌝`, `ack`) | `⌈_⌉` a functor Alphᵒᵖ → `Prot` up to ≈ᵖ — **built**: `_⇝_`, `Alph`, `_++ʳ_`, the wires `⌈_⌉ʳ` with `⌈⌉ʳ-factor`, `⌈−⌉ʳ : Functor (Category.op Alph) Prot`, `⌈⌉ʳ-++` (§3.1) |
| A2 | `CategoricalCrypto/ND/A.agda` | §3.2: the class R and its closure, `𝒢A`, `incl`, `NDA`, `A⇒B` (G1's `unrestrict-≤UC` at `incl`) | `A⇒B : f ≤UC_A g → f ≤UC_B g`, all f, g |
| L1 | `CategoricalCrypto/ND/SSP/Laws.agda` | §5.1 at SSP; §3.4's swap; `collapse` against a callee | the swap instance as `≈ᵖ` |
| L2 (opt.) | `CategoricalCrypto/ND/Undesignate.agda` | §4: Φᵤ, B → A by `Between`, the retract | — |
| L3 (opt.) | `CategoricalCrypto/ND/SSP/Shuffle.agda` | §5.2: `_∥ᶜ_`, commutativity by relabelling | — |
| P1 | `CategoricalCrypto/UC/Model/Symmetric.agda` | §2.3: `𝔾ᵒ`'s braiding σᴳ, naturality, hexagon | a `SymmetricMonoidalCategory` over `∣𝔾ᵒ∣` |
| P2 | B1, A1, A2 at PM | choice factors ⊤ ⇿ S in `𝔾ᵒ`; PM's online B | — |

Order: G1 with G2 first (independent of ND; the causal-boxes plan's step 9 then imports G1), then B1–B2,
A1–A2, L1 over SSP; P1–P2 when PM's online B, or A at PM, is wanted.  Traps: the `refl`s of §1.5 against
`FromMonad`'s triple; one spelling of 𝒥's levels, ascribed, so that records are not eta-compared; ν is
`idᵛ`, so no `pullbackᵛ`; `𝔾ᵒ` is `opaque`, so P1 works on `𝒢ₚᴹ` and is sealed with it.

## 7. Sources

**Reused, archived** (`docs/kb/sources/papers/`, each with an `INDEX.md` line and a `refs.bib` entry):
**segala1995** (§5.2: perfect-information schedulers), **canetti2006taskpioa**
(abstract, §1: perfect information is too strong for security; task schedules for inessential choices),
**varacca2006** (§1), **zwart2019nogo** (§1, §3.1, Thms 3.5, 3.12), **bonchi2022** (§4.1–4.2, §5),
**canetti2015suc** (§1.3, §2.2: the router; delivery when the adversary instructs), **backes2007rsim**
(abstract, §1.3), **brzuska2018** (Lemma 3), **fujii2016** (graded monads as lax monoidal functors, so a
restriction of grades is a precomposition).  **In `refs.bib` only**: jsv1996 (the Int construction, as
`docs/uc-models.typ` cites it), canetti2020uc (UC's full version; blocked).  **Blocked**
(`docs/kb/sources/litreview/BLOCKED-URLS.md`): goy2020.  **Newly archived:** none.
