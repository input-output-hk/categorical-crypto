# The quantitative family layer

The ε-contextual relation on families of morphisms, the emulation bound at a
named simulator and schedule, its composition laws, and the machine instance
the examples use. Generic home: `UC.Quantitative.Contextual` (one level) and
`UC.Quantitative.Family` (families). Machine instance:
`UC.Model.Family.Contextual` (a module application) and
`UC.Model.Family.Emulation` (protocol images and the crossings out of the
layer). Paths are relative to `src/CategoricalCrypto/`.

## 1. The relation

### 1.1 One level

```agda
_≈ᵁᵠ[_]_ : A ⇒ X ⊗₀ B → (ℕ → ℚ) → A ⇒ X ⊗₀ B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≈ᵁᵠ[_]_ {A} {X} {B} f ε g =
  (W : Obj) (E : W ⊗₀ (X ⊗₀ B) ⇒ Ω) (m : 𝟙 ⇒ W ⊗₀ A) {c r′ : ℕ⁺}
  → Image forget c E → Image forget r′ m
  → ⟦ (E ∘ id ⊗₁ f) ∘ m ⟧ A.≈[ ε (value (c · r′)) ] ⟦ (E ∘ id ⊗₁ g) ∘ m ⟧
```

Every ancilla `W`, every test `E` certified at rate `c`, every closure `m`
certified at rate `r′`; the error schedule is read at the context's allowance
`value (c · r′)`.

**Only the test and the closure carry certificates; the compared morphisms do
not.** A certified simulator must not force every process it is compared with
to be certified. So the allowance indexes the *relation*, never the
computation category. A morphism a theorem moves into a context is asked for
its own `Image` certificate as a premise of that theorem (§2).

**It is the admitted agreement of the filtered space of tests.** `Agreeᵠ ε r r′`
is `Approx.Filtered._≈ᵃ[_]_` for `Query.filteredᵠ` at the schedule
`λ q r′ → ε (value (q · r′))`: two test-pullback maps that agree on the
*admitted* tests. `ctx⇒agree`/`agree⇒ctx` convert between the two forms. They
are not definitionally equal, because `_≈ᵁᵠ[_]_` takes the closure before the
test's certificate and `_≈ᵃ[_]_` takes the admittance first; they differ in
nothing else. The relation is not one `QUCSetup`'s `_≤UC_`, and cannot be made
one. A presheaf acting on every morphism of the base would need a budgeted
base, and then the uncertified compared homs would have no filtered structure
to act through. So the filtered structure sits only on the certified morphisms
a theorem moves.

The enrichment kit, levelwise from `Approx.Filtered`: `ctx-refl` (zero
schedule), `ctx-trans` (schedules add; both are explicit because unification
cannot split a sum), `ctx-mono`, `ctx-resp`. Zero error is the ambient hom
equality, observed exactly through the readout's `read-resp₀` (`cast₀`).

### 1.2 Families

```agda
Homᶠ : (A X B : ℕ → Obj) → Set ℓ
Homᶠ A X B = (n : ℕ) → A n ⇒ T₀ (X n) (B n)

_≈ctx[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
f ≈ctx[ ε ] g = (n : ℕ) → f n ≈ᵁᵠ[ ε n ] g n
```

Each level quantifies its own context. `≈C⇒≈ctx` (zero schedule from levelwise
hom equality) and `≈ctx-resp` are the family congruences.

### 1.3 The resource grading

The module takes a graded wide subcategory
`Rg : GradedSubCat Rates.monoidalCategory M qs` over the positive naturals
`ℕ⁺` (`Data.Nat.Positive`). A process certified at rate `r` is an `L.Hom r`,
read by `⌊_⌋`. Composition and `_⊗ʰ_` multiply rates, and the structural maps
sit at `1⁺`. A test is admitted at `c : ℕ⁺` by an `Image forget c E`
certificate, and a hom at its own rate by `(h , Equiv.refl)`. Zero-query tests
have no allowance of their own: every count that was ever used was a
quantified hypothesis or read off a rate. Error schedules stay indexed by `ℕ`
and are reindexed by `scale q r = q * value r`, with `scale-·`, `scale-comm`
and `scale-unit`. The family category and its monoidal structure are
`Categories.LocallyGraded.Family` at `Poly⁺` (`Families Rg ℕ (λ n → n) Poly⁺ …`).
Its homs `_⇒^ω_` carry a `Poly⁺` rate schedule `schedOf` with admissibility
`schedOf-adm`. Composition is `Fam [_∘_]`, the tensor `_⊗^ω_`, the unitor
`Famᴹ`'s `unitorˡ.from`.

At the machine, `UC.Model.Enrichment.gradingᵒ` is the grading.
`qbᵒ`/`qb-gradedᵒ` turn a machine query bound `UC.QueryBound.QB (value r) f`
into a `Pred r`, and `pred⇒image` turns that into an `Image forget r`.

## 2. Transport: moving a certified morphism into the context

Each plug is one absorption at every level. **Every allowance substitution is
an identity, not a bound**, so no theorem in this layer spends monotonicity of
`ε`: an arbitrary `NegligibleBound` has none.

```agda
≈ctx-sub : (s : Y ⇒^ω X) (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A Y B} → f ≈ctx[ ε ] g
         → subᶠ s f ≈ctx[ (λ n q → ε n (scale q (schedOf s n))) ] subᶠ s g

≈ctx-ext : (k : Homᶠ B P C) (rk : ℕ → ℕ⁺) → ((n : ℕ) → Image forget (rk n) (k n))
         → (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g
         → (k ∙ᶠ f) ≈ctx[ (λ n q → ε n (scale q (rk n))) ] (k ∙ᶠ g)

≈ctx-pre : (f : Homᶠ A X B) (rf : ℕ → ℕ⁺) → ((n : ℕ) → Image forget (rf n) (f n))
         → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ B P C} → u ≈ctx[ ε ] v
         → (u ∙ᶠ f) ≈ctx[ (λ n q → ε n (scale q (rf n))) ] (v ∙ᶠ f)
```

`≈ctx-sub` moves a simulator's action and `≈ctx-ext` a continuation into the
**test**. Both go through `ctx-absorb` and `absorb-testᵠ`, which is `pullᵠ`'s
allowance map. `scale-comm` (as `Query.absorb-test`) makes the substitution
exact. `≈ctx-pre` moves an earlier process into the **closure** through
`absorb-closureᵠ`, which is `pullᵠ`'s control. There the closure's rate is
multiplied, and `scale-·` (as `Query.absorb-closure`) makes it exact. `W`'s
context of `u ∙ᶠ f` is `(W ⊗ X)`'s context of `u` along `id ⊗ α⇐ ∘ α⇒`. The
only inexact-looking step, `q · 1 = q` for a structural leg, is `scale-unit`.

## 3. The witness forms

```agda
_≤UC[_,_]_ : Homᶠ A X B → Y ⇒^ω X → (ℕ → ℕ → ℚ) → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
f ≤UC[ s , ε ] g = f ≈ctx[ ε ] subᶠ s g

_≤UC^ωᵉ_ : Homᶠ A X B → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≤UC^ωᵉ_ {X = X} {Y = Y} f g =
  Σ[ s ∈ Y ⇒^ω X ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × f ≤UC[ s , ε ] g
```

A simulator is a `Fam` hom, i.e. a family certified levelwise at a `Poly⁺` rate
schedule. `sim s n = ⌊ hom s n ⌋` and `subᶠ s g n = sub (sim s n) ∘ g n`.

**The fixed-data bound `_≤UC[_,_]_` is the primary interface.** Every
composition theorem (§4) is proved at a named simulator and schedule and takes
no negligibility premise. `_≤UC^ωᵉ_` hides both and classifies the schedule as
negligible, and its lemmas (`≤UC^ωᵉ-resp`, `≤UC^ωᵉ-trans`) are a few lines each
over the fixed-data ones. A consumer that needs the number keeps the
`_≤UC[_,_]_` data. That is why the coin modules publish `coin-toss-idealᵇ`
beside `coin-toss-ideal` and `coin-toss-idealᴺ` (§6). The schedule does not
survive the crossing into the canonical negligible order either (§5.3).

## 4. The composition laws

```agda
seqError : Y ⇒^ω X → (ℕ → ℕ → ℚ) → (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
seqError s ε δ n q = ε n q ℚ.+ δ n (scale q (schedOf s n))

≤UC[]-trans : (s : Y ⇒^ω X) (t : Z ⇒^ω Y) (ε δ : ℕ → ℕ → ℚ)
              {f : Homᶠ A X B} {g : Homᶠ A Y B} {h : Homᶠ A Z B}
            → f ≤UC[ s , ε ] g → g ≤UC[ t , δ ] h → f ≤UC[ Fam [ s ∘ t ] , seqError s ε δ ] h

≤UC[]-dom : (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → Image forget 1⁺ (p n))
          → (s : Y ⇒^ω X) (ε : ℕ → ℕ → ℚ) {f : Homᶠ A X B} {g : Homᶠ A Y B}
          → f ≤UC[ s , ε ] g → (λ n → f n ∘ p n) ≤UC[ s , ε ] (λ n → g n ∘ p n)

composeError : (rf rtv : ℕ → ℕ⁺) → (ℕ → ℕ → ℚ) → (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
composeError rf rtv εf εu n q = εu n (scale q (rf n)) ℚ.+ εf n (scale q (rtv n))

≤UC[]-compose :
    {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
    (sf : Y ⇒^ω X) (t : Q ⇒^ω P) (rf rv : ℕ → ℕ⁺) (εf εu : ℕ → ℕ → ℚ)
  → ((n : ℕ) → Image forget (rf n) (f n)) → ((n : ℕ) → Image forget (rv n) (v n))
  → f ≤UC[ sf , εf ] g → u ≤UC[ t , εu ] v
  → (u ∙ᶠ f) ≤UC[ sf ⊗^ω t , composeError rf (λ n → rv n · schedOf t n) εf εu ] (v ∙ᶠ g)
```

- **Sequential.** The second comparison is pulled back along the first
  simulator (`Contextual.at-trans`), so `δ` is read at `scale q (schedOf s n)`,
  not at `q`, and the simulator is `Fam [ s ∘ t ]`.
- **Domain.** A process plugged under the domain at rate `1⁺` costs nothing:
  same simulator, same schedule. This closes a comparison boundary over an
  installed resource (the coin chain's `resᶠ`).
- **Graded.** `≤UC[]-compose` follows `Abstract2.UC-compose` at the identity
  adversary. `≈ctx-pre` moves `f` into the closure (`εu` at `scale q (rf n)`).
  `≈ctx-ext` moves the *simulated* continuation `subᶠ t v` into the test, at
  rate `rv n · schedOf t n`. Then `UC-compose`'s `strict-final` chain
  (`sub-commute₂`, `sub-commute₁`, `sub-homomorphism`) rewrites the right side
  to `sub (s₁ ⊗₁ t₁) ∘ …`, so the simulator is `Famᴹ`'s tensor `sf ⊗^ω t`. The
  certificates asked for are those of the two morphisms the proof moves, never
  of the compared homs.
- **Negligibility is split off.** `seqError-negligible` and
  `composeError-negligible` are where `NegligibleBound-scale` and
  `GradedBound-+[ Negligible ] Negligible-+` are spent, and where `Poly⁺ rf` /
  `Poly⁺ rtv` are consumed. `≤UC^ωᵉ-trans` packages the sequential law. No
  packaged existential form of `≤UC[]-compose` exists. Its consumers package it
  themselves at their own rates (`Examples.CoinToss.Compose.toss-over`).

## 5. The machine instance

### 5.1 The application

`UC.Model.Family.Contextual` applies `UC.Quantitative.Family` at the sealed
machine bundle:

```agda
open import CategoricalCrypto.UC.Quantitative.Family
  𝔾ᵒ gradingᵒ Q.approx Q.J Q.Ω Q.read Q.read-resp₀ public
```

with `Q = QEvaluation qevaluationᵒ` (`UC.Model.Observation`). The observation is
the quantitative readout of §7.

### 5.2 Protocol images

```agda
Systems : (ℕ → Iface) → Set₁
Systems B = (n : ℕ) → Protocol unitᴵ (B n)

imgᶠ : (B : ℕ → Iface) (R : Systems B) (n : ℕ) → 𝟘ᵒ ⇒ gradedᶠ B n
imgᶠ B R n = Gr.closedᵒ (morphism (R n))

_≈ᶠ[_]_ : Systems B → (ℕ → ℕ → ℚ) → Systems B → Set₁
_≈ᶠ[_]_ {B} R ε I = imgᶠ B R ≈ctx[ ε ] imgᶠ B I

_≈ᶠᴺ_ : Systems B → Systems B → Set₁
R ≈ᶠᴺ I = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × R ≈ᶠ[ ε ] I
```

`_≈ᶠᴺ_` is symmetric and simulator-free, at the trivial adversary grade
`Gr.𝟘ᴳ`. The simulator-bearing relation is `_≤UC^ωᵉ_`. No map between the two
exists in the tree. The ledger example is stated over `_≈ᶠᴺ_`, the coin chain
over `_≤UC^ωᵉ_`.

```agda
≈ᶠ-runs : (ε : ℕ → ℕ → ℚ) → R ≈ᶠ[ ε ] I
        → (n : ℕ) (q : ℕ⁺) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ (value q) d
        → runᴹ (morphism (R n)) d ≈ₚ[ ε n (value q) ] runᴹ (morphism (I n)) d
```

The adequacy step. It reads the premise at the context defined beside it:
the embedded strategy (`auditTest`, certified by `audit-qb` at the strategy's
own ask depth) behind the unitors, with closure `Gr.ιᴳ unitᴵ` at `1⁺`. Hence
`*-identityʳ`, and `audit-run` lands the premise's `ε` on the direct runs. The
cap is `ℕ⁺` because a context's allowance has no zero.

### 5.3 Leaving the layer

```agda
≈ctx⇒≈ℰ[] : {A X B : Obj^ω} (ε : ℕ → ℕ → ℚ) (f g : A ⇒^ω (X ⊛ω B))
          → sim f ≈ctx[ ε ] sim g → _≈ℰ[_]_ {A} {X ⊛ω B} f ε g
```

An implication, not an identification. `UC.Family._≈ℰ[_]_` quantifies
levelwise *families* of contexts carrying one polynomial rate, where
`_≈ctx[_]_` quantifies each level's context separately. `ε` is explicit, for
`UC.Approximate.GradedBound-+[_]`'s reason.

In `module _ {A X Y B : Obj^ω} (s : Y ⇒^ω X) (ε : ℕ → ℕ → ℚ) (neg : NegligibleBound ε) (f : A ⇒^ω (X ⊛ω B)) (g : A ⇒^ω (Y ⊛ω B)) (e : sim f ≤UC[ s , ε ] sim g)`:

```agda
≤UC[]⇒≈ℰⁿ : _≈ℰⁿ_ {A} {X ⊛ω B} f (Cᴺ.sub s Cᴺ.∘ g)
≤UC[]⇒≤UCᴺ : f Cᴺ.≤UC g
```

with `Cᴺ = UC.Family.Negligible.Canonicalᴺ`. The route is
`carried-negligible` into `_≈ℰⁿ_`, then `≈ℰⁿ⇒≈ℰᴺ`, then `dummy-complete` at `s`.
It does not pass through the vanishing collapse (`absorb`), so it lands in
the local-negligible setup, not only in `Canonical^ω`.

**What survives:** the certified simulator. **What does not:** the global
schedule. `≈ℰⁿ⇒≈ℰᴺ` specializes the one schedule to the allowance each context
carries, so `Canonicalᴺ._≤UC_` records only a negligible witness chosen inside
the context quantification, and no theorem recovers a global one from it. The
witness's `ε` is fixed before any context is seen. Nowhere is "∀ context, ∃
negligible ε" traded for "∀ allowance, ∃ ε, ∀ context".

## 6. Public theorem map

`Module :: name`, verified against `src/`. **Kind:** *def*, *uncond* (no
premise beyond the statement), *cond* (rests on a named premise), *inst*
(instantiated, nothing assumed), *neg* (refutation).

### 6.1 Generic

| Name | Kind | Notes |
|---|---|---|
| `UC.Quantitative.Family :: _≤UC[_,_]_`, `_≤UC^ωᵉ_` | def | §3 |
| `… :: ≤UC[]-trans`, `≤UC[]-dom`, `≤UC[]-compose` | uncond | §4; no negligibility, no `Poly⁺` |
| `… :: seqError-negligible`, `composeError-negligible` | uncond | the only places negligibility is spent |
| `… :: ≤UC^ωᵉ-resp`, `≤UC^ωᵉ-trans` | uncond | existential packaging |
| `UC.Model.Family.Emulation :: ≈ᶠ-runs` | uncond | adequacy at strategy contexts (§5.2) |
| `… :: ≈ctx⇒≈ℰ[]`, `≤UC[]⇒≈ℰⁿ`, `≤UC[]⇒≤UCᴺ` | uncond | one-way crossings (§5.3) |
| `UC.Machine.EventBounds :: bounded-absorb` | uncond | `f 𝒫.≈ subᴵ s 𝒫.∘ g → QB t s → AdvBoundedAt (k ℕ.* t) q r g → AdvBoundedAt k q r f`: the simulator's rate multiplies the *adversary's* allowance, and the context cap is untouched |

### 6.2 The ledger example (`Examples.ChimericLedger.{Property,Transfer}`, parameterised by `ser`)

The schedule is `εᴸ n q = fromℕ (q ℕ.* q ℕ.+ q) ℚ.* inv-pow-2 n`, with hash
width equal to the security parameter. The event layer (`Hitsᴺ`, `hitsᵘ`,
`hits⇒bounded`) and the proof path from the ideal birthday bound are in
`docs/state-event-contract.md`. Inside the `module _ (t : ℕ)` (watch total):

```agda
PreservesValue : Systems LedgerIf^ω → Set₁
PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴸ
```

`auditMonitorᶠ n = monitorᴹ (Watched.reportsLoss n t)`. The event read is the
monitor's flag, an interface message. No internal state is read, and the
compared system carries no certificate. The quantifiers are: polynomial cap
first, negligible slack second (uniform over every context the cap admits),
level third, context last.

| Name | Kind | Statement / notes |
|---|---|---|
| `Property :: ideal-preserves-value` | cond on `SerInj` | `SerInj → PreservesValue (genesisTotal V) Ideal`. Slack 0, through `boundedᶠ⇒boundedᴺ`. `Serialize.ideal-preserves-valueˢ` discharges `SerInj` for one encoding (`serInj`) |
| `Transfer :: preserves-value-transfer` | cond | `(a V : ℕ) (R : Systems LedgerIf^ω) → SerInj → R ≈ᶠᴺ Ideal a V → PreservesValue (genesisTotal V) R`. Ideal bound at the context's cap `p n`, comparison at `p n + 1` only because `≈ᶠ-runs` takes a positive cap. Slack `ν n = ε n (p n + 1)` |
| `Transfer :: hash-liftᵇ` / `hash-liftⁿ` | uncond | `hash ≈ᶠ[ ε ] oracle^ω → Realᴴ hash vr s ≈ᶠ[ εᴴ ε ] Realᴴ oracle^ω vr s` with `εᴴ ε n q = ε n (scale (scale q 1⁺) 1⁺)`. `≈ctx-ext` absorbs the ledger stage at rate `1⁺` (`ledgerᶠ-qb`), then `≈ctx-sub` absorbs the unit regrading. Both substitutions are exact. There is one upper stage, so there is no simulator to compose |
| `Transfer :: ledger-preserves-value-from-hash` | cond | `SerInj → hash ≈ᶠᴺ oracle^ω → PreservesValue (genesisTotal V) (Realᴴ hash inputConsuming (genesisAt a V))` |
| `Property :: preservesValue⇒saturated` | uncond | back to strategies at the same cap (`hits⇒bounded`); nothing is spent returning |
| `Property :: preservesValue⇒stateSafe` | cond on `TruthfulAudit` | `Hitsᴺ … ε → TruthfulAudit R bad → StateSafe R bad (λ n q → ε n (q ℕ.+ q))`. `withAudits` doubles the allowance |
| `Transfer :: ledger-uc-to-state`, `ledger-uc-to-hit-family`, `ledger-hit-family-negligible` | cond | state-event safety for a supplied `badR` at `λ n q → εᴸ n (q ℕ.+ q)`, as `StateSafe`, as `BoundedHitᴺ`, and as one negligible `f`. They rest on `SerInj`, the emulation, and `TruthfulAudit` |
| `Transfer :: ledger-conserves-value-from-hash` | cond | the same at the ledger's own `badTotal`, where `TruthfulAudit` is a theorem (`auditWatch-complete`) |
| `Property :: ideal-conserves-value` | cond on `SerInj` | `StateSafe Ideal badᴸ εᴸ`, straight from the birthday bound; no audit is spent |
| `Transfer :: ideal-spends-genesis` | inst | acceptance at probability `1ℚ` plus its state effect, at every level |
| `Transfer :: mute-preserves-value`, `mute-never-accepts` | inst | claim 1 does not imply responsiveness |
| `Transfer :: liar-preserves-value`, `liar-not-truthful` | inst | a trajectory conclusion needs `TruthfulAudit` |
| `Transfer :: chimeric-not-preserving` | neg | `(ε : ℕ → ℕ → ℚ) → NegligibleBound ε → ¬ Hitsᴺ (λ n → morphism (Chimericᶠ V n)) (auditMonitorᶠ (genesisTotal (suc (suc V)))) ε`. Probability 1 against `ε n 3 + ν n` at the replay strategy (`asks≤ 3`). Asymptotic, at an account-funded start (`funded-total`) |

### 6.3 The hash-forward toy (`Examples.HashForward.UC`)

`hf-bounded : AdvBoundedAt (k ℕ.* 2) q r ideal → AdvBoundedAt k q r real` is
`bounded-absorb real-factors simQB`. The simulator is retained and absorbed
into the adversary at rate 2. `real-factors` is an exact machine equality, so
there is no slack. `hf-exact`/`hf-pr-bound` are the same thing at one
strategy, one adversary and one closed input. *inst*.

### 6.4 The coin / commitment chain

| Name | Kind | Notes |
|---|---|---|
| `Examples.CoinToss.Compose :: coin-toss-from-comᵇ` / `coin-toss-from-com` | cond | `toss-over`: `≤UC[]-compose` with the toss stage compared with itself, simulator `simᶜᵗ sf = sf ⊗^ω Category.id Fam`, schedule `εᶜᵗ ε n q = 0ℚ ℚ.+ ε n (scale q 1⁺)` |
| `Examples.CoinToss.Ideal.Compose :: coin-hybridᵇ` | inst | second hop, exact: `≈C⇒≈ctx CTIU.coin-hop` at simulator `simᶜᶠ` (rate `1⁺`) and the zero schedule |
| `… :: coin-toss-idealᵇ` | cond | `realᶠ ≤UC[ sf , εf ] idealᶠ → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC[ simᶜⁱ sf , εᶜⁱ εf ] Fcoinᶠ`. `≤UC[]-dom` closes the boundary over the installed resource, then `≤UC[]-trans` |
| `… :: coin-toss-ideal`, `coin-toss-idealᶜ`, `coin-toss-idealᴺ` | cond | existential packaging; `ᶜ` narrows the premise to `realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ`; `ᴺ` crosses with `≤UC[]⇒≤UCᴺ`, keeping the simulator but not the schedule |
| `… :: ideal-ε` | inst | `εᶜⁱ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n`: the commitment's error, unrescaled |
| `Examples.CoinToss.Ideal.Receiver.Compose :: coin-hybridʳᵇ`, `coin-toss-idealʳᵇ`, `coin-toss-idealʳ`, `coin-toss-idealʳᴺ`, `ideal-εʳ` | cond / inst | the corrupted-receiver twin. Its second hop is not exact: only the runs agree, and carrying that into a context costs `ηʰ n _ = inv-pow-2 n`, so `ideal-εʳ` pins `fromℕ (q + (q + q)) *ℚ inv-pow-2 n ℚ.+ inv-pow-2 n` |
| `Examples.ROCommitment.Realization.Assembly :: assembly`, `assemblyʰ`, `pin`, `pinʰ` | cond on `Realization` | `Realization = Rcom ≤UC^ωᵉ Icom` at the resource-installed boundary is a hypothesis. `pin` is `refl` |
| `Examples.ROCommitment.Realization.Bound :: extraction-real` | inst, partial | bounds the closed real *machine* against the pruned ideal *game*; not a machine realization |

## 7. The observation the layer is stated over

`UC.Quantitative.Contextual` and `UC.Quantitative.Family` take a
`QEvaluation`: a reading `read : J ⇒ Ω → Carrier` into an approximate space,
with `read-resp₀`, which says it observes hom equality at error `0ℚ`.

- `UC.Core.Evaluation`: `J Ω S eval`, with `observe t m = read (t ∘ m)` and the
  test presheaf `ℰᴼ` (tests up to what they observe). `J` is not assumed to be the monoidal unit.
- `Approx.Evaluation.QEvaluation`: the reading lands in an approximate space and
  observes hom equality exactly (`eval₀` into `zeroSetoid`). `qualBy` coarsens
  only the equality: `qual₊` is closeness at every positive error. So `Evaluation.read (qualBy Q _ _)` *is*
  `QEvaluation.read Q`.
- Instances: `UC.Model.Observation.qevaluationᵒ` (the one this layer is applied
  at) with `evaluationᵒ = qual₊ ℚ-refinement qevaluationᵒ`,
  `UC.Family.QEvaluation^ω`, and
  `UC.Family.Negligible.Evaluationᴺ`, which is `qualBy` at the negligible class.
- Zero error (`Approx.Space.zeroSetoid`) and every positive error
  (`Approx.Error.AllPositive`) agree on carriers but not on equality
  (`Approx.Separating`), so an exact bound is not asked to respect the coarser one.

## 8. Deferred assumptions

1. **The real-hash premise.** `hash ≈ᶠᴺ oracle^ω`, the premise of
   `ledger-preserves-value-from-hash` and `ledger-conserves-value-from-hash`, is
   not discharged anywhere. `Examples.MerkleDamgard.indistinguishable` is a
   single-level `_≈adv[_]_` statement with no simulator, not a `_≈ᶠᴺ_` family
   premise, and nothing adapts one to the other.
2. **The commitment's emulation.** `Realization`/`Realizationʰ` are hypotheses,
   so `assembly` and every coin headline above them is conditional.
   `Examples.ROCommitment :: simStep` adds `(x , d)` to the simulator's log at
   every relayed answer, including one the oracle served from its table. After
   a repeated query `extract` reads `false`
   (`Realization.Bisim :: extract-relog` vs `extract-table`), while the game's
   bad event is a duplicate in the oracle's log, which a repeat does not raise.
   The ideal machine leg is blocked on this. The maintainer's options are in
   `docs/rcom-icom-b1.md` (row B2-M3).
3. **The chimeric verdict at the UTxO genesis.** `chimeric-not-preserving`
   refutes the property at an account-funded start, and
   `System.ledger-keeps-accts-[]` shows the UTxO genesis never funds an account
   (per activation; the induction along a run is not a theorem here). Whether
   the chimeric variant preserves value at the UTxO genesis is open.
