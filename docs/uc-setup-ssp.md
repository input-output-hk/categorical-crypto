# State-separating proofs as a UC setup

Plan, 2026-10-09. A1–A7, C1, C3 and part of C2 are built on branch `ssp-setup`; §6 records their names, warm
times and deviations. Every other claim about a module is a design claim. Line references are
to the `uc-setup-landscape` worktree.

## 1. Summary

**The deliverable** is the call/return discipline as a setup of its own:

- `SSP = Standard2.StdUC Protᴹ ℰᵖ` over `Protocol`s, in namespace `CategoricalCrypto.SSP` under the existing names (`Iface`, `Calls`, `Protocol`, `wireᵖ`, `_∘ᵖ_`, `_⊗ᵖ_`, `unitᴵ`, `Ωᴵ`).
- `Iface` is channel-indexed (`Ch`, `Q`, `R`); the flat `Pos ⇿ Neg` is the one-channel case.
- Equality is state simulation of call trees.
- Tests are closed protocols into `Ωᴵ`, read from one activation as a `Dist⊥ Bool`.
- No `Dₚ` and no `--guardedness`.

**Its link to protocol-model** (`UC/Model/Setup.agda`, "PM") goes through a variant of PM obtained by swapping parameters (table in §4.2):

```
SSP ──StdUCMorphism──▶ PM[wb] ◀──quotientF── 𝒲[ℰᵂ]          𝒲[ι*ℰᵒ] ──ι──▶ PM
```

- **𝒞 and ℐ:** all machines → the well-bracketed ones, `𝒲`.
- **ℰ:** `ℰᵒ` → the well-bracketed environments `ℰᵂ`. Neither presheaf is a sub-presheaf of the other on 𝒲, so `changeKernel` and `Factorization` do not apply.
- **Hom-equality:** `≈ᴹ` → `ℰᵂ`'s own two-sided ancilla kernel (`uKernel`). It is built with the RS plan's generic `Categories.Category.Monoidal.Construction.Quotient` and adds no new datum.

The two swaps beyond ℰ are forced:

- `ℰᵂ` is a presheaf only on 𝒲;
- a `StdUCMorphism`'s functor laws live at the target's equality.

**Headline lemmas** (§4.3). Under well-bracketed environments:

- **Lemma 1:** `morphism wireᵖ ≈ᵁ 𝒢.id`;
- **Lemma 2:** `morphism (P ⊗ᵖ Q) ≈ᵁ morphism P ⊗ morphism Q`.

These are exactly `F.identity` and `⊗-homo`. They are false in PM, and §4.1's two counterexamples are exactly the non-well-bracketed contexts that `ℰᵂ` removes.

**Escape hatch for asynchronous events:** pollable state (§5.2).

## 2. The source model

Packages and their algebra (brzuska2018 §2.1; ssprove2023 §3.3–3.4):

- **Package** (Def. 3): oracle definitions with private state, up to injective renaming of state variables.
  - Output interface `out(M)`, input interface `in(M)`; no internal calls.
  - Every program terminates (Def. 1). No `assert` is violated (§3, after Def. 9).
- **Sequential composition** (Def. 4): `M ∘ M′` is defined when `in(M) ⊆ out(M′)`, by inlining. `out(M ∘ M′) = out(M)`, `in(M ∘ M′) = in(M′)`. SSProve implements the inlining as an effect handler over a free monad of calls, sampling and state (ssprove2023 §3.3).
- **Identity** `ID_X` (Def. 5) forwards `X`. Lemma 2: `M = ID_out(M) ∘ M = M ∘ ID_in(M)`.
- **Parallel composition** (Def. 6) requires disjoint outputs; inputs may be shared.
- **Laws:**
  - `∘` is associative (Lemma 1);
  - `∥` is commutative and associative (Lemma 3);
  - interchange `(M₀ ∥ M₁) ∘ (M₀′ ∥ M₁′) = (M₀ ∘ M₀′) ∥ (M₁ ∘ M₁′)` (Lemma 4).
  - SSProve proves them as Coq propositional equality (§3.4).

Games and advantage (brzuska2018 §2.3; ssprove2023 §2.1):

- A **game** has `in(G) = ∅`. An **adversary** has `out(A) = {run}`, and `run` returns a bit (Def. 7).
- `ε_G(A) = |Pr[1 ← A∘G₀] − Pr[1 ← A∘G₁]|`, written `G₀ ≈^ε G₁` (Def. 8). **Perfect** means `ε = 0` for every adversary.
- Lemma 5 is the triangle inequality. Lemma 6 is `Pr[1 ← A∘(M∘G_b)] = Pr[1 ← (A∘M)∘G_b]`.

The same call/return algebra appears elsewhere:

- **CryptHOL constructive cryptography** (lochbihler2019cc §IV). Converters step through call trees. There are identity and embedding converters (§IV-B), parallel composition (Def. 2), and an interchange law for attachment (§IV-C). Interface typing is the coinductive predicate "respectfulness" (Defs. 1, 3), needed because tagging "does not enforce that the response is sent via the same interface as the query".
- **Maurer's invocation `C(F)`** (maurer2002 §3.3).

What the tree has today:

| SSP notion | in the tree | status |
|---|---|---|
| package `in = A`, `out = B` | `Protocol A B`, `Protocol.agda:59-63` | one channel only |
| call tree | `Calls`, `Protocol.agda:35-39` | the reply type does not depend on the query |
| `∘` | `_∘ᵖ_` (`graft`/`serve`), `Protocol.agda:73-95` | no laws: `Protocol` has no equality |
| `ID` | `wireᵖ`, `Protocol.agda:66-67` | no identity laws |
| `∥`, interchange | none (grep finds no `⊗ᵖ`) | **missing** |
| one-shot call | `OracleCall.Call`/`reCall`, `OracleCall.agda:14-35` | one channel; `reCall` untags the reply |
| adversary body | `Strat`, `Strategy.agda:24-27` | one `run` activation, without state or `dead` |
| compile to 𝔾ᵒ | `morphism`, `Protocol/Machine.agda:71-72`; `morphismCompose`, `Compose.agda:226-231` | preserves `∘`, not the identity (`:14-19`) |
| closed-run agreement | `prAgree`, `Agree.agda:101-112`; `adequacy`, `UC/Seam/Adequacy.agda:95-98` | present |

## 3. The `StdUC` instantiation

### 3.1 Objects: oracle signatures

`StdUC` over the **flat** `Protocol` is impossible.

- At `A ⊗ᴵ C`, a continuation receives `Pos A ⊎ Pos C` whatever it asked. So a lifted `P ⊗ᵖ P′` must send a reply from the other side to `dead`, while `wireᵖ` forwards it.
- Counterexample. The game answers everything with `inj₂ true`. The distinguisher asks on `inj₁` and outputs "reply came on `inj₂`". It gets Pr = 1 through `wireᵖ` and 0 through `wireᵖ ⊗ᵖ wireᵖ`.
- So `⊗.identity` fails even observationally. `OracleCall.reCall`'s "untag the reply" (`OracleCall.agda:31-35`) is the same partiality.

The reply type must depend on the channel. This is the maintainer's record, and it is CryptHOL's interface type turned into a type:

```agda
-- CategoricalCrypto/SSP/Iface.agda          {-# OPTIONS --safe --without-K #-}
import CategoricalCrypto.Iface as Flat
record Iface : Set₁ where
  field Ch : Set; Q R : Ch → Set               -- oracle names, argument and result types

unitᴵ Ωᴵ : Iface
unitᴵ = record { Ch = ⊥ ; Q = λ () ; R = λ () }
Ωᴵ    = record { Ch = ⊤ ; Q = λ _ → ⊤ ; R = λ _ → Bool }          -- the adversary's `run`

_⊗ᴵ_ : Iface → Iface → Iface                   -- disjoint oracle sets (CryptHOL's ⊕)
A ⊗ᴵ B = record { Ch = Ch A ⊎ Ch B ; Q = [ Q A , Q B ]′ ; R = [ R A , R B ]′ }

record _⇒ᴵ_ (A B : Iface) : Set where         -- CryptHOL's embeddings = container morphisms
  field ch : Ch A → Ch B
        qu : ∀ {c} → Q A c → Q B (ch c)
        re : ∀ {c} → R B (ch c) → R A c
-- idᴵ, _∘ᴵ_, _⊗ᴵᴵ_, ι₁ ι₂, ∇, λᴵ ρᴵ αᴵ αᴵ⁻¹ swapᴵ: pointwise, by case on Ch
-- (as built: one direction each; λᴵ and ρᴵ are inverted by ι₂ and ι₁)

oneᴵ : Flat.Iface → Iface                      -- today's Iface is the one-channel case
oneᴵ A = record { Ch = ⊤ ; Q = λ _ → Flat.Neg A ; R = λ _ → Flat.Pos A }
flat : Iface → Flat.Iface                      -- the machine layer's wire format
flat A = Σ (Ch A) (R A) Flat.⇿ Σ (Ch A) (Q A)
```

In container terms: `Shape = Σ Ch Q`, with positions that depend only on the channel. SSP's "named oracles" are exactly this.

- **Subset matching** is precomposition with `⌜ ι ⌝`.
- **Shared imports** (Def. 6) are `(M ⊗ᵖ M′) ∘ᵖ ⌜ ∇ ⌝`.
- **Reuse.** With `toProtocol : ⦃ DecidableEquality (Ch A) ⦄ → Protocol A B → Flat.Protocol (flat A) (flat B)` (each reply checked against the open call's channel; a mismatch gives `dead`), the existing `morphism`, `morphismCompose`, `prAgree` and `adequacy` are reused unchanged.

If the flat modules themselves became dependent:

- `Protocol.agda` takes the clauses of §3.2, `fromCall` works per channel, and `reCall` becomes precomposition with a `⇒ᴵ`.
- In `Protocol/Machine.agda:47-66`, `⟦_⟧ᴵ = ifaceᵒ ∘ flat`, `wait b a k` stores both channels, and `stepᴹ` tests `a ≟ a′` (a mismatch goes to `botₚ`).
- `Compose`, `Observe`, `Strategy` and `UC/Seam` carry channels in their `susp` states.
- `⟦_⟧ᴵ`/`retᴵ` stop being a definitional bijection (`UC/Machine.agda:5-7`), and `⊗ᵒ` stops being `refl` (`Seal.agda:86-87`).

This plan uses the parallel namespace; the migration cost is listed as a risk in §5.1.

### 3.2 Calls, protocols, composition, identity, tensor

```agda
-- CategoricalCrypto/SSP/Protocol.agda       {-# OPTIONS --safe --without-K #-}
data Calls (A : Iface) (X : Set) : Set where
  ret  : X → Calls A X
  call : (c : Ch A) → Q A c → (R A c → Calls A X) → Calls A X
  coin : Dist-ℚ Bool → (Bool → Calls A X) → Calls A X
  dead : Calls A X                               -- abort (SSP's violated assert)

record Protocol (A B : Iface) : Set₁ where
  field St : Set; init : St
        step : St → (c : Ch B) → Q B c → Calls A (St × R B c)

module _ (P₂ : Protocol B C) (P₁ : Protocol A B) where
  mutual   -- `Protocol.agda:73-88`, generalised over the answer type Y
    graft : Calls B (St P₂ × Y) → St P₁ → Calls A ((St P₂ × St P₁) × Y)
    graft (ret (s₂ , y)) s₁ = ret ((s₂ , s₁) , y)
    graft (call b q k)   s₁ = serve k (step P₁ s₁ b q)
    graft (coin μ k)     s₁ = coin μ λ x → graft (k x) s₁
    graft dead           s₁ = dead
    serve : (R B b → Calls B (St P₂ × Y)) → Calls A (St P₁ × R B b) → Calls A ((St P₂ × St P₁) × Y)
    serve k (ret (s₁ , r)) = graft (k r) s₁
    serve k (call a q k₁)  = call a q λ r → serve k (k₁ r)
    serve k (coin μ k₁)    = coin μ λ x → serve k (k₁ x)
    serve k dead           = dead
  _∘ᵖ_ : Protocol A C
  _∘ᵖ_ = record { St = St P₂ × St P₁ ; init = init P₂ , init P₁
                ; step = λ (s₂ , s₁) c q → graft (step P₂ s₂ c q) s₁ }

⌜_⌝ : A ⇒ᴵ B → Protocol B A                    -- relabelling wire
⌜ m ⌝ = record { St = ⊤ ; init = tt ; step = λ _ c q → call (ch m c) (qu m q) λ r → ret (tt , re m r) }
wireᵖ : Protocol A A
wireᵖ = ⌜ idᴵ ⌝

reindex : A ⇒ᴵ A′ → Calls A X → Calls A′ X    -- calls forwards, replies backwards
_⊗ᵖ_ : Protocol A B → Protocol C D → Protocol (A ⊗ᴵ C) (B ⊗ᴵ D)
P ⊗ᵖ P′ = record { St = St P × St P′ ; init = init P , init P′ ; step = λ where
  (s , t) (inj₁ b) q → mapᶜ (λ (s′ , r) → (s′ , t) , r) (reindex ι₁ (step P s b q))
  (s , t) (inj₂ d) q → mapᶜ (λ (t′ , r) → (s , t′) , r) (reindex ι₂ (step P′ t d q)) }
```

- `R (B ⊗ᴵ D) (inj₁ b)` *is* `R B b`, so no `dead` branch is needed.
- While `P` serves a query, a query to `P′` cannot be written down: control is a single thread.

### 3.3 Hom-equality

```agda
data _≈ᶜ_ {A X} : Calls A X → Calls A X → Set where       -- extensional tree equality (no funext)
  ret  : x ≡ x′ → ret x ≈ᶜ ret x′
  call : (∀ r → k r ≈ᶜ k′ r) → call c q k ≈ᶜ call c q k′
  coin : (∀ b → k b ≈ᶜ k′ b) → coin μ k ≈ᶜ coin μ k′
  dead : dead ≈ᶜ dead

record _≲ᵖ_ (P P′ : Protocol A B) : Set where             -- `Machines/Sim.agda:39-44`, one level up
  field θ      : St P → St P′
        θ-init : θ (init P) ≡ init P′
        θ-step : ∀ s c q → mapᶜ (map₁ θ) (step P s c q) ≈ᶜ step P′ (θ s) c q

_≈ᵖ_ : Rel (Protocol A B) (suc 0ℓ)
_≈ᵖ_ = EqClosure _≲ᵖ_                                       -- a setoid; no quotient
Prot-setoid : Iface → Iface → Setoid (suc 0ℓ) (suc 0ℓ)
Prot-setoid A B = record { Carrier = Protocol A B ; _≈_ = _≈ᵖ_ ; isEquivalence = EqC.isEquivalence _≲ᵖ_ }
```

- SSP's renaming of state is the case of bijective `θ`; every law holds with a functional `θ`.
- Rejected alternatives:
  - *Syntactic equality*: the two sides have different state types (`⊤ × St` against `St`).
  - *Relational bisimulation with couplings* (lochbihler2019cc Def. 4): coarser and not needed, and it cannot reach `≈ᴹ` without a quotient (landscape §4).
  - *Pullback of `≈ᴹ` along `morphism`*: not a `⊗ᵖ`-congruence (§4.1).
- **Consequence for `F-resp-≈`** (corrected while building A1–A7). `θ ↦ MSt-map θ` is *not* a machine simulation, so `morphism-resp` is not one induction on `drive`. A `wait` state stores the continuation: where `step P′ (θ s)` reaches `wait k′`, `MSt-map θ` gives `wait (mapᶜ (map₁ θ) ∘ k)`, and the two are only `≈ᶜ`-equal pointwise. `≈ₚ` quantifies over every test of the states (`Dp.agda:427-431`), so without funext the machine step square does not close. `morphism-resp` needs the `Protocol/Machine/Compose.agda:12-19` technique instead: a third machine on pairs of `≈ᶜ`-related configurations, stepped in lockstep along the `≈ᶜ` proof, with both projections as simulations out of it.

### 3.4 The monoidal category

```agda
-- CategoricalCrypto/SSP/Protocol/Category.agda, …/Monoidal.agda (as built)
Prot : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)                    -- Categories.Category.EquivClosureHelper
Prot = categoryHelperᵉ record                                  -- laws at _≲ᵖ_; _≈_ = EqClosure _≲ᵖ_ = _≈ᵖ_
  { Obj = Iface ; _⇒_ = Protocol ; _≈_ = _≲ᵖ_ ; id = wireᵖ ; _∘_ = _∘ᵖ_
  ; assoc = ∘ᵖ-assoc h g f ; identityˡ = wireᵖ-identityˡ f ; identityʳ = wireᵖ-identityʳ f
  ; ∘-resp-≈ = ∘ᵖ-resp-≲ᵖ }                                    -- one joint simulation, θ = map θ₁ θ₂

Protᴹ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
Protᴹ = record { U = Prot ; monoidal = monoidalHelper Prot record
  { ⊗ = ⊗ᵖ-bifunctor                                           -- ⊗ᵖ-identity, ⊗ᵖ-homomorphism, ⊗ᵖ-resp-≈ᵖ
  ; unit = unitᴵ
  ; unitorˡ = ⌜ ι₂ ⌝ / ⌜ λᴵ ⌝ ; unitorʳ = ⌜ ι₁ ⌝ / ⌜ ρᴵ ⌝ ; associator = ⌜ αᴵ⁻¹ ⌝ / ⌜ αᴵ ⌝   -- from / to
  ; unitorˡ-commute = ⌜⌝-natˡ f ; unitorʳ-commute = ⌜⌝-natʳ f ; assoc-commute = ⌜⌝-natα f g h
  ; triangle = … ; pentagon = … } }                            -- ≲ᵖ-const, by computation per channel
```

| law | proof (all simulations, all structural inductions) |
|---|---|
| `wireᵖ-identityˡ/ʳ` (Lemma 2) | `θ = proj₂`/`proj₁`; one induction on the call tree |
| `∘ᵖ-assoc` (Lemma 1) | `θ = assocʳ′`; three mutual lemmas (`graft-graft`, `graft-serve`, `serve-serve`) on the termination pattern `Protocol.agda:73-88` already passes |
| `∘ᵖ-resp-≲ᵖ`, `⊗ᵖ-resp-≲ᵖ` | one joint simulation each (`graft-sim`/`serve-sim`; `reindex-sim`); `≈ᵖ` versions by `EqC.gmap` per argument |
| `⊗ᵖ-identity` | `θ = const tt`: `reindex ι₁ (call c q k)` reduces to `call (inj₁ c) q k` |
| `⊗ᵖ-homomorphism` (Lemma 4) | `θ` = the middle-four iso; per side, `graft`/`serve` commute with `mapᶜ ∘ reindex ιᵢ` (two mutual lemmas each) |
| unitors, associator, coherence | `⌜ m ⌝` is contravariant, so `λ⇒ = ⌜ ι₂ ⌝`, `ρ⇒ = ⌜ ι₁ ⌝`, `α⇒ = ⌜ αᴵ⁻¹ ⌝`. Iso laws, triangle and pentagon are wires against wires: `≲ᵖ-const` and one `≈ᶜ-refl` per channel case, so no `⌜⌝-∘`/`⌜⌝-⊗`/`⌜⌝-above`/`⌜⌝-below` is needed. Naturality: `⌜⌝-natˡ`/`⌜⌝-natʳ` slide the wire through the factor's step tree (one induction; they hold for an arbitrary discarded factor, not only `unitᴵ`), `⌜⌝-natα` one induction per channel group |

- **Lemma 3** (optional): braiding `⌜ swapᴵ ⌝` gives `Protˢ`.
- **The unit is terminal**: all protocols `A → unitᴵ` are `≈ᵖ`. So `⌜ ι ⌝` is SSP's discard.

### 3.5 The test presheaf

```agda
-- CategoricalCrypto/SSP/Observation.agda    {-# OPTIONS --safe --without-K #-}
evalC : Calls unitᴵ X → Dist⊥ X                -- `Protocol/Observe.agda:41-45`
evalC (ret x) = return⊥ x ; evalC (call () _ _) ; evalC (coin μ k) = μ >>=ᴹ λ b → evalC (k b)
evalC dead = return-ℚ nothing

runᵖ : Protocol unitᴵ Ωᴵ → Dist⊥ Bool          -- the adversary's whole interaction is ONE activation
runᵖ W = evalC (mapᶜ proj₂ (step W (init W) tt tt))   -- as built: = Dmap⊥ proj₂ (evalC …), map kept on the tree

Approximation⊥ : Approximation (Dist⊥ Bool) ℚ-ordered 0ℓ      -- `Approx/Error.agda:61-72`
Approximation⊥ = record { _≈[_]_ = λ μ ε ν → (b : Bool) → advᵇ⊥ b μ ν ≤ ε
  ; ≈[]-refl = 0 by ∣x-x∣ ; ≈[]-sym = advᵇ⊥-sym ; ≈[]-trans = advᵇ⊥-triangle + ≤-trans ; ≈[]-mono = ≤-trans }

qevaluationᵖ : QEvaluation Prot 0ℓ 0ℓ         -- `Approx/Evaluation.agda:36-51`
qevaluationᵖ = record { J = unitᴵ ; Ω = Ωᴵ ; X = record { Carrier = Dist⊥ Bool ; approx = Approximation⊥ }
                      ; eval₀ = record { to = runᵖ ; cong = ≈Mℚ⇒≈[0] ∘ runᵖ-resp } }
-- as built: runᵖ-resp : W ≈ᵖ W′ → runᵖ W ≈Mℚ runᵖ W′ (exact; EqC.gfold of runᵖ-sim), ≈Mℚ⇒≈[0] turns it into zero error
evaluationᵖ : Evaluation Prot 0ℓ 0ℓ
evaluationᵖ = qual₊ ℚ-refinement qevaluationᵖ    -- the `UC/Model/Observation.agda:69-76` pattern
```

- `UC/Core.agda:Evaluation` is reused as `UC/Model/Observation.agda` does.
  - Tests at `A` are distinguishers `A ⇒ Ωᴵ`; closures `unitᴵ ⇒ A` are games.
  - So `≈ℰ` is SSP's perfect indistinguishability in every game context.
  - The pull-back along `M` sends `D` to `D ∘ᵖ M`. So Lemma 6 is the presheaf law `pull-∘` (`UCSetup.agda:116-118`).
- `J` is the monoidal unit itself; UC/Model spells it differently (`UC/Model/Observation.agda:15-22`).
- The readout compares **both** verdicts (`Protocol/Observe.agda:163-169`), so `dead` is not identified with answering `false`.
  - SSProve compares `Pr[true]` only (ssprove2023 §3.2). The two agree when nothing aborts.
- Rational masses make `qual₊` coincide with `qual`.
- **Levels:** `ℰᵖ : Presheaf Prot (Setoids (suc 0ℓ) (suc 0ℓ))`, the same as `ℰᵒ`.

### 3.6 The setup, OPTIONS and module layout

```agda
{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.SSP.Setup where
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol.Monoidal
open import CategoricalCrypto.UC.Core
import CategoricalCrypto.Standard2 as Std2
open Evaluation evaluationᵖ public
open Observable observable public using (Test; _≋_; ℰ₀) renaming (≈⇒≋ to ≈ᵖ⇒≋; ℰᴼ to ℰᵖ)
open Std2.StdUC Protᴹ ℰᵖ public     -- StdSetup : UCSetup (suc 0ℓ) … (suc 0ℓ), all eight levels
```

- Under `src/CategoricalCrypto/SSP/`: `Iface`, `Protocol`, `Protocol/Category`, `Protocol/Monoidal`, `Observation`, `Setup`, optionally `Reduction`, and the test leaf `Pin` (refl pins of `runᵖ` and `observe`). All are `--safe --without-K`. None is imported by the root `src/CategoricalCrypto.agda`.
- The modules of §4 add `--guardedness`.
- In the grade reading, `T₀ X B = X ⊗ᴵ B` is a protocol that also exports adversary oracles `X`. `sub c` puts a simulator protocol on them, so `≤UC` reads "for every adversary-side protocol there is a simulator".

## 4. Morphisms

### 4.1 Into PM with `F = morphism`: the two obstructions

This is what `StdUCMorphism` would need; it does not typecheck at the two ✗:

```agda
F : StrongMonoidalFunctor Protᴹ 𝔾ᵒ            -- needs DecidableEquality on every `Ch`
F = record { F = record { F₀ = ifaceᵒ ∘ flat ; F₁ = procᵒ ∘ morphism ∘ toProtocol
                        ; identity = ✗ ; homomorphism = …morphismCompose… ; F-resp-≈ = …morphism-resp… }
           ; isStrongMonoidal = record { ε = …𝔾ᵒ.unit ≅ ifaceᵒ (flat unitᴵ)…
                                       ; ⊗-homo = …flat A ⊗ flat B ≅ flat (A ⊗ᴵ B), naturality ✗… ; … } }
SSP→PM = StdUCMorphism Protᴹ 𝔾ᵒ ℰᵖ ℰᵒ F ν            -- κ = Oplax.δ F, `Standard2/Morphism.agda:39-55`
```

| obligation | status | lemma |
|---|---|---|
| `F-resp-≈` | true, new | `morphism-resp` + `toProtocol-resp` |
| `F.homomorphism` | true | `Protocol.Machine.Compose.morphismCompose` (`:226-231`) + new `toProtocol-∘`; across the seal by `procᵒ-∘` (`Seal.agda:116-118`) as in `UC.Seam.Grounded.factorᵖ` (`:76-81`) |
| `F.identity` | **false** | `morphism wireᵖ ≉ᴹ σ⇒` (`Protocol/Machine.agda:14-19`) |
| `ε` | true, costly | `𝟘ᵒ` against the unit spelling, >150 s (`UC/Model/Observation.agda:15-22`) |
| `⊗-homo` naturality | **false** | `_⊗ᵉ_` serves either factor whatever the other's state (`Machines/Tensor.agda:98-99`) |

Both failures are observable through an ancilla `Y`, which is the context `≈ᵁ` quantifies over.

- **Identity.** Closure `m : 𝟘 → Y ⊗ A` answers a `Y`-query with an `A`-reply nobody asked for. Test `t` asks `Y` on the tick and outputs `true` on any `A`-reply. Through `σ⇒`, Pr[true] = 1. Through `morphism wireᵖ` the run goes to `botₚ`: Pr = 0.
- **Tensor.** `P` makes one call per query; `P′` answers at once. On `P`'s call, `m` passes control to `t` through `Y`, and `t` asks `P′`.
  - The 𝔾 tensor answers: Pr = 1.
  - `morphism (P ⊗ᵖ P′)` is waiting, and the query goes to `botₚ`: Pr = 0.

In both counterexamples the culprit is an environment that is **not well-bracketed**:

- `m` emits on a channel that has no open query;
- or `m` answers on `Y` while `P`'s call is open.

The `κ`-laws come from strong monoidality and are moot here.

### 4.2 The well-bracketed variant `PM[wb]`

```agda
-- CategoricalCrypto/UC/Bracket.agda         {-# OPTIONS --safe --without-K --guardedness #-}
module _ {A B : SSP.Iface} where             -- Proc (flat A) (flat B), `UC/Machine.agda:62-63`
  data Phase : Set where
    idle : Phase ; serving : Ch B → Phase ; calling : Ch B → Ch A → Phase
  data Opp : Phase → Flat.Pos (flat A) ⊎ Flat.Neg (flat B) → Phase → Set where   -- legal environment moves
    query  : Opp idle (inj₂ (b , q)) (serving b)
    return : Opp (calling b a) (inj₁ (a , r)) (serving b)                        -- on the same channel a
  data Ply : Phase → Flat.Neg (flat A) ⊎ Flat.Pos (flat B) → Phase → Set where   -- ours: call below, or answer on b
    call   : Ply (serving b) (inj₁ (a , q)) (calling b a)
    answer : Ply (serving b) (inj₂ (b , r)) idle
  record W (f : Proc (flat A) (flat B)) : Set₁ where           -- on legal plays, play legally
    field I      : MC.St f → Phase → Set
          I-init : ∀ n → Supp n (MC.point (MC.state f) tt) λ s → I s idle
          I-step : I s φ → Opp φ x φ′ → ∀ n → Supp n (MC.step f (s , x)) (Legal I φ′)
-- as built: Phase/Opp/Ply/Legal take A B as (implicit) parameters; Legal I φ′ (s′ , y) = Σ[ φ″ ∈ Phase A B ] Ply φ′ y φ″ × I s′ φ″
```

- `W` is CryptHOL's respectfulness (lochbihler2019cc Def. 3) moved to 𝔾ᵒ.
- `morphism-W : W (morphism (toProtocol P))`, with invariant `I (idle s) idle` and `I (wait k) (calling b a) = ∀ r → Bracketed B b (k (a , r))`. The proof is one induction on `drive` (as built: `UC/Bracket`).

Closure under the 𝔾ᵒ structure:

- **`σ⇒`** is copycat.
- **`∘`** carries the invariant `Σ b. I_g (calling c b) × I_f (calling b a)` between activations, and needs a new Dp lemma `Supp-iterₚ`.
- **`⊗`** works because a legal environment has one open query.
- **Relabelling wires** preserve channels.
- **But `SetupSubcategory.W-sub`** (`WideSubcategory.agda:58`) ranges over every grade morphism of ℐ = 𝔾ᵒ, and an undisciplined simulator breaks it. Moreover the discipline needs channels, which bare 𝔾ᵒ objects lack.
- So **`𝒲ᴹ`** is the *monoidal* form of a `SetupSubcategory`: the same closure fields (`:52-60`) plus `⊗`, with ℐ restricted together with 𝒞. Objects are `SSP.Iface`, mapped in by `ifaceᵒ ∘ flat`; homs are `W`-machines.
- **Its inclusion** is `StdUCMorphism 𝒲ᴹ 𝔾ᵒ (ι*ℰᵒ) ℰᵒ ιᴹ (pullbackᵛ ι ℰᵒ)`.
  - It has the shape of `Restriction.inclusion` (`:118-131`: `F = ι`, `κ = id`), except `Φ = ιᴹ` instead of `idF-Monoidal ℐ`.
  - `pullbackᵛ` is Epi and Mono, so `≈ℰ` crosses both ways (`Abstract2/Morphism.agda:48-52`).

```agda
-- CategoricalCrypto/UC/Bracket/Setup.agda: well-bracketed environments on 𝒲
evaluationᵂ : Evaluation ∣𝒲ᴹ∣ 0ℓ 0ℓ          -- tests and closures are 𝒲-morphisms, i.e. W-machines
evaluationᵂ = qual₊ ℚ-refinement record { J = unitᴵ ; Ω = Ωᴵ ; X = spaceᴹ ; eval₀ = …Obs, obs-resp… }
ℰᵂ = Observable.ℰᴼ (Evaluation.observable evaluationᵂ)

-- CategoricalCrypto/Standard2/UKernel.agda (generic, new, --safe --without-K): a two-sided ancilla kernel
open import Categories.Category.Monoidal.Construction.Quotient     -- docs/uc-setup-random-systems.md §3.4
uKernel : (𝕄 : MonoidalCategory o ℓ e) (ℰ : Presheaf (U 𝕄) (Setoids cs ℓs)) → MonoidalCongruence 𝕄 (o ⊔ cs ⊔ ℓs)
uKernel 𝕄 ℰ = record
  { _∼_      = λ f g → ∀ Y Z → (id {Y} ⊗₁ f) ⊗₁ id {Z} ≈ℰ (id {Y} ⊗₁ g) ⊗₁ id {Z}
  ; ∼-equiv  = ≈ℰ-refl/sym/trans pointwise ; ≈⇒∼ = λ e Y Z → ≈C⇒≈ℰ (… ⊗-resp-≈ e …)
  ; ∘-resp-∼ = ⊗ functoriality + ≈ℰ-cong-pre/post        -- no unit-grade plumbing
  ; ⊗-resp-∼ = a factor beside f is absorbed into an ancilla, up to α }   -- no braiding needed (𝔾ᵒ exports none)
∼⇒≈ℰ : f ∼ g → f ≈ℰ g          -- Y = Z = unit, unitors; so ℰ descends.  ∼⇒≈ᵁ: Z = unit

PM[wb]ᴹ = quotient 𝒲ᴹ (uKernel 𝒲ᴹ ℰᵂ)
ℰ[wb]   = descend 𝒲ᴹ (uKernel 𝒲ᴹ ℰᵂ) ℰᵂ ∼⇒≈ℰ
open Std2.StdUC PM[wb]ᴹ ℰ[wb] public                          -- PM[wb]
q = StdUCMorphism 𝒲ᴹ PM[wb]ᴹ ℰᵂ ℰ[wb] (quotientF 𝒲ᴹ _) (descendᵛ 𝒲ᴹ _ ℰᵂ ∼⇒≈ℰ)   -- 𝒲[ℰᵂ] → PM[wb]
```

**PM[wb] against PM, parameter by parameter.** The ℰ swap forces the 𝒞/ℐ swap; the functor laws force the equality swap.

| parameter | PM | PM[wb] | how | why it has to change |
|---|---|---|---|---|
| 𝒞, ℐ | `∣𝔾ᵒ∣`, `𝔾ᵒ` | `𝒲ᴹ`: `W`-machines on `SSP.Iface` | monoidal `SetupSubcategory` form + `ιᴹ` | for an undisciplined `f`, `t ∘ f` is not a well-bracketed test and `f ∘ m` is not a well-bracketed closure, so no well-bracketed presheaf exists on all of `∣𝔾ᵒ∣`; `W-sub` (`:58`) forces ℐ down too |
| ℰ | `ℰᵒ` (`ι*ℰᵒ` on 𝒲): all tests, all closures | `ℰᵂ`: `W`-tests, `W`-closures | new presheaf on 𝒲 | the reason neither is a sub-presheaf is given below the table |
| hom-equality | `≈ᴹ` | `∼` of `uKernel 𝒲ᴹ ℰᵂ`, which lies between `≈ᴹ` and `≈ᵁ` | `quotient`/`quotientF`/`descend`/`descendᵛ` | a `StdUCMorphism`'s `F` is a functor at the target's equality; with `≈ᴹ`, `F.identity` (`morphism wireᵖ ≈ᴹ σ⇒`) is false whatever ℰ is |

**Why neither ℰ is a sub-presheaf of the other.**

- **`ℰᵂ ⊄ ι*ℰᵒ`.** The carriers are included (`W`-tests ⊂ tests), but `ℰᵂ`'s equality is coarser. Two `W`-tests that differ only in their reaction to a reply on the wrong channel agree on every `W`-closure, but not on an undisciplined one. So the inclusion is not a setoid map, let alone Mono.
- **`ι*ℰᵒ ⊄ ℰᵂ`.** Its carriers contain non-`W` tests.
- **No natural `ν` in either direction.** `ℰᵂ → ι*ℰᵒ` is ill-defined by the same pair. `ι*ℰᵒ → ℰᵂ` must monitor arbitrary tests (`t ↦ t ∘ e`), and that is not natural: at a `W`-morphism `f`, `t ∘ f ∘ e` and `t ∘ e ∘ f` differ when `t` misbehaves.
- Hence neither `changeKernel` (`UCSetup/Morphism.agda:48-51`) nor `Factorization` (`:101-114`, images of an existing `ν`) reaches PM[wb].

The quotient changes no contexts and no kernel, so `≤UC` in PM[wb] is `≤UC` in `𝒲[ℰᵂ]`, and `q` transports it both ways.

### 4.3 `SSP → PM[wb]`: the main line

The two headline lemmas, with `e A = morphism (toProtocol (wireᵖ {A}))`, `m = morphism ∘ toProtocol`, and `∼` the kernel of `uKernel 𝒲ᴹ ℰᵂ` (well-bracketed tests and closures, any ancillas on both sides):

- **Lemma 1 (`wire≈σ`):** `m (wireᵖ {A}) ∼ σ⇒`, i.e. `morphism wireᵖ ≈ᵁ 𝒢.id` under well-bracketed environments.
- **Lemma 2 (`⊗≈⊗`):** `m (P ⊗ᵖ P′) ∼ ρ ∘ (m P ⊗ m P′) ∘ ρ⁻¹`, where `ρ` is the stateless flat relabelling `wireᴹ` (`UC/Machine.agda:107-108`); i.e. `morphism (P ⊗ᵖ Q) ≈ᵁ morphism P ⊗ morphism Q`.

```agda
-- CategoricalCrypto/SSP/Semantics.agda      {-# OPTIONS --safe --without-K --guardedness #-}
Fᵂ : StrongMonoidalFunctor Protᴹ PM[wb]ᴹ      -- F₀ = id;  F₁ P = m P , morphism-W P
                                                -- identity = wire≈σ;  ⊗-homo = ρ with ⊗≈⊗
νᵂ : PresheafMorphism (StrongMonoidalFunctor.F Fᵂ) ℰᵖ ℰ[wb]
νᵂ = record { ν = ntHelper record { η = λ A → record { to = λ D → m D , morphism-W D ; cong = games-dense }
                                  ; commute = λ f → ≈ᴹ⇒≋ (morphismCompose …) } }
SSP→PM[wb] : UCSetupMorphism SSP.StdSetup PM[wb].StdSetup
SSP→PM[wb] = StdUCMorphism Protᴹ PM[wb]ᴹ ℰᵖ ℰ[wb] Fᵂ νᵂ      -- κ = Oplax.δ Fᵂ
```

| obligation | status | needs |
|---|---|---|
| `F-resp-≈` | true | `morphism-resp` → `≈ᴹ` → `∼` (`≈⇒∼`) |
| `F.homomorphism` | true | `morphismCompose` + `toProtocol-∘`, then `≈⇒∼` |
| `F.identity` | **Lemma 1** | see below |
| `⊗-homo` | **Lemma 2** | see below |
| `ε`, associativity, unitality | true | relabelling wires are stateless `W`-machines; `J` is the unit |
| `ν.cong` / `ν.commute` | true | `games-dense` (§5.1) / `morphismCompose` |

Both lemmas are false in PM. The contexts `∼` excludes are exactly §4.1's two counterexamples:

- a closure that emits on a channel with no open query;
- a closure that answers on `Y` while `P`'s call is open.

The lemmas need:

- **`monitor-invisible`** (`e` is `σ⇒` on legal plays and `botₚ` at the first violation):
  - statement: for ancillas `Y`, `Z` and `W`-machines `t`, `m′`, `X`: `Obs (t ∘ ((Y ⊗ X) ⊗ Z) ∘ m′) ≈ₚ Obs (t ∘ ((Y ⊗ (e ∘ X ∘ e)) ⊗ Z) ∘ m′)`;
  - inputs: `W`'s invariants, `Supp-iterₚ`, and the corecursive attachment of support proofs (`Supp ⇒ Dₚ (Σ A P)`);
  - proof: a reachable-configuration simulation into both closed composites (the `machineᶜ` technique, `Compose.agda:12-19`), then `runᴹ-resp-≈ᴹ` (`UC/Machine/Run.agda:116-118`).
- **For Lemma 1:** `e ∘ e ≈ᴹ e` and `e ∘ σ⇒ ∘ e ≈ᴹ e`, from `morphismCompose` and `wireᵖ ∘ᵖ wireᵖ ≈ᵖ wireᵖ` through `toProtocol-∘`.
- **For Lemma 2:** `⊗-monitor : e (B ⊗ᴵ D) ∘ ρ ∘ (m P ⊗ m P′) ∘ ρ⁻¹ ∘ e (A ⊗ᴵ C) ≈ᴹ e (B ⊗ᴵ D) ∘ m (P ⊗ᵖ P′) ∘ e (A ⊗ᴵ C)`. It is a reachable-configuration simulation whose states are "both idle" or "one side waiting"; a legal environment never interleaves.

**Alternative (one paragraph).** A morphism *into PM itself* whose `F` extends `morphism` exists only from `Termᴹ`: the free monoidal category on `prot P` generators, with equality the pullback of `≈ᴹ` along its interpretation `⟦_⟧`. That gives `StdUCMorphism Termᴹ 𝔾ᵒ (⟦_⟧*ℰᵒ) ℰᵒ ⟦_⟧ pullbackᵛ`, with `⟦ prot P ⟧ = morphism P`. But identity, `∘` and `⊗` are interpreted as 𝔾ᵒ's, so `prot wireᵖ ≉ id` and `prot (P ⊗ᵖ P′) ≉ prot P ⊗ prot P′`. It is PM generated by protocols, not the call/return setup.

### 4.4 Other setups

- **machine-iso:** none. `≅ᴹ` needs a state bijection with the stateless identity (`Machine/Iso.agda:42-51`).
- **`Examples/RelSetup.agda`:** none (cartesian).
- **Random systems:** `SSP → RS` exists only if RS composes by call/return invocation `C(F)` (maurer2002 §3.3). Built as 𝔾ᵒ with behavioural equality, RS needs the same well-bracketed variant.
- **`docs/uc-setup-causal-boxes.md`:** none (§4 there).
- **`docs/uc-setup-symbolic.md`:** none.
- **IPDL:** none.
- **`docs/uc-setup-nondeterministic.md`:** it includes `SSP` via a `StdUCMorphism`; its side is designed there. It assumed a flat `Iface`, a `Dₚ Bool` readout and a direct morphism into PM; the deviations (§3.1, §3.5, §4.1) were sent to `PlanNondeterminism`.

## 5. Hard parts and risks

### 5.1 Technical

- **Coinduction.**
  - None in SSP: call trees are inductive, and the readout is one finite activation.
  - `∘ᵖ-assoc` follows the termination pattern `Protocol.agda` already passes.
  - `--guardedness` is needed only in §4.2–4.3, for the support attachment.
- **Quotients.**
  - `≈ᵖ` is `EqClosure`.
  - `uKernel`'s `∼` is a relation on unchanged carriers (a setoid), so no HIT is needed.
  - Ancillas sit on both sides, so `⊗-resp-∼` needs no braiding; 𝔾ᵒ exports none, as PlanRandomSystems noted.
- **Levels.** Everything is `suc 0ℓ`. `cs ℓs` match `ℰᵒ`. `∼` is at `o ⊔ cs ⊔ ℓs = suc 0ℓ`, so `PM[wb]ᴹ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)`.
- **Without-K.**
  - `≈ᶜ` uses `≡` only at the leaves; channel checks match `yes refl` on variables.
  - Laws are proved by case analysis on `Ch`.
- **Performance.**
  - The known risk is the record expansion in `open StdUC`: 12 GiB at the transparent `𝒢ₚᴹ` (`Seal.agda:4-20`). Measure first; seal the *whole* bundle only if over budget.
  - Keep `_∘ᵖ_` transparent so that small games pin by `refl` (the `Pin.agda` pattern).
  - §4.3's composites must be proved, not computed (`Pin.agda:9-13`). `Compose.agda` alone takes 11 s warm, and `monitor-invisible` is larger.
- **Migration.** Moving the flat `Iface`/`Protocol` to channels in place touches 95 importers of `Iface`, 21 of `Protocol` and 41 of `Protocol.Machine`. It also breaks the definitional `⊗ᵒ`/`retᴵ` the seal disciplines rely on (§3.1). Hence the parallel namespace.
- **Expressiveness.** No unbounded loops, as in SSProve's free monad.
- **`GradeStable` is not claimed and not needed.**
  - For **closed** `f g : unitᴵ ⇒ T₀ X B`, `≈ℰ ⇒ ≈ᵁ` holds anyway. With `m = ρ⇐ ∘ m′`, naturality, interchange and `λ_I = ρ_I` give `(id ⊗ f) ∘ m ≈ (m′ ⊗ id) ∘ λ⇐ ∘ f`. This is the optional `closed-bridge`, valid in any `StdUC` with `J = unit`.
- **`games-dense`.**
  - `Dₚ` is a coinductive tree of rational coins (`Dp.agda:48-54`). Cutting a `W`-closure's steps at depth `n` gives SSP games `G_n` whose readouts increase to the closure's.
  - Agreement against all `G_n` gives `∼ᵃ`.
  - It is the one non-structural proof besides `monitor-invisible`.

### 5.2 Escape hatch for asynchronous events: recommend pollable state

There are two options:

- **(a) Pollable state.** An asynchronous event becomes protocol state that the environment drives by queries: `send`, the adversary's `deliver`/`drop`, and `read` polled by the receiver. This is CryptHOL's channel ("Bob's query polls the channel", lochbihler2019cc §IV-A, Fig. 2) and constructive cryptography's delivery at interface `E` (maurer2011cc §5.1).
- **(b)** Keep undisciplined machines in PM, outside `W`.

Choose **(a)**:

1. **Under (b), `W` is no sub-setup** (`W-sub`, wideness; §4.2).
2. **Under (b), SSP's identity and interchange laws are false** in `ℰᵒ`, because §4.1's contexts are exactly the undisciplined ones and `≈ᵁ` quantifies over contexts.
3. **Under (a), `PM[wb]` is the intended model**, and the `Abstract2` metatheory runs in `Prot` and `PM[wb]` unchanged, with simulators as protocols.
4. **The tree is already (a) de facto:** off-protocol input goes to `botₚ` (`Protocol/Machine.agda:12-14`, `UC/Seam.agda:54-60`).
5. **Cost of (a).** Spontaneous outputs (timeouts, unprompted leakage) must be polled, and liveness becomes the environment's choice. That is constructive cryptography's separate "availability" condition (maurer2011cc Def. 3).

### 5.3 Quantitative layer

**Scalar ε.**

- SSP's `G₀ ≈^ε G₁` is closeness of the `runᵖ` readouts at ε.
- The setup is `UC.Quantitative.Observed Protᴹ ℚ-ordered qevaluationᵖ …`: one `open import`, as in `UC/Model/Quantitative.agda:22-27`.
- Lemma 6 is its nonexpansive pullback (`splice`, `Observed.agda:81-83`). Lemma 5 is `≈[]-trans` (`advᵇ⊥-triangle`).

**Adversary-dependent ε.**

- SSP's `ε(A)`, and the tree's budgeted `_≈adv[_]_` (`Observe.agda:170-173`), need `UC.Quantitative.Query.Tests` (`Query.agda:84-87`) at a rate grading of `Prot`. The rate is calls per activation, Maurer's `m_C(k)`.
- Moving a reduction into the distinguisher is `absorb-testᵠ` (`Contextual.agda:143-152`). Asymptotics go through `UC.Family.Negligible`.

**New:** only the `GradedSubCat` of rated protocols.

### 5.4 Disagreements with `docs/uc-setup-landscape.md`

**The SSP edge.** §4 (lines 136-146), §5 (line 172) and §6 item 2 (lines 185-186) say "`morphism` is `F` for `SSP → protocol-rewrite`", "objects coincide" and "composition lemmas exist". In fact:

- `F.identity` is false (`Protocol/Machine.agda:14-19`);
- `⊗` is not preserved;
- objects need channels;
- only `∘` is a theorem.

**Replace the edge** by `SSP → PM[wb] ← 𝒲[ℰᵂ]` and `𝒲[ι*ℰᵒ] → PM` (§4.2–4.3).

- An ℰ-only variant of PM cannot receive SSP: functor laws live at `≈ᴹ`, and `ℰᵂ` lives only on 𝒲.
- Any well-bracketed target, RS included, needs the same three swaps.

## 6. Work breakdown

Every step is checked by `pagda` per module. The warning grep must be empty and the escape-hatch baseline must not grow. Paths are under `src/CategoricalCrypto/`.

Status: warm single-module check (one `Checking` line, `+RTS -M3G -H1G`, free gate), measured 2026-10-09; the budget is 60 s + LOC/4 s, and every built module is far inside it.

| # | module | delivers (as built where ✓) | acceptance | status |
|---|---|---|---|---|
| A1 | `SSP/Iface` | `Iface` (`Ch`, `Q`, `R`), `unitᴵ`, `Ωᴵ`, `_⊗ᴵ_`, `_⇒ᴵ_` (`ch`, `qu`, `re`), `idᴵ`, `_∘ᴵ_`, `_⊗ᴵᴵ_`, `ι₁`, `ι₂`, `∇`, `λᴵ`, `ρᴵ`, `αᴵ`, `αᴵ⁻¹`, `swapᴵ`, `oneᴵ`, `flat` | typechecks `--safe --without-K` | ✓ 107 lines, 1.7 s |
| A2 | `SSP/Protocol` | `Calls`, `mapᶜ`, `mapᶜ-cong`, `mapᶜ-id`, `mapᶜ-∘`, `reindex`, `reindex-sim`, `_≈ᶜ_`, `≈ᶜ-refl`/`-sym`/`-trans`, `Protocol` (`St`, `init`, `step`), `graft`/`serve`, `_∘ᵖ_`, `⌜_⌝`, `wireᵖ`, `_⊗ᵖ_`, `_≲ᵖ_` (`θ`, `θ-init`, `θ-step`), `≲ᵖ-refl`, `≲ᵖ-const`, `_≈ᵖ_`, `≲⇒≈ᵖ`, `Prot-setoid` | exports `≈ᶜ-isEquivalence` | ✓ 189 lines, 7.5 s |
| A3 | `SSP/Protocol/Category` | `wireᵖ-identityˡ`, `wireᵖ-identityʳ`, `∘ᵖ-assoc`, `∘ᵖ-resp-≲ᵖ`, `∘ᵖ-resp-≈ᵖ` | exports `Prot : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)` | ✓ 123 lines, 7.5 s |
| A4 | `SSP/Protocol/Monoidal` | `⊗ᵖ-identity`, `⊗ᵖ-homomorphism`, `⊗ᵖ-resp-≲ᵖ`, `⊗ᵖ-resp-≈ᵖ`, `⊗ᵖ-bifunctor`, `⌜⌝-natˡ`, `⌜⌝-natʳ`, `⌜⌝-natα`, `⌜⌝-natσ` | exports `Protᴹ`; optionally `Protˢ` | ✓ both; 299 lines, 9.1 s |
| A5 | `SSP/Observation`; test leaf `SSP/Pin` | `evalC`, `evalC-cong`, `runᵖ`, `runᵖ-sim`, `runᵖ-resp`, `Approximation⊥`, `≈Mℚ⇒≈[0]`, `qevaluationᵖ`, `evaluationᵖ`; pins `echo-flip`, `echo-flip-false`, `echo-nay`, `echo-nay-false`, `echo-stuck-false`, `same-flip`, `same-alt`, `both-flip-nay`, `observe-echo-flip` | a two-protocol composite pins by `refl` | ✓ 89 lines, 8.0 s; `Pin` 86 lines, 7.6 s |
| A6 | `SSP/Setup` | §3.6: the fields of `evaluationᵖ`, `Test`, `_≋_`, `ℰ₀`, `≈ᵖ⇒≋`, `ℰᵖ`, and `StdUC Protᴹ ℰᵖ` (`StdSetup`, `Channel`, `∣machines∣`, the `AbstractUC` names) | `StdSetup : UCSetup (suc 0ℓ)…`; warm time recorded | ✓ 23 lines, 10.2 s |
| A7 | `SSP/Reduction` (optional) | `_≈ᵍ[_]_`, `≈ᵍ-trans` (Lemma 5), `reduction` (Lemma 6), `≈ᵍ-reduce`, `closed-bridge`, `≈ᵍ⇒≈ᵁ` (used by `docs/examples-ssp-otp.md`) | exports `closed-bridge` | ✓ 121 lines, 11 s |
| B1 | `SSP/Obstruction` (optional, `--guardedness`) | `morphism-not-unital`, `morphism-not-monoidal` (first-step invariant as `UC.Machine.Run.step-sim`, new `¬ botₚ ≈ₚ returnₚ x`) | both exported: §4.1 checkable | not started |
| C1 | `SSP/Compile`; flat `Protocol/Sim`, `Protocol/Machine/Resp` | `Protocol/Sim`: flat `_≈ᶜ_`, `_≲ᵖ_` (`θ`, `θ-init`, `θ-step`), `_≈ᵖ_`. `Protocol/Machine/Resp`: `RSt`, `driveʳ`, `stepʳ`, `machineʳ`, `π-sim`, `π′-sim`, `morphism-sim`, `morphism-resp`. `SSP/Compile`: `reply`, `reply-refl`, `reply-≈`, `toCalls`, `toCalls-sim`, `toProtocol`, `toProtocol-sim`, `toProtocol-resp`, `toProtocol-∘` | exports `morphism-resp` | ✓ `Protocol/Sim` 36 lines, 7.5 s; `Resp` 120 lines, 12.6 s; `Compile` 112 lines, 7.9 s |
| C2 | `UC/Bracket`, `UC/Bracket/Category` (+ `Dp/Iter/Supp`, `Machines/Supp`) | built: `UC/Bracket`: `Phase`, `Opp` (`query`, `return`), `Ply` (`call`, `answer`), `Legal`, `W` (`I`, `I-init`, `I-step`), `Bracketed`, `toCalls-bracketed`, `morphism-W`, `id-W`, `wire-W`. `UC/Bracket/Category`: `_⊙_`, `⊙≈∘`, `⊙-W`, `W̃`, `bracketed`, `𝒲`, `ι : Functor 𝒲 𝒫ᴵ`. `Dp/Iter/Supp`: `Turn`, `Supp-stepᵢ`, `SuppL-tagᵢ`, `Supp-iterₚ`. `Machines/Supp`: `Supp-pair`, `Supp-traced`. Not built: closure under `⊗`, `𝒲ᴹ`, `ιᴹ` and its `StdUCMorphism` | exports `morphism-W` and the inclusion | partial: `UC/Bracket` 160 lines, 12.8 s; `UC/Bracket/Category` 130 lines, 12.3 s; `Dp/Iter/Supp` 44 lines, 5.5 s; `Machines/Supp` 46 lines, 11.2 s |
| C3 | `Standard2/UKernel` (generic; uses the RS plan's step 1, `Categories/Category/Monoidal/Construction/Quotient`) | module parameters `𝕄 ℰ`; `_∼_`, `∼-equiv`, `≈⇒∼`, `∘-resp-∼`, `⊗-resp-∼`, `uKernel : MonoidalCongruence 𝕄 (o ⊔ cs ⊔ ℓs)`, `∼⇒≈ℰ`, `∼⇒≈ᵁ` | `--safe --without-K`; exports `uKernel` | ✓ 125 lines, 10.3 s; `Quotient` copied verbatim from `rs-quotient` `e5eddcdb`, 105 lines, 4.1 s |
| C4 | `UC/Bracket/Setup` | `evaluationᵂ`, `ℰᵂ`, `PM[wb]ᴹ = quotient 𝒲ᴹ (uKernel 𝒲ᴹ ℰᵂ)`, `ℰ[wb] = descend …`, `q = StdUCMorphism … quotientF descendᵛ` | `PM[wb].StdSetup` and `q` typecheck | not started |
| C5 | `UC/Bracket/Monitor` | `e`, `e-idem`, `monitor-invisible`, `⊗-monitor` | exports `monitor-invisible` | not started |
| C6 | `SSP/Semantics` | `wire≈σ`, `⊗≈⊗`, `games-dense`, `Fᵂ`, `νᵂ` | exports `SSP→PM[wb] : UCSetupMorphism SSP.StdSetup PM[wb].StdSetup` | not started |

Order: A1–A6 deliver the standalone setup (the primary deliverable); C1–C6 deliver the link. A7 and B1 can be done at any time.

**Deviations of the built steps** (the code blocks of §3 carry the same corrections):

- **A1.** Each structural map exists in one direction; `λᴵ` and `ρᴵ` are inverted by `ι₂` and `ι₁`, `αᴵ` by the added `αᴵ⁻¹`.
- **A3.** `Prot` is built with `Categories.Category.EquivClosureHelper.categoryHelperᵉ`: the laws are simulations (`_≲ᵖ_`) and the helper lifts them to `_≈ᵖ_ = EqClosure _≲ᵖ_`. The congruence is `∘ᵖ-resp-≲ᵖ`, one joint simulation; `∘ᵖ-resp-≈ᵖ` is derived.
- **A4.** The interchange law is `⊗ᵖ-homomorphism`. Since `⌜_⌝` is contravariant, `λ⇒ = ⌜ ι₂ ⌝`, `ρ⇒ = ⌜ ι₁ ⌝`, `α⇒ = ⌜ αᴵ⁻¹ ⌝`. Iso laws, triangle, pentagon and hexagon are `≲ᵖ-const` with one `≈ᶜ-refl` per channel case, so the `⌜⌝-∘`/`⌜⌝-⊗`/`⌜⌝-above`/`⌜⌝-below` lemmas were not needed.
- **A5.** `runᵖ` maps `proj₂` on the tree before `evalC`. `runᵖ-resp` is exact (`≈Mℚ`, by `EqC.gfold` of `runᵖ-sim`), and `≈Mℚ⇒≈[0]` turns it into zero error. The `refl` pins live in the leaf `SSP/Pin`, which nothing imports.
- **A7.** Lemma 6 is `reduction = runᵖ-sim (∘ᵖ-assoc D M G)`, the associativity simulation read out, rather than `pull-∘` plus associativity.
- **C1.** The flat simulation and `morphism-resp` are facts about the flat layer, so they live there (`Protocol/Sim`, `Protocol/Machine/Resp`, beside `Protocol/Machine/Compose`); `SSP/Compile` holds the compilation and needs no `--guardedness`. Channels are compared with `Class.DecEq` (`⦃ DecEq (Ch A) ⦄`), the tree's class, and the reply check `reply (c′ ≟ c)` reduces at a matching channel through `≡-≟-identity` (`reply-refl`), with no K. `toProtocol-∘` is a simulation with `θ = id`. `morphism-resp` is not one induction on `drive` (§3.3): both legs are simulations out of `machineʳ`, whose states pair the two configurations with their `≈ᶜ` proof.
- **C2.** The environment's return is `Opp.return` (`reply` is `SSP.Compile`'s check). `Legal I φ′` names the post-move predicate of `I-step`. The compiled invariant needs no channels in the machine state: `I (idle s) idle = ⊤` and `I (wait k) (calling b a) = ∀ r → Bracketed B b (k (a , r))`, where `Bracketed` is the shape of a compiled step tree (answers only on `b`, well-bracketed at every return on the called channel). `𝒢ₚ`'s identity is definitionally `σᴹ = pureᴹ +-swap`, so `id-W` is stated at `Category.id 𝒫ᴵ`.
  - **Composition.** `W` reads `Supp` off the actual step term, and `Supp` is not `≈ₚ`-invariant (a zero-weight branch is still in the support). So `⊙-W` is proved for `g ⊙ f`, `Machines.Collapse`'s single traced machine `traceᴹ (mk Sᴳ kᴳ)`, which `⊙≈∘` (`collapseᵀ`, `compose-raw≈∘ᴳ`) equates with `𝒫ᴵ`'s composite. The invariant is the planned `Σ b. I_g (calling c b) × I_f (calling b a)`. Inside an activation, every loop letter finds `g` calling on its channel and `f` idle; `Supp-traced` reads a traced step through `Supp-iterₚ`.
  - **The category.** `𝒲`'s homs carry the saturation `W̃ f = Σ f′. W f′ × f ≈ f′`, because `W` itself is not closed under `𝒫ᴵ`'s own composite. `𝒲 = SubCategory bracketed` over `U = flat` (agda-categories' `SubCat`, as `Abstract2.WideSubcategory` does), and `ι = Sub bracketed`. Tests and closures in `W̃` are observationally those in `W`, since `≈ᴹ` preserves the readout (`runᴹ-resp-≈ᴹ`).
  - **Open: the tensor.** `flat (A ⊗ᴵ C)` is not `𝒢ₚ`'s tensor `⟦ flat A ⟧ᴵ ⊗ ⟦ flat C ⟧ᴵ`. So `𝒲ᴹ`'s `⊗` on homs is `𝒢ₚ`'s tensor conjugated by stateless relabelling wires `ρ`, and `ιᴹ`'s `⊗-homo` is `ρ`. Its `W̃`-witness is a direct tensor `f ⊗ʷ g` (state `St f × St g`, dispatch on the channel's side), whose `W` follows from "one open query". Still to prove: `ρ ∘ (f ⊗ g) ∘ ρ⁻¹ ≈ᴹ f ⊗ʷ g`, through `UC.Machine.Wire`'s absorption and a pointwise simulation of `_⊗ᵉ_`'s step. Then come the monoidal laws transported along `ρ`, and `ιᴹ` with `StdUCMorphism 𝒲ᴹ 𝔾ᵒ (ι*ℰᵒ) ℰᵒ ιᴹ (pullbackᵛ ι ℰᵒ)` across the seal (`procᵒ`, `≈ᴹ⇒≈ᵒ`).
- **C3.** `uKernel` is a definition inside the module `Standard2.UKernel 𝕄 ℰ` rather than a function of `𝕄` and `ℰ`.

## 7. Sources

**Used (all already archived):**

- **brzuska2018**: §2.1 (Defs. 1–6, Lemmas 1–4), §2.3 (Defs. 7–8, Lemmas 5–6), §3 (Def. 9).
- **ssprove2023**: §2.1 (Def. 2.1, Lemmas 2.2–2.3), §3.2–3.4.
- **lochbihler2019cc**: §IV-A (Fig. 2, Defs. 1–2), §IV-B (Def. 3, identity and embedding converters), §IV-C, §V (Def. 4).
- **maurer2002**: §3.3 (invocation `C(F)`, Lemma 4).
- **maurer2011cc**: §5.1, Def. 3.

**Not retrievable**, recorded in `docs/kb/sources/litreview/BLOCKED-URLS.md` (Cloudflare challenge, three attempts each); the plan uses their abstracts only:

- Dupressoir–Kohbrok–Oechsner, CSF 2022 (ePrint 2021/326).
- Larsen–Schürmann, CSF 2025 (ePrint 2025/598).

**Newly archived:** none.
