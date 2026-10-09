# Nondeterministic choice as a UC setup

Plan, 2026-10-09. Nothing here is typechecked; every claim about a module that does not exist yet is a design claim, and
`[INFERENCE]` marks what was reasoned but not checked. Line references are to the `uc-setup-landscape` worktree. The setup extends
[uc-setup-ssp.md](uc-setup-ssp.md) and keeps its names (`Iface`, `Calls`, `Protocol`, `wireᵖ`, `_∘ᵖ_`, `_⊗ᵖ_`, `unitᴵ`, `Ωᴵ`, `Prot`, `Protᴹ`,
`evalC`, `Approximation⊥`); new names are marked `⁺`/`ˢ` or are specific to this plan. Namespace `CategoricalCrypto.ND`, every module `--safe --without-K`, no `--guardedness`.

## 1. Summary

**The deliverable** is `ND = Standard2.StdUC Prot⁺ᴹ ℰ⁺`:

- **Machines.** SSP's `Protocol A B` plus one `Calls` constructor, `choose : (n : ℕ) → (Fin (suc n) → Calls A X) → Calls A X`; `graft`, `serve`,
  `reindex`, `mapᶜ` get one clause each, shaped like `coin`'s. Probability stays `Dist⊥`; there is no combined monad.
- **Observation.** A scheduler resolves `choose` only when a *closed* system is read: `run⁺ : Sched → Calls unitᴵ X → Dist⊥ X`. Outcomes are
  `Sched → Dist⊥ Bool` under image equality; the ε-version is Hausdorff closeness of the images, collapsed by `qual₊` as in SSP. `J = unitᴵ`;
  levels as SSP (`Evaluation Prot⁺ 0ℓ 0ℓ`, `ℰ⁺` at `suc 0ℓ`).
- **Equality.** `_≈ᶜ_` is SSP's tree equality plus five law constructors (§3.2), so the `choose` laws are hom-equalities: `≈ᵁ` by `≈C⇒≈ᵁ`, no `GradeStable`.
- **Grade.** Arbitrary, `T₀ X B = X ⊗ᴵ B`. `Schedᴵ H` is the pollable oracle through which the adversary resolves a choice (§3.7): `choose` for choices
  the spec proves immaterial, `Schedᴵ` for those the informal model leaves to the adversary.

**Changes to the brief** (evidence in the section named):

1. `Sched` is a history-dependent function: stream and coin-blind schedulers make `choose-comm` false under a coin (§3.3).
2. `Fin n` becomes `Fin (suc n)`: for `n = 0` no scheduler exists and `≋ˢ` is the total relation (§3.1).
3. The laws are `≈ᶜ` constructors proved sound once against `run⁺` (§3.4), not `≈ℰ` facts needing `bridge` (§3.6).
4. **`SSP → ND` with `ν` = constant-in-σ tests is not a presheaf morphism**: a demonic closure sees the test's coins and separates two SSP-equal tests
   (CE1, §4.1). What holds is a one-way reflection, ND-secure ⇒ SSP-secure. The cause is the global perfect-information scheduler (task-PIOA's leak,
   §2.2); repairs and costs are in §5.1, to be chosen before N1.
5. The brief's (2a) "⇔" fails; pointwise transfer along a *threaded* routing holds (§4.2). (2b) has no instance (`GradedKleisli` has no monoidal structure, the locally
   graded variant needs a braided ℐ, and the routing is lax). **Recommended: (2a).**
6. "No probability×nondeterminism monad" holds for distributive laws only; the convex powerset monad exists (§2.3–2.4).
7. `P ∥ Q` is not derivable from `choose` and `⊗ᵖ`; the self-scheduled shuffle is a tree operation (§4.4).
8. ND reaches protocol-model only through SSP's chain (§4.3).

## 2. Source notions

### 2.1 Segala's probabilistic automata and schedulers (segala1995)

- A probabilistic automaton has transitions `s —a→ μ` with `μ` a distribution; nondeterminism is which transition leaves `s`. A **scheduler**
  (adversary) is `A : frag*(M) → Probs(ctrans(M))`, from finite execution fragments to a *combined* transition leaving the last state (§5.2): it sees
  the whole fragment (perfect information). Deterministic ones return a transition; general ones randomize, which "in general" adds power (ch. 5
  intro); randomized schedulers are kept so that a run of `M₁‖M₂` projects to a run of each component (§4.3, Prop. 4.3.4).
- Restrictions are *adversary schemas*: off-line (oblivious) schedulers fix the process order in advance (Ex. 5.6.1); partial on-line information is an equivalence on
  fragments plus correlation functions (§5.6). Trace-distribution inclusion is not a precongruence (Ex. 7.4.1): the coarsest precongruence below it is decided by one
  *principal context* correlating the scheduler with probabilistic choices (Thm 7.5.1). Our `≈ℰ` quantifies over all contexts, so it already is that contextual notion;
  the correlation is CE1.

### 2.2 Task-PIOA, and why unrestricted schedulers leak (canetti2006taskpioa)

- Perfect-information schedulers "are too powerful in the setting of security analysis, leading to unrealistic adversarial behaviors" (abstract).
  §1 separates an *adaptive adversarial scheduler*, an automaton acting as message delivery system with access to dynamic information (it orders
  deliveries), from a *task schedule*, a sequence of tasks "fixed nondeterministically in advance" (oblivious; at most one enabled action per task
  and state) for inessential choices: in their OT proof it is inconsequential whether Transmitter or Receiver samples first. Implementation is
  inclusion of external-behaviour sets (§5, Def. 6), not equality; §5 adds *local schedulers* using only a component's own past.
- **The leak** (CE1, §4.1): a demon in one component that sees another component's toss is a covert channel between them. Obliviousness is the
  paper's cure and needs *named* tasks; an anonymous `choose` under an oblivious scheduler correlates exclusive branches (CE0, §3.3).

### 2.3 The no-go for one monad (varacca2006, zwart2019nogo)

Plotkin's counterexample (varacca2006 §1; zwart2019nogo §3.1): there is no distributive law of type `D∘P ⇒ P∘D`, `D` the finite distribution monad and `P` the finite powerset
monad; Dahlqvist–Neves: "the composite functor carries no monad structure at all" (zwart2019nogo §1); Zwart–Marsden generalise to theories with a binary commutative idempotent
term (Thms 3.5, 3.12). So there is no composite monad `P∘D`: `Dist⊥` stays the only semantic monad and `choose` is syntax resolved at observation. The landscape's wording
(§5) is right for strict distributive laws and the composite functor, not for "no such monad exists" (§2.4).

### 2.4 The convex powerset alternative, and why it is rejected here

- `C X` = non-empty finitely generated convex subsets of `D X`, unit `x ↦ {δₓ}`, presented by convex semilattices (a semilattice `⊕`, convex combinations `+ₚ`, and
  `(x ⊕ y) +ₚ z = (x +ₚ z) ⊕ (y +ₚ z)`); `C(−+1)` adds termination (bonchi2022 §4.1–4.2, §5). It arises from the distributive combination of the *theories* (varacca2006 §1:
  Tix, Mislove) and as the weak lifting of a *weak* distributive law (goy2020: abstract only, blocked). It is adequate for *randomized* schedulers; deterministic ones match
  indexed valuations, which lose some probability laws (varacca2006 §1). It would make the `choose` laws semilattice axioms and `read` a function of the closed protocol.
- Rejected here: (1) it does not repair CE1 (the hull of `{0, ½, 1}` is `[0,1]`, the other side stays `{½}`); (2) it needs convex hulls of finitely supported rational
  subdistributions with decidable equality, or the unique-basis normal form (bonchi2022's [BSV21]), and the tree has neither (`Possibility.agda` is lists); (3) it is coarser
  (`x ⊕ y` = `x ⊕ y ⊕ (x +_½ y)`), while image equality has a Hausdorff ε-version with no geometry; (4) the monad is not needed, since composition lives in `Calls`. It would
  remove one artefact of non-convex images, a *dead coin*: `coin μ λ _ → p` and `p` have different images once a demon sees the coin (`{0,½,1}` against `{0,1}` for a verdict
  read off a later `choose 1`).

### 2.5 "Send X to A, B, C" is adversary-scheduled delivery (canetti2015suc, backes2007rsim)

- SUC (canetti2015suc §1.3, §2.2): parties and functionality sit in a star around a *router*. An activated machine may write *any number* of messages;
  the router stores each and shows the adversary only sender, receiver and *public header* ("the private content is simply not sent"); a message is
  delivered once, to one party, when the adversary instructs it, and the adversary "can only influence when". So "send X to A, B, C" is three stored
  messages delivered in the adversary's order. Full UC (ePrint 2000/067) is not archived and not cited.
- RSIM (backes2007rsim abstract, §1.3): "scheduling by the adversary with realistic information" and "procedure-call-style scheduling for colocated
  components", the latter being the SSP call/return discipline.
- Mapping: `Schedᴵ H` = router with header view (adversary-resolved, simulator-resolvable); `choose` = the task schedule for inessential choices; the
  global `Sched` = Segala's perfect information, the part to restrict.

## 3. The `StdUC` instantiation

### 3.1 Calls, protocols, composition

`Iface`, `⇒ᴵ`, `unitᴵ`, `Ωᴵ`, `⊗ᴵ` are SSP's (SSP §3.1). The call-tree layer is a copy with one more constructor, so SSP's `evalC` stays total (a
signature-parametric `Calls` would share code but is cheap only before SSP's A2 exists).

```agda
-- CategoricalCrypto/ND/Protocol.agda
data Calls (A : Iface) (X : Set) : Set where
  ret : X → Calls A X ;  dead : Calls A X
  call   : (c : Ch A) → Q A c → (R A c → Calls A X) → Calls A X
  coin   : Dist-ℚ Bool → (Bool → Calls A X) → Calls A X
  choose : (n : ℕ) → (Fin (suc n) → Calls A X) → Calls A X        -- demonic: only `run⁺` resolves it
-- Protocol, wireᵖ, ⌜_⌝, reindex, _⊗ᵖ_: SSP §3.2 verbatim; graft, serve, mapᶜ, reindex gain
--   graft P₂ P₁ (choose n k) s₁ = choose n λ i → graft P₂ P₁ (k i) s₁      serve P₂ P₁ k (choose n k₁) = choose n λ i → serve P₂ P₁ k (k₁ i)
```

- `Fin (suc n)`: with `Fin n` and `n = 0` no scheduler exists, `Sched` is empty, `∀σ` is vacuous and `_≋ˢ_` holds between any two outcomes. `dead` is the abort.
- Position decides information: `serve` puts the caller's continuation under the callee's `choose`, `graft` puts a callee under the caller's coins, so a
  choice sees exactly the tosses above it in the composite tree.
- `choose` is a *tree* operation (inside one activation). A choice between protocols with different states has no per-activation reading; a
  once-and-for-all choice of implementation is an `init`-level family (option K, §5.1).

### 3.2 Hom-equality and the laws

`_≲ᵖ_`, `_≈ᵖ_ = EqClosure _≲ᵖ_` and `Prot-setoid` are SSP §3.3 over the new `Calls` and the new `_≈ᶜ_`:

```agda
data _≈ᶜ_ {A X} : Calls A X → Calls A X → Set where
  ret : x ≡ x′ → ret x ≈ᶜ ret x′ ;  dead : dead ≈ᶜ dead
  call : (∀ r → k r ≈ᶜ k′ r) → call c q k ≈ᶜ call c q k′
  coin : (∀ b → k b ≈ᶜ k′ b) → coin μ k ≈ᶜ coin μ k′
  sym  : p ≈ᶜ q → q ≈ᶜ p ;  trans : p ≈ᶜ q → q ≈ᶜ r → p ≈ᶜ r
  -- a demonic choice is decided by the SET of its alternatives (a semilattice presentation)
  choose-set  : (∀ i → Σ[ j ∈ Fin (suc m) ] k i ≈ᶜ k′ j) → (∀ j → Σ[ i ∈ Fin (suc n) ] k i ≈ᶜ k′ j) → choose n k ≈ᶜ choose m k′
  choose-unit : choose 0 (λ _ → p) ≈ᶜ p
  choose-join : (e : Fin (suc N) → Σ[ i ∈ Fin (suc n) ] Fin (suc (m i))) → (∀ x → Σ[ j ] e j ≡ x)
              → choose n (λ i → choose (m i) (k i)) ≈ᶜ choose N (λ j → k (proj₁ (e j)) (proj₂ (e j)))
  -- the two coin laws that stay sound against a demon that sees every toss
  coin-comm   : coin μ (λ x → coin ν (λ y → k x y)) ≈ᶜ coin ν (λ y → coin μ (λ x → k x y))
  coin-dead   : coin μ (λ _ → dead) ≈ᶜ dead
```

- `refl`, `choose-cong`, idempotence, commutativity and associativity are derived (§3.6). `ret` carries `≡` only at leaves, as in SSP.
- **Not laws**, because a demon sees what is above it: `coin-unit` (`coin μ λ _ → p ≈ p`); commuting `choose` past a `coin` or a `call` (a demon choosing
  *before* the toss is weaker). The sound mixed form is a *plan* law (a choice over functions `Bool → Fin`); add it only if a proof needs it.

### 3.3 Schedulers and `run⁺`

```agda
-- CategoricalCrypto/ND/Sched.agda
data Event : Set where toss : Bool → Event ; pick : ℕ → Event
Sched : Set                                       -- deterministic, history-dependent: the decision at the node reached by `h`
Sched = List Event → (n : ℕ) → Fin (suc n)
_/_ : Sched → Event → Sched ;  (σ / e) h = σ (e ∷ h)                              -- the residual after `e`

run⁺ : Sched → Calls unitᴵ X → Dist⊥ X           -- structural in the tree; σ is generalised in the recursion
run⁺ σ (ret x)      = return⊥ x
run⁺ σ (call () _ _)                              -- Ch unitᴵ = ⊥
run⁺ σ (coin μ k)   = μ >>=ᴹ λ b → run⁺ (σ / toss b) (k b)
run⁺ σ (choose n k) = let i = σ [] n in run⁺ (σ / pick (toℕ i)) (k i)
run⁺ σ dead         = return-ℚ nothing           -- as `evalC`, `Protocol/Observe.agda:41-45`
runᴺ : Protocol unitᴵ Ωᴵ → Sched → Dist⊥ Bool
runᴺ W σ = Dmap⊥ proj₂ (run⁺ σ (step W (init W) tt tt))                           -- one activation, as `runᵖ`
```

- Candidates: a stream `ℕ → ℕ`, or a history of picks only, also make `run⁺` total and `≋ˢ` an equivalence (it is one for *any* `Sched`, §3.4) but break
  the laws (CE0); a coinductive `{ pick : (n : ℕ) → Fin (suc n) × Sched ; toss : Bool → Sched }` is equivalent to the function above on reachable histories and costs
  `--guardedness`. A closed one-activation tree has finitely many events per path, so finite histories suffice.
- **CE0.** `T₁ = coin ½ λ b → if b then choose 1 [x; y] else choose 1 [u; u′]`, `T₂` = `T₁` with `[y; x]`. A scheduler that does not see the toss picks
  once for both branches: `Im T₁ = {½x+½u, ½y+½u′}`, `Im T₂ = {½y+½u, ½x+½u′}`, separated by the verdict `[v ∈ {x,u}]`. A history-dependent one picks per
  branch and both images are all four mixtures. So `choose-comm` under a coin *needs* tosses in the history; this is `coin`-congruence at work: combining
  per-branch witnesses is `σ′ (toss b ∷ h) := σ′_b h`. It is Segala's perfect information; its price is §4.1.

### 3.4 The outcome space, the readout, soundness

```agda
-- CategoricalCrypto/ND/Observation.agda
Outcome = Sched → Dist⊥ Bool
_≋ˢ_ : Rel Outcome 0ℓ
e ≋ˢ e′ = (∀ σ → Σ[ σ′ ] e σ ≈Mℚ e′ σ′) × (∀ σ′ → Σ[ σ ] e σ ≈Mℚ e′ σ′)           -- image equality

≋ˢ-isEquivalence : IsEquivalence _≋ˢ_              -- for ANY Sched; Mℚ = `RationalDist/Setoid.agda:18-21`
≋ˢ-isEquivalence = record
  { refl  = (λ σ → σ , Mℚ.refl) , (λ σ → σ , Mℚ.refl)
  ; sym   = λ (f , b) → (λ σ′ → let σ , p = b σ′ in σ , Mℚ.sym p) , (λ σ → let σ′ , p = f σ in σ′ , Mℚ.sym p)
  ; trans = λ (f₁ , b₁) (f₂ , b₂) → (λ σ → let σ′ , p = f₁ σ ; σ″ , q = f₂ σ′ in σ″ , Mℚ.trans p q)
                                   , (λ σ″ → let σ′ , q = b₂ σ″ ; σ , p = b₁ σ′ in σ , Mℚ.trans p q) }

ApproximationH : Approximation Outcome ℚ-ordered 0ℓ                               -- Hausdorff closeness of the images
ApproximationH ._≈[_]_ e ε e′ = (∀ σ → Σ[ σ′ ] e σ ≈⊥[ ε ] e′ σ′) × (∀ σ′ → Σ[ σ ] e σ ≈⊥[ ε ] e′ σ′)   -- ≈⊥ = SSP's `Approximation⊥`
-- ≈[]-refl, ≈[]-sym as above; ≈[]-trans chains the witnesses with `advᵇ⊥-triangle`; ≈[]-mono pointwise

qevaluation⁺ : QEvaluation Prot⁺ 0ℓ 0ℓ
qevaluation⁺ = record { J = unitᴵ ; Ω = Ωᴵ ; X = record { Carrier = Outcome ; approx = ApproximationH }
                      ; eval₀ = record { to = runᴺ ; cong = runᴺ-resp } }          -- W ≈ᵖ W′ → runᴺ W ≈[ 0ℚ ] runᴺ W′
evaluation⁺ : Evaluation Prot⁺ 0ℓ 0ℓ
evaluation⁺ = qual₊ ℚ-refinement qevaluation⁺                                      -- the `UC/Model/Observation.agda:69-76` pattern
```

- Image equality is symmetric because `Evaluation.S` is a `Setoid` (`UC/Core.agda:103-111`); a refinement (`⊆`) order would need a preorder-valued
  `Evaluation`, a framework change (§3.7).
- **Equivalent finite form.** `⟦_⟧ : Calls unitᴵ X → List (Dist⊥ X)` with `⟦ret x⟧ = [return⊥ x]`, `⟦dead⟧ = [return-ℚ nothing]`, `⟦choose n k⟧ = ⋃ᵢ ⟦k i⟧` and
  `⟦coin μ k⟧ = [ μ >>=ᴹ (λ b → if b then d₁ else d₀) | d₁ ∈ ⟦k true⟧ , d₀ ∈ ⟦k false⟧ ]` (all independent resolutions) satisfies `d ∈ ⟦t⟧ ⇔ ∃σ. d ≈Mℚ run⁺ σ t` (one induction;
  its `coin` case is the witness combination of §3.3). Then `≋ˢ` is set equality of lists, every image is finite, `qual₊` agrees with `qual` (related by `Abstract2/Morphism.agda:Refine`),
  and each law is a fact about `∪` and Fubini; `Sched` is needed only for `Th` (§4.2). This selection is non-idempotent on non-convex sets (`S +_½ S ⊋ S`): the dead-coin non-law, and the
  concrete face of the idempotent-term obstruction of zwart2019nogo §3 [INFERENCE].
- **`runᴺ-resp` is the one new semantic proof.** `EqClosure`-induction reduces to one `θ`-step; then `run⁺ σ (mapᶜ f t) ≈ Dmap⊥ f (run⁺ σ t)` and
  `run⁺-resp : p ≈ᶜ q → p ≃ q` for `p q : Calls unitᴵ X`, `p ≃ q := (∀σ ∃σ′ …) × (∀σ′ ∃σ …)`, by induction on the derivation (`call` is absurd at `unitᴵ`):

| constructor | σ′ from σ (residuals `σ / e`) |
|---|---|
| `coin` | `σ′ (toss b ∷ h) := σ′_b h`, with `σ′_b` from the hypothesis at `σ / toss b` (`Bool`: case split) |
| `choose-set` | `i = σ [] n`, `(j , d) = fwd i`; `σ′ [] m := j`, `σ′ (pick j ∷ h) := (hyp. d at σ / pick i) h`; backwards symmetric |
| `choose-unit` | `σ′ := σ / pick 0`; backwards `σ [] _ := 0`, `σ (pick 0 ∷ h) := σ′ h` |
| `choose-join` | `i = σ [] n`, `j′ = (σ / pick i) [] (m i)`, `e j = (i , j′)`; `σ′ [] N := j`, `σ′ (pick j ∷ h) := σ (pick i ∷ pick j′ ∷ h)` |
| `coin-comm` | `σ′ (toss y ∷ toss x ∷ h) := σ (toss x ∷ toss y ∷ h)`, then `>>=ᴹ-comm` (`RationalDist.agda:331`) |
| `coin-dead`, `sym`, `trans` | any σ (mass-1 constant bind); swap; compose the witnesses |

### 3.5 The monoidal category and the setup

```agda
-- ND/Protocol/{Category,Monoidal}.agda: SSP §3.4 line by line; each structural induction gains a `choose` clause shaped like its `coin` clause
Prot⁺  : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
Prot⁺  = categoryHelper record { Obj = Iface ; _⇒_ = Protocol ; _≈_ = _≈ᵖ_ ; id = wireᵖ ; _∘_ = _∘ᵖ_ ; … }
Prot⁺ᴹ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
Prot⁺ᴹ = record { U = Prot⁺ ; monoidal = monoidalHelper Prot⁺ record
  { ⊗ = record { F₀ = uncurry _⊗ᴵ_ ; F₁ = uncurry _⊗ᵖ_ ; … } ; unit = unitᴵ ; unitorˡ = ⌜ λᴵ ⌝≅ ; … } }
-- ND/Setup.agda
open Evaluation evaluation⁺ public
open Observable observable public using (Test; _≋_; ℰ₀) renaming (≈⇒≋ to ≈ᵖ⇒≋; ℰᴼ to ℰ⁺)
open Std2.StdUC Prot⁺ᴹ ℰ⁺ public                  -- StdSetup : UCSetup (suc 0ℓ) … (suc 0ℓ)
```

### 3.6 Theorems about `choose`

**(a) Laws.** All derived inside `_≈ᶜ_`, hence hom-equalities of `Prot⁺`:

```agda
choose-idem  : choose n (λ _ → p) ≈ᶜ p                                           -- choose-set (fwd = const 0), then choose-unit
choose-comm  : choose 1 (λ { 0 → p ; 1 → q }) ≈ᶜ choose 1 (λ { 0 → q ; 1 → p })   -- choose-set, i ↦ swap i (the brief's σ ↦ σ ∘ swap)
choose-assoc : choose 1 (λ { 0 → choose 1 [ p ; q ] ; 1 → r }) ≈ᶜ choose 2 [ p ; q ; r ]    -- choose-join
choose-perm  : (π : Fin (suc n) ≃ Fin (suc n)) → choose n (k ∘ π) ≈ᶜ choose n k
collapse     : (∀ i → k i ≈ᶜ k 0) → choose n k ≈ᶜ k 0                           -- choose-set, then choose-unit
```

For protocols the step-level versions give `f ≈ᵖ g` by `θ = id`, hence `f ≈ᵁ g` (`≈C⇒≈ᵁ`, `Abstract2.agda:63`). The brief's route, `≈ℰ` by `σ ↦ σ ∘ swap` and
then `bridge` (`Abstract2.agda:124`), is not used: it needs `GradeStable`, and its context lemma is the `≈ᶜ` induction of §3.4 anyway.

**`GradeStable ℰ⁺`** (`UCSetup.agda:146-147`) is not claimed, as for SSP (SSP §5.1). It needs an ancilla-absorption lemma: from `h ≈ℰ h′` and a pair
`(t : Y ⊗ C ⇒ Ω, m : unit ⇒ Y ⊗ B)` an ancilla-free pair with the same readout. `GradeStableFromTests` (`:155-175`) has its retraction (`θ = α⇒`) but needs a
conjugation-closed generating relation with `ℰ⇒≋`, which is `GradeStable` again. For `ℰᵒ` it is false (landscape §4); for call/return nesting no counterexample was found,
though `t` and `m` share their `Y`-traffic [INFERENCE]. The laws avoid it; for *closed* `f g : unitᴵ ⇒ T₀ X B`, `closed-bridge` (SSP §5.1, A7) carries over verbatim
(`J = unitᴵ`); an open bare `≈ℰ` artifact needs an ancilla-quantified proof.

**(b) Congruence.** By induction on the derivation (old cases are SSP's):

```agda
graft-resp : p ≈ᶜ p′ → graft P₂ P₁ p s ≈ᶜ graft P₂ P₁ p′ s     serve-resp : (∀ r → k r ≈ᶜ k′ r) → t ≈ᶜ t′ → serve P₂ P₁ k t ≈ᶜ serve P₂ P₁ k′ t′
reindex-resp, mapᶜ-resp : likewise     ∘ᵖ-resp-≲ᵖ, ⊗ᵖ-resp-≲ᵖ : θ = θ₂ × θ₁ ;  ∘ᵖ-resp-≈ᵖ, ⊗ᵖ-resp-≈ᵖ by EqC.gmap
```

Every law case is the *same constructor at the grafted family*: the clauses of §3.1 only post-compose the children of a `choose`, e.g.
`graft (choose n λ i → choose (m i) (k i)) s ≡ choose n λ i → choose (m i) λ j → graft (k i j) s`, then `choose-join` with the same `e`.

**(c) Order-independence transports along `≤UC`.**

```agda
module OrderSpec (St : Set) (s₀ : St) (stepᵒ : Fin (suc n) → St → (c : Ch B) → Q B c → Calls A (St × R B c)) where
  Spec    = record { St = St ; init = s₀ ; step = λ s c q → choose n λ i → stepᵒ i s c q }
  Order i = record { St = St ; init = s₀ ; step = stepᵒ i }
  collapse⁺ : (∀ i s c q → stepᵒ i s c q ≈ᶜ stepᵒ 0 s c q) → Spec ≈ᵖ Order 0       -- θ = id; `collapse` pointwise
  transport : Spec ≈ᵖ Order 0 → (f ≤UC Spec ⇔ f ≤UC Order 0) × (Spec ≤UC g ⇔ Order 0 ≤UC g)
  transport e = …  ≤UC-trans, ≈ᵁ⇒≤UC (≈C⇒≈ᵁ e), ≈ᵁ-sym …                           -- Abstract2.agda:142-147, 163-164
```

- The hypothesis is about *trees*, and for an open import it is false: calls on different channels do not commute for an order-sensitive closure. It is a
  statement about the **composite with the actual callee** `F : Protocol A′ A`: `graft F (stepᵒ i s c q) sF ≈ᶜ graft F (stepᵒ 0 s c q) sF` on reachable
  states (restrict `St` to a Σ-subtype, SSP §4.3's reachable-configuration technique), giving `Spec ∘ᵖ F ≈ᵖ Order 0 ∘ᵖ F`.
- Proof of it: an adjacent swap of two calls becomes, after `serve`, a swap of two callee subtrees: `ret` leaves equal by `≡` when `F`'s steps commute as
  functions on states, independent coins by `coin-comm`, `dead` by `coin-dead`. **Not available:** a callee with a `coin` in one block and a `choose` in the
  other (§3.2). Sugar: `sendAll ts = choose (n! ∸ 1) λ π → seqᶜ (permute π ts)`.

### 3.7 The grade, `Schedᴵ`, and who resolves

The grade is any `Iface`; `ext`, `sub`, `μ`, `return` are SSP's wires. `Schedᴵ` is an ordinary `Iface`:

```agda
Schedᴵ : (H : Set) → Iface                         -- the router of canetti2015suc §2.2, header view only
Schedᴵ H = record { Ch = Bool ; Q = λ { false → ⊤ ; true → ℕ } ; R = λ { false → List H ; true → ⊤ } }
-- false: poll the public headers of the pending items;  true i: deliver pending item i (no-op if absent)
-- f : A ⇒ T₀ (Schedᴵ H ⊗ᴵ X) B     the functionality keeps a pending bag in `St`; "send X to A, B, C" appends three items;
-- `deliver` moves one to its recipient's mailbox and recipients poll (SSP §5.2: call/return cannot suspend a step)
```

Real and ideal worlds both export `Schedᴵ H`; the simulator answers the real adversary's `deliver` by issuing the ideal `deliver`s, so the choice is
*simulator-resolvable*.

| informal step | model | resolved by | consequence for `f ≤UC g` |
|---|---|---|---|
| "in any order", order immaterial | `choose` + `collapse⁺` | nobody (a `≈ᵖ`) | none; transports along `≤UC` |
| delivery order, timing, corruption order | `Schedᴵ`, both worlds | adversary, then simulator | the simulator may shrink: refinement-like |
| a genuine worst-case internal choice | `choose`, not collapsible | the global demon | real must exhibit the same behaviours |

**Image equality is symmetric: the simulator cannot shrink.** The second half of `≋ˢ` says every ideal resolution must be matched by a real one, and `s`
sees only `g`'s grade, never its internal `choose` nodes. If `f` is determinate and `sub s ∘ g` has a non-singleton image in some context, that `s` does not
witness `f ≤UC g`: a simulator can make `g`'s choices immaterial by how it interacts, never resolve them. Realising a spec therefore means proving its choices
immaterial or exposing them on `Schedᴵ`. A refinement order (`⊆`, task-PIOA's implementation) needs a preorder-valued `Evaluation`.

## 4. Morphisms

### 4.1 `SSP → ND`: the inclusion and CE1

```agda
-- CategoricalCrypto/ND/Include.agda
ι̂ : SSP.Calls A X → Calls A X                       -- ret/call/coin/dead ↦ the same constructor
ιᵖ P = record P { step = λ s c q → ι̂ (step P s c q) }
ι̂-graft : ι̂ (graft P₂ P₁ t s) ≡ graft (ιᵖ P₂) (ιᵖ P₁) (ι̂ t) s       -- with ι̂-serve, ι̂-reindex, ι̂-mapᶜ: three mutual structural lemmas
ι : StrongMonoidalFunctor Protᴹ Prot⁺ᴹ             -- F₀ = id, F₁ = ιᵖ, κ = Oplax.δ ι (a wire)
ν : PresheafMorphism ι.F ℰᵖ ℰ⁺                     -- the brief: η A t = ιᵖ t ("constant in σ": `run⁺ σ (ι̂ t) ≈ evalC t` for choose-free t); `cong` ✗, below
ι⁺ = StdUCMorphism Protᴹ Prot⁺ᴹ ℰᵖ ℰ⁺ ι ν           -- κ-return/ext/sub come with it (`Standard2/Morphism.agda:39-55`)
```

| obligation | status | proof |
|---|---|---|
| `F.identity`, `F.homomorphism`, `F-resp-≈` | ✓ | the `wireᵖ` clause is the same; `ι̂-graft` with `θ = id`; `ι̂` maps `≈ᶜ` to `≈ᶜ` |
| `ε`, `⊗-homo`, unitors, `α` | ✓ | stateless wires, `ι̂` of a call tree |
| `ν.commute` | ✓ | `ι` functorial, `pull-∘` |
| **`ν.cong`** | **✗ CE1** | an SSP-equal pair is separated by a demonic closure |

**CE1** (`t ≋ᵖ u` but `ιt ≋̸⁺ ιu`; worked by hand, N7 formalises it):

```agda
Bit : Iface ; Bit = record { Ch = ⊤ ; Q = λ _ → ⊤ ; R = λ _ → Bool }                  -- one oracle returning a bit
t u : SSP.Protocol Bit Ωᴵ
t .step s _ _ = coin ½ λ c → call tt tt λ r → ret (s , c xor r)                      -- verdict c ⊕ r
u .step s _ _ = coin ½ λ c → call tt tt λ _ → ret (s , c)                            -- same calls, verdict c
m⁺ : Protocol unitᴵ Bit ;  m⁺ .step s _ _ = choose 1 λ i → ret (s , toBool i)         -- a demonic bit
-- t ≋ᵖ u: against every SSP closure the reply r is independent of c, so both read the same.
-- t ∘ m⁺ = coin ½ λ c → choose 1 λ i → ret (c ⊕ i). A demon answering i = c gives verdict false at both tosses, so
-- Im (t ∘ m⁺) ∋ Pr[true] = 0 (and ½, 1), while Im (u ∘ m⁺) = {½}.
```

Cause: the demon in `m⁺` sees the toss of `t`, a covert channel between two components (§2.2); convexification does not remove it. With a global demon ND-`≈ℰ` on included
protocols is strictly finer than SSP-`≈ℰ`: perfect (`≈ᵖ`) equalities and simulations transfer, observational reductions do not. What exists instead:

- `ι` itself, a strict strong monoidal functor, and the trivial pullback morphism `StdUCMorphism Protᴹ Prot⁺ᴹ (ℰ⁺ ∘F op ι.F) ℰ⁺ ι (pullbackᵛ ι.F ℰ⁺)` (Epi and Mono,
  `Presheaf/Morphism.agda:165-169`), whose source is SSP with ND's tests.
- No functor `ND → SSP` is evident: `choose` has no image, and `det (choose n k) = k 0` ignores `choose-comm`.
- **Reflection (R)**: for choose-free `f g`, `ιf ≤UC ιg` (ND) ⇒ `f ≤UC g` (SSP). Take an SSP adversary `a`; ND gives `s` with `sub ιa ∘ ιf ≈ᵁ sub s ∘ ιg`. In a choose-free
  context the left side reads one distribution `d` at every σ, so the second half of `≋ˢ` gives `read (C[sub s ∘ ιg]) σ′ ≈ d` for all σ′. With `s₀ = det s` (every
  `choose n k ↦ k 0`) and σ₀ = "always `0`", `run⁺ σ₀ (graft … s …) ≈ evalC (graft … s₀ …)` (induction; `det` commutes with `graft`/`serve`), so `sub s₀ ∘ g` is an SSP
  simulator. No `GradeStable`, no `Full`. The landscape edge `SSP ──▶ ND` becomes the dashed reflection `ND ⇢ SSP`.

### 4.2 Routing the choices: (2a) and (2b)

**The brief's routing** `rtˡ P : Protocol A (Instᴵ ⊗ᴵ B)`, with `Instᴵ = record { Ch = ⊤ ; Q = λ _ → Sched ; R = λ _ → ⊤ }`: state `St P × Sched × List Event`, `install σ` on the
grade, each `choose` answered by the installed σ at the component's *local* history. It types as `A ⇒ T₀ Instᴵ B` but is lax rather than a functor [INFERENCE]: in `rtˡ (g ∘ᵖ f)`
one σ sees the merged tree, in `rtˡ g ∘ᵖ rtˡ f` `g`'s demon never sees `f`'s tosses, and the `Slide` equality `sub ∇ ∘ (rtˡ g ⊙ rtˡ f) ≈ rtˡ (g ∘ f)` (`GradedKleisli.agda:58-63`)
would need a state map recovering the merged history, an interleaving of events, from the two local ones.

**Threaded routing** is the functorial reading: the global scheduler is a token passed through every call and reply (call/return is single-threaded, so this is exact).

```agda
-- CategoricalCrypto/ND/Route.agda
Th : Iface → Iface
Th A = record { Ch = Ch A ; Q = λ c → Q A c × Sched ; R = λ c → R A c × Sched }       -- Th unitᴵ = unitᴵ; Th (A ⊗ᴵ B) ≅ Th A ⊗ᴵ Th B (identity channel maps)
routeᶜ : Sched → Calls A X → SSP.Calls (Th A) (X × Sched)
routeᶜ σ (ret x)      = ret (x , σ)
routeᶜ σ (call c q k) = call c (q , σ) λ (r , σ′) → routeᶜ σ′ (k r)
routeᶜ σ (coin μ k)   = coin μ λ b → routeᶜ (σ / toss b) (k b)
routeᶜ σ (choose n k) = let i = σ [] n in routeᶜ (σ / pick (toℕ i)) (k i)
routeᶜ σ dead         = dead
routeᵖ : Protocol A B → SSP.Protocol (Th A) (Th B)      -- same St, init; step s c (q , σ) = mapᶜ regroup (routeᶜ σ (step P s c q))
close  : Sched → SSP.Protocol (Th Ωᴵ) Ωᴵ                -- feeds the token σ, keeps the verdict
```

- `routeᵖ (g ∘ᵖ f) ≡ routeᵖ g ∘ᵖ routeᵖ f` (from `routeᶜ σ (serve k t) = serve′ … (routeᶜ σ t)`), `routeᵖ wireᵖ = wireᵖ`, `routeᵖ (P ⊗ᵖ Q) ≈ routeᵖ P ⊗ᵖ routeᵖ Q`: a
  strong monoidal functor from ND *with structural equality* to SSP. It does **not** respect the law constructors (they hold only up to token adapters; `choose-comm`
  moves the token), so it is not defined on `≈ᵖ`-classes of `Prot⁺`.
- Who holds the token is the internal/adversary split again: the top-level `read` supplies the global demon; a component that passes the token on is resolved by it,
  one that substitutes its own resolves the choice itself.

**(2a) The theorem, quantifiers explicit.** Unfolded, `f ≤UC g` (ND) is `∀a ∃s ∀Y t m. (∀σ ∃σ′ E_f(σ) ≈ E_g(σ′)) × (∀σ′ ∃σ …)`; the routed statement in SSP at grade `Th X` is
`∀a′ ∃s′ ∀Y t m. E′_f ≈ E′_g`, with `a′`, `s′` free to tamper with tokens.

| claim | status | needs |
|---|---|---|
| (A) `runᴺ W σ ≈ runᵖ (close σ ∘ᵖ routeᵖ W)` for closed `W` | ✓ tree induction | |
| (T) `routeᵖ f ≈ᵁ routeᵖ g` (SSP, ancillas `Th Y`) ⇒ `f ≈ᵁ g` (ND) | ✓ | functoriality, (A); witness σ′ = σ |
| `f ≈ᵁ g` ⇒ `routeᵖ f ≈ᵁ routeᵖ g` | ✗ in general | witnesses move the token (`choose-comm`); true up to a token adapter |
| `routeᵖ f ≤UC routeᵖ g` ⇒ `f ≤UC g` | needs a `Full`-like hypothesis | the SSP simulator must be a `routeᵖ`-image (`Abstract2/Morphism.agda:79-100` shape) |
| `f ≤UC g` ⇒ `routeᵖ f ≤UC routeᵖ g` | needs σ′ uniform in the context | ND's `∃σ′` sits *inside* `∀ctx`, SSP's simulator is fixed before: a `τ̂ : Sched → Sched` |

(T) proof: `routeᵖ` of an ND context is an SSP context (functor, strong monoidal) and (A) turns each σ into a closed SSP run, so SSP's equality at the single token σ gives
image equality with σ′ = σ. It lets the SSP toolbox (reductions, Lemmas 5–6) prove ND equalities in which no witness moves. The brief's iff needs the two uniformity
hypotheses and, for `⇐`, a determinate (or `∀σ′∃σ`) ideal side: the second half of `≋ˢ` has no SSP counterpart.

**(2b) A `UCSetupMorphism` into the Kleisli category**, recommended against:

```agda
record UCSetupMorphismᴷ (𝕊 𝕊′ : UCSetup …) : Set _ where
  field F : Functor S.𝒞 (GradedKleisli S′.𝒞 S′.ℐ S′.ℳ)          -- F₀ A = (unit , A), F₁ f = (Instᴵ , rtˡ f , ρ⇒)
        Φ : MonoidalFunctor S.ℐ (K S′)                          -- ✗ `GradedKleisli.agda` is a plain Category (no ⊗ on (grade , object)); `LocallyGraded/Monoidal.agda` needs a braided ℐ
        κ : ∀ {X A} → U₀ (F₀ (T X A)) 𝒞′.⇒ T′ (Φ₀ X) (U₀ (F₀ A))  -- U₀ (i , c) = T′ i c  (`GradedKleisli.agda:157-164`)
        ν : PresheafMorphism F S.ℰ (S′.ℰ ∘F U-functor.op)       -- tests of the exported object, ℰ′ (T′ i c)
```

`κ` and its laws transport along `U`; `composeMorphism` survives only after `induced` (`Graded/Morphism.agda:91-104`) is redone for Kleisli-valued `F`; `Transfer.transfer` uses
`G f = κ ∘ F₁ f` and `S′.bridge`, restated at `ℰ′ ∘ U`. Obstacles: no monoidal Kleisli category (`Φ`); the functor laws (`rtˡ` lax); and (2a) needs none of it, since `rtˡ f ≤UC rtˡ g`
already concerns `𝒞′`-morphisms `A ⇒ T₀ Instᴵ B`. Under the site-local model of §5.1 the laws would hold up to `Slide` [INFERENCE]; the missing monoidal structure would remain.

### 4.3 Protocol-model and the other setups

**protocol-model** (`UC/Model/Setup.agda`) is reached only through SSP's chain (SSP §4.2–4.3): ND-secure ⇒ SSP-secure by (R), then SSP ─▶ `PM[wb]`. No direct `ND → PM` is available: PM's machines
are `Dₚ` Mealy machines without nondeterminism (`Protocol/Machine.agda` `morphism` has no `choose` case), and determinisation is not defined on `≈ᵖ`-classes of `Prot⁺` (§4.1). `machine-iso`, `Rel`, RS, IPDL and
causal boxes: none, for SSP's reasons (SSP §4.4).

### 4.4 Parallelism

`P ∥ Q` is **not derivable from `choose` and `⊗ᵖ`**. (1) `(P ⊗ᵖ Q) ∘ᵖ ⌜∇⌝` (shared import, SSP §3.1) is already *caller-scheduled* interleaving: each query is atomic and goes to one
factor, the caller's query order is the interleaving, and `≈ℰ` quantifies over all callers; no `choose` is involved. (2) Self-scheduled interleaving inside one activation needs both
operands on the *same* activation, and `⊗ᵖ` dispatches on the queried channel and has no fork; `choose` over *protocols* picks one implementation per activation. (3) What *is*
definable is a tree-level shuffle, by structural recursion:

```agda
_∥ᶜ_ : Calls A X → Calls A Y → Calls A (X × Y)       -- call granularity (a callee's step is atomic); clauses in order
ret x ∥ᶜ q = mapᶜ (x ,_) q ;  p ∥ᶜ ret y = mapᶜ (_, y) p ;  dead ∥ᶜ q = dead ;  p ∥ᶜ dead = dead
coin μ k ∥ᶜ q = coin μ λ b → k b ∥ᶜ q ;  choose n k ∥ᶜ q = choose n λ i → k i ∥ᶜ q          -- internal steps first
p@(call _ _ _) ∥ᶜ coin μ k′ = coin μ λ b → p ∥ᶜ k′ b ;  p@(call _ _ _) ∥ᶜ choose n k′ = choose n λ i → p ∥ᶜ k′ i
call c a k ∥ᶜ call c′ a′ k′ = choose 1 λ { 0 → call c a λ r → k r ∥ᶜ call c′ a′ k′ ; 1 → call c′ a′ λ r → call c a k ∥ᶜ k′ r }
```

Termination is lexicographic (first argument smaller, or equal with the second smaller). Obligations: congruence for `≈ᶜ` (product induction), commutativity up to `mapᶜ swap` by
`choose-comm` and `coin-comm`, associativity by `choose-join`. It is a tree operation, not a bifunctor of `Prot⁺ᴹ`; apply it to the steps of components triggered by one activation
(e.g. `Protocol A Tickᴵ`, `step (P ∥ Q) (s , t) tt tt = mapᶜ regroup (step P s tt tt ∥ᶜ step Q t tt tt)`). With a global demon the interleaving choice sees the coins of both operands
(§4.1); under the site-local model only its own site's.

## 5. Hard parts and risks

### 5.1 The information model: CE1 and its repairs

CE1 is the leak of §2.2. The options, to be decided before N1 because sites and tags live in `Calls`:

| option | `choose` laws | `ι` a presheaf morphism | routing a functor | leak | cost |
|---|---|---|---|---|---|
| G global history (§3, the brief) | ✓ | ✗ (CE1); (R) only | `rtˡ` lax [INFERENCE]; exact via `Th` | yes | baseline |
| S stream / coin-blind | ✗ (CE0) | | | none | — |
| D named tasks, oblivious per label (task-PIOA) | ✓ for fresh labels | ✓ [INFERENCE] | | none | a freshness side condition on every law use |
| K choice only in `init` (a family of protocols, composed by set lifting) | ✓ trivial | ✓ [INFERENCE] | ✓ | none | no per-activation choice: no interleaving |
| L site-local demons | ✓ per site | ✓ [INFERENCE] | up to `Slide` [INFERENCE] | none | `Site` tags, renaming in `≲ᵖ`; about twice N1–N2 |

**L, in deltas.** `Site = List Bool`; `call`, `coin`, `choose` carry a `Site`; `graft` tags the caller's nodes `L ∷ s` and `serve` the callee's `R ∷ s` as it visits them; a `note : Site → Event →
Calls A X → Calls A X` records a query received or a reply obtained, so a site's history is what an SSP component sees (without it, exclusive branches that differ only by query collide). `Sched = Site →
List Event → (n : ℕ) → Fin (suc n)`; `run⁺` carries `Site → List Event`. `_≲ᵖ_` gains a site bijection ρ (`θ-step` up to `renameSite ρ`) because `∘ᵖ-assoc` and `⊗ᵖ-interchange` re-bracket sites;
`run⁺-resp` gains the renaming `σ ↦ σ ∘ ρ`. Claim to prove: a local resolution of a closure's demons is an SSP closure (the local history in its state), so `ι` preserves `≈ℰ` and `ν-cong` holds. Even then
`ν` is Mono but not Epi, so `Transfer.transfer` needs a variant taking `Preserves-≈ℰ` directly: the same shape as the `transfer⁺` that symbolic and RS need (landscape §7).

**Recommendation.** If SSP-proof transfer or realistic adversaries matter, take L; otherwise build G (complete and cheaper), state ND-security as the stronger notion, and use (R) as the bridge
down. §3 is written for G because it is the brief.

### 5.2 Technical

- `run⁺-resp` (§3.4) is the only non-structural proof; `choose-join` needs an enumeration of `Σ i. Fin (suc (m i))` (`Data.Fin` has products, not dependent sums).
- Every structural induction of SSP's A2–A4 gains a `choose` case; `ι̂` needs three mutual lemmas (§4.1).
- `qual₊` and `qual` agree only through the finite-image lemma (§3.4); decide which `Evaluation` consumers use.
- A `dead` branch is an outcome like any other: a demon that may pick `dead` puts divergence in the image of every spec that has one.
- `Sched` is a function type and is never compared, so funext is not involved; levels are SSP's. Performance: SSP's record-expansion risk; keep `_∘ᵖ_` transparent.

### 5.3 Disagreements with the landscape and SSP

- SSP §4.4 and the landscape (§5, §6) say ND "includes SSP via a `StdUCMorphism`": false from `ℰᵖ` (CE1). Replace the edge by the reflection (R); the pullback morphism exists but its source is not SSP.
- Landscape §5: "no probability×nondeterminism monad" holds for strict distributive laws only (§2.3–2.4). "Routing either a theorem or a Kleisli-valued generalisation": a theorem, for threaded routing (§4.2).

## 6. Work breakdown

Every step is checked by `pagda` per module; the warning grep must be empty and the escape-hatch baseline must not grow. Paths are under `src/CategoricalCrypto/ND/`. Decide §5.1 (G or L) and the sharing
of the call-tree layer with SSP's A2 first.

| # | module | delivers | acceptance |
|---|---|---|---|
| N1 | `Protocol` | `Calls`, `mapᶜ`, `reindex`, `_≈ᶜ_`, `Protocol`, `graft`/`serve`, `_∘ᵖ_`, `⌜_⌝`, `wireᵖ`, `_⊗ᵖ_`, `_≲ᵖ_`, `_≈ᵖ_`, the `*-resp` lemmas | exports `≈ᶜ-isEquivalence`, `∘ᵖ-resp-≈ᵖ`, `⊗ᵖ-resp-≈ᵖ` |
| N2 | `Protocol/Category`, `Protocol/Monoidal` | `Prot⁺`, `Prot⁺ᴹ` (SSP A3–A4 plus `choose` cases) | exports `Prot⁺ᴹ` |
| N3 | `Sched` | `Event`, `Sched`, `_/_`, `run⁺`, `run⁺-map` | a two-protocol composite pins by `refl` |
| N4 | `Observation` | `_≋ˢ_`, `≋ˢ-isEquivalence`, `run⁺-resp` (every law), `ApproximationH`, `qevaluation⁺`, `evaluation⁺`; optionally `⟦_⟧` and its adequacy | exports `runᴺ-resp` |
| N5 | `Setup` | §3.5 | `StdSetup : UCSetup (suc 0ℓ)…`; warm time recorded |
| N6 | `Laws` | derived laws, `collapse`, `OrderSpec`, `bind-comm`, `_∥ᶜ_` | exports `transport` |
| N7 | `Include` | `ι`, the pullback morphism, CE1 as a checked counterexample, (R) | exports (R) |
| N8 | `Route` | `Th`, `routeᶜ`, `routeᵖ`, functoriality, (A), (T); `Schedᴵ` and the router example | exports (A), (T) |
| N9 | `Local` (if L) | §5.1 deltas, N1–N4 re-proved, N7's `ν` | `ι` a `StdUCMorphism` from SSP's own `ℰᵖ` |

Order: N1–N5 deliver the setup, N6 the laws, N7–N8 the links; N9 replaces the `choose` core of N1–N4 if L is chosen.

## 7. Sources

**Used (archived in `docs/kb/sources/papers/`):** **segala1995** (§4.3, Prop. 4.3.4; ch. 5 intro, §5.2, §5.6; ch. 7, Ex. 7.4.1, Thm 7.5.1), **canetti2006taskpioa** (abstract, §1, §2, §5 Def. 6),
**varacca2006** (§1), **zwart2019nogo** (§1, §3.1, Thms 3.5, 3.12), **bonchi2022** (§4.1–4.2, §5), **canetti2015suc** (§1.2–1.3, §2.2), **backes2007rsim** (abstract, §1.3); via SSP: brzuska2018,
ssprove2023, lochbihler2019cc §IV, maurer2011cc §5.1.

**Index check:** `segala1995`, `varacca2006`, `zwart2019nogo`, `bonchi2022`, `canetti2006taskpioa`, `backes2007rsim` each have an `INDEX.md` line and a `refs.bib` entry; nothing was missing.

**Not retrievable**, in `docs/kb/sources/litreview/BLOCKED-URLS.md` (default-deny firewall; three attempts 75 s apart against ACM, doi.org, IRIF, HAL): Goy–Petrişan, LICS 2020 (`goy2020`; abstract only,
one statement in §2.4). Canetti's UC (ePrint 2000/067) was already blocked and is not cited; Mislove 2000, Jacobs 2008 and Tix–Keimel–Plotkin 2009 are cited only through bonchi2022 and varacca2006.
**Newly archived:** none.
