# IPDL as a UC setup

Plan of 2026-10-09, refining `docs/uc-setup-landscape.md` §4–§5; nothing is typechecked. "IPDL" is
gancher2023ipdl, whose numbering is used (appendices complete only in the archived
`gancher2023ipdl-tech-report.pdf`); Coq files are those of github.com/ipdl/ipdl.

## 1. Summary

- **𝕀 = `Standard2.StdUC 𝕀ᴹ ℰⁿ`.** Objects: *polarised* typed channel contexts `pos ⇌ neg`
  (`Ctx = List Set`), `⊗` = componentwise `_++_`. A morphism `A ⇒ⁿ B` is an IPDL reaction
  network in flat form reading `pos A ++ neg B` and defining `neg A ++ pos B`; composition is
  `new B in (f ∥ g)`, identities are copy reactions. Hom-setoid: IPDL's exact theory as an
  inductive relation `_≐_`. Tests: IPDL protocols `A ⇒ⁿ Ωⁿ` (`Ωⁿ = [Bool] ⇌ []`) modulo IPDL
  closures, via `UC.Core.Evaluation`, read by lazy memoised evaluation into `Dₚ Bool`. Levels `suc 0ℓ`.
- Closest existing setup: 𝔾ᵒ (𝕀 is the G-construction of unpolarised nets; `Ωⁿ` compiles to `Ωᴵ`).
- **No `UCSetupMorphism` to or from any existing or planned setup.** The landscape's
  `IPDL → random systems` (and `→ 𝔾ᵒ`) fails `F.identity` and `F-resp-≈`: IPDL's `exch` and
  `unused` hold only against IPDL-shaped environments (§4.1: a closure with advantage 1).
  `→ docs/uc-setup-causal-boxes.md`: none (§4 there). `docs/uc-setup-symbolic.md`: none.
- What survives is a semifunctor: the pull compile preserves composites and closed runs, so attacks
  transfer from 𝕀 to 𝔾ᵒ, security does not (§4.4, optional).

## 2. The source model

- **Syntax** (§4.1, Fig. 4): reactions `ret e | samp D | read c | if e then R else R | x ← R; S`;
  protocols `o := R | P ∥ Q | new o : τ in P`, up to α on `new`-bound channels.
- **Typing** (Figs. 5–6): `Δ ⊢ P : I → O`. `o := R : I → {o}` needs `o ∉ I`; R reads `I ∪ {o}`
  (`o := read o` diverges). `P ∥ Q : I → O₁ ∪ O₂` from `P : I ∪ O₂ → O₁`, `Q : I ∪ O₁ → O₂`:
  mutual reading, disjoint outputs, so every channel has one reaction and fires at most once.
  `new o in P` hides an output; a simulator is any `Sim : I → O` (paper §4.1). **Composition** of
  `P : I → M`, `Q : M → O` is `new M in (P ∥ Q)`; **tensor** is `∥` with disjoint inputs, no cross reads.
- **Operational semantics** (§4.2.1, Figs. 7–8): an output `o := v` substitutes every `read o`;
  `P ⇓ η` runs to quiescence. Reads block, hence confluence (Lemma 4.3) and a unique ⇓ (Cor. 4.4).
- **Distinguishers** (Defs 4.5–4.7, Fig. 9): k-bounded PTMs issuing `Input(i, v)` (no effect once
  i is assigned), `Get(o)` (`Some v` or `None`: absence is observable, which IPDL protocols cannot
  do, §4.2.2) and `Step`, with ⇓ after each query. **Advantage** `|Pr[A(C[P])] − Pr[A(C[Q])]|`
  over program contexts C (Def 4.11; Def C.1 with explicit bounds).
- **Equality** (§4.3): exact `Δ ⊢ P = Q : I → O` inductively by Figs. 10–11 and 15, relative to an
  exact theory `T=` (Def 4.12). Approximate `P ≈^{(k,l)}_λ Q` (Figs. 12/18): k counts axiom uses,
  l bounds context size, error `ε^l_k(p,q) = k · max_i εᵢ(p+l, q)` (Lemma C.2); asymptotics Thm C.5.
- **Soundness** (§4.4, App. B): each exact rule induces a protocol bisimulation (Lemma 4.19/B.15,
  Def 4.14/B.10), and bisimilar protocols give equal Pr to every A, k, C (Lemma 4.18).
- **Coq** (§5.1): shallow, `chan t` abstract. `Exp.v`: `rxn = Samp | Ret | Read | Bind`, `EqRxn`
  (`EqBindC` commutes *any* two reactions). `Core.v`: `ipdl = Zero | Out | Par | New`, PHOAS
  `New : (chan t → ipdl) → ipdl`, `EqProt` (incl. `EqZero`, `EqFold`, `EqSubst` with `isDet`,
  `EqUnused`, `EqSplitBranch`). `Approx.v`: `AEqProt` indexed by `err = (k, l)`. Axioms are Coq
  `Axiom`s (`EqProt_base`, `AEqProt_base`); semantics and soundness are on paper only.

What the rest depends on: IPDL's `=` is a contextual equivalence relative to IPDL contexts and
Fig. 9 distinguishers, made sound by confluence — not a behavioural equality of a sequential system.

## 3. The `StdUC` instantiation

### 3.1 Decisions

1. **Polarised objects** (refines the landscape's "typed channel sets"). With one-directional
   channel sets every closure `J ⇒ A`, test `B ⇒ Ω` and ancilla is one-directional, so neither
   `_≈ℰ_` nor `_≈ᵁ_` feeds outputs back into inputs: environments are non-adaptive and adversary
   inputs (scheduling, corruption: paper §5.2–5.5) are fixed by the closure. With `pos ⇌ neg` the
   adversary interface is `leakage ⇌ adversary-inputs`, an ancilla `[] ⇌ [τ]` carries a test's
   value back to the closure, and `Sim` is a grade morphism. `new B in (f ∥ g)` hides both
   directions natively, so `Categories.GConstruction` (trace and solver coherence) is not used.
2. **Flat nets**: `(H, one reaction per channel of O ++ H)`, IPDL's prenex form
   `new H in ∥_c (c := R_c)`. `comp-comm/assoc`, `new-exch`, `comp-new`, `embed` become one α rule.
3. **Hom-setoid = the inductive theory (a).** `_≤UC_` reads 𝒞's equality only through `≈C⇒≈ᵁ`
   and `≤UC-resp-≈` (`Abstract2.agda:63,149`); the rest is `_≈ᵁ_`, built from ℰ. So (a) and (b)
   give the same `_≤UC_` for one ℰ, and the choice decides two other things. Under (a) the
   category laws use structural constructors only, IPDL derivations are hom-equalities, and
   `F-resp-≈` out of 𝕀 is an induction over derivations (§4.2 is its case list). Under (b)
   (agreement of `eval` in every closing context, i.e. 𝕀's `_≈ᵁ_` [INFERENCE: contexts factor
   through an ancilla]) the laws are semantic, derivations enter through the same `sound`, and
   `F-resp-≈` needs full abstraction; (b) as equality of compiled machines is excluded (§4.2).
   **One setup suffices**: an identity-on-nets `StdUCMorphism` (a) → (b) would have
   `F-resp-≈ = sound`, ν = id and a `Transfer.transfer` that is the identity on `_≤UC_`;
   `changeKernel` cannot express it (it fixes 𝒞 with its hom-setoid), `Factorization` acts on ν.
4. **Semantics: lazy memoised evaluation of closed nets** — read = demand, memoise the first value;
   demanding a channel under evaluation is a cycle and yields `nothing` (left unassigned by Fig. 8's
   quiescence), which blocks its readers and is mass loss at the verdict. It is the closed run of
   the pull compile (§4.1) [INFERENCE: it computes ⇓'s least fixed point on the verdict].

### 3.2 Syntax and operations (`IPDL/Syntax.agda`, `IPDL/Net.agda`; `--safe --without-K`)

```agda
Ctx : Set₁
Ctx = List Set

infix 4 _∋_                          -- positions, not `≡` on `Set`: `--without-K` costs nothing
data _∋_ : Ctx → Set → Set₁ where
  here  : ∀ {Γ τ}   → (τ ∷ Γ) ∋ τ
  there : ∀ {Γ σ τ} → Γ ∋ τ → (σ ∷ Γ) ∋ τ
Ren : Ctx → Ctx → Set₁
Ren Γ Δ = ∀ {τ} → Γ ∋ τ → Δ ∋ τ

-- Fig. 4 in the continuation form of `Protocol.Calls`: `if`/`x ← R; S` are Agda's,
-- `samp` is a cascade of coins (`Protocol.uniformVec`)
data Rxn (Γ : Ctx) (τ : Set) : Set₁ where
  ret  : τ → Rxn Γ τ
  read : ∀ {σ} → Γ ∋ σ → (σ → Rxn Γ τ) → Rxn Γ τ
  coin : Dist-ℚ Bool → (Bool → Rxn Γ τ) → Rxn Γ τ

_>>=ʳ_ : Rxn Γ σ → (σ → Rxn Γ τ) → Rxn Γ τ      -- by recursion, as `Protocol._>>=ᶜ_`
renʳ   : Ren Γ Δ → Rxn Γ τ → Rxn Δ τ             -- read (ρ c) λ v → renʳ ρ (k v), …
IsDet  : Rxn Γ τ → Set                           -- `Core.v:isDet`: no `coin` on any path
-- `Covers R₂ R₁` (R₂ reads on every path what R₁ may read: `EqUnused`), `ReadFree R`: likewise

record Net (I O : Ctx) : Set₁ where  -- new H in (∥_{c ∈ O ++ H} c := def c)
  field H   : Ctx
        def : All (Rxn (I ++ O ++ H)) (O ++ H)

record Chans : Set₁ where            -- `pos` travels rightwards, `neg` leftwards
  constructor _⇌_
  field pos neg : Ctx

_⇒ⁿ_ : Chans → Chans → Set₁
A ⇒ⁿ B = Net (pos A ++ neg B) (neg A ++ pos B)
_⊗ᶜ_ : Chans → Chans → Chans
A ⊗ᶜ B = (pos A ++ pos B) ⇌ (neg A ++ neg B)

_∘ⁿ_ : B ⇒ⁿ C → A ⇒ⁿ B → A ⇒ⁿ C                 -- new B in (f ∥ g): both polarities hidden
g ∘ⁿ f = record { H = pos B ++ neg B ++ H f ++ H g
                ; def = assemble (map (renʳ ρᶠ) (def f)) (map (renʳ ρᵍ) (def g)) }

_⊗ⁿ_ : A ⇒ⁿ B → C ⇒ⁿ D → (A ⊗ᶜ C) ⇒ⁿ (B ⊗ᶜ D)
f ⊗ⁿ g = record { H = H f ++ H g ; def = interleave (map (renʳ ρˡ) (def f)) (map (renʳ ρʳ) (def g)) }

wireⁿ : Ren (neg A ++ pos B) (pos A ++ neg B) → A ⇒ⁿ B     -- every output copies one input
wireⁿ ρ = record { H = [] ; def = tabulateᶜ λ c → read (inputᶜ (ρ c)) ret }
idⁿ : A ⇒ⁿ A                         -- copy reactions `o := read i` (`Core.v:copy`)
idⁿ = wireⁿ swap-blocks
```

Helpers: `ρᶠ ρᵍ ρˡ ρʳ` split `_∋_` over `_++_`; `assemble`/`interleave` reorder `All` blocks
(`All.Properties.++⁺/++⁻ˡ/++⁻ʳ`); `lookupᶜ tabulateᶜ _[_]≔_` are `_∋_`-indexed `lookup/tabulate/updateAt`;
`⟨ R ⟩`, `⟨ R₁ , R₂ ⟩`, `⟨ R₁ , R₂ , R₃ ⟩` are nets with those outputs (reactions over `I ++ outputs`),
`₀ ₁` their first outputs, `ν₁` hides the first, `wk₁` weakens past it, `∅ⁿ : Net I []`.

### 3.3 The hom-setoid (`IPDL/Theory.agda`; `--safe --without-K`)

```agda
record Axioms : Set₂ where           -- IPDL's T= (Def 4.12): a parameter, not `Core.v`'s `Axiom`
  field Tʳ : ∀ {Γ τ} → Rxn Γ τ → Rxn Γ τ → Set₁
        Tⁿ : ∀ {I O} → Net I O → Net I O → Set₁

module Theory (𝒜 : Axioms) where
  open Axioms 𝒜

  data _≐ʳ_ {Γ τ} : Rxn Γ τ → Rxn Γ τ → Set₁ where                          -- Fig. 15, Exp.v
    refl      : R ≐ʳ R                -- sym, trans likewise
    read-cong : (∀ v → k v ≐ʳ k′ v) → read c k ≐ʳ read c k′                   -- EqRxnBind
    coin-cong : (∀ b → k b ≐ʳ k′ b) → coin μ k ≐ʳ coin μ k′
    read-det  : read c (λ x → read c (k x)) ≐ʳ read c (λ x → k x x)           -- EqReadSame
    coin-pure : coin μ (λ _ → R) ≐ʳ R                                         -- EqSampUnused
    pure-sem  : (p : ReadFree R) (q : ReadFree S) → distʳ R p ≈Mℚ distʳ S q → R ≐ʳ S
                                                      -- flip-unif, EqSampBijection/Bind/Ret
    axiom     : Tʳ R S → R ≐ʳ S

  data _≐_ : Net I O → Net I O → Set₁ where                                 -- Figs. 10–11, Core.v
    refl    : N ≐ N                   -- sym, trans likewise
    α       : (ρ : H N ↔ᶜ H N′)
            → (∀ c → lookupᶜ (def N′) c ≐ʳ renʳ (lift ρ) (lookupᶜ (def N) (lift⁻¹ ρ c)))
            → N ≐ N′                  -- comp-comm, comp-assoc, new-exch, comp-new, embed
    react   : (c : (O ++ H N) ∋ τ) → lookupᶜ (def N) c ≐ʳ R → N ≐ N [ c ]≔ R    -- cong-react
    cong-∘  : g ≐ g′ → f ≐ f′ → (g ∘ⁿ f) ≐ (g′ ∘ⁿ f′)                          -- cong-comp, cong-new
    cong-⊗  : f ≐ f′ → g ≐ g′ → (f ⊗ⁿ g) ≐ (f′ ⊗ⁿ g′)
    alias   : CopyOf N h y → N ≐ elim N h y     -- hidden `h := read y` renamed away (not IPDL)
    promote : CopyOf N o h → N ≐ adopt N o h    -- output `o := read h` takes over hidden h
    gc      : (N : Net I []) → N ≐ ∅ⁿ                                         -- absorb-left, EqZero
    diverge : ⟨ read ₀ k ⟩ ≐ ⟨ read ₀ ret ⟩                                   -- diverge
    fold    : ν₁ ⟨ wk₁ R , read ₀ (wk₁ ∘ k) ⟩ ≐ ⟨ R >>=ʳ k ⟩                  -- fold-bind, EqFold
    split   : ⟨ read b λ x → if x then l else r ⟩      -- fold-if, EqSplitBranch (weakenings elided)
            ≐ ν₁ (ν₁ ⟨ read b (λ _ → l) , read b (λ _ → r) , read b λ x → if x then read ₀ ret else read ₁ ret ⟩)
    subsume : ⟨ read c₀ R₁ , read c₀ (λ _ → read ₀ R₂) ⟩ ≐ ⟨ read c₀ R₁ , read ₀ R₂ ⟩    -- c₀ ∈ I ∪ O
    subst   : IsDet R₁ → ⟨ R₁ , read ₀ k ⟩ ≐ ⟨ R₁ , R₁ >>=ʳ k ⟩                       -- EqSubst
    axiom   : Tⁿ N N′ → N ≐ N′
```

`ret-bind` is definitional; `bind-ret`, `bind-assoc`, `if-*`, `input-unused`, `embed`, `renʳ-id`,
`renʳ-∘` are lemmas (`read-cong`/`coin-cong`; Agda's `if`; `cong-∘` with wires). `exch`
(`EqBindC`) and `unused` (`EqUnused`) are **not** constructors but the canonical axioms `𝒜ᴵᴾᴰᴸ`
(`Tʳ ⊇ exch`, `Tⁿ ⊇ unused`, plus the user's): 𝕀 and `sound` exist before their soundness (§5) is
proved, and that proof discharges a module parameter, not a postulate.

### 3.4 Category and monoidal structure (`IPDL/Monoidal.agda`; `--safe --without-K`)

```agda
𝕀 : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝕀 = categoryHelper record
  { Obj = Chans ; _⇒_ = _⇒ⁿ_ ; _≈_ = _≐_ ; id = idⁿ ; _∘_ = _∘ⁿ_
  ; assoc = ∘ⁿ-assoc ; identityˡ = ∘ⁿ-identityˡ ; identityʳ = ∘ⁿ-identityʳ
  ; equiv = record { refl = refl ; sym = sym ; trans = trans } ; ∘-resp-≈ = cong-∘ }

𝕀-monoidal : Monoidal 𝕀
𝕀-monoidal = monoidalHelper 𝕀 record
  { ⊗               = record { F₀ = λ (A , B) → A ⊗ᶜ B ; F₁ = λ (f , g) → f ⊗ⁿ g
                             ; identity = ⊗ⁿ-identity ; homomorphism = ⊗ⁿ-interchange
                             ; F-resp-≈ = λ (φ , ψ) → cong-⊗ φ ψ }
  ; unit            = [] ⇌ []
  ; unitorˡ         = wire-iso λ-ren ; unitorʳ = wire-iso ρ-ren ; associator = wire-iso α-ren
  ; unitorˡ-commute = wire-natural λ-ren ; unitorʳ-commute = wire-natural ρ-ren
  ; assoc-commute   = wire-natural α-ren
  ; triangle        = wire-coherence triangle-ren ; pentagon = wire-coherence pentagon-ren }

𝕀ᴹ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝕀ᴹ = record { U = 𝕀 ; monoidal = 𝕀-monoidal }

-- all of the coherence: wires compose and rename (`alias`/`promote` + α), equal renamings agree (`react`)
wire-∘    : wireⁿ ρ ∘ⁿ wireⁿ σ ≐ wireⁿ (σ ∘ ρ)
wire-cong : (∀ {τ} (c : _ ∋ τ) → ρ c ≡ ρ′ c) → wireⁿ ρ ≐ wireⁿ ρ′
wire-renᵒ : wireⁿ ρ ∘ⁿ f ≐ renᵒ ρ f
wire-renⁱ : f ∘ⁿ wireⁿ ρ ≐ renⁱ ρ f
```

**On the nose vs up to `_≐_`.** Objects: `unit ⊗ᶜ A = A` is definitional (`[] ++ xs = xs`);
`A ⊗ᶜ unit`, `(A ⊗ᶜ B) ⊗ᶜ C` are only propositional, so `unitorʳ` and the associator are proper
wires. No morphism law is definitional: `assoc` is α (permuting the hidden blocks), identities are
`alias` + `promote` + α, `⊗` functoriality is `react` on renamings, naturality/triangle/pentagon
are the wire lemmas plus pointwise renaming equalities. Only structural constructors appear, so 𝕀ᴹ
exists for every `Axioms`.

### 3.5 Evaluation and the test presheaf (`IPDL/Eval.agda`, `IPDL/Observation.agda`; `--guardedness`)

```agda
data Slot (τ : Set) : Set where
  empty busy : Slot τ
  done       : Maybe τ → Slot τ      -- `nothing`: never fires

Memo : Ctx → Set                     -- small by recursion: `_>>=ₚ_` binds within one level,
Memo []      = ⊤                     -- and the memo sits under `Dₚ` beside `Bool`
Memo (τ ∷ Γ) = Slot τ × Memo Γ

module Lazy {Γ : Ctx} (Δ : All (Rxn Γ) Γ) where        -- a closed net over its own channels
  mutual
    evalCh : ℕ → Memo Γ → Γ ∋ τ → Dₚ (Memo Γ × Maybe τ)
    evalCh zero    m c = returnₚ (m , nothing)          -- unreachable at fuel `suc (length Γ)`
    evalCh (suc n) m c = case lookupᶜ m c of λ where
      (done v) → returnₚ (m , v)                        -- single shot
      busy     → returnₚ (m , nothing)                  -- c depends on itself: deadlock
      empty    → evalR n (m [ c ]≔ busy) (lookupᶜ Δ c) >>=ₚ λ (m′ , v) → returnₚ (m′ [ c ]≔ done v , v)

    evalR : ℕ → Memo Γ → Rxn Γ τ → Dₚ (Memo Γ × Maybe τ)
    evalR n m (ret x)    = returnₚ (m , just x)
    evalR n m (coin μ k) = coinₚ μ >>=ₚ λ b → evalR n m (k b)
    evalR n m (read c k) = evalCh n m c >>=ₚ λ where
      (m′ , just v)  → evalR n m′ (k v)
      (m′ , nothing) → returnₚ (m′ , nothing)           -- a read blocks

eval : Net [] (Bool ∷ []) → Dₚ Bool                    -- `def N` is over `Bool ∷ H N` by reduction
eval N = Lazy.evalCh (def N) (suc (length (Bool ∷ H N))) emptyᶜ here >>=ₚ (detₚ ∘ proj₂)

Context : Chans → Chans → Set₁        -- reads f's outputs, defines f's inputs and the verdict
Context A B = Net (neg A ++ pos B) (pos A ++ neg B ++ (Bool ∷ []))
_⊛_ : Context A B → A ⇒ⁿ B → Net [] (Bool ∷ [])        -- new (A , B) in (K ∥ f)

-- IPDL/Sound.agda, parametrised by 𝒜 and `Sound 𝒜` (each axiom sound in every context)
sound        : f ≐ f′ → (K : Context A B) → eval (K ⊛ f) ≈ₚ eval (K ⊛ f′)
sound-closed : N ≐ N′ → eval N ≈ₚ eval N′

-- IPDL/Observation.agda: `UC.Model.Observation` with nets for machines
𝟘ⁿ Ωⁿ : Chans
𝟘ⁿ = [] ⇌ []                          -- the monoidal unit itself, unlike 𝔾ᵒ's `𝟘ᵒ`
Ωⁿ = (Bool ∷ []) ⇌ []                 -- no tick: a net computes unprompted, a machine does not

qevaluationⁿ : QEvaluation 𝕀 0ℓ 0ℓ
qevaluationⁿ = record
  { J = 𝟘ⁿ ; Ω = Ωⁿ ; X = spaceᴰ
  ; eval₀ = record { to = eval ; cong = λ e → ≈ₚ⇒≈ₚ[0] (sound-closed e) } }
evaluationⁿ : Evaluation 𝕀 0ℓ 0ℓ
evaluationⁿ = qual₊ ℚ-refinement qevaluationⁿ
open Evaluation evaluationⁿ public
open Observable observable public using (Test; _≋_) renaming (ℰᴼ to ℰⁿ)
```

A test on A is an IPDL protocol reading `pos A`, defining `neg A` and one `Bool`; `t ≋ t′` iff every
closure `𝟘ⁿ ⇒ⁿ A` gives verdict masses agreeing within every ε > 0, both compared as in
`Dp.Advantage` (an undefined verdict is lost mass). `spaceᴰ` is `UC.Machine.spaceᴹ` moved to
`CategoricalCrypto/Approx/Dp.agda` (§6 step 0), so 𝕀 does not import the machine layer. Approximately:

```agda
data _≈⟨_⟩_ : Net I O → ℚ → Net I O → Set₁ where                              -- Figs. 12/18
  strict : N ≐ N′ → N ≈⟨ 0ℚ ⟩ N′
  sym    : N ≈⟨ ε ⟩ N′ → N′ ≈⟨ ε ⟩ N
  trans  : N ≈⟨ ε ⟩ N′ → N′ ≈⟨ δ ⟩ N″ → N ≈⟨ ε ℚ.+ δ ⟩ N″            -- k adds up
  mono   : ε ℚ.≤ δ → N ≈⟨ ε ⟩ N′ → N ≈⟨ δ ⟩ N′                          -- subsume
  cong-∘ : g ≈⟨ ε ⟩ g′ → f ≈⟨ δ ⟩ f′ → (g ∘ⁿ f) ≈⟨ ε ℚ.+ δ ⟩ (g′ ∘ⁿ f′)  -- cong-comp, cong-new
  cong-⊗ : f ≈⟨ ε ⟩ f′ → g ≈⟨ δ ⟩ g′ → (f ⊗ⁿ g) ≈⟨ ε ℚ.+ δ ⟩ (f′ ⊗ⁿ g′)
  axiom  : Tᵃ ε N N′ → N ≈⟨ ε ⟩ N′

sound≈ : f ≈⟨ ε ⟩ f′ → (K : Context A B) → eval (K ⊛ f) ≈ₚ[ ε ] eval (K ⊛ f′)
```

Contexts are unbounded, so IPDL's `l` disappears and Lemma C.2's error is a sum; only *statistical*
ε-axioms are sound here (computational ones: §5). The quantitative setup is
`UC.Quantitative.Observed 𝕀ᴹ ℚ-ordered qevaluationⁿ P.∼ᵃ-isEquivalence P.zero⇒positive`,
as `UC.Model.Quantitative` does for 𝔾ᵒ.

### 3.6 Setup, levels, layout

```agda
module CategoricalCrypto.IPDL.Setup (𝒜 : Axioms) (𝒜-sound : Sound 𝒜) where   -- … --guardedness
open Std2.StdUC 𝕀ᴹ ℰⁿ public          -- 𝕀ᴹ from IPDL.Monoidal 𝒜, ℰⁿ from IPDL.Observation 𝒜 𝒜-sound
```

Levels: `read` quantifies over `σ : Set`, so `Rxn`, `Net`, `Chans`, `_≐_` live in `Set₁`,
`𝕀 : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)`, and `Evaluation 𝕀 0ℓ 0ℓ` gives
`ℰⁿ : Presheaf 𝕀 (Setoids (suc 0ℓ) (suc 0ℓ))`: `StdSetup` is a `UCSetup` at `suc 0ℓ` throughout,
`cs = ℓs = suc 0ℓ`, the levels of `UC.Model.Setup` and of the causal-box plan's ℰ. `Memo`, `Val`,
`Req` are small because `Dₚ`'s bind and `Protocol.St` live at `Set`. No K (`_∋_` instead of `≡`
on `Set`); no quotient (setoids; α is a constructor).

| module (`src/CategoricalCrypto/IPDL/`) | OPTIONS | exports |
|---|---|---|
| `Syntax`, `Net` | `--safe --without-K` | `Rxn`, `Net`, `Chans`, `_⇒ⁿ_`, `_∘ⁿ_`, `_⊗ⁿ_`, `wireⁿ`, `idⁿ` |
| `Theory`, `Monoidal` | `--safe --without-K` | `Axioms`, `_≐ʳ_`, `_≐_`, `𝕀`, `𝕀ᴹ`, wire lemmas |
| `Eval`, `Eval/Commute`, `Sound` | `… --guardedness` | `eval`, `Context`, `_⊛_`, `commute`, `sound` |
| `Observation`, `Setup`, `Approx` | `… --guardedness` | `ℰⁿ`, `StdSetup`, `_≈⟨_⟩_`, `sound≈` |
| `Compile` (optional, §4) | `… --guardedness` | `compileᴾ`, `compile-∘`, `compile-run`, counterexamples |

## 4. Morphisms

### 4.1 `IPDL → random systems` and `→ 𝔾ᵒ` (landscape §4): blocked

The landscape's F is the pull compile (an output request evaluates its reaction; an input read
queries the left; replies and outputs are memoised), for unidirectional nets a call/return package:

```agda
Val Req : Ctx → Set                   -- small alphabets by recursion
Val []      = ⊥
Val (τ ∷ Γ) = τ ⊎ Val Γ
Req []      = ⊥
Req (_ ∷ Γ) = ⊤ ⊎ Req Γ

iface : Chans → Iface                 -- Neg asks for a channel, Pos answers it
iface A = (Val (pos A) ⊎ Req (neg A)) ⇿ (Req (pos A) ⊎ Val (neg A))

compileᴾ : (I ⇌ []) ⇒ⁿ (O ⇌ []) → Protocol (iface (I ⇌ [])) (iface (O ⇌ []))
compileᴾ N = record
  { St = Memo ((I ++ []) ++ O ++ H N) ; init = emptyᶜ
  ; step = λ m q → serve m (askedᶜ q) >>=ᶜ λ where
      (m′ , just v)  → ret (m′ , answerᶜ q v)
      (m′ , nothing) → dead }        -- `serve` = `Lazy.evalCh` in `Calls`: an empty input slot `call`s

F₀ : Chans → MonoidalCategory.Obj 𝔾ᵒ
F₀ = ifaceᵒ ∘ iface
F₁ : (I ⇌ []) ⇒ⁿ (O ⇌ []) → F₀ (I ⇌ []) 𝔾ᵒ.⇒ F₀ (O ⇌ [])
F₁ = procᵒ ∘ morphism ∘ compileᴾ                 -- Protocol.Machine.morphism, UC.Model.Seal.procᵒ
-- Φ = F (StdUC: 𝒞 = ℐ).  κ = Op.δ : F₀ (X ⊗ᶜ A) ⇒ F₀ X ⊗ F₀ A is procᵒ (wireᴹ split merge),
-- the Val/Req relabelling across `_++_` (UC.Machine.wireᴹ); ε likewise.
-- ν.η A t = procᵒ (wireᴹ toΩ fromΩ) ∘ F₁ t    (iface Ωⁿ ≅ Ωᴵ = Bool ⇿ ⊤)
```

RS has 𝔾ᵒ's objects and morphisms (the premise of `docs/uc-setup-random-systems.md`), so the same
data serve both, and `StdUCMorphism` would apply (F is strong monoidal on objects). Obligations:

1. **`F.identity`: false in both.** `F₁ idⁿ` memoises, `𝒢.id = σ⇒` forwards every message. A test
   that asks for o twice, against a closure answering its first request `true` and later ones
   `false`, sees `true, false` through `σ⇒` and `true, true` through `F₁ idⁿ`.
2. **`F.homomorphism`: plausible for unidirectional nets.** The consumer memoises, so each middle
   channel is requested once, in its order: relate `compileᴾ (g ∘ⁿ f)` and `compileᴾ g ∘ᵖ compileᴾ f`
   through a reachable-configuration machine (`Protocol.Machine.Compose`), then `morphismCompose`.
   Polarised nets need re-entrant states, which `Protocol.Machine.stepᴹ` sends to `botₚ`.
3. **`F.F-resp-≈`: false in both** (the ctx rows of §4.2), for 𝔾ᵒ also at the beh row. With
   `i j o : Bool`, `P₁ = ⟨ read i λ x → read j λ _ → ret x ⟩` and
   `P₂ = ⟨ read j λ _ → read i λ x → ret x ⟩` satisfy `P₁ ≐ P₂` (`react` + `exch`). The closure
   `order = MC.mk (initˢ ℕ 0) λ where (n , inj₂ r) → returnₚ (suc n , inj₂ (answer r (n ≡ᵇ 0)))`
   (`inj₁` absurd) and the test "ask o, output it" give `Obs = returnₚ true` for `F₁ P₁` and
   `returnₚ false` for `F₁ P₂`: advantage 1. No IPDL closure can see the order of demands.
4. **Strong monoidal structure: true** (relabelling wires compose; `κ-return/sub/ext` come from
   `Oplax` as in `StdUCMorphism`). Not the obstruction.
5. **ν: `η` is not a setoid map**: `P₁`, `P₂` as tests on `(Bool ∷ Bool ∷ []) ⇌ []` are `≋`-equal,
   their images are not (`order` again).

The security transport the landscape wants is **false**, not merely unproved: `P₁ ≤UC P₂` holds in
𝕀 (`≈ᵁ⇒≤UC`), `F₁ P₁ ≤UC F₁ P₂` fails in 𝔾ᵒ (trivial adversary interfaces leave no simulator to
absorb the order). Only a non-IPDL variant maps — formal linear aliases as identities, no
`exch`/`unused` (into RS; also no samp/read exchange for 𝔾ᵒ) — and it drops `EqBindC`, on which
IPDL proofs run (`Exp.v`'s `r_swap` tactics).

### 4.2 Rule by rule

*𝕀*: how `sound` proves the rule for closed lazy evaluation in every context — **nose**
(definitional), **Dₚ** (`>>=ₚ-comm`, coin mass 1, `>>=ₚ-cong`), **sim** (a memo relation preserved
step by step), **L3** (§5). *Compile*: the open pull compile of §4.1 — **nose**; **sim** (`_≈ᴹ_` by a
pure state map, possibly through a reachable-configuration machine: valid into 𝔾ᵒ); **beh** (equal
conditional output distributions only: RS); **ctx** (equal only against IPDL-shaped environments).

| rule (paper / Coq) | 𝕀 | compile |
|---|---|---|
| ret-bind / `EqRetBind`; if-left, if-right, if-ext | nose | nose |
| bind-ret, bind-bind / `EqBindRet`, `EqBindA`; cong-bind / `EqRxnBind` | lemma, induction | sim |
| exch, samp–samp / `EqBindC` | Dₚ | sim (one activation) |
| exch, samp–read / `EqBindC` | Dₚ | **beh** (eager vs lazy sample across a query) |
| exch, read–read; `EqBindC` in general | **L3** | **ctx** (query order) |
| read-det, diverge, fold-bind, fold-if, subsume / `EqReadSame`, `EqDiverge`, `EqFold`, `EqSplitBranch`, `EqSubsume` | sim (same demand order; memo hit, blackhole, fewer memo entries) | sim |
| samp-pure, flip-unif / `EqSampUnused`, `EqSampBijection`, `EqSampBind`, `EqSampRet` | Dₚ | sim |
| comp-comm, comp-assoc, new-exch, comp-new, embed / `EqCompComm`, `EqCompAssoc`, `EqNewExch`, `EqCompNew`, `EqCongCompZero` (α) | sim (memo reindexing) | sim |
| input-unused (derived: `cong-∘`, projection wire); cong-react / `EqCongReact` (`react`) | from `_≐ʳ_` | class of premise |
| cong-comp-left, cong-new / `EqCongComp`, `EqCongNew` | contexts compose | needs `F.homomorphism` |
| absorb-left / `EqZero` (`gc`); `alias`, `promote` | sim (never demanded; copies) | sim |
| subst / `EqSubst` (`IsDet`) | sim + determinism | sim |
| unused / `EqUnused` | **L3** | **ctx** (R₁'s reads move first) |
| exact axioms T= / `EqAxiom` | hypothesis | the user's |
| approximate: strict, sym, trans, subsume, embed, cong-comp, cong-new, axiom / `AEqProt` | `≈ₚ[_]` triangle; contexts nonexpansive | as the exact rows |
| category: identity | `alias`, `promote` | **fails** (§4.1.1) |
| category: composition, ⊗, κ | α, wires | sim (unidirectional) |

So no compilation target in the tree is reachable: RS is blocked by the ctx rows and the identity,
𝔾ᵒ additionally by the beh row.

### 4.3 The other setups

- **Into 𝕀: none.** 𝔾ᵒ/RS machines, SSP packages (`Protocol A B` serves unboundedly many queries)
  and `machine-iso` relations are not single-shot networks.
- **→ `docs/uc-setup-causal-boxes.md`: none (§4 there)**; their obstruction is time, not order.
- **→ / ← `docs/uc-setup-symbolic.md`: none.** Symbolic → 𝕀 would be a computational-soundness
  theorem into a computational setup; not planned.
- **Inside 𝕀**: one setup (§3.1.3). If ℰⁿ proves coarser than Fig. 9 (§5), the repair is a strategy
  presheaf ℰˢ and `changeKernel ℰⁿ ℰˢ ν` (ν runs a protocol test as a Fig. 9 strategy).

### 4.4 What survives: an attack-transfer semifunctor (optional)

For unidirectional nets, `compile-∘ : F₁ (g ∘ⁿ f) ≈ F₁ g ∘ F₁ f` (§4.1.2) and
`compile-run : eval N ≈ₚ ⟦ F₁ N ⟧ᴼ` (through the relabelling wires at `𝟘ⁿ`, `Ωⁿ`; `compileᴾ`'s closed
run is `Lazy.evalCh` plus `drive` junctions) give `compile-reflects-≈ℰ : F₁ f ≈ℰᵒ F₁ g → f ≈ℰⁿ g`,
the one square of `Presheaf.Morphism.mono⇒reflects` restated because F is not a functor: attacks on
IPDL protocols are attacks in 𝔾ᵒ. `reflects-≤UC` does not follow (`Full Φ` fails).

## 5. Hard parts and risks

- **The commutation lemma (L3)**, the only non-local proof and the price of `exch` and `unused`:
  for a consistent memo m (done entries agree with the net, nothing busy),
  `(evalR n m R >>=ₚ λ (m₁ , x) → evalR n m₁ S >>=ₚ λ (m₂ , y) → returnₚ (m₂ , x , y))`
  `≈ₚ (evalR n m S >>=ₚ λ (m₁ , y) → evalR n m₁ R >>=ₚ λ (m₂ , x) → returnₚ (m₂ , x , y))`.
  Strategy: fix per channel the outcomes of its coins; then evaluation is deterministic and
  computes the order-free least fixed point (a busy demand is a genuine cycle in either order), and
  the `Dₚ` weight is the product of the channels' path weights, reordered by `>>=ₚ-comm`. It is
  Lemma 4.3 in this semantics; staging (§3.3) keeps it off the setup's critical path.
- **Per-rule simulations**: one generic lemma (a memo relation preserved by `evalCh`/`evalR` gives
  `≈ₚ`) plus one relation per sim row; `subst` needs "a deterministic re-run makes no new demand".
- **Coinduction, funext**: `Dₚ` only from `Eval` on, and evaluation is fuel-bounded recursion (fuel =
  one more than the number of channels, `fuel-irrelevant` beyond it), never corecursion. Continuations
  are compared pointwise (`read-cong`); `≡` side conditions (`CopyOf`) are on user syntax (`refl`).
- **Performance**: `open StdUC` at a transparent bundle cost 𝔾ᵒ 12 GiB (`UC/Model/Seal.agda`); 𝕀's
  homs are small first-order records, but measure `Setup` warm and, over budget, seal `𝕀ᴹ` with that
  header's four disciplines. Build `curriedTensor` triples over an abstract bundle (`Machine/MonoidalCategory.agda`).
- **Faithfulness of ℰⁿ**: Fig. 9 distinguishers observe absence without blocking; IPDL protocols
  cannot. IPDL-provable ⇒ ℰⁿ-equal (a 2-round `Step; Get b` distinguisher simulates a test), and
  polarised ancillas recover stage correlations (disagreement 2); equality with Fig. 9's kernel is open.
- **Computational assumptions**: ℰⁿ ranges over all contexts, so IND-CPA or DDH are not sound
  ε-axioms. IPDL's PPT layer (Def 4.11, Thm C.5) maps to a size grading
  `GradedSubCat Rates.monoidalCategory 𝕀ᴹ (suc 0ℓ)` (size = number of reactions, `Approx.v:size_ipdl`)
  under `UC.Family` + `UC.Family.Negligible`, as `UC.Model.Family` does at `gradingᵒ`.
- **Disagreements with `docs/uc-setup-landscape.md`**:
  1. §4 "IPDL embeds into random systems (or 𝔾ᵒ) as the single-use fragment … strong monoidal
     because both tensors are ⊎": κ is fine; identity and `F-resp-≈` fail and the transport claim
     is false (§4.1). §5's `IPDL ──▶ random systems` should go: IPDL is an island.
  2. §4 "a probabilistic kernel from input-channel values to output-channel values": quiescent
     output distributions indexed by partial input assignments are not compositional.
     `P_A = {c := samp flip (hidden); o := x ← read c; if x then ret false else (_ ← read i;
     ret false); o₂ := _ ← read i; read c}` and `P_B` (`o₂ := _ ← read i; samp flip`) agree on every
     partial assignment, yet the context `i := read o`, `b := read o₂` (o carried back by an ancilla
     `[] ⇌ [Bool]`) gives b true ½, undefined ½ for `P_A` and true ¼, false ¼, undefined ½ for `P_B`.
  3. §4 "objects = typed channel sets": non-adaptive (§3.1.1).
  4. The identity failure is the one `Protocol/Machine.agda`'s header records for `morphism wireᵖ`
     vs `𝒢.id`, so §4's `SSP → protocol-rewrite` with `F = Protocol.Machine.morphism` has it too.

## 6. Work breakdown

0. Move `Approximationᴹ`/`spaceᴹ` from `UC.Machine` to `CategoricalCrypto/Approx/Dp.agda` (rule 27).
   Accept: `UC.Machine`, `UC.Model.Observation`, `UC.Model.Quantitative` and their importers green.
1. `IPDL/Syntax.agda`, `IPDL/Net.agda`. Accept: green; Fig. 1's encryption protocol as a net.
2. `IPDL/Theory.agda`. Accept: green; exports `Axioms`, `_≐ʳ_`, `_≐_`, `bind-ret`, `bind-assoc`,
   `renʳ-id`, `renʳ-∘`, `input-unused`, `embed`.
3. `IPDL/Monoidal.agda`. Accept: green; exports `𝕀`, `𝕀ᴹ`; no semantic constructor in it.
4. `IPDL/Eval.agda`. Accept: green; exports `eval`, `Context`, `_⊛_`, `fuel-irrelevant`; `eval` of a
   closed two-coin net normalises (a `refl`-checked example).
5. `IPDL/Sound.agda`. Accept: green; `sound`, `sound-closed` cover every constructor.
6. `IPDL/Observation.agda`, `IPDL/Setup.agda`. Accept: green within budget (cost in the header);
   `StdSetup`, `_≤UC_`, `UC-compose`, `dummy-complete` at nets (sanity terms as in `Machine/UC.agda`).
7. `IPDL/Eval/Commute.agda`. Accept: green; exports `commute`, `exch-sound`, `unused-sound`: `Sound 𝒜ᴵᴾᴰᴸ`.
8. `IPDL/Approx.agda`. Accept: green; exports `_≈⟨_⟩_`, `sound≈`, the `Observed` instance.
9. `IPDL/Examples/Encryption.agda` (Figs. 1–3; decryption correctness a `Tⁿ` axiom, semantic
   security a `Tᵃ` hypothesis whose computational reading needs step 11). Accept: green; exports
   the `≤UCᵈ` statement against the ideal channel.
10. (optional) `IPDL/Compile.agda`. Accept: green; exports `compileᴾ`, `compile-∘`, `compile-run`,
    `compile-reflects-≈ℰ` and the §4.1 counterexamples `¬compile-identity`, `¬compile-exch`.
11. (optional) `IPDL/Family.agda`. Accept: green; exports the size grading and the negligible order.
12. Docs: landscape §4–§5 per the disagreements above (parent).

"Green" = house rules 5–6. Steps 1–6 are sequential; 7 needs only 4 and runs beside 5–6; 8–11
need 6. After integration: pagda on each module, the step-0 importers, the closure check, baseline grep.

## 7. Sources

- `gancher2023ipdl` (§§3–5; Figs. 4–12, 15–19; Defs 4.1–4.16, B.3, B.10, C.1; Lemmas 4.3, 4.18,
  4.19, B.15, C.2; Thm C.5). Newly archived: `gancher2023ipdl-tech-report.pdf` (full version, from
  github.com/ipdl/ipdl) and `.txt` extracts of both PDFs; INDEX lines appended, no new bib key.
  Read, not archived: `theories/Exp.v`, `Core.v`, `Approx.v` of that repository.
- Earlier versions (ePrint 2019/1422, 2021/147): not archived (Cloudflare challenge; superseded).
- The causal-box verdict is `docs/uc-setup-causal-boxes.md` §4 (portmann2017), not re-derived here.
