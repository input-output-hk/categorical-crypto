# The symbolic (Dolev–Yao) UC setup — plan

Plan of 2026-10-09. Steps 1–8 of §6 are built (2026-10-10); §3.2–§3.6 and §4.1 give their real
signatures. Steps 9–10 are blocked (§6). Statements about unwritten modules are design claims.
`[INFERENCE]` marks reasoning backed by neither a read source nor the tree. Citations are
`bibkey §/Def/p.` with printed pages (`docs/kb/sources/papers/INDEX.md`). Short names: CLC =
`comonlundhcortier2008`, CH = `canettiherzog2006`, BPW = `backes2003library`, AR = `abadirogaway2002`.

## 1. Summary

`Sym = StdUC 𝔻𝕐 ℰˢʸᵐ`, where 𝔻𝕐 is the free monoidal category (`Categories/FreeMonoidal.agda`)
on **Dolev–Yao roles**: finite reactive programs whose outputs are recipes over their own frame
(CH's roles, CLC's basic processes). Hom-equality is coherence `_≈Term_`. Tests are DY roles with
an ancilla, as in `Machine/UC.agda`. Two tests are equal when the same verdicts are possible under
some *globally fresh* naming, run in 𝔾ᵒ at term alphabets. The kernel is DY trace (may-testing)
equivalence; E is a kernel fact, because roles emit and store canonical forms; `GradeStable` holds
without hypotheses. Morphisms leave from the
syntactic twin `Sym≅`: to `Sym` (`changeKernel`), to machine-iso and to `ucSetupᴺ` (both
`StdUCMorphism`, unconditional). Computational soundness is a side-conditioned theorem over the
last. Nothing leaves `Sym` itself.

## 2. The source model

**Terms and knowledge.** Sorted signature, names and variables (`abadi2018applied` §2.1
pp. 3–5). An equational theory is a sort-respecting, non-trivial congruence, closed under
substitution for variables and names (§2.2 p. 6). DY cancellation (`dolevyao1983` §II-A p. 200,
§III-B p. 202) is the first destructor theory; these theories are convergent rewrite systems
(`blanchet2016proverif` §2.4 pp. 25–26). A frame `νñ.σ` is the exposed knowledge
(`abadi2018applied` §2.1 p. 4). Deducibility has four rules (`abadicortier2006` §2.3 p. 6). By
Prop 1 (p. 6), `φ ⊢ M` iff `ζσ =E M` for some recipe ζ with `fn(ζ) ∩ ñ = ∅`. Static equivalence
is Defs 1–2 p. 7 (`abadi2018applied` Defs 4.2–4.3 p. 15), and it is not the same as `⊢`
(Props 3–4 p. 8).

**Attacker.** It reads everything, applies public operations and its own keys, and starts and
answers sessions (`dolevyao1983` §I pp. 198–199). It is a closed process over public symbols
(`blanchet2016proverif` Def 3.1 p. 43), or a nondeterministic machine drawing from the closure of
its knowledge (CH §2.2 pp. 389–390).

**Composition and tensor.** Applied-π has `|`, `ν`, `!`, `if M = N` and I/O; `≡` includes
α-renaming and `Rewrite` by E (`abadi2018applied` §2.1 pp. 3–4, §2.2 p. 7). An adversary attaches
by `|` with the shared channels restricted (`delaune2009simulation` Def 6 p. 173;
`bohlunruh2013` Def 4.2 p. 33). The tensor is `|` on disjoint names (Thm 5.37(ii) p. 59). Fresh
names are global: `(Red Res)` picks `a′ ∉ Npub ∪ Npriv` (`blanchet2016proverif` Fig. 2.4 p. 26).
Token-passing variants exist: CH's roles `S × A × M → A × A × S` (Def 1 p. 389); BPW's `TH_H`,
one machine over a term database (§4 pp. 7–10); and CLC's
`cin(x).if … then cout(t) else cout(⊥)·0`, with all I/O through the attacker (§3.3 pp. 10–12).

**Equality and security.** Observational equivalence (`abadi2018applied` Def 4.1 p. 14) is
labelled bisimilarity (Thm 4.1 p. 17); diff-equivalence is finer (`blanchet2016proverif`
Thm 3.5 p. 74). In symbolic UC, `P ≤ Q` iff `∃ (S, φ, n). P ≋ νn.(Qφ | S)` (`bohlunruh2013`
Def 4.3 p. 33). This equals the black-box and `∀A ∃S` forms (Lemma 4.4 p. 34) and is closed under
`|`, `ν`, renamings and `!!`, but not `!` (p. 36, Thm 5.37 p. 59). `delaune2009simulation` uses a
preorder (Def 2 p. 173), under which SS = BB = UC (Thm 16 p. 175). The symbolic outcome is a barb,
not an advantage.

**Computational soundness.**
- AR Thm 1 (§5.2 p. 118) is passive: for acyclic expressions and type-0 encryption, pattern
  equivalence (§3.2 pp. 109–111) implies indistinguishability. Completeness fails (p. 124).
- BPW Thm 7.1 p. 33: the real library realizes `TH_H` under EUF-CMA and IND-CCA2 (Defs 5.1–5.2).
  It leaks lengths and has a commitment problem (§2.2 p. 5).
- CH Lemma 1 p. 394: concrete traces are DY-valid with overwhelming probability, even against
  unbounded environments, because encryption is `Fcpke` (p. 395, Fig. 4 p. 393).
- CLC Thm 12 p. 20: `P₁ ∼o P₂ ⇒ [[P₁]] ≈ [[P₂]]`, where `≈` is negligible advantage for PPT
  attackers (Defs 2, 4 pp. 6–7). It assumes simple processes with a key hierarchy (Def 11 p. 19)
  and joint IND-CPA + INT-CTXT (Defs 8–9 p. 15), and needs tags (§5.1 p. 19), observable lengths
  (§3.2 p. 10) and honest keys (p. 15). Non-failing `else` is open (§8 p. 34).

## 3. The `StdUC` instantiation

### 3.1 Decisions

**Process model (b): DY machines, presented by syntax.** Morphisms are circuits of DY roles;
`Machine/Core` relations serve only as one semantics (§4.2). Four reasons:
1. *Attackers must be DY.* Tests compose with every morphism, because `ℰ` is a presheaf.
   Generating 𝒞 from DY roles makes every morphism DY, with no `W` and no closure proofs.
2. *Interpretation needs programs* that evaluate recipes (AR Fig. 1 p. 118; CLC §4.3 p. 14).
   Relations have neither recipes nor a `Dₚ` image (landscape §2).
3. *Freshness is global.* With locally chosen names an environment may pick the protocol's key,
   and possibilistically that run counts. Names located at occurrences give `(Red Res)`.
4. *Token passing*, as in all targets and in CH, BPW and CLC. A racy `|` would turn functoriality
   into a scheduling theorem.

Option (a) brings α-equivalence, `≡`, extrusion and races. Option (c), `Examples/RelSetup.agda`,
is one-shot and ×-tensored: it hosts passive static equivalence (`otp-perfect`) and is joined to
`Sym` only laxly (landscape §§3, 5).

**Not a restriction of machine-iso**, contra `Abstract2/WideSubcategory.agda:3-6`, for three
reasons. `SetupSubcategory` is wide, and DY-definability means nothing on channels without terms.
`Restriction.ν` must be a setoid map into `ι*ℰ`, whose `_≅ᴹ_` is finer than symbolic test
equality. And relations have no programs. So `Sym` is a free setup plus `changeKernel`.

**Observation runs in 𝔾ᵒ at term alphabets.** 𝔾ᵒ provides initial states (`θ-point` sits inside
`_≈ᴹ_`, `Machines/Sim.agda:42-44`), answers on every activation (CLC fails with `cout(⊥)`, not
silence), is `--without-K`, and lets the soundness proof compare two runs of a single model.
Roles are deterministic. Nondeterminism enters only as `∀` over attacker roles (deterministic
strategies realize every trace) and `∃` over fresh names.

### 3.2 Signature, terms, equational theory, deducibility

Built: `Symbolic/Term.agda`, `Symbolic/Term/PairEnc.agda`, `Symbolic/Deduction.agda`, all
`--safe --without-K`, each about 4 s warm; `Symbolic/Test.agda` exercises them. Freshness uses
located names, as §5 risk 1 recommends: the occurrence bijections cost 24 cases in `Decorated`
(§3.5).

```agda
-- CategoricalCrypto.Symbolic.Term
record Signature : Set₁ where
  field Sort Sym : Set ; dom : Sym → List Sort ; cod : Sym → Sort
        _≟ˢ_ : DecidableEquality Sort ; _≟ᶠ_ : DecidableEquality Sym
Name = ℕ × ℕ                                    -- (occurrence code, counter); §3.5
_≟ₙ_ : DecidableEquality Name
module Terms (𝔖 : Signature) where              -- downstream: `open Terms 𝔖`
  data Tm : Sort → Set where
    name : Name → Tm s
    app  : (f : Sym) → All Tm (dom f) → Tm (cod f)
  Frame = All Tm                                 -- every name of a frame is restricted
  ren : (Name → Name) → Tm s → Tm s ; names : Tm s → List Name   -- and ren*, names* on tuples
  data Each (P : ∀ {s} → Tm s → Set) : All Tm ss → Set            -- lookupᴱ, mapᴱ
  data All₂ (R : ∀ {s} → Tm s → Tm s → Set) : All Tm ss → All Tm ss → Set
  _≟ᵗ_ : DecidableEquality (Tm s)               -- decided in Σ Sort Tm, read back by UIP
  data Recipe (Δ : List Sort) (own : Name → Set) : Sort → Set where
    var  : s ∈ Δ → Recipe Δ own s
    mine : (n : Name) → own n → Recipe Δ own s
    app  : (f : Sym) → All (Recipe Δ own) (dom f) → Recipe Δ own (cod f)
  _⟨_⟩ : Recipe Δ own s → Frame Δ → Tm s       -- and _⟨_⟩* on tuples
  bind : (∀ {s} → s ∈ Δ → Recipe Δ′ own′ s) → own ⊆ own′ → Recipe Δ own s → Recipe Δ′ own′ s
  Ground : Recipe Δ own s → Set                 -- no `var`
record EqTheory (𝔖 : Signature) : Set₁ where   -- abadi2018applied §2.2 p. 6
  field _≈E_       : ∀ {s} → Tm s → Tm s → Set
        isEquiv    : ∀ {s} → IsEquivalence (_≈E_ {s})
        app-cong   : ∀ f {ts us} → All₂ _≈E_ ts us → app f ts ≈E app f us
        ren-cong   : ∀ ρ {s} {t u : Tm s} → t ≈E u → ren ρ t ≈E ren ρ u
        _≟E_       : ∀ {s} → Decidable (_≈E_ {s})  -- guards are computed (§3.5)
        nontrivial : ∀ s → ∃₂ λ (t u : Tm s) → ¬ t ≈E u
        canon      : ∀ {s} → Tm s → Tm s           -- what roles emit and store (§3.3)
        canon-≈E   : ∀ {s} (t : Tm s) → canon t ≈E t
        ≈E⇒canon   : ∀ {s} {t u : Tm s} → t ≈E u → canon t ≡ canon u
  module ≈E {s} = IsEquivalence (isEquiv {s}) ; Tm-setoid : Sort → Setoid 0ℓ 0ℓ

-- CategoricalCrypto.Symbolic.Term.PairEnc: CLC Examples 3.1 and 3.3 (pp. 9–10)
data Op : Set where pair fst snd enc dec : Op ; cst : ℕ → Op   -- enc: plaintext, key, coins
Σ₀ : Signature                                  -- one sort, ⊤; Msg = Tm tt
data _⟶ʳ_ : Msg → Msg → Set where              -- E₀ oriented
  π₁⟨,⟩ : π₁ ⟪ x , y ⟫ ⟶ʳ x ; π₂⟨,⟩ : π₂ ⟪ x , y ⟫ ⟶ʳ y ; dec-enc : dec⟨ enc⟨ x , k , r ⟩ , k ⟩ ⟶ʳ x
data _⟶_ : Msg → Msg → Set                     -- root, arg: one step anywhere
nf : Msg → Msg ; app↓ : (f : Op) → All Tm (arity f) → Msg       -- nf (app f ts) = app↓ f (nf* ts)
nf-normal : (t : Msg) → Normal (nf t) ; nf-reduces : (t : Msg) → t ⟶* nf t
⟶-nf : t ⟶ u → nf t ≡ nf u ; terminating : WellFounded (flip _⟶_)
confluent : t ⟶* u → t ⟶* v → ∃[ w ] u ⟶* w × v ⟶* w
E₀ : EqTheory Σ₀                                -- t ≈E u = nf t ≡ nf u; canon = nf
≈E⇔⟷* : nf t ≡ nf u ⇔ EqClosure _⟶_ t u         -- the theory the three rules generate

-- CategoricalCrypto.Symbolic.Deduction (𝔖 : Signature) (E : EqTheory 𝔖)
Knowledge Δ = Frame Δ × (Name → Set)            -- exposed frame, names the deducer may use
_⊢_ : Knowledge Δ → Tm s → Set                  -- abadicortier2006 Prop 1, as definition
K ⊢ M = Σ[ ζ ∈ Recipe _ (proj₂ K) _ ] ζ ⟨ proj₁ K ⟩ ≈E M
data _⊢ᵢ_ (K : Knowledge Δ) : Tm s → Set where  -- the rules of §2.3 p. 6
  entry : (i : s ∈ Δ) → K ⊢ᵢ lookup (proj₁ K) i ; owned : proj₂ K n → K ⊢ᵢ name n
  apply : Each (K ⊢ᵢ_) ts → K ⊢ᵢ app f ts       ; conv  : K ⊢ᵢ M → M ≈E M′ → K ⊢ᵢ M′
⊢⇔⊢ᵢ : K ⊢ M ⇔ K ⊢ᵢ M
⊢-cut : Each (K ⊢_) φ → own ⊆ proj₂ K → (φ , own) ⊢ M → K ⊢ M   -- with ⊢-conv, ⊢-entry,
⊢-wk  : (φ , own) ⊢ M → (t ∷ φ , own) ⊢ M                      --   ⊢-owned, ⊢-own, bind-⟨⟩
Foreign φ ψ n = n ∉ names* φ × n ∉ names* ψ
_≈ₛ_ : Frame Δ → Frame Δ → Set                 -- Def 2 p. 7; abadi2018applied Def 4.3
φ ≈ₛ ψ = ∀ {s} (ζ ζ′ : Recipe _ (Foreign φ ψ) s) → (ζ ⟨ φ ⟩ ≈E ζ′ ⟨ φ ⟩) ⇔ (ζ ⟨ ψ ⟩ ≈E ζ′ ⟨ ψ ⟩)
```

Departures from the first draft, all forced:
- `Signature` gains `_≟ᶠ_`: syntactic term equality, hence a decidable E, needs it. The sort
  decision is `_≟ˢ_`, since `_≟_` clashes on opening.
- `app f ts ≡ app f us` cannot be split without K, because the index `cod f` is not a pattern.
  `_≟ᵗ_` therefore decides equality in `Σ Sort Tm` and reads it back with `Decidable⇒UIP`. Σ₀
  has the single sort `⊤`, so `cod f` reduces and its rules can match terms with known heads.
- The term layer is a named module `Terms 𝔖`; an anonymous one cannot be opened at 𝔖.
- Recipes, `bind` and `Ground` live in `Term`, not `Deduction`, because roles need them without
  E. A role recipe is `Recipe Δ ∅`.
- `Sym` clashes with `Relation.Binary.Definitions.Sym`, and `_⊢_`, `_∈_` clash with
  `Relation.Unary`; import those with `using`.
- `EqTheory` gains canonical forms (step 8). Roles emit and store `canon` of what they compute, so
  programs equal modulo E have *equal* steps and `emit-≈E` (§3.6) is a functional simulation.
  With raw wire terms it needs a simulation along a message relation through 𝔾ᵒ's trace, which
  the machine layer lacks (`Machines.Sim._≲_` takes a function; `Dp.Iter.Transfer` a pure map).
  The price is a convergent theory, the class §2 names; E₀'s canonical forms are its normal forms.

### 3.3 Dolev–Yao roles: the generators

Built: `Symbolic/Role.agda` (6 s warm). Atoms are ports. `port s t` carries sort `s` on `Pos`
and sort `t` on `Neg` (`Iface.agda:3-5`). `verdict` is `Ωᴵ = Bool ⇿ ⊤`, and `void` is the empty
interface. On each activation a role runs a decision tree: guards, fresh names, then one emission
and a jump.

```agda
-- CategoricalCrypto.Symbolic.Role (𝔖 : Signature)
data Atom : Set where port : (pos neg : Sort) → Atom ; verdict void : Atom
_≟ᴬ_ : DecidableEquality Atom
open FreeMonoidalHelper Mon Atom                       -- ObjTerm
data Dir : Set where pos neg : Dir                     -- rightwards, leftwards
data Kind : Set where msg : Sort → Kind ; flag tick : Kind
Value : Kind → Set                                     -- Tm s, Bool, ⊤
kinds : Dir → Atom → List Kind ; Kinds : Dir → ObjTerm → List Kind        -- `++` at ⊗₀
alphabet : Dir → Atom → Set ; Alphabet : Dir → ObjTerm → Set              -- `⊎` at ⊗₀, ⊥ at unit
read  : ∀ d x → Alphabet d x → Σ[ k ∈ Kind ] k ∈ Kinds d x × Value k
write : ∀ d x {k} → k ∈ Kinds d x → Value k → Alphabet d x
Ins Outs : ObjTerm → ObjTerm → List Kind               -- Ins x y = Kinds pos x ++ Kinds neg y
data Input (x y : ObjTerm) : Set where _↦_ : k ∈ Ins x y → Value k → Input x y
data Emission (O : List Kind) : Set where _↦_ : k ∈ O → Value k → Emission O
decode : ∀ x y → Alphabet pos x ⊎ Alphabet neg y → Input x y
encode : ∀ x y → Emission (Outs x y) → Alphabet neg x ⊎ Alphabet pos y
Branch : Kind → Set                                    -- Bool on `flag`, ⊤ otherwise
carried : Kind → List Sort ; branch : Value k → Branch k ; carry : Value k → Frame (carried k)
Rcp Δ = Recipe Δ ∅                                     -- a role holds no name it did not draw
Payload : List Sort → Kind → Set                       -- Rcp Δ s, Bool, ⊤
data React (n : ℕ) (Γ : Fin n → List Sort) (O : List Kind) : List Sort → Set where
  test : Rcp Δ s → Rcp Δ s → React n Γ O Δ → React n Γ O Δ → React n Γ O Δ
  new  : ∀ s → React n Γ O (s ∷ Δ) → React n Γ O Δ
  emit : (c : Fin n) → All (Rcp Δ) (Γ c) → k ∈ O → Payload Δ k → React n Γ O Δ
record Role (x y : ObjTerm) : Set where
  field n : ℕ ; Γ : Fin n → List Sort ; start : Fin n ; fresh : Γ start ≡ []
        react : (c : Fin n) {k : Kind} → k ∈ Ins x y → Branch k
              → React n Γ (Outs x y) (carried k ++ Γ c)
Reactions : Role x y → Set                     -- `react`'s type at p's shape
data Halts (h : Fin n) : React n Γ O Δ → Set   -- `emit h _ _ π` with a ground payload
data Guarded (h : Fin n) : React n Γ O Δ → Set -- every failed `test` halts at h
record Simple (p : Role x y) : Set where       -- CLC §3.3 basic processes
  field halt : Fin (Role.n p)
        halted  : ∀ {k} (i : k ∈ Ins x y) b → Halts halt (Role.react p halt i b)
        guarded : ∀ c {k} (i : k ∈ Ins x y) b → Guarded halt (Role.react p c i b)
record Config (n : ℕ) (Γ : Fin n → List Sort) : Set where
  constructor config ; field control : Fin n ; registers : Frame (Γ control) ; counter : ℕ
init : (p : Role x y) → Config (Role.n p) (Role.Γ p)
received : (hist : List (Input x y)) → Frame (Received hist)   -- newest first
Own : ℕ → Name → Set ; Own κ (κ′ , _) = κ′ ≡ κ
module Run (E : EqTheory 𝔖) where
  canonᵛ : Value k → Value k ; canon* : Frame Δ → Frame Δ           -- `canon` on terms
  exec : (κ : ℕ) → React n Γ O Δ → Frame Δ → ℕ → Config n Γ × Emission O   -- names (κ , j)
  exec κ (emit c ρs o π) φ j = config c (canon* (ρs ⟨ φ ⟩*)) j , o ↦ canonᵛ (payload _ π φ)
  step : (κ : ℕ) (p : Role x y) → Config (Role.n p) (Role.Γ p) → Input x y
       → Config (Role.n p) (Role.Γ p) × Emission (Outs x y)
  Known : Knowledge Δ → Emission O → Set               -- an emitted term is deducible
  exec⊢ : Own κ ⊆ proj₂ K → (t : React n Γ O Δ) → Each (K ⊢_) φ → Deduced K (exec κ t φ j)
  after : (κ : ℕ) (p : Role x y) → List (Input x y) → Config (Role.n p) (Role.Γ p)
  emits⊢ : ∀ κ p (hist : List (Input x y)) (inp : Input x y)
         → Known (received (inp ∷ hist) , Own κ) (proj₂ (step κ p (after κ p hist) inp))
  _≈ᵛ_ : Value k → Value k → Set                       -- _≈E_ on terms, _≡_ otherwise
  data ReactE : React n Γ O Δ → React n Γ O Δ → Set    -- one shape, recipes ≈E at every frame
  exec-≈E : ReactE t t′ → ∀ φ j → exec κ t φ j ≡ exec κ t′ φ j
  step-≈E : (∀ c {k} (i : k ∈ Ins x y) b → ReactE (Role.react p c i b) (r c i b))
          → ∀ cfg inp → step κ p cfg inp ≡ step κ (record p { react = r }) cfg inp
```

A role's frame grows at the front: a received term and a `new` name are pushed. `emits⊢` says
roles are DY deducers: what occurrence κ emits is deducible from every term it has received,
its trigger included, together with its own names `(κ , _)`. The recipe is the emitting branch's
`Rcp`, with each `new` turned into `mine` (`exec⊢`, `⊢-cut`). Ports are kinds listed in tensor
order. A role branches on a received bit, so a verdict in its domain can be read, and it pushes
a received term on its frame. `Simple` keeps CLC's shape: a failed guard emits a ground payload
(CLC's `⊥`) and jumps to a halting point that answers every activation that way. CLC's
well-formedness guard `M` is not an equation, so it needs check symbols in the signature
(step 13). Everything is first-order data in `Set`, as `FreeMonoidalData.mor` requires. Unbounded
sessions are a single role that dispatches on session tags. This is `bohlunruh2013`'s `!!`
(Def 5.11 p. 42), the only replication their composition theorem covers. An emission and the
stored registers are canonical (§3.2): `emits⊢` still holds through `⊢-conv`, and `exec-≈E`
follows by `≈E⇒canon`, guards agreeing because both sides of a `test` are E-equal.

`Symbolic/Test.agda` checks that `⟦_⟧ᴵ` (§3.5) is the `_⊗ᴵ_`-tree on the nose, with `unitᴵ` at
`unit` and `Bool ⇿ ⊤` (`Ωᴵ`) at `verdict`; it runs `step` on a concrete role and checks
`emit-≈E` at Σ₀ (a role answering `π₁ ⟪ x , x ⟫` against one answering `x`).

### 3.4 The category and its hom-setoid

Built: `Symbolic/Fine.agda` (80 lines, 10 s warm).

```agda
{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Symbolic.Fine (𝔖 : Signature) where
UnitFree : ObjTerm → Set                           -- no `unit` leaf; ⊤ at `Var`, × at ⊗₀
symData : FreeMonoidalData {0ℓ}
symData = record { v = Mon ; X = Atom ; mor = λ x y → UnitFree x × UnitFree y × Role x y }
open FreeMonoidal symData public                   -- ObjTerm, HomTerm, _≈Term_, FMC
𝔻𝕐 : MonoidalCategory 0ℓ 0ℓ 0ℓ
𝔻𝕐 = FMC
Test : ObjTerm → Set
Test A = Σ[ Y ∈ ObjTerm ] HomTerm (Y ⊗₀ A) (Var verdict)   -- ancilla on the grade side
pullᵗ : HomTerm B A → Test A → Test B               -- (Y , T) ↦ (Y , T ∘ id ⊗₁ f)
data SameTerm {A} : Test A → Test A → Set where
  same : T ≈Term T′ → SameTerm (Y , T) (Y , T′)
ℰᵗ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids 0ℓ 0ℓ)   -- F₁ = pullᵗ
ℰ≅ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰ≅ = LiftSetoids (suc 0ℓ) (suc 0ℓ) ∘F ℰᵗ
module Sym≅ = StdUC 𝔻𝕐 ℰ≅                          -- `Sym≅.UC-compose` instantiated
```

Departures: `Fine` takes no E, since roles do not depend on it; `Test`, `pullᵗ` and `UnitFree` live
here, shared by `Sym≅` and `Sym`; `homˢ` was dropped (nothing uses it); `Sym≅` is a module, not an
`open … public`, because `StdUC`'s category names clash with the term syntax.

Hom-equality is `_≈Term_` (`FreeMonoidal.agda:140-164`): coherence only, and finer than `_≅ᴹ_` on
purpose. It has two jobs: `F-resp-≈` for every outgoing functor, which comes free
(`⟦⟧-resp-≈`, lines 466-490), and `≈C⇒≈ℰ`. E-equality, name renaming and bookkeeping are kernel
facts, and `≈ℰ = ≈ᵁ` (§3.6). The alternatives gain nothing:
- Bisimulation up to E proves no new UC statement and needs a congruence proof.
- The kernel quotient would turn soundness into `F-resp-≈` and block §4.2.
- `Factorization` never changes a hom-equality.

`Mon` is enough: the UC structure uses only α, and `Famᴹ` is a plain `MonoidalCategory`
(`LocallyGraded/Family.agda:115`).

### 3.5 Observation with located names

```agda
-- Categories.FreeMonoidal.Decorated (built; 151 lines, 4 s warm)
module Categories.FreeMonoidal.Decorated
  {ℓ′ o ℓ e d} (dat : FreeMonoidalData {ℓ′}) (⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e}) (⟦_⟧ᵖ₀ : X → C.Obj)
  (D : Set d) (⟦_⟧ᵈ : ∀ {x y} → mor x y → D → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀) where
Occ : HomTerm A B → Set
Occ (var _) = ⊤ ; Occ (g ∘ f) = Occ g ⊎ Occ f ; Occ (f ⊗₁ g) = Occ f ⊎ Occ g ; Occ _ = ⊥
⟦_⟧[_] : (f : HomTerm A B) → (Occ f → D) → ⟦ A ⟧₀ C.⇒ ⟦ B ⟧₀
⟦ var p ⟧[ ι ]  = ⟦ p ⟧ᵈ (ι tt)
⟦ g ∘ f ⟧[ ι ]  = ⟦ g ⟧[ ι ∘′ inj₁ ] C.∘ ⟦ f ⟧[ ι ∘′ inj₂ ]
⟦ f ⊗₁ g ⟧[ ι ] = ⟦ f ⟧[ ι ∘′ inj₁ ] C.⊗₁ ⟦ g ⟧[ ι ∘′ inj₂ ]   -- structural: as FreeFunctor
⟦⟧[]-cong : (f : HomTerm A B) → (∀ x → ι x ≡ ι′ x) → ⟦ f ⟧[ ι ] ≡ ⟦ f ⟧[ ι′ ]
⟦⟧[]-resp-≈ : f ≈Term g → Σ[ π ∈ Occ f ↔ Occ g ] (∀ ι → ⟦ f ⟧[ ι ∘′ Inverse.to π ] C.≈ ⟦ g ⟧[ ι ])

-- CategoricalCrypto.Symbolic.Semantics (built; 205 lines, 12 s warm)
{-# OPTIONS --safe --without-K --guardedness #-}
module CategoricalCrypto.Symbolic.Semantics (𝔖 : Signature) (E : EqTheory 𝔖) where
atomᴵ : Atom → Iface ; atomᴵ a = alphabet pos a ⇿ alphabet neg a   -- Tm s ⇿ Tm t ; Ωᴵ ; unitᴵ
⟦_⟧ᴵ  : ObjTerm → Iface ; ⟦ x ⟧ᴵ = Alphabet pos x ⇿ Alphabet neg x  -- the _⊗ᴵ_-tree of atomᴵ
⟦v⟧ᵒ = fromMC 𝔾ᵒ noSymmetric ; open FreeObjInterp Mon Atom ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ)
tree≡ : (x : ObjTerm) → UnitFree x → ⟦ x ⟧₀ ≡ ifaceᵒ ⟦ x ⟧ᴵ        -- ⊗ᵒ at ⊗₀, refl at Var
treeᵒ : UnitFree x → UnitFree y → ifaceᵒ ⟦ x ⟧ᴵ G.⇒ ifaceᵒ ⟦ y ⟧ᴵ → ⟦ x ⟧₀ G.⇒ ⟦ y ⟧₀
treeᵒ-resp : f G.≈ g → treeᵒ ux uy f G.≈ treeᵒ ux uy g
runᴿ : ℕ → Role x y → Proc ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ
runᴿ κ p = MC.mk (initˢ (Config (Role.n p) (Role.Γ p)) (init p))
  λ (cfg , m) → returnₚ (map₂ (encode x y) (step κ p cfg (decode x y m)))
runᴿ-≈E : (∀ c {k} (i : k ∈ Ins x y) b → ReactE (Role.react p c i b) (r c i b))
        → procᵒ (runᴿ κ p) G.≈ procᵒ (runᴿ κ (record p { react = r }))   -- θ = id, ≈ᴹ⇒≈ᵒ
leafᵒ : UnitFree x × UnitFree y × Role x y → ℕ → ⟦ x ⟧₀ G.⇒ ⟦ y ⟧₀
leafᵒ (ux , uy , p) κ = treeᵒ ux uy (procᵒ (runᴿ κ p))
open Decorated symData ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ) ℕ leafᵒ public
record eval (c : HomTerm (Var void) (Var verdict)) (b : Bool) : Set where   -- possible verdict
  constructor named
  field naming : Occ c → ℕ ; fresh : Injective _≡_ _≡_ naming ; answer : Obs ⟦ c ⟧[ naming ] ≈ₚ returnₚ b
eval-cong : c ≈Term c′ → ∀ b → eval c b ⇔ eval c′ b       -- ⟦⟧[]-resp-≈, ⟦⟧[]-cong, obs-resp
```

`treeᵒ` coerces along `⊗ᵒ` (`Seal.agda:87-88`); at a single atom it is `refl`, so a role on atoms
is its `procᵒ` on the nose. Generator boundaries are unit-free because `G.unit ≠ ifaceᵒ unitᴵ`
(`Observation.agda:15-22`). Each occurrence gets its own name supply,
attackers included, so an attacker holds a protocol name only once it has been sent one. The
`∃ι` absorbs re-bracketing, so no equivariance lemma is needed here. A naming `ι′` of `c′` gives
`c` the naming `ι′ ∘ to π` directly. A naming `ι` of `c` gives `c′` the naming `ι ∘ from π`, and
`⟦⟧[]-cong` closes the gap, because `from ∘ to` is the identity only pointwise. Equivariance
(`ren-cong`, guards modulo E) makes the verdict independent of `ι`; only the soundness proof
uses it.

Departures: `eval` is a record, not a `Σ`. As a definition it unfolds into `_≈ₚ_`'s rationals
whenever unification meets a meta, and `Setup`'s presheaf then exhausted a 3 GiB heap; as a record
type, unification compares circuits. The two-role example is private to the module: a tester draws
a name, sends it to an echo and answers `true` on the reply, under the naming `[ 0 , 1 ]`. Its run
crosses the seal with `unprocᵒ-∘`, then `UC.Seam.Plug` (`collapse`, `observe`, two `loop-pass`es).
The loop passes are given their states and messages, because unification cannot invert `kᴳ`.

### 3.6 The DY-environment presheaf and the setup

Built: `Symbolic/Setup.agda` (163 lines, 14 s warm).

```agda
{-# OPTIONS --safe --without-K --guardedness #-}
module CategoricalCrypto.Symbolic.Setup (𝔖 : Signature) (E : EqTheory 𝔖) where
Closure A = HomTerm (Var void) A
Agree T T′ = ∀ (m : Closure (Y ⊗₀ A)) b → eval (T ∘ m) b ⇔ eval (T′ ∘ m) b
data SameObs {A} : Test A → Test A → Set where
  same : Agree T T′ → SameObs (Y , T) (Y , T′)
same⁻¹ : SameObs (Y , T) (Y , T′) → Agree T T′          -- Decidable⇒UIP (≟ObjTerm _≟ᴬ_)
term⇒obs : SameTerm t t′ → SameObs t t′                  -- eval-cong
ℰᵒᵇˢ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids 0ℓ 0ℓ)  -- F₁ = pullᵗ; laws: ℰᵗ's, by term⇒obs
ℰˢʸᵐ = LiftSetoids (suc 0ℓ) (suc 0ℓ) ∘F ℰᵒᵇˢ
module Sym = StdUC 𝔻𝕐 ℰˢʸᵐ
regroup : ((T ∘ α⇒) ∘ id ⊗₁ h) ∘ (α⇐ ∘ m) ≈Term (T ∘ id ⊗₁ (id ⊗₁ h)) ∘ m
grade-stable : Sym.GradeStable      -- (Y , T) on Z ⊗₀ C is (Y ⊗₀ Z , T ∘ α⇒) on C
≈ᵁ⇔≈ℰ : f Sym.≈ᵁ g ⇔ f Sym.≈ℰ g    -- ≈ᵁ⇒≈ℰ, bridge grade-stable
leaf-≈ℰ : (∀ κ → leafᵒ p κ G.≈ leafᵒ q κ) → var p Sym.≈ℰ var q
emit-≈E : (p : Role x y) {r : Reactions p}            -- E lives in the kernel
        → (∀ c {k} (i : k ∈ Ins x y) b → ReactE (Role.react p c i b) (r c i b))
        → var (ux , uy , p) Sym.≈ℰ var (ux , uy , record p { react = r })
```

Departures: `Sym` is a module like `Sym≅` (§3.4), not `open StdUC … public`. `emit-≈E` compares a
role with another reaction table of its shape: `ReactE (react p c i) (react q c i)` needs one set
of control points. It is `leaf-≈ℰ` at `runᴿ-≈E`, so it rests on canonical emissions (§3.2).
`leaf-≈ℰ` holds because occurrences are counted by shape, so one naming serves both circuits.

The kernel `f ≈ℰ g` holds iff every DY environment and closure sharing an ancilla allows the
same verdicts; it is trace (may-testing) equivalence against DY contexts. Diff-equivalence
implies `∼o`, which implies this kernel, so ProVerif proofs certify it `[INFERENCE: needs a
translation of roles into applied-π]`. On frame emitters the kernel is static equivalence
(`abadi2018applied` Lemma 4.2 p. 15); this is step 9, blocked (§6). `≤UC` is `bohlunruh2013`
Def 4.3, and `≤UCᵈ⇔≤UC` is their Lemma 4.4, here without hypotheses. The reflexivity concern of
`delaune2009simulation` (p. 175) does not arise: `≤UC-refl` takes `s = a`.

**Levels, options, layout.** 𝔻𝕐 lives at `0ℓ`. Tests are lifted to `cs = ℓs = suc 0ℓ`, which
matches machine-iso, ℰᵒ, ℰᴿ and `ucSetupᴺ` (`Enrichment.agda:46`). So
`Sym : UCSetup 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ (suc 0ℓ) (suc 0ℓ)`. Everything is `--safe --without-K`, with
two exceptions: `--guardedness` from `Semantics` on, and K in `Symbolic/Machine.agda`. The modules
under `Symbolic/` are `Term`, `Term/PairEnc`, `Deduction`, `Role`, `Test`, `Fine`, `Semantics`,
`Setup`, `Static`, `Machine`, `Computational`, `Soundness` and `Example/SecureChannel`. General additions:
`freeStrongMonoidal`, `Categories/FreeMonoidal/Decorated.agda`, and `transfer⁺` in
`Abstract2/Morphism.agda`.

## 4. Morphisms

`Sym≅ = StdUC 𝔻𝕐 ℰ≅` (built, §3.4) has the same tests, compared by `SameTerm (Y , T) (Y , T′) =
T ≈Term T′`. It shares 𝒞, ℐ and ℳ with `Sym`. Every morphism starts from it, so each `ν`'s `cong` is
`⟦⟧-resp-≈`.

### 4.1 `Sym≅ → Sym`

Built, in `Symbolic/Setup.agda`:

```agda
coarse : PresheafMorphism idF ℰ≅ ℰˢʸᵐ
coarse = record { ν = ntHelper record
  { η = λ _ → record { to = λ t → t ; cong = λ { (lift s) → lift (term⇒obs s) } }
  ; commute = λ _ → Setoid.refl (Functor.₀ ℰˢʸᵐ _) } }
coarse-epi : PresheafMorphism.Epi coarse
fine→sym : UCSetupMorphism Sym≅.StdSetup Sym.StdSetup
fine→sym = changeKernel ℰ≅ ℰˢʸᵐ coarse
```

`coarse` is Epi (`coarse-epi`). So `epi⇒preserves` and `Transfer.transfer` (with `grade-stable`)
carry every `Sym≅` emulation to `Sym`.

### 4.2 `Sym≅ → machine-iso`; nothing from `Sym`

```agda
{-# OPTIONS --safe #-}
module CategoricalCrypto.Symbolic.Machine (𝔖 : Signature) (E : EqTheory 𝔖) where
relational : FreeFunctorData symData
relational = record
  { ⟦v⟧   = fromMC machines noSymmetric                 -- Machine.UC.machines (reversed)
  ; ⟦_⟧ᵖ₀ = λ { (port s t) → Tm s ⇿ Tm t ; verdict → Bool ⇿ ⊤ ; void → I }
  ; ⟦_⟧ᵖ₁ = roleMachine }            -- guards as ≈E; `new` picks any name; always `just`
Fᴿ : StrongMonoidalFunctor 𝔻𝕐 machines
Fᴿ = freeStrongMonoidal relational                      -- Φ = Fᴿ, κ = Oplax.δ = id
νᴿ : PresheafMorphism (StrongMonoidalFunctor.F Fᴿ) ℰ≅ ℰ-tests
νᴿ = record { ν = ntHelper record
  { η = λ A → record { to   = λ (Y , E) → ⟦ Y ⟧₀ , untick CC.∘ ⟦ E ⟧₁   -- untick : Bool ⇿ ⊤ ⇒ ℰ-Out
                     ; cong = λ { (lift (same e)) → same (refl⟩∘⟨ ⟦⟧-resp-≈ e) } }
  ; commute = λ f → same ∘-assoc-≅ᴹ } }
sym≅→iso : UCSetupMorphism Sym≅.StdSetup Machine.UC.StdSetup
sym≅→iso = StdUCMorphism 𝔻𝕐 machines ℰ≅ ℰ-tests Fᴿ νᴿ
```

Reversal makes the shapes agree: `⟦ Y ⊗₀ A ⟧₀ = ⟦ A ⟧₀ ⊗₀ ⟦ Y ⟧₀`, which is machine-iso's
`Machine (A ⊗₀ Y) ℰ-Out`. None of the obligations is cryptographic. `F-resp-≈` is free;
strong-monoidal coherence follows from `⊗₁-id` and `∘-identityˡ-≅ᴹ`; the κ laws come from
`StdUCMorphism`; naturality is `∘-assoc-≅ᴹ`. This is the "forget E, terms as sets" map, and E
survives only in guards. It transfers nothing: `νᴿ` is not Epi (most machine-iso tests are not
DY) and not Mono (different circuits can have isomorphic semantics).

`Sym → machine-iso` does not exist, for three reasons:
- `cong` would need observationally equal tests to be state-isomorphic;
- machine-iso's environments are arbitrary relations on raw terms, which see through encryption,
  so no coarser test equality respects `Sym`'s kernel;
- `⟦_⟧[_]` is not a functor.

The same three reasons exclude `Sym → 𝔾ᵒ` at term alphabets.

### 4.3 Computational soundness over `Sym≅ → ucSetupᴺ`

**Target.** `UC.Model.Family.ucSetupᴺ = StdUC Famᴹ ℰᴺ`, the negligible tier over 𝔾ᵒ. Random
systems 𝔾ᴿ has no asymptotic tier (`uc-setup-random-systems.md` §3.1). Exact (Δ = 0) soundness
into 𝔾ᴿ fails as soon as names appear: a `Dₚ` machine samples them from a finite space, so they
can be guessed with positive probability (CH p. 395; BPW §5.3 p. 19). RS identities still reach
this target through that plan's `≈ᴿ ⇒ 𝔾ᵒ.≈ᵁ`.

```agda
{-# OPTIONS --safe --without-K --guardedness #-}
module CategoricalCrypto.Symbolic.Computational (𝔖 : Signature) (E : EqTheory 𝔖) where
record Scheme : Set₁ where                    -- CoSP's computational implementation; AR Fig. 1
  field Bits  : Set
        impl  : (f : Sym) → ℕ → All (λ _ → Bits) (dom f) → Bits   -- coins are explicit names
        nonce : ℕ → Dₚ Bits                                       -- uniform on {0,1}^η
        _≟ᵇ_  : DecidableEquality Bits
        tag   : Sort → Bits → Bits                                -- CLC §5.1 p. 19
computational : Scheme → FreeFunctorData symData
computational sch = record
  { ⟦v⟧   = fromMC Famᴹ noSymmetric
  ; ⟦_⟧ᵖ₀ = λ { (port _ _) → ifaceᶠ (λ _ → Bits ⇿ Bits) ; verdict → Δ Ωᵒ ; void → Δ 𝟘ᵒ }
  ; ⟦_⟧ᵖ₁ = λ (_ , _ , p) → family (λ η → treeᵒ … (procᵒ (runᶜ sch η p))) (rate-one p) }
Fᶜ : Scheme → StrongMonoidalFunctor 𝔻𝕐 Famᴹ                  -- Φ = Fᶜ, κ = Oplax.δ = id
Fᶜ = freeStrongMonoidal ∘ computational
νᶜ : (sch : Scheme) → PresheafMorphism (StrongMonoidalFunctor.F (Fᶜ sch)) ℰ≅ ℰᴺ
νᶜ sch .η A = λ (Y , E) → ⟦ E ⟧₁ Famᴹ.∘ (deadᶠ Famᴹ.⊗₁ Famᴹ.id) Famᴹ.∘ Famᴹ.λ⇐  -- ancilla closed
fine→comp : Scheme → UCSetupMorphism Sym≅.StdSetup ucSetupᴺ
fine→comp sch = StdUCMorphism 𝔻𝕐 Famᴹ ℰ≅ ℰᴺ (Fᶜ sch) (νᶜ sch)      -- ℰᴺ = UCSetup.ℰ ucSetupᴺ
```

| obligation | discharged by | crypto |
|---|---|---|
| functor, `F-resp-≈`, strong monoidal | `freeFunctor`, `⟦⟧-resp-≈`, `freeStrongMonoidal` | none |
| `κ-return`, `κ-ext`, `κ-sub` | `StdUCMorphism` | none |
| generators land in `Famᴹ` | `rate-one`: each reaction emits one message | none |
| `νᶜ` cong (from `ℰ≅`), naturality | `⟦⟧-resp-≈`, `≈⇒≋`; `⊗-∘-dist`, `λ⇐` naturality | none |
| `νᶜ` cong from `ℰˢʸᵐ` (`Sym → ucSetupᴺ`) | soundness with arbitrary DY tests as honest systems | open: non-failing `else` (CLC §8 p. 34) |

**Where soundness lives.** Soundness is preservation of the kernel. `Mono` gives *reflection*
(`mono⇒reflects`, `Presheaf/Morphism.agda:81-83`), i.e. computational ⇒ symbolic; that is
completeness, the other half of CH Thm 1, and it fails in AR (p. 124). Preservation would follow
from `Epi` (`epi⇒preserves`, lines 73-79), but `νᶜ` is not Epi: few PPT distinguishers are images
of DY tests. `Factorization (fine→comp sch)` puts the content in the right place. The image
kernel is agreement under *interpreted* DY attackers. Passing from it to the target kernel,
across the Mono half `image-morphism`, is exactly CH Lemma 1: on interpreted protocols, every
feasible attacker behaves like an interpreted DY attacker. `sound⁺` proves the composite
directly, for simple honest systems and under side conditions:

```agda
module Soundness (sch : Scheme) (Feasible : ∀ {A B} → A Famᴹ.⇒ B → Set)   -- itm §5.6: open
                 (hyp : CSHyp sch Feasible) where
  open Transfer (fine→comp sch)
  _≈ᶠ_ : A Famᴹ.⇒ B → A Famᴹ.⇒ B → Set     -- agreement on Feasible tests/closures: no kernel
  sound⁺ : ∀ {A B} {f g : HomTerm A B} → SimpleC f → SimpleC g
         → f ≈ℰ g → ∀ Y′ → Famᴹ.id {Y′} Famᴹ.⊗₁ F.₁ f ≈ᶠ Famᴹ.id {Y′} Famᴹ.⊗₁ F.₁ g
record CSSignature : Set₁ where              -- CLC §3, made compositional
  field sig : Signature ; level : Sort → Maybe ℕ   -- enc at level ℓ+1 takes keys of level ≤ ℓ
        lenTest : … ; typed : … ; randOne : …      -- §3.2 p. 10; §5.1 p. 19; §3.3 p. 11
record CSHyp (sch : Scheme) (Feasible : …) : Set₁ where
  field correct  : Realizes sch E                  -- E-axioms on tagged honest values
        ind-cpa  : LR-CPA₀ sch ≈ᶠ LR-CPA₁ sch      -- joint IND-CPA = AR type 3 (CLC Def 8)
        int-ctxt : CTXT₀ sch ≈ᶠ CTXT₁ sch          -- CLC Def 9
```

| ingredient of `sound⁺` | hypothesis | source |
|---|---|---|
| E-equal honest terms evaluate equally | `correct` | AR §5.1; CLC §4.3 p. 14 |
| ciphertexts hide plaintexts | joint IND-CPA + INT-CTXT; IND-CCA2, EUF-CMA for public-key encryption and signatures | CLC Thm 12; BPW Defs 5.1–5.2, Thm 7.1 |
| no key cycles | key-level sorts (sufficient for CLC Def 11 `[INFERENCE]`) | CLC Def 11 p. 19; AR §3.1 |
| parsing, lengths | `tag`/`typed`; lengths observable in guards | CLC §5.1 p. 19, §3.2 p. 10; BPW §2.2 |
| honest systems | `SimpleC f`, `SimpleC g`: every occurrence `Simple` | CLC §3.3 pp. 10–12 |
| dishonest keys, PPT attackers | `Feasible` on tests and closures (registered keys, time bounds) | CLC p. 15, Defs 2, 4; itm §5.6 |
| nonce guessing | none (statistical, `≤ q·2^{-η}`) | CH p. 395; BPW §5.3 p. 19 |
| trace vs `∼o` | roles deterministic, hence determinate | lemma `det⇒∼o` (§6 step 13) |

**The hypotheses are neither a `WideSubcategory` nor data of `F`.** Feasible machines form no
category: no identity is a priori polynomial, and the double repeater breaks composition. This
obstruction is `uc-setup-itm.md` §5.6, after `hofheinz2013`; a feasible target is unowned and
open. A feasible-closure presheaf on `Famᴹ` is not functorial along infeasible maps. So
`Feasible` and the security artifacts are side conditions of the theorem, and `F` needs only the
algorithms. The source restrictions are pointwise (`SimpleC`) or live in the signature
(`CSSignature`), so `Sym`'s attackers keep full DY strength. Restricting `Sym` to simple roles
would weaken its tests and make soundness *harder*.

**From kernels to emulation.** `Transfer.transfer` needs `Epi` and a target `GradeStable`. Neither
holds here: ℰᵒ is not `GradeStable` (`uc-setup-random-systems.md` §5.3). A pointwise variant
takes exactly what `sound⁺` provides:

```agda
transfer⁺ : (f≤g : f S.≤UC g) (let s₀ = proj₁ (S.≤UC⇒dummy f≤g))   -- Abstract2/Morphism, Transfer
          → (∀ Y′ → S′.T₁ Y′ (F.₁ f) S′.≈ℰ S′.T₁ Y′ (F.₁ (S.sub s₀ S.𝒞.∘ g)))
          → G f S′.≤UC G g
-- transfer = transfer⁺ fed λ Y′ → gs′ Y′ (epi⇒preserves-≈ℰ epi …)
```

The proof is `transfer`'s, with `T₁ Y′ κ` post-composed (`T-homomorphism`, `≈ℰ-cong-post`), and
it already covers information-theoretic interpretations. The computational corollary is a
side-conditioned twin:
`sound-≤UC : SimpleC f → SimpleC g → SimpleC s₀ → f ≤UC g → ≤UCᶠ (G f) (G g)`.
The simulator is honest in the ideal world, so it must be simple too. How side-conditioned
emulations compose is open (`uc-setup-itm.md` §5.6). Inside `Sym`, `UC-compose` and
`dummy-complete` stay unconditional; only the final emulation crosses.

**Ideal interpretation, rejected.** Interpreting encryption by `Fcpke` or `TH_H` would make
soundness statistical and condition-free (CH p. 395). But the table would then be shared across
morphisms, so `F` would be neither local nor a functor. The sharing analysis is in §3.3 of the
2026-07-31 memo `docs/uc-symbolic-crypto.md` (main checkout, untracked).

### 4.4 Other planned setups

None to or from `uc-setup-random-systems.md` (§4.3), `uc-setup-itm.md` (§4.4 there),
`uc-setup-ssp.md`, `uc-setup-ipdl.md` (both probabilistic, so §4.3 applies), or
`Examples/RelSetup.agda` (lax crossing). None to or from `uc-setup-causal-boxes.md` (§4 there):
zero-time rounds with an interleaving ⊗ have no causal-box image. A timed symbolic model is out
of scope.

## 5. Hard parts and risks

1. **Freshness.** Located names cost an occurrence bijection per `≈Term` constructor, about 25
   cases. The alternative is nominal sets with equivariance on every morphism. §4.2
   over-approximates freshness and transfers nothing. *Settled: located names.* The bijections
   are 24 cases in `Categories/FreeMonoidal/Decorated.agda`, 4 s warm. Coherence-only cases are
   isos of empty types. The rest are `⊎-assoc`, `⊎-cong` and seven small sum isos.
2. **No quotients.** Terms stay raw: `Tm-setoid` appears only in guards and deducibility. Guards
   are computed, so E must be decidable, and roles emit and store canonical forms, so `emit-≈E`
   carries E (§3.2): a convergent theory (`abadicortier2006` Props 3–4). `Term/PairEnc.E₀`
   decides by normal forms, which are its canonical forms.
3. **K and the seal.** K appears only in `Symbolic/Machine.agda`, as coinfectivity forces;
   `SameObs` inverts through `Decidable⇒UIP`. Generators go through `procᵒ`/`treeᵒ`. Never
   `unfolding 𝔾ᵒ` beside `StdUC` (12 GiB, `Enrichment.agda:12-13`); `Sym`'s `StdUC` is over 𝔻𝕐.
   Types at `curriedTensor machines` cost 9–15 min (`Machine/MonoidalCategory.agda:95-98`), so
   state them over abstract bundles, as in `Machine.UC.Kleisli`.
4. **Definitional matches.** `F₀ (Var verdict)` must be `Δ Ωᵒ` on the nose
   (`UC/Family.agda:115`), or `νᶜ` needs a coercion. `deadᶠ` is built at `objᵒ G.unit`.
5. **Scope.** CLC covers symmetric encryption, pairing, simple processes and `∼o`. Our kernel is
   trace-style, so `det⇒∼o` is needed. Public-key primitives have only realization results (BPW,
   CH). The proof is research-grade (CLC §§5–6, Lemma 15 p. 22).
6. **Disagreements.**
   - Landscape: the symbolic setup is not "possibilistic next to machine-iso". It is
     deterministic up to names and has no morphism to machine-iso.
   - The comment at `WideSubcategory.agda:3-6` should point to §3.1.
   - "ν Mono ⇒ soundness": Mono gives completeness, not soundness (§4.3).
   - Memo §4.1 proposes `𝔽(Σ)/E`, a separate ℐ, and a deducibility kernel `≈s`. But E needs no
     quotient, ℐ = 𝒞 suffices, deducibility is not `≈s` (Props 3–4), and verdict tests already
     give `≈s` on frames.

## 6. Work breakdown

Each step lands in the named module and is accepted when green under the house gate with the
listed exports.

1. `Abstract2/Morphism.agda`: `transfer⁺`, with `transfer` re-derived and its type unchanged.
2. `Categories/FreeMonoidal.agda`: `freeStrongMonoidal`, reused by the ITM plan.
3. `Categories/FreeMonoidal/Decorated.agda`: `⟦⟧[]-resp-≈`, generic in `⟦v⟧`. **Built.**
4. `Symbolic/{Term,Deduction}.agda`: `⊢⇔⊢ᵢ`, plus a convergent pairing/encryption theory. **Built**,
   with the theory in `Symbolic/Term/PairEnc.agda` (§3.2).
5. `Symbolic/Role.agda`: `Role`, `Simple`, a decidable `Atom`, and `emits⊢`, which shows that roles
   are DY deducers. **Built** (§3.3); `Symbolic/Test.agda` runs a role.
6. `Symbolic/Fine.agda`: `Sym≅`, with `Sym≅.UC-compose` instantiated. **Built** (§3.4).
7. `Symbolic/Semantics.agda`: `eval-cong`, plus a two-role example that evaluates to `true`.
   **Built** (§3.5), with `runᴿ-≈E`.
8. `Symbolic/Setup.agda`: hypothesis-free `grade-stable`, `≈ᵁ⇔≈ℰ`, `emit-≈E`, `fine→sym`.
   **Built** (§3.6, §4.1), with `leaf-≈ℰ` and `coarse-epi`; `emit-≈E` needed canonical forms
   in `EqTheory` and `Role.Run` (§3.2), and `Symbolic/Test.agda` checks it at Σ₀.
9. `Symbolic/Static.agda`: `≈ℰ⇔≈ₛ` on frame emitters. **Blocked.** `⇒` is a distinguishing test
   and needs only work: a generic run of the test against the emitter, and a renaming of the
   recipes' foreign names onto the test's own. `⇐` is not functional: the two worlds store
   *different* terms, the same recipe applied to φ and to ψ, so no state map relates them. It needs
   circuits related along a message relation, or along the substitution of φ's entries for
   placeholders (with E closed under substitution, a law `EqTheory` lacks). In both cases
   `Machines.Trace` and the G-composition must preserve such simulations; the machine layer has
   only `Machines.Sim._≲_` along a state function and `Dp.Iter.Transfer` along a pure map.
10. `Symbolic/Example/SecureChannel.agda`: `smt≤ideal`, with simulator `enc(0_ℓ, k′, r)`
    (proved by `dummy-complete` and step 9). **Blocked** on step 9's `⇐`: the real and ideal
    worlds expose statically equivalent ciphertexts.
11. `Symbolic/Machine.agda`: `sym≅→iso`, with a warm check inside the budget.
12. `Symbolic/Computational.agda`: `fine→comp`.
13. `Symbolic/Soundness.agda`: `det⇒∼o`, `sound⁺`, `sound-≤UC`. Pairing and symmetric encryption
    first, with `Feasible` abstract and no postulates.
14. Docs: a pointer in the `WideSubcategory.agda` header, and `Sym` in landscape §5.

## 7. Sources

Used: `abadi2018applied`, `abadicortier2006`, `blanchet2016proverif`, `canettiherzog2006`,
`backes2007rsim`, and `hofheinz2013` (via the ITM plan). `lowe1996` and `paulson1998inductive`
are background only.

Newly archived with PDF, `.txt`, INDEX lines and the `refs.bib` block "Symbolic UC setup plan":
`dolevyao1983` (`web.archive.org` copy of the `www.cs.huji.ac.il` file), `abadirogaway2002`,
`backes2003library` (ePrint 2003/015, converted from PostScript), `comonlundhcortier2008` (author
report, revised December 2008), `delaune2009simulation`, and `bohlunruh2013` (ePrint 2013/062;
its `.txt` drops some glyphs). No download was blocked.
