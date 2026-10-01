# Quality review — protocol-rewrite R3A, examples (2026-10-01)

Scope: the 60 files of `scope-R3A.txt` (`Examples/**` plus `Examples/{Basic,Commitment,RelSetup,Signatures}`,
`CategoricalCrypto/RandomOracle{,2}`), base `27cda67f`. Cut short by the maintainer's 15:57 deadline:
see **Not reached**.

Verification: soundness grep over `src` 16 before, 16 after (0 in scope). Each `using-drop` site was
checked by the toolkit oracle on its own file. The comment commit is comment-only, checked
mechanically (the code is identical once comments and whitespace are stripped). Final checks at the
tip: the 7 non-root leaves plus the root, results in the table at the end. Sweep tally
(`QUALITY-REVIEW-R3A.d/`):

| class | candidates | kept | notes |
|---|---|---|---|
| using-drop | 112 | 15 | 20 skipped (public / `using ()` renaming) |
| enum-comments | 406 blocks | 53 cut, 38 reworded, 315 kept | per-block dispositions: `comments-1.json`, `comments-2.json` |
| enum-with | 93 sites | — | enumerated only, not dispositioned (Not reached) |
| enum-where | 192 sites (150 single-use flags) | — | enumerated only, not dispositioned (Not reached) |
| implicit-drop, binder-drop, join-lines | — | — | not run (Not reached) |

## Committed

- `f200ab1e` Sweep using-drop over Examples (+14/−15). Toolkit class; each site kept only if its file stayed green.
- `daefd005` Comments: per-block trim and accuracy fixes over the scope (+122/−262).
  - Comment-only, every block dispositioned.
  - Stale pointers fixed: `UC.Seam.Grounded.SubBlind`, `QBᵢ`, the "`defer-commit` below" pointer, `lookup-bs` "branches on a `with`".
  - The false "`b₂ = false` gives the same term" in `Receiver/Machine`.
  - Stale plan/provenance tags in `RandomOracle{,2}`.
  - Restated-statement glosses in `RelSetup`.
  - Per-module banners.

## Suggestions (need your call), ranked by LOC / notions removed

1. `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda :: UniqueKeys, Rooted, HasVal` — dead invariant, **−73 (A) / −107 (B)**.
   - The three predicates are threaded through `MDInv`/`MDInv₀`, `CBnd`/`Bnd`, `callC-supp`, `walk-supp(L)` and the uk/rt tuple slots, but no proof reads them.
     - `walk-hit-collC` takes `uk' rt'` and never uses them.
     - `codet` comes from the collision count.
   - `walk-hit-collC`/`walk-owned` also ignore their `RecChains` argument.
   - Patches prepared but NOT typechecked:
     - `/tmp/r3a/spike/Core-A.agda` (conservative): deletes `HasVal`, `UniqueKeys`, `Rooted` and seven producer lemmas, plus `callC-supp`'s `idx < k`.
     - `Core-B.agda`: also moves `Bnd`'s `runPath` conjunct into `FKout` and deletes `CBnd`/`Bnd`/`callC-supp`/`walk-supp(L)`.
   - The `md-cert`, `ideal-marginal`, `ghost-erase` and `MDInvData` types are unchanged; `MDInv` and internal lemma statements lose dead conjuncts or hypotheses.
   - Docs: `docs/ro-game-hop.md:187-188`.
2. `src/CategoricalCrypto/RandomOracle.agda`, `RandomOracle2.agda` (+ `CategoricalCrypto/Standard.agda`) — delete, **−227**.
   - No importer anywhere, and the root does not import them.
   - `ROData`'s free fields `_≈ℰ[_]_`/`VanishingBound`/`absorb` can be instantiated so that `MD≤UC-RO` restates its hypotheses.
   - `Standard` is orphaned with them.
   - Re-listed from A-examples (Integration-owned); still your call.
3. `src/CategoricalCrypto/Examples/CoinToss/Ideal/{Machine,Receiver/Machine,Receiver/Hybrid}.agda :: botᴵ downᴵ backᴵ honᴵ botᴵʰ downᴵʰ backᴵʰ honᴵʰ lkᴴʰ` — **−41**.
   - Residue of the `Walk` hoist: each wrapper is `Walk.R-bot/R-down/F-up` behind a `bindˣ ≈refl` adapter.
   - Inlined patch prepared, NOT typechecked: `/tmp/r3a/spike/ct/`. `bypᴵʰ` is kept, because it has 9 sites and would wrap.
4. Fourteen single-use `stateX : State` aliases (`= initˢ …`, one `mk` use each) — **−42**.
   - Sites:
     - `CoinToss`: `stateᵖ`
     - `Hiding`: `stateᵗ`
     - `Ideal`: `stateᵏ`, `stateʲ`
     - `Ideal/Receiver`: `stateᵏʰ`, `stateʲʰ`
     - `Ideal/Reach`: `stateᶜ`
     - `Receiver/Reach`: `stateᴱ`, `stateᴰ`
     - `ROCommitment`: `stateᴿ`, `stateˢ`
     - `ROCommitment/Hiding`: `stateʰ`, `stateᵖ`
     - `Resource`: `stateᵒ`
     - `HashForward`: `stateˢ`
   - Script `/tmp/r3a/inline_state.py` (grep-guarded); not run. Rule 26: there are more in `UC/Seam`.
5. `src/CategoricalCrypto/Examples/CoinToss/Ideal/Compose.agda` vs `Receiver/Compose.agda` — **−15..−20**.
   - `simᶜⁱ/simᶜʳ`, `coin-toss-idealᵇ/ʳᵇ`, `coin-toss-ideal/ʳ`, `coinRealʷ/ʰʷ` and `coin-toss-idealᴺ/ʳᴺ` differ only in the first-hop certificate, `sh`, `η` and the hop.
   - Merge them into one parameterised second-stage module; public names and types stay.
   - Crux: implicit-channel inference.
6. `src/CategoricalCrypto/Examples/ROCommitment/Hiding/{Game,Defer}.agda :: ask-redᴸ ask-redᴮ ask-redᴾ ask-redᴿ` — **−16**. Named instances of `E-bind₂`/`lookupᴰℚ-Dmap`; inline at the 13 sites. `docs/fcom-hiding.md:317` names two of them.
7. `src/CategoricalCrypto/Examples/ROCommitment/Transport.agda :: map-return map-bot respᵀ respᴿ respᴮ` — **−18 here, +8 in `Dp/Settle`**.
   - Generic `Settles` facts at `Dmap⊥ f`.
   - `Protocol/Machine/Agree.agda:90-94` proves `respᴮ` inline, which makes it a second consumer.
8. `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Defer.agda :: idle-join` — **−15 / +8**. Re-spells `GamePlaying.Hop.JoinStep`'s Σ. Add `JoinAt`/`join-return` in `Hop`.
9. `src/CategoricalCrypto/Examples/ROCommitment/Extraction.agda :: lookupPt lookup-here lookup-there` — **−14**.
   - These are `RandomOracle.lookup-bs{,-here,-there}` at `Pt`/`Dig`; MD's copy already went (`603b6511`).
   - Crux: `lookup-bs` lives in a parameterised module, the argument order differs, and the import is heavier.
10. `src/CategoricalCrypto/Examples/MerkleDamgard/Core.agda` small library swaps — about **−22**. Not committed for lack of time.
    - `walk-replayC (just w)` = `OnSupport-bind-return`
    - `callC-marg`/`walkR []` = `E-return-cong … refl`
    - `dich-owned` = `map₂ proj₁ ∘ dich`
    - `stepR`'s `aux` needs no `eq`
    - `φ-step.aux`'s shared tail
    - `⌊≟⌋-refl` = `Class.DecEq.Ext.≟-refl`. This refines the pending `QUALITY-REVIEW.md:1041` entry; it is not new.
11. `src/CategoricalCrypto/Examples/ChimericLedger` small items:
    - `Observable :: auditWatch-sound/-complete`: drop the `subst` (`sound (≤-minimum _)`, `complete (≤-reflexive init-good)`), −6.
    - `ChimericLedger`/`Value`/`Replay :: DecEq-×′`: three private copies of `categorical-crypto.Prelude.DecEq-×′`, −6. Risk: instance overlap.
    - `Value :: checkIns-head`: one consumer, inline, −4.
    - `Replay :: module One/OneG`: `open Attack … using (…)`, −2.
    - `Birthday`: adjacent `private` blocks merge, −3.
    - `Property :: εᴸ` is `Uniform.Birthday.birthday-bound`: one notion.
    - `Transfer :: ledger-uc-to-pov-family`, `ledger-pov-family-negligible`: "pov" is a fossil of the retired POV notion. Rename to `…-hit`; this is interface, and docs cite it.
12. `src/CategoricalCrypto/Examples/CoinToss/Ideal/{UC,Receiver/UC}.agda :: onL, Aᵍ`.
    - Five `onL … = botₚ` clauses are subsumed by the catch-all.
    - `Aᵍ` is a one-use alias; spell it out as `Hiding/UC` does.
    - −11 total.
13. `src/CategoricalCrypto/Examples/ROCommitment/Hiding/Defer.agda :: ∨-≤, 0≤εᴾ, idle-drift`: hand-rolled `Data.Rational.Properties.Ext.p≤p+q` (−3). `Resource :: lazy-map` has zero uses: delete (−5). `Hiding/Test`'s `import … Hiding.Game as G` is redundant with the open (−1).
14. `src/CategoricalCrypto/Examples/HashForward/Audit.agda` — fossil module name: `UC.Audit` is deleted and nothing in the module is about audits.
    - Rename it to `HashForward.Bound`, or fold it into `HashForward/UC` (−20, one module fewer).
    - The root's import changes.
15. Statement: `src/CategoricalCrypto/Examples/Basic.agda :: Encryption.Dec` computes `p = lookupPlainText …`, ignores it, and returns `inj₁ c`.
    - `EncryptionShim.DecRcv` is therefore uninhabited, and `SecureFromAuthenticated` can never deliver.
    - Fix: `return just $ L⊗ ϵ ↑ₒ inj₂ p`. Spec change, so your call.
16. Tests (rule 33):
    - `CoinToss/Test :: attack-bound ideal-bound ideal-boundʳ` pin the auxiliary schedules, not the headline theorems. The retarget is `proj₁ (proj₂ (coin-toss-idealᶜ e)) 5 3 ≡ …`, which also gives `coin-toss-idealʳᶜ` its first consumer.
    - `HashForward/UC :: sim-round` pins the raw `behᵍ` triple, not `behᴾ simulator` (the A-examples #21 fix, missed here).
17. Docs drift (exact lines are in the finder reports; resync not done):
    - `docs/end-to-end.md:102,107,169,194,212,275,399` (the spurious `a`, "appendix", "monitor's one query").
    - `docs/quantitative-family.md` §14.1 (`εᴹ`, `hitsᶠ⇒hitsᴺ`, wrong signatures) and §6 (`hf-witness`).
    - `docs/coin-toss.md` and `docs/rcom-icom-b1.md`: `UC-composeᵉ`, `idᶜ`, `≤UC^ωᵉ-dom`, `UC.Asymptotic.Compose`, and about 60 stale `file:line` pins.
    - `docs/fcom-hiding.md`, `fcom-extraction.md`, `hash-forward.md`, `dp-transport.md`.
    - `docs/state-event-contract.md` is unmarked historical.
    - `README.md:87-89,119`.

## Tried, not worth it

- `src/CategoricalCrypto/Examples/ROCommitment/{Resource,Oracle,Transport} :: lazyₚ, fetchT` — not one oracle kernel twice. They live in different monads (`Dₚ` vs `Dist-ℚ`), and `Transport.hash` is the theorem connecting them. `Game.fetch` raises the flag only on a miss.
- `src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Machine.agda :: μʰ` — used 10 times; keep.
- `src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Machine.agda :: bypᴵʰ` — inlining makes 9 sites wrap.

## Not reached

- Sweep classes not run: `implicit-drop`, `binder-drop`, `join-lines`.
- `enum-with` (93 sites) and `enum-where` (192 sites, 150 flagged) were enumerated but not dispositioned. Patched transform scripts are at `/tmp/r3a/{with_case_fixed,where_inline_fixed}.py`; the canonical scripts have the A-examples W2 bugs.
- Suggestions 1, 3, 4 and 10–13 are commit-grade candidates whose patches or scripts exist. None is typechecked, so all stay suggestions.
- Docs resync (17) not done.

## Verification table (tip)

Run at the tip, with `-M8G -H2G`; rc and warn grep for each:

| module | rc | warn | elaborated | wall |
|---|---|---|---|---|
| `Examples/ChimericLedger/Transfer` | 0 | 0 | 8 | 130 s |
| `Examples/ChimericLedger/Serialize` | 0 | 0 | 1 | 11 s |
| `Examples/MerkleDamgard/Pin` | 0 | 0 | 3 | 11 s |
| `Examples/MerkleDamgard/QueryBound` | 0 | 0 | 1 | 9 s |
| `Examples/RelSetup` | 0 | 0 | 1 | 8 s |
| `RandomOracle` | 0 | 0 | 1 | 7 s |
| `RandomOracle2` | 0 | 0 | 1 | 7 s |
| `CategoricalCrypto` (root) | 0 | 0 | 41 | 34 s |

These are every non-root leaf the scope reaches, plus the root; together they cover all 60 scope modules.
