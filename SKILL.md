---
name: cipherlean
description: |
  Formalize a theorem from a cryptanalysis paper in Lean 4 + Mathlib: pin the statement
  and every hypothesis (implicit ones too), encode and state it, test it on a toy instance
  and a counterexample, prove it lemma by lemma, check with lake build and an axiom report
  (no sorry, standard axioms), then have an independent agent review it against the paper.
  Runs in a persistent workspace (~/cipherlean, Lean v4.33.0 + Mathlib v4.33.0) that
  scripts/setup_env.sh checks and installs. Use whenever the user mentions Lean, Mathlib,
  a formal or machine-checked proof, "形式化", "用 Lean 证明/验证", "把定理写成 Lean", "formalize
  Theorem 3", or wants a checked proof of an identity between cryptanalytic statistics
  (linear/integral sums, DDT/LAT counts, divisibility, Walsh coefficients, subspace
  character sums) or of a cipher-component property (S-box bijectivity, differential
  uniformity, Feistel round invertibility). Not for brute-force numerics or attack code
  (crypto-code), nor paper reading without a formalization goal (paper-reading).
allowed-tools: ["Read", "Write", "Edit", "Bash", "Grep", "Glob", "WebFetch", "AskUserQuestion"]
---

# Theorem → Lean 4 formalization

Deliverable for one paper theorem, a directory `CipherLean/<Slug>/` in the workspace: `README.md` (the statement as the paper
states it, every hypothesis, the status table, the position at every stop), `CHAIN.md` + `CHAIN.pdf` (the proof chain, its
graph and the roadmap, confirmed by the reader before any Lean), `NOTATION.md` (paper symbol ↔ Lean name), `.lean` files that
`lake build` accepts with no `sorry` and standard axioms, a toy instance and one counterexample per hypothesis. The final
message says what was proved, which hypotheses were added, where the Lean statement departs from the paper, and where the
whole theorem stands. Lean checks proofs, not definitions (Hadipour, "Lean for Cryptanalysts", 2026): most of this is the statement.

## Workspace and commands

Persistent Lake project at `~/cipherlean` (override with `CIPHERLEAN_WS`), created by `setup_env.sh --install`: Lean `v4.33.0`,
Mathlib `v4.33.0` prebuilt (≈ 6 GB under `.lake/`), `autoImplicit = false`, one subdirectory per paper, and the shared library
`CipherLean/Lib/` (vectors over `F_2`, characters, subspaces and duality, affine hulls, Walsh, DDT, linear structures, table
S-boxes; its `README.md` and `NOTATION.md`), a symlink to the skill's `assets/lib` so that a promoted lemma is committed in
the skill. Every paper file starts with `import CipherLean`; define an object yourself only when the library lacks it. Run
everything from the workspace root (the scripts put `~/.elan/bin` on PATH).

| task | `$SKILL/scripts/cipherlean <subcommand>` from `~/cipherlean` (`$SKILL` = `~/.claude/skills/cipherlean`; the script paths `scripts/<name>` work too; this table is the only copy in the skill) |
|---|---|
| environment (step 1) | `cipherlean setup --check` (2 s); `--install [--examples]` once; `--update-library` after a `git pull` of the skill |
| scaffold a paper | `cipherlean new <Slug> [--paper-dir <paper repo>] [--file <Piece>]` (README, CHAIN, NOTATION, Main.lean; `--file` adds a piece file) |
| graph and roadmap (step 3) | `cipherlean graph CipherLean/<Slug>/CHAIN.md` → `CHAIN.tex`, `CHAIN.pdf`, mermaid; `--gaps` what remains; `--focus <id> [--depth N]` or `--rows a,b,c` one piece's sub-chain |
| position and status board | `cipherlean status <Slug>` (`--position` the Position block alone; `--check` reruns the verdicts on one Lean listing, `cipherlean inspect <files> --out FILE.json`, which every check also accepts as `--listing`) |
| try a snippet (7 s) | `printf '#check @Foo.bar\n' \| cipherlean eval -` (`--full` for all of Mathlib) |
| find a lemma | `cipherlean search "<name fragment or statement shape>"` (local grep, Loogle, LeanSearch) |
| build one module | `cipherlean build CipherLean.<Slug>.<File>` (`lake build` under the workspace lock; `CipherLean` rebuilds the library) |
| chain vs. Lean (step 7) | `cipherlean chain CipherLean/<Slug>/CHAIN.md CipherLean/<Slug>/<File>.lean […]` (every piece file in one run) |
| final check (step 7) | `cipherlean check CipherLean/<Slug>/<File>.lean [--no-build] [--allow-native]` |
| trim imports (step 7) | `cipherlean trim CipherLean/<Slug>/<File>.lean --apply` (`--why` names what each surviving module supplies) |
| cited names exist? (step 7) | `cipherlean notation CipherLean/<Slug>/NOTATION.md <every piece file> --also README.md CHAIN.md` |
| promotion candidates (step 7) | `cipherlean promote CipherLean/<Slug>/<File>.lean […] --write` (all pieces in one run; appends to `PROMOTE.md`) |
| re-point after a move (step 7) | `cipherlean repoint CipherLean/<Slug>/ <name>[=<new>] … [--lib] [--apply]`; the library is the skill's `assets/lib` through the symlink, so commit there |
| the same steps on a server | `CIPHERLEAN_REMOTE=user@host cipherlean remote sync\|build\|check\|chain\|trim\|lib\|eval …` (sources stay here) |
| someone else's project | `cipherlean sandbox <project>`; `cipherlean profile <lake build log>` or `--sites <dir>`; then `references/verify-existing.md` |
| independent review (step 8) | a fresh agent given `references/review-brief.md` |

With `--paper-dir` the real files live in `<paper repo>/formal/`, symlinked as `CipherLean/<Slug>`. Models to imitate:
`CipherLean/Examples/{Feistel,Halfspace,SboxDDT}.lean` and the complete run `CipherLean/Examples/DdtInverse/`.

The reader is not watching the tool calls. At the end of every step, and whenever a job that takes minutes starts, print the
status board and say which machine the job runs on and what the next gate is. At every stop — the gate of step 3, the end of
every piece, every budget stop — print the Position block (`status.py <Slug> --position`: the end the user chose, pieces done
of planned, rows proved of total, the size-weighted progress, the remaining pieces with their estimates, the next piece) and
the colored graph (`chain_graph.py`, plus `--gaps`); update the Roadmap table (status, actual against estimate), paste the
block under a dated heading in README's Roadmap section, name the next piece and ask which one to do. "Done" for a piece is
never reported without the whole theorem's position. Keep the day's log (quoted heredoc) and read the task's `NOTATION.md`.

## Workflow
### 1. Check the environment (every task, seconds)
Run `setup_env.sh --check`. All OK: go on. Something MISSING: say what `--install` does (elan, the toolchain ≈ 300 MB, shallow
clones ≈ 170 MB, the prebuilt Mathlib ≈ 2 GB, 6 GB on disk, 10–30 min) and run it once the user agrees, or at once if they
asked for the setup; it is idempotent, never overwrites a file, and is simply rerun after a failure.

### 2. Pin the statement
- Get the source: the LaTeX (arXiv e-print, the user's `paper/`) over the PDF; never work from memory of the paper. When the
  user's message is the source, quote it verbatim under "Source", write "no paper", skip the literature hunt. Read a cited
  result from its own source, not from the citing sentence.
- Copy the statement verbatim into `README.md` with label and page; list (a) every object with its type, (b) every hypothesis,
  marked *explicit* or *implicit* (the ones proofs use silently: "E is a permutation", "the mask is nonzero", "n ≥ 1"), (c) the
  conclusion, (d) the proof as numbered steps — each becomes one row of the chain and one Lean lemma.
- Keep the paper's constants and generality; a needed specialization goes under "Departures from the paper" with its reason,
  an ambiguity with the reading taken. For a whole section, list every numbered statement first, then state them all.

### 3. The proof chain, its graph and the roadmap — the reader's gate
Write `CHAIN.md` from the template: one row per thing the proof relies on (the target, every lemma and proof step, every
definition, every cited result checked in its own source, every hypothesis or modelling assumption) with `uses` (`id?` for
a premise the paper's text relies on but the Lean lemma will not: drawn dashed, accepted by `chain_check.py`), `where`
(section and statement first, then `;` and notes), implicit hypotheses and `status: pending`. Then size the job in the
Roadmap table: the end the user chooses (self-contained: every row proved here; relative: named lemmas accepted from a
companion project), the milestones, and one row per piece with its rows, route (`prove here` · `port from <project>` ·
`assume by citation` · `hypothesis`), size in sessions with the evidence (an existing formalization's line count, the
computational cases, what a comparable piece took) and status. One session delivers about ten rows with one or two
computational cases; seven directions, two appendix tables and a length induction (52 000 lines in an existing
formalization) is a multi-week project, and saying so is the deliverable. Run `chain_graph.py`, give the reader the table,
the graph, the questions and the Position block, and stop: nothing is encoded before they confirm the chain and pick the
first piece. This is the one gate of the workflow, where a misread theorem is cheapest to fix.

### 4. Skeleton: NOTATION.md and the statement with `sorry`
Write `NOTATION.md` (paper symbol, Lean name, type, meaning, scope): encodings from the library first, then the cheatsheet §1;
counts rather than probabilities (division is total in Lean, `x / 0 = 0`; the normalized form is a corollary). Create the
file (`new_paper.sh`, `--file` per piece), write the definitions, then every row of the confirmed chain as a declaration with
`sorry` in dependency order, each with a docstring quoting the paper (`/-- Paper: Theorem 2, "..." -/`), and compile together
with the finite checks of step 5. Fill the `lean` column of CHAIN.md as you go (one declaration name or `—`; notes go in
`implicit`) and set `status: stated`. A piece file imports the previous piece and, explicitly, the library modules it uses
(cheatsheet idiom 35); when the last piece is done, `Main.lean` becomes the aggregator (imports of all pieces, the target
restated) so no `sorry` stub survives. A wrong statement is cheap here, not after a 200-line proof.

### 5. Test the statement before proving it
On a toy instance (2–4 bits, a concrete S-box) prove by `decide` or `decide +kernel` that the conclusion holds where the
hypotheses hold and fails for a concrete object that drops one hypothesis (a constant map instead of a permutation, a zero
mask). This is the only check that catches a definition encoding the wrong object; keep the checks as theorems in the file,
they document why each hypothesis is there. Compute the toy's numbers outside Lean first (a ten-line Python script, kept in
the paper directory) and pick an instance where the wrong side really differs; a hypothesis implied by the others on finite
types is proved, not refuted. Kernel costs, `maxRecDepth`, a stuck `decide`: cheatsheet idioms 25, 34, 36, 37.

### 6. Prove, one lemma per proof step
- Search before proving: the library (`rg <word> CipherLean/Lib`), then Mathlib with `exact?`, `apply?`, `simp?` and
  `search_mathlib.sh` — names drift between versions. Tactics and compiled idioms: cheatsheet §2–§3.
- Test lemma names and small examples with `lean_eval.sh` (7 s); build a module once a lemma is finished, and batch finished
  lemmas into one build. Keep the declaration headers fixed; if a statement must change, go back to step 2.
- Budget: after a serious attempt (several strategies, Mathlib searched; about half an hour or five builds for one lemma)
  leave it as `sorry` with the exact remaining goal and what was tried, and move on. Never weaken a statement to hide a gap,
  never close a general goal with `native_decide`. When the remaining work is a known-large piece (appendix tables, an
  induction over a general parameter, a certificate that takes hours): update the Roadmap, print the position, ask.
#### Cases the paper settles by computation
Formalize along the paper's case split, each computational case a closed decidable statement over a finite domain; symbolic
splits (`m` odd or even, a parameter in a range) are `rcases` / `fin_cases` / `interval_cases` / `omega`, no axiom. For the
computations, in order: (1) `decide +kernel` up to about 2^14–2^16 evaluations, no axiom; (2) make the kernel able — `BitVec`
instead of `Vec (Fin n)`, `Nat` arithmetic, a search turned into the check of an offline certificate shipped as data; (3)
`native_decide` only when the kernel cannot finish, with a kernel-checked bridge `checker_true : checker = true → P` (idiom
26), the declaration reported as NATIVE (`check_lean.py --allow-native`) and everything depending on it stated as "proved
relative to the compiler axiom"; `bv_decide` carries the same obligations. Record in CHAIN.md how each computational row is
discharged; large closed data only through `opaque` (idiom 27); the first certificate module is built alone and profiled.

### 7. Check, trim, report
`chain_check.py` over every piece file compares the confirmed chain with the dependency graph Lean used (edges direct,
statement-only, transitive, the paper's route or MISSING; extra edges; unknown names) and must end in `VERDICT: CONSISTENT`;
explain every difference in CHAIN.md. `check_lean.py` builds each file, lists every declaration with its axioms and
elaborated statement, and fails on `sorryAx`, on custom axioms and on the compiler-trusting axioms unless `--allow-native`
covers the computational cases; read the printed statements against the paper once more — the human half of the check.
Then `trim_imports.py --apply` (3–7 s loads instead of 27 s), the README status table (paper label · declaration · status ·
axioms · note) and "Departures", and `notation_check.py --also README.md CHAIN.md`, so that every cited Lean name exists and
every cited script lives in the paper directory. Say "proved" only after both verdicts, and only for the paper's statement
in full (both directions of an "exactly", every case). In the reply: what is proved, what is `sorry` and why, the hypotheses
the paper left implicit, the rebuild commands, every caveat at the top, and the Position block.
#### Promote to the shared library
`promote_candidates.py` over all piece files classifies every declaration (A general lemma about library objects · B general
but about a paper object · E an object the paper defined · F general, Mathlib only · D duplicate of a library statement · C
toy); apply the five questions of `references/promotion.md`, give the user one recommendation per row, and after their
decision move the accepted ones with that page's checklist (library names and variables, docstring with the source, a finite
check per definition, the library rebuilt and checked, NOTATION and README rows, the paper file and its `.md`
files re-pointed, the skill repository committed). Unpublished results stay with the paper however general they look.

### 8. Independent review (two agents)
Lean checked the proof; nobody has checked that the *statement* is the paper's. For any result the user will cite, hand the
directory to a reviewer that has not seen your reasoning — a fresh subagent or a second session given
`references/review-brief.md`, the paper source, the label, the directory and the workspace. It compares every Lean statement
with the paper, checks CHAIN.md row by row, reruns both scripts and appends `Round n — reviewer` to `REVIEW.md` (template
`assets/REVIEW-template.md`) ending in `VERDICT: ACCEPT` or `REVISE` with objections `R<n>.<k>`. Answer each in `Round n —
formalizer` (`fixed` / `rejected` with a checkable reason / `needs the user`), post objections and answers in the chat, fix
every BLOCKER and MAJOR, ask for a new round; from round 2 the reviewer examines only what changed plus the answers. Finished
when a round ends in ACCEPT and both checks pass; after three rounds without ACCEPT, stop and give the user the open objections.

## Verifying an existing formalization
When the Lean project already exists and the question is whether it proves the paper, `references/verify-existing.md`
replaces steps 2–6 (pin and sandbox first, count the computational proofs, build the heaviest module alone under a written
budget, `check_lean.py` on every file, a chain table from the README and `chain_check.py`), then step 8.

## What to formalize first
Normalization and conversion identities between statistics; local properties of components (S-box bijectivity, differential
uniformity, round invertibility, key-schedule facts); divisibility or counting statements; that a search model's constraints
are satisfied exactly by the valid transitions. Modelling assumptions are hypotheses, never theorems; `PMF` only on request.

## Resources
- `references/lean-crypto-cheatsheet.md` — encodings, compiled idioms, tactics, pitfalls, speed, names that do not exist; read before step 4.
- `references/workspace.md` — versions, what costs time, VS Code, upgrading, errors.
- `references/promotion.md` — the candidate classes, the five questions, the moving checklist (step 7).
- `references/review-brief.md` — the reviewer's instructions and the stopping rule (step 8).
- `references/verify-existing.md` — verifying someone else's project, with the measured lessons.
- `references/postmortems.md` — two runs that went wrong and the rule each left behind.
- `references/ecosystem.md` — other Lean tools and what this skill borrows from each.
- `assets/` — the templates (README, CHAIN, NOTATION, REVIEW, `file-template.lean`), the examples, the library `lib/`, the pinned workspace files.
