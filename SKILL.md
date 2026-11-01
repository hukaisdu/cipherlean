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

Deliverable for one paper theorem: a directory `CipherLean/<Slug>/` in the workspace holding
(1) `README.md` — the statement as the paper states it, every hypothesis, the proof plan,
and a status table; (2) `NOTATION.md` — paper symbol ↔ Lean name; (3) `.lean` files that
`lake build` accepts with no `sorry` and standard axioms only; (4) one toy instance where
the theorem holds and one counterexample per hypothesis that the paper needs. The final
message reports exactly what was proved, which hypotheses were added, and where the Lean
statement departs from the paper.

Lean checks proofs, not definitions (Hadipour, "Lean for Cryptanalysts", 2026). A
compiling proof of the wrong statement is worth nothing, so most of this skill is about
getting the statement right; the proof is the part Lean can vouch for.

## Workspace

Persistent Lake project at `~/cipherlean` (override with `CIPHERLEAN_WS`), created by
`$SKILL/scripts/setup_env.sh --install`: Lean `v4.33.0`, Mathlib `v4.33.0` prebuilt (about
6 GB under `.lake/`; do not delete it casually), one library `CipherLean`, one subdirectory per
paper, `autoImplicit = false` so a misspelled variable is an error instead of a silent new
hypothesis. Commands, VS Code use,
version bumps and troubleshooting: `references/workspace.md`. Run everything from the
workspace root.

Shared library `CipherLean/Lib/` (installed and compiled by `setup_env.sh`): the carrier
`Vec ι := ι → ZMod 2` with the `BitVec` bridge, characters, `Finset` subspaces with cosets,
annihilators and duality, Walsh coefficients with Parseval, the DDT with differential uniformity,
the Chabaud–Vaudenay link, and table S-boxes (PRESENT as the test instance). Every new paper file
starts with `import CipherLean`; `CipherLean/Lib/NOTATION.md` is the symbol table for these
objects and `CipherLean/Lib/README.md` lists the lemmas. Define an object yourself only when the
library lacks it.

`$SKILL` below is this skill's directory, `~/.claude/skills/cipherlean`.

| task | command (from `~/cipherlean`) |
|---|---|
| check / create the environment | `$SKILL/scripts/setup_env.sh --check` (2 s) / `--install` (first time) |
| scaffold a paper | `$SKILL/scripts/new_paper.sh <Slug> [--paper-dir <paper repo>]` |
| compile one file | `$SKILL/scripts/lake_build.sh CipherLean.<Slug>.<File>` (= `lake build` under a file lock, so parallel agents queue instead of colliding) |
| final check | `$SKILL/scripts/check_lean.py CipherLean/<Slug>/<File>.lean` |
| find a lemma | `$SKILL/scripts/search_mathlib.sh "<name fragment or statement shape>"` |
| try a snippet (7 s) | `printf '#check @Foo.bar\n' \| $SKILL/scripts/lean_eval.sh -` (`--full` for all of Mathlib) |
| trim imports when done | `$SKILL/scripts/trim_imports.py CipherLean/<Slug>/Main.lean --apply` |
| rebuild the shared library | `$SKILL/scripts/lake_build.sh CipherLean` (after adding a lemma to `CipherLean/Lib/`) |
| promotion candidates (step 7b) | `$SKILL/scripts/promote_candidates.py CipherLean/<Slug>/Main.lean --write` |
| library back into the skill | `$SKILL/scripts/sync_library.sh` (then commit / pull request, see `CONTRIBUTING.md`) |
| independent review | a fresh agent with `references/review-brief.md` (step 8) |

One Lean job at a time per workspace: the wrapper and the check script share a lock. Costs,
measured on a laptop: a Lean process that starts with `import Mathlib` spends ≈ 27 s mapping
8300 oleans before doing anything; the light preset of `lean_eval.sh` loads in ≈ 7 s and a
file trimmed by `trim_imports.py` in 3–7 s; a cached `lake build` costs ≈ 6 s of trace
checks; `check_lean.py` runs two Lean processes (build + listing): ≈ 1.5 min on an
untrimmed file, 7 s on a trimmed one. So: check lemma names and 3-line examples with
`lean_eval.sh` (7 s), build a module only when a lemma is finished, and trim the imports once
the proof is done (the shipped examples build in 3–6 s each after trimming). Compiled models to imitate for structure, docstrings
and finite checks: `CipherLean/Examples/{Feistel,Halfspace,SboxDDT}.lean`, and one complete run
with its README and NOTATION: `CipherLean/Examples/DdtInverse/` (a user-stated lemma, DDT
transpose).

With `--paper-dir`, the real files live in `<paper repo>/formal/` (versioned and synced with
the paper) and `CipherLean/<Slug>` is a symlink to them; without it they live in the workspace.

Before starting, read the task's `NOTATION.md` if one exists and keep the day's log as
usual; the per-paper `NOTATION.md` created here is that table for the formalization task.

## Workflow

### 0. Check the environment (every task, a few seconds)

Run `$SKILL/scripts/setup_env.sh --check`. It reports OK or MISSING for: macOS/Linux, `curl`
`git` `python3`, 10 GB of free disk, elan, the pinned Lean toolchain, the workspace files, the
prebuilt Mathlib, the examples. All OK: go on. Something MISSING: tell the user what
`--install` will do (install elan, download the toolchain ≈ 300 MB, a shallow clone of Mathlib
and its dependencies ≈ 170 MB, the prebuilt Mathlib ≈ 2 GB, 6 GB on disk, create
`~/cipherlean`; 10–30 min on a normal connection) and run
`$SKILL/scripts/setup_env.sh --install` once they agree, or straight away if they asked for
the setup. The script is idempotent, never overwrites an existing file, and ends with a smoke
build plus `check_lean.py`; rerun it after a failure (a lost network connection is the usual
cause). `--install --examples` also compiles the examples; `--check --smoke` adds the smoke
build to a check.

### 1. Pin the statement (the extraction step)

- Get the source. Prefer the LaTeX source (arXiv e-print, the user's `paper/` folder) over
  the PDF: macros and labels make the statement exact. Locate PDFs the paper-reading way
  (Zotero `library.bib`, cwd, ePrint). Never work from memory of the paper. When the user's
  own message is the source, quote it verbatim under "Source", write "no paper", and skip
  the literature hunt.
- Copy the statement verbatim into `README.md`, with its label and page. Then list, in
  words, (a) every object it mentions (sets, functions, parameters, masks, keys) with its
  type; (b) every hypothesis, marking each as *explicit in the paper* or *implicit* — the
  ones proofs use silently: "E is a permutation", "the mask is nonzero", "n ≥ 1", "the
  S-box is bijective", "round keys are independent"; (c) the conclusion; (d) the paper's
  proof as numbered steps. Each step will become one Lean lemma.
- Read any cited result from its own source, not from the paper's summary of it; what the
  proof needs can differ from the sentence that cites it.
- Keep the paper's constants and generality. Do not quietly prove a weaker or more
  convenient statement; if a specialization is needed (fixing a mask by a change of basis,
  fixing a block size), write it down under "Departures from the paper" with the reason.
  When the paper is ambiguous, record the reading you took.
- When the user names a section instead of a theorem, list every numbered statement with
  its label first, then formalize the statements (with `sorry`) before proving any — so
  the user sees the full map early.

### 2. Choose encodings and fix names

Write `NOTATION.md`: one row per paper object — paper symbol, Lean name, Lean type,
meaning, scope (per key / per round / global). Take the encoding from the shared library first
(`CipherLean/Lib/NOTATION.md`: `Vec ι` for `F_2^n`, `u ⬝ᵥ x`, `chi`, `walsh`, `linCount`, `ddt`,
`diffUniformity`, `IsSubspace`/`coset`/`ann`, `Sbox.ofTable`/`toFun`); for objects it lacks, pick
one from `references/lean-crypto-cheatsheet.md` (bits as `Bool`, words as `BitVec n`, masks and
linear maps over `ZMod 2`, sums as integer sums over a `Fintype`, probabilities as counts).
Prefer counting statements over probability statements: division is total in Lean
(`x / 0 = 0`), so a theorem about `count / 2^n` can hold for reasons unrelated to the
mathematics. Derive the normalized form as a corollary if the user wants it.

### 3. Definitions and statement first, with `sorry`

Create `CipherLean/<Slug>/Main.lean` from the template (`$SKILL/scripts/new_paper.sh` does this).
Write the definitions, then the main theorem with `sorry`, and compile together with the
finite checks of step 4 (they only need the definitions, so one build serves both). Give every
declaration a docstring with the paper's wording (`/-- Paper: Theorem 2, "..." -/`), the way
formal-conjectures requires an English version next to each formal statement. Type errors
at this stage are cheap; a wrong statement discovered after a 200-line proof is not.

### 4. Test the statement before proving it

On a toy instance (block size 2–4 bits, a concrete S-box) state and prove by `decide` or
`decide +kernel`: the conclusion holds where the hypotheses hold, and fails for a concrete
object that drops one hypothesis (a constant map instead of a permutation, a zero mask).
This is the only check that catches a definition encoding the wrong object, and it costs
minutes. Keep these as theorems in the file; they also document why each hypothesis is
there. For a symmetry or transpose statement, compute the toy's table outside Lean first (a
ten-line Python script) and pick an instance where the wrong side really differs. When a
hypothesis is implied by the others on finite types (one of the two inverse equations, say),
prove that implication and record it instead of hunting for a counterexample that cannot
exist.

### 5. Prove, one lemma per proof step

- Before proving anything general, search the library (`rg <word> ~/cipherlean/CipherLean/Lib`)
  and then Mathlib: `exact?`, `apply?`, `simp?`, and `$SKILL/scripts/search_mathlib.sh` (local
  grep, Loogle, LeanSearch), even when you think you know the file: Mathlib uses both `theorem`
  and `lemma`, and names drift between versions. Most algebra and big-operator facts exist
  already; the character-sum, duality, DDT and Walsh facts are in `CipherLean/Lib`.
- Tactic toolbox and compiled idioms for sums over bits, bijection reindexing, BitVec
  identities, divisibility: `references/lean-crypto-cheatsheet.md`.
- Test lemma names and small examples with `lean_eval.sh` (7 s), not with a module build; build
  the module once a lemma is finished, and batch several finished lemmas into one build. Keep
  the declaration headers fixed while proving; if a statement must change, go back to step 1
  and say so.
- Budget: after a serious attempt (several tactic strategies, searched Mathlib), leave the
  lemma as `sorry` with a comment stating the exact remaining goal and what was tried, and
  move on. Never hide a gap by weakening the statement or by `native_decide`.

### 6. Check

`$SKILL/scripts/check_lean.py CipherLean/<Slug>/Main.lean` builds the module, lists every declaration
with its axioms and its elaborated statement, and fails on `sorryAx`, on custom axioms, and
on the compiler-trusting axioms that `native_decide` / `bv_decide` introduce
(`<decl>._native.*.ax_*`, `Lean.ofReduceBool`) unless `--allow-native` is passed for
labelled finite checks. Read the printed statements against the paper one final time; this
is the human half of the check.

### 7. Trim and report

Run `$SKILL/scripts/trim_imports.py CipherLean/<Slug>/Main.lean --apply` (it asks Mathlib's
`#min_imports`, adds the tactic modules, and only rewrites the file after the trimmed copy
compiles): every later build, check and reader of the file gets the 3–7 s load instead of 27 s.
Then fill the status table in `README.md` (paper label · Lean declaration · status · axioms ·
note) and the "Departures from the paper" section. Then step 7b. In the reply: what is proved, what is
`sorry` and why, hypotheses the paper left implicit (these are findings about the paper),
and the exact commands to rebuild. Say "proved" only after step 6 passes.

### 7b. Promote to the shared library

Run `$SKILL/scripts/promote_candidates.py CipherLean/<Slug>/Main.lean --write`. It classifies every
declaration of the finished file: A (general lemma about library objects: move), B (general but
about an object the paper defined), E (an object the paper defined: general notion or
paper-specific?), F (general, Mathlib only), D (duplicate of a library statement: delete, import),
C (toy or test instance: stays). Read the statements, apply the five questions of
`references/promotion.md` (general in `ι`? a notion two papers would share? already there? part of
an unpublished result? explainable without the paper?), and give the user a table with one
recommendation per row. After their decision, move the accepted ones with the checklist in
`references/promotion.md`: library variables and names, docstring with the source, finite check for
a definition, `lake_build.sh CipherLean`, `check_lean.py`, rows in `CipherLean/Lib/NOTATION.md` and
`README.md`, the paper file re-pointed at the library and re-checked, `scripts/sync_library.sh`,
commit. Unpublished results stay in the paper directory however general they look.

### 8. Independent review (two agents)

Lean checks the proof; nobody has yet checked that the *statement* is the paper's. For any
result the user will cite or publish, hand the directory to a reviewer that has not seen your
reasoning: a fresh subagent (or a second Claude Code session) given `references/review-brief.md`,
the paper source, the theorem label, the directory and the workspace path. It compares every
Lean statement with the paper's text, builds the proof-correspondence table, reruns the check
script and writes `REVIEW.md` ending in `VERDICT: ACCEPT` or `REVISE` with numbered objections.
Fix every BLOCKER and MAJOR, update README, ask for a new round. The task is finished when a
round ends in ACCEPT and the check passes; after three rounds without ACCEPT, stop and give the
user the open objections. Skip this step only for throwaway statements, and say so.

## What to formalize first

Good first targets, in the order the blog recommends: normalization and conversion
identities between statistics; local properties of components (S-box bijectivity and
differential uniformity, round invertibility, key-schedule facts); divisibility or counting
statements; the claim that a search-model constraint set is satisfied exactly by the valid
transitions (no shipped example for this one yet). State as hypotheses, not as theorems, anything that is a modelling
assumption (Markov-cipher independence, random round keys, heuristic trail probabilities).
Asymptotic complexity claims and probabilistic statements over random keys need Mathlib's
`PMF` / measure theory; do them only when the user asks for exactly that.

## Resources

- `references/lean-crypto-cheatsheet.md` — encodings of cryptanalysis objects, compiled
  Mathlib lemma names, tactic toolbox, pitfalls. Read before step 2.
- `references/workflow-example.md` — one full run on the linear ↔ integral halfspace
  identity (ePrint 2026/2471), including the departure it records.
- `references/promotion.md` — step 7b: the candidate classes, the five questions, the moving
  checklist, and the first harvests as examples.
- `references/review-brief.md` — the reviewer agent's instructions and the stopping rule (step 8).
- `references/workspace.md` — layout, versions, commands, VS Code, upgrading, errors.
- `references/ecosystem.md` — other Lean tools (Tex2Lean, PaperFormalizer, autoform-bot,
  lean4-skills, lean-lsp-mcp, Lean REPL, VCVio) and what this skill borrows from each; when
  to hand a whole paper to one of them.
- `scripts/setup_env.sh` and `assets/workspace/` — the environment check / installer and the
  pinned workspace files it installs (`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`);
  `scripts/lean_eval.sh` (snippet runner), `scripts/trim_imports.py` (minimal imports),
  `scripts/lake_build.sh` (serialized build), `scripts/check_lean.py` (final check).
- `assets/examples/` — compiled examples (Feistel round, halfspace identity, S-box DDT) and
  the complete run `DdtInverse/` (Main.lean, README.md, NOTATION.md); `setup_env.sh` installs
  them as `CipherLean/Examples/`.
- `assets/lib/` — the shared library `CipherLean` (README.md, NOTATION.md, six modules);
  `setup_env.sh --install` copies it to `CipherLean/Lib/` and compiles it.
