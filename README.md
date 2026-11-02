# cipherlean — a Claude Code skill: paper theorem → checked Lean 4 proof

Takes a theorem from a cryptanalysis paper (or a statement you type), pins its exact
hypotheses, encodes it in Lean 4 + Mathlib, tests the definitions on a toy instance and a
counterexample, proves it lemma by lemma, and checks the result (`lake build`, no `sorry`,
standard axioms only). Written around Hosein Hadipour's post "Lean for Cryptanalysts"
(hoseinhadipour.com/blog/lean-for-cryptanalysts, 2026). Ships with `CipherLean`, a small
Lean library of the objects these statements use (vectors over `F_2`, characters, subspaces with
duality, Walsh coefficients, the DDT, table S-boxes) with its lemmas machine-checked.

## Requirements
- macOS (tested) or Linux (Ubuntu 24.04 tested 2026-11-02; Windows through WSL untested), `curl`, `git`,
  `python3`, 10 GB of free disk (the installed workspace takes about 7 GB), network for
  the first setup (Lean toolchain ≈ 300 MB, shallow git clones ≈ 170 MB, prebuilt Mathlib ≈ 2 GB).
- Claude Code (the skill lives in `~/.claude/skills/`). Lean and Mathlib are installed by the
  skill's own script; nothing else is needed.

## Install
1. Clone this repository to `~/.claude/skills/cipherlean/` (keep the name):
   ```
   git clone https://github.com/hukaisdu/cipherlean ~/.claude/skills/cipherlean
   ```
   (or unzip a `cipherlean.skill` package to the same place).
2. In a terminal, or by asking Claude "set up the cipherlean environment":
   ```
   bash ~/.claude/skills/cipherlean/scripts/setup_env.sh --install --examples
   ```
   This installs elan (official installer) and Lean `v4.33.0` if missing, creates the workspace
   `~/cipherlean` (override with `CIPHERLEAN_WS`), downloads the prebuilt Mathlib `v4.33.0`,
   copies and compiles the shared library `CipherLean` and the examples, and ends with a smoke
   build and the check script. Rerun it after any failure; it never overwrites existing files.
   `--check` only reports.

## Update
`git pull` in `~/.claude/skills/cipherlean`, then
```
bash ~/.claude/skills/cipherlean/scripts/setup_env.sh --update-library
```
which rebuilds the library. The workspace's `CipherLean/Lib/` and the umbrella `CipherLean.lean` are
symlinks to this repository's `assets/lib/` and `assets/workspace/CipherLean.lean`, so the pull is the
update and a lemma promoted in the workspace is a change of this repository (commit it, or send it as a
pull request). A workspace installed before 2026-11-03 holds copies: `--update-library` replaces a copy
that is identical to the repository's by the symlink, and refuses while they differ — put the difference
into `assets/lib/` first.

## Use
In Claude Code, inside a paper's directory: "formalize Theorem 2 of this paper in Lean",
"用 Lean 证明这个 lemma", "check whether the DDT row-sum identity holds for every S-box".
Claude runs the environment check, pins the statement in `README.md`, writes the proof chain
`CHAIN.md` with its TikZ dependency graph `CHAIN.pdf` and the roadmap (the end you choose, the pieces
with their sizes) and stops for you to confirm it (the one gate of the workflow), then encodes the chain
in `CipherLean/<Slug>/Main.lean` with `NOTATION.md`, proves it, checks that Lean's dependency graph
matches the confirmed chain, and reports the status table and the position of the whole theorem (pieces
done, size-weighted progress, the next piece) at every stop. Results live in the workspace;
`new_paper.sh` with `--paper-dir` keeps the Lean files with the paper instead (`<repo>/formal/`,
symlinked into the workspace). Every command is in the table of `SKILL.md`.

## Faster iterations (optional)
- The snippet runner (`lean_eval.sh`) answers a `#check` in about 7 s with a light import preset;
  the import trimmer (`trim_imports.py`) shrinks a finished file's imports so later builds and checks
  load in seconds.
- `setup_env.sh --mcp` registers the `lean-lsp-mcp` server with Claude Code (needs `uv`); that
  server's documentation says it keeps Mathlib loaded between proof attempts. Not tested from this skill.

## On a server

The same skill and workspace install on a Linux machine (tested 2026-11-02 on Ubuntu 24.04, x86_64:
`git clone` of this repository to `~/.claude/skills/cipherlean`, then `setup_env.sh --install --examples`,
3 minutes with a fast connection to the Mathlib cache; `ENVIRONMENT OK`). Keep the sources on your own
machine and run the slow steps there with `remote.sh` (sync, build, check, chain, trim, lib, eval; the
host in `CIPHERLEAN_REMOTE`): it rsyncs `CipherLean/<Slug>/` first and puts `~/.elan/bin` on the remote
PATH, which non-login ssh shells lack.

## What one session can deliver
A theorem whose proof chain has about ten rows and one or two computational cases: pinned
statement, confirmed chain and graph, definitions tested on a toy, lemmas proved, checks passed,
review done. Verifying an *existing* formalization is a different job (`references/verify-existing.md`).
A theorem whose proof is a long case analysis with appendix tables or an induction over a general
parameter is a multi-week project; the skill's job is then to say so with an estimate and to
deliver the first lemma-sized piece.

## Running outside Claude Code
The scripts are plain bash and Python and the references are Markdown, so any agent harness that
can read a `SKILL.md` can use the skill: clone it anywhere, set `SKILL` to the clone's path where the
instructions write `$SKILL`, and run the installer once. The reviewer of step 8 can be a second chat
given `references/review-brief.md`; `REVIEW.md` is the record either way. Two cautions from a run in
another harness: do not let the harness re-inject the task as a recurring "goal" (it produced fifty
one-minute turns), and the workflow's judgement steps (3, 6, the promotion of 7) need a frontier-class
model; a small model is fine for the checks. One agent per workspace: the build lock serializes two
agents, it does not make them fast.

### Task books for another agent

When you hand a formalization step to another agent as a written task (a "task book"), date it against
the repository state (the commit of this skill and of the paper directory), say which log file the
agent may write and that the installed workspace is to be checked with `setup_env.sh --check` before
anything is reinstalled, and ask for the status board and the Position block (`status.py`) at the end of
every step. A task book that contradicts the standing rules of the user's own configuration (which files may
be written, where logs go) costs the agent a round of clarification.

## Growing the library
After a formalization, `promote_candidates.py` (all the pieces of a split theorem in one run) lists the
declarations that are general enough for the shared library (class A/B/E/F) and those that are not
(toys, duplicates); the user decides, the agent moves them, `repoint_names.py` re-points the
directory's Markdown files at the library names, and the move is committed here, since the workspace
library is this repository's `assets/lib/` through a symlink. Criteria and checklist: `references/promotion.md`.

## Contribute
Pull requests that add general lemmas to the library, fix scripts, or add an example are
welcome: see `CONTRIBUTING.md` (fork, develop in the workspace, which edits `assets/lib/` through the
symlink, PR with the `check_lean.py` verdicts). The *Update* section above is only about refreshing your local copy.

## Review by a second agent
`references/review-brief.md` is the brief for an independent reviewer (a subagent or a second
session) that checks every Lean statement against the paper and the confirmed `CHAIN.md`. The
exchange is written down in `REVIEW.md`, round by round: the reviewer's numbered objections, the
formalizer's answer to each (`fixed` / `rejected` with a reason / `needs the user`), and the
reviewer's judgement of those answers in the next round; each round is also summarized in the
chat as it happens. Step 8 stops only when a round ends in ACCEPT and both check scripts pass.

## Layout
```
SKILL.md          the workflow Claude follows (steps 1–8: environment, statement, chain + roadmap gate, skeleton,
                  finite checks, proofs, check + report + promotion, review) and the one table of every command
references/       cheatsheet (encodings, idioms, pitfalls), workspace notes, promotion criteria, review brief,
                  verifying an existing project, postmortems, related tools
scripts/          the environment installer, the paper scaffold, the chain graph and the chain check, the
                  status board, the snippet runner, the lemma search, the serialized build, the one Lean listing
                  (inspect_lean) that the final axiom check, the chain check, the notation check and the promotion
                  classifier read, the import trimmer, the re-pointer, the remote runner, the build profiler,
                  the sandbox for external projects
assets/           templates (README, CHAIN, NOTATION, REVIEW, Lean file), examples (Feistel, Halfspace,
                  SboxDDT, the complete run DdtInverse/), the shared library lib/ (the workspace's
                  CipherLean/Lib/ is a symlink to it), the pinned workspace files (lakefile, lean-toolchain, lake-manifest.json)
CONTRIBUTING.md   how to send a pull request
```

## License
MIT, see `LICENSE`. The statements formalized in the examples are cited to their sources in the
file headers; the Lean code here is original.

## Trust model
Every result is reported with its axioms. The default is the standard three (`propext`,
`Classical.choice`, `Quot.sound`) with `decide +kernel` for finite computations. When a case the
paper settles by computation is too large for the kernel, `native_decide` is allowed under the
computational-cases rule of step 6: a kernel-checked bridge lemma ties the Boolean program to the mathematical
statement, the declaration is reported as NATIVE, and the result is stated as proved relative to
the compiler axiom. Nothing general is ever closed with `native_decide`.

## Versions
Lean `v4.33.0`, Mathlib `v4.33.0` (commit `db584cd6`), pinned in `assets/workspace/`. Every
lemma name in the cheatsheet was compiled against this pin; see `references/workspace.md`
before changing it.
