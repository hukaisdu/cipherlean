# cipherlean — a Claude Code skill: paper theorem → checked Lean 4 proof

Takes a theorem from a cryptanalysis paper (or a statement you type), pins its exact
hypotheses, encodes it in Lean 4 + Mathlib, tests the definitions on a toy instance and a
counterexample, proves it lemma by lemma, and checks the result (`lake build`, no `sorry`,
standard axioms only). Written around Hosein Hadipour's post "Lean for Cryptanalysts"
(hoseinhadipour.com/blog/lean-for-cryptanalysts, 2026). Ships with `CipherLean`, a small
Lean library of the objects these statements use (vectors over `F_2`, characters, subspaces with
duality, Walsh coefficients, the DDT, table S-boxes) with its lemmas machine-checked.

## Requirements
- macOS (tested) or Linux (untested; Windows through WSL also untested), `curl`, `git`,
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
which copies the current `assets/lib/` over `CipherLean/Lib/` in the workspace and rebuilds it
(the installer alone never overwrites files that already exist). `setup_env.sh` keeps a copy of
the library it installed last in `~/cipherlean/.lake/cipherlean-lib-installed/`; a file of
`CipherLean/Lib/` that matches neither that copy nor the new `assets/lib/` counts as changed (a
lemma promoted in step 7b, say), and the update then lists it and stops without copying anything.
Send the change upstream first (*Contribute* below), or move the file out of `CipherLean/Lib/`,
then rerun.

## Use
In Claude Code, inside a paper's directory: "formalize Theorem 2 of this paper in Lean",
"用 Lean 证明这个 lemma", "check whether the DDT row-sum identity holds for every S-box".
Claude runs the environment check, pins the statement in `README.md`, writes the proof chain
`CHAIN.md` with its TikZ dependency graph `CHAIN.pdf` and stops for you to confirm it (the one
gate of the workflow), then encodes the chain in `CipherLean/<Slug>/Main.lean` with `NOTATION.md`,
proves it, checks that Lean's dependency graph matches the confirmed chain (`chain_check.py`), and
reports the status table. Results live in the
workspace; `new_paper.sh <Slug> --paper-dir <your paper repo>` keeps the Lean files with the
paper instead (`<repo>/formal/`, symlinked into the workspace).

## Faster iterations (optional)
- `scripts/lean_eval.sh` runs a snippet in ~7 s (light import preset); `scripts/trim_imports.py`
  shrinks a finished file's imports so later builds and checks load in seconds.
- `scripts/setup_env.sh --mcp` runs the `claude mcp add` registration of the `lean-lsp-mcp` server
  (needs `uv`); that server's documentation says it keeps Mathlib loaded between proof attempts.
  This option has not been tested from this skill.

## Growing the library
After a formalization, `scripts/promote_candidates.py CipherLean/<Slug>/Main.lean` lists the
declarations that are general enough for the shared library (class A/B/E/F) and those that are
not (toys, duplicates); the user decides, the agent moves them, `scripts/sync_library.sh` copies
the library back into this repository. Criteria and checklist: `references/promotion.md`.

## Contribute
Pull requests that add general lemmas to the library, fix scripts, or add an example are
welcome: see `CONTRIBUTING.md` (fork, develop in the workspace, `scripts/sync_library.sh`, PR with
the `check_lean.py` verdicts). The *Update* section above is only about refreshing your local copy.

## Review by a second agent
`references/review-brief.md` is the brief for an independent reviewer (a subagent or a second
session) that checks every Lean statement against the paper and the confirmed `CHAIN.md`. The
exchange is written down in `REVIEW.md`, round by round: the reviewer's numbered objections, the
formalizer's answer to each (`fixed` / `rejected` with a reason / `needs the user`), and the
reviewer's judgement of those answers in the next round; each round is also summarized in the
chat as it happens. Step 8 stops only when a round ends in ACCEPT and both check scripts pass.

## Layout
```
SKILL.md                 the workflow Claude follows (steps 0–8; 1b = proof chain confirmed by the reader, 7b = library promotion)
references/              cheatsheet of encodings + Mathlib lemma names, worked example,
                         workspace notes, survey of related tools
scripts/setup_env.sh     environment check / installer      scripts/check_lean.py  final check
scripts/new_paper.sh     scaffold a paper                   scripts/lake_build.sh  serialized build
scripts/search_mathlib.sh  local grep + Loogle + LeanSearch
scripts/lean_eval.sh     snippet runner (7 s)              scripts/trim_imports.py  minimal imports
scripts/chain_graph.py   proof chain -> TikZ graph (step 1b)   scripts/chain_check.py  chain vs. Lean dependencies
scripts/promote_candidates.py  what belongs in the library (step 7b)   scripts/sync_library.sh  workspace -> assets/lib
CONTRIBUTING.md          how to send a pull request
references/review-brief.md  instructions for the independent reviewer (step 8)
assets/workspace/        pinned lakefile, lean-toolchain, lake-manifest.json, Smoke.lean
assets/examples/         Feistel, Halfspace, SboxDDT, DdtInverse/ (complete run, with CHAIN.md + CHAIN.pdf)
assets/CHAIN-template.md the proof-chain table filled in step 1b
assets/lib/           shared library CipherLean (installed as CipherLean/Lib/, compiled by the installer)
```

## License
MIT, see `LICENSE`. The statements formalized in the examples are cited to their sources in the
file headers; the Lean code here is original.

## Trust model
Every result is reported with its axioms. The default is the standard three (`propext`,
`Classical.choice`, `Quot.sound`) with `decide +kernel` for finite computations. When a case the
paper settles by computation is too large for the kernel, `native_decide` is allowed under step 5b
of the workflow: a kernel-checked bridge lemma ties the Boolean program to the mathematical
statement, the declaration is reported as NATIVE, and the result is stated as proved relative to
the compiler axiom. Nothing general is ever closed with `native_decide`.

## Versions
Lean `v4.33.0`, Mathlib `v4.33.0` (commit `db584cd6`), pinned in `assets/workspace/`. Every
lemma name in the cheatsheet was compiled against this pin; see `references/workspace.md`
before changing it.
