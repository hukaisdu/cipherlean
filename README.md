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
(the installer alone never overwrites files that already exist).

## Use
In Claude Code, inside a paper's directory: "formalize Theorem 2 of this paper in Lean",
"用 Lean 证明这个 lemma", "check whether the DDT row-sum identity holds for every S-box".
Claude runs the environment check, pins the statement in `README.md` + `NOTATION.md`, writes
`CipherLean/<Slug>/Main.lean`, proves it, and reports the status table. Results live in the
workspace; `new_paper.sh <Slug> --paper-dir <your paper repo>` keeps the Lean files with the
paper instead (`<repo>/formal/`, symlinked into the workspace).

## Faster iterations (optional)
- `scripts/lean_eval.sh` runs a snippet in ~7 s (light import preset); `scripts/trim_imports.py`
  shrinks a finished file's imports so later builds and checks load in seconds.
- `scripts/setup_env.sh --mcp` runs the `claude mcp add` registration of the `lean-lsp-mcp` server
  (needs `uv`); that server's documentation says it keeps Mathlib loaded between proof attempts.
  This option has not been tested from this skill.

## Review by a second agent
`references/review-brief.md` is the brief for an independent reviewer (a subagent or a second
session) that checks every Lean statement against the paper and writes `REVIEW.md`; the
workflow's step 8 stops only when the reviewer accepts and the check script passes.

## Layout
```
SKILL.md                 the workflow Claude follows (steps 0–7)
references/              cheatsheet of encodings + Mathlib lemma names, worked example,
                         workspace notes, survey of related tools
scripts/setup_env.sh     environment check / installer      scripts/check_lean.py  final check
scripts/new_paper.sh     scaffold a paper                   scripts/lake_build.sh  serialized build
scripts/search_mathlib.sh  local grep + Loogle + LeanSearch
scripts/lean_eval.sh     snippet runner (7 s)              scripts/trim_imports.py  minimal imports
references/review-brief.md  instructions for the independent reviewer (step 8)
assets/workspace/        pinned lakefile, lean-toolchain, lake-manifest.json, Smoke.lean
assets/examples/         Feistel, Halfspace, SboxDDT, DdtInverse/ (complete run)
assets/lib/           shared library CipherLean (installed as CipherLean/Lib/, compiled by the installer)
```

## License
MIT, see `LICENSE`. The statements formalized in the examples are cited to their sources in the
file headers; the Lean code here is original.

## Versions
Lean `v4.33.0`, Mathlib `v4.33.0` (commit `db584cd6`), pinned in `assets/workspace/`. Every
lemma name in the cheatsheet was compiled against this pin; see `references/workspace.md`
before changing it.
