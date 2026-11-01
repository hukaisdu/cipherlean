# The `~/lean-formal` workspace

One Lake project for all formalizations, so Mathlib is built once (7 GB) and every paper
gets a subdirectory instead of its own 7 GB. Override the location with `LEAN_FORMAL_WS`.

```
~/lean-formal/
├── lean-toolchain        leanprover/lean4:v4.33.0
├── lakefile.toml         package LeanFormal, library Formal, autoImplicit = false
├── lake-manifest.json    Mathlib v4.33.0 = commit db584cd6d46c92f209a44c0f1c829460d327499d
├── Formal.lean           empty root module (so an unfinished paper never blocks the others)
├── Formal/
│   ├── Smoke.lean        import Mathlib; one trivial theorem (tests the install)
│   ├── Examples/         compiled examples: Feistel, Halfspace, SboxDDT, DdtInverse/ (full run)
│   ├── Crypto/           shared library (Vec, Subspace, Walsh, DDT, Links, Sbox) + README, NOTATION
│   ├── Crypto.lean       umbrella module: `import Formal.Crypto`
│   └── <Slug>/           one paper: Main.lean (+ more files), README.md, NOTATION.md
└── .lake/                build products + packages (Mathlib and its dependencies, 7 GB)
```

Created by `scripts/setup_env.sh --install` from `assets/workspace/` (the three pin files are
copied verbatim, so every installation uses the same Mathlib commit). Keep the workspace
outside folders that Dropbox, iCloud or Syncthing synchronize: `.lake/` holds about 6 GB of
build products. Paper files that must travel with the paper use the symlink scheme below.

## Setup and checks

| command | what it does |
|---|---|
| `setup_env.sh --check` | OK / MISSING per item, changes nothing (2 s) |
| `setup_env.sh --check --smoke` | also builds `Formal/Smoke.lean` (10–40 s) |
| `setup_env.sh --install` | installs elan (official installer), the toolchain, the workspace, the prebuilt Mathlib (`lake exe cache get`), the examples; then smoke build + `check_lean.py` |
| `setup_env.sh --install --examples` | also compiles the examples |
| `setup_env.sh --install --build-from-source` | if the cache download keeps failing: compile Mathlib (hours) |
| `--workspace DIR` / `LEAN_FORMAL_WS` | use another location |

Downloads on a first install: toolchain ≈ 300 MB, shallow git clones of Mathlib and its eight
dependencies ≈ 170 MB (measured: 92 s; Lake accepts them and never re-clones), prebuilt oleans
≈ 2 GB (unpacked ≈ 6 GB). `lake exe cache get` keeps its download in `~/.cache/mathlib`, so a
second workspace with the same pin on the same machine unpacks instead of downloading.

## Commands (run from the workspace root)

| what | command |
|---|---|
| compile one module (preferred) | `~/.claude/skills/cipherlean/scripts/lake_build.sh Formal.<Slug>.Main` (`lake build` under the workspace lock) |
| quick pass on a file, no cache | `lake env lean Formal/<Slug>/Main.lean` |
| axioms of one theorem | add `#print axioms <Slug>.main` to the file, or run the check script |
| full check (build + axioms + statements) | `~/.claude/skills/cipherlean/scripts/check_lean.py Formal/<Slug>/Main.lean` |
| find a lemma | `~/.claude/skills/cipherlean/scripts/search_mathlib.sh "<query>"` |
| new paper | `~/.claude/skills/cipherlean/scripts/new_paper.sh <Slug> [--paper-dir <dir>]` |

Module name = path with `/` → `.` and no `.lean`: `Formal/Foo/Main.lean` is `Formal.Foo.Main`.
A file imports a sibling with `import Formal.Foo.Defs`; build the sibling first (or build the
importing module, which builds its dependencies). One Lean job at a time in this workspace:
`lake_build.sh` and `check_lean.py` serialize themselves through `.lake/formal-build.lock`
(macOS has no `flock`; the lock is a Python `fcntl.flock`). A bare `lake build` bypasses it. Loading Mathlib takes ~30 s the first time per process; `decide` on 2^8–2^12
cases takes seconds, 2^16 and beyond is usually hopeless (switch to a symbolic proof).

## What costs time, and the fast paths (measured 2026-11-01, Apple M-series laptop)

| operation | time | fast path |
|---|---|---|
| any Lean process starting with `import Mathlib` | ≈ 27 s before the first line is checked (maps 8322 oleans, 5.9 GB; I/O-bound) | `lean_eval.sh --light` preset ≈ 7 s; a file trimmed by `trim_imports.py` 3–7 s |
| `lake build` with nothing to do | ≈ 6 s (trace checks of the import closure) | fewer imports → fewer traces |
| `check_lean.py` | build + a second process that lists axioms: ≈ 1.5 min untrimmed, 7 s trimmed | trim imports first; `--no-build` right after a build |
| `decide +kernel` on `Finset.univ` of `Fin 2 → ZMod 2` with `ℚ` sums | tens of seconds | toys over `BitVec`; keep toys at 2–3 bits |
| four build-fix rounds of one proof | 4 × (27 s + proof time) | iterate with `lean_eval.sh` on the one lemma, build once |
| another Lean job on the same machine | everything 2–3× slower (I/O contention) | `lake_build.sh` queues builds in *this* workspace; other projects are outside its control |

`lean-lsp-mcp` removes the per-process load entirely for the proving loop (the server keeps
Mathlib in memory and re-elaborates only the file; goal states and diagnostics come back in
seconds). `setup_env.sh --mcp` registers it for Claude Code (needs `uv` and the `claude` CLI);
it is optional because it changes the user's Claude configuration.

## Where the files live: two options

- **In the workspace** (`new_paper.sh <Slug>`): `Formal/<Slug>/` is a real directory. Fine for
  experiments and for papers kept elsewhere.
- **With the paper** (`new_paper.sh <Slug> --paper-dir <paper repo>`): the real files are
  `<paper repo>/formal/{Main.lean,README.md,NOTATION.md}` and `Formal/<Slug>` is a symlink to
  that directory. Lake follows the symlink, so `lake build Formal.<Slug>.Main` works, and the
  paper repository carries the Lean source without carrying Mathlib. The check script accepts
  either path. In VS Code, open the file through the workspace path
  (`~/lean-formal/Formal/<Slug>/Main.lean`) so the Lean server knows which project it is in.

Publishing a paper's formalization as a standalone project later: copy `lean-toolchain`,
`lakefile.toml` (drop the other libraries) and `lake-manifest.json` next to the `formal/`
files, run `lake exe cache get` there; the files themselves need no change.

## Editing in VS Code

`File → Open Folder…` on `~/lean-formal`, with the Lean 4 extension installed
(https://lean-lang.org/install/). The Infoview (Cmd+Shift+Enter) shows the goal after `⊢`
at the cursor; a proof is done when "No goals" appears. Unicode: `\to`, `\forall`, `\sum`,
`\mid` (∣), `\N`, `\Z`, `\ne`, `\and`, `\xor` is typed as `^^^` for `BitVec`.

## Versions and upgrading

Lean and Mathlib must match (Mathlib tags `v4.X.0` track Lean `v4.X.0`). The whole
workspace shares one pin; do not change it in the middle of a paper. To upgrade:
1. edit `lean-toolchain` and the `rev` in `lakefile.toml` to the same `v4.Y.0`;
2. `lake update mathlib` (rewrites the manifest; elan downloads the toolchain);
3. `lake exe cache get` (downloads the prebuilt Mathlib, several GB, into `~/.cache/mathlib`
   and unpacks it; without this step Lake compiles Mathlib for hours);
4. `lake build Formal.Smoke`, then rebuild each paper and fix renamed lemmas
   (`scripts/search_mathlib.sh` helps).
Mathlib ≥ v4.35 files may use the module system (`module`, `public import Mathlib`,
`public section`, as in Hadipour's tutorial); plain `import Mathlib` works on every version
and is what this workspace uses.

## Optional tools

- **lean-lsp-mcp** (goal states, diagnostics, multi-attempt, hover, Loogle/LeanSearch from
  inside Claude Code): `uv` required, then from the workspace root
  `claude mcp add lean-lsp -s user -e LEAN_PROJECT_PATH=$HOME/lean-formal -- uvx lean-lsp-mcp`.
  Not installed by default; the `lake build` + check-script loop needs nothing extra.
- **Lean REPL** (`leanprover-community/repl`): JSON in / JSON out, tactic mode, useful for
  scripted proof search. Build it as its own project, run `lake env <path>/repl` from here.
- **Tex2Lean / PaperFormalizer / autoform-bot** for whole papers: see `ecosystem.md`.

## Errors seen and what they mean

| message | cause / fix |
|---|---|
| `unknown identifier 'Foo.bar'` | wrong lemma name or missing import; search, or `import Mathlib` |
| `unknown constant` on a variable | `autoImplicit = false`: declare `{n : ℕ}` or `(x : α)` |
| `failed to synthesize Decidable …` | `decide` needs a decidable proposition: use `Fintype` quantifiers, `DecidableEq`, or `classical` + a symbolic proof |
| `maximum recursion depth has been reached` / very slow `decide` | instance too large; use `decide +kernel`, shrink the toy, or prove symbolically |
| `linarith failed to find a contradiction` (goal shown negated) | a hypothesis is missing from the context: `have h := lemma …` first |
| `motive is not type correct` in `rw` | rewrite inside dependent types; use `simp only [...]` or `conv` |
| `declaration uses 'sorry'` | expected while drafting; the check script fails on it |
| `'thm' depends on axioms: [Lean.ofReduceBool]` | `native_decide` / `bv_decide`: trusts the compiler; keep only in labelled finite checks |
| `error: … lake-manifest.json: name: expected a Name` | package names must be Lean identifiers (no hyphens) |
| `no default toolchain configured` | `elan default stable` (only affects files outside a project; this workspace pins its own) |
| Lake starts building thousands of Mathlib files | the pin changed or `.lake/packages` is gone: stop, restore the pin or run `lake exe cache get` |
| `elan: command not found` right after `--install` | `~/.elan/bin` is not on the PATH of this shell yet: open a new shell or `export PATH=$HOME/.elan/bin:$PATH` |
| `lake exe cache get` fails or stalls | network / proxy / GitHub access; rerun `setup_env.sh --install` (it resumes), or `--build-from-source` |
| `no such file: .lake/packages/mathlib` | the clone was interrupted: rerun `setup_env.sh --install` |
