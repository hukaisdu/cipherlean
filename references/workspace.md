# The `~/cipherlean` workspace

One Lake project for all formalizations, so Mathlib is built once (7 GB) and every paper
gets a subdirectory instead of its own 7 GB. Override the location with `CIPHERLEAN_WS`.

```
~/cipherlean/
├── lean-toolchain        leanprover/lean4:v4.33.0
├── lakefile.toml         package CipherLean, library CipherLean, autoImplicit = false
├── lake-manifest.json    Mathlib v4.33.0 = commit db584cd6d46c92f209a44c0f1c829460d327499d
├── CipherLean.lean       -> the skill's assets/workspace/CipherLean.lean: the umbrella `import CipherLean` (the library only, so an unfinished paper never blocks the others)
├── CipherLean/
│   ├── Smoke.lean        import Mathlib; one trivial theorem (tests the install)
│   ├── Examples/         compiled examples: Feistel, Halfspace, SboxDDT, DdtInverse/ (full run)
│   ├── Lib/              -> the skill's assets/lib: the shared library (F2/Vec, F2/Subspace, F2/Affine, Chi, Sbox, Walsh, DDT, LinStruct, Links) + README, NOTATION
│   └── <Slug>/           one paper: Main.lean (+ piece files), README.md, CHAIN.md (+ .pdf), NOTATION.md, REVIEW.md, PROMOTE.md
└── .lake/                build products + packages (Mathlib and its dependencies, 7 GB)
```

Created by `scripts/setup_env.sh --install` from `assets/workspace/` (the three pin files are
copied verbatim, so every installation uses the same Mathlib commit). Keep the workspace
outside folders that Dropbox, iCloud or Syncthing synchronize: `.lake/` holds about 6 GB of
build products. Paper files that must travel with the paper use the symlink scheme below.

## Setup

The installer's options (`--check`, `--check --smoke`, `--install`, `--examples`, `--build-from-source`,
`--update-library`, `--workspace DIR`, `--mcp`) are listed by `setup_env.sh --help`; the commands of the
workflow are in the table of `SKILL.md`. Downloads on a first install: toolchain ≈ 300 MB, shallow git clones of Mathlib and its eight
dependencies ≈ 170 MB (measured: 92 s; Lake accepts them and never re-clones), prebuilt oleans
≈ 2 GB (unpacked ≈ 6 GB). `lake exe cache get` keeps its download in `~/.cache/mathlib`, so a
second workspace with the same pin on the same machine unpacks instead of downloading.

## Modules, the lock, bare Lake

Module name = path with `/` → `.` and no `.lean`: `CipherLean/Foo/Main.lean` is `CipherLean.Foo.Main`.
A file imports a sibling with `import CipherLean.Foo.Defs`; build the sibling first (or build the
importing module, which builds its dependencies). One Lean job at a time in this workspace:
`lake_build.sh` and `check_lean.py` serialize themselves through `.lake/cipherlean-build.lock`
(macOS has no `flock`; the lock is a Python `fcntl.flock`). A bare `lake build` or `lake env lean <file>`
(a quick pass with no cache) bypasses it; `#print axioms <decl>` at the end of a file shows one theorem's
axioms without the check script. `decide` on 2^8–2^12 cases takes seconds, 2^16 and beyond is usually
hopeless (switch to a symbolic proof).

## What costs time, and the fast paths (measured 2026-11-01, Apple M-series laptop)

| operation | time | fast path |
|---|---|---|
| any Lean process starting with `import Mathlib` | ≈ 27 s before the first line is checked (maps 8322 oleans, 5.9 GB; I/O-bound) | `lean_eval.sh --light` preset ≈ 7 s; a file trimmed by `trim_imports.py` 3–7 s |
| `lake build` with nothing to do | ≈ 6 s (trace checks of the import closure) | fewer imports → fewer traces |
| `check_lean.py` | build + a second process that lists axioms: ≈ 1.5 min untrimmed, 7 s trimmed | trim imports first; `--no-build` right after a build |
| `decide +kernel` on `Finset.univ` of `Fin 2 → ZMod 2` with `ℚ` sums | tens of seconds | toys over `BitVec`; keep toys at 2–3 bits |
| four build-fix rounds of one proof | 4 × (27 s + proof time) | iterate with `lean_eval.sh` on the one lemma, build once |
| another Lean job on the same machine | everything 2–3× slower (I/O contention) | `lake_build.sh` queues builds in *this* workspace; other projects are outside its control |

`lean-lsp-mcp` is documented to remove the per-process load for the proving loop (its server keeps
Mathlib in memory and re-elaborates only the file). `setup_env.sh --mcp` runs its `claude mcp add`
registration (needs `uv` and the `claude` CLI); it is optional because it changes the user's Claude
configuration, and it has not been tested from this skill.

## Where the files live: two options

- **In the workspace** (`new_paper.sh` without options): `CipherLean/<Slug>/` is a real directory. Fine for
  experiments and for papers kept elsewhere.
- **With the paper** (`new_paper.sh` with `--paper-dir <paper repo>`): the real files are
  `<paper repo>/formal/{Main.lean,README.md,NOTATION.md}` and `CipherLean/<Slug>` is a symlink to
  that directory. Lake follows the symlink, so `lake build CipherLean.<Slug>.Main` works, and the
  paper repository carries the Lean source without carrying Mathlib. The check script accepts
  either path. In VS Code, open the file through the workspace path
  (`~/cipherlean/CipherLean/<Slug>/Main.lean`) so the Lean server knows which project it is in.

Publishing a paper's formalization as a standalone project later: copy `lean-toolchain`,
`lakefile.toml` (drop the other libraries) and `lake-manifest.json` next to the `formal/`
files, run `lake exe cache get` there; the files themselves need no change.

## Editing in VS Code

`File → Open Folder…` on `~/cipherlean`, with the Lean 4 extension installed
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
4. `lake build CipherLean.Smoke`, then rebuild each paper and fix renamed lemmas
   (`scripts/search_mathlib.sh` helps).
Mathlib ≥ v4.35 files may use the module system (`module`, `public import Mathlib`,
`public section`, as in Hadipour's tutorial); plain `import Mathlib` works on every version
and is what this workspace uses.

## Optional tools

- **lean-lsp-mcp** (goal states, diagnostics, multi-attempt, hover, Loogle/LeanSearch from
  inside Claude Code): `uv` required, then from the workspace root
  `claude mcp add lean-lsp -s user -e LEAN_PROJECT_PATH=$HOME/cipherlean -- uvx lean-lsp-mcp`.
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
| `maximum recursion depth has been reached` / very slow `decide` | the elaborator's limit, not the kernel's: `decide +kernel` (cheatsheet idiom 34), shrink the toy, or prove symbolically |
| `linarith failed to find a contradiction` (goal shown negated) | a hypothesis is missing from the context: `have h := lemma …` first |
| `motive is not type correct` in `rw` | rewrite inside dependent types; use `simp only [...]` or `conv` |
| `declaration uses 'sorry'` | expected while drafting; the check script fails on it |
| `'thm' depends on axioms: [thm._native.native_decide.ax_1_1]` (`bv_decide`: `thm._native.bv_decide.ax_*`; older toolchains: `Lean.ofReduceBool`) | `native_decide` / `bv_decide`: trusts the compiler; keep only in labelled finite checks |
| `error: … lake-manifest.json: name: expected a Name` | package names must be Lean identifiers (no hyphens) |
| `no default toolchain configured` | `elan default stable` (only affects files outside a project; this workspace pins its own) |
| Lake starts building thousands of Mathlib files | the pin changed or `.lake/packages` is gone: stop, restore the pin or run `lake exe cache get` |
| `elan: command not found` right after `--install`, or in a non-login ssh shell | `~/.elan/bin` is not on the PATH of this shell: open a new shell or `export PATH=$HOME/.elan/bin:$PATH`. The skill's scripts add it themselves (`setup_env.sh --check` says when it is missing), so only bare `lake` / `lean` commands of your own need it |
| `lake exe cache get` fails or stalls | network / proxy / GitHub access; rerun `setup_env.sh --install` (it resumes), or `--build-from-source` |
| `no such file: .lake/packages/mathlib` | the clone was interrupted: rerun `setup_env.sh --install` |
