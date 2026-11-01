# Contributing to cipherlean

The shared library `CipherLean` grows one paper at a time: when a formalization proves something
general about library objects, that lemma moves into `assets/lib/` and ships with the next
version. Pull requests that do exactly that are the contributions this repository wants.

## What a library contribution contains
- The declaration in the right module (`assets/lib/F2/Vec.lean`, `F2/Subspace.lean`, `Sbox.lean`,
  `Walsh.lean`, `DDT.lean`, `Links.lean`, or a new module imported from `assets/workspace/CipherLean.lean`),
  stated over the library carrier `Vec ι` with the library's names, with a docstring naming the
  source (paper, venue or ePrint number) — see `references/promotion.md` for the criteria.
- A finite check for every new definition (a toy where it computes the expected number).
- A row in `assets/lib/NOTATION.md` and in the module table of `assets/lib/README.md`.
- Evidence in the PR description: `check_lean.py` verdict PASS for every touched module (no `sorry`,
  standard axioms only; `native_decide` only in labelled finite checks), `trim_imports.py` applied
  if imports changed. The maintainers rerun both.

## Workflow
1. Fork and clone the repository to `~/.claude/skills/cipherlean`, run
   `scripts/setup_env.sh --install` once (workspace `~/cipherlean`).
2. Develop in the workspace: edit `~/cipherlean/CipherLean/Lib/…`, build with
   `scripts/lake_build.sh CipherLean`, check with `scripts/check_lean.py`.
3. Copy the library back into the repository with `scripts/sync_library.sh` (it copies
   `~/cipherlean/CipherLean/Lib` over `assets/lib` and shows the diff), commit on a branch, push,
   open a pull request against `main`.
4. Keep the Lean/Mathlib pin (`assets/workspace/lean-toolchain`, `lake-manifest.json`); version
   bumps are separate PRs that rebuild everything (`references/workspace.md`). Pin releases, never
   release candidates: a project pinned to an `-rc` cannot be verified on a machine that has only
   the release, and the two were 417 commits apart in the case that taught this.

Skill-side contributions (scripts, references, examples) follow the same route; an example must
compile in the workspace and be listed in `setup_env.sh`'s example build.

Unpublished results do not belong in the library: a paper's main theorem stays in its own
`CipherLean/<Slug>/` directory until the paper is public.

By contributing you agree that your contribution is licensed under the repository's MIT license.
