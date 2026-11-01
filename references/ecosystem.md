# Existing Lean 4 tooling, and what this skill borrows (surveyed 2026-11-01)

Nothing found does symmetric-key cryptanalysis statistics (Walsh/DDT/divisibility) in Lean;
that gap is what `lean-crypto-cheatsheet.md` and the examples fill. The pieces below are
worth borrowing or reaching for.

## Whole-paper pipelines (hand a paper over, get a Lean project back)

| tool | what it is | notes |
|---|---|---|
| [Tex2Lean](https://github.com/meelgroup/tex2lean-releases) (Meel group) | CLI: `tex2lean connect / setup / scan / targets / plan t1 / prove t1 / all` in the folder with the `.tex` files; providers `claude-cli`, `codex-cli`, `openrouter` | aimed at algorithm papers (Hadipour's blog); PDF input needs `pdftotext`/`mutool`; one run per project at a time |
| [PaperFormalizer](https://github.com/Jiyuan-Tan/PaperFormalizer) (Tan–Blanchet–Syrgkanis, arXiv 2610.31810) | stages V1 transcription → V1.5 faithfulness / ambiguity / correctness check (no Lean) → F1–F5 plan, scaffold, proofs, reviews → V6 report; author decides every change that weakens a result | LaTeX only ("never the PDF"); pins Lean v4.33.0 + Mathlib `db584cd` (same as our workspace); runs take hours to days; non-OSI "responsible use" licence |
| [autoform-bot](https://github.com/facebookresearch/autoform-bot) (Meta FAIR, MIT) | Claude Code / Codex plugin: `/autoform:setup`, `roadmap`, `formalize`, `human-review`, `agent-review`; roadmap + dependency graph as Markdown "blueprint" | built for books/long texts; Lean ≥ 4.27; several sessions coordinate through git refs |
| LeanMarathon (arXiv 2606.05400) | research harness formalizing whole papers | paper, not a tool |

When the user wants a *whole* paper formalized and accepts the cost, run Tex2Lean or
PaperFormalizer and then apply this skill's step 6–7 (axiom check, statement comparison,
report) to their output. For one theorem at a time, this skill is cheaper and keeps the user
in control of the statement.

## Claude Code skills for Lean (same host as this skill)

| skill | borrowed idea |
|---|---|
| [lean4-skills](https://github.com/cameronfreer/lean4-skills) (MIT): `draft / formalize / autoformalize / prove / autoprove / disprove / checkpoint / review / refactor / golf` | the loop *plan → work → checkpoint → review → replan*; headers frozen while proving; `disprove` = certified counterexample; `checkpoint` = build + axiom check + commit |
| [lean-skills](https://github.com/matt-w-horn/lean-skills) (Apache-2.0): seven skills incl. `lean-verification`, `lean-latex-sync`, `loogle` | "a statement that does not mean what its author intended compiles perfectly": junk-value and vacuity checks (`x / 0 = 0`), keep paper prose and Lean statements in sync |
| [mathproof-skill](https://github.com/Ztang-Yit-Xiaang/mathproof-skill) (MIT) | `lean_check.py`: compile, no `sorry`, only `propext / Classical.choice / Quot.sound`, no `native_decide`; prints each elaborated statement for comparison; a `sorry` hidden in a macro is caught by the axiom check → our `check_lean.py` |
| [mathlib-quality](https://github.com/CBirkbeck/mathlib-quality) | `/cleanup`, `/mathlibable`, `/bump-mathlib`: polishing after the proof is done |
| [dbenbenn/claude-skills-public](https://github.com/dbenbenn/claude-skills-public) (prove2.me) | fidelity = the paper's constants, generality and definitions, never a convenient variant; read the cited proposition, not the summarizing sentence; blind read-back of each statement by an agent that sees only the declaration |
| [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (DeepMind) | every statement carries a docstring with the English version and a `*Reference:*` link; one problem per file; no placeholder definitions (`def foo : Type := sorry`); bespoke definitions need API tests |

## Interaction infrastructure

- [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp): MCP server over the Lean
  language server (`lean_goal`, `lean_multi_attempt`, `lean_run_code`, `lean_local_search`,
  `lean_verify`, LeanSearch/Loogle/Lean Finder/Lean Hammer); `claude mcp add lean-lsp uvx
  lean-lsp-mcp` from the project root; beta; Loogle limited to 3 requests / 30 s.
- [Lean REPL](https://github.com/leanprover-community/repl): `{"cmd": ...}` / `{"tactic":
  ..., "proofState": n}` JSON protocol, reports `sorries` and goals, can pickle
  environments; `lean-interact` (PyPI) wraps it in Python; LeanDojo and Pantograph are
  the heavier research alternatives.
- Search: [Loogle](https://loogle.lean-lang.org) (by name / type pattern, JSON API),
  [LeanSearch](https://leansearch.net) (natural language, POST API), local `grep` over
  `.lake/packages/mathlib` — all three in `scripts/search_mathlib.sh`.

## Neural provers (not used by this skill)

DeepSeek-Prover ([V1.5 repo](https://github.com/deepseek-ai/DeepSeek-Prover-V1.5)),
[OpenProver](https://github.com/kripner/OpenProver) (CICM 2026, agentic), Gödel's Poetry,
Pythagoras-Prover-32B: open models or harnesses for competition-style proving. Our
statements are small and bespoke; a general LLM with `exact?` / search and the check script
has been enough. Revisit if a lemma resists for hours.

## Cryptography in Lean 4

- [VCVio](https://github.com/Verified-zkEVM/VCV-io) (Devon Tuma, ePrint 2026/899): game-based
  provable security via an oracle-computation monad; lattice schemes, hash-based
  signatures, Schnorr / forking lemma. [ArkLib](https://github.com/Verified-zkEVM/ArkLib)
  builds SNARK formalizations on it. Relevant if a reduction or a security game is to be
  formalized; irrelevant for distinguisher statistics.
- Nothing found for Boolean-function cryptanalysis (Walsh spectrum, DDT/LAT, differential
  uniformity, division property). Mathlib provides the building blocks (`Finset.sum`,
  `ZMod 2`, `BitVec`, `Fintype`); the cheatsheet records the encodings that compiled.
