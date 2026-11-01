# Independent review brief (the second agent)

Two agents, two jobs: the *formalizer* writes the Lean; the *reviewer* checks it against the paper
and against Lean, without having seen the formalizer's reasoning. This page is the reviewer's
instructions. The pattern comes from the skill's author, who ran it as two Claude Code sessions
(one formalizing Conjectures 1–4 of a paper, one checking them and matching them to the paper's
proofs) and stopped only when both sessions agreed; prove2me's "blind read-back" and
PaperFormalizer's referee stages do the same.

## You receive
- the paper source (`.tex` preferred) and the label of the theorem(s);
- the formalization directory: `README.md`, `CHAIN.md` (+ `CHAIN.pdf`), `NOTATION.md`, `Main.lean`
  (and any other `.lean`);
- the workspace path and `$SKILL/scripts/check_lean.py`.

You change nothing in that directory. You may build, run the check script, and compile scratch
files (`$SKILL/scripts/lean_eval.sh`). Your only output is `REVIEW.md` next to `README.md`.

## Procedure

1. **Statement fidelity, before reading any proof.** For every row of README's status table:
   copy the statement from the *paper source* (not from README); list its objects, hypotheses and
   conclusion; take the elaborated Lean statement from `check_lean.py` (section "Statements") or
   `#check`. Confirm, one by one: every paper hypothesis is present, either as a Lean hypothesis
   or by construction of the encoding (say which); no hypothesis was added except ones README
   declares as implicit-in-the-paper with a reason; the generality is the paper's (constants,
   ranges of quantifiers, coefficient field, block sizes) or every departure is in README's
   "Departures" section with a justification; the encodings in `NOTATION.md` mean what the paper's
   symbols mean (a coset is a coset, an annihilator is an annihilator, a probability is a count
   over the right set); the conclusion is the same formula. Then look for junk-value traps that
   make a statement true for the wrong reason: division (`x / 0 = 0`), `Nat` subtraction, empty
   types, `0 ^ 0`, a toy instance too small to exercise a hypothesis.
2. **Proof correspondence.** Start from `CHAIN.md` (the chain the reader confirmed): check every
   row against the paper (statement, location, `uses`), rerun
   `$SKILL/scripts/chain_check.py CHAIN.md Main.lean` and read its report: a missing edge is a
   proof step the paper has and Lean does not, an extra edge a dependency the chain hides; a
   `?`-marked edge is a route the paper takes and Lean does not, which must be explained in
   CHAIN.md and be sound. Where the paper cites an external result, name the Mathlib lemma used
   and compare hypotheses. The chain's `lean` column is the proof-correspondence table.
3. **Mechanical checks, yourself.** Run `check_lean.py` and record the verdict and axioms; grep
   for `sorry`, `native_decide`, `axiom`; confirm the finite checks test what README says (recompute
   the toy numbers from the definitions by hand or with `lean_eval.sh`; confirm each counterexample
   drops exactly one hypothesis and nothing else).
4. **Verdict.** Write `REVIEW.md`:
   ```
   # Review of <Slug> (round n, date)
   ## Statement fidelity      | paper statement | Lean declaration | OK / ISSUE | why |
   ## Proof correspondence    | paper step | Lean lemma | note |
   ## Checks                  check_lean verdict, axioms, greps, toy recomputation
   ## Objections              numbered; BLOCKER (statement unfaithful, proof gap, non-standard axiom),
                              MAJOR (departure or added hypothesis not recorded), MINOR (naming, docs)
   VERDICT: ACCEPT | REVISE
   ```
   `ACCEPT` only when the check script passes, every fidelity row is OK or a recorded departure,
   and the correspondence table is complete.

## The loop and its stopping condition
The formalizer fixes every BLOCKER and MAJOR, updates README, and asks for another round; a new
round reads the files afresh. Stop when a round ends in `ACCEPT` **and** `check_lean.py` passes.
After three rounds without `ACCEPT`, both agents stop and the open objections go to the user.
Run the reviewer with a fresh context (a subagent given this page and the inputs, or a second
Claude Code session); never let the formalizer review its own work in the same context.
