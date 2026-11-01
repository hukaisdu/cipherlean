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

- `REVIEW.md` if it exists (the earlier rounds, including the formalizer's written answers).

You change nothing in that directory except `REVIEW.md`. You may build, run the check scripts,
and compile scratch files (`$SKILL/scripts/lean_eval.sh`). Your only output is a new
`## Round n — reviewer` section appended to `REVIEW.md` (created from
`$SKILL/assets/REVIEW-template.md` in round 1); earlier sections are never edited.

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
   drops exactly one hypothesis and nothing else). For every NATIVE declaration (step 5b): the
   computation must be a closed decidable statement, a kernel-checked bridge lemma must connect
   `checker = true` to the mathematical statement, the kernel route must have been tried or shown
   infeasible, and README must disclose the axiom; a `native_decide` on a general goal is a BLOCKER.
4. **Verdict.** Append `## Round n — reviewer (<date>)` to `REVIEW.md` with the sections of the
   template: in round n > 1 first a `Previous objections` table that judges every answer of the
   formalizer (`resolved` / `still open` with the reason / `superseded`), then statement fidelity,
   proof correspondence, checks, and `New objections`. Objections are numbered `R<n>.<k>`, each
   with a severity (BLOCKER: statement unfaithful, proof gap, non-standard axiom, chain
   inconsistent · MAJOR: departure or added hypothesis not recorded, missing finite check · MINOR:
   naming, docs) and a location (file:line or chain row). End with `VERDICT: ACCEPT | REVISE`.
   `ACCEPT` only when both check scripts pass, every fidelity row is OK or a recorded departure,
   the correspondence is complete, and no BLOCKER or MAJOR is still open.

## The loop and its stopping condition
Between rounds the formalizer appends `## Round n — formalizer (<date>)`: one row per objection,
`fixed` (what changed, where), `rejected` (a reason the reviewer can check) or `needs the user`
(the question goes to the user before the next round). No next round starts until every
objection of the previous round has a written answer, and the agent running the loop posts the
round's objections and answers in the chat, so the exchange is visible as it happens and
`REVIEW.md` is its complete record afterwards. A new round reads the files afresh. Stop when a
round ends in `ACCEPT` **and** `check_lean.py` and `chain_check.py` pass; write the `## Outcome`
section. After three rounds without `ACCEPT`, both agents stop and the open objections go to the
user. Run the reviewer with a fresh context (a subagent given this page and the inputs, or a
second Claude Code session); never let the formalizer review its own work in the same context.
