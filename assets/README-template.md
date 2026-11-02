# <Slug> — formalization of <Theorem label> from <paper>

## Source
- Paper: <authors>, "<title>", <venue / ePrint ID>, <year>. File used: `<path>`. Statement: <Theorem X.Y>, page <n>.
  (No paper: "source: the user's statement, quoted below", no literature hunt.)
- Files: `Main.lean` (+ one file per piece), `CHAIN.md` + `CHAIN.pdf` (chain, graph, roadmap), `NOTATION.md` (every
  symbol and its Lean name), `REVIEW.md` (the review rounds), `PROMOTE.md` (library candidates).

## Statement (verbatim)
> ...

## Hypotheses
Objects and their encodings are in `NOTATION.md`; the proof's steps are the rows of `CHAIN.md`. Here only what
the theorem assumes, explicit or implicit, and the Lean hypothesis that carries it.

| hypothesis | in the paper | explicit or implicit | Lean |
|---|---|---|---|
| `E` is a permutation of the state | "let E be a block cipher" | implicit | `hE : Function.Bijective E` |

## Finite checks
One line per check: the declaration and the number it pins (the narration is the declaration's docstring).
- Toy: `toy_values` — `ddt toyS 1 2 = 4`, `ddt toyS 2 1 = 0` (Python beforehand: `check_toy.py`, this directory).
- Counterexample for <hypothesis>: `toy_not_symmetric` — the conclusion fails for <the object that drops it>.

## Status
<date>: `check_lean.py` VERDICT: PASS (n declarations, standard axioms) · `chain_check.py` CONSISTENT ·
`notation_check.py` OK · review round <n> ACCEPT. `status.py <Slug>` prints the live board.

| paper label | Lean declaration | status | axioms | note |
|---|---|---|---|---|
| Theorem X.Y | `<Slug>.main` | proved / sorry (reason) | standard | under `hE` |

`standard` = `propext`, `Classical.choice`, `Quot.sound`; name every other axiom (a `native_decide` finite check).

## Departures from the paper
- (generality, encoding, added hypotheses, readings of ambiguous passages)

## Roadmap
The plan (end, pieces, routes, sizes) is the Roadmap table of `CHAIN.md`; this section records the position
at every stop (the chain gate, the end of each piece, each budget stop): paste `status.py <Slug> --position`
under a dated heading, newest last, so the reader sees how the estimates met the actuals.

### <date> — <after the chain gate / after piece A / budget stop in piece B>
<the Position block>

## Rebuild
```
cd ~/cipherlean && ~/.claude/skills/cipherlean/scripts/lake_build.sh CipherLean.<Slug>.Main && ~/.claude/skills/cipherlean/scripts/check_lean.py CipherLean/<Slug>/Main.lean --no-build && ~/.claude/skills/cipherlean/scripts/chain_check.py CipherLean/<Slug>/CHAIN.md CipherLean/<Slug>/Main.lean
```
