# <Slug> — formalization of <Theorem label> from <paper>

## Source
- Paper: <authors>, "<title>", <venue / ePrint ID>, <year>. File used: `<path>`.
- Statement: <Theorem X.Y>, page <n>.
- (No paper: write "source: the user's statement, quoted below" and skip the literature hunt.)

## Statement (verbatim)
> ...

## Objects, hypotheses, conclusion
| object / hypothesis | in the paper | explicit or implicit | Lean |
|---|---|---|---|
| `E` is a permutation of the state | "let E be a block cipher" | implicit | `hE : Function.Bijective E` |

## Proof plan
| step | paper argument | Lean lemma |
|---|---|---|
| 1 | split the sum over the two halfspaces | `linearSum_eq_sub` |

## Finite checks
- Toy instance: ...
- Counterexamples: ...

## Status
| paper label | Lean declaration | status | axioms | note |
|---|---|---|---|---|
| Theorem X.Y | `<Slug>.main` | proved / sorry (reason) | propext, Classical.choice, Quot.sound | |

## Departures from the paper
- (generality, encoding, added hypotheses, readings of ambiguous passages)

## Rebuild
```
cd ~/cipherlean && ~/.claude/skills/cipherlean/scripts/lake_build.sh CipherLean.<Slug>.Main && ~/.claude/skills/cipherlean/scripts/check_lean.py CipherLean/<Slug>/Main.lean
```
