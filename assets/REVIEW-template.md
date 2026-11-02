# REVIEW — <Slug>: the formalizer ↔ reviewer record

One file for the whole review; rounds are appended in order and nothing is deleted or rewritten.
The reviewer writes the `reviewer` section of a round after reading the files afresh; the
formalizer answers every objection in writing in the `formalizer` section before the next round
starts; the next reviewer section begins by judging those answers. Objections are numbered
`R<round>.<k>` and keep their number for life, so the reader can follow one objection across rounds.

Severity: BLOCKER (statement unfaithful, proof gap, non-standard axiom, chain inconsistent) ·
MAJOR (departure or added hypothesis not recorded, missing finite check) · MINOR (naming, docs).
Response: `fixed` (what changed, where) · `rejected` (a reason the reviewer can check) ·
`needs the user` (a question only the user can answer; it goes to the user before the next round).

## Round 1 — reviewer (<date>)

### Statement fidelity
The Lean column is pasted from `check_lean.py`'s "Statements" section (never retyped); one row per declaration
of README's status table.
| paper statement | Lean declaration and statement (pasted) | OK / ISSUE | why |
|---|---|---|---|
| | | | |

### Proof correspondence (CHAIN.md rows and `chain_check.py`)
| chain row | Lean declaration | in Lean: direct / transitive / paper's route / MISSING | note |
|---|---|---|---|
| | | | |

### Checks
- `check_lean.py`: <verdict, axioms>
- `chain_check.py`: <verdict>
- greps (`sorry`, `native_decide`, `axiom`): <result>
- toy numbers recomputed: <result>

### Objections
| id | severity | where | objection |
|---|---|---|---|
| R1.1 | | | |

VERDICT: REVISE

## Round 1 — formalizer (<date>)

| id | response | what changed / why not | declarations changed or added |
|---|---|---|---|
| R1.1 | fixed / rejected / needs the user | | `<Slug>.foo`, `<Slug>.bar` |

## Round 2 — reviewer (<date>)

From round 2 on the reviewer re-examines only the declarations the formalizer's answers list as changed or
added (statement fidelity and proof correspondence for those rows, pasted from the new `check_lean.py` run),
judges every answer, and reruns the two checks; unchanged rows are not re-tabulated.

### Previous objections
| id | status | note |
|---|---|---|
| R1.1 | resolved / still open / superseded | |

### Changed or added declarations (from the formalizer's answers)
| declaration | statement (pasted from `check_lean.py`) | OK / ISSUE | why |
|---|---|---|---|
| | | | |

### Checks
- `check_lean.py`: <verdict> · `chain_check.py`: <verdict>

### New objections
| id | severity | where | objection |
|---|---|---|---|
| R2.1 | | | |

VERDICT: ACCEPT | REVISE

## Outcome

Rounds: <n>. Final verdict: <ACCEPT | stopped after 3 rounds>. Open items for the user: <list or none>.
