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
| paper statement | Lean declaration | OK / ISSUE | why |
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

| id | response | what changed / why not |
|---|---|---|
| R1.1 | fixed / rejected / needs the user | |

## Round 2 — reviewer (<date>)

### Previous objections
| id | status | note |
|---|---|---|
| R1.1 | resolved / still open / superseded | |

### New objections
| id | severity | where | objection |
|---|---|---|---|
| R2.1 | | | |

VERDICT: ACCEPT | REVISE

## Outcome

Rounds: <n>. Final verdict: <ACCEPT | stopped after 3 rounds>. Open items for the user: <list or none>.
