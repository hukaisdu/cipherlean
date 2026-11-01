# CHAIN — <Slug>: the proof chain of <theorem label>, for the reader to confirm before any Lean

Target: `<id of the target theorem>` (paper label, section, page). Read the table from the target
down to the definitions and the cited results. Every row is one thing the proof relies on; `uses`
are the rows it relies on directly. Please confirm, correct, or add rows; nothing is formalized
until this table and the graph below are confirmed.

## Nodes

| id | kind | title | statement | uses | where | implicit | lean | status |
|---|---|---|---|---|---|---|---|---|
| thm:<label> | theorem | <three words> | <verbatim statement> | lem:<a>, step:<b> | §<n> p.<m> | — | — | pending |
| lem:<a> | lemma | <three words> | <statement> | def:<x>, ext:<y> | §<n> eq. (<k>) | <hypothesis the proof uses silently, or —> | — | pending |
| step:<b> | step | <three words> | <what this proof step claims> | def:<x> | proof of <label>, line "<first words>" | — | — | pending |
| def:<x> | def | <three words> | <definition as the paper states it> | — | §<n> | — | — | pending |
| ext:<y> | external | <three words> | <the cited result, checked in its own source> | — | [<author year>, Thm <k>] | <conditions the citing sentence omits> | — | cited |
| assume:<z> | assumption | <three words> | <modelling assumption or hypothesis of the theorem> | — | §<n> | — | — | assumed |

`kind`: theorem · lemma · step (one step of a proof) · def · external (cited result, checked in its
own source) · assumption (a hypothesis of the theorem or a modelling assumption stated as such).
`uses`: comma-separated ids. `implicit`: a hypothesis the text uses without stating, or `—`.
`lean`: the Lean declaration that discharges the row (filled in step 3; a library lemma is allowed).
A row the paper settles by computation says so in `implicit` ("computation: 2^12 cases") and, once
formalized, names the route in `lean` (`decide +kernel`, or the `checker_eval` of a native bridge).
`status`: pending · stated (Lean statement with `sorry`) · proved · cited · assumed.

## External results

For every `ext:` row: the source, the exact statement there, and what differs from the paper's
quotation of it.

## Implicit hypotheses found

One line each; these become named hypotheses in Lean and findings in the report.

## Questions for the reader

Ambiguities in the text, places where two readings differ, constants or conventions to fix.

## Dependency graph

`$SKILL/scripts/chain_graph.py CHAIN.md` writes `CHAIN.tex` (TikZ) and compiles `CHAIN.pdf`; the
mermaid version below is kept in sync by the same script.

<!-- chain-graph:begin -->
<!-- chain-graph:end -->
