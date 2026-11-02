# CHAIN — <Slug>: the proof chain of <theorem label>, for the reader to confirm before any Lean

Target: `<id of the target theorem>` (paper label, section, page). Read the table from the target
down to the definitions and the cited results. Every row is one thing the proof relies on; `uses`
are the rows it relies on directly. Please confirm, correct, or add rows; nothing is formalized
until this table and the graph below are confirmed.

## Nodes

| id | kind | title | statement | uses | where | implicit | lean | status |
|---|---|---|---|---|---|---|---|---|
| thm:<label> | theorem | <three words> | <verbatim statement> | lem:<a>, step:<b> | §<n>.<m> Theorem <k> (<label>), p. <q>; <notes> | — | — | pending |
| lem:<a> | lemma | <three words> | <statement> | def:<x>, ext:<y> | §<n>.<m> Lemma <k> (<label>); eq. (<k>) | <hypothesis the proof uses silently, or —> | — | pending |
| step:<b> | step | <three words> | <what this proof step claims> | def:<x> | §<n>.<m> proof of <label>; line "<first words>" | — | — | pending |
| def:<x> | def | <three words> | <definition as the paper states it> | — | §<n>.<m> <name> | — | — | pending |
| ext:<y> | external | <three words> | <the cited result, checked in its own source> | — | [<author year>, Thm <k>]; <where our paper cites it> | <conditions the citing sentence omits> | — | cited |
| assume:<z> | assumption | <three words> | <modelling assumption or hypothesis of the theorem> | — | §<n>.<m> | — | — | assumed |

`kind`: theorem · lemma · step (one step of a proof) · def · external (cited result, checked in its
own source) · assumption (a hypothesis of the theorem or a modelling assumption stated as such).
`uses`: comma-separated ids. `where`: the paper's section and statement first (`§7.3 Lemma 24 (lem:…)`),
then `;` and notes — the graph prints the part before the `;` under each node, and the H1 line of this
file is the graph's title, so it names the paper; rows from another paper say that paper first.
`implicit`: a hypothesis the text uses without stating, or `—`.
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
