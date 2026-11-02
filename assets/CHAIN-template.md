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
`uses`: comma-separated ids; `id?` marks a premise the paper relies on that the Lean declaration of this row does not
use (the paper's route where Lean goes another way, or a step whose Lean form is a self-contained finite check whose
premises enter where the target applies it) — explained in `implicit`, accepted by `chain_check.py`. `where`: the paper's section and statement first (`§7.3 Lemma 24 (lem:…)`),
then `;` and notes — the graph prints the part before the `;` under each node, and the H1 line of this
file is the graph's title, so it names the paper; rows from another paper say that paper first.
`implicit`: a hypothesis the text uses without stating, or `—`. Cells stay short — `statement` at most 300
characters, `implicit` at most 200 — so the table reads and the graph's labels fit; anything longer (how the
paper argues, what Lean does instead, why an edge is `?`) goes under "Notes" below, keyed by the row id.
`lean`: the one Lean declaration of this formalization that discharges the row (filled in step 3; a library
lemma is allowed), or `—`; a note about another project's declaration goes in `implicit` (a cell that is
not one name is listed by `chain_check.py` as a note and not checked).
A row the paper settles by computation says so in `implicit` ("computation: 2^12 cases") and, once
formalized, names the route in `lean` (`decide +kernel`, or the `checker_eval` of a native bridge).
`status`: pending · stated (Lean statement with `sorry`) · proved · cited · assumed.

## Notes (by row id)

- `lem:<a>`: <the long explanation that does not fit the cell: the paper's argument, the Lean route, the reason for a `?`>

## External results

For every `ext:` row: the source, the exact statement there, and what differs from the paper's
quotation of it.

## Implicit hypotheses found

One line each; these become named hypotheses in Lean and findings in the report.

## Questions for the reader

Ambiguities in the text, places where two readings differ, constants or conventions to fix.

## Roadmap

The whole map, confirmed with the chain and updated at every stop (`status.py <Slug>` prints the Position
block from it; `chain_graph.py --gaps` draws what remains). The "End" line is the end the user chose; a
"Milestone" line names an intermediate end worth reporting. One row per piece of work, in the order they
are to be done: `rows` the ids of this table it discharges (`—` when its rows live in another chain, named
in `route`); `route` one of `prove here` · `port from <project>` · `assume by citation` · `hypothesis` (of
the theorem); `size` the estimate in sessions, with its evidence in parentheses (the existing project's
line count, the number of computational cases, what a comparable piece took); `status` `done <date>` ·
`next` · `in progress` · `planned`; `actual` the sessions and lines a done piece took (so the next estimate
is better). Nothing is formalized until the table above, the graph and this roadmap are confirmed.

End S: self-contained — every row of the chain proved here, standard axioms (`decide +kernel`; a disclosed `native_decide` only under step 5's rule).
Milestone R: <an intermediate end, e.g. the theorem under one named hypothesis>, reached after piece <x>.

| piece | title | rows | route | size | status | actual |
|---|---|---|---|---|---|---|
| A | <three words> | def:<x>, lem:<a> | prove here | 1 session (<evidence>) | next | |
| B | <three words> | thm:<label>, step:<b> | prove here | 2–3 sessions (<evidence>) | planned | |
| cite | cited results | ext:<y> | assume by citation | — | — | |
| hyp | the theorem's hypotheses | assume:<z> | hypothesis | — | — | |

## Dependency graph

`chain_graph.py` writes `CHAIN.tex` (TikZ) and compiles `CHAIN.pdf` (border = kind of row, fill = status,
legend with the counts and the roadmap's progress; `--gaps` draws only what remains as `CHAIN-gaps.pdf`); the
mermaid version below is kept in sync by the same script.

<!-- chain-graph:begin -->
<!-- chain-graph:end -->
