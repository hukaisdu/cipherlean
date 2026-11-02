# Promoting definitions and lemmas into the shared library (step 7b)

Every paper formalization leaves behind a few declarations that the next paper will need again.
Step 7b finds them, the user decides, and the move is done before the paper directory is closed.
The mechanical part is `scripts/promote_candidates.py`; the judgement is yours and the user's.

## What the script does

```
python3 $SKILL/scripts/promote_candidates.py CipherLean/<Slug>/<File>.lean [<File2>.lean …] [--write]
python3 $SKILL/scripts/promote_candidates.py CipherLean/<Slug>/            # its built, non-template files
```
loads the (already built) modules next to the library in one Lean process and prints, per module, every
declaration with its elaborated statement and a class. The paper objects are the definitions of *all* the
files given, so run the pieces of a split theorem together: alone, a lemma of piece C about piece B's
`Bout` came out as A "only library objects". `--write` saves one `PROMOTE.md` with all the tables.

| class | meaning | default action |
|---|---|---|
| A | lemma whose statement uses only library objects and is general in the index type | move as it is |
| B | general, but the statement uses an object the paper defined | move together with that object if the object is promoted (see E), else keep |
| E | an object the paper defined (`def`, `abbrev`, `structure`) | decide: a general notion (coset average, DDT as a matrix, a halfspace sum) is promoted with its B lemmas; a paper-specific one (`Φ[ψ,φ]`, a specific cipher's state, an abbreviation such as `Vec N := Vec (Fin N)`) stays |
| F | general, Mathlib only (no library object) | move to `F2/Vec` or a new module; low priority |
| D | the same statement already exists in the library | delete the copy, import the library |
| C | concrete sizes or a named test instance (`toy*`, `*_counterexample`, PRESENT, a paper definition applied to numerals such as `map 3 3 0 1`, ...) | stays with the paper; test instances are promoted only when the library needs one of that size |

`--write` saves the report as `PROMOTE.md` next to the file. The classes are heuristics: an alias
of a library object (class E) makes its users class B, a lemma can be general and still too
specialised to be worth a library name, and a duplicate with a differently shaped statement is not
detected. Read the statements, not only the table.

## Deciding (five questions per candidate)

1. Is the statement general in the index type `ι` (no `Fin 4`, no particular cipher)? If not, C.
2. Does it speak only about library notions, or about a notion that at least two papers would
   name the same way? Otherwise it stays with the paper.
3. Is it already there? `rg <name or keyword> CipherLean/Lib` and compare statements.
4. Does it carry an unpublished result of the user? The library is public; a paper's main theorem,
   or a definition whose only purpose is that theorem, stays in the paper directory until the
   paper is out, however general it looks (ask the user when unsure).
5. Would a reviewer understand its docstring without the paper? Promote only with a docstring
   that names the source (paper, venue/ePrint) in the library's words.

## Moving (checklist)

1. Put the declaration into the target module with the library's variables (`{ι : Type*}
   [Fintype ι] [DecidableEq ι]`, `K` a `CommRing` unless division is needed), the library's
   names for everything it mentions, and `omit … in` for instances its type does not need.
2. Keep the proof; adjust names (`Crypto.*`-style prefixes disappear inside `namespace CipherLean`).
3. Add a finite check if it is a definition; keep the paper's toy where it is.
4. `$SKILL/scripts/lake_build.sh CipherLean`, then `check_lean.py` on the module, then
   `trim_imports.py` only if a new import was added. With a remote workspace (`CIPHERLEAN_REMOTE`),
   `remote.sh lib <touched library files>` syncs `CipherLean/Lib/` and `CipherLean.lean` there, rebuilds
   the library and checks each file (`remote.sh sync/build/check/chain` cover only `CipherLean/<Slug>/`).
5. Add a row to `CipherLean/Lib/NOTATION.md` and the module table of `CipherLean/Lib/README.md`. Then
   `notation_check.py CipherLean/Lib/NOTATION.md <the touched library files>` (it reads a library NOTATION
   as well as a paper's).
6. In the paper file, replace the moved declaration by the library's name (keep a one-line instance
   under the paper's name if README or NOTATION refer to it), rebuild and re-check the paper file.
7. Re-point the Markdown files. Before the move, `repoint_names.py CipherLean/<Slug>/ name[=new] … --lib`
   lists every `<Slug>.name` and every bare `` `name` `` in CHAIN.md, NOTATION.md, README.md, PROMOTE.md,
   REVIEW.md (with `--lib` also `Lib/NOTATION.md`, `Lib/README.md`; `.lean` files are listed, never
   rewritten); after it, `--apply` rewrites `<Slug>.name` → `CipherLean.new` and the bare renamed names.
   Then `chain_check.py` and `notation_check.py … --also README.md CHAIN.md` must be clean: piece C of
   WHConj3 had about forty such places, one of them a rename, and the stale ones surfaced only in review.
8. Copy the library into the skill (`scripts/sync_library.sh`), commit, and open a pull request
   or push (CONTRIBUTING.md).

## The first two harvests (2026-11-01), as examples

| from | promoted | kept with the paper | why |
|---|---|---|---|
| CosetSpectrum (unpublished) | `chi_eq_of_mem_ann`, `card_ne_zero_of_isSubspace`, `card_ann_ne_zero` (A/B modulo the alias `Vec N`) | `cosetAvg`, `coeff`, the quotient `walsh`, `quotCard`, `Phi`, both main theorems | general facts about cosets were already standard; the rest is the paper's result |
| Examples/Halfspace | `halfSum`, `walsh_single_eq_sub`, `halfSum_add_halfSum`, `walsh_single_eq_two_mul_halfSum`, `pow_dvd_halfSum`, `single_dot`, `filter_ne_zero_eq` | `linearSum` (the paper's name for `walsh E e e`), toys | the identity is a published result about library objects |
| DdtInverse | `ddtMatrix`, `ddtMatrix_symm`, `ddt_invFun`, `ddt_eq_ddt_of_leftInverse` | toys | general spellings of a library lemma |
| Examples/SboxDDT | `ddt_toFun_row_sum` | the 3-bit cube S-box and its APN proof | a named test instance stays where it is used |
