# Worked example: the halfspace identity (linear sum = 2 × integral sum)

Source of the statement: H. Hadipour, "Connecting Cryptanalytic Distinguishers through
Divisibility", ePrint 2026/2471. The formalization is the one in his blog post "Lean for
Cryptanalysts" (2026-10-29), restated on the shared library (`Formal.Crypto`: carrier `Vec ι`, Walsh
coefficient `walsh`) as `Formal/Examples/Halfspace.lean` in the workspace (`assets/examples/Halfspace.lean`
in this skill). This page shows the *paper-side* work the skill asks for; the Lean file shows the
proof side. Both compile with standard axioms only.

## Step 1 — the statement as the source gives it

The blog renders the paper's identity as: for any permutation `E` of `F_2^n` and nonzero
masks `α, β`, split the input space by the value of `α·x` into the halfspaces `X₀`, `X₁`
(each of size `2^(n-1)`); then the linear correlation satisfies
`L_{α,β}(E) = 2·I_β(X₀; E) = −2·I_β(X₁; E)`, where `I_β(X; E) = ∑_{x∈X} (−1)^{β·E(x)}` and
`L_{α,β}(E) = ∑_x (−1)^{α·x ⊕ β·E(x)}`, all sums unnormalized integers.

Objects: `E` (a permutation of `n`-bit states), `α, β` (masks), the two halfspaces, the two
sums. Hypotheses: `E` bijective (explicit here, but a cipher paper often writes "let `E` be
a block cipher" and never says it), `α ≠ 0` (needed so that the halfspaces have equal size),
`β ≠ 0` (not needed for the identity; it only makes the sums interesting). Conclusion: the
two equations. Proof: (1) split `L` over `X₀ ∪ X₁`, which gives `L = I₀ − I₁` with no
hypothesis on `E`; (2) since `E` is a bijection, `∑_x (−1)^{β·E(x)} = ∑_y (−1)^{β·y} = 0`,
i.e. `I₀ + I₁ = 0`; (3) solve the two linear equations.

## Step 2 — NOTATION.md (the correspondence table)

| paper | Lean | type | meaning / scope |
|---|---|---|---|
| state `x ∈ F_2^n` | `x : Vec ι` (library carrier, `ι → ZMod 2`) | type | any finite index type; `i₀ : ι` is the selected coordinate |
| `α·x` with `α = e_{i₀}` | `x i₀`, i.e. `Pi.single i₀ 1 ⬝ᵥ x` | `ZMod 2` | input mask fixed to one coordinate (see departure) |
| `β·E(x)` with `β = e_{i₀}` | `(E x) i₀` | `ZMod 2` | output mask fixed to the same coordinate |
| `(−1)^b` | `sgn ℤ b` (library) | `ZMod 2 → ℤ` | `0 ↦ 1`, `1 ↦ −1` |
| `I_β(X_b; E)` | `halfSum E i₀ b` | `ℤ` | sum over the halfspace `x i₀ = b` |
| `L_{α,β}(E)` | `linearSum E i₀ := walsh E (Pi.single i₀ 1) (Pi.single i₀ 1)` | `ℤ` | the library's Walsh coefficient, unnormalized |
| "E is a permutation" | `hE : Function.Bijective E` | hypothesis | per key when `E = E K` |

## Step 3 — statement first

```lean
theorem linearSum_eq_two_mul_halfSum (E : Vec ι → Vec ι) (hE : Function.Bijective E) (i₀ : ι) :
    linearSum E i₀ = 2 * halfSum E i₀ 0 := by
  sorry
```
compiles; so do `linearSum_eq_sub` and `halfSum_add_halfSum` with `sorry`. The docstrings
quote the paper's names (`I_β(X_b; E)`, `L_{α,β}(E)`).

## Step 4 — finite checks before proving

`toy : Vec (Fin 3) → Vec (Fin 3)` flips coordinate `0` exactly when the other two bits are `11`.
`decide +kernel` shows `halfSum toy 0 0 = 2`, `halfSum toy 0 1 = −2`, `linearSum toy 0 = 4`,
so the identity holds on the toy with the expected numbers (this is what catches a wrong
sign or a swapped coordinate). `constantMap x = 0` has `linearSum = 0` but
`2 * halfSum = 8`, so the bijectivity hypothesis cannot be dropped.

## Step 5 — one lemma per proof step

| paper step | Lean lemma | tactic idea |
|---|---|---|
| split over the two halfspaces | `linearSum_eq_sub` | `Finset.sum_filter_add_sum_filter_not`, then `sgn_add`, `sgn_one` on the `x i₀ = 1` half |
| bijection reindexes the sum | `halfSum_add_halfSum` | `Equiv.sum_comp (Equiv.ofBijective E hE)`, then the library's orthogonality `sum_chi` for the mask `Pi.single i₀ 1 ≠ 0` |
| solve the linear system | `linearSum_eq_two_mul_halfSum` | `linarith` from the two lemmas |
| divisibility transfer | `pow_dvd_halfSum` | `rw [pow_succ'] at h` and `mul_dvd_mul_iff_left` |
| per key | `all_keys` | apply the theorem to `E K` |

## Step 6 — check

`scripts/check_lean.py Formal/Examples/Halfspace.lean` → every declaration PASS, axioms
`propext, Classical.choice, Quot.sound`; the printed statements are read once more against
the table above.

## Step 7 — report: status and departures

| paper label | Lean declaration | status | axioms |
|---|---|---|---|
| identity `L = 2·I₀` | `Halfspace.linearSum_eq_two_mul_halfSum` | proved | standard |
| divisibility transfer | `Halfspace.pow_dvd_halfSum` | proved | standard |
| per-key statement | `Halfspace.all_keys` | proved | standard |

Departures from the paper, recorded in the README:
- **Masks fixed to one coordinate.** The paper states the identity for arbitrary nonzero
  `α, β`; the Lean statement takes `α = β = e_{i₀}` for a selected coordinate `i₀`. The general
  case follows by composing `E` with two invertible linear maps that send `α` and `β` to `e_{i₀}`;
  that change of basis is *not* formalized. Saying this is the difference between "Theorem 1 is
  formalized" and "a special case of Theorem 1 is formalized".
- **Any finite index type.** The formal statement is for every `Vec ι` with a coordinate `i₀`,
  so `ι` has at least one element; the paper assumes a real block size. Harmless, worth a line.
- **`β ≠ 0` dropped.** Not needed for the identity, so the Lean statement is slightly more
  general on that axis; the README says so.
- **Implicit hypothesis made explicit.** `Function.Bijective E` appears as a named hypothesis
  and `constantMap_counterexample` shows it is necessary.
