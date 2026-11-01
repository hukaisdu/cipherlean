# Lean 4 + Mathlib cheatsheet for cryptanalysis statements

Since 2026-11-01 the encodings of sections 1–2 that recur (vectors over `F_2`, characters,
`Finset` subspaces with duality, Walsh coefficients, DDT, table S-boxes) are *definitions and
proved lemmas* in the shared library `CipherLean/Lib/` (`import CipherLean`, symbol table in
`CipherLean/Lib/NOTATION.md`). Use the library; this page remains the reference for the idioms
behind it and for objects the library does not have (ARX words, keyed families, iterated rounds).

Everything here compiled in the workspace (Lean v4.33.0, Mathlib v4.33.0) on 2026-11-01,
either in `CipherLean/Examples/*.lean`, in `CipherLean/Lib/*.lean`, or in a scratch file run with
`lean_eval.sh` (the rows of the encodings table that no shipped file uses were re-checked that way). Names that did *not* exist are
listed at the end so nobody searches for them twice.

## 1. Encodings — pick the type that makes the needed lemmas available

| paper object | Lean | operations / instances | use it for |
|---|---|---|---|
| a bit | `Bool` | `xor`, `&&`, `!`, `b.toNat`, `if b then … else …`, `DecidableEq` | anything `decide` must evaluate; coordinates of states |
| a bit, algebraically | `ZMod 2` | `+` is xor, `*` is and; `CharTwo.add_self_eq_zero x : x + x = 0`; `fin_cases x <;> rfl` | linear maps, masks, ANF, dot products |
| `n`-bit word | `BitVec n` | `^^^ &&& ||| ~~~`, `+` mod `2^n`, `<<< >>>`, `rotateLeft`, `getLsbD i : Bool`, literals `3#4`, `0xC`; `x.toNat`, `x.isLt : x.toNat < 2 ^ n`; `Fintype`, `DecidableEq`, `∑ x : BitVec n, …` | concrete ciphers, S-boxes, ARX, finite checks |
| mask / vector over `F_2` | `CipherLean.Vec ι` (= `ι → ZMod 2`; `ι = Fin n` for words) | dot product `u ⬝ᵥ x`; `CipherLean.card_vec`; characters `CipherLean.chi`, orthogonality `CipherLean.sum_chi` | linear cryptanalysis, linear layers as matrices; the library carrier |
| state with a selected bit | `Vec ι` with a selected index `i₀ : ι`; the halfspace is `Finset.univ.filter (fun x => x i₀ = b)` | `Finset.sum_filter_add_sum_filter_not` splits a sum into the two halfspaces; a `Bool × _` product state splits with `Fintype.sum_prod_type`, `Fintype.sum_bool` | halfspace / integral arguments (`Halfspace.linearSum_eq_sub`) |
| S-box from a table | `CipherLean.Sbox.ofTable (#v[0xC, 0x5, …] : Vector (BitVec 4) 16)` on words; `CipherLean.Sbox.toFun S` on `Vec (Fin n)` | `decide` evaluates the table; bijectivity by `CipherLean.Sbox.bijective_of_injective (by decide)`; DDT facts decided on words through `CipherLean.ddt_toFun` | PRESENT (`CipherLean.Sbox.present`), 8-bit tables also fine |
| `(−1)^b` | `CipherLean.sgn K b` for `b : ZMod 2` (`if b = 0 then 1 else -1`), `CipherLean.chi K u x = sgn K (u ⬝ᵥ x)` | `sgn_add`, `sgn_mul_self`, `chi_add_left/right`, `chi_eq_one/neg_one`; the `if` form simps better than `(-1) ^ b.toNat` | correlations, Walsh sums (`CipherLean.walsh`) |
| a statistic | an *integer* sum `∑ x : α, f x : ℤ`, unnormalized | `ℤ` has no truncation (`ℕ` subtraction truncates, division is total) | linear / integral / DL sums |
| a count | `(Finset.univ.filter fun x : BitVec n => P x).card` (`P` decidable) | `Finset.card_eq_sum_card_fiberwise`, `Finset.card_filter_le`, `Finset.card_univ` | DDT / LAT entries, number of solutions |
| a probability | state the count; `count / 2 ^ n : ℚ` only as a final corollary | `x / 0 = 0` in Lean makes some ratio statements vacuously true | DP, correlation |
| permutation | `Function.Bijective E` | `Equiv.ofBijective E hE : α ≃ α`; `Function.Involutive.bijective`; `Function.bijective_iff_has_inverse`; `Finite.injective_iff_bijective` | round functions, S-boxes, keyed ciphers |
| permutation with its inverse | `S : Equiv.Perm α`, `S.symm` | `S.symm_apply_apply`, `S.apply_symm_apply`; from a function: `Function.invFun S` with `Function.leftInverse_invFun hS.1`, `Function.rightInverse_invFun hS.2`; one-sided → two-sided on finite types: `h.rightInverse_of_surjective (Finite.injective_iff_surjective.mp h.injective)` | "let `S` be a permutation and `S⁻¹` its inverse" (`CipherLean/Examples/DdtInverse/`) |
| subspace `V ≤ F_2^N` | `V : Finset (Vec ι)` with `CipherLean.IsSubspace V` (library; `0 ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V, a + b ∈ V`) | computable: `coset V k := univ.filter (· + k ∈ V)`, `ann V := univ.filter fun w => ∀ v ∈ V, w ⬝ᵥ v = 0`; `instance : Decidable (IsSubspace V) := inferInstanceAs (Decidable (_ ∧ _))`; `decide +kernel` evaluates sums over `Fin 2 → ZMod 2` with `ℚ` coefficients | fixed-key / coset averages, annihilators |
| keyed family | `E : Key → State → State` with `hE : ∀ K, Function.Bijective (E K)` | apply the per-permutation theorem to `E K` | per-key statements without enumerating keys |
| `r` rounds | `f^[r] x` (`Nat.iterate`), `Function.iterate_succ` | `f^[2] x = f (f x)` is `rfl` | iterated ciphers |
| a parity | `(List.range n).foldl (fun acc i => xor acc (x.getLsbD i)) false` | computable; `decide` evaluates it | mask parities `a·x` on `BitVec` |
| random keys / distributions | `PMF`, `PMF.uniformOfFintype` exist | heavy; only when the statement is genuinely probabilistic | provable-security style claims |

Core Lean alone has `BitVec`, `Bool`, `Nat`, `Function.LeftInverse / RightInverse`; `ℕ`, `∑`,
`Finset`, `Function.Bijective`, `ZMod` need `import Mathlib` (30 s load, fine).

## 2. Idioms that compiled (see `CipherLean/Examples/`)

`Halfspace.*`, `SboxDDT.*`, `Feistel.*` and `DdtInverse.*` are in `CipherLean/Examples/` and, since the
migration of 2026-11-01, build on the library (`CipherLean.*`); the `CosetSpectrum.*` names come from a
formalization of a coset-average theorem that is not shipped, so those idioms are quoted in full here
(its duality and character-sum lemmas are now the library's `CipherLean.sum_chi_ann`,
`CipherLean.card_mul_card_ann`, `CipherLean.exists_ann_dot_ne`, `CipherLean.ann_ann`).

1. **Split a sum into two halfspaces** (`CipherLean.walsh_single_eq_sub`; `Halfspace.linearSum_eq_sub` is its instance):
   `rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Vec ι => x i₀ = 0)]`, rewrite the
   summand on each part with the filter condition (`(Finset.mem_filter.mp hx).2`, then `sgn_add`,
   `sgn_one`), and turn `¬ x i₀ = 0` into `x i₀ = 1` by an explicit set equality (`ext x; simp only
   [Finset.mem_filter, Finset.mem_univ, true_and]; exact zmod2_ne_zero_iff`): `rw [Finset.filter_congr …]`
   picks the wrong `filter` when the goal has two. For a `Bool × _` product state the split is
   `simp only [Fintype.sum_prod_type, Fintype.sum_bool, …]` then `ring`.
2. **Reindex a sum along a bijection** (`CipherLean.halfSum_add_halfSum`):
   `Equiv.sum_comp (Equiv.ofBijective E hE) g : ∑ x, g (E x) = ∑ y, g y`; alternative
   `Function.Bijective.finsetSum` (the snake_case `finset_sum` is deprecated).
3. **Finish linear algebra on the sums**: `have h1 := …; have h2 := …; linarith`.
4. **Divisibility transfer** (`CipherLean.pow_dvd_halfSum`): `rw [thm, pow_succ'] at h` then
   `(mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h`. Also `Finset.dvd_sum`,
   `dvd_sub`, `Dvd.dvd.mul_left`, `Dvd.dvd.mul_right`, `Int.emod_emod_of_dvd`,
   `Int.even_or_odd`, `Int.emod_two_eq_zero_or_one`.
5. **A row of a count table sums to the domain size** (`CipherLean.ddt_row_sum`; `SboxDDT.ddt_row_sum` is its instance for a table S-box):
   `rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)]`, then the
   cardinality of `Finset.univ`; the hypothesis is `Set.MapsTo f ↑s ↑t`.
6. **Finite checks by `decide`** (`CipherLean.present_diffUniformity`, `SboxDDT.cube_isAPN`): state
   `diffUniformity (Sbox.toFun S) = d` on `Vec (Fin n)`, prove `≤` with
   `(diffUniformity_toFun_le_iff S).mpr (by decide +kernel)` (the bound checked on words: 256 pairs ×
   16 inputs in about 8 s) and `≥` from `ddt_le_diffUniformity` at a witness entry whose value
   `decide` computes after `rw [ddt_toFun]`. `∀ x : BitVec 4`, `∑ x : BitVec 3`, and
   `Finset.univ.filter` over `BitVec 3` all work with plain `decide`. Beyond ~2^14
   evaluations prove symbolically instead.
7. **Bijectivity of a concrete S-box**: `Finite.injective_iff_bijective.mp (by decide)`.
8. **Fixed-width bit identities**: `bv_decide` (SAT, e.g. `(x &&& y) + (x ||| y) = x + y` on
   `BitVec 8`). It adds an axiom `<decl>._native.bv_decide.ax_*` whenever a certificate is
   needed, as `native_decide` adds `<decl>._native.native_decide.ax_*`; `decide +kernel`
   adds nothing. The check script reports these as NATIVE.
9. **XOR cancellation**: `simp [round, roundInv, BitVec.xor_assoc]` closes
   `(l ^^^ F r) ^^^ F r = l`; with Mathlib loaded plain `simp [round, roundInv]` suffices.
10. **`ZMod 2` facts**: `fin_cases x <;> rfl` (or `decide`) for `x + x = 0`, `2 * x = 0`;
    `CharTwo.add_self_eq_zero x`; linearity of a dot product by
    `simp [dot, mul_add, Finset.sum_add_distrib]`.
11. **Cardinalities**: `Fintype.card_bool`, `Fintype.card_fin`, `Fintype.card_prod`,
    `Fintype.card_fun`, `Finset.card_univ`. There is no simp lemma for `Fintype.card (BitVec n)`
    (`FinEnum.card_bitVec` is about `FinEnum.card`); use the ring equivalence
    `BitVec.equivFin : BitVec m ≃+* Fin (2 ^ m)`:
    `(Fintype.card_congr (BitVec.equivFin (m := n)).toEquiv).trans (Fintype.card_fin _)`
    (`CipherLean.card_bitVec` uses the bridge `bvEquiv` instead), or `rw [Fintype.card_congr (BitVec.equivFin (m := n)).toEquiv, Fintype.card_fin]`.
12. **Signs**: `pow_add`, `pow_mul`, `neg_one_pow_eq_pow_mod_two`, `Even.neg_one_pow`,
    `Odd.neg_one_pow`.
14. **Equal cardinalities via an explicit bijection** (`CipherLean.ddt_eq_ddt_of_inverse`, `CipherLean.card_coset`, `CipherLean.ddt_toFun`):
    `refine Finset.card_nbij' i j ?_ ?_ ?_ ?_`, then in each goal `intro x hx` and
    `simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢` (the goals are
    `Set.MapsTo` / `Set.LeftInvOn` / `Set.RightInvOn` on coerced finsets). Same for sums:
    `Finset.sum_nbij'` (one more argument `∀ a ∈ s, f a = g (i a)`). Also `Finset.card_equiv`,
    `Finset.card_bijective`.
15. **A character sum over a subspace vanishes** (`CosetSpectrum.sum_chi_ann`): pick `w₀` with
    `w₀ᵀy = 1` and use `Finset.sum_involution (fun w _ => w + w₀)` with the four side goals
    `f a + f (a + w₀) = 0`, `a + w₀ ≠ a` (`add_eq_left`), closure, `a + w₀ + w₀ = a`. The sign rule
    `(-1)^{a+b} = (-1)^a (-1)^b` on `ZMod 2`: `rcases zmod2_cases a with rfl | rfl <;> … <;> simp [h11]`
    with `zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide` and `h11 : (1 : ZMod 2) + 1 = 0 := by decide`.
16. **Duality `V^⊥⊥ = V`, `|V|·|V^⊥| = 2^N`** for a `Finset` subspace (`CosetSpectrum.card_mul_card_ann`,
    `exists_ann_dot_ne`): submodule `AddSubgroup.toZModSubmodule 2 ⟨V, add_mem, zero_mem, neg_mem⟩`
    (`neg_mem` from `CharTwo.neg_eq`); the dot product as a bilinear form
    `LinearMap.mk₂ (ZMod 2) (· ⬝ᵥ ·) (fun _ _ _ => add_dotProduct _ _ _) (fun _ _ _ => smul_dotProduct _ _ _) …`;
    then `LinearMap.BilinForm.orthogonal_orthogonal hnondeg hrefl W : B.orthogonal (B.orthogonal W) = W`,
    `LinearMap.BilinForm.finrank_orthogonal hnondeg W`, `Module.natCard_eq_pow_finrank (K := ZMod 2)`
    (needs `have : Module.Finite (ZMod 2) ↥W := Module.Finite.of_finite`), `Module.finrank_fin_fun`,
    `Submodule.finrank_le`; back to finsets with `Nat.card_congr (Equiv.subtypeEquivRight h)` +
    `Nat.card_eq_fintype_card` + `Fintype.card_coe`. Nondegeneracy of the dot product:
    `unfold LinearMap.BilinForm.Nondegenerate LinearMap.Nondegenerate LinearMap.SeparatingLeft LinearMap.SeparatingRight`,
    `refine ⟨fun m hm => ?_, fun m hm => ?_⟩`, test against `Pi.single i 1` with `dotProduct_single` / `single_dotProduct`.
17. **Regrouping a double sum by cosets** (`CosetSpectrum.walsh_div_quotCard_eq_coeff`): `Finset.sum_comm`,
    `Finset.sum_filter` (`∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0`),
    `Finset.sum_boole` (`∑ x ∈ s, if p x then 1 else 0 = ↑{x ∈ s | p x}.card`), `Finset.sum_div`,
    `Finset.sum_mul`, `Finset.mul_sum`, `split_ifs <;> simp`, then `field_simp` with
    `(V.card : K) ≠ 0` from `Finset.card_pos.mpr ⟨0, h0⟩` and `exact_mod_cast`.
18. **BitVec xor toolbox** beyond `xor_assoc` / `xor_self`: `BitVec.xor_comm`, `xor_zero`, `zero_xor`,
    `xor_left_inj`, `xor_right_inj`, `xor_eq_zero_iff` (source:
    `~/.elan/toolchains/leanprover--lean4---v4.33.0/src/lean/Init/Data/BitVec/Lemmas.lean`); when the
    output difference `b` is a variable, `subst h` beats `rw [← h]`.
13. **Small explicit sums**: `Fin.sum_univ_two`, `Fin.sum_univ_succ`; **big operators**:
    `Finset.sum_comm`, `Finset.sum_add_distrib`, `Finset.sum_sub_distrib`, `Finset.mul_sum`,
    `Finset.sum_mul`, `Finset.sum_const`, `Finset.sum_ite_eq`, `Finset.sum_boole`,
    `Finset.sum_bij`, `Finset.sum_nbij`, `Fintype.sum_equiv`.

19. **Rewriting inside an `if` whose condition carries a `Decidable` instance** (`rw [foo_iff]` fails
    with "motive is not type correct"): use `by_cases h : cond` and `rw [if_pos (foo_iff.mpr h), …]` /
    `rw [if_neg (fun h' => h (foo_iff.mp h')), …]`, or `simp only [foo_iff]` (`CipherLean.walsh_eq_two_mul_linCount_sub`).
20. **`Finset.le_sup` / `Finset.sup_le_iff` for a max over a table** (`CipherLean.ddt_le_diffUniformity`):
    state each inequality with `have h : f b ≤ s.sup f := Finset.le_sup (f := f) hb` so the function is
    fixed; a bare `le_trans ?_ (Finset.le_sup ?_)` leaves the element unresolved.
21. **Parity of a count from an involution** (`CipherLean.even_ddt`): `∑ _x ∈ s, (1 : ZMod 2) = 0` by
    `Finset.sum_involution`, then `Finset.sum_const`, `nsmul_eq_mul`, `mul_one` and
    `ZMod.natCast_eq_zero_iff_even : ((n : ℕ) : ZMod 2) = 0 ↔ Even n`.
22. **Regroup a sum over inputs by output difference** (`CipherLean.sum_chi_diff_eq_sum_ddt`):
    `rw [← Finset.sum_fiberwise Finset.univ (fun x => F (x + a) + F x) f]`, then inside each fiber
    rewrite with `(Finset.mem_filter.mp hx).2` and finish with `Finset.sum_const`, `nsmul_eq_mul`.
23. **Substitute `y = x + a` in an inner sum** (`CipherLean.inner_sum_subst`):
    `rw [← Equiv.sum_comp (Equiv.addLeft x) g]`, `simp only [Equiv.coe_addLeft]`, then
    `← add_assoc, add_self, zero_add` in characteristic 2.
24. **Words ↔ vectors**: `BitVec.ofFn` does not exist in Lean v4.33.0; `CipherLean.ofVec` builds the word
    by recursion with `BitVec.cons` and `BitVec.getLsbD_cons`; injectivity of `toVec` is
    `BitVec.eq_of_getLsbD_eq`; `Pi.single i 1` needs a type ascription `(Pi.single i 1 : Vec ι)` when the
    expected type does not fix the function family.
25. **Kernel `decide` cost on `Vec (Fin n)`** (`Pi` Fintype instance): one DDT row of a 4-bit S-box ≈ 45 s,
    two Walsh coefficients ≈ 1 min; a full differential-uniformity table is minutes. State the fact on
    `Vec` and move the computation to `BitVec` with `CipherLean.ddt_toFun` / `diffUniformity_toFun_le_iff`
    (`CipherLean.present_diffUniformity`: < 10 s).

26. **A computational case with a semantic bridge** (step 5b), when `decide +kernel` cannot finish:
    ```lean
    /-- The finite computation, as a Boolean program (or a checker of an offline certificate). -/
    def checker : Bool := (Finset.univ.filter fun x : BitVec 8 => …).card ≤ 4   -- decidable, closed
    /-- Kernel-checked: `true` means the mathematical statement. Nothing native here. -/
    theorem checker_true_iff : checker = true ↔ ∀ x : BitVec 8, … := by simp [checker, …]
    /-- The only native step; `#print axioms` shows `checker_eval._native.native_decide.ax_1_1`. -/
    theorem checker_eval : checker = true := by native_decide
    /-- The case, proved relative to the compiler axiom. -/
    theorem the_case : ∀ x : BitVec 8, … := checker_true_iff.mp checker_eval
    ```
    Keep `checker_eval` the one declaration that uses `native_decide`, so the trust is visible in one
    place; `check_lean.py --allow-native` reports it as NATIVE and everything depending on it.
    Measured on this machine: kernel `decide` handles a 4-bit DDT bound (256 × 16) in 8 s and one DDT
    row of a 4-bit S-box on `Vec (Fin 4)` in 45 s; an 8-bit S-box's full DDT (2^16 × 256) needs the
    native route or an offline certificate.

27. **Large closed data under `native_decide`: `opaque`, not `def`** (verify-existing.md §3). The
    compiled decision procedure recomputes a transparent `def` every time the term refers to it; a
    30-million-element `HashSet` referenced three times took 200 s as a `def` and 25 s as an `opaque`
    (`let`-binding, `@[noinline]`, passing it as an argument: 156 s, 212 s, 198 s). Write
    `opaque bigTable : Finset … := …` (or a precomputed literal) and prove facts about it through
    `rfl`-free bridge lemmas; one missed `def` in a loop of 32³ iterations cost 1 h 49 min. A closure
    computed by breadth-first search inside the proof grows exponentially with the depth (K = 8:
    272 s, K = 9: minutes); compute it offline and let Lean check closedness.

## 3. Tactics, in the order to try them

`simp only [...]` (controlled) → `rw [...]` (literal pattern) → `ring` / `linarith` / `omega`
(ℕ, ℤ linear arithmetic, knows `x.isLt` once it is a hypothesis) / `norm_num` / `positivity`
/ `push_cast` → `decide`, `decide +kernel` (finite) → `fin_cases x <;> …` (small types) →
`ext` / `funext` → `exact?`, `apply?`, `rw?`, `simp?` (search) → `aesop` → `bv_decide`.
When `exact?` finds nothing, run `scripts/search_mathlib.sh "<fragment>"` (local grep,
Loogle by type pattern such as `Finset.sum _ (_ + _)`, LeanSearch in words) before writing
a lemma yourself.

## 4. Pitfalls met while compiling the examples

- `Unknown identifier ℕ` in a file without `import Mathlib`: core only knows `Nat`.
- `autoImplicit = false`: every `{n : ℕ}` must be declared; a typo becomes an error (good).
- `rw [BitVec.xor_self]` fails on `(l ^^^ a) ^^^ a`: the two copies must be adjacent, so
  `rw [BitVec.xor_assoc]` first. `simp` finds this itself.
- `linarith failed` with the negated goal printed: the needed equation is not in context;
  `have h := lemma …` first.
- `decide` after `fin_cases` can leave `(fun i => i) ⟨0, ⋯⟩ * …` goals it cannot decide; use
  `rfl` or `simp` instead.
- `Finset.card_eq_sum_card_fiberwise` expects `Set.MapsTo f ↑s ↑t`; a `fun x _ => …` lambda
  is accepted.
- Linters warn on unused `simp` arguments and lines over 100 characters; harmless, but
  keep the file clean so real warnings stand out.
- `declaration uses 'sorry'` is only a warning; a file full of them "compiles". The check
  script fails on `sorryAx` and prints every statement so the human half of the check
  is one read.
- `omit [CharZero K] in` goes *before* the docstring of the theorem, not between docstring and
  `theorem`; `intro` does not unfold `Nondegenerate`-style definitions (use `unfold` first or a
  term-mode `fun`); `push_neg` is deprecated here (`simp only [not_exists, not_and, ne_eq, not_not]`);
  `haveI` on a `Prop` draws a linter warning (`have`); `Module.natCard_eq_pow_finrank` needs
  `(K := …)` because the field is not determined by `Nat.card`.
- Lean checks proofs, not definitions: a toy instance with the expected numbers and a
  counterexample for each hypothesis are the only tests of the definitions.

## 5. Speed

- Check a lemma name or a 3-line example with `scripts/lean_eval.sh` (light preset, ≈ 7 s), not
  with a module build (≈ 27 s of Mathlib loading first).
- Toy instances over `BitVec 2..4` evaluate fast with `decide`; `Fin N → ZMod 2` with rational
  sums takes tens of seconds (kernel evaluation of `Finset.univ` on function types).
- `simp only [...]` with a named list beats bare `simp` in big files; `field_simp` once at the
  end, not inside a `calc` chain.
- When the proof is done, `scripts/trim_imports.py --apply`: the Halfspace example loads with
  9 modules instead of all of Mathlib.
- Keep finite checks that use `native_decide` in their own file (`Checks.lean` next to `Main.lean`):
  every build of a file re-elaborates its `native_decide` blocks, so a 1 000-line file with fifteen of
  them makes every `check_lean.py` run cost minutes; one run burned 25 full checks in two hours
  where `lean_eval.sh` on the one lemma was the right tool. After a build, `check_lean.py --no-build`.
- Long builds: count the computational sites first (`scripts/build_profile.py --sites`), build the
  heaviest module alone under a written time budget, sample the process (CPU time rising, RSS
  flat, no swap = progress, not a hang), and never run probes or a second `lake build` beside it.
  Afterwards `scripts/build_profile.py <log>` shows where the time went (one module was 94 % of a
  6 800 s build). Killing a progressing build at 85 min threw away 58 min of CPU and saved nothing.

## 6. Names that do not exist in Mathlib v4.33.0 (do not search again)

`Fintype.card_bitVec`, `BitVec.card`, `FinEnum.card_eq`, `Finset.sum_mod`, `BitVec.ofFn`,
`finFunctionFinEquiv_symm_apply`, `ZMod.natCast_zmod_eq_zero_iff_dvd` (now `ZMod.natCast_eq_zero_iff`
and `ZMod.natCast_eq_zero_iff_even`), `Finset.even_card_of_involution`, `Nat.testBit_to_div_mod`
(it is `Nat.testBit_eq_decide_div_mod_eq`); `simp` does not prove
`Fintype.card (BitVec n) = 2 ^ n` and `exact?` does not find it. Deprecated:
`Function.Bijective.finset_sum` → `Function.Bijective.finsetSum`.
