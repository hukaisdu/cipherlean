# NOTATION — `CipherLean` (shared library, carrier fixed 2026-11-01)

Carrier decision: every statement is over `Vec ι := ι → ZMod 2` with `[Fintype ι] [DecidableEq ι]`
(`ι = Fin n` for an `n`-bit word; a product index for a state split into words). Concrete tables
live on `BitVec n`; `bvEquiv : BitVec n ≃ Vec (Fin n)` is the bridge (`toVec_xor`: xor ↦ `+`).
All statistics are unnormalized integers or counts; normalized forms are corollary definitions.

| paper symbol | Lean name | type | meaning / scope |
|---|---|---|---|
| `F_2^n`, `F_2^ι` | `Vec ι` | `ι → ZMod 2` | vectors; `+` is bitwise xor; `n = Fintype.card ι` |
| `u·x`, `uᵀx` | `u ⬝ᵥ x` | `ZMod 2` | `dotProduct`, mask applied to a value |
| `(-1)^a`, `a ∈ F_2` | `sgn K a` | `K` (any `CommRing`) | `ℤ` for statistics, `ℚ`/`ℝ` for normalized values |
| `χ_u(x) = (-1)^{u·x}` | `chi K u x` | `K` | character; `sum_chi`: `Σ_x χ_u(x) = 2^n [u = 0]` |
| `V ≤ F_2^n` | `V : Finset (Vec ι)`, `IsSubspace V` | `Finset`, `Prop` (decidable) | subspace as its set of vectors |
| `k + V` | `coset V k` | `Finset (Vec ι)` | `x ∈ coset V k ↔ x + k ∈ V` |
| `V^⊥` | `ann V` | `Finset (Vec ι)` | annihilator; `ann_ann hV : ann (ann V) = V`; `card_mul_card_ann hV : |V|·|V^⊥| = 2^n` |
| `Σ_{w ∈ V^⊥} (-1)^{w·y}` | `sum_chi_ann K hV y` | theorem | `= if y ∈ V then |V^⊥| else 0` |
| `W_F(u, v) = Σ_x (-1)^{u·x + v·F(x)}` | `walsh F u v` | `ℤ` | Walsh coefficient of `F : Vec ι → Vec κ` (Carlet 2021 §2.2.1) |
| `#{x : u·x = v·F(x)}` | `linCount F u v` | `ℕ` | `walsh_eq_two_mul_linCount_sub`: `W = 2·# − 2^n` |
| `c_F(u, v) = W_F(u,v)/2^n` | `correlation F u v` | `ℚ` | corollary definition only |
| `Σ_u W_F(u,v)^2 = 2^{2n}` | `sum_walsh_sq F v` | theorem | Parseval |
| `δ_F(a, b) = #{x : F(x+a)+F(x) = b}` | `ddt F a b` | `ℕ` | DDT entry; `ddt_row_sum`, `ddt_zero_left`, `even_ddt`, `ddt_symm` |
| `δ(F) = max_{a≠0,b} δ_F(a,b)` | `diffUniformity F` | `ℕ` | Nyberg (EUROCRYPT 1993); `IsAPN F : δ(F) = 2` |
| `Σ_{a,b} δ_F(a,b)(-1)^{u·a+v·b} = W_F(u,v)^2` | `sum_ddt_mul_sgn F u v` | theorem | Chabaud–Vaudenay (EUROCRYPT 1994) |
| S-box table | `Sbox.ofTable t`, `Sbox.toFun S` | `BitVec n → BitVec n`, `Vec (Fin n) → Vec (Fin n)` | `toFun S = toVec ∘ S ∘ ofVec` |
| PRESENT S-box | `Sbox.present`, `Sbox.presentVec` | — | standard 4-bit test instance (CHES 2007) |
| word ↔ vector | `toVec`, `ofVec`, `bvEquiv` | `BitVec n ≃ Vec (Fin n)` | coordinate `i` = bit `i` (LSB first) |

Not interchangeable: `walsh` (integer) vs `correlation` (rational); `ddt` (count) vs `ddt / 2^n`
(probability, not defined here); `Vec (Fin n)` vs `BitVec n` (bridge required, `+` vs `^^^`).

Open: `lat` (LAT entry `W/2`) is not defined; add it with `two_mul_lat` when a paper needs it.
