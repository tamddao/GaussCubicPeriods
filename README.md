# Cubic Gauss Periods — Lean 4 Formal Verification

Companion Lean 4 + Mathlib 4 code for the paper:

> **"Explicit Formulas for Cubic Gauss Periods via the Representation q = a² + ab + 7b²"**
> Dao Van Tam, 2026

OEIS sequence: [A394567](https://oeis.org/A394567)

## ✓ Verified on live.lean-lang.org (no errors)

The file `GaussCubicPeriods.lean` has been tested on
[live.lean-lang.org](https://live.lean-lang.org) and compiles
with **0 errors, 0 sorry, 1 named axiom**.

## Main Result

For every prime q ≡ 1 (mod 3), q ≠ 3, write q = a² + ab + 7b² and set
c = 2a + b normalized so that c ≡ 1 (mod 3). Then the product of the
three cubic Gauss periods satisfies:

$$\eta_0\,\eta_1\,\eta_2 = \frac{(c+3)\,q - 1}{27} \in \mathbb{Z}$$

## What is Verified

| Section | Content | Tactic | Status |
|---------|---------|--------|--------|
| §1 | Eisenstein integer algebra: norm, mul, conj | `ring` | ✓ no sorry |
| §2 | Primary elements: definition, conjugation | `omega` | ✓ no sorry |
| §3 | Uniqueness of primary in orbit (6 units) | `decide` | ✓ no sorry |
| §4 | Key construction: π₀ = (a+2b)+3bω is primary, N(π₀)=q, 2re−im=c | `ring`+`omega` | ✓ no sorry |
| §5 | Bijection φ: well-defined, injective, φ(π̄)=(X,−Y) | `ring`+`omega` | ✓ no sorry |
| §5b | Improper automorphism f(x+y,−y)=f(x,y); d=0 forms | `ring` | ✓ no sorry |
| §6 | Integrality: 27 ∣ (c+3)q−1 via 4[(c+3)q-1]=(c-1)(c+2)²+27b²(c+3) | `ring`+`omega` | ✓ no sorry |
| §7 | jacobi_coords: J primary with N(J)=q and 2re−im=c | `rcases`+`rw` | ✓ no sorry |
| §8 | Formula checks for all 30 primes in Table 1 (7 ≤ q ≤ 349) | `norm_num` | ✓ no sorry |
| §8 | Primary element checks for 10 primes | `decide` | ✓ no sorry |

## Key Theorem (no axiom needed)

```lean
theorem integrality_uniform (a b : ℤ) (hc : (2 * a + b) % 3 = 1) :
    (27 : ℤ) ∣ (2 * a + b + 3) * (a ^ 2 + a * b + 7 * b ^ 2) - 1
```

**Proof**: `4[(c+3)q-1] = (c-1)(c+2)² + 27b²(c+3)` using `4q = c²+27b²`.
Since `c ≡ 1 (mod 3)`: `(c-1)(c+2)² ≡ 0 (mod 27)`.
Hence `27 ∣ 4[(c+3)q-1]`, and `gcd(4,27)=1` gives `27 ∣ (c+3)q-1`.

## Single Named Axiom

```
axiom IR_Jacobi_Primary : J(χ,χ) is primary with N(J) = q,
                          and J = π₀ or J = π̄₀
```

This axiom encapsulates three results:

1. **IR Prop 8.3.1**: τ(χ)³ = q·J(χ,χ) — requires Jacobi sum infrastructure
2. **IR Thm 9.4.2**: J(χ,χ) is primary with N(J) = q
3. **Uniqueness**: J ∈ {π₀, π̄₀} — requires ℤ[ω] is a UFD

**Why ℤ[ω] UFD is in the axiom**: Mathlib 4 has `GaussianInt`
(ℤ[i] is a UFD) but not `EisensteinInt` (ℤ[ω] = ℤ[(1+√(-3))/2] is a UFD).
This is classical mathematics (h(-3) = 1) proved in the paper but not
yet formalized in Mathlib 4.

**Given the axiom**, `jacobi_coords` is proved with **no sorry** by a
two-case argument: if J = π₀ then 2·Re(J) = c by `pi0_phi_coord`;
if J = π̄₀ then 2·Re(J) = c by `pi0_conj_phi_coord`.

## Requirements

- Lean 4 (v4.x)
- Mathlib 4

```bash
lake update
lake build
```

Or paste directly into [live.lean-lang.org](https://live.lean-lang.org).

## Statistics

| Metric | Value |
|--------|-------|
| Lines | 715 |
| Theorems | 50+ |
| Axioms | 1 (`IR_Jacobi_Primary`) |
| sorry | 0 |
| Tested | ✓ live.lean-lang.org |

## License

This project is released under the [MIT License](LICENSE).

## Citation

```bibtex
@misc{daovantam2026gauss,
  author = {Dao Van Tam},
  title  = {Explicit Formulas for Cubic Gauss Periods via the Representation $q = a^2+ab+7b^2$},
  year   = {2026},
  note   = {Lean 4 verification, available at https://github.com/tamddao/GaussCubicPeriods}
}
```
