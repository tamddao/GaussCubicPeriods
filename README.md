# Cubic Gauss Periods — Lean 4 Formal Verification

Companion Lean 4 + Mathlib 4 code for the paper:

> **"Explicit Formulas for Cubic Gauss Periods via the Representation q = a² + ab + 7b²"**
> Dao Van Tam, 2026

OEIS sequence: [A394567](https://oeis.org/A394567)

## Main Result

For every prime q ≡ 1 (mod 3), q ≠ 3, write q = a² + ab + 7b² and set
c = 2a + b normalized so that c ≡ 1 (mod 3). Then the product of the
three cubic Gauss periods satisfies:

$$\eta_0\,\eta_1\,\eta_2 = \frac{(c+3)\,q - 1}{27} \in \mathbb{Z}$$

## What is Verified (0 sorry)

| Section | Content | Tactic |
|---------|---------|--------|
| §1 | Eisenstein integer algebra: norm, mul, conj | `ring` |
| §2 | Primary elements: definition, conjugation | `omega` |
| §3 | Uniqueness of primary in orbit (6 units) | `decide` |
| §4 | Key construction: π₀ = (a+2b)+3bω is primary, N(π₀)=q, 2re−im=c | `ring`+`omega` |
| §5 | Bijection φ: injectivity, φ(π̄)=(X,−Y) | `linarith` |
| §6 | Integrality: 27 ∣ (c+3)q−1 with explicit witness | `ring` |
| §8 | Formula checks for all 30 primes in Table 1 (7 ≤ q ≤ 349) | `norm_num` |
| §8 | Primary element checks for 10 primes | `decide` |

## Key Theorem (no axiom needed)

```lean
theorem integrality_uniform (a b : ℤ) :
    (27 : ℤ) ∣ (2 * a + b + 3) * (a ^ 2 + a * b + 7 * b ^ 2) - 1 :=
  ⟨a^3 + 2*a^2*b + a^2 + 7*a*b^2 + 2*a*b + 7*b^3 + 7*b^2, by ring⟩
```

## Single Named Axiom

```
axiom IR_Jacobi_Primary : J(χ,χ) is primary with N(J) = q
```

This encapsulates Ireland–Rosen Prop 8.3.1 (τ³ = q·J) and
Thm 9.4.2 (J primary), which require Jacobi-sum infrastructure
not yet in Mathlib 4. All other theorems are proved without `sorry`.

## Requirements

- Lean 4 (v4.x)
- Mathlib 4

```bash
lake update
lake build
```

## Statistics

| Metric | Value |
|--------|-------|
| Lines | ~675 |
| Theorems | 50+ |
| Axioms | 1 |
| sorry | 0 |

## License

This project is released under the [MIT License](LICENSE).

## Citation

If you use this code, please cite:

```bibtex
@misc{daovantam2025gauss,
  author = {Dao Van Tam},
  title  = {Explicit Formulas for Cubic Gauss Periods via the Representation $q = a^2+ab+7b^2$},
  year   = {2025},
  note   = {Lean 4 verification}
}
```
