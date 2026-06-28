# Empirical analysis (companion to the Lean proofs)

Executable reference implementations and **numeric experiments** for the paper
*"Extended Montgomery reduction in n²+1 digit multiplications…"*
(`../paper/main.tex`).

**Machine-checked proofs** live in `../formal/` (`EmrFormal.lean`). That
formalization proves correctness and the general overflow bounds (Corollaries
6.4–6.6: δ ≤ 2 / n / 3, and the δ ≤ 1 pass conditions). It does **not**
instantiate the four standard ECDSA moduli or search for tight examples.

These Python scripts fill that gap. They are **supplemental**, not part of the
proof chain.

## Requirements

Python 3.9+ (uses `pow(..., -1, m)` for modular inverses). No third-party
packages.

## Files

| File | Role |
|------|------|
| **`overflow.py`** | Shared **reference implementations** of standard Montgomery REDC and the three EMR variants (iterative, parallel, log), plus random stress tests. Use as a library (`from overflow import emr_iterative, …`) or run directly for a quick δ sweep. |
| **`ecdsa_delta.py`** | **Paper Remark 6.7** — analytic and empirical δ bounds for P-256 and secp256k1 (base and scalar moduli) at `r = 2^64`, `n = 4`. Re-run this to regenerate the table numbers or check tightness (δ = 2 achievable). |
| **`adversarial.py`** | **Exploratory** stress test for parallel EMR (Cor. 6.5): compares measured δ against the analytic bound and searches for hard moduli. The bound δ ≤ n is already proved in Lean; this script is for intuition and regression only. |

## Usage

From this directory:

```bash
# Reference implementations + random overflow sweep (all variants)
python3 overflow.py

# Remark 6.7 table: analytic bounds + empirical max δ (iterative EMR)
python3 ecdsa_delta.py

# Parallel EMR: bound vs measurement + adversarial modulus search
python3 adversarial.py
```

## What Python does vs Lean

| Question | Lean | Python |
|----------|------|--------|
| Is EMR correct mod p? | Proved | `check()` asserts on samples |
| Is δ ≤ 2 / n / 3 in general? | Proved | Stress tests (sanity only) |
| Does P-256 base need only one subtraction? | Not instantiated | `ecdsa_delta.py` |
| Is δ ≤ 2 tight for P-256 scalar? | Not proved (existential) | Empirical search finds δ = 2 |
| Readable bigint reference code? | Single ℕ accumulator | Limb-style reference |

## Conventions

- **Modulus** `p`: odd integer coprime to digit base `r`.
- **Limb count** `n`: `R = r^n`.
- **δ** = `⌊S/p⌋`: conditional subtractions of the modulus needed after the algorithm returns `S` (before final normalization into `[0, p)`).
- Algorithms return **S before subtraction(s)**, matching the overflow section of the paper.
