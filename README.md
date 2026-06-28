# Extended Montgomery reduction in n²+1 digit multiplications

**Yuval Domb, Brian Koziel**

This repository holds the LaTeX source for a short note on extended Montgomery
reduction (EMR) and a Barrett–Montgomery duality theorem. The paper is the main
artifact; everything else supports it.

## Paper

[**Extended Montgomery reduction in n²+1 digit multiplications and a Barrett–Montgomery duality**](paper/main.pdf)
([LaTeX source](paper/main.tex))

EMR performs modular reduction with **n²+1 digit multiplications** instead of the
usual **n²+n**, by replacing the first n−1 Montgomery rounds with multiplications
by ρ₁ = r⁻¹ mod p. The note also gives parallel and logarithmic EMR variants,
tight overflow (normalization) bounds, and a dual extended Barrett reduction.
It expands material first presented in the [HackMD blog post (March 2025)](https://hackmd.io/@Ingonyama/Barret-Montgomery).

Rebuild the PDF after editing: `cd paper && make` (`paper/references.bib`).

## Supporting material

| Directory | Role |
|-----------|------|
| [`formal/`](formal/) | Machine-checked Lean 4 proofs of the paper's theorems — [formal/README.md](formal/README.md) |
| [`analysis/`](analysis/) | Supplemental Python: reference implementations, ECDSA instantiations (Remark 6.7), stress tests — [analysis/README.md](analysis/README.md) |

Lean proves correctness and the general overflow bounds (δ ≤ 2 / n / 3). Python
fills in concrete numeric examples and readable reference code; it is not part of
the proof chain.

```bash
# Lean (requires elan / Lean 4)
cd formal && lake exe cache get && lake build EmrFormal && lake env lean Audit.lean

# Python (3.9+, no dependencies)
cd analysis && python3 ecdsa_delta.py
```

CI (`.github/workflows/ci.yml`) compiles the paper and runs the Lean build and
axiom audit on every push/PR.

## Citation

Bibliography for prior work: `paper/references.bib`. A citation entry for this
paper will be added when published.
