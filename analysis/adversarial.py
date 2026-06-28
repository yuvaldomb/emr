#!/usr/bin/env python3
"""
Exploratory stress test for parallel EMR overflow (Corollary 6.5).

Purpose
-------
δ ≤ n for parallel EMR is **proved** in ../formal/ (``emrParallel_delta_le_n``).
This script is supplemental:

  1. Compare measured S/p and δ against the analytic bound at ``c = pR − 1``
  2. Randomly search moduli p that maximize δ (how close to the cap n?)

Use for intuition, regression checks, and paper development — not for proofs.

Run: ``python3 adversarial.py``

Depends on: ``overflow.emr_parallel``
"""

from __future__ import annotations

import random

from overflow import emr_parallel


def worst_c(p: int, r: int, n: int) -> int:
    """Largest c with c < pR (natural worst case for the overflow bound)."""
    return p * r**n - 1


def predicted_S_over_p(p: int, r: int, n: int) -> float:
    """Analytic upper bound on S/p from Corollary 6.5 at c = pR − 1."""
    R = r**n
    rho_sum = sum(pow(r, -k, p) for k in range(1, n))
    c = worst_c(p, r, n)
    T_par = (r - 1) / r * rho_sum
    return c / (R * p) + T_par / p + 1


def measured(p: int, r: int, n: int) -> tuple[int, float]:
    c = worst_c(p, r, n)
    R = r**n
    S = emr_parallel(c, p, r, n)
    assert S % p == (c * pow(R, -1, p)) % p
    return S // p, S / p


def table_fixed_p() -> None:
    print("Phase 1: c = pR − 1, p ≈ R − 1 (Corollary 6.5 bound vs measurement)\n")
    print(f"{'w':>3} {'n':>3} {'Σρ/p':>10} {'bound S/p':>12} {'meas S/p':>10} {'meas δ':>8}")
    for w in [4, 8, 16]:
        r = 1 << w
        for n in [2, 3, 4, 6, 8, 12, 16]:
            R = r**n
            p = (R - 1) | 1
            if p >= R:
                p = (R - 2) | 1
            rho_sum = sum(pow(r, -k, p) for k in range(1, n))
            d, sp = measured(p, r, n)
            print(f"{w:>3} {n:>3} {rho_sum / p:>10.3f} {predicted_S_over_p(p, r, n):>12.3f} {sp:>10.3f} {d:>8}")


def search_hard_moduli() -> None:
    print("\nPhase 2: random search for p maximizing parallel δ (c = pR − 1)\n")
    print(f"{'w':>3} {'n':>3} {'best δ':>8} {'cap n':>6} {'Σρ/p at best':>14}")
    rng = random.Random(7)
    for w in [4, 8]:
        r = 1 << w
        for n in [2, 4, 8, 16]:
            R = r**n
            best = 0
            best_rho = 0.0
            for _ in range(4000):
                p = rng.randrange(R // 2, R) | 1
                try:
                    pow(r, -1, p)
                except ValueError:
                    continue
                d = emr_parallel(p * R - 1, p, r, n) // p
                if d > best:
                    best = d
                    best_rho = sum(pow(r, -k, p) for k in range(1, n)) / p
            print(f"{w:>3} {n:>3} {best:>8} {n:>6} {best_rho:>14.3f}")


def main() -> None:
    print("adversarial.py — parallel EMR overflow exploration (Corollary 6.5)")
    print("δ ≤ n is proved in ../formal/; this script is supplemental.\n")
    table_fixed_p()
    search_hard_moduli()


if __name__ == "__main__":
    main()
