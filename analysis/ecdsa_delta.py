#!/usr/bin/env python3
"""
Remark 6.7 — iterative EMR δ bounds on standard 256-bit ECDSA moduli.

Purpose
-------
Instantiates Corollary 6.4 for the four moduli in paper Remark 6.7:
P-256 base/scalar and secp256k1 base/scalar, at ``r = 2^64``, ``n = 4`` limbs.

Lean (../formal/) proves the general bound δ ≤ 2; this script:
  • Evaluates the tight analytic bound at worst-case ``c`` under ``c < p²`` and ``c < pR``
  • Searches empirically for the true maximum δ (including tightness: δ = 2 examples)
  • Prints the summary table matching the paper

Run: ``python3 ecdsa_delta.py``

Depends on: ``overflow.emr_iterative``
"""

from __future__ import annotations

import math
import random
from fractions import Fraction

from overflow import emr_iterative

# Paper Remark 6.7 moduli (256-bit)
MODULI: dict[str, int] = {
    "P-256 base": 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF,
    "P-256 scalar": 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551,
    "secp256k1 base": 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F,
    "secp256k1 scalar": 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141,
}

W = 64
N_LIMBS = 4
R = 1 << (W * N_LIMBS)  # 2^256


def rho_correction(r: int, n_limbs: int) -> tuple[int, int]:
    """T_iter = ρ₁(1 − r^{−(n−1)}) as (numerator, denominator) with denominator r^{n−1}."""
    nm1 = n_limbs - 1
    return r**nm1 - 1, r**nm1


def bound_S(c: int, p: int, r: int, n_limbs: int, rho1: int) -> Fraction:
    """Corollary 6.4: tight rational upper bound on S before subtractions."""
    rc_num, rc_den = rho_correction(r, n_limbs)
    return Fraction(c, R) + Fraction(rho1 * rc_num, rc_den) + p


def analyze_modulus(name: str, p: int, c_max: int, r: int, n_limbs: int, rho1: int) -> dict:
    """Analytic δ bound at worst c ≤ c_max."""
    rc_num, rc_den = rho_correction(r, n_limbs)
    T_iter = Fraction(rho1 * rc_num, rc_den)

    if c_max == p * R - 1:
        c_over_R = Fraction(p * R - 1, R)
        regime = "c < pR"
    elif c_max == p * p - 1:
        c_over_R = Fraction(p * p - 1, R)
        regime = "c < p²"
    else:
        c_over_R = Fraction(c_max, R)
        regime = f"c ≤ {c_max}"

    S_over_p = c_over_R / p + T_iter / p + 1
    return {
        "regime": regime,
        "delta_bound": math.floor(float(S_over_p + 1e-18)),
        "single_sub": T_iter < p - c_over_R,
    }


def empirical_max_delta(p: int, r: int, n_limbs: int, c_values) -> tuple[int, int | None]:
    worst_d, worst_c = 0, None
    for c in c_values:
        d = emr_iterative(c, p, r, n_limbs) // p
        if d > worst_d:
            worst_d, worst_c = d, c
    return worst_d, worst_c


def sample_c_values(p: int, regime: str, cap: int = 200_000) -> list[int]:
    rng = random.Random(0)
    out: set[int] = set()
    if regime == "pR":
        hi = p * R
        for c in [0, 1, p - 1, R - 1, hi - 1, hi - 2, hi // 2]:
            if c < hi:
                out.add(c)
        for _ in range(cap):
            out.add(rng.randrange(hi))
    else:  # p2
        hi = p * p
        for c in [0, 1, p - 1, hi - 1, hi - 2, hi // 2]:
            out.add(c)
        for _ in range(cap):
            out.add(rng.randrange(hi))
    return sorted(out)


def main() -> None:
    r = 1 << W
    n = N_LIMBS

    print("ecdsa_delta.py — Remark 6.7 (iterative EMR, r=2^64, n=4)")
    print("Analytic: Corollary 6.4 with T_iter = ρ₁(1 − r^{−(n−1)})")
    print("Proofs: ../formal/  |  Reference impl: overflow.emr_iterative\n")

    print(f"{'modulus':<18} {'R−p bits':>8} {'ρ₁/p':>10} {'δ|p²':>5} {'δ|pR':>5} {'emp p²':>7} {'emp pR':>7} {'T<p−c/R':>8}")
    print("-" * 84)

    for name, p in MODULI.items():
        gap = R - p
        rho1 = pow(r, -1, p)
        d_p2 = analyze_modulus(name, p, p * p - 1, r, n, rho1)
        d_pR = analyze_modulus(name, p, p * R - 1, r, n, rho1)
        emp_p2, _ = empirical_max_delta(p, r, n, sample_c_values(p, "p2", 100_000))
        emp_pR, _ = empirical_max_delta(p, r, n, sample_c_values(p, "pR", 100_000))
        pass_p2 = "yes" if d_p2["single_sub"] else "no"
        print(
            f"{name:<18} {gap.bit_length():>8} {rho1 / p:>10.4f} "
            f"{d_p2['delta_bound']:>5} {d_pR['delta_bound']:>5} "
            f"{emp_p2:>7} {emp_pR:>7} {pass_p2:>8}"
        )

    print("\nNotes:")
    print("  δ|p² / δ|pR — analytic bound ⌊c/(Rp) + T_iter/p + 1⌋ at worst c in each regime")
    print("  emp p² / emp pR — max δ found by sampling + edge cases (tightness check)")
    print("  T<p−c/R — Corollary 6.4 pass for δ ≤ 1 (only P-256 base at c < p²)")


if __name__ == "__main__":
    main()
