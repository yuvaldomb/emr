"""
Reference implementations and random stress tests for EMR overflow (δ).

Purpose
-------
Companion code for ../paper/main.tex — **not** part of the proof chain.
General theorems (correctness, δ ≤ 2/n/3) are machine-checked in
../formal/EmrFormal.lean.

This module provides:
  • Readable bigint reference implementations of Montgomery REDC and EMR variants
  • ``check()`` — assert S ≡ cR⁻¹ (mod p) and return δ = ⌊S/p⌋
  • ``sweep()`` / ``sweep_by_n()`` — random searches for large δ (sanity / exploration)

Run ``python3 overflow.py`` for a quick multi-variant sweep.

Conventions
-----------
Algorithms return the value S *before* final conditional subtractions, as in
Section 6 of the paper. All arithmetic is exact (Python int).
"""

from __future__ import annotations

import random
from math import gcd
from typing import Callable, Dict, Optional, Tuple

# Type alias: (c, p, r, n) -> S before normalization
EmrFn = Callable[..., int]


def digits(x: int, r: int, length: int) -> list[int]:
    out = []
    for _ in range(length):
        out.append(x % r)
        x //= r
    return out


def mont_standard(c: int, p: int, r: int, n: int) -> int:
    """Baseline multiprecision Montgomery REDC (Proposition 6.1)."""
    mu = (-pow(p, -1, r)) % r
    S = c
    for _ in range(n):
        ctil = S % r
        m = (ctil * mu) % r
        S = (S + m * p) // r
    return S


def emr_iterative(c: int, p: int, r: int, n: int) -> int:
    """Iterative EMR (Algorithm 4.2): ``n−1`` extended rounds + one Montgomery round."""
    rho1 = pow(r, -1, p)
    mu = (-pow(p, -1, r)) % r
    S = c
    for _ in range(n - 1):
        ctil = S % r
        S = (S // r) + ctil * rho1
    ctil = S % r
    m = (ctil * mu) % r
    return (S + m * p) // r


def emr_parallel(c: int, p: int, r: int, n: int) -> int:
    """Parallel EMR (Eq. (4)): one width-``(n−1)`` pass + one Montgomery round."""
    mu = (-pow(p, -1, r)) % r
    rho = {k: pow(r, -k, p) for k in range(1, n)}
    d = digits(c, r, 2 * n)
    V = c // (r ** (n - 1))
    for i in range(n - 1):
        V += d[i] * rho[n - 1 - i]
    ctil = V % r
    m = (ctil * mu) % r
    return (V + m * p) // r


def log_widths(n: int) -> list[int]:
    """Halving pass widths (Corollary 6.6 / Lean ``logWidths``)."""
    D = n - 1
    out: list[int] = []
    while D > 0:
        out.append((D + 1) // 2)
        D //= 2
    return out


def pass_width(S: int, r: int, b: int, rho: Dict[int, int]) -> int:
    """One reduction pass Π_b (Lemma 6.2)."""
    d = [S // (r ** i) % r for i in range(b)]
    low = sum(d[i] * rho[b - i] for i in range(b))
    return S // (r ** b) + low


def emr_log(c: int, p: int, r: int, n: int) -> int:
    """Log EMR (Corollary 6.6): halving schedule + one Montgomery round."""
    mu = (-pow(p, -1, r)) % r
    rho = {k: pow(r, -k, p) for k in range(1, n + 2)}
    S = c
    for b in log_widths(n):
        S = pass_width(S, r, b, rho)
    ctil = S % r
    m = (ctil * mu) % r
    return (S + m * p) // r


def emr_batched(c: int, p: int, r: int, n: int, b: int) -> int:
    """Experimental fixed-width batched schedule (not in the paper; for comparison only)."""
    mu = (-pow(p, -1, r)) % r
    S = c
    remaining = n
    rho = {k: pow(r, -k, p) for k in range(1, n + 1)}
    while remaining > 1:
        step = min(b, remaining - 1)
        d = digits(S, r, step)
        low = sum(d[i] * rho[step - i] for i in range(step))
        S = (S // (r ** step)) + low
        remaining -= step
    for _ in range(remaining):
        ctil = S % r
        m = (ctil * mu) % r
        S = (S + m * p) // r
    return S


def check(alg: EmrFn, c: int, p: int, r: int, n: int, **kw) -> int:
    """Verify residue correctness and return δ = ⌊S/p⌋."""
    R = r ** n
    S = alg(c, p, r, n, **kw)
    target = (c * pow(R, -1, p)) % p
    name = getattr(alg, "__name__", repr(alg))
    assert S % p == target, f"residue mismatch: {name} c={c} p={p} r={r} n={n}"
    return S // p


def sweep(alg: EmrFn, trials: int = 20_000, **kw) -> Tuple[int, Optional[dict]]:
    """Random search: return (max δ seen, parameters at worst case)."""
    max_delta = 0
    worst = None
    rng = random.Random(12345)
    for _ in range(trials):
        w = rng.choice([2, 3, 4, 8, 16])
        r = 1 << w
        n = rng.choice([2, 3, 4, 6, 8])
        R = r ** n
        if rng.random() < 0.5:
            p = rng.randrange(R // 2, R) | 1
        else:
            p = rng.randrange(3, R) | 1
        if gcd(p, r) != 1:
            continue
        mode = rng.random()
        if mode < 0.4:
            c = rng.randrange(0, p * p)
        elif mode < 0.7:
            c = rng.randrange(0, p * R)
        elif mode < 0.9:
            c = rng.randrange(0, R * R)
        else:
            c = rng.choice([p * p - 1, p * R - 1, R * R - 1, R * R - 2])
        d = check(alg, c, p, r, n, **kw)
        if d > max_delta:
            max_delta = d
            worst = dict(w=w, r=r, n=n, p=p, c=c, rho1=pow(r, -1, p))
    return max_delta, worst


def sweep_by_n(alg: EmrFn, **kw) -> Dict[int, int]:
    """Bucket max δ by limb count ``n`` (inputs with ``c < pR``)."""
    rng = random.Random(999)
    buckets: Dict[int, int] = {}
    for _ in range(40_000):
        w = rng.choice([4, 8, 16])
        r = 1 << w
        n = rng.choice([2, 3, 4, 5, 6, 8, 12, 16])
        R = r ** n
        p = rng.randrange(R // 2, R) | 1
        if gcd(p, r) != 1:
            continue
        c = rng.randrange(0, p * R)
        d = check(alg, c, p, r, n, **kw)
        buckets[n] = max(buckets.get(n, 0), d)
    return dict(sorted(buckets.items()))


def main() -> None:
    print("overflow.py — reference EMR implementations + random δ stress tests")
    print("(General bounds are proved in ../formal/; this is supplemental.)\n")
    print("=== max δ (conditional subtractions before normalization) ===\n")

    for label, alg in [
        ("Standard Montgomery", mont_standard),
        ("EMR iterative", emr_iterative),
        ("EMR parallel", emr_parallel),
        ("EMR log", emr_log),
        ("EMR batched (b=2, experimental)", lambda c, p, r, n: emr_batched(c, p, r, n, b=2)),
    ]:
        md, w = sweep(alg)
        extra = f"   worst={w}" if w else ""
        print(f"{label:32} max δ = {md}{extra}")

    print("\n=== max δ vs limb count n (c < pR) ===")
    for label, alg in [
        ("Standard Montgomery", mont_standard),
        ("EMR iterative", emr_iterative),
        ("EMR parallel", emr_parallel),
        ("EMR log", emr_log),
        ("EMR batched b=2", lambda c, p, r, n: emr_batched(c, p, r, n, b=2)),
        ("EMR batched b=3", lambda c, p, r, n: emr_batched(c, p, r, n, b=3)),
    ]:
        print(f"{label:20} {sweep_by_n(alg)}")


if __name__ == "__main__":
    main()
