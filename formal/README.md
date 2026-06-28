# Machine-checked verification of the EMR paper

Lean 4 + mathlib formalization of the theorems in
*"Extended Montgomery reduction in n²+1 digit multiplications and a
Barrett–Montgomery duality"* (`../paper/main.tex`).

All results live in `EmrFormal.lean`. `Audit.lean` runs `#print axioms` on 72
capstone theorems; each depends only on mathlib's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — there is **no `sorry`**.

## Build

Continuous integration (`.github/workflows/ci.yml`) runs `lake build EmrFormal`,
the axiom audit, and a LaTeX build of `../paper/main.tex` on every push/PR.

```
lake exe cache get   # prebuilt mathlib oleans
lake build EmrFormal
lake env lean Audit.lean   # axiom audit
```

**Empirical companion:** numeric experiments and the Remark 6.7 ECDSA table live in
[`../analysis/`](../analysis/README.md) (Python reference code; supplemental to these proofs).

## Modelling conventions

* Modular inverses are explicit elements of `ZMod p` satisfying their defining
  relation (`R * Rinv = 1`, `rᵏ * ρ_k = 1`). No primality of `p` is assumed.
* Overflow bounds are proved over `ℝ` using the relaxed inequalities the integer
  algorithm satisfies (`⌊S/r⌋ ≤ S/r`, digits `≤ r−1`).
* The formalization uses a single `ℕ` accumulator, not limb arrays.

## Verification status (amsart theorem numbers)

Numbers match the paper’s shared theorem counter (Theorem/Proposition/Lemma/
Corollary/Algorithm in each section). They are **not** `\section` numbers
(e.g. baseline Montgomery is proved in §6 as Proposition 6.1, while §3 describes
the scan).

| # | Statement | Status | Lean |
|---|---|---|---|
| **2.1** | Theorem (Barrett–Montgomery duality) | **Full** | `EMR.duality` |
| **4.1** | Proposition (ρ-replacement + digit bound) | **Full** | `EMR.rho_reduces`, `EMR.rho_bound` |
| **4.2** | Algorithm (iterative EMR) | **Full** (single-accumulator model) | `EMR.emrStep`, `EMR.emrIter`, `EMR.montStep`, `EMR.emr` |
| **4.3** | Theorem (`n²+1` digit multiplications, `cR⁻¹ mod p`) | **Full** | `EMR.count`, `EMR.emr_correct`, `EMR.n2p1` |
| **6.1** | Proposition (baseline Montgomery: `S < 2p`, `δ ≤ 1`) | **Full** | `EMR.montScan`, `EMR.montScan_decomp`, `EMR.montScan_baseline`, `EMR.montScan_delta_le_one`, `EMR.montScan_correct`; also `EMR.baseline`, `EMR.montStep_lt_2p`, `EMR.montStep_delta_le_one` |
| **6.2** | Lemma (pass `Π_b`: congruence + magnitude) | **Full** (abstract + concrete pass) | `EMR.pass_correct`, `EMR.passWidth_correct`, `EMR.pass_magnitude`, `EMR.passWidth_real_bound` |
| **6.3** | Theorem (general schedule overflow) | **Full** | `EMR.scheduleWeight`, `EMR.emrSchedule`, `EMR.emrSchedule_correct`, `EMR.logFold_real_bound`, `EMR.emrSchedule_overflow`; ℝ engines `EMR.unroll`, `EMR.overflow_parallel`, … |
| **6.4** | Corollary (iterative EMR: overflow, `δ ≤ 2`, `δ ≤ 1` if `T_iter < p−c/R`) | **Full** | `EMR.emr_overflow_tight`, `EMR.emr_overflow_tight_bound`, `EMR.iterative_delta_le_two_div`, `EMR.iterative_delta_le_one` |
| **6.5** | Corollary (parallel EMR: overflow, `δ ≤ n`, `δ ≤ 1` if `T_par < p−c/R`) | **Full** | `EMR.emrParallel_overflow`, `EMR.emrParallel_delta_le_n`, `EMR.emrParallel_delta_le_one` |
| **6.6** | Corollary (log EMR: overflow, `δ ≤ 3`, `δ ≤ 1` if `T_log < p−c/R`) | **Full** | `EMR.emrLog_overflow`, `EMR.emrLog_delta_le_three`, `EMR.emrLog_delta_le_one`; series via `EMR.logPre_real_bound`, … |

**Not formalized:** EBR remark, Barrett scan, limb-level implementations, primality-dependent shortcuts.

## Executable EMR variants

### Iterative EMR — Algorithm 4.2 (`EMR.emr`)

| Object | Lean |
|---|---|
| Extended round `S ↦ ⌊S/r⌋ + (S mod r)·ρ₁` | `EMR.emrStep` |
| `k` extended rounds | `EMR.emrIter` |
| Final Montgomery round | `EMR.montStep` |
| Full algorithm | `EMR.emr` |
| One round is `·r⁻¹ mod p` | `EMR.emrStep_correct`, `EMR.montStep_correct` |
| Montgomery round divides exactly | `EMR.montStep_dvd` |
| **Correctness** `rⁿ·emr ≡ c` | `EMR.emr_correct`, `EMR.n2p1` |
| Recursion bounds | `EMR.emrStep_real_bound`, `EMR.montStep_real_bound` |
| Extended rounds overflow | `EMR.emrIter_overflow` |
| Full algorithm overflow (ℝ) | `EMR.emr_overflow`, `EMR.emr_overflow_tight` |
| **δ ≤ 2** on `ℕ` | `EMR.iterative_delta_le_two_div` |
| **δ ≤ 1** if `T_iter < p − c/R` | `EMR.iterative_delta_le_one` |

### Parallel EMR — Corollary 6.5 (`EMR.emrParallel`)

| Object | Lean |
|---|---|
| Width-`(n−1)` pass + Montgomery round | `EMR.passWidth`, `EMR.parallelPre`, `EMR.emrParallel` |
| Pass divides by `r^b` mod `p` | `EMR.passWidth_correct` |
| **Correctness** `rⁿ·emrParallel ≡ c` | `EMR.parallelPre_correct`, `EMR.emrParallel_correct` |
| Pass overflow (ℝ) | `EMR.passWidth_real_bound`, `EMR.emrParallel_overflow` |
| **δ ≤ n** on `ℕ` | `EMR.emrParallel_delta_le_n` |
| **δ ≤ 1** if `T_par < p − c/R` | `EMR.emrParallel_delta_le_one` |

### Arbitrary schedule (`EMR.emrSchedule`)

| Object | Lean |
|---|---|
| Geometric schedule weight | `EMR.scheduleWeight` |
| `logFold` + Montgomery round | `EMR.emrSchedule` |
| **Correctness** `rⁿ·output ≡ c` | `EMR.emrSchedule_correct` |
| Pre-Montgomery overflow (ℝ) | `EMR.logFold_real_bound` |
| Full overflow (ℝ) | `EMR.emrSchedule_overflow` |

### Baseline Montgomery scan — Proposition 6.1 (`EMR.montScan`)

| Object | Lean |
|---|---|
| `n`-round digit scan | `EMR.montScan`, `EMR.montM` |
| Identity `rⁿS = c + pM` | `EMR.montScan_decomp` |
| Output `< 2p`, **δ ≤ 1** | `EMR.montScan_baseline`, `EMR.montScan_delta_le_one` |
| **Correctness** `rⁿ·montScan ≡ c` | `EMR.montScan_correct` |

### Log EMR — Corollary 6.6 (`EMR.emrLog`)

| Object | Lean |
|---|---|
| Halving schedule + passes | `EMR.logWidths`, `EMR.logFold`, `EMR.emrLog` |
| Pass list sums to `n−1` | `EMR.logWidths_sum` |
| **Correctness** `rⁿ·emrLog ≡ c` | `EMR.logFold_correct`, `EMR.emrLog_correct` |
| Series bound `Σ(d+1)r^{−d} ≤ r²/(r−1)²` | `EMR.log_overflow`, `EMR.logWidths_scheduleWeight` |
| Pre-Montgomery weighted bound (halving schedule) | `EMR.logPre_real_bound` |
| Overflow + **δ ≤ 3** | `EMR.emrLog_overflow`, `EMR.emrLog_delta_le_three` |
| **δ ≤ 1** if `T_log < p − c/R` | `EMR.emrLog_delta_le_one` |

## Normalization tool

`δ := ⌊S/p⌋` is the number of conditional subtractions of `p` needed to normalize
the algorithm output `S` into `[0,p)`.
`EMR.normalization_count` converts any bound `S < (k+1)p` into `δ ≤ k`.
