import EmrFormal

/-! Axiom audit for amsart-numbered results in `EmrFormal.lean`.
Each `#print axioms` confirms the result depends only on Mathlib's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — never on `sorry`. -/

/-! ## §2.1 — Theorem (Barrett–Montgomery duality) -/

#print axioms EMR.duality

/-! ## §4.1 — Proposition (ρ-replacement) -/

#print axioms EMR.rho_reduces
#print axioms EMR.rho_bound

/-! ## §4.2 / §6.4 — Algorithm (iterative EMR) and Corollary (overflow) -/

#print axioms EMR.emrStep_correct
#print axioms EMR.emrIter_correct
#print axioms EMR.montStep_dvd
#print axioms EMR.montStep_correct
#print axioms EMR.emr_correct
#print axioms EMR.emrStep_real_bound
#print axioms EMR.emrIter_overflow
#print axioms EMR.montStep_real_bound
#print axioms EMR.emr_overflow
#print axioms EMR.emr_overflow_tight
#print axioms EMR.emr_overflow_tight_bound
#print axioms EMR.iterative_delta_le_two
#print axioms EMR.iterative_delta_le_two_div
#print axioms EMR.iterative_delta_le_one

/-! ## §4.3 — Theorem (`n²+1` digit multiplications) -/

#print axioms EMR.count
#print axioms EMR.n2p1

/-! ## §6.1 — Proposition (baseline Montgomery) -/

#print axioms EMR.baseline
#print axioms EMR.montgomery_M_le
#print axioms EMR.baseline_from_montgomery_scan
#print axioms EMR.baseline_delta_le_one
#print axioms EMR.baseline_subtraction_count
#print axioms EMR.montStep_lt_2p
#print axioms EMR.montStep_delta_le_one
#print axioms EMR.montScan_decomp
#print axioms EMR.montM_le
#print axioms EMR.montScan_eq_div
#print axioms EMR.montScan_baseline
#print axioms EMR.montScan_delta_le_one
#print axioms EMR.montScan_correct

/-! ## §6.2 — Lemma (width-`b` pass `Π_b`) -/

#print axioms EMR.pass_correct
#print axioms EMR.pass_magnitude
#print axioms EMR.passWidth_correct
#print axioms EMR.passWidth_real_bound
#print axioms EMR.sigmaSum_le

/-! ## §6.3 — Theorem (general schedule overflow) -/

#print axioms EMR.unroll
#print axioms EMR.unroll_gen
#print axioms EMR.iterative_overflow
#print axioms EMR.iterative_overflow_le
#print axioms EMR.parallel_pass_bound
#print axioms EMR.overflow_iterative
#print axioms EMR.overflow_parallel
#print axioms EMR.overflow_log
#print axioms EMR.logFold_real_bound
#print axioms EMR.emrSchedule_correct
#print axioms EMR.emrSchedule_overflow

/-! ## §6.6 — Corollary (log EMR): supporting series lemmas -/

#print axioms EMR.log_series
#print axioms EMR.log_partial_bound
#print axioms EMR.log_factor
#print axioms EMR.log_overflow
#print axioms EMR.logWidths_sum
#print axioms EMR.logWidths_scheduleWeight
#print axioms EMR.logPre_real_bound

/-! ## Normalization (`δ = ⌊S/p⌋`) -/

#print axioms EMR.normalization_count

/-! ## §6.5 — Corollary (parallel EMR) -/

#print axioms EMR.parallelPre_correct
#print axioms EMR.parallelPre_real_bound
#print axioms EMR.emrParallel_is_schedule
#print axioms EMR.emrParallel_correct
#print axioms EMR.emrParallel_overflow
#print axioms EMR.parallel_delta_le_n
#print axioms EMR.emrParallel_delta_le_n
#print axioms EMR.emrParallel_delta_le_one

/-! ## §6.6 — Corollary (log EMR) -/

#print axioms EMR.logFold_correct
#print axioms EMR.emrLog_is_schedule
#print axioms EMR.emrLog_correct
#print axioms EMR.emrLog_overflow
#print axioms EMR.log_delta_le_three
#print axioms EMR.emrLog_delta_le_three
#print axioms EMR.emrLog_delta_le_one
