import Mathlib

/-!
# Machine-checked verification of the theorems in
  "Extended Montgomery reduction in n²+1 digit multiplications
   and a Barrett–Montgomery duality"

Modular inverses are modelled as explicit elements of `ZMod p` satisfying their
defining relation (`R * Rinv = 1`, `r * rho = 1`, …).  No primality of `p` is
assumed, matching the paper's setting of an arbitrary odd modulus.

Conventions: `r = 2^w` is the digit base, `R = r^n`, `p` the (odd) modulus,
`0 < p < R`, `gcd(r,p)=1`.
-/

namespace EMR

/-! ## Theorem 2.1 — the Barrett–Montgomery duality -/

/-- From the integer decomposition `c = c₁R + c₀`, both reductions follow:
the Barrett identity `c ≡ c₁R + c₀ (mod p)` and the Montgomery identity
`cR⁻¹ ≡ c₁ + c₀R⁻¹ (mod p)`. -/
theorem duality {p : ℕ} (c c0 c1 R : ℤ) (Rinv : ZMod p)
    (hsplit : c = c1 * R + c0) (hRinv : (R : ZMod p) * Rinv = 1) :
    ((c : ZMod p) = (c1 : ZMod p) * (R : ZMod p) + (c0 : ZMod p)) ∧
    ((c : ZMod p) * Rinv = (c1 : ZMod p) + (c0 : ZMod p) * Rinv) := by
  have hbar : (c : ZMod p) = (c1 : ZMod p) * (R : ZMod p) + (c0 : ZMod p) := by
    rw [hsplit]; push_cast; ring
  refine ⟨hbar, ?_⟩
  rw [hbar]
  linear_combination (c1 : ZMod p) * hRinv

/-! ## Proposition 4.1 — the per-round replacement and its digit bound -/

/-- The replacement value `c̃·ρ₁` is congruent to `c̃·r⁻¹`: multiplying it by `r`
recovers `c̃`.  Here `rho` is the modular inverse of `r` (`r·rho = 1`). -/
theorem rho_reduces {p : ℕ} (r_ : ZMod p) (ctil rho : ℕ)
    (hrho : r_ * (rho : ZMod p) = 1) :
    r_ * ((ctil : ZMod p) * (rho : ZMod p)) = (ctil : ZMod p) := by
  linear_combination (ctil : ZMod p) * hrho

/-- Digit bound of Proposition 4.1: for a single digit `c̃ < r` and `ρ₁ < p ≤ R`,
the product `c̃·ρ₁` is below `r·R`, hence has at most `n+1` base-`r` digits
(since `R = rⁿ`). -/
theorem rho_bound {r p R ctil rho1 : ℕ}
    (hc : ctil < r) (hrho : rho1 < p) (hpR : p ≤ R) (hp : 0 < p) :
    ctil * rho1 < r * R := by
  have hR : 0 < R := lt_of_lt_of_le hp hpR
  have h1 : ctil * rho1 ≤ ctil * R := by
    gcongr
    exact le_of_lt (lt_of_lt_of_le hrho hpR)
  have h2 : ctil * R < r * R := (Nat.mul_lt_mul_right hR).mpr hc
  exact lt_of_le_of_lt h1 h2

/-! ## Theorem 4.3 — `n²+1` digit multiplications and correctness -/

/-- The cost identity `(n-1)·n + (n+1) = n² + 1` for `n ≥ 1`
(the `n-1` extended rounds at `n` mults each, plus a final round at `n+1`). -/
theorem count (n : ℕ) (hn : 1 ≤ n) : (n - 1) * n + (n + 1) = n ^ 2 + 1 := by
  cases n with
  | zero => omega
  | succ k => simp only [Nat.succ_sub_one]; ring

/-! ## Proposition 6.1 — baseline Montgomery output is below `2p` -/

/-- Standard Montgomery reduction returns `(c + pM)/R` with `M ≤ R-1`; for an
input `c < pR` this is `< 2p`, so a single conditional subtraction normalizes. -/
theorem baseline {c p R M : ℕ} (hR : 0 < R) (hM : M ≤ R - 1) (hc : c < p * R) :
    (c + p * M) / R < 2 * p := by
  rw [Nat.div_lt_iff_lt_mul hR]
  have h2 : p * M ≤ p * R := by
    gcongr
    omega
  have e : 2 * p * R = 2 * (p * R) := by ring
  have h1 : c + p * M < p * R + p * M := Nat.add_lt_add_right hc _
  omega

/-! ## Lemma 6.2 — a width-`b` reduction pass computes `r^{-b} S`

A pass replaces `S = r^b·q + Σ_{i<b} s_i r^i` by `Π = q + Σ_{i<b} s_i ρ_{b-i}`,
where `ρ_k` is the inverse of `r^k` (`r^k · ρ_k = 1`).  We certify correctness by
showing `r^b · Π = S`, i.e. `Π ≡ r^{-b} S (mod p)`. -/
theorem pass_correct {p : ℕ} (r_ : ZMod p) (ρ s : ℕ → ZMod p) (q : ZMod p) (b : ℕ)
    (hρ : ∀ k, 1 ≤ k → r_ ^ k * ρ k = 1) :
    r_ ^ b * (q + ∑ i ∈ Finset.range b, s i * ρ (b - i))
      = r_ ^ b * q + ∑ i ∈ Finset.range b, s i * r_ ^ i := by
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have hbi : i + (b - i) = b := by omega
  have hk : 1 ≤ b - i := by omega
  have hpow : r_ ^ b = r_ ^ i * r_ ^ (b - i) := by rw [← pow_add, hbi]
  calc r_ ^ b * (s i * ρ (b - i))
        = s i * (r_ ^ b * ρ (b - i)) := by ring
    _ = s i * (r_ ^ i * (r_ ^ (b - i) * ρ (b - i))) := by rw [hpow]; ring
    _ = s i * (r_ ^ i * 1) := by rw [hρ (b - i) hk]
    _ = s i * r_ ^ i := by ring

/-- Lower magnitude bound of Lemma 6.2: the injected correction is nonnegative. -/
theorem pass_lower (q σ : ℝ) (hσ : 0 ≤ σ) : q ≤ q + σ := by linarith

/-- Upper magnitude bound of Lemma 6.2 (real relaxation of `⌊S/r^b⌋ ≤ S/r^b`). -/
theorem pass_upper (r q S σ sig : ℝ) (b : ℕ) (hq : q ≤ S / r ^ b) (hσ : σ ≤ (r - 1) * sig) :
    q + σ ≤ S / r ^ b + (r - 1) * sig := by linarith

/-- `Σ_m = Σ_{k=1}^m ρ_k`. -/
def sigmaSum (ρ : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range m, ρ (k + 1)

theorem sigmaSum_le (ρ : ℕ → ℕ) (m p : ℕ) (hm : 0 < m)
    (hρ : ∀ k, 1 ≤ k → k ≤ m → ρ k ≤ p - 1) :
    sigmaSum ρ m ≤ m * (p - 1) := by
  have step : ∀ k ∈ Finset.range m, ρ (k + 1) ≤ p - 1 := by
    intro k hk
    have hk1 : 1 ≤ k + 1 := by omega
    have hkm : k + 1 ≤ m := by rw [Finset.mem_range] at hk; omega
    exact hρ (k + 1) hk1 hkm
  calc sigmaSum ρ m = ∑ k ∈ Finset.range m, ρ (k + 1) := rfl
    _ ≤ ∑ _k ∈ Finset.range m, (p - 1) := Finset.sum_le_sum step
    _ = m * (p - 1) := by simp

theorem sigmaSum_ge (ρ : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (hρ : ∀ k, 1 ≤ k → k ≤ m → 1 ≤ ρ k) :
    m ≤ sigmaSum ρ m := by
  have step : ∀ j ∈ Finset.range m, (1 : ℕ) ≤ ρ (j + 1) := by
    intro j hj
    have hk1 : 1 ≤ j + 1 := by omega
    have hkm : j + 1 ≤ m := by rw [Finset.mem_range] at hj; omega
    exact hρ (j + 1) hk1 hkm
  calc m = ∑ _j ∈ Finset.range m, 1 := by simp
    _ ≤ ∑ j ∈ Finset.range m, ρ (j + 1) := Finset.sum_le_sum step
    _ = sigmaSum ρ m := rfl

/-- `(r−1) · Σ_{j<n} r^j = r^n − 1` for `r > 1`. -/
private theorem nat_geom_sum (r n : ℕ) (hr : 1 < r) :
    (r - 1) * ∑ j ∈ Finset.range n, r ^ j = r ^ n - 1 := by
  have hr2 : 2 ≤ r := by omega
  have hsum := Nat.geomSum_eq hr2 n
  calc (r - 1) * ∑ j ∈ Finset.range n, r ^ j
      = (r - 1) * ((r ^ n - 1) / (r - 1)) := by rw [hsum]
    _ = r ^ n - 1 := Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one r n)

private theorem div_div_rpow_succ (c r : ℝ) (m : ℕ) (hr : r ≠ 0) :
    c / r ^ m / r = c / r ^ (m + 1) := by
  field_simp [hr, pow_ne_zero m hr, pow_succ]
  ring

/-- Montgomery scan digit polynomial: `M = Σ m_j r^j ≤ R−1` when each `m_j ≤ r−1`. -/
theorem montgomery_M_le {r n : ℕ} (hr : 1 < r) (m : ℕ → ℕ) (hm : ∀ j, j < n → m j ≤ r - 1) :
    ∑ j ∈ Finset.range n, m j * r ^ j ≤ r ^ n - 1 := by
  have h1 : ∀ j ∈ Finset.range n, m j * r ^ j ≤ (r - 1) * r ^ j := by
    intro j hj
    rw [Finset.mem_range] at hj
    exact Nat.mul_le_mul_right _ (hm j hj)
  calc ∑ j ∈ Finset.range n, m j * r ^ j
      ≤ ∑ j ∈ Finset.range n, (r - 1) * r ^ j := Finset.sum_le_sum h1
    _ = (r - 1) * ∑ j ∈ Finset.range n, r ^ j := by rw [Finset.mul_sum]
    _ = r ^ n - 1 := nat_geom_sum r n hr

/-- Montgomery scan quotient `M = Σ m_j r^j` satisfies `M ≤ R − 1`, so Proposition 6.1
applies with `R = r^n`. -/
theorem baseline_from_montgomery_scan {c p r n M : ℕ} (hr : 1 < r) (hn : 0 < n)
    (hM : M ≤ r ^ n - 1) (hc : c < p * r ^ n) :
    (c + p * M) / r ^ n < 2 * p :=
  baseline (R := r ^ n) (pow_pos (Nat.zero_lt_of_lt hr) n) hM hc

theorem sigmaSum_one (ρ : ℕ → ℕ) : sigmaSum ρ 1 = ρ 1 := by simp [sigmaSum]

theorem baseline_delta_le_one {S p : ℕ} (hp : 0 < p) (hS : S < 2 * p) :
    S / p ≤ 1 := by
  have : S / p < 1 + 1 := (Nat.div_lt_iff_lt_mul hp).mpr (by omega : S < (1 + 1) * p)
  omega

/-- Proposition 6.1 packaged: an overflow bound `S < 2p` gives `δ ≤ 1`. -/
theorem baseline_subtraction_count {S p : ℕ} (hp : 0 < p) (hS : S < 2 * p) :
    S / p ≤ 1 :=
  baseline_delta_le_one hp hS

/-! ## Theorem 6.3 (core) — the overflow unrolling recursion

The mathematical engine of the overflow theorem.  If a sequence satisfies the
per-step relaxed recursion `x_{k+1} ≤ x_k / r + a_k` (each pass divides the
running value by `r` and injects an additive correction `a_k`), then, in
denominator-free form,
  `r^N · x_N ≤ c + Σ_{k<N} a_k r^{k+1}`.
Dividing by `r^N` gives the paper's `x_N ≤ c/r^N + Σ_k a_k / r^{N-1-k}`; the
factor `r^{k+1}/r^N = r^{-(N-1-k)}` is the geometric contraction that bounds the
Montgomery-side overflow. -/
theorem unroll (r : ℝ) (hr : 0 < r) (c : ℝ) (a x : ℕ → ℝ)
    (h0 : x 0 = c) (hstep : ∀ k, x (k + 1) ≤ x k / r + a k) (N : ℕ) :
    r ^ N * x N ≤ c + ∑ k ∈ Finset.range N, a k * r ^ (k + 1) := by
  induction N with
  | zero => simp [h0]
  | succ M ih =>
    have hrne : r ≠ 0 := hr.ne'
    have hpow : (0 : ℝ) < r ^ (M + 1) := by positivity
    have key : r ^ (M + 1) * x (M + 1) ≤ r ^ (M + 1) * (x M / r + a M) :=
      mul_le_mul_of_nonneg_left (hstep M) (le_of_lt hpow)
    have simp1 : r ^ (M + 1) * (x M / r + a M) = r ^ M * x M + a M * r ^ (M + 1) := by
      field_simp
      ring
    rw [Finset.sum_range_succ]
    have hkey : r ^ (M + 1) * x (M + 1) ≤ r ^ M * x M + a M * r ^ (M + 1) := by
      rw [← simp1]; exact key
    linarith

/-- General-schedule version of Theorem 6.3: passes of arbitrary widths divide by
`D_k` (e.g. `D_k = r^{b_k}`).  With `P_N = ∏_{j<N} D_j`,
  `P_N · x_N ≤ c + Σ_{k<N} a_k P_{k+1}`,
which is the denominator-free form of the Theorem 6.3 overflow bound for any reduction
schedule (iterative, parallel, logarithmic are instantiations). -/
theorem unroll_gen (D a x : ℕ → ℝ) (hD : ∀ k, 0 < D k) (c : ℝ) (h0 : x 0 = c)
    (hstep : ∀ k, x (k + 1) ≤ x k / D k + a k) (N : ℕ) :
    (∏ j ∈ Finset.range N, D j) * x N
      ≤ c + ∑ k ∈ Finset.range N, a k * ∏ j ∈ Finset.range (k + 1), D j := by
  induction N with
  | zero => simp [h0]
  | succ M ih =>
    have hPpos : (0 : ℝ) < ∏ j ∈ Finset.range (M + 1), D j :=
      Finset.prod_pos (fun j _ => hD j)
    have key : (∏ j ∈ Finset.range (M + 1), D j) * x (M + 1)
        ≤ (∏ j ∈ Finset.range (M + 1), D j) * (x M / D M + a M) :=
      mul_le_mul_of_nonneg_left (hstep M) (le_of_lt hPpos)
    have hsplit : ∏ j ∈ Finset.range (M + 1), D j
        = (∏ j ∈ Finset.range M, D j) * D M := Finset.prod_range_succ D M
    have hDMne : D M ≠ 0 := (hD M).ne'
    have simp1 : (∏ j ∈ Finset.range (M + 1), D j) * (x M / D M + a M)
        = (∏ j ∈ Finset.range M, D j) * x M + a M * (∏ j ∈ Finset.range (M + 1), D j) := by
      rw [hsplit]; field_simp
    rw [Finset.sum_range_succ]
    have hkey : (∏ j ∈ Finset.range (M + 1), D j) * x (M + 1)
        ≤ (∏ j ∈ Finset.range M, D j) * x M + a M * (∏ j ∈ Finset.range (M + 1), D j) := by
      rw [← simp1]; exact key
    linarith

/-- Divide the denominator-free `unroll_gen` bound by the accumulated product. -/
theorem unroll_gen_divided (D a x : ℕ → ℝ) (hD : ∀ k, 0 < D k) (c : ℝ) (h0 : x 0 = c)
    (hstep : ∀ k, x (k + 1) ≤ x k / D k + a k) (N : ℕ) :
    x N ≤ c / (∏ j ∈ Finset.range N, D j) +
      ∑ k ∈ Finset.range N,
        a k * (∏ j ∈ Finset.range (k + 1), D j) / (∏ j ∈ Finset.range N, D j) := by
  have hP : (0 : ℝ) < ∏ j ∈ Finset.range N, D j := Finset.prod_pos (fun j _ => hD j)
  have H := unroll_gen D a x hD c h0 hstep N
  have hle : x N ≤ (c + ∑ k ∈ Finset.range N, a k * ∏ j ∈ Finset.range (k + 1), D j) /
      (∏ j ∈ Finset.range N, D j) :=
    (le_div_iff₀ hP).mpr (by rw [mul_comm]; exact H)
  rw [add_div, Finset.sum_div] at hle
  exact hle

/-! ## Corollary 6.4 — iterative EMR overflow bound -/

/-- Iterative EMR: each of the `N` extended rounds divides by `r` and adds the
fixed correction `(r-1)ρ₁`.  Closed form:
  `r^N · x_N ≤ c + ρ₁ r (r^N − 1)`,
the geometric closed form of the accumulated correction. -/
theorem iterative_overflow (r ρ₁ : ℝ) (hr : 0 < r) (c : ℝ) (x : ℕ → ℝ)
    (h0 : x 0 = c) (hstep : ∀ k, x (k + 1) ≤ x k / r + (r - 1) * ρ₁) (N : ℕ) :
    r ^ N * x N ≤ c + ρ₁ * r * (r ^ N - 1) := by
  have H := unroll r hr c (fun _ => (r - 1) * ρ₁) x h0 hstep N
  have hgeo : (∑ k ∈ Finset.range N, r ^ k) * (r - 1) = r ^ N - 1 := geom_sum_mul r N
  have hsum : ∑ k ∈ Finset.range N, ((r - 1) * ρ₁) * r ^ (k + 1)
      = ρ₁ * r * (r ^ N - 1) := by
    calc ∑ k ∈ Finset.range N, ((r - 1) * ρ₁) * r ^ (k + 1)
        = (r - 1) * ρ₁ * r * ∑ k ∈ Finset.range N, r ^ k := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      _ = ρ₁ * r * ((∑ k ∈ Finset.range N, r ^ k) * (r - 1)) := by ring
      _ = ρ₁ * r * (r ^ N - 1) := by rw [hgeo]
  rw [hsum] at H; exact H

/-- Consequently `x_N ≤ c/r^N + ρ₁ r`: the running value stays within `ρ₁ r`
of the ideal `c/r^N`, independent of `N`. -/
theorem iterative_overflow_le (r ρ₁ : ℝ) (hr : 1 < r) (hρ : 0 ≤ ρ₁) (c : ℝ) (x : ℕ → ℝ)
    (h0 : x 0 = c) (hstep : ∀ k, x (k + 1) ≤ x k / r + (r - 1) * ρ₁) (N : ℕ) :
    x N ≤ c / r ^ N + ρ₁ * r := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have H := iterative_overflow r ρ₁ hr0 c x h0 hstep N
  have hpos : (0 : ℝ) < r ^ N := by positivity
  have hρr : 0 ≤ ρ₁ * r := mul_nonneg hρ (le_of_lt hr0)
  have h2 : r ^ N * x N ≤ c + ρ₁ * r * r ^ N := by nlinarith [H, hρr]
  have h3 : r ^ N * x N ≤ r ^ N * (c / r ^ N + ρ₁ * r) := by
    have e : r ^ N * (c / r ^ N + ρ₁ * r) = c + ρ₁ * r * r ^ N := by
      field_simp
    rw [e]; exact h2
  exact le_of_mul_le_mul_left h3 hpos

/-! ## Corollary 6.5 — parallel EMR correction bound -/

/-- Parallel EMR collapses all corrections into one width-`b` pass.  The injected
correction `Σ_{i<b} s_i ρ_{b-i}` is bounded by `(r-1) Σ_{k=1}^{b} ρ_k`, the
linear-in-`b` overflow term.  (`s_i ∈ [0,r-1]` are digits, `ρ_k ≥ 0`.) -/
theorem parallel_pass_bound (r : ℝ) (q : ℝ) (s ρ : ℕ → ℝ) (b : ℕ)
    (hs : ∀ i, s i ≤ r - 1) (hρ : ∀ k, 0 ≤ ρ k) :
    q + ∑ i ∈ Finset.range b, s i * ρ (b - i)
      ≤ q + (r - 1) * ∑ k ∈ Finset.range b, ρ (k + 1) := by
  have step1 : ∑ i ∈ Finset.range b, s i * ρ (b - i)
      ≤ ∑ i ∈ Finset.range b, (r - 1) * ρ (b - i) := by
    apply Finset.sum_le_sum; intro i _
    exact mul_le_mul_of_nonneg_right (hs i) (hρ _)
  have step3 : ∑ i ∈ Finset.range b, ρ (b - i) = ∑ k ∈ Finset.range b, ρ (k + 1) := by
    rw [← Finset.sum_range_reflect (fun k => ρ (k + 1)) b]
    apply Finset.sum_congr rfl
    intro i hi; rw [Finset.mem_range] at hi
    have : b - 1 - i + 1 = b - i := by omega
    simp only [this]
  calc q + ∑ i ∈ Finset.range b, s i * ρ (b - i)
      ≤ q + ∑ i ∈ Finset.range b, (r - 1) * ρ (b - i) := by linarith [step1]
    _ = q + (r - 1) * ∑ i ∈ Finset.range b, ρ (b - i) := by rw [Finset.mul_sum]
    _ = q + (r - 1) * ∑ k ∈ Finset.range b, ρ (k + 1) := by rw [step3]

/-- One width-`b` pass upper bound (Lemma 6.2 magnitude): `q + Σ s_i ρ_{b-i} ≤ S/r^b + (r-1)Σ_b`. -/
theorem pass_step_bound (r q S : ℝ) (s ρ : ℕ → ℝ) (b : ℕ)
    (hq : q ≤ S / r ^ b) (hs : ∀ i, s i ≤ r - 1) (hρ : ∀ k, 0 ≤ ρ k) :
    q + ∑ i ∈ Finset.range b, s i * ρ (b - i)
      ≤ S / r ^ b + (r - 1) * ∑ k ∈ Finset.range b, ρ (k + 1) := by
  have h := parallel_pass_bound r q s ρ b hs hρ
  linarith

/-- Lemma 6.2 magnitude bound packaged for a width-`b` pass. -/
theorem pass_magnitude (r q S : ℝ) (s ρ : ℕ → ℝ) (b : ℕ)
    (hq : q ≤ S / r ^ b) (hs : ∀ i, s i ≤ r - 1) (hρ : ∀ k, 0 ≤ ρ k) :
    q + ∑ i ∈ Finset.range b, s i * ρ (b - i)
      ≤ S / r ^ b + (r - 1) * ∑ k ∈ Finset.range b, ρ (k + 1) :=
  pass_step_bound r q S s ρ b hq hs hρ

/-! ## Theorem 6.3 — specialized overflow bounds -/

/-- Theorem 6.3, iterative schedule `(1,…,1)`: after the final Montgomery round,
  `final(x_{n-1}) ≤ c/r^n + ρ₁(1 − r^{-(n−1)}) + p`. -/
theorem overflow_iterative (r c p ρ₁ : ℝ) (hr : 1 < r) (n : ℕ) (hn : 1 ≤ n)
    (x : ℕ → ℝ) (final : ℝ → ℝ) (h0 : x 0 = c)
    (hstep : ∀ k, x (k + 1) ≤ x k / r + (r - 1) * ρ₁)
    (hfinal : ∀ S, final S ≤ S / r + p) :
    final (x (n - 1)) ≤ c / r ^ n + ρ₁ * (1 - r ^ (-((n : ℝ) - 1))) + p := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hrne : r ≠ 0 := hr0.ne'
  have hn1 : n - 1 + 1 = n := by omega
  have hgeo := iterative_overflow r ρ₁ hr0 c x h0 hstep (n - 1)
  have hpos : (0 : ℝ) < r ^ (n - 1) := by positivity
  have hx : x (n - 1) ≤ c / r ^ (n - 1) + ρ₁ * r * (r ^ (n - 1) - 1) / r ^ (n - 1) := by
    have h1 : (x (n - 1) : ℝ) * r ^ (n - 1) ≤ c + ρ₁ * r * (r ^ (n - 1) - 1) := by nlinarith [hgeo]
    calc x (n - 1)
        = (x (n - 1) * r ^ (n - 1)) / r ^ (n - 1) := by field_simp [pow_ne_zero _ hpos.ne']
      _ ≤ (c + ρ₁ * r * (r ^ (n - 1) - 1)) / r ^ (n - 1) := by gcongr
      _ = c / r ^ (n - 1) + ρ₁ * r * (r ^ (n - 1) - 1) / r ^ (n - 1) := by rw [add_div]
  have hdiv : x (n - 1) / r ≤ c / r ^ n + ρ₁ * (1 - r ^ (-((n : ℝ) - 1))) := by
    have := div_le_div_of_nonneg_right hx (le_of_lt hr0)
    rw [add_div] at this
    rw [show c / r ^ (n - 1) / r = c / r ^ n from by simpa [hn1] using div_div_rpow_succ c r (n - 1) hrne] at this
    rw [show (ρ₁ * r * (r ^ (n - 1) - 1) / r ^ (n - 1)) / r = ρ₁ * (1 - r ^ (-((n : ℝ) - 1))) from by
      have hρdiv : (ρ₁ * r * (r ^ (n - 1) - 1) / r ^ (n - 1)) / r
          = ρ₁ * (1 - (r ^ (n - 1))⁻¹) := by
        field_simp [hrne, hpos.ne']
      have hinv : (r ^ (n - 1))⁻¹ = r ^ (-((n : ℝ) - 1)) := by
        symm
        rw [Real.rpow_neg (le_of_lt hr0)]
        congr 1
        rw [← Nat.cast_pred (R := ℝ) (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le zero_lt_one hn)),
          Real.rpow_natCast]
      rw [hρdiv, hinv]] at this
    exact this
  calc final (x (n - 1)) ≤ x (n - 1) / r + p := hfinal _
    _ ≤ c / r ^ n + ρ₁ * (1 - r ^ (-((n : ℝ) - 1))) + p := by linarith

/-- Theorem 6.3, parallel schedule `(n−1)`: one pass then the final Montgomery round. -/
theorem overflow_parallel (r c p σ x_pre : ℝ) (hr : 1 < r) (n : ℕ) (hn : 1 ≤ n)
    (final : ℝ) (hfinal : final ≤ x_pre / r + p)
    (hx : x_pre ≤ c / r ^ (n - 1) + (r - 1) * σ) :
    final ≤ c / r ^ n + (r - 1) / r * σ + p := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hrne : r ≠ 0 := hr0.ne'
  have hn1 : n - 1 + 1 = n := by omega
  calc final ≤ x_pre / r + p := hfinal
    _ ≤ (c / r ^ (n - 1) + (r - 1) * σ) / r + p := by gcongr
    _ = c / r ^ n + (r - 1) / r * σ + p := by
      rw [add_div, div_div_rpow_succ c r (n - 1) hrne, show n - 1 + 1 = n from hn1]
      ring

/-- Theorem 6.3, logarithmic schedule: weighted correction sum bounded by
  `p·r²/(r−1)²` (from `log_overflow`) yields
  `final ≤ c/r^n + r/(r−1)·p + p`. -/
theorem overflow_log (r c p weighted : ℝ) (hr : 1 < r) (n : ℕ) (hn : 1 ≤ n)
    (x_pre final : ℝ) (hfinal : final ≤ x_pre / r + p)
    (hx : x_pre ≤ c / r ^ (n - 1) + (r - 1) * weighted)
    (hW : weighted ≤ p * r ^ 2 / (r - 1) ^ 2) :
    final ≤ c / r ^ n + r / (r - 1) * p + p := by
  have hr0 : (0 : ℝ) < r := lt_trans zero_lt_one hr
  have hrne : r ≠ 0 := hr0.ne'
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hr1ne : r - 1 ≠ 0 := hr1.ne'
  have hn1 : n - 1 + 1 = n := by omega
  have hcorr : (r - 1) / r * weighted ≤ r / (r - 1) * p := by
    have hbnd := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ (r - 1) / r)
    calc (r - 1) / r * weighted
        ≤ (r - 1) / r * (p * r ^ 2 / (r - 1) ^ 2) := hbnd
      _ = r / (r - 1) * p := by field_simp [hr1ne, hrne]
  calc final ≤ x_pre / r + p := hfinal
    _ ≤ (c / r ^ (n - 1) + (r - 1) * weighted) / r + p := by gcongr
    _ = c / r ^ n + (r - 1) / r * weighted + p := by
      rw [add_div, div_div_rpow_succ c r (n - 1) hrne, show n - 1 + 1 = n from hn1]
      ring
    _ ≤ c / r ^ n + r / (r - 1) * p + p := by linarith [hcorr]

/-! ## Normalization count — conditional subtractions from an overflow bound -/

/-- If a reduced value satisfies `S < (k+1)p`, then `⌊S/p⌋ ≤ k`: at most `k`
conditional subtractions normalize it into `[0,p)`.  This converts every overflow
bound above into a concrete subtraction count `δ`. -/
theorem normalization_count {S p k : ℕ} (hp : 0 < p) (h : S < (k + 1) * p) :
    S / p ≤ k := by
  have : S / p < k + 1 := (Nat.div_lt_iff_lt_mul hp).mpr h
  omega

/-! ## Corollary 6.6 — logarithmic EMR overflow series

The log-depth schedule weights pass `d` by `r^{-d}` with multiplicity `d+1`.  The
governing series `Σ_d (d+1) x^d` converges to `1/(1-x)²`; at `x = 1/r` this gives
the closed-form overflow factor `r²/(r-1)²`. -/

/-- `∑' d, (d+1) x^d = 1/(1-x)²` for `0 ≤ x < 1`. -/
theorem log_series (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun d : ℕ => (d + 1 : ℝ) * x ^ d) (1 / (1 - x) ^ 2) := by
  have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have hxpos : (0 : ℝ) < 1 - x := by linarith
  have hxne : (1 : ℝ) - x ≠ 0 := hxpos.ne'
  have A : HasSum (fun n : ℕ => (n : ℝ) * x ^ n) (x / (1 - x) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have B : HasSum (fun n : ℕ => x ^ n) (1 - x)⁻¹ := hasSum_geometric_of_norm_lt_one hnorm
  have hfun : (fun d : ℕ => (d + 1 : ℝ) * x ^ d)
      = (fun n : ℕ => (n : ℝ) * x ^ n + x ^ n) := by
    funext n; push_cast; ring
  have hval : (1 : ℝ) / (1 - x) ^ 2 = x / (1 - x) ^ 2 + (1 - x)⁻¹ := by
    field_simp; ring
  rw [hfun, hval]
  exact A.add B

/-- Partial sums are bounded by the limit `1/(1-x)²`. -/
theorem log_partial_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (D : ℕ) :
    ∑ d ∈ Finset.range D, (d + 1 : ℝ) * x ^ d ≤ 1 / (1 - x) ^ 2 := by
  have hs := log_series x hx0 hx1
  have hnn : ∀ d : ℕ, 0 ≤ (d + 1 : ℝ) * x ^ d := fun d => by positivity
  have key := hs.summable.sum_le_tsum (Finset.range D) (fun i _ => hnn i)
  rw [hs.tsum_eq] at key
  exact key

/-- At `x = 1/r`, `1/(1-1/r)² = r²/(r-1)²`. -/
theorem log_factor (r : ℝ) (hr : 1 < r) : 1 / (1 - 1 / r) ^ 2 = r ^ 2 / (r - 1) ^ 2 := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hrne : r ≠ 0 := hr0.ne'
  have hr1ne : r - 1 ≠ 0 := hr1.ne'
  rw [eq_div_iff (by positivity)]
  field_simp

/-- Logarithmic EMR overflow series bound: the accumulated correction factor is
at most `r²/(r-1)²`, uniformly in the number of passes. -/
theorem log_overflow (r : ℝ) (hr : 1 < r) (D : ℕ) :
    ∑ d ∈ Finset.range D, (d + 1 : ℝ) * (1 / r) ^ d ≤ r ^ 2 / (r - 1) ^ 2 := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / r := by positivity
  have hx1 : (1 : ℝ) / r < 1 := by rw [div_lt_one hr0]; exact hr
  have h := log_partial_bound (1 / r) hx0 hx1 D
  rwa [log_factor r hr] at h

/-! ## Algorithm 4.2 — executable iterative EMR over `ℕ`

The results above bound an abstract sequence satisfying `x_{k+1} ≤ x_k/r + a_k`.
Here we exhibit the *actual integer program* — using genuine `ℕ` floor division
and remainder — and prove it (i) computes the correct residue mod `p` and
(ii) provably satisfies that recursion.  Hence the abstract correctness and
overflow bounds apply verbatim to the concrete algorithm. -/

/-- One extended (ρ₁) round on the running integer `S`:
`S ↦ ⌊S/r⌋ + (S mod r)·ρ₁`. -/
def emrStep (ρ₁ r S : ℕ) : ℕ := S / r + (S % r) * ρ₁

/-- `k` successive extended rounds. -/
def emrIter (ρ₁ r : ℕ) : ℕ → ℕ → ℕ
  | 0, S => S
  | k + 1, S => emrStep ρ₁ r (emrIter ρ₁ r k S)

/-- The final Montgomery round: `m = μ(S mod r) mod r`, then `S ↦ (S + m·p)/r`. -/
def montStep (μ p r S : ℕ) : ℕ := (S + ((μ * (S % r)) % r) * p) / r

/-- The complete iterative EMR: `n-1` extended rounds then one Montgomery round. -/
def emr (μ ρ₁ p r n c : ℕ) : ℕ := montStep μ p r (emrIter ρ₁ r (n - 1) c)

/-- Base-`r` digit `i` of `c` (least significant at `i = 0`). -/
def digit (c r i : ℕ) : ℕ := c / r ^ i % r

/-- One width-`b` reduction pass on the integer accumulator. -/
def passWidth (ρ : ℕ → ℕ) (r b S : ℕ) : ℕ :=
  S / r ^ b + ∑ i ∈ Finset.range b, digit S r i * ρ (b - i)

/-- Parallel pre-round value: `⌊c/r^{n-1}⌋ + Σ_{i<n-1} c'_i ρ_{n-1-i}`. -/
def parallelPre (ρ : ℕ → ℕ) (r n c : ℕ) : ℕ :=
  passWidth ρ r (n - 1) c

/-- Parallel EMR: one wide pass then the final Montgomery round. -/
def emrParallel (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) : ℕ :=
  montStep μ p r (parallelPre ρ r n c)

/-- Halving-schedule pass widths for log EMR (`b_t = ⌈D_{t-1}/2⌉`). -/
def logWidths (n : ℕ) : List ℕ :=
  let rec go (D : ℕ) : List ℕ :=
    if D = 0 then [] else (D + 1) / 2 :: go (D / 2)
  go (n - 1)

/-- Apply a list of pass widths in order. -/
def logFold (ρ : ℕ → ℕ) (r : ℕ) : List ℕ → ℕ → ℕ
  | [], S => S
  | b :: bs, S => logFold ρ r bs (passWidth ρ r b S)

/-- Log EMR: halving passes then the final Montgomery round. -/
def emrLog (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) : ℕ :=
  montStep μ p r (logFold ρ r (logWidths n) c)

private theorem digit_le (c r i : ℕ) (hr : 0 < r) : digit c r i < r :=
  Nat.mod_lt _ hr

private theorem digit_le_pred (c r i : ℕ) (hr : 2 ≤ r) : digit c r i ≤ r - 1 := by
  have := digit_le c r i (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr))
  omega

private theorem mod_mul_add (a m c r : ℕ) (hr : 0 < r) (hm : 0 < m) (hc : c < m) :
    (a * m + c) % (m * r) = (a % r) * m + c := by
  set s := a % r
  set q := a / r
  have ha : a = q * r + s := by rw [← Nat.div_add_mod a r, Nat.mul_comm r q]
  have hs : s < r := Nat.mod_lt a hr
  calc (a * m + c) % (m * r)
      = ((q * r + s) * m + c) % (m * r) := by rw [ha]
    _ = (q * (r * m) + (s * m + c)) % (m * r) := by ring_nf
    _ = (s * m + c) % (m * r) := by
        have h0 : q * (r * m) % (m * r) = 0 := by
          rw [Nat.mul_comm r m]
          exact Nat.mul_mod_left q (m * r)
        rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod]
    _ = s * m + c := Nat.mod_eq_of_lt (by nlinarith [hc, hs, hm])

private theorem mod_add_div_pow (S r b : ℕ) (hr : 0 < r) :
    digit S r b * r ^ b + S % r ^ b = S % r ^ (b + 1) := by
  unfold digit
  have hm : 0 < r ^ b := pow_pos hr b
  have hc : S % r ^ b < r ^ b := Nat.mod_lt S hm
  have h := mod_mul_add (S / r ^ b) (r ^ b) (S % r ^ b) r hr hm hc
  have hS : S / r ^ b * r ^ b + S % r ^ b = S := by
    rw [Nat.mul_comm (S / r ^ b), Nat.div_add_mod]
  calc S / r ^ b % r * r ^ b + S % r ^ b
      = (S / r ^ b * r ^ b + S % r ^ b) % (r ^ b * r) := h.symm
    _ = S % (r ^ b * r) := by rw [hS]
    _ = S % r ^ (b + 1) := by rw [← pow_succ]

private theorem mod_pow_eq_sum_digit (S r b : ℕ) (hr : 0 < r) :
    S % r ^ b = ∑ i ∈ Finset.range b, digit S r i * r ^ i := by
  induction b with
  | zero => simp [digit, pow_zero, Nat.mod_one]
  | succ b ih =>
    rw [Finset.sum_range_succ, ← mod_add_div_pow S r b hr, ih, add_comm]

private theorem nat_pow_decomp (S r b : ℕ) (hr : 0 < r) :
    (S / r ^ b) * r ^ b + ∑ i ∈ Finset.range b, digit S r i * r ^ i = S := by
  rw [← mod_pow_eq_sum_digit S r b hr, Nat.mul_comm (S / r ^ b), Nat.div_add_mod]

/-! ### Correctness mod `p` -/

/-- One extended round divides the value by `r` mod `p`: `r · emrStep(S) ≡ S`. -/
theorem emrStep_correct {p : ℕ} (r ρ₁ S : ℕ) (hρ : (r : ZMod p) * (ρ₁ : ZMod p) = 1) :
    (r : ZMod p) * (emrStep ρ₁ r S : ZMod p) = (S : ZMod p) := by
  have hdm : (r : ZMod p) * ((S / r : ℕ) : ZMod p) + ((S % r : ℕ) : ZMod p) = (S : ZMod p) := by
    calc (r : ZMod p) * ((S / r : ℕ) : ZMod p) + ((S % r : ℕ) : ZMod p)
        = ((r * (S / r) + S % r : ℕ) : ZMod p) := by push_cast; ring
      _ = (S : ZMod p) := by rw [Nat.div_add_mod]
  unfold emrStep
  push_cast
  linear_combination ((S % r : ℕ) : ZMod p) * hρ + hdm

/-- After `k` rounds, `r^k · emrIter(k,S) ≡ S`: the running value is `S·r^{-k} mod p`. -/
theorem emrIter_correct {p : ℕ} (r ρ₁ : ℕ) (hρ : (r : ZMod p) * (ρ₁ : ZMod p) = 1) (k S : ℕ) :
    (r : ZMod p) ^ k * (emrIter ρ₁ r k S : ZMod p) = (S : ZMod p) := by
  induction k generalizing S with
  | zero => simp [emrIter]
  | succ k ih =>
    have hstep : (r : ZMod p) * (emrStep ρ₁ r (emrIter ρ₁ r k S) : ZMod p)
        = (emrIter ρ₁ r k S : ZMod p) := emrStep_correct r ρ₁ _ hρ
    calc (r : ZMod p) ^ (k + 1) * (emrIter ρ₁ r (k + 1) S : ZMod p)
        = (r : ZMod p) ^ k * ((r : ZMod p) * (emrStep ρ₁ r (emrIter ρ₁ r k S) : ZMod p)) := by
          rw [show emrIter ρ₁ r (k + 1) S = emrStep ρ₁ r (emrIter ρ₁ r k S) from rfl, pow_succ]
          ring
      _ = (r : ZMod p) ^ k * (emrIter ρ₁ r k S : ZMod p) := by rw [hstep]
      _ = (S : ZMod p) := ih S

/-- The Montgomery round produces an exact division: `r ∣ S + m·p`, where
`μ` is `-p⁻¹ mod r` (encoded as `p·μ ≡ -1 (mod r)`). -/
theorem montStep_dvd (μ p r S : ℕ) (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    r ∣ (S + ((μ * (S % r)) % r) * p) := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast [ZMod.natCast_mod]
  linear_combination (S : ZMod r) * hμ

/-- One Montgomery round also divides the value by `r` mod `p`: `r · montStep(S) ≡ S`. -/
theorem montStep_correct {p : ℕ} (μ r S : ℕ) (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    (r : ZMod p) * (montStep μ p r S : ZMod p) = (S : ZMod p) := by
  have hdvd : r ∣ (S + ((μ * (S % r)) % r) * p) := montStep_dvd μ p r S hμ
  have hmul : montStep μ p r S * r = S + ((μ * (S % r)) % r) * p := Nat.div_mul_cancel hdvd
  have h := congrArg (Nat.cast : ℕ → ZMod p) hmul
  push_cast at h
  rw [mul_comm, h, ZMod.natCast_self, mul_zero, add_zero]

/-- **Full correctness.**  `r^n · emr ≡ c (mod p)`, i.e. `emr ≡ c·R⁻¹` with `R = r^n`. -/
theorem emr_correct {p : ℕ} (μ ρ₁ r n c : ℕ) (hn : 1 ≤ n)
    (hρ : (r : ZMod p) * (ρ₁ : ZMod p) = 1) (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    (r : ZMod p) ^ n * (emr μ ρ₁ p r n c : ZMod p) = (c : ZMod p) := by
  have hn1 : n - 1 + 1 = n := by omega
  have key : (r : ZMod p) * (montStep μ p r (emrIter ρ₁ r (n - 1) c) : ZMod p)
      = (emrIter ρ₁ r (n - 1) c : ZMod p) := montStep_correct μ r _ hμ
  have hc : (r : ZMod p) ^ (n - 1) * (emrIter ρ₁ r (n - 1) c : ZMod p) = (c : ZMod p) :=
    emrIter_correct r ρ₁ hρ (n - 1) c
  unfold emr
  calc (r : ZMod p) ^ n * (montStep μ p r (emrIter ρ₁ r (n - 1) c) : ZMod p)
      = (r : ZMod p) ^ (n - 1 + 1) * (montStep μ p r (emrIter ρ₁ r (n - 1) c) : ZMod p) := by
        rw [hn1]
    _ = (r : ZMod p) ^ (n - 1)
          * ((r : ZMod p) * (montStep μ p r (emrIter ρ₁ r (n - 1) c) : ZMod p)) := by
        rw [pow_succ]; ring
    _ = (r : ZMod p) ^ (n - 1) * (emrIter ρ₁ r (n - 1) c : ZMod p) := by rw [key]
    _ = (c : ZMod p) := hc

/-- A width-`b` pass divides the accumulator by `r^b` mod `p`. -/
theorem passWidth_correct {p : ℕ} (ρ : ℕ → ℕ) (r b S : ℕ) (hr : 0 < r)
    (hρ : ∀ k, 1 ≤ k → (r : ZMod p) ^ k * (ρ k : ZMod p) = 1) :
    (r : ZMod p) ^ b * (passWidth ρ r b S : ZMod p) = (S : ZMod p) := by
  have hpass := pass_correct (r : ZMod p) (fun k => (ρ k : ZMod p))
    (fun i => (digit S r i : ZMod p)) ((S / r ^ b : ℕ) : ZMod p) b hρ
  unfold passWidth
  push_cast
  rw [hpass]
  have hsum : ∑ i ∈ Finset.range b, (digit S r i : ZMod p) * (r : ZMod p) ^ i
      = (S % r ^ b : ZMod p) := by
    norm_cast
    rw [mod_pow_eq_sum_digit S r b hr]
  have hmain : (r : ZMod p) ^ b * ((S / r ^ b : ℕ) : ZMod p) + (S % r ^ b : ZMod p) = (S : ZMod p) := by
    calc (r : ZMod p) ^ b * ((S / r ^ b : ℕ) : ZMod p) + (S % r ^ b : ZMod p)
        = ((r ^ b * (S / r ^ b) + S % r ^ b : ℕ) : ZMod p) := by push_cast; ring
      _ = (S : ZMod p) := by
        show ((r ^ b * (S / r ^ b) + S % r ^ b : ℕ) : ZMod p) = (S : ZMod p)
        rw [Nat.div_add_mod S (r ^ b)]
  rw [hsum, hmain]

/-- Applying a list of pass widths divides by `r^{∑ widths}` mod `p`. -/
theorem logFold_correct {p : ℕ} (ρ : ℕ → ℕ) (r : ℕ) (bs : List ℕ) (S : ℕ) (hr : 0 < r)
    (hρ : ∀ k, 1 ≤ k → (r : ZMod p) ^ k * (ρ k : ZMod p) = 1) :
    (r : ZMod p) ^ bs.sum * (logFold ρ r bs S : ZMod p) = (S : ZMod p) := by
  induction bs generalizing S with
  | nil => simp [logFold]
  | cons b bs ih =>
    rw [logFold, List.sum_cons]
    have hw := passWidth_correct ρ r b S hr hρ
    calc (r : ZMod p) ^ (b + bs.sum) * logFold ρ r bs (passWidth ρ r b S)
        = (r : ZMod p) ^ b * ((r : ZMod p) ^ bs.sum * logFold ρ r bs (passWidth ρ r b S)) := by
          rw [pow_add, mul_assoc]
      _ = (r : ZMod p) ^ b * (passWidth ρ r b S : ZMod p) := by rw [ih]
      _ = (S : ZMod p) := hw

private theorem logWidths_go_sum (D : ℕ) : (logWidths.go D).sum = D := by
  refine Nat.strongRecOn D ?_
  intro D ih
  rcases D with _ | D
  · simp [logWidths.go, List.sum_nil]
  · rw [logWidths.go, if_neg (Nat.succ_ne_zero _)]
    simp only [List.sum_cons]
    have hlt : (D + 1) / 2 < D + 1 := Nat.div_lt_self (Nat.succ_pos D) (by decide : 1 < 2)
    rw [ih ((D + 1) / 2) hlt]
    omega

theorem logWidths_sum (n : ℕ) : (logWidths n).sum = n - 1 :=
  logWidths_go_sum (n - 1)

/-- Geometric weight `Σ_t Σ_{b_t}/r^{(n-1)-B_t}` for a pass schedule (Theorem 6.3). -/
noncomputable def scheduleWeight (ρ : ℕ → ℕ) (r : ℕ) : List ℕ → ℝ
  | [] => 0
  | b :: bs => (sigmaSum ρ b : ℝ) / (r : ℝ) ^ bs.sum + scheduleWeight ρ r bs

/-- EMR for an arbitrary pass schedule `bs` with `bs.sum = n − 1`. -/
def emrSchedule (μ : ℕ) (ρ : ℕ → ℕ) (p r c : ℕ) (bs : List ℕ) : ℕ :=
  montStep μ p r (logFold ρ r bs c)

/-- **Theorem 6.3 (correctness).** Any schedule with `bs.sum = n−1` yields `r^n · output ≡ c`. -/
theorem emrSchedule_correct {p : ℕ} (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (bs : List ℕ)
    (hn : 1 ≤ n) (hsum : bs.sum = n - 1) (hr : 0 < r)
    (hρ : ∀ k, 1 ≤ k → (r : ZMod p) ^ k * (ρ k : ZMod p) = 1)
    (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    (r : ZMod p) ^ n * (emrSchedule μ ρ p r c bs : ZMod p) = (c : ZMod p) := by
  have hfold := logFold_correct ρ r bs c hr hρ
  have hmont := montStep_correct μ r (logFold ρ r bs c) hμ
  unfold emrSchedule
  calc (r : ZMod p) ^ n * (montStep μ p r (logFold ρ r bs c) : ZMod p)
      = (r : ZMod p) ^ (n - 1 + 1) * (montStep μ p r (logFold ρ r bs c) : ZMod p) := by
        rw [Nat.sub_add_cancel hn]
    _ = (r : ZMod p) ^ (n - 1) * ((r : ZMod p) * (montStep μ p r (logFold ρ r bs c) : ZMod p)) := by
        rw [pow_succ, mul_assoc]
    _ = (r : ZMod p) ^ (n - 1) * (logFold ρ r bs c : ZMod p) := by rw [hmont]
    _ = (c : ZMod p) := by rw [← hfold, hsum]

theorem emrParallel_is_schedule (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) :
    emrParallel μ ρ p r n c = emrSchedule μ ρ p r c [n - 1] := by
  unfold emrParallel emrSchedule parallelPre
  simp [logFold, passWidth]

theorem emrLog_is_schedule (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) :
    emrLog μ ρ p r n c = emrSchedule μ ρ p r c (logWidths n) := by
  unfold emrLog emrSchedule
  rfl

/-- Parallel pre-round: `r^{n-1} · parallelPre ≡ c (mod p)`. -/
theorem parallelPre_correct {p : ℕ} (ρ : ℕ → ℕ) (r n c : ℕ) (hn : 1 ≤ n) (hr : 0 < r)
    (hρ : ∀ k, 1 ≤ k → (r : ZMod p) ^ k * (ρ k : ZMod p) = 1) :
    (r : ZMod p) ^ (n - 1) * (parallelPre ρ r n c : ZMod p) = (c : ZMod p) := by
  have hn0 : n - 1 + 1 = n := by omega
  simpa [parallelPre, hn0] using passWidth_correct ρ r (n - 1) c hr hρ

/-- **Parallel EMR correctness.** `r^n · emrParallel ≡ c (mod p)`. -/
theorem emrParallel_correct {p : ℕ} (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (hn : 1 ≤ n) (hr : 0 < r)
    (hρ : ∀ k, 1 ≤ k → (r : ZMod p) ^ k * (ρ k : ZMod p) = 1)
    (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    (r : ZMod p) ^ n * (emrParallel μ ρ p r n c : ZMod p) = (c : ZMod p) := by
  have hpre := parallelPre_correct ρ r n c hn hr hρ
  have hmont := montStep_correct μ r (parallelPre ρ r n c) hμ
  unfold emrParallel
  calc (r : ZMod p) ^ n * (montStep μ p r (parallelPre ρ r n c) : ZMod p)
      = (r : ZMod p) ^ (n - 1 + 1) * (montStep μ p r (parallelPre ρ r n c) : ZMod p) := by
        rw [Nat.sub_add_cancel hn]
    _ = (r : ZMod p) ^ (n - 1) * ((r : ZMod p) * (montStep μ p r (parallelPre ρ r n c) : ZMod p)) := by
        rw [pow_succ, mul_assoc]
    _ = (r : ZMod p) ^ (n - 1) * (parallelPre ρ r n c : ZMod p) := by rw [hmont]
    _ = (c : ZMod p) := hpre

/-- **Log EMR correctness.** `r^n · emrLog ≡ c (mod p)`. -/
theorem emrLog_correct {p : ℕ} (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (hn : 1 ≤ n) (hr : 0 < r)
    (hρ : ∀ k, 1 ≤ k → (r : ZMod p) ^ k * (ρ k : ZMod p) = 1)
    (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    (r : ZMod p) ^ n * (emrLog μ ρ p r n c : ZMod p) = (c : ZMod p) := by
  have hfold := logFold_correct ρ r (logWidths n) c hr hρ
  have hsum := logWidths_sum n
  have hmont := montStep_correct μ r (logFold ρ r (logWidths n) c) hμ
  unfold emrLog
  calc (r : ZMod p) ^ n * (montStep μ p r (logFold ρ r (logWidths n) c) : ZMod p)
      = (r : ZMod p) ^ (n - 1 + 1) * (montStep μ p r (logFold ρ r (logWidths n) c) : ZMod p) := by
        rw [Nat.sub_add_cancel hn]
    _ = (r : ZMod p) ^ (n - 1) * ((r : ZMod p) * (montStep μ p r (logFold ρ r (logWidths n) c) : ZMod p)) := by
        rw [pow_succ, mul_assoc]
    _ = (r : ZMod p) ^ (n - 1) * (logFold ρ r (logWidths n) c : ZMod p) := by rw [hmont]
    _ = (c : ZMod p) := by rw [← hfold, hsum]

/-! ### Overflow: the concrete program satisfies the recursion hypothesis -/

/-- The integer round satisfies the real recursion bound used by `iterative_overflow_le`. -/
theorem emrStep_real_bound (r ρ₁ S : ℕ) (hr : 0 < r) :
    (emrStep ρ₁ r S : ℝ) ≤ (S : ℝ) / (r : ℝ) + ((r : ℝ) - 1) * (ρ₁ : ℝ) := by
  unfold emrStep
  push_cast
  have h1 : ((S / r : ℕ) : ℝ) ≤ (S : ℝ) / (r : ℝ) := Nat.cast_div_le
  have hmlt : S % r < r := Nat.mod_lt _ hr
  have h2 : ((S % r : ℕ) : ℝ) ≤ (r : ℝ) - 1 := by
    have hle : S % r + 1 ≤ r := hmlt
    have : ((S % r : ℕ) : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hle
    linarith
  have hρnn : (0 : ℝ) ≤ (ρ₁ : ℝ) := Nat.cast_nonneg ρ₁
  have hprod : ((S % r : ℕ) : ℝ) * (ρ₁ : ℝ) ≤ ((r : ℝ) - 1) * (ρ₁ : ℝ) :=
    mul_le_mul_of_nonneg_right h2 hρnn
  linarith

/-- **Concrete overflow of the extended rounds.**  The actual integer value after
`N` rounds obeys the closed bound `≤ c/r^N + ρ₁ r`. -/
theorem emrIter_overflow (r ρ₁ c : ℕ) (hr : 1 < r) (N : ℕ) :
    (emrIter ρ₁ r N c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ N + (ρ₁ : ℝ) * (r : ℝ) := by
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr0 : 0 < r := by omega
  exact iterative_overflow_le (r : ℝ) (ρ₁ : ℝ) hr1 (Nat.cast_nonneg ρ₁) (c : ℝ)
    (fun k => (emrIter ρ₁ r k c : ℝ)) (by simp [emrIter])
    (fun k => by
      show (emrIter ρ₁ r (k + 1) c : ℝ)
        ≤ (emrIter ρ₁ r k c : ℝ) / (r : ℝ) + ((r : ℝ) - 1) * (ρ₁ : ℝ)
      rw [show emrIter ρ₁ r (k + 1) c = emrStep ρ₁ r (emrIter ρ₁ r k c) from rfl]
      exact emrStep_real_bound r ρ₁ (emrIter ρ₁ r k c) hr0)
    N

/-- The Montgomery round contributes at most `+p`: `montStep(S) ≤ S/r + p`. -/
theorem montStep_real_bound (μ p r S : ℕ) (hr : 0 < r) :
    (montStep μ p r S : ℝ) ≤ (S : ℝ) / (r : ℝ) + (p : ℝ) := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hmlt : (μ * (S % r)) % r < r := Nat.mod_lt _ hr
  have hmle : (((μ * (S % r)) % r : ℕ) : ℝ) ≤ (r : ℝ) - 1 := by
    have hle : (μ * (S % r)) % r + 1 ≤ r := hmlt
    have : (((μ * (S % r)) % r : ℕ) : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hle
    linarith
  have h1 : (montStep μ p r S : ℝ)
      ≤ ((S + ((μ * (S % r)) % r) * p : ℕ) : ℝ) / (r : ℝ) := by
    rw [show montStep μ p r S = (S + ((μ * (S % r)) % r) * p) / r from rfl]
    exact Nat.cast_div_le
  rw [show ((S + ((μ * (S % r)) % r) * p : ℕ) : ℝ)
        = (S : ℝ) + (((μ * (S % r)) % r : ℕ) : ℝ) * (p : ℝ) from by push_cast; ring] at h1
  have hmp : (((μ * (S % r)) % r : ℕ) : ℝ) * (p : ℝ) / (r : ℝ) ≤ (p : ℝ) := by
    rw [div_le_iff₀ hr']
    nlinarith [hmle, hpnn]
  rw [add_div] at h1
  linarith

/-- **Capstone: concrete overflow of the full algorithm.**
`emr ≤ c/r^n + ρ₁ + p` in `ℝ`. With `c < pR` and `ρ₁ < p` this implies
`emr < 3p` and hence `δ ≤ 2` (Corollary 6.4). -/
theorem emr_overflow (μ ρ₁ p r n c : ℕ) (hr : 1 < r) (hn : 1 ≤ n) :
    (emr μ ρ₁ p r n c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n + (ρ₁ : ℝ) + (p : ℝ) := by
  have hr0 : 0 < r := by omega
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hn1 : n - 1 + 1 = n := by omega
  have hb := montStep_real_bound μ p r (emrIter ρ₁ r (n - 1) c) hr0
  have hi := emrIter_overflow r ρ₁ c hr (n - 1)
  have hr1 : (r : ℝ) ^ (n - 1) * (r : ℝ) = (r : ℝ) ^ n := by
    rw [← pow_succ, hn1]
  have hsimp : ((c : ℝ) / (r : ℝ) ^ (n - 1) + (ρ₁ : ℝ) * (r : ℝ)) / (r : ℝ)
      = (c : ℝ) / (r : ℝ) ^ n + (ρ₁ : ℝ) := by
    rw [add_div, div_div, hr1, mul_div_assoc, div_self hr'.ne', mul_one]
  have hdiv : (emrIter ρ₁ r (n - 1) c : ℝ) / (r : ℝ)
      ≤ ((c : ℝ) / (r : ℝ) ^ (n - 1) + (ρ₁ : ℝ) * (r : ℝ)) / (r : ℝ) :=
    (div_le_div_iff_of_pos_right hr').mpr hi
  rw [show emr μ ρ₁ p r n c = montStep μ p r (emrIter ρ₁ r (n - 1) c) from rfl]
  calc (montStep μ p r (emrIter ρ₁ r (n - 1) c) : ℝ)
      ≤ (emrIter ρ₁ r (n - 1) c : ℝ) / (r : ℝ) + (p : ℝ) := hb
    _ ≤ ((c : ℝ) / (r : ℝ) ^ (n - 1) + (ρ₁ : ℝ) * (r : ℝ)) / (r : ℝ) + (p : ℝ) := by linarith
    _ = (c : ℝ) / (r : ℝ) ^ n + (ρ₁ : ℝ) + (p : ℝ) := by rw [hsimp]

/-- Tighter Corollary 6.4 overflow bound (`T_iter = ρ₁(1−r^{−(n−1)})`). -/
theorem emr_overflow_tight (μ ρ₁ p r n c : ℕ) (hr : 1 < r) (hn : 1 ≤ n) :
    (emr μ ρ₁ p r n c : ℝ) ≤
      (c : ℝ) / (r : ℝ) ^ n + (ρ₁ : ℝ) * (1 - (r : ℝ) ^ (-((n : ℝ) - 1))) + (p : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hr)
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h := overflow_iterative (r : ℝ) (c : ℝ) (p : ℝ) (ρ₁ : ℝ) hr1 n hn
    (fun k => (emrIter ρ₁ r k c : ℝ)) (fun S => S / (r : ℝ) + (p : ℝ))
    (by simp [emrIter])
    (fun k => by
      rw [show emrIter ρ₁ r (k + 1) c = emrStep ρ₁ r (emrIter ρ₁ r k c) from rfl]
      exact emrStep_real_bound r ρ₁ (emrIter ρ₁ r k c) (by omega))
    (fun _ => le_rfl)
  rw [show emr μ ρ₁ p r n c = montStep μ p r (emrIter ρ₁ r (n - 1) c) from rfl]
  have hfinal := montStep_real_bound μ p r (emrIter ρ₁ r (n - 1) c) (by omega)
  linarith [h, hfinal]

/-- A single Montgomery round on a one-digit-over-`p` input stays below `2p`. -/
theorem montStep_lt_2p (μ p r S : ℕ) (hr : 2 ≤ r) (hp : 0 < p) (hS : S < p * r) :
    montStep μ p r S < 2 * p := by
  have hr0 : 0 < r := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr)
  have h := montStep_real_bound μ p r S hr0
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hS' : (S : ℝ) < (p : ℝ) * (r : ℝ) := by exact_mod_cast hS
  have hdiv : (S : ℝ) / (r : ℝ) < (p : ℝ) := by
    rw [div_lt_iff₀ hr']
    nlinarith
  have hlt : (montStep μ p r S : ℝ) < 2 * (p : ℝ) := by nlinarith [h, hdiv]
  exact_mod_cast hlt

theorem montStep_delta_le_one (μ p r S : ℕ) (hr : 2 ≤ r) (hp : 0 < p) (hS : S < p * r) :
    montStep μ p r S / p ≤ 1 :=
  baseline_subtraction_count hp (montStep_lt_2p μ p r S hr hp hS)

/-! ### Executable baseline Montgomery scan (Proposition 6.1) -/

/-- Montgomery digit `m = μ(S mod r) mod r` chosen in one scan round. -/
def montDigit (μ r S : ℕ) : ℕ := (μ * (S % r)) % r

/-- Standard Montgomery scan: `n` successive `montStep` rounds. -/
def montScan (μ p r : ℕ) : ℕ → ℕ → ℕ
  | 0, S => S
  | n + 1, S => montStep μ p r (montScan μ p r n S)

/-- Accumulated digit polynomial `M = Σ_{j<n} m_j r^j` from the scan. -/
def montM (μ p r : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, c => montDigit μ r (montScan μ p r n c) * r ^ n + montM μ p r n c

private theorem montDigit_le (μ r S : ℕ) (hr : 2 ≤ r) : montDigit μ r S ≤ r - 1 := by
  unfold montDigit
  have hr0 : 0 < r := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr)
  exact Nat.le_sub_of_add_le (Nat.succ_le_of_lt (Nat.mod_lt _ hr0))

private theorem montM_eq_sum (μ p r n c : ℕ) :
    montM μ p r n c =
      ∑ j ∈ Finset.range n, montDigit μ r (montScan μ p r j c) * r ^ j := by
  induction n generalizing c with
  | zero => simp [montM]
  | succ n ih =>
    simp [montM, montScan, ih, Finset.sum_range_succ, pow_succ]
    ring

theorem montScan_decomp (μ p r n c : ℕ) (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    r ^ n * montScan μ p r n c = c + p * montM μ p r n c := by
  induction n generalizing c with
  | zero => simp [montScan, montM]
  | succ n ih =>
    set S := montScan μ p r n c
    set m := montDigit μ r S
    have hmul : montStep μ p r S * r = S + m * p := by
      have hdvd := montStep_dvd μ p r S hμ
      dsimp [montStep, montDigit]
      exact Nat.div_mul_cancel hdvd
    have ih' := ih c
    simp [montScan, montM]
    calc r ^ (n + 1) * montStep μ p r S
        = r ^ n * (montStep μ p r S * r) := by ring
      _ = r ^ n * (S + m * p) := by rw [hmul]
      _ = r ^ n * S + p * m * r ^ n := by ring
      _ = c + p * montM μ p r n c + p * m * r ^ n := by rw [ih']
      _ = c + p * (montDigit μ r S * r ^ n + montM μ p r n c) := by ring

theorem montM_le (μ p r n c : ℕ) (hr : 1 < r) :
    montM μ p r n c ≤ r ^ n - 1 := by
  let m := fun j => montDigit μ r (montScan μ p r j c)
  have hm : ∀ j, j < n → m j ≤ r - 1 := fun j _ => montDigit_le μ r _ (by omega)
  rw [montM_eq_sum]
  exact montgomery_M_le hr m hm

theorem montScan_eq_div (μ p r n c : ℕ) (hμ : (p : ZMod r) * (μ : ZMod r) = -1) (hr : 0 < r) :
    montScan μ p r n c = (c + p * montM μ p r n c) / r ^ n := by
  have h := montScan_decomp μ p r n c hμ
  have hrn : 0 < r ^ n := pow_pos hr n
  calc montScan μ p r n c
      = (r ^ n * montScan μ p r n c) / r ^ n := (Nat.mul_div_cancel_left _ hrn).symm
    _ = (c + p * montM μ p r n c) / r ^ n := by rw [h]

theorem montScan_baseline (μ p r n c : ℕ) (hμ : (p : ZMod r) * (μ : ZMod r) = -1)
    (hr : 1 < r) (_hn : 0 < n) (hc : c < p * r ^ n) :
    montScan μ p r n c < 2 * p := by
  have hM := montM_le μ p r n c hr
  rw [montScan_eq_div μ p r n c hμ (Nat.zero_lt_of_lt hr)]
  exact baseline (R := r ^ n) (pow_pos (Nat.zero_lt_of_lt hr) n) hM hc

theorem montScan_delta_le_one (μ p r n c : ℕ) (hμ : (p : ZMod r) * (μ : ZMod r) = -1)
    (hr : 1 < r) (hn : 0 < n) (hp : 0 < p) (hc : c < p * r ^ n) :
    montScan μ p r n c / p ≤ 1 :=
  baseline_subtraction_count hp (montScan_baseline μ p r n c hμ hr hn hc)

theorem montScan_correct {p : ℕ} (μ p r n c : ℕ) (_hn : 0 < n) (_hr : 0 < r)
    (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    (r : ZMod p) ^ n * (montScan μ p r n c : ZMod p) = (c : ZMod p) := by
  have h := montScan_decomp μ p r n c hμ
  apply_fun (fun x => (x : ZMod p)) at h
  push_cast at h
  rw [ZMod.natCast_self, zero_mul, add_zero] at h
  exact h

/-- Real overflow bound for a concrete width-`b` pass. -/
theorem passWidth_real_bound (ρ : ℕ → ℕ) (r b S : ℕ) (hr : 2 ≤ r)
    (hρ : ∀ k, 0 ≤ (ρ k : ℝ)) :
    (passWidth ρ r b S : ℝ) ≤ (S : ℝ) / (r : ℝ) ^ b +
      ((r : ℝ) - 1) * (sigmaSum ρ b : ℝ) := by
  unfold passWidth digit
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr))
  have hrpos : 0 < r := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr)
  have hbpos : 0 < r ^ b := pow_pos hrpos b
  have hq : ((S / r ^ b : ℕ) : ℝ) ≤ (S : ℝ) / (r : ℝ) ^ b := by
    rw [← Nat.cast_pow]
    exact Nat.cast_div_le
  have hs : ∀ i, (digit S r i : ℝ) ≤ (r : ℝ) - 1 := fun i => by
    rw [← Nat.cast_pred hrpos]
    simp [digit]
    exact_mod_cast digit_le_pred S r i hr
  have hρ' : ∀ k, (0 : ℝ) ≤ (ρ k : ℝ) := hρ
  have h := pass_magnitude (r : ℝ) ((S / r ^ b : ℕ) : ℝ) (S : ℝ)
    (fun i => (digit S r i : ℝ)) (fun k => (ρ k : ℝ)) b hq hs hρ'
  calc (passWidth ρ r b S : ℝ)
      = ((S / r ^ b : ℕ) : ℝ) + ∑ i ∈ Finset.range b, (digit S r i : ℝ) * (ρ (b - i) : ℝ) := by
        unfold passWidth digit; push_cast; ring
    _ ≤ (S : ℝ) / (r : ℝ) ^ b + ((r : ℝ) - 1) * (sigmaSum ρ b : ℝ) := by
      simpa [sigmaSum] using h

/-- Real overflow bound after an arbitrary pass schedule (Theorem 6.3, pre-Montgomery). -/
theorem logFold_real_bound (ρ : ℕ → ℕ) (r c : ℕ) (bs : List ℕ) (hr : 2 ≤ r)
    (hρ : ∀ k, 0 ≤ (ρ k : ℝ)) :
    (logFold ρ r bs c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ bs.sum +
      ((r : ℝ) - 1) * scheduleWeight ρ r bs := by
  induction bs generalizing c with
  | nil => simp [logFold, scheduleWeight]
  | cons b bs ih =>
    rw [logFold, scheduleWeight, List.sum_cons]
    have hpass := passWidth_real_bound ρ r b c hr hρ
    have hrpos : (0 : ℝ) < (r : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr))
    have ih' := ih (passWidth ρ r b c)
    have hdiv : (passWidth ρ r b c : ℝ) / (r : ℝ) ^ bs.sum
        ≤ (c : ℝ) / (r : ℝ) ^ (b + bs.sum) +
          ((r : ℝ) - 1) * (sigmaSum ρ b : ℝ) / (r : ℝ) ^ bs.sum := by
      have hpos : 0 < (r : ℝ) ^ bs.sum := pow_pos hrpos bs.sum
      have := div_le_div_of_nonneg_right hpass (le_of_lt hpos)
      rw [add_div, div_div, ← pow_add] at this
      exact this
    calc (logFold ρ r bs (passWidth ρ r b c) : ℝ)
        ≤ (passWidth ρ r b c : ℝ) / (r : ℝ) ^ bs.sum +
            ((r : ℝ) - 1) * scheduleWeight ρ r bs := ih'
      _ ≤ (c : ℝ) / (r : ℝ) ^ (b + bs.sum) +
            ((r : ℝ) - 1) * (sigmaSum ρ b : ℝ) / (r : ℝ) ^ bs.sum +
            ((r : ℝ) - 1) * scheduleWeight ρ r bs := by linarith [hdiv]
      _ = (c : ℝ) / (r : ℝ) ^ (b + bs.sum) +
            ((r : ℝ) - 1) * ((sigmaSum ρ b : ℝ) / (r : ℝ) ^ bs.sum +
              scheduleWeight ρ r bs) := by ring

/-- Theorem 6.3 packaged: arbitrary schedule overflow bound. -/
theorem emrSchedule_overflow (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (bs : List ℕ) (hr : 1 < r)
    (hn : 1 ≤ n) (hsum : bs.sum = n - 1) (hr2 : 2 ≤ r)
    (hρ : ∀ k, 0 ≤ (ρ k : ℝ)) :
    (emrSchedule μ ρ p r c bs : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n +
      ((r - 1 : ℕ) : ℝ) / (r : ℝ) * scheduleWeight ρ r bs + (p : ℝ) := by
  have hr0 : 0 < r := by omega
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hcast_r : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (show (1 : ℕ) ≤ r from by omega)
  have hpre := logFold_real_bound ρ r c bs hr2 hρ
  rw [show emrSchedule μ ρ p r c bs = montStep μ p r (logFold ρ r bs c) from rfl]
  have h := overflow_parallel (r : ℝ) (c : ℝ) (p : ℝ) (scheduleWeight ρ r bs)
    (logFold ρ r bs c : ℝ) hr1 n hn
    (montStep μ p r (logFold ρ r bs c) : ℝ)
    (montStep_real_bound μ p r (logFold ρ r bs c) hr0)
    (by rw [hsum] at hpre; exact hpre)
  simpa [hcast_r] using h

/-- Indices `D, D/2, …` visited by the halving schedule. -/
private def logHalfChainFin : ℕ → Finset ℕ
  | 0 => ∅
  | D + 1 => insert ((D + 1) / 2) (logHalfChainFin ((D + 1) / 2))

/-- Halving-chain geometric series `Σ (d+1)/r^d` over remainders `D, D/2, …`. -/
noncomputable def logHalfSeries (r : ℝ) (D : ℕ) : ℝ :=
  ∑ d ∈ logHalfChainFin D, (d + 1 : ℝ) * (1 / r) ^ d

private theorem logHalfChainFin_lt {k d : ℕ} (hk : 0 < k) (hd : d ∈ logHalfChainFin k) : d < k := by
  match k, hd with
  | 0, hd => simp [logHalfChainFin] at hd
  | k + 1, hd =>
    simp [logHalfChainFin] at hd
    rcases hd with rfl | hmem
    · exact Nat.div_lt_self hk (by decide : 1 < 2)
    · have hm : (k + 1) / 2 < k + 1 := Nat.div_lt_self hk (by decide : 1 < 2)
      have hmpos : 0 < (k + 1) / 2 := by
        rcases k with _ | k
        · simp [logHalfChainFin] at hmem
        · exact Nat.div_pos (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))) (by decide : 0 < 2)
      exact lt_trans (logHalfChainFin_lt hmpos hmem) hm

private theorem not_mem_logHalfChainFin {D : ℕ} (hD : D ≠ 0) :
    D / 2 ∉ logHalfChainFin (D / 2) := by
  rcases D with _ | D
  · exact absurd rfl hD
  · by_cases h : (D + 1) / 2 = 0
    · simp [logHalfChainFin, h]
    · intro hmem
      exact Nat.lt_irrefl ((D + 1) / 2) <|
        logHalfChainFin_lt (Nat.pos_of_ne_zero h) hmem

private theorem logHalfChainFin_subset {D d : ℕ} (hd : d ∈ logHalfChainFin D) : d < D + 2 := by
  by_cases hD : D = 0
  · subst hD; simp [logHalfChainFin] at hd
  · exact lt_trans (logHalfChainFin_lt (Nat.pos_of_ne_zero hD) hd) (Nat.lt_succ_of_le (Nat.le_add_right D 1))

private theorem logHalfSeries_succ (r : ℝ) {D : ℕ} (hD : D ≠ 0) (_hr : 0 < r) :
    logHalfSeries r D =
      (↑(D / 2) + 1) * (1 / r) ^ (D / 2) + logHalfSeries r (D / 2) := by
  rcases D with _ | D
  · exact absurd rfl hD
  · simp [logHalfSeries, logHalfChainFin]
    rw [Finset.sum_insert (not_mem_logHalfChainFin (Nat.succ_ne_zero D))]

private theorem logHalfSeries_le (r : ℝ) (hr : 1 < r) (D : ℕ) :
    logHalfSeries r D ≤ r ^ 2 / (r - 1) ^ 2 := by
  have hx0 : (0 : ℝ) ≤ 1 / r := by positivity
  have hx1 : (1 : ℝ) / r < 1 := by
    rw [div_lt_one (by linarith : (0 : ℝ) < r)]
    exact hr
  have hle := log_partial_bound (1 / r) hx0 hx1 (D + 2)
  unfold logHalfSeries
  calc ∑ d ∈ logHalfChainFin D, (d + 1 : ℝ) * (1 / r) ^ d
      ≤ ∑ d ∈ Finset.range (D + 2), (d + 1 : ℝ) * (1 / r) ^ d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd
          rw [Finset.mem_range]
          exact logHalfChainFin_subset hd
        · intro _ _ _; positivity
    _ ≤ r ^ 2 / (r - 1) ^ 2 := by
        rw [← log_factor r hr]
        simpa [div_eq_mul_inv, mul_comm] using hle

private theorem logGoWeight (ρ : ℕ → ℕ) (r p : ℕ) (D : ℕ) (hr : 2 ≤ r) (hp : 0 < p)
    (hρ : ∀ k, 1 ≤ k → ρ k ≤ p - 1) :
    scheduleWeight ρ r (logWidths.go D) ≤ ↑(p - 1) * logHalfSeries (r : ℝ) D := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr))
  induction D using Nat.strongRecOn with
  | _ D ih =>
    by_cases hD : D = 0
    · simp [logWidths.go, scheduleWeight, logHalfSeries, logHalfChainFin, hD]
    · set d := D / 2
      set b := (D + 1) / 2
      have hsum' : (logWidths.go d).sum = d := logWidths_go_sum d
      have hDpos : 0 < D := Nat.pos_of_ne_zero hD
      have hdlt : d < D := Nat.div_lt_self hDpos (by decide : 1 < 2)
      have hbpos : 0 < b := by
        have : 1 ≤ b := by omega
        omega
      have hsigma : (sigmaSum ρ b : ℝ) ≤ ↑b * ↑(p - 1) := by
        have hρ' : ∀ k, 1 ≤ k → k ≤ b → ρ k ≤ p - 1 := fun k hk1 _ => hρ k hk1
        exact_mod_cast sigmaSum_le ρ b p hbpos hρ'
      have hbnd : b ≤ d + 1 := by omega
      have hbndR : (↑b : ℝ) ≤ ↑(d + 1) := by
        exact_mod_cast (show b ≤ d + 1 from hbnd)
      have hpred : (0 : ℝ) ≤ ↑(p - 1) := by exact_mod_cast (Nat.zero_le (p - 1))
      have hsigma' : (sigmaSum ρ b : ℝ) ≤ ↑(d + 1) * ↑(p - 1) :=
        le_trans hsigma (mul_le_mul_of_nonneg_right hbndR hpred)
      have hrest := ih d hdlt
      have hrpow : 0 ≤ (r : ℝ) ^ d := pow_nonneg (le_of_lt hrpos) d
      calc scheduleWeight ρ r (logWidths.go D)
          = (sigmaSum ρ b : ℝ) / (r : ℝ) ^ d +
              scheduleWeight ρ r (logWidths.go d) := by
            rw [logWidths.go, if_neg hD, scheduleWeight, hsum']
          _ ≤ ↑(d + 1) * ↑(p - 1) / (r : ℝ) ^ d +
                ↑(p - 1) * logHalfSeries (r : ℝ) d := by
            apply add_le_add
            · exact div_le_div_of_nonneg_right hsigma' hrpow
            · exact hrest
          _ = ↑(p - 1) * logHalfSeries (r : ℝ) D := by
            rw [logHalfSeries_succ (r := r) hD hrpos]
            have hd : d = D / 2 := rfl
            rw [hd, show (↑(d + 1) : ℝ) = ↑(D / 2) + 1 from by simp [hd]]
            ring

theorem logWidths_scheduleWeight (ρ : ℕ → ℕ) (p r n : ℕ) (hr : 2 ≤ r) (hp : 0 < p)
    (hρ : ∀ k, 1 ≤ k → ρ k ≤ p - 1) :
    scheduleWeight ρ r (logWidths n) ≤ (p : ℝ) * (r : ℝ) ^ 2 / (r - 1) ^ 2 := by
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hr
  have hgo := logGoWeight ρ r p (n - 1) hr hp hρ
  rw [logWidths]
  have hp1 : (0 : ℝ) ≤ ↑(p - 1) := by exact_mod_cast (Nat.zero_le (p - 1))
  have hple : ↑(p - 1) ≤ (p : ℝ) := by
    cases p with
    | zero => cases hp
    | succ p => simp
  calc scheduleWeight ρ r (logWidths.go (n - 1))
      ≤ ↑(p - 1) * logHalfSeries (r : ℝ) (n - 1) := hgo
    _ ≤ ↑(p - 1) * ((r : ℝ) ^ 2 / (r - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (logHalfSeries_le (r : ℝ) hr1 (n - 1)) hp1
    _ = ↑(p - 1) * (r : ℝ) ^ 2 / (r - 1) ^ 2 := by ring
    _ ≤ (p : ℝ) * (r : ℝ) ^ 2 / (r - 1) ^ 2 := by gcongr

theorem logPre_real_bound (ρ : ℕ → ℕ) (p r n c : ℕ) (hr : 2 ≤ r) (hp : 0 < p) (hn : 1 ≤ n)
    (hρ : ∀ k, 1 ≤ k → ρ k ≤ p - 1) :
    (logFold ρ r (logWidths n) c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ (n - 1) +
      ((r : ℝ) - 1) * ((p : ℝ) * (r : ℝ) ^ 2 / (r - 1) ^ 2) := by
  have hρ' : ∀ k, 0 ≤ (ρ k : ℝ) := fun k => by exact_mod_cast (Nat.zero_le (ρ k))
  have hsum := logWidths_sum n
  calc (logFold ρ r (logWidths n) c : ℝ)
      ≤ (c : ℝ) / (r : ℝ) ^ (logWidths n).sum +
          ((r : ℝ) - 1) * scheduleWeight ρ r (logWidths n) :=
        logFold_real_bound ρ r c (logWidths n) hr hρ'
    _ = (c : ℝ) / (r : ℝ) ^ (n - 1) +
          ((r : ℝ) - 1) * scheduleWeight ρ r (logWidths n) := by rw [hsum]
    _ ≤ (c : ℝ) / (r : ℝ) ^ (n - 1) +
          ((r : ℝ) - 1) * ((p : ℝ) * (r : ℝ) ^ 2 / (r - 1) ^ 2) := by
      have hb := logWidths_scheduleWeight ρ p r n hr hp hρ
      have hrnon : 0 ≤ (r : ℝ) - 1 := by
        have := show (2 : ℝ) ≤ (r : ℝ) from by exact_mod_cast hr
        linarith
      linarith [mul_le_mul_of_nonneg_left hb hrnon]

/-- Real overflow bound after the parallel pre-round. -/
theorem parallelPre_real_bound (ρ : ℕ → ℕ) (r n c : ℕ) (hn : 1 ≤ n) (hr : 2 ≤ r)
    (hρ : ∀ k, 0 ≤ (ρ k : ℝ)) :
    (parallelPre ρ r n c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ (n - 1) +
      ((r : ℝ) - 1) * (sigmaSum ρ (n - 1) : ℝ) := by
  simpa [parallelPre] using passWidth_real_bound ρ r (n - 1) c hr hρ

/-- Concrete parallel EMR overflow bound (Corollary 6.5: `T_par = (r−1)/r·Σ_{n−1}`). -/
theorem emrParallel_overflow (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (hr : 1 < r) (hn : 1 ≤ n)
    (hρ : ∀ k, 0 ≤ (ρ k : ℝ)) :
    (emrParallel μ ρ p r n c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n +
      ((r - 1 : ℕ) : ℝ) / (r : ℝ) * (sigmaSum ρ (n - 1) : ℝ) + (p : ℝ) := by
  have hr0 : 0 < r := by omega
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hr2 : 2 ≤ r := by omega
  have hpre := parallelPre_real_bound ρ r n c hn hr2 hρ
  rw [show emrParallel μ ρ p r n c = montStep μ p r (parallelPre ρ r n c) from rfl]
  have hcast_r : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    exact_mod_cast Nat.cast_sub (Nat.succ_le_iff.mp (Nat.le_of_lt hr))
  have h := overflow_parallel (r : ℝ) (c : ℝ) (p : ℝ) (sigmaSum ρ (n - 1) : ℝ)
    (parallelPre ρ r n c : ℝ) hr1 n hn
    (montStep μ p r (parallelPre ρ r n c) : ℝ)
    (montStep_real_bound μ p r (parallelPre ρ r n c) hr0)
    (by simpa [hcast_r] using hpre)
  simpa [hcast_r] using h

/-- Concrete log EMR overflow bound (Corollary 6.6: `T_log = (r/(r−1))p`). -/
theorem emrLog_overflow (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (hr : 1 < r) (hn : 1 ≤ n)
    (hr2 : 2 ≤ r) (hp : 0 < p) (hρ : ∀ k, 1 ≤ k → ρ k ≤ p - 1) :
    (emrLog μ ρ p r n c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n +
      (r : ℝ) / (r - 1) * (p : ℝ) + (p : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hr)
  have hweighted := logPre_real_bound ρ p r n c hr2 hp hn hρ
  rw [show emrLog μ ρ p r n c = montStep μ p r (logFold ρ r (logWidths n) c) from rfl]
  refine overflow_log (r : ℝ) (c : ℝ) (p : ℝ) (p * r ^ 2 / (r - 1) ^ 2)
    (by exact_mod_cast hr) n hn
    (logFold ρ r (logWidths n) c : ℝ) (montStep μ p r (logFold ρ r (logWidths n) c) : ℝ)
    (montStep_real_bound μ p r (logFold ρ r (logWidths n) c) (by omega)) hweighted le_rfl

/-! ## Corollaries 6.4–6.6 — subtraction counts on `ℕ` -/

/-- Corollary 6.4: iterative EMR output is below `3p`, so at most two subtractions. -/
theorem iterative_delta_le_two (μ ρ₁ p r n c : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hp : 0 < p)
    (hc : c < p * r ^ n) (hρ : ρ₁ < p) :
    emr μ ρ₁ p r n c < 3 * p := by
  have hr1 : 1 < r := lt_of_lt_of_le one_lt_two hr
  have ho := emr_overflow μ ρ₁ p r n c hr1 hn
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr1)
  have hc' : (c : ℝ) / (r : ℝ) ^ n < (p : ℝ) := by
    rw [div_lt_iff₀ (pow_pos hr0 n)]
    exact_mod_cast hc
  have hρ' : (ρ₁ : ℝ) < (p : ℝ) := by exact_mod_cast hρ
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h3 : (emr μ ρ₁ p r n c : ℝ) < 3 * (p : ℝ) := by nlinarith [ho, hc', hρ', hp']
  exact_mod_cast h3

theorem iterative_delta_le_two_div (μ ρ₁ p r n c : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hp : 0 < p)
    (hc : c < p * r ^ n) (hρ : ρ₁ < p) :
    emr μ ρ₁ p r n c / p ≤ 2 :=
  normalization_count hp (iterative_delta_le_two μ ρ₁ p r n c hr hn hp hc hρ)

/-- Corollary 6.4: `δ ≤ 1` when `T_iter := ρ₁(1−r^{−(n−1)})` satisfies `T_iter < p − c/R`. -/
theorem iterative_delta_le_one (μ ρ₁ p r n c : ℕ) (hr : 2 ≤ r) (hn : 1 ≤ n) (hp : 0 < p)
    (hT : (ρ₁ : ℝ) * (1 - (r : ℝ) ^ (-((n : ℝ) - 1)))
      < (p : ℝ) - (c : ℝ) / (r : ℝ) ^ n) :
    emr μ ρ₁ p r n c / p ≤ 1 := by
  have hr1 : 1 < r := lt_of_lt_of_le one_lt_two hr
  have ho := emr_overflow_tight μ ρ₁ p r n c hr1 hn
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h2 : (emr μ ρ₁ p r n c : ℝ) < 2 * (p : ℝ) := by nlinarith [ho, hT, hp']
  exact normalization_count hp (by exact_mod_cast h2)

/-- Corollary 6.4 with the paper's tighter overflow bound (ℝ). -/
theorem emr_overflow_tight_bound (μ ρ₁ p r n c : ℕ) (hr : 1 < r) (hn : 1 ≤ n) :
    (emr μ ρ₁ p r n c : ℝ) ≤
      (c : ℝ) / (r : ℝ) ^ n + (ρ₁ : ℝ) * (1 - (r : ℝ) ^ (-((n : ℝ) - 1))) + (p : ℝ) :=
  emr_overflow_tight μ ρ₁ p r n c hr hn

/-- Corollary 6.5: parallel EMR needs at most `n` conditional subtractions. -/

theorem parallel_delta_le_one {S c p r n σ : ℕ} (hr : 2 ≤ r) (hp : 0 < p) (_hn : 1 ≤ n)
    (hT : ((r - 1 : ℕ) : ℝ) / (r : ℝ) * (σ : ℝ) < (p : ℝ) - (c : ℝ) / (r : ℝ) ^ n)
    (hS : (S : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n + (r - 1 : ℝ) / r * σ + (p : ℝ)) :
    S / p ≤ 1 := by
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hcast_r : ((r - 1 : ℕ) : ℝ) / (r : ℝ) = (r - 1 : ℝ) / r := by
    have hrpos : 0 < r := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr)
    rw [show ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 from Nat.cast_pred hrpos]
  have hS' : (S : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n + ((r - 1 : ℕ) : ℝ) / (r : ℝ) * (σ : ℝ) + (p : ℝ) := by
    simpa [hcast_r] using hS
  have h2 : (S : ℝ) < 2 * (p : ℝ) := by nlinarith [hS', hT, hp']
  exact normalization_count hp (by exact_mod_cast h2)

theorem parallel_delta_le_n {S c p r n σ : ℕ} (hr : 2 ≤ r) (hp : 0 < p) (hn : 1 ≤ n)
    (hc : c < p * r ^ n) (hσ : σ ≤ (n - 1) * (p - 1))
    (hS : (S : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n + (r - 1 : ℝ) / r * σ + (p : ℝ)) :
    S / p ≤ n := by
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le one_lt_two hr)
  have hr0nat : 0 < r := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr)
  have hc' : (c : ℝ) / (r : ℝ) ^ n < (p : ℝ) := by
    rw [div_lt_iff₀ (pow_pos (by exact_mod_cast hr0nat) n)]
    exact_mod_cast hc
  have hlt : S < (n + 1) * p := by
    by_cases hn1 : n = 1
    · subst hn1
      simp only [pow_one, Nat.sub_self] at hc' hS hσ ⊢
      have hσ0 : σ = 0 := Nat.le_zero.mp (by simpa using hσ)
      have hσ0R : (σ : ℝ) = 0 := by exact_mod_cast hσ0
      rw [hσ0R] at hS
      have hltR : (S : ℝ) < 2 * (p : ℝ) := by nlinarith [hS, hc']
      exact_mod_cast hltR
    · have hn1pos : 0 < n - 1 := by omega
      have hcast_r : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        exact_mod_cast Nat.cast_sub (Nat.succ_le_iff.mp (Nat.le_of_lt (Nat.lt_of_lt_of_le one_lt_two hr)))
      have hS' : (S : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n + ((r - 1 : ℕ) : ℝ) / (r : ℝ) * (σ : ℝ) + (p : ℝ) := by
        simpa [hcast_r] using hS
      have hσR : (σ : ℝ) ≤ ↑((n - 1) * (p - 1)) := by exact_mod_cast hσ
      have hσprod : ((r - 1 : ℕ) : ℝ) / (r : ℝ) * (σ : ℝ)
          ≤ ((r - 1 : ℕ) : ℝ) / (r : ℝ) * ↑((n - 1) * (p - 1)) := by
        have hrnn : (0 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) / (r : ℝ) := by
          apply div_nonneg (by exact_mod_cast (Nat.zero_le (r - 1)))
            (by exact_mod_cast hr0nat.le)
        exact mul_le_mul_of_nonneg_left hσR hrnn
      have hstrict : (S : ℝ) < 2 * (p : ℝ) + ((r - 1 : ℕ) : ℝ) / (r : ℝ) * ↑((n - 1) * (p - 1)) := by
        have hmid : (c : ℝ) / (r : ℝ) ^ n + ((r - 1 : ℕ) : ℝ) / (r : ℝ) * (σ : ℝ) + (p : ℝ)
            < 2 * (p : ℝ) + ((r - 1 : ℕ) : ℝ) / (r : ℝ) * ↑((n - 1) * (p - 1)) := by
          nlinarith [hc', hσprod]
        exact lt_of_le_of_lt hS' hmid
      have hcap : 2 * (p : ℝ) + ((r - 1 : ℕ) : ℝ) / (r : ℝ) * ↑((n - 1) * (p - 1))
          < ↑(n + 1) * ↑p := by
        have hratio_lt : ((r - 1 : ℕ) : ℝ) / (r : ℝ) < 1 := by
          rw [div_lt_one (by exact_mod_cast hr0nat)]
          linarith
        have hσcapNat : (n - 1) * (p - 1) < (n - 1) * p := by
          exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt_self (by decide) hp) hn1pos
        have hσcapR : (↑((n - 1) * (p - 1)) : ℝ) < ↑((n - 1) * p) := by
          exact_mod_cast hσcapNat
        have hrpos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) / (r : ℝ) := by
          have hr1pos : 0 < r - 1 := by omega
          apply div_pos (by exact_mod_cast hr1pos)
          exact_mod_cast hr0nat
        have hn1R : (0 : ℝ) < ↑((n - 1) * p) := by exact_mod_cast (Nat.mul_pos hn1pos hp)
        have hterm : ((r - 1 : ℕ) : ℝ) / (r : ℝ) * ↑((n - 1) * (p - 1)) < ↑((n - 1) * p) := by
          have h1 : ((r - 1 : ℕ) : ℝ) / (r : ℝ) * ↑((n - 1) * (p - 1))
              < ((r - 1 : ℕ) : ℝ) / (r : ℝ) * ↑((n - 1) * p) :=
            mul_lt_mul_of_pos_left hσcapR hrpos
          have h2 : ((r - 1 : ℕ) : ℝ) / (r : ℝ) * ↑((n - 1) * p) < ↑((n - 1) * p) := by
            nlinarith [hratio_lt, hn1R]
          linarith
        have hnNat : 2 * p + (n - 1) * p = (n + 1) * p := by
          rw [← Nat.add_mul, show 2 + (n - 1) = n + 1 by omega]
        have hnR : (2 : ℝ) * ↑p + ↑((n - 1) * p) = ↑(n + 1) * ↑p := by exact_mod_cast hnNat
        linarith [hterm, hnR]
      have hltR : (S : ℝ) < ↑(n + 1) * ↑p := by linarith [hstrict, hcap]
      exact_mod_cast hltR
  exact normalization_count hp hlt

/-- Concrete parallel EMR: at most `n` conditional subtractions. -/
theorem emrParallel_delta_le_n (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (hr : 2 ≤ r) (hp : 0 < p)
    (hn : 1 ≤ n) (hc : c < p * r ^ n)
    (hρ : ∀ k, 1 ≤ k → k ≤ n - 1 → ρ k ≤ p - 1) :
    emrParallel μ ρ p r n c / p ≤ n := by
  have hr1 : 1 < r := lt_of_lt_of_le one_lt_two hr
  have hσ : sigmaSum ρ (n - 1) ≤ (n - 1) * (p - 1) := by
    by_cases hn1 : n ≤ 1
    · have : n - 1 = 0 := by omega
      simp [sigmaSum, this]
    · have hm1 : 0 < n - 1 := by omega
      exact sigmaSum_le ρ (n - 1) p hm1 hρ
  have ho := emrParallel_overflow μ ρ p r n c hr1 hn (fun k => by exact_mod_cast (Nat.zero_le (ρ k)))
  have hcast_r : ((r - 1 : ℕ) : ℝ) / (r : ℝ) = (r - 1 : ℝ) / r := by
    have hrpos : 0 < r := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr)
    rw [show ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 from Nat.cast_pred hrpos]
  have ho' : (emrParallel μ ρ p r n c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n +
      (r - 1 : ℝ) / r * (sigmaSum ρ (n - 1) : ℝ) + (p : ℝ) := by
    simpa [hcast_r] using ho
  exact parallel_delta_le_n (S := emrParallel μ ρ p r n c) (σ := sigmaSum ρ (n - 1))
    hr hp hn hc hσ ho'

/-- Corollary 6.5: `δ ≤ 1` when `T_par := (r−1)/r·Σ_{n−1}` satisfies `T_par < p − c/R`. -/
theorem emrParallel_delta_le_one (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (hr : 2 ≤ r) (hp : 0 < p)
    (hn : 1 ≤ n)
    (hT : ((r - 1 : ℕ) : ℝ) / (r : ℝ) * (sigmaSum ρ (n - 1) : ℝ)
      < (p : ℝ) - (c : ℝ) / (r : ℝ) ^ n) :
    emrParallel μ ρ p r n c / p ≤ 1 := by
  have hr1 : 1 < r := lt_of_lt_of_le one_lt_two hr
  have ho := emrParallel_overflow μ ρ p r n c hr1 hn (fun k => by exact_mod_cast (Nat.zero_le (ρ k)))
  have hcast_r : ((r - 1 : ℕ) : ℝ) / (r : ℝ) = (r - 1 : ℝ) / r := by
    have hrpos : 0 < r := Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le one_lt_two hr)
    rw [show ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 from Nat.cast_pred hrpos]
  have ho' : (emrParallel μ ρ p r n c : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n +
      (r - 1 : ℝ) / r * (sigmaSum ρ (n - 1) : ℝ) + (p : ℝ) := by
    simpa [hcast_r] using ho
  exact parallel_delta_le_one hr hp hn hT ho'

/-- Corollary 6.6 — logarithmic EMR needs at most three conditional subtractions. -/
theorem log_delta_le_one {S c p r n : ℕ} (hr : 2 ≤ r) (hp : 0 < p) (_hn : 1 ≤ n)
    (hT : (r : ℝ) / (r - 1) * (p : ℝ) < (p : ℝ) - (c : ℝ) / (r : ℝ) ^ n)
    (hS : (S : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n + (r : ℝ) / (r - 1) * (p : ℝ) + (p : ℝ)) :
    S / p ≤ 1 := by
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h2 : (S : ℝ) < 2 * (p : ℝ) := by nlinarith [hS, hT, hp']
  exact normalization_count hp (by exact_mod_cast h2)

theorem log_delta_le_three {S c p r n : ℕ} (hr : 2 ≤ r) (hp : 0 < p) (_hn : 1 ≤ n)
    (hc : c < p * r ^ n)
    (hS : (S : ℝ) ≤ (c : ℝ) / (r : ℝ) ^ n + (r : ℝ) / (r - 1) * (p : ℝ) + (p : ℝ)) :
    S / p ≤ 3 := by
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le one_lt_two hr)
  have hr0 : (0 : ℝ) < (r : ℝ) := by linarith
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hc' : (c : ℝ) / (r : ℝ) ^ n < (p : ℝ) := by
    rw [div_lt_iff₀ (pow_pos hr0 n)]
    exact_mod_cast hc
  have hratio : (r : ℝ) / (r - 1) ≤ 2 := by
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < r - 1)]
    nlinarith
  have hbound : (S : ℝ) < 4 * (p : ℝ) := by nlinarith [hS, hc', hratio, hp']
  have hS' : S < 4 * p := by exact_mod_cast hbound
  exact normalization_count hp hS'

/-- Concrete log EMR: at most three conditional subtractions. -/
theorem emrLog_delta_le_three (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (hr : 2 ≤ r) (hp : 0 < p)
    (hn : 1 ≤ n) (hc : c < p * r ^ n) (hρ : ∀ k, 1 ≤ k → ρ k ≤ p - 1) :
    emrLog μ ρ p r n c / p ≤ 3 :=
  log_delta_le_three hr hp hn hc
    (emrLog_overflow μ ρ p r n c (lt_of_lt_of_le one_lt_two hr) hn hr hp hρ)

/-- Corollary 6.6: `δ ≤ 1` when `T_log := (r/(r−1))p` satisfies `T_log < p − c/R`. -/
theorem emrLog_delta_le_one (μ : ℕ) (ρ : ℕ → ℕ) (p r n c : ℕ) (hr : 2 ≤ r) (hp : 0 < p)
    (hn : 1 ≤ n) (hρ : ∀ k, 1 ≤ k → ρ k ≤ p - 1)
    (hT : (r : ℝ) / (r - 1) * (p : ℝ) < (p : ℝ) - (c : ℝ) / (r : ℝ) ^ n) :
    emrLog μ ρ p r n c / p ≤ 1 :=
  log_delta_le_one hr hp hn hT
    (emrLog_overflow μ ρ p r n c (lt_of_lt_of_le one_lt_two hr) hn hr hp hρ)

/-- Theorem 4.3 packaged with executable correctness: `n²+1` multiplications and
  `r^n · emr ≡ c (mod p)`. -/
theorem n2p1 (μ ρ₁ p r n c : ℕ) (hn : 1 ≤ n)
    (hρ : (r : ZMod p) * (ρ₁ : ZMod p) = 1) (hμ : (p : ZMod r) * (μ : ZMod r) = -1) :
    (n - 1) * n + (n + 1) = n ^ 2 + 1 ∧
    (r : ZMod p) ^ n * (emr μ ρ₁ p r n c : ZMod p) = (c : ZMod p) :=
  ⟨count n hn, emr_correct μ ρ₁ r n c hn hρ hμ⟩

end EMR
