import Mathlib

/-!
# The binary entropy correction of AH-6: average identity and cubic Hermite minorant

Source: `ResearchNotes/QI/seven_qubit_entanglement/joint_entropy_analytic_proof.tex`,
`sec:seven-joint-analytic-proof`, equation `eq:seven-joint-binary-minorant`.

* `avg_identity`: `(f(λ)+f(μ))/2 = f(M) - M Φ(s)` with `f = negMulLog`, `M = (λ+μ)/2`, `s = (λ-μ)/(λ+μ)` and
  `Φ(s) = [(1+s) ln(1+s) + (1-s) ln(1-s)]/2` (`phiB`; the paper's `Φ(z)` with `z = s²`).
* `phiB_hasSum`: `Φ = ∑ₙ z^{n+1}/(2(n+1)(2n+1))`, `z = s²`, for `|s| < 1`.
* `phiB_minorant`: `Φ ≥ z/2 + η₂ z² + η₃ z³` for `|s| < 1` (the paper states it on `[0,1]`; the endpoint `z = 1` is
  not needed, since the majorant is then extended by continuity).  The proof is the tangent line inequality for the
  power series termwise at `z₀ = 1/9` (the paper's argument: `Φ⁗ > 0` and the Hermite error), with the two
  series values `Φ(1/3) = (5/3) ln 2 - ln 3` and `Φ'(1/9) = (3/4) ln 2`.
-/

namespace FormalResearch.FourQubitEntropy.AH6

open Real

/-- `Φ(s) = ((1+s) ln(1+s) + (1-s) ln(1-s))/2`. -/
noncomputable def phiB (s : ℝ) : ℝ := ((1 + s) * Real.log (1 + s) + (1 - s) * Real.log (1 - s)) / 2

/-- The Hermite coefficients `η₂, η₃`. -/
noncomputable def eta2R : ℝ := 1593 / 4 * Real.log 2 - 243 * Real.log 3 - 9
noncomputable def eta3R : ℝ := 81 / 2 - 9477 / 4 * Real.log 2 + 1458 * Real.log 3

/-- The coefficients `1/(2(n+1)(2n+1))` of the series of `Φ`. -/
noncomputable def cc (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1))

theorem avg_identity {l m : ℝ} (hl : 0 < l) (hm : 0 < m) :
    (Real.negMulLog l + Real.negMulLog m) / 2 =
      Real.negMulLog ((l + m) / 2) - (l + m) / 2 * phiB ((l - m) / (l + m)) := by
  have hlm : 0 < l + m := by linarith
  have h1 : 1 + (l - m) / (l + m) = l / ((l + m) / 2) := by field_simp; ring
  have h2 : 1 - (l - m) / (l + m) = m / ((l + m) / 2) := by field_simp; ring
  have hM : 0 < (l + m) / 2 := by positivity
  unfold phiB Real.negMulLog
  rw [h1, h2, Real.log_div hl.ne' hM.ne', Real.log_div hm.ne' hM.ne']
  field_simp
  ring

theorem phiB_hasSum {s : ℝ} (hs : |s| < 1) :
    HasSum (fun n : ℕ => cc n * (s ^ 2) ^ (n + 1)) (phiB s) := by
  have hz : |s ^ 2| < 1 := by
    rw [abs_pow]; nlinarith [abs_nonneg s]
  have h1 := Real.hasSum_pow_div_log_of_abs_lt_one hz
  have h2 := (Real.hasSum_log_sub_log_of_abs_lt_one hs).mul_left s
  have h3 := (h2.sub h1).mul_left (1 / 2)
  convert h3 using 1
  · funext n
    unfold cc
    have e : s * s ^ (2 * n + 1) = (s ^ 2) ^ (n + 1) := by ring
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    field_simp
    rw [← e]
    ring
  · have h1s : 0 < 1 + s := by have := abs_lt.mp hs; linarith
    have h2s : 0 < 1 - s := by have := abs_lt.mp hs; linarith
    have e : Real.log (1 - s ^ 2) = Real.log (1 + s) + Real.log (1 - s) := by
      rw [← Real.log_mul h1s.ne' h2s.ne']; congr 1; ring
    unfold phiB
    rw [e]
    ring

theorem phiB_third : phiB (1 / 3) = 5 / 3 * Real.log 2 - Real.log 3 := by
  unfold phiB
  have e1 : Real.log (1 + 1 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [show (1 + 1 / 3 : ℝ) = 2 ^ 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; norm_num
  have e2 : Real.log (1 - 1 / 3 : ℝ) = Real.log 2 - Real.log 3 := by
    rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [e1, e2]; ring

/-- Termwise tangent inequality `z^k ≥ z₀^k + k z₀^{k-1} (z - z₀)` for `k = m + 2`. -/
theorem tangent_pow {z z0 : ℝ} (hz : 0 ≤ z) (hz0 : 0 < z0) (m : ℕ) :
    z0 ^ (m + 2) + ((m : ℝ) + 2) * z0 ^ (m + 1) * (z - z0) ≤ z ^ (m + 2) := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ z / z0 - 1 by
    have : 0 ≤ z / z0 := by positivity
    linarith) (m + 2)
  have e : (1 + (z / z0 - 1)) = z / z0 := by ring
  rw [e, div_pow, le_div_iff₀ (pow_pos hz0 _)] at h
  have e2 : z0 ^ (m + 2) + ((m : ℝ) + 2) * z0 ^ (m + 1) * (z - z0) =
      (1 + ((m + 2 : ℕ) : ℝ) * (z / z0 - 1)) * z0 ^ (m + 2) := by
    push_cast
    field_simp
    ring
  rw [e2]; exact h


theorem phiB_deriv_series :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * cc n * (1 / 9 : ℝ) ^ n) (3 / 4 * Real.log 2) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one (x := 1 / 3) (by norm_num [abs_of_pos])).mul_left (3 / 4)
  convert h using 1
  · funext n
    unfold cc
    have e : ((1 : ℝ) / 3) ^ (2 * n + 1) = (1 / 3) * (1 / 9 : ℝ) ^ n := by
      rw [pow_succ, pow_mul]; norm_num; ring
    rw [e]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    field_simp
    ring
  · have e1 : Real.log (1 + 1 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
      rw [show (1 + 1 / 3 : ℝ) = 2 ^ 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
        Real.log_pow]; norm_num
    have e2 : Real.log (1 - 1 / 3 : ℝ) = Real.log 2 - Real.log 3 := by
      rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    rw [e1, e2]; ring

theorem cc_pos (n : ℕ) : 0 < cc n := by unfold cc; positivity

/-- **Cubic Hermite minorant of the binary entropy correction** (`eq:seven-joint-binary-minorant`). -/
theorem phiB_minorant {s : ℝ} (hs : |s| < 1) :
    s ^ 2 / 2 + eta2R * (s ^ 2) ^ 2 + eta3R * (s ^ 2) ^ 3 ≤ phiB s := by
  set z : ℝ := s ^ 2 with hzdef
  have hz0 : 0 ≤ z := sq_nonneg s
  have hS := phiB_hasSum hs
  have hS0 := phiB_hasSum (s := 1 / 3) (by norm_num [abs_of_pos])
  have e9 : ((1 : ℝ) / 3) ^ 2 = 1 / 9 := by norm_num
  rw [e9] at hS0
  rw [← hzdef] at hS
  have T := (hasSum_nat_add_iff' 3).mpr hS
  have T0 := (hasSum_nat_add_iff' 3).mpr hS0
  have D0 := (hasSum_nat_add_iff' 3).mpr phiB_deriv_series
  have hR := (((T0.mul_left (1 - 2 * (z - 1 / 9) / (1 / 9))).add
    (D0.mul_left (z - 1 / 9))).mul_left (z ^ 2 / (1 / 9) ^ 2))
  have hle := hasSum_le (fun m => ?_) hR T
  · -- the final identity
    rw [phiB_third] at hle
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cc] at hle
    unfold eta2R eta3R
    norm_num at hle ⊢
    nlinarith [hle]
  · -- termwise tangent inequality
    have hc := cc_pos (m + 3)
    have hpow := tangent_pow hz0 (show (0 : ℝ) < 1 / 9 by norm_num) m
    show z ^ 2 / (1 / 9) ^ 2 *
        ((1 - 2 * (z - 1 / 9) / (1 / 9)) * (cc (m + 3) * (1 / 9 : ℝ) ^ (m + 3 + 1)) +
          (z - 1 / 9) * ((((m + 3 : ℕ) : ℝ) + 1) * cc (m + 3) * (1 / 9 : ℝ) ^ (m + 3))) ≤
        cc (m + 3) * z ^ (m + 3 + 1)
    have key : z ^ 2 / (1 / 9) ^ 2 *
        ((1 - 2 * (z - 1 / 9) / (1 / 9)) * (cc (m + 3) * (1 / 9 : ℝ) ^ (m + 3 + 1)) +
          (z - 1 / 9) * ((((m + 3 : ℕ) : ℝ) + 1) * cc (m + 3) * (1 / 9 : ℝ) ^ (m + 3))) =
        cc (m + 3) * z ^ 2 * ((1 / 9 : ℝ) ^ (m + 2) + ((m : ℝ) + 2) * (1 / 9 : ℝ) ^ (m + 1) * (z - 1 / 9)) := by
      push_cast
      field_simp
      ring
    rw [key]
    calc cc (m + 3) * z ^ 2 * ((1 / 9 : ℝ) ^ (m + 2) + ((m : ℝ) + 2) * (1 / 9 : ℝ) ^ (m + 1) * (z - 1 / 9))
        ≤ cc (m + 3) * z ^ 2 * z ^ (m + 2) := by gcongr
      _ = cc (m + 3) * z ^ (m + 3 + 1) := by ring

end FormalResearch.FourQubitEntropy.AH6
