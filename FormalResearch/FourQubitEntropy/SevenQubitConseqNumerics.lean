import FormalResearch.FourQubitEntropy.SevenQubitConseqConvex

/-!
# Rigorous rational enclosure of `g₈` at the two ceiling points

`g₈(455/1572) + g₈(641/3144) < (35 · 2.97354 - 99) ln 2`  (`CE-1` of `seven_qubit_entropy_global_upper.tex`,
in nats).  No floating point: `g₈(p) = Gsp(t(p)) ≤ Gsp(t_lo)` for a rational `t_lo ≤ t(p)`
(`Gsp` is antitone on `[1/8,1]`), and `Gsp(t_lo)` is bounded by the rational function
`Gub t = ln2 (4 - 3t) - t Lb(2t) - (1-t) Lb(2(1-t)) - (1-t) Lb(8/7)` where `Lb x ≤ ln x` is the
two/three-term `arctanh` series bound (`Real.sum_range_le_log_div`, `Real.log_div_le_sum_range_add`).
-/

open Real

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

theorem Gsp_antitoneOn : AntitoneOn Gsp (Set.Icc (1 / 8) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · unfold Gsp
    have := Real.continuous_negMulLog
    exact (by fun_prop : Continuous fun a : ℝ => negMulLog a + 7 * negMulLog ((1 - a) / 7)).continuousOn
  · intro a ha
    rw [interior_Icc] at ha
    exact (hasDerivAt_Gsp (by linarith [ha.1]) ha.2).differentiableAt.differentiableWithinAt
  · intro a ha
    rw [interior_Icc] at ha
    rw [(hasDerivAt_Gsp (by linarith [ha.1]) ha.2).deriv]
    have h1 : 0 < (1 - a) / 7 := by linarith [ha.2]
    have : log ((1 - a) / 7) ≤ log a :=
      Real.log_le_log h1 (by linarith [ha.1])
    linarith

/-- Lower bound for `log x` by the `arctanh` series. -/
noncomputable def Lb (x : ℝ) : ℝ :=
  if 1 ≤ x then 2 * (((x - 1) / (x + 1)) + ((x - 1) / (x + 1)) ^ 3 / 3)
  else -2 * (((1 - x) / (1 + x)) + ((1 - x) / (1 + x)) ^ 3 / 3 +
    ((1 - x) / (1 + x)) ^ 5 / (1 - ((1 - x) / (1 + x)) ^ 2))

theorem Lb_le_log {x : ℝ} (hx : 0 < x) : Lb x ≤ log x := by
  unfold Lb
  split_ifs with h
  · set y := (x - 1) / (x + 1) with hy
    have hy0 : 0 ≤ y := div_nonneg (by linarith) (by linarith)
    have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
    have := Real.sum_range_le_log_div hy0 hy1 2
    have hr : (1 + y) / (1 - y) = x := by
      rw [hy]; field_simp; ring
    rw [hr] at this
    simp [Finset.sum_range_succ] at this
    linarith
  · rw [not_le] at h
    set y := (1 - x) / (1 + x) with hy
    have hy0 : 0 ≤ y := div_nonneg (by linarith) (by linarith)
    have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
    have := Real.log_div_le_sum_range_add hy0 hy1 2
    have hr : (1 + y) / (1 - y) = x⁻¹ := by
      have e1 : 1 + y = 2 / (1 + x) := by rw [hy]; field_simp; ring
      have e2 : 1 - y = 2 * x / (1 + x) := by rw [hy]; field_simp; ring
      rw [e1, e2]
      field_simp
    rw [hr, Real.log_inv] at this
    simp [Finset.sum_range_succ] at this
    linarith

/-- The closed form of the spike entropy in terms of `ln 2`, `ln 2t`, `ln 2(1-t)`, `ln (8/7)`. -/
theorem Gsp_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Gsp t = log 2 * (4 - 3 * t) - t * log (2 * t) - (1 - t) * log (2 * (1 - t)) -
      (1 - t) * log (8 / 7) := by
  have h2 : 0 < 1 - t := by linarith
  have e1 : log (2 * t) = log 2 + log t := Real.log_mul (by norm_num) h0.ne'
  have e2 : log (2 * (1 - t)) = log 2 + log (1 - t) := Real.log_mul (by norm_num) h2.ne'
  have e3 : log (8 / 7) = 3 * log 2 - log 7 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    have : log 8 = 3 * log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [this]
  have e4 : log ((1 - t) / 7) = log (1 - t) - log 7 := Real.log_div h2.ne' (by norm_num)
  unfold Gsp
  simp only [negMulLog]
  rw [e4, e1, e2, e3]
  ring

noncomputable def Gub (t : ℝ) : ℝ :=
  log 2 * (4 - 3 * t) - t * Lb (2 * t) - (1 - t) * Lb (2 * (1 - t)) - (1 - t) * Lb (8 / 7)

theorem Gsp_le_Gub {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : Gsp t ≤ Gub t := by
  rw [Gsp_eq h0 h1]
  unfold Gub
  have a1 := Lb_le_log (x := 2 * t) (by linarith)
  have a2 := Lb_le_log (x := 2 * (1 - t)) (by linarith)
  have a3 := Lb_le_log (x := 8 / 7) (by norm_num)
  have h2 : 0 < 1 - t := by linarith
  nlinarith [mul_le_mul_of_nonneg_left a1 h0.le, mul_le_mul_of_nonneg_left a2 h2.le,
    mul_le_mul_of_nonneg_left a3 h2.le]

/-- `g₈(p) ≤ Gsp(t_lo)` for rational `t_lo ≤ t(p)`. -/
theorem g8_le_Gsp {p tl : ℝ} (hp : 1 / 8 ≤ p) (hp1 : p ≤ 1) (htl : 1 / 8 ≤ tl)
    (hsq : (8 * tl - 1) ^ 2 ≤ 7 * (8 * p - 1)) : g8 p ≤ Gsp tl := by
  unfold g8 tOf
  have hs : 8 * tl - 1 ≤ Real.sqrt (7 * (8 * p - 1)) :=
    Real.le_sqrt_of_sq_le hsq
  have hs7 : Real.sqrt (7 * (8 * p - 1)) ≤ 7 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  apply Gsp_antitoneOn ⟨htl, by linarith [hs, hs7, show tl ≤ 1 from by nlinarith [hs7]]⟩
    ⟨by have := Real.sqrt_nonneg (7 * (8 * p - 1)); linarith, by linarith⟩
  linarith

theorem g8_sum_lt :
    g8 (455 / 1572) + g8 (641 / 3144) < (35 * (297354 / 100000) - 99) * log 2 := by
  have h1 : g8 (455 / 1572) ≤ Gsp (504321 / 1000000) :=
    g8_le_Gsp (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 : g8 (641 / 3144) ≤ Gsp (387717 / 1000000) :=
    g8_le_Gsp (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have u1 := Gsp_le_Gub (t := 504321 / 1000000) (by norm_num) (by norm_num)
  have u2 := Gsp_le_Gub (t := 387717 / 1000000) (by norm_num) (by norm_num)
  have l2 := Real.log_two_lt_d9
  have l2' := Real.log_two_gt_d9
  unfold Gub at u1 u2
  norm_num [Lb] at u1 u2
  linarith

end FormalResearch.FourQubitEntropy.SevenQubitConseq
