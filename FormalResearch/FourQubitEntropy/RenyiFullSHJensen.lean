import FormalResearch.FourQubitEntropy.RenyiFullBQBinary
import FormalResearch.FourQubitEntropy.RenyiFullSliverEnt

/-!
# Small-head dual: the head/tail Jensen estimate

Paper E, `lem:fqe-small-head-dual` (`renyi_small_head_dual.tex`), first display.  For the chart
`λ = ((1-u+δ)/2, (1-u-δ)/2, u/2, u/2)` (a head pair of total weight `1-u`, a uniform tail pair of weight `u`),
Jensen's inequality for the logarithm gives
`H_q(λ) ≤ 1 + h(u) - (1-w) D_q(z)`, `w = u^q/((1-u)^q+u^q)`, `z = δ²/(1-u)²`.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

theorem qBQ_eq_qS : qBQ = qS := rfl

theorem shSpec_sum {u δ : ℝ} (hu1 : u < 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 - u) (hu0 : 0 ≤ u) :
    ∑ i, (![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] : Fin 4 → ℝ) i ^ qS =
      2 * ((1 - u) ^ qS * (((1 + δ / (1 - u)) ^ qS + (1 - δ / (1 - u)) ^ qS) / 2) + u ^ qS) /
        (2 : ℝ) ^ qS := by
  have h1u : 0 < 1 - u := by linarith
  have e1 : (1 - u + δ) / 2 = (1 - u) * (1 + δ / (1 - u)) / 2 := by field_simp
  have e2 : (1 - u - δ) / 2 = (1 - u) * (1 - δ / (1 - u)) / 2 := by field_simp
  have hs0 : 0 ≤ δ / (1 - u) := div_nonneg hδ0 h1u.le
  have hs1 : δ / (1 - u) ≤ 1 := (div_le_one h1u).2 hδ1
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [e1, e2, Real.div_rpow (by positivity) (by norm_num), Real.div_rpow (by nlinarith) (by norm_num),
    Real.div_rpow hu0 (by norm_num), Real.mul_rpow h1u.le (by linarith),
    Real.mul_rpow h1u.le (by linarith)]
  ring

theorem bqD_mul_eq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    bqD qBQ (s ^ 2) * ((qS - 1) * Real.log 2) =
      Real.log (((1 + s) ^ qS + (1 - s) ^ qS) / 2) := by
  have hc : (qS - 1) * Real.log 2 ≠ 0 := by
    have := qS_gt_one
    have := log_two_pos'
    positivity
  have hE : 0 < (1 + s) ^ qS + (1 - s) ^ qS := by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 1 + s by linarith) qS
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 1 - s by linarith) qS
    linarith
  unfold bqD bqf bqFs
  rw [Real.sqrt_sq hs0, Real.log_div hE.ne' (by norm_num)]
  rw [qBQ_eq_qS]
  have hq1 : qS - 1 ≠ 0 := by have := qS_gt_one; intro h; linarith
  field_simp

theorem binH_mul_eq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    binH qBQ u * ((qS - 1) * Real.log 2) = -Real.log ((1 - u) ^ qS + u ^ qS) := by
  have hq := qS_gt_one
  have hL := log_two_pos'
  unfold binH Real.logb
  rw [qBQ_eq_qS]
  have h1 : (1 - qS) ≠ 0 := by linarith
  have e : u ^ qS + (1 - u) ^ qS = (1 - u) ^ qS + u ^ qS := by ring
  rw [e]
  field_simp
  ring

/-- **Head/tail Jensen estimate.** -/
theorem sh_jensen {u δ : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 - u) :
    renyiSpec qS ![(1 - u + δ) / 2, (1 - u - δ) / 2, u / 2, u / 2] ≤
      1 + binH qBQ u -
        (1 - u) ^ qS / ((1 - u) ^ qS + u ^ qS) * bqD qBQ ((δ / (1 - u)) ^ 2) := by
  have hq := qS_gt_one
  have h1u : 0 < 1 - u := by linarith
  have hs0 : 0 ≤ δ / (1 - u) := div_nonneg hδ0 h1u.le
  have hs1 : δ / (1 - u) < 1 := (div_lt_one h1u).2 hδ1
  set s := δ / (1 - u) with hs
  set T := (1 - u) ^ qS with hT
  have hT0 : 0 < T := Real.rpow_pos_of_pos h1u _
  have hU0 : 0 < u ^ qS := Real.rpow_pos_of_pos hu0 _
  set S := T + u ^ qS with hS
  have hS0 : 0 < S := by linarith
  have hE : 0 < (1 + s) ^ qS + (1 - s) ^ qS := by
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 1 + s by linarith) qS
    have := Real.rpow_pos_of_pos (show (0 : ℝ) < 1 - s by linarith) qS
    linarith
  set m := ((1 + s) ^ qS + (1 - s) ^ qS) / 2 with hm
  have hm0 : 0 < m := by positivity
  set ω := T / S with hω
  have hω0 : 0 ≤ ω := by positivity
  have hω1 : 0 ≤ 1 - ω := by
    rw [hω, sub_nonneg, div_le_one hS0]; linarith
  have hN : 0 < T * m + u ^ qS := by positivity
  have hsum := shSpec_sum hu1 hδ0 hδ1.le hu0.le
  have hR : -Real.log (T * m + u ^ qS) ≤ (qS - 1) * Real.log 2 *
      (binH qBQ u - ω * bqD qBQ (s ^ 2)) := by
    have hb := binH_mul_eq hu0 hu1
    have hd := bqD_mul_eq hs0 hs1
    have hAM : m ^ ω * (1 : ℝ) ^ (1 - ω) ≤ ω * m + (1 - ω) * 1 :=
      Real.geom_mean_le_arith_mean2_weighted hω0 hω1 hm0.le zero_le_one (by ring)
    rw [Real.one_rpow, mul_one, mul_one] at hAM
    have hlogm : ω * Real.log m ≤ Real.log (ω * m + (1 - ω)) := by
      rw [← Real.log_rpow hm0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hm0 _) hAM
    have hNe : T * m + u ^ qS = S * (ω * m + (1 - ω)) := by
      rw [hω]; field_simp; rw [hS]; ring
    have hpos : 0 < ω * m + (1 - ω) := by nlinarith [mul_nonneg hω0 hm0.le]
    rw [hNe, Real.log_mul hS0.ne' hpos.ne']
    have : (qS - 1) * Real.log 2 * (binH qBQ u - ω * bqD qBQ (s ^ 2)) =
        -Real.log S - ω * Real.log m := by
      have := hb; have := hd
      nlinarith [hb, hd]
    rw [this]
    linarith
  have := renyiSpec_of_sum hN (by rw [hsum]) hR
  linarith [this]

end FormalResearch.FourQubitEntropy.RenyiFull
