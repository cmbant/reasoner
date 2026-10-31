import FormalResearch.FourQubitEntropy.RenyiRankTwoSharp
import FormalResearch.FourQubitEntropy.RenyiTwoUp

/-!
# The HS–cluster crossing of the mean Rényi entropies

* the mean Rényi entropy of the cluster state is `5/3` for every `q > 0`;
* the mean Rényi entropy `h_q = log₂(2^{-q} + 3·6^{-q})/(1-q)` of `M₄` (the "HS" value) is
  strictly decreasing in `q > 1`;
* there is a unique `q_* ∈ (3/2, 8/5)` with `h_{q_*} = 5/3`, `M₄` is above the cluster state for
  `1 < q < q_*` and below it for `q > q_*`.

Paper: `prop:fqe-renyi-crossing` (renyi_above_one.tex). The paper's finer enclosure
`1587/1000 < q_* < 1589/1000` (RA-4) is also proved here, by exact rational enclosures of the rational
powers (`crossing_fine`); the paper's analytic arguments (strict decrease, crossing in
`(3/2, 8/5)`) are reproduced without numerical brackets other than these exact rational ones.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- `h_q = log₂ m_q/(1-q)`, `m_q = 2^{-q} + 3·6^{-q}`: the mean Rényi value of the HS spectrum. -/
noncomputable def hsRenyi (q : ℝ) : ℝ :=
  Real.logb 2 ((2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q)) / (1 - q)

/-! ### Elementary rational enclosures of rational powers -/

theorem rpow_div_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (k n : ℕ) (hn : n ≠ 0)
    (h : a ^ k ≤ c ^ n) : a ^ ((k : ℝ) / n) ≤ c := by
  have h1 : (a ^ ((k : ℝ) / n)) ^ n = a ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha, div_mul_cancel₀ _ (by exact_mod_cast hn),
      Real.rpow_natCast]
  exact le_of_pow_le_pow_left₀ hn hc (by rw [h1]; exact h)

theorem le_rpow_div {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (k n : ℕ) (hn : n ≠ 0)
    (h : c ^ n ≤ a ^ k) : c ≤ a ^ ((k : ℝ) / n) := by
  have h1 : (a ^ ((k : ℝ) / n)) ^ n = a ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha, div_mul_cancel₀ _ (by exact_mod_cast hn),
      Real.rpow_natCast]
  exact le_of_pow_le_pow_left₀ hn (Real.rpow_nonneg ha _) (by rw [h1]; exact h)

/-! ### The cluster state -/

theorem logb_two_rpow_one_sub (q : ℝ) : Real.logb 2 ((2 : ℝ) ^ (1 - q)) = 1 - q :=
  Real.logb_rpow (by norm_num) (by norm_num)

theorem logb_four_mul_quarter_rpow (q : ℝ) : Real.logb 2 (4 * (1 / 4 : ℝ) ^ q) = 2 * (1 - q) := by
  have h4 : Real.logb 2 (4 : ℝ) = 2 := logb_two_four
  have h41 : Real.logb 2 (1 / 4 : ℝ) = -2 := by
    rw [one_div, Real.logb_inv, h4]
  rw [Real.logb_mul (by norm_num) (by positivity), h4,
    Real.logb_rpow_eq_mul_logb_of_pos (by norm_num), h41]
  ring

/-- The mean Rényi entropy of the cluster state is `5/3` for every `q > 0`, `q ≠ 1`
(`prop:fqe-renyi-crossing`, first assertion of the proof). -/
theorem meanRenyi_cluster4 {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) : meanRenyi q cluster4 = 5 / 3 := by
  have hq' : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq1)
  have e1 := cutMoment_cluster12 (q := q) hq0
  have e2 := cutMoment_cluster13 (q := q)
  have e3 := cutMoment_cluster14 (q := q)
  unfold cutMoment at e1 e2 e3
  unfold meanRenyi renyiCut
  rw [e1, e2, e3, logb_two_rpow_one_sub, logb_four_mul_quarter_rpow]
  field_simp
  ring

/-- The von Neumann case (`q = 1`): the mean entropy of the cluster state is also `5/3`. -/
theorem meanEntropy_cluster4 : meanEntropy cluster4 = 5 / 3 := by
  have hR : red12 cluster4 = Matrix.diagonal (fun i : Fin 2 × Fin 2 =>
      if i = (0, 0) ∨ i = (1, 1) then (1 / 2 : ℂ) else 0) := red12_cluster4
  have hcub : red12 cluster4 * (red12 cluster4 - (((1 / 2 : ℝ)) : ℂ) • 1)
      * (red12 cluster4 - (((1 / 2 : ℝ)) : ℂ) • 1) = 0 := by
    rw [hR]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two] <;> norm_num
  have htr : (Matrix.trace (red12 cluster4)).re = 1 := by
    rw [trace_red12, cluster4_vals.1]; simp
  have htr2 : (Matrix.trace (red12 cluster4 * red12 cluster4)).re = (1 / 2 : ℝ) ^ 2 + (1 / 2 : ℝ) ^ 2 := by
    rw [hR]
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two]
    norm_num
  have h12 := cutSum_rank_two (red12_herm cluster4) (by norm_num) (by norm_num) (by norm_num) hcub htr
    htr2 Real.negMulLog Real.negMulLog_zero
  have e12 : entSpec (red12_herm cluster4).eigenvalues = 1 := by
    unfold entSpec
    rw [h12]
    have : Real.negMulLog (1 / 2 : ℝ) = Real.log 2 / 2 := by
      rw [Real.negMulLog, one_div, Real.log_inv]; ring
    rw [this]
    have l2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp
    ring
  have u13 : ∀ i, (red13_herm cluster4).eigenvalues i = 1 / 4 :=
    eigenvalues_of_scalar _ (by rw [red13_cluster4]; simp)
  have u14 : ∀ i, (red14_herm cluster4).eigenvalues i = 1 / 4 :=
    eigenvalues_of_scalar _ (by rw [red14_cluster4]; simp)
  have e13 : entSpec (red13_herm cluster4).eigenvalues = 2 :=
    (entSpec_eq_two_iff (isProb13 cluster4_vals.1)).2 u13
  have e14 : entSpec (red14_herm cluster4).eigenvalues = 2 :=
    (entSpec_eq_two_iff (isProb14 cluster4_vals.1)).2 u14
  simp only [meanEntropy, vnEntropy_eq_entSpec, e12, e13, e14]; norm_num

/-- Strict order monotonicity of the Rényi entropy of a non-constant positive vector, `1 < q < q'`. -/
theorem renyiSpec_strictAnti {ι : Type*} [Fintype ι] {q q' : ℝ} (hq : 1 < q) (hqq : q < q')
    {l : ι → ℝ} (hl : ∀ i, 0 < l i) (hs : ∑ i, l i = 1) (hne : ∃ j k, l j ≠ l k) :
    renyiSpec q' l < renyiSpec q l := by
  have hpos : 0 < ∑ i, l i ^ q := by
    have : Nonempty ι := by
      by_contra h; rw [not_nonempty_iff] at h; simp at hs
    exact sum_rpow_pos (fun i => (hl i).le) hs
  have hle := sum_rpow_lt_sum_rpow hq hqq hl hs hne
  have hlog := Real.log_lt_log (Real.rpow_pos_of_pos hpos _) hle
  rw [Real.log_rpow hpos] at hlog
  rw [renyiSpec_eq_neg hq, renyiSpec_eq_neg (by linarith)]
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : 0 < q - 1 := by linarith
  have h2 : 0 < q' - 1 := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have := mul_lt_mul_of_pos_left hlog (mul_pos h1 h2)
  have e : (q - 1) * (q' - 1) * ((q' - 1) / (q - 1) * Real.log (∑ i, l i ^ q))
      = (q' - 1) ^ 2 * Real.log (∑ i, l i ^ q) := by field_simp
  rw [e] at this
  nlinarith [this, mul_pos l2 l2, mul_pos h1 h2]

/-- The HS spectrum `(1/2, 1/6, 1/6, 1/6)`. -/
noncomputable def hsSpec : Fin 4 → ℝ := ![1 / 2, 1 / 6, 1 / 6, 1 / 6]

theorem hsRenyi_eq (q : ℝ) : hsRenyi q = renyiSpec q hsSpec := by
  unfold hsRenyi renyiSpec hsSpec
  have h1 : ∑ i, ![(1 / 2 : ℝ), 1 / 6, 1 / 6, 1 / 6] i ^ q = (1 / 2 : ℝ) ^ q + 3 * (1 / 6 : ℝ) ^ q := by
    simp [Fin.sum_univ_four]; ring
  rw [h1, moment_const_eq]

/-- `h_q` is strictly decreasing for `q > 1` (`prop:fqe-renyi-crossing`: the HS Rényi value of the
non-uniform full-support spectrum is strictly decreasing in the order). -/
theorem hsRenyi_strictAntiOn : StrictAntiOn hsRenyi (Set.Ioi 1) := by
  intro q hq q' hq' hlt
  rw [hsRenyi_eq, hsRenyi_eq]
  refine renyiSpec_strictAnti hq hlt ?_ ?_ ⟨0, 1, by simp [hsSpec]⟩
  · intro i; fin_cases i <;> simp [hsSpec] <;> norm_num
  · simp [hsSpec, Fin.sum_univ_four]; norm_num

/-- The mean Rényi entropy of `M₄` is `h_q` (every order). -/
theorem meanRenyi_M4 (q : ℝ) : meanRenyi q M4 = hsRenyi q := by
  have t12 : (Matrix.trace (red12 M4)).re = 1 := by rw [trace_red12, M4_unit]; simp
  have t13 : (Matrix.trace (red13 M4)).re = 1 := by rw [trace_red13, M4_unit]; simp
  have t14 : (Matrix.trace (red14 M4)).re = 1 := by rw [trace_red14, M4_unit]; simp
  have e12 := cutMoment_of_quadratic q (red12_herm M4) M4_cutQuadratics.q12 t12
  have e13 := cutMoment_of_quadratic q (red13_herm M4) M4_cutQuadratics.q13 t13
  have e14 := cutMoment_of_quadratic q (red14_herm M4) M4_cutQuadratics.q14 t14
  unfold cutMoment at e12 e13 e14
  unfold meanRenyi renyiCut hsRenyi
  rw [e12, e13, e14]; ring

/-! ### Numerical enclosures -/

theorem hs_gt_at_three_halves : 5 / 3 < hsRenyi (3 / 2) := by
  unfold hsRenyi
  have hm : (2 : ℝ) ^ (-(3 / 2 : ℝ)) + 3 * (6 : ℝ) ^ (-(3 / 2 : ℝ)) < 14 / 25 := by
    have a1 : (2828 / 1000 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℕ) / (2 : ℕ) : ℝ) :=
      le_rpow_div (by norm_num) (by norm_num) 3 2 (by norm_num) (by norm_num)
    have a2 : (1469 / 100 : ℝ) ≤ (6 : ℝ) ^ ((3 : ℕ) / (2 : ℕ) : ℝ) :=
      le_rpow_div (by norm_num) (by norm_num) 3 2 (by norm_num) (by norm_num)
    push_cast at a1 a2
    rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
    have b1 : ((2 : ℝ) ^ (3 / 2 : ℝ))⁻¹ ≤ (2828 / 1000 : ℝ)⁻¹ := inv_anti₀ (by norm_num) a1
    have b2 : ((6 : ℝ) ^ (3 / 2 : ℝ))⁻¹ ≤ (1469 / 100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) a2
    linarith [show (2828 / 1000 : ℝ)⁻¹ + 3 * (1469 / 100 : ℝ)⁻¹ < 14 / 25 by norm_num]
  have hm0 : 0 < (2 : ℝ) ^ (-(3 / 2 : ℝ)) + 3 * (6 : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
  have hlt : Real.logb 2 ((2 : ℝ) ^ (-(3 / 2 : ℝ)) + 3 * (6 : ℝ) ^ (-(3 / 2 : ℝ))) < -(5 / 6) := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) hm0]
    have c1 : (2 : ℝ) ^ ((5 : ℕ) / (6 : ℕ) : ℝ) ≤ 25 / 14 :=
      rpow_div_le (by norm_num) (by norm_num) 5 6 (by norm_num) (by norm_num)
    push_cast at c1
    have e : (2 : ℝ) ^ (-(5 / 6 : ℝ)) = ((2 : ℝ) ^ (5 / 6 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
    have := inv_anti₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (5 / 6 : ℝ)) c1
    rw [e]
    calc _ < 14 / 25 := hm
      _ = (25 / 14 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := this
  rw [show (1 : ℝ) - 3 / 2 = -(1 / 2) by norm_num, lt_div_iff_of_neg (by norm_num)]
  linarith

theorem hs_lt_at_eight_fifths : hsRenyi (8 / 5) < 5 / 3 := by
  unfold hsRenyi
  have hm : (1 : ℝ) / 2 < (2 : ℝ) ^ (-(8 / 5 : ℝ)) + 3 * (6 : ℝ) ^ (-(8 / 5 : ℝ)) := by
    have a1 : (2 : ℝ) ^ ((8 : ℕ) / (5 : ℕ) : ℝ) ≤ 3032 / 1000 :=
      rpow_div_le (by norm_num) (by norm_num) 8 5 (by norm_num) (by norm_num)
    have a2 : (6 : ℝ) ^ ((8 : ℕ) / (5 : ℕ) : ℝ) ≤ 176 / 10 :=
      rpow_div_le (by norm_num) (by norm_num) 8 5 (by norm_num) (by norm_num)
    push_cast at a1 a2
    rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
    have b1 : (3032 / 1000 : ℝ)⁻¹ ≤ ((2 : ℝ) ^ (8 / 5 : ℝ))⁻¹ :=
      inv_anti₀ (by positivity) a1
    have b2 : (176 / 10 : ℝ)⁻¹ ≤ ((6 : ℝ) ^ (8 / 5 : ℝ))⁻¹ :=
      inv_anti₀ (by positivity) a2
    linarith [show (1 : ℝ) / 2 < (3032 / 1000 : ℝ)⁻¹ + 3 * (176 / 10 : ℝ)⁻¹ by norm_num]
  have hlt : -1 < Real.logb 2 ((2 : ℝ) ^ (-(8 / 5 : ℝ)) + 3 * (6 : ℝ) ^ (-(8 / 5 : ℝ))) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
    rw [Real.rpow_neg (by norm_num), Real.rpow_one]
    linarith
  rw [show (1 : ℝ) - 8 / 5 = -(3 / 5) by norm_num, div_lt_iff_of_neg (by norm_num)]
  linarith

theorem hsRenyi_continuousOn : ContinuousOn hsRenyi (Set.Icc (3 / 2) (8 / 5)) := by
  unfold hsRenyi
  have hc : ContinuousOn (fun q : ℝ => (2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q)) (Set.Icc (3 / 2) (8 / 5)) := by
    apply Continuous.continuousOn
    exact (Real.continuous_const_rpow (by norm_num)).comp continuous_neg |>.add
      (continuous_const.mul ((Real.continuous_const_rpow (by norm_num)).comp continuous_neg))
  refine ContinuousOn.div ?_ (continuousOn_const.sub continuousOn_id) ?_
  · unfold Real.logb
    exact (hc.log (fun q _ => by positivity)).div_const _
  · intro q hq; have := hq.1; linarith [hq.1]

/-- **HS–cluster crossing** (`prop:fqe-renyi-crossing`): there is a unique `q_* ∈ (3/2, 8/5)` with
`h_{q_*} = 5/3`; the cluster state has strictly larger mean Rényi entropy than `M₄` for `q > q_*`,
strictly smaller for `1 < q < q_*`, and the two values coincide at `q_*`. -/
theorem renyi_crossing :
    ∃ qs : ℝ, (3 / 2 < qs ∧ qs < 8 / 5) ∧ hsRenyi qs = 5 / 3 ∧
      (∀ q', 3 / 2 < q' → q' < 8 / 5 → hsRenyi q' = 5 / 3 → q' = qs) ∧
      meanRenyi qs M4 = meanRenyi qs cluster4 ∧
      (∀ q, 1 < q → q < qs → meanRenyi q cluster4 < meanRenyi q M4) ∧
      (∀ q, qs < q → meanRenyi q M4 < meanRenyi q cluster4) := by
  have hmem : (5 / 3 : ℝ) ∈ Set.Icc (hsRenyi (8 / 5)) (hsRenyi (3 / 2)) :=
    ⟨hs_lt_at_eight_fifths.le, hs_gt_at_three_halves.le⟩
  obtain ⟨qs, hqs, hq5⟩ := intermediate_value_Icc' (by norm_num : (3 / 2 : ℝ) ≤ 8 / 5)
    hsRenyi_continuousOn hmem
  have h1 : 3 / 2 < qs := by
    rcases hqs.1.eq_or_lt with h | h
    · rw [← h] at hq5; linarith [hs_gt_at_three_halves]
    · exact h
  have h2 : qs < 8 / 5 := by
    rcases hqs.2.eq_or_lt with h | h
    · rw [h] at hq5; linarith [hs_lt_at_eight_fifths]
    · exact h
  have hanti := hsRenyi_strictAntiOn
  have hc : ∀ q : ℝ, 0 < q → q ≠ 1 → meanRenyi q cluster4 = 5 / 3 := fun q h0 h1 =>
    meanRenyi_cluster4 h0 h1
  refine ⟨qs, ⟨h1, h2⟩, hq5, ?_, ?_, ?_, ?_⟩
  · intro q' h3 h4 h5
    exact hanti.injOn (Set.mem_Ioi.2 (by linarith)) (Set.mem_Ioi.2 (by linarith)) (h5.trans hq5.symm)
  · rw [meanRenyi_M4, hq5, hc qs (by linarith) (by linarith)]
  · intro q hq hlt
    rw [meanRenyi_M4, hc q (by linarith) hq.ne']
    have := hanti (Set.mem_Ioi.2 hq) (Set.mem_Ioi.2 (by linarith : (1 : ℝ) < qs)) hlt
    linarith
  · intro q hlt
    rw [meanRenyi_M4, hc q (by linarith) (by linarith)]
    have := hanti (Set.mem_Ioi.2 (by linarith : (1 : ℝ) < qs)) (Set.mem_Ioi.2 (by linarith : (1 : ℝ) < q)) hlt
    linarith

set_option exponentiation.threshold 5000 in
theorem hs_gt_at_1587 : 5 / 3 < hsRenyi (1587 / 1000) := by
  unfold hsRenyi
  have hm : (2 : ℝ) ^ (-(1587 / 1000 : ℝ)) + 3 * (6 : ℝ) ^ (-(1587 / 1000 : ℝ))
      < (19701881 / 10000000 : ℝ)⁻¹ := by
    have a1 : (30042398 / 10000000 : ℝ) ≤ (2 : ℝ) ^ ((1587 : ℕ) / (1000 : ℕ) : ℝ) :=
      le_rpow_div (by norm_num) (by norm_num) 1587 1000 (by norm_num) (by norm_num)
    have a2 : (17176158 / 1000000 : ℝ) ≤ (6 : ℝ) ^ ((1587 : ℕ) / (1000 : ℕ) : ℝ) :=
      le_rpow_div (by norm_num) (by norm_num) 1587 1000 (by norm_num) (by norm_num)
    push_cast at a1 a2
    rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
    have b1 := inv_anti₀ (by norm_num) a1
    have b2 := inv_anti₀ (by norm_num) a2
    linarith [show (30042398 / 10000000 : ℝ)⁻¹ + 3 * (17176158 / 1000000 : ℝ)⁻¹
      < (19701881 / 10000000 : ℝ)⁻¹ by norm_num]
  have hm0 : 0 < (2 : ℝ) ^ (-(1587 / 1000 : ℝ)) + 3 * (6 : ℝ) ^ (-(1587 / 1000 : ℝ)) := by positivity
  have hlt : Real.logb 2 ((2 : ℝ) ^ (-(1587 / 1000 : ℝ)) + 3 * (6 : ℝ) ^ (-(1587 / 1000 : ℝ)))
      < -(587 / 600) := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) hm0]
    have c1 : (2 : ℝ) ^ ((587 : ℕ) / (600 : ℕ) : ℝ) ≤ 19701881 / 10000000 :=
      rpow_div_le (by norm_num) (by norm_num) 587 600 (by norm_num) (by norm_num)
    push_cast at c1
    have e : (2 : ℝ) ^ (-(587 / 600 : ℝ)) = ((2 : ℝ) ^ (587 / 600 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
    have := inv_anti₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (587 / 600 : ℝ)) c1
    rw [e]
    exact lt_of_lt_of_le hm this
  rw [show (1 : ℝ) - 1587 / 1000 = -(587 / 1000) by norm_num, lt_div_iff_of_neg (by norm_num)]
  linarith

set_option exponentiation.threshold 5000 in
theorem hs_lt_at_1589 : hsRenyi (1589 / 1000) < 5 / 3 := by
  unfold hsRenyi
  have hm : (19747454 / 10000000 : ℝ)⁻¹ < (2 : ℝ) ^ (-(1589 / 1000 : ℝ)) + 3 * (6 : ℝ) ^ (-(1589 / 1000 : ℝ)) := by
    have a1 : (2 : ℝ) ^ ((1589 : ℕ) / (1000 : ℕ) : ℝ) ≤ 30084076 / 10000000 :=
      rpow_div_le (by norm_num) (by norm_num) 1589 1000 (by norm_num) (by norm_num)
    have a2 : (6 : ℝ) ^ ((1589 : ℕ) / (1000 : ℕ) : ℝ) ≤ 17237820 / 1000000 :=
      rpow_div_le (by norm_num) (by norm_num) 1589 1000 (by norm_num) (by norm_num)
    push_cast at a1 a2
    rw [Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num)]
    have b1 := inv_anti₀ (by positivity) a1
    have b2 := inv_anti₀ (by positivity) a2
    linarith [show (19747454 / 10000000 : ℝ)⁻¹
      < (30084076 / 10000000 : ℝ)⁻¹ + 3 * (17237820 / 1000000 : ℝ)⁻¹ by norm_num]
  have hlt : -(589 / 600) < Real.logb 2 ((2 : ℝ) ^ (-(1589 / 1000 : ℝ)) + 3 * (6 : ℝ) ^ (-(1589 / 1000 : ℝ))) := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
    have c1 : (19747454 / 10000000 : ℝ) ≤ (2 : ℝ) ^ ((589 : ℕ) / (600 : ℕ) : ℝ) :=
      le_rpow_div (by norm_num) (by norm_num) 589 600 (by norm_num) (by norm_num)
    push_cast at c1
    have e : (2 : ℝ) ^ (-(589 / 600 : ℝ)) = ((2 : ℝ) ^ (589 / 600 : ℝ))⁻¹ := Real.rpow_neg (by norm_num) _
    have := inv_anti₀ (by norm_num) c1
    rw [e]
    exact lt_of_le_of_lt this hm
  rw [show (1 : ℝ) - 1589 / 1000 = -(589 / 1000) by norm_num, div_lt_iff_of_neg (by norm_num)]
  linarith

/-- **The paper's enclosure** (`prop:fqe-renyi-crossing`): `1587/1000 < q_* < 1589/1000`. -/
theorem crossing_fine {qs : ℝ} (h1 : 1 < qs) (h : hsRenyi qs = 5 / 3) :
    1587 / 1000 < qs ∧ qs < 1589 / 1000 := by
  have hanti := hsRenyi_strictAntiOn
  constructor
  · by_contra hle
    push Not at hle
    rcases hle.eq_or_lt with he | hlt
    · rw [he] at h; linarith [hs_gt_at_1587]
    · have := hanti (Set.mem_Ioi.2 h1) (Set.mem_Ioi.2 (by norm_num : (1 : ℝ) < 1587 / 1000)) hlt
      linarith [hs_gt_at_1587]
  · by_contra hle
    push Not at hle
    rcases hle.eq_or_lt with he | hlt
    · rw [← he] at h; linarith [hs_lt_at_1589]
    · have := hanti (Set.mem_Ioi.2 (by norm_num : (1 : ℝ) < 1589 / 1000)) (Set.mem_Ioi.2 h1) hlt
      linarith [hs_lt_at_1589]

/-- info: 'FormalResearch.FourQubitEntropy.meanRenyi_cluster4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms meanRenyi_cluster4

/-- info: 'FormalResearch.FourQubitEntropy.meanEntropy_cluster4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms meanEntropy_cluster4

/-- info: 'FormalResearch.FourQubitEntropy.meanRenyi_M4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms meanRenyi_M4

/-- info: 'FormalResearch.FourQubitEntropy.hsRenyi_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hsRenyi_strictAntiOn

/-- info: 'FormalResearch.FourQubitEntropy.renyi_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms renyi_crossing

/-- info: 'FormalResearch.FourQubitEntropy.crossing_fine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms crossing_fine

end FormalResearch.FourQubitEntropy
