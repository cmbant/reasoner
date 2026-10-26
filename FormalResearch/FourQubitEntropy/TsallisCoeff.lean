import FormalResearch.FourQubitEntropy.HermiteBound

/-!
# The Tsallis coefficient inequality (T)

With `g(q) = (15 - 7q) 3^{q-1} / (5 + 3q)` we show `g > 1` on `(0,1)` and `g < 1` on `(1,2)`,
which is the sign claim behind the paper's equation (T) (`eq:fqe-tsallis-coefficient`) in the
proof of `cor:fqe-tsallis`.

Proof (as in the paper, via `ℓ = log g`): `ℓ' = log 3 - 80/D` with `D = (15-7q)(5+3q)`, and the
bounds `16/15 < log 3 < 8/7`. On `[0, 10/21]`, `D ≥ 75`, so `ℓ' > 0`; on `[1,2)`, `D ≤ 64`, so
`ℓ' < 0`; on `[10/21, 1]`, `ℓ'` is strictly decreasing so `ℓ` is concave, and
`ℓ(10/21) > 0 = ℓ(1)`.
-/

namespace FormalResearch.FourQubitEntropy

open Real

/-- `ℓ(q) = log g(q)`. -/
noncomputable def ell (q : ℝ) : ℝ := Real.log (15 - 7 * q) + (q - 1) * Real.log 3 - Real.log (5 + 3 * q)

/-- `ℓ'(q)`. -/
noncomputable def ell' (q : ℝ) : ℝ := -7 / (15 - 7 * q) + Real.log 3 - 3 / (5 + 3 * q)

theorem ell_hasDerivAt {q : ℝ} (h1 : 15 - 7 * q ≠ 0) (h2 : 5 + 3 * q ≠ 0) :
    HasDerivAt ell (ell' q) q := by
  have d1 : HasDerivAt (fun x : ℝ => 15 - 7 * x) (-7) q := by
    simpa using ((hasDerivAt_id q).const_mul 7).const_sub 15
  have d2 : HasDerivAt (fun x : ℝ => 5 + 3 * x) 3 q := by
    simpa using ((hasDerivAt_id q).const_mul 3).const_add 5
  have d3 : HasDerivAt (fun x : ℝ => (x - 1) * Real.log 3) (Real.log 3) q := by
    simpa using ((hasDerivAt_id q).sub_const 1).mul_const (Real.log 3)
  have := (d1.log h1).add d3 |>.sub (d2.log h2)
  exact this

theorem ell'_eq {q : ℝ} (h1 : 15 - 7 * q ≠ 0) (h2 : 5 + 3 * q ≠ 0) :
    ell' q = Real.log 3 - 80 / ((15 - 7 * q) * (5 + 3 * q)) := by
  have hD : (15 - 7 * q) * (5 + 3 * q) ≠ 0 := mul_ne_zero h1 h2
  have e : -7 / (15 - 7 * q) - 3 / (5 + 3 * q) = -(80 / ((15 - 7 * q) * (5 + 3 * q))) := by
    rw [div_sub_div _ _ h1 h2, ← neg_div]; congr 1; ring
  unfold ell'
  linarith

theorem ell_zero : ell 0 = 0 := by
  unfold ell
  have : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  norm_num [this]

theorem ell_one : ell 1 = 0 := by
  unfold ell; norm_num

/-- `ℓ` is differentiable on `[0,2]`. -/
theorem ell_hasDerivAt' {q : ℝ} (h0 : 0 ≤ q) (h2 : q ≤ 2) : HasDerivAt ell (ell' q) q :=
  ell_hasDerivAt (by linarith) (by linarith)

theorem ell_continuousOn : ContinuousOn ell (Set.Icc 0 2) := fun x hx =>
  (ell_hasDerivAt' hx.1 hx.2).continuousAt.continuousWithinAt

/-- On `[1, 2)`, `ℓ' < 0`. -/
theorem ell'_neg {q : ℝ} (h1 : 1 ≤ q) (h2 : q < 2) : ell' q < 0 := by
  rw [ell'_eq (by linarith) (by linarith)]
  have hD : 0 < (15 - 7 * q) * (5 + 3 * q) := mul_pos (by linarith) (by linarith)
  have hD64 : (15 - 7 * q) * (5 + 3 * q) ≤ 64 := by nlinarith
  have : 5 / 4 ≤ 80 / ((15 - 7 * q) * (5 + 3 * q)) := by
    rw [le_div_iff₀ hD]; nlinarith
  have := log_three_lt
  linarith

/-- On `[0, 10/21]`, `ℓ' > 0`. -/
theorem ell'_pos {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 10 / 21) : 0 < ell' q := by
  rw [ell'_eq (by linarith) (by linarith)]
  have hD75 : 75 ≤ (15 - 7 * q) * (5 + 3 * q) := by nlinarith
  have : 80 / ((15 - 7 * q) * (5 + 3 * q)) ≤ 16 / 15 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have := lt_log_three
  linarith

theorem ell_pos_Ioc {q : ℝ} (h0 : 0 < q) (h1 : q ≤ 10 / 21) : 0 < ell q := by
  have hm : StrictMonoOn ell (Set.Icc 0 q) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 q)
    · exact ell_continuousOn.mono (Set.Icc_subset_Icc le_rfl (by linarith))
    · intro x hx
      rw [interior_Icc] at hx
      rw [(ell_hasDerivAt' hx.1.le (by linarith [hx.2])).deriv]
      exact ell'_pos hx.1.le (by linarith [hx.2])
  have := hm ⟨le_rfl, h0.le⟩ ⟨h0.le, le_rfl⟩ h0
  rwa [ell_zero] at this

theorem ell_neg_Ioo {q : ℝ} (h1 : 1 < q) (h2 : q < 2) : ell q < 0 := by
  have hm : StrictAntiOn ell (Set.Icc 1 q) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 1 q)
    · exact ell_continuousOn.mono (Set.Icc_subset_Icc (by norm_num) (by linarith))
    · intro x hx
      rw [interior_Icc] at hx
      rw [(ell_hasDerivAt' (by linarith [hx.1]) (by linarith [hx.2])).deriv]
      exact ell'_neg hx.1.le (by linarith [hx.2])
  have := hm ⟨le_rfl, h1.le⟩ ⟨h1.le, le_rfl⟩ h1
  rwa [ell_one] at this

/-- `ℓ` is concave on `[10/21, 1]`. -/
theorem ell_concaveOn : ConcaveOn ℝ (Set.Icc (10 / 21 : ℝ) 1) ell := by
  apply StrictConcaveOn.concaveOn
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _)
  · exact ell_continuousOn.mono (Set.Icc_subset_Icc (by norm_num) (by norm_num))
  · intro x hx y hy hxy
    rw [interior_Icc] at hx hy
    rw [(ell_hasDerivAt' (q := x) (by linarith [hx.1]) (by linarith [hx.2])).deriv,
      (ell_hasDerivAt' (q := y) (by linarith [hy.1]) (by linarith [hy.2])).deriv,
      ell'_eq (q := x) (by linarith [hx.2]) (by linarith [hx.1]),
      ell'_eq (q := y) (by linarith [hy.2]) (by linarith [hy.1])]
    have hDx : 0 < (15 - 7 * x) * (5 + 3 * x) := mul_pos (by linarith [hx.2]) (by linarith [hx.1])
    have hDy : 0 < (15 - 7 * y) * (5 + 3 * y) := mul_pos (by linarith [hy.2]) (by linarith [hy.1])
    have hlt : (15 - 7 * y) * (5 + 3 * y) < (15 - 7 * x) * (5 + 3 * x) := by
      nlinarith [hx.1, hy.1, hxy]
    have := div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 80) hDy hlt
    linarith

theorem ell_pos_Ioo {q : ℝ} (h0 : 0 < q) (h1 : q < 1) : 0 < ell q := by
  rcases le_total q (10 / 21) with h | h
  · exact ell_pos_Ioc h0 h
  · have hA : 0 < ell (10 / 21) := ell_pos_Ioc (by norm_num) le_rfl
    -- `q = (1 - t) (10/21) + t`
    set t : ℝ := (q - 10 / 21) / (11 / 21) with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith) (by norm_num)
    have ht1 : t < 1 := by rw [ht, div_lt_one (by norm_num)]; linarith
    have hq : (1 - t) • (10 / 21 : ℝ) + t • (1 : ℝ) = q := by
      simp only [smul_eq_mul, ht]; field_simp; ring
    have hc := ell_concaveOn.2 (x := 10 / 21) (y := 1) ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
      (by linarith : 0 ≤ 1 - t) ht0 (by ring)
    rw [hq] at hc
    simp only [smul_eq_mul, ell_one, mul_zero, add_zero] at hc
    have : 0 < (1 - t) * ell (10 / 21) := mul_pos (by linarith) hA
    linarith

/-- `g(q) = (15 - 7q) 3^{q-1} / (5 + 3q)` equals `exp (ℓ q)`. -/
theorem g_eq_exp {q : ℝ} (h0 : 0 ≤ q) (h2 : q < 2) :
    (15 - 7 * q) * (3 : ℝ) ^ (q - 1) / (5 + 3 * q) = Real.exp (ell q) := by
  have a1 : 0 < 15 - 7 * q := by linarith
  have a2 : 0 < 5 + 3 * q := by linarith
  unfold ell
  rw [Real.exp_sub, Real.exp_add, Real.exp_log a1, Real.exp_log a2,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [mul_comm (Real.log 3)]

/-- `g > 1` on `(0,1)`. -/
theorem tsallis_g_gt_one {q : ℝ} (h0 : 0 < q) (h1 : q < 1) :
    5 + 3 * q < (15 - 7 * q) * (3 : ℝ) ^ (q - 1) := by
  have := g_eq_exp h0.le (by linarith)
  have e : 1 < Real.exp (ell q) := by simpa using Real.exp_lt_exp.2 (ell_pos_Ioo h0 h1)
  rw [← this, lt_div_iff₀ (by linarith)] at e
  linarith

/-- `g < 1` on `(1,2)`. -/
theorem tsallis_g_lt_one {q : ℝ} (h1 : 1 < q) (h2 : q < 2) :
    (15 - 7 * q) * (3 : ℝ) ^ (q - 1) < 5 + 3 * q := by
  have := g_eq_exp (by linarith) h2
  have e : Real.exp (ell q) < 1 := by simpa using Real.exp_lt_exp.2 (ell_neg_Ioo h1 h2)
  rw [← this, div_lt_iff₀ (by linarith)] at e
  linarith

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_g_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tsallis_g_gt_one

/-- info: 'FormalResearch.FourQubitEntropy.tsallis_g_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tsallis_g_lt_one

end FormalResearch.FourQubitEntropy
