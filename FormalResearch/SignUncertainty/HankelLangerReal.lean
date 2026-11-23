module

public import FormalResearch.SignUncertainty.HankelLangerY

/-!
# Reality and monotonicity of the Langer coordinate on the real axis (`gt:7.7b` (iv))

`y(conj w) = conj y(w)` for `‖w‖ ≤ 10⁻³` (real coefficients, uniqueness of `K^{-1}`), hence `y` is real on the real
axis; with `y' + 1 = O(4·10⁻³)` this makes it strictly decreasing there, and `y(0) = 0`.
-/

@[expose] public section

open Complex Set Metric Filter Topology
open scoped Real ComplexConjugate

namespace FormalResearch.SignUncertainty

section Real

variable {η : ℕ → ℝ}

lemma psW_conj (a : ℕ → ℝ) (w : ℂ) : psW a (conj w) = conj (psW a w) := by
  unfold psW
  rw [Complex.conj_tsum]
  refine tsum_congr (fun j => ?_)
  simp [map_mul, map_pow]

lemma chartK_conj (η : ℕ → ℝ) (u : ℂ) : chartK η (conj u) = conj (chartK η u) := by
  unfold chartK; rw [map_mul, psW_conj]

lemma chartKinv_conj (h : LangerEta η) {v : ℂ} (hv : v ∈ chartVdisc) :
    chartKinv η (conj v) = conj (chartKinv η v) := by
  have hv' : conj v ∈ chartVdisc := by
    rw [mem_chartVdisc, Complex.norm_conj]; exact mem_chartVdisc.1 hv
  obtain ⟨hu, hK⟩ := chartKinv_spec h hv
  refine chartKinv_eq_of (h := h) hv' ?_ ?_
  · rw [mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.1 hu
  · rw [chartK_conj, hK]

lemma chartM_conj (h : LangerEta η) {u : ℂ} (hu : ‖u‖ ≤ 0.035 ^ 2) :
    chartM η (conj u) = conj (chartM η u) := by
  have hx := norm_psW_aE_sub_one_u h hu
  have hs : psW (aE η) u ∈ slitPlane := by
    have := one_add_mem_slitPlane (y := psW (aE η) u - 1) (lt_of_le_of_lt hx (by norm_num))
    simpa using this
  have harg : (psW (aE η) u).arg ≠ π := (Complex.mem_slitPlane_iff_arg.1 hs).1
  unfold chartM powMapU
  rw [psW_conj, Complex.conj_cpow _ _ harg, Complex.conj_ofReal, map_mul]

lemma chartVofW_conj {w : ℂ} (hw : ‖w‖ ≤ 1e-3) : chartVofW (conj w) = conj (chartVofW w) := by
  have hs : (1 + w) ∈ slitPlane := one_add_mem_slitPlane (lt_of_le_of_lt hw (by norm_num))
  have harg : (1 + w).arg ≠ π := (Complex.mem_slitPlane_iff_arg.1 hs).1
  unfold chartVofW
  rw [map_mul, Complex.conj_ofReal, map_neg, ← Complex.log_conj _ harg, map_add, map_one]

lemma chartY_conj (h : LangerEta η) {w : ℂ} (hw : ‖w‖ ≤ 1e-3) :
    chartY η (conj w) = conj (chartY η w) := by
  have hv := chartVofW_mem hw
  obtain ⟨hu, _⟩ := chartKinv_spec h hv
  have hun : ‖chartKinv η (chartVofW w)‖ ≤ 0.035 ^ 2 := (mem_ball_zero_iff.1 hu).le
  unfold chartY chartXi
  rw [chartVofW_conj hw, chartKinv_conj h hv, chartM_conj h hun, map_mul, Complex.conj_ofReal]

/-- `y` is real on the real axis. -/
lemma chartY_real (h : LangerEta η) {t : ℝ} (ht : |t| ≤ 1e-3) : (chartY η (t : ℂ)).im = 0 := by
  have hw : ‖(t : ℂ)‖ ≤ 1e-3 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have := chartY_conj h hw
  rw [Complex.conj_ofReal] at this
  have h2 := congrArg Complex.im this
  simp only [Complex.conj_im] at h2
  linarith

/-- `y` is strictly decreasing on the real segment `[-10⁻³, 10⁻³]`. -/
lemma chartY_strictAntiOn (h : LangerEta η) :
    StrictAntiOn (fun t : ℝ => (chartY η (t : ℂ)).re) (Icc (-1e-3) 1e-3) := by
  have hderiv : ∀ t ∈ Icc (-1e-3 : ℝ) 1e-3,
      HasDerivAt (fun t : ℝ => (chartY η (t : ℂ)).re) (chartYD η (t : ℂ)).re t := by
    intro t ht
    have hw : ‖(t : ℂ)‖ ≤ 1e-3 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; exact ⟨ht.1, ht.2⟩
    have h1 := (hasDerivAt_chartY h hw).comp_ofReal
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  have hcont : ContinuousOn (fun t : ℝ => (chartY η (t : ℂ)).re) (Icc (-1e-3) 1e-3) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont (fun t ht => ?_)
  rw [interior_Icc] at ht
  rw [(hderiv t ⟨ht.1.le, ht.2.le⟩).deriv]
  have hw : ‖(t : ℂ)‖ ≤ 1e-3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; exact ⟨ht.1.le, ht.2.le⟩
  have := re_neg_chartYD_pos h hw
  simp only [Complex.neg_re] at this
  linarith

lemma chartY_zero (h : LangerEta η) : chartY η 0 = 0 := by
  have hv : chartVofW 0 ∈ chartVdisc := chartVofW_mem (by simp; norm_num)
  have h0 : chartVofW 0 = 0 := by simp [chartVofW]
  have hK0 : chartKinv η 0 = 0 := by
    refine chartKinv_eq_of (h := h) (by rw [← h0]; exact hv) (mem_ball_self (by norm_num)) ?_
    simp [chartK]
  unfold chartY chartXi
  rw [h0, hK0]; simp [chartM, powMapU]

end Real

/-- info: 'FormalResearch.SignUncertainty.chartY_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chartY_real

/-- info: 'FormalResearch.SignUncertainty.chartY_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chartY_strictAntiOn

/-- info: 'FormalResearch.SignUncertainty.chartY_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms chartY_zero

end FormalResearch.SignUncertainty
