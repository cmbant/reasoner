module

public import FormalResearch.ModularBootstrap.Upper.Holes.K8

/-!
# The near-tip amplitude-to-level ratio (`rem:thmU` Step (3), "Amplitude")

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (3), "Amplitude":
"`Amp/Lev ≤ vρ_∞(x; 3/4)(1 + O(1/c'))` ... the near-tip ratio gives `|ĥ_0|/Lev ≤ C_2 (n/c')^{5/6}(...)`".

`nearTip_ratio`: there is `C_v < ∞` with `vρ_∞(ξ_* + r; 3/4) ≤ C_v r^{5/4}` for `0 < r ≤ 1`.  The mechanism:
`F'(v_0)² = (sinh²(πx) - 1)/cosh²(πx) ≥ 2πr/K` vanishes like `r` at the tip (`sinh(πξ_*) = 1`), so
`F'(v_0)^{-1/2} ≲ r^{-1/4}`, while `T(x)^{3/2} ≲ r^{3/2}` (`T(ξ_* + r) ≤ tanh(πr/2) ≤ πr/2`); the other factors
(`√(v_0² + 1/4)/x`, `coth(πx/2)`) are bounded on `[ξ_*, ξ_* + 1]`.
-/

@[expose] public section

open Real
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Holes

lemma sinh_le_mul_cosh_R {z : ℝ} (hz : 0 ≤ z) : Real.sinh z ≤ z * Real.cosh z := by
  have hmono : MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_id.mul Real.continuous_cosh |>.sub Real.continuous_sinh).continuousOn
    · exact ((differentiable_id.mul Real.differentiable_cosh).sub
        Real.differentiable_sinh).differentiableOn.mono (fun _ _ => trivial) |>.mono
          (Set.subset_univ _)
    · intro t ht
      rw [interior_Ici] at ht
      have hd : HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t)
          (1 * Real.cosh t + t * Real.sinh t - Real.cosh t) t :=
        ((hasDerivAt_id' t).mul (Real.hasDerivAt_cosh t)).sub (Real.hasDerivAt_sinh t)
      rw [hd.deriv, show 1 * Real.cosh t + t * Real.sinh t - Real.cosh t = t * Real.sinh t by ring]
      exact mul_nonneg ht.out.le (Real.sinh_nonneg_iff.mpr ht.out.le)
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hz) hz
  change 0 * Real.cosh 0 - Real.sinh 0 ≤ z * Real.cosh z - Real.sinh z at this
  simp only [Real.cosh_zero, Real.sinh_zero, zero_mul, sub_zero] at this
  linarith

lemma tanh_le_self_R {z : ℝ} (hz : 0 ≤ z) : Real.tanh z ≤ z := by
  rw [Real.tanh_eq_sinh_div_cosh, div_le_iff₀ (Real.cosh_pos z)]
  exact sinh_le_mul_cosh_R hz

lemma tanh_nonneg_R {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Real.tanh z := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hz) (Real.cosh_pos z).le

lemma tanh_lt_one_R (u : ℝ) : Real.tanh u < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos u), Real.sinh_eq, Real.cosh_eq]
  linarith [Real.exp_pos (-u)]

/-- `sinh(π(ξ_* + r)) ≥ 1 + πr`. -/
lemma sinh_tip_ge {r : ℝ} (hr : 0 ≤ r) : 1 + π * r ≤ Real.sinh (π * (xiStar + r)) := by
  have hpi := Real.pi_pos
  have h1 : Real.sinh (π * (xiStar + r)) =
      Real.sinh (π * xiStar) * Real.cosh (π * r) + Real.cosh (π * xiStar) * Real.sinh (π * r) := by
    rw [show π * (xiStar + r) = π * xiStar + π * r by ring, Real.sinh_add]
  have hs0 : Real.sinh (π * xiStar) = 1 := sinh_pi_mul_xiStar
  have hc1 : 1 ≤ Real.cosh (π * xiStar) := Real.one_le_cosh _
  have hc2 : 1 ≤ Real.cosh (π * r) := Real.one_le_cosh _
  have hs2 : π * r ≤ Real.sinh (π * r) := Real.self_le_sinh_iff.mpr (by positivity)
  have hs3 : 0 ≤ Real.sinh (π * r) := by linarith [mul_nonneg hpi.le hr]
  rw [h1, hs0]
  nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hs3]

/-- `0 ≤ v₀(x) ≤ x` for `x > ξ_*`. -/
lemma vZeroK8_bounds {x : ℝ} (hx : xiStar < x) : 0 ≤ vZeroK8 x ∧ vZeroK8 x ≤ x := by
  have hpi := Real.pi_pos
  have hx0 : 0 < x := xiStar_pos.trans hx
  have hs1 : 1 ≤ Real.sinh (π * x) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_le_sinh.mpr (by nlinarith)
  unfold vZeroK8
  refine ⟨div_nonneg (arccoshR_nonneg hs1) hpi.le, ?_⟩
  rw [div_le_iff₀ hpi]
  have hle : Real.sinh (π * x) ≤ Real.cosh (π * x) := by
    rw [Real.sinh_eq, Real.cosh_eq]; linarith [Real.exp_pos (-(π * x))]
  have hmono := strictMonoOn_arccoshR.monotoneOn (Set.mem_Ici.mpr hs1)
    (Set.mem_Ici.mpr (hs1.trans hle)) hle
  rw [arccoshR_cosh (by positivity)] at hmono
  linarith

lemma edgeDerivK8_sq_lower {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    2 * π * r / Real.cosh (π * (xiStar + 1)) ^ 2 ≤ edgeDerivK8 (xiStar + r) ^ 2 := by
  have hpi := Real.pi_pos
  have hge := sinh_tip_ge hr0.le
  set c := Real.cosh (π * (xiStar + r)) with hc
  set sh := Real.sinh (π * (xiStar + r)) with hsh
  have hch : c ^ 2 = 1 + sh ^ 2 := by
    have := Real.cosh_sq_sub_sinh_sq (π * (xiStar + r)); rw [hc, hsh]; linarith
  have hcpos : 0 < c := Real.cosh_pos _
  have hnum : 2 * π * r ≤ sh ^ 2 - 1 := by
    nlinarith [mul_pos hpi hr0, sq_nonneg (π * r)]
  have hharg : 0 ≤ 1 - 2 / c ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith [mul_pos hpi hr0, sq_nonneg (π * r)]
  have hsq : edgeDerivK8 (xiStar + r) ^ 2 = 1 - 2 / c ^ 2 := by
    unfold edgeDerivK8
    exact Real.sq_sqrt hharg
  have hform : 1 - 2 / c ^ 2 = (sh ^ 2 - 1) / c ^ 2 := by
    field_simp
    linarith
  have hcK : c ^ 2 ≤ Real.cosh (π * (xiStar + 1)) ^ 2 := by
    have h : c ≤ Real.cosh (π * (xiStar + 1)) := by
      rw [hc]
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (by have := xiStar_pos; positivity),
        abs_of_nonneg (by have := xiStar_pos; positivity)]
      have := xiStar_pos
      nlinarith
    exact pow_le_pow_left₀ hcpos.le h 2
  rw [hsq, hform]
  calc 2 * π * r / Real.cosh (π * (xiStar + 1)) ^ 2 ≤ 2 * π * r / c ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hcK
    _ ≤ (sh ^ 2 - 1) / c ^ 2 := div_le_div_of_nonneg_right hnum (by positivity)

/-- The constants of the near-tip ratio. -/
noncomputable def tipK7 : ℝ :=
  (1 + 1 / (2 * xiStar)) ^ 2 * Real.cosh (π * (xiStar + 1)) ^ 2 / (2 * π)

noncomputable def tipK3 : ℝ :=
  Real.cosh (π * (xiStar + 1) / 2) / (π * xiStar / 2)

lemma tipK7_pos : 0 < tipK7 := by
  have := xiStar_pos
  unfold tipK7; positivity

lemma tipK3_pos : 0 < tipK3 := by
  have := xiStar_pos
  unfold tipK3; positivity

/-- The saddle factor: `A^{1/2} r^{1/4} ≤ K7^{1/4}` for `A = √(v₀² + 1/4)/(x F'(v₀))`, `x = ξ_* + r`. -/
lemma saddle_factor_bound {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (√(vZeroK8 (xiStar + r) ^ 2 + 1 / 4) / ((xiStar + r) * edgeDerivK8 (xiStar + r))) ^ (1 / 2 : ℝ) *
        r ^ (1 / 4 : ℝ) ≤ tipK7 ^ (1 / 4 : ℝ) := by
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  have hxξ : xiStar < xiStar + r := by linarith
  have hx0 : 0 < xiStar + r := by linarith
  obtain ⟨hv0, hvx⟩ := vZeroK8_bounds hxξ
  have hu2 := edgeDerivK8_sq_lower hr0 hr1
  have hu0 : 0 ≤ edgeDerivK8 (xiStar + r) := Real.sqrt_nonneg _
  set K := Real.cosh (π * (xiStar + 1)) ^ 2 with hK
  have hKpos : 0 < K := by positivity
  set u := edgeDerivK8 (xiStar + r) with hu
  set x := xiStar + r with hx
  have hupos : 0 < u := by
    have : 0 < u ^ 2 := lt_of_lt_of_le (by positivity) hu2
    exact lt_of_le_of_ne hu0 (fun h => by rw [← h] at this; simp at this)
  set K4 : ℝ := 1 + 1 / (2 * xiStar) with hK4
  have hK4pos : 0 < K4 := by positivity
  set A : ℝ := √(vZeroK8 x ^ 2 + 1 / 4) / (x * u) with hA
  have hA0 : 0 ≤ A := by positivity
  have hsqrt : √(vZeroK8 x ^ 2 + 1 / 4) ≤ x + 1 / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hxK4 : x + 1 / 2 ≤ K4 * x := by
    rw [hK4]
    have : 1 / (2 * xiStar) * x ≥ 1 / 2 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have h1 : A ≤ K4 / u := by
    rw [hA, div_le_div_iff₀ (by positivity) hupos]
    calc √(vZeroK8 x ^ 2 + 1 / 4) * u ≤ K4 * x * u :=
          mul_le_mul_of_nonneg_right (hsqrt.trans hxK4) hu0
      _ = K4 * (x * u) := by ring
  have h2 : A ^ 2 ≤ K4 ^ 2 / u ^ 2 := by
    calc A ^ 2 ≤ (K4 / u) ^ 2 := pow_le_pow_left₀ hA0 h1 2
      _ = K4 ^ 2 / u ^ 2 := by rw [div_pow]
  have h3 : K4 ^ 2 / u ^ 2 ≤ K4 ^ 2 / (2 * π * r / K) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hu2
  have h4 : K4 ^ 2 / (2 * π * r / K) = tipK7 / r := by
    unfold tipK7; rw [hK4, hK]; field_simp
  have h5 : A ^ 2 ≤ tipK7 / r := h2.trans (h3.trans_eq h4)
  rw [le_div_iff₀ hr0] at h5
  have e1 : A ^ (1 / 2 : ℝ) = (A ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA0]; norm_num
  rw [e1, ← Real.mul_rpow (by positivity) hr0.le]
  exact Real.rpow_le_rpow (by positivity) h5 (by norm_num)

/-- The tip factor: `T(ξ_* + r)^{3/2} ≤ (π/2)^{3/2} r^{3/2}`. -/
lemma tip_factor_bound {r : ℝ} (hr0 : 0 < r) :
    0 ≤ tanhTipK8 (xiStar + r) ∧
      tanhTipK8 (xiStar + r) ^ (2 * (3 / 4 : ℝ)) ≤ (π / 2) ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) := by
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  have hT0 : 0 ≤ tanhTipK8 (xiStar + r) := by
    unfold tanhTipK8
    exact mul_nonneg (tanh_nonneg_R (by nlinarith)) (tanh_nonneg_R (by nlinarith))
  refine ⟨hT0, ?_⟩
  have hTle : tanhTipK8 (xiStar + r) ≤ π / 2 * r := by
    unfold tanhTipK8
    have e : π * (xiStar + r - xiStar) / 2 = π / 2 * r := by ring
    have h1 : Real.tanh (π * (xiStar + r - xiStar) / 2) ≤ π / 2 * r := by
      rw [e]; exact tanh_le_self_R (by positivity)
    have h2 := tanh_lt_one_R (π * (xiStar + r + xiStar) / 2)
    have h0 : 0 ≤ Real.tanh (π * (xiStar + r - xiStar) / 2) := tanh_nonneg_R (by nlinarith)
    calc Real.tanh (π * (xiStar + r - xiStar) / 2) * Real.tanh (π * (xiStar + r + xiStar) / 2)
        ≤ Real.tanh (π * (xiStar + r - xiStar) / 2) * 1 := mul_le_mul_of_nonneg_left h2.le h0
      _ ≤ π / 2 * r := by linarith
  have e32 : (2 * (3 / 4 : ℝ)) = 3 / 2 := by norm_num
  rw [e32]
  calc tanhTipK8 (xiStar + r) ^ (3 / 2 : ℝ) ≤ (π / 2 * r) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hT0 hTle (by norm_num)
    _ = (π / 2) ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ) := Real.mul_rpow (by positivity) hr0.le

/-- The cotangent factor: `coth(πx/2) ≤ K3` for `ξ_* < x ≤ ξ_* + 1`. -/
lemma coth_factor_bound {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    0 ≤ Real.cosh (π * (xiStar + r) / 2) / Real.sinh (π * (xiStar + r) / 2) ∧
      Real.cosh (π * (xiStar + r) / 2) / Real.sinh (π * (xiStar + r) / 2) ≤ tipK3 := by
  have hpi := Real.pi_pos
  have hξ := xiStar_pos
  set x := xiStar + r with hx
  have hy : 0 < π * x / 2 := by positivity
  have hsp : 0 < Real.sinh (π * x / 2) := Real.sinh_pos_iff.mpr hy
  refine ⟨div_nonneg (Real.cosh_pos _).le hsp.le, ?_⟩
  have hs : π * x / 2 ≤ Real.sinh (π * x / 2) := Real.self_le_sinh_iff.mpr hy.le
  have hc : Real.cosh (π * x / 2) ≤ Real.cosh (π * (xiStar + 1) / 2) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg hy.le, abs_of_nonneg (by positivity)]
    rw [hx]; nlinarith
  have hsx : π * xiStar / 2 ≤ Real.sinh (π * x / 2) := by
    refine le_trans ?_ hs
    rw [hx]; nlinarith
  rw [div_le_iff₀ hsp]
  have hk3 : 0 < tipK3 := tipK3_pos
  calc Real.cosh (π * x / 2) ≤ Real.cosh (π * (xiStar + 1) / 2) := hc
    _ = tipK3 * (π * xiStar / 2) := by unfold tipK3; field_simp
    _ ≤ tipK3 * Real.sinh (π * x / 2) := mul_le_mul_of_nonneg_left hsx hk3.le

/-- **The near-tip ratio** (`rem:thmU` Step (3), "Amplitude"): `vρ_∞(ξ_* + r; 3/4) ≤ C_v r^{5/4}`
for `0 < r ≤ 1`. -/
theorem nearTip_ratio : ∃ C_v : ℝ, 0 < C_v ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
    vRhoInfty (xiStar + r) (3 / 4) ≤ C_v * r ^ (5 / 4 : ℝ) := by
  have hpi := Real.pi_pos
  have hK7 := tipK7_pos
  have hK3 := tipK3_pos
  refine ⟨1 / 2 * tipK7 ^ (1 / 4 : ℝ) * tipK3 * (π / 2) ^ (3 / 2 : ℝ), by positivity, ?_⟩
  intro r hr0 hr1
  have hsad := saddle_factor_bound hr0 hr1
  obtain ⟨hT0, hT⟩ := tip_factor_bound hr0
  obtain ⟨hc0, hc⟩ := coth_factor_bound hr0 hr1
  set A : ℝ := √(vZeroK8 (xiStar + r) ^ 2 + 1 / 4) /
    ((xiStar + r) * edgeDerivK8 (xiStar + r)) with hA
  have hA0 : 0 ≤ A := by
    have hx0 : 0 < xiStar + r := by have := xiStar_pos; linarith
    have hu0 : 0 ≤ edgeDerivK8 (xiStar + r) := Real.sqrt_nonneg _
    positivity
  have hAh : 0 ≤ A ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA0 _
  have hr14 : 0 < r ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hrr : r ^ (3 / 2 : ℝ) = r ^ (1 / 4 : ℝ) * r ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_add hr0]; norm_num
  have hT0' : 0 ≤ tanhTipK8 (xiStar + r) ^ (2 * (3 / 4 : ℝ)) := Real.rpow_nonneg hT0 _
  unfold vRhoInfty
  calc (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) *
        (Real.cosh (π * (xiStar + r) / 2) / Real.sinh (π * (xiStar + r) / 2)) *
        tanhTipK8 (xiStar + r) ^ (2 * (3 / 4 : ℝ))
      ≤ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) * tipK3 * ((π / 2) ^ (3 / 2 : ℝ) * r ^ (3 / 2 : ℝ)) := by
        apply mul_le_mul _ hT hT0' (by positivity)
        exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (1 / 2 : ℝ) * (A ^ (1 / 2 : ℝ) * r ^ (1 / 4 : ℝ)) * tipK3 * (π / 2) ^ (3 / 2 : ℝ) *
        r ^ (5 / 4 : ℝ) := by rw [hrr]; ring
    _ ≤ (1 / 2 : ℝ) * tipK7 ^ (1 / 4 : ℝ) * tipK3 * (π / 2) ^ (3 / 2 : ℝ) * r ^ (5 / 4 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0.le _)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hK3.le
        exact mul_le_mul_of_nonneg_left hsad (by norm_num)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.nearTip_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Ramped.nearTip_ratio

end FormalResearch.ModularBootstrap.Upper.Ramped
