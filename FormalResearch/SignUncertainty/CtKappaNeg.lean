module

public import FormalResearch.SignUncertainty.CtOuterTheta1
public import FormalResearch.SignUncertainty.CtOuterSinhIneq
public import FormalResearch.SignUncertainty.CtLowerDefs

/-!
# `κ_± < 0`: `I₀ < 3 log 2` (F1, `ct:theta1`)

`constant_terms_lower.tex`, `ct:theta1`: `θ₁^- = -3 log 2 + I₀`, `θ₁^+ = θ₁^- - π`, `κ_ε = θ₁^ε/π²`.  **Proved.**  The TeX
gives `I₀ ≈ 0.243`, far below `3 log 2 ≈ 2.079`; here `I₀ ≤ π/2` suffices:

* `sinh_sub_le_cube_cosh`: `sinh y - y ≤ (y³/6) cosh y` (twice-integrated `x cosh x - sinh x ≥ 0`), so that
  `6(sinh y - y)/y³ ≤ cosh y` and `log(6(sinh y - y)/y³) ≤ log cosh y`;
* `integral_logCosh_mul`: `∫_0^∞ log cosh y · cosh y/sinh² y dy = π/2`, with the antiderivative
  `-log cosh y/sinh y + arctan (sinh y)` (`logCoshPrim`);
* `ctI0_le : I₀ ≤ π/2`, and **`ctKappa_neg`**: `κ_ε < 0` for `ε = ±1`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

/-- `sinh y - y ≤ (y³/6) cosh y` for `y ≥ 0`. -/
lemma sinh_sub_le_cube_cosh {y : ℝ} (hy : 0 ≤ y) : Real.sinh y - y ≤ y ^ 3 / 6 * Real.cosh y := by
  set g1 : ℝ → ℝ := fun x => x ^ 2 / 2 * Real.cosh x + x ^ 3 / 6 * Real.sinh x - Real.cosh x + 1 with hg1
  have hd1 : ∀ x, HasDerivAt g1
      ((x * Real.cosh x - Real.sinh x) + x ^ 2 * Real.sinh x + x ^ 3 / 6 * Real.cosh x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      simpa using ((hasDerivAt_pow 2 x).div_const 2)
    have h2 : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (x ^ 2 / 2) x := by
      have := (hasDerivAt_pow 3 x).div_const 6
      refine this.congr_deriv ?_
      simp; ring
    have h3 := ((h1.mul (Real.hasDerivAt_cosh x)).add (h2.mul (Real.hasDerivAt_sinh x))).sub
      (Real.hasDerivAt_cosh x) |>.add_const 1
    exact h3.congr_deriv (by ring)
  have hmono1 : MonotoneOn g1 (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd1 s).continuousAt).continuousOn
    · intro s _; exact (hd1 s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd1 s).deriv]
      have hs0 : 0 < s := hs
      have h1 := sinh_lt_mul_cosh hs0
      have := Real.sinh_pos_iff.mpr hs0
      have := Real.cosh_pos s
      have : 0 ≤ s ^ 2 * Real.sinh s := by positivity
      have : 0 ≤ s ^ 3 / 6 * Real.cosh s := by positivity
      linarith
  have hg1_0 : g1 0 = 0 := by simp [hg1]
  have hg1_nn : ∀ x, 0 ≤ x → 0 ≤ g1 x := fun x hx => by
    have := hmono1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
    rw [hg1_0] at this; exact this
  set g : ℝ → ℝ := fun x => x ^ 3 / 6 * Real.cosh x - Real.sinh x + x with hg
  have hd : ∀ x, HasDerivAt g (g1 x) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => x ^ 3 / 6) (x ^ 2 / 2) x := by
      have := (hasDerivAt_pow 3 x).div_const 6
      refine this.congr_deriv ?_
      simp; ring
    have h3 := ((h2.mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x)).add (hasDerivAt_id x)
    refine h3.congr_deriv ?_
    simp only [hg1]
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt).continuousOn
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact hg1_nn s (le_of_lt hs)
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy
  simp [hg] at this
  linarith

/-- the antiderivative `F(y) = -log cosh y / sinh y + arctan (sinh y)` of `log cosh y · cosh y / sinh² y`. -/
noncomputable def logCoshPrim (y : ℝ) : ℝ := -(Real.log (Real.cosh y) / Real.sinh y) + Real.arctan (Real.sinh y)

lemma hasDerivAt_logCoshPrim {y : ℝ} (hy : 0 < y) :
    HasDerivAt logCoshPrim (Real.log (Real.cosh y) * (Real.cosh y / Real.sinh y ^ 2)) y := by
  have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  have hc := Real.cosh_pos y
  have h1 : HasDerivAt (fun x => Real.log (Real.cosh x)) (Real.sinh y / Real.cosh y) y :=
    (Real.hasDerivAt_cosh y).log hc.ne'
  have h2 := (h1.div (Real.hasDerivAt_sinh y) hs.ne').neg
  have h3 := (Real.hasDerivAt_sinh y).arctan
  have h4 := h2.add h3
  refine h4.congr_deriv ?_
  have hcs : Real.cosh y ^ 2 = 1 + Real.sinh y ^ 2 := by nlinarith [Real.cosh_sq y]
  field_simp
  rw [← hcs]
  ring

lemma logCosh_div_sinh_bounds {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ Real.log (Real.cosh y) / Real.sinh y ∧ Real.log (Real.cosh y) / Real.sinh y ≤ y / 2 := by
  rcases hy.eq_or_lt with rfl | hy
  · simp
  have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  have hc1 : 1 ≤ Real.cosh y := Real.one_le_cosh y
  have hl0 : 0 ≤ Real.log (Real.cosh y) := Real.log_nonneg hc1
  have hl : Real.log (Real.cosh y) ≤ y ^ 2 / 2 := by
    have := Real.log_le_log (Real.cosh_pos y) (Real.cosh_le_exp_half_sq y)
    rwa [Real.log_exp] at this
  refine ⟨div_nonneg hl0 hs.le, ?_⟩
  rw [div_le_iff₀ hs]
  have := sinh_gt_self hy
  nlinarith

lemma tendsto_logCoshPrim_zero : Tendsto logCoshPrim (𝓝[Ici 0] 0) (𝓝 0) := by
  have hB : Tendsto (fun y : ℝ => Real.arctan (Real.sinh y)) (𝓝[Ici 0] 0) (𝓝 0) := by
    have : Continuous fun y : ℝ => Real.arctan (Real.sinh y) := Real.continuous_arctan.comp Real.continuous_sinh
    have h := this.tendsto 0
    simp only [Real.sinh_zero, Real.arctan_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hy2 : Tendsto (fun y : ℝ => y / 2) (𝓝[Ici 0] 0) (𝓝 0) := by
    have := (continuous_id.div_const (2 : ℝ)).tendsto (0 : ℝ)
    simp only [id, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun y : ℝ => Real.log (Real.cosh y) / Real.sinh y) (𝓝[Ici 0] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hy2 ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with y hy using (logCosh_div_sinh_bounds hy).1
    · filter_upwards [self_mem_nhdsWithin] with y hy using (logCosh_div_sinh_bounds hy).2
  have h := hB.sub hA
  rw [sub_zero] at h
  exact h.congr (fun y => by simp [logCoshPrim]; ring)

lemma tendsto_logCoshPrim_top : Tendsto logCoshPrim atTop (𝓝 (π / 2)) := by
  have hB : Tendsto (fun y : ℝ => Real.arctan (Real.sinh y)) atTop (𝓝 (π / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp (tendsto_atTop_mono' atTop
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy using (sinh_gt_self hy).le) tendsto_id)
  have hy : Tendsto (fun y : ℝ => 3 * (y ^ 1 * Real.exp (-y))) atTop (𝓝 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) 1 one_pos).const_mul 3
    simpa using this
  have hA : Tendsto (fun y : ℝ => Real.log (Real.cosh y) / Real.sinh y) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hy ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy using (logCosh_div_sinh_bounds (by linarith)).1
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy1
      have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr (by linarith)
      have h3 := exp_div_three_le_sinh hy1
      have hl : Real.log (Real.cosh y) ≤ y := by
        have hce : Real.cosh y ≤ Real.exp y := by
          rw [Real.cosh_eq]
          have : Real.exp (-y) ≤ Real.exp y := Real.exp_le_exp.2 (by linarith)
          linarith
        have := Real.log_le_log (Real.cosh_pos y) hce
        rwa [Real.log_exp] at this
      rw [div_le_iff₀ hs]
      have he : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
      have : 3 * (y ^ 1 * Real.exp (-y)) * Real.sinh y ≥ 3 * (y ^ 1 * Real.exp (-y)) * (Real.exp y / 3) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have e2 : 3 * (y ^ 1 * Real.exp (-y)) * (Real.exp y / 3) = y := by
        calc 3 * (y ^ 1 * Real.exp (-y)) * (Real.exp y / 3) = y * (Real.exp (-y) * Real.exp y) := by ring
          _ = y := by rw [he, mul_one]
      linarith
  have h := hB.sub hA
  rw [sub_zero] at h
  exact h.congr (fun y => by simp [logCoshPrim]; ring)

lemma integral_logCosh_mul : ∫ y in Ioi (0 : ℝ), Real.log (Real.cosh y) * (Real.cosh y / Real.sinh y ^ 2) = π / 2 ∧
    IntegrableOn (fun y : ℝ => Real.log (Real.cosh y) * (Real.cosh y / Real.sinh y ^ 2)) (Ioi 0) := by
  have hcont : ContinuousWithinAt logCoshPrim (Ici 0) 0 := by
    have h := tendsto_logCoshPrim_zero
    have h0 : logCoshPrim 0 = 0 := by simp [logCoshPrim]
    rw [ContinuousWithinAt, h0]; exact h
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ Real.log (Real.cosh x) * (Real.cosh x / Real.sinh x ^ 2) := by
    intro x _
    have := Real.log_nonneg (Real.one_le_cosh x)
    have := Real.cosh_pos x
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont (fun x hx => hasDerivAt_logCoshPrim hx) hnn
    tendsto_logCoshPrim_top
  refine ⟨?_, hint⟩
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun x hx => hasDerivAt_logCoshPrim hx) hint
    tendsto_logCoshPrim_top
  rw [this]
  simp [logCoshPrim]

/-- **`I_0 ≤ π/2`** (`ct:theta1`): from `6(sinh y - y)/y³ ≤ cosh y` and `∫_0^∞ log cosh y · cosh y/sinh² y dy = π/2`. -/
theorem ctI0_le : ctI0 ≤ π / 2 := by
  obtain ⟨hval, hint⟩ := integral_logCosh_mul
  have hI1 := integrable_ctLogRatio_mul
  have hI2 := integrable_ctU3_mul
  have hI3 := integrable_ctNu
  have hla : IntegrableOn (fun y : ℝ => Real.log (6 * (Real.sinh y - y) / y ^ 3) * (Real.cosh y / Real.sinh y ^ 2)) (Ioi 0) := by
    refine ((hI3.sub hI1).add hI2).congr_fun (fun y hy => ?_) measurableSet_Ioi
    have := ctNu_eq (show 0 < y from hy)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [this]; ring
  unfold ctI0
  rw [← hval]
  refine setIntegral_mono_on hla hint measurableSet_Ioi (fun y hy => ?_)
  have hy0 : 0 < y := hy
  have hw : 0 ≤ Real.cosh y / Real.sinh y ^ 2 := by
    have := Real.cosh_pos y; positivity
  refine mul_le_mul_of_nonneg_right ?_ hw
  have h1 := sinh_gt_self hy0
  have h2 := sinh_sub_le_cube_cosh hy0.le
  have hpos : 0 < 6 * (Real.sinh y - y) / y ^ 3 := by
    have : 0 < Real.sinh y - y := by linarith
    positivity
  apply Real.log_le_log hpos
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ctI0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctI0_le

end FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-- **`κ_ε < 0` for `ε = ±1`** (`ct:theta1`; the TeX uses it for `ψ₀^ε < 0`): `θ₁^ε ≤ -3 log 2 + π/2 < 0`. -/
theorem ctKappa_neg {ε : ℝ} (_hε : ε = 1 ∨ ε = -1) : ctKappa ε < 0 := by
  have h := CtOuter.ctI0_le
  have hl := Real.log_two_gt_d9
  have hp := Real.pi_lt_d2
  have h1 : CtOuter.ctTheta1 ε < 0 := by
    unfold CtOuter.ctTheta1
    split_ifs <;> linarith [Real.pi_pos]
  unfold ctKappa
  exact div_neg_of_neg_of_pos h1 (by positivity)

/-- info: 'FormalResearch.SignUncertainty.ctKappa_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctKappa_neg

end FormalResearch.SignUncertainty
