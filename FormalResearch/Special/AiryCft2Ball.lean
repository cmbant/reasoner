module

public import FormalResearch.Special.AiryCft2Generic

/-!
# Theorem D for `f` holomorphic only near the closed disc

`AIRY_POISSON.md` Theorem D is stated for `f` holomorphic on a neighbourhood of the closed disc `|u| ≤ r` (`REMAINDER.md`
Theorem L\* applies it to a function holomorphic only on a disc); `AiryCftDefect.airy_defect_bound` and
`AiryCft2Generic.cft2_defect_bound` need `f` entire.  This file removes that hypothesis (generic complex analysis, no Airy
function): for `N`, `M` entire, `CftCircleData N c s R` (simple zeros `c_i`, `i ∈ s`, of `N` in the disc) and `f` holomorphic on the
open disc `|w| < R'`, `R < R'`:

* `cft2_factor_on`: division of a function holomorphic on an open set `U` by `Π(w - c_i)` when it vanishes at the `c_i ∈ U` (the entire
  case is `cftCircle_factor`; proof by `dslope`, `differentiableOn_dslope`);
* `cft2_residue_ball`: `∮_{|w|=R} H/N = 2πi Σ_{i∈s} H(c_i)/N'(c_i)` for `H` holomorphic on `|w| < R'`;
* `cft2_defect_ball`: `‖-π Σ_{i∈s} f(c_i) M(c_i)/N'(c_i) - ∫_{-R}^{R} f‖ ≤ π R B` if `‖f (M/N - i)‖ ≤ B` on the upper and
  `‖f (M/N + i)‖ ≤ B` on the lower half circle (primitive of `f` on the disc: `DifferentiableOn.isExactOn_ball`, Mathlib);
* `airy_defect_ball`: the case `N = Ai`, `M = Bi` (**Theorem D** of `AIRY_POISSON.md` §2 as stated there):
  `‖Σ_{n ≤ N} f(a_n)/Ai'(a_n)² - ∫_{-R}^{R} f‖ ≤ π R B` for `f` holomorphic on `|w| < R'` (any `R' > R`);
* `airyNC_defect_ball` (in `AiryCft2ComboQuadrature`'s setting) is not repeated: use `cft2_defect_ball` with
  `cft2_circleData_of_finset`.

Proved (axiom-checked).  Not formalised: `f` holomorphic on a neighbourhood that is not a disc (not needed: a neighbourhood of
the closed disc contains a larger open disc), the identity with the arc integrals `A_±` as separate statements (intermediate step).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.Special

/-- Division by simple zeros for functions holomorphic on an open set. -/
lemma cft2_factor_on {U : Set ℂ} (hU : IsOpen U) (c : ℕ → ℂ) (s : Finset ℕ) (hinj : Set.InjOn c s)
    (hcU : ∀ i ∈ s, c i ∈ U) :
    ∀ (H : ℂ → ℂ), DifferentiableOn ℂ H U → (∀ i ∈ s, H (c i) = 0) →
      ∃ K : ℂ → ℂ, DifferentiableOn ℂ K U ∧ ∀ w ∈ U, H w = (∏ i ∈ s, (w - c i)) * K w := by
  classical
  induction s using Finset.induction_on with
  | empty => intro H hH _; exact ⟨H, hH, fun w _ => by simp⟩
  | insert j s hj ih =>
    intro H hH hz
    have hinj' : Set.InjOn c s := hinj.mono (by intro x hx; simp [hx])
    obtain ⟨K, hK, hKe⟩ := ih hinj' (fun i hi => hcU i (Finset.mem_insert_of_mem hi)) H hH
      (fun i hi => hz i (Finset.mem_insert_of_mem hi))
    have hcj : c j ∈ U := hcU j (Finset.mem_insert_self j s)
    have hKj : K (c j) = 0 := by
      have h1 := hz j (Finset.mem_insert_self j s)
      rw [hKe (c j) hcj] at h1
      have hne : ∏ i ∈ s, (c j - c i) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi h
        have := hinj (by simp) (by simp [hi]) (sub_eq_zero.mp h)
        exact hj (this ▸ hi)
      exact (mul_eq_zero.mp h1).resolve_left hne
    have hd : DifferentiableOn ℂ (dslope K (c j)) U :=
      (differentiableOn_dslope (hU.mem_nhds hcj)).mpr hK
    refine ⟨dslope K (c j), hd, fun w hw => ?_⟩
    have h2 := sub_smul_dslope K (c j) w
    rw [hKj, sub_zero, smul_eq_mul] at h2
    rw [Finset.prod_insert hj, hKe w hw, ← h2]
    ring

section residue

variable {f : ℂ → ℂ} {c : ℕ → ℂ} {s : Finset ℕ} {R : ℝ}

/-- **Residue formula on a circle for `H` holomorphic on a larger open disc.** -/
theorem cft2_residue_ball (h : CftCircleData f c s R) {R' : ℝ} (hR' : R < R') {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball 0 R')) :
    ∮ w in C(0, R), H w / f w = 2 * π * I * ∑ i ∈ s, H (c i) / deriv f (c i) := by
  classical
  obtain ⟨φ, hφ, hfe, hφne⟩ := h.factor
  have hR := h.radius_pos
  have hU : IsOpen (ball (0 : ℂ) R') := isOpen_ball
  set r : ℕ → ℂ := fun i => H (c i) / deriv f (c i) with hr
  set P : ℕ → ℂ → ℂ := fun i w => ∏ j ∈ s.erase i, (w - c j) with hP
  set G : ℂ → ℂ := fun w => H w - φ w * ∑ i ∈ s, r i * P i w with hG
  have hPd : ∀ i, Differentiable ℂ (P i) := fun i => by rw [hP]; fun_prop
  have hGd : DifferentiableOn ℂ G (ball 0 R') := by
    refine hH.sub ((hφ.differentiableOn).mul ?_)
    exact (Differentiable.fun_sum fun i _ => (differentiable_const _).mul (hPd i)).differentiableOn
  have hGz : ∀ j ∈ s, G (c j) = 0 := by
    intro j hj
    have hsum : ∑ i ∈ s, r i * P i (c j) = r j * P j (c j) := by
      refine Finset.sum_eq_single j (fun i hi hij => ?_) (fun hj' => absurd hj hj')
      have : P i (c j) = 0 := by
        rw [hP]; exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun e => hij e.symm, hj⟩) (sub_self _)
      rw [this, mul_zero]
    have hd := cftRes_deriv_eq hφ hfe hj
    have hdj := h.simple j hj
    rw [hG]; simp only
    rw [hsum]
    have : φ (c j) * (r j * P j (c j)) = H (c j) := by
      rw [hr]; simp only; rw [hP]; simp only
      rw [hd]
      have hne : φ (c j) * ∏ k ∈ s.erase j, (c j - c k) ≠ 0 := by rw [← hd]; exact hdj
      obtain ⟨hn1, hn2⟩ := mul_ne_zero_iff.mp hne
      field_simp
    rw [this, sub_self]
  have hcU : ∀ i ∈ s, c i ∈ ball (0 : ℂ) R' := fun i hi => by
    have := h.inside i hi
    rw [mem_ball_zero_iff]; linarith
  obtain ⟨K, hK, hKe⟩ := cft2_factor_on hU c s h.inj hcU G hGd hGz
  have hsph_sub : sphere (0 : ℂ) R ⊆ ball 0 R' := fun w hw => by
    rw [mem_sphere_zero_iff_norm] at hw
    rw [mem_ball_zero_iff]; linarith
  -- the identity on the circle
  have hsph : ∀ w ∈ sphere (0 : ℂ) R, H w / f w = K w / φ w + ∑ i ∈ s, r i * (w - c i)⁻¹ := by
    intro w hw
    have hn : ‖w‖ = R := by simpa using hw
    have hfw := h.ne_zero_sphere hn
    have hpw : (∏ i ∈ s, (w - c i)) ≠ 0 := by
      intro h0; apply hfw; rw [hfe, h0, zero_mul]
    have hφw : φ w ≠ 0 := by
      intro h0; apply hfw; rw [hfe, h0, mul_zero]
    have hHw : H w = (∏ i ∈ s, (w - c i)) * K w + φ w * ∑ i ∈ s, r i * P i w := by
      have := hKe w (hsph_sub hw); rw [hG] at this; simp only at this; linear_combination this
    have hPi : ∀ i ∈ s, P i w = (∏ j ∈ s, (w - c j)) * (w - c i)⁻¹ := by
      intro i hi
      have hwi : w - c i ≠ 0 := fun h0 => hpw (Finset.prod_eq_zero hi h0)
      rw [hP]; simp only
      rw [← Finset.mul_prod_erase s (fun j => w - c j) hi]
      field_simp
    rw [hfe w, hHw]
    have : ∑ i ∈ s, r i * P i w = (∏ j ∈ s, (w - c j)) * ∑ i ∈ s, r i * (w - c i)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hPi i hi]; ring
    rw [this]
    field_simp
  have hKφ : DifferentiableOn ℂ (fun w => K w / φ w) (closedBall 0 R) := fun x hx =>
    (((hK.differentiableAt (hU.mem_nhds (by
        rw [mem_ball_zero_iff]; have := mem_closedBall_zero_iff.mp hx; linarith))).div (hφ x)
      (hφne x (by simpa using hx))).differentiableWithinAt)
  have hint1 : CircleIntegrable (fun w => K w / φ w) 0 R :=
    ContinuousOn.circleIntegrable hR.le (hKφ.continuousOn.mono sphere_subset_closedBall)
  have hint2 : ∀ i ∈ s, CircleIntegrable (fun w => r i * (w - c i)⁻¹) 0 R := by
    intro i hi
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => ?_)
    have hn : ‖ζ‖ = R := by simpa using hζ
    intro h0; have : ζ = c i := sub_eq_zero.mp h0
    have := h.inside i hi
    rw [← ‹ζ = c i›, hn] at this; exact lt_irrefl _ this
  obtain ⟨hint3, hsum⟩ := cftRes_integral_finset_sum s (fun i w => r i * (w - c i)⁻¹) hint2
  rw [circleIntegral.integral_congr hR.le hsph, circleIntegral.integral_add hint1 hint3,
    DiffContOnCl.circleIntegral_eq_zero hR.le (hKφ.mono closure_ball_subset_closedBall |>.diffContOnCl), zero_add,
    hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball (by simpa using h.inside i hi)]
  rw [hr]; ring

end residue

lemma cft2_mem_ball {R R' : ℝ} (hR : 0 < R) (hRR : R < R') (θ : ℝ) : circleMap 0 R θ ∈ ball (0 : ℂ) R' := by
  rw [mem_ball_zero_iff, norm_circleMap_zero, abs_of_pos hR]; exact hRR

/-- Arc integral of `f dw` against a primitive on the disc. -/
lemma cft2_arc_ball {F f : ℂ → ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R')
    (hF : ∀ z ∈ ball (0 : ℂ) R', HasDerivAt F (f z) z) (hf : DifferentiableOn ℂ f (ball 0 R')) (a b : ℝ) :
    ∫ θ in a..b, (circleMap 0 R θ * I) * f (circleMap 0 R θ) =
      F (circleMap 0 R b) - F (circleMap 0 R a) := by
  refine integral_eq_sub_of_hasDerivAt (f := fun θ : ℝ => F (circleMap 0 R θ))
    (f' := fun θ : ℝ => (circleMap 0 R θ * I) * f (circleMap 0 R θ)) (fun θ _ => ?_) ?_
  · have := (hF _ (cft2_mem_ball hR hRR θ)).scomp θ (hasDerivAt_circleMap 0 R θ)
    rw [smul_eq_mul] at this
    exact this
  · refine Continuous.intervalIntegrable ?_ _ _
    have hc : Continuous (circleMap 0 R) := continuous_circleMap 0 R
    have hfc : Continuous (fun θ : ℝ => f (circleMap 0 R θ)) :=
      hf.continuousOn.comp_continuous hc (fun θ => cft2_mem_ball hR hRR θ)
    exact (hc.mul continuous_const).mul hfc

lemma cft2_diam_ball {F f : ℂ → ℂ} {R R' : ℝ} (hR : 0 < R) (hRR : R < R')
    (hF : ∀ z ∈ ball (0 : ℂ) R', HasDerivAt F (f z) z) (hf : DifferentiableOn ℂ f (ball 0 R')) :
    ∫ x in (-R)..R, f (x : ℂ) = F (R : ℂ) - F ((-R : ℝ) : ℂ) := by
  have hmem : ∀ x ∈ Set.uIcc (-R) R, (x : ℂ) ∈ ball (0 : ℂ) R' := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    have := abs_le.mpr ⟨hx.1, hx.2⟩
    linarith
  refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x : ℂ)) (f' := fun x : ℝ => f (x : ℂ))
    (fun x hx => (hF (x : ℂ) (hmem x hx)).comp_ofReal) ?_
  have hc : ContinuousOn (fun x : ℝ => f (x : ℂ)) (Set.uIcc (-R) R) :=
    hf.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun x hx => hmem x hx)
  exact hc.intervalIntegrable

/-- **Residue-defect bound for `f` holomorphic on a larger open disc.** `CftCircleData N c s R`, `M` entire,
`f` holomorphic on `|w| < R'`, `R < R'`; if `‖f (M/N - i)‖ ≤ B` on the upper half circle and `‖f (M/N + i)‖ ≤ B` on the lower one,
then `‖-π Σ_{i∈s} f(c_i) M(c_i)/N'(c_i) - ∫_{-R}^{R} f‖ ≤ π R B`. -/
theorem cft2_defect_ball {N M f : ℂ → ℂ} {c : ℕ → ℂ} {s : Finset ℕ} {R R' : ℝ}
    (hD : CftCircleData N c s R) (hM : Differentiable ℂ M) (hRR : R < R')
    (hf : DifferentiableOn ℂ f (ball 0 R')) {B : ℝ}
    (hp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im → ‖f w * (M w / N w - I)‖ ≤ B)
    (hm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 → ‖f w * (M w / N w + I)‖ ≤ B) :
    ‖(-(π : ℂ)) * (∑ i ∈ s, f (c i) * M (c i) / deriv N (c i)) - ∫ x in (-R)..R, f (x : ℂ)‖ ≤ π * R * B := by
  have hR := hD.radius_pos
  have hN := hD.entire
  obtain ⟨F, hF0, hF⟩ := hf.isExactOn_ball.with_val_at 0 0
  have hF' : ∀ z ∈ ball (0 : ℂ) R', HasDerivAt F (f z) z := fun z hz => hF z hz
  set w : ℝ → ℂ := circleMap 0 R with hw
  have hwn : ∀ θ, ‖w θ‖ = R := fun θ => by
    rw [hw, norm_circleMap_zero, abs_of_pos hR]
  have hNw : ∀ θ, N (w θ) ≠ 0 := fun θ => hD.ne_zero_sphere (hwn θ)
  have hwc : Continuous w := continuous_circleMap 0 R
  have hfc : Continuous (fun θ : ℝ => f (w θ)) :=
    hf.continuousOn.comp_continuous hwc (fun θ => cft2_mem_ball hR hRR θ)
  set J : ℝ → ℂ := fun θ => (w θ * I) * f (w θ) with hJ
  have hJc : Continuous J := by rw [hJ]; exact (hwc.mul continuous_const).mul hfc
  set Rp : ℝ → ℂ := fun θ => M (w θ) / N (w θ) - I with hRp
  set Rm : ℝ → ℂ := fun θ => M (w θ) / N (w θ) + I with hRm
  have hMc : Continuous (fun θ => M (w θ)) := hM.continuous.comp hwc
  have hNc : Continuous (fun θ => N (w θ)) := hN.continuous.comp hwc
  have hQc : Continuous (fun θ => M (w θ) / N (w θ)) := hMc.div hNc hNw
  have hRpc : Continuous Rp := by rw [hRp]; exact hQc.sub continuous_const
  have hRmc : Continuous Rm := by rw [hRm]; exact hQc.add continuous_const
  have hcirc : ∮ z in C(0, R), f z * M z / N z =
      ∫ θ in (0 : ℝ)..(2 * π), J θ * (M (w θ) / N (w θ)) := by
    rw [circleIntegral]
    refine integral_congr fun θ _ => ?_
    simp only [deriv_circleMap, smul_eq_mul, hJ, hw]
    ring
  have hΦc : Continuous (fun θ => J θ * (M (w θ) / N (w θ))) := hJc.mul hQc
  have hup : ∫ θ in (0 : ℝ)..π, J θ * (M (w θ) / N (w θ)) =
      (∫ θ in (0 : ℝ)..π, J θ * Rp θ) + I * (∫ θ in (0 : ℝ)..π, J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rp θ) volume 0 π := (hJc.mul hRpc).intervalIntegrable 0 π
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume 0 π := (hJc.const_mul I).intervalIntegrable 0 π
    rw [← intervalIntegral.integral_const_mul, ← integral_add h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRp]
    ring
  have hlow : ∫ θ in π..(2 * π), J θ * (M (w θ) / N (w θ)) =
      (∫ θ in π..(2 * π), J θ * Rm θ) - I * (∫ θ in π..(2 * π), J θ) := by
    have h1 : IntervalIntegrable (fun θ => J θ * Rm θ) volume π (2 * π) :=
      (hJc.mul hRmc).intervalIntegrable π (2 * π)
    have h2 : IntervalIntegrable (fun θ => I * J θ) volume π (2 * π) :=
      (hJc.const_mul I).intervalIntegrable π (2 * π)
    rw [← intervalIntegral.integral_const_mul, ← integral_sub h1 h2]
    refine integral_congr fun θ _ => ?_
    simp only [hRm]
    ring
  have hJup : ∫ θ in (0 : ℝ)..π, J θ = F (-(R : ℂ)) - F R := by
    have := cft2_arc_ball hR hRR hF' hf 0 π
    rw [cftDef_circleMap_pi, cftDef_circleMap_zero] at this
    simpa using this
  have hJlow : ∫ θ in π..(2 * π), J θ = F R - F (-(R : ℂ)) := by
    have := cft2_arc_ball hR hRR hF' hf π (2 * π)
    rw [cftDef_circleMap_pi, cftDef_circleMap_two_pi] at this
    simpa using this
  have hdiam := cft2_diam_ball hR hRR hF' hf
  have hdiam' : ∫ x in (-R)..R, f (x : ℂ) = F R - F (-(R : ℂ)) := by simpa using hdiam
  have hres : ∮ z in C(0, R), f z * M z / N z =
      2 * π * I * ∑ i ∈ s, f (c i) * M (c i) / deriv N (c i) :=
    cft2_residue_ball hD hRR (H := fun z => f z * M z) (hf.mul hM.differentiableOn)
  rw [hcirc, ← integral_add_adjacent_intervals (hΦc.intervalIntegrable 0 π)
    (hΦc.intervalIntegrable π (2 * π)), hup, hlow, hJup, hJlow] at hres
  have hA1 : ‖∫ θ in (0 : ℝ)..π, J θ * Rp θ‖ ≤ R * B * |π - 0| := by
    refine norm_integral_le_of_norm_le_const (fun θ hθ => ?_)
    rw [Set.uIoc_of_le Real.pi_pos.le] at hθ
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2
    have him : 0 ≤ (w θ).im := by rw [hw, cftDef_im_circleMap]; positivity
    have := hp (w θ) (hwn θ) him
    simp only [hJ, hRp]
    rw [norm_mul, norm_mul, norm_mul, hwn θ, Complex.norm_I, mul_one, mul_assoc, ← norm_mul]
    exact mul_le_mul_of_nonneg_left this hR.le
  have hA2 : ‖∫ θ in π..(2 * π), J θ * Rm θ‖ ≤ R * B * |2 * π - π| := by
    refine norm_integral_le_of_norm_le_const (fun θ hθ => ?_)
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    have hsin : Real.sin θ ≤ 0 := by
      have h1 := Real.sin_nonneg_of_nonneg_of_le_pi (x := θ - π) (by linarith [hθ.1]) (by linarith [hθ.2])
      rw [Real.sin_sub_pi] at h1
      linarith
    have him : (w θ).im ≤ 0 := by
      rw [hw, cftDef_im_circleMap]; nlinarith
    have := hm (w θ) (hwn θ) him
    simp only [hJ, hRm]
    rw [norm_mul, norm_mul, norm_mul, hwn θ, Complex.norm_I, mul_one, mul_assoc, ← norm_mul]
    exact mul_le_mul_of_nonneg_left this hR.le
  obtain ⟨T, hTdef⟩ : ∃ T : ℂ, T = ∑ i ∈ s, f (c i) * M (c i) / deriv N (c i) := ⟨_, rfl⟩
  obtain ⟨A1, hA1def⟩ : ∃ A : ℂ, A = ∫ θ in (0 : ℝ)..π, J θ * Rp θ := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ A : ℂ, A = ∫ θ in π..(2 * π), J θ * Rm θ := ⟨_, rfl⟩
  rw [← hTdef, ← hA1def, ← hA2def] at hres
  rw [← hA1def] at hA1
  rw [← hA2def] at hA2
  rw [← hTdef]
  have key : (-(π : ℂ)) * T - (∫ x in (-R)..R, f (x : ℂ)) = (I / 2) * (A1 + A2) := by
    rw [hdiam']
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (-(I / 2)) * hres - ((π : ℂ) * T + (F R - F (-(R : ℂ)))) * hI
  have hfin : ‖(-(π : ℂ)) * T - ∫ x in (-R)..R, f (x : ℂ)‖ ≤ π * R * B := by
    rw [key, norm_mul]
    have h2 : ‖I / 2‖ = 1 / 2 := by simp
    rw [h2]
    have h3 : ‖A1 + A2‖ ≤ 2 * (π * R * B) := by
      have := norm_add_le A1 A2
      rw [abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < π - 0)] at hA1
      rw [abs_of_pos (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * π - π)] at hA2
      nlinarith
    linarith
  exact hfin

/-- **Theorem D for `f` holomorphic on a neighbourhood of the closed disc** (`AIRY_POISSON.md` §2): for a zero-free circle
`|u| = R` enclosing the zeros `a_1, …, a_N` of `Ai` and `f` holomorphic on `|w| < R'`, `R' > R`: if `‖f R_+‖ ≤ B` on the upper and
`‖f R_-‖ ≤ B` on the lower half circle (`R_± = (Bi ∓ iAi)/Ai`), then `‖Σ_{n≤N} f(a_n)/Ai'(a_n)² - ∫_{-R}^{R} f‖ ≤ π R B`. -/
theorem airy_defect_ball {N : ℕ} {R R' : ℝ}
    (hD : CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R) (hRR : R < R')
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 R')) {B : ℝ}
    (hp : ∀ w : ℂ, ‖w‖ = R → 0 ≤ w.im →
      ‖f w * ((airyBiC w - I * airyAiC w) / airyAiC w)‖ ≤ B)
    (hm : ∀ w : ℂ, ‖w‖ = R → w.im ≤ 0 →
      ‖f w * ((airyBiC w + I * airyAiC w) / airyAiC w)‖ ≤ B) :
    ‖(∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2) -
        ∫ x in (-R)..R, f (x : ℂ)‖ ≤ π * R * B := by
  have h := cft2_defect_ball hD differentiable_airyBiC hRR hf (B := B)
    (fun w hw him => by
      have hA := hD.ne_zero_sphere hw
      have e : airyBiC w / airyAiC w - I = (airyBiC w - I * airyAiC w) / airyAiC w := by
        field_simp
      rw [e]; exact hp w hw him)
    (fun w hw him => by
      have hA := hD.ne_zero_sphere hw
      have e : airyBiC w / airyAiC w + I = (airyBiC w + I * airyAiC w) / airyAiC w := by
        field_simp
      rw [e]; exact hm w hw him)
  have hsum : (-(π : ℂ)) * (∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) * airyBiC (airyZero n : ℂ) /
      deriv airyAiC (airyZero n : ℂ)) =
      ∑ n ∈ Finset.Icc 1 N, f (airyZero n : ℂ) / (deriv airyAiC (airyZero n : ℂ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [cftDef_airyBiC_at_zero n]
    have hd := airyZero_deriv_ne_zero n
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
  rw [hsum] at h
  exact h

/-- info: 'FormalResearch.Special.cft2_residue_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cft2_residue_ball

/-- info: 'FormalResearch.Special.cft2_defect_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cft2_defect_ball

/-- info: 'FormalResearch.Special.airy_defect_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_defect_ball

end FormalResearch.Special
