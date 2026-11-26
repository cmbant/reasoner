module

public import FormalResearch.SignUncertainty.StripAdmiss
public import FormalResearch.SignUncertainty.UctSeedEdgeAsm
public import FormalResearch.CohnElkies.SeedSqrtForm
public import FormalResearch.CohnElkies.DualPhaseAndO3

/-!
# The edge traces of the floor lift symbol (`uct:admiss` (M3) for `W_pos`), square-root and far parts (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, proof of `fct:main-hankel`, Step 1 (the floor summand).  **Proved.**

Abstract analysis facts used for `StripEdge0` of a lift symbol `μ(τ) T(i s τ)` whose Airy factor has the square-root form
`T = A + y^{1/2} B` (`A, B` entire) and the imaginary-axis bounds `(e27)`:

* `sqrt_edge_near`: `P + ρ Q` with `P, Q` of class `C²` and `ρ` a square-root profile is `C²` off `0` with the `(M3)` bounds
  `|τ|^{1/2}`, `|τ|^{-1/2}`, `|τ|^{-3/2}` on `0 < |τ| ≤ 1`;
* `prod_far`: a globally `C²` factor with bounded derivatives times a `C²` factor with `(1+|τ|)^{-2}` bounds keeps them.
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

lemma exists_bound_Icc1 {f : ℝ → ℂ} (hf : Continuous f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : ℝ, |τ| ≤ 1 → ‖f τ‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨|C|, abs_nonneg _, fun τ hτ => (hC τ (abs_le.mp hτ)).trans (le_abs_self C)⟩

/-- A square-root profile: continuous, zero at `0`, `C²` off `0`, with `|ρ| ≲ |τ|^{1/2}`, `|ρ'| ≲ |τ|^{-1/2}`, `|ρ''| ≲ |τ|^{-3/2}`. -/
structure SqrtProfile (ρ : ℝ → ℂ) : Prop where
  cont : Continuous ρ
  zero : ρ 0 = 0
  contDiffOn : ContDiffOn ℝ 2 ρ {τ : ℝ | τ ≠ 0}
  bound : ∃ C : ℝ, ∀ τ : ℝ, τ ≠ 0 → ‖ρ τ‖ ≤ C * |τ| ^ (1 / 2 : ℝ) ∧ ‖deriv ρ τ‖ ≤ C * |τ| ^ ((1 / 2 : ℝ) - 1) ∧
    ‖deriv (deriv ρ) τ‖ ≤ C * |τ| ^ ((1 / 2 : ℝ) - 2)

/-- `P + ρ Q` near `0`: the `(M3)` shape. -/
theorem sqrt_edge_near {P Q ρ : ℝ → ℂ} (hP : ContDiff ℝ 2 P) (hQ : ContDiff ℝ 2 Q) (hρ : SqrtProfile ρ) :
    ContDiffOn ℝ 2 (fun τ => P τ + ρ τ * Q τ) {τ : ℝ | τ ≠ 0} ∧
    ∃ C : ℝ, ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ 1 →
      ‖(P τ + ρ τ * Q τ) - (P 0 + ρ 0 * Q 0)‖ ≤ C * |τ| ^ (1 / 2 : ℝ) ∧
      ‖deriv (fun t => P t + ρ t * Q t) τ‖ ≤ C * |τ| ^ ((1 / 2 : ℝ) - 1) ∧
      ‖deriv (deriv (fun t => P t + ρ t * Q t)) τ‖ ≤ C * |τ| ^ ((1 / 2 : ℝ) - 2) := by
  have hS : IsOpen {τ : ℝ | τ ≠ 0} := isOpen_ne
  refine ⟨hP.contDiffOn.add (hρ.contDiffOn.mul hQ.contDiffOn), ?_⟩
  obtain ⟨Cρ, hCρ⟩ := hρ.bound
  have hP1 : ContDiff ℝ 1 (deriv P) := hP.deriv'
  have hQ1 : ContDiff ℝ 1 (deriv Q) := hQ.deriv'
  obtain ⟨MP1, hMP1, bP1⟩ := exists_bound_Icc1 hP1.continuous
  obtain ⟨MP2, hMP2, bP2⟩ := exists_bound_Icc1 hP1.continuous_deriv_one
  obtain ⟨MQ, hMQ, bQ⟩ := exists_bound_Icc1 hQ.continuous
  obtain ⟨MQ1, hMQ1, bQ1⟩ := exists_bound_Icc1 hQ1.continuous
  obtain ⟨MQ2, hMQ2, bQ2⟩ := exists_bound_Icc1 hQ1.continuous_deriv_one
  have hCρ0 : 0 ≤ Cρ := by
    have := (hCρ 1 one_ne_zero).1
    simp only [abs_one, Real.one_rpow, mul_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨MP1 + MP2 + 4 * Cρ * (MQ + MQ1 + MQ2) + 1, fun τ hτ hτ1 => ?_⟩
  have hy : 0 < |τ| := abs_pos.mpr hτ
  have h1 := one_le_rpow_neg_half hy hτ1
  have h2 := one_le_rpow_neg_three_half hy hτ1
  have h12 := rpow_neg_half_le_neg_three_half hy hτ1
  have hhalf := rpow_half_le_of_le_one hy.le hτ1
  have hh1 : |τ| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hy.le hτ1 (by norm_num)
  have hPd : Differentiable ℝ P := hP.differentiable (by norm_num)
  have hQd : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have hPd1 : Differentiable ℝ (deriv P) := hP1.differentiable (by norm_num)
  have hQd1 : Differentiable ℝ (deriv Q) := hQ1.differentiable (by norm_num)
  have hρ1 : ContDiffOn ℝ 1 (deriv ρ) {τ : ℝ | τ ≠ 0} := hρ.contDiffOn.deriv_of_isOpen hS (by norm_num)
  have hρd : ∀ x : ℝ, x ≠ 0 → DifferentiableAt ℝ ρ x := fun x hx =>
    (hρ.contDiffOn.differentiableOn (by norm_num) x hx).differentiableAt (hS.mem_nhds hx)
  have hρd1 : ∀ x : ℝ, x ≠ 0 → DifferentiableAt ℝ (deriv ρ) x := fun x hx =>
    (hρ1.differentiableOn (by norm_num) x hx).differentiableAt (hS.mem_nhds hx)
  have hform : ∀ x : ℝ, x ≠ 0 → HasDerivAt (fun t => P t + ρ t * Q t)
      (deriv P x + (deriv ρ x * Q x + ρ x * deriv Q x)) x := fun x hx =>
    (hPd x).hasDerivAt.add ((hρd x hx).hasDerivAt.mul (hQd x).hasDerivAt)
  have hev : deriv (fun t => P t + ρ t * Q t) =ᶠ[𝓝 τ] fun x => deriv P x + (deriv ρ x * Q x + ρ x * deriv Q x) := by
    filter_upwards [hS.mem_nhds hτ] with x hx using (hform x hx).deriv
  have hd2 : deriv (deriv (fun t => P t + ρ t * Q t)) τ =
      deriv (deriv P) τ + ((deriv (deriv ρ) τ * Q τ + deriv ρ τ * deriv Q τ) +
        (deriv ρ τ * deriv Q τ + ρ τ * deriv (deriv Q) τ)) := by
    rw [hev.deriv_eq]
    exact ((hPd1 τ).hasDerivAt.add (((hρd1 τ hτ).hasDerivAt.mul (hQd τ).hasDerivAt).add
      ((hρd τ hτ).hasDerivAt.mul (hQd1 τ).hasDerivAt))).deriv
  obtain ⟨r0, r1, r2⟩ := hCρ τ hτ
  have e0 := bQ τ hτ1
  have e1 := bQ1 τ hτ1
  have e2 := bQ2 τ hτ1
  have p1 := bP1 τ hτ1
  have p2 := bP2 τ hτ1
  have hpos : 0 ≤ (MP1 + MP2 + 4 * Cρ * (MQ + MQ1 + MQ2) + 1) := by positivity
  have hLip : ‖P τ - P 0‖ ≤ MP1 * |τ| := by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := P) (C := MP1) (s := Set.Icc (-1 : ℝ) 1) (x := 0) (y := τ)
      (fun x _ => hPd x) (fun x hx => bP1 x (abs_le.mpr hx)) (convex_Icc _ _) (by simp)
      (by simpa [abs_le] using hτ1)
    simpa [Real.norm_eq_abs] using this
  have hA0 : 0 ≤ |τ| ^ (1 / 2 : ℝ) := Real.rpow_nonneg hy.le _
  have hA10 : 0 ≤ |τ| ^ ((1 / 2 : ℝ) - 1) := Real.rpow_nonneg hy.le _
  have hA20 : 0 ≤ |τ| ^ ((1 / 2 : ℝ) - 2) := Real.rpow_nonneg hy.le _
  set A := |τ| ^ (1 / 2 : ℝ) with hA
  set A1 := |τ| ^ ((1 / 2 : ℝ) - 1) with hA1
  set A2 := |τ| ^ ((1 / 2 : ℝ) - 2) with hA2
  have hCQ : 0 ≤ Cρ * MQ := mul_nonneg hCρ0 hMQ
  have hCQ1 : 0 ≤ Cρ * MQ1 := mul_nonneg hCρ0 hMQ1
  have hCQ2 : 0 ≤ Cρ * MQ2 := mul_nonneg hCρ0 hMQ2
  refine ⟨?_, ?_, ?_⟩
  · have : (P τ + ρ τ * Q τ) - (P 0 + ρ 0 * Q 0) = (P τ - P 0) + ρ τ * Q τ := by rw [hρ.zero]; ring
    rw [this]
    calc ‖(P τ - P 0) + ρ τ * Q τ‖ ≤ ‖P τ - P 0‖ + ‖ρ τ‖ * ‖Q τ‖ := (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ MP1 * A + Cρ * A * MQ := by
          gcongr
          exact hLip.trans (by gcongr)
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ MP2 + 4 * Cρ * (MQ1 + MQ2) + 3 * (Cρ * MQ) + 1) hA0]
  · have hd1 : deriv (fun t => P t + ρ t * Q t) τ = deriv P τ + (deriv ρ τ * Q τ + ρ τ * deriv Q τ) := hev.eq_of_nhds
    rw [hd1]
    have hAA1 : A ≤ A1 := hh1.trans h1
    calc ‖deriv P τ + (deriv ρ τ * Q τ + ρ τ * deriv Q τ)‖
        ≤ ‖deriv P τ‖ + (‖deriv ρ τ‖ * ‖Q τ‖ + ‖ρ τ‖ * ‖deriv Q τ‖) :=
          (norm_add_le _ _).trans (by gcongr; exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul]))
      _ ≤ MP1 + (Cρ * A1 * MQ + Cρ * A * MQ1) := by gcongr
      _ ≤ _ := by
          nlinarith [mul_nonneg hMP2 hA10, mul_nonneg hCQ hA10, mul_nonneg hCQ1 hA10, mul_nonneg hCQ2 hA10,
            mul_le_mul_of_nonneg_left h1 hMP1, mul_le_mul_of_nonneg_left hAA1 hCQ1]
  · have hd2' := hd2
    rw [hd2]
    have hAA2 : A ≤ A2 := hh1.trans h2
    have h12' : A1 ≤ A2 := h12
    calc ‖deriv (deriv P) τ + ((deriv (deriv ρ) τ * Q τ + deriv ρ τ * deriv Q τ) +
            (deriv ρ τ * deriv Q τ + ρ τ * deriv (deriv Q) τ))‖
        ≤ ‖deriv (deriv P) τ‖ + ((‖deriv (deriv ρ) τ‖ * ‖Q τ‖ + ‖deriv ρ τ‖ * ‖deriv Q τ‖) +
            (‖deriv ρ τ‖ * ‖deriv Q τ‖ + ‖ρ τ‖ * ‖deriv (deriv Q) τ‖)) := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          · exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
          · exact (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ MP2 + ((Cρ * A2 * MQ + Cρ * A1 * MQ1) + (Cρ * A1 * MQ1 + Cρ * A * MQ2)) := by gcongr
      _ ≤ _ := by
          nlinarith [mul_nonneg hMP1 hA20, mul_nonneg hCQ hA20, mul_nonneg hCQ1 hA20, mul_nonneg hCQ2 hA20,
            mul_le_mul_of_nonneg_left h2 hMP2, mul_le_mul_of_nonneg_left h12' hCQ1, mul_le_mul_of_nonneg_left hAA2 hCQ2]

/-! ### The square-root profile along a scaled imaginary line -/

/-- The point `i s τ` of the imaginary axis. -/
noncomputable def yLine (s τ : ℝ) : ℂ := ((s * τ : ℝ) : ℂ) * Complex.I

/-- `(i s τ)^{1/2}`. -/
noncomputable def sqrtLine (s τ : ℝ) : ℂ := (yLine s τ) ^ (1 / 2 : ℂ)

lemma yLine_eq (s τ : ℝ) : yLine s τ = (s : ℂ) * ((τ : ℂ) * Complex.I) := by unfold yLine; push_cast; ring

lemma yLine_re (s τ : ℝ) : (yLine s τ).re = 0 := by simp [yLine]

lemma yLine_ne {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : τ ≠ 0) : yLine s τ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [yLine] at this
  rcases this with h | h
  · exact hs.ne' h
  · exact hτ h

lemma yLine_mem_slit {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : τ ≠ 0) : yLine s τ ∈ Complex.slitPlane :=
  Or.inr (by simpa [yLine] using And.intro hs.ne' hτ)

lemma norm_yLine (s τ : ℝ) (hs : 0 < s) : ‖yLine s τ‖ = s * |τ| := by
  simp [yLine, abs_of_pos hs]

lemma hasDerivAt_yLine (s τ : ℝ) : HasDerivAt (yLine s) ((s : ℂ) * Complex.I) τ := by
  have h0 : HasDerivAt (fun z : ℂ => (s : ℂ) * (z * Complex.I)) ((s : ℂ) * Complex.I) (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).mul_const Complex.I).const_mul (s : ℂ)
  have h1 := h0.comp_ofReal
  have : yLine s = fun τ : ℝ => (s : ℂ) * ((τ : ℂ) * Complex.I) := funext (yLine_eq s)
  rw [this]; exact h1

lemma contDiff_yLine (s : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (yLine s) := by
  have : yLine s = fun τ : ℝ => (s : ℂ) * ((τ : ℂ) * Complex.I) := funext (yLine_eq s)
  rw [this]
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.mul contDiff_const)

lemma norm_yLine_cpow {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : τ ≠ 0) (p : ℝ) :
    ‖(yLine s τ) ^ (p : ℂ)‖ = (s * |τ|) ^ p := by
  rw [FormalResearch.CohnElkies.norm_cpow_ofReal_exponent (yLine_ne hs hτ), norm_yLine s τ hs]

lemma hasDerivAt_sqrtLine {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt (sqrtLine s) ((1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (yLine s τ) ^ (-(1 / 2 : ℂ))) τ := by
  have h1 : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ((1 / 2 : ℂ) * (yLine s τ) ^ ((1 / 2 : ℂ) - 1)) (yLine s τ) :=
    ((hasDerivAt_id (yLine s τ)).cpow_const (yLine_mem_slit hs hτ)).congr_deriv (by simp)
  have h2 := h1.scomp τ (hasDerivAt_yLine s τ)
  refine h2.congr_deriv ?_
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring]
  simp only [smul_eq_mul]; ring

lemma hasDerivAt_sqrtLine' {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : τ ≠ 0) :
    HasDerivAt (fun x : ℝ => (1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (yLine s x) ^ (-(1 / 2 : ℂ)))
      ((1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (-(1 / 2 : ℂ) * (yLine s τ) ^ (-(3 / 2 : ℂ)) * ((s : ℂ) * Complex.I))) τ := by
  have h1 : HasDerivAt (fun z : ℂ => z ^ (-(1 / 2 : ℂ))) (-(1 / 2 : ℂ) * (yLine s τ) ^ (-(1 / 2 : ℂ) - 1)) (yLine s τ) :=
    ((hasDerivAt_id (yLine s τ)).cpow_const (yLine_mem_slit hs hτ)).congr_deriv (by simp)
  have h2 := (h1.scomp τ (hasDerivAt_yLine s τ)).const_mul ((1 / 2 : ℂ) * ((s : ℂ) * Complex.I))
  refine h2.congr_deriv ?_
  rw [show -(1 / 2 : ℂ) - 1 = -(3 / 2 : ℂ) by ring]
  simp only [smul_eq_mul]; ring

theorem sqrtProfile_sqrtLine {s : ℝ} (hs : 0 < s) : SqrtProfile (sqrtLine s) where
  cont := by
    refine continuous_iff_continuousAt.mpr fun τ => ?_
    exact (Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by rw [yLine_re])) (by norm_num)).comp
      (contDiff_yLine s (n := 0)).continuous.continuousAt
  zero := by simp [sqrtLine, yLine]
  contDiffOn := by
    intro τ hτ
    have hτ' : τ ≠ 0 := hτ
    have h1 : ContDiffAt ℂ 2 (fun y : ℂ => y ^ (1 / 2 : ℂ)) (yLine s τ) :=
      (AnalyticAt.cpow (f := fun z : ℂ => z) (g := fun _ => (1 / 2 : ℂ)) analyticAt_id analyticAt_const
        (yLine_mem_slit hs hτ')).contDiffAt
    exact (((h1.restrict_scalars ℝ).comp τ (contDiff_yLine s).contDiffAt)).contDiffWithinAt
  bound := by
    refine ⟨s ^ (1 / 2 : ℝ), fun τ hτ => ?_⟩
    have hτ0 : 0 < |τ| := abs_pos.mpr hτ
    have hd1 : deriv (sqrtLine s) τ = (1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (yLine s τ) ^ (-(1 / 2 : ℂ)) :=
      (hasDerivAt_sqrtLine hs hτ).deriv
    have hev : deriv (sqrtLine s) =ᶠ[𝓝 τ] fun x : ℝ => (1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (yLine s x) ^ (-(1 / 2 : ℂ)) := by
      filter_upwards [isOpen_ne.mem_nhds hτ] with x hx using (hasDerivAt_sqrtLine hs hx).deriv
    have hd2 : deriv (deriv (sqrtLine s)) τ =
        (1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (-(1 / 2 : ℂ) * (yLine s τ) ^ (-(3 / 2 : ℂ)) * ((s : ℂ) * Complex.I)) := by
      rw [hev.deriv_eq]; exact (hasDerivAt_sqrtLine' hs hτ).deriv
    have e0 : ‖sqrtLine s τ‖ = s ^ (1 / 2 : ℝ) * |τ| ^ (1 / 2 : ℝ) := by
      have := norm_yLine_cpow hs hτ (1 / 2)
      unfold sqrtLine
      rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring] at this
      rw [this, Real.mul_rpow hs.le hτ0.le]
    have hs1 : s * s ^ (-(1 / 2 : ℝ)) = s ^ (1 / 2 : ℝ) := by
      calc s * s ^ (-(1 / 2 : ℝ)) = s ^ (1 : ℝ) * s ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hs]; norm_num
    have hs2 : s ^ 2 * s ^ (-(3 / 2 : ℝ)) = s ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_two, ← Real.rpow_add hs]; norm_num
    have e1 : ‖(1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (yLine s τ) ^ (-(1 / 2 : ℂ))‖ =
        (1 / 2) * s ^ (1 / 2 : ℝ) * |τ| ^ ((1 / 2 : ℝ) - 1) := by
      have := norm_yLine_cpow hs hτ (-(1 / 2))
      rw [show (((-(1 / 2) : ℝ)) : ℂ) = -(1 / 2 : ℂ) by push_cast; ring] at this
      rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
      simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
        Complex.norm_I, mul_one, this, Real.mul_rpow hs.le hτ0.le]
      rw [← hs1]; ring
    have e2 : ‖(1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (-(1 / 2 : ℂ) * (yLine s τ) ^ (-(3 / 2 : ℂ)) * ((s : ℂ) * Complex.I))‖ =
        (1 / 4) * s ^ (1 / 2 : ℝ) * |τ| ^ ((1 / 2 : ℝ) - 2) := by
      have := norm_yLine_cpow hs hτ (-(3 / 2))
      rw [show (((-(3 / 2) : ℝ)) : ℂ) = -(3 / 2 : ℂ) by push_cast; ring] at this
      rw [show (1 / 2 : ℝ) - 2 = -(3 / 2) by norm_num, ← hs2]
      have h4 : ‖(1 / 2 : ℂ) * ((s : ℂ) * Complex.I) * (-(1 / 2 : ℂ) * (yLine s τ) ^ (-(3 / 2 : ℂ)) * ((s : ℂ) * Complex.I))‖ =
          (1 / 4) * s ^ 2 * ‖(yLine s τ) ^ (-(3 / 2 : ℂ))‖ := by
        simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
          Complex.norm_I, norm_neg]
        ring
      rw [h4, this, Real.mul_rpow hs.le hτ0.le]; ring
    refine ⟨?_, ?_, ?_⟩
    · rw [e0]
    · rw [hd1, e1]; nlinarith [Real.rpow_nonneg hs.le (1 / 2 : ℝ), Real.rpow_nonneg hτ0.le ((1 / 2 : ℝ) - 1),
        mul_nonneg (Real.rpow_nonneg hs.le (1 / 2 : ℝ)) (Real.rpow_nonneg hτ0.le ((1 / 2 : ℝ) - 1))]
    · rw [hd2, e2]; nlinarith [mul_nonneg (Real.rpow_nonneg hs.le (1 / 2 : ℝ)) (Real.rpow_nonneg hτ0.le ((1 / 2 : ℝ) - 2))]

/-! ### Far parts -/

/-- A globally `C²` factor with bounded derivatives times a factor with `(1+|τ|)^{-2}` bounds, away from `0`. -/
theorem prod_far {Y V : ℝ → ℂ} (hY : ContDiff ℝ 2 Y) {CY : ℝ}
    (hCY : ∀ τ : ℝ, ‖Y τ‖ ≤ CY ∧ ‖deriv Y τ‖ ≤ CY ∧ ‖deriv (deriv Y) τ‖ ≤ CY)
    (hV : ContDiffOn ℝ 2 V {τ : ℝ | τ ≠ 0}) {CV : ℝ}
    (hVb : ∀ τ : ℝ, 1 / 2 ≤ |τ| → ‖V τ‖ ≤ CV * (1 + |τ|) ^ (-(2 : ℝ)) ∧ ‖deriv V τ‖ ≤ CV * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (deriv V) τ‖ ≤ CV * (1 + |τ|) ^ (-(2 : ℝ))) :
    ∀ τ : ℝ, 1 / 2 ≤ |τ| →
      ‖Y τ * V τ‖ ≤ 4 * CY * CV * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (fun t => Y t * V t) τ‖ ≤ 4 * CY * CV * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (deriv (fun t => Y t * V t)) τ‖ ≤ 4 * CY * CV * (1 + |τ|) ^ (-(2 : ℝ)) := by
  intro τ hτ
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h] at hτ; simp at hτ; linarith
  obtain ⟨hd1, hd2⟩ := prod_deriv isOpen_ne hY hV (show τ ∈ {τ : ℝ | τ ≠ 0} from hτ0)
  obtain ⟨y0, y1, y2⟩ := hCY τ
  obtain ⟨v0, v1, v2⟩ := hVb τ hτ
  have hP : 0 < (1 + |τ|) ^ (-(2 : ℝ)) := by positivity
  have hCY0 : 0 ≤ CY := (norm_nonneg _).trans y0
  have hCV0 : 0 ≤ CV := by
    have := (norm_nonneg _).trans v0
    exact nonneg_of_mul_nonneg_left this hP
  have a0 := norm_nonneg (Y τ)
  have a1 := norm_nonneg (deriv Y τ)
  have a2 := norm_nonneg (deriv (deriv Y) τ)
  have b0 := norm_nonneg (V τ)
  have b1 := norm_nonneg (deriv V τ)
  have b2 := norm_nonneg (deriv (deriv V) τ)
  have hPCV : 0 ≤ CV * (1 + |τ|) ^ (-(2 : ℝ)) := by positivity
  have hm0 : ‖Y τ‖ * ‖V τ‖ ≤ CY * (CV * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul y0 v0 b0 hCY0
  have hm1 : ‖deriv Y τ‖ * ‖V τ‖ ≤ CY * (CV * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul y1 v0 b0 hCY0
  have hm2 : ‖Y τ‖ * ‖deriv V τ‖ ≤ CY * (CV * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul y0 v1 b1 hCY0
  have hm3 : ‖deriv (deriv Y) τ‖ * ‖V τ‖ ≤ CY * (CV * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul y2 v0 b0 hCY0
  have hm4 : ‖deriv Y τ‖ * ‖deriv V τ‖ ≤ CY * (CV * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul y1 v1 b1 hCY0
  have hm5 : ‖Y τ‖ * ‖deriv (deriv V) τ‖ ≤ CY * (CV * (1 + |τ|) ^ (-(2 : ℝ))) := mul_le_mul y0 v2 b2 hCY0
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul]; nlinarith
  · rw [hd1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]; nlinarith
  · rw [hd2]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]; nlinarith

lemma rpow_neg_far_le {q : ℝ} (hq : 2 ≤ q) (hq' : q ≤ 9 / 2) {τ : ℝ} (hτ : 1 / 2 ≤ |τ|) :
    |τ| ^ (-q) ≤ 72 * (1 + |τ|) ^ (-(2 : ℝ)) := by
  have hx : 0 < |τ| := lt_of_lt_of_le (by norm_num) hτ
  have h1 : |τ| ^ (-q) = |τ| ^ (-(2 : ℝ)) * |τ| ^ (2 - q) := by
    rw [← Real.rpow_add hx]; ring_nf
  have h2 : |τ| ^ (2 - q) ≤ 8 := by
    have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) hτ (by linarith : 2 - q ≤ 0)
    refine this.trans ?_
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    calc (2 : ℝ) ^ (-(2 - q)) ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := by norm_num
  have h3 : |τ| ^ (-(2 : ℝ)) ≤ 9 * (1 + |τ|) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hx.le, Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.rpow_natCast]
    rw [← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [h1]
  have hp : 0 ≤ |τ| ^ (-(2 : ℝ)) := Real.rpow_nonneg hx.le _
  nlinarith [Real.rpow_nonneg hx.le (2 - q)]

/-- The imaginary-axis bounds `(e27)` along the scaled line, in the weight `(1+|τ|)^{-2}` for `|τ| ≥ 1/2`, `s > 2`. -/
theorem imag_far {T : ℂ → ℂ} (hT : FormalResearch.CohnElkies.ImagAxisBounds T) {s : ℝ} (hs : 2 < s) :
    ∃ C : ℝ, ∀ τ : ℝ, 1 / 2 ≤ |τ| →
      ‖T (yLine s τ)‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (fun x => T (yLine s x)) τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (deriv (fun x => T (yLine s x))) τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) := by
  obtain ⟨g1, g2, h1, h2, C, hC, hb⟩ := hT
  have hs0 : 0 < s := by linarith
  refine ⟨72 * C * s ^ 2, fun τ hτ => ?_⟩
  have hτ0 : 0 < |τ| := lt_of_lt_of_le (by norm_num) hτ
  have hω : ∀ x : ℝ, 1 / 2 ≤ |x| → 1 < |s * x| := fun x hx => by
    rw [abs_mul, abs_of_pos hs0]; nlinarith
  have hGd : ∀ x : ℝ, 1 < |s * x| → HasDerivAt (fun x => T (yLine s x)) (s * g1 (s * x)) x := fun x hx => by
    have := (h1 (s * x) hx).scomp x ((hasDerivAt_id x).const_mul s)
    convert this using 1
    · simp [yLine, Function.comp_def]
    · simp
  have hopen : IsOpen {x : ℝ | 1 < |s * x|} := isOpen_lt continuous_const (continuous_abs.comp (continuous_const.mul continuous_id))
  have hτU : τ ∈ {x : ℝ | 1 < |s * x|} := hω τ hτ
  have hev : deriv (fun x => T (yLine s x)) =ᶠ[𝓝 τ] fun x => s * g1 (s * x) := by
    filter_upwards [hopen.mem_nhds hτU] with x hx using (hGd x hx).deriv
  have hG2 : deriv (deriv (fun x => T (yLine s x))) τ = s * (s * g2 (s * τ)) := by
    rw [hev.deriv_eq]
    have := ((h2 (s * τ) (hω τ hτ)).scomp τ ((hasDerivAt_id τ).const_mul s)).const_mul (s : ℂ)
    simpa using this.deriv
  have hG1 : deriv (fun x => T (yLine s x)) τ = s * g1 (s * τ) := (hGd τ (hω τ hτ)).deriv
  obtain ⟨b0, b1, b2⟩ := hb (s * τ) (hω τ hτ)
  have hu : |s * τ| = s * |τ| := by rw [abs_mul, abs_of_pos hs0]
  rw [hu] at b0 b1 b2
  have hmul : ∀ q : ℝ, (s * |τ|) ^ (-q) = s ^ (-q) * |τ| ^ (-q) := fun q => Real.mul_rpow hs0.le hτ0.le
  have hs1 : 1 ≤ s := by linarith
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hsp : ∀ q : ℝ, 0 ≤ q → s ^ (-q) ≤ 1 := fun q hq => Real.rpow_le_one_of_one_le_of_nonpos hs1 (by linarith)
  have hτp : ∀ q : ℝ, 0 ≤ |τ| ^ (-q) := fun q => Real.rpow_nonneg hτ0.le _
  have hsp0 : ∀ q : ℝ, 0 ≤ s ^ (-q) := fun q => Real.rpow_nonneg hs0.le _
  have f0 := rpow_neg_far_le (q := 5 / 2) (by norm_num) (by norm_num) hτ
  have f1 := rpow_neg_far_le (q := 7 / 2) (by norm_num) (by norm_num) hτ
  have f2 := rpow_neg_far_le (q := 9 / 2) (by norm_num) (by norm_num) hτ
  have hP : 0 < (1 + |τ|) ^ (-(2 : ℝ)) := by positivity
  have hs52 : s * s ^ (-(7 / 2 : ℝ)) ≤ 1 := by
    have : s * s ^ (-(7 / 2 : ℝ)) = s ^ (-(5 / 2 : ℝ)) := by
      calc s * s ^ (-(7 / 2 : ℝ)) = s ^ (1 : ℝ) * s ^ (-(7 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hs0]; norm_num
    rw [this]; exact hsp _ (by norm_num)
  have hs52' : s * (s * s ^ (-(9 / 2 : ℝ))) ≤ 1 := by
    have : s * (s * s ^ (-(9 / 2 : ℝ))) = s ^ (-(5 / 2 : ℝ)) := by
      calc s * (s * s ^ (-(9 / 2 : ℝ))) = s ^ (2 : ℝ) * s ^ (-(9 / 2 : ℝ)) := by rw [Real.rpow_two]; ring
        _ = _ := by rw [← Real.rpow_add hs0]; norm_num
    rw [this]; exact hsp _ (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · calc ‖T (yLine s τ)‖ ≤ C * (s ^ (-(5 / 2 : ℝ)) * |τ| ^ (-(5 / 2 : ℝ))) := by
          have := b0
          rw [show -(5 / 2 : ℝ) = -(5 / 2) from rfl, hmul] at this
          exact this
      _ ≤ C * (1 * (72 * (1 + |τ|) ^ (-(2 : ℝ)))) := by
          gcongr
          · exact hsp _ (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC.le hP.le) (sub_nonneg.mpr hs2)]
  · rw [hG1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    calc s * ‖g1 (s * τ)‖ ≤ s * (C * (s ^ (-(7 / 2 : ℝ)) * |τ| ^ (-(7 / 2 : ℝ)))) := by
          gcongr
          have := b1
          rw [hmul] at this
          exact this
      _ = C * ((s * s ^ (-(7 / 2 : ℝ))) * |τ| ^ (-(7 / 2 : ℝ))) := by ring
      _ ≤ C * (1 * (72 * (1 + |τ|) ^ (-(2 : ℝ)))) := by
          gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC.le hP.le) (sub_nonneg.mpr hs2)]
  · rw [hG2, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    calc s * (s * ‖g2 (s * τ)‖) ≤ s * (s * (C * (s ^ (-(9 / 2 : ℝ)) * |τ| ^ (-(9 / 2 : ℝ))))) := by
          gcongr
          have := b2
          rw [hmul] at this
          exact this
      _ = C * ((s * (s * s ^ (-(9 / 2 : ℝ)))) * |τ| ^ (-(9 / 2 : ℝ))) := by ring
      _ ≤ C * (1 * (72 * (1 + |τ|) ^ (-(2 : ℝ)))) := by
          gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC.le hP.le) (sub_nonneg.mpr hs2)]

/-! ### The `(M3)` data of the left edge -/

/-- `StripEdge0` for an edge trace `Y(τ) T(i s τ)` with `Y` globally `C²` with bounded derivatives and `T = A + y^{1/2} B`
(`A, B` entire) obeying the imaginary-axis bounds. -/
theorem stripEdge0_of_sqrt {W : ℂ → ℂ} {Y : ℝ → ℂ} (hY : ContDiff ℝ 2 Y) {CY : ℝ}
    (hCY : ∀ τ : ℝ, ‖Y τ‖ ≤ CY ∧ ‖deriv Y τ‖ ≤ CY ∧ ‖deriv (deriv Y) τ‖ ≤ CY)
    {T A B : ℂ → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hTAB : ∀ y : ℂ, 0 ≤ y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y)
    (hT : FormalResearch.CohnElkies.ImagAxisBounds T) {s : ℝ} (hs : 2 < s)
    (hW : ∀ τ : ℝ, stripEdge0 W τ = Y τ * T (yLine s τ)) : StripEdge0 (1 / 2 : ℝ) W := by
  have hs0 : 0 < s := by linarith
  have hρ := sqrtProfile_sqrtLine hs0
  have hP : ContDiff ℝ 2 (fun τ => A (yLine s τ)) := (hA.contDiff.restrict_scalars ℝ).comp (contDiff_yLine s)
  have hQ : ContDiff ℝ 2 (fun τ => B (yLine s τ)) := (hB.contDiff.restrict_scalars ℝ).comp (contDiff_yLine s)
  have hV : ∀ τ : ℝ, T (yLine s τ) = A (yLine s τ) + sqrtLine s τ * B (yLine s τ) := fun τ =>
    hTAB _ (by rw [yLine_re])
  have hVfun : (fun τ : ℝ => T (yLine s τ)) = fun τ => A (yLine s τ) + sqrtLine s τ * B (yLine s τ) := funext hV
  have hfun : stripEdge0 W = fun τ => Y τ * A (yLine s τ) + sqrtLine s τ * (Y τ * B (yLine s τ)) := by
    funext τ; rw [hW, hV]; ring
  have hfun2 : stripEdge0 W = fun τ => Y τ * T (yLine s τ) := funext hW
  obtain ⟨hc2, C1, hC1⟩ := sqrt_edge_near (hY.mul hP) (hY.mul hQ) hρ
  have hVc : ContDiffOn ℝ 2 (fun τ => T (yLine s τ)) {τ : ℝ | τ ≠ 0} := by
    rw [hVfun]; exact hP.contDiffOn.add (hρ.contDiffOn.mul hQ.contDiffOn)
  obtain ⟨CV, hCV⟩ := imag_far hT hs
  have hfar := prod_far hY hCY hVc hCV
  refine ⟨?_, ⟨C1, fun τ hτ hτ1 => ?_⟩, ⟨4 * CY * CV, fun τ hτ => ?_⟩⟩
  · rw [hfun]; exact hc2
  · rw [hfun]; exact hC1 τ hτ hτ1
  · rw [hfun2]; exact hfar τ hτ

/-- `StripEdge0` for an edge trace that is globally `C²` with `(1+|τ|)^{-2}` bounds. -/
theorem stripEdge0_of_smooth {W : ℂ → ℂ} {α : ℝ} (hα1 : α ≤ 1) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) {C : ℝ}
    (hb : ∀ τ : ℝ, ‖g τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧ ‖deriv g τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (deriv g) τ‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)))
    (hW : stripEdge0 W = g) : StripEdge0 α W := by
  subst hW
  set g := stripEdge0 W with hgdef
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hb 0).1
    simpa using this
  have hdg : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hpw : ∀ τ' : ℝ, ‖deriv g τ'‖ ≤ C := fun τ' => by
    have := (hb τ').2.1
    have h1 : (1 + |τ'|) ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ']) (by norm_num)
    nlinarith
  have hpw2 : ∀ τ' : ℝ, ‖deriv (deriv g) τ'‖ ≤ C := fun τ' => by
    have := (hb τ').2.2
    have h1 : (1 + |τ'|) ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg τ']) (by norm_num)
    nlinarith
  refine ⟨hg.contDiffOn, ⟨C, fun τ hτ hτ1 => ?_⟩, ⟨C, fun τ hτ => ?_⟩⟩
  · have hy : 0 < |τ| := abs_pos.mpr hτ
    have hlip : ‖g τ - g 0‖ ≤ C * ‖τ - 0‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun x _ => hdg x) (fun x _ => hpw x) convex_univ trivial trivial
    rw [sub_zero, Real.norm_eq_abs] at hlip
    have hα : |τ| ≤ |τ| ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge hy hτ1 hα1
      simpa using this
    have h1 : 1 ≤ |τ| ^ (α - 1) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hτ1 (by linarith)
    have h2 : 1 ≤ |τ| ^ (α - 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hτ1 (by linarith)
    refine ⟨hlip.trans (mul_le_mul_of_nonneg_left hα hC0), ?_, ?_⟩
    · nlinarith [hpw τ, mul_le_mul_of_nonneg_left h1 hC0]
    · nlinarith [hpw2 τ, mul_le_mul_of_nonneg_left h2 hC0]
  · exact hb τ

end FormalResearch.SignUncertainty
