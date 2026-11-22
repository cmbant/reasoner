module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Binet Remainder and Derivative Bounds (Lemma T.1)

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`,
Lemma T.1 (`mat:T1`) and equation `(e31)`.

## Main definitions
* `muBin t`: the Binet kernel `t⁻¹ * ((exp t - 1)⁻¹ - t⁻¹ + 1 / 2)` for `t ≠ 0`, extended by `1 / 12` at `0`.
* `binetRem w`: Binet's integral `∫ t in Ioi 0, (muBin t : ℂ) * exp (-((t : ℂ) * w))` for `0 < w.re`.
* `binetDiff c ζ`: the shifted Binet difference `binetRem (c * (1 - ζ)) - binetRem c`.

## Main results
* `muBin_pos`, `muBin_le`, `muBin_continuousOn`: `0 < muBin t ≤ 1 / 12` for `t > 0`, and continuity on `(0, ∞)`.
* `binetRem_differentiableOn`, `iteratedDeriv_binetRem`, `binetRem_iteratedDeriv_norm_le`:
  holomorphicity on `{w : ℂ | 0 < w.re}`, differentiation under the integral sign, and
  `‖iteratedDeriv r binetRem w‖ ≤ r! / (12 * w.re ^ (r + 1))`.
* `binetDiff_norm_le`, `binetDiff_norm_le_left`, `binetDiff_norm_le_strip`,
  `binetDiff_iteratedDeriv_norm_le`, `binetDiff_re_vertical_le`: Lemma T.1(b), `(e31)`, and vertical comparison.
-/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped Nat Topology

namespace FormalResearch.Asymptotics

/-! ### Definitions -/

/-- Binet kernel `μ_Bin(t) = t⁻¹ ((e^t - 1)⁻¹ - t⁻¹ + 1/2)` (`1/12` at `t = 0`). -/
noncomputable def muBin (t : ℝ) : ℝ :=
  if t = 0 then 1 / 12 else t⁻¹ * ((Real.exp t - 1)⁻¹ - t⁻¹ + 1 / 2)

/-- Binet remainder `B_Bin(w) = ∫_{0}^∞ μ_Bin(t) e^{-t w} dt`. -/
noncomputable def binetRem (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (muBin t : ℂ) * Complex.exp (-((t : ℂ) * w))

/-- Shifted Binet remainder `B_c(ζ) = B_Bin(c(1 - ζ)) - B_Bin(c)`. -/
noncomputable def binetDiff (c : ℝ) (ζ : ℂ) : ℂ :=
  binetRem ((c : ℂ) * (1 - ζ)) - binetRem (c : ℂ)

/-! ### Elementary positivity, bound, and continuity of `muBin` -/

private lemma pos_of_zero_of_deriv_pos {g g' : ℝ → ℝ} (h0 : g 0 = 0)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hpos : ∀ x > 0, 0 < g' x) {x : ℝ} (hx : 0 < x) :
    0 < g x := by
  have hmono : StrictMonoOn g (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt).continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact hpos s hs
  rw [← h0]
  exact hmono le_rfl hx.le hx

private lemma nonneg_of_zero_of_deriv_nonneg {g : ℝ → ℝ} (g' : ℝ → ℝ) (h0 : g 0 = 0)
    (hnn : ∀ x ≥ 0, 0 ≤ g' x) (hd : ∀ x, HasDerivAt g (g' x) x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ g x := by
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt).continuousOn
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact hnn s hs.le
  rw [← h0]
  exact hmono le_rfl hx hx

private lemma sinh_pos_of_pos {z : ℝ} (hz : 0 < z) : 0 < Real.sinh z := by
  have h : 0 < Real.sinh z - z :=
    pos_of_zero_of_deriv_pos (by simp)
      (fun u => (Real.hasDerivAt_sinh u).sub (hasDerivAt_id u))
      (fun u hu => by
        have hch : Real.cosh u = 1 + (Real.exp u - 1) ^ 2 / (2 * Real.exp u) := by
          rw [Real.cosh_eq, Real.exp_neg]
          have he : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
          field_simp; ring
        have hpos : 0 < (Real.exp u - 1) ^ 2 / (2 * Real.exp u) :=
          div_pos (sq_pos_of_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu))) (by positivity)
        linarith) hz
  linarith

private lemma id_mul_cosh_sub_sinh_pos {z : ℝ} (hz : 0 < z) :
    0 < z * Real.cosh z - Real.sinh z :=
  pos_of_zero_of_deriv_pos (by simp)
    (fun s =>
      (((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s)).congr_deriv
        (by dsimp; ring))
    (fun s hs => mul_pos hs (sinh_pos_of_pos hs)) hz

private lemma id_mul_cosh_sub_sinh_nonneg {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ z * Real.cosh z - Real.sinh z := by
  rcases eq_or_lt_of_le hz with rfl | h
  · simp
  · exact (id_mul_cosh_sub_sinh_pos h).le

private lemma three_id_mul_cosh_sub_sinh_le {z : ℝ} (hz : 0 ≤ z) :
    3 * (z * Real.cosh z - Real.sinh z) ≤ z ^ 2 * Real.sinh z := by
  have hφ : 0 ≤ (3 + z ^ 2) * Real.sinh z - 3 * z * Real.cosh z := by
    refine nonneg_of_zero_of_deriv_nonneg
      (g := fun t => (3 + t ^ 2) * Real.sinh t - 3 * t * Real.cosh t)
      (fun s => s * (s * Real.cosh s - Real.sinh s)) (by simp)
      (fun s hs => mul_nonneg hs (id_mul_cosh_sub_sinh_nonneg hs)) (fun s => ?_) hz
    have hA : HasDerivAt (fun t => (3 + t ^ 2) * Real.sinh t)
        ((0 + 2 * s) * Real.sinh s + (3 + s ^ 2) * Real.cosh s) s :=
      (((hasDerivAt_const s 3).add (hasDerivAt_pow 2 s)).mul (Real.hasDerivAt_sinh s)).congr_deriv
        (by dsimp; ring)
    have hB : HasDerivAt (fun t => 3 * t * Real.cosh t)
        (3 * 1 * Real.cosh s + 3 * s * Real.sinh s) s :=
      ((hasDerivAt_id s).const_mul 3).mul (Real.hasDerivAt_cosh s)
    exact (hA.sub hB).congr_deriv (by ring)
  linarith

private lemma muBin_eq_sinh_cosh {t : ℝ} (ht : 0 < t) :
    muBin t = ((t / 2) * Real.cosh (t / 2) - Real.sinh (t / 2)) /
      (4 * (t / 2) ^ 2 * Real.sinh (t / 2)) := by
  have ht0 : t ≠ 0 := ht.ne'
  simp only [muBin, ht0, ↓reduceIte]
  set z : ℝ := t / 2
  have hz : 0 < z := by positivity
  have hsh : Real.sinh z ≠ 0 := (sinh_pos_of_pos hz).ne'
  have hsq : Real.exp z ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]
    congr 1
    dsimp [z]
    ring
  have hexp_neg : Real.exp (-z) = (Real.exp z)⁻¹ := Real.exp_neg z
  have hez : Real.exp z ≠ 0 := (Real.exp_pos z).ne'
  have het : Real.exp t - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)).ne'
  have hcosh_sinh : Real.cosh z / (2 * Real.sinh z) = (Real.exp t - 1)⁻¹ + 1 / 2 := by
    rw [Real.cosh_eq, Real.sinh_eq, hexp_neg, ← hsq]
    have hsq1 : Real.exp z ^ 2 - 1 ≠ 0 := by rwa [hsq]
    field_simp
    ring
  have ht_eq : t = 2 * z := by dsimp [z]; ring
  rw [show t⁻¹ * ((Real.exp t - 1)⁻¹ - t⁻¹ + 1 / 2) =
      (2 * z)⁻¹ * (((Real.exp t - 1)⁻¹ + 1 / 2) - (2 * z)⁻¹) by rw [← ht_eq]; ring]
  rw [← hcosh_sinh]
  have hz0 : z ≠ 0 := hz.ne'
  field_simp
  ring

/-- Positivity of the Binet kernel `μ_Bin(t) > 0` for `t > 0` (`mat:T1`). -/
theorem muBin_pos {t : ℝ} (ht : 0 < t) : 0 < muBin t := by
  rw [muBin_eq_sinh_cosh ht]
  have hz : 0 < t / 2 := by positivity
  exact div_pos (id_mul_cosh_sub_sinh_pos hz)
    (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hz)) (sinh_pos_of_pos hz))

/-- Upper bound `μ_Bin(t) ≤ 1 / 12` for `t > 0` (`mat:T1`). -/
theorem muBin_le {t : ℝ} (ht : 0 < t) : muBin t ≤ 1 / 12 := by
  rw [muBin_eq_sinh_cosh ht]
  have hz : 0 < t / 2 := by positivity
  have hsh : 0 < Real.sinh (t / 2) := sinh_pos_of_pos hz
  have hden : 0 < 4 * (t / 2) ^ 2 * Real.sinh (t / 2) := by positivity
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 12)]
  linarith [three_id_mul_cosh_sub_sinh_le hz.le]

lemma muBin_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ muBin t := by
  rcases eq_or_lt_of_le ht with rfl | h
  · simp [muBin]
  · exact (muBin_pos h).le

lemma muBin_le_of_nonneg {t : ℝ} (ht : 0 ≤ t) : muBin t ≤ 1 / 12 := by
  rcases eq_or_lt_of_le ht with rfl | h
  · simp [muBin]
  · exact muBin_le h

/-- Continuity of `μ_Bin` on `(0, ∞)`. -/
theorem muBin_continuousOn : ContinuousOn muBin (Ioi 0) := by
  refine ContinuousOn.congr (f := fun t : ℝ => t⁻¹ * ((Real.exp t - 1)⁻¹ - t⁻¹ + 1 / 2)) ?_ ?_
  · intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (mem_Ioi.mp ht)
    have het : Real.exp t - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)).ne'
    have hcont : ContinuousAt (fun s : ℝ => s⁻¹ * ((Real.exp s - 1)⁻¹ - s⁻¹ + 1 / 2)) t := by
      refine (continuousAt_id.inv₀ ht0).mul (((((Real.continuous_exp.continuousAt.sub
        continuousAt_const).inv₀ het).sub (continuousAt_id.inv₀ ht0)).add continuousAt_const))
    exact hcont.continuousWithinAt
  · intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (mem_Ioi.mp ht)
    simp only [muBin, ht0, ↓reduceIte]

private lemma measurable_muBin : Measurable muBin := by
  unfold muBin
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact measurable_id.inv.mul
    (((Real.measurable_exp.sub measurable_const).inv.sub measurable_id.inv).add measurable_const)

/-! ### Gamma decay integrals on `Ioi 0` -/

private lemma integrableOn_pow_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (r : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ r * Real.exp (-(a * t))) (Ioi 0) := by
  have hgam : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (r : ℝ)) (Ioi 0) := by
    simpa [add_sub_cancel_right] using
      Real.GammaIntegral_convergent (by positivity : (0 : ℝ) < (r : ℝ) + 1)
  have hscaled : IntegrableOn (fun t : ℝ => Real.exp (-(a * t)) * (a * t) ^ (r : ℝ)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (r : ℝ)) 0 ha).mpr
    rw [mul_zero] at h
    exact h hgam
  have hconst : IntegrableOn
      (fun t : ℝ => (a ^ r)⁻¹ * (Real.exp (-(a * t)) * (a * t) ^ (r : ℝ))) (Ioi 0) :=
    hscaled.const_mul (a ^ r)⁻¹
  refine hconst.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_natCast, mul_pow]
  have ha0 : a ^ r ≠ 0 := pow_ne_zero r ha.ne'
  field_simp

private lemma integral_pow_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (r : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ r * Real.exp (-(a * t)) = (r.factorial : ℝ) / a ^ (r + 1) := by
  have hgam := Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : (0 : ℝ) < (r : ℝ) + 1) ha
  have hLHS : ∫ t in Ioi (0 : ℝ), t ^ r * Real.exp (-(a * t)) =
      ∫ t in Ioi (0 : ℝ), t ^ (((r : ℝ) + 1) - 1) * Real.exp (-(a * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [hLHS, hgam, Real.Gamma_nat_eq_factorial,
    show (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, one_div_pow]
  ring

/-! ### Differentiation under the integral sign for `binetRem` -/

/-- Auxiliary integral `∫_{0}^∞ μ_Bin(t) t^r e^{-t w} dt` for `Re w > 0`. -/
private noncomputable def binetKernel (r : ℕ) (w : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (muBin t : ℂ) * (t : ℂ) ^ r * Complex.exp (-((t : ℂ) * w))

private lemma binetKernel_zero (w : ℂ) : binetKernel 0 w = binetRem w := by
  simp [binetKernel, binetRem]

private lemma integrableOn_binetKernel (r : ℕ) {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (muBin t : ℂ) * (t : ℂ) ^ r * Complex.exp (-((t : ℂ) * w)))
      (Ioi 0) := by
  have hmeas : Measurable (fun t : ℝ => (muBin t : ℂ) * (t : ℂ) ^ r * Complex.exp (-((t : ℂ) * w))) :=
    ((Complex.continuous_ofReal.measurable.comp measurable_muBin).mul
      ((Complex.continuous_ofReal.measurable).pow_const r)).mul
      (Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.mul measurable_const).neg))
  have hdom : IntegrableOn (fun t : ℝ => (1 / 12 : ℝ) * (t ^ r * Real.exp (-(w.re * t)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_mul_Ioi hw r).const_mul (1 / 12)
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  rw [mem_Ioi] at ht
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (muBin_pos ht).le,
    Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, Complex.norm_exp]
  have hre : (-((t : ℂ) * w)).re = -(w.re * t) := by simp [mul_comm]
  rw [hre, mul_assoc]
  exact mul_le_mul_of_nonneg_right (muBin_le ht) (by positivity)

private lemma hasDerivAt_binetKernel (r : ℕ) {w₀ : ℂ} (hw₀ : 0 < w₀.re) :
    HasDerivAt (binetKernel r) (-binetKernel (r + 1) w₀) w₀ := by
  let F : ℂ → ℝ → ℂ := fun w t => (muBin t : ℂ) * (t : ℂ) ^ r * Complex.exp (-((t : ℂ) * w))
  let F' : ℂ → ℝ → ℂ := fun w t =>
    -((muBin t : ℂ) * (t : ℂ) ^ (r + 1) * Complex.exp (-((t : ℂ) * w)))
  let δ : ℝ := w₀.re / 2
  have hδ : 0 < δ := by positivity
  let bound : ℝ → ℝ := fun t => (1 / 12 : ℝ) * (t ^ (r + 1) * Real.exp (-(δ * t)))
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    refine Eventually.of_forall fun w => ?_
    exact (((Complex.continuous_ofReal.measurable.comp measurable_muBin).mul
      (Complex.continuous_ofReal.measurable.pow_const r)).mul
      (Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.mul measurable_const).neg))).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' w₀) (volume.restrict (Ioi 0)) := by
    exact (((Complex.continuous_ofReal.measurable.comp measurable_muBin).mul
      (Complex.continuous_ofReal.measurable.pow_const (r + 1))).mul
      (Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.mul measurable_const).neg))).neg.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ∀ w ∈ ball w₀ δ, ‖F' w t‖ ≤ bound t := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht w hw => ?_)
    rw [mem_Ioi] at ht
    rw [mem_ball, Complex.dist_eq] at hw
    have hw_re : δ < w.re := by
      have habs : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
        simpa [Complex.sub_re] using Complex.abs_re_le_norm (w - w₀)
      have hδ_eq : δ = w₀.re / 2 := rfl
      linarith [abs_sub_le_iff.mp habs |>.1, abs_sub_le_iff.mp habs |>.2]
    dsimp only [F', bound]
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (muBin_pos ht).le,
      Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, Complex.norm_exp]
    have hre : (-((t : ℂ) * w)).re = -(w.re * t) := by simp [mul_comm]
    rw [hre, mul_assoc]
    refine mul_le_mul (muBin_le ht) ?_ (by positivity) (by positivity)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    nlinarith [ht.le, hw_re]
  have h_diff : ∀ᵐ t ∂(volume.restrict (Ioi 0)),
      ∀ w ∈ ball w₀ δ, HasDerivAt (F · t) (F' w t) w := by
    refine Eventually.of_forall fun t w _ => ?_
    have hd1 : HasDerivAt (fun z : ℂ => -((t : ℂ) * z)) (-(t : ℂ)) w := by
      simp_rw [← neg_mul]
      exact ((hasDerivAt_id w).const_mul (-(t : ℂ))).congr_deriv (mul_one _)
    have hd2 := hd1.cexp.const_mul ((muBin t : ℂ) * (t : ℂ) ^ r)
    refine hd2.congr_deriv ?_
    dsimp [F']
    rw [pow_succ]
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds w₀ hδ) hF_meas (integrableOn_binetKernel r hw₀) hF'_meas
    h_bound ((integrableOn_pow_mul_exp_neg_mul_Ioi hδ (r + 1)).const_mul (1 / 12)) h_diff
  have heq_int : ∫ t in Ioi (0 : ℝ), F' w₀ t = -binetKernel (r + 1) w₀ := by
    dsimp only [F', binetKernel]
    rw [integral_neg]
  rw [heq_int] at hmain
  exact hmain.2

/-- Holomorphicity of `binetRem` on `{w : ℂ | 0 < w.re}` (`mat:T1`). -/
theorem binetRem_differentiableOn : DifferentiableOn ℂ binetRem {w : ℂ | 0 < w.re} := by
  intro w hw
  have hfun : binetKernel 0 = binetRem := funext binetKernel_zero
  have hd : HasDerivAt binetRem (-binetKernel 1 w) w := by
    rw [← hfun]
    exact hasDerivAt_binetKernel 0 hw
  exact hd.differentiableAt.differentiableWithinAt

private lemma iteratedDeriv_binetKernel (r : ℕ) {w : ℂ} (hw : 0 < w.re) :
    iteratedDeriv r binetRem w = (-1 : ℂ) ^ r * binetKernel r w := by
  induction r generalizing w with
  | zero =>
    simp [binetKernel_zero]
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq : (iteratedDeriv r binetRem) =ᶠ[𝓝 w] fun z => (-1 : ℂ) ^ r * binetKernel r z := by
      filter_upwards [hopen.mem_nhds hw] with z hz
      exact ih hz
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun z => (-1 : ℂ) ^ r * binetKernel r z)
        ((-1 : ℂ) ^ r * (-binetKernel (r + 1) w)) w :=
      (hasDerivAt_binetKernel r hw).const_mul ((-1 : ℂ) ^ r)
    rw [hd.deriv, pow_succ]
    ring

/-- Explicit integral formula for the `r`-th complex derivative of `binetRem` on `Re w > 0`. -/
theorem iteratedDeriv_binetRem (r : ℕ) {w : ℂ} (hw : 0 < w.re) :
    iteratedDeriv r binetRem w =
      (-1 : ℂ) ^ r * ∫ t in Ioi (0 : ℝ), (muBin t : ℂ) * (t : ℂ) ^ r * Complex.exp (-((t : ℂ) * w)) :=
  iteratedDeriv_binetKernel r hw

/-- Derivative bound for `B_Bin^(r)(w)` on `Re w > 0` (`mat:T1`(a)). -/
theorem binetRem_iteratedDeriv_norm_le (r : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ‖iteratedDeriv r binetRem w‖ ≤ (r.factorial : ℝ) / (12 * w.re ^ (r + 1)) := by
  rw [iteratedDeriv_binetRem r hw, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have hnorm_le : ‖∫ t in Ioi (0 : ℝ), (muBin t : ℂ) * (t : ℂ) ^ r * Complex.exp (-((t : ℂ) * w))‖ ≤
      ∫ t in Ioi (0 : ℝ), (1 / 12 : ℝ) * (t ^ r * Real.exp (-(w.re * t))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on ?_ ((integrableOn_pow_mul_exp_neg_mul_Ioi hw r).const_mul (1 / 12))
      measurableSet_Ioi fun t ht => ?_
    · exact (integrableOn_binetKernel r hw).norm
    · rw [mem_Ioi] at ht
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (muBin_pos ht).le,
        Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le, Complex.norm_exp]
      have hre : (-((t : ℂ) * w)).re = -(w.re * t) := by simp [mul_comm]
      rw [hre, mul_assoc]
      exact mul_le_mul_of_nonneg_right (muBin_le ht) (by positivity)
  have hint_val : ∫ t in Ioi (0 : ℝ), (1 / 12 : ℝ) * (t ^ r * Real.exp (-(w.re * t))) =
      (r.factorial : ℝ) / (12 * w.re ^ (r + 1)) := by
    rw [integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi hw r]
    ring
  exact hnorm_le.trans_eq hint_val

/-- Zero-order bound `‖binetRem w‖ ≤ 1 / (12 * w.re)` for `Re w > 0` (`mat:T1`(a)). -/
theorem binetRem_norm_le {w : ℂ} (hw : 0 < w.re) :
    ‖binetRem w‖ ≤ 1 / (12 * w.re) := by
  simpa using binetRem_iteratedDeriv_norm_le 0 hw

/-! ### Lemma T.1(b), `(e31)`, and vertical comparison for `binetDiff` -/

/-- General strip bound for `B_c(ζ) = B_Bin(c(1 - ζ)) - B_Bin(c)` (`mat:T1`(b)). -/
theorem binetDiff_norm_le {c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ζ.re < 1) :
    ‖binetDiff c ζ‖ ≤ (1 / (12 * c)) * (1 / (1 - ζ.re) + 1) := by
  have hw1 : 0 < ((c : ℂ) * (1 - ζ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re,
      zero_mul, sub_zero]
    exact mul_pos hc (sub_pos.mpr hζ)
  have hw2 : 0 < (c : ℂ).re := by simpa using hc
  have hb1 : ‖binetRem ((c : ℂ) * (1 - ζ))‖ ≤ 1 / (12 * (c * (1 - ζ.re))) := by
    simpa [Complex.mul_re, Complex.sub_re] using binetRem_norm_le hw1
  have hb2 : ‖binetRem (c : ℂ)‖ ≤ 1 / (12 * c) := by
    simpa using binetRem_norm_le hw2
  calc ‖binetDiff c ζ‖
      = ‖binetRem ((c : ℂ) * (1 - ζ)) - binetRem (c : ℂ)‖ := rfl
    _ ≤ ‖binetRem ((c : ℂ) * (1 - ζ))‖ + ‖binetRem (c : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 / (12 * (c * (1 - ζ.re))) + 1 / (12 * c) := add_le_add hb1 hb2
    _ = (1 / (12 * c)) * (1 / (1 - ζ.re) + 1) := by
        have hc0 : c ≠ 0 := hc.ne'
        have h1s : 1 - ζ.re ≠ 0 := (sub_pos.mpr hζ).ne'
        field_simp

/-- Left half-plane bound `‖B_c(ζ)‖ ≤ 1 / (6 c)` for `Re ζ ≤ 0` (`mat:T1`(b), `(e31)`). -/
theorem binetDiff_norm_le_left {c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ζ.re ≤ 0) :
    ‖binetDiff c ζ‖ ≤ 1 / (6 * c) := by
  have hζ1 : ζ.re < 1 := by linarith
  have hinv : 1 / (1 - ζ.re) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
  calc ‖binetDiff c ζ‖
      ≤ (1 / (12 * c)) * (1 / (1 - ζ.re) + 1) := binetDiff_norm_le hc hζ1
    _ ≤ (1 / (12 * c)) * (1 + 1) := by gcongr
    _ = 1 / (6 * c) := by ring

/-- Strip bound `‖B_c(ζ)‖ ≤ 1 / (5 c)` for `0 < Re ζ ≤ 1 / 10` (`mat:T1`(b)). -/
theorem binetDiff_norm_le_strip {c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ0 : 0 < ζ.re)
    (hζ1 : ζ.re ≤ 1 / 10) : ‖binetDiff c ζ‖ ≤ 1 / (5 * c) := by
  have hζlt : ζ.re < 1 := by linarith
  have hinv : 1 / (1 - ζ.re) ≤ 10 / 9 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  calc ‖binetDiff c ζ‖
      ≤ (1 / (12 * c)) * (1 / (1 - ζ.re) + 1) := binetDiff_norm_le hc hζlt
    _ ≤ (1 / (12 * c)) * (10 / 9 + 1) := by gcongr
    _ = (19 / 108) * c⁻¹ := by ring
    _ ≤ (1 / 5) * c⁻¹ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = 1 / (5 * c) := by ring

private lemma iteratedDeriv_binetRem_comp_left (c : ℝ) (hc : 0 < c) (r : ℕ) {ζ : ℂ}
    (hζ : ζ.re < 1) :
    iteratedDeriv r (fun z : ℂ => binetRem ((c : ℂ) * (1 - z))) ζ =
      (c : ℂ) ^ r * binetKernel r ((c : ℂ) * (1 - ζ)) := by
  induction r generalizing ζ with
  | zero =>
    simp [binetKernel_zero]
  | succ r ih =>
    rw [iteratedDeriv_succ]
    have hopen : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    have heq : (iteratedDeriv r fun z : ℂ => binetRem ((c : ℂ) * (1 - z))) =ᶠ[𝓝 ζ]
        fun z => (c : ℂ) ^ r * binetKernel r ((c : ℂ) * (1 - z)) := by
      filter_upwards [hopen.mem_nhds hζ] with z hz
      exact ih hz
    rw [heq.deriv_eq]
    have hre : 0 < ((c : ℂ) * (1 - ζ)).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re,
        zero_mul, sub_zero]
      exact mul_pos hc (sub_pos.mpr hζ)
    have hd_aff : HasDerivAt (fun z : ℂ => (c : ℂ) * (1 - z)) (-(c : ℂ)) ζ := by
      have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) ζ := by
        simpa using (hasDerivAt_id ζ).const_sub (1 : ℂ)
      exact (h1.const_mul (c : ℂ)).congr_deriv (by ring)
    have hd_comp : HasDerivAt (fun z : ℂ => (c : ℂ) ^ r * binetKernel r ((c : ℂ) * (1 - z)))
        ((c : ℂ) ^ r * (-binetKernel (r + 1) ((c : ℂ) * (1 - ζ)) * -(c : ℂ))) ζ :=
      ((hasDerivAt_binetKernel r hre).comp ζ hd_aff).const_mul ((c : ℂ) ^ r)
    rw [hd_comp.deriv, pow_succ]
    ring

/-- Higher-derivative bound on `Re ζ ≤ 0` for `r ≥ 1`:
`‖∂_ζ^r B_c(ζ)‖ ≤ r! / (12 c)` (`mat:T1`(b), eq. `(e31)`). -/
theorem binetDiff_iteratedDeriv_norm_le {c : ℝ} (hc : 0 < c) {ζ : ℂ} (hζ : ζ.re ≤ 0)
    {r : ℕ} (hr : 1 ≤ r) :
    ‖iteratedDeriv r (binetDiff c) ζ‖ ≤ (r.factorial : ℝ) / (12 * c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hr
  have hderiv_eq : iteratedDeriv (k + 1) (binetDiff c) ζ =
      iteratedDeriv (k + 1) (fun z : ℂ => binetRem ((c : ℂ) * (1 - z))) ζ := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hconst : deriv (binetDiff c) = deriv (fun z : ℂ => binetRem ((c : ℂ) * (1 - z))) := by
      ext z
      exact deriv_sub_const (f := fun w : ℂ => binetRem ((c : ℂ) * (1 - w))) (binetRem (c : ℂ))
    rw [hconst]
  have hζ1 : ζ.re < 1 := by linarith
  have hw_re : 0 < ((c : ℂ) * (1 - ζ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.one_re,
      zero_mul, sub_zero]
    exact mul_pos hc (sub_pos.mpr hζ1)
  have hkern_norm : ‖binetKernel (k + 1) ((c : ℂ) * (1 - ζ))‖ ≤
      ((k + 1).factorial : ℝ) / (12 * (c * (1 - ζ.re)) ^ (k + 1 + 1)) := by
    have h1 := binetRem_iteratedDeriv_norm_le (k + 1) hw_re
    rw [iteratedDeriv_binetKernel (k + 1) hw_re, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      one_mul] at h1
    simpa [Complex.mul_re, Complex.sub_re] using h1
  rw [hderiv_eq, iteratedDeriv_binetRem_comp_left c hc (k + 1) hζ1, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hc.le]
  have h1s : 1 ≤ 1 - ζ.re := by linarith
  have h1s_pow : 1 ≤ (1 - ζ.re) ^ (k + 1 + 1) := one_le_pow₀ h1s
  calc c ^ (k + 1) * ‖binetKernel (k + 1) ((c : ℂ) * (1 - ζ))‖
      ≤ c ^ (k + 1) * (((k + 1).factorial : ℝ) / (12 * (c * (1 - ζ.re)) ^ (k + 1 + 1))) :=
          mul_le_mul_of_nonneg_left hkern_norm (by positivity)
    _ = ((k + 1).factorial : ℝ) / (12 * c * (1 - ζ.re) ^ (k + 1 + 1)) := by
          rw [mul_pow, pow_succ c (k + 1)]
          have hc0 : c ^ (k + 1) ≠ 0 := pow_ne_zero _ hc.ne'
          field_simp
    _ ≤ ((k + 1).factorial : ℝ) / (12 * c) := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          nlinarith [mul_pos (by norm_num : (0 : ℝ) < 12) hc]

/-- Vertical comparison: `Re B_c(σ + i τ) ≤ Re B_c(σ)` for `c > 0`, `σ < 1`, `τ : ℝ` (`mat:T1`(b)). -/
theorem binetDiff_re_vertical_le {c σ : ℝ} (hc : 0 < c) (hσ : σ < 1) (τ : ℝ) :
    (binetDiff c ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ (binetDiff c (σ : ℂ)).re := by
  simp only [binetDiff, Complex.sub_re, sub_le_sub_iff_right]
  set w₁ : ℂ := (c : ℂ) * (1 - ((σ : ℂ) + (τ : ℂ) * Complex.I))
  set w₀ : ℂ := (c : ℂ) * (1 - (σ : ℂ))
  have hw₁_re : 0 < w₁.re := by
    simp only [w₁, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.one_re, Complex.add_re, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact mul_pos hc (sub_pos.mpr hσ)
  have hw₀_re : 0 < w₀.re := by
    simp only [w₀, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.one_re, zero_mul, sub_zero]
    exact mul_pos hc (sub_pos.mpr hσ)
  have hint₁ := (integrableOn_binetKernel 0 hw₁_re).integrable
  have hint₀ := (integrableOn_binetKernel 0 hw₀_re).integrable
  simp only [pow_zero, mul_one] at hint₁ hint₀
  change (∫ t in Ioi (0 : ℝ), (muBin t : ℂ) * Complex.exp (-((t : ℂ) * w₁))).re ≤
      (∫ t in Ioi (0 : ℝ), (muBin t : ℂ) * Complex.exp (-((t : ℂ) * w₀))).re
  rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, ← integral_re hint₁, ← integral_re hint₀]
  refine setIntegral_mono_on hint₁.re hint₀.re measurableSet_Ioi fun t ht => ?_
  rw [mem_Ioi] at ht
  have hexp₁ : (-((t : ℂ) * w₁)) = (-(t * c * (1 - σ)) : ℝ) + ((t * c * τ : ℝ) * Complex.I) := by
    apply Complex.ext <;> simp [w₁] <;> ring
  have hexp₀ : (-((t : ℂ) * w₀)) = ((-(t * c * (1 - σ)) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [w₀]; ring
    · simp [w₀]
  simp only [RCLike.re_to_complex]
  rw [hexp₁, hexp₀, Complex.exp_add_mul_I]
  simp only [← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  have hcos : Real.cos (t * c * τ) ≤ 1 := Real.cos_le_one _
  have hnn : 0 ≤ muBin t * Real.exp (-(t * c * (1 - σ))) :=
    mul_nonneg (muBin_pos ht).le (Real.exp_pos _).le
  nlinarith

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.Asymptotics.muBin_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.muBin_pos

/-- info: 'FormalResearch.Asymptotics.muBin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.muBin_le

/-- info: 'FormalResearch.Asymptotics.muBin_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.muBin_continuousOn

/-- info: 'FormalResearch.Asymptotics.binetRem_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.binetRem_differentiableOn

/-- info: 'FormalResearch.Asymptotics.iteratedDeriv_binetRem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.iteratedDeriv_binetRem

/-- info: 'FormalResearch.Asymptotics.binetRem_iteratedDeriv_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.binetRem_iteratedDeriv_norm_le

/-- info: 'FormalResearch.Asymptotics.binetDiff_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.binetDiff_norm_le

/-- info: 'FormalResearch.Asymptotics.binetDiff_norm_le_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.binetDiff_norm_le_left

/-- info: 'FormalResearch.Asymptotics.binetDiff_norm_le_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.binetDiff_norm_le_strip

/-- info: 'FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.binetDiff_iteratedDeriv_norm_le

/-- info: 'FormalResearch.Asymptotics.binetDiff_re_vertical_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.binetDiff_re_vertical_le

end FormalResearch.Asymptotics
