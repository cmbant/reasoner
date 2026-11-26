module

public import FormalResearch.CohnElkies.CoherentSectorialLimit
public import FormalResearch.CohnElkies.MovingDiagonalSource
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Cancelled Origin Symbol (`O.11c`), Coherent Right-Half-Plane Bounds (`P.1(2)`, `U.2`), and Two-Scale Laplace Decay

Unconditional formalization via the direct Gaussian-IBP route:
* Exact Gaussian transforms on `{y : ℂ | 0 < y.re}` for `ceF1`, `ceG1 (airyZero 1)`, and
  `ceG1Deriv airyDerivFirstZero`.
* Higher-derivative Airy decay on `[0, ∞)` and uniform 4-fold / (3+3+1)-fold Gaussian IBP
  expansions on `{y : ℂ | 0 < y.re ∧ 1 ≤ ‖y‖}` (`airyTwistedLaplaceC_ceF1_asymp`,
  `airyTwistedLaplaceC_ceG1Deriv_asymp`, `airyTwistedLaplaceC_ceG1_bound`).
* `ce_o1_route.tex` Lemma `O.11c` (`(ceo:O11c.1)`–`(ceo:O11c.2)`) for
  `ceCancelE := ceF1 - ceG1Deriv airyDerivFirstZero`.
* `ce_rate.tex` Lemma `P.1(2)` and `u1c_o1_upper.tex` Lemma `U.2` right-half-plane and
  vertical-line Cauchy bounds for `ceS0` and `ceSb`.
* Unconditional `twoScaleQ0_real_laplace_bound` discharging `hQ0_lap` of
  `MovingDiagonalSource.twoScale_mellin_origin`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Section 0: Analytic, Cauchy, and Laplace regularity helpers -/

private lemma holomorphic_real_contDiff_and_cauchy {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hR : ∀ t : ℝ, (t : ℂ) ∈ U) {r : ℝ} (hr : 0 < r)
    (hball : ∀ τ : ℝ, Metric.closedBall (τ : ℂ) r ⊆ U)
    {B : ℝ → ℝ} (hB : ∀ τ : ℝ, ∀ ω ∈ Metric.sphere (τ : ℂ) r, ‖F ω‖ ≤ B τ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (t : ℂ)) ∧
      ∀ (j : ℕ) (τ : ℝ), ‖iteratedDeriv j (fun t : ℝ => F (t : ℂ)) τ‖ ≤ j.factorial * B τ / r ^ j := by
  have hC_on : ContDiffOn ℂ (⊤ : ℕ∞) F U := (hF.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (t : ℂ)) := contDiff_iff_contDiffAt.mpr fun t =>
    ((hC_on.contDiffAt (hU.mem_nhds (hR t))).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  have hiter : ∀ (j : ℕ) (t : ℝ), iteratedDeriv j (fun s : ℝ => F (s : ℂ)) t = iteratedDeriv j F (t : ℂ) := fun j => by
    induction j with
    | zero => intro t; simp
    | succ k ih =>
      intro t; rw [iteratedDeriv_succ, show iteratedDeriv k (fun s : ℝ => F (s : ℂ)) =
        fun s : ℝ => iteratedDeriv k F (s : ℂ) from funext ih, iteratedDeriv_succ]
      have hwk := hC_on.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast WithTop.coe_lt_top k) hU.uniqueDiffOn
      exact (((hwk _ (hR t)).differentiableAt (hU.mem_nhds (hR t))).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hU.mem_nhds (hR t)) fun z hz => (iteratedDerivWithin_of_isOpen hU hz).symm) |>.hasDerivAt.comp_ofReal).deriv
  refine ⟨hC, fun j τ => ?_⟩; rw [hiter j τ]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    ⟨hF.mono (Metric.ball_subset_closedBall.trans (hball τ)),
      (hF.continuousOn.mono (hball τ)).mono Metric.closure_ball_subset_closedBall⟩ (hB τ)

private lemma norm_one_sub_I_mul_ge' {τ : ℝ} {ω : ℂ} (hdist : ‖ω - (τ : ℂ)‖ ≤ 1 / 2) :
    Real.sqrt (1 + τ ^ 2) / 2 ≤ ‖1 - Complex.I * ω‖ := by
  have hτ_norm : ‖1 - Complex.I * (τ : ℂ)‖ = Real.sqrt (1 + τ ^ 2) := by rw [Complex.norm_def, Complex.normSq_apply]; simp [sq]
  have htri : ‖1 - Complex.I * (τ : ℂ)‖ ≤ ‖1 - Complex.I * ω‖ + 1 / 2 := calc
    ‖1 - Complex.I * (τ : ℂ)‖ = ‖(1 - Complex.I * ω) + Complex.I * (ω - (τ : ℂ))‖ := by congr 1; ring
    _ ≤ ‖1 - Complex.I * ω‖ + ‖Complex.I * (ω - (τ : ℂ))‖ := norm_add_le _ _
    _ ≤ ‖1 - Complex.I * ω‖ + 1 / 2 := by rw [norm_mul, Complex.norm_I, one_mul]; linarith
  have h1_ge : 1 ≤ ‖1 - Complex.I * (τ : ℂ)‖ := hτ_norm ▸ Real.one_le_sqrt.mpr (by linarith [sq_nonneg τ])
  linarith

private lemma norm_le_one_add_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) : ‖w‖ ≤ ‖1 + w‖ := by
  rw [← Real.sqrt_sq (norm_nonneg w), ← Real.sqrt_sq (norm_nonneg (1 + w))]
  refine Real.sqrt_le_sqrt ?_
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]; nlinarith

private lemma neg_c_rpow32_add_le {α R u : ℝ} (hα : 0 < α) (hR : 0 ≤ R) (hu : 0 ≤ u) :
    -α * u ^ (3 / 2 : ℝ) + R * u ≤ (R + 1) * ((R + 1) / α) ^ 2 - u := by
  let M : ℝ := (R + 1) / α; have hM_sq : 0 ≤ (R + 1) * M ^ 2 := by positivity
  by_cases hru : M ≤ Real.sqrt u
  · have hpow : u ^ (3 / 2 : ℝ) = u * Real.sqrt u := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hu (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]
    have hαM : α * M = R + 1 := mul_div_cancel₀ (R + 1) hα.ne'
    have hmul : (R + 1) * u ≤ α * u ^ (3 / 2 : ℝ) := by rw [hpow]; nlinarith [mul_le_mul_of_nonneg_left hru hα.le]
    dsimp [M] at hM_sq; linarith
  · push Not at hru
    have hu_le : u ≤ M ^ 2 := by nlinarith [Real.sqrt_nonneg u, sq_nonneg (M - Real.sqrt u), Real.sq_sqrt hu]
    nlinarith [mul_nonneg hα.le (Real.rpow_nonneg hu (3 / 2 : ℝ))]

lemma integrableOn_exp_neg_rpow32_add {α R : ℝ} (hα : 0 < α) (hR : 0 ≤ R) :
    IntegrableOn (fun u : ℝ => Real.exp (-α * u ^ (3 / 2 : ℝ) + R * u)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine ((integrableOn_exp_mul_Ioi (by norm_num : -(1 : ℝ) < 0) 0).const_mul (Real.exp ((R + 1) * ((R + 1) / α) ^ 2))).mono'
    ((Real.continuous_exp.comp ((continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))).add
      (continuous_const.mul continuous_id))).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [neg_c_rpow32_add_le hα hR (mem_Ioi.mp hu).le])

private lemma mul_exp_le_inv_of_nonpos {c u : ℝ} (hc : 0 < c) (hu : u ≤ 0) : |u| * Real.exp (c * u) ≤ c⁻¹ := by
  rw [abs_of_nonpos hu]
  have h1 : c * (-u) ≤ Real.exp (c * (-u)) := by linarith [Real.add_one_le_exp (c * (-u))]
  have h2 : c * (-u) * Real.exp (c * u) ≤ 1 := (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le).trans_eq
    (by rw [← Real.exp_add, show c * -u + c * u = 0 by ring, Real.exp_zero])
  calc (-u) * Real.exp (c * u) = c⁻¹ * (c * (-u) * Real.exp (c * u)) := by field_simp [hc.ne']
    _ ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hc.le)
    _ = c⁻¹ := mul_one _

lemma rpow_neg_half_mul_four_pi {y : ℂ} (hy : 0 < y.re) :
    (4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)) = (((2 * Real.sqrt π)⁻¹ : ℝ) : ℂ) * y ^ (-(1 / 2 : ℂ)) := by
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have h4pi_pos : (0 : ℝ) < 4 * π := by positivity
  have h4pi_ne : ((4 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h4pi_pos.ne'
  have hlog : Complex.log (((4 * π : ℝ) : ℂ) * y) = Complex.log ((4 * π : ℝ) : ℂ) + Complex.log y := by
    rw [Complex.log, Complex.log, Complex.log, Complex.arg_real_mul y h4pi_pos, Complex.arg_ofReal_of_nonneg h4pi_pos.le,
      norm_mul, Complex.norm_of_nonneg h4pi_pos.le, Real.log_mul h4pi_pos.ne' (norm_ne_zero_iff.mpr hy_ne)]; push_cast; ring
  have hsplit : (4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)) = ((4 * π : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * y ^ (-(1 / 2 : ℂ)) := by
    rw [show (4 * (π : ℂ) * y) = ((4 * π : ℝ) : ℂ) * y by push_cast; ring, Complex.cpow_def_of_ne_zero (mul_ne_zero h4pi_ne hy_ne),
      Complex.cpow_def_of_ne_zero h4pi_ne, Complex.cpow_def_of_ne_zero hy_ne, hlog, add_mul, Complex.exp_add]
  have hc4pi : ((4 * π : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = (((2 * Real.sqrt π)⁻¹ : ℝ) : ℂ) := by
    rw [show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow h4pi_pos.le]; congr 1
    rw [Real.rpow_neg h4pi_pos.le, ← Real.sqrt_eq_rpow, show (4 : ℝ) * π = (2 * Real.sqrt π) ^ 2 by rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring, Real.sqrt_sq (by positivity)]
  rw [hsplit, hc4pi]

lemma norm_cpow_ofReal_exponent {y : ℂ} (hy : y ≠ 0) (r : ℝ) : ‖y ^ (r : ℂ)‖ = ‖y‖ ^ r := by
  rw [Complex.norm_cpow_of_ne_zero hy (r : ℂ), Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one]

private lemma integrable_if_neg_pos {g h : ℝ → ℝ} (hg : IntegrableOn g (Iio 0))
    (hh : IntegrableOn h (Ici 0)) : Integrable (fun u : ℝ => if u < 0 then g u else h u) := by
  rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0 : ℝ))]
  exact (hg.congr_fun (fun u hu => by simp [mem_Iio.mp hu]) measurableSet_Iio).union
    (hh.congr_fun (fun u hu => by simp [not_lt.mpr (mem_Ici.mp hu)]) measurableSet_Ici)

private lemma integrable_prod_of_norm_le_mul {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {F : ℝ → ℝ → ℂ} {U T : ℝ → ℝ} (hF_cont : Continuous (Function.uncurry F))
    (hU : Integrable U μ) (hT : Integrable T ν) (hbd : ∀ᵐ u ∂μ, ∀ᵐ t ∂ν, ‖F u t‖ ≤ U u * T t) :
    Integrable (Function.uncurry F) (μ.prod ν) := by
  have hFu_cont : ∀ u : ℝ, AEStronglyMeasurable (F u) ν := fun u => (hF_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  refine (integrable_prod_iff hF_cont.aestronglyMeasurable).mpr ⟨hbd.mono fun u hu => (hT.const_mul (U u)).mono' (hFu_cont u) hu, ?_⟩
  refine (hU.mul_const (∫ t : ℝ, T t ∂ν)).mono' hF_cont.aestronglyMeasurable.norm.integral_prod_right' ?_
  filter_upwards [hbd] with u hu; dsimp only [Function.uncurry]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact (integral_mono_ae ((hT.const_mul (U u)).mono' (hFu_cont u) hu).norm (hT.const_mul (U u)) hu).trans_eq (integral_const_mul _ _)

/-- Master regularity, continuity on `{0 ≤ Re y}`, holomorphy on `{0 < Re y}`, integrability,
and unit-disc uniform bound for `airyTwistedLaplaceC X`. -/
lemma airyTwistedLaplaceC_regularity {X : ℝ → ℝ} (hX_cont : Continuous X) (hX_int : Integrable X)
    {C_t : ℝ} (hC_t : 0 < C_t) (hX_tail : ∀ u : ℝ, 0 ≤ u → |X u| ≤ C_t * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) :
    (∀ y : ℂ, 0 ≤ y.re → Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ)))) ∧
    ContinuousOn (airyTwistedLaplaceC X) {y : ℂ | 0 ≤ y.re} ∧ DifferentiableOn ℂ (airyTwistedLaplaceC X) {y : ℂ | 0 < y.re} ∧
    ∃ C_bd > 0, ∀ {y : ℂ}, 0 ≤ y.re → ‖y‖ ≤ 1 → ‖airyTwistedLaplaceC X y‖ ≤ C_bd := by
  let bound : ℝ → ℝ → ℝ := fun R u => if u < 0 then ‖X u‖ else C_t * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ) + R * u)
  have hmeas_fun : ∀ y : ℂ, AEStronglyMeasurable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ))) volume := fun y =>
    (Complex.continuous_ofReal.comp hX_cont).aestronglyMeasurable.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  have hdom_piece : ∀ (y : ℂ) {R : ℝ}, 0 ≤ y.re → y.re ≤ R → ∀ u : ℝ, ‖(X u : ℂ) * Complex.exp (y * (u : ℂ))‖ ≤ bound R u := fun y R hy0 hyR u => by
    rw [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.norm_eq_abs]; dsimp [bound]
    split_ifs with hu
    · exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy0 hu.le))
    · have hu0 : 0 ≤ u := not_lt.mp hu
      exact (mul_le_mul (hX_tail u hu0) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hyR hu0)) (Real.exp_pos _).le (by positivity)).trans_eq (by rw [mul_assoc, ← Real.exp_add])
  have hbound_int : ∀ {R : ℝ}, 0 ≤ R → Integrable (bound R) := fun {R} hR =>
    integrable_if_neg_pos hX_int.norm.integrableOn ((integrableOn_exp_neg_rpow32_add (by norm_num : (0 : ℝ) < 2 / 3) hR).const_mul C_t)
  have hint_all : ∀ y : ℂ, 0 ≤ y.re → Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ))) := fun y hy =>
    (hbound_int hy).mono' (hmeas_fun y) (ae_of_all _ (hdom_piece y hy le_rfl))
  refine ⟨hint_all, ?_, ?_, ?_⟩
  · intro y₀ _; let R : ℝ := ‖y₀‖ + 1
    have hint_c : ContinuousWithinAt (fun y : ℂ => ∫ u : ℝ, (X u : ℂ) * Complex.exp (y * (u : ℂ))) {y : ℂ | 0 ≤ y.re} y₀ := by
      refine continuousWithinAt_of_dominated (bound := bound R) (Eventually.of_forall hmeas_fun) ?_ (hbound_int (by positivity)) (ae_of_all _ fun u => by fun_prop)
      filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds y₀ one_pos)] with y hy
      have hdist : ‖y - y₀‖ < 1 := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hy.2
      exact ae_of_all _ (hdom_piece y hy.1 ((Complex.re_le_norm y).trans (by rw [show y = (y - y₀) + y₀ by ring]; exact (norm_add_le _ _).trans (by dsimp [R]; linarith))))
    exact (by fun_prop : ContinuousWithinAt (fun y : ℂ => (ceK : ℂ) * Complex.exp (-(y ^ 3) / 12)) {y : ℂ | 0 ≤ y.re} y₀).mul hint_c
  · intro y₀ hy₀; have hy₀_pos : 0 < y₀.re := hy₀
    let c : ℝ := y₀.re / 2; have hc : 0 < c := half_pos hy₀_pos; let R : ℝ := ‖y₀‖ + c
    let bound' : ℝ → ℝ := fun u => if u < 0 then c⁻¹ * ‖X u‖ else C_t * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ) + (R + 1) * u)
    have hbound'_int : Integrable bound' := integrable_if_neg_pos (hX_int.norm.integrableOn.const_mul c⁻¹)
      ((integrableOn_exp_neg_rpow32_add (by norm_num : (0 : ℝ) < 2 / 3) (by positivity)).const_mul C_t)
    let F : ℂ → ℝ → ℂ := fun y u => (X u : ℂ) * Complex.exp (y * (u : ℂ)); let F' : ℂ → ℝ → ℂ := fun y u => (u : ℂ) * (X u : ℂ) * Complex.exp (y * (u : ℂ))
    have hF'_meas : AEStronglyMeasurable (F' y₀) volume :=
      ((Complex.continuous_ofReal.mul (Complex.continuous_ofReal.comp hX_cont)).mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
    have hball_re : ∀ {y : ℂ}, y ∈ Metric.ball y₀ c → c ≤ y.re ∧ y.re ≤ R := fun {y} hy => by
      have hdist : ‖y - y₀‖ < c := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hy
      have hre : y₀.re - y.re ≤ c := (le_abs_self _).trans ((Complex.abs_re_le_norm (y₀ - y)).trans (by rw [norm_sub_rev]; exact hdist.le))
      exact ⟨by dsimp [c] at hre ⊢; linarith, (Complex.re_le_norm y).trans (by rw [show y = (y - y₀) + y₀ by ring]; exact (norm_add_le _ _).trans (by dsimp [R]; linarith))⟩
    have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (Metric.ball_mem_nhds y₀ hc)
      (Eventually.of_forall hmeas_fun) (hint_all y₀ hy₀_pos.le) hF'_meas (ae_of_all _ fun u y hy => by
        obtain ⟨hc_le, hR_le⟩ := hball_re hy; dsimp [F', bound']
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_exp,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        split_ifs with hu
        · have h1 : |u| * Real.exp (y.re * u) ≤ c⁻¹ := (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hc_le hu.le)) (abs_nonneg u)).trans (mul_exp_le_inv_of_nonpos hc hu.le)
          exact (mul_le_mul_of_nonneg_right h1 (abs_nonneg (X u))).trans_eq' (by ring)
        · have hu0 : 0 ≤ u := not_lt.mp hu; rw [abs_of_nonneg hu0]
          have h1 : u * |X u| ≤ Real.exp u * (C_t * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) := mul_le_mul (by linarith [Real.add_one_le_exp u]) (hX_tail u hu0) (abs_nonneg _) (Real.exp_pos _).le
          exact (mul_le_mul h1 (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hR_le hu0)) (Real.exp_pos _).le (by positivity)).trans_eq
            (by rw [show Real.exp u * (C_t * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ))) * Real.exp (R * u) = C_t * (Real.exp u * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (R * u)) by ring, ← Real.exp_add, ← Real.exp_add]; congr 2; ring))
      hbound'_int (ae_of_all _ fun u y _ => (((hasDerivAt_id y).mul_const (u : ℂ)).cexp.const_mul (X u : ℂ)).congr_deriv (by dsimp [F']; ring))
    exact ((((differentiableAt_id.pow 3).neg.div_const 12).cexp.const_mul (ceK : ℂ)).mul hd.2.differentiableAt).differentiableWithinAt
  · have hbi : 0 ≤ ∫ u : ℝ, bound 1 u := integral_nonneg fun u => by dsimp [bound]; split_ifs <;> positivity
    refine ⟨ceK * Real.exp 1 * (∫ u : ℝ, bound 1 u) + 1, by linarith [mul_nonneg (mul_nonneg ceK_pos.le (Real.exp_pos 1).le) hbi], fun {y} hy0 hy1 => ?_⟩
    have hexp : ‖Complex.exp (-(y ^ 3) / 12)‖ ≤ Real.exp 1 := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      exact (Complex.re_le_norm _).trans (by rw [norm_div, norm_neg, norm_pow, norm_ofNat]; have : ‖y‖ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hy1 3; linarith)
    have hint_bd := norm_integral_le_of_norm_le (hbound_int zero_le_one) (ae_of_all _ fun u => hdom_piece y hy0 ((Complex.re_le_norm y).trans hy1) u)
    unfold airyTwistedLaplaceC; rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceK_pos]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hexp ceK_pos.le) hint_bd (norm_nonneg _) (mul_nonneg ceK_pos.le (Real.exp_pos 1).le)).trans (le_add_of_nonneg_right zero_le_one)

lemma integrable_const_mul_ofReal {b : ℝ} {X : ℝ → ℝ} {y : ℂ} (hX : Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ)))) :
    Integrable (fun u : ℝ => ((b * X u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) := (hX.const_mul (b : ℂ)).congr (ae_of_all _ fun u => by push_cast; ring)

lemma airyTwistedLaplaceC_sub {X Y : ℝ → ℝ} {y : ℂ} (hX : Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ))))
    (hY : Integrable (fun u : ℝ => (Y u : ℂ) * Complex.exp (y * (u : ℂ)))) :
    airyTwistedLaplaceC (fun u => X u - Y u) y = airyTwistedLaplaceC X y - airyTwistedLaplaceC Y y := by
  unfold airyTwistedLaplaceC; rw [show (fun u : ℝ => ((X u - Y u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) =
    fun u => (X u : ℂ) * Complex.exp (y * (u : ℂ)) - (Y u : ℂ) * Complex.exp (y * (u : ℂ)) from funext fun u => by push_cast; ring, integral_sub hX hY, mul_sub]

lemma airyTwistedLaplaceC_add {X Y : ℝ → ℝ} {y : ℂ} (hX : Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ))))
    (hY : Integrable (fun u : ℝ => (Y u : ℂ) * Complex.exp (y * (u : ℂ)))) :
    airyTwistedLaplaceC (fun u => X u + Y u) y = airyTwistedLaplaceC X y + airyTwistedLaplaceC Y y := by
  unfold airyTwistedLaplaceC; rw [show (fun u : ℝ => ((X u + Y u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) =
    fun u => (X u : ℂ) * Complex.exp (y * (u : ℂ)) + (Y u : ℂ) * Complex.exp (y * (u : ℂ)) from funext fun u => by push_cast; ring, integral_add hX hY, mul_add]

lemma airyTwistedLaplaceC_const_mul (b : ℝ) (X : ℝ → ℝ) (y : ℂ) :
    airyTwistedLaplaceC (fun u => b * X u) y = (b : ℂ) * airyTwistedLaplaceC X y := by
  unfold airyTwistedLaplaceC; rw [show (fun u : ℝ => ((b * X u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) =
    fun u => (b : ℂ) * ((X u : ℂ) * Complex.exp (y * (u : ℂ))) from funext fun u => by push_cast; ring, integral_const_mul]; ring

lemma rhp_extend_to_boundary {F : ℂ → ℂ} {p C : ℝ} (hcont : ContinuousOn F {y : ℂ | 0 ≤ y.re})
    (hbd : ∀ w : ℂ, 0 < w.re → ‖F ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-p)) :
    ∀ w : ℂ, 0 ≤ w.re → ‖F ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-p) := fun w hw => by
  rcases hw.lt_or_eq with hw_pos | hw_zero
  · exact hbd w hw_pos
  · let g : ℝ → ℂ := fun δ => w + (δ : ℂ)
    have hF_cont : ContinuousWithinAt (fun z : ℂ => F ((ceCs : ℂ) * z)) {z : ℂ | 0 ≤ z.re} w :=
      (hcont ((ceCs : ℂ) * w) (by change 0 ≤ ((ceCs : ℂ) * w).re; simp [Complex.mul_re, ← hw_zero])).comp
        (continuous_const.mul continuous_id).continuousAt.continuousWithinAt fun z hz => by change 0 ≤ ((ceCs : ℂ) * z).re; simp [Complex.mul_re, mul_nonneg ceCs_pos.le hz]
    have hg_tend : Tendsto g (nhdsWithin 0 (Ioi 0)) (𝓝 w) := by
      have hc : Continuous g := continuous_const.add Complex.continuous_ofReal
      simpa [g] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hLHS : Tendsto (fun δ : ℝ => ‖F ((ceCs : ℂ) * g δ)‖) (nhdsWithin 0 (Ioi 0)) (𝓝 ‖F ((ceCs : ℂ) * w)‖) :=
      (hF_cont.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hg_tend
        (eventually_of_mem self_mem_nhdsWithin fun δ (hδ : 0 < δ) => by change 0 ≤ (g δ).re; simp [g, ← hw_zero, hδ.le]))).norm
    have h1w : 1 + w ≠ 0 := fun h => by have := congrArg Complex.re h; simp [← hw_zero] at this
    have hRHS : Tendsto (fun δ : ℝ => C * ‖1 + g δ‖ ^ (-p)) (nhdsWithin 0 (Ioi 0)) (𝓝 (C * ‖1 + w‖ ^ (-p))) := by
      have hg1 : ContinuousAt (fun δ : ℝ => C * ‖1 + g δ‖ ^ (-p)) 0 := continuousAt_const.mul ((ContinuousAt.norm (by fun_prop)).rpow continuousAt_const (Or.inl (by simpa [g] using h1w)))
      simpa [g] using hg1.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto_of_tendsto hLHS hRHS (eventually_of_mem self_mem_nhdsWithin fun δ (hδ : 0 < δ) => hbd (g δ) (by simp [g, ← hw_zero, hδ]))

lemma rhp_bound_of_unit_and_tail {F : ℂ → ℂ} {p C_lo C_hi : ℝ} (hp : 0 ≤ p) (hC_lo : 0 < C_lo)
    (hlo : ∀ y : ℂ, 0 < y.re → ‖y‖ ≤ 1 → ‖F y‖ ≤ C_lo) (hhi : ∀ y : ℂ, 0 < y.re → 1 ≤ ‖y‖ → ‖F y‖ ≤ C_hi * ‖y‖ ^ (-p)) :
    ∃ C > 0, ∀ w : ℂ, 0 < w.re → ‖F ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-p) := by
  let M_cs : ℝ := 1 + ceCs⁻¹; have hM_cs : 1 ≤ M_cs := by dsimp [M_cs]; linarith [inv_pos.mpr ceCs_pos]
  let K : ℝ := max C_lo C_hi * M_cs ^ p
  refine ⟨K, mul_pos (lt_of_lt_of_le hC_lo (le_max_left _ _)) (Real.rpow_pos_of_pos (by linarith) _), fun w hw => ?_⟩
  let y : ℂ := (ceCs : ℂ) * w; have hy_re : 0 < y.re := by dsimp [y]; simp [Complex.mul_re, mul_pos ceCs_pos hw]
  have hnorm_y : ‖y‖ = ceCs * ‖w‖ := by dsimp [y]; rw [norm_mul, Complex.norm_of_nonneg ceCs_pos.le]
  have h1w_pos : 0 < ‖1 + w‖ := norm_pos_iff.mpr fun h => by have := congrArg Complex.re h; simp at this; linarith
  by_cases hy1 : ‖y‖ ≤ 1
  · have hw_le : ‖w‖ ≤ ceCs⁻¹ := by nlinarith [inv_pos.mpr ceCs_pos, mul_inv_cancel₀ ceCs_pos.ne']
    have h1w_le : ‖1 + w‖ ≤ M_cs := (norm_add_le 1 w).trans (by rw [norm_one]; dsimp [M_cs]; linarith)
    have hmul : (1 : ℝ) ≤ M_cs ^ p * ‖1 + w‖ ^ (-p) := (by rw [← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero] : (1 : ℝ) = M_cs ^ p * M_cs ^ (-p)).trans_le
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos h1w_pos h1w_le (by linarith)) (by positivity))
    exact ((hlo y hy_re hy1).trans (le_max_left _ _)).trans ((le_mul_of_one_le_right (by positivity) hmul).trans_eq (by dsimp [K]; ring))
  · push Not at hy1
    have hw_eq : ‖w‖ = ceCs⁻¹ * ‖y‖ := by rw [hnorm_y]; field_simp [ceCs_pos.ne']
    have h1w_le : ‖1 + w‖ ≤ M_cs * ‖y‖ := (norm_add_le 1 w).trans (by rw [norm_one, hw_eq]; dsimp [M_cs]; nlinarith [norm_nonneg y])
    have hrpow := Real.rpow_le_rpow_of_nonpos h1w_pos h1w_le (by linarith : -p ≤ 0); rw [Real.mul_rpow (by linarith) (by linarith)] at hrpow
    have hrpow_y : ‖y‖ ^ (-p) ≤ M_cs ^ p * ‖1 + w‖ ^ (-p) :=
      (by rw [← mul_assoc, ← Real.rpow_add (by linarith), add_neg_cancel, Real.rpow_zero, one_mul] : ‖y‖ ^ (-p) = M_cs ^ p * (M_cs ^ (-p) * ‖y‖ ^ (-p))).trans_le
        (mul_le_mul_of_nonneg_left hrpow (by positivity))
    exact ((hhi y hy_re hy1.le).trans (mul_le_mul_of_nonneg_right (le_max_right C_lo C_hi) (by positivity))).trans
      ((mul_le_mul_of_nonneg_left hrpow_y (by positivity)).trans_eq (by dsimp [K]; ring))

private lemma cauchy_dual_deriv_bound_of_rhp {X : ℝ → ℝ} {p C_rhp : ℝ} (hp : 0 ≤ p) (hC_rhp : 0 < C_rhp)
    (hdiff : DifferentiableOn ℂ (airyTwistedLaplaceC X) {y : ℂ | 0 < y.re})
    (hrhp : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ C_rhp * ‖1 + w‖ ^ (-p)) :
    ∀ j : ℕ, ∃ C_j > 0, ∀ {c : ℝ}, 2 ≤ c → ∀ τ : ℝ,
      ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC X (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤ C_j * c ^ (-p / 3) * (1 + τ ^ 2) ^ (-p / 2) := fun j => by
  refine ⟨(j.factorial : ℝ) * (C_rhp * (2 : ℝ) ^ p) / (1 / 2 : ℝ) ^ j, by positivity, fun {c} hc τ => ?_⟩
  have hc_pos : 0 < c := by linarith
  have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  let U : Set ℂ := {ω : ℂ | -(3 / 4 : ℝ) < ω.im}
  let F : ℂ → ℂ := fun ω => airyTwistedLaplaceC X (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * ω))
  have hF_re : ∀ ω ∈ U, 0 < (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * ω)).re := fun ω hω => by
    rw [show (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * ω)).re = (ceCs * c ^ (1 / 3 : ℝ)) * (1 + ω.im) by simp [Complex.mul_re]]
    exact mul_pos (mul_pos ceCs_pos hc13_pos) (by linarith [show -(3 / 4 : ℝ) < ω.im from hω])
  have hball : ∀ τ₀ : ℝ, Metric.closedBall (τ₀ : ℂ) (1 / 2) ⊆ U := by
    intro τ₀ ω hω
    have him : |ω.im| ≤ 1 / 2 := by simpa [Complex.sub_im, Complex.ofReal_im, sub_zero] using (Complex.abs_im_le_norm (ω - (τ₀ : ℂ))).trans (by simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hω)
    change -(3 / 4 : ℝ) < ω.im; linarith [(abs_le.mp him).1]
  let B : ℝ → ℝ := fun τ₀ => C_rhp * (2 : ℝ) ^ p * c ^ (-p / 3) * (1 + τ₀ ^ 2) ^ (-p / 2)
  have hB : ∀ τ₀ : ℝ, ∀ ω ∈ Metric.sphere (τ₀ : ℂ) (1 / 2), ‖F ω‖ ≤ B τ₀ := fun τ₀ ω hω => by
    let w : ℂ := ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * ω)
    have hw_re : 0 ≤ w.re := by
      have him : -(3 / 4 : ℝ) < ω.im := hball τ₀ (Metric.sphere_subset_closedBall hω)
      rw [show w.re = c ^ (1 / 3 : ℝ) * (1 + ω.im) by dsimp [w]; simp [Complex.mul_re]]; exact mul_nonneg hc13_pos.le (by linarith)
    have hnorm_ge : (c ^ (1 / 3 : ℝ) / 2) * Real.sqrt (1 + τ₀ ^ 2) ≤ ‖1 + w‖ :=
      (by ring_nf : (c ^ (1 / 3 : ℝ) / 2) * Real.sqrt (1 + τ₀ ^ 2) = c ^ (1 / 3 : ℝ) * (Real.sqrt (1 + τ₀ ^ 2) / 2)).le.trans
        ((mul_le_mul_of_nonneg_left (norm_one_sub_I_mul_ge' (by simpa [Complex.dist_eq] using (Metric.mem_sphere.mp hω).le)) hc13_pos.le).trans
          ((by dsimp [w]; rw [norm_mul, Complex.norm_of_nonneg hc13_pos.le] : c ^ (1 / 3 : ℝ) * ‖1 - Complex.I * ω‖ = ‖w‖).le.trans (norm_le_one_add_of_re_nonneg hw_re)))
    have hrpow_simp : ((c ^ (1 / 3 : ℝ) / 2) * Real.sqrt (1 + τ₀ ^ 2)) ^ (-p) = (2 : ℝ) ^ p * c ^ (-p / 3) * (1 + τ₀ ^ 2) ^ (-p / 2) := by
      rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), Real.div_rpow hc13_pos.le (by norm_num), ← Real.rpow_mul hc_pos.le,
        Real.rpow_neg (by norm_num) p, div_inv_eq_mul, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + τ₀ ^ 2)]; congr 1 <;> [ring_nf; ring_nf]
    rw [show F ω = airyTwistedLaplaceC X ((ceCs : ℂ) * w) by dsimp [F, w]; congr 1; push_cast; ring]
    exact (hrhp w hw_re).trans ((mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_nonpos (by positivity) hnorm_ge (by linarith)).trans_eq hrpow_simp) hC_rhp.le).trans_eq (by dsimp [B]; ring))
  exact ((holomorphic_real_contDiff_and_cauchy (isOpen_lt continuous_const Complex.continuous_im) (hdiff.comp (by fun_prop) hF_re)
    (fun t => by change -(3 / 4 : ℝ) < ((t : ℂ)).im; simp) (by norm_num) hball hB).2 j τ).trans_eq (by dsimp [B]; ring)

/-! ### Section 1: Airy polynomial derivatives, super-exponential decay, and boundary values -/

private noncomputable def airyPolyPair : ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (1, 0)
  | n + 1 => let pq := airyPolyPair n; (pq.1.derivative + Polynomial.X * pq.2, pq.2.derivative + pq.1)

private lemma iteratedDeriv_airyAi_eq (n : ℕ) (x : ℝ) : iteratedDeriv n airyAi x = (airyPolyPair n).1.eval x * airyAi x + (airyPolyPair n).2.eval x * airyAi' x := by
  induction n generalizing x with
  | zero => simp [airyPolyPair]
  | succ k ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv k airyAi = fun t => (airyPolyPair k).1.eval t * airyAi t + (airyPolyPair k).2.eval t * airyAi' t from funext ih]
    exact ((((airyPolyPair k).1.hasDerivAt x).mul (hasDerivAt_airyAi x) |>.add (((airyPolyPair k).2.hasDerivAt x).mul (hasDerivAt_airyAi' x))).congr_deriv
      (by dsimp only [airyPolyPair]; simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]; ring)).deriv

private lemma iteratedDeriv_airyAi_shift (z : ℝ) (n : ℕ) (t : ℝ) : iteratedDeriv n (fun s => airyAi (z + s)) t = iteratedDeriv n airyAi (z + t) := by
  induction n generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun s => airyAi (z + s)) = fun s => iteratedDeriv k airyAi (z + s) from funext ih, iteratedDeriv_succ]
    simpa [Function.comp_def] using (((contDiff_airyAi.differentiable_iteratedDeriv k (by simp)).differentiableAt).hasDerivAt.comp t ((hasDerivAt_id t).const_add z)).deriv

private lemma continuous_airyAi' : Continuous airyAi' := by
  have heq : iteratedDeriv 1 airyAi = airyAi' := funext fun x => by rw [iteratedDeriv_one, deriv_airyAi]
  rw [← heq]; exact contDiff_airyAi.continuous_iteratedDeriv 1 (by simp)

lemma airyAi_and_deriv_rpow32_decay :
    ∃ C > 0, ∀ x : ℝ, 0 ≤ x → |airyAi x| ≤ C * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) ∧ |airyAi' x| ≤ C * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := by
  obtain ⟨M₀_raw, hbd₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_airyAi.abs.add continuous_airyAi'.abs).continuousOn : ContinuousOn (fun x => |airyAi x| + |airyAi' x|) (Icc 0 1))
  let M₀ := max M₀_raw 1; let C : ℝ := max (M₀ * Real.exp 1) (1 + 6 * (Real.sqrt π + 1) / (2 * π))
  refine ⟨C, lt_of_lt_of_le (by positivity) (le_max_left _ _), fun x hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · have hsum_le : |airyAi x| + |airyAi' x| ≤ M₀ := by have h := hbd₀ x ⟨hx, hx1⟩; dsimp at h; rw [abs_of_nonneg (by positivity)] at h; exact h.trans (le_max_left _ _)
    have h1_le : 1 ≤ Real.exp 1 * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) :=
      (by rw [← Real.exp_add]; norm_num : (1 : ℝ) = Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ))).trans_le
        (mul_le_mul (Real.exp_le_exp.mpr (by norm_num)) (Real.exp_le_exp.mpr (by linarith [Real.rpow_le_one hx hx1 (by norm_num : (0 : ℝ) ≤ 3 / 2)])) (Real.exp_pos _).le (Real.exp_pos _).le)
    have hC_mul : |airyAi x| + |airyAi' x| ≤ C * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := calc
      |airyAi x| + |airyAi' x| ≤ M₀ * (Real.exp 1 * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ))) := hsum_le.trans (le_mul_of_one_le_right (by positivity) h1_le)
      _ = (M₀ * Real.exp 1) * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := by ring
      _ ≤ C * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans hC_mul, (le_add_of_nonneg_left (abs_nonneg _)).trans hC_mul⟩
  · push Not at hx1
    have h23 : Real.exp (-(2 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) = Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) * Real.exp (-((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ))) := by rw [← Real.exp_add]; ring_nf
    have hsqrt_pi : 1 ≤ Real.sqrt π := Real.one_le_sqrt.mpr (by linarith [Real.two_le_pi])
    have hpre : 1 / (2 * Real.sqrt π) * x ^ (-(1 / 4 : ℝ)) ≤ 1 :=
      (mul_le_mul (div_le_one_of_le₀ (by linarith) (by positivity)) (Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)) (by positivity) zero_le_one).trans_eq (one_mul 1)
    have hAi : |airyAi x| ≤ C * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := calc
      |airyAi x| ≤ 1 / (2 * Real.sqrt π) * x ^ (-(1 / 4 : ℝ)) * Real.exp (-(2 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) := airyAi_abs_le (by linarith)
      _ ≤ 1 * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := mul_le_mul hpre (Real.exp_le_exp.mpr (by linarith [Real.rpow_nonneg hx (3 / 2 : ℝ)])) (Real.exp_pos _).le zero_le_one
      _ ≤ C * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right
          ((le_add_of_nonneg_right (by positivity) : (1 : ℝ) ≤ 1 + 6 * (Real.sqrt π + 1) / (2 * π)).trans (le_max_right (M₀ * Real.exp 1) _)) (Real.exp_pos (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ))).le
    have h14_exp : x ^ (3 / 2 : ℝ) ≤ 6 * Real.exp ((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ)) := by linarith [Real.add_one_le_exp ((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ))]
    have h1_exp : (1 : ℝ) ≤ 6 * Real.exp ((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ)) := by linarith [Real.one_le_exp (show (0 : ℝ) ≤ (1 / 6 : ℝ) * x ^ (3 / 2 : ℝ) by positivity)]
    have hbrack : Real.sqrt π * x ^ (1 / 4 : ℝ) + x ^ (-(1 / 2 : ℝ)) ≤ 6 * (Real.sqrt π + 1) * Real.exp ((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ)) :=
      (add_le_add (mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)).trans h14_exp) (Real.sqrt_nonneg _))
        ((Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)).trans h1_exp)).trans_eq (by ring)
    have hexp_c : Real.exp ((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ)) * Real.exp (-((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ))) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hAi' : |airyAi' x| ≤ C * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := calc
      |airyAi' x| ≤ 1 / (2 * π) * (Real.sqrt π * x ^ (1 / 4 : ℝ) + x ^ (-(1 / 2 : ℝ))) * Real.exp (-(2 / 3 : ℝ) * x ^ (3 / 2 : ℝ)) := airyAi'_abs_le (by linarith)
      _ ≤ 1 / (2 * π) * (6 * (Real.sqrt π + 1) * Real.exp ((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ))) * (Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) * Real.exp (-((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ)))) := by rw [h23]; gcongr
      _ = (6 * (Real.sqrt π + 1) / (2 * π)) * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := by
          calc _ = (6 * (Real.sqrt π + 1) / (2 * π)) * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) * (Real.exp ((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ)) * Real.exp (-((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ)))) := by ring
            _ = _ := by rw [hexp_c, mul_one]
      _ ≤ C * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left zero_le_one).trans (le_max_right (M₀ * Real.exp 1) _)) (Real.exp_pos _).le
    exact ⟨hAi, hAi'⟩

private lemma airyAi_and_deriv_exp_decay (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C > 0, ∀ x : ℝ, 0 ≤ x → (1 + x) ^ k * (|airyAi x| + |airyAi' x|) ≤ C * Real.exp (-c * x) := by
  obtain ⟨C₀, _, hbd⟩ := airyAi_and_deriv_rpow32_decay; let A : ℝ := (c + 2) * ((c + 2) / (1 / 2 : ℝ)) ^ 2
  refine ⟨2 * C₀ * Real.exp A * (k.factorial : ℝ) * Real.exp 1, by positivity, fun x hx => ?_⟩
  have h_rpow : Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) ≤ Real.exp A * Real.exp (-(c + 1) * x) := by
    have h1 := neg_c_rpow32_add_le (by norm_num : (0 : ℝ) < 1 / 2) (by positivity : 0 ≤ c + 1) hx
    calc Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) = Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ) + (c + 1) * x) * Real.exp (-(c + 1) * x) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (A - x) * Real.exp (-(c + 1) * x) := by gcongr; dsimp [A]; linarith
      _ ≤ Real.exp A * Real.exp (-(c + 1) * x) := by gcongr; linarith
  have h_poly : (1 + x) ^ k * Real.exp (-x) ≤ (k.factorial : ℝ) * Real.exp 1 :=
    (mul_le_mul_of_nonneg_right ((div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp (Real.pow_div_factorial_le_exp (1 + x) (by linarith) k)) (Real.exp_pos _).le).trans_eq
      (by rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]; ring_nf)
  have hsum := (by have := hbd x hx; linarith : |airyAi x| + |airyAi' x| ≤ 2 * C₀ * Real.exp (-(1 / 2 : ℝ) * x ^ (3 / 2 : ℝ))).trans (mul_le_mul_of_nonneg_left h_rpow (by positivity))
  calc (1 + x) ^ k * (|airyAi x| + |airyAi' x|) ≤ 2 * C₀ * Real.exp A * ((1 + x) ^ k * Real.exp (-x)) * Real.exp (-c * x) :=
        (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by rw [show Real.exp (-(c + 1) * x) = Real.exp (-x) * Real.exp (-c * x) by rw [← Real.exp_add]; ring_nf]; ring)
    _ ≤ (2 * C₀ * Real.exp A * (k.factorial : ℝ) * Real.exp 1) * Real.exp (-c * x) :=
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_poly (by positivity)) (Real.exp_pos _).le).trans_eq (by ring)

private lemma poly_eval_abs_le (P : Polynomial ℝ) : ∃ M > 0, ∀ x : ℝ, |P.eval x| ≤ M * (1 + |x|) ^ P.natDegree := by
  let M : ℝ := ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| + 1
  refine ⟨M, by positivity, fun x => ?_⟩; rw [Polynomial.eval_eq_sum_range]
  calc |∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * x ^ k| ≤ ∑ k ∈ Finset.range (P.natDegree + 1), |P.coeff k| * (1 + |x|) ^ P.natDegree :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => by
          rw [abs_mul, abs_pow]; exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg x]) k).trans
            (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))) (abs_nonneg _))
    _ ≤ M * (1 + |x|) ^ P.natDegree := by rw [← Finset.sum_mul]; gcongr; dsimp [M]; linarith

private lemma iteratedDeriv_airyAi_shift_decay (z : ℝ) (n k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n (fun s => airyAi (z + s)) t‖ ≤ C * Real.exp (-c * t) := by
  let P := (airyPolyPair n).1; let Q := (airyPolyPair n).2; obtain ⟨MP, hMP, hP⟩ := poly_eval_abs_le P; obtain ⟨MQ, _, hQ⟩ := poly_eval_abs_le Q
  let d : ℕ := max P.natDegree Q.natDegree; let M₀ : ℝ := max MP MQ; obtain ⟨C₁, _, hexp₁⟩ := airyAi_and_deriv_exp_decay (k + d) hc
  let R₀ : ℝ := max 0 (-z)
  have hcont_t : Continuous (fun t : ℝ => (1 + t) ^ k * ‖iteratedDeriv n (fun s => airyAi (z + s)) t‖ * Real.exp (c * t)) :=
    (((continuous_const.add continuous_id).pow k).mul (((contDiff_airyAi.comp (contDiff_const.add contDiff_id)).continuous_iteratedDeriv n (by simp)).norm)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  obtain ⟨C₀_raw, hbd₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont_t.continuousOn : ContinuousOn _ (Icc 0 R₀))
  let C₀ : ℝ := max C₀_raw 1; let C_pos : ℝ := M₀ * (1 + |z|) ^ k * C₁ * Real.exp (-c * z)
  refine ⟨max C₀ C_pos + 1, by positivity, fun t ht => ?_⟩
  by_cases ht_le : t ≤ R₀
  · have hval : (1 + t) ^ k * ‖iteratedDeriv n (fun s => airyAi (z + s)) t‖ * Real.exp (c * t) ≤ C₀ := by
      have h := hbd₀ t ⟨ht, ht_le⟩; rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h; exact h.trans (le_max_left _ _)
    exact ((by rw [mul_assoc, ← Real.exp_add]; simp : (1 + t) ^ k * ‖iteratedDeriv n (fun s => airyAi (z + s)) t‖ =
      ((1 + t) ^ k * ‖iteratedDeriv n (fun s => airyAi (z + s)) t‖ * Real.exp (c * t)) * Real.exp (-c * t)).trans_le
      (mul_le_mul_of_nonneg_right hval (Real.exp_pos _).le)).trans (by gcongr; linarith [le_max_left C₀ C_pos])
  · push Not at ht_le; have hm_le : -z ≤ R₀ := le_max_right 0 (-z); have hzt_nn : 0 ≤ z + t := by linarith
    rw [iteratedDeriv_airyAi_shift z n t, iteratedDeriv_airyAi_eq n (z + t), Real.norm_eq_abs]
    have hP' : |P.eval (z + t)| ≤ M₀ * (1 + (z + t)) ^ d := (hP (z + t)).trans (by rw [abs_of_nonneg hzt_nn]; exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ (by linarith) (le_max_left _ _)) (by positivity) (by positivity))
    have hQ' : |Q.eval (z + t)| ≤ M₀ * (1 + (z + t)) ^ d := (hQ (z + t)).trans (by rw [abs_of_nonneg hzt_nn]; exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ (by linarith) (le_max_right _ _)) (by positivity) (by positivity))
    have hcomb : |P.eval (z + t) * airyAi (z + t) + Q.eval (z + t) * airyAi' (z + t)| ≤ M₀ * (1 + (z + t)) ^ d * (|airyAi (z + t)| + |airyAi' (z + t)|) :=
      ((by rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _ : _ ≤ |P.eval (z + t)| * |airyAi (z + t)| + |Q.eval (z + t)| * |airyAi' (z + t)|).trans
        (add_le_add (mul_le_mul_of_nonneg_right hP' (abs_nonneg _)) (mul_le_mul_of_nonneg_right hQ' (abs_nonneg _)))).trans_eq (by ring)
    have h1tp_le : (1 + t) ^ k ≤ (1 + |z|) ^ k * (1 + (z + t)) ^ k := by simpa [mul_pow] using pow_le_pow_left₀ (by linarith) (by nlinarith [abs_nonneg z, neg_le_abs z] : 1 + t ≤ (1 + |z|) * (1 + (z + t))) k
    have hM₀_nn : 0 ≤ M₀ := hMP.le.trans (le_max_left _ _)
    calc (1 + t) ^ k * |P.eval (z + t) * airyAi (z + t) + Q.eval (z + t) * airyAi' (z + t)|
        ≤ M₀ * (1 + |z|) ^ k * ((1 + (z + t)) ^ (k + d) * (|airyAi (z + t)| + |airyAi' (z + t)|)) := (mul_le_mul h1tp_le hcomb (abs_nonneg _) (by positivity)).trans_eq (by rw [pow_add]; ring)
      _ ≤ C_pos * Real.exp (-c * t) := (mul_le_mul_of_nonneg_left (hexp₁ (z + t) hzt_nn) (by positivity)).trans_eq (by dsimp [C_pos]; rw [show -c * (z + t) = -c * z + -c * t by ring, Real.exp_add]; ring)
      _ ≤ (max C₀ C_pos + 1) * Real.exp (-c * t) := by gcongr; linarith [le_max_right C₀ C_pos]

lemma contDiff_dirichletPhi0 : ContDiff ℝ ⊤ (dirichletPhi 0) := (contDiff_airyAi.comp (contDiff_id.add contDiff_const)).div_const _

lemma contDiff_airyRatio (z : ℝ) : ContDiff ℝ ⊤ (airyRatio z) := (contDiff_airyAi.comp (contDiff_const.add contDiff_id)).div_const _

private lemma iteratedDeriv_shift_div_eq (z d : ℝ) (n : ℕ) (t : ℝ) : iteratedDeriv n (fun s => airyAi (z + s) / d) t = iteratedDeriv n (fun s => airyAi (z + s)) t / d := by
  rw [show (fun s => airyAi (z + s) / d) = fun s => d⁻¹ * airyAi (z + s) from funext fun _ => by ring, iteratedDeriv_const_mul_field]; ring

lemma airyAi_shift_div_decay (z : ℝ) {d : ℝ} (hd : d ≠ 0) (n k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n (fun s => airyAi (z + s) / d) t‖ ≤ C * Real.exp (-c * t) := by
  obtain ⟨C, hC, hbd⟩ := iteratedDeriv_airyAi_shift_decay z n k hc; refine ⟨C * |d|⁻¹, mul_pos hC (inv_pos.mpr (abs_pos.mpr hd)), fun t ht => ?_⟩
  rw [iteratedDeriv_shift_div_eq, norm_div, Real.norm_eq_abs, div_eq_mul_inv]
  exact ((by ring : (1 + t) ^ k * (‖iteratedDeriv n (fun s => airyAi (z + s)) t‖ * |d|⁻¹) = ((1 + t) ^ k * ‖iteratedDeriv n (fun s => airyAi (z + s)) t‖) * |d|⁻¹).trans_le
    (mul_le_mul_of_nonneg_right (hbd t ht) (by positivity))).trans_eq (by ring)

lemma dirichletPhi0_vals_at_zero :
    dirichletPhi 0 0 = 0 ∧ deriv (dirichletPhi 0) 0 = 1 ∧ iteratedDeriv 2 (dirichletPhi 0) 0 = 0 ∧ iteratedDeriv 3 (dirichletPhi 0) 0 = airyZero 1 := by
  have hfn : dirichletPhi 0 = fun s => airyAi (airyZero 1 + s) / airyAi' (airyZero 1) := by ext s; unfold dirichletPhi; ring_nf
  have hne : airyAi' (airyZero 1) ≠ 0 := airyAi'_first_pos.ne'
  have heq : ∀ n, iteratedDeriv n (dirichletPhi 0) 0 = ((airyPolyPair n).2.eval (airyZero 1) * airyAi' (airyZero 1)) / airyAi' (airyZero 1) := fun n => by
    rw [hfn, iteratedDeriv_shift_div_eq, iteratedDeriv_airyAi_shift, add_zero, iteratedDeriv_airyAi_eq, airyAi_airyZero 1, mul_zero, zero_add]
  refine ⟨by simpa [airyPolyPair] using heq 0, by rw [← iteratedDeriv_one]; simpa [airyPolyPair, hne] using heq 1, by simpa [airyPolyPair] using heq 2, ?_⟩
  have h3 := heq 3; simp only [airyPolyPair, Polynomial.derivative_one, Polynomial.derivative_zero, zero_add, mul_zero, Polynomial.derivative_X, Polynomial.eval_X, mul_one, add_zero] at h3
  rw [h3]; field_simp [hne]

private lemma airyRatio_vals_at_zero :
    airyRatio airyDerivFirstZero 0 = 1 ∧ deriv (airyRatio airyDerivFirstZero) 0 = 0 ∧ iteratedDeriv 2 (airyRatio airyDerivFirstZero) 0 = airyDerivFirstZero ∧ iteratedDeriv 3 (airyRatio airyDerivFirstZero) 0 = 1 := by
  set a := airyDerivFirstZero; have hne : airyAi a ≠ 0 := (airyAi_pos_of_gt airyDerivFirstZero_spec.1).ne'
  have heq : ∀ n, iteratedDeriv n (airyRatio a) 0 = ((airyPolyPair n).1.eval a * airyAi a) / airyAi a := fun n => by
    rw [show airyRatio a = fun s => airyAi (a + s) / airyAi a from rfl, iteratedDeriv_shift_div_eq, iteratedDeriv_airyAi_shift, add_zero, iteratedDeriv_airyAi_eq, airyDerivFirstZero_spec.2.2, mul_zero, add_zero]
  refine ⟨by simpa [airyPolyPair, hne] using heq 0, by rw [← iteratedDeriv_one]; simpa [airyPolyPair] using heq 1, ?_, ?_⟩
  · have h2 := heq 2; simp only [airyPolyPair, Polynomial.derivative_one, Polynomial.derivative_zero, zero_add, mul_zero, Polynomial.eval_X, mul_one, add_zero] at h2; rw [h2]; field_simp [hne]
  · have h3 := heq 3; simp only [airyPolyPair, Polynomial.derivative_one, Polynomial.derivative_zero, zero_add, mul_zero, Polynomial.derivative_X, Polynomial.eval_one, mul_one, add_zero] at h3; rw [h3]; field_simp [hne]

private lemma dslope_sq_tail_of_zero {g : ℝ → ℝ} {a C₀ : ℝ} (ha : a < 0) (hC₀ : 0 < C₀) (hga : g a = 0)
    (hg : ∀ u : ℝ, 0 ≤ u → |g u| ≤ C₀ * Real.exp (-(1 / 2 : ℝ) * u ^ (3 / 2 : ℝ))) :
    ∀ u : ℝ, 0 ≤ u → dslope g a u ^ 2 ≤ (C₀ ^ 2 / a ^ 2) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := fun u hu => by
  have h1 : dslope g a u ^ 2 ≤ |g u| ^ 2 / a ^ 2 := by
    rw [dslope_of_ne _ (by linarith), slope_def_field, hga, sub_zero, div_pow, ← sq_abs (g u)]; exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_neg ha) (by nlinarith)
  calc dslope g a u ^ 2 ≤ (C₀ * Real.exp (-(1 / 2 : ℝ) * u ^ (3 / 2 : ℝ))) ^ 2 / a ^ 2 := h1.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hg u hu) 2) (sq_nonneg _))
    _ = (C₀ ^ 2 / a ^ 2) * Real.exp (-u ^ (3 / 2 : ℝ)) := by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    _ ≤ (C₀ ^ 2 / a ^ 2) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [Real.rpow_nonneg hu (3 / 2 : ℝ)])) (by positivity)

lemma ceF1_tail_exp_rpow32 : ∃ C > 0, ∀ u : ℝ, 0 ≤ u → |ceF1 u| ≤ C * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := by
  obtain ⟨C₀, _, hbd⟩ := airyAi_and_deriv_rpow32_decay; have ha1_neg : 0 < -airyZero 1 := neg_pos.mpr (airyZero_neg 1)
  refine ⟨C₀ ^ 2 / (-airyZero 1), by positivity, fun u hu => ?_⟩
  have hF1 : |ceF1 u| ≤ |airyAi u| ^ 2 / (-airyZero 1) := by
    unfold ceF1; rw [dslope_of_ne _ (by linarith [airyZero_neg 1]), slope_def_field, airyAi_airyZero, sub_zero,
      show airyAi u * (airyAi u / (u - airyZero 1)) = airyAi u ^ 2 / (u - airyZero 1) by ring, abs_div, abs_sq, abs_of_pos (by linarith [airyZero_neg 1]), ← sq_abs (airyAi u)]
    exact div_le_div_of_nonneg_left (sq_nonneg _) ha1_neg (by linarith)
  calc |ceF1 u| ≤ (C₀ * Real.exp (-(1 / 2 : ℝ) * u ^ (3 / 2 : ℝ))) ^ 2 / (-airyZero 1) := hF1.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hbd u hu).1 2) ha1_neg.le)
    _ = (C₀ ^ 2 / (-airyZero 1)) * Real.exp (-u ^ (3 / 2 : ℝ)) := by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    _ ≤ (C₀ ^ 2 / (-airyZero 1)) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [Real.rpow_nonneg hu (3 / 2 : ℝ)])) (by positivity)

lemma ceG1_tail_exp_rpow32 : ∃ C > 0, ∀ u : ℝ, 0 ≤ u → |ceG1 (airyZero 1) u| ≤ C * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) :=
  let ⟨C₀, hC₀, hbd⟩ := airyAi_and_deriv_rpow32_decay
  ⟨C₀ ^ 2 / airyZero 1 ^ 2, div_pos (sq_pos_of_pos hC₀) (sq_pos_of_neg (airyZero_neg 1)), fun u hu => by
    rw [ceG1, abs_of_nonneg (sq_nonneg _)]; exact dslope_sq_tail_of_zero (airyZero_neg 1) hC₀ (airyAi_airyZero 1) (fun v hv => (hbd v hv).1) u hu⟩

lemma ceG1Deriv_tail_exp_rpow32 : ∃ C > 0, ∀ u : ℝ, 0 ≤ u → |ceG1Deriv airyDerivFirstZero u| ≤ C * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) :=
  let ⟨C₀, hC₀, hbd⟩ := airyAi_and_deriv_rpow32_decay
  ⟨C₀ ^ 2 / airyDerivFirstZero ^ 2, div_pos (sq_pos_of_pos hC₀) (sq_pos_of_neg airyDerivFirstZero_spec.2.1), fun u hu => by
    rw [ceG1Deriv, abs_of_nonneg (sq_nonneg _)]; exact dslope_sq_tail_of_zero airyDerivFirstZero_spec.2.1 hC₀ airyDerivFirstZero_spec.2.2 (fun v hv => (hbd v hv).2) u hu⟩

/-! ### Section 2: Exact Gaussian transforms on `{y : ℂ | 0 < y.re}` -/

private noncomputable def basisZero : ℕ → ℝ := fun k => if k = 0 then 1 else 0

private lemma basisZero_sq_summable : Summable (fun k : ℕ => basisZero k ^ 2) :=
  summable_of_ne_finset_zero (s := {0}) fun k hk => by simp [basisZero, show k ≠ 0 by simpa using hk]

private lemma dslope_airyAi_firstZero_eq_cohnL0 (u : ℝ) : dslope airyAi (airyZero 1) u = cohnL 0 u := by
  unfold cohnL; rw [show (0 + 1 : ℕ) = 1 from rfl]
  by_cases hu : u = airyZero 1
  · subst hu; simp [dslope_same, deriv_airyAi]
  · simp [hu, dslope_of_ne _ hu, slope_def_field, airyAi_airyZero]

private lemma cardinalHb_basisZero_eq (u : ℝ) : cardinalHb basisZero u = cohnL 0 u := by
  unfold cardinalHb; rw [tsum_eq_single 0 (fun n hn => by simp [basisZero, hn])]; simp [basisZero]

private lemma cohnL0_eq_integral_dirichletPhi0 (u : ℝ) : cohnL 0 u = ∫ t in Ioi (0 : ℝ), airyAi (u + t) * dirichletPhi 0 t := by
  rw [← cardinalHb_basisZero_eq u, cardinalHb_eq_reproducing basisZero_sq_summable u]
  refine integral_congr_ae ?_; filter_upwards [dirichletV_singleton_ae 0 1] with t ht
  rw [show (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) = basisZero from rfl] at ht; rw [ht, one_mul]

/-- Exact Gaussian transform of `f₁(u) = Ai(u)² / (u - a₁)` on `Re y > 0`. -/
theorem airyTwistedLaplaceC_ceF1_eq {y : ℂ} (hy : 0 < y.re) :
    airyTwistedLaplaceC ceF1 y = (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
      ∫ t in Ioi (0 : ℝ), (dirichletPhi 0 t : ℂ) * Complex.exp (-y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y)) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℂ := fun u t => ((airyAi u : ℂ) * (airyAi (u + t) : ℂ) * Complex.exp (y * (u : ℂ))) * (dirichletPhi 0 t : ℂ)
  obtain ⟨C_r, _, hAi_r⟩ := airyAi_and_deriv_rpow32_decay
  obtain ⟨C_phi, _, hPhi_bd⟩ := airyAi_shift_div_decay (airyZero 1) airyAi'_first_pos.ne' 0 0 (by norm_num : (0 : ℝ) < 1 / 4)
  let U : ℝ → ℝ := fun u => 3 * (if u < 0 then 3 * Real.exp (y.re * u) else C_r * Real.exp (-(1 / 2 : ℝ) * u ^ (3 / 2 : ℝ) + y.re * u))
  let T : ℝ → ℝ := fun t => C_phi * Real.exp (-(1 / 4 : ℝ) * t)
  have h_iio : IntegrableOn (fun u : ℝ => 3 * Real.exp (y.re * u)) (Iio 0) volume := by
    have h := (integrableOn_exp_mul_Ioi (by linarith : -y.re < 0) 0).const_mul 3
    have mp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage (MeasurableEquiv.neg ℝ).measurableEmbedding (f := fun u : ℝ => 3 * Real.exp (-y.re * u)) (s := Ioi 0)
    simpa [Function.comp_def, mul_neg] using mp.mpr h
  have hU_int : Integrable U volume := (integrable_if_neg_pos h_iio ((integrableOn_exp_neg_rpow32_add (by norm_num : (0 : ℝ) < 1 / 2) hy.le).const_mul C_r)).const_mul 3
  have hT_int : Integrable T ν := (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0).const_mul C_phi
  have hF_cont : Continuous (Function.uncurry F) := by
    unfold Function.uncurry F
    exact (((Complex.continuous_ofReal.comp (continuous_airyAi.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp (continuous_airyAi.comp (continuous_fst.add continuous_snd)))).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)))).mul
      (Complex.continuous_ofReal.comp (contDiff_dirichletPhi0.continuous.comp continuous_snd))
  have hF_prod_int : Integrable (Function.uncurry F) (volume.prod ν) := by
    refine integrable_prod_of_norm_le_mul hF_cont hU_int hT_int (ae_of_all _ fun u => ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h2 : |airyAi u| * Real.exp (y.re * u) ≤ if u < 0 then 3 * Real.exp (y.re * u) else C_r * Real.exp (-(1 / 2 : ℝ) * u ^ (3 / 2 : ℝ) + y.re * u) := by
      split_ifs with hu
      · exact mul_le_mul_of_nonneg_right (abs_airyAi_le_three u) (Real.exp_pos _).le
      · exact (mul_le_mul_of_nonneg_right (hAi_r u (not_lt.mp hu)).1 (Real.exp_pos _).le).trans_eq (by rw [mul_assoc, ← Real.exp_add])
    have hphi : |dirichletPhi 0 t| ≤ T t := by
      simpa [Real.norm_eq_abs, T, show (fun s => airyAi (airyZero 1 + s) / airyAi' (airyZero 1)) = dirichletPhi 0 by ext s; unfold dirichletPhi; ring_nf] using hPhi_bd t (mem_Ioi.mp ht).le
    rw [show ‖F u t‖ = |airyAi u| * Real.exp (y.re * u) * |airyAi (u + t)| * |dirichletPhi 0 t| by
      dsimp [F]; rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Complex.norm_exp,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]; ring]
    exact (mul_le_mul (mul_le_mul h2 (abs_airyAi_le_three (u + t)) (abs_nonneg _) (by split_ifs <;> positivity)) hphi (abs_nonneg _) (by split_ifs <;> positivity)).trans_eq (by dsimp [U, T]; ring)
  have h_u_eq : ∀ u : ℝ, (ceF1 u : ℂ) * Complex.exp (y * (u : ℂ)) = ∫ t : ℝ, F u t ∂ν := fun u => by
    rw [show ceF1 u = airyAi u * ∫ t in Ioi (0 : ℝ), airyAi (u + t) * dirichletPhi 0 t by unfold ceF1; rw [dslope_airyAi_firstZero_eq_cohnL0, cohnL0_eq_integral_dirichletPhi0], Complex.ofReal_mul]
    have hC1 : ((∫ t in Ioi (0 : ℝ), airyAi (u + t) * dirichletPhi 0 t : ℝ) : ℂ) = ∫ t in Ioi (0 : ℝ), (airyAi (u + t) : ℂ) * (dirichletPhi 0 t : ℂ) := by
      rw [← integral_complex_ofReal]; exact integral_congr_ae (ae_of_all _ fun t => by simp [Complex.ofReal_mul])
    rw [show (airyAi u : ℂ) * ((∫ t in Ioi (0 : ℝ), airyAi (u + t) * dirichletPhi 0 t : ℝ) : ℂ) * Complex.exp (y * (u : ℂ)) =
      ((airyAi u : ℂ) * Complex.exp (y * (u : ℂ))) * ∫ t : ℝ, (airyAi (u + t) : ℂ) * (dirichletPhi 0 t : ℂ) ∂ν by rw [hC1]; ring, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun t => by dsimp [F]; ring)
  unfold airyTwistedLaplaceC; rw [integral_congr_ae (ae_of_all _ h_u_eq), integral_integral_swap hF_prod_int]
  have h_inner : ∀ t : ℝ, ∫ u : ℝ, F u t = ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) * Complex.exp (y ^ 3 / 12) * ((dirichletPhi 0 t : ℂ) * Complex.exp (-y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y))) := fun t => by
    rw [show (fun u : ℝ => F u t) = fun u => ((airyAi (u + 0) : ℂ) * (airyAi (u + t) : ℂ) * Complex.exp (y * (u : ℂ))) * (dirichletPhi 0 t : ℂ) by ext u; simp [F],
      integral_mul_const, (airy_pair_laplace_eq 0 t hy).2, show Complex.exp (y ^ 3 / 12 - y * ((0 + t : ℝ) : ℂ) / 2 - ((0 - t : ℝ) : ℂ) ^ 2 / (4 * y)) =
        Complex.exp (y ^ 3 / 12) * Complex.exp (-y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y)) by rw [← Complex.exp_add]; congr 1; push_cast; ring]; ring
  rw [integral_congr_ae (ae_of_all _ h_inner), integral_const_mul]
  have hexp_cancel : Complex.exp (-(y ^ 3) / 12) * Complex.exp (y ^ 3 / 12) = 1 := by rw [← Complex.exp_add, show -(y ^ 3) / 12 + y ^ 3 / 12 = 0 by ring, Complex.exp_zero]
  rw [show (ceK : ℂ) * Complex.exp (-(y ^ 3) / 12) * (((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) * Complex.exp (y ^ 3 / 12) *
      ∫ t : ℝ, (dirichletPhi 0 t : ℂ) * Complex.exp (-y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y)) ∂ν) =
    (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) * (Complex.exp (-(y ^ 3) / 12) * Complex.exp (y ^ 3 / 12)) *
      ∫ t : ℝ, (dirichletPhi 0 t : ℂ) * Complex.exp (-y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y)) ∂ν by ring, hexp_cancel, mul_one]

/-- Exact Gaussian transform of `g₁(u) = (Ai(u) / (u - a₁))²` on `Re y > 0`. -/
theorem airyTwistedLaplaceC_ceG1_eq {y : ℂ} (hy : 0 < y.re) :
    airyTwistedLaplaceC (ceG1 (airyZero 1)) y = (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletPhi 0 t * dirichletPhi 0 s : ℝ) : ℂ) *
        Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) := by
  have hfun : ceG1 (airyZero 1) = cardinalPb basisZero := funext fun u => by unfold cardinalPb ceG1; rw [cardinalHb_basisZero_eq, dslope_airyAi_firstZero_eq_cohnL0]
  rw [hfun, airySquare_gaussian_transform basisZero_sq_summable hy]
  congr 1; refine integral_congr_ae ?_; filter_upwards [dirichletV_singleton_ae 0 1] with t ht
  rw [show (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) = basisZero from rfl] at ht
  refine integral_congr_ae ?_; filter_upwards [dirichletV_singleton_ae 0 1] with s hs
  rw [show (fun k : ℕ => if k = 0 then (1 : ℝ) else 0) = basisZero from rfl] at hs; rw [ht, hs, one_mul, one_mul]

/-- Exact Gaussian transform of `g₁'(u) = (Ai'(u) / (u - a₁'))²` on `Re y > 0`. -/
theorem airyTwistedLaplaceC_ceG1Deriv_eq {y : ℂ} (hy : 0 < y.re) :
    airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero) y = (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((airyRatio airyDerivFirstZero t * airyRatio airyDerivFirstZero s : ℝ) : ℂ) *
        Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) := by
  have hfun : ceG1Deriv airyDerivFirstZero = cardinalPb (cohnC airyDerivFirstZero) := funext fun u => by
    unfold cardinalPb cardinalHb ceG1Deriv; rw [(cardinal_Hstar_hasSum_firstDerivZero u).tsum_eq]; rfl
  have hsum : Summable (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2) := by
    have h := hasSum_inv_sq airyDerivFirstZero (airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2)
    rw [show cohnM airyDerivFirstZero = 0 by simp [cohnM, airyDerivFirstZero_spec.2.2], zero_pow two_ne_zero, zero_sub] at h
    exact (h.congr_fun fun n => by rw [cohnC, inv_pow]; ring).summable
  rw [hfun, airySquare_gaussian_transform hsum hy]
  congr 1; refine integral_congr_ae ?_; filter_upwards [dirichletV_Hstar_eq] with t ht
  refine integral_congr_ae ?_; filter_upwards [dirichletV_Hstar_eq] with s hs; rw [ht, hs, neg_mul_neg]

/-! ### Section 3: Gaussian kernel IBP asymptotics on `{0 < Re y, 1 ≤ ‖y‖}` -/

noncomputable def gaussKern (y : ℂ) (u : ℝ) : ℂ := Complex.exp (-((u : ℂ) ^ 2) / (4 * y))

noncomputable def gaussPoly : ℕ → ℂ → Polynomial ℂ
  | 0, _ => 1
  | n + 1, a => (gaussPoly n a).derivative - Polynomial.C a * Polynomial.X * gaussPoly n a

lemma norm_gaussKern_le {y : ℂ} (hy : 0 < y.re) (u : ℝ) : ‖gaussKern y u‖ ≤ 1 := by
  unfold gaussKern; rw [Complex.norm_exp, Real.exp_le_one_iff]
  have hre : (-((u : ℂ) ^ 2) / (4 * y)).re = -(u ^ 2 / 4 * (y.re / Complex.normSq y)) := by
    rw [neg_div, Complex.neg_re, show ((u : ℂ) ^ 2) = ((u ^ 2 : ℝ) : ℂ) by push_cast; ring, show (4 : ℂ) * y = ((4 : ℝ) : ℂ) * y by norm_num,
      div_eq_mul_inv, mul_inv, ← mul_assoc, show ((u ^ 2 : ℝ) : ℂ) * ((4 : ℝ) : ℂ)⁻¹ = ((u ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.inv_re]
  rw [hre]; exact neg_nonpos.mpr (mul_nonneg (by positivity) (div_nonneg hy.le (Complex.normSq_nonneg y)))

lemma contDiff_gaussKern {y : ℂ} (_ : y ≠ 0) : ContDiff ℝ ⊤ (gaussKern y) :=
  (Complex.differentiable_exp.contDiff.restrict_scalars ℝ).comp (((Complex.ofRealCLM.contDiff.pow 2).neg).div_const (4 * y))

private lemma hasDerivAt_gaussPoly_kern {y : ℂ} (hy : y ≠ 0) (P : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => P.eval (t : ℂ) * gaussKern y t) ((P.derivative - Polynomial.C (2 * y)⁻¹ * Polynomial.X * P).eval (x : ℂ) * gaussKern y x) x := by
  have harg : HasDerivAt (fun t : ℝ => -((t : ℂ) ^ 2) / (4 * y)) (-((2 * y)⁻¹ * (x : ℂ))) x := by
    refine (((hasDerivAt_pow 2 (x : ℂ)).comp_ofReal).neg.div_const (4 * y)).congr_deriv ?_
    have h4 : (4 : ℂ) * y ≠ 0 := mul_ne_zero (by norm_num) hy; have h2 : (2 : ℂ) * y ≠ 0 := mul_ne_zero (by norm_num) hy; field_simp [h4, h2]; ring
  refine (((P.hasDerivAt (x : ℂ)).comp_ofReal).mul harg.cexp).congr_deriv ?_
  unfold gaussKern; simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]; ring

lemma iteratedDeriv_gaussKern_eq {y : ℂ} (hy : y ≠ 0) (n : ℕ) (u : ℝ) : iteratedDeriv n (gaussKern y) u = (gaussPoly n (2 * y)⁻¹).eval (u : ℂ) * gaussKern y u := by
  induction n generalizing u with
  | zero => simp only [iteratedDeriv_zero, gaussPoly, Polynomial.eval_one, one_mul]
  | succ k ih => rw [iteratedDeriv_succ, show iteratedDeriv k (gaussKern y) = fun (t : ℝ) => (gaussPoly k (2 * y)⁻¹).eval (t : ℂ) * gaussKern y t from funext ih]; exact (hasDerivAt_gaussPoly_kern hy _ u).deriv

private lemma contDiff_gaussKern_deriv {y : ℂ} (hy : y ≠ 0) (m : ℕ) : ContDiff ℝ ⊤ (iteratedDeriv m (gaussKern y)) := by
  rw [show iteratedDeriv m (gaussKern y) = fun (u : ℝ) => (gaussPoly m (2 * y)⁻¹).eval (u : ℂ) * gaussKern y u from funext (iteratedDeriv_gaussKern_eq hy m)]
  refine ContDiff.mul ?_ (contDiff_gaussKern hy)
  rw [show (fun (u : ℝ) => (gaussPoly m (2 * y)⁻¹).eval (u : ℂ)) = fun (u : ℝ) =>
      ∑ k ∈ Finset.range ((gaussPoly m (2 * y)⁻¹).natDegree + 1), (gaussPoly m (2 * y)⁻¹).coeff k * (u : ℂ) ^ k from funext fun u => Polynomial.eval_eq_sum_range _]
  exact ContDiff.sum fun k _ => contDiff_const.mul (Complex.ofRealCLM.contDiff.pow k)

private lemma gaussPoly_deg_and_coeff (n : ℕ) :
    ∃ M > 0, ∀ {a : ℂ}, ‖a‖ ≤ 1 → (gaussPoly n a).natDegree ≤ n ∧ ∀ k : ℕ, ‖(gaussPoly n a).coeff k‖ ≤ M := by
  induction n with
  | zero => refine ⟨1, zero_lt_one, fun {a} _ => ⟨by simp [gaussPoly], fun k => by simp [gaussPoly, Polynomial.coeff_one]; split_ifs <;> norm_num⟩⟩
  | succ m ih =>
    obtain ⟨M, hM, hih⟩ := ih; refine ⟨(m + 3 : ℝ) * M, by positivity, fun {a} ha => ?_⟩
    obtain ⟨hdeg, hcoeff⟩ := hih ha; set P := gaussPoly m a; set Q := P.derivative - Polynomial.C a * Polynomial.X * P
    have hCX : (Polynomial.C a * Polynomial.X).natDegree ≤ 1 := (Polynomial.natDegree_mul_le).trans (by simp)
    have hQ_deg : Q.natDegree ≤ m + 1 := (Polynomial.natDegree_sub_le _ _).trans (max_le ((Polynomial.natDegree_derivative_le P).trans (by omega)) ((Polynomial.natDegree_mul_le).trans (by omega)))
    refine ⟨hQ_deg, fun k => ?_⟩
    by_cases hk : m + 1 < k
    · change ‖Q.coeff k‖ ≤ _; rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ_deg hk), norm_zero]; positivity
    · push Not at hk; change ‖Q.coeff k‖ ≤ (m + 3 : ℝ) * M; dsimp [Q]
      rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_derivative]
      have h1 : ‖P.coeff (k + 1) * (k + 1 : ℂ)‖ ≤ (m + 2 : ℝ) * M := calc
        ‖P.coeff (k + 1) * (k + 1 : ℂ)‖ = ‖P.coeff (k + 1)‖ * ((k + 1 : ℕ) : ℝ) := by rw [norm_mul, show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
        _ ≤ M * ((m + 2 : ℕ) : ℝ) := mul_le_mul (hcoeff (k + 1)) (by exact_mod_cast (by omega : k + 1 ≤ m + 2)) (by positivity) hM.le
        _ = (m + 2 : ℝ) * M := by push_cast; ring
      have h2 : ‖a * (Polynomial.X * P).coeff k‖ ≤ 1 * M := by rw [norm_mul]; cases k with
        | zero => rw [Polynomial.coeff_X_mul_zero, norm_zero, mul_zero]; positivity
        | succ r => rw [Polynomial.coeff_X_mul]; exact mul_le_mul ha (hcoeff r) (norm_nonneg _) zero_le_one
      exact (norm_sub_le _ _).trans (by linarith)

lemma norm_iteratedDeriv_gaussKern_le (n : ℕ) :
    ∃ B > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ u : ℝ, ‖iteratedDeriv n (gaussKern y) u‖ ≤ B * (1 + |u|) ^ n := by
  obtain ⟨M, hM, hdc⟩ := gaussPoly_deg_and_coeff n; refine ⟨(n + 1 : ℝ) * M, by positivity, fun {y} hy hy1 u => ?_⟩
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have ha : ‖(2 * y)⁻¹‖ ≤ 1 := by rw [norm_inv, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; exact inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨hdeg, hcoeff⟩ := hdc ha; rw [iteratedDeriv_gaussKern_eq hy_ne n u, norm_mul]
  have hpoly : ‖(gaussPoly n (2 * y)⁻¹).eval (u : ℂ)‖ ≤ ((n + 1 : ℝ) * M) * (1 + |u|) ^ n := by
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg (Nat.lt_succ_self n))]
    calc ‖∑ k ∈ Finset.range (n + 1), (gaussPoly n (2 * y)⁻¹).coeff k * (u : ℂ) ^ k‖
        ≤ ∑ _k ∈ Finset.range (n + 1), M * (1 + |u|) ^ n := (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul (hcoeff k) ((pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg u]) k).trans
            (pow_le_pow_right₀ (by linarith [abs_nonneg u]) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))) (by positivity) hM.le)
      _ = ((n + 1 : ℝ) * M) * (1 + |u|) ^ n := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  exact (mul_le_mul hpoly (norm_gaussKern_le hy u) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

lemma iteratedDeriv_ofReal_comp {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (n : ℕ) (t : ℝ) : iteratedDeriv n (fun s => (f s : ℂ)) t = ((iteratedDeriv n f t : ℝ) : ℂ) := by
  induction n generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun s => (f s : ℂ)) = fun s => ((iteratedDeriv k f s : ℝ) : ℂ) from funext ih, iteratedDeriv_succ]
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t ((hf.differentiable_iteratedDeriv k (by simp)).differentiableAt.hasDerivAt)).deriv

private lemma iteratedDeriv_comp_sub_const (h : ℝ → ℂ) (s : ℝ) (n : ℕ) (t : ℝ) : iteratedDeriv n (fun x => h (x - s)) t = iteratedDeriv n h (t - s) := by
  induction n generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun x => h (x - s)) = fun x => iteratedDeriv k h (x - s) from funext ih, iteratedDeriv_succ]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv k h) (t - s)
    · change deriv (iteratedDeriv k h ∘ fun x => id x - s) t = deriv (iteratedDeriv k h) (t - s)
      rw [(hd.hasDerivAt.scomp t ((hasDerivAt_id t).sub_const s)).deriv, one_smul]
    · have hnd : ¬ DifferentiableAt ℝ (fun x => iteratedDeriv k h (x - s)) t := fun hc => by
        have hc' : DifferentiableAt ℝ (fun x => iteratedDeriv k h (x - s)) ((t - s) + s) := by rwa [sub_add_cancel]
        exact hd (by simpa [Function.comp_def, add_sub_cancel_right] using hc'.comp (t - s) ((hasDerivAt_id (t - s)).add_const s).differentiableAt)
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd]

private lemma iteratedDeriv_comp_const_sub (h : ℝ → ℂ) (t : ℝ) (n : ℕ) (s : ℝ) : iteratedDeriv n (fun x => h (t - x)) s = (-1 : ℂ) ^ n * iteratedDeriv n h (t - s) := by
  induction n generalizing s with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun x => h (t - x)) = fun x => (-1 : ℂ) ^ k * iteratedDeriv k h (t - x) from funext ih,
      deriv_const_mul_field, iteratedDeriv_succ, pow_succ]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv k h) (t - s)
    · change (-1 : ℂ) ^ k * deriv (iteratedDeriv k h ∘ HSub.hSub t) s = _
      rw [(hd.hasDerivAt.scomp s ((hasDerivAt_id s).const_sub t)).deriv, neg_one_smul]; ring
    · have hnd : ¬ DifferentiableAt ℝ (fun x => iteratedDeriv k h (t - x)) s := fun hc => by
        have hc' : DifferentiableAt ℝ (fun x => iteratedDeriv k h (t - x)) (t - (t - s)) := by rwa [sub_sub_cancel]
        exact hd (by simpa [Function.comp_def, sub_sub_cancel_left] using hc'.comp (t - s) ((hasDerivAt_id (t - s)).const_sub t).differentiableAt)
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, mul_zero, mul_zero]

private lemma iteratedDeriv_add_nat (h : ℝ → ℂ) (j i : ℕ) (x : ℝ) : iteratedDeriv j (iteratedDeriv i h) x = iteratedDeriv (j + i) h x := by
  induction j generalizing x with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ, show iteratedDeriv k (iteratedDeriv i h) = iteratedDeriv (k + i) h from funext ih, ← iteratedDeriv_succ, Nat.succ_add]

lemma integrableOn_Ioi_exp_neg_quarter (C : ℝ) : IntegrableOn (fun t : ℝ => C * Real.exp (-(1 / 4 : ℝ) * t)) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0).const_mul C

private lemma norm_Ioi_integral_exp_quarter_le {φ : ℝ → ℂ} {C : ℝ} (hbd : ∀ t : ℝ, 0 ≤ t → ‖φ t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t)) :
    ‖∫ t in Ioi (0 : ℝ), φ t‖ ≤ 4 * C := by
  have hI : ∫ t in Ioi (0 : ℝ), C * Real.exp (-(1 / 4 : ℝ) * t) = 4 * C := by rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0]; norm_num; ring
  rw [← hI]; exact norm_integral_le_of_norm_le (integrableOn_Ioi_exp_neg_quarter C) (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht => hbd t (mem_Ioi.mp ht).le)

lemma norm_exp_neg_mul_half_le {y : ℂ} (hy : 0 < y.re) {t : ℝ} (ht : 0 ≤ t) : ‖Complex.exp (-y * (t : ℂ) / 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff, show (-y * (t : ℂ) / 2).re = -y.re * t / 2 by simp [Complex.div_ofNat_re]]; nlinarith

private lemma ibp_Ioi_exp_mul {φ : ℝ → ℂ} {y : ℂ} (hy : 0 < y.re) (hdiff : Differentiable ℝ φ) (hcont_deriv : Continuous (deriv φ))
    {C : ℝ} (hC : 0 ≤ C) (hbd : ∀ t : ℝ, 0 ≤ t → ‖φ t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t) ∧ ‖deriv φ t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t)) :
    ∫ t in Ioi (0 : ℝ), φ t * Complex.exp (-y * (t : ℂ) / 2) = (2 / y) * φ 0 + (2 / y) * ∫ t in Ioi (0 : ℝ), deriv φ t * Complex.exp (-y * (t : ℂ) / 2) := by
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  let v : ℝ → ℂ := fun t => -(2 / y) * Complex.exp (-y * (t : ℂ) / 2); let v' : ℝ → ℂ := fun t => Complex.exp (-y * (t : ℂ) / 2)
  have hv_deriv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x := fun x _ => by
    refine (((((hasDerivAt_id x).ofReal_comp.const_mul (-y)).div_const 2).cexp.const_mul (-(2 / y))).congr_deriv ?_); dsimp [v']; field_simp [hy_ne]
  have hint1 : IntegrableOn (φ * v') (Ioi 0) :=
    (integrableOn_Ioi_exp_neg_quarter C).mono' ((hdiff.continuous.mul (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable.restrict)
      (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht => by
        rw [Pi.mul_apply, norm_mul]
        exact (mul_le_mul (hbd t (mem_Ioi.mp ht).le).1 (norm_exp_neg_mul_half_le hy (mem_Ioi.mp ht).le) (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)).trans_eq (mul_one _))
  have hint2 : IntegrableOn (deriv φ * v) (Ioi 0) :=
    (integrableOn_Ioi_exp_neg_quarter (C * (2 / ‖y‖))).mono' ((hcont_deriv.mul (continuous_const.mul (Complex.continuous_exp.comp (by fun_prop)))).aestronglyMeasurable.restrict)
      (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht => by
        rw [Pi.mul_apply, norm_mul, show v t = -(2 / y) * v' t from rfl, norm_mul, norm_neg, norm_div, norm_ofNat]
        exact (mul_le_mul (hbd t (mem_Ioi.mp ht).le).2 (mul_le_mul_of_nonneg_left (norm_exp_neg_mul_half_le hy (mem_Ioi.mp ht).le) (by positivity))
          (by positivity) (mul_nonneg hC (Real.exp_pos _).le)).trans_eq (by ring))
  have hlim0 : Tendsto (φ * v) (nhdsWithin 0 (Ioi 0)) (𝓝 (φ 0 * -(2 / y))) := by
    have hc : ContinuousAt (fun t : ℝ => φ t * v t) 0 := hdiff.continuous.continuousAt.mul (by fun_prop)
    have h0 : φ 0 * v 0 = φ 0 * -(2 / y) := by simp [v]
    rw [← h0]; exact hc.continuousWithinAt.tendsto
  have hlimtop : Tendsto (φ * v) atTop (𝓝 0) := by
    have hsub : Tendsto (fun t : ℝ => -(1 / 4 : ℝ) * t) atTop atBot := Filter.tendsto_atTop_atBot.mpr fun b => ⟨max 0 (-4 * b), fun x hx => by linarith [le_max_right 0 (-4 * b)]⟩
    have hexp0 : Tendsto (fun t : ℝ => (C * (2 / ‖y‖)) * Real.exp (-(1 / 4 : ℝ) * t)) atTop (𝓝 0) := by simpa using Filter.Tendsto.const_mul (C * (2 / ‖y‖)) (Real.tendsto_exp_atBot.comp hsub)
    refine squeeze_zero_norm' (eventually_ge_atTop 0 |>.mono fun t ht => ?_) hexp0
    rw [Pi.mul_apply, norm_mul, show v t = -(2 / y) * v' t from rfl, norm_mul, norm_neg, norm_div, norm_ofNat]
    exact (mul_le_mul (hbd t ht).1 (mul_le_mul_of_nonneg_left (norm_exp_neg_mul_half_le hy ht) (by positivity)) (by positivity) (mul_nonneg hC (Real.exp_pos _).le)).trans_eq (by ring)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (u := φ) (v := v) (u' := deriv φ) (v' := v') (fun x _ => hdiff.differentiableAt.hasDerivAt) hv_deriv hint1 hint2 hlim0 hlimtop
  rw [hibp, show (fun t : ℝ => deriv φ t * v t) = fun t => -(2 / y) * (deriv φ t * v' t) from funext fun t => by dsimp [v]; ring, integral_const_mul]; ring

private lemma ibp_main_term_mul {y : ℂ} (hy_ne : y ≠ 0) (m : ℝ) :
    ((ceK / (2 * Real.sqrt π) : ℝ) : ℂ) * y ^ (-(1 / 2 : ℂ)) * (4 / y ^ 2 * (m : ℂ)) = (2 * ceK / Real.sqrt π * m : ℂ) * y ^ (-(5 / 2 : ℂ)) := by
  have hypow : y ^ (-(1 / 2 : ℂ)) * (y ^ 2)⁻¹ = y ^ (-(5 / 2 : ℂ)) := by
    rw [← Complex.cpow_natCast y 2, ← Complex.cpow_neg y (2 : ℕ), ← Complex.cpow_add _ _ hy_ne]; congr 1; norm_num
  calc _ = (4 * ((ceK / (2 * Real.sqrt π) : ℝ) : ℂ) * (m : ℂ)) * (y ^ (-(1 / 2 : ℂ)) * (y ^ 2)⁻¹) := by ring
    _ = _ := by rw [hypow]; push_cast; ring

private lemma ibp_rem_norm_le {y : ℂ} (hy : 0 < y.re) (hy1 : 1 ≤ ‖y‖) {R : ℂ} {C_r : ℝ} (hR : ‖R‖ ≤ C_r * ‖y‖ ^ (-4 : ℝ)) :
    ‖((ceK / (2 * Real.sqrt π) : ℝ) : ℂ) * y ^ (-(1 / 2 : ℂ)) * R‖ ≤ (ceK / (2 * Real.sqrt π) * C_r) * ‖y‖ ^ (-(9 / 2 : ℝ)) := by
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have hceK := ceK_pos
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ceK / (2 * Real.sqrt π)),
    show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl, norm_cpow_ofReal_exponent hy_ne]
  exact (mul_le_mul_of_nonneg_left hR (by positivity)).trans_eq (by
    rw [show ceK / (2 * Real.sqrt π) * ‖y‖ ^ (-(1 / 2 : ℝ)) * (C_r * ‖y‖ ^ (-4 : ℝ)) =
      (ceK / (2 * Real.sqrt π) * C_r) * (‖y‖ ^ (-(1 / 2 : ℝ)) * ‖y‖ ^ (-4 : ℝ)) by ring, ← Real.rpow_add (by linarith)]; norm_num)

private lemma ceF1_kernel_deriv_bound :
    ∃ M > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ n ≤ 4, ∀ t : ℝ, 0 ≤ t →
      ‖iteratedDeriv n (fun x : ℝ => (dirichletPhi 0 x : ℂ) * gaussKern y x) t‖ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) := by
  have hget : ∀ a b : ℕ, ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ t : ℝ, 0 ≤ t →
      |iteratedDeriv a (dirichletPhi 0) t| * ‖iteratedDeriv b (gaussKern y) t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t) := fun a b => by
    obtain ⟨C₁, hC₁, hφ⟩ := airyAi_shift_div_decay (airyZero 1) airyAi'_first_pos.ne' a b (by norm_num : (0 : ℝ) < 1 / 4)
    obtain ⟨B, hB, hG⟩ := norm_iteratedDeriv_gaussKern_le b
    refine ⟨C₁ * B, mul_pos hC₁ hB, fun {y} hy hy1 t ht => ?_⟩
    have hfn : (fun s => airyAi (airyZero 1 + s) / airyAi' (airyZero 1)) = dirichletPhi 0 := funext fun s => by unfold dirichletPhi; ring_nf
    have h2 : (1 + t) ^ b * |iteratedDeriv a (dirichletPhi 0) t| ≤ C₁ * Real.exp (-(1 / 4 : ℝ) * t) := by simpa [Real.norm_eq_abs, hfn] using hφ t ht
    calc |iteratedDeriv a (dirichletPhi 0) t| * ‖iteratedDeriv b (gaussKern y) t‖ ≤ |iteratedDeriv a (dirichletPhi 0) t| * (B * (1 + |t|) ^ b) := mul_le_mul_of_nonneg_left (hG hy hy1 t) (abs_nonneg _)
      _ = ((1 + t) ^ b * |iteratedDeriv a (dirichletPhi 0) t|) * B := by rw [abs_of_nonneg ht]; ring
      _ ≤ C₁ * B * Real.exp (-(1 / 4 : ℝ) * t) := (mul_le_mul_of_nonneg_right h2 hB.le).trans_eq (by ring)
  choose C_ab hC_ab hbd_ab using hget
  let M : ℝ := ∑ n ∈ Finset.range 5, ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * C_ab a (n - a) + 1
  have hM_pos : 0 < M := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg _) (hC_ab a (m - a)).le) zero_lt_one
  refine ⟨M, hM_pos, fun {y} hy hy1 n hn t ht => ?_⟩
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ => (dirichletPhi 0 x : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_dirichletPhi0; have h2 := contDiff_gaussKern hy_ne
  rw [iteratedDeriv_fun_mul (h1.contDiffAt.of_le (by simp)) (h2.contDiffAt.of_le (by simp))]
  calc ‖∑ a ∈ Finset.range (n + 1), _‖ ≤ ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * C_ab a (n - a) * Real.exp (-(1 / 4 : ℝ) * t) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by
          rw [norm_mul, norm_mul, Complex.norm_natCast, iteratedDeriv_ofReal_comp contDiff_dirichletPhi0 a t, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
          exact (mul_le_mul_of_nonneg_left (hbd_ab a (n - a) hy hy1 t ht) (Nat.cast_nonneg _)).trans_eq (by ring))
    _ = (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * C_ab a (n - a)) * Real.exp (-(1 / 4 : ℝ) * t) := (Finset.sum_mul _ _ _).symm
    _ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) := mul_le_mul_of_nonneg_right (le_trans (Finset.single_le_sum (s := Finset.range 5)
        (f := fun m => ∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) * C_ab a (m - a))
        (fun m _ => Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg _) (hC_ab a (m - a)).le)
        (Finset.mem_range.mpr (by omega))) (by dsimp [M]; linarith)) (Real.exp_pos _).le

/-- Uniform 4-fold Gaussian IBP asymptotic for `ceF1` on `{Re y > 0, ‖y‖ ≥ 1}`. -/
theorem airyTwistedLaplaceC_ceF1_asymp :
    ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ‖airyTwistedLaplaceC ceF1 y - (2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ))‖ ≤ C * ‖y‖ ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨M, hM, hkern⟩ := ceF1_kernel_deriv_bound; let C_err : ℝ := 16 * (|airyZero 1| + 3 / 2 + 4 * M)
  have hceK := ceK_pos; refine ⟨ceK / (2 * Real.sqrt π) * C_err + 1, by positivity, fun {y} hy hy1 => ?_⟩
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  let H : ℝ → ℂ := fun t => (dirichletPhi 0 t : ℂ) * gaussKern y t
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ => (dirichletPhi 0 x : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_dirichletPhi0
  have h2 := contDiff_gaussKern hy_ne; have hH_cd : ContDiff ℝ ⊤ H := h1.mul h2
  have hibp_step : ∀ k < 4, ∫ t in Ioi (0 : ℝ), iteratedDeriv k H t * Complex.exp (-y * (t : ℂ) / 2) =
      (2 / y) * iteratedDeriv k H 0 + (2 / y) * ∫ t in Ioi (0 : ℝ), iteratedDeriv (k + 1) H t * Complex.exp (-y * (t : ℂ) / 2) := fun k hk => by
    have hderiv_eq : deriv (iteratedDeriv k H) = iteratedDeriv (k + 1) H := iteratedDeriv_succ.symm
    have hc : Continuous (deriv (iteratedDeriv k H)) := hderiv_eq ▸ hH_cd.continuous_iteratedDeriv (k + 1) (by simp)
    rw [← hderiv_eq]; exact ibp_Ioi_exp_mul hy (hH_cd.differentiable_iteratedDeriv k (by simp)) hc hM.le fun t ht =>
      ⟨hkern hy hy1 k (by omega) t ht, by rw [hderiv_eq]; exact hkern hy hy1 (k + 1) (by omega) t ht⟩
  obtain ⟨hv0, hv1, hv2, hv3⟩ := dirichletPhi0_vals_at_zero; have hv1' : iteratedDeriv 1 (dirichletPhi 0) 0 = 1 := by rw [iteratedDeriv_one]; exact hv1
  have hg0 : gaussKern y 0 = 1 := by simp [gaussKern]
  have hg1 : iteratedDeriv 1 (gaussKern y) 0 = 0 := by rw [iteratedDeriv_gaussKern_eq hy_ne]; simp [gaussPoly]
  have hg2 : iteratedDeriv 2 (gaussKern y) 0 = -(2 * y)⁻¹ := by rw [iteratedDeriv_gaussKern_eq hy_ne]; simp [gaussPoly, gaussKern]
  have hH_iter : ∀ n : ℕ, iteratedDeriv n H 0 = ∑ a ∈ Finset.range (n + 1), (n.choose a : ℂ) * ((iteratedDeriv a (dirichletPhi 0) 0 : ℝ) : ℂ) * iteratedDeriv (n - a) (gaussKern y) 0 := fun n => by
    rw [show H = fun x => (dirichletPhi 0 x : ℂ) * gaussKern y x from rfl, iteratedDeriv_fun_mul (h1.contDiffAt.of_le (by simp)) (h2.contDiffAt.of_le (by simp))]
    exact Finset.sum_congr rfl fun a _ => by rw [iteratedDeriv_ofReal_comp contDiff_dirichletPhi0 a 0]
  have hs0 : H 0 = 0 := by simp [H, hv0]
  have hs1 : iteratedDeriv 1 H 0 = 1 := by simp [hH_iter 1, Finset.sum_range_succ, hv0, hv1', hg0, hg1]
  have hs2 : iteratedDeriv 2 H 0 = 0 := by simp [hH_iter 2, Finset.sum_range_succ, hv0, hv1', hv2, hg0, hg1]
  have hs3 : iteratedDeriv 3 H 0 = (3 : ℂ) * -(2 * y)⁻¹ + (airyZero 1 : ℂ) := by simp [hH_iter 3, Finset.sum_range_succ, hv0, hv1', hv2, hv3, hg0, hg1, hg2]
  have h4_eq : ∫ t in Ioi (0 : ℝ), H t * Complex.exp (-y * (t : ℂ) / 2) =
      4 / y ^ 2 * ((1 : ℝ) : ℂ) + (16 / y ^ 4) * (iteratedDeriv 3 H 0 + ∫ t in Ioi (0 : ℝ), iteratedDeriv 4 H t * Complex.exp (-y * (t : ℂ) / 2)) := by
    have s0 := hibp_step 0 (by norm_num); rw [iteratedDeriv_zero] at s0
    rw [s0, hibp_step 1 (by norm_num), hibp_step 2 (by norm_num), hibp_step 3 (by norm_num), hs0, hs1, hs2]; norm_num; ring
  have hH3_bd : ‖iteratedDeriv 3 H 0‖ ≤ |airyZero 1| + 3 / 2 := by
    rw [hs3]
    calc ‖(3 : ℂ) * -(2 * y)⁻¹ + (airyZero 1 : ℂ)‖ ≤ 3 / (2 * ‖y‖) + |airyZero 1| :=
          (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_neg, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs]; norm_num; ring)
      _ ≤ |airyZero 1| + 3 / 2 := by have : 3 / (2 * ‖y‖) ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith); linarith
  have hint4_bd := norm_Ioi_integral_exp_quarter_le (φ := fun t => iteratedDeriv 4 H t * Complex.exp (-y * (t : ℂ) / 2)) fun t ht => calc
    ‖iteratedDeriv 4 H t * Complex.exp (-y * (t : ℂ) / 2)‖ = ‖iteratedDeriv 4 H t‖ * ‖Complex.exp (-y * (t : ℂ) / 2)‖ := norm_mul _ _
    _ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) * 1 := mul_le_mul (hkern hy hy1 4 le_rfl t ht) (norm_exp_neg_mul_half_le hy ht) (norm_nonneg _) (mul_nonneg hM.le (Real.exp_pos _).le)
    _ = M * Real.exp (-(1 / 4 : ℝ) * t) := mul_one _
  have hrem_bd : ‖(16 / y ^ 4) * (iteratedDeriv 3 H 0 + ∫ t in Ioi (0 : ℝ), iteratedDeriv 4 H t * Complex.exp (-y * (t : ℂ) / 2))‖ ≤ C_err * ‖y‖ ^ (-4 : ℝ) := by
    rw [norm_mul, norm_div, show ‖(16 : ℂ)‖ = 16 by norm_num, norm_pow, div_eq_mul_inv,
      show ‖y‖ ^ (-4 : ℝ) = (‖y‖ ^ 4)⁻¹ by rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg y), Real.rpow_natCast]]
    exact (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hH3_bd hint4_bd)) (by positivity)).trans_eq (by dsimp [C_err]; ring)
  have hL : airyTwistedLaplaceC ceF1 y = ((ceK / (2 * Real.sqrt π) : ℝ) : ℂ) * y ^ (-(1 / 2 : ℂ)) * ∫ t in Ioi (0 : ℝ), H t * Complex.exp (-y * (t : ℂ) / 2) := by
    rw [airyTwistedLaplaceC_ceF1_eq hy, rpow_neg_half_mul_four_pi hy]; congr 1; · push_cast; ring
    · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_; dsimp [H, gaussKern]; rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
  rw [hL, h4_eq, mul_add, ibp_main_term_mul hy_ne 1, Complex.ofReal_one, mul_one, add_sub_cancel_left]
  exact (ibp_rem_norm_le hy hy1 hrem_bd).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))

/-- Derivative bound for `φ · gaussKern y` from the `exp(-t/4)` decay of all derivatives of `φ`. -/
private lemma gen_kernel_deriv_bound {φ : ℝ → ℝ} (hφ : ContDiff ℝ ⊤ φ)
    (hφ_dec : ∀ n k : ℕ, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n φ t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t)) :
    ∃ M > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ n ≤ 4, ∀ t : ℝ, 0 ≤ t →
      ‖iteratedDeriv n (fun x : ℝ => (φ x : ℂ) * gaussKern y x) t‖ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) := by
  have hget : ∀ a b : ℕ, ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ t : ℝ, 0 ≤ t →
      |iteratedDeriv a φ t| * ‖iteratedDeriv b (gaussKern y) t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t) := fun a b => by
    obtain ⟨C₁, hC₁, hφ'⟩ := hφ_dec a b
    obtain ⟨B, hB, hG⟩ := norm_iteratedDeriv_gaussKern_le b
    refine ⟨C₁ * B, mul_pos hC₁ hB, fun {y} hy hy1 t ht => ?_⟩
    have h2 : (1 + t) ^ b * |iteratedDeriv a φ t| ≤ C₁ * Real.exp (-(1 / 4 : ℝ) * t) := by simpa [Real.norm_eq_abs] using hφ' t ht
    calc |iteratedDeriv a φ t| * ‖iteratedDeriv b (gaussKern y) t‖ ≤ |iteratedDeriv a φ t| * (B * (1 + |t|) ^ b) := mul_le_mul_of_nonneg_left (hG hy hy1 t) (abs_nonneg _)
      _ = ((1 + t) ^ b * |iteratedDeriv a φ t|) * B := by rw [abs_of_nonneg ht]; ring
      _ ≤ C₁ * B * Real.exp (-(1 / 4 : ℝ) * t) := (mul_le_mul_of_nonneg_right h2 hB.le).trans_eq (by ring)
  choose C_ab hC_ab hbd_ab using hget
  let M : ℝ := ∑ n ∈ Finset.range 5, ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * C_ab a (n - a) + 1
  have hM_pos : 0 < M := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg _) (hC_ab a (m - a)).le) zero_lt_one
  refine ⟨M, hM_pos, fun {y} hy hy1 n hn t ht => ?_⟩
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ; have h2 := contDiff_gaussKern hy_ne
  rw [iteratedDeriv_fun_mul (h1.contDiffAt.of_le (by simp)) (h2.contDiffAt.of_le (by simp))]
  calc ‖∑ a ∈ Finset.range (n + 1), _‖ ≤ ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * C_ab a (n - a) * Real.exp (-(1 / 4 : ℝ) * t) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by
          rw [norm_mul, norm_mul, Complex.norm_natCast, iteratedDeriv_ofReal_comp hφ a t, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
          exact (mul_le_mul_of_nonneg_left (hbd_ab a (n - a) hy hy1 t ht) (Nat.cast_nonneg _)).trans_eq (by ring))
    _ = (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * C_ab a (n - a)) * Real.exp (-(1 / 4 : ℝ) * t) := (Finset.sum_mul _ _ _).symm
    _ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) := mul_le_mul_of_nonneg_right (le_trans (Finset.single_le_sum (s := Finset.range 5)
        (f := fun m => ∑ a ∈ Finset.range (m + 1), (m.choose a : ℝ) * C_ab a (m - a))
        (fun m _ => Finset.sum_nonneg fun a _ => mul_nonneg (Nat.cast_nonneg _) (hC_ab a (m - a)).le)
        (Finset.mem_range.mpr (by omega))) (by dsimp [M]; linarith)) (Real.exp_pos _).le

/-- **Generic 1-dimensional (4-fold) Gaussian IBP expansion** (no vanishing hypotheses): for `φ` smooth with the
`exp(-t/4)` decay of all derivatives, uniformly on `{Re y > 0, ‖y‖ ≥ 1}`,
`∫_0^∞ φ(t) e^{-yt/2 - t²/(4y)} dt = 2 φ(0)/y + 4 φ'(0)/y² + 8 φ''(0)/y³ + O(‖y‖⁻⁴)`. -/
theorem gaussian_1d_ibp_general {φ : ℝ → ℝ} (hφ : ContDiff ℝ ⊤ φ)
    (hφ_dec : ∀ n k : ℕ, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n φ t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t)) :
    ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ →
      ‖(∫ t in Ioi (0 : ℝ), (φ t : ℂ) * Complex.exp (-y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y))) -
        (2 / y * (φ 0 : ℂ) + 4 / y ^ 2 * (iteratedDeriv 1 φ 0 : ℝ) + 8 / y ^ 3 * (iteratedDeriv 2 φ 0 : ℝ))‖ ≤ C * ‖y‖ ^ (-4 : ℝ) := by
  obtain ⟨M, hM, hkern⟩ := gen_kernel_deriv_bound hφ hφ_dec
  refine ⟨16 * (M + 4 * M) + 4 * |φ 0| + 1, by positivity, fun {y} hy hy1 => ?_⟩
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  let H : ℝ → ℂ := fun t => (φ t : ℂ) * gaussKern y t
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
  have h2 := contDiff_gaussKern hy_ne; have hH_cd : ContDiff ℝ ⊤ H := h1.mul h2
  have hibp_step : ∀ k < 4, ∫ t in Ioi (0 : ℝ), iteratedDeriv k H t * Complex.exp (-y * (t : ℂ) / 2) =
      (2 / y) * iteratedDeriv k H 0 + (2 / y) * ∫ t in Ioi (0 : ℝ), iteratedDeriv (k + 1) H t * Complex.exp (-y * (t : ℂ) / 2) := fun k hk => by
    have hderiv_eq : deriv (iteratedDeriv k H) = iteratedDeriv (k + 1) H := iteratedDeriv_succ.symm
    have hc : Continuous (deriv (iteratedDeriv k H)) := hderiv_eq ▸ hH_cd.continuous_iteratedDeriv (k + 1) (by simp)
    rw [← hderiv_eq]; exact ibp_Ioi_exp_mul hy (hH_cd.differentiable_iteratedDeriv k (by simp)) hc hM.le fun t ht =>
      ⟨hkern hy hy1 k (by omega) t ht, by rw [hderiv_eq]; exact hkern hy hy1 (k + 1) (by omega) t ht⟩
  have hg0 : gaussKern y 0 = 1 := by simp [gaussKern]
  have hg1 : iteratedDeriv 1 (gaussKern y) 0 = 0 := by rw [iteratedDeriv_gaussKern_eq hy_ne]; simp [gaussPoly]
  have hg2 : iteratedDeriv 2 (gaussKern y) 0 = -(2 * y)⁻¹ := by rw [iteratedDeriv_gaussKern_eq hy_ne]; simp [gaussPoly, gaussKern]
  have hH_iter : ∀ n : ℕ, iteratedDeriv n H 0 = ∑ a ∈ Finset.range (n + 1), (n.choose a : ℂ) * ((iteratedDeriv a φ 0 : ℝ) : ℂ) * iteratedDeriv (n - a) (gaussKern y) 0 := fun n => by
    rw [show H = fun x => (φ x : ℂ) * gaussKern y x from rfl, iteratedDeriv_fun_mul (h1.contDiffAt.of_le (by simp)) (h2.contDiffAt.of_le (by simp))]
    exact Finset.sum_congr rfl fun a _ => by rw [iteratedDeriv_ofReal_comp hφ a 0]
  have hs0 : H 0 = (φ 0 : ℂ) := by simp [H, hg0]
  have hs1 : iteratedDeriv 1 H 0 = ((iteratedDeriv 1 φ 0 : ℝ) : ℂ) := by simp [hH_iter 1, Finset.sum_range_succ, hg0, hg1]
  have hs2 : iteratedDeriv 2 H 0 = ((iteratedDeriv 2 φ 0 : ℝ) : ℂ) - (φ 0 : ℂ) * (2 * y)⁻¹ := by
    simp [hH_iter 2, Finset.sum_range_succ, hg0, hg1, hg2]; ring
  have h4_eq : ∫ t in Ioi (0 : ℝ), H t * Complex.exp (-y * (t : ℂ) / 2) =
      2 / y * (φ 0 : ℂ) + 4 / y ^ 2 * ((iteratedDeriv 1 φ 0 : ℝ) : ℂ) + 8 / y ^ 3 * ((iteratedDeriv 2 φ 0 : ℝ) : ℂ) +
        (8 / y ^ 3 * (-(φ 0 : ℂ) * (2 * y)⁻¹) + (16 / y ^ 4) * (iteratedDeriv 3 H 0 + ∫ t in Ioi (0 : ℝ), iteratedDeriv 4 H t * Complex.exp (-y * (t : ℂ) / 2))) := by
    have s0 := hibp_step 0 (by norm_num); rw [iteratedDeriv_zero] at s0
    rw [s0, hibp_step 1 (by norm_num), hibp_step 2 (by norm_num), hibp_step 3 (by norm_num), hs0, hs1, hs2]
    field_simp; ring
  have hint4_bd := norm_Ioi_integral_exp_quarter_le (φ := fun t => iteratedDeriv 4 H t * Complex.exp (-y * (t : ℂ) / 2)) fun t ht => calc
    ‖iteratedDeriv 4 H t * Complex.exp (-y * (t : ℂ) / 2)‖ = ‖iteratedDeriv 4 H t‖ * ‖Complex.exp (-y * (t : ℂ) / 2)‖ := norm_mul _ _
    _ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) * 1 := mul_le_mul (hkern hy hy1 4 le_rfl t ht) (norm_exp_neg_mul_half_le hy ht) (norm_nonneg _) (mul_nonneg hM.le (Real.exp_pos _).le)
    _ = M * Real.exp (-(1 / 4 : ℝ) * t) := mul_one _
  have hH3 : ‖iteratedDeriv 3 H 0‖ ≤ M := by simpa using hkern hy hy1 3 (by norm_num) 0 le_rfl
  have hy4 : ‖y‖ ^ (-4 : ℝ) = (‖y‖ ^ 4)⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg y), Real.rpow_natCast]
  have hy_pos : 0 < ‖y‖ := by linarith
  have hrem1 : ‖8 / y ^ 3 * (-(φ 0 : ℂ) * (2 * y)⁻¹)‖ ≤ 4 * |φ 0| * ‖y‖ ^ (-4 : ℝ) := by
    rw [hy4, norm_mul, norm_div, norm_pow, norm_mul, norm_neg, norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show ‖(8 : ℂ)‖ = 8 by norm_num, show ‖(2 : ℂ)‖ = 2 by norm_num]
    refine le_of_eq ?_
    field_simp
    ring
  have hrem2 : ‖(16 / y ^ 4) * (iteratedDeriv 3 H 0 + ∫ t in Ioi (0 : ℝ), iteratedDeriv 4 H t * Complex.exp (-y * (t : ℂ) / 2))‖ ≤ 16 * (M + 4 * M) * ‖y‖ ^ (-4 : ℝ) := by
    rw [hy4, norm_mul, norm_div, show ‖(16 : ℂ)‖ = 16 by norm_num, norm_pow, div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hH3 hint4_bd)) (by positivity)).trans_eq (by ring)
  have hL : (∫ t in Ioi (0 : ℝ), (φ t : ℂ) * Complex.exp (-y * (t : ℂ) / 2 - (t : ℂ) ^ 2 / (4 * y))) = ∫ t in Ioi (0 : ℝ), H t * Complex.exp (-y * (t : ℂ) / 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_; dsimp [H, gaussKern]; rw [mul_assoc, ← Complex.exp_add]; congr 2; ring
  rw [hL, h4_eq, add_sub_cancel_left]
  have hpos : 0 ≤ ‖y‖ ^ (-4 : ℝ) := Real.rpow_nonneg hy_pos.le _
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 4 * |φ 0| * ‖y‖ ^ (-4 : ℝ) + 16 * (M + 4 * M) * ‖y‖ ^ (-4 : ℝ) := add_le_add hrem1 hrem2
    _ ≤ _ := by nlinarith [hpos]

/-! #### Generic 2-dimensional 3+3+1 Gaussian IBP theorem (`ceG1Deriv` & `ceG1`) -/

private noncomputable def twoDimK (f g : ℝ → ℝ) (y : ℂ) (t s : ℝ) : ℂ := (f t : ℂ) * (g s : ℂ) * gaussKern y (t - s)

private noncomputable def twoDimKD (f g : ℝ → ℝ) (y : ℂ) (i j : ℕ) (t s : ℝ) : ℂ :=
  iteratedDeriv j (fun r => iteratedDeriv i (fun x => twoDimK f g y x r) t) s

private lemma twoDimK_t_eq {f : ℝ → ℝ} (g : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) {y : ℂ} (hy : y ≠ 0) (i : ℕ) (t s : ℝ) :
    twoDimKD f g y i 0 t s = ∑ a ∈ Finset.range (i + 1), (i.choose a : ℂ) * ((iteratedDeriv a f t : ℝ) : ℂ) * (g s : ℂ) * iteratedDeriv (i - a) (gaussKern y) (t - s) := by
  unfold twoDimKD; rw [iteratedDeriv_zero]
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have h2 : ContDiff ℝ ⊤ (fun x : ℝ => (g s : ℂ) * gaussKern y (x - s)) := contDiff_const.mul ((contDiff_gaussKern hy).comp (contDiff_id.sub contDiff_const))
  rw [show (fun x => twoDimK f g y x s) = fun x => (f x : ℂ) * ((g s : ℂ) * gaussKern y (x - s)) from funext fun x => by unfold twoDimK; ring,
    iteratedDeriv_fun_mul (h1.contDiffAt.of_le (by simp)) (h2.contDiffAt.of_le (by simp))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [iteratedDeriv_ofReal_comp hf a t, iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const (gaussKern y) s (i - a) t]; ring

private lemma twoDimKD_contDiff_s {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) {y : ℂ} (hy : y ≠ 0) (i : ℕ) (t : ℝ) :
    ContDiff ℝ ⊤ (fun s => twoDimKD f g y i 0 t s) := by
  rw [show (fun s => twoDimKD f g y i 0 t s) = fun s => ∑ a ∈ Finset.range (i + 1), (i.choose a : ℂ) * ((iteratedDeriv a f t : ℝ) : ℂ) *
      ((g s : ℂ) * iteratedDeriv (i - a) (gaussKern y) (t - s)) from funext fun s => by rw [twoDimK_t_eq g hf hy i t s]; exact Finset.sum_congr rfl fun a _ => by ring]
  exact ContDiff.sum fun a _ => contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp hg).mul ((contDiff_gaussKern_deriv hy (i - a)).comp (contDiff_const.sub contDiff_id)))

private lemma twoDimKD_eq_sum {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) {y : ℂ} (hy : y ≠ 0) (i j : ℕ) (t s : ℝ) :
    twoDimKD f g y i j t s = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
      (i.choose a : ℂ) * (j.choose b : ℂ) * ((iteratedDeriv a f t : ℝ) : ℂ) * ((iteratedDeriv b g s : ℝ) : ℂ) * (-1 : ℂ) ^ (j - b) *
        iteratedDeriv ((j - b) + (i - a)) (gaussKern y) (t - s) := by
  have heq : (fun r => iteratedDeriv i (fun x => twoDimK f g y x r) t) = ∑ a ∈ Finset.range (i + 1), fun r => (i.choose a : ℂ) * ((iteratedDeriv a f t : ℝ) : ℂ) *
      ((g r : ℂ) * iteratedDeriv (i - a) (gaussKern y) (t - r)) := funext fun r => by
    have h := twoDimK_t_eq g hf hy i t r; unfold twoDimKD at h; rw [iteratedDeriv_zero] at h; rw [Finset.sum_apply, h]; exact Finset.sum_congr rfl fun a _ => by ring
  unfold twoDimKD; rw [heq, iteratedDeriv_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hcd1 : ContDiff ℝ ⊤ (fun r : ℝ => (g r : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hcd2 : ContDiff ℝ ⊤ (fun r : ℝ => iteratedDeriv (i - a) (gaussKern y) (t - r)) := (contDiff_gaussKern_deriv hy (i - a)).comp (contDiff_const.sub contDiff_id)
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul (hcd1.contDiffAt.of_le (by simp)) (hcd2.contDiffAt.of_le (by simp)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [iteratedDeriv_ofReal_comp hg b s, iteratedDeriv_comp_const_sub _ t (j - b) s, iteratedDeriv_add_nat]; ring
  · exact fun a _ => (contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp hg).mul ((contDiff_gaussKern_deriv hy (i - a)).comp (contDiff_const.sub contDiff_id)))).contDiffAt.of_le (by simp)

private lemma twoDimKD_norm_le {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hf_dec : ∀ n k : ℕ, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n f t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t))
    (hg_dec : ∀ n k : ℕ, ∃ C > 0, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ k * ‖iteratedDeriv n g s‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * s)) (i j : ℕ) :
    ∃ M > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ‖twoDimKD f g y i j t s‖ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s) := by
  let term_bd : ℕ → ℕ → ℝ := fun a b => Classical.choose (hf_dec a (i + j)) * Classical.choose (hg_dec b (i + j)) * Classical.choose (norm_iteratedDeriv_gaussKern_le ((j - b) + (i - a)))
  let M : ℝ := ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (i.choose a : ℝ) * (j.choose b : ℝ) * term_bd a b + 1
  have hM_nn : ∀ a b, 0 ≤ term_bd a b := fun a b => mul_nonneg (mul_nonneg (Classical.choose_spec (hf_dec a (i + j))).1.le (Classical.choose_spec (hg_dec b (i + j))).1.le)
    (Classical.choose_spec (norm_iteratedDeriv_gaussKern_le ((j - b) + (i - a)))).1.le
  have hM_pos : 0 < M := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hM_nn a b)) zero_lt_one
  refine ⟨M, hM_pos, fun {y} hy hy1 t s ht hs => ?_⟩
  rw [twoDimKD_eq_sum hf hg (fun h => by simp [h] at hy) i j t s]
  have hterm : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
      ‖(i.choose a : ℂ) * (j.choose b : ℂ) * ((iteratedDeriv a f t : ℝ) : ℂ) * ((iteratedDeriv b g s : ℝ) : ℂ) * (-1 : ℂ) ^ (j - b) *
        iteratedDeriv ((j - b) + (i - a)) (gaussKern y) (t - s)‖ ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * term_bd a b * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s) := fun a ha b hb => by
    let B_ab := Classical.choose (norm_iteratedDeriv_gaussKern_le ((j - b) + (i - a)))
    have hB_pos : 0 < B_ab := (Classical.choose_spec (norm_iteratedDeriv_gaussKern_le ((j - b) + (i - a)))).1
    have hB := (Classical.choose_spec (norm_iteratedDeriv_gaussKern_le ((j - b) + (i - a)))).2 hy hy1 (t - s)
    have h1ts : (1 + |t - s|) ^ ((j - b) + (i - a)) ≤ (1 + t) ^ (i + j) * (1 + s) ^ (i + j) := by
      have hts : 1 + |t - s| ≤ (1 + t) * (1 + s) := by nlinarith [abs_sub t s, abs_of_nonneg ht, abs_of_nonneg hs]
      calc (1 + |t - s|) ^ ((j - b) + (i - a)) ≤ ((1 + t) * (1 + s)) ^ ((j - b) + (i - a)) := pow_le_pow_left₀ (by positivity) hts _
        _ = (1 + t) ^ ((j - b) + (i - a)) * (1 + s) ^ ((j - b) + (i - a)) := mul_pow _ _ _
        _ ≤ (1 + t) ^ (i + j) * (1 + s) ^ (i + j) := mul_le_mul (pow_le_pow_right₀ (by linarith) (by have := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha); have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb); omega))
            (pow_le_pow_right₀ (by linarith) (by have := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha); have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb); omega)) (by positivity) (by positivity)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, Complex.norm_real, Complex.norm_real, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    have hB' : ‖iteratedDeriv ((j - b) + (i - a)) (gaussKern y) (t - s)‖ ≤ B_ab * ((1 + t) ^ (i + j) * (1 + s) ^ (i + j)) := hB.trans (mul_le_mul_of_nonneg_left h1ts hB_pos.le)
    calc _ ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * ‖iteratedDeriv a f t‖ * ‖iteratedDeriv b g s‖ * (B_ab * ((1 + t) ^ (i + j) * (1 + s) ^ (i + j))) := by gcongr
      _ = (i.choose a : ℝ) * (j.choose b : ℝ) * ((1 + t) ^ (i + j) * ‖iteratedDeriv a f t‖) * ((1 + s) ^ (i + j) * ‖iteratedDeriv b g s‖) * B_ab := by ring
      _ ≤ (i.choose a : ℝ) * (j.choose b : ℝ) * (Classical.choose (hf_dec a (i + j)) * Real.exp (-(1 / 4 : ℝ) * t)) *
          (Classical.choose (hg_dec b (i + j)) * Real.exp (-(1 / 4 : ℝ) * s)) * B_ab :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left ((Classical.choose_spec (hf_dec a (i + j))).2 t ht) (by positivity))
            ((Classical.choose_spec (hg_dec b (i + j))).2 s hs) (by positivity)
            (mul_nonneg (by positivity) (mul_nonneg (Classical.choose_spec (hf_dec a (i + j))).1.le (Real.exp_pos _).le))) hB_pos.le
      _ = (i.choose a : ℝ) * (j.choose b : ℝ) * term_bd a b * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s) := by dsimp [term_bd, B_ab]; ring
  calc ‖∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), _‖
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (i.choose a : ℝ) * (j.choose b : ℝ) * term_bd a b * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => hterm a ha b hb))
    _ = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (i.choose a : ℝ) * (j.choose b : ℝ) * term_bd a b) * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s) := by
        simp only [← Finset.sum_mul]
    _ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s) := by gcongr; dsimp [M]; linarith

private lemma twoDimKD_zero_vals {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) {y : ℂ} (hy : y ≠ 0) :
    twoDimKD f g y 0 0 0 0 = (f 0 * g 0 : ℂ) ∧ twoDimKD f g y 0 1 0 0 = ((f 0 * deriv g 0 : ℝ) : ℂ) ∧ twoDimKD f g y 1 0 0 0 = ((deriv f 0 * g 0 : ℝ) : ℂ) := by
  have hg_0 : gaussKern y 0 = 1 := by simp [gaussKern]
  have hg_1 : deriv (gaussKern y) 0 = 0 := by rw [← iteratedDeriv_one, iteratedDeriv_gaussKern_eq hy]; simp [gaussPoly]
  have hG_d : HasDerivAt (gaussKern y) 0 0 := by rw [← hg_1]; exact ((contDiff_gaussKern hy).differentiable (by simp)).differentiableAt.hasDerivAt
  refine ⟨by simp [twoDimKD, twoDimK, gaussKern], ?_, ?_⟩
  · unfold twoDimKD; simp only [iteratedDeriv_zero, iteratedDeriv_one]
    have hfun : (fun r => twoDimK f g y 0 r) = fun r => (f 0 : ℂ) * ((g r : ℂ) * gaussKern y (0 - r)) := funext fun r => by unfold twoDimK; ring
    have hd_g := (hg.differentiable (by simp) 0).hasDerivAt.ofReal_comp
    have hd_G : HasDerivAt (fun r : ℝ => gaussKern y (0 - r)) 0 0 :=
      hG_d.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => by dsimp [gaussKern]; rw [zero_sub, Complex.ofReal_neg, neg_sq])
    have hd_tot : HasDerivAt (fun r => (f 0 : ℂ) * ((g r : ℂ) * gaussKern y (0 - r))) ((f 0 * deriv g 0 : ℝ) : ℂ) 0 :=
      ((hd_g.mul hd_G).const_mul (f 0 : ℂ)).congr_deriv (by simp [hg_0])
    rw [hfun, hd_tot.deriv]
  · unfold twoDimKD; simp only [iteratedDeriv_zero, iteratedDeriv_one]
    have hfun : (fun x => twoDimK f g y x 0) = fun x => ((f x : ℂ) * (g 0 : ℂ)) * gaussKern y (x - 0) := funext fun x => by unfold twoDimK; ring
    have hd_f := (hf.differentiable (by simp) 0).hasDerivAt.ofReal_comp
    have hd_G : HasDerivAt (fun x : ℝ => gaussKern y (x - 0)) 0 0 :=
      hG_d.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by simp)
    have hd_tot : HasDerivAt (fun x => ((f x : ℂ) * (g 0 : ℂ)) * gaussKern y (x - 0)) ((deriv f 0 * g 0 : ℝ) : ℂ) 0 :=
      ((hd_f.mul_const (g 0 : ℂ)).mul hd_G).congr_deriv (by simp [hg_0])
    rw [hfun, hd_tot.deriv]

private lemma twoDimKD_prod_integrable {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) {y : ℂ} (hy : 0 < y.re) {M : ℝ}
    (hM : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ‖twoDimKD f g y i j t s‖ ≤ M * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s)) :
    Integrable (Function.uncurry fun t s : ℝ => twoDimKD f g y i j t s * Complex.exp (-y * (t : ℂ) / 2) * Complex.exp (-y * (s : ℂ) / 2)) ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have hM0 : 0 ≤ M := by simpa using (norm_nonneg (twoDimKD f g y i j 0 0)).trans (hM 0 0 le_rfl le_rfl)
  have hK_cont : Continuous (fun p : ℝ × ℝ => twoDimKD f g y i j p.1 p.2) := by
    rw [show (fun p : ℝ × ℝ => twoDimKD f g y i j p.1 p.2) = fun p => ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        (i.choose a : ℂ) * (j.choose b : ℂ) * ((iteratedDeriv a f p.1 : ℝ) : ℂ) * ((iteratedDeriv b g p.2 : ℝ) : ℂ) * (-1 : ℂ) ^ (j - b) * iteratedDeriv ((j - b) + (i - a)) (gaussKern y) (p.1 - p.2) from
      funext fun p => twoDimKD_eq_sum hf hg hy_ne i j p.1 p.2]
    exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((((continuous_const.mul (Complex.continuous_ofReal.comp ((hf.continuous_iteratedDeriv a (by simp)).comp continuous_fst))).mul
        (Complex.continuous_ofReal.comp ((hg.continuous_iteratedDeriv b (by simp)).comp continuous_snd))).mul continuous_const).mul
        ((contDiff_gaussKern_deriv hy_ne _).continuous.comp (continuous_fst.sub continuous_snd)))
  refine integrable_prod_of_norm_le_mul ((hK_cont.mul (Complex.continuous_exp.comp (by fun_prop))).mul (Complex.continuous_exp.comp (by fun_prop)))
    (integrableOn_Ioi_exp_neg_quarter M) (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 4 : ℝ) < 0) 0) (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht => ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hK := hM t s (mem_Ioi.mp ht).le (mem_Ioi.mp hs).le; have hEt := norm_exp_neg_mul_half_le hy (mem_Ioi.mp ht).le; have hEs := norm_exp_neg_mul_half_le hy (mem_Ioi.mp hs).le
  calc ‖twoDimKD f g y i j t s * Complex.exp (-y * (t : ℂ) / 2) * Complex.exp (-y * (s : ℂ) / 2)‖ = ‖twoDimKD f g y i j t s‖ * ‖Complex.exp (-y * (t : ℂ) / 2)‖ * ‖Complex.exp (-y * (s : ℂ) / 2)‖ := by rw [norm_mul, norm_mul]
    _ ≤ (M * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s)) * 1 * 1 := by gcongr
    _ = (M * Real.exp (-(1 / 4 : ℝ) * t)) * Real.exp (-(1 / 4 : ℝ) * s) := by ring

private lemma twoDimK_ibp_t {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) {y : ℂ} (hy : 0 < y.re) (hy1 : 1 ≤ ‖y‖) {M : ℕ → ℕ → ℝ} (hMp : ∀ i j, 0 < M i j)
    (hMb : ∀ i j {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ‖twoDimKD f g y i j t s‖ ≤ M i j * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s)) (i : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    ∫ t in Ioi (0 : ℝ), twoDimKD f g y i 0 t s * Complex.exp (-y * (t : ℂ) / 2) = (2 / y) * twoDimKD f g y i 0 0 s + (2 / y) * ∫ t in Ioi (0 : ℝ), twoDimKD f g y (i + 1) 0 t s * Complex.exp (-y * (t : ℂ) / 2) := by
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have ht_eq : (fun t => twoDimKD f g y i 0 t s) = iteratedDeriv i (fun x => twoDimK f g y x s) := funext fun t => by unfold twoDimKD; rw [iteratedDeriv_zero]
  have hcd : ContDiff ℝ ⊤ (fun t => twoDimK f g y t s) := ((Complex.ofRealCLM.contDiff.comp hf).mul contDiff_const).mul ((contDiff_gaussKern hy_ne).comp (contDiff_id.sub contDiff_const))
  have hderiv_eq : ∀ t, deriv (fun x => twoDimKD f g y i 0 x s) t = twoDimKD f g y (i + 1) 0 t s := fun t => by rw [ht_eq, congrFun (iteratedDeriv_succ (n := i)).symm t]; unfold twoDimKD; rw [iteratedDeriv_zero]
  have hc : Continuous (deriv fun t => twoDimKD f g y i 0 t s) :=
    (show (deriv fun t => twoDimKD f g y i 0 t s) = iteratedDeriv (i + 1) (fun x => twoDimK f g y x s) from funext fun t => by rw [hderiv_eq t]; unfold twoDimKD; rw [iteratedDeriv_zero]).symm ▸ hcd.continuous_iteratedDeriv (i + 1) (by simp)
  let Cmax := max (M i 0) (M (i + 1) 0) * Real.exp (-(1 / 4 : ℝ) * s)
  have hCmax : 0 ≤ Cmax := mul_nonneg (le_max_of_le_left (hMp i 0).le) (Real.exp_pos _).le
  simpa only [hderiv_eq] using ibp_Ioi_exp_mul (C := Cmax) hy (ht_eq ▸ hcd.differentiable_iteratedDeriv i (by simp)) hc hCmax fun t ht =>
    ⟨(hMb i 0 hy hy1 t s ht hs).trans (by dsimp [Cmax]; rw [mul_assoc, mul_comm (Real.exp (-(1 / 4 : ℝ) * t)), ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le) (Real.exp_pos _).le),
      by rw [hderiv_eq t]; exact (hMb (i + 1) 0 hy hy1 t s ht hs).trans (by dsimp [Cmax]; rw [mul_assoc, mul_comm (Real.exp (-(1 / 4 : ℝ) * t)), ← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le) (Real.exp_pos _).le)⟩

private lemma twoDimKD_ibp_s {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) {y : ℂ} (hy : 0 < y.re) (hy1 : 1 ≤ ‖y‖) {M : ℕ → ℕ → ℝ} (hMp : ∀ i j, 0 < M i j)
    (hMb : ∀ i j {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → ‖twoDimKD f g y i j t s‖ ≤ M i j * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s)) (i j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Ioi (0 : ℝ), twoDimKD f g y i j t s * Complex.exp (-y * (s : ℂ) / 2) = (2 / y) * twoDimKD f g y i j t 0 + (2 / y) * ∫ s in Ioi (0 : ℝ), twoDimKD f g y i (j + 1) t s * Complex.exp (-y * (s : ℂ) / 2) := by
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have hcd := twoDimKD_contDiff_s hf hg hy_ne i t
  have hs_eq : (fun s => twoDimKD f g y i j t s) = iteratedDeriv j (fun r => twoDimKD f g y i 0 t r) := funext fun s => by unfold twoDimKD; rw [iteratedDeriv_add_nat, add_zero]
  have hderiv_eq : ∀ s, deriv (fun r => twoDimKD f g y i j t r) s = twoDimKD f g y i (j + 1) t s := fun s => by rw [hs_eq, congrFun (iteratedDeriv_succ (n := j)).symm s]; unfold twoDimKD; rw [iteratedDeriv_add_nat, add_zero]
  have hc : Continuous (deriv fun r => twoDimKD f g y i j t r) :=
    (show (deriv fun r => twoDimKD f g y i j t r) = iteratedDeriv (j + 1) (fun r => twoDimKD f g y i 0 t r) from
      funext fun s => by rw [hderiv_eq s]; unfold twoDimKD; rw [iteratedDeriv_add_nat, add_zero]).symm ▸ hcd.continuous_iteratedDeriv (j + 1) (by simp)
  let Cmax := max (M i j) (M i (j + 1)) * Real.exp (-(1 / 4 : ℝ) * t)
  have hCmax : 0 ≤ Cmax := mul_nonneg (le_max_of_le_left (hMp i j).le) (Real.exp_pos _).le
  simpa only [hderiv_eq] using ibp_Ioi_exp_mul (C := Cmax) hy (hs_eq ▸ hcd.differentiable_iteratedDeriv j (by simp)) hc hCmax fun s hs =>
    ⟨(hMb i j hy hy1 t s ht hs).trans (by dsimp [Cmax]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le) (Real.exp_pos _).le),
      by rw [hderiv_eq s]; exact (hMb i (j + 1) hy hy1 t s ht hs).trans (by dsimp [Cmax]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le) (Real.exp_pos _).le)⟩

/-- **Generic 2-dimensional (3+3+1)-fold Gaussian IBP expansion** (no vanishing hypotheses): for `f, g` smooth with
the `exp(-t/4)` decay of all derivatives, uniformly on `{Re y > 0, ‖y‖ ≥ 1}`,
`∫_0^∞∫_0^∞ f(t) g(s) e^{-y(t+s)/2 - (t-s)²/(4y)} ds dt = 4 f(0) g(0)/y² + 8 (f(0) g'(0) + f'(0) g(0))/y³ + O(‖y‖⁻⁴)`. -/
theorem gaussian_2d_ibp_general {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hf_dec : ∀ n k : ℕ, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n f t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t))
    (hg_dec : ∀ n k : ℕ, ∃ C > 0, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ k * ‖iteratedDeriv n g s‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * s)) :
    ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ →
      ‖(∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((f t * g s : ℝ) : ℂ) *
        Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))) -
        (4 / y ^ 2 * ((f 0 * g 0 : ℝ) : ℂ) + 8 / y ^ 3 * ((f 0 * deriv g 0 + deriv f 0 * g 0 : ℝ) : ℂ))‖ ≤ C * ‖y‖ ^ (-4 : ℝ) := by
  choose M hM_pos hM_bd using twoDimKD_norm_le hf hg hf_dec hg_dec
  let M_all := 16 * (M 0 2 + M 1 1 + M 2 0 + 4 * (M 0 3 + M 1 2 + M 2 1 + M 3 0 + 4 * M 3 1))
  refine ⟨M_all + 1, by
    have := hM_pos 0 2; have := hM_pos 1 1; have := hM_pos 2 0; have := hM_pos 0 3; have := hM_pos 1 2; have := hM_pos 2 1; have := hM_pos 3 0; have := hM_pos 3 1; positivity, fun {y} hy hy1 => ?_⟩
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  let E : ℝ → ℂ := fun t => Complex.exp (-y * (t : ℂ) / 2)
  have hint0 := twoDimKD_prod_integrable hf hg hy (i := 0) (j := 0) (hM_bd 0 0 hy hy1)
  have hint30 := twoDimKD_prod_integrable hf hg hy (i := 3) (j := 0) (hM_bd 3 0 hy hy1)
  have hint31 := twoDimKD_prod_integrable hf hg hy (i := 3) (j := 1) (hM_bd 3 1 hy hy1)
  have hibp_t := twoDimK_ibp_t hf hy hy1 hM_pos hM_bd; have hibp_s := twoDimKD_ibp_s hf hg hy hy1 hM_pos hM_bd
  have hswap0 : ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((f t * g s : ℝ) : ℂ) * Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) =
      ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), twoDimKD f g y 0 0 t s * E t * E s := by
    trans ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), twoDimKD f g y 0 0 t s * E t * E s
    · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
      dsimp [twoDimKD, twoDimK, gaussKern, E]; rw [iteratedDeriv_zero, iteratedDeriv_zero, Complex.ofReal_mul, mul_assoc ((f t : ℂ) * (g s : ℂ)), mul_assoc ((f t : ℂ) * (g s : ℂ)), ← Complex.exp_add, ← Complex.exp_add]; congr 2; push_cast; ring
    · exact integral_integral_swap hint0
  have hint_s_slice : ∀ i : ℕ, IntegrableOn (fun s => twoDimKD f g y i 0 0 s * E s) (Ioi 0) := fun i =>
    (integrableOn_Ioi_exp_neg_quarter (M i 0)).mono' ((twoDimKD_contDiff_s hf hg hy_ne i 0).continuous.mul (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
      (ae_restrict_mem measurableSet_Ioi |>.mono fun s hs => calc
        ‖twoDimKD f g y i 0 0 s * E s‖ = ‖twoDimKD f g y i 0 0 s‖ * ‖E s‖ := norm_mul _ _
        _ ≤ (M i 0 * Real.exp (-(1 / 4 : ℝ) * s)) * 1 := mul_le_mul (by simpa [Real.exp_zero] using hM_bd i 0 hy hy1 0 s le_rfl (mem_Ioi.mp hs).le) (norm_exp_neg_mul_half_le hy (mem_Ioi.mp hs).le) (norm_nonneg _) (mul_nonneg (hM_pos i 0).le (Real.exp_pos _).le)
        _ = M i 0 * Real.exp (-(1 / 4 : ℝ) * s) := mul_one _)
  have houter : ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), twoDimKD f g y 0 0 t s * E t * E s =
      (2 / y) * (∫ s in Ioi (0 : ℝ), twoDimKD f g y 0 0 0 s * E s) + (4 / y ^ 2) * (∫ s in Ioi (0 : ℝ), twoDimKD f g y 1 0 0 s * E s) +
      (8 / y ^ 3) * (∫ s in Ioi (0 : ℝ), twoDimKD f g y 2 0 0 s * E s) + (8 / y ^ 3) * (∫ s in Ioi (0 : ℝ), (∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t) * E s) := by
    have hinner : Set.EqOn (fun s => ∫ t in Ioi (0 : ℝ), twoDimKD f g y 0 0 t s * E t * E s) (fun s =>
        (2 / y) * (twoDimKD f g y 0 0 0 s * E s) + (4 / y ^ 2) * (twoDimKD f g y 1 0 0 s * E s) +
        (8 / y ^ 3) * (twoDimKD f g y 2 0 0 s * E s) + (8 / y ^ 3) * ((∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t) * E s)) (Ioi 0) := fun s hs => by
      dsimp only; rw [integral_mul_const]; dsimp only [E]; rw [hibp_t 0 hs.le, hibp_t 1 hs.le, hibp_t 2 hs.le]; ring
    have hint3_out : IntegrableOn (fun s => (∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t) * E s) (Ioi 0) := by
      rw [show (fun s => (∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t) * E s) = fun s => ∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t * E s from funext fun s => (integral_mul_const _ _).symm]
      exact hint30.integral_prod_right
    have hi0 := (hint_s_slice 0).const_mul (2 / y); have hi1 := (hint_s_slice 1).const_mul (4 / y ^ 2)
    have hi2 := (hint_s_slice 2).const_mul (8 / y ^ 3); have hi3 := hint3_out.const_mul (8 / y ^ 3)
    have hi01 : IntegrableOn (fun s => (2 / y) * (twoDimKD f g y 0 0 0 s * E s) + (4 / y ^ 2) * (twoDimKD f g y 1 0 0 s * E s)) (Ioi 0) := hi0.add hi1
    have hi012 : IntegrableOn (fun s => (2 / y) * (twoDimKD f g y 0 0 0 s * E s) + (4 / y ^ 2) * (twoDimKD f g y 1 0 0 s * E s) + (8 / y ^ 3) * (twoDimKD f g y 2 0 0 s * E s)) (Ioi 0) := hi01.add hi2
    rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_add hi012 hi3, integral_add hi01 hi2, integral_add hi0 hi1,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hterm3 : ∫ s in Ioi (0 : ℝ), (∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t) * E s =
      (2 / y) * (∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t 0 * E t) + (2 / y) * (∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 1 t s * E s * E t) := by
    rw [show (fun s => (∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t) * E s) = fun s => ∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t * E s from funext fun s => (integral_mul_const _ _).symm, ← integral_integral_swap hint30]
    have hin : Set.EqOn (fun t => ∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 0 t s * E t * E s) (fun t =>
        (2 / y) * (twoDimKD f g y 3 0 t 0 * E t) + (2 / y) * ∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 1 t s * E s * E t) (Ioi 0) := fun t ht => by
      dsimp only
      rw [show (fun s => twoDimKD f g y 3 0 t s * E t * E s) = fun s => (twoDimKD f g y 3 0 t s * E s) * E t from funext fun _ => by ring, integral_mul_const]
      dsimp only [E]; rw [hibp_s 3 0 ht.le, add_mul, mul_assoc (2 / y), mul_assoc (2 / y),
        show (fun s => twoDimKD f g y 3 1 t s * Complex.exp (-y * (s : ℂ) / 2) * Complex.exp (-y * (t : ℂ) / 2)) =
          fun s => (twoDimKD f g y 3 1 t s * Complex.exp (-y * (s : ℂ) / 2)) * Complex.exp (-y * (t : ℂ) / 2) from funext fun _ => by ring,
        ← integral_mul_const]
    have hint_t0 : IntegrableOn (fun t => twoDimKD f g y 3 0 t 0 * E t) (Ioi 0) :=
      (integrableOn_Ioi_exp_neg_quarter (M 3 0)).mono' ((((Complex.ofRealCLM.contDiff.comp hf).mul contDiff_const |>.mul
        ((contDiff_gaussKern hy_ne).comp (contDiff_id.sub contDiff_const))).continuous_iteratedDeriv 3 (by simp)).congr (fun t => by unfold twoDimKD twoDimK; rw [iteratedDeriv_zero]; rfl) |>.mul (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
        (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht => calc
          ‖twoDimKD f g y 3 0 t 0 * E t‖ = ‖twoDimKD f g y 3 0 t 0‖ * ‖E t‖ := norm_mul _ _
          _ ≤ (M 3 0 * Real.exp (-(1 / 4 : ℝ) * t)) * 1 := mul_le_mul (by simpa [Real.exp_zero] using hM_bd 3 0 hy hy1 t 0 (mem_Ioi.mp ht).le le_rfl) (norm_exp_neg_mul_half_le hy (mem_Ioi.mp ht).le) (norm_nonneg _) (mul_nonneg (hM_pos 3 0).le (Real.exp_pos _).le)
          _ = M 3 0 * Real.exp (-(1 / 4 : ℝ) * t) := mul_one _)
    have hint_t31 : IntegrableOn (fun t => ∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 1 t s * E s * E t) (Ioi 0) := by
      rw [show (fun t => ∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 1 t s * E s * E t) = fun t => ∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 1 t s * E t * E s from funext fun t => setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring]
      exact hint31.integral_prod_left
    rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_add (hint_t0.const_mul _) (hint_t31.const_mul _), integral_const_mul, integral_const_mul]
  obtain ⟨hK00, hK01, hK10⟩ := twoDimKD_zero_vals hf hg hy_ne
  let rem : ℂ := ((twoDimKD f g y 0 2 0 0 + twoDimKD f g y 1 1 0 0 + twoDimKD f g y 2 0 0 0) +
    (∫ s in Ioi (0 : ℝ), twoDimKD f g y 0 3 0 s * E s) + (∫ s in Ioi (0 : ℝ), twoDimKD f g y 1 2 0 s * E s) +
    (∫ s in Ioi (0 : ℝ), twoDimKD f g y 2 1 0 s * E s) + (∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t 0 * E t) +
    (∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 1 t s * E s * E t))
  have hexpand : ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((f t * g s : ℝ) : ℂ) * Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) =
      4 / y ^ 2 * ((f 0 * g 0 : ℝ) : ℂ) + 8 / y ^ 3 * ((f 0 * deriv g 0 + deriv f 0 * g 0 : ℝ) : ℂ) + (16 / y ^ 4) * rem := by
    rw [hswap0, houter]; dsimp only [E, rem]
    rw [hibp_s 0 0 le_rfl, hibp_s 0 1 le_rfl, hibp_s 0 2 le_rfl, hibp_s 1 0 le_rfl, hibp_s 1 1 le_rfl, hibp_s 2 0 le_rfl]
    erw [hterm3]; rw [hK00, hK01, hK10]; push_cast; ring
  have h1d_s : ∀ i j, ‖∫ s in Ioi (0 : ℝ), twoDimKD f g y i j 0 s * E s‖ ≤ 4 * M i j := fun i j =>
    norm_Ioi_integral_exp_quarter_le fun s hs => calc
      ‖twoDimKD f g y i j 0 s * E s‖ = ‖twoDimKD f g y i j 0 s‖ * ‖E s‖ := norm_mul _ _
      _ ≤ (M i j * Real.exp (-(1 / 4 : ℝ) * s)) * 1 := mul_le_mul (by simpa [Real.exp_zero] using hM_bd i j hy hy1 0 s le_rfl hs) (norm_exp_neg_mul_half_le hy hs) (norm_nonneg _) (mul_nonneg (hM_pos i j).le (Real.exp_pos _).le)
      _ = M i j * Real.exp (-(1 / 4 : ℝ) * s) := mul_one _
  have h1d_t : ‖∫ t in Ioi (0 : ℝ), twoDimKD f g y 3 0 t 0 * E t‖ ≤ 4 * M 3 0 :=
    norm_Ioi_integral_exp_quarter_le fun t ht => calc
      ‖twoDimKD f g y 3 0 t 0 * E t‖ = ‖twoDimKD f g y 3 0 t 0‖ * ‖E t‖ := norm_mul _ _
      _ ≤ (M 3 0 * Real.exp (-(1 / 4 : ℝ) * t)) * 1 := mul_le_mul (by simpa [Real.exp_zero] using hM_bd 3 0 hy hy1 t 0 ht le_rfl) (norm_exp_neg_mul_half_le hy ht) (norm_nonneg _) (mul_nonneg (hM_pos 3 0).le (Real.exp_pos _).le)
      _ = M 3 0 * Real.exp (-(1 / 4 : ℝ) * t) := mul_one _
  have h2d_in : ∀ t : ℝ, 0 ≤ t → ‖∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 1 t s * E s * E t‖ ≤ (4 * M 3 1) * Real.exp (-(1 / 4 : ℝ) * t) := fun t ht =>
    (norm_Ioi_integral_exp_quarter_le fun s hs => calc
      ‖twoDimKD f g y 3 1 t s * E s * E t‖ = ‖twoDimKD f g y 3 1 t s‖ * ‖E s‖ * ‖E t‖ := by rw [norm_mul, norm_mul]
      _ ≤ (M 3 1 * Real.exp (-(1 / 4 : ℝ) * t) * Real.exp (-(1 / 4 : ℝ) * s)) * 1 * 1 :=
          mul_le_mul (mul_le_mul (hM_bd 3 1 hy hy1 t s ht hs) (norm_exp_neg_mul_half_le hy hs) (norm_nonneg _) (mul_nonneg (mul_nonneg (hM_pos 3 1).le (Real.exp_pos _).le) (Real.exp_pos _).le))
            (norm_exp_neg_mul_half_le hy ht) (norm_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg (hM_pos 3 1).le (Real.exp_pos _).le) (Real.exp_pos _).le) zero_le_one)
      _ = (M 3 1 * Real.exp (-(1 / 4 : ℝ) * t)) * Real.exp (-(1 / 4 : ℝ) * s) := by ring).trans_eq (by ring)
  have h2d : ‖∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), twoDimKD f g y 3 1 t s * E s * E t‖ ≤ 16 * M 3 1 :=
    (norm_Ioi_integral_exp_quarter_le h2d_in).trans_eq (by ring)
  have hrem_norm : ‖(16 / y ^ 4) * rem‖ ≤ M_all * ‖y‖ ^ (-4 : ℝ) := by
    have hK02 := by simpa [Real.exp_zero] using hM_bd 0 2 hy hy1 0 0 le_rfl le_rfl
    have hK11 := by simpa [Real.exp_zero] using hM_bd 1 1 hy hy1 0 0 le_rfl le_rfl
    have hK20 := by simpa [Real.exp_zero] using hM_bd 2 0 hy hy1 0 0 le_rfl le_rfl
    have htri : ‖rem‖ ≤ M 0 2 + M 1 1 + M 2 0 + 4 * (M 0 3 + M 1 2 + M 2 1 + M 3 0 + 4 * M 3 1) :=
      (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hK02 hK11)) hK20)) (h1d_s 0 3))) (h1d_s 1 2))) (h1d_s 2 1))) h1d_t)) h2d).trans_eq (by ring))
    rw [norm_mul, norm_div, show ‖(16 : ℂ)‖ = 16 by norm_num, norm_pow, div_eq_mul_inv, show ‖y‖ ^ (-4 : ℝ) = (‖y‖ ^ 4)⁻¹ by rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg y), Real.rpow_natCast]]
    exact (mul_le_mul_of_nonneg_left htri (by positivity)).trans_eq (by dsimp [M_all]; ring)
  rw [hexpand, add_sub_cancel_left]
  exact hrem_norm.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))

private lemma gaussian_2d_ibp_asymp {f g : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hf_dec : ∀ n k : ℕ, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n f t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t))
    (hg_dec : ∀ n k : ℕ, ∃ C > 0, ∀ s : ℝ, 0 ≤ s → (1 + s) ^ k * ‖iteratedDeriv n g s‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * s))
    (hf0 : f 0 * deriv g 0 = 0) (hg0 : deriv f 0 * g 0 = 0) :
    ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ →
      ‖(ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) * (∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((f t * g s : ℝ) : ℂ) *
        Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))) - (2 * ceK / Real.sqrt π * (f 0 * g 0) : ℂ) * y ^ (-(5 / 2 : ℂ))‖ ≤ C * ‖y‖ ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbd⟩ := gaussian_2d_ibp_general hf hg hf_dec hg_dec
  have hceK := ceK_pos
  refine ⟨ceK / (2 * Real.sqrt π) * C, by positivity, fun {y} hy hy1 => ?_⟩
  have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have h := hbd hy hy1
  rw [hf0, hg0, add_zero, Complex.ofReal_zero, mul_zero, add_zero] at h
  rw [rpow_neg_half_mul_four_pi hy,
    show (ceK : ℂ) * ((((2 * Real.sqrt π)⁻¹ : ℝ) : ℂ) * y ^ (-(1 / 2 : ℂ))) = ((ceK / (2 * Real.sqrt π) : ℝ) : ℂ) * y ^ (-(1 / 2 : ℂ)) by push_cast; ring]
  generalize (∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((f t * g s : ℝ) : ℂ) * Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))) = J at h ⊢
  rw [show J = 4 / y ^ 2 * ((f 0 * g 0 : ℝ) : ℂ) + (J - 4 / y ^ 2 * ((f 0 * g 0 : ℝ) : ℂ)) by ring, mul_add,
    ibp_main_term_mul hy_ne (f 0 * g 0), Complex.ofReal_mul, add_sub_cancel_left]
  rw [Complex.ofReal_mul] at h
  exact ibp_rem_norm_le hy hy1 h

/-- Uniform (3+3+1)-fold Gaussian IBP asymptotic for `ceG1Deriv` on `{Re y > 0, ‖y‖ ≥ 1}`. -/
theorem airyTwistedLaplaceC_ceG1Deriv_asymp :
    ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ‖airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero) y - (2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ))‖ ≤ C * ‖y‖ ^ (-(9 / 2 : ℝ)) := by
  have hdec : ∀ n k : ℕ, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n (airyRatio airyDerivFirstZero) t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t) :=
    fun n k => airyAi_shift_div_decay airyDerivFirstZero (airyAi_pos_of_gt airyDerivFirstZero_spec.1).ne' n k (by norm_num)
  obtain ⟨hv0, hv1, _, _⟩ := airyRatio_vals_at_zero
  obtain ⟨C, hC, hbd⟩ := gaussian_2d_ibp_asymp (contDiff_airyRatio airyDerivFirstZero) (contDiff_airyRatio airyDerivFirstZero) hdec hdec (by rw [hv0, hv1, mul_zero]) (by rw [hv0, hv1, zero_mul])
  exact ⟨C, hC, fun {y} hy hy1 => by rw [airyTwistedLaplaceC_ceG1Deriv_eq hy]; simpa [hv0, mul_one] using hbd hy hy1⟩

/-- Uniform (3+3+1)-fold Gaussian IBP bound `‖g̃₁(i y)‖ ≤ C ‖y‖^{-9/2}` for `ceG1` on `{Re y > 0, ‖y‖ ≥ 1}`. -/
theorem airyTwistedLaplaceC_ceG1_bound :
    ∃ C > 0, ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) y‖ ≤ C * ‖y‖ ^ (-(9 / 2 : ℝ)) := by
  have hfn : (fun s => airyAi (airyZero 1 + s) / airyAi' (airyZero 1)) = dirichletPhi 0 := funext fun s => by unfold dirichletPhi; ring_nf
  have hdec : ∀ n k : ℕ, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k * ‖iteratedDeriv n (dirichletPhi 0) t‖ ≤ C * Real.exp (-(1 / 4 : ℝ) * t) := fun n k => by
    obtain ⟨C, hC, hbd⟩ := airyAi_shift_div_decay (airyZero 1) airyAi'_first_pos.ne' n k (by norm_num : (0 : ℝ) < 1 / 4); exact ⟨C, hC, fun t ht => by simpa [hfn] using hbd t ht⟩
  obtain ⟨hv0, _, _, _⟩ := dirichletPhi0_vals_at_zero
  obtain ⟨C, hC, hbd⟩ := gaussian_2d_ibp_asymp contDiff_dirichletPhi0 contDiff_dirichletPhi0 hdec hdec (by rw [hv0, zero_mul]) (by rw [hv0, mul_zero])
  exact ⟨C, hC, fun {y} hy hy1 => by rw [airyTwistedLaplaceC_ceG1_eq hy]; simpa [hv0] using hbd hy hy1⟩

/-! ### Section 4: Lemma `O.11c`, Lemma `P.1(2)` / `U.2`, and unconditional `twoScaleQ0` Laplace bound -/

/-- Cancelled origin symbol `E(u) = f₁(u) - g₁'(u)` (`ce_o1_route.tex` Lemma `O.11c`). -/
noncomputable def ceCancelE (u : ℝ) : ℝ := ceF1 u - ceG1Deriv airyDerivFirstZero u

private lemma ceCancelE_regularity :
    (∀ y : ℂ, 0 ≤ y.re → Integrable (fun u : ℝ => (ceCancelE u : ℂ) * Complex.exp (y * (u : ℂ)))) ∧ ContinuousOn (airyTwistedLaplaceC ceCancelE) {y : ℂ | 0 ≤ y.re} ∧
    DifferentiableOn ℂ (airyTwistedLaplaceC ceCancelE) {y : ℂ | 0 < y.re} ∧ ∃ C_bd > 0, ∀ {y : ℂ}, 0 ≤ y.re → ‖y‖ ≤ 1 → ‖airyTwistedLaplaceC ceCancelE y‖ ≤ C_bd := by
  obtain ⟨C1, hC1, hF1⟩ := ceF1_tail_exp_rpow32; obtain ⟨C2, hC2, hG1'⟩ := ceG1Deriv_tail_exp_rpow32
  exact airyTwistedLaplaceC_regularity (continuous_ceF1.sub (continuous_ceG1Deriv _)) (ceF1_integral_eq_zero.1.sub ceG1Deriv_integral_eq_M.1)
    (add_pos hC1 hC2) fun u hu => ((abs_sub _ _).trans (add_le_add (hF1 u hu) (hG1' u hu))).trans_eq (by ring)

lemma ceF1_regularity :
    (∀ y : ℂ, 0 ≤ y.re → Integrable (fun u : ℝ => (ceF1 u : ℂ) * Complex.exp (y * (u : ℂ)))) ∧ ContinuousOn (airyTwistedLaplaceC ceF1) {y : ℂ | 0 ≤ y.re} ∧
    DifferentiableOn ℂ (airyTwistedLaplaceC ceF1) {y : ℂ | 0 < y.re} ∧ ∃ C_bd > 0, ∀ {y : ℂ}, 0 ≤ y.re → ‖y‖ ≤ 1 → ‖airyTwistedLaplaceC ceF1 y‖ ≤ C_bd :=
  let ⟨_, hC1, hF1⟩ := ceF1_tail_exp_rpow32; airyTwistedLaplaceC_regularity continuous_ceF1 ceF1_integral_eq_zero.1 hC1 hF1

lemma ceS0_regularity :
    (∀ y : ℂ, 0 ≤ y.re → Integrable (fun u : ℝ => (ceS0 (airyZero 1) airyDerivFirstZero u : ℂ) * Complex.exp (y * (u : ℂ)))) ∧
    ContinuousOn (airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero)) {y : ℂ | 0 ≤ y.re} ∧
    DifferentiableOn ℂ (airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero)) {y : ℂ | 0 < y.re} ∧
    ∃ C_bd > 0, ∀ {y : ℂ}, 0 ≤ y.re → ‖y‖ ≤ 1 → ‖airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero) y‖ ≤ C_bd := by
  obtain ⟨C1, hC1, hG1⟩ := ceG1_tail_exp_rpow32; obtain ⟨C2, hC2, hG1'⟩ := ceG1Deriv_tail_exp_rpow32
  exact airyTwistedLaplaceC_regularity (continuous_ceS0 _ _) (ceS0_integrable (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2)
    (add_pos hC1 hC2) fun u hu => ((abs_add_le _ _).trans (add_le_add (hG1 u hu) (hG1' u hu))).trans_eq (by ring)

/-- **Lemma `O.11c` (`(ceo:O11c.1)`):** `‖Ẽ(i c_s w)‖ ≤ C ‖1 + w‖^{-9/2}` for all `w : ℂ` with `Re w ≥ 0`. -/
theorem airyTwistedLaplaceC_ceCancelE_rhp :
    ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC ceCancelE ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨_, hE_cont, _, C_lo, hC_lo, hlo⟩ := ceCancelE_regularity; obtain ⟨C2, hC2, hG1'⟩ := ceG1Deriv_tail_exp_rpow32
  have hG1'_int := (airyTwistedLaplaceC_regularity (continuous_ceG1Deriv _) ceG1Deriv_integral_eq_M.1 hC2 hG1').1
  obtain ⟨CF, _, hF_asymp⟩ := airyTwistedLaplaceC_ceF1_asymp; obtain ⟨CG, _, hG_asymp⟩ := airyTwistedLaplaceC_ceG1Deriv_asymp
  have hhi : ∀ y : ℂ, 0 < y.re → 1 ≤ ‖y‖ → ‖airyTwistedLaplaceC ceCancelE y‖ ≤ (CF + CG) * ‖y‖ ^ (-(9 / 2 : ℝ)) := fun y hy hy1 => by
    rw [show ceCancelE = fun u => ceF1 u - ceG1Deriv airyDerivFirstZero u from rfl, airyTwistedLaplaceC_sub (ceF1_regularity.1 y hy.le) (hG1'_int y hy.le)]
    calc ‖airyTwistedLaplaceC ceF1 y - airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero) y‖
        = ‖(airyTwistedLaplaceC ceF1 y - (2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ))) - (airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero) y - (2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ)))‖ := by ring_nf
      _ ≤ (CF + CG) * ‖y‖ ^ (-(9 / 2 : ℝ)) := (norm_sub_le _ _).trans ((add_le_add (hF_asymp hy hy1) (hG_asymp hy hy1)).trans_eq (by ring))
  obtain ⟨C, hC, hpos⟩ := rhp_bound_of_unit_and_tail (by norm_num : (0 : ℝ) ≤ 9 / 2) hC_lo (fun y hy => hlo hy.le) hhi
  exact ⟨C, hC, rhp_extend_to_boundary hE_cont hpos⟩

/-- **Lemma `O.11c` (`(ceo:O11c.2)`):** uniform vertical-line Cauchy derivative bounds for `ceCancelE`, all `j : ℕ`, `c ≥ 2`, `τ : ℝ`. -/
theorem airyTwistedLaplaceC_ceCancelE_dual_deriv_bound :
    ∀ j : ℕ, ∃ C_j > 0, ∀ {c : ℝ}, 2 ≤ c → ∀ τ : ℝ,
      ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC ceCancelE (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤ C_j * c ^ (-(3 / 2 : ℝ)) * (1 + τ ^ 2) ^ (-(9 / 4 : ℝ)) := by
  obtain ⟨C_rhp, hC_rhp, hrhp⟩ := airyTwistedLaplaceC_ceCancelE_rhp
  have h := cauchy_dual_deriv_bound_of_rhp (by norm_num : (0 : ℝ) ≤ 9 / 2) hC_rhp ceCancelE_regularity.2.2.1 hrhp
  intro j; obtain ⟨C_j, hC_j, hbd⟩ := h j
  exact ⟨C_j, hC_j, fun hc τ => by simpa [show -(9 / 2 : ℝ) / 3 = -(3 / 2 : ℝ) by norm_num, show -(9 / 2 : ℝ) / 2 = -(9 / 4 : ℝ) by norm_num] using hbd hc τ⟩

lemma rhp_bound_52_of_asymp {X : ℝ → ℝ} (hX_cont : ContinuousOn (airyTwistedLaplaceC X) {y : ℂ | 0 ≤ y.re}) {C_lo : ℝ} (hC_lo : 0 < C_lo)
    (hlo : ∀ {y : ℂ}, 0 ≤ y.re → ‖y‖ ≤ 1 → ‖airyTwistedLaplaceC X y‖ ≤ C_lo) {C_a : ℝ} (hhi : ∀ {y : ℂ}, 0 < y.re → 1 ≤ ‖y‖ → ‖airyTwistedLaplaceC X y‖ ≤ C_a * ‖y‖ ^ (-(5 / 2 : ℝ))) :
    ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
  let ⟨C, hC, hpos⟩ := rhp_bound_of_unit_and_tail (by norm_num : (0 : ℝ) ≤ 5 / 2) hC_lo (fun y hy => hlo hy.le) (fun y hy => hhi hy); ⟨C, hC, rhp_extend_to_boundary hX_cont hpos⟩

lemma norm_le_add_norm_sub_52 {F : ℂ → ℂ} {y : ℂ} (hy : 0 < y.re) (hy1 : 1 ≤ ‖y‖) {C_e : ℝ}
    (h_asymp : ‖F y - (2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ))‖ ≤ C_e * ‖y‖ ^ (-(9 / 2 : ℝ))) : ‖F y‖ ≤ (2 * ceK / Real.sqrt π + C_e) * ‖y‖ ^ (-(5 / 2 : ℝ)) := by
  have hceK := ceK_pos; have hy_ne : y ≠ 0 := fun h => by simp [h] at hy
  have hL : ‖(2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ))‖ = (2 * ceK / Real.sqrt π) * ‖y‖ ^ (-(5 / 2 : ℝ)) := by
    rw [norm_mul, show (2 * ceK / Real.sqrt π : ℂ) = ((2 * ceK / Real.sqrt π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * ceK / Real.sqrt π), show (-(5 / 2 : ℂ)) = ((-(5 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl, norm_cpow_ofReal_exponent hy_ne]
  have h95 : ‖y‖ ^ (-(9 / 2 : ℝ)) ≤ ‖y‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  have hCe : 0 ≤ C_e := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h_asymp) (Real.rpow_pos_of_pos (by linarith) _)
  calc ‖F y‖ = ‖(2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ)) + (F y - (2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ)))‖ := by congr 1; ring
    _ ≤ ‖(2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ))‖ + ‖F y - (2 * ceK / Real.sqrt π : ℂ) * y ^ (-(5 / 2 : ℂ))‖ := norm_add_le _ _
    _ ≤ (2 * ceK / Real.sqrt π) * ‖y‖ ^ (-(5 / 2 : ℝ)) + C_e * ‖y‖ ^ (-(9 / 2 : ℝ)) := by rw [hL]; exact add_le_add le_rfl h_asymp
    _ ≤ (2 * ceK / Real.sqrt π + C_e) * ‖y‖ ^ (-(5 / 2 : ℝ)) := by nlinarith

lemma airyTwistedLaplaceC_ceF1_rhp :
    ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC ceF1 ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨_, h_cont, _, C_lo, hC_lo, hlo⟩ := ceF1_regularity; obtain ⟨CF, _, hF_asymp⟩ := airyTwistedLaplaceC_ceF1_asymp
  exact rhp_bound_52_of_asymp h_cont hC_lo hlo fun {y} hy hy1 => norm_le_add_norm_sub_52 hy hy1 (hF_asymp hy hy1)

/-- **Lemma `P.1(2)` / `U.2` right-half-plane bound for `S₀`:** `‖S̃₀(i c_s w)‖ ≤ C ‖1 + w‖^{-5/2}` on `Re w ≥ 0`. -/
theorem airyTwistedLaplaceC_ceS0_bound :
    ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero) ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨_, h_cont, _, C_lo, hC_lo, hlo⟩ := ceS0_regularity; obtain ⟨C1, hC1, hG1_t⟩ := ceG1_tail_exp_rpow32; obtain ⟨C2, hC2, hG1'_t⟩ := ceG1Deriv_tail_exp_rpow32
  have hG1_int := (airyTwistedLaplaceC_regularity (continuous_ceG1 _) ceG1_integrable hC1 hG1_t).1
  have hG1'_int := (airyTwistedLaplaceC_regularity (continuous_ceG1Deriv _) ceG1Deriv_integral_eq_M.1 hC2 hG1'_t).1
  obtain ⟨CG1, hCG1, hG1_bd⟩ := airyTwistedLaplaceC_ceG1_bound; obtain ⟨CG1', hCG1', hG1'_asymp⟩ := airyTwistedLaplaceC_ceG1Deriv_asymp
  refine rhp_bound_52_of_asymp h_cont hC_lo hlo (C_a := CG1 + (2 * ceK / Real.sqrt π + CG1')) fun {y} hy hy1 => ?_
  have h95 : ‖y‖ ^ (-(9 / 2 : ℝ)) ≤ ‖y‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  rw [show ceS0 (airyZero 1) airyDerivFirstZero = fun u => ceG1 (airyZero 1) u + ceG1Deriv airyDerivFirstZero u from rfl, airyTwistedLaplaceC_add (hG1_int y hy.le) (hG1'_int y hy.le)]
  have htri := (norm_add_le _ _).trans (add_le_add (hG1_bd hy hy1) (norm_le_add_norm_sub_52 hy hy1 (hG1'_asymp hy hy1)))
  nlinarith [Real.rpow_pos_of_pos (by linarith : 0 < ‖y‖) (-(5 / 2 : ℝ))]

/-- **Lemma `U.2` right-half-plane bound for `S_b`:** `‖S̃_b(i c_s w)‖ ≤ C ‖1 + w‖^{-5/2}` on `Re w ≥ 0`. -/
theorem airyTwistedLaplaceC_ceSb_bound (b : ℝ) :
    ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC (ceSb b) ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨C0, hC0, hS0⟩ := airyTwistedLaplaceC_ceS0_bound; obtain ⟨CF, hCF, hF1⟩ := airyTwistedLaplaceC_ceF1_rhp
  refine ⟨C0 + |b| * CF, by positivity, fun w hw => ?_⟩
  have hy_re : 0 ≤ ((ceCs : ℂ) * w).re := by simp [Complex.mul_re, mul_nonneg ceCs_pos.le hw]
  rw [show ceSb b = fun u => ceS0 (airyZero 1) airyDerivFirstZero u - b * ceF1 u from funext fun _ => rfl,
    airyTwistedLaplaceC_sub (ceS0_regularity.1 _ hy_re) (integrable_const_mul_ofReal (ceF1_regularity.1 _ hy_re)), airyTwistedLaplaceC_const_mul]
  calc ‖airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero) ((ceCs : ℂ) * w) - (b : ℂ) * airyTwistedLaplaceC ceF1 ((ceCs : ℂ) * w)‖
      ≤ ‖airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero) ((ceCs : ℂ) * w)‖ + |b| * ‖airyTwistedLaplaceC ceF1 ((ceCs : ℂ) * w)‖ :=
          (norm_sub_le _ _).trans_eq (by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs])
    _ ≤ C0 * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) + |b| * (CF * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := add_le_add (hS0 w hw) (mul_le_mul_of_nonneg_left (hF1 w hw) (abs_nonneg b))
    _ = (C0 + |b| * CF) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by ring

lemma dual_deriv_bound_52 {X : ℝ → ℝ} (hdiff : DifferentiableOn ℂ (airyTwistedLaplaceC X) {y : ℂ | 0 < y.re})
    (hbd : ∃ C > 0, ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :
    ∀ j : ℕ, ∃ C_j > 0, ∀ {c : ℝ}, 2 ≤ c → ∀ τ : ℝ,
      ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC X (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤ C_j * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨C_rhp, hC_rhp, hrhp⟩ := hbd; have h := cauchy_dual_deriv_bound_of_rhp (by norm_num : (0 : ℝ) ≤ 5 / 2) hC_rhp hdiff hrhp
  intro j; obtain ⟨C_j, hC_j, hres⟩ := h j
  exact ⟨C_j, hC_j, fun hc τ => by simpa [show -(5 / 2 : ℝ) / 3 = -(5 / 6 : ℝ) by norm_num, show -(5 / 2 : ℝ) / 2 = -(5 / 4 : ℝ) by norm_num] using hres hc τ⟩

/-- **Lemma `U.2` vertical-line Cauchy derivative bounds for `S₀`:** all `j : ℕ`, `c ≥ 2`, `τ : ℝ`. -/
theorem airyTwistedLaplaceC_ceS0_dual_deriv_bound :
    ∀ j : ℕ, ∃ C_j > 0, ∀ {c : ℝ}, 2 ≤ c → ∀ τ : ℝ,
      ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC (ceS0 (airyZero 1) airyDerivFirstZero)
        (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤ C_j * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) :=
  dual_deriv_bound_52 ceS0_regularity.2.2.1 airyTwistedLaplaceC_ceS0_bound

/-- **Lemma `U.2` vertical-line Cauchy derivative bounds for `S_b`:** all `j : ℕ`, `c ≥ 2`, `τ : ℝ`. -/
theorem airyTwistedLaplaceC_ceSb_dual_deriv_bound (b : ℝ) :
    ∀ j : ℕ, ∃ C_j > 0, ∀ {c : ℝ}, 2 ≤ c → ∀ τ : ℝ,
      ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC (ceSb b)
        (((ceCs * c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤ C_j * c ^ (-(5 / 6 : ℝ)) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) :=
  dual_deriv_bound_52 ((ceS0_regularity.2.2.1.sub (ceF1_regularity.2.2.1.const_mul (b : ℂ))).congr fun y hy => by
    rw [show ceSb b = fun u => ceS0 (airyZero 1) airyDerivFirstZero u - b * ceF1 u from funext fun _ => rfl,
      airyTwistedLaplaceC_sub (ceS0_regularity.1 _ hy.le) (integrable_const_mul_ofReal (ceF1_regularity.1 _ hy.le)), airyTwistedLaplaceC_const_mul]; rfl)
    (airyTwistedLaplaceC_ceSb_bound b)

/-- **Unconditional two-scale origin Laplace decay:** discharges the `hQ0_lap` hypothesis of
`MovingDiagonalSource.twoScale_mellin_origin` for all `p ∈ (1/2, 1)`, `lam > 0`, `R ≥ 0`, and `max 2 (R^3) ≤ c`. -/
theorem twoScaleQ0_real_laplace_bound :
    ∃ C_Q > 0, ∀ {p lam R : ℝ}, p ∈ Ioo (1 / 2 : ℝ) 1 → 0 < lam → 0 ≤ R → ∀ {c : ℝ}, max 2 (R ^ 3) ≤ c →
      |airyTwistedLaplace (twoScaleQ0 p lam R c) (ceCs * c ^ (1 / 3 : ℝ))| ≤ C_Q * c ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨C_E, hCE, hE_bd⟩ := airyTwistedLaplaceC_ceCancelE_dual_deriv_bound 0; obtain ⟨C_P, hCP, hP_bd⟩ := cardinalP_dual_deriv_bound
  refine ⟨C_E + C_P 0, add_pos hCE (hCP 0), fun {p lam R} hp hlam hR {c} hc => ?_⟩
  have hc2 : 2 ≤ c := (le_max_left _ _).trans hc
  have hc_pos : 0 < c := by linarith
  have hc13_pos : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc_pos _
  let ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc_pos _
  have hε_inv : ε⁻¹ = c ^ (1 / 3 : ℝ) := by dsimp [ε]; rw [Real.rpow_neg hc_pos.le, inv_inv]
  have hε_52 : ε ^ (5 / 2 : ℝ) = c ^ (-(5 / 6 : ℝ)) := by dsimp [ε]; rw [← Real.rpow_mul hc_pos.le]; congr 1; norm_num
  let h : ℝ := lam * ε ^ 2; have hh_pos : 0 < h := mul_pos hlam (sq_pos_of_pos hε_pos); let σ : ℝ := Real.sqrt (1 - R * ε)
  have hRε : R * ε ≤ 1 := by
    by_cases hR0 : R = 0
    · simp [hR0]
    · have hRc : R ≤ c ^ (1 / 3 : ℝ) := by rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]; exact (Real.pow_rpow_inv_natCast hR (by norm_num : 3 ≠ 0)).symm.le.trans (Real.rpow_le_rpow (by positivity) ((le_max_right _ _).trans hc) (by positivity))
      exact (mul_le_mul_of_nonneg_right hRc (inv_nonneg.mpr hc13_pos.le)).trans_eq (mul_inv_cancel₀ hc13_pos.ne') |>.trans' (by dsimp [ε]; rw [Real.rpow_neg hc_pos.le])
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _; have hσ1 : σ ≤ 1 := Real.sqrt_le_one.mpr (sub_le_self _ (mul_nonneg hR hε_pos.le))
  let x : ℝ := ceCs * c ^ (1 / 3 : ℝ); have hx_nn : 0 ≤ x := mul_nonneg ceCs_pos.le hc13_pos.le
  have hP_int : Integrable (fun u : ℝ => (cardinalP p h σ u : ℂ) * Complex.exp ((x : ℂ) * (u : ℂ))) := by
    have hP_real := (cardinalPQ_integrals (by linarith [hp.1] : 0 < p) hh_pos.le hσ0 hσ1).1
    have hmeas : AEStronglyMeasurable (fun u : ℝ => (cardinalP p h σ u : ℂ) * Complex.exp ((x : ℂ) * (u : ℂ))) volume :=
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hP_real.aestronglyMeasurable).mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    let B0 : ℝ → ℝ := fun u => if u < 0 then ‖cardinalP p h σ u‖ else 23 * (-airyDerivFirstZero) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ) + (x + 1) * u)
    have hB0_int : Integrable B0 := integrable_if_neg_pos hP_real.norm.integrableOn ((integrableOn_exp_neg_rpow32_add (by norm_num : (0 : ℝ) < 2 / 3) (by linarith)).const_mul (23 * (-airyDerivFirstZero)))
    refine hB0_int.mono' hmeas (ae_of_all _ fun u => ?_)
    rw [norm_mul, Complex.norm_real, Complex.norm_exp, show ((x : ℂ) * (u : ℂ)).re = x * u by simp [Complex.mul_re]]; dsimp [B0]; split_ifs with hu
    · exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hx_nn hu.le))
    · have hu0 : 0 ≤ u := not_lt.mp hu; have hH_le := cardinalHC_norm_sq_le (by linarith [hp.1] : 0 < p) hh_pos.le hσ0 hσ1 (u : ℂ)
      have hs := cardinalH_hasSum (by linarith [hp.1] : 0 < p) hh_pos.le hσ0 hσ1
      have hP_eq : cardinalP p h σ u = ‖cardinalHC p h σ (u : ℂ)‖ ^ 2 := by
        unfold cardinalP; rw [show cardinalHC p h σ (u : ℂ) = (cardinalH p h σ u : ℂ) by rw [← (hs.1 (u : ℂ)).tsum_eq, ← (hs.2 u).tsum_eq]; push_cast; exact tsum_congr fun n => by rw [cohnLC_ofReal], Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0, ← hP_eq, airyEnv_ofReal_nonneg hu0] at hH_le
      have hP_nn : 0 ≤ cardinalP p h σ u := by unfold cardinalP; positivity
      rw [abs_of_nonneg hP_nn]
      calc cardinalP p h σ u * Real.exp (x * u) ≤ 23 * (-airyDerivFirstZero) * Real.exp u * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ)) * Real.exp (x * u) := by
            have hma : 0 ≤ 23 * (-airyDerivFirstZero) := by have := airyDerivFirstZero_spec.2.1; linarith
            have h1u : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
            have h42 := Real.exp_le_exp.mpr (by linarith [Real.rpow_nonneg hu0 (3 / 2 : ℝ)] : -(4 / 3 : ℝ) * u ^ (3 / 2 : ℝ) ≤ -(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ))
            exact (mul_le_mul_of_nonneg_right hH_le (Real.exp_pos _).le).trans (by gcongr)
        _ = 23 * (-airyDerivFirstZero) * Real.exp (-(2 / 3 : ℝ) * u ^ (3 / 2 : ℝ) + (x + 1) * u) := by rw [mul_assoc (23 * _), mul_assoc (23 * _), ← Real.exp_add, ← Real.exp_add]; congr 2; ring
  have hQ0_fn : twoScaleQ0 p lam R c = fun u => (-1) * ceCancelE u - cardinalP p h σ u := funext fun u => by unfold twoScaleQ0 cardinalQ ceCancelE; ring
  have hlap_eq : (airyTwistedLaplace (twoScaleQ0 p lam R c) x : ℂ) = -airyTwistedLaplaceC ceCancelE (x : ℂ) - airyTwistedLaplaceC (cardinalP p h σ) (x : ℂ) := by
    rw [← airyTwistedLaplaceC_ofReal, hQ0_fn, airyTwistedLaplaceC_sub (integrable_const_mul_ofReal (ceCancelE_regularity.1 (x : ℂ) (by simpa using hx_nn))) hP_int, airyTwistedLaplaceC_const_mul]; simp
  have hE0 := hE_bd hc2 0; simp only [iteratedDeriv_zero, Complex.ofReal_zero, mul_zero, sub_zero, mul_one, zero_pow two_ne_zero, add_zero, Real.one_rpow] at hE0
  have hE0' : ‖airyTwistedLaplaceC ceCancelE (x : ℂ)‖ ≤ C_E * c ^ (-(5 / 6 : ℝ)) :=
    hE0.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : -(3 / 2 : ℝ) ≤ -(5 / 6 : ℝ))) hCE.le)
  have hP0 := @hP_bd p h σ hp hh_pos hσ0 hσ1 0 (by norm_num) ε hε_pos 0
  simp only [iteratedDeriv_zero, Complex.ofReal_zero, mul_zero, sub_zero, mul_one, hε_inv, hε_52, zero_pow two_ne_zero, add_zero, Real.one_rpow] at hP0
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hlap_eq]; exact (norm_sub_le _ _).trans (by rw [norm_neg]; exact (add_le_add hE0' hP0).trans_eq (by ring))

/-! ### Section 5: Axiom hygiene (`#guard_msgs`) -/

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceF1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceF1_eq

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceG1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceG1_eq

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceG1Deriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceG1Deriv_eq

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceF1_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceF1_asymp

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceG1Deriv_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceG1Deriv_asymp

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceG1_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceG1_bound

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceCancelE_rhp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceCancelE_rhp

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceCancelE_dual_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceCancelE_dual_deriv_bound

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceS0_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceS0_bound

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceSb_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceSb_bound

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceS0_dual_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceS0_dual_deriv_bound

/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplaceC_ceSb_dual_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_ceSb_dual_deriv_bound

/-- info: 'FormalResearch.CohnElkies.twoScaleQ0_real_laplace_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoScaleQ0_real_laplace_bound

/-- info: 'FormalResearch.CohnElkies.gaussian_1d_ibp_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gaussian_1d_ibp_general

/-- info: 'FormalResearch.CohnElkies.gaussian_2d_ibp_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gaussian_2d_ibp_general
