module

public import FormalResearch.CohnElkies.MellinKernel
public import FormalResearch.CohnElkies.FourierL1Interp
public import FormalResearch.CohnElkies.TwoSaddleContraction
public import FormalResearch.CohnElkies.AiryGaussianTransform
public import FormalResearch.Special.AiryPwsClass
public import FormalResearch.Special.AiryCftWeights
public import FormalResearch.Special.AiryKernelOpSharp

/-!
# Mellin main-edge kernel, B-spline multipliers, and diagonal vector transfer (`O.11ae`, `GT.2b`)

Formalisation of CFT Paper I main-edge kernel and global-transfer multiplier lemmas:
* B-spline Laplace/Mellin multiplier `bsplineE1 ζ = (1 - e^{-ζ}) / ζ` (`= 1` at `0`) and its
  `m`-fold powers `bsplineMult β m` (reflected vertical line) and `bsplineImag β m` (imaginary axis).
* Lemma `O.11ae` (`CFT/sign_uncertainty/paper/ce_o1_route.tex`, `(ceo:O11ae.2)`–`(ceo:O11ae.7)`):
  regularity and symbol bounds of `edgeR`, complex-amplitude wrapper `pf3_kernel_bound_complex`,
  concrete imaginary-edge amplitude `mainEdgeAmp` (`H²` and `‖R' a_c‖₂` bounds), `L¹` bound
  `‖K_c‖_{L¹} = O(c^{-1/2})` via `fourier_L1_le_sqrt_mul_H1`, rapid decay `O(c^{-2} y^{-2})` on
  `y ≥ d > 0` via `pf3_kernel_bound_complex`, exact Fubini kernel identity, and `(mellinK0, airyFtilde)`
  bridge.
* Lemma `GT.2b(1)–(2)` (`CFT/sign_uncertainty/paper/ce_o1_global_transfer.tex`, `(cegt:eqGT2b)`):
  exact vector Gaussian transform for diagonal mixtures `diagAirySource w`, uniform vertical-line
  Cauchy derivative bounds (`β ∈ {0, 1}`, plus `(ceo:O11n.11)`), general Leibniz product bound with
  `bsplineMult`, combined `θ 𝒮_h + γ ε S₀` corollary, and explicit non-vacuity witness.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real FourierTransform ComplexInnerProductSpace

namespace FormalResearch.CohnElkies

open FormalResearch.Special
open FormalResearch.Asymptotics

/-! ## Section 1: Cauchy helper and B-spline Mellin/Laplace multiplier `E₁(ζ)` -/

private lemma holomorphic_real_contDiff_and_cauchy {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (hR : ∀ t : ℝ, (t : ℂ) ∈ U) {r : ℝ} (hr : 0 < r) (hball : ∀ τ : ℝ, Metric.closedBall (τ : ℂ) r ⊆ U)
    {B : ℝ → ℝ} (hB : ∀ τ : ℝ, ∀ ω ∈ Metric.sphere (τ : ℂ) r, ‖F ω‖ ≤ B τ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (t : ℂ)) ∧
      ∀ (j : ℕ) (τ : ℝ), ‖iteratedDeriv j (fun t : ℝ => F (t : ℂ)) τ‖ ≤ j.factorial * B τ / r ^ j := by
  have hC_on : ContDiffOn ℂ (⊤ : ℕ∞) F U := (hF.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F (t : ℂ)) := contDiff_iff_contDiffAt.mpr fun t =>
    ((hC_on.contDiffAt (hU.mem_nhds (hR t))).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
  have hiter : ∀ (j : ℕ) (t : ℝ), iteratedDeriv j (fun s : ℝ => F (s : ℂ)) t = iteratedDeriv j F (t : ℂ) := by
    intro j; induction j with
    | zero => intro t; simp
    | succ k ih =>
      intro t; rw [iteratedDeriv_succ, show iteratedDeriv k (fun s : ℝ => F (s : ℂ)) = fun s : ℝ => iteratedDeriv k F (s : ℂ) from funext ih, iteratedDeriv_succ]
      have hwk := hC_on.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast WithTop.coe_lt_top k) hU.uniqueDiffOn
      exact (((hwk _ (hR t)).differentiableAt (hU.mem_nhds (hR t))).congr_of_eventuallyEq
        (Filter.eventually_of_mem (hU.mem_nhds (hR t)) fun z hz => (iteratedDerivWithin_of_isOpen hU hz).symm) |>.hasDerivAt.comp_ofReal).deriv
  refine ⟨hC, fun j τ => ?_⟩; rw [hiter j τ]
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    ⟨hF.mono (Metric.ball_subset_closedBall.trans (hball τ)), (hF.continuousOn.mono (hball τ)).mono Metric.closure_ball_subset_closedBall⟩ (hB τ)

private lemma norm_one_sub_I_mul_ge {τ : ℝ} {ω : ℂ} (hdist : ‖ω - (τ : ℂ)‖ ≤ 1 / 2) :
    Real.sqrt (1 + τ ^ 2) / 2 ≤ ‖1 - Complex.I * ω‖ ∧ (1 + |τ|) / 16 ≤ ‖1 - Complex.I * ω‖ := by
  have hτ_norm : ‖1 - Complex.I * (τ : ℂ)‖ = Real.sqrt (1 + τ ^ 2) := by rw [Complex.norm_def, Complex.normSq_apply]; simp [sq]
  have htri : ‖1 - Complex.I * (τ : ℂ)‖ ≤ ‖1 - Complex.I * ω‖ + 1 / 2 :=
    calc ‖1 - Complex.I * (τ : ℂ)‖ = ‖(1 - Complex.I * ω) + Complex.I * (ω - (τ : ℂ))‖ := by congr 1; ring
      _ ≤ ‖1 - Complex.I * ω‖ + ‖Complex.I * (ω - (τ : ℂ))‖ := norm_add_le _ _
      _ ≤ ‖1 - Complex.I * ω‖ + 1 / 2 := by rw [norm_mul, Complex.norm_I, one_mul]; linarith
  have h1_ge : 1 ≤ ‖1 - Complex.I * (τ : ℂ)‖ := hτ_norm ▸ Real.one_le_sqrt.mpr (by linarith [sq_nonneg τ])
  have hsq : 1 + |τ| ≤ Real.sqrt 2 * Real.sqrt (1 + τ ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]; exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (1 - |τ|), abs_nonneg τ, sq_abs τ])
  have hs2 : Real.sqrt 2 ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  exact ⟨by linarith, by nlinarith⟩

/-- B-spline Laplace/Mellin multiplier `E₁(ζ) = (1 - e^{-ζ}) / ζ`, extended continuously by `1` at `0`. -/
noncomputable def bsplineE1 (ζ : ℂ) : ℂ := if ζ = 0 then 1 else (1 - Complex.exp (-ζ)) / ζ

/-- Moment integral `I_l(ζ) = ∫₀¹ s^l e^{-ζ s} ds` representing `(-1)^l E₁^{(l)}(ζ)`. -/
noncomputable def bsplineKernel (l : ℕ) (ζ : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, (s : ℂ) ^ l * Complex.exp (-ζ * (s : ℂ))

@[simp] lemma bsplineE1_zero : bsplineE1 0 = 1 := by simp [bsplineE1]

lemma bsplineE1_eq_integral (ζ : ℂ) : bsplineE1 ζ = bsplineKernel 0 ζ := by
  unfold bsplineE1 bsplineKernel; by_cases hζ : ζ = 0; · simp [hζ]
  simp only [hζ, ↓reduceIte, pow_zero, one_mul]
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => -Complex.exp (-ζ * (t : ℂ)) / ζ) (Complex.exp (-ζ * (s : ℂ))) s := fun s _ =>
    ((((hasDerivAt_id' s).ofReal_comp.const_mul (-ζ)).cexp.neg.div_const ζ)).congr_deriv (by push_cast; field_simp [hζ])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((Continuous.cexp (by fun_prop)).intervalIntegrable 0 1)]; simp; ring

private lemma bsplineKernel_eq_setIntegral (l : ℕ) (ζ : ℂ) :
    bsplineKernel l ζ = ∫ s in Ioc (0 : ℝ) 1, (s : ℂ) ^ l * Complex.exp (-ζ * (s : ℂ)) := by
  rw [bsplineKernel, intervalIntegral.integral_of_le zero_le_one]

theorem hasDerivAt_bsplineKernel (l : ℕ) (ζ : ℂ) : HasDerivAt (bsplineKernel l) (-bsplineKernel (l + 1) ζ) ζ := by
  let F : ℂ → ℝ → ℂ := fun z s => (s : ℂ) ^ l * Complex.exp (-z * (s : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z s => -((s : ℂ) ^ (l + 1) * Complex.exp (-z * (s : ℂ)))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc (0 : ℝ) 1)) (F := F) (F' := F')
    (Metric.ball_mem_nhds ζ one_pos) (Eventually.of_forall fun z => (by fun_prop : Continuous fun s : ℝ => F z s).aestronglyMeasurable)
    ((by fun_prop : Continuous fun s : ℝ => F ζ s).integrableOn_Ioc) (by fun_prop : Continuous fun s : ℝ => F' ζ s).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioc).mono fun s hs z hz => by
      have hnorm : ‖(s : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1.le]; exact hs.2
      have hz' : ‖z - ζ‖ < 1 := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz
      have hre : (-z * (s : ℂ)).re ≤ ‖ζ‖ + 1 := (Complex.re_le_norm _).trans (by
        rw [norm_mul, norm_neg]; exact (mul_le_mul (by linarith [norm_le_insert' z ζ]) hnorm (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
      calc ‖F' z s‖ = ‖(s : ℂ)‖ ^ (l + 1) * Real.exp (-z * (s : ℂ)).re := by simp [F', norm_pow, Complex.norm_exp]
        _ ≤ 1 ^ (l + 1) * Real.exp (‖ζ‖ + 1) := by gcongr
        _ = Real.exp (‖ζ‖ + 1) := by simp)
    (integrable_const (Real.exp (‖ζ‖ + 1))) (ae_of_all _ fun s z _ => by
      have h1 : HasDerivAt (fun w : ℂ => -w * (s : ℂ)) (-(s : ℂ)) z := by simpa using ((hasDerivAt_id z).neg.mul_const (s : ℂ))
      convert (h1.cexp.const_mul ((s : ℂ) ^ l)) using 1
      simp only [F', pow_succ]; ring)
  refine (hd.2.congr_of_eventuallyEq (Eventually.of_forall fun z => bsplineKernel_eq_setIntegral l z)).congr_deriv ?_
  simp only [F', integral_neg, bsplineKernel_eq_setIntegral]

theorem differentiable_bsplineE1 : Differentiable ℂ bsplineE1 := by
  rw [show bsplineE1 = bsplineKernel 0 from funext bsplineE1_eq_integral]; exact fun ζ => (hasDerivAt_bsplineKernel 0 ζ).differentiableAt

theorem contDiff_bsplineE1 : ContDiff ℂ (⊤ : ℕ∞) bsplineE1 :=
  contDiffOn_univ.mp ((differentiable_bsplineE1.differentiableOn.analyticOnNhd isOpen_univ).contDiffOn uniqueDiffOn_univ)

lemma iteratedDeriv_bsplineKernel (j l : ℕ) (ζ : ℂ) : iteratedDeriv j (bsplineKernel l) ζ = (-1 : ℂ) ^ j * bsplineKernel (l + j) ζ := by
  induction j generalizing l with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', show deriv (bsplineKernel l) = fun z => -bsplineKernel (l + 1) z from funext fun z => (hasDerivAt_bsplineKernel l z).deriv,
      iteratedDeriv_fun_neg, ih (l + 1), pow_succ, show l + 1 + k = l + (k + 1) by omega]; ring

theorem iteratedDeriv_bsplineE1 (l : ℕ) (ζ : ℂ) : iteratedDeriv l bsplineE1 ζ = (-1 : ℂ) ^ l * bsplineKernel l ζ := by
  rw [show bsplineE1 = bsplineKernel 0 from funext bsplineE1_eq_integral, iteratedDeriv_bsplineKernel l 0 ζ, zero_add]

theorem norm_bsplineKernel_le_of_re_ge {l : ℕ} {ζ : ℂ} {σ : ℝ} (hσ : 0 ≤ σ) (hζ : -σ ≤ ζ.re) : ‖bsplineKernel l ζ‖ ≤ Real.exp σ := by
  rw [bsplineKernel_eq_setIntegral]; refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ s in Ioc (0 : ℝ) 1, ‖(s : ℂ) ^ l * Complex.exp (-ζ * (s : ℂ))‖
      ≤ ∫ _ in Ioc (0 : ℝ) 1, Real.exp σ := integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (integrableOn_const (by simp))
          ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => by
            have hre : (-ζ * (s : ℂ)).re ≤ σ := by
              simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
              exact (mul_le_mul_of_nonneg_right (by linarith) hs.1.le).trans ((mul_le_mul_of_nonneg_left hs.2 hσ).trans_eq (mul_one σ))
            have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1.le]; exact hs.2
            calc ‖(s : ℂ) ^ l * Complex.exp (-ζ * (s : ℂ))‖ = |s| ^ l * Real.exp (-ζ * (s : ℂ)).re := by simp [norm_pow, Complex.norm_real, Complex.norm_exp]
              _ ≤ 1 ^ l * Real.exp σ := by gcongr
              _ = Real.exp σ := by simp)
    _ = Real.exp σ := by simp [Measure.real]

theorem norm_bsplineKernel_le_inv_of_re_nonneg {l : ℕ} {ζ : ℂ} (hζ : 0 ≤ ζ.re) (hζ0 : ζ ≠ 0) : ‖bsplineKernel l ζ‖ ≤ (l + 2 : ℝ) * ‖ζ‖⁻¹ := by
  have hmul : ‖ζ‖ * ‖bsplineKernel l ζ‖ ≤ (l + 2 : ℝ) := by
    cases l with
    | zero =>
      rw [← norm_mul, show ζ * bsplineKernel 0 ζ = 1 - Complex.exp (-ζ) by rw [← bsplineE1_eq_integral]; simp [bsplineE1, hζ0, mul_div_cancel₀]]
      calc ‖1 - Complex.exp (-ζ)‖ ≤ 1 + Real.exp (-ζ.re) := (norm_sub_le _ _).trans (by simp [Complex.norm_exp])
        _ ≤ ((0 : ℕ) + 2 : ℝ) := by have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hζ); norm_num; linarith
    | succ k =>
      let F : ℝ → ℂ := fun s => (s : ℂ) ^ (k + 1) * Complex.exp (-ζ * (s : ℂ))
      let f : ℝ → ℂ := fun s => (k + 1 : ℂ) * ((s : ℂ) ^ k * Complex.exp (-ζ * (s : ℂ))) - ζ * ((s : ℂ) ^ (k + 1) * Complex.exp (-ζ * (s : ℂ)))
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1) (f := F) (f' := f)
        (fun s _ => (((hasDerivAt_id' s).ofReal_comp.pow (k + 1)).mul (((hasDerivAt_id' s).ofReal_comp.const_mul (-ζ)).cexp)).congr_deriv
          (by dsimp [f]; push_cast; ring)) ((by fun_prop : Continuous f).intervalIntegrable 0 1)
      have hsub : F 1 - F 0 = Complex.exp (-ζ) := by
        show ((1 : ℝ) : ℂ) ^ (k + 1) * Complex.exp (-ζ * ((1 : ℝ) : ℂ)) - ((0 : ℝ) : ℂ) ^ (k + 1) * Complex.exp (-ζ * ((0 : ℝ) : ℂ)) = _; simp
      have hint_sub : ∫ s in (0 : ℝ)..1, f s = (k + 1 : ℂ) * bsplineKernel k ζ - ζ * bsplineKernel (k + 1) ζ := by
        dsimp [f]; rw [intervalIntegral.integral_sub ((by fun_prop : Continuous fun s : ℝ => (k + 1 : ℂ) * _).intervalIntegrable 0 1)
          ((by fun_prop : Continuous fun s : ℝ => ζ * _).intervalIntegrable 0 1), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]; rfl
      rw [hint_sub, hsub] at hftc
      have hident : ζ * bsplineKernel (k + 1) ζ = (k + 1 : ℂ) * bsplineKernel k ζ - Complex.exp (-ζ) := by linear_combination -hftc
      have hk_norm : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by rw [show (k + 1 : ℂ) = (((k + 1 : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [← norm_mul, hident]; calc ‖(k + 1 : ℂ) * bsplineKernel k ζ - Complex.exp (-ζ)‖
          ≤ (k + 1 : ℝ) * ‖bsplineKernel k ζ‖ + Real.exp (-ζ.re) := by refine (norm_sub_le _ _).trans ?_; rw [norm_mul, hk_norm, Complex.norm_exp, neg_re]
        _ ≤ (k + 1 : ℝ) * Real.exp 0 + 1 := by gcongr; exact norm_bsplineKernel_le_of_re_ge le_rfl (by linarith); exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hζ)
        _ ≤ ((k + 1 : ℕ) + 2 : ℝ) := by rw [Real.exp_zero, mul_one]; push_cast; linarith
  have hpos := norm_pos_iff.mpr hζ0
  calc ‖bsplineKernel l ζ‖ = ‖ζ‖⁻¹ * (‖ζ‖ * ‖bsplineKernel l ζ‖) := by field_simp [hpos.ne']
    _ ≤ (l + 2 : ℝ) * ‖ζ‖⁻¹ := by rw [mul_comm]; gcongr

theorem norm_iteratedDeriv_bsplineE1_le (l : ℕ) {ζ : ℂ} (hζ : 0 ≤ ζ.re) :
    ‖iteratedDeriv l bsplineE1 ζ‖ ≤ 1 ∧ (ζ ≠ 0 → ‖iteratedDeriv l bsplineE1 ζ‖ ≤ (l + 2 : ℝ) * ‖ζ‖⁻¹) ∧ ‖iteratedDeriv l bsplineE1 ζ‖ ≤ (l + 3 : ℝ) / (1 + ‖ζ‖) := by
  have heq : ‖iteratedDeriv l bsplineE1 ζ‖ = ‖bsplineKernel l ζ‖ := by rw [iteratedDeriv_bsplineE1, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have h1 : ‖iteratedDeriv l bsplineE1 ζ‖ ≤ 1 := by rw [heq]; simpa using norm_bsplineKernel_le_of_re_ge le_rfl (by linarith)
  have h2 : ζ ≠ 0 → ‖iteratedDeriv l bsplineE1 ζ‖ ≤ (l + 2 : ℝ) * ‖ζ‖⁻¹ := fun hζ0 => heq ▸ norm_bsplineKernel_le_inv_of_re_nonneg hζ hζ0
  refine ⟨h1, h2, ?_⟩; rw [le_div_iff₀ (by positivity)]
  by_cases hζ0 : ζ = 0; · subst hζ0; simp only [norm_zero, add_zero, mul_one]; linarith
  have hp := norm_pos_iff.mpr hζ0
  have hmul : ‖iteratedDeriv l bsplineE1 ζ‖ * ‖ζ‖ ≤ (l + 2 : ℝ) := (mul_le_mul_of_nonneg_right (h2 hζ0) (norm_nonneg _)).trans_eq (by field_simp [hp.ne'])
  linarith

lemma norm_iterate_deriv_bsplineE1_le (l : ℕ) {ζ : ℂ} (hζ : 0 ≤ ζ.re) :
    ‖deriv^[l] bsplineE1 ζ‖ ≤ 1 ∧ (ζ ≠ 0 → ‖deriv^[l] bsplineE1 ζ‖ ≤ (l + 2 : ℝ) * ‖ζ‖⁻¹) := by
  rw [← iteratedDeriv_eq_iterate]; exact ⟨(norm_iteratedDeriv_bsplineE1_le l hζ).1, (norm_iteratedDeriv_bsplineE1_le l hζ).2.1⟩

lemma norm_bsplineE1_le_of_re_ge_neg_half {ζ : ℂ} (hζ : -(1 / 2 : ℝ) ≤ ζ.re) : ‖bsplineE1 ζ‖ ≤ 5 / (1 + ‖ζ‖) := by
  have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 < 2 ^ 2 := by rw [sq, ← Real.exp_add, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]; exact Real.exp_one_lt_d9.trans (by norm_num)
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have h1 : ‖bsplineE1 ζ‖ ≤ 2 := by rw [bsplineE1_eq_integral]; exact (norm_bsplineKernel_le_of_re_ge (by norm_num) hζ).trans hexp
  have h2 : ‖ζ‖ * ‖bsplineE1 ζ‖ ≤ 3 := by
    by_cases hζ0 : ζ = 0; · simp [hζ0]
    rw [← norm_mul, show ζ * bsplineE1 ζ = 1 - Complex.exp (-ζ) by simp [bsplineE1, hζ0, mul_div_cancel₀]]
    calc ‖1 - Complex.exp (-ζ)‖ ≤ 1 + Real.exp (-ζ.re) := (norm_sub_le _ _).trans (by simp [Complex.norm_exp])
      _ ≤ 1 + Real.exp (1 / 2 : ℝ) := by gcongr; linarith
      _ ≤ 3 := by linarith
  rw [le_div_iff₀ (by positivity)]; linarith

private lemma bsplineE1_line_sphere_bound {z₀ v : ℂ} (hz₀im : z₀.im = 0) (hvre : v.re = 0) (hvim : v.im ≠ 0)
    (hz₀ : 0 ≤ z₀.re) {τ r : ℝ} (hvr : ‖v‖ * r ≤ 1 / 2) {ω : ℂ} (hdist : ‖ω - (τ : ℂ)‖ = r) :
    ‖bsplineE1 (z₀ + v * ω)‖ ≤ (10 / min 1 |v.im|) * (1 + |τ|)⁻¹ := by
  have hre : -(1 / 2 : ℝ) ≤ (z₀ + v * ω).re := by
    have hdiff : |(z₀ + v * ω).re - (z₀ + v * (τ : ℂ)).re| ≤ 1 / 2 :=
      calc |(z₀ + v * ω).re - (z₀ + v * (τ : ℂ)).re| = |(v * (ω - (τ : ℂ))).re| := by congr 1; simp [mul_sub]
        _ ≤ ‖v * (ω - (τ : ℂ))‖ := Complex.abs_re_le_norm _
        _ ≤ 1 / 2 := by rw [norm_mul, hdist]; exact hvr
    have hre_τ : (z₀ + v * (τ : ℂ)).re = z₀.re := by simp [hvre]
    linarith [(abs_le.mp hdiff).1]
  have hnorm_lb : (1 / 2 : ℝ) * (min 1 |v.im| * (1 + |τ|)) ≤ 1 + ‖z₀ + v * ω‖ := by
    have him_ge : |v.im| * |τ| ≤ ‖z₀ + v * (τ : ℂ)‖ := (by simp [hz₀im, abs_mul] : |v.im| * |τ| = |(z₀ + v * (τ : ℂ)).im|).trans_le (Complex.abs_im_le_norm _)
    have hcτ : min 1 |v.im| * (1 + |τ|) ≤ 1 + ‖z₀ + v * (τ : ℂ)‖ := by nlinarith [min_le_left (1 : ℝ) |v.im|, min_le_right (1 : ℝ) |v.im|, abs_nonneg τ]
    have htri : ‖z₀ + v * (τ : ℂ)‖ ≤ ‖z₀ + v * ω‖ + 1 / 2 :=
      calc ‖z₀ + v * (τ : ℂ)‖ = ‖(z₀ + v * ω) - v * (ω - (τ : ℂ))‖ := by congr 1; ring
        _ ≤ ‖z₀ + v * ω‖ + ‖v * (ω - (τ : ℂ))‖ := norm_sub_le _ _
        _ ≤ ‖z₀ + v * ω‖ + 1 / 2 := by rw [norm_mul, hdist]; linarith
    linarith [mul_le_mul_of_nonneg_left hcτ (by norm_num : (0 : ℝ) ≤ 1 / 2), norm_nonneg (z₀ + v * ω)]
  have hpos_c : 0 < min 1 |v.im| := lt_min one_pos (abs_pos.mpr hvim)
  exact (norm_bsplineE1_le_of_re_ge_neg_half hre).trans ((div_le_div_of_nonneg_left (by norm_num) (by positivity) hnorm_lb).trans_eq (by field_simp; ring))

/-- Reflected vertical-line `m`-fold B-spline multiplier `τ ↦ E₁(β (1 - i τ))^m`. -/
noncomputable def bsplineMult (β : ℝ) (m : ℕ) (τ : ℝ) : ℂ := bsplineE1 ((β : ℂ) * (1 - Complex.I * (τ : ℂ))) ^ m

/-- Imaginary-axis `m`-fold B-spline multiplier `τ ↦ E₁(i β τ)^m`. -/
noncomputable def bsplineImag (β : ℝ) (m : ℕ) (τ : ℝ) : ℂ := bsplineE1 (Complex.I * (β : ℂ) * (τ : ℂ)) ^ m

@[simp] lemma bsplineImag_zero (β : ℝ) (m : ℕ) : bsplineImag β m 0 = 1 := by simp [bsplineImag]

private lemma bsplineAffine_holomorphic_bounds {z₀ v : ℂ} (hz₀ : 0 ≤ z₀.re) (hz₀im : z₀.im = 0)
    (hvre : v.re = 0) (hvim : v.im ≠ 0) (m N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun τ : ℝ => bsplineE1 (z₀ + v * (τ : ℂ)) ^ m) ∧
      ∃ C > 0, ∀ j ≤ N, ∀ τ : ℝ, ‖iteratedDeriv j (fun t : ℝ => bsplineE1 (z₀ + v * (t : ℂ)) ^ m) τ‖ ≤ C * (1 + |τ|) ^ (-(m : ℝ)) := by
  let F : ℂ → ℂ := fun ω => bsplineE1 (z₀ + v * ω) ^ m
  have hF : DifferentiableOn ℂ F Set.univ := fun ω _ =>
    ((differentiable_bsplineE1 (z₀ + v * ω)).comp ω ((differentiable_id ω).const_mul v |>.const_add z₀)).pow m |>.differentiableWithinAt
  let r : ℝ := 1 / (2 * (‖v‖ + 1)); let c₀ : ℝ := min 1 |v.im|; have hr : 0 < r := by positivity
  have hc₀ : 0 < c₀ := lt_min one_pos (abs_pos.mpr hvim); let B₀ : ℝ := (10 / c₀) ^ m
  have hsphere : ∀ (τ : ℝ) (ω : ℂ), ω ∈ Metric.sphere (τ : ℂ) r → ‖F ω‖ ≤ B₀ * (1 + |τ|) ^ (-(m : ℝ)) := fun τ ω hω => by
    have hdist : ‖ω - (τ : ℂ)‖ = r := by simpa [Complex.dist_eq] using Metric.mem_sphere.mp hω
    have hvr : ‖v‖ * r ≤ 1 / 2 := by dsimp [r]; rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith [norm_nonneg v]
    calc ‖F ω‖ = ‖bsplineE1 (z₀ + v * ω)‖ ^ m := norm_pow _ m
      _ ≤ ((10 / c₀) * (1 + |τ|)⁻¹) ^ m := pow_le_pow_left₀ (norm_nonneg _) (bsplineE1_line_sphere_bound hz₀im hvre hvim hz₀ hvr hdist) m
      _ = B₀ * (1 + |τ|) ^ (-(m : ℝ)) := by rw [mul_pow, inv_pow, ← Real.rpow_natCast (1 + |τ|) m, ← Real.rpow_neg (by positivity)]
  obtain ⟨hC, hbd⟩ := holomorphic_real_contDiff_and_cauchy isOpen_univ hF (fun _ => mem_univ _) hr (fun _ => subset_univ _) hsphere
  refine ⟨hC, (N.factorial : ℝ) * B₀ * (max 1 r⁻¹) ^ N, by positivity, fun j hj τ => ?_⟩
  have hjf : (j.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hj
  have hrp : r⁻¹ ^ j ≤ (max 1 r⁻¹) ^ N := (pow_le_pow_left₀ (by positivity) (le_max_right _ _) j).trans (pow_le_pow_right₀ (le_max_left _ _) hj)
  calc ‖iteratedDeriv j (fun t : ℝ => bsplineE1 (z₀ + v * (t : ℂ)) ^ m) τ‖ ≤ (j.factorial : ℝ) * (B₀ * (1 + |τ|) ^ (-(m : ℝ))) / r ^ j := hbd j τ
    _ = (j.factorial : ℝ) * B₀ * r⁻¹ ^ j * (1 + |τ|) ^ (-(m : ℝ)) := by rw [div_eq_mul_inv, inv_pow]; ring
    _ ≤ (N.factorial : ℝ) * B₀ * (max 1 r⁻¹) ^ N * (1 + |τ|) ^ (-(m : ℝ)) := by gcongr

theorem bsplineMult_contDiff (β : ℝ) (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (bsplineMult β m) := by
  rw [show bsplineMult β m = fun τ : ℝ => bsplineE1 ((β : ℂ) + (-(Complex.I * (β : ℂ))) * (τ : ℂ)) ^ m from funext fun τ => by simp only [bsplineMult]; congr 2; ring]
  exact ((contDiff_bsplineE1.restrict_scalars ℝ).comp (contDiff_const.add (contDiff_const.mul Complex.ofRealCLM.contDiff))).pow m

theorem bsplineMult_iteratedDeriv_bound {β : ℝ} (hβ : 0 < β) (m : ℕ) :
    ∃ C > 0, ∀ j ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv j (bsplineMult β m) τ‖ ≤ C * (1 + |τ|) ^ (-(m : ℝ)) := by
  rw [show bsplineMult β m = fun τ : ℝ => bsplineE1 ((β : ℂ) + (-(Complex.I * (β : ℂ))) * (τ : ℂ)) ^ m from funext fun τ => by simp only [bsplineMult]; congr 2; ring]
  exact (bsplineAffine_holomorphic_bounds (by simp [hβ.le]) (by simp) (by simp) (by simp [hβ.ne']) m 2).2

theorem bsplineImag_contDiff (β : ℝ) (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (bsplineImag β m) := by
  rw [show bsplineImag β m = fun τ : ℝ => bsplineE1 (0 + (Complex.I * (β : ℂ)) * (τ : ℂ)) ^ m from funext fun τ => by simp only [bsplineImag, zero_add, mul_assoc]]
  exact ((contDiff_bsplineE1.restrict_scalars ℝ).comp (contDiff_const.add (contDiff_const.mul Complex.ofRealCLM.contDiff))).pow m

theorem bsplineImag_iteratedDeriv_bound {β : ℝ} (hβ : β ≠ 0) (m : ℕ) :
    ∃ C > 0, ∀ j ≤ 3, ∀ τ : ℝ, ‖iteratedDeriv j (bsplineImag β m) τ‖ ≤ C * (1 + |τ|) ^ (-(m : ℝ)) := by
  rw [show bsplineImag β m = fun τ : ℝ => bsplineE1 (0 + (Complex.I * (β : ℂ)) * (τ : ℂ)) ^ m from funext fun τ => by simp only [bsplineImag, zero_add, mul_assoc]]
  exact (bsplineAffine_holomorphic_bounds (by simp) (by simp) (by simp) (by simp [hβ]) m 3).2

/-! ## Section 2: Lemma `O.11ae` (`edgeR`, complex `PF.3`, `L¹` and `y ≥ d` bounds, Fubini) -/

/-- Real main-edge residual phase `R(τ) = ∫₀^τ h_th(π t / 2) dt` (`(ceo:O11ae)`). -/
noncomputable def edgeR (τ : ℝ) : ℝ := ∫ t in (0 : ℝ)..τ, ceHth (Real.pi * t / 2)

lemma edgeR5_eq_I_mul_edgeR (τ : ℝ) : edgeR5 τ = Complex.I * (edgeR τ : ℂ) := by rw [edgeR5_eq_imag_integral]; simp [edgeR]

lemma ceHth_mul_pi_div_two (t : ℝ) :
    ceHth (Real.pi * t / 2) = if t = 0 then 0 else Real.log (Real.tanh (Real.pi * t / 2) / (Real.pi * t / 2)) + Real.pi ^ 2 * t ^ 2 / 12 := by
  by_cases ht : t = 0 <;> [simp [ht, ceHth]; (simp only [ht, ↓reduceIte, ceHth]; ring)]

lemma ceHth_even (x : ℝ) : ceHth (-x) = ceHth x := by simp only [ceHth, Real.tanh_neg, neg_div_neg_eq, neg_sq]

lemma ceHth_nonneg (x : ℝ) : 0 ≤ ceHth x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx; · rw [← ceHth_even]; exact (ceHth_pos (neg_pos.mpr hx)).le
  · simp [ceHth]
  · exact (ceHth_pos hx).le

lemma ceHth_le_sq_div_three (x : ℝ) : ceHth x ≤ x ^ 2 / 3 := by
  have hpos : ∀ t > 0, ceHth t ≤ t ^ 2 / 3 := fun t ht => by
    have hp := ceEll_pos ht; simp only [ceHth, ceEll] at *
    rw [show Real.log (Real.tanh t / t) = -Real.log (t / Real.tanh t) from by rw [← Real.log_inv, inv_div]]; linarith
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [← ceHth_even, show x ^ 2 / 3 = (-x) ^ 2 / 3 by ring]; exact hpos (-x) (neg_pos.mpr hx)
  · simp [ceHth]
  · exact hpos x hx

lemma continuous_ceHth : Continuous ceHth := continuous_iff_continuousAt.mpr fun x => by
  by_cases hx : x = 0
  · subst hx; rw [ContinuousAt, show ceHth 0 = 0 by simp [ceHth]]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using ((continuous_id.pow 2).div_const 3).continuousAt.tendsto (x := (0 : ℝ))) ceHth_nonneg ceHth_le_sq_div_three
  · have hth : Real.tanh x / x ≠ 0 := by
      rcases lt_or_gt_of_ne hx with h | h
      · have : Real.tanh x < 0 := by rw [← neg_neg x, Real.tanh_neg]; linarith [tanh_pos_of_pos (neg_pos.mpr h)]
        exact (div_pos_of_neg_of_neg this h).ne'
      · exact (div_pos (tanh_pos_of_pos h) h).ne'
    have hct : Continuous Real.tanh := by
      rw [show Real.tanh = fun y => Real.sinh y / Real.cosh y from funext Real.tanh_eq_sinh_div_cosh]; exact Real.continuous_sinh.div Real.continuous_cosh fun y => (Real.cosh_pos y).ne'
    exact ((hct.continuousAt.div continuousAt_id hx).log hth).add (by fun_prop)

private lemma sinh_pi_ne_zero {s : ℝ} (hs : s ≠ 0) : Real.sinh (Real.pi * s) ≠ 0 := by
  rcases lt_or_gt_of_ne hs with h | h
  · rw [← neg_neg (Real.pi * s), Real.sinh_neg]; exact (neg_lt_zero.mpr (Real.sinh_pos_iff.mpr (neg_pos.mpr (mul_neg_of_pos_of_neg Real.pi_pos h)))).ne
  · exact (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos h)).ne'

private lemma hasDerivAt_of_continuous_hasDerivAt_ne {f f' : ℝ → ℝ} (hf : Continuous f)
    (hf'0 : ContinuousAt f' 0) (hne : ∀ x ≠ 0, HasDerivAt f (f' x) x) : HasDerivAt f (f' 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]; intro ε hε; obtain ⟨δ, hδ, hclose⟩ := Metric.tendsto_nhds_nhds.mp hf'0 ε hε
  refine ⟨δ, hδ, fun {x} hx0 hxd => ?_⟩
  have hneq : x ≠ 0 := by simpa using hx0
  have hxd' : |x| < δ := by simpa [Real.dist_eq] using hxd
  rcases lt_or_gt_of_ne hneq with hn | hp
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hn hf.continuousOn fun y hy => hne y hy.2.ne
    have hdc := hclose (by rw [Real.dist_eq, sub_zero, abs_of_neg hc.2]; linarith [hc.1, abs_of_neg hn, hxd'])
    have heq : (f x - f 0) / (x - 0) = f' c := by rw [hslope]; field_simp [hneq]; ring
    rwa [slope_def_field, heq]
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hp hf.continuousOn fun y hy => hne y hy.1.ne'
    have hdc := hclose (by rw [Real.dist_eq, sub_zero, abs_of_pos hc.1]; linarith [hc.2, abs_of_pos hp, hxd'])
    have heq : (f x - f 0) / (x - 0) = f' c := by rw [hslope]
    rwa [slope_def_field, heq]

private noncomputable def edgeR1 (τ : ℝ) : ℝ := ceHth (Real.pi * τ / 2)
private noncomputable def edgeR2 (τ : ℝ) : ℝ := edgePhiDeriv2 τ + Real.pi ^ 2 * τ / 6
private noncomputable def edgeR3 (τ : ℝ) : ℝ := if τ = 0 then 0 else edgePhiDeriv3 τ + Real.pi ^ 2 / 6

private lemma continuousAt_edgeR2_zero : ContinuousAt edgeR2 0 := by
  rw [ContinuousAt, show edgeR2 0 = 0 by simp [edgeR2, edgePhiDeriv2]]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using (by fun_prop : Continuous fun t : ℝ => -(Real.pi ^ 2 / 3 * |t|)).continuousAt.tendsto (x := 0))
    (by simpa using (by fun_prop : Continuous fun t : ℝ => Real.pi ^ 2 / 3 * |t|).continuousAt.tendsto (x := 0)) (fun t => ?_) (fun t => ?_) <;> {
      by_cases ht : t = 0; · subst ht; simp [edgeR2, edgePhiDeriv2]
      · have hbd := (edgePhiDeriv2_abs_le ht).trans (min_le_left _ _)
        have hlin : |Real.pi ^ 2 * t / 6| ≤ Real.pi ^ 2 / 6 * |t| := by rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos Real.pi_pos), abs_of_pos (by norm_num : (0 : ℝ) < 6)]; ring_nf; rfl
        dsimp [edgeR2]; linarith [abs_le.mp hbd, abs_le.mp hlin] }

private lemma edgeR1_hasDerivAt (τ : ℝ) : HasDerivAt edgeR1 (edgeR2 τ) τ := by
  have hne : ∀ t ≠ 0, HasDerivAt edgeR1 (edgeR2 t) t := fun t ht => by
    have hce : ∀ s : ℝ, edgeR1 s = -ceEll (Real.pi * s / 2) + Real.pi ^ 2 * s ^ 2 / 12 := fun s => by
      rcases eq_or_ne s 0 with rfl | hs; · simp [edgeR1, ceHth, ceEll]
      · simp only [edgeR1, ceHth, ceEll]; rw [← Real.log_inv, inv_div]; ring_nf
    have hsq : HasDerivAt (fun s : ℝ => Real.pi ^ 2 * s ^ 2 / 12) (Real.pi ^ 2 * t / 6) t := (((hasDerivAt_pow 2 t).const_mul (Real.pi ^ 2)).div_const 12).congr_deriv (by ring)
    rcases lt_or_gt_of_ne ht with htn | htp
    · refine (((m2_bounds (neg_pos.mpr htn)).1.comp t (hasDerivAt_neg t)).neg.add hsq).congr_of_eventuallyEq
        (Eventually.of_forall fun s => by rw [hce s]; simp only [Pi.add_apply, Pi.neg_apply, Function.comp_apply, ceEll, show Real.pi * (-s) / 2 = -(Real.pi * s / 2) by ring, Real.tanh_neg, neg_div_neg_eq]) |>.congr_deriv
        (by simp only [edgeR2, show edgePhiDeriv2 (-t) = -edgePhiDeriv2 t by simp only [edgePhiDeriv2, mul_neg, Real.sinh_neg]; ring]; ring)
    · exact ((m2_bounds htp).1.neg.add hsq).congr_of_eventuallyEq (Eventually.of_forall fun s => by rw [hce s]; rfl) |>.congr_deriv (by simp [edgeR2])
  by_cases hτ : τ = 0; · subst hτ; exact hasDerivAt_of_continuous_hasDerivAt_ne (continuous_ceHth.comp (by fun_prop)) continuousAt_edgeR2_zero hne
  · exact hne τ hτ

private lemma cosh_sinh_poly_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.sinh y ≤ y + y ^ 3 / 6 + y ^ 5 / 60 ∧ 1 + y ^ 2 / 2 + y ^ 4 / 24 ≤ Real.cosh y ∧ Real.cosh y ≤ 1 + y ^ 2 / 2 + y ^ 4 / 24 + y ^ 6 / 360 := by
  have step : ∀ {f g : ℝ → ℝ}, f 0 = 0 → Continuous f → (∀ u, HasDerivAt f (g u) u) → (∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g u) → ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f u := fun hf0 hfc hd hg u hu => by
    simpa [hf0] using (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hfc.continuousOn (fun x _ => (hd x).hasDerivWithinAt) (fun x hx => hg x (interior_subset hx))) ⟨le_rfl, zero_le_one⟩ hu hu.1
  have hc2 : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.cosh u ≤ 2 := fun u hu => by rw [Real.cosh_eq]; linarith [(Real.exp_le_exp.mpr hu.2).trans Real.exp_one_lt_d9.le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.1)]
  have h1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.sinh u ≤ 2 * u := fun u hu => by
    have := step (f := fun t => 2 * t - Real.sinh t) (g := fun t => 2 - Real.cosh t) (by simp) (by fun_prop) (fun t => (((hasDerivAt_id' t).const_mul 2).sub (Real.hasDerivAt_sinh t)).congr_deriv (by ring)) (fun t ht => by linarith [hc2 t ht]) u hu; linarith
  have h2 : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.cosh u ≤ 1 + u ^ 2 := fun u hu => by
    have := step (f := fun t => 1 + t ^ 2 - Real.cosh t) (g := fun t => 2 * t - Real.sinh t) (by simp) (by fun_prop) (fun t => (((hasDerivAt_const t 1).add (hasDerivAt_pow 2 t)).sub (Real.hasDerivAt_cosh t)).congr_deriv (by ring)) (fun t ht => by linarith [h1 t ht]) u hu; linarith
  have h3 : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.sinh u ≤ u + u ^ 3 / 3 := fun u hu => by
    have := step (f := fun t => t + t ^ 3 / 3 - Real.sinh t) (g := fun t => 1 + t ^ 2 - Real.cosh t) (by simp) (by fun_prop) (fun t => (((hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 3)).sub (Real.hasDerivAt_sinh t)).congr_deriv (by ring)) (fun t ht => by linarith [h2 t ht]) u hu; linarith
  have h4 : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.cosh u ≤ 1 + u ^ 2 / 2 + u ^ 4 / 12 := fun u hu => by
    have := step (f := fun t => 1 + t ^ 2 / 2 + t ^ 4 / 12 - Real.cosh t) (g := fun t => t + t ^ 3 / 3 - Real.sinh t) (by simp) (by fun_prop) (fun t => ((((hasDerivAt_const t 1).add ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 12)).sub (Real.hasDerivAt_cosh t)).congr_deriv (by ring)) (fun t ht => by linarith [h3 t ht]) u hu; linarith
  have h5 : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.sinh u ≤ u + u ^ 3 / 6 + u ^ 5 / 60 := fun u hu => by
    have := step (f := fun t => t + t ^ 3 / 6 + t ^ 5 / 60 - Real.sinh t) (g := fun t => 1 + t ^ 2 / 2 + t ^ 4 / 12 - Real.cosh t) (by simp) (by fun_prop) (fun t => ((((hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 6)).add ((hasDerivAt_pow 5 t).div_const 60)).sub (Real.hasDerivAt_sinh t)).congr_deriv (by ring)) (fun t ht => by linarith [h4 t ht]) u hu; linarith
  have h6 : ∀ u ∈ Set.Icc (0 : ℝ) 1, Real.cosh u ≤ 1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 360 := fun u hu => by
    have := step (f := fun t => 1 + t ^ 2 / 2 + t ^ 4 / 24 + t ^ 6 / 360 - Real.cosh t) (g := fun t => t + t ^ 3 / 6 + t ^ 5 / 60 - Real.sinh t) (by simp) (by fun_prop) (fun t => (((((hasDerivAt_const t 1).add ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24)).add ((hasDerivAt_pow 6 t).div_const 360)).sub (Real.hasDerivAt_cosh t)).congr_deriv (by ring)) (fun t ht => by linarith [h5 t ht]) u hu; linarith
  have hl : ∀ u ∈ Set.Icc (0 : ℝ) 1, 1 + u ^ 2 / 2 + u ^ 4 / 24 ≤ Real.cosh u := fun u hu => by
    have := step (f := fun t => Real.cosh t - (1 + t ^ 2 / 2 + t ^ 4 / 24)) (g := fun t => Real.sinh t - (t + t ^ 3 / 6)) (by simp) (by fun_prop) (fun t => ((Real.hasDerivAt_cosh t).sub (((hasDerivAt_const t 1).add ((hasDerivAt_pow 2 t).div_const 2)).add ((hasDerivAt_pow 4 t).div_const 24))).congr_deriv (by ring)) (fun t ht => by linarith [sinh_taylor_lower ht.1, pow_nonneg ht.1 5]) u hu; linarith
  exact ⟨h5 y ⟨hy0, hy1⟩, hl y ⟨hy0, hy1⟩, h6 y ⟨hy0, hy1⟩⟩

private lemma continuousAt_edgeR3_zero : ContinuousAt edgeR3 0 := by
  rw [ContinuousAt, show edgeR3 0 = 0 by simp [edgeR3]]
  have hquad : ∀ t : ℝ, |t| ≤ 1 / Real.pi → |edgeR3 t| ≤ 10 * Real.pi ^ 4 * t ^ 2 := fun t ht => by
    by_cases ht0 : t = 0; · subst ht0; simp [edgeR3]
    have hev : edgeR3 (-t) = edgeR3 t := by simp [edgeR3, edgePhiDeriv3, mul_neg, Real.cosh_neg, Real.sinh_neg]
    suffices ∀ s : ℝ, 0 < s → s ≤ 1 / Real.pi → |edgeR3 s| ≤ 10 * Real.pi ^ 4 * s ^ 2 by
      rcases lt_or_gt_of_ne ht0 with hn | hp; · rw [← hev]; convert this (-t) (neg_pos.mpr hn) (by rwa [abs_of_neg hn] at ht) using 1; ring
      · exact this t hp (by rwa [abs_of_pos hp] at ht)
    intro s hs0 hs1; set y : ℝ := Real.pi * s; have hy0 : 0 < y := mul_pos Real.pi_pos hs0
    have hy1 : y ≤ 1 := (mul_le_mul_of_nonneg_left hs1 Real.pi_pos.le).trans_eq (mul_one_div_cancel Real.pi_ne_zero)
    have hsh_ge : y ≤ Real.sinh y := by linarith [sinh_taylor_lower hy0.le, pow_nonneg hy0.le 3, pow_nonneg hy0.le 5]
    have hsh_pos : 0 < Real.sinh y := lt_of_lt_of_le hy0 hsh_ge
    have hid : edgeR3 s = Real.pi ^ 2 * (6 * Real.sinh y ^ 2 - 6 * y ^ 2 * Real.cosh y + y ^ 2 * Real.sinh y ^ 2) / (6 * y ^ 2 * Real.sinh y ^ 2) := by
      simp only [edgeR3, hs0.ne', ↓reduceIte, edgePhiDeriv3]; field_simp [hy0.ne', hsh_pos.ne']; ring
    obtain ⟨hsh_ub, hch_lb, hch_ub⟩ := cosh_sinh_poly_bounds hy0.le hy1
    have hsh_sq_lb := pow_le_pow_left₀ (by positivity) (sinh_taylor_lower hy0.le) 2; have hsh_sq_ub := pow_le_pow_left₀ hsh_pos.le hsh_ub 2; have hy2 : y ^ 2 ≤ 1 := pow_le_one₀ hy0.le hy1
    have hnum_abs : |6 * Real.sinh y ^ 2 - 6 * y ^ 2 * Real.cosh y + y ^ 2 * Real.sinh y ^ 2| ≤ 10 * y ^ 6 :=
      abs_le.mpr ⟨by nlinarith [pow_nonneg hy0.le 2, pow_nonneg hy0.le 4, pow_nonneg hy0.le 6], by nlinarith [pow_nonneg hy0.le 2, pow_nonneg hy0.le 4, pow_nonneg hy0.le 6]⟩
    have hden_lb : 6 * y ^ 4 ≤ 6 * y ^ 2 * Real.sinh y ^ 2 := by have := pow_le_pow_left₀ hy0.le hsh_ge 2; nlinarith [sq_nonneg y]
    rw [hid, abs_div, abs_mul, abs_of_pos (sq_pos_of_pos Real.pi_pos), abs_of_pos (by positivity : 0 < 6 * y ^ 2 * Real.sinh y ^ 2)]
    calc Real.pi ^ 2 * |6 * Real.sinh y ^ 2 - 6 * y ^ 2 * Real.cosh y + y ^ 2 * Real.sinh y ^ 2| / (6 * y ^ 2 * Real.sinh y ^ 2)
        ≤ Real.pi ^ 2 * (10 * y ^ 6) / (6 * y ^ 4) := by gcongr
      _ = (5 / 3 : ℝ) * Real.pi ^ 2 * y ^ 2 := by field_simp [hy0.ne']; ring
      _ ≤ 10 * Real.pi ^ 4 * s ^ 2 := by simp only [y]; nlinarith [sq_nonneg Real.pi, sq_nonneg s, Real.two_le_pi]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using (by fun_prop : Continuous fun t : ℝ => -(10 * Real.pi ^ 4 * t ^ 2)).continuousAt.tendsto (x := 0))
    (by simpa using (by fun_prop : Continuous fun t : ℝ => 10 * Real.pi ^ 4 * t ^ 2).continuousAt.tendsto (x := 0)) ?_ ?_ <;> {
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < 1 / Real.pi)] with t ht; rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht; linarith [abs_le.mp (hquad t ht.le)] }

private lemma edgeR2_hasDerivAt (τ : ℝ) : HasDerivAt edgeR2 (edgeR3 τ) τ := by
  have hcont2 : Continuous edgeR2 := continuous_iff_continuousAt.mpr fun t => by
    by_cases ht : t = 0; · subst ht; exact continuousAt_edgeR2_zero
    · unfold edgeR2 edgePhiDeriv2; fun_prop (disch := exact mul_ne_zero (mul_ne_zero Real.pi_ne_zero ht) (sinh_pi_ne_zero ht))
  have hne : ∀ t ≠ 0, HasDerivAt edgeR2 (edgeR3 t) t := fun t ht => by
    have heq : ∀ᶠ s in 𝓝 t, edgeR2 s = -s⁻¹ + Real.pi / Real.sinh (Real.pi * s) + Real.pi ^ 2 * s / 6 :=
      Filter.eventually_of_mem ((isOpen_ne (x := (0 : ℝ))).mem_nhds ht) fun s hs => by have hs0 : s ≠ 0 := hs; simp only [edgeR2, edgePhiDeriv2]; field_simp [hs0, Real.pi_ne_zero, sinh_pi_ne_zero hs0]; ring
    have hd_inv : HasDerivAt (fun s : ℝ => -s⁻¹) (t⁻¹ ^ 2) t := (hasDerivAt_inv ht).neg.congr_deriv (by ring)
    have h1 := (Real.hasDerivAt_sinh (Real.pi * t)).comp t (((hasDerivAt_id' t).const_mul Real.pi).congr_deriv (by ring))
    have hd_sh : HasDerivAt (fun s : ℝ => Real.pi / Real.sinh (Real.pi * s)) (-Real.pi ^ 2 * Real.cosh (Real.pi * t) / Real.sinh (Real.pi * t) ^ 2) t :=
      ((h1.inv (sinh_pi_ne_zero ht)).const_mul Real.pi).congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Function.comp_apply, div_eq_mul_inv]) |>.congr_deriv (by simp only [Function.comp_apply]; ring)
    refine ((hd_inv.add hd_sh).add (by simpa using ((hasDerivAt_id' t).const_mul (Real.pi ^ 2)).div_const 6)).congr_of_eventuallyEq heq |>.congr_deriv ?_
    simp only [edgeR3, ht, ↓reduceIte, edgePhiDeriv3]; field_simp [ht, Real.pi_ne_zero, sinh_pi_ne_zero ht]; ring
  by_cases hτ : τ = 0; · subst hτ; exact hasDerivAt_of_continuous_hasDerivAt_ne hcont2 continuousAt_edgeR3_zero hne
  · exact hne τ hτ

theorem hasDerivAt_edgeR (τ : ℝ) : HasDerivAt edgeR (ceHth (Real.pi * τ / 2)) τ := by
  have hcont : Continuous edgeR1 := continuous_ceHth.comp (by fun_prop)
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _) hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

theorem edgeR_contDiff : ContDiff ℝ 3 edgeR := by
  have hcont3 : Continuous edgeR3 := continuous_iff_continuousAt.mpr fun t => by
    by_cases ht : t = 0; · subst ht; exact continuousAt_edgeR3_zero
    · have hc_ne : ContinuousAt (fun s => edgePhiDeriv3 s + Real.pi ^ 2 / 6) t := by
        unfold edgePhiDeriv3; fun_prop (disch := first | positivity | exact pow_ne_zero 2 (mul_ne_zero Real.pi_ne_zero ht) | exact pow_ne_zero 2 (sinh_pi_ne_zero ht))
      exact hc_ne.congr (Filter.eventually_of_mem ((isOpen_ne (x := (0 : ℝ))).mem_nhds ht) fun s hs => by simp [edgeR3, show s ≠ 0 from hs])
  have hd2 : ContDiff ℝ (0 : ℕ) edgeR3 := contDiff_zero.mpr hcont3
  have hd1 : ContDiff ℝ (1 : ℕ) edgeR2 := (contDiff_succ_iff_deriv (n := 0)).mpr ⟨fun t => (edgeR2_hasDerivAt t).differentiableAt, by simp, by rwa [show deriv edgeR2 = edgeR3 from funext fun t => (edgeR2_hasDerivAt t).deriv]⟩
  have hd0 : ContDiff ℝ (2 : ℕ) edgeR1 := (contDiff_succ_iff_deriv (n := 1)).mpr ⟨fun t => (edgeR1_hasDerivAt t).differentiableAt, by simp, by rwa [show deriv edgeR1 = edgeR2 from funext fun t => (edgeR1_hasDerivAt t).deriv]⟩
  exact (contDiff_succ_iff_deriv (n := 2)).mpr ⟨fun t => (hasDerivAt_edgeR t).differentiableAt, by simp, by rwa [show deriv edgeR = edgeR1 from funext fun t => (hasDerivAt_edgeR t).deriv]⟩

private lemma continuous_edgeR : Continuous edgeR := edgeR_contDiff.continuous

theorem edgeR_deriv_bounds (τ : ℝ) :
    0 ≤ iteratedDeriv 1 edgeR τ ∧ iteratedDeriv 1 edgeR τ ≤ (Real.pi ^ 2 / 12) * (1 + |τ|) ^ 2 ∧
      |iteratedDeriv 2 edgeR τ| ≤ (Real.pi ^ 2 / 3) * (1 + |τ|) ∧ |iteratedDeriv 3 edgeR τ| ≤ Real.pi ^ 2 / 2 := by
  have h1 : iteratedDeriv 1 edgeR = edgeR1 := funext fun t => by rw [iteratedDeriv_one]; exact (hasDerivAt_edgeR t).deriv
  have h2 : iteratedDeriv 2 edgeR = edgeR2 := funext fun t => by rw [iteratedDeriv_succ, h1]; exact (edgeR1_hasDerivAt t).deriv
  have h3 : iteratedDeriv 3 edgeR = edgeR3 := funext fun t => by rw [iteratedDeriv_succ, h2]; exact (edgeR2_hasDerivAt t).deriv
  rw [h1, h2, h3]; refine ⟨ceHth_nonneg _, ?_, ?_, ?_⟩
  · calc edgeR1 τ ≤ (Real.pi * τ / 2) ^ 2 / 3 := ceHth_le_sq_div_three _
      _ = (Real.pi ^ 2 / 12) * |τ| ^ 2 := by rw [sq_abs]; ring
      _ ≤ (Real.pi ^ 2 / 12) * (1 + |τ|) ^ 2 := by gcongr; linarith
  · by_cases hτ : τ = 0; · subst hτ; simp [edgeR2, edgePhiDeriv2]; positivity
    have hbd := (edgePhiDeriv2_abs_le hτ).trans (min_le_left _ _)
    have hlin : |Real.pi ^ 2 * τ / 6| ≤ Real.pi ^ 2 / 6 * |τ| := by rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos Real.pi_pos), abs_of_pos (by norm_num : (0 : ℝ) < 6)]; ring_nf; rfl
    calc |edgeR2 τ| ≤ |edgePhiDeriv2 τ| + |Real.pi ^ 2 * τ / 6| := abs_add_le _ _
      _ ≤ (Real.pi ^ 2 / 3) * |τ| := by linarith
      _ ≤ (Real.pi ^ 2 / 3) * (1 + |τ|) := by gcongr; linarith
  · by_cases hτ : τ = 0; · subst hτ; simp [edgeR3]; positivity
    simp only [edgeR3, hτ, ↓reduceIte]; calc |edgePhiDeriv3 τ + Real.pi ^ 2 / 6| ≤ |edgePhiDeriv3 τ| + |Real.pi ^ 2 / 6| := abs_add_le _ _
      _ ≤ Real.pi ^ 2 / 3 + Real.pi ^ 2 / 6 := by gcongr; exact edgePhiDeriv3_abs_le hτ; rw [abs_of_pos (by positivity)]
      _ = Real.pi ^ 2 / 2 := by ring

private lemma inv_one_add_abs_pow_le_inv_sq {p τ : ℝ} (hp : p ≤ -2) : (1 + |τ|) ^ p ≤ 2 * (1 + τ ^ 2)⁻¹ := by
  have hrp := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ] : 1 ≤ 1 + |τ|) hp; rw [Real.rpow_neg (by positivity), Real.rpow_two] at hrp
  calc (1 + |τ|) ^ p ≤ ((1 + |τ|) ^ 2)⁻¹ := hrp
    _ ≤ (1 + τ ^ 2)⁻¹ := by gcongr; nlinarith [abs_nonneg τ, sq_abs τ]
    _ ≤ 2 * (1 + τ ^ 2)⁻¹ := by linarith [inv_nonneg.mpr (by positivity : 0 ≤ 1 + τ ^ 2)]

private lemma inv_one_add_abs_sq_le_sqrt_inv {τ : ℝ} : (1 + |τ|) ^ (-2 : ℝ) ≤ (1 + τ ^ 2) ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_two, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  have h1 : Real.sqrt (1 + τ ^ 2) ≤ 1 + τ ^ 2 := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg τ, sq_nonneg (1 + τ ^ 2)]⟩
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (h1.trans (by nlinarith [abs_nonneg τ, sq_abs τ]))

/-- Main-edge oscillatory kernel `K_c(y) = ∫ a(τ) exp(i c (y τ + R(τ))) dτ` (`(ceo:O11ae)`). -/
noncomputable def mainEdgeKernel (a : ℝ → ℂ) (c y : ℝ) : ℂ :=
  ∫ τ : ℝ, a τ * Complex.exp (Complex.I * (c : ℂ) * ((y * τ + edgeR τ : ℝ) : ℂ))

/-- Complex-amplitude wrapper around `TwoSaddleContraction.pf3_kernel_bound`. -/
theorem pf3_kernel_bound_complex {a : ℝ → ℂ} {R : ℝ → ℝ} {m : ℕ} (hm : 4 ≤ m)
    {C_a C₂ C₃ y₀ c : ℝ} (hc : 2 ≤ c) (hy₀ : 0 < y₀) (ha_cd : ContDiff ℝ 2 a) (hR_cd : ContDiff ℝ 3 R)
    (hR1_nn : ∀ τ, 0 ≤ iteratedDeriv 1 R τ) (hR2_bd : ∀ τ, |iteratedDeriv 2 R τ| ≤ C₂ * (1 + |τ|)) (hR3_bd : ∀ τ, |iteratedDeriv 3 R τ| ≤ C₃)
    (ha_bd : ∀ j ≤ 2, ∀ τ, ‖iteratedDeriv j a τ‖ ≤ C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2)) {y : ℝ} (hy : y₀ ≤ y) :
    ‖∫ τ : ℝ, a τ * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))‖ ≤ 2 * pf3Const C_a C₂ C₃ y₀ * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) := by
  let a_re : ℝ → ℝ := fun τ => (a τ).re; let a_im : ℝ → ℝ := fun τ => (a τ).im
  have hclm_iter : ∀ (L : ℂ →L[ℝ] ℝ) {j : ℕ}, j ≤ 2 → ∀ τ, iteratedDeriv j (fun t => L (a t)) τ = L (iteratedDeriv j a τ) := by
    intro L j hj; induction j with
    | zero => intro τ; simp
    | succ k ih =>
      intro τ; have hkd : Differentiable ℝ (iteratedDeriv k a) := fun t => (ha_cd.differentiable_iteratedDeriv k (by exact_mod_cast (by omega : k < 2))).differentiableAt
      rw [iteratedDeriv_succ, show iteratedDeriv k (fun t => L (a t)) = fun t => L (iteratedDeriv k a t) from funext (ih (by omega)), iteratedDeriv_succ]
      exact (L.hasFDerivAt.comp_hasDerivAt τ (hkd τ).hasDerivAt).deriv
  have ha_re_bd : ∀ j ≤ 2, ∀ τ, |iteratedDeriv j a_re τ| ≤ C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := fun j hj τ => hclm_iter Complex.reCLM hj τ ▸ (Complex.abs_re_le_norm _).trans (ha_bd j hj τ)
  have ha_im_bd : ∀ j ≤ 2, ∀ τ, |iteratedDeriv j a_im τ| ≤ C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := fun j hj τ => hclm_iter Complex.imCLM hj τ ▸ (Complex.abs_im_le_norm _).trans (ha_bd j hj τ)
  have hC_a_nn : 0 ≤ C_a := le_trans (norm_nonneg _) (by simpa using ha_bd 0 (by decide) 0)
  have hint_fn : ∀ (b : ℝ → ℝ), ContDiff ℝ 2 b → (∀ τ, |b τ| ≤ C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2)) →
      Integrable (fun τ : ℝ => (b τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))) := fun b hb_cd hb_bd => by
    refine (integrable_inv_one_add_sq.const_mul (2 * C_a)).mono' ((Complex.continuous_ofReal.comp hb_cd.continuous).mul (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    have hre : (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ))).re = 0 := by rw [show Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)) = (((c * (y * τ + R τ) : ℝ) : ℂ) * Complex.I) by push_cast; ring]; simp
    rw [norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]; have hm_real : (4 : ℝ) ≤ m := by exact_mod_cast hm
    exact (hb_bd τ).trans ((mul_le_mul_of_nonneg_left (inv_one_add_abs_pow_le_inv_sq (by linarith)) hC_a_nn).trans_eq (by ring))
  let I₁ := ∫ τ : ℝ, (a_re τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))
  let I₂ := ∫ τ : ℝ, (a_im τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))
  have h1 : ‖I₁‖ ≤ pf3Const C_a C₂ C₃ y₀ * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) := pf3_kernel_bound hm hc hy₀ (Complex.reCLM.contDiff.comp ha_cd) hR_cd hR1_nn hR2_bd hR3_bd ha_re_bd hy
  have h2 : ‖I₂‖ ≤ pf3Const C_a C₂ C₃ y₀ * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) := pf3_kernel_bound hm hc hy₀ (Complex.imCLM.contDiff.comp ha_cd) hR_cd hR1_nn hR2_bd hR3_bd ha_im_bd hy
  have hsplit : (fun τ : ℝ => a τ * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))) =
      fun τ : ℝ => (a_re τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ))) + Complex.I * ((a_im τ : ℂ) * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (R τ : ℂ)))) :=
    funext fun τ => by rw [← Complex.re_add_im (a τ)]; dsimp [a_re, a_im]; ring
  rw [hsplit, integral_add (hint_fn a_re (Complex.reCLM.contDiff.comp ha_cd) (ha_re_bd 0 (by decide))) ((hint_fn a_im (Complex.imCLM.contDiff.comp ha_cd) (ha_im_bd 0 (by decide))).const_mul Complex.I), integral_const_mul]
  calc ‖I₁ + Complex.I * I₂‖ ≤ ‖I₁‖ + ‖Complex.I * I₂‖ := norm_add_le I₁ (Complex.I * I₂)
    _ = ‖I₁‖ + ‖I₂‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ 2 * pf3Const C_a C₂ C₃ y₀ * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) := by linarith

/-- Concrete imaginary-edge amplitude `a_c(τ)` of `(ceo:O11ae.3)`. -/
noncomputable def mainEdgeAmp (κ : ℝ) (m : ℕ) (c τ : ℝ) : ℂ :=
  (1 - (τ : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c ((τ : ℂ) * Complex.I)) * bsplineImag (ceCs * κ / m) m τ

@[simp] lemma mainEdgeAmp_zero (κ : ℝ) (m : ℕ) (c : ℝ) : mainEdgeAmp κ m c 0 = 1 := by simp [mainEdgeAmp, binetDiff]

theorem mainEdgeAmp_contDiff_and_bound {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 1 ≤ m) :
    (∀ {c : ℝ}, 1 ≤ c → ContDiff ℝ (⊤ : ℕ∞) (mainEdgeAmp κ m c)) ∧
      ∃ C_a > 0, ∀ {c : ℝ}, 1 ≤ c → ∀ j ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv j (mainEdgeAmp κ m c) τ‖ ≤ C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := by
  let β : ℝ := ceCs * κ / m; have hβ : 0 < β := div_pos (mul_pos ceCs_pos hκ) (Nat.cast_pos.mpr (by omega))
  let U : Set ℂ := {ω : ℂ | |ω.im| < 3 / 4}; have hU : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  let r : ℝ := min (1 / 2) (1 / (2 * (β + 1))); have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hball : ∀ τ : ℝ, Metric.closedBall (τ : ℂ) r ⊆ U := fun τ ω hω =>
    ((Complex.abs_im_le_norm _).trans_eq' (by simp) |>.trans (Metric.mem_closedBall.mp hω)).trans_lt (lt_of_le_of_lt (min_le_left _ _) (by norm_num))
  let F : ℝ → ℂ → ℂ := fun c ω => (1 - ω * Complex.I) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (ω * Complex.I)) * bsplineE1 (Complex.I * (β : ℂ) * ω) ^ m
  have hdiff : ∀ {c : ℝ}, 1 ≤ c → DifferentiableOn ℂ (F c) U := fun {c} hc ω hω => by
    change |ω.im| < 3 / 4 at hω
    have h1_re : 0 < (1 - ω * Complex.I).re := by simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one]; linarith [(abs_lt.mp hω).1]
    have h1 := ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul_const Complex.I)).cpow (differentiableAt_const (-(1 / 2 : ℂ))) (Or.inl h1_re)
    have h2_re : 0 < ((c : ℂ) * (1 - ω * Complex.I)).re := by rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; exact mul_pos (by linarith) h1_re
    have h2 := (((binetRem_differentiableOn _ h2_re).differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2_re)).comp ω
      (((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.mul_const Complex.I)).const_mul (c : ℂ))).sub_const (binetRem (c : ℂ)) |>.cexp
    exact ((h1.mul h2).mul (((differentiable_bsplineE1 _).comp ω (differentiableAt_id.const_mul _)).pow m)).differentiableWithinAt
  let B₀ : ℝ := 4 * Real.exp (1 / 4) * (10 / min 1 β) ^ m
  have hsphere : ∀ {c : ℝ}, 1 ≤ c → ∀ (τ : ℝ) (ω : ℂ), ω ∈ Metric.sphere (τ : ℂ) r → ‖F c ω‖ ≤ B₀ * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := fun {c} hc τ ω hω => by
    have hdist : ‖ω - (τ : ℂ)‖ = r := by simpa [Complex.dist_eq] using Metric.mem_sphere.mp hω
    have him12 : |ω.im| ≤ 1 / 2 := (((Complex.abs_im_le_norm _).trans_eq' (by simp)).trans_eq hdist).trans (min_le_left _ _)
    have hnorm1 : ‖(1 - ω * Complex.I) ^ (-(1 / 2 : ℂ))‖ ≤ 4 * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := by
      rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real, show 1 - ω * Complex.I = 1 - Complex.I * ω by ring]
      have h16 : (16 : ℝ)⁻¹ ^ (-(1 / 2 : ℝ)) = 4 := by rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv, show (16 : ℝ) = 4 ^ 2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
      calc ‖1 - Complex.I * ω‖ ^ (-(1 / 2 : ℝ)) ≤ ((1 + |τ|) * 16⁻¹) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by positivity) (by simpa [div_eq_mul_inv] using (norm_one_sub_I_mul_ge (hdist.le.trans (min_le_left _ _))).2) (by norm_num)
        _ = 4 * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := by rw [Real.mul_rpow (by positivity) (by positivity), h16]; ring
    have hnorm2 : ‖Complex.exp (binetDiff c (ω * Complex.I))‖ ≤ Real.exp (1 / 4) := by
      have hre_le : (ω * Complex.I).re ≤ 1 / 2 := by simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub]; linarith [(abs_le.mp him12).1]
      have h12 : 1 / (12 * c) ≤ 1 / 12 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      have hden : 1 / (1 - (ω * Complex.I).re) ≤ 1 / (1 - 1 / 2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 1 - 1 / 2) (by linarith)
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; calc (binetDiff c (ω * Complex.I)).re ≤ ‖binetDiff c (ω * Complex.I)‖ := Complex.re_le_norm _
        _ ≤ (1 / (12 * c)) * (1 / (1 - (ω * Complex.I).re) + 1) := binetDiff_norm_le (by linarith) (by linarith)
        _ ≤ (1 / 12) * (1 / (1 - 1 / 2) + 1) := mul_le_mul h12 (add_le_add hden le_rfl) (add_nonneg (one_div_nonneg.mpr (by linarith)) zero_le_one) (by norm_num)
        _ = 1 / 4 := by norm_num
    have hnorm3 : ‖bsplineE1 (Complex.I * (β : ℂ) * ω) ^ m‖ ≤ (10 / min 1 β) ^ m * (1 + |τ|) ^ (-(m : ℝ)) := by
      have hIb : ‖Complex.I * (β : ℂ)‖ = β := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
      have hvr : ‖Complex.I * (β : ℂ)‖ * r ≤ 1 / 2 := by rw [hIb]; exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hβ.le).trans (by rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]; linarith)
      have hbase := bsplineE1_line_sphere_bound (z₀ := 0) (v := Complex.I * (β : ℂ)) (by simp) (by simp) (by simp [hβ.ne']) le_rfl hvr hdist
      simp only [zero_add, Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_add, abs_of_pos hβ, mul_assoc] at hbase ⊢
      calc ‖bsplineE1 (Complex.I * (↑β * ω)) ^ m‖ = ‖bsplineE1 (Complex.I * (↑β * ω))‖ ^ m := norm_pow _ m
        _ ≤ ((10 / min 1 β) * (1 + |τ|)⁻¹) ^ m := pow_le_pow_left₀ (norm_nonneg _) hbase m
        _ = (10 / min 1 β) ^ m * (1 + |τ|) ^ (-(m : ℝ)) := by rw [mul_pow, inv_pow, ← Real.rpow_natCast (1 + |τ|) m, ← Real.rpow_neg (by positivity)]
    have hexp_add : (1 + |τ|) ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-(m : ℝ)) = (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := by rw [← Real.rpow_add (by positivity)]; ring_nf
    calc ‖F c ω‖ = ‖(1 - ω * Complex.I) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (binetDiff c (ω * Complex.I))‖ * ‖bsplineE1 (Complex.I * (β : ℂ) * ω) ^ m‖ := by simp [F]
      _ ≤ (4 * (1 + |τ|) ^ (-(1 / 2 : ℝ))) * Real.exp (1 / 4) * ((10 / min 1 β) ^ m * (1 + |τ|) ^ (-(m : ℝ))) := by gcongr
      _ = B₀ * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := by rw [← hexp_add]; simp only [B₀]; ring
  have heq : ∀ {c : ℝ}, mainEdgeAmp κ m c = fun τ : ℝ => F c (τ : ℂ) := fun {_} => funext fun τ => by simp [mainEdgeAmp, F, bsplineImag, β, mul_assoc]
  refine ⟨fun {c} hc => by rw [heq]; exact (holomorphic_real_contDiff_and_cauchy hU (hdiff hc) (fun t => by simp [U]) hr hball (hsphere hc)).1,
    2 * B₀ * (max 1 r⁻¹) ^ 2, by positivity, fun {c} hc j hj τ => ?_⟩
  rw [heq]; have hbd := (holomorphic_real_contDiff_and_cauchy hU (hdiff hc) (fun t => by simp [U]) hr hball (hsphere hc)).2 j τ
  have hjf : (j.factorial : ℝ) ≤ 2 := by exact_mod_cast (by interval_cases j <;> decide : j.factorial ≤ 2)
  have hrp : r⁻¹ ^ j ≤ (max 1 r⁻¹) ^ 2 := (pow_le_pow_left₀ (by positivity) (le_max_right _ _) j).trans (pow_le_pow_right₀ (le_max_left _ _) hj)
  calc ‖iteratedDeriv j (fun t : ℝ => F c (t : ℂ)) τ‖ ≤ (j.factorial : ℝ) * (B₀ * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2)) / r ^ j := hbd
    _ = (j.factorial : ℝ) * B₀ * r⁻¹ ^ j * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := by rw [div_eq_mul_inv, inv_pow]; ring
    _ ≤ 2 * B₀ * (max 1 r⁻¹) ^ 2 * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) := by gcongr

/-- Uniform `H²` and `‖R' a_c‖_{L²}` bounds for `mainEdgeAmp` (`(ceo:O11ae.3)`). -/
theorem mainEdgeAmp_H2_and_phase_L2 {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 4 ≤ m) :
    ∃ M > 0, ∀ {c : ℝ}, 1 ≤ c →
      MemLp (mainEdgeAmp κ m c) 2 volume ∧ MemLp (iteratedDeriv 1 (mainEdgeAmp κ m c)) 2 volume ∧ MemLp (iteratedDeriv 2 (mainEdgeAmp κ m c)) 2 volume ∧
      MemLp (fun τ : ℝ => ((iteratedDeriv 1 edgeR τ : ℝ) : ℂ) * mainEdgeAmp κ m c τ) 2 volume ∧
      l2norm (mainEdgeAmp κ m c) ≤ M ∧ l2norm (iteratedDeriv 1 (mainEdgeAmp κ m c)) ≤ M ∧ l2norm (iteratedDeriv 2 (mainEdgeAmp κ m c)) ≤ M ∧
      l2norm (fun τ : ℝ => ((iteratedDeriv 1 edgeR τ : ℝ) : ℂ) * mainEdgeAmp κ m c τ) ≤ M := by
  obtain ⟨hcd, C_a, hC_a, hbd⟩ := mainEdgeAmp_contDiff_and_bound hκ (by omega : 1 ≤ m)
  let M₀ : ℝ := max C_a (Real.pi ^ 2 / 12 * C_a); let M : ℝ := 2 * M₀ * Real.sqrt (∫ τ : ℝ, (1 + τ ^ 2)⁻¹) + 1; have hM₀_nn : 0 ≤ M₀ := le_max_of_le_left hC_a.le
  have memLp_of_decay : ∀ {g : ℝ → ℂ}, Continuous g → (∀ τ : ℝ, ‖g τ‖ ≤ M₀ * (1 + |τ|) ^ (-2 : ℝ)) → MemLp g 2 volume ∧ l2norm g ≤ M := fun {g} hg_c hg_bd => by
    have hpt : ∀ τ : ℝ, ‖g τ‖ ^ 2 ≤ M₀ ^ 2 * (1 + τ ^ 2)⁻¹ := fun τ =>
      calc ‖g τ‖ ^ 2 ≤ (M₀ * (1 + τ ^ 2) ^ (-(1 / 2 : ℝ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ((hg_bd τ).trans (mul_le_mul_of_nonneg_left inv_one_add_abs_sq_le_sqrt_inv hM₀_nn)) 2
        _ = M₀ ^ 2 * (1 + τ ^ 2)⁻¹ := by rw [mul_pow, ← Real.rpow_natCast ((1 + τ ^ 2) ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul (by positivity : 0 ≤ 1 + τ ^ 2), show (-(1 / 2 : ℝ)) * (2 : ℕ) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
    have hsq_int : Integrable (fun τ : ℝ => ‖g τ‖ ^ 2) := (integrable_inv_one_add_sq.const_mul (M₀ ^ 2)).mono' (hg_c.norm.pow 2).aestronglyMeasurable
      (ae_of_all _ fun τ => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt τ)
    refine ⟨(memLp_two_iff_integrable_sq_norm hg_c.aestronglyMeasurable).mpr hsq_int, ?_⟩; unfold l2norm
    have hi : ∫ τ : ℝ, ‖g τ‖ ^ 2 ≤ M₀ ^ 2 * ∫ τ : ℝ, (1 + τ ^ 2)⁻¹ := by rw [← integral_const_mul]; exact integral_mono hsq_int (integrable_inv_one_add_sq.const_mul _) hpt
    calc Real.sqrt (∫ τ : ℝ, ‖g τ‖ ^ 2) ≤ M₀ * Real.sqrt (∫ τ : ℝ, (1 + τ ^ 2)⁻¹) := (Real.sqrt_le_sqrt hi).trans_eq (by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM₀_nn])
      _ ≤ M := by dsimp [M]; linarith [mul_nonneg hM₀_nn (Real.sqrt_nonneg (∫ τ : ℝ, (1 + τ ^ 2)⁻¹))]
  refine ⟨M, by positivity, fun {c} hc => ?_⟩; have hm_real : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hdec : ∀ j ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv j (mainEdgeAmp κ m c) τ‖ ≤ M₀ * (1 + |τ|) ^ (-2 : ℝ) := fun j hj τ =>
    (hbd hc j hj τ).trans (mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by linarith)) (by positivity) hM₀_nn)
  have h0 := memLp_of_decay (hcd hc).continuous (fun τ => iteratedDeriv_zero (f := mainEdgeAmp κ m c) ▸ hdec 0 (by decide) τ)
  have h1 := memLp_of_decay ((hcd hc).continuous_iteratedDeriv 1 (by simp)) (hdec 1 (by decide))
  have h2 := memLp_of_decay ((hcd hc).continuous_iteratedDeriv 2 (by simp)) (hdec 2 (by decide))
  have hph := memLp_of_decay ((Complex.continuous_ofReal.comp (edgeR_contDiff.continuous_iteratedDeriv 1 (by simp))).mul (hcd hc).continuous) fun τ => by
    have hR := edgeR_deriv_bounds τ
    have hrp : (1 + |τ|) ^ 2 * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2) ≤ (1 + |τ|) ^ (-2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]; exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by linarith)
    calc ‖((iteratedDeriv 1 edgeR τ : ℝ) : ℂ) * mainEdgeAmp κ m c τ‖ = |iteratedDeriv 1 edgeR τ| * ‖mainEdgeAmp κ m c τ‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (Real.pi ^ 2 / 12 * (1 + |τ|) ^ 2) * (C_a * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2)) := by gcongr; rw [abs_of_nonneg hR.1]; exact hR.2.1; exact iteratedDeriv_zero (f := mainEdgeAmp κ m c) ▸ hbd hc 0 (by decide) τ
      _ = Real.pi ^ 2 / 12 * C_a * ((1 + |τ|) ^ 2 * (1 + |τ|) ^ (-(m : ℝ) - 1 / 2)) := by ring
      _ ≤ M₀ * (1 + |τ|) ^ (-2 : ℝ) := mul_le_mul (le_max_right _ _) hrp (by positivity) hM₀_nn
  exact ⟨h0.1, h1.1, h2.1, hph.1, h0.2, h1.2, h2.2, hph.2⟩

private lemma eq_zero_ae_of_forall_schwartz_inner_local {u : ℝ → ℂ} (hu : MemLp u 2 volume)
    (h0 : ∀ η : SchwartzMap ℝ ℂ, ∫ x : ℝ, starRingEnd ℂ (η x) * u x = 0) : u =ᵐ[volume] 0 := by
  set U : Lp ℂ 2 volume := hu.toLp u
  have hinner : ∀ η : SchwartzMap ℝ ℂ, ⟪η.toLp 2 volume, U⟫ = 0 := fun η => by
    rw [MeasureTheory.L2.inner_def]; refine (integral_congr_ae ?_).trans (h0 η)
    filter_upwards [η.coeFn_toLp 2 volume, hu.coeFn_toLp] with x hx1 hx2; rw [hx1, hx2, RCLike.inner_apply, starRingEnd_apply]; ring
  have hU0 : U = 0 := inner_self_eq_zero.mp <| congrFun ((SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top).equalizer (continuous_id.inner continuous_const) continuous_const (funext hinner)) U
  exact hu.coeFn_toLp.symm.trans (by rw [show U = hu.toLp u from rfl] at hU0; rw [hU0]; exact Lp.coeFn_zero _ _ _)

/-- Bridge: when `f ∈ L¹(ℝ)` and `WeakDerivL2 f f'`, `fourierPaper f` agrees a.e. with `fourierPaperL2 h`. -/
theorem fourierPaper_L1_le_sqrt_mul_H1 {f f' : ℝ → ℂ} (hf1 : Integrable f) (h : WeakDerivL2 f f') :
    Integrable (fourierPaper f) ∧ ∫ ξ : ℝ, ‖fourierPaper f ξ‖ ≤ 2 * π * Real.sqrt (l2norm f * l2norm f') := by
  set F : Lp ℂ 2 volume := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (h.memLp.toLp f); have hF2 : MemLp (F : ℝ → ℂ) 2 volume := Lp.memLp F
  let w : ℝ → ℝ := fun ξ => (1 + ξ ^ 2)⁻¹; have hw_pos : ∀ ξ : ℝ, 0 < w ξ := fun ξ => by dsimp [w]; positivity
  have hw_le : ∀ ξ : ℝ, w ξ ≤ 1 := fun ξ => inv_le_one_of_one_le₀ (by linarith [sq_nonneg ξ])
  have hinv_tg : (fun ξ : ℝ => (w ξ : ℂ)).HasTemperateGrowth := by
    rw [show (fun ξ : ℝ => (w ξ : ℂ)) = Complex.ofReal ∘ fun ξ : ℝ => (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) from funext fun ξ => by simp [w, Real.rpow_neg_one]]
    exact Complex.hasTemperateGrowth_ofReal.comp (Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1))
  let u : ℝ → ℂ := fun ξ => (w ξ : ℂ) * ((F : ℝ → ℂ) ξ - 𝓕 f ξ)
  have hFour_bdd : Continuous (𝓕 f) ∧ ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ ∫ x : ℝ, ‖f x‖ :=
    ⟨VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf1, fun ξ => VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ ξ⟩
  have hc_inv : Continuous (fun ξ : ℝ => (w ξ : ℂ)) := Complex.continuous_ofReal.comp (((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).add (continuous_id.pow 2)).inv₀ fun ξ => by dsimp; positivity)
  have hu2 : MemLp u 2 volume := by
    have hF_part : MemLp (fun ξ : ℝ => (w ξ : ℂ) * (F : ℝ → ℂ) ξ) 2 volume :=
      (memLp_two_iff_integrable_sq_norm (hc_inv.aestronglyMeasurable.fun_mul hF2.aestronglyMeasurable)).mpr
        ((hF2.integrable_norm_pow two_ne_zero).mono' ((hc_inv.aestronglyMeasurable.fun_mul hF2.aestronglyMeasurable).norm.pow 2) (ae_of_all _ fun ξ => by
          rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw_pos ξ)]
          have hw2 : w ξ ^ 2 ≤ 1 := by have := hw_le ξ; nlinarith [(hw_pos ξ).le]
          nlinarith [sq_nonneg ‖(F : ℝ → ℂ) ξ‖]))
    have hg_part : MemLp (fun ξ : ℝ => (w ξ : ℂ) * 𝓕 f ξ) 2 volume :=
      (memLp_two_iff_integrable_sq_norm (hc_inv.mul hFour_bdd.1).aestronglyMeasurable).mpr
        ((integrable_inv_one_add_sq.const_mul ((∫ x : ℝ, ‖f x‖) ^ 2)).mono' ((hc_inv.mul hFour_bdd.1).norm.pow 2).aestronglyMeasurable (ae_of_all _ fun ξ => by
          dsimp only [Pi.mul_apply]; rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw_pos ξ)]
          have hsq : w ξ ^ 2 ≤ w ξ := by have := hw_le ξ; nlinarith [(hw_pos ξ).le]
          have hfb : ‖𝓕 f ξ‖ ^ 2 ≤ (∫ x : ℝ, ‖f x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hFour_bdd.2 ξ) 2
          calc w ξ ^ 2 * ‖𝓕 f ξ‖ ^ 2 ≤ w ξ * (∫ x : ℝ, ‖f x‖) ^ 2 := by gcongr
            _ = (∫ x : ℝ, ‖f x‖) ^ 2 * w ξ := mul_comm _ _))
    exact (hF_part.sub hg_part).ae_eq (ae_of_all _ fun ξ => by dsimp [u]; ring)
  have h0 : ∀ η : SchwartzMap ℝ ℂ, ∫ ξ : ℝ, starRingEnd ℂ (η ξ) * u ξ = 0 := fun η => by
    set ψ : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun ξ : ℝ => (w ξ : ℂ)) η
    have hψ_val : ∀ ξ : ℝ, ψ ξ = (w ξ : ℂ) * η ξ := fun ξ => by simpa [ψ, smul_eq_mul] using SchwartzMap.smulLeftCLM_apply_apply hinv_tg η ξ
    have hinner1 : ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ = ∫ x : ℝ, starRingEnd ℂ ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) x) * f x := by
      have h1 : ⟪ψ.toLp 2 volume, F⟫ = ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ := by rw [MeasureTheory.L2.inner_def]; exact integral_congr_ae <| (ψ.coeFn_toLp 2 volume).mono fun ξ hξ => by dsimp only; rw [hξ, RCLike.inner_apply]; ring
      have h2 : ⟪ψ.toLp 2 volume, F⟫ = ⟪(𝓕⁻ ψ).toLp 2 volume, h.memLp.toLp f⟫ := by have hstep := MeasureTheory.Lp.inner_fourier_eq (𝓕⁻ (ψ.toLp 2 volume)) (h.memLp.toLp f); rwa [FourierInvPair.fourier_fourierInv_eq _, SchwartzMap.toLp_fourierInv_eq] at hstep
      have h3 : ⟪(𝓕⁻ ψ).toLp 2 volume, h.memLp.toLp f⟫ = ∫ x : ℝ, starRingEnd ℂ ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) x) * f x := by
        rw [MeasureTheory.L2.inner_def]; refine integral_congr_ae ?_; filter_upwards [(𝓕⁻ ψ).coeFn_toLp 2 volume, h.memLp.coeFn_toLp] with x hx1 hx2; rw [hx1, hx2, RCLike.inner_apply]; ring
      rw [← h1, h2, h3]
    have hp : ∀ ξ : ℝ, (ψ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)) ξ = starRingEnd ℂ (ψ ξ) := fun _ => rfl
    have hconj_finv : ∀ x : ℝ, starRingEnd ℂ ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) x) = 𝓕 (⇑(ψ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ))) x := fun x => by
      rw [show (𝓕⁻ ψ : SchwartzMap ℝ ℂ) x = (𝓕⁻ (ψ : ℝ → ℂ)) x from congrFun (SchwartzMap.fourierInv_coe ψ) x, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      dsimp only; rw [smul_eq_mul, smul_eq_mul, hp, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]; congr 2; push_cast; ring
    have hinner2 : ∫ x : ℝ, starRingEnd ℂ ((𝓕⁻ ψ : SchwartzMap ℝ ℂ) x) * f x = ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * 𝓕 f ξ := by
      simp_rw [hconj_finv]
      have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner ((ψ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)).integrable (μ := volume)) hf1
      have hlhs : (innerₗ ℝ).flip = innerₗ ℝ := by ext; simp
      have hflip' : ∫ x : ℝ, 𝓕 (⇑(ψ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ))) x * f x =
          ∫ ξ : ℝ, (ψ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)) ξ * 𝓕 f ξ := by
        simpa only [hlhs, smul_eq_mul, Real.fourier_eq, VectorFourier.fourierIntegral, innerₗ_apply_apply] using hflip
      exact hflip'.trans (integral_congr_ae (ae_of_all _ fun ξ => by dsimp only; rw [hp]))
    have hiF : Integrable (fun ξ : ℝ => starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ) volume := (((ψ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)).memLp 2 volume).integrable_mul hF2).congr (ae_of_all _ fun ξ => by dsimp only [Pi.mul_apply]; rw [hp])
    have hig : Integrable (fun ξ : ℝ => starRingEnd ℂ (ψ ξ) * 𝓕 f ξ) volume := ((ψ.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)).integrable.bdd_mul hFour_bdd.1.aestronglyMeasurable (ae_of_all _ hFour_bdd.2)).congr (ae_of_all _ fun ξ => by dsimp only; rw [hp, mul_comm])
    calc ∫ ξ : ℝ, starRingEnd ℂ (η ξ) * u ξ = ∫ ξ : ℝ, (starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ - starRingEnd ℂ (ψ ξ) * 𝓕 f ξ) := integral_congr_ae (ae_of_all _ fun ξ => by dsimp only; rw [hψ_val, map_mul, Complex.conj_ofReal]; dsimp [u]; ring)
      _ = (∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * (F : ℝ → ℂ) ξ) - ∫ ξ : ℝ, starRingEnd ℂ (ψ ξ) * 𝓕 f ξ := integral_sub hiF hig
      _ = 0 := by rw [hinner1, hinner2, sub_self]
  have hF_ae : (F : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
    filter_upwards [eq_zero_ae_of_forall_schwartz_inner_local hu2 h0] with ξ hξ; exact sub_eq_zero.mp ((mul_eq_zero.mp hξ).resolve_left (Complex.ofReal_ne_zero.mpr (hw_pos ξ).ne'))
  have hcov_ae : fourierPaperL2 h =ᵐ[volume] fourierPaper f := by
    let err : ℝ → ℝ := fun ξ => w ξ * min 1 ‖(F : ℝ → ℂ) ξ - 𝓕 f ξ‖
    have herr_meas : AEStronglyMeasurable err volume := (((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).add (continuous_id.pow 2)).inv₀ fun ξ => by dsimp; positivity).aestronglyMeasurable.mul
      ((continuous_const.min continuous_id).comp_aestronglyMeasurable (hF2.aestronglyMeasurable.sub hFour_bdd.1.aestronglyMeasurable).norm)
    have herr_int : Integrable err := integrable_inv_one_add_sq.mono' herr_meas (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw_pos ξ).le (le_min zero_le_one (norm_nonneg _)))]; exact mul_le_of_le_one_right (hw_pos ξ).le (min_le_left _ _))
    have hcomp_zero : ∫ ξ : ℝ, err ((2 * π)⁻¹ * ξ) = 0 := by have hz : err =ᵐ[volume] (fun _ : ℝ => (0 : ℝ)) := (hF_ae.mono fun ξ hξ => by simp [err, hξ]); rw [Measure.integral_comp_mul_left err (2 * π)⁻¹, integral_congr_ae hz]; simp
    have hcomp_ae := (integral_eq_zero_iff_of_nonneg (fun ξ => mul_nonneg (hw_pos _).le (le_min zero_le_one (norm_nonneg _))) ((integrable_comp_mul_left_iff err (inv_ne_zero (by positivity : 2 * π ≠ 0))).mpr herr_int)).mp hcomp_zero
    filter_upwards [hcomp_ae] with ξ hξ
    have hmin0 : min 1 ‖(F : ℝ → ℂ) ((2 * π)⁻¹ * ξ) - 𝓕 f ((2 * π)⁻¹ * ξ)‖ = 0 := (mul_eq_zero.mp hξ).resolve_left (hw_pos _).ne'
    have hnorm0 : ‖(F : ℝ → ℂ) ((2 * π)⁻¹ * ξ) - 𝓕 f ((2 * π)⁻¹ * ξ)‖ = 0 := by by_contra hne; exact (lt_min one_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne))).ne' hmin0
    have heq : 𝓕 f ((2 * π)⁻¹ * ξ) = fourierPaper f ξ := by rw [Real.fourier_real_eq_integral_exp_smul]; unfold fourierPaper; congr 1; funext x; rw [smul_eq_mul]; congr 2; push_cast; field_simp [Real.pi_ne_zero]
    rw [fourierPaperL2, ← heq]; exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  obtain ⟨hL1, hbd⟩ := fourier_L1_le_sqrt_mul_H1 h
  exact ⟨hL1.congr hcov_ae, (integral_congr_ae (hcov_ae.mono fun ξ hξ => congrArg norm hξ)).symm.trans_le hbd⟩

/-- `(ceo:O11ae.5)`: `L¹` bound `∫ ‖K_c(y)‖ dy ≤ C c^{-1/2}` for `c ≥ 2`, `m ≥ 4`, `κ > 0`. -/
theorem mainEdgeKernel_L1_bound {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 4 ≤ m) :
    ∃ C > 0, ∀ {c : ℝ}, 2 ≤ c → Integrable (mainEdgeKernel (mainEdgeAmp κ m c) c) ∧ ∫ y : ℝ, ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖ ≤ C * c ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨hcd, C_a, hC_a, ha_bd⟩ := mainEdgeAmp_contDiff_and_bound hκ (by omega : 1 ≤ m); obtain ⟨M, hM, hH2⟩ := mainEdgeAmp_H2_and_phase_L2 hκ hm
  refine ⟨2 * π * Real.sqrt (2 * M ^ 2) + 1, by positivity, fun {c} hc => ?_⟩; have hc1 : 1 ≤ c := (by linarith); have hc0 : 0 < c := by linarith
  obtain ⟨hM0, hM1, _, hMph, hN0, hN1, _, hNph⟩ := hH2 hc1
  let a := mainEdgeAmp κ m c; let e : ℝ → ℂ := fun τ => Complex.exp (Complex.I * (c : ℂ) * (edgeR τ : ℂ)); let g : ℝ → ℂ := fun τ => a τ * e τ
  let g' : ℝ → ℂ := fun τ => (iteratedDeriv 1 a τ + Complex.I * (c : ℂ) * ((iteratedDeriv 1 edgeR τ : ℝ) : ℂ) * a τ) * e τ
  have he_norm : ∀ τ, ‖e τ‖ = 1 := fun τ => by dsimp [e]; rw [show Complex.I * (c : ℂ) * (edgeR τ : ℂ) = (((c * edgeR τ : ℝ) : ℂ) * Complex.I) by push_cast; ring]; exact Complex.norm_exp_ofReal_mul_I _
  have hc_e : Continuous e := Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_edgeR))
  have hg_L1 : Integrable g := (integrable_inv_one_add_sq.const_mul (2 * C_a)).mono' ((hcd hc1).continuous.mul hc_e).aestronglyMeasurable (ae_of_all _ fun τ => by
    rw [norm_mul, he_norm, mul_one]; have hm_real : (4 : ℝ) ≤ m := by exact_mod_cast hm
    exact (iteratedDeriv_zero (f := mainEdgeAmp κ m c) ▸ ha_bd hc1 0 (by decide) τ).trans ((mul_le_mul_of_nonneg_left (inv_one_add_abs_pow_le_inv_sq (by linarith)) hC_a.le).trans_eq (by ring)))
  have he_mem_mul : ∀ {u : ℝ → ℂ}, MemLp u 2 volume → MemLp (fun τ => u τ * e τ) 2 volume ∧ l2norm (fun τ => u τ * e τ) = l2norm u := fun {u} hu =>
    ⟨(memLp_two_iff_integrable_sq_norm (hu.aestronglyMeasurable.mul hc_e.aestronglyMeasurable)).mpr ((hu.integrable_norm_pow two_ne_zero).congr (ae_of_all _ fun x => by dsimp only; rw [Pi.mul_apply, norm_mul, he_norm x, mul_one])), by simp [l2norm, he_norm]⟩
  have hg_L2 := he_mem_mul hM0; have h1_L2 := he_mem_mul hM1; have hph_L2 := he_mem_mul hMph
  have hg'_L2 : MemLp g' 2 volume := by
    rw [show g' = fun τ => iteratedDeriv 1 a τ * e τ + (Complex.I * (c : ℂ)) • (((iteratedDeriv 1 edgeR τ : ℝ) : ℂ) * a τ * e τ) from funext fun τ => by dsimp [g']; ring]
    exact h1_L2.1.add (hph_L2.1.const_smul (Complex.I * (c : ℂ)))
  have hweak : WeakDerivL2 g g' := by
    refine ⟨hg_L2.1, hg'_L2, fun φ => ?_⟩
    have hd : ∀ x : ℝ, HasDerivAt g (g' x) x := fun x => by
      have ha_d : HasDerivAt a (iteratedDeriv 1 a x) x := by rw [iteratedDeriv_one]; exact (((hcd hc1).differentiable (by simp)).differentiableAt).hasDerivAt
      have he_d : HasDerivAt e (Complex.I * (c : ℂ) * ((iteratedDeriv 1 edgeR x : ℝ) : ℂ) * e x) x := by
        have hre_d : HasDerivAt edgeR (iteratedDeriv 1 edgeR x) x := by rw [iteratedDeriv_one, (hasDerivAt_edgeR x).deriv]; exact hasDerivAt_edgeR x
        exact ((hre_d.ofReal_comp.const_mul (Complex.I * (c : ℂ))).cexp).congr_deriv (by dsimp [e]; ring)
      convert ha_d.mul he_d using 1; simp only [g']; ring
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => (by rw [SchwartzMap.derivCLM_apply]; exact φ.differentiable.differentiableAt.hasDerivAt : HasDerivAt (⇑φ) ((SchwartzMap.derivCLM ℂ ℂ φ) x) x))
      (fun x _ => hd x) ((φ.memLp 2 volume).integrable_mul hg'_L2) (((SchwartzMap.derivCLM ℂ ℂ φ).memLp 2 volume).integrable_mul hg_L2.1) ((φ.memLp 2 volume).integrable_mul hg_L2.1)
    rw [show (fun x => deriv (⇑φ) x * g x) = fun x => (SchwartzMap.derivCLM ℂ ℂ φ) x * g x from funext fun x => by rw [SchwartzMap.derivCLM_apply], hibp, neg_neg]
  obtain ⟨hFL1, hFbd⟩ := fourierPaper_L1_le_sqrt_mul_H1 hg_L1 hweak
  have hK_eq : mainEdgeKernel a c = fun y : ℝ => fourierPaper g (-c * y) := funext fun y => by
    unfold mainEdgeKernel fourierPaper; dsimp only [g, e]; congr 1; funext τ; rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring
  have hl2g' : l2norm g' ≤ 2 * c * M := by
    rw [l2norm_eq_norm_toLp hg'_L2]; let U1 := h1_L2.1.toLp _; let U2 := hph_L2.1.toLp _
    have htoLp : hg'_L2.toLp g' = U1 + (Complex.I * (c : ℂ)) • U2 := by
      apply Lp.ext; filter_upwards [hg'_L2.coeFn_toLp, Lp.coeFn_add U1 ((Complex.I * (c : ℂ)) • U2), Lp.coeFn_smul (Complex.I * (c : ℂ)) U2, h1_L2.1.coeFn_toLp, hph_L2.1.coeFn_toLp] with τ h0 ha hs h1 h2
      rw [h0, ha, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul, h1, h2]; dsimp [g']; ring
    rw [htoLp]; calc ‖U1 + (Complex.I * (c : ℂ)) • U2‖ ≤ ‖U1‖ + ‖(Complex.I * (c : ℂ)) • U2‖ := norm_add_le _ _
      _ = l2norm (fun τ => iteratedDeriv 1 a τ * e τ) + c * l2norm (fun τ => ((iteratedDeriv 1 edgeR τ : ℝ) : ℂ) * a τ * e τ) := by
          rw [norm_smul, Complex.norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, ← l2norm_eq_norm_toLp h1_L2.1, ← l2norm_eq_norm_toLp hph_L2.1]
      _ ≤ M + c * M := by rw [h1_L2.2, hph_L2.2]; exact add_le_add hN1 (mul_le_mul_of_nonneg_left hNph hc0.le)
      _ ≤ 2 * c * M := by linarith [le_mul_of_one_le_left hM.le hc1]
  refine ⟨by rw [hK_eq]; exact (integrable_comp_mul_left_iff (fourierPaper g) (neg_ne_zero.mpr hc0.ne')).mpr hFL1, ?_⟩
  rw [hK_eq, Measure.integral_comp_mul_left (fun ξ => ‖fourierPaper g ξ‖) (-c), abs_inv, abs_neg, abs_of_pos hc0, smul_eq_mul]
  have hsqrt : Real.sqrt (l2norm g * l2norm g') ≤ Real.sqrt (2 * M ^ 2) * Real.sqrt c :=
    (Real.sqrt_le_sqrt (mul_le_mul (hg_L2.2 ▸ hN0) hl2g' (Real.sqrt_nonneg _) hM.le)).trans_eq (by rw [show M * (2 * c * M) = 2 * M ^ 2 * c by ring, Real.sqrt_mul (by positivity)])
  calc c⁻¹ * ∫ ξ : ℝ, ‖fourierPaper g ξ‖ ≤ c⁻¹ * (2 * π * (Real.sqrt (2 * M ^ 2) * Real.sqrt c)) := by gcongr; exact hFbd.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))
    _ = 2 * π * Real.sqrt (2 * M ^ 2) * c ^ (-(1 / 2 : ℝ)) := by rw [show c⁻¹ * (2 * π * (Real.sqrt (2 * M ^ 2) * Real.sqrt c)) = 2 * π * Real.sqrt (2 * M ^ 2) * (c⁻¹ * Real.sqrt c) by ring, ← Real.rpow_neg_one c, Real.sqrt_eq_rpow c, ← Real.rpow_add hc0]; norm_num
    _ ≤ (2 * π * Real.sqrt (2 * M ^ 2) + 1) * c ^ (-(1 / 2 : ℝ)) := by gcongr; linarith

/-- `(ceo:O11ae.6)`: rapid decay `‖K_c(y)‖ ≤ C c^{-2} y^{-2}` (and `≤ C_d c^{-2}`) on `y ≥ d > 0`. -/
theorem mainEdgeKernel_right_decay {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 4 ≤ m) {d : ℝ} (hd : 0 < d) :
    ∃ C > 0, ∀ {c y : ℝ}, 2 ≤ c → d ≤ y →
      ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖ ≤ C * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) ∧ ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖ ≤ (C * d ^ (-2 : ℝ)) * c ^ (-2 : ℝ) := by
  obtain ⟨hcd, C_a, _, ha_bd⟩ := mainEdgeAmp_contDiff_and_bound hκ (by omega : 1 ≤ m)
  let C : ℝ := max (2 * pf3Const C_a (Real.pi ^ 2 / 3) (Real.pi ^ 2 / 2) d) 0 + 1; refine ⟨C, by positivity, fun {c y} hc hy => ?_⟩
  have hc1 : 1 ≤ c := (by linarith); have hy0 : 0 < y := hd.trans_le hy
  have hpf := pf3_kernel_bound_complex hm hc hd ((hcd hc1).of_le (by simp)) edgeR_contDiff (fun τ => (edgeR_deriv_bounds τ).1) (fun τ => (edgeR_deriv_bounds τ).2.2.1) (fun τ => (edgeR_deriv_bounds τ).2.2.2) (ha_bd hc1) hy
  have h1 : ‖mainEdgeKernel (mainEdgeAmp κ m c) c y‖ ≤ C * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) := by
    rw [show mainEdgeKernel (mainEdgeAmp κ m c) c y = ∫ τ : ℝ, mainEdgeAmp κ m c τ * Complex.exp (Complex.I * (c : ℂ) * ((y : ℂ) * (τ : ℂ) + (edgeR τ : ℂ))) from by unfold mainEdgeKernel; congr 1; funext τ; push_cast; ring]
    exact hpf.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [le_max_left (2 * pf3Const C_a (Real.pi ^ 2 / 3) (Real.pi ^ 2 / 2) d) 0]) (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg hy0.le _))
  exact ⟨h1, h1.trans (calc C * c ^ (-2 : ℝ) * y ^ (-2 : ℝ) ≤ C * c ^ (-2 : ℝ) * d ^ (-2 : ℝ) := by have := Real.rpow_le_rpow_of_nonpos hd hy (by norm_num : (-2 : ℝ) ≤ 0); gcongr
    _ = (C * d ^ (-2 : ℝ)) * c ^ (-2 : ℝ) := by ring)⟩

/-- Rescaled tail `F_ε(X) = ε^{-3} F(-X / ε^2)` of `(ceo:O11ae.7)`. -/
noncomputable def rescaledTail (F : ℝ → ℝ) (ε X : ℝ) : ℝ := ε ^ (-3 : ℝ) * F (-X / ε ^ 2)

/-- `(ceo:O11ae.7)`: exact Fubini kernel identity pairing `a(τ)` with `T̃ F(c_s τ / ε)`. -/
theorem mainEdge_fubini_kernel {F : ℝ → ℝ} (hF : Integrable F) {a : ℝ → ℂ} (ha : Integrable a) {c : ℝ} (hc : 0 < c) (L : ℝ) (k : ℂ) :
    let ε : ℝ := c ^ (-(1 / 3 : ℝ))
    (2 * (π : ℂ))⁻¹ * (ε⁻¹ : ℂ) * ∫ τ : ℝ, a τ * Complex.exp (Complex.I * (c : ℂ) * ((L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ)) *
        (k * Complex.exp (Complex.I * (((ceCs * τ / ε : ℝ) ^ 3 / 12 : ℝ) : ℂ)) * ∫ u : ℝ, (F u : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / ε) * u : ℝ) : ℂ)))
    = k * (2 * (π : ℂ))⁻¹ * ∫ X : ℝ, (rescaledTail F ε X : ℂ) * mainEdgeKernel a c (L - ceCs * X) := by
  dsimp only; set ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε : 0 < ε := Real.rpow_pos_of_pos hc _
  have hε3 : ε ^ (-3 : ℝ) = c := by dsimp [ε]; rw [← Real.rpow_mul hc.le]; norm_num
  have hε_cube : ε ^ 3 = c⁻¹ := by dsimp [ε]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num; rw [Real.rpow_neg_one]
  have hcs3 : ceCs ^ 3 = Real.pi ^ 2 / 3 := by dsimp [ceCs]; rw [← Real.rpow_natCast ((Real.pi ^ 2 / 3) ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul (by positivity)]; norm_num
  have hF_rescaled_int : Integrable (fun X : ℝ => (rescaledTail F ε X : ℂ)) :=
    Complex.ofRealCLM.integrable_comp <| (((integrable_comp_mul_left_iff F (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hε.ne')))).mpr hF).const_mul (ε ^ (-3 : ℝ))).congr
      (ae_of_all _ fun X => by show ε ^ (-3 : ℝ) * F (-(ε ^ 2)⁻¹ * X) = rescaledTail F ε X; unfold rescaledTail; ring_nf)
  have hinner_cov : ∀ τ : ℝ, ((ε⁻¹ : ℝ) : ℂ) * ∫ u : ℝ, (F u : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / ε) * u : ℝ) : ℂ)) =
      ∫ X : ℝ, (rescaledTail F ε X : ℂ) * Complex.exp (-Complex.I * ((c * ceCs * X * τ : ℝ) : ℂ)) := fun τ => by
    have hcov := Measure.integral_comp_mul_left (fun u : ℝ => (F u : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / ε) * u : ℝ) : ℂ))) (-(ε ^ 2)⁻¹)
    simp only [abs_inv, abs_neg, abs_of_pos (pow_pos hε 2), inv_inv] at hcov
    have hu_eq : ∫ u : ℝ, (F u : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / ε) * u : ℝ) : ℂ)) =
        (((ε ^ 2)⁻¹ : ℝ) : ℂ) * ∫ X : ℝ, (F (-(ε ^ 2)⁻¹ * X) : ℂ) * Complex.exp (Complex.I * (((ceCs * τ / ε) * (-(ε ^ 2)⁻¹ * X) : ℝ) : ℂ)) := by
      have hne : (ε ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hε.ne'
      calc ∫ u : ℝ, _ = (((ε ^ 2)⁻¹ : ℝ) : ℂ) * ((ε ^ 2 : ℝ) : ℂ) * _ := by rw [← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one, one_mul]
        _ = (((ε ^ 2)⁻¹ : ℝ) : ℂ) * ((ε ^ 2 : ℝ) • _) := by rw [mul_assoc, Complex.real_smul]
        _ = _ := by rw [← hcov]
    have hpow : ((ε⁻¹ : ℝ) : ℂ) * (((ε ^ 2)⁻¹ : ℝ) : ℂ) = ((ε ^ (-3 : ℝ) : ℝ) : ℂ) := by norm_cast; rw [← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_neg hε.le, ← Real.rpow_add hε]; norm_num
    rw [hu_eq, ← mul_assoc, hpow, ← integral_const_mul]; congr 1; funext X
    have hid : (ceCs * τ / ε) * (-(ε ^ 2)⁻¹ * X) = -(c * ceCs * X * τ) := by
      have hε3' : ε ^ (-3 : ℝ) = (ε ^ 3)⁻¹ := (Real.rpow_neg hε.le 3).trans (congrArg Inv.inv (Real.rpow_natCast ε 3)); rw [← hε3, hε3']; field_simp [hε.ne']
    have harg : -(ε ^ 2)⁻¹ * X = -X / ε ^ 2 := by ring
    rw [hid, harg]; simp only [rescaledTail]; push_cast; ring_nf
  have hcubic : ∀ τ : ℝ, (c : ℂ) * ((L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ) + (((ceCs * τ / ε : ℝ) ^ 3 / 12 : ℝ) : ℂ) = ((c * (L * τ + edgeR τ) : ℝ) : ℂ) := fun τ => by
    have hval : (ceCs * τ / ε) ^ 3 / 12 = c * (Real.pi ^ 2 / 36 * τ ^ 3) := by rw [div_pow, mul_pow, hcs3, hε_cube]; field_simp; ring
    exact_mod_cast (show c * (L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ) + (ceCs * τ / ε) ^ 3 / 12 = c * (L * τ + edgeR τ) by rw [hval]; ring)
  have hF_prod : Integrable (fun p : ℝ × ℝ => a p.1 * (rescaledTail F ε p.2 : ℂ) * Complex.exp (Complex.I * ((c * ((L - ceCs * p.2) * p.1 + edgeR p.1) : ℝ) : ℂ))) := by
    refine (ha.norm.mul_prod hF_rescaled_int.norm).mono' ((ha.aestronglyMeasurable.comp_fst.mul hF_rescaled_int.aestronglyMeasurable.comp_snd).mul
      ((Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_const.mul ((continuous_const.sub (continuous_const.mul continuous_snd)).mul continuous_fst |>.add (continuous_edgeR.comp continuous_fst))))))).aestronglyMeasurable))
      (ae_of_all _ fun p => by rw [norm_mul, norm_mul, show Complex.I * ((c * ((L - ceCs * p.2) * p.1 + edgeR p.1) : ℝ) : ℂ) = (((c * ((L - ceCs * p.2) * p.1 + edgeR p.1) : ℝ) : ℂ) * Complex.I) by ring, Complex.norm_exp_ofReal_mul_I, mul_one])
  calc (2 * (π : ℂ))⁻¹ * (ε⁻¹ : ℂ) * _ = k * (2 * (π : ℂ))⁻¹ * ∫ τ : ℝ, a τ * Complex.exp (Complex.I * ((c * (L * τ + edgeR τ) : ℝ) : ℂ)) *
          ∫ X : ℝ, (rescaledTail F ε X : ℂ) * Complex.exp (-Complex.I * ((c * ceCs * X * τ : ℝ) : ℂ)) := by
          rw [← integral_const_mul, ← integral_const_mul]; congr 1; funext τ
          have he₁ : Complex.exp (Complex.I * (c : ℂ) * ((L * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ)) * Complex.exp (Complex.I * (((ceCs * τ / ε : ℝ) ^ 3 / 12 : ℝ) : ℂ)) = Complex.exp (Complex.I * ((c * (L * τ + edgeR τ) : ℝ) : ℂ)) := by rw [← Complex.exp_add, mul_assoc Complex.I (c : ℂ), ← mul_add, hcubic τ]
          have hswap : ∀ x y z : ℂ, (2 * (π : ℂ))⁻¹ * (ε⁻¹ : ℂ) * (a τ * x * (k * y * z)) = k * (2 * (π : ℂ))⁻¹ * (a τ * (x * y) * (((ε⁻¹ : ℝ) : ℂ) * z)) := fun x y z => by simp only [Complex.ofReal_inv]; ring
          rw [hswap _ _ _, he₁, hinner_cov τ]
    _ = k * (2 * (π : ℂ))⁻¹ * ∫ τ : ℝ, ∫ X : ℝ, a τ * (rescaledTail F ε X : ℂ) * Complex.exp (Complex.I * ((c * ((L - ceCs * X) * τ + edgeR τ) : ℝ) : ℂ)) := by
          congr 2; funext τ; rw [← integral_const_mul]; congr 1; funext X; rw [mul_mul_mul_comm, ← Complex.exp_add]; congr 2; push_cast; ring_nf
    _ = k * (2 * (π : ℂ))⁻¹ * ∫ X : ℝ, (rescaledTail F ε X : ℂ) * mainEdgeKernel a c (L - ceCs * X) := by
          rw [integral_integral_swap hF_prod]; congr 2; funext X; rw [mainEdgeKernel, ← integral_const_mul]; congr 1; funext τ; push_cast; ring_nf

/-- Bridge identifying `(mellinK0 * bsplineImag, airyFtilde)` with `mainEdge_fubini_kernel`. -/
theorem mainEdge_mellinK0_airyFtilde_bridge {κ c ξ : ℝ} {m : ℕ} (hξ : 0 < ξ) (F : ℝ → ℝ) (τ : ℝ) :
    let ε : ℝ := c ^ (-(1 / 3 : ℝ)); let ξL : ℝ := ceCs * τ / ε
    mellinK0 c ((τ : ℂ) * Complex.I) ξ * bsplineImag (ceCs * κ / m) m τ =
      mainEdgeAmp κ m c τ * Complex.exp (Complex.I * (c : ℂ) * ((Real.log (Real.pi ^ 2 * ξ) * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ)) ∧
    airyFtilde (fun z : ℂ => (F z.re : ℂ)) (-(ξL : ℂ)) = (ceK : ℂ) * Complex.exp (Complex.I * ((ξL ^ 3 / 12 : ℝ) : ℂ)) * ∫ u : ℝ, (F u : ℂ) * Complex.exp (Complex.I * ((ξL * u : ℝ) : ℂ)) := by
  dsimp only; constructor
  · unfold mellinK0 mainEdgeAmp mellinPhi
    have hlog : Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) = (Real.log (Real.pi ^ 2 * ξ) : ℂ) := by
      rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring]; exact (Complex.ofReal_log (by positivity)).symm
    have hs : stripS0Tilde ((τ : ℂ) * Complex.I) = Complex.I * ((edgeR τ - Real.pi ^ 2 / 36 * τ ^ 3 : ℝ) : ℂ) := by
      have hed : edgeR5 τ = stripS0Tilde ((τ : ℂ) * Complex.I) - (Real.pi ^ 2 / 36 : ℂ) * ((τ : ℂ) * Complex.I) ^ 3 := rfl
      have hi3 : ((τ : ℂ) * Complex.I) ^ 3 = -(((τ ^ 3 : ℝ) : ℂ) * Complex.I) := by calc ((τ : ℂ) * Complex.I) ^ 3 = (τ : ℂ) ^ 3 * (Complex.I ^ 2 * Complex.I) := by ring
        _ = -(((τ ^ 3 : ℝ) : ℂ) * Complex.I) := by rw [Complex.I_sq]; push_cast; ring
      rw [hi3] at hed
      have hsub : stripS0Tilde ((τ : ℂ) * Complex.I) = Complex.I * (edgeR τ : ℂ) - Complex.I * ((Real.pi ^ 2 / 36 * τ ^ 3 : ℝ) : ℂ) := by
        have h' : Complex.I * (edgeR τ : ℂ) = stripS0Tilde ((τ : ℂ) * Complex.I) + Complex.I * ((Real.pi ^ 2 / 36 * τ ^ 3 : ℝ) : ℂ) := by rw [← edgeR5_eq_I_mul_edgeR, hed]; push_cast; ring
        linear_combination -h'
      rw [hsub]; push_cast; ring
    rw [hlog, hs]
    have hexp : (c : ℂ) * (Complex.I * ((edgeR τ - Real.pi ^ 2 / 36 * τ ^ 3 : ℝ) : ℂ) + (τ : ℂ) * Complex.I * (Real.log (Real.pi ^ 2 * ξ) : ℂ)) =
        Complex.I * (c : ℂ) * ((Real.log (Real.pi ^ 2 * ξ) * τ - Real.pi ^ 2 / 36 * τ ^ 3 + edgeR τ : ℝ) : ℂ) := by push_cast; ring
    rw [hexp]; ring
  · unfold airyFtilde airyFhat airyPhiK ceK; congr 1; · congr 2; push_cast; ring_nf
    · congr 1; funext u; simp only [Complex.ofReal_re]; congr 2; push_cast; ring_nf

/-! ## Section 3: Vector Gaussian transform and Lemma `GT.2b(1)–(2)` -/

/-- Diagonal Airy cardinal mixture `diagAirySource w u = ∑' n, w n * cohnL n u ^ 2`. -/
noncomputable def diagAirySource (w : ℕ → ℝ) (u : ℝ) : ℝ := ∑' n : ℕ, w n * cohnL n u ^ 2

lemma cohnL_sq_le (n : ℕ) (u : ℝ) : cohnL n u ^ 2 ≤ 23 * (1 + |u|) * airyEnv (u : ℂ) := by
  have h1 := norm_airyPWFun_sq_le (cohnLL2 n) (u : ℂ)
  rwa [airyPWFun_cohnLL2, cohnLC_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs, cohnLL2_orthonormal.norm_eq_one n, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs] at h1

lemma diagAirySource_summable {w : ℕ → ℝ} (hw_nn : ∀ n, 0 ≤ w n) (hw_sum : Summable w) (u : ℝ) : Summable (fun n : ℕ => w n * cohnL n u ^ 2) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (hw_nn n) (sq_nonneg _)) (fun n => mul_le_mul_of_nonneg_left (cohnL_sq_le n u) (hw_nn n)) (hw_sum.mul_right _)

lemma diagAirySource_le {w : ℕ → ℝ} (hw_nn : ∀ n, 0 ≤ w n) (hw_sum : Summable w) (u : ℝ) :
    0 ≤ diagAirySource w u ∧ diagAirySource w u ≤ (∑' n : ℕ, w n) * 23 * (1 + |u|) * airyEnv (u : ℂ) :=
  ⟨tsum_nonneg fun n => mul_nonneg (hw_nn n) (sq_nonneg _),
    ((diagAirySource_summable hw_nn hw_sum u).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (cohnL_sq_le n u) (hw_nn n)) (hw_sum.mul_right _)).trans_eq (by rw [tsum_mul_right]; ring)⟩

private lemma airyEnv_ofReal_nonneg' {u : ℝ} (hu : 0 ≤ u) : 0 ≤ airyEnv (u : ℂ) := by rw [airyEnv_ofReal_nonneg hu]; positivity

private lemma integrable_pow_mul_airyEnv_mul_exp {k : ℕ} {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) :
    Integrable (fun u : ℝ => (1 + |u|) ^ k * airyEnv (u : ℂ) * (if u < 0 then Real.exp (c * u) else Real.exp (R * u))) := by
  have hcomp : IntegrableOn (fun x : ℝ => (1 + -x) ^ k * Real.exp (-(c * -x))) (Iio 0) volume := by
    simpa [Set.neg_Ioi] using (airyPws_integrableOn_pow_mul_exp k hc).comp_neg
  have h_neg : IntegrableOn (fun u : ℝ => (1 + |u|) ^ k * airyEnv (u : ℂ) * Real.exp (c * u)) (Iio 0) :=
    hcomp.congr_fun (fun u hu => by have hu0 : u < 0 := mem_Iio.mp hu; rw [abs_of_neg hu0, airyEnv_ofReal_neg hu0, mul_one]; ring_nf) measurableSet_Iio
  have h_pos : IntegrableOn (fun u : ℝ => (1 + |u|) ^ k * airyEnv (u : ℂ) * Real.exp (R * u)) (Ici 0) := by
    have hi := (integrableOn_Ici_iff_integrableOn_Ioi).mpr ((airyPws_integrableOn_pow_mul_exp k (by norm_num : (0 : ℝ) < 2 / 3)).const_mul (Real.exp (R ^ 3 / 3 + 2 / 3)))
    have hcont : ContinuousOn (fun u : ℝ => (1 + u) ^ k * Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) * Real.exp (R * u)) (Ici 0) :=
      (((continuous_const.add continuous_id).pow k).continuousOn.mul (ContinuousOn.rexp (continuousOn_const.mul (continuousOn_id.rpow_const fun _ _ => Or.inr (by norm_num))))).mul (by fun_prop)
    have hmeas : AEStronglyMeasurable (fun u : ℝ => (1 + |u|) ^ k * airyEnv (u : ℂ) * Real.exp (R * u)) (volume.restrict (Ici 0)) :=
      (hcont.aestronglyMeasurable measurableSet_Ici).congr (by filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu; rw [abs_of_nonneg (mem_Ici.mp hu), airyEnv_ofReal_nonneg (mem_Ici.mp hu)])
    refine hi.mono' hmeas ((ae_restrict_mem measurableSet_Ici).mono fun u hu => ?_); have hu0 : 0 ≤ u := mem_Ici.mp hu
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by positivity) (airyEnv_ofReal_nonneg' hu0)) (Real.exp_pos _).le), abs_of_nonneg hu0, mul_assoc, mul_comm (airyEnv (u : ℂ))]
    calc (1 + u) ^ k * (Real.exp (R * u) * airyEnv (u : ℂ)) ≤ (1 + u) ^ k * (Real.exp (R ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u)) := mul_le_mul_of_nonneg_left (exp_mul_airyEnv_le hR hu0) (by positivity)
      _ = Real.exp (R ^ 3 / 3 + 2 / 3) * ((1 + u) ^ k * Real.exp (-(2 / 3) * u)) := by ring
  exact ((integrable_indicator_iff measurableSet_Iio).mpr h_neg |>.add ((integrable_indicator_iff measurableSet_Ici).mpr h_pos)).congr (ae_of_all _ fun u => by by_cases hu : u < 0 <;> simp [hu, mem_Iio, mem_Ici, not_le])

private lemma differentiableOn_airyTwistedLaplaceC_of_le {X : ℝ → ℝ} (hXm : AEStronglyMeasurable (fun u : ℝ => (X u : ℂ)) volume)
    {C_X : ℝ} (hX_bd : ∀ u : ℝ, |X u| ≤ C_X * (1 + |u|) * airyEnv (u : ℂ)) : DifferentiableOn ℂ (airyTwistedLaplaceC X) {y : ℂ | 0 < y.re} := by
  intro y₀ hy₀; have hy₀_pos : 0 < y₀.re := hy₀
  have hCX : 0 ≤ C_X := by have h0 := hX_bd 0; rw [abs_zero, add_zero, mul_one, airyEnv_ofReal_nonneg le_rfl, show -(4 / 3 : ℝ) * (0 : ℝ) ^ (3 / 2 : ℝ) = 0 by norm_num, Real.exp_zero, mul_one] at h0; exact (abs_nonneg _).trans h0
  let c : ℝ := y₀.re / 2; let R : ℝ := ‖y₀‖ + c
  have hdom : Integrable (fun u : ℝ => C_X * ((1 + |u|) ^ 2 * airyEnv (u : ℂ) * (if u < 0 then Real.exp (c * u) else Real.exp (R * u)))) :=
    (integrable_pow_mul_airyEnv_mul_exp (k := 2) (half_pos hy₀_pos) (by positivity)).const_mul C_X
  have hball_re : ∀ {y : ℂ}, y ∈ Metric.ball y₀ c → c ≤ y.re ∧ y.re ≤ R := fun {y} hy => by
    have hny : ‖y - y₀‖ ≤ c := by simpa [Complex.dist_eq] using (Metric.mem_ball.mp hy).le
    have hd : |y.re - y₀.re| ≤ c := by rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans hny
    exact ⟨by dsimp [c] at hd ⊢; linarith [(abs_le.mp hd).1], (Complex.re_le_norm y).trans ((norm_le_insert' y y₀).trans (by linarith))⟩
  have hexp_if : ∀ {y : ℂ}, c ≤ y.re → y.re ≤ R → ∀ u : ℝ, Real.exp (y.re * u) ≤ if u < 0 then Real.exp (c * u) else Real.exp (R * u) :=
    fun hc_le hR_le u => by split_ifs with hu <;> [exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hc_le hu.le); exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hR_le (not_lt.mp hu))]
  have hnn_env : ∀ u : ℝ, 0 ≤ airyEnv (u : ℂ) := fun u => by by_cases hu : u < 0; rw [airyEnv_ofReal_neg hu]; norm_num; exact airyEnv_ofReal_nonneg' (not_lt.mp hu)
  have hint_ball : ∀ y ∈ Metric.ball y₀ c, Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ))) := fun y hy => by
    obtain ⟨hc_le, hR_le⟩ := hball_re hy
    refine hdom.mono' (hXm.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun u => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hnn_if : 0 ≤ if u < 0 then Real.exp (c * u) else Real.exp (R * u) := by split_ifs <;> positivity
    have h1u : 1 + |u| ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
    calc |X u| * Real.exp (y.re * u) ≤ C_X * (1 + |u|) * airyEnv (u : ℂ) * (if u < 0 then Real.exp (c * u) else Real.exp (R * u)) :=
          mul_le_mul (hX_bd u) (hexp_if hc_le hR_le u) (Real.exp_pos _).le (mul_nonneg (mul_nonneg hCX (by linarith [abs_nonneg u])) (hnn_env u))
      _ = C_X * ((1 + |u|) * (airyEnv (u : ℂ) * (if u < 0 then Real.exp (c * u) else Real.exp (R * u)))) := by ring
      _ ≤ C_X * ((1 + |u|) ^ 2 * (airyEnv (u : ℂ) * (if u < 0 then Real.exp (c * u) else Real.exp (R * u)))) := by gcongr; exact mul_nonneg (hnn_env u) hnn_if
      _ = _ := by ring
  let F : ℂ → ℝ → ℂ := fun y u => (X u : ℂ) * Complex.exp (y * (u : ℂ)); let F' : ℂ → ℝ → ℂ := fun y u => (u : ℂ) * (X u : ℂ) * Complex.exp (y * (u : ℂ))
  have hF'_meas : AEStronglyMeasurable (F' y₀) volume := ((Complex.continuous_ofReal.aestronglyMeasurable.mul (hXm.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)).congr (ae_of_all _ fun u => by dsimp [F']; ring))
  have hd_int := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (Metric.ball_mem_nhds y₀ (half_pos hy₀_pos))
    (Eventually.of_forall fun y => hXm.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable) (hint_ball y₀ (Metric.mem_ball_self (half_pos hy₀_pos))) hF'_meas
    (ae_of_all _ fun u y hy => by
      obtain ⟨hc_le, hR_le⟩ := hball_re hy; dsimp [F']; rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; have hne := hnn_env u
      calc |u| * |X u| * Real.exp (y.re * u) ≤ (1 + |u|) * (C_X * (1 + |u|) * airyEnv (u : ℂ)) * (if u < 0 then Real.exp (c * u) else Real.exp (R * u)) :=
            mul_le_mul (mul_le_mul (by linarith [abs_nonneg u]) (hX_bd u) (abs_nonneg _) (by positivity)) (hexp_if hc_le hR_le u) (Real.exp_pos _).le (by positivity)
        _ = C_X * ((1 + |u|) ^ 2 * airyEnv (u : ℂ) * (if u < 0 then Real.exp (c * u) else Real.exp (R * u))) := by ring)
    hdom (ae_of_all _ fun u y _ => (((hasDerivAt_id y).mul_const (u : ℂ)).cexp.const_mul (X u : ℂ)).congr_deriv (by dsimp [F']; ring))
  exact ((((differentiableAt_id.pow 3).neg.div_const 12).cexp.const_mul (ceK : ℂ)).mul hd_int.2.differentiableAt).differentiableWithinAt

lemma dirichletPhi_abs_le (n : ℕ) (t : ℝ) : |dirichletPhi n t| ≤ 18 * π := by
  unfold dirichletPhi; have hderiv := airyZero_inv_deriv_sq_le (n + 1); have hneg : airyZero (n + 1) < 0 := airyZero_neg (n + 1)
  have hrp : (1 + (-airyZero (n + 1))) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hsq : (airyAi' (airyZero (n + 1)) ^ 2)⁻¹ ≤ (6 * π) ^ 2 := by
    have hD : ‖((deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)⁻¹‖ = (airyAi' (airyZero (n + 1)) ^ 2)⁻¹ := by rw [deriv_airyAiC_ofReal, ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    calc (airyAi' (airyZero (n + 1)) ^ 2)⁻¹ ≤ 36 * π ^ 2 * (1 + (-airyZero (n + 1))) ^ (-(1 / 2 : ℝ)) := hD ▸ hderiv
      _ ≤ 36 * π ^ 2 * 1 := by gcongr
      _ = (6 * π) ^ 2 := by ring
  have hinv : |airyAi' (airyZero (n + 1))|⁻¹ ≤ 6 * π := by rw [← abs_inv, ← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_sq (by positivity : 0 ≤ 6 * π)]; exact Real.sqrt_le_sqrt (by simpa [sq_abs, inv_pow] using hsq)
  rw [abs_div, div_eq_mul_inv]; calc |airyAi (t + airyZero (n + 1))| * |airyAi' (airyZero (n + 1))|⁻¹ ≤ 3 * (6 * π) := by have := abs_airyAi_le_three (t + airyZero (n + 1)); gcongr
    _ = 18 * π := by ring

lemma dirichletV_singleton_ae (n : ℕ) (a : ℝ) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), dirichletV (fun k => if k = n then a else 0) t = a * dirichletPhi n t := by
  let b : ℕ → ℝ := fun k => if k = n then a else 0
  have hb : Summable (fun k => b k ^ 2) := summable_of_ne_finset_zero (s := {n}) fun k hk => by simp [b, show k ≠ n by simpa using hk]
  have hsum : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), Summable (fun k => b k * dirichletPhi k t) := ae_of_all _ fun t => summable_of_ne_finset_zero (s := {n}) fun k hk => by simp [b, show k ≠ n by simpa using hk]
  filter_upwards [dirichletV_eq_tsum_ae hb hsum] with t ht; rw [ht, tsum_eq_single n (fun k hk => by simp [b, hk])]; simp [b]

private lemma gaussian_kernel_exp_le {y : ℂ} (hy : 0 < y.re) (t s : ℝ) :
    ‖Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))‖ ≤ Real.exp (-y.re / 2 * t) * Real.exp (-y.re / 2 * s) := by
  rw [Complex.norm_exp, ← Real.exp_add]; apply Real.exp_le_exp.mpr
  have h1 : (-y * ((t + s : ℝ) : ℂ) / 2).re = -y.re * (t + s) / 2 := by simp [Complex.div_ofNat_re]
  have h2 : (((t - s : ℝ) : ℂ) ^ 2 / (4 * y)).re = (t - s) ^ 2 / 4 * (y.re / Complex.normSq y) := by
    have hnum : ((t - s : ℝ) : ℂ) ^ 2 = (((t - s) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hnum, show (4 : ℂ) * y = ((4 : ℝ) : ℂ) * y by norm_num, div_eq_mul_inv, mul_inv, ← mul_assoc,
      show (((t - s) ^ 2 : ℝ) : ℂ) * (((4 : ℝ) : ℂ)⁻¹) = (((t - s) ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.inv_re]
  have hnonneg : 0 ≤ (t - s) ^ 2 / 4 * (y.re / Complex.normSq y) := mul_nonneg (by positivity) (div_nonneg hy.le (Complex.normSq_nonneg y))
  rw [Complex.sub_re, h1, h2]; linarith

private lemma norm_w_dirichletPhi_mul_le {w : ℕ → ℝ} (hw_nn : ∀ n, 0 ≤ w n) (n : ℕ) (t s : ℝ) :
    ‖w n * dirichletPhi n t * dirichletPhi n s‖ ≤ w n * (18 * π) ^ 2 := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hw_nn n), mul_assoc]
  exact mul_le_mul_of_nonneg_left ((mul_le_mul (dirichletPhi_abs_le n t) (dirichletPhi_abs_le n s) (abs_nonneg _) (by positivity)).trans_eq (by ring)) (hw_nn n)

/-- Exact vector Gaussian transform for `diagAirySource w` (`GT.2b` setup). -/
theorem diagAirySource_gaussian_transform {w : ℕ → ℝ} (hw_nn : ∀ n, 0 ≤ w n) (hw_sum : Summable w) {y : ℂ} (hy : 0 < y.re) :
    airyTwistedLaplaceC (diagAirySource w) y = (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((∑' n : ℕ, w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) := by
  let K : ℝ → ℝ → ℂ := fun t s => Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))
  let G0 : ℝ → ℝ := fun u => 23 * (1 + |u|) * airyEnv (u : ℂ) * Real.exp (y.re * u)
  have hdom_u : Integrable G0 := ((integrable_pow_mul_airyEnv_mul_exp (k := 1) hy hy.le).const_mul 23).congr (ae_of_all _ fun u => by dsimp [G0]; split_ifs <;> ring)
  have hcohn_ae : ∀ n, AEStronglyMeasurable (fun u : ℝ => (cohnL n u : ℂ)) volume := fun n => (Lp.aestronglyMeasurable (cohnLL2 n)).congr (cohnLL2_ae n)
  have hFu_bd : ∀ (n : ℕ) (u : ℝ), ‖((w n * cohnL n u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))‖ ≤ w n * G0 u := fun n u => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw_nn n) (sq_nonneg _)), Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    dsimp [G0]; calc w n * cohnL n u ^ 2 * Real.exp (y.re * u) ≤ w n * (23 * (1 + |u|) * airyEnv (u : ℂ)) * Real.exp (y.re * u) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (cohnL_sq_le n u) (hw_nn n)) (Real.exp_pos _).le
      _ = w n * (23 * (1 + |u|) * airyEnv (u : ℂ) * Real.exp (y.re * u)) := by ring
  have hFu_int : ∀ n, Integrable (fun u : ℝ => ((w n * cohnL n u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) := fun n => by
    have hmeas : AEStronglyMeasurable (fun u : ℝ => ((w n * cohnL n u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) volume := by
      rw [show (fun u : ℝ => ((w n * cohnL n u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) = fun u => (w n : ℂ) * (cohnL n u : ℂ) ^ 2 * Complex.exp (y * (u : ℂ)) from funext fun u => by push_cast; ring]
      exact (aestronglyMeasurable_const.mul ((hcohn_ae n).pow 2)).mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    exact (hdom_u.const_mul (w n)).mono' hmeas (ae_of_all _ (hFu_bd n))
  have hFu_sum : Summable (fun n : ℕ => ∫ u : ℝ, ‖((w n * cohnL n u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => (integral_mono (hFu_int n).norm (hdom_u.const_mul (w n)) (hFu_bd n)).trans_eq (integral_const_mul _ _)) (hw_sum.mul_right (∫ u : ℝ, G0 u))
  have hLHS : airyTwistedLaplaceC (diagAirySource w) y = ∑' n : ℕ, airyTwistedLaplaceC (cardinalPb (fun k => if k = n then Real.sqrt (w n) else 0)) y := by
    unfold airyTwistedLaplaceC
    have hsum_u : ∀ u : ℝ, (diagAirySource w u : ℂ) * Complex.exp (y * (u : ℂ)) = ∑' n : ℕ, ((w n * cohnL n u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ)) := fun u => by
      simpa [diagAirySource] using ((Complex.ofRealCLM.hasSum (diagAirySource_summable hw_nn hw_sum u).hasSum).mul_right (Complex.exp (y * (u : ℂ)))).tsum_eq.symm
    have hsumm : Summable (fun n : ℕ => ∫ u : ℝ, ((w n * cohnL n u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) :=
      Summable.of_norm_bounded hFu_sum fun n => norm_integral_le_integral_norm _
    simp_rw [hsum_u]; rw [← integral_tsum_of_summable_integral_norm hFu_int hFu_sum, ← hsumm.tsum_mul_left]
    refine tsum_congr fun n => ?_; congr 2; funext u
    have hb : cardinalPb (fun k => if k = n then Real.sqrt (w n) else 0) u = w n * cohnL n u ^ 2 := by unfold cardinalPb cardinalHb; rw [tsum_eq_single n (fun k hk => by simp [hk])]; simp [mul_pow, Real.sq_sqrt (hw_nn n)]
    rw [hb]
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hE1 : Integrable (fun t : ℝ => Real.exp (-y.re / 2 * t)) μ := (show IntegrableOn (fun t : ℝ => Real.exp (-(y.re / 2 * t))) (Ioi 0) volume by simpa using airyPws_integrableOn_pow_mul_exp 0 (half_pos hy)).congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  have hE2 : Integrable (fun p : ℝ × ℝ => Real.exp (-y.re / 2 * p.1) * Real.exp (-y.re / 2 * p.2)) (μ.prod μ) := hE1.mul_prod hE1
  have hcPhi : ∀ k, Continuous (dirichletPhi k) := fun k => (continuous_airyAi.comp (continuous_id.add continuous_const)).div_const _
  have hGn_bd : ∀ (n : ℕ) (p : ℝ × ℝ), ‖((w n * dirichletPhi n p.1 * dirichletPhi n p.2 : ℝ) : ℂ) * K p.1 p.2‖ ≤ w n * (18 * π) ^ 2 * (Real.exp (-y.re / 2 * p.1) * Real.exp (-y.re / 2 * p.2)) := fun n p => by
    rw [norm_mul, Complex.norm_real]; exact mul_le_mul (norm_w_dirichletPhi_mul_le hw_nn n p.1 p.2) (gaussian_kernel_exp_le hy p.1 p.2) (norm_nonneg _) (mul_nonneg (hw_nn n) (by positivity))
  have hGn_int : ∀ n : ℕ, Integrable (fun p : ℝ × ℝ => ((w n * dirichletPhi n p.1 * dirichletPhi n p.2 : ℝ) : ℂ) * K p.1 p.2) (μ.prod μ) := fun n =>
    (hE2.const_mul (w n * (18 * π) ^ 2)).mono' (((Complex.continuous_ofReal.comp ((continuous_const.mul ((hcPhi n).comp continuous_fst)).mul ((hcPhi n).comp continuous_snd))).mul (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable) (ae_of_all _ (hGn_bd n))
  have hGn_sum : Summable (fun n : ℕ => ∫ p : ℝ × ℝ, ‖((w n * dirichletPhi n p.1 * dirichletPhi n p.2 : ℝ) : ℂ) * K p.1 p.2‖ ∂(μ.prod μ)) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => (integral_mono (hGn_int n).norm (hE2.const_mul (w n * (18 * π) ^ 2)) (hGn_bd n)).trans_eq (by rw [integral_const_mul, mul_assoc]))
      (hw_sum.mul_right ((18 * π) ^ 2 * ∫ p : ℝ × ℝ, Real.exp (-y.re / 2 * p.1) * Real.exp (-y.re / 2 * p.2) ∂(μ.prod μ)))
  have hRHS_swap : (∑' n : ℕ, ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * K t s) =
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((∑' n : ℕ, w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * K t s := by
    have hprod : ∀ n, ∫ p : ℝ × ℝ, ((w n * dirichletPhi n p.1 * dirichletPhi n p.2 : ℝ) : ℂ) * K p.1 p.2 ∂(μ.prod μ) = ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * K t s := fun n => integral_prod _ (hGn_int n)
    simp_rw [← hprod, integral_tsum_of_summable_integral_norm hGn_int hGn_sum]
    have hsumm_pt : ∀ t s : ℝ, Summable (fun n : ℕ => w n * dirichletPhi n t * dirichletPhi n s) := fun t s => Summable.of_norm_bounded (hw_sum.mul_right ((18 * π) ^ 2)) fun n => norm_w_dirichletPhi_mul_le hw_nn n t s
    have hpt_sum : ∀ t s : ℝ, ((∑' n : ℕ, w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * K t s = ∑' n : ℕ, ((w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * K t s := fun t s => by simpa using ((Complex.ofRealCLM.hasSum (hsumm_pt t s).hasSum).mul_right (K t s)).tsum_eq.symm
    have hInt_tot : Integrable (fun p : ℝ × ℝ => ((∑' n : ℕ, w n * dirichletPhi n p.1 * dirichletPhi n p.2 : ℝ) : ℂ) * K p.1 p.2) (μ.prod μ) := by
      refine (hE2.const_mul ((∑' n : ℕ, w n) * (18 * π) ^ 2)).mono' ?_ (ae_of_all _ fun p => ?_)
      · refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N (p : ℝ × ℝ) => ∑ n ∈ Finset.range N, ((w n * dirichletPhi n p.1 * dirichletPhi n p.2 : ℝ) : ℂ) * K p.1 p.2)
          (fun N => Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n _ => (hGn_int n).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
        simpa using ((Complex.ofRealCLM.hasSum (hsumm_pt p.1 p.2).hasSum).mul_right (K p.1 p.2)).tendsto_sum_nat
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hs_n : Summable (fun n : ℕ => ‖w n * dirichletPhi n p.1 * dirichletPhi n p.2‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_w_dirichletPhi_mul_le hw_nn n p.1 p.2) (hw_sum.mul_right ((18 * π) ^ 2))
        exact mul_le_mul ((norm_tsum_le_tsum_norm hs_n).trans ((hs_n.tsum_le_tsum (fun n => norm_w_dirichletPhi_mul_le hw_nn n p.1 p.2) (hw_sum.mul_right _)).trans_eq tsum_mul_right))
          (gaussian_kernel_exp_le hy p.1 p.2) (norm_nonneg _) (mul_nonneg (tsum_nonneg hw_nn) (by positivity))
    rw [← integral_prod _ hInt_tot]; congr 1; funext p; exact (hpt_sum p.1 p.2).symm
  rw [hLHS]
  have hterm : ∀ n : ℕ, airyTwistedLaplaceC (cardinalPb (fun k => if k = n then Real.sqrt (w n) else 0)) y =
      (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) * ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * K t s := fun n => by
    rw [airySquare_gaussian_transform (summable_of_ne_finset_zero (s := {n}) fun k hk => by simp [show k ≠ n by simpa using hk]) hy]; congr 1
    refine setIntegral_congr_ae measurableSet_Ioi ?_; filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp (dirichletV_singleton_ae n (Real.sqrt (w n)))] with t ht ht0
    refine setIntegral_congr_ae measurableSet_Ioi ?_; filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp (dirichletV_singleton_ae n (Real.sqrt (w n)))] with s hs hs0
    rw [ht ht0, hs hs0]; congr 1; exact congrArg Complex.ofReal <| by rw [mul_mul_mul_comm, Real.mul_self_sqrt (hw_nn n)]; ring
  simp_rw [hterm]
  have hsum_R : Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * K t s) := by
    have hprod : ∀ n, ∫ p : ℝ × ℝ, ((w n * dirichletPhi n p.1 * dirichletPhi n p.2 : ℝ) : ℂ) * K p.1 p.2 ∂(μ.prod μ) = ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((w n * dirichletPhi n t * dirichletPhi n s : ℝ) : ℂ) * K t s := fun n => integral_prod _ (hGn_int n)
    simp_rw [← hprod]; exact Summable.of_norm_bounded hGn_sum fun n => norm_integral_le_integral_norm _
  rw [hsum_R.tsum_mul_left, hRHS_swap]

private lemma sum_dirichletPhi_mul_le {w : ℕ → ℝ} (hw_nn : ∀ n, 0 ≤ w n) (hw_sum : Summable w)
    {A : ℝ} (_hA : 0 ≤ A) {β : ℕ} (hdiag : ∀ t ≥ 0, ∑' n : ℕ, w n * dirichletPhi n t ^ 2 ≤ A ^ 2 * (min t 1) ^ (2 * β))
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) : |∑' n : ℕ, w n * dirichletPhi n t * dirichletPhi n s| ≤ A ^ 2 * t ^ (β : ℝ) * s ^ (β : ℝ) := by
  have hsum : Summable (fun n : ℕ => ‖w n * dirichletPhi n t * dirichletPhi n s‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_w_dirichletPhi_mul_le hw_nn n t s) (hw_sum.mul_right ((18 * π) ^ 2))
  let mt : ℝ := min t 1; let ms : ℝ := min s 1; have hmt : 0 < mt := lt_min ht one_pos; have hms : 0 < ms := lt_min hs one_pos
  let r : ℝ := ms ^ β / mt ^ β; have hr : 0 < r := div_pos (pow_pos hms β) (pow_pos hmt β)
  have hr_sq' : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le; have hri_sq' : (Real.sqrt r)⁻¹ ^ 2 = r⁻¹ := by rw [inv_pow, hr_sq']
  have hinv : Real.sqrt r * (Real.sqrt r)⁻¹ = 1 := mul_inv_cancel₀ (Real.sqrt_pos.mpr hr).ne'
  have hfin : ∀ N : ℕ, ∑ n ∈ Finset.range N, ‖w n * dirichletPhi n t * dirichletPhi n s‖ ≤ A ^ 2 * t ^ (β : ℝ) * s ^ (β : ℝ) := fun N => by
    have hpt : ∀ n, ‖w n * dirichletPhi n t * dirichletPhi n s‖ ≤ (1 / 2 : ℝ) * (r * (w n * dirichletPhi n t ^ 2) + r⁻¹ * (w n * dirichletPhi n s ^ 2)) := fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hw_nn n)]; have hsq : 0 ≤ (Real.sqrt r * |dirichletPhi n t| - (Real.sqrt r)⁻¹ * |dirichletPhi n s|) ^ 2 := sq_nonneg _
      have hexp : (Real.sqrt r * |dirichletPhi n t| - (Real.sqrt r)⁻¹ * |dirichletPhi n s|) ^ 2 = r * |dirichletPhi n t| ^ 2 + r⁻¹ * |dirichletPhi n s| ^ 2 - 2 * (|dirichletPhi n t| * |dirichletPhi n s|) := by
        calc _ = Real.sqrt r ^ 2 * |dirichletPhi n t| ^ 2 + (Real.sqrt r)⁻¹ ^ 2 * |dirichletPhi n s| ^ 2 - 2 * (Real.sqrt r * (Real.sqrt r)⁻¹) * (|dirichletPhi n t| * |dirichletPhi n s|) := by ring
          _ = _ := by rw [hr_sq', hri_sq', hinv]; ring
      have hbase : |dirichletPhi n t| * |dirichletPhi n s| ≤ (1 / 2 : ℝ) * (r * |dirichletPhi n t| ^ 2 + r⁻¹ * |dirichletPhi n s| ^ 2) := by linarith
      calc w n * |dirichletPhi n t| * |dirichletPhi n s| = w n * (|dirichletPhi n t| * |dirichletPhi n s|) := by ring
        _ ≤ w n * ((1 / 2 : ℝ) * (r * |dirichletPhi n t| ^ 2 + r⁻¹ * |dirichletPhi n s| ^ 2)) := mul_le_mul_of_nonneg_left hbase (hw_nn n)
        _ = (1 / 2 : ℝ) * (r * (w n * dirichletPhi n t ^ 2) + r⁻¹ * (w n * dirichletPhi n s ^ 2)) := by rw [sq_abs, sq_abs]; ring
    have hsum_u : ∀ u ≥ 0, ∑ n ∈ Finset.range N, w n * dirichletPhi n u ^ 2 ≤ A ^ 2 * (min u 1) ^ (2 * β) := fun u hu =>
      ((Summable.of_nonneg_of_le (fun n => mul_nonneg (hw_nn n) (sq_nonneg _)) (fun n => mul_le_mul_of_nonneg_left (sq_abs (dirichletPhi n u) ▸ pow_le_pow_left₀ (abs_nonneg _) (dirichletPhi_abs_le n u) 2) (hw_nn n))
        (hw_sum.mul_right _)).sum_le_tsum (Finset.range N) (fun n _ => mul_nonneg (hw_nn n) (sq_nonneg _))).trans (hdiag u hu)
    have hsum1 := hsum_u t ht.le; have hsum2 := hsum_u s hs.le
    calc ∑ n ∈ Finset.range N, ‖w n * dirichletPhi n t * dirichletPhi n s‖ ≤ ∑ n ∈ Finset.range N, (1 / 2 : ℝ) * (r * (w n * dirichletPhi n t ^ 2) + r⁻¹ * (w n * dirichletPhi n s ^ 2)) := Finset.sum_le_sum fun n _ => hpt n
      _ = (1 / 2 : ℝ) * (r * ∑ n ∈ Finset.range N, w n * dirichletPhi n t ^ 2 + r⁻¹ * ∑ n ∈ Finset.range N, w n * dirichletPhi n s ^ 2) := by simp only [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ (1 / 2 : ℝ) * (r * (A ^ 2 * mt ^ (2 * β)) + r⁻¹ * (A ^ 2 * ms ^ (2 * β))) := by gcongr
      _ = A ^ 2 * mt ^ β * ms ^ β := by dsimp [r]; rw [show 2 * β = β + β by omega, pow_add]; field_simp [hmt.ne', hms.ne']; ring
      _ ≤ A ^ 2 * t ^ (β : ℝ) * s ^ (β : ℝ) := by rw [← Real.rpow_natCast mt β, ← Real.rpow_natCast ms β]; have := Real.rpow_le_rpow hmt.le (min_le_left t 1) (Nat.cast_nonneg β); have := Real.rpow_le_rpow hms.le (min_le_left s 1) (Nat.cast_nonneg β); gcongr
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_of_sum_range_le hfin)

private lemma airyTwisted_line_analytic {X : ℝ → ℝ} (hX_diff : DifferentiableOn ℂ (airyTwistedLaplaceC X) {y : ℂ | 0 < y.re}) {ε : ℝ} (hε : 0 < ε) :
    let U : Set ℂ := {ω : ℂ | -1 < ω.im}; let y_of : ℂ → ℂ := fun ω => ((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * ω)
    IsOpen U ∧ DifferentiableOn ℂ (fun ω => airyTwistedLaplaceC X (y_of ω)) U ∧ (∀ t : ℝ, Metric.closedBall (t : ℂ) (1 / 2) ⊆ U) ∧ ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => airyTwistedLaplaceC X (y_of (t : ℂ))) := by
  let U : Set ℂ := {ω : ℂ | -1 < ω.im}; let y_of : ℂ → ℂ := fun ω => ((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * ω); have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hy_re : ∀ {ω : ℂ}, ω ∈ U → 0 < (y_of ω).re := fun {ω} hω => by
    change -1 < ω.im at hω; simp only [y_of, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re, Complex.one_re, Complex.I_re, Complex.I_im, one_mul]
    exact mul_pos (mul_pos ceCs_pos (inv_pos.mpr hε)) (by linarith)
  have hF_diff : DifferentiableOn ℂ (fun ω => airyTwistedLaplaceC X (y_of ω)) U := fun ω hω =>
    (hX_diff (y_of ω) (hy_re hω)).comp ω (((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.const_mul Complex.I)).const_mul _ |>.differentiableWithinAt) (fun _ hz => hy_re hz)
  have hball : ∀ t : ℝ, Metric.closedBall (t : ℂ) (1 / 2) ⊆ U := fun t ω hω => by
    have him : |ω.im| ≤ 1 / 2 := by simpa [Complex.sub_im, Complex.ofReal_im, sub_zero] using (Complex.abs_im_le_norm (ω - (t : ℂ))).trans (by simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hω)
    change -1 < ω.im; linarith [(abs_le.mp him).1]
  have hC_on : ContDiffOn ℂ (⊤ : ℕ∞) (fun ω => airyTwistedLaplaceC X (y_of ω)) U := (hF_diff.analyticOnNhd hU).contDiffOn hU.uniqueDiffOn
  exact ⟨hU, hF_diff, hball, contDiff_iff_contDiffAt.mpr fun t => ((hC_on.contDiffAt (hU.mem_nhds (by change -1 < ((t : ℂ)).im; simp))).restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt⟩

private noncomputable def gt2bDiagConst (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * 2 ^ j * (ceK * (2 * π * ceCs) ^ (-(1 / 2 : ℝ)) * max ((4 / ceCs) ^ (2 : ℝ)) ((4 / ceCs) ^ (4 : ℝ))) + 1

private lemma gt2bDiagConst_pos (j : ℕ) : 0 < gt2bDiagConst j := by
  unfold gt2bDiagConst; have h0 : 0 ≤ (j.factorial : ℝ) * 2 ^ j * (ceK * (2 * π * ceCs) ^ (-(1 / 2 : ℝ)) * max ((4 / ceCs) ^ (2 : ℝ)) ((4 / ceCs) ^ (4 : ℝ))) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _)) (mul_nonneg (mul_nonneg ceK_pos.le (Real.rpow_nonneg (mul_pos (mul_pos two_pos Real.pi_pos) ceCs_pos).le _)) (le_max_of_le_left (Real.rpow_nonneg (div_pos (by norm_num) ceCs_pos).le _))); linarith

private lemma gaussian_double_integral_cauchy_bounds {X : ℝ → ℝ} {K : ℝ → ℝ → ℝ} {β : ℕ}
    (hβ : β = 0 ∨ β = 1) {A : ℝ} (_hA : 0 ≤ A) (hX_diff : DifferentiableOn ℂ (airyTwistedLaplaceC X) {y : ℂ | 0 < y.re})
    (hX_eq : ∀ {y : ℂ}, 0 < y.re → airyTwistedLaplaceC X y = (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), (K t s : ℂ) * Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)))
    (hK_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => (K p.1 p.2 : ℂ)) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))
    (hK_bd : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))), |K p.1 p.2| ≤ A ^ 2 * p.1 ^ (β : ℝ) * p.2 ^ (β : ℝ))
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC X (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤
      gt2bDiagConst j * A ^ 2 * ε ^ (5 / 2 + 2 * (β : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  let Mβ : ℝ := ceK * (2 * π * ceCs) ^ (-(1 / 2 : ℝ)) * max ((4 / ceCs) ^ (2 : ℝ)) ((4 / ceCs) ^ (4 : ℝ))
  let U : Set ℂ := {ω : ℂ | -1 < ω.im}; let y_of : ℂ → ℂ := fun ω => ((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * ω)
  obtain ⟨hU, hF_diff, hball, _⟩ := airyTwisted_line_analytic hX_diff hε
  let B : ℝ → ℝ := fun t => Mβ * A ^ 2 * ε ^ (5 / 2 + 2 * (β : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))
  have hsphere : ∀ (t : ℝ) (ω : ℂ), ω ∈ Metric.sphere (t : ℂ) (1 / 2) → ‖airyTwistedLaplaceC X (y_of ω)‖ ≤ B t := fun t ω hω => by
    have hdist : ‖ω - (t : ℂ)‖ = 1 / 2 := by simpa [Complex.dist_eq] using Metric.mem_sphere.mp hω
    have him : |ω.im| ≤ 1 / 2 := by simpa [Complex.sub_im, Complex.ofReal_im, sub_zero] using (Complex.abs_im_le_norm (ω - (t : ℂ))).trans_eq hdist
    have hre1 : (1 / 2 : ℝ) ≤ (1 - Complex.I * ω).re := by simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub]; linarith [(abs_le.mp him).1]
    have hceε : 0 < ceCs * ε⁻¹ := mul_pos ceCs_pos (inv_pos.mpr hε)
    have hyre_lb : (1 / 2 : ℝ) * (ceCs * ε⁻¹) ≤ (y_of ω).re := by dsimp [y_of]; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]; linarith [mul_le_mul_of_nonneg_left hre1 hceε.le]
    have hyre_pos : 0 < (y_of ω).re := lt_of_lt_of_le (mul_pos (by norm_num) hceε) hyre_lb
    have hynorm_lb : (1 / 2 : ℝ) * (ceCs * ε⁻¹) * Real.sqrt (1 + t ^ 2) ≤ ‖y_of ω‖ := by
      dsimp [y_of]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hceε]
      calc (1 / 2 : ℝ) * (ceCs * ε⁻¹) * Real.sqrt (1 + t ^ 2) = (ceCs * ε⁻¹) * (Real.sqrt (1 + t ^ 2) / 2) := by ring
        _ ≤ (ceCs * ε⁻¹) * ‖1 - Complex.I * ω‖ := mul_le_mul_of_nonneg_left (norm_one_sub_I_mul_ge hdist.le).1 hceε.le
    rw [hX_eq hyre_pos, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceK_pos]
    have hpref_norm : ‖(4 * (π : ℂ) * y_of ω) ^ (-(1 / 2 : ℂ))‖ ≤ (2 * π * ceCs) ^ (-(1 / 2 : ℝ)) * ε ^ (1 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
      rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
      have h4norm : 2 * π * ceCs * ε⁻¹ * Real.sqrt (1 + t ^ 2) ≤ ‖4 * (π : ℂ) * y_of ω‖ := by
        rw [show 4 * (π : ℂ) * y_of ω = ((4 * π : ℝ) : ℂ) * y_of ω by push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; nlinarith [Real.pi_pos]
      have h2p : 0 < 2 * π * ceCs := mul_pos (mul_pos two_pos Real.pi_pos) ceCs_pos; have h2pe : 0 < 2 * π * ceCs * ε⁻¹ := mul_pos h2p (inv_pos.mpr hε)
      calc ‖4 * (π : ℂ) * y_of ω‖ ^ (-(1 / 2 : ℝ)) ≤ (2 * π * ceCs * ε⁻¹ * Real.sqrt (1 + t ^ 2)) ^ (-(1 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (mul_pos h2pe (Real.sqrt_pos.mpr (by positivity))) h4norm (by norm_num)
        _ = (2 * π * ceCs) ^ (-(1 / 2 : ℝ)) * ε ^ (1 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
            rw [Real.mul_rpow h2pe.le (Real.sqrt_nonneg _), Real.mul_rpow h2p.le (inv_nonneg.mpr hε.le), Real.inv_rpow hε.le, Real.rpow_neg hε.le, inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ 1 + t ^ 2)]; norm_num
    let μ := volume.restrict (Ioi (0 : ℝ))
    have hE_int : Integrable (fun u : ℝ => u ^ (β : ℝ) * Real.exp (-((y_of ω).re / 2) * u)) μ :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg β)) one_pos (half_pos hyre_pos)).congr_fun (fun u _ => by simp [Real.rpow_one]) measurableSet_Ioi
    have hE_val : ∫ u in Ioi (0 : ℝ), u ^ (β : ℝ) * Real.exp (-((y_of ω).re / 2) * u) = (2 / (y_of ω).re) ^ ((β : ℝ) + 1) := by
      have hv := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (β : ℝ) + 1) (r := (y_of ω).re / 2) (by positivity) (half_pos hyre_pos)
      have hG : Real.Gamma ((β : ℝ) + 1) = 1 := by rcases hβ with rfl | rfl; simp [Real.Gamma_one]; norm_num [Real.Gamma_two]
      simpa [add_sub_cancel_right, hG, one_div, inv_div] using hv
    have hint_norm : ‖∫ t' in Ioi (0 : ℝ), ∫ s' in Ioi (0 : ℝ), (K t' s' : ℂ) * Complex.exp (-(y_of ω) * ((t' + s' : ℝ) : ℂ) / 2 - ((t' - s' : ℝ) : ℂ) ^ 2 / (4 * y_of ω))‖ ≤ A ^ 2 * (2 / (y_of ω).re) ^ (2 * (β : ℝ) + 2) := by
      let Φ : ℝ → ℝ → ℂ := fun t' s' => (K t' s' : ℂ) * Complex.exp (-(y_of ω) * ((t' + s' : ℝ) : ℂ) / 2 - ((t' - s' : ℝ) : ℂ) ^ 2 / (4 * y_of ω))
      have hΦ_bd : ∀ᵐ p ∂(μ.prod μ), ‖Φ p.1 p.2‖ ≤ A ^ 2 * ((p.1 ^ (β : ℝ) * Real.exp (-((y_of ω).re / 2) * p.1)) * (p.2 ^ (β : ℝ) * Real.exp (-((y_of ω).re / 2) * p.2))) := by
        filter_upwards [hK_bd, Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi), Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)] with p hp hp1 hp2
        dsimp [Φ]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |K p.1 p.2| * ‖Complex.exp _‖ ≤ (A ^ 2 * p.1 ^ (β : ℝ) * p.2 ^ (β : ℝ)) * (Real.exp (-(y_of ω).re / 2 * p.1) * Real.exp (-(y_of ω).re / 2 * p.2)) :=
              mul_le_mul hp (gaussian_kernel_exp_le hyre_pos p.1 p.2) (norm_nonneg _) (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt hp1) _)) (Real.rpow_nonneg (le_of_lt hp2) _))
          _ = _ := by rw [show -(y_of ω).re / 2 = -((y_of ω).re / 2) by ring]; ring
      have hΦ_int : Integrable (fun p : ℝ × ℝ => Φ p.1 p.2) (μ.prod μ) := ((hE_int.mul_prod hE_int).const_mul (A ^ 2)).mono' (hK_meas.mul (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) hΦ_bd
      rw [← integral_prod _ hΦ_int]; calc ‖∫ p : ℝ × ℝ, Φ p.1 p.2 ∂(μ.prod μ)‖ ≤ ∫ p : ℝ × ℝ, ‖Φ p.1 p.2‖ ∂(μ.prod μ) := norm_integral_le_integral_norm _
        _ ≤ ∫ p : ℝ × ℝ, A ^ 2 * ((p.1 ^ (β : ℝ) * Real.exp (-((y_of ω).re / 2) * p.1)) * (p.2 ^ (β : ℝ) * Real.exp (-((y_of ω).re / 2) * p.2))) ∂(μ.prod μ) := integral_mono_ae hΦ_int.norm ((hE_int.mul_prod hE_int).const_mul (A ^ 2)) hΦ_bd
        _ = A ^ 2 * (2 / (y_of ω).re) ^ (2 * (β : ℝ) + 2) := by
            rw [integral_const_mul, integral_prod_mul (fun u => u ^ (β : ℝ) * Real.exp (-((y_of ω).re / 2) * u)) (fun u => u ^ (β : ℝ) * Real.exp (-((y_of ω).re / 2) * u)), hE_val, ← Real.rpow_add (div_pos two_pos hyre_pos)]; congr 2; ring
    have hre_pow : (2 / (y_of ω).re) ^ (2 * (β : ℝ) + 2) ≤ max ((4 / ceCs) ^ (2 : ℝ)) ((4 / ceCs) ^ (4 : ℝ)) * ε ^ (2 + 2 * (β : ℝ)) := by
      have h4cs : 0 < 4 / ceCs := div_pos (by norm_num) ceCs_pos
      have hdiv : 2 / (y_of ω).re ≤ (4 / ceCs) * ε := by rw [div_le_iff₀ hyre_pos]; calc 2 = (4 / ceCs) * ε * ((1 / 2 : ℝ) * (ceCs * ε⁻¹)) := by field_simp [ceCs_pos.ne', hε.ne']; ring
        _ ≤ (4 / ceCs) * ε * (y_of ω).re := mul_le_mul_of_nonneg_left hyre_lb (mul_pos h4cs hε).le
      calc (2 / (y_of ω).re) ^ (2 * (β : ℝ) + 2) ≤ ((4 / ceCs) * ε) ^ (2 * (β : ℝ) + 2) := Real.rpow_le_rpow (div_pos two_pos hyre_pos).le hdiv (by positivity)
        _ = (4 / ceCs) ^ (2 * (β : ℝ) + 2) * ε ^ (2 + 2 * (β : ℝ)) := by rw [Real.mul_rpow h4cs.le hε.le, add_comm (2 * (β : ℝ)) 2]
        _ ≤ max ((4 / ceCs) ^ (2 : ℝ)) ((4 / ceCs) ^ (4 : ℝ)) * ε ^ (2 + 2 * (β : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hε.le _)
            rcases hβ with rfl | rfl
            · simp
            · norm_num
    have hε_add : ε ^ (1 / 2 : ℝ) * ε ^ (2 + 2 * (β : ℝ)) = ε ^ (5 / 2 + 2 * (β : ℝ)) := by rw [← Real.rpow_add hε]; congr 1; ring
    have h2pe_nn : 0 ≤ (2 * π * ceCs) ^ (-(1 / 2 : ℝ)) * ε ^ (1 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (mul_pos (mul_pos two_pos Real.pi_pos) ceCs_pos).le _) (Real.rpow_nonneg hε.le _)) (Real.rpow_nonneg (by positivity) _)
    calc ceK * ‖(4 * (π : ℂ) * y_of ω) ^ (-(1 / 2 : ℂ))‖ * ‖∫ t' in Ioi (0 : ℝ), ∫ s' in Ioi (0 : ℝ), (K t' s' : ℂ) * Complex.exp (-(y_of ω) * ((t' + s' : ℝ) : ℂ) / 2 - ((t' - s' : ℝ) : ℂ) ^ 2 / (4 * y_of ω))‖
        ≤ ceK * ((2 * π * ceCs) ^ (-(1 / 2 : ℝ)) * ε ^ (1 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) * (A ^ 2 * (max ((4 / ceCs) ^ (2 : ℝ)) ((4 / ceCs) ^ (4 : ℝ)) * ε ^ (2 + 2 * (β : ℝ)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpref_norm ceK_pos.le) (hint_norm.trans (mul_le_mul_of_nonneg_left hre_pow (sq_nonneg A))) (norm_nonneg _) (mul_nonneg ceK_pos.le h2pe_nn)
      _ = B t := by dsimp [B, Mβ]; rw [← hε_add]; ring
  have hbd := (holomorphic_real_contDiff_and_cauchy hU hF_diff (fun t => by change -1 < ((t : ℂ)).im; simp) (by norm_num : (0 : ℝ) < 1 / 2) hball hsphere).2 j τ
  calc ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC X (y_of (t : ℂ))) τ‖ ≤ (j.factorial : ℝ) * B τ / (1 / 2 : ℝ) ^ j := hbd
    _ = ((j.factorial : ℝ) * 2 ^ j * Mβ) * A ^ 2 * ε ^ (5 / 2 + 2 * (β : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by dsimp [B]; rw [div_eq_mul_inv, show ((1 / 2 : ℝ) ^ j)⁻¹ = 2 ^ j by simp [inv_pow]]; ring
    _ ≤ gt2bDiagConst j * A ^ 2 * ε ^ (5 / 2 + 2 * (β : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by unfold gt2bDiagConst; gcongr; linarith

private lemma diagAirySource_differentiableOn {w : ℕ → ℝ} (hw_nn : ∀ n, 0 ≤ w n) (hw_sum : Summable w) :
    DifferentiableOn ℂ (airyTwistedLaplaceC (diagAirySource w)) {y : ℂ | 0 < y.re} := by
  have hcohn_ae : ∀ n, AEStronglyMeasurable (fun u : ℝ => (cohnL n u : ℂ)) volume := fun n => (Lp.aestronglyMeasurable (cohnLL2 n)).congr (cohnLL2_ae n)
  let S : ℕ → ℝ → ℂ := fun N u => ∑ n ∈ Finset.range N, (w n : ℂ) * (cohnL n u : ℂ) ^ 2
  have hXm : AEStronglyMeasurable (fun u : ℝ => (diagAirySource w u : ℂ)) volume := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := S) (fun N => Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n _ => aestronglyMeasurable_const.mul ((hcohn_ae n).pow 2)) (ae_of_all _ fun u => ?_)
    simpa [S, diagAirySource, Complex.ofReal_sum] using (Complex.ofRealCLM.hasSum (diagAirySource_summable hw_nn hw_sum u).hasSum).tendsto_sum_nat
  exact differentiableOn_airyTwistedLaplaceC_of_le hXm fun u => by have hd := diagAirySource_le hw_nn hw_sum u; rw [abs_of_nonneg hd.1]; exact hd.2

/-- **Lemma `GT.2b(1)` (`(cegt:eqGT2b)`):** uniform vertical-line Cauchy derivative bounds (`j : ℕ`, hence
`j = 0, 1, 2`) for any diagonal mixture `diagAirySource w` satisfying the `min(t, 1)^{2β}` envelope (`β ∈ {0, 1}`). -/
theorem diagAirySource_dual_deriv_bound :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ {w : ℕ → ℝ} (_hw_nn : ∀ n, 0 ≤ w n) (_hw_sum : Summable w) {A : ℝ} (_hA : 0 ≤ A) {β : ℕ} (_hβ : β = 0 ∨ β = 1)
        (_hdiag : ∀ t ≥ 0, ∑' n : ℕ, w n * dirichletPhi n t ^ 2 ≤ A ^ 2 * (min t 1) ^ (2 * β)) (j : ℕ) {ε : ℝ} (_hε : 0 < ε) (τ : ℝ),
        ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC (diagAirySource w) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤ C j * A ^ 2 * ε ^ (5 / 2 + 2 * (β : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  refine ⟨gt2bDiagConst, gt2bDiagConst_pos, fun {w} hw_nn hw_sum {A} hA {β} hβ hdiag j {ε} hε τ => ?_⟩
  have hcPhi : ∀ k, Continuous (dirichletPhi k) := fun k => (continuous_airyAi.comp (continuous_id.add continuous_const)).div_const _
  have hK_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => ((∑' n : ℕ, w n * dirichletPhi n p.1 * dirichletPhi n p.2 : ℝ) : ℂ)) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable (measurable_of_tendsto_metrizable (f := fun N (p : ℝ × ℝ) => ∑ n ∈ Finset.range N, w n * dirichletPhi n p.1 * dirichletPhi n p.2)
      (fun N => Finset.measurable_sum (Finset.range N) fun n _ => ((measurable_const.mul ((hcPhi n).comp continuous_fst).measurable).mul ((hcPhi n).comp continuous_snd).measurable))
      (tendsto_pi_nhds.mpr fun p => (Summable.of_norm_bounded (hw_sum.mul_right ((18 * π) ^ 2)) (fun n => norm_w_dirichletPhi_mul_le hw_nn n p.1 p.2)).hasSum.tendsto_sum_nat)).aemeasurable).aestronglyMeasurable
  have hK_bd : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))), |∑' n : ℕ, w n * dirichletPhi n p.1 * dirichletPhi n p.2| ≤ A ^ 2 * p.1 ^ (β : ℝ) * p.2 ^ (β : ℝ) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi), Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)] with p hp1 hp2
    exact sum_dirichletPhi_mul_le hw_nn hw_sum hA hdiag hp1 hp2
  exact gaussian_double_integral_cauchy_bounds hβ hA (diagAirySource_differentiableOn hw_nn hw_sum) (fun {y} hy => diagAirySource_gaussian_transform hw_nn hw_sum hy) hK_meas hK_bd j hε τ

/-- Coherent vertical-line Cauchy derivative bounds (`(ceo:O11n.11)` for all `j : ℕ`, extending `β = 0`). -/
theorem cardinalPb_dual_deriv_bound :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧ ∀ {b : ℕ → ℝ} (_hb : Summable (fun n : ℕ => b n ^ 2)) {M : ℝ} (_hM : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |dirichletV b t| ≤ M)
        (j : ℕ) {ε : ℝ} (_hε : 0 < ε) (τ : ℝ),
        ‖iteratedDeriv j (fun t : ℝ => airyTwistedLaplaceC (cardinalPb b) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤ C j * M ^ 2 * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  refine ⟨gt2bDiagConst, gt2bDiagConst_pos, fun {b} hb {M} hM j {ε} hε τ => ?_⟩
  let μ := volume.restrict (Ioi (0 : ℝ))
  have : (ae μ).NeBot := ae_neBot.2 fun h => by have := congrArg (· (Ioi (0 : ℝ))) h; simp [μ, Measure.restrict_apply measurableSet_Ioi] at this
  have hM0 : 0 ≤ M := by obtain ⟨t₀, ht₀⟩ := hM.exists; exact (abs_nonneg _).trans ht₀
  have hpack := cardinal_series_of_sq_hasSum hb.hasSum; let F : AiryL2 := ∑' n : ℕ, (b n : ℂ) • cohnLL2 n
  have hcohn_ae : ∀ n, AEStronglyMeasurable (fun u : ℝ => (cohnL n u : ℂ)) volume := fun n => (Lp.aestronglyMeasurable (cohnLL2 n)).congr (cohnLL2_ae n)
  have hXm : AEStronglyMeasurable (fun u : ℝ => (cardinalPb b u : ℂ)) volume := by
    let S : ℕ → ℝ → ℂ := fun N u => ∑ n ∈ Finset.range N, (b n : ℂ) * (cohnL n u : ℂ)
    have hHb : AEStronglyMeasurable (fun u : ℝ => (cardinalHb b u : ℂ)) volume := by
      refine aestronglyMeasurable_of_tendsto_ae atTop (f := S) (fun N => Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n _ => aestronglyMeasurable_const.mul (hcohn_ae n)) (ae_of_all _ fun u => ?_)
      unfold cardinalHb; rw [(hpack.2.2.2.2.1 u).1.tsum_eq]
      simpa [S, Complex.ofReal_sum] using (Complex.ofRealCLM.hasSum (hpack.2.2.2.2.1 u).1).tendsto_sum_nat
    exact (hHb.pow 2).congr (ae_of_all _ fun u => by simp [cardinalPb])
  have hX_diff : DifferentiableOn ℂ (airyTwistedLaplaceC (cardinalPb b)) {y : ℂ | 0 < y.re} :=
    differentiableOn_airyTwistedLaplaceC_of_le hXm (C_X := 23 * ‖F‖ ^ 2) fun u => by
      have hHb_eq : (cardinalHb b u : ℂ) = airyPWFun F (u : ℂ) := by unfold cardinalHb; dsimp only [F]; rw [(hpack.2.2.2.2.1 u).1.tsum_eq, ← (hpack.2.2.2.2.1 u).2]
      have hnorm_sq := norm_airyPWFun_sq_le F (u : ℂ); rw [← hHb_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.norm_real, Real.norm_eq_abs] at hnorm_sq
      simpa [cardinalPb, abs_of_nonneg (sq_nonneg (cardinalHb b u)), mul_assoc] using hnorm_sq
  have hVm : Measurable (dirichletV b) := Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable (dirichletVL2 b)).measurable
  have hK_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => ((dirichletV b p.1 * dirichletV b p.2 : ℝ) : ℂ)) (μ.prod μ) :=
    (Complex.continuous_ofReal.measurable.comp ((hVm.comp measurable_fst).mul (hVm.comp measurable_snd))).aestronglyMeasurable
  have hK_bd : ∀ᵐ p ∂(μ.prod μ), |dirichletV b p.1 * dirichletV b p.2| ≤ M ^ 2 * p.1 ^ ((0 : ℕ) : ℝ) * p.2 ^ ((0 : ℕ) : ℝ) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hM, Measure.quasiMeasurePreserving_snd.ae hM] with p hp1 hp2
    simp only [Nat.cast_zero, Real.rpow_zero, mul_one, abs_mul, sq]; exact mul_le_mul hp1 hp2 (abs_nonneg _) hM0
  simpa only [gt2bDiagConst, Nat.cast_zero, mul_zero, add_zero] using gaussian_double_integral_cauchy_bounds (Or.inl rfl) hM0 hX_diff
    (fun {y} hy => airySquare_gaussian_transform hb hy) hK_meas hK_bd j hε τ

/-- **Lemma `GT.2b(2)` (general Leibniz product):** multiplying a `C²` function obeying
`C_f ε^{7/2} (1 + τ²)^{-1/4}` bounds through `j ≤ 2` by `bsplineMult (c_s κ / m) m` (`m ≥ 3`)
improves decay to `(1 + τ²)^{-3/2}`. -/
theorem bsplineMult_mul_dual_bound {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 3 ≤ m) :
    ∃ C > 0, ∀ {ε C_f : ℝ} (_hε : 0 < ε) (_hCf : 0 ≤ C_f) {f : ℝ → ℂ}, ContDiff ℝ 2 f →
      (∀ j ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv j f τ‖ ≤ C_f * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) →
      ∀ j ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv j (fun t : ℝ => bsplineMult (ceCs * κ / m) m t * f t) τ‖ ≤ C * C_f * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := by
  let μ : ℝ → ℂ := bsplineMult (ceCs * κ / m) m; have hμ_cd : ContDiff ℝ (⊤ : ℕ∞) μ := bsplineMult_contDiff (ceCs * κ / m) m
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega); obtain ⟨Cμ, hCμ, hμ_bd⟩ := bsplineMult_iteratedDeriv_bound (div_pos (mul_pos ceCs_pos hκ) hm_pos) m
  refine ⟨4 * Cμ + 1, by positivity, fun {ε C_f} hε hCf {f} hf_cd hf_bd j hj τ => ?_⟩; have hm_real : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hdec : ∀ k ≤ 2, ∀ t : ℝ, ‖iteratedDeriv k μ t‖ ≤ Cμ * (1 + t ^ 2) ^ (-(5 / 4 : ℝ)) := fun k hk t => by
    have hr1 : (1 + t ^ 2) ^ (5 / 4 : ℝ) ≤ (1 + |t|) ^ (m : ℝ) :=
      calc (1 + t ^ 2) ^ (5 / 4 : ℝ) ≤ ((1 + |t|) ^ 2) ^ (5 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg t, sq_abs t]) (by positivity)
        _ = (1 + |t|) ^ (5 / 2 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ (1 + |t|) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
    exact (hμ_bd k hk t).trans (mul_le_mul_of_nonneg_left (by rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]; exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hr1) hCμ.le)
  have hterm : ∀ {a b : ℕ}, a ≤ 2 → b ≤ 2 → ‖iteratedDeriv a μ τ * iteratedDeriv b f τ‖ ≤ Cμ * C_f * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := fun {a b} ha hb => by
    have hpow : (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) = (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add (by positivity)]; norm_num
    rw [norm_mul]; calc ‖iteratedDeriv a μ τ‖ * ‖iteratedDeriv b f τ‖ ≤ (Cμ * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) * (C_f * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) := mul_le_mul (hdec a ha τ) (hf_bd b hb τ) (norm_nonneg _) (by positivity)
      _ = Cμ * C_f * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := by rw [← hpow]; ring
  have hd1 : deriv (fun t : ℝ => μ t * f t) = fun t : ℝ => iteratedDeriv 1 μ t * f t + μ t * iteratedDeriv 1 f t :=
    funext fun t => by rw [iteratedDeriv_one, iteratedDeriv_one]; exact (((hμ_cd.differentiable (by simp)).differentiableAt).hasDerivAt.mul ((hf_cd.differentiable (by simp)).differentiableAt).hasDerivAt).deriv
  have hd2 : deriv (deriv (fun t : ℝ => μ t * f t)) τ = iteratedDeriv 2 μ τ * f τ + 2 * (iteratedDeriv 1 μ τ * iteratedDeriv 1 f τ) + μ τ * iteratedDeriv 2 f τ := by
    rw [hd1]
    have ha := ((((hμ_cd.differentiable_iteratedDeriv 1 (by simp)).differentiableAt (x := τ)).hasDerivAt.mul ((hf_cd.differentiable (by simp)).differentiableAt (x := τ)).hasDerivAt).add
      (((hμ_cd.differentiable (by simp)).differentiableAt (x := τ)).hasDerivAt.mul ((hf_cd.differentiable_iteratedDeriv 1 (by norm_num)).differentiableAt (x := τ)).hasDerivAt)).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
    have hsum := ha.deriv; change deriv (fun t : ℝ => iteratedDeriv 1 μ t * f t + μ t * iteratedDeriv 1 f t) τ = _ at hsum
    rw [← iteratedDeriv_succ (n := 1) (f := μ), ← iteratedDeriv_succ (n := 1) (f := f), ← iteratedDeriv_one (f := μ), ← iteratedDeriv_one (f := f)] at hsum; rw [hsum]; ring
  have hnonneg : 0 ≤ Cμ * C_f * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := by positivity
  interval_cases j
  · simpa only [iteratedDeriv_zero] using (hterm (a := 0) (b := 0) (by decide) (by decide)).trans (by nlinarith)
  · rw [iteratedDeriv_one, hd1]; have ht1 := hterm (a := 1) (b := 0) (by decide) (by decide); have ht2 := hterm (a := 0) (b := 1) (by decide) (by decide)
    simp only [iteratedDeriv_zero] at ht1 ht2; have hadd := norm_add_le (iteratedDeriv 1 μ τ * f τ) (μ τ * iteratedDeriv 1 f τ); nlinarith
  · rw [iteratedDeriv_succ, iteratedDeriv_one, hd2]
    have ht20 := hterm (a := 2) (b := 0) (by decide) (by decide); have ht11 := hterm (a := 1) (b := 1) (by decide) (by decide); have ht02 := hterm (a := 0) (b := 2) (by decide) (by decide); simp only [iteratedDeriv_zero] at ht20 ht02
    have htri := (norm_add_le (iteratedDeriv 2 μ τ * f τ + 2 * (iteratedDeriv 1 μ τ * iteratedDeriv 1 f τ)) (μ τ * iteratedDeriv 2 f τ)).trans (add_le_add (norm_add_le _ _) le_rfl)
    rw [norm_mul (2 : ℂ), show ‖(2 : ℂ)‖ = 2 by norm_num] at htri; nlinarith

/-- Packaged input data for `GT.2b(2)` reflected combination `θ 𝒮_h + γ ε S₀`. -/
structure GT2bReflectedData where
  w : ℕ → ℝ
  hw_nn : ∀ n, 0 ≤ w n
  hw_sum : Summable w
  A : ℝ
  hA : 0 ≤ A
  hdiag : ∀ t ≥ 0, ∑' n : ℕ, w n * dirichletPhi n t ^ 2 ≤ A ^ 2 * (min t 1) ^ 2
  S₀ : ℝ → ℝ → ℂ
  C₀ : ℝ
  hC₀ : 0 ≤ C₀
  hS₀_cd : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ContDiff ℝ 2 (S₀ ε)
  hS₀_bd : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ j ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv j (S₀ ε) τ‖ ≤ C₀ * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))
  θ : ℝ
  γ : ℝ

/-- **Lemma `GT.2b(2)` (`(cegt:eqGT2b)`):** combined bound on `bsplineMult * (θ 𝒮_h + γ ε S₀)` for `0 < ε ≤ 1`, `m ≥ 3`, `κ > 0`. -/
theorem gt2b_reflected_combined {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 3 ≤ m) :
    ∃ C > 0, ∀ (d : GT2bReflectedData) {ε : ℝ} (_hε : 0 < ε) (_hε1 : ε ≤ 1) (j : ℕ) (_hj : j ≤ 2) (τ : ℝ),
      ‖iteratedDeriv j (fun t : ℝ => bsplineMult (ceCs * κ / m) m t *
        ((d.θ : ℂ) * airyTwistedLaplaceC (diagAirySource d.w) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ))) + (d.γ : ℂ) * (ε : ℂ) * d.S₀ ε t)) τ‖ ≤
        C * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀) * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨C₁, hC₁, hdiag_bd⟩ := diagAirySource_dual_deriv_bound; obtain ⟨C₂, hC₂, hmul_bd⟩ := bsplineMult_mul_dual_bound hκ hm
  let C_diag : ℝ := max 1 (max (C₁ 0) (max (C₁ 1) (C₁ 2)))
  refine ⟨C₂ * C_diag, mul_pos hC₂ (lt_of_lt_of_le one_pos (le_max_left _ _)), fun d {ε} hε hε1 j hj τ => ?_⟩
  let g₁ : ℝ → ℂ := fun t => airyTwistedLaplaceC (diagAirySource d.w) (((ceCs * ε⁻¹ : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))
  let f : ℝ → ℂ := fun t => (d.θ : ℂ) * g₁ t + (d.γ : ℂ) * (ε : ℂ) * d.S₀ ε t
  have hg₁_cd : ContDiff ℝ (⊤ : ℕ∞) g₁ := (airyTwisted_line_analytic (diagAirySource_differentiableOn d.hw_nn d.hw_sum) hε).2.2.2
  have hf_cd : ContDiff ℝ 2 f := (contDiff_const.mul (hg₁_cd.of_le (by simp))).add (contDiff_const.mul (d.hS₀_cd hε hε1))
  have hdiag1 : ∀ t ≥ 0, ∑' n : ℕ, d.w n * dirichletPhi n t ^ 2 ≤ d.A ^ 2 * (min t 1) ^ (2 * 1) := by simpa using d.hdiag
  have hf_bd : ∀ k ≤ 2, ∀ t : ℝ, ‖iteratedDeriv k f t‖ ≤ (C_diag * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀)) * ε ^ (7 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := fun k hk t => by
    have hg₁_k : ContDiffAt ℝ k (fun s => (d.θ : ℂ) * g₁ s) t := ((contDiff_const.mul hg₁_cd).contDiffAt (x := t)).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
    have hS₀_k : ContDiffAt ℝ k (fun s => (d.γ : ℂ) * (ε : ℂ) * d.S₀ ε s) t := (contDiff_const.mul (d.hS₀_cd hε hε1)).contDiffAt.of_le (by exact_mod_cast hk)
    have hadd : iteratedDeriv k f t = (d.θ : ℂ) * iteratedDeriv k g₁ t + (d.γ : ℂ) * (ε : ℂ) * iteratedDeriv k (d.S₀ ε) t := by
      dsimp [f]; rw [iteratedDeriv_fun_add hg₁_k hS₀_k, iteratedDeriv_const_mul_field (d.θ : ℂ) g₁, show (fun s => (d.γ : ℂ) * (ε : ℂ) * d.S₀ ε s) = fun s => ((d.γ : ℂ) * (ε : ℂ)) * d.S₀ ε s from funext fun s => by ring, iteratedDeriv_const_mul_field ((d.γ : ℂ) * (ε : ℂ)) (d.S₀ ε)]
    have hb1 : ‖iteratedDeriv k g₁ t‖ ≤ C_diag * d.A ^ 2 * ε ^ (7 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
      have hk_bd := hdiag_bd d.hw_nn d.hw_sum d.hA (Or.inr rfl) hdiag1 k hε t
      have hC_le : C₁ k ≤ C_diag := by
        dsimp [C_diag]; interval_cases k
        · exact le_trans (le_max_left _ _) (le_max_right _ _)
        · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
        · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
      have hε_le : ε ^ (5 / 2 + 2 * ((1 : ℕ) : ℝ)) ≤ ε ^ (7 / 2 : ℝ) := by rw [Nat.cast_one, show (5 / 2 + 2 * (1 : ℝ)) = 1 + (7 / 2 : ℝ) by norm_num, Real.rpow_add hε, Real.rpow_one]; exact mul_le_of_le_one_left (Real.rpow_nonneg hε.le _) hε1
      calc ‖iteratedDeriv k g₁ t‖ ≤ C₁ k * d.A ^ 2 * ε ^ (5 / 2 + 2 * ((1 : ℕ) : ℝ)) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := hk_bd
        _ ≤ C_diag * d.A ^ 2 * ε ^ (7 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by gcongr
    have hb2 : ε * ‖iteratedDeriv k (d.S₀ ε) t‖ ≤ C_diag * d.C₀ * ε ^ (7 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by
      have hS := d.hS₀_bd hε hε1 k hk t; have hC_ge : 1 ≤ C_diag := le_max_left _ _
      have hτ_le : (1 + t ^ 2) ^ (-(5 / 4 : ℝ)) ≤ (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith [sq_nonneg t]) (by norm_num)
      have hε_mul : ε * ε ^ (5 / 2 : ℝ) = ε ^ (7 / 2 : ℝ) := by calc ε * ε ^ (5 / 2 : ℝ) = ε ^ (1 : ℝ) * ε ^ (5 / 2 : ℝ) := by rw [Real.rpow_one]
        _ = ε ^ (7 / 2 : ℝ) := by rw [← Real.rpow_add hε]; norm_num
      have hCd_nn : 0 ≤ C_diag * d.C₀ * ε ^ (7 / 2 : ℝ) := mul_nonneg (mul_nonneg (by linarith) d.hC₀) (Real.rpow_nonneg hε.le _)
      calc ε * ‖iteratedDeriv k (d.S₀ ε) t‖ ≤ ε * (d.C₀ * ε ^ (5 / 2 : ℝ) * (1 + t ^ 2) ^ (-(5 / 4 : ℝ))) := by gcongr
        _ = 1 * d.C₀ * (ε * ε ^ (5 / 2 : ℝ)) * (1 + t ^ 2) ^ (-(5 / 4 : ℝ)) := by ring
        _ ≤ C_diag * d.C₀ * ε ^ (7 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by rw [hε_mul]; gcongr; exact d.hC₀
    rw [hadd]; calc ‖(d.θ : ℂ) * iteratedDeriv k g₁ t + (d.γ : ℂ) * (ε : ℂ) * iteratedDeriv k (d.S₀ ε) t‖
        ≤ ‖(d.θ : ℂ) * iteratedDeriv k g₁ t‖ + ‖(d.γ : ℂ) * (ε : ℂ) * iteratedDeriv k (d.S₀ ε) t‖ := norm_add_le _ _
      _ = |d.θ| * ‖iteratedDeriv k g₁ t‖ + |d.γ| * (ε * ‖iteratedDeriv k (d.S₀ ε) t‖) := by rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε]; ring
      _ ≤ |d.θ| * (C_diag * d.A ^ 2 * ε ^ (7 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) + |d.γ| * (C_diag * d.C₀ * ε ^ (7 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ))) := by gcongr
      _ = (C_diag * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀)) * ε ^ (7 / 2 : ℝ) * (1 + t ^ 2) ^ (-(1 / 4 : ℝ)) := by ring
  have hCf_nn : 0 ≤ C_diag * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀) := mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (add_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (mul_nonneg (abs_nonneg _) d.hC₀))
  calc ‖iteratedDeriv j (fun t : ℝ => bsplineMult (ceCs * κ / m) m t * f t) τ‖ ≤ C₂ * (C_diag * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀)) * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := hmul_bd hε hCf_nn hf_cd hf_bd j hj τ
    _ = C₂ * C_diag * (|d.θ| * d.A ^ 2 + |d.γ| * d.C₀) * ε ^ (7 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(3 / 2 : ℝ)) := by ring

/-- Explicit non-vacuity witness for `GT2bReflectedData` using `w = δ₀` and `S₀(ε, τ) = ε^{5/2} (1 - i τ)^{-5/2}`. -/
theorem gt2bReflected_nonvacuous : Nonempty GT2bReflectedData := by
  have hAi'_c : Continuous fun x : ℝ => |airyAi' (x + airyZero 1)| := continuous_abs.comp ((continuous_iff_continuousAt.mpr fun x => (hasDerivAt_airyAi' x).continuousAt).comp (continuous_id.add continuous_const))
  obtain ⟨M', hM'_ub⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image hAi'_c.continuousOn
  let M'₀ : ℝ := max M' 0; let Cφ : ℝ := M'₀ * |airyAi' (airyZero 1)|⁻¹; let A : ℝ := max Cφ (18 * π); have hA : 0 ≤ A := le_trans (by positivity) (le_max_right _ _)
  have hdiag : ∀ t ≥ 0, ∑' n : ℕ, (if n = 0 then (1 : ℝ) else 0) * dirichletPhi n t ^ 2 ≤ A ^ 2 * (min t 1) ^ 2 := fun t ht => by
    rw [tsum_eq_single 0 (fun n hn => by simp [hn]), show (if (0 : ℕ) = 0 then (1 : ℝ) else 0) * dirichletPhi 0 t ^ 2 = |dirichletPhi 0 t| ^ 2 by simp [sq_abs]]
    have hphi : |dirichletPhi 0 t| ≤ A * min t 1 := by
      rcases le_or_gt t 1 with ht1 | ht1
      · rw [min_eq_left ht1]; rcases eq_or_lt_of_le ht with rfl | ht0; · simp [dirichletPhi, airyAi_airyZero]
        · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => airyAi (s + airyZero 1)) (fun s => airyAi' (s + airyZero 1)) ht0
            (differentiable_airyAi.continuous.comp (continuous_id.add continuous_const)).continuousOn (fun x _ => by have h := (hasDerivAt_airyAi (x + airyZero 1)).comp x ((hasDerivAt_id' x).add_const (airyZero 1)); simpa [Function.comp_def] using h)
          have hzero : airyAi (0 + airyZero 1) = 0 := by rw [zero_add]; exact airyAi_airyZero 1
          rw [hzero, sub_zero, sub_zero, eq_div_iff ht0.ne'] at hslope
          have hc_bd : |airyAi' (c + airyZero 1)| ≤ M'₀ := le_trans (hM'_ub ⟨c, ⟨hc.1.le, hc.2.le.trans ht1⟩, rfl⟩) (le_max_left _ _)
          have hnum : |airyAi (t + airyZero 1)| ≤ M'₀ * t := by rw [← hslope, abs_mul, abs_of_pos ht0]; exact mul_le_mul_of_nonneg_right hc_bd ht0.le
          have hd_le : |dirichletPhi 0 t| ≤ Cφ * t := by unfold dirichletPhi; rw [abs_div, div_eq_mul_inv]; calc |airyAi (t + airyZero 1)| * |airyAi' (airyZero 1)|⁻¹ ≤ (M'₀ * t) * |airyAi' (airyZero 1)|⁻¹ := by gcongr
            _ = Cφ * t := by dsimp [Cφ]; ring
          exact hd_le.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)
      · rw [min_eq_right ht1.le, mul_one]; exact (dirichletPhi_abs_le 0 t).trans (le_max_right _ _)
    calc |dirichletPhi 0 t| ^ 2 ≤ (A * min t 1) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hphi 2
      _ = A ^ 2 * (min t 1) ^ 2 := by ring
  let U : Set ℂ := {ω : ℂ | |ω.im| < 3 / 4}; have hU : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const; let F : ℂ → ℂ := fun ω => (1 - Complex.I * ω) ^ (-(5 / 2 : ℂ))
  have hF_diff : DifferentiableOn ℂ F U := fun ω hω => by
    change |ω.im| < 3 / 4 at hω; have hre : 0 < (1 - Complex.I * ω).re := by simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub]; linarith [(abs_lt.mp hω).1]
    exact (((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.const_mul Complex.I)).cpow (differentiableAt_const (-(5 / 2 : ℂ))) (Or.inl hre)).differentiableWithinAt
  have hball : ∀ τ : ℝ, Metric.closedBall (τ : ℂ) (1 / 2) ⊆ U := fun τ ω hω => by
    change |ω.im| < 3 / 4; simpa [Complex.sub_im, Complex.ofReal_im, sub_zero] using ((Complex.abs_im_le_norm (ω - (τ : ℂ))).trans (by simpa [Complex.dist_eq] using Metric.mem_closedBall.mp hω)).trans_lt (by norm_num)
  have hsphere : ∀ (τ : ℝ) (ω : ℂ), ω ∈ Metric.sphere (τ : ℂ) (1 / 2) → ‖F ω‖ ≤ 8 * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := fun τ ω hω => by
    have hdist : ‖ω - (τ : ℂ)‖ = 1 / 2 := by simpa [Complex.dist_eq] using Metric.mem_sphere.mp hω
    dsimp [F]; rw [show (-(5 / 2 : ℂ)) = ((-(5 / 2 : ℝ) : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real]
    have h2 : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ 8 := (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (5 / 2 : ℝ) ≤ 3)).trans_eq (by norm_num)
    calc ‖1 - Complex.I * ω‖ ^ (-(5 / 2 : ℝ)) ≤ (Real.sqrt (1 + τ ^ 2) * 2⁻¹) ^ (-(5 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by positivity) (by simpa [div_eq_mul_inv] using (norm_one_sub_I_mul_ge hdist.le).1) (by norm_num)
      _ = (2 : ℝ) ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ 1 + τ ^ 2), show (1 / 2 : ℝ) * -(5 / 2 : ℝ) = -(5 / 4 : ℝ) by norm_num]; ring
      _ ≤ 8 * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by gcongr
  obtain ⟨hF_cd, hF_bd⟩ := holomorphic_real_contDiff_and_cauchy hU hF_diff (fun t => by simp [U]) (by norm_num : (0 : ℝ) < 1 / 2) hball hsphere
  let S₀ : ℝ → ℝ → ℂ := fun ε τ => ((ε ^ (5 / 2 : ℝ) : ℝ) : ℂ) * F (τ : ℂ)
  have hw_nn : ∀ n : ℕ, 0 ≤ (if n = 0 then (1 : ℝ) else 0) := fun n => by split_ifs <;> norm_num
  have hw_sum : Summable (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) := summable_of_ne_finset_zero (s := {0}) fun n hn => by simp [show n ≠ 0 by simpa using hn]
  have hS₀_cd : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ContDiff ℝ 2 (S₀ ε) := fun _ _ => contDiff_const.mul (hF_cd.of_le (by simp))
  have hS₀_bd : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ j ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv j (S₀ ε) τ‖ ≤ 64 * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := fun {ε} hε _ j hj τ => by
    rw [show S₀ ε = fun t : ℝ => ((ε ^ (5 / 2 : ℝ) : ℝ) : ℂ) * F (t : ℂ) from rfl, iteratedDeriv_const_mul_field ((ε ^ (5 / 2 : ℝ) : ℝ) : ℂ) (fun t : ℝ => F (t : ℂ)), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hε _)]
    have hjf : (j.factorial : ℝ) ≤ 2 := by exact_mod_cast (by interval_cases j <;> decide : j.factorial ≤ 2)
    have hrp : (1 / 2 : ℝ)⁻¹ ^ j ≤ 4 := by interval_cases j <;> norm_num
    calc ε ^ (5 / 2 : ℝ) * ‖iteratedDeriv j (fun t : ℝ => F (t : ℂ)) τ‖ ≤ ε ^ (5 / 2 : ℝ) * ((j.factorial : ℝ) * (8 * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ))) / (1 / 2 : ℝ) ^ j) := by gcongr; exact hF_bd j τ
      _ = ((j.factorial : ℝ) * (1 / 2 : ℝ)⁻¹ ^ j * 8) * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by rw [div_eq_mul_inv, inv_pow]; ring
      _ ≤ (2 * 4 * 8) * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by gcongr
      _ = 64 * ε ^ (5 / 2 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by norm_num
  exact ⟨{ w := fun n => if n = 0 then 1 else 0, hw_nn := hw_nn, hw_sum := hw_sum, A := A, hA := hA, hdiag := hdiag, S₀ := S₀, C₀ := 64, hC₀ := by norm_num, hS₀_cd := hS₀_cd, hS₀_bd := hS₀_bd, θ := 1, γ := 1 }⟩

/-! ### Axiom verification -/

/-- info: 'FormalResearch.CohnElkies.bsplineE1_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bsplineE1_eq_integral
/-- info: 'FormalResearch.CohnElkies.differentiable_bsplineE1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.differentiable_bsplineE1
/-- info: 'FormalResearch.CohnElkies.norm_iteratedDeriv_bsplineE1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.norm_iteratedDeriv_bsplineE1_le
/-- info: 'FormalResearch.CohnElkies.bsplineMult_iteratedDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bsplineMult_iteratedDeriv_bound
/-- info: 'FormalResearch.CohnElkies.bsplineImag_iteratedDeriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bsplineImag_iteratedDeriv_bound
/-- info: 'FormalResearch.CohnElkies.ceHth_mul_pi_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.ceHth_mul_pi_div_two
/-- info: 'FormalResearch.CohnElkies.hasDerivAt_edgeR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.hasDerivAt_edgeR
/-- info: 'FormalResearch.CohnElkies.edgeR_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.edgeR_contDiff
/-- info: 'FormalResearch.CohnElkies.edgeR_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.edgeR_deriv_bounds
/-- info: 'FormalResearch.CohnElkies.pf3_kernel_bound_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.pf3_kernel_bound_complex
/-- info: 'FormalResearch.CohnElkies.mainEdgeAmp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainEdgeAmp_zero
/-- info: 'FormalResearch.CohnElkies.mainEdgeAmp_contDiff_and_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainEdgeAmp_contDiff_and_bound
/-- info: 'FormalResearch.CohnElkies.mainEdgeAmp_H2_and_phase_L2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainEdgeAmp_H2_and_phase_L2
/-- info: 'FormalResearch.CohnElkies.mainEdgeKernel_L1_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainEdgeKernel_L1_bound
/-- info: 'FormalResearch.CohnElkies.mainEdgeKernel_right_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainEdgeKernel_right_decay
/-- info: 'FormalResearch.CohnElkies.mainEdge_fubini_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainEdge_fubini_kernel
/-- info: 'FormalResearch.CohnElkies.mainEdge_mellinK0_airyFtilde_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.mainEdge_mellinK0_airyFtilde_bridge
/-- info: 'FormalResearch.CohnElkies.diagAirySource_gaussian_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.diagAirySource_gaussian_transform
/-- info: 'FormalResearch.CohnElkies.diagAirySource_dual_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.diagAirySource_dual_deriv_bound
/-- info: 'FormalResearch.CohnElkies.cardinalPb_dual_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.cardinalPb_dual_deriv_bound
/-- info: 'FormalResearch.CohnElkies.bsplineMult_mul_dual_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.bsplineMult_mul_dual_bound
/-- info: 'FormalResearch.CohnElkies.gt2b_reflected_combined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.gt2b_reflected_combined
/-- info: 'FormalResearch.CohnElkies.gt2bReflected_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.gt2bReflected_nonvacuous

end FormalResearch.CohnElkies
