module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodCircle
public import FormalResearch.ModularBootstrap.FiveTerm.LowerGoodArea
public import FormalResearch.ModularBootstrap.FiveTerm.LowerDyadic
public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQScaleBridge

/-!
# `LowerFirstGood` from `LowerChart` at Spinless Virasoro (Paper II, Lemma C7 (1), `cts:rosc-uncond` (1))

Proves `lowerFirstGood_of_chart`: given `LowerChart c0 γ0 c1 phi uhat` with `0 < c1` and
`10 * c1 ≤ virasoroBVChoice`, we have `LowerFirstGood virasoroProblem c1 phi`.

Proof outline:
1. For `c` large enough, `r₀ := c1 * c^{1/3} ≥ 10` and `A := √(3/2) * virasoroBVChoice * c^{1/3}`
   satisfies `virasoroBVChoice^2 c^{2/3} ≤ A^2` and `A^2 + 1 ≤ virasoroACAt virasoroBVChoice c ^ 2`.
2. Any weakly feasible `g` with `LowerViolator phi c T` satisfies `T ∈ [Δ(0), Δ(-virasoroAThr)]`
   (lower bound from `theoremJ_unconditional`, upper bound from `LowerViolator` + `LowerChart`).
   Hence `yvInputFor_virasoroBVChoice` and `virasoro_band_sums_le` give `YVEnvBound` at `R = A^2`
   with `L' ≤ C_fb (3 c^{1/3} + 1)`.
3. Using `lowerGood_GReg_poisson_bound`, `lowerGood_inv_norm_area_le`, `lowerGood_airyEnv_ratio_le`,
   and `(lemmaQ_part3 hc hg).2.1`, the integral of `lowerEta virasoroProblem phi c g (r^2)` over
   `r ∈ [r₀, (3/2) r₀]` is `≤ C_tot * r₀`.
4. `markov_select` on `lowerGoodSet r₀` (measure `≥ r₀ / 36` by `lowerGoodSet_measure`) yields
   `r ∈ lowerGoodSet r₀` with `lowerEta ≤ 36 * C_tot`, and `lowerGood_circle_of_phase` gives
   `LowerGoodCircle N (r^2)` and `LowerRadiusRange c1 c (r^2)`.

**Added hypothesis beyond `LowerMainInputs`:**
* `hc1_small : 10 * c1 ≤ virasoroBVChoice` (strengthening `LowerMainInputs.c1_small : 4 * c1^2 < 2 * virasoroBV^2`),
  so that `‖w‖ ≤ (3/2) r₀` and its `φ_c`-image lie inside `‖z‖ ≤ A / 4` for the half-disc Poisson
  kernel bound `pArc_le` at radius `A = √(3/2) * virasoroBVChoice * c^{1/3}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Contour FormalResearch.SignUncertainty.CtHalfDiscPoisson
open FormalResearch.HalfDiscCauchy FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.PoissonJensen FormalResearch.ModularBootstrap.TipFront
open FormalResearch.ModularBootstrap.FixedWeightBand
open FormalResearch.ModularBootstrap.FixedWeightTip (psiTilde)

/-! ### 1. Diameter `L¹` bound for `lowerGoodGReg` -/

lemma lowerGood_diam_integral_le {A c : ℝ} (hc_Q : virasoroCQEnv ≤ c)
    (hA0 : 0 < A) (hA_ub : A ^ 2 ≤ virasoroAC c ^ 2) {T : ℝ} {g : ℝ → ℝ}
    (hg : virasoroProblem.IsWeaklyFeasible (c / 12) T g) :
    ∫⁻ t in Ioo (-A) A, ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ ≤ 1 := by
  have hc_pos : 0 < c := lt_of_lt_of_le (by have := virasoroCQEnv_ge; linarith) hc_Q
  have hc_10000 : 10000 ≤ c :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc_Q)
  have hL1 : ∫ u in (-(virasoroAC c ^ 2))..(virasoroAC c ^ 2),
      ‖virasoroPsiTilde c g (u : ℂ)‖ ≤ 1 := (lemmaQ_part3 hc_Q hg).2.1
  have h_pt : ∀ t ∈ Ioo (-A) A, ‖lowerGoodGReg A c g (t : ℂ)‖ ≤
      |t| * ‖virasoroPsiTilde c g (-(t ^ 2) : ℂ)‖ := by
    intro t ht
    have ht_abs : |t| ≤ A := (abs_lt.mpr ht).le
    have hpre : ‖(1 - (t : ℂ) ^ 2 / (A : ℂ) ^ 2) ^ 2‖ ≤ 1 := by
      have h1 : (1 - (t : ℂ) ^ 2 / (A : ℂ) ^ 2) = (((1 - t ^ 2 / A ^ 2 : ℝ) : ℂ)) := by
        push_cast; ring
      rw [h1, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      have ht2 : 0 ≤ t ^ 2 / A ^ 2 := by positivity
      have ht2_le : t ^ 2 / A ^ 2 ≤ 1 := by
        rw [div_le_one (pow_pos hA0 2), ← sq_abs t]
        exact pow_le_pow_left₀ (abs_nonneg _) ht_abs 2
      have habs : |1 - t ^ 2 / A ^ 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      exact pow_le_one₀ (abs_nonneg _) habs
    have hexp : ‖Complex.exp ((4 / 3 : ℂ) * I * (t : ℂ) ^ 3)‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : ((4 / 3 : ℂ) * I * (t : ℂ) ^ 3).re = 0 := by
        simp [Complex.mul_re, ← Complex.ofReal_pow]
      rw [hre, Real.exp_zero]
    unfold lowerGoodGReg
    rw [norm_mul, norm_mul, norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hneg_eq : -((t : ℂ) ^ 2) = ((-(t ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [hneg_eq]
    calc ‖(1 - (t : ℂ) ^ 2 / (A : ℂ) ^ 2) ^ 2‖ * |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖
        ≤ 1 * |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ := by gcongr
      _ = |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ := by ring
  have hcont_psi : ContinuousOn (fun u : ℝ => ‖virasoroPsiTilde c g (u : ℂ)‖)
      (Icc (-(virasoroAC c ^ 2)) (virasoroAC c ^ 2)) :=
    continuous_norm.comp_continuousOn
      ((virasoroPsiTilde_analyticOnNhd (by linarith) hg.1).continuousOn.comp
        Complex.continuous_ofReal.continuousOn fun v hv => virasoro_closedBall_subset_psiDom hc_pos (by
          rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr hv))
  have h_sub_int : ∫ u in (-A ^ 2)..0, ‖virasoroPsiTilde c g (u : ℂ)‖ ≤ 1 := by
    have h1 : ∫ u in (-A ^ 2)..0, ‖virasoroPsiTilde c g (u : ℂ)‖ ≤
        ∫ u in (-(virasoroAC c ^ 2))..(virasoroAC c ^ 2), ‖virasoroPsiTilde c g (u : ℂ)‖ := by
      refine intervalIntegral.integral_mono_interval (by linarith) (by nlinarith)
        (by positivity) (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (hcont_psi.intervalIntegrable_of_Icc (by linarith [sq_nonneg (virasoroAC c)]))
    exact h1.trans hL1
  have h_half : ∫ t in (0 : ℝ)..A, t * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ =
      (1 / 2 : ℝ) * ∫ u in (-A ^ 2)..0, ‖virasoroPsiTilde c g (u : ℂ)‖ := by
    have hderiv : ∀ t ∈ Set.uIcc 0 A, HasDerivAt (fun s : ℝ => -(s ^ 2)) (-2 * t) t := by
      intro t _
      exact ((hasDerivAt_pow 2 t).neg).congr_deriv (by ring)
    have hcont_u : ContinuousOn (fun u : ℝ => ‖virasoroPsiTilde c g (u : ℂ)‖)
        ((fun s : ℝ => -(s ^ 2)) '' Set.uIcc 0 A) := by
      refine hcont_psi.mono ?_
      rintro u ⟨t, ht, rfl⟩
      rw [Set.uIcc_of_le hA0.le] at ht
      have ht2 : t ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
      exact ⟨by linarith, by linarith [sq_nonneg (virasoroAC c), sq_nonneg t]⟩
    have hcomp := intervalIntegral.integral_comp_mul_deriv' hderiv
      ((continuous_const.mul continuous_id).continuousOn) hcont_u
    simp only [neg_zero, zero_pow two_ne_zero] at hcomp
    have hcomp' : ∫ t in (0 : ℝ)..A, ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ * (-2 * t) =
        -(∫ u in (-A ^ 2)..0, ‖virasoroPsiTilde c g (u : ℂ)‖) := by
      have hcomp0 : ∫ t in (0 : ℝ)..A, ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ * (-2 * t) =
          ∫ u in (0 : ℝ)..(-A ^ 2), ‖virasoroPsiTilde c g (u : ℂ)‖ := hcomp
      rw [hcomp0, intervalIntegral.integral_symm (-A ^ 2) 0]
    have h_eq : (fun t : ℝ => t * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖) =
        fun t => -(1 / 2 : ℝ) * (‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ * (-2 * t)) := by
      ext t; ring
    rw [h_eq, intervalIntegral.integral_const_mul, hcomp']
    ring
  have h_full : ∫ t in (-A)..A, |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ ≤ 1 := by
    have h_even : ∫ t in (-A)..0, |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ =
        ∫ t in (0 : ℝ)..A, t * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ := by
      have h1 := intervalIntegral.integral_comp_neg
        (fun t : ℝ => |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖) (a := 0) (b := A)
      simp only [neg_zero] at h1
      rw [← h1]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hA0.le] at ht
      simp [abs_neg, abs_of_nonneg ht.1]
    have h_pos_side : ∫ t in (0 : ℝ)..A, |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ =
        ∫ t in (0 : ℝ)..A, t * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ :=
      intervalIntegral.integral_congr fun t ht => by
        rw [Set.uIcc_of_le hA0.le] at ht
        rw [abs_of_nonneg ht.1]
    have hcont_f : ContinuousOn (fun t : ℝ => |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖)
        (Icc (-A) A) := by
      refine continuous_abs.continuousOn.mul (hcont_psi.comp (by fun_prop) fun t ht => ?_)
      have ht2 : t ^ 2 ≤ A ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ht) 2
      exact ⟨by linarith, by linarith [sq_nonneg (virasoroAC c), sq_nonneg t]⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hcont_f.mono (Icc_subset_Icc_right hA0.le)).intervalIntegrable_of_Icc (by linarith))
      ((hcont_f.mono (Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc hA0.le)
    rw [← hadd, h_even, h_pos_side, h_half]
    linarith
  have h_eq_coe : (fun t : ℝ => ‖virasoroPsiTilde c g (-(t : ℂ) ^ 2)‖) =
      fun t : ℝ => ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ := by
    ext t; congr 3; push_cast; ring
  have h_le_real' : ∫⁻ t in Ioo (-A) A, ENNReal.ofReal ‖lowerGoodGReg A c g (t : ℂ)‖ ≤
      ∫⁻ t in Ioo (-A) A, ENNReal.ofReal (|t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖) := by
    refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    refine (ENNReal.ofReal_le_ofReal (h_pt t ht)).trans_eq ?_
    rw [show ‖virasoroPsiTilde c g (-(t : ℂ) ^ 2)‖ = ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖ from
      congrFun h_eq_coe t]
  refine h_le_real'.trans ?_
  have hcont_f : ContinuousOn (fun t : ℝ => |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖)
      (Icc (-A) A) := by
    refine continuous_abs.continuousOn.mul (hcont_psi.comp (by fun_prop) fun t ht => ?_)
    have ht2 : t ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ht) 2
    exact ⟨by linarith, by linarith [sq_nonneg (virasoroAC c), sq_nonneg t]⟩
  have hint : IntegrableOn (fun t : ℝ => |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖) (Ioc (-A) A) :=
    (hcont_f.intervalIntegrable_of_Icc (by linarith)).1
  have h_eq_int : (∫⁻ t in Ioo (-A) A, ENNReal.ofReal (|t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖)) =
      ENNReal.ofReal (∫ t in (-A)..A, |t| * ‖virasoroPsiTilde c g ((-(t ^ 2) : ℝ) : ℂ)‖) := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint.mono_set Ioo_subset_Ioc_self)
      (ae_restrict_of_forall_mem measurableSet_Ioo fun t _ => by positivity)]
  rw [h_eq_int]
  exact ENNReal.ofReal_le_ofReal h_full |>.trans (by norm_num)

/-! ### 2. The perturbed square-root map `w̃(w) = √(-φ_c(-w²))` on the annulus -/

/-- For `ζ ∈ ball 1 (1/2)`, `‖ζ ^ (1/2 : ℂ) - 1‖ ≤ ‖ζ - 1‖`. -/
private lemma cpow_half_sub_one_le {ζ : ℂ} (hζ : ‖ζ - 1‖ ≤ 1 / 2) :
    ‖ζ ^ (1 / 2 : ℂ) - 1‖ ≤ ‖ζ - 1‖ := by
  have hre : 0 < (ζ ^ (1 / 2 : ℂ)).re := by
    have hζ_re : 1 / 2 ≤ ζ.re := by
      have := (abs_le.mp ((Complex.abs_re_le_norm (ζ - 1)).trans hζ)).1
      simp only [Complex.sub_re, Complex.one_re] at this
      linarith
    have hsp : ζ ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
    have harg : |ζ.arg| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith))
    have hne : ζ ≠ 0 := Complex.slitPlane_ne_zero hsp
    rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re]
    refine mul_pos (Real.exp_pos _) ?_
    have : (Complex.log ζ * (1 / 2 : ℂ)).im = ζ.arg / 2 := by simp [Complex.log_im]; ring
    rw [this]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_lt.mp harg], by linarith [abs_lt.mp harg]⟩
  have hadd : 1 ≤ ‖ζ ^ (1 / 2 : ℂ) + 1‖ := by
    have h1 : 1 ≤ (ζ ^ (1 / 2 : ℂ) + 1).re := by
      simp only [Complex.add_re, Complex.one_re]; linarith
    exact h1.trans (Complex.re_le_norm _)
  have hmul : (ζ ^ (1 / 2 : ℂ) - 1) * (ζ ^ (1 / 2 : ℂ) + 1) = ζ - 1 := by
    rw [show (ζ ^ (1 / 2 : ℂ) - 1) * (ζ ^ (1 / 2 : ℂ) + 1) = (ζ ^ (1 / 2 : ℂ)) ^ 2 - 1 by ring,
      cpow_half_sq]
  have hnorm : ‖ζ ^ (1 / 2 : ℂ) - 1‖ * ‖ζ ^ (1 / 2 : ℂ) + 1‖ = ‖ζ - 1‖ := by
    rw [← norm_mul, hmul]
  nlinarith [norm_nonneg (ζ ^ (1 / 2 : ℂ) - 1)]

/-- `w̃(w) := w * (φ_c(-w²) / (-w²))^{1/2}` on the annulus `r₀/2 ≤ ‖w‖ ≤ 2 r₀`. -/
noncomputable def lowerGoodWtilde (phi : ℝ → ℂ → ℂ) (c : ℝ) (w : ℂ) : ℂ :=
  w * (phi c (-(w ^ 2)) / (-(w ^ 2))) ^ (1 / 2 : ℂ)

private lemma lowerGood_wtilde_real_pos {c1 c Cφ r₀ : ℝ} {phi : ℝ → ℂ → ℂ}
    (hr₀ : 10 ≤ r₀) (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hr₀_eq : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hc_pos : 0 < c)
    (h_main : ∀ w : ℂ, r₀ / 2 ≤ ‖w‖ → ‖w‖ ≤ 2 * r₀ →
      lowerGoodWtilde phi c w ^ 2 = -(phi c (-(w ^ 2))) ∧
      ‖lowerGoodWtilde phi c w - w‖ ≤ 8 / r₀ * (Cφ * c ^ (-(1 / 3 : ℝ))) ∧
      ‖lowerGoodWtilde phi c w - w‖ ≤ r₀ / 32 ∧
      ‖lowerGoodWtilde phi c w‖ ≤ 9 / 4 * r₀ ∧
      r₀ / 4 ≤ ‖lowerGoodWtilde phi c w‖) :
    ∀ t : ℝ, r₀ / 2 ≤ t → t ≤ 2 * r₀ → (lowerGoodWtilde phi c (t : ℂ)).im = 0 ∧
      t / 2 ≤ (lowerGoodWtilde phi c (t : ℂ)).re ∧ (lowerGoodWtilde phi c (t : ℂ)).re ≤ 9 / 4 * r₀ := by
  have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
    unfold lowerRmax
    rw [hr₀_eq, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    norm_num; ring
  intro t ht1 ht2
  have hnorm_t : ‖(t : ℂ)‖ = t := by simp [abs_of_pos (by linarith : 0 < t)]
  have hm := h_main (t : ℂ) (by rw [hnorm_t]; exact ht1) (by rw [hnorm_t]; exact ht2)
  have him_t : (lowerGoodWtilde phi c (t : ℂ)).im = 0 := by
    have hu_eq : -((t : ℂ) ^ 2) = ((-(t ^ 2) : ℝ) : ℂ) := by push_cast; ring
    have hu_abs : |-(t ^ 2)| ≤ lowerRmax c1 c := by
      rw [abs_neg, abs_of_nonneg (sq_nonneg t), hRmax_eq]; nlinarith
    have hphi_im : (phi c ((-(t ^ 2) : ℝ) : ℂ)).im = 0 := him (-(t ^ 2)) hu_abs
    have hphi_re : (phi c ((-(t ^ 2) : ℝ) : ℂ)).re ≤ -(t ^ 2) / 2 := by
      have h1 := (hcl (-(t : ℂ) ^ 2) (by rw [norm_neg, norm_pow, hnorm_t, hRmax_eq]; nlinarith)).1
      have h2 := (abs_le.mp ((Complex.abs_re_le_norm _).trans h1)).2
      rw [hu_eq] at h2
      simp only [Complex.sub_re, Complex.ofReal_re] at h2
      nlinarith
    have hphi_c : phi c ((-(t ^ 2) : ℝ) : ℂ) = (((phi c ((-(t ^ 2) : ℝ) : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl hphi_im
    have hratio_eq : phi c (-((t : ℂ) ^ 2)) / (-((t : ℂ) ^ 2)) =
        (((phi c ((-(t ^ 2) : ℝ) : ℂ)).re / -(t ^ 2) : ℝ) : ℂ) := by
      rw [hu_eq, hphi_c]
      exact (Complex.ofReal_div ((phi c ((-(t ^ 2) : ℝ) : ℂ)).re) (-(t ^ 2))).symm
    have hratio_pos : 0 ≤ (phi c ((-(t ^ 2) : ℝ) : ℂ)).re / -(t ^ 2) :=
      div_nonneg_of_nonpos (hphi_re.trans (by nlinarith)) (neg_nonpos.mpr (sq_nonneg t))
    dsimp only [lowerGoodWtilde]
    rw [hratio_eq, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hratio_pos]
    simp [Complex.mul_im]
  have hre_bd := abs_le.mp ((Complex.abs_re_le_norm _).trans hm.2.2.1)
  simp only [Complex.sub_re, Complex.ofReal_re] at hre_bd
  exact ⟨him_t, by linarith only [hre_bd.1, ht1, hr₀], by linarith only [hre_bd.2, ht2, hr₀]⟩

private lemma lowerGood_wtilde_real_neg {c1 c Cφ r₀ : ℝ} {phi : ℝ → ℂ → ℂ}
    (hr₀ : 10 ≤ r₀) (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hr₀_eq : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hc_pos : 0 < c)
    (h_main : ∀ w : ℂ, r₀ / 2 ≤ ‖w‖ → ‖w‖ ≤ 2 * r₀ →
      lowerGoodWtilde phi c w ^ 2 = -(phi c (-(w ^ 2))) ∧
      ‖lowerGoodWtilde phi c w - w‖ ≤ 8 / r₀ * (Cφ * c ^ (-(1 / 3 : ℝ))) ∧
      ‖lowerGoodWtilde phi c w - w‖ ≤ r₀ / 32 ∧
      ‖lowerGoodWtilde phi c w‖ ≤ 9 / 4 * r₀ ∧
      r₀ / 4 ≤ ‖lowerGoodWtilde phi c w‖) :
    ∀ t : ℝ, -(2 * r₀) ≤ t → t ≤ -(r₀ / 2) → (lowerGoodWtilde phi c (t : ℂ)).im = 0 ∧
      -(9 / 4 * r₀) ≤ (lowerGoodWtilde phi c (t : ℂ)).re ∧ (lowerGoodWtilde phi c (t : ℂ)).re ≤ t / 2 := by
  have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
    unfold lowerRmax
    rw [hr₀_eq, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    norm_num; ring
  intro t ht1 ht2
  have hnorm_t : ‖(t : ℂ)‖ = -t := by simp [abs_of_neg (by linarith : t < 0)]
  have hm := h_main (t : ℂ) (by rw [hnorm_t]; linarith) (by rw [hnorm_t]; linarith)
  have him_t : (lowerGoodWtilde phi c (t : ℂ)).im = 0 := by
    have hu_eq : -((t : ℂ) ^ 2) = ((-(t ^ 2) : ℝ) : ℂ) := by push_cast; ring
    have hu_abs : |-(t ^ 2)| ≤ lowerRmax c1 c := by
      rw [abs_neg, abs_of_nonneg (sq_nonneg t), hRmax_eq]; nlinarith
    have hphi_im : (phi c ((-(t ^ 2) : ℝ) : ℂ)).im = 0 := him (-(t ^ 2)) hu_abs
    have hphi_re : (phi c ((-(t ^ 2) : ℝ) : ℂ)).re ≤ -(t ^ 2) / 2 := by
      have h1 := (hcl (-(t : ℂ) ^ 2) (by rw [norm_neg, norm_pow, hnorm_t, hRmax_eq]; nlinarith)).1
      have h2 := (abs_le.mp ((Complex.abs_re_le_norm _).trans h1)).2
      rw [hu_eq] at h2
      simp only [Complex.sub_re, Complex.ofReal_re] at h2
      nlinarith
    have hphi_c : phi c ((-(t ^ 2) : ℝ) : ℂ) = (((phi c ((-(t ^ 2) : ℝ) : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext rfl hphi_im
    have hratio_eq : phi c (-((t : ℂ) ^ 2)) / (-((t : ℂ) ^ 2)) =
        (((phi c ((-(t ^ 2) : ℝ) : ℂ)).re / -(t ^ 2) : ℝ) : ℂ) := by
      rw [hu_eq, hphi_c]
      exact (Complex.ofReal_div ((phi c ((-(t ^ 2) : ℝ) : ℂ)).re) (-(t ^ 2))).symm
    have hratio_pos : 0 ≤ (phi c ((-(t ^ 2) : ℝ) : ℂ)).re / -(t ^ 2) :=
      div_nonneg_of_nonpos (hphi_re.trans (by nlinarith)) (neg_nonpos.mpr (sq_nonneg t))
    dsimp only [lowerGoodWtilde]
    rw [hratio_eq, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hratio_pos]
    simp [Complex.mul_im]
  have hre_bd := abs_le.mp ((Complex.abs_re_le_norm _).trans hm.2.2.1)
  simp only [Complex.sub_re, Complex.ofReal_re] at hre_bd
  exact ⟨him_t, by linarith only [hre_bd.1, ht1, hr₀], by linarith only [hre_bd.2, ht2, hr₀]⟩

private lemma lowerGood_wtilde_im_sign {c1 c Cφ r₀ : ℝ} {phi : ℝ → ℂ → ℂ}
    (hr₀ : 10 ≤ r₀) (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hr₀_eq : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hc_pos : 0 < c) :
    ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      (0 < u.im → 0 < (phi c u).im) ∧ (u.im < 0 → (phi c u).im < 0) := by
  obtain ⟨ρ, hρ_gt, hdiff⟩ := hρ
  have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
    unfold lowerRmax
    rw [hr₀_eq, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    norm_num; ring
  intro u hu
  let γ : ℝ → ℂ := fun s => (u.re : ℂ) + (s * u.im : ℝ) * I
  have h_ball : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ ball (0 : ℂ) ρ := by
    intro s hs
    rw [mem_ball_zero_iff]
    have hsq : ‖γ s‖ ^ 2 ≤ lowerRmax c1 c ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      have h1 : Complex.normSq (γ s) = u.re ^ 2 + (s * u.im) ^ 2 := by
        simp [γ, Complex.normSq_apply, pow_two]
      have h2 : (s * u.im) ^ 2 ≤ u.im ^ 2 := by
        have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
        nlinarith [sq_nonneg u.im]
      have h3 : u.re ^ 2 + u.im ^ 2 ≤ lowerRmax c1 c ^ 2 := by
        rw [pow_two u.re, pow_two u.im, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) hu 2
      linarith
    have hnorm : ‖γ s‖ ≤ lowerRmax c1 c := by
      have hRmax0 : 0 ≤ lowerRmax c1 c := by rw [hRmax_eq]; positivity
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hRmax0 two_ne_zero).mp hsq
    exact hnorm.trans_lt hρ_gt
  have h_deriv : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (phi c (γ t)).im) (u.im * (deriv (phi c) (γ s)).re) s := by
    intro s hs
    have hγ_d : HasDerivAt γ ((u.im : ℝ) * I) s := by
      have h1 : γ = fun t : ℝ => (u.re : ℂ) + (t : ℂ) * ((u.im : ℂ) * I) := by
        ext t; apply Complex.ext <;> simp [γ]
      rw [h1]
      simpa using ((Complex.ofRealCLM.hasDerivAt).mul_const ((u.im : ℂ) * I)).const_add (u.re : ℂ)
    have hφ_d : HasDerivAt (phi c) (deriv (phi c) (γ s)) (γ s) :=
      (hdiff.differentiableAt (isOpen_ball.mem_nhds (h_ball s hs))).hasDerivAt
    have hcomp := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s (hφ_d.comp s hγ_d)
    refine hcomp.congr_deriv ?_
    simp [Complex.mul_im]; ring
  have h_re_lb : ∀ s ∈ Icc (0 : ℝ) 1, 3 / 4 ≤ (deriv (phi c) (γ s)).re := by
    intro s hs
    have hnorm_s : ‖γ s‖ ≤ lowerRmax c1 c := by
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by rw [hRmax_eq]; positivity) two_ne_zero,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have h1 : Complex.normSq (γ s) = u.re ^ 2 + (s * u.im) ^ 2 := by
        simp [γ, Complex.normSq_apply, pow_two]
      have h2 : (s * u.im) ^ 2 ≤ u.im ^ 2 := by
        have hs2 : s ^ 2 ≤ 1 := pow_le_one₀ hs.1 hs.2
        nlinarith [sq_nonneg u.im]
      have h3 : u.re ^ 2 + u.im ^ 2 ≤ lowerRmax c1 c ^ 2 := by
        rw [pow_two u.re, pow_two u.im, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) hu 2
      rw [Complex.normSq_eq_norm_sq] at h1
      linarith
    have hder := (hcl (γ s) hnorm_s).2
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hder)).1
    simp only [Complex.sub_re, Complex.one_re] at h1
    linarith
  have hcont_d : ContinuousOn (fun s : ℝ => u.im * (deriv (phi c) (γ s)).re) (Icc 0 1) := by
    refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn ?_)
    have hdiff_on : DifferentiableOn ℂ (deriv (phi c)) (ball 0 ρ) :=
      (hdiff.analyticOnNhd isOpen_ball).deriv.differentiableOn
    exact hdiff_on.continuousOn.comp (by fun_prop : Continuous γ).continuousOn fun s hs => h_ball s hs
  have hev := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => by rw [Set.uIcc_of_le zero_le_one] at hs; exact h_deriv s hs)
    (hcont_d.intervalIntegrable_of_Icc zero_le_one)
  have h0 : (phi c (γ 0)).im = 0 := by
    have : γ 0 = (u.re : ℂ) := by simp [γ]
    rw [this]
    exact him u.re ((Complex.abs_re_le_norm u).trans hu)
  have h1 : γ 1 = u := by
    apply Complex.ext <;> simp [γ]
  rw [h0, h1, sub_zero] at hev
  rw [← hev]
  constructor
  · intro hu_pos
    have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 3 / 4 * u.im ≤ u.im * (deriv (phi c) (γ s)).re := fun s hs => by
      have := h_re_lb s hs
      nlinarith
    have hint_lb : 3 / 4 * u.im ≤ ∫ s in (0 : ℝ)..1, u.im * (deriv (phi c) (γ s)).re := by
      calc 3 / 4 * u.im = ∫ _ in (0 : ℝ)..1, 3 / 4 * u.im := by simp
        _ ≤ ∫ s in (0 : ℝ)..1, u.im * (deriv (phi c) (γ s)).re :=
          intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
            (hcont_d.intervalIntegrable_of_Icc zero_le_one) hpos
    linarith
  · intro hu_neg
    have hneg : ∀ s ∈ Icc (0 : ℝ) 1, u.im * (deriv (phi c) (γ s)).re ≤ 3 / 4 * u.im := fun s hs => by
      have := h_re_lb s hs
      nlinarith
    have hint_ub : ∫ s in (0 : ℝ)..1, u.im * (deriv (phi c) (γ s)).re ≤ 3 / 4 * u.im := by
      calc ∫ s in (0 : ℝ)..1, u.im * (deriv (phi c) (γ s)).re
          ≤ ∫ _ in (0 : ℝ)..1, 3 / 4 * u.im :=
            intervalIntegral.integral_mono_on zero_le_one
              (hcont_d.intervalIntegrable_of_Icc zero_le_one) intervalIntegrable_const hneg
        _ = 3 / 4 * u.im := by simp
    linarith

lemma lowerGood_wtilde_props {c1 c Cφ r₀ : ℝ} {phi : ℝ → ℂ → ℂ}
    (hr₀ : 10 ≤ r₀) (_hCφ : 0 ≤ Cφ)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hr₀_eq : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hc_pos : 0 < c) :
    (∀ w : ℂ, r₀ / 2 ≤ ‖w‖ → ‖w‖ ≤ 2 * r₀ →
      lowerGoodWtilde phi c w ^ 2 = -(phi c (-(w ^ 2))) ∧
      ‖lowerGoodWtilde phi c w - w‖ ≤ 8 / r₀ * (Cφ * c ^ (-(1 / 3 : ℝ))) ∧
      ‖lowerGoodWtilde phi c w - w‖ ≤ r₀ / 32 ∧
      ‖lowerGoodWtilde phi c w‖ ≤ 9 / 4 * r₀ ∧
      r₀ / 4 ≤ ‖lowerGoodWtilde phi c w‖) ∧
    (∀ w : ℂ, r₀ ≤ ‖w‖ → ‖w‖ ≤ 3 / 2 * r₀ → 0 < w.im →
      0 < (lowerGoodWtilde phi c w).im) ∧
    (∀ t : ℝ, r₀ / 2 ≤ t → t ≤ 2 * r₀ → (lowerGoodWtilde phi c (t : ℂ)).im = 0 ∧
      t / 2 ≤ (lowerGoodWtilde phi c (t : ℂ)).re ∧ (lowerGoodWtilde phi c (t : ℂ)).re ≤ 9 / 4 * r₀) ∧
    (∀ t : ℝ, -(2 * r₀) ≤ t → t ≤ -(r₀ / 2) → (lowerGoodWtilde phi c (t : ℂ)).im = 0 ∧
      -(9 / 4 * r₀) ≤ (lowerGoodWtilde phi c (t : ℂ)).re ∧ (lowerGoodWtilde phi c (t : ℂ)).re ≤ t / 2) ∧
    (∀ w : ℂ, r₀ ≤ ‖w‖ → ‖w‖ ≤ 3 / 2 * r₀ → ∀ t : ℝ, r₀ / 2 ≤ t → t ≤ 2 * r₀ →
      0 ≤ w.re → 1 / 2 * ‖w - (t : ℂ)‖ ≤ ‖lowerGoodWtilde phi c w - lowerGoodWtilde phi c (t : ℂ)‖) ∧
    (∀ w : ℂ, r₀ ≤ ‖w‖ → ‖w‖ ≤ 3 / 2 * r₀ → ∀ t : ℝ, -(2 * r₀) ≤ t → t ≤ -(r₀ / 2) →
      w.re ≤ 0 → 1 / 2 * ‖w - (t : ℂ)‖ ≤ ‖lowerGoodWtilde phi c w - lowerGoodWtilde phi c (t : ℂ)‖) := by
  have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
    unfold lowerRmax
    rw [hr₀_eq, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    norm_num; ring
  have hr₀_pos : 0 < r₀ := by linarith
  obtain ⟨ρ, hρ_gt, hdiff⟩ := hρ
  have h_main : ∀ w : ℂ, r₀ / 2 ≤ ‖w‖ → ‖w‖ ≤ 2 * r₀ →
      lowerGoodWtilde phi c w ^ 2 = -(phi c (-(w ^ 2))) ∧
      ‖lowerGoodWtilde phi c w - w‖ ≤ 8 / r₀ * (Cφ * c ^ (-(1 / 3 : ℝ))) ∧
      ‖lowerGoodWtilde phi c w - w‖ ≤ r₀ / 32 ∧
      ‖lowerGoodWtilde phi c w‖ ≤ 9 / 4 * r₀ ∧
      r₀ / 4 ≤ ‖lowerGoodWtilde phi c w‖ := by
    intro w hw1 hw2
    have hu_norm : ‖-(w ^ 2)‖ ≤ lowerRmax c1 c := by
      rw [hRmax_eq, norm_neg, norm_pow]; nlinarith
    have hu_lb : r₀ ^ 2 / 4 ≤ ‖-(w ^ 2)‖ := by
      rw [norm_neg, norm_pow]; nlinarith
    have h_diff := (hcl (-(w ^ 2)) hu_norm).1
    have h_ratio : ‖phi c (-(w ^ 2)) / (-(w ^ 2)) - 1‖ ≤ 4 / r₀ ^ 2 * (Cφ * c ^ (-(1 / 3 : ℝ))) := by
      have hu_ne : -(w ^ 2) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hu_lb; nlinarith
      rw [div_sub_one hu_ne, norm_div]
      calc ‖phi c (-(w ^ 2)) - -(w ^ 2)‖ / ‖-(w ^ 2)‖
          ≤ (Cφ * c ^ (-(1 / 3 : ℝ))) / (r₀ ^ 2 / 4) :=
            div_le_div₀ (by positivity) h_diff (by positivity) hu_lb
        _ = 4 / r₀ ^ 2 * (Cφ * c ^ (-(1 / 3 : ℝ))) := by ring
    have h_half : ‖phi c (-(w ^ 2)) / (-(w ^ 2)) - 1‖ ≤ 1 / 2 := by
      refine h_ratio.trans ?_
      rw [show (1 / 2 : ℝ) = 4 / r₀ ^ 2 * (r₀ ^ 2 / 8) by field_simp; ring]
      gcongr; linarith
    have hsq : lowerGoodWtilde phi c w ^ 2 = -(phi c (-(w ^ 2))) := by
      unfold lowerGoodWtilde
      rw [mul_pow, cpow_half_sq]
      have hu_ne : -(w ^ 2) ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hu_lb; nlinarith
      rw [show w ^ 2 * (phi c (-(w ^ 2)) / -(w ^ 2)) =
          -((- (w ^ 2)) * (phi c (-(w ^ 2)) / -(w ^ 2))) by ring, mul_div_cancel₀ _ hu_ne]
    have hsub : ‖lowerGoodWtilde phi c w - w‖ ≤ 8 / r₀ * (Cφ * c ^ (-(1 / 3 : ℝ))) := by
      unfold lowerGoodWtilde
      rw [show w * (phi c (-(w ^ 2)) / (-(w ^ 2))) ^ (1 / 2 : ℂ) - w =
          w * ((phi c (-(w ^ 2)) / (-(w ^ 2))) ^ (1 / 2 : ℂ) - 1) by ring, norm_mul]
      calc ‖w‖ * ‖(phi c (-(w ^ 2)) / (-(w ^ 2))) ^ (1 / 2 : ℂ) - 1‖
          ≤ (2 * r₀) * ‖phi c (-(w ^ 2)) / (-(w ^ 2)) - 1‖ :=
            mul_le_mul hw2 (cpow_half_sub_one_le h_half) (norm_nonneg _) (by positivity)
        _ ≤ (2 * r₀) * (4 / r₀ ^ 2 * (Cφ * c ^ (-(1 / 3 : ℝ)))) := by gcongr
        _ = 8 / r₀ * (Cφ * c ^ (-(1 / 3 : ℝ))) := by field_simp; ring
    have hsub32 : ‖lowerGoodWtilde phi c w - w‖ ≤ r₀ / 32 := by
      refine hsub.trans ?_
      calc 8 / r₀ * (Cφ * c ^ (-(1 / 3 : ℝ)))
          ≤ 8 / r₀ * (r₀ ^ 2 / 256) := by gcongr
        _ = r₀ / 32 := by field_simp; ring
    have hup : ‖lowerGoodWtilde phi c w‖ ≤ 9 / 4 * r₀ := by
      calc ‖lowerGoodWtilde phi c w‖
          = ‖(lowerGoodWtilde phi c w - w) + w‖ := by ring_nf
        _ ≤ ‖lowerGoodWtilde phi c w - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ r₀ / 32 + 2 * r₀ := add_le_add hsub32 hw2
        _ ≤ 9 / 4 * r₀ := by linarith
    have hlo : r₀ / 4 ≤ ‖lowerGoodWtilde phi c w‖ := by
      have := norm_sub_norm_le w (lowerGoodWtilde phi c w)
      rw [norm_sub_rev] at this
      linarith
    exact ⟨hsq, hsub, hsub32, hup, hlo⟩
  have him_sign : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      (0 < u.im → 0 < (phi c u).im) ∧ (u.im < 0 → (phi c u).im < 0) :=
    lowerGood_wtilde_im_sign hr₀ h_der ⟨ρ, hρ_gt, hdiff⟩ him hcl hr₀_eq hc_pos
  refine ⟨h_main, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw1 hw2 hw_im
    have hw_m := h_main w (by linarith) (by linarith)
    have hu_norm : ‖-(w ^ 2)‖ ≤ lowerRmax c1 c := by
      rw [hRmax_eq, norm_neg, norm_pow]; nlinarith
    have him_sq : (lowerGoodWtilde phi c w ^ 2).im = 2 * (lowerGoodWtilde phi c w).re * (lowerGoodWtilde phi c w).im := by
      simp [sq, Complex.mul_im]; ring
    by_cases hre : r₀ / 2 ≤ w.re
    · have hu_im : (-(w ^ 2)).im < 0 := by
        simp [sq, Complex.mul_im]; nlinarith
      have hphi_im : (phi c (-(w ^ 2))).im < 0 := (him_sign _ hu_norm).2 hu_im
      have hsq_im : 0 < (lowerGoodWtilde phi c w ^ 2).im := by
        rw [hw_m.1, Complex.neg_im]; linarith
      have hw_re_pos : 0 < (lowerGoodWtilde phi c w).re := by
        have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw_m.2.2.1)).1
        simp only [Complex.sub_re] at this
        linarith
      rw [him_sq] at hsq_im
      nlinarith
    · by_cases hre2 : w.re ≤ -(r₀ / 2)
      · have hu_im : 0 < (-(w ^ 2)).im := by
          simp [sq, Complex.mul_im]; nlinarith
        have hphi_im : 0 < (phi c (-(w ^ 2))).im := (him_sign _ hu_norm).1 hu_im
        have hsq_im : (lowerGoodWtilde phi c w ^ 2).im < 0 := by
          rw [hw_m.1, Complex.neg_im]; linarith
        have hw_re_neg : (lowerGoodWtilde phi c w).re < 0 := by
          have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw_m.2.2.1)).2
          simp only [Complex.sub_re] at this
          linarith
        rw [him_sq] at hsq_im
        nlinarith
      · have hre_abs : |w.re| < r₀ / 2 := abs_lt.mpr ⟨not_le.mp hre2, not_le.mp hre⟩
        have hy2 : w.im ^ 2 ≥ 3 / 4 * r₀ ^ 2 := by
          have h1 : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
            rw [pow_two, pow_two, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
          have h2 : w.re ^ 2 < (r₀ / 2) ^ 2 := by
            rw [← sq_abs w.re]; exact pow_lt_pow_left₀ hre_abs (abs_nonneg _) two_ne_zero
          nlinarith
        have hy_lb : r₀ / 2 ≤ w.im := by
          nlinarith [sq_nonneg (w.im - r₀ / 2)]
        have := (abs_le.mp ((Complex.abs_im_le_norm _).trans hw_m.2.2.1)).1
        simp only [Complex.sub_im] at this
        linarith
  · exact lowerGood_wtilde_real_pos hr₀ h_err him hcl hr₀_eq hc_pos h_main
  · exact lowerGood_wtilde_real_neg hr₀ h_err him hcl hr₀_eq hc_pos h_main
  · -- Bi-Lipschitz on `Re w ≥ 0`, `t ∈ [r₀/2, 2 r₀]`
    intro w hw1 hw2 t ht1 ht2 hw_re
    have hnorm_t : ‖(t : ℂ)‖ = t := by simp [abs_of_pos (by linarith : 0 < t)]
    have hmw := h_main w (by linarith) (by linarith)
    have hmt := h_main (t : ℂ) (by rw [hnorm_t]; exact ht1) (by rw [hnorm_t]; exact ht2)
    have h_lip : ‖(phi c (-(w ^ 2)) - -(w ^ 2)) - (phi c (-((t : ℂ) ^ 2)) - -((t : ℂ) ^ 2))‖ ≤
        1 / 4 * ‖-(w ^ 2) - -((t : ℂ) ^ 2)‖ := by
      refine (convex_closedBall (0 : ℂ) (lowerRmax c1 c)).norm_image_sub_le_of_norm_deriv_le
        (fun u hu => (hdiff.differentiableAt (isOpen_ball.mem_nhds
          (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt hρ_gt)))).sub differentiableAt_id)
        (fun u hu => ?_)
        (mem_closedBall_zero_iff.mpr (by rw [hRmax_eq, norm_neg, norm_pow, hnorm_t]; nlinarith only [ht1, ht2, hr₀_pos]))
        (mem_closedBall_zero_iff.mpr (by rw [hRmax_eq, norm_neg, norm_pow]; nlinarith only [hw2, norm_nonneg w, hr₀_pos]))
      have hsub := (hcl u (mem_closedBall_zero_iff.mp hu)).2
      have hd_eq : deriv (phi c - id) u = deriv (phi c) u - 1 := by
        have hd := (hdiff.differentiableAt (isOpen_ball.mem_nhds
          (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt hρ_gt)))).hasDerivAt
        exact (hd.sub (hasDerivAt_id u)).deriv
      rw [hd_eq]
      exact hsub.trans h_der
    have h_phi_lb : 3 / 4 * ‖w - (t : ℂ)‖ * ‖w + (t : ℂ)‖ ≤ ‖phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))‖ := by
      have htri := norm_sub_norm_le (-(w ^ 2) - -((t : ℂ) ^ 2))
        ((-(w ^ 2) - -((t : ℂ) ^ 2)) - (phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))))
      have heq1 : (-(w ^ 2) - -((t : ℂ) ^ 2)) - (phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))) =
          -((phi c (-(w ^ 2)) - -(w ^ 2)) - (phi c (-((t : ℂ) ^ 2)) - -((t : ℂ) ^ 2))) := by ring
      have heq2 : (-(w ^ 2) - -((t : ℂ) ^ 2)) -
          ((-(w ^ 2) - -((t : ℂ) ^ 2)) - (phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2)))) =
          phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2)) := by ring
      rw [heq2, heq1, norm_neg] at htri
      have h_sq : ‖-(w ^ 2) - -((t : ℂ) ^ 2)‖ = ‖w - (t : ℂ)‖ * ‖w + (t : ℂ)‖ := by
        rw [show -(w ^ 2) - -((t : ℂ) ^ 2) = -((w - (t : ℂ)) * (w + (t : ℂ))) by ring, norm_neg, norm_mul]
      linarith
    have h_sum_lb : r₀ / 2 ≤ ‖w + (t : ℂ)‖ := by
      have h1 : r₀ / 2 ≤ (w + (t : ℂ)).re := by simp; linarith
      exact h1.trans (Complex.re_le_norm _)
    have h_sum_ub : ‖lowerGoodWtilde phi c w + lowerGoodWtilde phi c (t : ℂ)‖ ≤ 9 / 8 * ‖w + (t : ℂ)‖ := by
      calc ‖lowerGoodWtilde phi c w + lowerGoodWtilde phi c (t : ℂ)‖
          = ‖(w + (t : ℂ)) + ((lowerGoodWtilde phi c w - w) + (lowerGoodWtilde phi c (t : ℂ) - (t : ℂ)))‖ := by
            congr 1; ring
        _ ≤ ‖w + (t : ℂ)‖ + (‖lowerGoodWtilde phi c w - w‖ + ‖lowerGoodWtilde phi c (t : ℂ) - (t : ℂ)‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ ‖w + (t : ℂ)‖ + (r₀ / 32 + r₀ / 32) := by gcongr; exact hmw.2.2.1; exact hmt.2.2.1
        _ ≤ ‖w + (t : ℂ)‖ + 1 / 8 * ‖w + (t : ℂ)‖ := by linarith
        _ = 9 / 8 * ‖w + (t : ℂ)‖ := by ring
    have h_prod : ‖lowerGoodWtilde phi c w - lowerGoodWtilde phi c (t : ℂ)‖ *
        ‖lowerGoodWtilde phi c w + lowerGoodWtilde phi c (t : ℂ)‖ =
        ‖phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))‖ := by
      rw [← norm_mul, show (lowerGoodWtilde phi c w - lowerGoodWtilde phi c (t : ℂ)) *
          (lowerGoodWtilde phi c w + lowerGoodWtilde phi c (t : ℂ)) =
          lowerGoodWtilde phi c w ^ 2 - lowerGoodWtilde phi c (t : ℂ) ^ 2 by ring,
        hmw.1, hmt.1, show -(phi c (-(w ^ 2))) - -(phi c (-((t : ℂ) ^ 2))) =
          -(phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))) by ring, norm_neg]
    have h_pos_sum : 0 < ‖w + (t : ℂ)‖ := by linarith
    nlinarith only [h_phi_lb, h_sum_ub, h_prod, h_pos_sum,
      norm_nonneg (lowerGoodWtilde phi c w - lowerGoodWtilde phi c (t : ℂ))]
  · -- Bi-Lipschitz on `Re w ≤ 0`, `t ∈ [-2 r₀, -r₀/2]`
    intro w hw1 hw2 t ht1 ht2 hw_re
    have hnorm_t : ‖(t : ℂ)‖ = -t := by simp [abs_of_neg (by linarith : t < 0)]
    have hmw := h_main w (by linarith) (by linarith)
    have hmt := h_main (t : ℂ) (by rw [hnorm_t]; linarith) (by rw [hnorm_t]; linarith)
    have h_lip : ‖(phi c (-(w ^ 2)) - -(w ^ 2)) - (phi c (-((t : ℂ) ^ 2)) - -((t : ℂ) ^ 2))‖ ≤
        1 / 4 * ‖-(w ^ 2) - -((t : ℂ) ^ 2)‖ := by
      refine (convex_closedBall (0 : ℂ) (lowerRmax c1 c)).norm_image_sub_le_of_norm_deriv_le
        (fun u hu => (hdiff.differentiableAt (isOpen_ball.mem_nhds
          (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt hρ_gt)))).sub differentiableAt_id)
        (fun u hu => ?_)
        (mem_closedBall_zero_iff.mpr (by rw [hRmax_eq, norm_neg, norm_pow, hnorm_t]; nlinarith only [ht1, ht2, hr₀_pos]))
        (mem_closedBall_zero_iff.mpr (by rw [hRmax_eq, norm_neg, norm_pow]; nlinarith only [hw2, norm_nonneg w, hr₀_pos]))
      have hsub := (hcl u (mem_closedBall_zero_iff.mp hu)).2
      have hd_eq : deriv (phi c - id) u = deriv (phi c) u - 1 := by
        have hd := (hdiff.differentiableAt (isOpen_ball.mem_nhds
          (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt hρ_gt)))).hasDerivAt
        exact (hd.sub (hasDerivAt_id u)).deriv
      rw [hd_eq]
      exact hsub.trans h_der
    have h_phi_lb : 3 / 4 * ‖w - (t : ℂ)‖ * ‖w + (t : ℂ)‖ ≤ ‖phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))‖ := by
      have htri := norm_sub_norm_le (-(w ^ 2) - -((t : ℂ) ^ 2))
        ((-(w ^ 2) - -((t : ℂ) ^ 2)) - (phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))))
      have heq1 : (-(w ^ 2) - -((t : ℂ) ^ 2)) - (phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))) =
          -((phi c (-(w ^ 2)) - -(w ^ 2)) - (phi c (-((t : ℂ) ^ 2)) - -((t : ℂ) ^ 2))) := by ring
      have heq2 : (-(w ^ 2) - -((t : ℂ) ^ 2)) -
          ((-(w ^ 2) - -((t : ℂ) ^ 2)) - (phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2)))) =
          phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2)) := by ring
      rw [heq2, heq1, norm_neg] at htri
      have h_sq : ‖-(w ^ 2) - -((t : ℂ) ^ 2)‖ = ‖w - (t : ℂ)‖ * ‖w + (t : ℂ)‖ := by
        rw [show -(w ^ 2) - -((t : ℂ) ^ 2) = -((w - (t : ℂ)) * (w + (t : ℂ))) by ring, norm_neg, norm_mul]
      linarith
    have h_sum_lb : r₀ / 2 ≤ ‖w + (t : ℂ)‖ := by
      have h1 : r₀ / 2 ≤ -(w + (t : ℂ)).re := by simp; linarith
      exact h1.trans (by rw [← Complex.neg_re]; exact (Complex.re_le_norm _).trans (by rw [norm_neg]))
    have h_sum_ub : ‖lowerGoodWtilde phi c w + lowerGoodWtilde phi c (t : ℂ)‖ ≤ 9 / 8 * ‖w + (t : ℂ)‖ := by
      calc ‖lowerGoodWtilde phi c w + lowerGoodWtilde phi c (t : ℂ)‖
          = ‖(w + (t : ℂ)) + ((lowerGoodWtilde phi c w - w) + (lowerGoodWtilde phi c (t : ℂ) - (t : ℂ)))‖ := by
            congr 1; ring
        _ ≤ ‖w + (t : ℂ)‖ + (‖lowerGoodWtilde phi c w - w‖ + ‖lowerGoodWtilde phi c (t : ℂ) - (t : ℂ)‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ ‖w + (t : ℂ)‖ + (r₀ / 32 + r₀ / 32) := by gcongr; exact hmw.2.2.1; exact hmt.2.2.1
        _ ≤ ‖w + (t : ℂ)‖ + 1 / 8 * ‖w + (t : ℂ)‖ := by linarith
        _ = 9 / 8 * ‖w + (t : ℂ)‖ := by ring
    have h_prod : ‖lowerGoodWtilde phi c w - lowerGoodWtilde phi c (t : ℂ)‖ *
        ‖lowerGoodWtilde phi c w + lowerGoodWtilde phi c (t : ℂ)‖ =
        ‖phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))‖ := by
      rw [← norm_mul, show (lowerGoodWtilde phi c w - lowerGoodWtilde phi c (t : ℂ)) *
          (lowerGoodWtilde phi c w + lowerGoodWtilde phi c (t : ℂ)) =
          lowerGoodWtilde phi c w ^ 2 - lowerGoodWtilde phi c (t : ℂ) ^ 2 by ring,
        hmw.1, hmt.1, show -(phi c (-(w ^ 2))) - -(phi c (-((t : ℂ) ^ 2))) =
          -(phi c (-(w ^ 2)) - phi c (-((t : ℂ) ^ 2))) by ring, norm_neg]
    have h_pos_sum : 0 < ‖w + (t : ℂ)‖ := by linarith
    nlinarith only [h_phi_lb, h_sum_ub, h_prod, h_pos_sum,
      norm_nonneg (lowerGoodWtilde phi c w - lowerGoodWtilde phi c (t : ℂ))]

lemma lowerGood_wtilde_continuousOn {c1 c : ℝ} {phi : ℝ → ℂ → ℂ} {r₀ : ℝ}
    (hr₀ : 10 ≤ r₀)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (hr₀_eq : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hc_pos : 0 < c) :
    ContinuousOn (lowerGoodWtilde phi c) {w : ℂ | r₀ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r₀} := by
  obtain ⟨ρ, hρ_gt, hdiff⟩ := hρ
  have hRmax_eq : lowerRmax c1 c = 4 * r₀ ^ 2 := by
    unfold lowerRmax
    rw [hr₀_eq, mul_pow, ← Real.rpow_natCast (c ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hc_pos.le]
    norm_num; ring
  have hr₀_pos : 0 < r₀ := by linarith
  intro w hw
  have hu_norm : ‖-(w ^ 2)‖ ≤ lowerRmax c1 c := by
    rw [hRmax_eq, norm_neg, norm_pow]; nlinarith [hw.2, norm_nonneg w]
  have hu_lb : r₀ ^ 2 / 4 ≤ ‖-(w ^ 2)‖ := by
    rw [norm_neg, norm_pow]; nlinarith [hw.1, norm_nonneg w]
  have hu_ne : -(w ^ 2) ≠ 0 := by intro h0; rw [h0, norm_zero] at hu_lb; nlinarith [sq_pos_of_pos hr₀_pos]
  have h_half : ‖phi c (-(w ^ 2)) / (-(w ^ 2)) - 1‖ ≤ 1 / 2 := by
    rw [div_sub_one hu_ne, norm_div]
    calc ‖phi c (-(w ^ 2)) - -(w ^ 2)‖ / ‖-(w ^ 2)‖
        ≤ ‖phi c (-(w ^ 2)) - -(w ^ 2)‖ / (r₀ ^ 2 / 4) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hu_lb
      _ ≤ (Cφ * c ^ (-(1 / 3 : ℝ))) / (r₀ ^ 2 / 4) :=
          div_le_div_of_nonneg_right (hcl _ hu_norm).1 (by positivity)
      _ ≤ (r₀ ^ 2 / 256) / (r₀ ^ 2 / 4) := by gcongr
      _ = 1 / 64 := by field_simp; ring
      _ ≤ 1 / 2 := by norm_num
  have h_slit : phi c (-(w ^ 2)) / (-(w ^ 2)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans h_half)).1
    simp only [Complex.sub_re, Complex.one_re] at h1
    linarith
  have h_phi_cont : ContinuousAt (fun z : ℂ => phi c (-(z ^ 2))) w := by
    have hd : DifferentiableAt ℂ (phi c) (-(w ^ 2)) :=
      hdiff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (hu_norm.trans_lt hρ_gt)))
    exact hd.continuousAt.comp_of_eq (by fun_prop) rfl
  have h_ratio_cont : ContinuousAt (fun z : ℂ => phi c (-(z ^ 2)) / (-(z ^ 2))) w :=
    h_phi_cont.div (by fun_prop) hu_ne
  have h_cpow_cont : ContinuousAt (fun z : ℂ => (phi c (-(z ^ 2)) / (-(z ^ 2))) ^ (1 / 2 : ℂ)) w :=
    ((Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ)) h_slit).hasDerivAt.continuousAt).comp_of_eq
      h_ratio_cont rfl
  exact (continuousAt_id.mul h_cpow_cont).continuousWithinAt

lemma lowerGood_wtilde_inv_norm_area_le {c1 c Cφ r₀ : ℝ} {phi : ℝ → ℂ → ℂ}
    (hr₀ : 10 ≤ r₀) (hCφ : 0 ≤ Cφ)
    (h_err : Cφ * c ^ (-(1 / 3 : ℝ)) ≤ r₀ ^ 2 / 256)
    (h_der : Cφ * c ^ (-1 : ℝ) ≤ 1 / 4)
    (hρ : ∃ ρ : ℝ, lowerRmax c1 c < ρ ∧ DifferentiableOn ℂ (phi c) (ball 0 ρ))
    (him : ∀ x : ℝ, |x| ≤ lowerRmax c1 c → (phi c (x : ℂ)).im = 0)
    (hcl : ∀ u : ℂ, ‖u‖ ≤ lowerRmax c1 c →
      ‖phi c u - u‖ ≤ Cφ * c ^ (-(1 / 3 : ℝ)) ∧ ‖deriv (phi c) u - 1‖ ≤ Cφ * c ^ (-1 : ℝ))
    (hr₀_eq : r₀ = c1 * c ^ (1 / 3 : ℝ)) (hc_pos : 0 < c) (t : ℝ) :
    ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
      ENNReal.ofReal p.1 * (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
      ENNReal.ofReal (72 * π * r₀) := by
  obtain ⟨h_main, _, h_pos_real, h_neg_real, h_lip_pos, h_lip_neg⟩ :=
    lowerGood_wtilde_props hr₀ hCφ h_err h_der hρ him hcl hr₀_eq hc_pos
  have h_cont := lowerGood_wtilde_continuousOn hr₀ h_err hcl hρ hr₀_eq hc_pos
  have hr₀_pos : 0 < r₀ := by linarith
  have h_polar_ball : ∀ s : ℝ,
      ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
        ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s : ℂ)‖)⁻¹ ≤
        ENNReal.ofReal (3 * π * (3 / 2 * r₀)) := by
    intro s
    have h_sub : (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π) ⊆ Complex.polarCoord.target := by
      intro p hp
      rw [Complex.polarCoord_target]
      exact ⟨lt_trans (by linarith : (0 : ℝ) < r₀) hp.1.1,
        ⟨lt_trans (by linarith [Real.pi_pos]) hp.2.1, hp.2.2⟩⟩
    have h_le1 : ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
          ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s : ℂ)‖)⁻¹ ≤
        ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator
            (fun z => (ENNReal.ofReal ‖z - (s : ℂ)‖)⁻¹) (Complex.polarCoord.symm p) := by
      have h_pt : ∀ p ∈ (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
          ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s : ℂ)‖)⁻¹ ≤
          ENNReal.ofReal p.1 • (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator
            (fun z => (ENNReal.ofReal ‖z - (s : ℂ)‖)⁻¹) (Complex.polarCoord.symm p) := by
        intro p hp
        have hp1 : 0 < p.1 := by linarith [hp.1.1]
        have hsymm : Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (p.2 * I) := by
          simp [Complex.exp_mul_I]
        have hmem : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) (3 / 2 * r₀) := by
          rw [mem_closedBall_zero_iff, hsymm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hp1, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact hp.1.2
        rw [Set.indicator_of_mem hmem, hsymm, smul_eq_mul]
      exact (setLIntegral_mono' (measurableSet_Ioc.prod measurableSet_Ioo) h_pt).trans
        (lintegral_mono_set h_sub)
    have h_eq : (∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator
            (fun z => (ENNReal.ofReal ‖z - (s : ℂ)‖)⁻¹) (Complex.polarCoord.symm p)) =
        ∫⁻ z in closedBall (0 : ℂ) (3 / 2 * r₀), (ENNReal.ofReal ‖z - (s : ℂ)‖)⁻¹ := by
      have h_pc := Complex.lintegral_comp_polarCoord_symm
        (fun z => (closedBall (0 : ℂ) (3 / 2 * r₀)).indicator (fun z => (ENNReal.ofReal ‖z - (s : ℂ)‖)⁻¹) z)
      exact h_pc.trans (lintegral_indicator measurableSet_closedBall _)
    rw [h_eq] at h_le1
    exact h_le1.trans (lowerGood_inv_norm_area_le (by positivity) s)
  -- Case split on `t`
  let a₁ := (lowerGoodWtilde phi c ((r₀ / 2 : ℝ) : ℂ)).re
  let b₁ := (lowerGoodWtilde phi c ((2 * r₀ : ℝ) : ℂ)).re
  let a₂ := (lowerGoodWtilde phi c ((-(2 * r₀) : ℝ) : ℂ)).re
  let b₂ := (lowerGoodWtilde phi c ((-(r₀ / 2) : ℝ) : ℂ)).re
  by_cases ht1 : t ∈ Icc a₁ b₁
  · have h_cont_re : ContinuousOn (fun s : ℝ => (lowerGoodWtilde phi c (s : ℂ)).re) (Icc (r₀ / 2) (2 * r₀)) :=
      Complex.continuous_re.comp_continuousOn (h_cont.comp Complex.continuous_ofReal.continuousOn
        fun s hs => by
          have hs0 : 0 ≤ s := by linarith [hs.1]
          refine ⟨?_, ?_⟩ <;>
            · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
              linarith [hs.1, hs.2])
    obtain ⟨s_t, hs_mem, hs_eq⟩ := intermediate_value_Icc (by linarith : r₀ / 2 ≤ 2 * r₀) h_cont_re ht1
    have hw_st : lowerGoodWtilde phi c (s_t : ℂ) = (t : ℂ) :=
      Complex.ext hs_eq (h_pos_real s_t hs_mem.1 hs_mem.2).1
    have h_pt_lb : ∀ p ∈ (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
        (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
        16 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹ := by
      intro p hp
      let w : ℂ := (p.1 : ℂ) * Complex.exp (p.2 * I)
      have hw_norm : ‖w‖ = p.1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hp.1.1]),
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have hw_lb : r₀ ≤ ‖w‖ := by rw [hw_norm]; exact hp.1.1.le
      have hw_ub : ‖w‖ ≤ 3 / 2 * r₀ := by rw [hw_norm]; exact hp.1.2
      have h_low : 1 / 16 * ‖w - (s_t : ℂ)‖ ≤ ‖lowerGoodWtilde phi c w - (t : ℂ)‖ := by
        by_cases hre : 0 ≤ w.re
        · rw [← hw_st]
          exact (by nlinarith [norm_nonneg (w - (s_t : ℂ)),
            h_lip_pos w hw_lb hw_ub s_t hs_mem.1 hs_mem.2 hre])
        · have hre_neg : w.re < 0 := not_le.mp hre
          have hwm := h_main w (by linarith) (by linarith)
          have hw_re_ub : (lowerGoodWtilde phi c w).re ≤ r₀ / 32 := by
            have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hwm.2.2.1)).2
            simp only [Complex.sub_re] at this
            linarith
          have ht_lb : r₀ / 4 ≤ t := by
            have := (h_pos_real s_t hs_mem.1 hs_mem.2).2.1
            dsimp only at hs_eq; rw [hs_eq] at this
            linarith [hs_mem.1]
          have hnorm_diff : 7 / 32 * r₀ ≤ ‖lowerGoodWtilde phi c w - (t : ℂ)‖ := by
            have h1 : 7 / 32 * r₀ ≤ -(lowerGoodWtilde phi c w - (t : ℂ)).re := by
              simp; linarith
            exact h1.trans (by rw [← Complex.neg_re]; exact (Complex.re_le_norm _).trans (by rw [norm_neg]))
          have hnorm_ws : ‖w - (s_t : ℂ)‖ ≤ 7 / 2 * r₀ := by
            calc ‖w - (s_t : ℂ)‖ ≤ ‖w‖ + ‖(s_t : ℂ)‖ := norm_sub_le _ _
              _ ≤ 3 / 2 * r₀ + 2 * r₀ := by
                rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hs_mem.1])]
                exact add_le_add hw_ub hs_mem.2
              _ = 7 / 2 * r₀ := by ring
          linarith
      have h_enn : ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal ‖w - (s_t : ℂ)‖ ≤
          ENNReal.ofReal ‖lowerGoodWtilde phi c w - (t : ℂ)‖ := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal h_low
      have h_inv := ENNReal.inv_le_inv.mpr h_enn
      rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr (by norm_num)).ne') (Or.inl ENNReal.ofReal_ne_top)] at h_inv
      have h16 : (ENNReal.ofReal (1 / 16 : ℝ))⁻¹ = 16 := by
        rw [← ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
      rwa [h16] at h_inv
    calc ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
          ENNReal.ofReal p.1 * (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹
        ≤ ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
            16 * (ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹) := by
          refine setLIntegral_mono' (measurableSet_Ioc.prod measurableSet_Ioo) fun p hp => ?_
          calc ENNReal.ofReal p.1 * (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹
              ≤ ENNReal.ofReal p.1 * (16 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹) := by
                gcongr; exact h_pt_lb p hp
            _ = 16 * (ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹) := by ring
      _ = 16 * ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
            ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹ :=
          lintegral_const_mul _ (by fun_prop)
      _ ≤ 16 * ENNReal.ofReal (3 * π * (3 / 2 * r₀)) := by gcongr; exact h_polar_ball s_t
      _ = ENNReal.ofReal (72 * π * r₀) := by
          rw [show (16 : ENNReal) = ENNReal.ofReal 16 by norm_num,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
  · by_cases ht2 : t ∈ Icc a₂ b₂
    · have h_cont_re : ContinuousOn (fun s : ℝ => (lowerGoodWtilde phi c (s : ℂ)).re) (Icc (-2 * r₀) (-(r₀ / 2))) :=
        Complex.continuous_re.comp_continuousOn (h_cont.comp Complex.continuous_ofReal.continuousOn
          fun s hs => by
            have hs0 : s ≤ 0 := by linarith [hs.2]
            refine ⟨?_, ?_⟩ <;>
              · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hs0]
                linarith [hs.1, hs.2])
      obtain ⟨s_t, hs_mem, hs_eq⟩ := intermediate_value_Icc (by linarith : -2 * r₀ ≤ -(r₀ / 2)) h_cont_re
        (by simpa [a₂, b₂] using ht2)
      have hw_st : lowerGoodWtilde phi c (s_t : ℂ) = (t : ℂ) :=
        Complex.ext hs_eq (h_neg_real s_t (by linarith [hs_mem.1]) hs_mem.2).1
      have h_pt_lb : ∀ p ∈ (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
          (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
          16 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹ := by
        intro p hp
        let w : ℂ := (p.1 : ℂ) * Complex.exp (p.2 * I)
        have hw_norm : ‖w‖ = p.1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hp.1.1]),
            Complex.norm_exp_ofReal_mul_I, mul_one]
        have hw_lb : r₀ ≤ ‖w‖ := by rw [hw_norm]; exact hp.1.1.le
        have hw_ub : ‖w‖ ≤ 3 / 2 * r₀ := by rw [hw_norm]; exact hp.1.2
        have h_low : 1 / 16 * ‖w - (s_t : ℂ)‖ ≤ ‖lowerGoodWtilde phi c w - (t : ℂ)‖ := by
          by_cases hre : w.re ≤ 0
          · rw [← hw_st]
            exact (by nlinarith [norm_nonneg (w - (s_t : ℂ)),
              h_lip_neg w hw_lb hw_ub s_t (by linarith [hs_mem.1]) hs_mem.2 hre])
          · have hre_pos : 0 < w.re := not_le.mp hre
            have hwm := h_main w (by linarith) (by linarith)
            have hw_re_lb : -(r₀ / 32) ≤ (lowerGoodWtilde phi c w).re := by
              have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hwm.2.2.1)).1
              simp only [Complex.sub_re] at this
              linarith
            have ht_ub : t ≤ -(r₀ / 4) := by
              have := (h_neg_real s_t (by linarith [hs_mem.1]) hs_mem.2).2.2
              dsimp only at hs_eq; rw [hs_eq] at this
              linarith [hs_mem.2]
            have hnorm_diff : 7 / 32 * r₀ ≤ ‖lowerGoodWtilde phi c w - (t : ℂ)‖ := by
              have h1 : 7 / 32 * r₀ ≤ (lowerGoodWtilde phi c w - (t : ℂ)).re := by
                simp; linarith
              exact h1.trans (Complex.re_le_norm _)
            have hnorm_ws : ‖w - (s_t : ℂ)‖ ≤ 7 / 2 * r₀ := by
              calc ‖w - (s_t : ℂ)‖ ≤ ‖w‖ + ‖(s_t : ℂ)‖ := norm_sub_le _ _
                _ ≤ 3 / 2 * r₀ + 2 * r₀ := by
                  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [hs_mem.2])]
                  linarith [hs_mem.1]
                _ = 7 / 2 * r₀ := by ring
            linarith
        have h_enn : ENNReal.ofReal (1 / 16 : ℝ) * ENNReal.ofReal ‖w - (s_t : ℂ)‖ ≤
            ENNReal.ofReal ‖lowerGoodWtilde phi c w - (t : ℂ)‖ := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal h_low
        have h_inv := ENNReal.inv_le_inv.mpr h_enn
        rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr (by norm_num)).ne') (Or.inl ENNReal.ofReal_ne_top)] at h_inv
        have h16 : (ENNReal.ofReal (1 / 16 : ℝ))⁻¹ = 16 := by
          rw [← ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
        rwa [h16] at h_inv
      calc ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
            ENNReal.ofReal p.1 * (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹
          ≤ ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
              16 * (ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹) := by
            refine setLIntegral_mono' (measurableSet_Ioc.prod measurableSet_Ioo) fun p hp => ?_
            calc ENNReal.ofReal p.1 * (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹
                ≤ ENNReal.ofReal p.1 * (16 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹) := by
                  gcongr; exact h_pt_lb p hp
              _ = 16 * (ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹) := by ring
        _ = 16 * ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
              ENNReal.ofReal p.1 * (ENNReal.ofReal ‖p.1 * Complex.exp (p.2 * I) - (s_t : ℂ)‖)⁻¹ :=
            lintegral_const_mul _ (by fun_prop)
        _ ≤ 16 * ENNReal.ofReal (3 * π * (3 / 2 * r₀)) := by gcongr; exact h_polar_ball s_t
        _ = ENNReal.ofReal (72 * π * r₀) := by
            rw [show (16 : ENNReal) = ENNReal.ofReal 16 by norm_num,
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; ring
    · -- Case 3: `t ∉ Icc a₁ b₁` and `t ∉ Icc a₂ b₂`
      have ha₁_le : a₁ ≤ 17 / 32 * r₀ := by
        have hm := h_main ((r₀ / 2 : ℝ) : ℂ) (by simp [abs_of_pos hr₀_pos])
          (by simp [abs_of_pos hr₀_pos]; linarith)
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hm.2.2.1)).2
        simp only [Complex.sub_re, Complex.ofReal_re] at h1
        dsimp [a₁]; linarith
      have hb₁_ge : 63 / 32 * r₀ ≤ b₁ := by
        have hm := h_main ((2 * r₀ : ℝ) : ℂ) (by simp [abs_of_pos hr₀_pos]; linarith)
          (by simp [abs_of_pos hr₀_pos])
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hm.2.2.1)).1
        simp only [Complex.sub_re, Complex.ofReal_re] at h1
        dsimp [b₁]; linarith
      have ha₂_le : a₂ ≤ -(63 / 32 * r₀) := by
        have hm := h_main ((-(2 * r₀) : ℝ) : ℂ) (by simp [abs_of_pos hr₀_pos]; linarith)
          (by simp [abs_of_pos hr₀_pos])
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hm.2.2.1)).2
        simp only [Complex.sub_re, Complex.ofReal_re] at h1
        dsimp [a₂]; linarith
      have hb₂_ge : -(17 / 32 * r₀) ≤ b₂ := by
        have hm := h_main ((-(r₀ / 2) : ℝ) : ℂ) (by simp [abs_of_pos hr₀_pos])
          (by simp [abs_of_pos hr₀_pos]; linarith)
        have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hm.2.2.1)).1
        simp only [Complex.sub_re, Complex.ofReal_re] at h1
        dsimp [b₂]; linarith
      have h_pt_const : ∀ p ∈ (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
          ENNReal.ofReal p.1 * (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹ ≤
          ENNReal.ofReal 6 := by
        intro p hp
        let w : ℂ := (p.1 : ℂ) * Complex.exp (p.2 * I)
        have hw_norm : ‖w‖ = p.1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hp.1.1]),
            Complex.norm_exp_ofReal_mul_I, mul_one]
        have hwm := h_main w (by rw [hw_norm]; linarith [hp.1.1]) (by rw [hw_norm]; linarith [hp.1.2])
        have hw_lb : 31 / 32 * r₀ ≤ ‖lowerGoodWtilde phi c w‖ := by
          have := norm_sub_norm_le w (lowerGoodWtilde phi c w)
          rw [norm_sub_rev] at this
          linarith [hwm.2.2.1, hp.1.1, hw_norm]
        have hw_ub : ‖lowerGoodWtilde phi c w‖ ≤ 49 / 32 * r₀ := by
          calc ‖lowerGoodWtilde phi c w‖ ≤ ‖w‖ + ‖lowerGoodWtilde phi c w - w‖ := by
                have := norm_add_le w (lowerGoodWtilde phi c w - w)
                simpa using this
            _ ≤ 3 / 2 * r₀ + r₀ / 32 := add_le_add (by rw [hw_norm]; exact hp.1.2) hwm.2.2.1
            _ = 49 / 32 * r₀ := by ring
        have h_diff_lb : r₀ / 4 ≤ ‖lowerGoodWtilde phi c w - (t : ℂ)‖ := by
          have hnot1 : t < a₁ ∨ b₁ < t := not_and_or.mp (fun h => ht1 h) |>.imp not_le.mp not_le.mp
          have hnot2 : t < a₂ ∨ b₂ < t := not_and_or.mp (fun h => ht2 h) |>.imp not_le.mp not_le.mp
          rcases hnot1 with h1 | h1
          · rcases hnot2 with h2 | h2
            · have : ‖(t : ℂ)‖ = -t := by simp [abs_of_neg (by linarith : t < 0)]
              have := norm_sub_norm_le (t : ℂ) (lowerGoodWtilde phi c w)
              rw [norm_sub_rev] at this
              linarith
            · have : ‖(t : ℂ)‖ ≤ 17 / 32 * r₀ := by
                rw [Complex.norm_real, Real.norm_eq_abs]
                exact abs_le.mpr ⟨by linarith, by linarith⟩
              have := norm_sub_norm_le (lowerGoodWtilde phi c w) (t : ℂ)
              linarith
          · have : ‖(t : ℂ)‖ = t := by simp [abs_of_pos (by linarith : 0 < t)]
            have := norm_sub_norm_le (t : ℂ) (lowerGoodWtilde phi c w)
            rw [norm_sub_rev] at this
            linarith
        have h_inv_le : (ENNReal.ofReal ‖lowerGoodWtilde phi c w - (t : ℂ)‖)⁻¹ ≤ (ENNReal.ofReal (r₀ / 4))⁻¹ :=
          ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal h_diff_lb)
        calc ENNReal.ofReal p.1 * (ENNReal.ofReal ‖lowerGoodWtilde phi c w - (t : ℂ)‖)⁻¹
            ≤ ENNReal.ofReal (3 / 2 * r₀) * (ENNReal.ofReal (r₀ / 4))⁻¹ :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hp.1.2) h_inv_le
          _ = ENNReal.ofReal 6 := by
              rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 1; field_simp; ring
      calc ∫⁻ p in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π),
            ENNReal.ofReal p.1 * (ENNReal.ofReal ‖lowerGoodWtilde phi c (p.1 * Complex.exp (p.2 * I)) - (t : ℂ)‖)⁻¹
          ≤ ∫⁻ _ in (Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π), ENNReal.ofReal 6 :=
            setLIntegral_mono' (measurableSet_Ioc.prod measurableSet_Ioo) h_pt_const
        _ = ENNReal.ofReal 6 * volume ((Ioc r₀ (3 / 2 * r₀)) ×ˢ (Ioo (0 : ℝ) π)) := setLIntegral_const _ _
        _ = ENNReal.ofReal (3 * π * r₀) := by
            rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioo, sub_zero,
              show 3 / 2 * r₀ - r₀ = r₀ / 2 by ring, ← ENNReal.ofReal_mul (by linarith : 0 ≤ r₀ / 2),
              ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (72 * π * r₀) := ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])

end FormalResearch.ModularBootstrap.FiveTerm
