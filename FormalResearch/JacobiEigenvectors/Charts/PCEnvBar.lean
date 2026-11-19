module

public import Mathlib
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal
public import FormalResearch.JacobiEigenvectors.Charts.PCLaplace

/-!
# Paper J, Layer 4 (phase B2, E1 + E4bar): `env_bar` for `a >= 1` and all `z`

Proves the two inequalities of `PCEnvelopeFacts.env_bar` for the actual function `pcU`
when `1 ≤ a` and `z : ℝ` is arbitrary, with the absolute constant `C = 20`:

* E1 (`errorDensity_bar`, `abs_errorDensity_bar_le`, `integral_abs_errorDensity_bar_le`,
  `integral_abs_errorDensity_bar_nonneg_le`): for `p(t) = t^2 / 4 + a` (`a > 0`),
  `errorDensity p p' p'' 0 t = (3/16 p(t) - 5/16 a) p(t)^{-5/2}`, so
  `|errorDensity| ≤ (5/16) p(t)^{-3/2}`; using `(t p(t)^{-1/2})' = a p(t)^{-3/2}` and
  `|t p(t)^{-1/2}| < 2`, the total variation over `(x, ∞)` is at most `5/(4a) ≤ 5/4`
  (and at most `5/(8a) ≤ 5/8` for `x ≥ 0`).
* E4bar (`pc_env_bar_first_ge_one`, `pc_env_bar_ge_one`): applying
  `LiouvilleGreen.exists_solution_exp_of_pos` on `(L, ∞)` for `L = min z 0 - 1`,
  identifying `pcU a` as a constant multiple of the recessive LG solution via the
  Wronskian (`tendsto_pcU`, `pcU_decay_bound`, `pc_shift_U_dn`), normalising at `z = 0`
  via `PCOrigin.origin_env_bar`, and obtaining the `U(a, -z)` bound via the symmetry
  `Ebar a (-z) = (Ebar a z)⁻¹`.

What is NOT proved here: `a ∈ (0, 1)` (compact range, E5), `env_well`, `molv_*`, `beyond`,
`U_pos`, `V_growth`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open MeasureTheory Set Real Filter Topology intervalIntegral

/-! ### E1: error-density and variation bounds for `p(t) = t^2 / 4 + a` -/

lemma p_pos {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 < t ^ 2 / 4 + a := by positivity

lemma errorDensity_bar (a t : ℝ) (ha : 0 < a) :
    LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a) (fun s => s / 2)
        (fun _ => 1 / 2) (fun _ => 0) t =
      (3 / 16 * (t ^ 2 / 4 + a) - 5 / 16 * a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
  have hp : 0 < t ^ 2 / 4 + a := p_pos ha t
  unfold LiouvilleGreen.errorDensity
  have h1 : (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) =
      (t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_one_add' hp.le (by norm_num)]
    norm_num
  rw [h1]
  ring

lemma abs_errorDensity_bar_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a) (fun s => s / 2)
        (fun _ => 1 / 2) (fun _ => 0) t| ≤
      5 / 16 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by
  have hp : 0 < t ^ 2 / 4 + a := p_pos ha t
  rw [errorDensity_bar a t ha, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hp _)]
  have hpa : a ≤ t ^ 2 / 4 + a := by linarith [sq_nonneg t]
  have hab : |3 / 16 * (t ^ 2 / 4 + a) - 5 / 16 * a| ≤ 5 / 16 * (t ^ 2 / 4 + a) := by
    rw [abs_le]
    constructor <;> linarith
  have h1 : (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) =
      (t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_one_add' hp.le (by norm_num)]
    norm_num
  calc |3 / 16 * (t ^ 2 / 4 + a) - 5 / 16 * a| * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)
      ≤ (5 / 16 * (t ^ 2 / 4 + a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
        gcongr
    _ = 5 / 16 * ((t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)) := by ring
    _ = 5 / 16 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by rw [← h1]

lemma hasDerivAt_bar_antideriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun s => s * (s ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ))
      (a * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) t := by
  have hp : 0 < t ^ 2 / 4 + a := p_pos ha t
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 4 + a) (t / 2) t := by
    have := ((hasDerivAt_pow 2 t).div_const 4).add_const a
    refine this.congr_deriv ?_
    ring
  have hrp := hsq.rpow_const (p := -(1 / 2)) (Or.inl hp.ne')
  have hprod := (hasDerivAt_id t).mul hrp
  refine hprod.congr_deriv ?_
  have h1 : (t ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ) =
      (t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_one_add' hp.le (by norm_num)]
    norm_num
  have h2 : (-(1 / 2) - 1 : ℝ) = -(3 / 2) := by norm_num
  rw [h2, h1]
  simp only [id_eq]
  ring

lemma abs_bar_antideriv_lt {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t * (t ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ)| < 2 := by
  have hp : 0 < t ^ 2 / 4 + a := p_pos ha t
  have hsq : (t * (t ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ)) ^ 2 < 2 ^ 2 := by
    have hpow : ((t ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ)) ^ 2 = (t ^ 2 / 4 + a)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      norm_num [Real.rpow_neg_one]
    rw [mul_pow, hpow]
    rw [← div_eq_mul_inv, div_lt_iff₀ hp]
    nlinarith
  exact abs_lt.mpr (abs_lt_of_sq_lt_sq' hsq (by norm_num))

lemma intervalIntegral_bar_rpow_le {a : ℝ} (ha : 0 < a) {x y : ℝ} (hxy : x ≤ y) :
    ∫ t in x..y, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ 4 / a := by
  have hcont : Continuous (fun t : ℝ => a * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) := by
    refine continuous_const.mul (Continuous.rpow_const ?_ ?_)
    · continuity
    · intro t; exact Or.inl (p_pos ha t).ne'
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_bar_antideriv ha t) (hcont.intervalIntegrable x y)
  have hbd : y * (y ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ) -
      x * (x ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ) ≤ 4 := by
    have hy := (abs_lt.mp (abs_bar_antideriv_lt ha y)).2
    have hx := (abs_lt.mp (abs_bar_antideriv_lt ha x)).1
    linarith
  have hmul : ∫ t in x..y, a * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ 4 := by
    rw [hint]; exact hbd
  rw [intervalIntegral.integral_const_mul] at hmul
  rw [le_div_iff₀ ha]
  linarith

lemma intervalIntegral_bar_rpow_nonneg_le {a : ℝ} (ha : 0 < a) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∫ t in x..y, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ 2 / a := by
  have hcont : Continuous (fun t : ℝ => a * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) := by
    refine continuous_const.mul (Continuous.rpow_const ?_ ?_)
    · continuity
    · intro t; exact Or.inl (p_pos ha t).ne'
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_bar_antideriv ha t) (hcont.intervalIntegrable x y)
  have hx0 : 0 ≤ x * (x ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ) :=
    mul_nonneg hx (Real.rpow_nonneg (p_pos ha x).le _)
  have hy : y * (y ^ 2 / 4 + a) ^ (-(1 / 2) : ℝ) < 2 :=
    (abs_lt.mp (abs_bar_antideriv_lt ha y)).2
  have hmul : ∫ t in x..y, a * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ 2 := by
    rw [hint]; linarith
  rw [intervalIntegral.integral_const_mul] at hmul
  rw [le_div_iff₀ ha]
  linarith

lemma integrableOn_bar_rpow {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun t : ℝ => (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) (Ioi c) := by
  have hcont : Continuous (fun t : ℝ => (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) :=
    Continuous.rpow_const (by continuity) (fun t => Or.inl (p_pos ha t).ne')
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (4 / a) c
    (fun _ => hcont.integrableOn_Ioc) tendsto_id ?_
  filter_upwards [Filter.eventually_ge_atTop c] with i hi
  calc ∫ t in c..i, ‖(t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)‖
      = ∫ t in c..i, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with t ht
        exact Real.norm_of_nonneg (Real.rpow_nonneg (p_pos ha t).le _)
    _ ≤ 4 / a := intervalIntegral_bar_rpow_le ha hi

lemma integrableOn_abs_errorDensity_bar {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun t => |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|) (Ioi c) := by
  refine ((integrableOn_bar_rpow ha c).const_mul (5 / 16 : ℝ)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    refine continuous_abs.comp ?_
    unfold LiouvilleGreen.errorDensity
    refine (((continuous_const.mul ((continuous_id.div_const 2).pow 2)).mul
      (Continuous.rpow_const (by continuity) (fun t => Or.inl (p_pos ha t).ne'))).sub
      ((continuous_const.mul continuous_const).mul
      (Continuous.rpow_const (by continuity) (fun t => Or.inl (p_pos ha t).ne')))).sub
      (continuous_const.mul
      (Continuous.rpow_const (by continuity) (fun t => Or.inl (p_pos ha t).ne')))
  · filter_upwards with t
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact abs_errorDensity_bar_le ha t

lemma integral_abs_errorDensity_bar_le {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| ≤ 5 / (4 * a) := by
  have hint : IntegrableOn (fun t : ℝ => 5 / 16 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) (Ioi x) :=
    (integrableOn_bar_rpow ha x).const_mul (5 / 16)
  have hlim : Tendsto (fun b : ℝ => ∫ t in x..b, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ))
      atTop (𝓝 (∫ t in Ioi x, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ))) :=
    intervalIntegral_tendsto_integral_Ioi x (integrableOn_bar_rpow ha x) tendsto_id
  have hIoi : ∫ t in Ioi x, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ 4 / a :=
    le_of_tendsto hlim (by
      filter_upwards [Filter.eventually_ge_atTop x] with b hb
      exact intervalIntegral_bar_rpow_le ha hb)
  calc ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
        (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|
      ≤ ∫ t in Ioi x, 5 / 16 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by
        refine setIntegral_mono_on (integrableOn_abs_errorDensity_bar ha x) hint
          measurableSet_Ioi (fun t _ => abs_errorDensity_bar_le ha t)
    _ = 5 / 16 * ∫ t in Ioi x, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ 5 / 16 * (4 / a) := by gcongr
    _ = 5 / (4 * a) := by ring

lemma integral_abs_errorDensity_bar_nonneg_le {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| ≤ 5 / (8 * a) := by
  have hint : IntegrableOn (fun t : ℝ => 5 / 16 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) (Ioi x) :=
    (integrableOn_bar_rpow ha x).const_mul (5 / 16)
  have hlim : Tendsto (fun b : ℝ => ∫ t in x..b, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ))
      atTop (𝓝 (∫ t in Ioi x, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ))) :=
    intervalIntegral_tendsto_integral_Ioi x (integrableOn_bar_rpow ha x) tendsto_id
  have hIoi : ∫ t in Ioi x, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ 2 / a :=
    le_of_tendsto hlim (by
      filter_upwards [Filter.eventually_ge_atTop x] with b hb
      exact intervalIntegral_bar_rpow_nonneg_le ha hx hb)
  calc ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
        (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|
      ≤ ∫ t in Ioi x, 5 / 16 * (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by
        refine setIntegral_mono_on (integrableOn_abs_errorDensity_bar ha x) hint
          measurableSet_Ioi (fun t _ => abs_errorDensity_bar_le ha t)
    _ = 5 / 16 * ∫ t in Ioi x, (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ 5 / 16 * (2 / a) := by gcongr
    _ = 5 / (8 * a) := by ring

/-! ### Constants, `k2`, `Mbal`, `Ebar` lemmas for `a ≥ 1` -/

lemma k2_eq_of_ge_one {a : ℝ} (ha : 1 ≤ a) (z : ℝ) : k2 a z = z ^ 2 / 4 + a := by
  unfold k2
  have ha0 : 0 ≤ a := by linarith
  have hp : 0 ≤ z ^ 2 / 4 + a := by positivity
  rw [abs_of_nonneg hp, abs_of_nonneg ha0, max_eq_left ha]
  have h1 : a ^ ((1 : ℝ) / 3) ≤ a := by
    calc a ^ ((1 : ℝ) / 3) ≤ a ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
      _ = a := Real.rpow_one a
  exact max_eq_left (by linarith [sq_nonneg z])

lemma Mbal_eq_of_ge_one {a : ℝ} (ha : 1 ≤ a) (z : ℝ) :
    Mbal a z = (z ^ 2 / 4 + a) ^ (-(1 / 4) : ℝ) := by
  unfold Mbal
  rw [k2_eq_of_ge_one ha z]
  norm_num

lemma exp_five_eighths_lt_two : Real.exp (5 / 8 : ℝ) < 2 := by
  have hlog : (5 / 8 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  calc Real.exp (5 / 8 : ℝ) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlog
    _ = 2 := Real.exp_log (by norm_num)

lemma exp_five_sixteenths_lt : Real.exp (5 / 16 : ℝ) < 3 / 2 := by
  have hsq : Real.exp (5 / 16 : ℝ) ^ 2 < (3 / 2 : ℝ) ^ 2 := by
    rw [sq, ← Real.exp_add]
    calc Real.exp (5 / 16 + 5 / 16 : ℝ) = Real.exp (5 / 8 : ℝ) := by norm_num
      _ < 2 := exp_five_eighths_lt_two
      _ < (3 / 2 : ℝ) ^ 2 := by norm_num
  nlinarith [Real.exp_pos (5 / 16 : ℝ)]

lemma Ebar_neg (a z : ℝ) : Ebar a (-z) = (Ebar a z)⁻¹ := by
  unfold Ebar
  rw [← Real.exp_neg]
  congr 1
  have hsub : ∫ t in (0 : ℝ)..(-z), Real.sqrt (t ^ 2 / 4 + a) =
      - ∫ t in (0 : ℝ)..z, Real.sqrt (t ^ 2 / 4 + a) := by
    rw [intervalIntegral.integral_symm (-z) 0]
    congr 1
    have hcomp := (intervalIntegral.integral_comp_neg
      (f := fun t => Real.sqrt (t ^ 2 / 4 + a)) (a := (0 : ℝ)) (b := z)).symm
    simp_rw [neg_zero, neg_sq] at hcomp
    exact hcomp
  linarith

lemma k2_neg (a z : ℝ) : k2 a (-z) = k2 a z := by
  unfold k2
  simp

lemma Mbal_neg (a z : ℝ) : Mbal a (-z) = Mbal a z := by
  unfold Mbal
  rw [k2_neg]

/-! ### Decay of `pcUD a` as `x → +∞` -/

lemma tendsto_pcU_mul_linear (a : ℝ) (ha : -1 / 2 < a) :
    Tendsto (fun x : ℝ => (1 + x) * pcU a x) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := pcU_decay_bound 0 a (by linarith)
  have hb : Tendsto (fun x : ℝ => |C| * ((1 + x) * Real.exp (-(1 / 4) * x))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x * Real.exp (-(1 / 4) * x)) atTop (𝓝 0) := by
      simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 4) (by norm_num)
    have h2 : Tendsto (fun x : ℝ => Real.exp (-(1 / 4) * x)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
    have h3 : Tendsto (fun x : ℝ => (1 + x) * Real.exp (-(1 / 4) * x)) atTop (𝓝 0) := by
      simpa [add_mul] using h2.add h1
    simpa [mul_zero] using h3.const_mul |C|
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 ≤ 1 + x := by linarith
  dsimp only [Function.comp_apply]
  rw [abs_mul, abs_of_nonneg hx1]
  have hcx := hC x hx0
  simp only [pow_zero, mul_one] at hcx
  have hexp : Real.exp (-x ^ 2 / 4) ≤ Real.exp (-(1 / 4) * x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc (1 + x) * |pcU a x|
      ≤ (1 + x) * (C * Real.exp (-x ^ 2 / 4)) := by gcongr
    _ ≤ (1 + x) * (|C| * Real.exp (-(1 / 4) * x)) := by
        gcongr; exact le_abs_self _
    _ = |C| * ((1 + x) * Real.exp (-(1 / 4) * x)) := by ring

lemma tendsto_pcUD (a : ℝ) (ha : 1 ≤ a) : Tendsto (pcUD a) atTop (𝓝 0) := by
  have heq : pcUD a = fun x => x / 2 * pcU a x - pcU (a - 1) x := by
    ext x
    have h := pc_shift_U_dn a x
    rw [deriv_pcU] at h
    linarith
  rw [heq]
  have h1 : Tendsto (fun x : ℝ => x / 2 * pcU a x) atTop (𝓝 0) := by
    have hmul := tendsto_pcU_mul_linear a (by linarith)
    rw [tendsto_zero_iff_abs_tendsto_zero] at hmul ⊢
    refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hmul
    filter_upwards [eventually_ge_atTop 0] with x hx
    dsimp only [Function.comp_apply]
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x / 2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + x)]
    gcongr
    linarith
  have h2 : Tendsto (pcU (a - 1)) atTop (𝓝 0) := tendsto_pcU (a - 1)
  simpa using h1.sub h2

/-! ### E4bar: `env_bar` for `a ≥ 1`, all `z` -/

/-- First conjunct of `PCEnvelopeFacts.env_bar` for `pcU`, `1 ≤ a`, and any `z : ℝ`,
with absolute constant `20`. -/
theorem pc_env_bar_first_ge_one {a : ℝ} (ha : 1 ≤ a) (z : ℝ) :
    Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
      20 * Ebar a z * Mbal a z := by
  have ha0 : 0 < a := by linarith
  set L : ℝ := min z 0 - 1
  have hLz : L < z := by dsimp [L]; linarith [min_le_left z 0]
  have hL0 : L < 0 := by dsimp [L]; linarith [min_le_right z 0]
  let p : ℝ → ℝ := fun t => t ^ 2 / 4 + a
  let p' : ℝ → ℝ := fun t => t / 2
  let p'' : ℝ → ℝ := fun _ => 1 / 2
  let g : ℝ → ℝ := fun _ => 0
  let ξ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, Real.sqrt (p s)
  have hp_pos : ∀ x, L < x → 0 < p x := fun x _ => p_pos ha0 x
  have hp' : ∀ x, L < x → HasDerivAt p (p' x) x := fun x _ => by
    have := ((hasDerivAt_pow 2 x).div_const 4).add_const a
    refine this.congr_deriv ?_
    dsimp [p']
    ring
  have hp'' : ∀ x, L < x → HasDerivAt p' (p'' x) x := fun x _ => by
    simpa [p', p''] using (hasDerivAt_id x).div_const 2
  have hp''c : ContinuousOn p'' (Ioi L) := continuousOn_const
  have hgc : ContinuousOn g (Ioi L) := continuousOn_const
  have hξ_deriv : ∀ x : ℝ, HasDerivAt ξ (Real.sqrt (p x)) x := fun x => by
    have hcont : Continuous (fun s => Real.sqrt (p s)) :=
      Real.continuous_sqrt.comp (by continuity)
    exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 x)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  obtain ⟨ε, ε', w', hLG⟩ := LiouvilleGreen.exists_solution_exp_of_pos (a := L) (u := 1)
    one_pos hp_pos hp' hp'' hp''c hgc (fun x _ => hξ_deriv x)
    (fun c _ => integrableOn_abs_errorDensity_bar ha0 c)
  let w : ℝ → ℝ := fun y => p y ^ (-(1 / 4) : ℝ) * Real.exp (-ξ y) * (1 + ε y)
  have hw_deriv : ∀ x, L < x → HasDerivAt w (w' x) x := fun x hx => by
    simpa [w, one_mul] using (hLG x hx).2.1
  have hw'_deriv : ∀ x, L < x → HasDerivAt w' (p x * w x) x := fun x hx => by
    simpa [w, g, one_mul] using (hLG x hx).2.2.1
  have hε_bd : ∀ x, L < x → |ε x| < 1 := fun x hx => by
    have h1 := (hLG x hx).2.2.2.1
    have hV : ∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t| ≤ 5 / (4 * a) :=
      integral_abs_errorDensity_bar_le ha0 x
    have hV' : (∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 8 := by
      have : 5 / (4 * a) / (2 * 1) ≤ 5 / 8 := by
        rw [div_div]
        have : (5 : ℝ) / (4 * a * 2) ≤ 5 / 8 := by
          gcongr
          linarith
        linarith
      linarith [div_le_div_of_nonneg_right hV (by norm_num : (0 : ℝ) ≤ 2 * 1)]
    have hexp : Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) < 2 :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr hV') exp_five_eighths_lt_two
    linarith
  have hε0_bd : |ε 0| < 1 / 2 := by
    have h1 := (hLG 0 hL0).2.2.2.1
    have hV : ∫ t in Ioi 0, |LiouvilleGreen.errorDensity p p' p'' g t| ≤ 5 / (8 * a) :=
      integral_abs_errorDensity_bar_nonneg_le ha0 (le_refl 0)
    have hV' : (∫ t in Ioi 0, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 16 := by
      have : 5 / (8 * a) / (2 * 1) ≤ 5 / 16 := by
        rw [div_div]
        have : (5 : ℝ) / (8 * a * 2) ≤ 5 / 16 := by
          gcongr
          linarith
        linarith
      linarith [div_le_div_of_nonneg_right hV (by norm_num : (0 : ℝ) ≤ 2 * 1)]
    have hexp : Real.exp ((∫ t in Ioi 0, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) < 3 / 2 :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr hV') exp_five_sixteenths_lt
    linarith
  have hw_pos : ∀ x, L < x → 0 < w x := fun x hx => by
    have h1 : 0 < 1 + ε x := by linarith [(abs_lt.mp (hε_bd x hx)).1]
    have h2 : 0 < p x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos (hp_pos x hx) _
    have h3 : 0 < Real.exp (-ξ x) := Real.exp_pos _
    positivity
  -- Explicit formula for `w'`
  have hw'_eq : ∀ x, L < x →
      w' x = p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) *
        ((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x) := by
    intro x hx
    have hpx := hp_pos x hx
    have hA : HasDerivAt (fun y => p y ^ (-(1 / 4) : ℝ))
        (p x ^ (-(1 / 4) : ℝ) * (-(1 / 4) * (x / 2) / p x)) x := by
      refine ((hp' x hx).rpow_const (p := -(1 / 4)) (Or.inl hpx.ne')).congr_deriv ?_
      have hsub : p x ^ (-(1 / 4) - 1 : ℝ) = p x ^ (-(1 / 4) : ℝ) * (p x)⁻¹ := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hpx]
        norm_num
      rw [hsub]
      simp only [p']
      ring
    have hE : HasDerivAt (fun y => Real.exp (-ξ y))
        (Real.exp (-ξ x) * (-Real.sqrt (p x))) x := by
      simpa using (hξ_deriv x).neg.exp
    have hAE : HasDerivAt (fun y => p y ^ (-(1 / 4) : ℝ) * Real.exp (-ξ y))
        (p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) *
          (-(1 / 4) * (x / 2) / p x - Real.sqrt (p x))) x := by
      refine (hA.mul hE).congr_deriv ?_
      ring
    have hfull : HasDerivAt w
        (p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) *
          ((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x)) x := by
      have h1ε : HasDerivAt (fun y => 1 + ε y) (ε' x) x :=
        (hLG x hx).1.const_add 1
      refine (hAE.mul h1ε).congr_deriv ?_
      ring
    exact (hw_deriv x hx).unique hfull
  -- Wronskian `W(x) = pcU a x * w' x - pcUD a x * w x` is 0 on `(L, ∞)`
  let W : ℝ → ℝ := fun x => pcU a x * w' x - pcUD a x * w x
  have hW_deriv : ∀ x, L < x → HasDerivAt W 0 x := fun x hx => by
    have hU := hasDerivAt_pcU a x
    have hUD : HasDerivAt (pcUD a) (p x * pcU a x) x := by
      simpa [p] using hasDerivAt_pcUD a x
    have h1 := hU.mul (hw'_deriv x hx)
    have h2 := hUD.mul (hw_deriv x hx)
    refine (h1.sub h2).congr_deriv ?_
    ring
  have hW_const : ∀ x, L < x → W x = W 0 := fun x hx =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun y hy => (hW_deriv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hW_deriv y hy).deriv) hx hL0
  -- Limit of `W x` as `x → +∞` is `0`
  have hW_tendsto : Tendsto W atTop (𝓝 0) := by
    have hw_bd : ∀ x : ℝ, 0 ≤ x → |w x| ≤ 2 := fun x hx => by
      have hpx : 1 ≤ p x := by dsimp [p]; linarith [sq_nonneg x]
      have hp14 : p x ^ (-(1 / 4) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hpx (by norm_num)
      have hξ0 : 0 ≤ ξ x := by
        dsimp [ξ]
        exact intervalIntegral.integral_nonneg hx (fun t _ => Real.sqrt_nonneg _)
      have hexp : Real.exp (-ξ x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h1ε : |1 + ε x| ≤ 2 := by
        have := hε_bd x (lt_of_lt_of_le hL0 hx)
        rw [abs_lt] at this
        rw [abs_le]
        constructor <;> linarith
      rw [show w x = p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) * (1 + ε x) from rfl,
        abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (p_pos ha0 x) _),
        abs_of_pos (Real.exp_pos _)]
      calc p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) * |1 + ε x|
          ≤ 1 * 1 * 2 := by gcongr
        _ = 2 := by ring
    have hw'_bd : ∀ x : ℝ, 0 ≤ x → |w' x| ≤ 5 * (1 + x + a) := fun x hx => by
      have hxL : L < x := lt_of_lt_of_le hL0 hx
      rw [hw'_eq x hxL]
      have hpx : 1 ≤ p x := by dsimp [p]; linarith [sq_nonneg x]
      have hp14 : p x ^ (-(1 / 4) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hpx (by norm_num)
      have hξ0 : 0 ≤ ξ x := by
        dsimp [ξ]
        exact intervalIntegral.integral_nonneg hx (fun t _ => Real.sqrt_nonneg _)
      have hexp : Real.exp (-ξ x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hsqp : Real.sqrt (p x) ≤ 1 + x + a := by
        have hle : p x ≤ (1 + x + a) ^ 2 := by
          dsimp [p]
          nlinarith [sq_nonneg x]
        calc Real.sqrt (p x) ≤ Real.sqrt ((1 + x + a) ^ 2) := Real.sqrt_le_sqrt hle
          _ = 1 + x + a := Real.sqrt_sq (by linarith)
      have hp_frac : |-(1 / 4) * (x / 2) / p x| ≤ 1 := by
        rw [abs_div, abs_of_pos (p_pos ha0 x), div_le_one (p_pos ha0 x),
          abs_of_nonpos (by nlinarith : -(1 / 4 : ℝ) * (x / 2) ≤ 0)]
        nlinarith [sq_nonneg (x - 1)]
      have h1ε : |1 + ε x| ≤ 2 := by
        have := abs_lt.mp (hε_bd x hxL)
        rw [abs_le]; constructor <;> linarith
      have hε' : |ε' x| ≤ 2 * Real.sqrt (p x) := by
        have h2 := (hLG x hxL).2.2.2.2
        have h1 := (hLG x hxL).2.2.2.1
        have hV : ∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t| ≤ 5 / (4 * a) :=
          integral_abs_errorDensity_bar_le ha0 x
        have hV' : (∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 8 := by
          have : (5 : ℝ) / (4 * a) / (2 * 1) ≤ 5 / 8 := by
            rw [div_div]
            gcongr
            linarith
          linarith [div_le_div_of_nonneg_right hV (by norm_num : (0 : ℝ) ≤ 2 * 1)]
        have hexp2 : Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1 ≤ 1 := by
          linarith [Real.exp_le_exp.mpr hV', exp_five_eighths_lt_two]
        calc |ε' x| ≤ 2 * 1 * Real.sqrt (p x) *
              (Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1) := h2
          _ ≤ 2 * 1 * Real.sqrt (p x) * 1 := by gcongr
          _ = 2 * Real.sqrt (p x) := by ring
      have hterm : |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x| ≤
          5 * (1 + x + a) := by
        have hsub : |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)| ≤ 1 + Real.sqrt (p x) := by
          calc |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)|
              ≤ |-(1 / 4) * (x / 2) / p x| + |Real.sqrt (p x)| := abs_sub _ _
            _ ≤ 1 + Real.sqrt (p x) := by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith
        calc |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x|
            ≤ |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x)| + |ε' x| := abs_add_le _ _
          _ = |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)| * |1 + ε x| + |ε' x| := by rw [abs_mul]
          _ ≤ (1 + Real.sqrt (p x)) * 2 + 2 * Real.sqrt (p x) := by gcongr
          _ = 2 + 4 * Real.sqrt (p x) := by ring
          _ ≤ 2 + 4 * (1 + x + a) := by gcongr
          _ ≤ 5 * (1 + x + a) := by linarith
      rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (p_pos ha0 x) _),
        abs_of_pos (Real.exp_pos _)]
      calc p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) *
            |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x|
          ≤ 1 * 1 * (5 * (1 + x + a)) := by gcongr
        _ = 5 * (1 + x + a) := by ring
    have ht1 : Tendsto (fun x : ℝ => pcU a x * w' x) atTop (𝓝 0) := by
      have hlin : Tendsto (fun x : ℝ => 5 * (1 + a) * |(1 + x) * pcU a x|) atTop (𝓝 0) := by
        have h0 := (tendsto_pcU_mul_linear a (by linarith)).abs.const_mul (5 * (1 + a))
        simpa [mul_zero] using h0
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlin
      filter_upwards [eventually_ge_atTop 0] with x hx
      dsimp only [Function.comp_apply]
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + x)]
      have hbd := hw'_bd x hx
      have hle : 1 + x + a ≤ (1 + a) * (1 + x) := by nlinarith
      calc |pcU a x| * |w' x|
          ≤ |pcU a x| * (5 * (1 + x + a)) := by gcongr
        _ ≤ |pcU a x| * (5 * ((1 + a) * (1 + x))) := by gcongr
        _ = 5 * (1 + a) * ((1 + x) * |pcU a x|) := by ring
    have ht2 : Tendsto (fun x : ℝ => pcUD a x * w x) atTop (𝓝 0) := by
      have hlin : Tendsto (fun x : ℝ => 2 * |pcUD a x|) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_pcUD a ha).abs.const_mul 2
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlin
      filter_upwards [eventually_ge_atTop 0] with x hx
      dsimp only [Function.comp_apply]
      rw [abs_mul]
      calc |pcUD a x| * |w x| ≤ |pcUD a x| * 2 := by gcongr; exact hw_bd x hx
        _ = 2 * |pcUD a x| := by ring
    simpa [W] using ht1.sub ht2
  have hW_zero : ∀ x, L < x → W x = 0 := by
    have hW0 : W 0 = 0 := by
      have hconst : Tendsto W atTop (𝓝 (W 0)) :=
        tendsto_const_nhds.congr' (by filter_upwards [eventually_gt_atTop 0] with x hx; exact (hW_const x (lt_trans hL0 hx)).symm)
      exact tendsto_nhds_unique hconst hW_tendsto
    intro x hx
    rw [hW_const x hx, hW0]
  -- Hence `pcU a x / w x` is constant on `(L, ∞)`
  have hdiv_deriv : ∀ x, L < x → HasDerivAt (fun y => pcU a y / w y) 0 x := fun x hx => by
    have hw0 : w x ≠ 0 := (hw_pos x hx).ne'
    have hq := (hasDerivAt_pcU a x).div (hw_deriv x hx) hw0
    refine hq.congr_deriv ?_
    have hWx := hW_zero x hx
    dsimp [W] at hWx
    rw [show pcUD a x * w x - pcU a x * w' x = -(pcU a x * w' x - pcUD a x * w x) by ring,
      hWx, neg_zero, zero_div]
  let c : ℝ := pcU a 0 / w 0
  have hpcU_eq : ∀ x, L < x → pcU a x = c * w x := fun x hx => by
    have hconst : pcU a x / w x = pcU a 0 / w 0 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun y hy => (hdiv_deriv y hy).differentiableAt.differentiableWithinAt)
        (fun y hy => (hdiv_deriv y hy).deriv) hx hL0
    dsimp [c]
    rw [← hconst]
    exact (div_mul_cancel₀ (pcU a x) (hw_pos x hx).ne').symm
  have hpcUD_eq : ∀ x, L < x → deriv (pcU a) x = c * w' x := fun x hx => by
    have h1 : HasDerivAt (fun y => c * w y) (c * w' x) x := (hw_deriv x hx).const_mul c
    have h2 : HasDerivAt (pcU a) (c * w' x) x := h1.congr_of_eventuallyEq (by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact hpcU_eq y hy)
    exact h2.deriv
  -- Bound `w(x)^2 + w'(x)^2 / k2 a x` for all `x > L`
  have hw_env : ∀ x, L < x →
      Real.sqrt (w x ^ 2 + w' x ^ 2 / k2 a x) ≤ 5 * Ebar a x * Mbal a x := fun x hx => by
    have hpx := hp_pos x hx
    have hk2 : k2 a x = p x := k2_eq_of_ge_one ha x
    have hM : Mbal a x = p x ^ (-(1 / 4) : ℝ) := Mbal_eq_of_ge_one ha x
    have hE : Ebar a x = Real.exp (-ξ x) := rfl
    rw [hk2, hw'_eq x hx]
    set A : ℝ := p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x)
    have hA_pos : 0 < A := mul_pos (Real.rpow_pos_of_pos hpx _) (Real.exp_pos _)
    have h1ε : |1 + ε x| ≤ 2 := by
      have := abs_lt.mp (hε_bd x hx)
      rw [abs_le]; constructor <;> linarith
    have hV : (∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 8 := by
      have hV0 : ∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t| ≤ 5 / (4 * a) :=
        integral_abs_errorDensity_bar_le ha0 x
      have : 5 / (4 * a) / (2 * 1) ≤ 5 / 8 := by
        rw [div_div]
        have : (5 : ℝ) / (4 * a * 2) ≤ 5 / 8 := by gcongr; linarith
        linarith
      linarith [div_le_div_of_nonneg_right hV0 (by norm_num : (0 : ℝ) ≤ 2 * 1)]
    have hε' : |ε' x| ≤ 2 * Real.sqrt (p x) := by
      have h2 := (hLG x hx).2.2.2.2
      have hexp2 : Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1 ≤ 1 :=
        by linarith [Real.exp_le_exp.mpr hV, exp_five_eighths_lt_two]
      calc |ε' x| ≤ 2 * 1 * Real.sqrt (p x) *
            (Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1) := h2
        _ ≤ 2 * 1 * Real.sqrt (p x) * 1 := by gcongr
        _ = 2 * Real.sqrt (p x) := by ring
    -- Bound `|(-(1/4)*(x/2)/p x - sqrt(p x))*(1 + ε x) + ε' x| / sqrt(p x) ≤ 9/2`
    have hsqp_pos : 0 < Real.sqrt (p x) := Real.sqrt_pos.mpr hpx
    have hterm_bd : |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x| ≤
        9 / 2 * Real.sqrt (p x) := by
      have hx_le_sqp : |x / 2| ≤ Real.sqrt (p x) := by
        rw [← Real.sqrt_sq_eq_abs]
        apply Real.sqrt_le_sqrt
        dsimp [p]
        linarith [show (x / 2) ^ 2 = x ^ 2 / 4 by ring]
      have hp1 : 1 ≤ p x := by dsimp [p]; linarith [sq_nonneg x]
      have hfrac : |-(1 / 4) * (x / 2) / p x| ≤ 1 / 4 * Real.sqrt (p x) := by
        rw [abs_div, abs_mul, abs_of_pos hpx, div_le_iff₀ hpx]
        have : |-(1 / 4 : ℝ)| = 1 / 4 := by norm_num
        rw [this]
        calc 1 / 4 * |x / 2| ≤ 1 / 4 * Real.sqrt (p x) := by gcongr
          _ ≤ 1 / 4 * Real.sqrt (p x) * p x := le_mul_of_one_le_right (by positivity) hp1
      have hsub : |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)| ≤ 5 / 4 * Real.sqrt (p x) := by
        calc |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)|
            ≤ |-(1 / 4) * (x / 2) / p x| + |Real.sqrt (p x)| := abs_sub _ _
          _ ≤ 1 / 4 * Real.sqrt (p x) + Real.sqrt (p x) := by
              rw [abs_of_nonneg hsqp_pos.le]; gcongr
          _ = 5 / 4 * Real.sqrt (p x) := by ring
      calc |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x|
          ≤ |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x)| + |ε' x| := abs_add_le _ _
        _ = |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)| * |1 + ε x| + |ε' x| := by rw [abs_mul]
        _ ≤ (5 / 4 * Real.sqrt (p x)) * 2 + 2 * Real.sqrt (p x) := by gcongr
        _ = 9 / 2 * Real.sqrt (p x) := by ring
    have hsq_bd : w x ^ 2 + (A * ((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x)) ^ 2 / p x ≤
        (5 * A) ^ 2 := by
      have hw_sq : w x ^ 2 ≤ A ^ 2 * 4 := by
        change (A * (1 + ε x)) ^ 2 ≤ A ^ 2 * 4
        rw [mul_pow]
        have : (1 + ε x) ^ 2 ≤ 4 := by
          rw [← sq_abs]
          nlinarith [abs_nonneg (1 + ε x), h1ε]
        gcongr
      have hterm_sq : (A * ((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x)) ^ 2 / p x ≤
          A ^ 2 * (81 / 4) := by
        have h1 : ((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x) ^ 2 ≤
            (9 / 2) ^ 2 * p x := by
          rw [← sq_abs]
          calc |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x| ^ 2
              ≤ (9 / 2 * Real.sqrt (p x)) ^ 2 := by gcongr
            _ = (9 / 2) ^ 2 * (Real.sqrt (p x)) ^ 2 := by ring
            _ = (9 / 2) ^ 2 * p x := by rw [Real.sq_sqrt hpx.le]
        rw [mul_pow, mul_div_assoc]
        calc A ^ 2 * (((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x) ^ 2 / p x)
            ≤ A ^ 2 * (((9 / 2) ^ 2 * p x) / p x) := by gcongr
          _ = A ^ 2 * (81 / 4) := by field_simp [hpx.ne']; ring
      nlinarith [sq_nonneg A]
    calc Real.sqrt (w x ^ 2 + (A * ((-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x)) ^ 2 / p x)
        ≤ Real.sqrt ((5 * A) ^ 2) := Real.sqrt_le_sqrt hsq_bd
      _ = 5 * A := Real.sqrt_sq (by positivity)
      _ = 5 * Ebar a x * Mbal a x := by
          dsimp [A]; rw [hE, hM]; ring
  -- Bound `kappaBal a * |c| ≤ 4` at `x = 0`
  have hc_bd : kappaBal a * |c| ≤ 4 := by
    have h0 := (origin_env_bar ha0).2.1
    have hκ := kappaBal_pos a
    have hM0 := Mbal_pos a 0
    have hE0 : Ebar a 0 = 1 := Ebar_zero a
    have hw0_lb : 1 / 2 * (Ebar a 0 * Mbal a 0) ≤ Real.sqrt (w 0 ^ 2 + w' 0 ^ 2 / k2 a 0) := by
      have hw0_eq : w 0 = 1 * Mbal a 0 * (1 + ε 0) := by
        dsimp [w]
        rw [Mbal_eq_of_ge_one ha 0]
        have hξ0 : ξ 0 = 0 := by dsimp [ξ]; simp
        rw [hξ0, neg_zero, Real.exp_zero, one_mul, mul_one]
      have h1ε0 : 1 / 2 ≤ 1 + ε 0 := by linarith [(abs_lt.mp hε0_bd).1]
      have hw0_pos : 0 ≤ w 0 := (hw_pos 0 hL0).le
      calc 1 / 2 * (Ebar a 0 * Mbal a 0)
          = 1 * Mbal a 0 * (1 / 2) := by rw [hE0]; ring
        _ ≤ 1 * Mbal a 0 * (1 + ε 0) := by gcongr
        _ = w 0 := hw0_eq.symm
        _ = Real.sqrt (w 0 ^ 2) := (Real.sqrt_sq hw0_pos).symm
        _ ≤ Real.sqrt (w 0 ^ 2 + w' 0 ^ 2 / k2 a 0) := by
            apply Real.sqrt_le_sqrt
            linarith [div_nonneg (sq_nonneg (w' 0)) (k2_pos a 0).le]
    have hscale : Real.sqrt ((kappaBal a * pcU a 0) ^ 2 + (kappaBal a * deriv (pcU a) 0) ^ 2 / k2 a 0) =
        (kappaBal a * |c|) * Real.sqrt (w 0 ^ 2 + w' 0 ^ 2 / k2 a 0) := by
      rw [hpcU_eq 0 hL0, hpcUD_eq 0 hL0]
      have hk0 : 0 ≤ kappaBal a * |c| := mul_nonneg hκ.le (abs_nonneg c)
      calc Real.sqrt ((kappaBal a * (c * w 0)) ^ 2 + (kappaBal a * (c * w' 0)) ^ 2 / k2 a 0)
          = Real.sqrt ((kappaBal a * |c|) ^ 2 * (w 0 ^ 2 + w' 0 ^ 2 / k2 a 0)) := by
            congr 1; simp only [mul_pow, sq_abs]; ring
        _ = Real.sqrt ((kappaBal a * |c|) ^ 2) * Real.sqrt (w 0 ^ 2 + w' 0 ^ 2 / k2 a 0) :=
            Real.sqrt_mul (sq_nonneg _) _
        _ = (kappaBal a * |c|) * Real.sqrt (w 0 ^ 2 + w' 0 ^ 2 / k2 a 0) := by
            rw [Real.sqrt_sq hk0]
    rw [hscale] at h0
    have hEM : 0 < Ebar a 0 * Mbal a 0 := by rw [hE0, one_mul]; exact hM0
    have h1 : kappaBal a * |c| * (1 / 2 * (Ebar a 0 * Mbal a 0)) ≤
        kappaBal a * |c| * Real.sqrt (w 0 ^ 2 + w' 0 ^ 2 / k2 a 0) := by
      gcongr
    have h2 : kappaBal a * |c| * (1 / 2 * (Ebar a 0 * Mbal a 0)) ≤ 2 * (Ebar a 0 * Mbal a 0) :=
      h1.trans h0
    have h3 : (kappaBal a * |c| * (1 / 2)) * (Ebar a 0 * Mbal a 0) ≤ 2 * (Ebar a 0 * Mbal a 0) := by
      linarith
    have h4 := le_of_mul_le_mul_right h3 hEM
    linarith
  -- Combine at `z`
  have hscale_z : Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) =
      (kappaBal a * |c|) * Real.sqrt (w z ^ 2 + w' z ^ 2 / k2 a z) := by
    rw [hpcU_eq z hLz, hpcUD_eq z hLz]
    have hκ := kappaBal_pos a
    have hk0 : 0 ≤ kappaBal a * |c| := mul_nonneg hκ.le (abs_nonneg c)
    calc Real.sqrt ((kappaBal a * (c * w z)) ^ 2 + (kappaBal a * (c * w' z)) ^ 2 / k2 a z)
        = Real.sqrt ((kappaBal a * |c|) ^ 2 * (w z ^ 2 + w' z ^ 2 / k2 a z)) := by
          congr 1; simp only [mul_pow, sq_abs]; ring
      _ = Real.sqrt ((kappaBal a * |c|) ^ 2) * Real.sqrt (w z ^ 2 + w' z ^ 2 / k2 a z) :=
          Real.sqrt_mul (sq_nonneg _) _
      _ = (kappaBal a * |c|) * Real.sqrt (w z ^ 2 + w' z ^ 2 / k2 a z) := by
          rw [Real.sqrt_sq hk0]
  rw [hscale_z]
  have hwz := hw_env z hLz
  calc (kappaBal a * |c|) * Real.sqrt (w z ^ 2 + w' z ^ 2 / k2 a z)
      ≤ 4 * (5 * Ebar a z * Mbal a z) := by gcongr
    _ = 20 * Ebar a z * Mbal a z := by ring

/-- The two inequalities of `PCEnvelopeFacts.env_bar` for the actual `pcU`, for all `1 ≤ a`
and all `z : ℝ`, with the absolute constant `C = 20`. -/
theorem pc_env_bar_ge_one :
    ∃ C : ℝ, 0 < C ∧ ∀ a, 1 ≤ a → ∀ z,
      Real.sqrt ((kappaBal a * pcU a z) ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
        C * Ebar a z * Mbal a z ∧
      Real.sqrt ((kappaBal a * pcU a (-z)) ^ 2 +
          (kappaBal a * deriv (fun w => pcU a (-w)) z) ^ 2 / k2 a z) ≤
        C * (Ebar a z)⁻¹ * Mbal a z := by
  refine ⟨20, by norm_num, fun a ha z => ?_⟩
  refine ⟨pc_env_bar_first_ge_one ha z, ?_⟩
  have hneg : deriv (fun w => pcU a (-w)) z = -deriv (pcU a) (-z) := by
    have h : HasDerivAt (fun w : ℝ => pcU a (-w)) (pcUD a (-z) * (-1)) z :=
      (hasDerivAt_pcU a (-z)).comp z (hasDerivAt_neg z)
    rw [h.deriv, deriv_pcU]
    ring
  rw [hneg, ← Ebar_neg a z, ← k2_neg a z, ← Mbal_neg a z]
  have hsq : (kappaBal a * -deriv (pcU a) (-z)) ^ 2 = (kappaBal a * deriv (pcU a) (-z)) ^ 2 := by
    ring
  rw [hsq]
  exact pc_env_bar_first_ge_one ha (-z)

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.pc_env_bar_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.pc_env_bar_ge_one

end FormalResearch.JacobiEigenvectors.Charts
