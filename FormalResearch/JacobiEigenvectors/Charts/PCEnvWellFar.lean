module

public import Mathlib
public import DLMFMathlib.Analysis.ODE.LiouvilleGreenReal
public import FormalResearch.JacobiEigenvectors.Charts.PCEnergyAiryEnv
public import FormalResearch.JacobiEigenvectors.Charts.PCPositive

/-!
# Paper J, Layer 4 (phase B2, E4-well): `env_well` beyond the Airy zone (`a ≤ -4`, `z ≥ z₂(a)`)

Proves two-sided `env_well` bounds for `pcU` and `pcV` when `a ≤ -4` (`A = -a ≥ 4`) and
`z2Airy a ≤ z`:

* E1 (`errorDensity_well`, `abs_errorDensity_well_le`, `integral_abs_errorDensity_well_le`):
  for `p(t) = t^2 / 4 + a` and `t > 2 * sqrt (-a)`,
  `errorDensity p p' p'' 0 t = (3/16 * p(t) + 5/16 * (-a)) * p(t)^{-5/2} ≤ (5/48) * (-t * p(t)^{-3/2})'`,
  so the total variation over `(x, ∞)` for `z2Airy a ≤ x` is at most `5 / 48`.
* Decay of `pcUD a` for every real `a` (`tendsto_pcU_mul_linear_all`, `tendsto_pcUD_all`).
* E4-U (`env_well_far_U`, `ut_pcU_well_far_lb`, `abs_deriv_pcU_le_well_far`):
  applying `LiouvilleGreen.exists_solution_exp_of_pos` on `(a₀, ∞)` with
  `a₀ = (2 * sqrt (-a) + z2Airy a) / 2 < z2Airy a`, identifying `pcU a` as a positive
  multiple of the recessive LG solution via the Wronskian, and normalising at `z2Airy a`
  via `PCEnergyAiryEnv.env_well_on_airy_U_V`.

* E4-V (`abs_vt_well_far_le`, `env_well_far_U_V`):
  integrating `(vt / ut)' = 1 / ut^2` from `z2Airy a` to `z` using `ut ≥ exp(-16) * Ewell * Mbal`
  and `(Ewell^{-2})' = 2 * sqrt(p) * Ewell^{-2}`, bounding `vt'` from `ut_vt_wronsk` and the
  derivative bound on `pcU`, and obtaining the lower bound from Cauchy-Schwarz and `ut_vt_wronsk`.
  Combined two-sided `env_well` bounds hold for `pcU` and `pcV` with explicit absolute constants
  `exp(-54)` and `exp(54)`.

What is NOT proved here: `a ∈ (-4, 0]` (compact range, E5), `molv_well`, `beyond` on `[2*sqrt(-a), z2Airy a]`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open MeasureTheory Set Real Filter Topology intervalIntegral

/-! ### E1: error-density and variation bounds for `p(t) = t^2 / 4 + a` (`a ≤ -4`) -/

lemma p_well_pos {a t : ℝ} (ha : a ≤ -4) (ht : 2 * Real.sqrt (-a) < t) :
    0 < t ^ 2 / 4 + a := by
  have hA0 : 0 ≤ -a := by linarith
  have hsq : (2 * Real.sqrt (-a)) ^ 2 < t ^ 2 := by
    nlinarith [Real.sqrt_nonneg (-a)]
  have h4 : (2 * Real.sqrt (-a)) ^ 2 = 4 * (-a) := by
    rw [mul_pow, Real.sq_sqrt hA0]; ring
  linarith

lemma errorDensity_well (a t : ℝ) (ha : a ≤ -4) (ht : 2 * Real.sqrt (-a) < t) :
    LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a) (fun s => s / 2)
        (fun _ => 1 / 2) (fun _ => 0) t =
      (3 / 16 * (t ^ 2 / 4 + a) + 5 / 16 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
  have hp : 0 < t ^ 2 / 4 + a := p_well_pos ha ht
  unfold LiouvilleGreen.errorDensity
  have h1 : (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) =
      (t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_one_add' hp.le (by norm_num)]
    norm_num
  rw [h1]
  ring

lemma hasDerivAt_well_antideriv {a t : ℝ} (ha : a ≤ -4) (ht : 2 * Real.sqrt (-a) < t) :
    HasDerivAt (fun s => -s * (s ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ))
      ((2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)) t := by
  have hp : 0 < t ^ 2 / 4 + a := p_well_pos ha ht
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2 / 4 + a) (t / 2) t := by
    have := ((hasDerivAt_pow 2 t).div_const 4).add_const a
    refine this.congr_deriv ?_
    ring
  have hrp := hsq.rpow_const (p := -(3 / 2)) (Or.inl hp.ne')
  have hprod := (hasDerivAt_id t).neg.mul hrp
  refine hprod.congr_deriv ?_
  have h1 : (t ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) =
      (t ^ 2 / 4 + a) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
    rw [← Real.rpow_one_add' hp.le (by norm_num)]
    norm_num
  have h2 : (-(3 / 2) - 1 : ℝ) = -(5 / 2) := by norm_num
  rw [h2, h1]
  simp only [Pi.neg_apply, id_eq]
  ring

lemma abs_errorDensity_well_le {a t : ℝ} (ha : a ≤ -4) (ht : 2 * Real.sqrt (-a) < t) :
    |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a) (fun s => s / 2)
        (fun _ => 1 / 2) (fun _ => 0) t| ≤
      5 / 48 * ((2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)) := by
  have hp : 0 < t ^ 2 / 4 + a := p_well_pos ha ht
  have hA : 0 < -a := by linarith
  have hrp : 0 < (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := Real.rpow_pos_of_pos hp _
  have hnum_nonneg : 0 ≤ 3 / 16 * (t ^ 2 / 4 + a) + 5 / 16 * (-a) := by positivity
  rw [errorDensity_well a t ha ht, abs_of_nonneg (mul_nonneg hnum_nonneg hrp.le)]
  have hle : 3 / 16 * (t ^ 2 / 4 + a) + 5 / 16 * (-a) ≤
      5 / 48 * (2 * (t ^ 2 / 4 + a) + 3 * (-a)) := by linarith
  calc (3 / 16 * (t ^ 2 / 4 + a) + 5 / 16 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)
      ≤ (5 / 48 * (2 * (t ^ 2 / 4 + a) + 3 * (-a))) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by gcongr
    _ = 5 / 48 * ((2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)) := by ring

lemma z2Airy_gt_turning {a : ℝ} (ha : a ≤ -4) : 2 * Real.sqrt (-a) < z2Airy a := by
  unfold z2Airy
  have hA : 0 < -a := by linarith
  have h13 : 0 < (-a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hA _
  gcongr
  linarith

lemma p_z2Airy_eq {a : ℝ} (ha : a ≤ -4) :
    (z2Airy a) ^ 2 / 4 + a = 2 * (-a) ^ ((1 : ℝ) / 3) := by
  unfold z2Airy
  have hA : 0 ≤ -a := by linarith
  have h13 : 0 ≤ (-a) ^ ((1 : ℝ) / 3) := by positivity
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  ring

lemma z2Airy_le_two_sqrt_two_mul_sqrt {a : ℝ} (ha : a ≤ -4) :
    z2Airy a ≤ 2 * Real.sqrt 2 * Real.sqrt (-a) := by
  have hA : 4 ≤ -a := by linarith
  have h2 : 2 * (-a) ^ ((1 : ℝ) / 3) ≤ -a := by
    linarith [two_mul_rpow_one_third_lt hA]
  unfold z2Airy
  have hA0 : 0 ≤ -a := by linarith
  calc 2 * Real.sqrt (-a + 2 * (-a) ^ ((1 : ℝ) / 3))
      ≤ 2 * Real.sqrt (2 * (-a)) := by gcongr; linarith
    _ = 2 * (Real.sqrt 2 * Real.sqrt (-a)) := by rw [Real.sqrt_mul (by norm_num)]
    _ = 2 * Real.sqrt 2 * Real.sqrt (-a) := by ring

lemma well_antideriv_at_z2Airy {a : ℝ} (ha : a ≤ -4) :
    z2Airy a * ((z2Airy a) ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ 1 := by
  have hA : 0 < -a := by linarith
  have hpz2 : (z2Airy a) ^ 2 / 4 + a = 2 * (-a) ^ ((1 : ℝ) / 3) := p_z2Airy_eq ha
  rw [hpz2]
  have hpow : (2 * (-a) ^ ((1 : ℝ) / 3)) ^ (-(3 / 2) : ℝ) =
      (2 * Real.sqrt 2 * Real.sqrt (-a))⁻¹ := by
    have h2 : (2 : ℝ) ^ (-(3 / 2) : ℝ) = (2 * Real.sqrt 2)⁻¹ := by
      rw [Real.sqrt_eq_rpow, show (2 : ℝ) * 2 ^ ((1 : ℝ) / 2) = 2 ^ (3 / 2 : ℝ) by
        rw [← Real.rpow_one_add' (by norm_num : (0 : ℝ) ≤ 2) (by norm_num)]; norm_num]
      rw [← Real.rpow_neg (by norm_num)]
    have hA1 : ((-a) ^ ((1 : ℝ) / 3)) ^ (-(3 / 2) : ℝ) = (Real.sqrt (-a))⁻¹ := by
      rw [← Real.rpow_mul hA.le, Real.sqrt_eq_rpow, ← Real.rpow_neg hA.le]
      norm_num
    rw [Real.mul_rpow (by norm_num) (by positivity), h2, hA1, mul_inv]
    ring
  rw [hpow, ← div_eq_mul_inv, div_le_one (by positivity)]
  exact z2Airy_le_two_sqrt_two_mul_sqrt ha

lemma well_antideriv_antitone {a x y : ℝ} (ha : a ≤ -4)
    (hx : 2 * Real.sqrt (-a) < x) (hxy : x ≤ y) :
    y * (y ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤ x * (x ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by
  have hcont : ContinuousOn (fun t : ℝ => (2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ))
      (Icc x y) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.rpow_const (by fun_prop) ?_)
    intro t ht
    exact Or.inl (p_well_pos ha (lt_of_lt_of_le hx ht.1)).ne'
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_well_antideriv ha (lt_of_lt_of_le hx (Set.mem_Icc.mp (by simpa [hxy] using ht)).1))
    (hcont.intervalIntegrable_of_Icc hxy)
  have hnonneg : 0 ≤ ∫ t in x..y, (2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) := by
    refine intervalIntegral.integral_nonneg hxy fun t ht => ?_
    have hp := p_well_pos ha (lt_of_lt_of_le hx ht.1)
    have hA : 0 < -a := by linarith
    positivity
  rw [hint] at hnonneg
  linarith

lemma intervalIntegral_abs_errorDensity_well_le {a x y : ℝ} (ha : a ≤ -4)
    (hx : 2 * Real.sqrt (-a) < x) (hxy : x ≤ y) :
    ∫ t in x..y, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
        (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| ≤
      5 / 48 * (x * (x ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) := by
  have hcont_lhs : ContinuousOn (fun t => |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|) (Icc x y) := by
    refine ContinuousOn.abs ?_
    unfold LiouvilleGreen.errorDensity
    refine (((continuousOn_const.mul ((continuousOn_id.div_const 2).pow 2)).mul
      (ContinuousOn.rpow_const (by fun_prop) fun t (ht : t ∈ Icc x y) =>
        Or.inl (p_well_pos ha (lt_of_lt_of_le hx ht.1)).ne')).sub
      ((continuousOn_const.mul continuousOn_const).mul
      (ContinuousOn.rpow_const (by fun_prop) fun t (ht : t ∈ Icc x y) =>
        Or.inl (p_well_pos ha (lt_of_lt_of_le hx ht.1)).ne'))).sub
      (continuousOn_const.mul
      (ContinuousOn.rpow_const (by fun_prop) fun t ht =>
        Or.inl (p_well_pos ha (lt_of_lt_of_le hx ht.1)).ne'))
  have hcont_rhs : ContinuousOn (fun t : ℝ => 5 / 48 * ((2 * (t ^ 2 / 4 + a) + 3 * (-a)) *
      (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ))) (Icc x y) := by
    refine continuousOn_const.mul (ContinuousOn.mul (by fun_prop)
      (ContinuousOn.rpow_const (by fun_prop) ?_))
    intro t ht
    exact Or.inl (p_well_pos ha (lt_of_lt_of_le hx ht.1)).ne'
  have hint_mono : ∫ t in x..y, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
        (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| ≤
      ∫ t in x..y, 5 / 48 * ((2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)) := by
    refine intervalIntegral.integral_mono_on hxy (hcont_lhs.intervalIntegrable_of_Icc hxy)
      (hcont_rhs.intervalIntegrable_of_Icc hxy) fun t ht => ?_
    exact abs_errorDensity_well_le ha (lt_of_lt_of_le hx ht.1)
  have hanti : ∫ t in x..y, (2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) =
      -y * (y ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) - (-x * (x ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_well_antideriv ha (lt_of_lt_of_le hx (Set.mem_Icc.mp (by simpa [hxy] using ht)).1))
      (((hcont_rhs.const_mul (48 / 5)).congr fun t _ => by ring).intervalIntegrable_of_Icc hxy)
  have hy_nonneg : 0 ≤ y * (y ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) := by
    have hy0 : 0 ≤ y := le_trans (le_trans (by positivity) hx.le) hxy
    have hpy : 0 < y ^ 2 / 4 + a := p_well_pos ha (lt_of_lt_of_le hx hxy)
    positivity
  calc ∫ t in x..y, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
          (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|
      ≤ ∫ t in x..y, 5 / 48 * ((2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ)) := hint_mono
    _ = 5 / 48 * ∫ t in x..y, (2 * (t ^ 2 / 4 + a) + 3 * (-a)) * (t ^ 2 / 4 + a) ^ (-(5 / 2) : ℝ) :=
        intervalIntegral.integral_const_mul _ _
    _ = 5 / 48 * (-y * (y ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) - (-x * (x ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ))) := by
        rw [hanti]
    _ ≤ 5 / 48 * (x * (x ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) := by
        gcongr; linarith

lemma integrableOn_abs_errorDensity_well {a c : ℝ} (ha : a ≤ -4) (hc : 2 * Real.sqrt (-a) < c) :
    IntegrableOn (fun t => |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|) (Ioi c) := by
  have hcont : ContinuousOn (fun t => |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|) (Ici c) := by
    refine ContinuousOn.abs ?_
    unfold LiouvilleGreen.errorDensity
    refine (((continuousOn_const.mul ((continuousOn_id.div_const 2).pow 2)).mul
      (ContinuousOn.rpow_const (by fun_prop) fun t ht =>
        Or.inl (p_well_pos ha (lt_of_lt_of_le hc ht)).ne')).sub
      ((continuousOn_const.mul continuousOn_const).mul
      (ContinuousOn.rpow_const (by fun_prop) fun t ht =>
        Or.inl (p_well_pos ha (lt_of_lt_of_le hc ht)).ne'))).sub
      (continuousOn_const.mul
      (ContinuousOn.rpow_const (by fun_prop) fun t ht =>
        Or.inl (p_well_pos ha (lt_of_lt_of_le hc ht)).ne'))
  refine integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (5 / 48 * (c * (c ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ))) c
    (fun b => by
      by_cases hcb : c ≤ b
      · exact ((hcont.mono (fun _ (hx : _ ∈ Set.Icc c b) => hx.1)).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
      · rw [show Ioc c (id b) = ∅ from Set.Ioc_eq_empty (fun h => hcb h.le)]
        exact integrableOn_empty)
    tendsto_id ?_
  filter_upwards [Filter.eventually_ge_atTop c] with b hb
  calc ∫ t in c..b, ‖|LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
          (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|‖
      = ∫ t in c..b, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
          (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| := by
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards with t _; exact Real.norm_of_nonneg (abs_nonneg _)
    _ ≤ 5 / 48 * (c * (c ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) :=
        intervalIntegral_abs_errorDensity_well_le ha hc hb

lemma integral_abs_errorDensity_well_le {a x : ℝ} (ha : a ≤ -4) (hx : z2Airy a ≤ x) :
    ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| ≤ 5 / 48 := by
  have hx_gt : 2 * Real.sqrt (-a) < x := lt_of_lt_of_le (z2Airy_gt_turning ha) hx
  have hint := integrableOn_abs_errorDensity_well ha hx_gt
  have hlim := intervalIntegral_tendsto_integral_Ioi x hint tendsto_id
  have hIoi : ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
      (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t| ≤
      5 / 48 * (x * (x ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop x] with b hb
    exact intervalIntegral_abs_errorDensity_well_le ha hx_gt hb
  have hanti : x * (x ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) ≤
      z2Airy a * ((z2Airy a) ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ) :=
    well_antideriv_antitone ha (z2Airy_gt_turning ha) hx
  calc ∫ t in Ioi x, |LiouvilleGreen.errorDensity (fun s => s ^ 2 / 4 + a)
          (fun s => s / 2) (fun _ => 1 / 2) (fun _ => 0) t|
      ≤ 5 / 48 * (x * (x ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) := hIoi
    _ ≤ 5 / 48 * (z2Airy a * ((z2Airy a) ^ 2 / 4 + a) ^ (-(3 / 2) : ℝ)) := by gcongr
    _ ≤ 5 / 48 * 1 := by gcongr; exact well_antideriv_at_z2Airy ha
    _ = 5 / 48 := by ring

/-! ### Decay of `pcU` and `pcUD` for every real `a` -/

lemma tendsto_pcU_mul_linear_all (a : ℝ) :
    Tendsto (fun x : ℝ => (1 + x) * pcU a x) atTop (𝓝 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-1 / 2 - a)
  obtain ⟨C, hC⟩ := pcU_decay_bound n a (by linarith)
  have hb : Tendsto (fun x : ℝ => |C| * 2 ^ (n + 1) * (x ^ ((n + 1 : ℕ) : ℝ) * Real.exp (-(1 / 4) * x)))
      atTop (𝓝 0) := by
    have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n + 1 : ℕ) : ℝ) (1 / 4) (by norm_num)).const_mul
      (|C| * 2 ^ (n + 1))
    rwa [mul_zero] at this
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 0 ≤ 1 + x := by linarith
  dsimp only [Function.comp_apply]
  rw [abs_mul, abs_of_nonneg hx1]
  have hcx := hC x hx0
  have hexp : Real.exp (-x ^ 2 / 4) ≤ Real.exp (-(1 / 4) * x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpow : (1 + x) ^ (n + 1) ≤ 2 ^ (n + 1) * x ^ ((n + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, ← mul_pow]
    exact pow_le_pow_left₀ hx1 (by linarith) (n + 1)
  calc (1 + x) * |pcU a x|
      ≤ (1 + x) * (C * (1 + x) ^ n * Real.exp (-x ^ 2 / 4)) := by gcongr
    _ ≤ (1 + x) * (|C| * (1 + x) ^ n * Real.exp (-(1 / 4) * x)) := by
        gcongr; exact le_abs_self _
    _ = |C| * (1 + x) ^ (n + 1) * Real.exp (-(1 / 4) * x) := by rw [pow_succ]; ring
    _ ≤ |C| * (2 ^ (n + 1) * x ^ ((n + 1 : ℕ) : ℝ)) * Real.exp (-(1 / 4) * x) := by gcongr
    _ = |C| * 2 ^ (n + 1) * (x ^ ((n + 1 : ℕ) : ℝ) * Real.exp (-(1 / 4) * x)) := by ring

lemma tendsto_pcUD_all (a : ℝ) : Tendsto (pcUD a) atTop (𝓝 0) := by
  have heq : pcUD a = fun x => x / 2 * pcU a x - pcU (a - 1) x := by
    ext x
    have h := pc_shift_U_dn a x
    rw [deriv_pcU] at h
    linarith
  rw [heq]
  have h1 : Tendsto (fun x : ℝ => x / 2 * pcU a x) atTop (𝓝 0) := by
    have hmul := tendsto_pcU_mul_linear_all a
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

/-! ### `k2`, `Mbal`, `Ewell` on `[z2Airy a, ∞)` (`a ≤ -4`) -/

lemma k2_well_far_eq {a z : ℝ} (ha : a ≤ -4) (hz : z2Airy a ≤ z) :
    k2 a z = z ^ 2 / 4 + a := by
  have hA : 4 ≤ -a := by linarith
  have hA13 : 0 < (-a) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos (by linarith) _
  have hp : 2 * (-a) ^ ((1 : ℝ) / 3) ≤ z ^ 2 / 4 + a := by
    have hz0 : 0 ≤ z2Airy a := le_trans (by positivity) (z2Airy_gt_turning ha).le
    calc 2 * (-a) ^ ((1 : ℝ) / 3) = (z2Airy a) ^ 2 / 4 + a := (p_z2Airy_eq ha).symm
      _ ≤ z ^ 2 / 4 + a := by gcongr
  have hp_pos : 0 ≤ z ^ 2 / 4 + a := by linarith
  have habs_a : max |a| 1 = -a := by
    rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
  unfold k2
  rw [habs_a, abs_of_nonneg hp_pos]
  exact max_eq_left (by linarith)

lemma Mbal_well_far_eq {a z : ℝ} (ha : a ≤ -4) (hz : z2Airy a ≤ z) :
    Mbal a z = (z ^ 2 / 4 + a) ^ (-(1 / 4) : ℝ) := by
  unfold Mbal
  rw [k2_well_far_eq ha hz]
  norm_num

lemma Ewell_well_far_eq {a z : ℝ} (ha : a ≤ -4) (hz : z2Airy a ≤ z) :
    Ewell a z = Real.exp (-(∫ t in (2 * Real.sqrt (-a))..z, Real.sqrt (t ^ 2 / 4 + a))) := by
  have hgt : 2 * Real.sqrt |a| < z := by
    rw [abs_of_nonpos (by linarith)]
    exact lt_of_lt_of_le (z2Airy_gt_turning ha) hz
  unfold Ewell
  rw [abs_of_nonpos (by linarith : a ≤ 0)] at hgt
  simp only [abs_of_nonpos (by linarith : a ≤ 0), hgt, ↓reduceIte]
  refine congr_arg Real.exp (congr_arg Neg.neg (intervalIntegral.integral_congr fun t _ => ?_))
  ring_nf

lemma exp_five_ninetysixths_lt : Real.exp (5 / 96 : ℝ) < 5 / 4 := by
  have hpow : Real.exp (5 / 96 : ℝ) ^ 5 < (5 / 4 : ℝ) ^ 5 := by
    rw [← Real.exp_nsmul]
    have hexp : Real.exp (5 • (5 / 96 : ℝ)) < Real.exp 1 :=
      Real.exp_lt_exp.mpr (by norm_num)
    have h1 : Real.exp 1 < 2.8 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith [show (2.8 : ℝ) < (5 / 4 : ℝ) ^ 5 by norm_num]
  exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : 5 ≠ 0)).mp hpow

/-! ### E4-U: `env_well` for `pcU` on `[z2Airy a, ∞)` (`a ≤ -4`) -/

/-- Existence of a positive scalar `c` and recessive LG solution `w` on `(a₀, ∞)` such that
`pcU a z = c * w z` and `deriv (pcU a) z = c * w' z` for `z ≥ z2Airy a`, together with
two-sided bounds on `w` and `w'`. -/
lemma pcU_well_far_lg {a : ℝ} (ha : a ≤ -4) :
    ∃ c : ℝ, 0 < c ∧ ∀ z, z2Airy a ≤ z →
      (1 / 2 * (Ewell a z * Mbal a z) ≤ pcU a z / c ∧
        pcU a z / c ≤ 5 / 4 * (Ewell a z * Mbal a z)) ∧
      |deriv (pcU a) z / c| ≤ 2 * Real.sqrt (k2 a z) * (Ewell a z * Mbal a z) := by
  set a0 : ℝ := (2 * Real.sqrt (-a) + z2Airy a) / 2 with ha0_def
  have hzt_lt_a0 : 2 * Real.sqrt (-a) < a0 := by rw [ha0_def]; linarith [z2Airy_gt_turning ha]
  have ha0_lt_z2 : a0 < z2Airy a := by rw [ha0_def]; linarith [z2Airy_gt_turning ha]
  let p : ℝ → ℝ := fun t => t ^ 2 / 4 + a
  let p' : ℝ → ℝ := fun t => t / 2
  let p'' : ℝ → ℝ := fun _ => 1 / 2
  let g : ℝ → ℝ := fun _ => 0
  let ξ : ℝ → ℝ := fun t => ∫ s in (2 * Real.sqrt (-a))..t, Real.sqrt (p s)
  have hp_pos : ∀ x, a0 < x → 0 < p x := fun x hx => p_well_pos ha (lt_trans hzt_lt_a0 hx)
  have hp' : ∀ x, a0 < x → HasDerivAt p (p' x) x := fun x _ => by
    have := ((hasDerivAt_pow 2 x).div_const 4).add_const a
    refine this.congr_deriv ?_
    ring
  have hp'' : ∀ x, a0 < x → HasDerivAt p' (p'' x) x := fun x _ => by
    simpa [p', p''] using (hasDerivAt_id x).div_const 2
  have hp''c : ContinuousOn p'' (Ioi a0) := continuousOn_const
  have hgc : ContinuousOn g (Ioi a0) := continuousOn_const
  have hξ_deriv : ∀ x : ℝ, HasDerivAt ξ (Real.sqrt (p x)) x := fun x => by
    have hcont : Continuous (fun s => Real.sqrt (p s)) :=
      Real.continuous_sqrt.comp (by continuity)
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable (2 * Real.sqrt (-a)) x)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  obtain ⟨ε, ε', w', hLG⟩ := LiouvilleGreen.exists_solution_exp_of_pos (a := a0) (u := 1)
    one_pos hp_pos hp' hp'' hp''c hgc (fun x _ => hξ_deriv x)
    (fun c hc => integrableOn_abs_errorDensity_well ha (lt_trans hzt_lt_a0 hc))
  let w : ℝ → ℝ := fun y => p y ^ (-(1 / 4) : ℝ) * Real.exp (-ξ y) * (1 + ε y)
  have hw_deriv : ∀ x, a0 < x → HasDerivAt w (w' x) x := fun x hx => by
    simpa [w, one_mul] using (hLG x hx).2.1
  have hw'_deriv : ∀ x, a0 < x → HasDerivAt w' (p x * w x) x := fun x hx => by
    simpa [w, g, one_mul] using (hLG x hx).2.2.1
  have hε_bd : ∀ x, z2Airy a ≤ x → |ε x| < 1 / 4 := fun x hx => by
    have hx_a0 : a0 < x := lt_of_lt_of_le ha0_lt_z2 hx
    have h1 := (hLG x hx_a0).2.2.2.1
    have hV := integral_abs_errorDensity_well_le ha hx
    have hV' : (∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 96 := by
      linarith
    have hexp : Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) < 5 / 4 :=
      lt_of_le_of_lt (Real.exp_le_exp.mpr hV') exp_five_ninetysixths_lt
    linarith
  have hw_pos : ∀ x, z2Airy a ≤ x → 0 < w x := fun x hx => by
    have h1 : 0 < 1 + ε x := by linarith [(abs_lt.mp (hε_bd x hx)).1]
    have h2 : 0 < p x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos (hp_pos x (lt_of_lt_of_le ha0_lt_z2 hx)) _
    have h3 : 0 < Real.exp (-ξ x) := Real.exp_pos _
    positivity
  have hw'_eq : ∀ x, a0 < x →
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
        ((hasDerivAt_const x 1).add (hLG x hx).1).congr_deriv (by ring)
      refine (hAE.mul h1ε).congr_deriv ?_
      ring
    exact (hw_deriv x hx).unique hfull
  -- Wronskian `W(x) = pcU a x * w' x - pcUD a x * w x` is 0 on `(a0, ∞)`
  let W : ℝ → ℝ := fun x => pcU a x * w' x - pcUD a x * w x
  have hW_deriv : ∀ x, a0 < x → HasDerivAt W 0 x := fun x hx => by
    have hU := hasDerivAt_pcU a x
    have hUD : HasDerivAt (pcUD a) (p x * pcU a x) x := by
      simpa [p] using hasDerivAt_pcUD a x
    have h1 := hU.mul (hw'_deriv x hx)
    have h2 := hUD.mul (hw_deriv x hx)
    refine (h1.sub h2).congr_deriv ?_
    ring
  have hW_const : ∀ x, a0 < x → W x = W (z2Airy a) := fun x hx =>
    isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun y hy => (hW_deriv y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hW_deriv y hy).deriv) hx ha0_lt_z2
  have hp_z2_ge : 2 ≤ p (z2Airy a) := by
    have hA : 4 ≤ -a := by linarith
    have h13 : (1 : ℝ) ≤ (-a) ^ ((1 : ℝ) / 3) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    dsimp [p]
    rw [p_z2Airy_eq ha]
    linarith
  have hp_ge_two : ∀ x : ℝ, z2Airy a ≤ x → 2 ≤ p x := fun x hx => by
    have hz0 : 0 ≤ z2Airy a := (z2Airy_gt_turning ha).le.trans' (by positivity)
    dsimp [p] at hp_z2_ge ⊢
    nlinarith
  have hξ_nonneg : ∀ x : ℝ, z2Airy a ≤ x → 0 ≤ ξ x := fun x hx =>
    intervalIntegral.integral_nonneg ((z2Airy_gt_turning ha).le.trans hx) (fun t _ => Real.sqrt_nonneg _)
  have hw_bd : ∀ x : ℝ, z2Airy a ≤ x → |w x| ≤ 2 := fun x hx => by
    have hpx : 1 ≤ p x := by linarith [hp_ge_two x hx]
    have hp14 : p x ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hpx (by norm_num)
    have hexp : Real.exp (-ξ x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hξ_nonneg x hx])
    have h1ε : |1 + ε x| ≤ 2 := by
      have := abs_lt.mp (hε_bd x hx)
      rw [abs_le]; constructor <;> linarith
    rw [show w x = p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) * (1 + ε x) from rfl,
      abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hp_pos x (lt_of_lt_of_le ha0_lt_z2 hx)) _),
      abs_of_pos (Real.exp_pos _)]
    calc p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) * |1 + ε x|
        ≤ 1 * 1 * 2 := by gcongr
      _ = 2 := by ring
  have hw'_bd : ∀ x : ℝ, z2Airy a ≤ x → |w' x| ≤ 2 * (1 + x) := fun x hx => by
    have hx_a0 : a0 < x := lt_of_lt_of_le ha0_lt_z2 hx
    rw [hw'_eq x hx_a0]
    have hpx_pos : 0 < p x := hp_pos x hx_a0
    have hpx1 : 1 ≤ p x := by linarith [hp_ge_two x hx]
    have hp14 : p x ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hpx1 (by norm_num)
    have hexp : Real.exp (-ξ x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hξ_nonneg x hx])
    have hx0 : 0 ≤ x := le_trans ((z2Airy_gt_turning ha).le.trans' (by positivity)) hx
    have hsqp : Real.sqrt (p x) ≤ x / 2 := by
      have hA : 0 ≤ -a := by linarith
      have hle : p x ≤ (x / 2) ^ 2 := by dsimp [p]; linarith
      calc Real.sqrt (p x) ≤ Real.sqrt ((x / 2) ^ 2) := Real.sqrt_le_sqrt hle
        _ = x / 2 := Real.sqrt_sq (by linarith)
    have hp_frac : |-(1 / 4) * (x / 2) / p x| ≤ 1 / 8 * Real.sqrt (p x) := by
      have hanti := well_antideriv_antitone ha (z2Airy_gt_turning ha) hx
      have hz2 := well_antideriv_at_z2Airy ha
      have hxp : x * p x ^ (-(3 / 2) : ℝ) ≤ 1 := le_trans hanti hz2
      have hdiv : x / p x ≤ Real.sqrt (p x) := by
        have h32 : p x ^ (-(3 / 2) : ℝ) = (p x * Real.sqrt (p x))⁻¹ := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hpx_pos.le (by norm_num),
            ← Real.rpow_neg hpx_pos.le]
          norm_num
        rw [h32, ← div_eq_mul_inv, div_le_one (by positivity)] at hxp
        rw [div_le_iff₀ hpx_pos]
        linarith
      rw [abs_div, abs_of_pos hpx_pos, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x / 2)]
      norm_num
      have : 1 / 4 * (x / 2) / p x = 1 / 8 * (x / p x) := by ring
      linarith
    have h1ε : |1 + ε x| ≤ 5 / 4 := by
      have := abs_lt.mp (hε_bd x hx)
      rw [abs_le]; constructor <;> linarith
    have hε' : |ε' x| ≤ 1 / 2 * Real.sqrt (p x) := by
      have h2 := (hLG x hx_a0).2.2.2.2
      have hV := integral_abs_errorDensity_well_le ha hx
      have hV' : (∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 96 := by
        linarith
      have hexp2 : Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1 ≤ 1 / 4 := by
        linarith [Real.exp_le_exp.mpr hV', exp_five_ninetysixths_lt]
      calc |ε' x| ≤ 2 * 1 * Real.sqrt (p x) *
            (Real.exp ((∫ t in Ioi x, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1) := h2
        _ ≤ 2 * 1 * Real.sqrt (p x) * (1 / 4) := by gcongr
        _ = 1 / 2 * Real.sqrt (p x) := by ring
    have hterm : |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x| ≤ 2 * (1 + x) := by
      have hsub : |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)| ≤ 9 / 8 * (x / 2) := by
        calc |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)|
            ≤ |-(1 / 4) * (x / 2) / p x| + |Real.sqrt (p x)| := abs_sub _ _
          _ ≤ 1 / 8 * Real.sqrt (p x) + Real.sqrt (p x) := by
              rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith
          _ = 9 / 8 * Real.sqrt (p x) := by ring
          _ ≤ 9 / 8 * (x / 2) := by gcongr
      calc |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x|
          ≤ |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x)| + |ε' x| := abs_add_le _ _
        _ = |-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)| * |1 + ε x| + |ε' x| := by rw [abs_mul]
        _ ≤ (9 / 8 * (x / 2)) * (5 / 4) + 1 / 2 * (x / 2) := by
            have hε'_x : |ε' x| ≤ 1 / 2 * (x / 2) := le_trans hε' (by gcongr)
            gcongr
        _ ≤ 2 * (1 + x) := by linarith
    rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpx_pos _), abs_of_pos (Real.exp_pos _)]
    calc p x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x) *
          |(-(1 / 4) * (x / 2) / p x - Real.sqrt (p x)) * (1 + ε x) + ε' x|
        ≤ 1 * 1 * (2 * (1 + x)) := by gcongr
      _ = 2 * (1 + x) := by ring
  have hW_tendsto : Tendsto W atTop (𝓝 0) := by
    have ht1 : Tendsto (fun x : ℝ => pcU a x * w' x) atTop (𝓝 0) := by
      have hlin : Tendsto (fun x : ℝ => 2 * |(1 + x) * pcU a x|) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_pcU_mul_linear_all a).abs.const_mul 2
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlin
      filter_upwards [eventually_ge_atTop (z2Airy a)] with x hx
      have hx0 : 0 ≤ x := le_trans ((z2Airy_gt_turning ha).le.trans' (by positivity)) hx
      dsimp only [Function.comp_apply]
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + x)]
      calc |pcU a x| * |w' x| ≤ |pcU a x| * (2 * (1 + x)) := by gcongr; exact hw'_bd x hx
        _ = 2 * ((1 + x) * |pcU a x|) := by ring
    have ht2 : Tendsto (fun x : ℝ => pcUD a x * w x) atTop (𝓝 0) := by
      have hlin : Tendsto (fun x : ℝ => 2 * |pcUD a x|) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_pcUD_all a).abs.const_mul 2
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun x => abs_nonneg _) ?_ hlin
      filter_upwards [eventually_ge_atTop (z2Airy a)] with x hx
      dsimp only [Function.comp_apply]
      rw [abs_mul]
      calc |pcUD a x| * |w x| ≤ |pcUD a x| * 2 := by gcongr; exact hw_bd x hx
        _ = 2 * |pcUD a x| := by ring
    simpa [W] using ht1.sub ht2
  have hW_zero : ∀ x, z2Airy a ≤ x → W x = 0 := by
    have hWz2 : W (z2Airy a) = 0 := by
      have hconst : Tendsto W atTop (𝓝 (W (z2Airy a))) :=
        tendsto_const_nhds.congr' (by
          filter_upwards [eventually_gt_atTop (z2Airy a)] with x hx
          exact (hW_const x (lt_trans ha0_lt_z2 hx)).symm)
      exact tendsto_nhds_unique hconst hW_tendsto
    intro x hx
    rw [hW_const x (lt_of_lt_of_le ha0_lt_z2 hx), hWz2]
  -- `pcU a / w` is constant on `(z2Airy a, ∞)` and hence on `[z2Airy a, ∞)`
  have hdiv_deriv : ∀ x, z2Airy a ≤ x → HasDerivAt (fun y => pcU a y / w y) 0 x := fun x hx => by
    have hx_a0 : a0 < x := lt_of_lt_of_le ha0_lt_z2 hx
    have h := (hasDerivAt_pcU a x).div (hw_deriv x hx_a0) (hw_pos x hx).ne'
    refine h.congr_deriv ?_
    have hW0 := hW_zero x hx
    dsimp [W] at hW0
    have e : pcUD a x * w x - pcU a x * w' x = 0 := by linarith
    rw [e, zero_div]
  let c : ℝ := pcU a (z2Airy a + 1) / w (z2Airy a + 1)
  have hpcU_gt : ∀ z, z2Airy a < z → pcU a z = c * w z := fun z hz => by
    have hconst : pcU a z / w z = c :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun y hy => (hdiv_deriv y (le_of_lt hy)).differentiableAt.differentiableWithinAt)
        (fun y hy => (hdiv_deriv y (le_of_lt hy)).deriv) hz (Set.mem_Ioi.mpr (by linarith))
    exact (div_eq_iff (hw_pos z hz.le).ne').mp hconst
  have hpcU_eq : ∀ z, z2Airy a ≤ z → pcU a z = c * w z := fun z hz => by
    rcases eq_or_lt_of_le hz with rfl | hgt
    · have hL : Tendsto (pcU a) (𝓝[>] (z2Airy a)) (𝓝 (pcU a (z2Airy a))) :=
        (hasDerivAt_pcU a (z2Airy a)).continuousAt.continuousWithinAt
      have hR : Tendsto (fun y => c * w y) (𝓝[>] (z2Airy a)) (𝓝 (c * w (z2Airy a))) :=
        ((hw_deriv (z2Airy a) ha0_lt_z2).continuousAt.const_mul c).continuousWithinAt
      refine tendsto_nhds_unique (hL.congr' ?_) hR
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hpcU_gt y hy
    · exact hpcU_gt z hgt
  have hpcUD_eq : ∀ z, z2Airy a ≤ z → deriv (pcU a) z = c * w' z := fun z hz => by
    have hgt : ∀ y, z2Airy a < y → deriv (pcU a) y = c * w' y := fun y hy => by
      have hU' : HasDerivAt (pcU a) (c * w' y) y := by
        refine ((hw_deriv y (lt_trans ha0_lt_z2 hy)).const_mul c).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hy] with t ht
        exact hpcU_gt t ht
      rw [deriv_pcU]
      exact (hasDerivAt_pcU a y).unique hU'
    rcases eq_or_lt_of_le hz with rfl | hgtz
    · have hL : Tendsto (deriv (pcU a)) (𝓝[>] (z2Airy a)) (𝓝 (deriv (pcU a) (z2Airy a))) := by
        rw [deriv_pcU]
        exact (hasDerivAt_pcUD a (z2Airy a)).continuousAt.continuousWithinAt
      have hR : Tendsto (fun y => c * w' y) (𝓝[>] (z2Airy a)) (𝓝 (c * w' (z2Airy a))) :=
        ((hw'_deriv (z2Airy a) ha0_lt_z2).continuousAt.const_mul c).continuousWithinAt
      refine tendsto_nhds_unique (hL.congr' ?_) hR
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hgt y hy
    · exact hgt z hgtz
  have hc_pos : 0 < c := by
    have hpos_U : 0 < pcU a (z2Airy a + 1) := by
      refine pcU_pos_beyond a (z2Airy a + 1) ?_
      rw [max_eq_left (by linarith)]
      linarith [z2Airy_gt_turning ha]
    exact div_pos hpos_U (hw_pos (z2Airy a + 1) (by linarith))
  refine ⟨c, hc_pos, ?_⟩
  · intro z hz
    have hc0 : c ≠ 0 := hc_pos.ne'
    have hdivU : pcU a z / c = w z := by rw [hpcU_eq z hz, mul_div_cancel_left₀ _ hc0]
    have hdivU' : deriv (pcU a) z / c = w' z := by rw [hpcUD_eq z hz, mul_div_cancel_left₀ _ hc0]
    have hz_a0 : a0 < z := lt_of_lt_of_le ha0_lt_z2 hz
    have hpz_pos : 0 < p z := hp_pos z hz_a0
    have hM : Mbal a z = p z ^ (-(1 / 4) : ℝ) := Mbal_well_far_eq ha hz
    have hE : Ewell a z = Real.exp (-ξ z) := Ewell_well_far_eq ha hz
    have hk : k2 a z = p z := k2_well_far_eq ha hz
    have hM_pos : 0 < Mbal a z := Mbal_pos a z
    have hE_pos : 0 < Ewell a z := by rw [hE]; exact Real.exp_pos _
    have h1ε := abs_lt.mp (hε_bd z hz)
    constructor
    · rw [hdivU]
      change 1 / 2 * (Ewell a z * Mbal a z) ≤ p z ^ (-(1 / 4) : ℝ) * Real.exp (-ξ z) * (1 + ε z) ∧
        p z ^ (-(1 / 4) : ℝ) * Real.exp (-ξ z) * (1 + ε z) ≤ 5 / 4 * (Ewell a z * Mbal a z)
      rw [← hM, ← hE]
      have hmul : Mbal a z * Ewell a z = Ewell a z * Mbal a z := mul_comm _ _
      rw [hmul]
      constructor
      · rw [mul_comm (1 / 2 : ℝ) _]
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_pos hE_pos hM_pos).le
      · rw [mul_comm (5 / 4 : ℝ) _]
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_pos hE_pos hM_pos).le
    · rw [hdivU', hw'_eq z hz_a0]
      have hz0 : 0 ≤ z := le_trans ((z2Airy_gt_turning ha).le.trans' (by positivity)) hz
      have hxp : z * p z ^ (-(3 / 2) : ℝ) ≤ 1 :=
        le_trans (well_antideriv_antitone ha (z2Airy_gt_turning ha) hz) (well_antideriv_at_z2Airy ha)
      have hz_div : z / p z ≤ Real.sqrt (p z) := by
        have h32 : p z ^ (-(3 / 2) : ℝ) = (p z * Real.sqrt (p z))⁻¹ := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hpz_pos.le (by norm_num),
            ← Real.rpow_neg hpz_pos.le]
          norm_num
        rw [h32, ← div_eq_mul_inv, div_le_one (by positivity)] at hxp
        rw [div_le_iff₀ hpz_pos]
        linarith
      have hp_frac : |-(1 / 4) * (z / 2) / p z| ≤ 1 / 8 * Real.sqrt (p z) := by
        rw [abs_div, abs_of_pos hpz_pos, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z / 2)]
        norm_num
        have : 1 / 4 * (z / 2) / p z = 1 / 8 * (z / p z) := by ring
        linarith
      have hε' : |ε' z| ≤ 1 / 2 * Real.sqrt (p z) := by
        have h2 := (hLG z hz_a0).2.2.2.2
        have hV := integral_abs_errorDensity_well_le ha hz
        have hV' : (∫ t in Ioi z, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1) ≤ 5 / 96 := by
          linarith
        have hexp2 : Real.exp ((∫ t in Ioi z, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1 ≤ 1 / 4 := by
          linarith [Real.exp_le_exp.mpr hV', exp_five_ninetysixths_lt]
        calc |ε' z| ≤ 2 * 1 * Real.sqrt (p z) *
              (Real.exp ((∫ t in Ioi z, |LiouvilleGreen.errorDensity p p' p'' g t|) / (2 * 1)) - 1) := h2
          _ ≤ 2 * 1 * Real.sqrt (p z) * (1 / 4) := by gcongr
          _ = 1 / 2 * Real.sqrt (p z) := by ring
      have hsub : |-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)| ≤ 9 / 8 * Real.sqrt (p z) := by
        calc |-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)|
            ≤ |-(1 / 4) * (z / 2) / p z| + |Real.sqrt (p z)| := abs_sub _ _
          _ ≤ 1 / 8 * Real.sqrt (p z) + Real.sqrt (p z) := by
              rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith
          _ = 9 / 8 * Real.sqrt (p z) := by ring
      have h1ε_abs : |1 + ε z| ≤ 5 / 4 := by rw [abs_le]; constructor <;> linarith
      have hterm : |(-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)) * (1 + ε z) + ε' z| ≤
          2 * Real.sqrt (p z) := by
        calc |(-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)) * (1 + ε z) + ε' z|
            ≤ |-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)| * |1 + ε z| + |ε' z| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ (9 / 8 * Real.sqrt (p z)) * (5 / 4) + 1 / 2 * Real.sqrt (p z) := by gcongr
          _ = 61 / 32 * Real.sqrt (p z) := by ring
          _ ≤ 2 * Real.sqrt (p z) := by gcongr; norm_num
      rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpz_pos _), abs_of_pos (Real.exp_pos _),
        ← hM, ← hE, hk]
      calc Mbal a z * Ewell a z * |(-(1 / 4) * (z / 2) / p z - Real.sqrt (p z)) * (1 + ε z) + ε' z|
          ≤ Mbal a z * Ewell a z * (2 * Real.sqrt (p z)) := by gcongr
        _ = 2 * Real.sqrt (p z) * (Ewell a z * Mbal a z) := by ring

lemma five_lt_exp_two : (5 : ℝ) < Real.exp 2 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
  rw [h2]
  nlinarith

/-- Two-sided `env_well` bound for `pcU`, pointwise lower bound for `ut pcU`, and Riccati
derivative bound `|deriv (pcU a) z| ≤ 4 * sqrt (k2 a z) * pcU a z` for `a ≤ -4` and
`z2Airy a ≤ z`. -/
theorem env_well_far_U_aux {a z : ℝ} (ha : a ≤ -4) (hz : z2Airy a ≤ z) :
    (Real.exp (-16) * (Ewell a z * Mbal a z) ≤
        Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ∧
      Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
        Real.exp 16 * (Ewell a z * Mbal a z)) ∧
    (Real.exp (-16) * (Ewell a z * Mbal a z) ≤ ut pcU a z ∧
      ut pcU a z ≤ Real.exp 15 * (Ewell a z * Mbal a z)) ∧
    |deriv (pcU a) z| ≤ 4 * Real.sqrt (k2 a z) * pcU a z := by
  obtain ⟨c, hc_pos, hc⟩ := pcU_well_far_lg ha
  have hκ : 0 < kappaBal a := kappaBal_pos a
  have hkc_pos : 0 < kappaBal a * c := mul_pos hκ hc_pos
  have hEU_scale : ∀ w, z2Airy a ≤ w →
      1 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w) ≤
        Real.sqrt (ut pcU a w ^ 2 + (kappaBal a * deriv (pcU a) w) ^ 2 / k2 a w) ∧
      Real.sqrt (ut pcU a w ^ 2 + (kappaBal a * deriv (pcU a) w) ^ 2 / k2 a w) ≤
        5 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w) := by
    intro w hw
    have hw_lg := hc w hw
    have hM_pos : 0 < Mbal a w := Mbal_pos a w
    have hE_pos : 0 < Ewell a w := by
      rw [Ewell_well_far_eq ha hw]; exact Real.exp_pos _
    have hk_pos : 0 < k2 a w := by
      rw [k2_well_far_eq ha hw]
      exact p_well_pos ha (lt_of_lt_of_le (z2Airy_gt_turning ha) hw)
    have hut_eq : ut pcU a w = kappaBal a * c * (pcU a w / c) := by
      unfold ut; field_simp [hc_pos.ne']
    have hdup_eq : kappaBal a * deriv (pcU a) w = kappaBal a * c * (deriv (pcU a) w / c) := by
      field_simp [hc_pos.ne']
    constructor
    · have h1 : 1 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w) ≤ ut pcU a w := by
        rw [hut_eq]
        calc 1 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w)
            = kappaBal a * c * (1 / 2 * (Ewell a w * Mbal a w)) := by ring
          _ ≤ kappaBal a * c * (pcU a w / c) := by gcongr; exact hw_lg.1.1
      have h2 : ut pcU a w ^ 2 ≤ ut pcU a w ^ 2 + (kappaBal a * deriv (pcU a) w) ^ 2 / k2 a w :=
        le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hk_pos.le)
      calc 1 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w)
          ≤ ut pcU a w := h1
        _ ≤ Real.sqrt (ut pcU a w ^ 2) := Real.le_sqrt_of_sq_le le_rfl
        _ ≤ Real.sqrt (ut pcU a w ^ 2 + (kappaBal a * deriv (pcU a) w) ^ 2 / k2 a w) :=
            Real.sqrt_le_sqrt h2
    · have h1 : ut pcU a w ^ 2 ≤ (5 / 4 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 := by
        have hpos : 0 ≤ ut pcU a w := by
          rw [hut_eq]
          exact mul_nonneg hkc_pos.le (le_trans (by positivity) hw_lg.1.1)
        have hle : ut pcU a w ≤ 5 / 4 * (kappaBal a * c) * (Ewell a w * Mbal a w) := by
          rw [hut_eq]
          calc kappaBal a * c * (pcU a w / c)
              ≤ kappaBal a * c * (5 / 4 * (Ewell a w * Mbal a w)) := by gcongr; exact hw_lg.1.2
            _ = 5 / 4 * (kappaBal a * c) * (Ewell a w * Mbal a w) := by ring
        exact pow_le_pow_left₀ hpos hle 2
      have h2 : (kappaBal a * deriv (pcU a) w) ^ 2 / k2 a w ≤
          (2 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 := by
        have habs : |kappaBal a * deriv (pcU a) w| ≤
            kappaBal a * c * (2 * Real.sqrt (k2 a w) * (Ewell a w * Mbal a w)) := by
          rw [hdup_eq, abs_mul, abs_of_pos hkc_pos]
          gcongr; exact hw_lg.2
        have hsq : (kappaBal a * deriv (pcU a) w) ^ 2 ≤
            (kappaBal a * c * (2 * Real.sqrt (k2 a w) * (Ewell a w * Mbal a w))) ^ 2 := by
          rw [← sq_abs (kappaBal a * deriv (pcU a) w)]
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
        rw [div_le_iff₀ hk_pos]
        calc (kappaBal a * deriv (pcU a) w) ^ 2
            ≤ (kappaBal a * c * (2 * Real.sqrt (k2 a w) * (Ewell a w * Mbal a w))) ^ 2 := hsq
          _ = (2 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 * (Real.sqrt (k2 a w)) ^ 2 := by ring
          _ = (2 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 * k2 a w := by
              rw [Real.sq_sqrt hk_pos.le]
      have hsum : ut pcU a w ^ 2 + (kappaBal a * deriv (pcU a) w) ^ 2 / k2 a w ≤
          (5 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 := by
        calc ut pcU a w ^ 2 + (kappaBal a * deriv (pcU a) w) ^ 2 / k2 a w
            ≤ (5 / 4 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 +
              (2 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 := add_le_add h1 h2
          _ = 89 / 16 * ((kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 := by ring
          _ ≤ 25 / 4 * ((kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 :=
              mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
          _ = (5 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2 := by ring
      calc Real.sqrt (ut pcU a w ^ 2 + (kappaBal a * deriv (pcU a) w) ^ 2 / k2 a w)
          ≤ Real.sqrt ((5 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w)) ^ 2) :=
            Real.sqrt_le_sqrt hsum
        _ = 5 / 2 * (kappaBal a * c) * (Ewell a w * Mbal a w) :=
            Real.sqrt_sq (by positivity)
  -- Normalise `kappaBal a * c` at `z2Airy a`
  have hairy := (env_well_on_airy_U_V ha (z1Well_le_z2Airy ha) le_rfl).1
  have hz2_scale := hEU_scale (z2Airy a) le_rfl
  have hEM_z2_pos : 0 < Ewell a (z2Airy a) * Mbal a (z2Airy a) := by
    have hE_pos : 0 < Ewell a (z2Airy a) := by
      rw [Ewell_well_far_eq ha le_rfl]; exact Real.exp_pos _
    exact mul_pos hE_pos (Mbal_pos a (z2Airy a))
  have hkc_lb : 2 / 5 * Real.exp (-14) ≤ kappaBal a * c := by
    have hle : Real.exp (-14) * (Ewell a (z2Airy a) * Mbal a (z2Airy a)) ≤
        5 / 2 * (kappaBal a * c) * (Ewell a (z2Airy a) * Mbal a (z2Airy a)) :=
      le_trans hairy.1 hz2_scale.2
    have hle' := le_of_mul_le_mul_right hle hEM_z2_pos
    linarith
  have hkc_ub : kappaBal a * c ≤ 2 * Real.exp 14 := by
    have hle : 1 / 2 * (kappaBal a * c) * (Ewell a (z2Airy a) * Mbal a (z2Airy a)) ≤
        Real.exp 14 * (Ewell a (z2Airy a) * Mbal a (z2Airy a)) :=
      le_trans hz2_scale.1 hairy.2
    have hle' := le_of_mul_le_mul_right hle hEM_z2_pos
    linarith
  have h5_exp2 : (5 : ℝ) ≤ Real.exp 2 := five_lt_exp_two.le
  have h52_exp1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hM_pos : 0 < Mbal a z := Mbal_pos a z
  have hE_pos : 0 < Ewell a z := by
    rw [Ewell_well_far_eq ha hz]; exact Real.exp_pos _
  have hEM_pos : 0 ≤ Ewell a z * Mbal a z := (mul_pos hE_pos hM_pos).le
  have hz_scale := hEU_scale z hz
  have hz_lg := hc z hz
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · calc Real.exp (-16) * (Ewell a z * Mbal a z)
        = (Real.exp (-2) * Real.exp (-14)) * (Ewell a z * Mbal a z) := by
          rw [← Real.exp_add]; norm_num
      _ ≤ (1 / 5 * Real.exp (-14)) * (Ewell a z * Mbal a z) := by
          gcongr
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
          norm_num; exact h5_exp2
      _ = 1 / 2 * (2 / 5 * Real.exp (-14)) * (Ewell a z * Mbal a z) := by ring
      _ ≤ 1 / 2 * (kappaBal a * c) * (Ewell a z * Mbal a z) := by gcongr
      _ ≤ Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) := hz_scale.1
  · calc Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z)
        ≤ 5 / 2 * (kappaBal a * c) * (Ewell a z * Mbal a z) := hz_scale.2
      _ ≤ 5 / 2 * (2 * Real.exp 14) * (Ewell a z * Mbal a z) := by gcongr
      _ = (5 * Real.exp 14) * (Ewell a z * Mbal a z) := by ring
      _ ≤ (Real.exp 2 * Real.exp 14) * (Ewell a z * Mbal a z) := by gcongr
      _ = Real.exp 16 * (Ewell a z * Mbal a z) := by rw [← Real.exp_add]; norm_num
  · have hut_eq : ut pcU a z = kappaBal a * c * (pcU a z / c) := by
      unfold ut; field_simp [hc_pos.ne']
    rw [hut_eq]
    calc Real.exp (-16) * (Ewell a z * Mbal a z)
        ≤ 1 / 2 * (kappaBal a * c) * (Ewell a z * Mbal a z) := by
          have h1 : Real.exp (-16) ≤ 1 / 2 * (kappaBal a * c) := by
            calc Real.exp (-16) = Real.exp (-2) * Real.exp (-14) := by
                  rw [← Real.exp_add]; norm_num
              _ ≤ 1 / 5 * Real.exp (-14) := by
                  gcongr
                  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
                  norm_num; exact h5_exp2
              _ = 1 / 2 * (2 / 5 * Real.exp (-14)) := by ring
              _ ≤ 1 / 2 * (kappaBal a * c) := by gcongr
          gcongr
      _ = kappaBal a * c * (1 / 2 * (Ewell a z * Mbal a z)) := by ring
      _ ≤ kappaBal a * c * (pcU a z / c) := by gcongr; exact hz_lg.1.1
  · have hut_eq : ut pcU a z = kappaBal a * c * (pcU a z / c) := by
      unfold ut; field_simp [hc_pos.ne']
    rw [hut_eq]
    calc kappaBal a * c * (pcU a z / c)
        ≤ kappaBal a * c * (5 / 4 * (Ewell a z * Mbal a z)) := by gcongr; exact hz_lg.1.2
      _ ≤ (2 * Real.exp 14) * (5 / 4 * (Ewell a z * Mbal a z)) := by gcongr
      _ = (5 / 2 * Real.exp 14) * (Ewell a z * Mbal a z) := by ring
      _ ≤ (Real.exp 1 * Real.exp 14) * (Ewell a z * Mbal a z) := by gcongr
      _ = Real.exp 15 * (Ewell a z * Mbal a z) := by rw [← Real.exp_add]; norm_num
  · calc |deriv (pcU a) z|
        = |c * (deriv (pcU a) z / c)| := by rw [mul_div_cancel₀ _ hc_pos.ne']
      _ = c * |deriv (pcU a) z / c| := by rw [abs_mul, abs_of_pos hc_pos]
      _ ≤ c * (2 * Real.sqrt (k2 a z) * (Ewell a z * Mbal a z)) := by
          gcongr; exact hz_lg.2
      _ = 4 * Real.sqrt (k2 a z) * (c * (1 / 2 * (Ewell a z * Mbal a z))) := by ring
      _ ≤ 4 * Real.sqrt (k2 a z) * (c * (pcU a z / c)) := by
          gcongr; exact hz_lg.1.1
      _ = 4 * Real.sqrt (k2 a z) * pcU a z := by
          rw [mul_div_cancel₀ _ hc_pos.ne']

/-! ### E4-V: `env_well` for `pcV` on `[z2Airy a, ∞)` (`a ≤ -4`) -/

/-- Wronskian of `ut pcU a` and `vt pcV a` is `1`. -/
lemma ut_vt_wronsk (a z : ℝ) :
    ut pcU a z * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) -
      (kappaBal a * deriv (pcU a) z) * vt pcV a z = 1 := by
  have hκ : kappaBal a ≠ 0 := (kappaBal_pos a).ne'
  have hpi : 0 ≤ π / 2 := by positivity
  have hwr := pc_wronsk a z
  unfold ut vt
  calc kappaBal a * pcU a z * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) -
        kappaBal a * deriv (pcU a) z * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * pcV a z)
      = (kappaBal a * (kappaBal a)⁻¹) * Real.sqrt (π / 2) *
          (pcU a z * deriv (pcV a) z - deriv (pcU a) z * pcV a z) := by ring
    _ = 1 * Real.sqrt (π / 2) * Real.sqrt (2 / π) := by rw [mul_inv_cancel₀ hκ, hwr]
    _ = Real.sqrt (π / 2 * (2 / π)) := by
          rw [one_mul, ← Real.sqrt_mul hpi]
    _ = 1 := by
          rw [show π / 2 * (2 / π) = 1 by field_simp [Real.pi_ne_zero], Real.sqrt_one]

lemma abs_vt_well_far_le {a z : ℝ} (ha : a ≤ -4) (hz : z2Airy a ≤ z) :
    |vt pcV a z| ≤ Real.exp 52 * (Ewell a z)⁻¹ * Mbal a z := by
  have hut_pos : ∀ t, z2Airy a ≤ t → 0 < ut pcU a t := fun t ht => by
    have h := (env_well_far_U_aux ha ht).2.1.1
    have hE : 0 < Ewell a t := by rw [Ewell_well_far_eq ha ht]; exact Real.exp_pos _
    have hM : 0 < Mbal a t := Mbal_pos a t
    exact lt_of_lt_of_le (by positivity) h
  have hderiv_quo : ∀ t, z2Airy a ≤ t →
      HasDerivAt (fun s => vt pcV a s / ut pcU a s) ((ut pcU a t)⁻¹ ^ 2) t := fun t ht => by
    have hV : HasDerivAt (vt pcV a) (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) t) t := by
      rw [deriv_pcV]
      exact (hasDerivAt_pcV a t).const_mul _
    have hU : HasDerivAt (ut pcU a) (kappaBal a * deriv (pcU a) t) t := by
      rw [deriv_pcU]
      exact (hasDerivAt_pcU a t).const_mul _
    refine (hV.div hU (hut_pos t ht).ne').congr_deriv ?_
    have hwr : Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) t * ut pcU a t -
        vt pcV a t * (kappaBal a * deriv (pcU a) t) = 1 := by
      linarith [ut_vt_wronsk a t]
    rw [hwr, inv_pow, one_div]
  have hcont_quo : ContinuousOn (fun t => (ut pcU a t)⁻¹ ^ 2) (Icc (z2Airy a) z) := by
    refine ContinuousOn.pow (ContinuousOn.inv₀ ?_ fun t (ht : t ∈ Icc (z2Airy a) z) => (hut_pos t ht.1).ne') 2
    exact (pcSmoothFacts.cont_U.comp (continuous_const.prodMk continuous_id)).continuousOn.const_mul _
  have hint_eq : vt pcV a z / ut pcU a z - vt pcV a (z2Airy a) / ut pcU a (z2Airy a) =
      ∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2 := by
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hderiv_quo t (Set.mem_Icc.mp (by simpa [hz] using ht)).1)
      (hcont_quo.intervalIntegrable_of_Icc hz)).symm
  -- Bound `∫_{z2}^z (ut pcU a t)^{-2}` using `(Ewell a t)^{-2} * sqrt(t^2/4 + a)`
  let ξ : ℝ → ℝ := fun t => ∫ s in (2 * Real.sqrt (-a))..t, Real.sqrt (s ^ 2 / 4 + a)
  have hξ_deriv : ∀ t : ℝ, HasDerivAt ξ (Real.sqrt (t ^ 2 / 4 + a)) t := fun t => by
    have hcont : Continuous (fun s => Real.sqrt (s ^ 2 / 4 + a)) :=
      Real.continuous_sqrt.comp (by continuity)
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable (2 * Real.sqrt (-a)) t)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have hanti_deriv : ∀ t : ℝ,
      HasDerivAt (fun s => 1 / 2 * Real.exp (2 * ξ s))
        (Real.exp (2 * ξ t) * Real.sqrt (t ^ 2 / 4 + a)) t := fun t => by
    refine (((hξ_deriv t).const_mul 2).exp.const_mul (1 / 2)).congr_deriv ?_
    ring
  have hcont_rhs : ContinuousOn (fun t : ℝ => Real.exp 32 * (Real.exp (2 * ξ t) * Real.sqrt (t ^ 2 / 4 + a)))
      (Icc (z2Airy a) z) := by
    refine continuousOn_const.mul (ContinuousOn.mul ?_ (ContinuousOn.sqrt (by fun_prop)))
    exact Continuous.continuousOn (Real.continuous_exp.comp (continuous_const.mul
      (intervalIntegral.continuous_primitive (fun a' b' =>
        (Real.continuous_sqrt.comp (by continuity : Continuous (fun s : ℝ => s ^ 2 / 4 + a))).intervalIntegrable a' b') _)))
  have hint_ub : ∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2 ≤
      1 / 2 * Real.exp 32 * (Ewell a z)⁻¹ ^ 2 := by
    have hmono : ∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2 ≤
        ∫ t in (z2Airy a)..z, Real.exp 32 * (Real.exp (2 * ξ t) * Real.sqrt (t ^ 2 / 4 + a)) := by
      refine intervalIntegral.integral_mono_on hz (hcont_quo.intervalIntegrable_of_Icc hz)
        (hcont_rhs.intervalIntegrable_of_Icc hz) fun t ht => ?_
      have hlb := (env_well_far_U_aux ha ht.1).2.1.1
      have hE : Ewell a t = Real.exp (-ξ t) := Ewell_well_far_eq ha ht.1
      have hM : Mbal a t = (t ^ 2 / 4 + a) ^ (-(1 / 4) : ℝ) := Mbal_well_far_eq ha ht.1
      have hp_pos : 0 < t ^ 2 / 4 + a := p_well_pos ha (lt_of_lt_of_le (z2Airy_gt_turning ha) ht.1)
      have hE_pos : 0 < Ewell a t := by rw [hE]; exact Real.exp_pos _
      have hM_pos : 0 < Mbal a t := Mbal_pos a t
      have hinv : (ut pcU a t)⁻¹ ≤ Real.exp 16 * (Ewell a t)⁻¹ * (Mbal a t)⁻¹ := by
        rw [inv_le_iff_one_le_mul₀' (hut_pos t ht.1)]
        calc (1 : ℝ) = Real.exp 16 * Real.exp (-16) * ((Ewell a t)⁻¹ * Ewell a t) * ((Mbal a t)⁻¹ * Mbal a t) := by
              rw [← Real.exp_add, inv_mul_cancel₀ hE_pos.ne', inv_mul_cancel₀ hM_pos.ne']; norm_num
          _ = Real.exp 16 * (Ewell a t)⁻¹ * (Mbal a t)⁻¹ * (Real.exp (-16) * (Ewell a t * Mbal a t)) := by ring
          _ ≤ Real.exp 16 * (Ewell a t)⁻¹ * (Mbal a t)⁻¹ * ut pcU a t :=
              mul_le_mul_of_nonneg_left hlb (by positivity)
          _ = ut pcU a t * (Real.exp 16 * (Ewell a t)⁻¹ * (Mbal a t)⁻¹) := by ring
      have hsq : (ut pcU a t)⁻¹ ^ 2 ≤ Real.exp 32 * (Ewell a t)⁻¹ ^ 2 * (Mbal a t)⁻¹ ^ 2 := by
        calc (ut pcU a t)⁻¹ ^ 2 ≤ (Real.exp 16 * (Ewell a t)⁻¹ * (Mbal a t)⁻¹) ^ 2 :=
              pow_le_pow_left₀ (inv_nonneg.mpr (hut_pos t ht.1).le) hinv 2
          _ = Real.exp 32 * (Ewell a t)⁻¹ ^ 2 * (Mbal a t)⁻¹ ^ 2 := by
              rw [mul_pow, mul_pow, sq (Real.exp 16), ← Real.exp_add]; norm_num
      have hE2 : (Ewell a t)⁻¹ ^ 2 = Real.exp (2 * ξ t) := by
        rw [hE, ← Real.exp_neg, neg_neg, sq, ← Real.exp_add, ← two_mul]
      have hM2 : (Mbal a t)⁻¹ ^ 2 = Real.sqrt (t ^ 2 / 4 + a) := by
        rw [hM, ← Real.rpow_neg hp_pos.le, neg_neg, Real.sqrt_eq_rpow,
          ← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
        norm_num
      rw [hE2, hM2] at hsq
      linarith
    have hanti_int : ∫ t in (z2Airy a)..z, Real.exp (2 * ξ t) * Real.sqrt (t ^ 2 / 4 + a) =
        1 / 2 * Real.exp (2 * ξ z) - 1 / 2 * Real.exp (2 * ξ (z2Airy a)) := by
      have hcont_anti : Continuous (fun t : ℝ => Real.exp (2 * ξ t) * Real.sqrt (t ^ 2 / 4 + a)) := by
        refine (Real.continuous_exp.comp (continuous_const.mul
          (intervalIntegral.continuous_primitive (fun a' b' =>
            (Real.continuous_sqrt.comp (by continuity : Continuous (fun s : ℝ => s ^ 2 / 4 + a))).intervalIntegrable a' b') _))).mul
          (Real.continuous_sqrt.comp (by continuity))
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hanti_deriv t)
        (hcont_anti.intervalIntegrable (z2Airy a) z)
    have hE2z : (Ewell a z)⁻¹ ^ 2 = Real.exp (2 * ξ z) := by
      rw [Ewell_well_far_eq ha hz, ← Real.exp_neg, neg_neg, sq, ← Real.exp_add, ← two_mul]
    calc ∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2
        ≤ ∫ t in (z2Airy a)..z, Real.exp 32 * (Real.exp (2 * ξ t) * Real.sqrt (t ^ 2 / 4 + a)) := hmono
      _ = Real.exp 32 * ∫ t in (z2Airy a)..z, Real.exp (2 * ξ t) * Real.sqrt (t ^ 2 / 4 + a) :=
          intervalIntegral.integral_const_mul _ _
      _ = Real.exp 32 * (1 / 2 * Real.exp (2 * ξ z) - 1 / 2 * Real.exp (2 * ξ (z2Airy a))) := by
          rw [hanti_int]
      _ ≤ Real.exp 32 * (1 / 2 * Real.exp (2 * ξ z)) := by
          gcongr; linarith [Real.exp_pos (2 * ξ (z2Airy a))]
      _ = 1 / 2 * Real.exp 32 * (Ewell a z)⁻¹ ^ 2 := by rw [hE2z]; ring
  -- Bound `|vt pcV a (z2Airy a) / ut pcU a (z2Airy a)| ≤ exp 36`
  have hquo_z2 : |vt pcV a (z2Airy a) / ut pcU a (z2Airy a)| ≤ Real.exp 36 := by
    have hairyV := (env_well_on_airy_U_V ha (z1Well_le_z2Airy ha) le_rfl).2.2
    have hEz2 := Ewell_airy_bounds ha (z1Well_le_z2Airy ha) le_rfl
    have hE_pos : 0 < Ewell a (z2Airy a) := lt_of_lt_of_le (Real.exp_pos (-3)) hEz2.1
    have hM_pos : 0 < Mbal a (z2Airy a) := Mbal_pos a (z2Airy a)
    have hvt_z2 : |vt pcV a (z2Airy a)| ≤ Real.exp 14 * (Ewell a (z2Airy a))⁻¹ * Mbal a (z2Airy a) := by
      calc |vt pcV a (z2Airy a)|
          = Real.sqrt (vt pcV a (z2Airy a) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (vt pcV a (z2Airy a) ^ 2 +
              (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) (z2Airy a)) ^ 2 / k2 a (z2Airy a)) :=
            Real.sqrt_le_sqrt (le_add_of_nonneg_right (div_nonneg (sq_nonneg _)
              (by rw [k2_well_far_eq ha le_rfl]; exact (p_well_pos ha (z2Airy_gt_turning ha)).le)))
        _ ≤ Real.exp 14 * ((Ewell a (z2Airy a))⁻¹ * Mbal a (z2Airy a)) := hairyV
        _ = Real.exp 14 * (Ewell a (z2Airy a))⁻¹ * Mbal a (z2Airy a) := by ring
    have hut_z2 : Real.exp (-16) * (Ewell a (z2Airy a) * Mbal a (z2Airy a)) ≤ ut pcU a (z2Airy a) :=
      (env_well_far_U_aux ha le_rfl).2.1.1
    have hEinv_ub : (Ewell a (z2Airy a))⁻¹ ≤ Real.exp 3 := by
      rw [show Real.exp 3 = (Real.exp (-3))⁻¹ by rw [Real.exp_neg, inv_inv]]
      exact inv_anti₀ (Real.exp_pos (-3)) hEz2.1
    rw [abs_div, abs_of_pos (hut_pos (z2Airy a) le_rfl), div_le_iff₀ (hut_pos (z2Airy a) le_rfl)]
    calc |vt pcV a (z2Airy a)|
        ≤ Real.exp 14 * (Ewell a (z2Airy a))⁻¹ * Mbal a (z2Airy a) := hvt_z2
      _ = Real.exp 30 * (Ewell a (z2Airy a))⁻¹ ^ 2 * (Real.exp (-16) * (Ewell a (z2Airy a) * Mbal a (z2Airy a))) := by
          rw [show Real.exp 30 * (Ewell a (z2Airy a))⁻¹ ^ 2 * (Real.exp (-16) * (Ewell a (z2Airy a) * Mbal a (z2Airy a))) =
            (Real.exp 30 * Real.exp (-16)) * ((Ewell a (z2Airy a))⁻¹ * Ewell a (z2Airy a)) *
              (Ewell a (z2Airy a))⁻¹ * Mbal a (z2Airy a) by ring]
          rw [← Real.exp_add, inv_mul_cancel₀ hE_pos.ne']; norm_num
      _ ≤ Real.exp 30 * (Real.exp 3) ^ 2 * ut pcU a (z2Airy a) := by gcongr
      _ = Real.exp 36 * ut pcU a (z2Airy a) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add]; norm_num
  -- Combine to bound `|vt pcV a z|`
  have hut_ub := (env_well_far_U_aux ha hz).2.1.2
  have hEz : Ewell a z ≤ 1 := by
    rw [Ewell_well_far_eq ha hz]
    have hξz_nonneg : 0 ≤ ∫ t in (2 * Real.sqrt (-a))..z, Real.sqrt (t ^ 2 / 4 + a) :=
      intervalIntegral.integral_nonneg ((z2Airy_gt_turning ha).le.trans hz)
        (fun t _ => Real.sqrt_nonneg _)
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hE_pos : 0 < Ewell a z := by rw [Ewell_well_far_eq ha hz]; exact Real.exp_pos _
  have hM_pos : 0 < Mbal a z := Mbal_pos a z
  have hEz_le_inv : Ewell a z ≤ (Ewell a z)⁻¹ := le_trans hEz (one_le_inv₀ hE_pos |>.mpr hEz)
  have hint_nonneg : 0 ≤ ∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2 := by
    apply intervalIntegral.integral_nonneg hz
    intro t _
    exact sq_nonneg _
  have hquo_z : |vt pcV a z / ut pcU a z| ≤ Real.exp 36 + 1 / 2 * Real.exp 32 * (Ewell a z)⁻¹ ^ 2 := by
    have heq : vt pcV a z / ut pcU a z =
        vt pcV a (z2Airy a) / ut pcU a (z2Airy a) + ∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2 := by
      linarith [hint_eq]
    rw [heq]
    calc |vt pcV a (z2Airy a) / ut pcU a (z2Airy a) + ∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2|
        ≤ |vt pcV a (z2Airy a) / ut pcU a (z2Airy a)| + |∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2| :=
          abs_add_le _ _
      _ = |vt pcV a (z2Airy a) / ut pcU a (z2Airy a)| + ∫ t in (z2Airy a)..z, (ut pcU a t)⁻¹ ^ 2 := by
          rw [abs_of_nonneg hint_nonneg]
      _ ≤ Real.exp 36 + 1 / 2 * Real.exp 32 * (Ewell a z)⁻¹ ^ 2 := add_le_add hquo_z2 hint_ub
  have hut_z_pos := hut_pos z hz
  calc |vt pcV a z|
      = |vt pcV a z / ut pcU a z * ut pcU a z| := by
        rw [div_mul_cancel₀ _ hut_z_pos.ne']
    _ = |vt pcV a z / ut pcU a z| * ut pcU a z := by
        rw [abs_mul, abs_of_pos hut_z_pos]
    _ ≤ (Real.exp 36 + 1 / 2 * Real.exp 32 * (Ewell a z)⁻¹ ^ 2) * (Real.exp 15 * (Ewell a z * Mbal a z)) := by
        gcongr
    _ = Real.exp 36 * Real.exp 15 * Ewell a z * Mbal a z +
          1 / 2 * (Real.exp 32 * Real.exp 15) * ((Ewell a z)⁻¹ * ((Ewell a z)⁻¹ * Ewell a z)) * Mbal a z := by
        ring
    _ ≤ Real.exp 51 * (Ewell a z)⁻¹ * Mbal a z + 1 / 2 * Real.exp 47 * (Ewell a z)⁻¹ * Mbal a z := by
        rw [← Real.exp_add, ← Real.exp_add, inv_mul_cancel₀ hE_pos.ne', mul_one]
        norm_num
        gcongr
    _ = (Real.exp 51 + 1 / 2 * Real.exp 47) * (Ewell a z)⁻¹ * Mbal a z := by ring
    _ ≤ Real.exp 52 * (Ewell a z)⁻¹ * Mbal a z := by
        have hexp : Real.exp 51 + 1 / 2 * Real.exp 47 ≤ Real.exp 52 := by
          have h47 : Real.exp 47 ≤ Real.exp 51 := Real.exp_le_exp.mpr (by norm_num)
          have h52 : Real.exp 52 = Real.exp 1 * Real.exp 51 := by rw [← Real.exp_add]; norm_num
          have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          nlinarith [Real.exp_pos 51]
        gcongr

/-- Two-sided `env_well` bounds for `pcU` and `pcV` for `a ≤ -4` and `z2Airy a ≤ z`,
with explicit absolute constants `exp(-54)` and `exp(54)` (matching `env_well_on_airy_U_V`). -/
theorem env_well_far_U_V {a z : ℝ} (ha : a ≤ -4) (hz : z2Airy a ≤ z) :
    (Real.exp (-54) * (Ewell a z * Mbal a z) ≤
        Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ∧
      Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) ≤
        Real.exp 54 * (Ewell a z * Mbal a z)) ∧
    (Real.exp (-54) * ((Ewell a z)⁻¹ * Mbal a z) ≤
        Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ∧
      Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) ≤
        Real.exp 54 * ((Ewell a z)⁻¹ * Mbal a z)) := by
  have hU := env_well_far_U_aux ha hz
  have hV_val := abs_vt_well_far_le ha hz
  have hM_pos : 0 < Mbal a z := Mbal_pos a z
  have hE_pos : 0 < Ewell a z := by rw [Ewell_well_far_eq ha hz]; exact Real.exp_pos _
  have hk_pos : 0 < k2 a z := by
    rw [k2_well_far_eq ha hz]
    exact p_well_pos ha (lt_of_lt_of_le (z2Airy_gt_turning ha) hz)
  have hU_pos : 0 < pcU a z := by
    refine pcU_pos_beyond a z ?_
    rw [max_eq_left (by linarith)]
    exact (z2Airy_gt_turning ha).le.trans hz
  have hM_sq : Mbal a z * Real.sqrt (k2 a z) = (k2 a z) ^ ((1 : ℝ) / 4) := by
    unfold Mbal
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hk_pos]
    norm_num
  have hM_inv : (Mbal a z * Real.sqrt (k2 a z))⁻¹ = Mbal a z := by
    rw [hM_sq]
    unfold Mbal
    rw [← Real.rpow_neg hk_pos.le]
    norm_num
  -- Bound `|γ * deriv (pcV a) z| / sqrt(k2)`
  have hVp_bd : |Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z| / Real.sqrt (k2 a z) ≤
      5 * Real.exp 52 * ((Ewell a z)⁻¹ * Mbal a z) := by
    have hut_pos : 0 < ut pcU a z := lt_of_lt_of_le (by positivity) hU.2.1.1
    have hwr := ut_vt_wronsk a z
    have hγV' : Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z =
        (kappaBal a * deriv (pcU a) z) / ut pcU a z * vt pcV a z + (ut pcU a z)⁻¹ := by
      have hwr' : ut pcU a z * (Real.sqrt (π / 2) * deriv (pcV a) z) -
          kappaBal a * (kappaBal a * deriv (pcU a) z * vt pcV a z) = kappaBal a := by
        have h := congr_arg (· * kappaBal a) hwr
        field_simp [(kappaBal_pos a).ne'] at h
        linarith
      field_simp [hut_pos.ne', (kappaBal_pos a).ne']
      linarith
    have hric : |kappaBal a * deriv (pcU a) z| / ut pcU a z ≤ 4 * Real.sqrt (k2 a z) := by
      unfold ut
      rw [abs_mul, abs_of_pos (kappaBal_pos a), div_le_iff₀ (mul_pos (kappaBal_pos a) hU_pos)]
      calc kappaBal a * |deriv (pcU a) z|
          ≤ kappaBal a * (4 * Real.sqrt (k2 a z) * pcU a z) :=
            mul_le_mul_of_nonneg_left hU.2.2 (kappaBal_pos a).le
        _ = 4 * Real.sqrt (k2 a z) * (kappaBal a * pcU a z) := by ring
    have hinv_ut : (ut pcU a z)⁻¹ / Real.sqrt (k2 a z) ≤ Real.exp 16 * ((Ewell a z)⁻¹ * Mbal a z) := by
      have h1 : (ut pcU a z)⁻¹ ≤ Real.exp 16 * (Ewell a z)⁻¹ * (Mbal a z)⁻¹ := by
        rw [inv_le_iff_one_le_mul₀' hut_pos]
        calc (1 : ℝ) = Real.exp 16 * Real.exp (-16) * ((Ewell a z)⁻¹ * Ewell a z) * ((Mbal a z)⁻¹ * Mbal a z) := by
              rw [← Real.exp_add, inv_mul_cancel₀ hE_pos.ne', inv_mul_cancel₀ hM_pos.ne']; norm_num
          _ = Real.exp 16 * (Ewell a z)⁻¹ * (Mbal a z)⁻¹ * (Real.exp (-16) * (Ewell a z * Mbal a z)) := by ring
          _ ≤ Real.exp 16 * (Ewell a z)⁻¹ * (Mbal a z)⁻¹ * ut pcU a z :=
              mul_le_mul_of_nonneg_left hU.2.1.1 (by positivity)
          _ = ut pcU a z * (Real.exp 16 * (Ewell a z)⁻¹ * (Mbal a z)⁻¹) := by ring
      calc (ut pcU a z)⁻¹ / Real.sqrt (k2 a z)
          ≤ (Real.exp 16 * (Ewell a z)⁻¹ * (Mbal a z)⁻¹) / Real.sqrt (k2 a z) := by gcongr
        _ = Real.exp 16 * (Ewell a z)⁻¹ * (Mbal a z * Real.sqrt (k2 a z))⁻¹ := by
            rw [mul_inv]; ring
        _ = Real.exp 16 * ((Ewell a z)⁻¹ * Mbal a z) := by rw [hM_inv]; ring
    rw [hγV']
    calc |kappaBal a * deriv (pcU a) z / ut pcU a z * vt pcV a z + (ut pcU a z)⁻¹| / Real.sqrt (k2 a z)
        ≤ (|kappaBal a * deriv (pcU a) z / ut pcU a z * vt pcV a z| + |(ut pcU a z)⁻¹|) / Real.sqrt (k2 a z) := by
          gcongr; exact abs_add_le _ _
      _ = (|kappaBal a * deriv (pcU a) z| / ut pcU a z / Real.sqrt (k2 a z)) * |vt pcV a z| +
            (ut pcU a z)⁻¹ / Real.sqrt (k2 a z) := by
          rw [abs_mul, abs_div, abs_of_pos hut_pos, abs_of_pos (inv_pos.mpr hut_pos)]; ring
      _ ≤ 4 * (Real.exp 52 * (Ewell a z)⁻¹ * Mbal a z) + Real.exp 16 * ((Ewell a z)⁻¹ * Mbal a z) := by
          have hric' : |kappaBal a * deriv (pcU a) z| / ut pcU a z / Real.sqrt (k2 a z) ≤ 4 := by
            rw [div_le_iff₀ (Real.sqrt_pos.mpr hk_pos)]
            exact hric
          gcongr
      _ ≤ 5 * Real.exp 52 * ((Ewell a z)⁻¹ * Mbal a z) := by
          have h16 : Real.exp 16 ≤ Real.exp 52 := Real.exp_le_exp.mpr (by norm_num)
          nlinarith [mul_pos (inv_pos.mpr hE_pos) hM_pos]
  -- Lower bound for `pcV` envelope via Cauchy-Schwarz and `ut_vt_wronsk`
  have hV_lb : Real.exp (-16) * ((Ewell a z)⁻¹ * Mbal a z) ≤
      Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) := by
    let EU := Real.sqrt (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z)
    let EV := Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z)
    have hCS : (Mbal a z ^ 2) ^ 2 ≤ EU ^ 2 * EV ^ 2 := by
      have h1 : (ut pcU a z * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z / Real.sqrt (k2 a z)) -
          (kappaBal a * deriv (pcU a) z / Real.sqrt (k2 a z)) * vt pcV a z) ^ 2 = (Mbal a z ^ 2) ^ 2 := by
        have heq : ut pcU a z * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z / Real.sqrt (k2 a z)) -
            (kappaBal a * deriv (pcU a) z / Real.sqrt (k2 a z)) * vt pcV a z =
            (ut pcU a z * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) -
              kappaBal a * deriv (pcU a) z * vt pcV a z) / Real.sqrt (k2 a z) := by ring
        rw [heq, ut_vt_wronsk a z, one_div]
        have hM4 : (Real.sqrt (k2 a z))⁻¹ ^ 2 = (Mbal a z ^ 2) ^ 2 := by
          rw [inv_pow, Real.sq_sqrt hk_pos.le]
          unfold Mbal
          rw [← Real.rpow_natCast (k2 a z ^ (-(1 : ℝ) / 4)), ← Real.rpow_mul hk_pos.le,
            ← Real.rpow_natCast (k2 a z ^ _), ← Real.rpow_mul hk_pos.le, ← Real.rpow_neg_one (k2 a z)]
          congr 1; norm_num
        exact hM4
      have h2 : (ut pcU a z * (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z / Real.sqrt (k2 a z)) -
          (kappaBal a * deriv (pcU a) z / Real.sqrt (k2 a z)) * vt pcV a z) ^ 2 ≤
          (ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z) *
            (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z) := by
        have hnonneg : 0 ≤ (ut pcU a z * vt pcV a z +
            (kappaBal a * deriv (pcU a) z / Real.sqrt (k2 a z)) *
              (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z / Real.sqrt (k2 a z))) ^ 2 :=
          sq_nonneg _
        have hdiv : (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z =
            (kappaBal a * deriv (pcU a) z / Real.sqrt (k2 a z)) ^ 2 := by
          rw [div_pow, Real.sq_sqrt hk_pos.le]
        have hdiv2 : (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z =
            (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z / Real.sqrt (k2 a z)) ^ 2 := by
          rw [div_pow, Real.sq_sqrt hk_pos.le]
        rw [hdiv, hdiv2]
        nlinarith
      rw [h1] at h2
      have hEU_sq : EU ^ 2 = ut pcU a z ^ 2 + (kappaBal a * deriv (pcU a) z) ^ 2 / k2 a z :=
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hk_pos.le))
      have hEV_sq : EV ^ 2 = vt pcV a z ^ 2 +
          (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z :=
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hk_pos.le))
      rw [hEU_sq, hEV_sq]
      exact h2
    have hM2_le : Mbal a z ^ 2 ≤ EU * EV := by
      have hsq : (Mbal a z ^ 2) ^ 2 ≤ (EU * EV) ^ 2 := by rw [mul_pow]; exact hCS
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    have hEU_pos : 0 < EU := lt_of_lt_of_le (by positivity) hU.1.1
    calc Real.exp (-16) * ((Ewell a z)⁻¹ * Mbal a z)
        = (Mbal a z ^ 2) / (Real.exp 16 * (Ewell a z * Mbal a z)) := by
          rw [Real.exp_neg]; field_simp [hE_pos.ne', hM_pos.ne']
      _ ≤ (EU * EV) / EU := div_le_div₀ (by positivity) hM2_le hEU_pos hU.1.2
      _ = EV := mul_div_cancel_left₀ EV hEU_pos.ne'
  -- Combine into `env_well_far_U_V`
  constructor
  · constructor
    · calc Real.exp (-54) * (Ewell a z * Mbal a z)
          ≤ Real.exp (-16) * (Ewell a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) (by positivity)
        _ ≤ _ := hU.1.1
    · calc _ ≤ Real.exp 16 * (Ewell a z * Mbal a z) := hU.1.2
        _ ≤ Real.exp 54 * (Ewell a z * Mbal a z) :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) (by positivity)
  · constructor
    · calc Real.exp (-54) * ((Ewell a z)⁻¹ * Mbal a z)
          ≤ Real.exp (-16) * ((Ewell a z)⁻¹ * Mbal a z) :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) (by positivity)
        _ ≤ _ := hV_lb
    · have h26_lt : (26 : ℝ) ≤ (Real.exp 2) ^ 2 := by
        have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
        have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [sq, ← Real.exp_add]; norm_num
        have h7 : (7 : ℝ) ≤ Real.exp 2 := by rw [h2]; nlinarith
        rw [sq]; nlinarith
      have hsum : vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z ≤
          (Real.exp 54 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2 := by
        have h1 : vt pcV a z ^ 2 ≤ (Real.exp 52 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2 := by
          rw [← sq_abs (vt pcV a z)]
          exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
        have h2 : (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z ≤
            (5 * Real.exp 52 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2 := by
          rw [← Real.sq_sqrt hk_pos.le, ← div_pow, ← sq_abs (_ / Real.sqrt (k2 a z)), abs_div,
            abs_of_pos (Real.sqrt_pos.mpr hk_pos)]
          exact pow_le_pow_left₀ (by positivity) hVp_bd 2
        calc vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z
            ≤ (Real.exp 52 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2 +
              (5 * Real.exp 52 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2 := add_le_add h1 h2
          _ = 26 * (Real.exp 52 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2 := by ring
          _ ≤ (Real.exp 2) ^ 2 * (Real.exp 52 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2 := by gcongr
          _ = (Real.exp 54 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2 := by
              rw [← mul_pow, ← mul_assoc, ← Real.exp_add]; norm_num
      calc Real.sqrt (vt pcV a z ^ 2 + (Real.sqrt (π / 2) * (kappaBal a)⁻¹ * deriv (pcV a) z) ^ 2 / k2 a z)
          ≤ Real.sqrt ((Real.exp 54 * ((Ewell a z)⁻¹ * Mbal a z)) ^ 2) := Real.sqrt_le_sqrt hsum
        _ = Real.exp 54 * ((Ewell a z)⁻¹ * Mbal a z) := Real.sqrt_sq (by positivity)

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.env_well_far_U_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env_well_far_U_V

end FormalResearch.JacobiEigenvectors.Charts