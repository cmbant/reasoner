module

public import FormalResearch.ModularBootstrap.Constants
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Edge Phase Normal Form and Uniform Saddle Geometry (`edge_transform_sd.tex`, (SD.2), (SD.5)–(SD.7))

Formalizes the edge phase function `F(v) = π⁻¹ arsinh(cosh(πv))`, the unique edge saddle
`v_x > 0` for `x > ξ_*`, the uniform scale parameters `α_x`, `s_x`, `m_x`, `b_x` and their
uniform comparability (SD.5), convexity bounds (SD.6), the abstract edge-phase hypothesis
`EdgePhaseData` (SD.2) with an explicit non-vacuity witness `edgePhi0Model`, the normal Taylor
formula (SD.7), and the local steepest-descent Taylor expansions along `b_x + r e^{-iπ/4}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Saddle

open FormalResearch.ModularBootstrap

/-! ### 1. Edge frequency function `F(v)` and its derivatives -/

/-- Edge frequency function `F(v) = π⁻¹ arsinh(cosh(πv))`. -/
noncomputable def edgeF (v : ℝ) : ℝ :=
  Real.arsinh (Real.cosh (Real.pi * v)) / Real.pi

/-- First derivative `F'(v) = sinh(πv) / √(1 + cosh(πv)²)`. -/
noncomputable def edgeF' (v : ℝ) : ℝ :=
  Real.sinh (Real.pi * v) / √(1 + Real.cosh (Real.pi * v) ^ 2)

/-- Second derivative `F''(v) = 2π cosh(πv) / (1 + cosh(πv)²)^{3/2}`. -/
noncomputable def edgeF'' (v : ℝ) : ℝ :=
  2 * Real.pi * Real.cosh (Real.pi * v) / (1 + Real.cosh (Real.pi * v) ^ 2) ^ (3 / 2 : ℝ)

lemma edgeF_zero : edgeF 0 = xiStar := by
  unfold edgeF xiStar
  simp [Real.cosh_zero]

lemma edgeF_neg (v : ℝ) : edgeF (-v) = edgeF v := by
  simp [edgeF, Real.cosh_neg]

lemma hasDerivAt_edgeF (v : ℝ) : HasDerivAt edgeF (edgeF' v) v := by
  unfold edgeF edgeF'
  have h1 : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi v := by
    simpa using (hasDerivAt_id v).const_mul Real.pi
  have h2 : HasDerivAt (fun t : ℝ => Real.cosh (Real.pi * t))
      (Real.sinh (Real.pi * v) * Real.pi) v :=
    (Real.hasDerivAt_cosh (Real.pi * v)).comp v h1
  have h3 := (Real.hasDerivAt_arsinh (Real.cosh (Real.pi * v))).comp v h2
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  refine (h3.div_const Real.pi).congr_deriv ?_
  have hs : 0 < √(1 + Real.cosh (Real.pi * v) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp [hpi, hs.ne']

lemma hasDerivAt_edgeF' (v : ℝ) : HasDerivAt edgeF' (edgeF'' v) v := by
  unfold edgeF' edgeF''
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hu : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi v := by
    simpa using (hasDerivAt_id v).const_mul Real.pi
  have hnum : HasDerivAt (fun t : ℝ => Real.sinh (Real.pi * t))
      (Real.cosh (Real.pi * v) * Real.pi) v :=
    (Real.hasDerivAt_sinh (Real.pi * v)).comp v hu
  have h_in : HasDerivAt (fun t : ℝ => 1 + Real.cosh (Real.pi * t) ^ 2)
      (2 * Real.cosh (Real.pi * v) * Real.sinh (Real.pi * v) * Real.pi) v := by
    have hc : HasDerivAt (fun t : ℝ => Real.cosh (Real.pi * t))
        (Real.sinh (Real.pi * v) * Real.pi) v :=
      (Real.hasDerivAt_cosh (Real.pi * v)).comp v hu
    have hsq := (hc.pow 2).const_add (1 : ℝ)
    exact hsq.congr_deriv (by ring)
  have hpos_in : 1 + Real.cosh (Real.pi * v) ^ 2 ≠ 0 := by positivity
  have hden : HasDerivAt (fun t : ℝ => √(1 + Real.cosh (Real.pi * t) ^ 2))
      ((2 * Real.cosh (Real.pi * v) * Real.sinh (Real.pi * v) * Real.pi) /
        (2 * √(1 + Real.cosh (Real.pi * v) ^ 2))) v :=
    h_in.sqrt hpos_in
  have hq := hnum.div hden (Real.sqrt_ne_zero'.mpr (by positivity))
  refine hq.congr_deriv ?_
  have hsq : √(1 + Real.cosh (Real.pi * v) ^ 2) ^ 2 = 1 + Real.cosh (Real.pi * v) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hpow32 : (1 + Real.cosh (Real.pi * v) ^ 2) ^ (3 / 2 : ℝ) =
      (1 + Real.cosh (Real.pi * v) ^ 2) * √(1 + Real.cosh (Real.pi * v) ^ 2) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hid : Real.cosh (Real.pi * v) ^ 2 - Real.sinh (Real.pi * v) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (Real.pi * v)
  rw [hpow32]
  have hs_pos : 0 < √(1 + Real.cosh (Real.pi * v) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hi_pos : 0 < 1 + Real.cosh (Real.pi * v) ^ 2 := by positivity
  rw [hsq]
  field_simp [hs_pos.ne', hi_pos.ne']
  rw [hsq]
  nlinarith [Real.cosh_sq_sub_sinh_sq (Real.pi * v)]

lemma edgeF''_pos (v : ℝ) : 0 < edgeF'' v := by
  unfold edgeF''
  have hpi := Real.pi_pos
  have hc := Real.cosh_pos (Real.pi * v)
  positivity

lemma edgeF'_strictMono : StrictMono edgeF' :=
  strictMono_of_deriv_pos fun v => by rw [(hasDerivAt_edgeF' v).deriv]; exact edgeF''_pos v

lemma edgeF'_zero : edgeF' 0 = 0 := by simp [edgeF']

lemma edgeF'_pos {v : ℝ} (hv : 0 < v) : 0 < edgeF' v := by
  rw [← edgeF'_zero]; exact edgeF'_strictMono hv

lemma edgeF'_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ edgeF' v := by
  rcases hv.eq_or_lt with rfl | hv'
  · simp [edgeF'_zero]
  · exact (edgeF'_pos hv').le

lemma edgeF'_lt_one (v : ℝ) : edgeF' v < 1 := by
  unfold edgeF'
  have hs : 0 < √(1 + Real.cosh (Real.pi * v) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_lt_one hs]
  have hsq : Real.sinh (Real.pi * v) ^ 2 < 1 + Real.cosh (Real.pi * v) ^ 2 := by
    have := Real.cosh_sq_sub_sinh_sq (Real.pi * v)
    linarith
  exact Real.lt_sqrt_of_sq_lt hsq

lemma edgeF_strictMonoOn : StrictMonoOn edgeF (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (continuous_iff_continuousAt.mpr fun v => (hasDerivAt_edgeF v).continuousAt).continuousOn
    fun v hv => ?_
  rw [interior_Ici] at hv
  rw [(hasDerivAt_edgeF v).deriv]
  exact edgeF'_pos hv

private lemma self_le_sinh_of_nonneg {u : ℝ} (hu : 0 ≤ u) : u ≤ Real.sinh u := by
  have hmono : MonotoneOn (fun t : ℝ => Real.sinh t - t) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      (fun t _ => ((Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)).differentiableAt.differentiableWithinAt)
      fun t _ => ?_
    have hd := (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
    have hdeq : deriv (fun s : ℝ => Real.sinh s - s) t = Real.cosh t - 1 := hd.deriv
    rw [hdeq]
    linarith [Real.one_le_cosh t]
  have h0 := hmono (le_rfl : (0 : ℝ) ∈ Ici 0) hu hu
  simp only [Real.sinh_zero, sub_zero] at h0
  linarith

private lemma sinh_le_mul_cosh_of_le {u M : ℝ} (hu : 0 ≤ u) (hM : u ≤ M) :
    Real.sinh u ≤ Real.cosh M * u := by
  have hmono : MonotoneOn (fun t : ℝ => Real.cosh M * t - Real.sinh t) (Icc 0 M) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 M) (by fun_prop)
      (fun t _ => (((hasDerivAt_id t).const_mul (Real.cosh M)).sub
        (Real.hasDerivAt_sinh t)).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Icc] at ht
    have hd := ((hasDerivAt_id t).const_mul (Real.cosh M)).sub (Real.hasDerivAt_sinh t)
    have hdeq : deriv (fun s : ℝ => Real.cosh M * s - Real.sinh s) t = Real.cosh M * 1 - Real.cosh t :=
      hd.deriv
    rw [hdeq]
    simp only [mul_one, sub_nonneg]
    exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg ht.1.le, abs_of_nonneg (hu.trans hM)]; exact ht.2.le)
  have h0 := hmono ⟨le_rfl, hu.trans hM⟩ ⟨hu, hM⟩ hu
  simp only [mul_zero, Real.sinh_zero, sub_zero] at h0
  linarith

lemma edgeF'_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ v ≥ 0,
      c * min 1 v ≤ edgeF' v ∧ edgeF' v ≤ C * min 1 v := by
  let c : ℝ := Real.pi / √(1 + Real.cosh Real.pi ^ 2)
  let C : ℝ := max 1 (Real.pi * Real.cosh Real.pi / √2)
  have hpi := Real.pi_pos
  have hc_pos : 0 < c := by positivity
  have hC_pos : 0 < C := by positivity
  refine ⟨c, C, hc_pos, hC_pos, fun v hv => ?_⟩
  rcases le_total v 1 with hv1 | hv1
  · rw [min_eq_right hv1]
    have hsinh_lb : Real.pi * v ≤ Real.sinh (Real.pi * v) := self_le_sinh_of_nonneg (by positivity)
    have hsinh_ub : Real.sinh (Real.pi * v) ≤ Real.cosh Real.pi * (Real.pi * v) :=
      sinh_le_mul_cosh_of_le (by positivity) (by nlinarith)
    have hcosh_le : Real.cosh (Real.pi * v) ≤ Real.cosh Real.pi :=
      Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg (by positivity), abs_of_nonneg hpi.le]; nlinarith)
    have hden_ub : √(1 + Real.cosh (Real.pi * v) ^ 2) ≤ √(1 + Real.cosh Real.pi ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      have h1 : 0 ≤ Real.cosh (Real.pi * v) := (Real.cosh_pos _).le
      nlinarith
    have hden_lb : √2 ≤ √(1 + Real.cosh (Real.pi * v) ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      have h1 : 1 ≤ Real.cosh (Real.pi * v) := Real.one_le_cosh _
      nlinarith
    have hsinh_nn : 0 ≤ Real.sinh (Real.pi * v) := Real.sinh_nonneg_iff.mpr (by positivity)
    constructor
    · dsimp [c, edgeF']
      calc Real.pi / √(1 + Real.cosh Real.pi ^ 2) * v
          = (Real.pi * v) / √(1 + Real.cosh Real.pi ^ 2) := by ring
        _ ≤ Real.sinh (Real.pi * v) / √(1 + Real.cosh Real.pi ^ 2) := by gcongr
        _ ≤ Real.sinh (Real.pi * v) / √(1 + Real.cosh (Real.pi * v) ^ 2) := by gcongr
    · dsimp [edgeF']
      have hC_ge : Real.pi * Real.cosh Real.pi / √2 ≤ C := le_max_right _ _
      calc Real.sinh (Real.pi * v) / √(1 + Real.cosh (Real.pi * v) ^ 2)
          ≤ (Real.cosh Real.pi * (Real.pi * v)) / √(1 + Real.cosh (Real.pi * v) ^ 2) := by gcongr
        _ ≤ (Real.cosh Real.pi * (Real.pi * v)) / √2 := by gcongr
        _ = (Real.pi * Real.cosh Real.pi / √2) * v := by ring
        _ ≤ C * v := by gcongr
  · rw [min_eq_left hv1]
    have h1 : c ≤ edgeF' 1 := by
      have hsinh_lb : Real.pi ≤ Real.sinh Real.pi := by
        simpa using self_le_sinh_of_nonneg hpi.le
      dsimp [c, edgeF']
      rw [mul_one]
      gcongr
    have hge1 : edgeF' 1 ≤ edgeF' v := edgeF'_strictMono.monotone hv1
    constructor
    · linarith
    · calc edgeF' v ≤ 1 := (edgeF'_lt_one v).le
        _ ≤ C := le_max_left _ _
        _ = C * 1 := (mul_one C).symm

/-! ### 2. Saddle point `v_x`, parameters `α_x`, `s_x`, `m_x`, `b_x`, and (SD.5)–(SD.6) -/

/-- Unique positive edge saddle `v_x > 0` solving `F(v_x) = x` for `x > ξ_*`. -/
noncomputable def edgeV (x : ℝ) : ℝ :=
  Real.arcosh (Real.sinh (Real.pi * x)) / Real.pi

/-- Saddle curvature `α_x = (4π/3) F'(v_x)`. -/
noncomputable def alphaX (x : ℝ) : ℝ :=
  (4 * Real.pi / 3) * edgeF' (edgeV x)

/-- Chord slope `s_x = (x - ξ_*) / v_x`. -/
noncomputable def slopeX (x : ℝ) : ℝ :=
  (x - xiStar) / edgeV x

/-- Uniform scale parameter `m_x = min {1, v_x, α_x, s_x}`. -/
noncomputable def mX (x : ℝ) : ℝ :=
  min 1 (min (edgeV x) (min (alphaX x) (slopeX x)))

/-- Upper-edge saddle point `b_x = v_x + i/2`. -/
noncomputable def bX (x : ℝ) : ℂ :=
  (edgeV x : ℂ) + Complex.I / 2

lemma one_lt_sinh_pi_mul {x : ℝ} (hx : xiStar < x) : 1 < Real.sinh (Real.pi * x) := by
  have h1 : Real.pi * xiStar < Real.pi * x := mul_lt_mul_of_pos_left hx Real.pi_pos
  have h2 := Real.sinh_strictMono h1
  rwa [sinh_pi_mul_xiStar] at h2

lemma edgeV_pos {x : ℝ} (hx : xiStar < x) : 0 < edgeV x := by
  unfold edgeV
  exact div_pos (Real.arcosh_pos (one_lt_sinh_pi_mul hx)) Real.pi_pos

lemma edgeF_edgeV {x : ℝ} (hx : xiStar < x) : edgeF (edgeV x) = x := by
  unfold edgeF edgeV
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  rw [mul_div_cancel₀ _ hpi, Real.cosh_arcosh (one_lt_sinh_pi_mul hx).le,
    Real.arsinh_sinh, mul_div_cancel_left₀ _ hpi]

lemma edgeV_unique {x v : ℝ} (hx : xiStar < x) (hv : 0 < v) (hFv : edgeF v = x) :
    v = edgeV x := by
  apply edgeF_strictMonoOn.injOn hv.le (edgeV_pos hx).le
  rw [hFv, edgeF_edgeV hx]

lemma alphaX_pos {x : ℝ} (hx : xiStar < x) : 0 < alphaX x := by
  unfold alphaX
  exact mul_pos (by positivity [Real.pi_pos]) (edgeF'_pos (edgeV_pos hx))

lemma alphaX_lt {x : ℝ} : alphaX x < 4 * Real.pi / 3 := by
  unfold alphaX
  calc (4 * Real.pi / 3) * edgeF' (edgeV x) < (4 * Real.pi / 3) * 1 :=
        mul_lt_mul_of_pos_left (edgeF'_lt_one _) (by positivity [Real.pi_pos])
    _ = 4 * Real.pi / 3 := mul_one _

lemma slopeX_pos {x : ℝ} (hx : xiStar < x) : 0 < slopeX x := by
  unfold slopeX
  exact div_pos (sub_pos.mpr hx) (edgeV_pos hx)

lemma mX_pos {x : ℝ} (hx : xiStar < x) : 0 < mX x := by
  unfold mX
  exact lt_min zero_lt_one (lt_min (edgeV_pos hx) (lt_min (alphaX_pos hx) (slopeX_pos hx)))

lemma mX_le_one (x : ℝ) : mX x ≤ 1 := min_le_left _ _
lemma mX_le_edgeV (x : ℝ) : mX x ≤ edgeV x := (min_le_right _ _).trans (min_le_left _ _)
lemma mX_le_alphaX (x : ℝ) : mX x ≤ alphaX x :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
lemma mX_le_slopeX (x : ℝ) : mX x ≤ slopeX x :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

lemma edgeF_sub_eq_integral {a b : ℝ} :
    edgeF b - edgeF a = ∫ t in a..b, edgeF' t := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_edgeF t) ?_).symm
  exact (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF' t).continuousAt).intervalIntegrable _ _

lemma slopeX_ge_half_edgeF'_half {x : ℝ} (hx : xiStar < x) :
    (1 / 2 : ℝ) * edgeF' (edgeV x / 2) ≤ slopeX x := by
  let v : ℝ := edgeV x
  have hv_pos : 0 < v := edgeV_pos hx
  have hftc : x - xiStar = ∫ t in (0 : ℝ)..v, edgeF' t := by
    rw [← edgeF_edgeV hx, ← edgeF_zero]
    exact edgeF_sub_eq_integral
  have hcont : Continuous edgeF' :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF' t).continuousAt
  have hsplit : ∫ t in (0 : ℝ)..v, edgeF' t =
      (∫ t in (0 : ℝ)..(v / 2), edgeF' t) + (∫ t in (v / 2)..v, edgeF' t) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have h1_nn : 0 ≤ ∫ t in (0 : ℝ)..(v / 2), edgeF' t :=
    intervalIntegral.integral_nonneg (by linarith) fun t ht => edgeF'_nonneg ht.1
  have h2_lb : (v / 2) * edgeF' (v / 2) ≤ ∫ t in (v / 2)..v, edgeF' t := by
    have hconst : ∫ _t in (v / 2)..v, edgeF' (v / 2) = (v / 2) * edgeF' (v / 2) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hcont.intervalIntegrable _ _) fun t ht => edgeF'_strictMono.monotone ht.1
  have hx_lb : (v / 2) * edgeF' (v / 2) ≤ x - xiStar := by linarith [hftc, hsplit, h1_nn, h2_lb]
  unfold slopeX
  change (1 / 2 : ℝ) * edgeF' (v / 2) ≤ (x - xiStar) / v
  rw [le_div_iff₀ hv_pos]
  linarith

/-- **(SD.5)** Uniform bounds on `m_x` and `α_x` relative to `min(1, v_x)` for all `x > ξ_*`. -/
lemma mX_uniform_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, xiStar < x →
      c * min 1 (edgeV x) ≤ mX x ∧ mX x ≤ min 1 (edgeV x) ∧ alphaX x ≤ C * mX x := by
  obtain ⟨cF, CF, hcF_pos, hCF_pos, hF'⟩ := edgeF'_bounds
  let c : ℝ := min 1 (min ((4 * Real.pi / 3) * cF) (cF / 4))
  let C_alpha : ℝ := (4 * Real.pi / 3) * CF
  have hpi := Real.pi_pos
  have hc_pos : 0 < c := by positivity
  have hCa_pos : 0 < C_alpha := by positivity
  refine ⟨c, C_alpha / c, hc_pos, by positivity, fun x hx => ?_⟩
  have hv_pos : 0 < edgeV x := edgeV_pos hx
  have hmin_nn : 0 ≤ min 1 (edgeV x) := le_min zero_le_one hv_pos.le
  have h_half_min : (1 / 2 : ℝ) * min 1 (edgeV x) ≤ min 1 (edgeV x / 2) := by
    rcases le_total (edgeV x) 1 with hv1 | hv1
    · rw [min_eq_right hv1, min_eq_right (by linarith)]; ring_nf; rfl
    · rw [min_eq_left hv1]
      rcases le_total (edgeV x / 2) 1 with hv2 | hv2
      · rw [min_eq_right hv2]; linarith
      · rw [min_eq_left hv2]; norm_num
  have h_alpha_lb : (4 * Real.pi / 3) * cF * min 1 (edgeV x) ≤ alphaX x := by
    have h1 := (hF' (edgeV x) hv_pos.le).1
    unfold alphaX
    have : 0 ≤ 4 * Real.pi / 3 := by positivity
    nlinarith
  have h_slope_lb : (cF / 4) * min 1 (edgeV x) ≤ slopeX x := by
    have h1 := slopeX_ge_half_edgeF'_half hx
    have h2 := (hF' (edgeV x / 2) (by positivity)).1
    calc (cF / 4) * min 1 (edgeV x)
        = (1 / 2 : ℝ) * (cF * ((1 / 2 : ℝ) * min 1 (edgeV x))) := by ring
      _ ≤ (1 / 2 : ℝ) * (cF * min 1 (edgeV x / 2)) := by gcongr
      _ ≤ (1 / 2 : ℝ) * edgeF' (edgeV x / 2) := by gcongr
      _ ≤ slopeX x := h1
  have h_m_lb : c * min 1 (edgeV x) ≤ mX x := by
    unfold mX
    refine le_min ?_ (le_min ?_ (le_min ?_ ?_))
    · calc c * min 1 (edgeV x) ≤ 1 * 1 := mul_le_mul (min_le_left _ _) (min_le_left _ _) hmin_nn zero_le_one
        _ = 1 := one_mul 1
    · calc c * min 1 (edgeV x) ≤ 1 * edgeV x :=
            mul_le_mul (min_le_left _ _) (min_le_right _ _) hmin_nn zero_le_one
        _ = edgeV x := one_mul _
    · calc c * min 1 (edgeV x) ≤ ((4 * Real.pi / 3) * cF) * min 1 (edgeV x) :=
            mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hmin_nn
        _ ≤ alphaX x := h_alpha_lb
    · calc c * min 1 (edgeV x) ≤ (cF / 4) * min 1 (edgeV x) :=
            mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hmin_nn
        _ ≤ slopeX x := h_slope_lb
  have h_m_ub : mX x ≤ min 1 (edgeV x) := le_min (mX_le_one x) (mX_le_edgeV x)
  have h_alpha_ub : alphaX x ≤ (C_alpha / c) * mX x := by
    have h1 := (hF' (edgeV x) hv_pos.le).2
    have h2 : alphaX x ≤ C_alpha * min 1 (edgeV x) := by
      unfold alphaX; dsimp [C_alpha]; nlinarith
    calc alphaX x ≤ C_alpha * min 1 (edgeV x) := h2
      _ = (C_alpha / c) * (c * min 1 (edgeV x)) := by field_simp [hc_pos.ne']
      _ ≤ (C_alpha / c) * mX x := by gcongr
  exact ⟨h_m_lb, h_m_ub, h_alpha_ub⟩

/-- **(SD.5)** Asymptotic equivalence `v_x ≍ √(x - ξ_*)` for `x ∈ (ξ_*, ξ_* + 1]`. -/
lemma edgeV_near_xiStar_bounds :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ x ∈ Ioc xiStar (xiStar + 1),
      c₁ * √(x - xiStar) ≤ edgeV x ∧ edgeV x ≤ c₂ * √(x - xiStar) := by
  obtain ⟨cF, CF, hcF_pos, hCF_pos, hF'⟩ := edgeF'_bounds
  let V₁ : ℝ := edgeV (xiStar + 1)
  have hV₁_pos : 0 < V₁ := edgeV_pos (by linarith)
  let M_V : ℝ := max 1 V₁
  have hM_pos : 0 < M_V := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let c₀ : ℝ := cF / M_V
  have hc₀_pos : 0 < c₀ := div_pos hcF_pos hM_pos
  have h_low : ∀ t ∈ Icc 0 V₁, c₀ * t ≤ edgeF' t := fun t ht => by
    have h1 := (hF' t ht.1).1
    rcases le_total t 1 with ht1 | ht1
    · rw [min_eq_right ht1] at h1
      have h_le : c₀ * t ≤ cF * t := by
        dsimp [c₀]
        have : cF / M_V ≤ cF := div_le_self hcF_pos.le (le_max_left _ _)
        nlinarith [ht.1]
      exact h_le.trans h1
    · rw [min_eq_left ht1] at h1
      rw [mul_one] at h1
      have h_le : c₀ * t ≤ cF := by
        dsimp [c₀]
        rw [div_mul_eq_mul_div, div_le_iff₀ hM_pos]
        exact mul_le_mul_of_nonneg_left (ht.2.trans (le_max_right _ _)) hcF_pos.le
      exact h_le.trans h1
  have h_up : ∀ t ∈ Icc 0 V₁, edgeF' t ≤ CF * t := fun t ht => by
    have h1 := (hF' t ht.1).2
    have hmin : min 1 t ≤ t := min_le_right _ _
    exact h1.trans (mul_le_mul_of_nonneg_left hmin hCF_pos.le)
  have hc₁_pos : 0 < √(2 / CF) := Real.sqrt_pos.mpr (by positivity)
  have hc₂_pos : 0 < √(2 / c₀) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨√(2 / CF), √(2 / c₀), hc₁_pos, hc₂_pos, fun x hx => ?_⟩
  have hxv : edgeV x ≤ V₁ := by
    have h_mono : edgeF (edgeV x) ≤ edgeF V₁ := by
      rw [edgeF_edgeV hx.1, edgeF_edgeV (by linarith)]
      exact hx.2
    by_contra hlt
    push Not at hlt
    exact absurd (edgeF_strictMonoOn (edgeV_pos (by linarith)).le (edgeV_pos hx.1).le hlt)
      (not_lt.mpr h_mono)
  have hv_pos : 0 < edgeV x := edgeV_pos hx.1
  have hftc : x - xiStar = ∫ t in (0 : ℝ)..(edgeV x), edgeF' t := by
    have h_eq : edgeF (edgeV x) - edgeF 0 = ∫ t in (0 : ℝ)..(edgeV x), edgeF' t :=
      edgeF_sub_eq_integral
    rwa [edgeF_edgeV hx.1, edgeF_zero] at h_eq
  have hcont : Continuous edgeF' :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF' t).continuousAt
  have h_int_lb : c₀ / 2 * edgeV x ^ 2 ≤ x - xiStar := by
    rw [hftc]
    have h_lin : ∫ t in (0 : ℝ)..(edgeV x), c₀ * t = c₀ / 2 * edgeV x ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    rw [← h_lin]
    exact intervalIntegral.integral_mono_on hv_pos.le
      ((by fun_prop : Continuous (fun t : ℝ => c₀ * t)).intervalIntegrable 0 (edgeV x))
      (hcont.intervalIntegrable _ _)
      fun t ht => h_low t ⟨ht.1, ht.2.trans hxv⟩
  have h_int_ub : x - xiStar ≤ CF / 2 * edgeV x ^ 2 := by
    rw [hftc]
    have h_lin : ∫ t in (0 : ℝ)..(edgeV x), CF * t = CF / 2 * edgeV x ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    rw [← h_lin]
    exact intervalIntegral.integral_mono_on hv_pos.le (hcont.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => CF * t)).intervalIntegrable 0 (edgeV x))
      fun t ht => h_up t ⟨ht.1, ht.2.trans hxv⟩
  have hx_nn : 0 ≤ x - xiStar := (sub_pos.mpr hx.1).le
  constructor
  · have hsq : (2 / CF) * (x - xiStar) ≤ edgeV x ^ 2 := by
      calc (2 / CF) * (x - xiStar) ≤ (2 / CF) * (CF / 2 * edgeV x ^ 2) := by gcongr
        _ = edgeV x ^ 2 := by field_simp [hCF_pos.ne']
    have hrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hv_pos.le, Real.sqrt_mul (by positivity)] at hrt
    exact hrt
  · have hsq : edgeV x ^ 2 ≤ (2 / c₀) * (x - xiStar) := by
      calc edgeV x ^ 2 = (2 / c₀) * (c₀ / 2 * edgeV x ^ 2) := by field_simp [hc₀_pos.ne']
        _ ≤ (2 / c₀) * (x - xiStar) := by gcongr
    have hrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hv_pos.le, Real.sqrt_mul (by positivity)] at hrt
    exact hrt

/-- **(SD.6)** First convexity bound: `x - F(v) ≥ s_x (v_x - v)` for `0 ≤ v ≤ v_x`. -/
lemma edgeF_chord_lower {x v : ℝ} (hx : xiStar < x) (hv0 : 0 ≤ v) (hvx : v ≤ edgeV x) :
    slopeX x * (edgeV x - v) ≤ x - edgeF v := by
  let vx := edgeV x
  have hvx_pos : 0 < vx := edgeV_pos hx
  have hcont : Continuous edgeF' :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF' t).continuousAt
  have h0v : ∫ t in (0 : ℝ)..v, edgeF' t ≤ v * edgeF' v := by
    have hc : ∫ _t in (0 : ℝ)..v, edgeF' v = v * edgeF' v := by simp
    rw [← hc]
    exact intervalIntegral.integral_mono_on hv0 (hcont.intervalIntegrable _ _)
      intervalIntegrable_const fun t ht => edgeF'_strictMono.monotone ht.2
  have hvx_int : (vx - v) * edgeF' v ≤ ∫ t in v..vx, edgeF' t := by
    have hc : ∫ _t in v..vx, edgeF' v = (vx - v) * edgeF' v := by simp [smul_eq_mul]
    rw [← hc]
    exact intervalIntegral.integral_mono_on hvx intervalIntegrable_const
      (hcont.intervalIntegrable _ _) fun t ht => edgeF'_strictMono.monotone ht.1
  have h1 : (vx - v) * ∫ t in (0 : ℝ)..v, edgeF' t ≤ v * ∫ t in v..vx, edgeF' t := by
    calc (vx - v) * ∫ t in (0 : ℝ)..v, edgeF' t
        ≤ (vx - v) * (v * edgeF' v) := mul_le_mul_of_nonneg_left h0v (by linarith)
      _ = v * ((vx - v) * edgeF' v) := by ring
      _ ≤ v * ∫ t in v..vx, edgeF' t := mul_le_mul_of_nonneg_left hvx_int hv0
  have hsplit : ∫ t in (0 : ℝ)..vx, edgeF' t =
      (∫ t in (0 : ℝ)..v, edgeF' t) + (∫ t in v..vx, edgeF' t) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hdiff_all : x - xiStar = ∫ t in (0 : ℝ)..vx, edgeF' t := by
    rw [← edgeF_edgeV hx, ← edgeF_zero]; exact edgeF_sub_eq_integral
  have hdiff_v : x - edgeF v = ∫ t in v..vx, edgeF' t := by
    rw [← edgeF_edgeV hx]; exact edgeF_sub_eq_integral
  have hmul : (vx - v) * (x - xiStar) ≤ vx * (x - edgeF v) := by
    rw [hdiff_all, hdiff_v, hsplit]
    linarith
  unfold slopeX
  change (x - xiStar) / vx * (vx - v) ≤ x - edgeF v
  rw [div_mul_eq_mul_div, div_le_iff₀ hvx_pos]
  linarith

/-- **(SD.6)** Second convexity bound: `F(v) - x ≥ F'(v_x)(v - v_x)` for `v ≥ v_x`. -/
lemma edgeF_tangent_lower {x v : ℝ} (hx : xiStar < x) (hvx : edgeV x ≤ v) :
    edgeF' (edgeV x) * (v - edgeV x) ≤ edgeF v - x := by
  have hcont : Continuous edgeF' :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_edgeF' t).continuousAt
  have hdiff : edgeF v - x = ∫ t in (edgeV x)..v, edgeF' t := by
    have h_eq : edgeF v - edgeF (edgeV x) = ∫ t in (edgeV x)..v, edgeF' t :=
      edgeF_sub_eq_integral
    rwa [edgeF_edgeV hx] at h_eq
  have hc : ∫ _t in (edgeV x)..v, edgeF' (edgeV x) = edgeF' (edgeV x) * (v - edgeV x) := by
    simp [smul_eq_mul, mul_comm]
  rw [hdiff, ← hc]
  exact intervalIntegral.integral_mono_on hvx intervalIntegrable_const
    (hcont.intervalIntegrable _ _) fun t ht => edgeF'_strictMono.monotone ht.1

/-! ### 3. Abstract edge-phase hypothesis `(SD.2)` and modified phase `φ_x` -/

/-- Closed two-sided neighbourhood `𝒩_δ = {b : ℂ | |Im b - 1/2| ≤ δ}` around `E_+`. -/
def edgeStrip (δ : ℝ) : Set ℂ :=
  {b : ℂ | |b.im - 1 / 2| ≤ δ}

lemma edgeStrip_convex (δ : ℝ) : Convex ℝ (edgeStrip δ) := by
  intro x hx y hy a b ha hb hab
  change |((a • x + b • y : ℂ).im) - 1 / 2| ≤ δ
  have him : (a • x + b • y : ℂ).im = a * x.im + b * y.im := by
    simp [Complex.add_im, Complex.real_smul]
  rw [him]
  have hid : a * x.im + b * y.im - 1 / 2 = a * (x.im - 1 / 2) + b * (y.im - 1 / 2) := by
    calc a * x.im + b * y.im - 1 / 2 = a * x.im + b * y.im - (a + b) * (1 / 2) := by rw [hab, one_mul]
      _ = a * (x.im - 1 / 2) + b * (y.im - 1 / 2) := by ring
  rw [hid]
  calc |a * (x.im - 1 / 2) + b * (y.im - 1 / 2)|
      ≤ |a * (x.im - 1 / 2)| + |b * (y.im - 1 / 2)| := abs_add_le _ _
    _ = a * |x.im - 1 / 2| + b * |y.im - 1 / 2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * δ + b * δ := by
        have hx' : |x.im - 1 / 2| ≤ δ := hx
        have hy' : |y.im - 1 / 2| ≤ δ := hy
        gcongr
    _ = δ := by rw [← add_mul, hab, one_mul]

lemma mem_edgeStrip_edge {δ : ℝ} (hδ : 0 ≤ δ) (v : ℝ) :
    ((v : ℂ) + Complex.I / 2) ∈ edgeStrip δ := by
  change |((v : ℂ) + Complex.I / 2).im - 1 / 2| ≤ δ
  simpa using hδ

lemma bX_mem_edgeStrip {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) : bX x ∈ edgeStrip δ :=
  mem_edgeStrip_edge hδ (edgeV x)

/-- Abstract hypothesis packaging the leading edge potential properties `(SD.2)` from `Lemma SD_0`. -/
structure EdgePhaseData (δ C₃ C₄ : ℝ) (Φ₀ : ℂ → ℂ) : Prop where
  holo : AnalyticOnNhd ℂ Φ₀ (edgeStrip δ)
  re_edge : ∀ v : ℝ, (Φ₀ ((v : ℂ) + Complex.I / 2)).re = 0
  deriv_edge : ∀ v : ℝ,
    deriv Φ₀ ((v : ℂ) + Complex.I / 2) = -(4 * (Real.pi : ℂ) * Complex.I / 3) * (edgeF v : ℂ)
  deriv3_bound : ∀ b ∈ edgeStrip δ, ‖iteratedDeriv 3 Φ₀ b‖ ≤ C₃
  deriv4_bound : ∀ b ∈ edgeStrip δ, ‖iteratedDeriv 4 Φ₀ b‖ ≤ C₄

/-- Modified saddle phase `φ_x(b) = Φ₀(b) + i (4π/3) x (b - i/2)`. -/
noncomputable def phiX (Φ₀ : ℂ → ℂ) (x : ℝ) (b : ℂ) : ℂ :=
  Φ₀ b + Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (b - Complex.I / 2)

lemma phiX_analyticOnNhd {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) (x : ℝ) :
    AnalyticOnNhd ℂ (phiX Φ₀ x) (edgeStrip δ) := by
  intro b hb
  unfold phiX
  exact (hΦ.holo b hb).add (by fun_prop)

lemma phiX_re_edge {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) (x v : ℝ) :
    (phiX Φ₀ x ((v : ℂ) + Complex.I / 2)).re = 0 := by
  unfold phiX
  have hsub : ((v : ℂ) + Complex.I / 2) - Complex.I / 2 = (v : ℂ) := by ring
  rw [Complex.add_re, hΦ.re_edge v, hsub, zero_add]
  have hmul : Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (v : ℂ) =
      Complex.I * (((4 * Real.pi / 3 * x * v : ℝ)) : ℂ) := by push_cast; ring
  rw [hmul, Complex.mul_re]
  simp

lemma deriv_phiX {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀) (x : ℝ)
    {b : ℂ} (hb : b ∈ edgeStrip δ) :
    deriv (phiX Φ₀ x) b = deriv Φ₀ b + Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) := by
  have h1 : HasDerivAt Φ₀ (deriv Φ₀ b) b := (hΦ.holo b hb).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ => Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (z - Complex.I / 2))
      (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ)) b := by
    have := ((hasDerivAt_id b).sub_const (Complex.I / 2)).const_mul
      (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ))
    simpa using this
  exact (h1.add h2).deriv

lemma deriv_phiX_edge {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (hδ : 0 ≤ δ) (x v : ℝ) :
    deriv (phiX Φ₀ x) ((v : ℂ) + Complex.I / 2) =
      Complex.I * (4 * (Real.pi : ℂ) / 3) * ((x - edgeF v : ℝ) : ℂ) := by
  rw [deriv_phiX hΦ x (mem_edgeStrip_edge hδ v), hΦ.deriv_edge v]
  push_cast
  ring

lemma deriv_phiX_saddle {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (hδ : 0 ≤ δ) {x : ℝ} (hx : xiStar < x) :
    deriv (phiX Φ₀ x) (bX x) = 0 := by
  unfold bX
  rw [deriv_phiX_edge hΦ hδ x (edgeV x), edgeF_edgeV hx]
  simp

lemma iteratedDeriv2_phiX_edge {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (hδ : 0 ≤ δ) (x v : ℝ) :
    iteratedDeriv 2 (phiX Φ₀ x) ((v : ℂ) + Complex.I / 2) =
      -Complex.I * ((4 * Real.pi / 3 * edgeF' v : ℝ) : ℂ) := by
  let g : ℝ → ℂ := fun t => deriv (phiX Φ₀ x) ((t : ℂ) + Complex.I / 2)
  have hg_eq : g = fun t => Complex.I * (4 * (Real.pi : ℂ) / 3) * ((x - edgeF t : ℝ) : ℂ) := by
    ext t; exact deriv_phiX_edge hΦ hδ x t
  have hg_deriv_real : HasDerivAt g (-Complex.I * ((4 * Real.pi / 3 * edgeF' v : ℝ) : ℂ)) v := by
    rw [hg_eq]
    have hd_f : HasDerivAt (fun t : ℝ => x - edgeF t) (-edgeF' v) v :=
      (hasDerivAt_edgeF v).const_sub x
    have hd_c : HasDerivAt (fun t : ℝ => ((x - edgeF t : ℝ) : ℂ)) ((-edgeF' v : ℝ) : ℂ) v :=
      hd_f.ofReal_comp
    refine (hd_c.const_mul (Complex.I * (4 * (Real.pi : ℂ) / 3))).congr_deriv ?_
    push_cast; ring
  have h_an : AnalyticAt ℂ (deriv (phiX Φ₀ x)) ((v : ℂ) + Complex.I / 2) :=
    (phiX_analyticOnNhd hΦ x _ (mem_edgeStrip_edge hδ v)).deriv
  have hd_c : HasDerivAt (deriv (phiX Φ₀ x)) (deriv (deriv (phiX Φ₀ x)) ((v : ℂ) + Complex.I / 2))
      ((v : ℂ) + Complex.I / 2) := h_an.differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun t : ℝ => (t : ℂ) + Complex.I / 2) (1 : ℂ) v := by
    simpa using (Complex.ofRealCLM.hasDerivAt).add_const (Complex.I / 2)
  have hg_deriv_complex : HasDerivAt g (deriv (deriv (phiX Φ₀ x)) ((v : ℂ) + Complex.I / 2)) v := by
    have hc := (hd_c.scomp v hline).congr_deriv (one_smul _ _)
    change HasDerivAt (fun t : ℝ => deriv (phiX Φ₀ x) ((t : ℂ) + Complex.I / 2))
      (deriv (deriv (phiX Φ₀ x)) ((v : ℂ) + Complex.I / 2)) v
    simpa [Function.comp_def] using hc
  have heq := hg_deriv_complex.unique hg_deriv_real
  conv_lhs => rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact heq

lemma iteratedDeriv2_phiX_saddle {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (hδ : 0 ≤ δ) (x : ℝ) :
    iteratedDeriv 2 (phiX Φ₀ x) (bX x) = -Complex.I * (alphaX x : ℂ) := by
  unfold bX alphaX
  rw [iteratedDeriv2_phiX_edge hΦ hδ x (edgeV x)]

lemma iteratedDeriv_succ_phiX_ge2 {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (x : ℝ) {b : ℂ} (hb : b ∈ edgeStrip δ) (k : ℕ) (hk : 2 ≤ k) :
    iteratedDeriv k (phiX Φ₀ x) b = iteratedDeriv k Φ₀ b := by
  let S_an : Set ℂ := {z : ℂ | AnalyticAt ℂ Φ₀ z}
  have hS_open : IsOpen S_an := isOpen_analyticAt ℂ Φ₀
  have h_all : ∀ m : ℕ, ∀ z ∈ S_an, iteratedDeriv (m + 2) (phiX Φ₀ x) z = iteratedDeriv (m + 2) Φ₀ z := by
    intro m
    induction m with
    | zero =>
      intro z hz
      have hev : ∀ᶠ w in 𝓝 z, deriv (phiX Φ₀ x) w =
          deriv Φ₀ w + Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) := by
        filter_upwards [hS_open.mem_nhds hz] with w hw
        have h1 : HasDerivAt Φ₀ (deriv Φ₀ w) w := hw.differentiableAt.hasDerivAt
        have h2 : HasDerivAt (fun u : ℂ => Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ) * (u - Complex.I / 2))
            (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ)) w := by
          simpa using ((hasDerivAt_id w).sub_const (Complex.I / 2)).const_mul
            (Complex.I * (4 * (Real.pi : ℂ) / 3) * (x : ℂ))
        exact (h1.add h2).deriv
      have heq_d : deriv (deriv (phiX Φ₀ x)) z = deriv (deriv Φ₀) z := by
        rw [Filter.EventuallyEq.deriv_eq hev, deriv_add_const]
      rw [zero_add]
      conv_lhs => rw [iteratedDeriv_succ, iteratedDeriv_one]
      conv_rhs => rw [iteratedDeriv_succ, iteratedDeriv_one]
      exact heq_d
    | succ m ih =>
      intro z hz
      have hev : iteratedDeriv (m + 2) (phiX Φ₀ x) =ᶠ[𝓝 z] iteratedDeriv (m + 2) Φ₀ :=
        Filter.eventually_of_mem (hS_open.mem_nhds hz) ih
      conv_lhs => rw [iteratedDeriv_succ]
      conv_rhs => rw [iteratedDeriv_succ]
      exact Filter.EventuallyEq.deriv_eq hev
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  exact h_all m b (hΦ.holo b hb)

lemma iteratedDeriv3_phiX_bound {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (x : ℝ) {b : ℂ} (hb : b ∈ edgeStrip δ) :
    ‖iteratedDeriv 3 (phiX Φ₀ x) b‖ ≤ C₃ := by
  rw [iteratedDeriv_succ_phiX_ge2 hΦ x hb 3 (by norm_num)]
  exact hΦ.deriv3_bound b hb

lemma iteratedDeriv4_phiX_bound {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (x : ℝ) {b : ℂ} (hb : b ∈ edgeStrip δ) :
    ‖iteratedDeriv 4 (phiX Φ₀ x) b‖ ≤ C₄ := by
  rw [iteratedDeriv_succ_phiX_ge2 hΦ x hb 4 (by norm_num)]
  exact hΦ.deriv4_bound b hb

/-! ### 4. Iterated-FTC Taylor bounds along lines in `edgeStrip δ` -/

private lemma analyticAt_iteratedDeriv {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (k : ℕ) :
    AnalyticAt ℂ (iteratedDeriv k f) z := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv

private lemma iteratedDeriv_line_hasDerivAt {f : ℂ → ℂ} {S : Set ℂ} (hf : AnalyticOnNhd ℂ f S)
    {b₀ dir : ℂ} {t : ℝ} (ht : b₀ + (t : ℂ) * dir ∈ S) (k : ℕ) :
    HasDerivAt (fun s : ℝ => iteratedDeriv k f (b₀ + (s : ℂ) * dir) * dir ^ k)
      (iteratedDeriv (k + 1) f (b₀ + (t : ℂ) * dir) * dir ^ (k + 1)) t := by
  have han : AnalyticAt ℂ (iteratedDeriv k f) (b₀ + (t : ℂ) * dir) :=
    analyticAt_iteratedDeriv (hf _ ht) k
  have hd_c : HasDerivAt (iteratedDeriv k f) (deriv (iteratedDeriv k f) (b₀ + (t : ℂ) * dir))
      (b₀ + (t : ℂ) * dir) := han.differentiableAt.hasDerivAt
  have hline : HasDerivAt (fun s : ℝ => b₀ + (s : ℂ) * dir) dir t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * dir) dir t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const dir
    exact h1.const_add b₀
  have hcomp := (hd_c.scomp t hline).mul_const (dir ^ k)
  refine hcomp.congr_deriv ?_
  rw [iteratedDeriv_succ, pow_succ, smul_eq_mul]
  ring

private lemma iterated_ftc_norm_bound {e e' : ℝ → ℂ} {r C : ℝ} {k : ℕ}
    (_hr : 0 ≤ C) (he0 : e 0 = 0)
    (hderiv : ∀ t ∈ uIcc 0 r, HasDerivAt e (e' t) t)
    (hcont : ContinuousOn e' (uIcc 0 r))
    (hbound : ∀ t ∈ uIcc 0 r, ‖e' t‖ ≤ C * |t| ^ k) :
    ∀ t ∈ uIcc 0 r, ‖e t‖ ≤ C * |t| ^ (k + 1) / (k + 1 : ℝ) := by
  intro t ht
  have hsub : uIcc 0 t ⊆ uIcc 0 r := uIcc_subset_uIcc left_mem_uIcc ht
  have hftc : e t = ∫ s in (0 : ℝ)..t, e' s := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hderiv s (hsub hs)) ((hcont.mono hsub).intervalIntegrable)
    rw [he0, sub_zero] at h
    exact h.symm
  rw [hftc]
  have hnorm : ‖∫ s in (0 : ℝ)..t, e' s‖ ≤ |∫ s in (0 : ℝ)..t, ‖e' s‖| :=
    intervalIntegral.norm_integral_le_abs_integral_norm
  rcases le_total 0 t with ht0 | ht0
  · have hint1 : ∫ s in (0 : ℝ)..t, ‖e' s‖ ≤ ∫ s in (0 : ℝ)..t, C * s ^ k := by
      refine intervalIntegral.integral_mono_on ht0
        (((hcont.mono hsub).norm.mono (by rw [Set.uIcc_of_le ht0])).intervalIntegrable)
        ((by fun_prop : Continuous (fun s : ℝ => C * s ^ k)).intervalIntegrable 0 t)
        fun s hs => ?_
      have hs_u : s ∈ uIcc 0 r := hsub ((Set.uIcc_of_le ht0).symm ▸ hs)
      simpa [abs_of_nonneg hs.1] using hbound s hs_u
    have hint2 : ∫ s in (0 : ℝ)..t, C * s ^ k = C * t ^ (k + 1) / (k + 1 : ℝ) := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp [mul_div_assoc]
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, ‖e' s‖ :=
      intervalIntegral.integral_nonneg ht0 fun _ _ => norm_nonneg _
    rw [abs_of_nonneg hnn] at hnorm
    rw [abs_of_nonneg ht0]
    exact hnorm.trans (hint1.trans_eq hint2)
  · have h_swap : ∫ s in (0 : ℝ)..t, ‖e' s‖ = -(∫ s in t..0, ‖e' s‖) :=
      intervalIntegral.integral_symm t 0
    have hnn : 0 ≤ ∫ s in t..0, ‖e' s‖ :=
      intervalIntegral.integral_nonneg ht0 fun _ _ => norm_nonneg _
    rw [h_swap, abs_neg, abs_of_nonneg hnn] at hnorm
    have hint1 : ∫ s in t..0, ‖e' s‖ ≤ ∫ s in t..0, C * (-s) ^ k := by
      refine intervalIntegral.integral_mono_on ht0
        (((hcont.mono hsub).norm.mono (by rw [uIcc_comm])).intervalIntegrable)
        ((by fun_prop : Continuous (fun s : ℝ => C * (-s) ^ k)).intervalIntegrable t 0)
        fun s hs => ?_
      have hs_u : s ∈ uIcc 0 r := hsub ((Set.uIcc_of_ge ht0).symm ▸ hs)
      simpa [abs_of_nonpos hs.2] using hbound s hs_u
    have hint2 : ∫ s in t..0, C * (-s) ^ k = C * (-t) ^ (k + 1) / (k + 1 : ℝ) := by
      have hcomp := intervalIntegral.integral_comp_neg (a := t) (b := 0) (fun s : ℝ => C * s ^ k)
      simp only [neg_zero] at hcomp
      rw [hcomp, intervalIntegral.integral_const_mul, integral_pow]
      simp [mul_div_assoc]
    rw [abs_of_nonpos ht0]
    exact hnorm.trans (hint1.trans_eq hint2)

lemma line_taylor_order2_le {f : ℂ → ℂ} {S : Set ℂ} (hf : AnalyticOnNhd ℂ f S)
    {b₀ dir : ℂ} (hdir : ‖dir‖ = 1) {C₃ r : ℝ} (hC₃_nn : 0 ≤ C₃)
    (hmem : ∀ t ∈ uIcc 0 r, b₀ + (t : ℂ) * dir ∈ S)
    (hC₃ : ∀ t ∈ uIcc 0 r, ‖iteratedDeriv 3 f (b₀ + (t : ℂ) * dir)‖ ≤ C₃) :
    ‖f (b₀ + (r : ℂ) * dir) - f b₀ - deriv f b₀ * dir * (r : ℂ) -
      (1 / 2 : ℂ) * iteratedDeriv 2 f b₀ * dir ^ 2 * (r : ℂ) ^ 2‖ ≤ C₃ * |r| ^ 3 / 6 := by
  let g₀ : ℝ → ℂ := fun t => f (b₀ + (t : ℂ) * dir)
  let g₁ : ℝ → ℂ := fun t => deriv f (b₀ + (t : ℂ) * dir) * dir
  let g₂ : ℝ → ℂ := fun t => iteratedDeriv 2 f (b₀ + (t : ℂ) * dir) * dir ^ 2
  let g₃ : ℝ → ℂ := fun t => iteratedDeriv 3 f (b₀ + (t : ℂ) * dir) * dir ^ 3
  have hd0 : ∀ t ∈ uIcc 0 r, HasDerivAt g₀ (g₁ t) t := fun t ht => by
    simpa [g₀, g₁, iteratedDeriv_zero, iteratedDeriv_one] using
      iteratedDeriv_line_hasDerivAt hf (hmem t ht) 0
  have hd1 : ∀ t ∈ uIcc 0 r, HasDerivAt g₁ (g₂ t) t := fun t ht => by
    simpa [g₁, g₂, iteratedDeriv_one] using iteratedDeriv_line_hasDerivAt hf (hmem t ht) 1
  have hd2 : ∀ t ∈ uIcc 0 r, HasDerivAt g₂ (g₃ t) t := fun t ht => by
    simpa [g₂, g₃] using iteratedDeriv_line_hasDerivAt hf (hmem t ht) 2
  have hc_line : Continuous (fun s : ℝ => b₀ + (s : ℂ) * dir) := by fun_prop
  have hc_g₂ : ContinuousOn g₂ (uIcc 0 r) := fun t ht => (hd2 t ht).continuousAt.continuousWithinAt
  have hc_g₃ : ContinuousOn g₃ (uIcc 0 r) := fun t ht =>
    ((analyticAt_iteratedDeriv (hf _ (hmem t ht)) 3).continuousAt.comp_of_eq
      hc_line.continuousAt rfl).mul continuousAt_const |>.continuousWithinAt
  let e₂ : ℝ → ℂ := fun t => g₂ t - g₂ 0
  have hb2 : ∀ t ∈ uIcc 0 r, ‖e₂ t‖ ≤ C₃ * |t| ^ 1 := by
    have h := iterated_ftc_norm_bound (k := 0) hC₃_nn (by simp)
      (fun t ht => (hd2 t ht).sub_const (g₂ 0)) hc_g₃
      fun t ht => by
        dsimp [g₃]
        rw [norm_mul, norm_pow, hdir, one_pow, mul_one, pow_zero, mul_one]
        exact hC₃ t ht
    intro t ht
    simpa using h t ht
  let e₁ : ℝ → ℂ := fun t => g₁ t - g₁ 0 - g₂ 0 * (t : ℂ)
  have he₁_d : ∀ t ∈ uIcc 0 r, HasDerivAt e₁ (e₂ t) t := fun t ht => by
    have hlin : HasDerivAt (fun s : ℝ => g₂ 0 * (s : ℂ)) (g₂ 0) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt).const_mul (g₂ 0)
    exact ((hd1 t ht).sub_const (g₁ 0)).sub hlin
  have hb1 : ∀ t ∈ uIcc 0 r, ‖e₁ t‖ ≤ (C₃ / 2) * |t| ^ 2 := by
    have h := iterated_ftc_norm_bound (k := 1) hC₃_nn (by simp [e₁]) he₁_d
      (hc_g₂.sub continuousOn_const) hb2
    intro t ht
    have h1 := h t ht
    norm_num at h1
    rw [sq_abs]
    linarith
  let e₀ : ℝ → ℂ := fun t => g₀ t - g₀ 0 - g₁ 0 * (t : ℂ) - (1 / 2 : ℂ) * g₂ 0 * (t : ℂ) ^ 2
  have he₀_d : ∀ t ∈ uIcc 0 r, HasDerivAt e₀ (e₁ t) t := fun t ht => by
    have hl1 : HasDerivAt (fun s : ℝ => g₁ 0 * (s : ℂ)) (g₁ 0) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt).const_mul (g₁ 0)
    have hl2 : HasDerivAt (fun s : ℝ => (1 / 2 : ℂ) * g₂ 0 * (s : ℂ) ^ 2) (g₂ 0 * (t : ℂ)) t := by
      have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ) ^ 1 * 1) t :=
        (Complex.ofRealCLM.hasDerivAt).pow 2
      exact (hsq.const_mul ((1 / 2 : ℂ) * g₂ 0)).congr_deriv (by ring)
    exact ((((hd0 t ht).sub_const (g₀ 0)).sub hl1).sub hl2).congr_deriv (by dsimp [e₁])
  have hc_e₁ : ContinuousOn e₁ (uIcc 0 r) := fun t ht => (he₁_d t ht).continuousAt.continuousWithinAt
  have hb0 : ∀ t ∈ uIcc 0 r, ‖e₀ t‖ ≤ (C₃ / 2) * |t| ^ (2 + 1) / (2 + 1 : ℝ) :=
    iterated_ftc_norm_bound (k := 2) (by positivity) (by simp [e₀]) he₀_d hc_e₁ hb1
  have hres := hb0 r right_mem_uIcc
  norm_num at hres
  have h_alg : C₃ / 2 * |r| ^ 3 / 3 = C₃ * |r| ^ 3 / 6 := by ring
  rw [h_alg] at hres
  simpa [e₀, g₀, g₁, g₂, mul_assoc] using hres

lemma line_taylor_order3_le {f : ℂ → ℂ} {S : Set ℂ} (hf : AnalyticOnNhd ℂ f S)
    {b₀ dir : ℂ} (hdir : ‖dir‖ = 1) {C₄ r : ℝ} (hC₄_nn : 0 ≤ C₄)
    (hmem : ∀ t ∈ uIcc 0 r, b₀ + (t : ℂ) * dir ∈ S)
    (hC₄ : ∀ t ∈ uIcc 0 r, ‖iteratedDeriv 4 f (b₀ + (t : ℂ) * dir)‖ ≤ C₄) :
    ‖f (b₀ + (r : ℂ) * dir) - f b₀ - deriv f b₀ * dir * (r : ℂ) -
      (1 / 2 : ℂ) * iteratedDeriv 2 f b₀ * dir ^ 2 * (r : ℂ) ^ 2 -
      (1 / 6 : ℂ) * iteratedDeriv 3 f b₀ * dir ^ 3 * (r : ℂ) ^ 3‖ ≤ C₄ * r ^ 4 / 24 := by
  let g₀ : ℝ → ℂ := fun t => f (b₀ + (t : ℂ) * dir)
  let g₁ : ℝ → ℂ := fun t => deriv f (b₀ + (t : ℂ) * dir) * dir
  let g₂ : ℝ → ℂ := fun t => iteratedDeriv 2 f (b₀ + (t : ℂ) * dir) * dir ^ 2
  let g₃ : ℝ → ℂ := fun t => iteratedDeriv 3 f (b₀ + (t : ℂ) * dir) * dir ^ 3
  let g₄ : ℝ → ℂ := fun t => iteratedDeriv 4 f (b₀ + (t : ℂ) * dir) * dir ^ 4
  have hd0 : ∀ t ∈ uIcc 0 r, HasDerivAt g₀ (g₁ t) t := fun t ht => by
    simpa [g₀, g₁, iteratedDeriv_zero, iteratedDeriv_one] using
      iteratedDeriv_line_hasDerivAt hf (hmem t ht) 0
  have hd1 : ∀ t ∈ uIcc 0 r, HasDerivAt g₁ (g₂ t) t := fun t ht => by
    simpa [g₁, g₂, iteratedDeriv_one] using iteratedDeriv_line_hasDerivAt hf (hmem t ht) 1
  have hd2 : ∀ t ∈ uIcc 0 r, HasDerivAt g₂ (g₃ t) t := fun t ht => by
    simpa [g₂, g₃] using iteratedDeriv_line_hasDerivAt hf (hmem t ht) 2
  have hd3 : ∀ t ∈ uIcc 0 r, HasDerivAt g₃ (g₄ t) t := fun t ht => by
    simpa [g₃, g₄] using iteratedDeriv_line_hasDerivAt hf (hmem t ht) 3
  have hc_line : Continuous (fun s : ℝ => b₀ + (s : ℂ) * dir) := by fun_prop
  have hc_g₃ : ContinuousOn g₃ (uIcc 0 r) := fun t ht => (hd3 t ht).continuousAt.continuousWithinAt
  have hc_g₄ : ContinuousOn g₄ (uIcc 0 r) := fun t ht =>
    ((analyticAt_iteratedDeriv (hf _ (hmem t ht)) 4).continuousAt.comp_of_eq
      hc_line.continuousAt rfl).mul continuousAt_const |>.continuousWithinAt
  let e₃ : ℝ → ℂ := fun t => g₃ t - g₃ 0
  have hb3 : ∀ t ∈ uIcc 0 r, ‖e₃ t‖ ≤ C₄ * |t| ^ 1 := by
    have h := iterated_ftc_norm_bound (k := 0) hC₄_nn (by simp)
      (fun t ht => (hd3 t ht).sub_const (g₃ 0)) hc_g₄
      fun t ht => by
        dsimp [g₄]
        rw [norm_mul, norm_pow, hdir, one_pow, mul_one, pow_zero, mul_one]
        exact hC₄ t ht
    intro t ht
    simpa using h t ht
  let e₂ : ℝ → ℂ := fun t => g₂ t - g₂ 0 - g₃ 0 * (t : ℂ)
  have he₂_d : ∀ t ∈ uIcc 0 r, HasDerivAt e₂ (e₃ t) t := fun t ht => by
    have hlin : HasDerivAt (fun s : ℝ => g₃ 0 * (s : ℂ)) (g₃ 0) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt).const_mul (g₃ 0)
    exact ((hd2 t ht).sub_const (g₂ 0)).sub hlin
  have hb2 : ∀ t ∈ uIcc 0 r, ‖e₂ t‖ ≤ (C₄ / 2) * |t| ^ 2 := by
    have h := iterated_ftc_norm_bound (k := 1) hC₄_nn (by simp [e₂]) he₂_d
      (hc_g₃.sub continuousOn_const) hb3
    intro t ht
    have ht' := h t ht
    norm_num at ht'
    rw [sq_abs]
    linarith
  let e₁ : ℝ → ℂ := fun t => g₁ t - g₁ 0 - g₂ 0 * (t : ℂ) - (1 / 2 : ℂ) * g₃ 0 * (t : ℂ) ^ 2
  have he₁_d : ∀ t ∈ uIcc 0 r, HasDerivAt e₁ (e₂ t) t := fun t ht => by
    have hl1 : HasDerivAt (fun s : ℝ => g₂ 0 * (s : ℂ)) (g₂ 0) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt).const_mul (g₂ 0)
    have hl2 : HasDerivAt (fun s : ℝ => (1 / 2 : ℂ) * g₃ 0 * (s : ℂ) ^ 2) (g₃ 0 * (t : ℂ)) t := by
      have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ) ^ 1 * 1) t :=
        (Complex.ofRealCLM.hasDerivAt).pow 2
      exact (hsq.const_mul ((1 / 2 : ℂ) * g₃ 0)).congr_deriv (by ring)
    exact ((((hd1 t ht).sub_const (g₁ 0)).sub hl1).sub hl2).congr_deriv (by dsimp [e₂])
  have hc_e₂ : ContinuousOn e₂ (uIcc 0 r) := fun t ht => (he₂_d t ht).continuousAt.continuousWithinAt
  have hb1 : ∀ t ∈ uIcc 0 r, ‖e₁ t‖ ≤ (C₄ / 6) * |t| ^ 3 := by
    have h := iterated_ftc_norm_bound (k := 2) (by positivity) (by simp [e₁]) he₁_d hc_e₂ hb2
    intro t ht
    have ht' := h t ht
    norm_num at ht'
    linarith
  let e₀ : ℝ → ℂ := fun t =>
    g₀ t - g₀ 0 - g₁ 0 * (t : ℂ) - (1 / 2 : ℂ) * g₂ 0 * (t : ℂ) ^ 2 -
      (1 / 6 : ℂ) * g₃ 0 * (t : ℂ) ^ 3
  have he₀_d : ∀ t ∈ uIcc 0 r, HasDerivAt e₀ (e₁ t) t := fun t ht => by
    have hl1 : HasDerivAt (fun s : ℝ => g₁ 0 * (s : ℂ)) (g₁ 0) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt).const_mul (g₁ 0)
    have hl2 : HasDerivAt (fun s : ℝ => (1 / 2 : ℂ) * g₂ 0 * (s : ℂ) ^ 2) (g₂ 0 * (t : ℂ)) t := by
      have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ) ^ 1 * 1) t :=
        (Complex.ofRealCLM.hasDerivAt).pow 2
      exact (hsq.const_mul ((1 / 2 : ℂ) * g₂ 0)).congr_deriv (by ring)
    have hl3 : HasDerivAt (fun s : ℝ => (1 / 6 : ℂ) * g₃ 0 * (s : ℂ) ^ 3)
        ((1 / 2 : ℂ) * g₃ 0 * (t : ℂ) ^ 2) t := by
      have hcb : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 3) (3 * (t : ℂ) ^ 2 * 1) t :=
        (Complex.ofRealCLM.hasDerivAt).pow 3
      exact (hcb.const_mul ((1 / 6 : ℂ) * g₃ 0)).congr_deriv (by ring)
    exact (((((hd0 t ht).sub_const (g₀ 0)).sub hl1).sub hl2).sub hl3).congr_deriv (by dsimp [e₁])
  have hc_e₁ : ContinuousOn e₁ (uIcc 0 r) := fun t ht => (he₁_d t ht).continuousAt.continuousWithinAt
  have hb0 : ∀ t ∈ uIcc 0 r, ‖e₀ t‖ ≤ (C₄ / 6) * |t| ^ (3 + 1) / (3 + 1 : ℝ) :=
    iterated_ftc_norm_bound (k := 3) (by positivity) (by simp [e₀]) he₀_d hc_e₁ hb1
  have hres := hb0 r right_mem_uIcc
  norm_num at hres
  have h_alg : C₄ / 6 * |r| ^ 4 / 4 = C₄ * r ^ 4 / 24 := by
    have h4 : |r| ^ 4 = r ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, pow_mul, sq_abs]
    rw [h4]; ring
  rw [h_alg] at hres
  simpa [e₀, g₀, g₁, g₂, g₃, mul_assoc] using hres

/-! ### 5. Normal Taylor `(SD.7)` and local saddle Taylor expansions -/

/-- **(SD.7)** Taylor formula normal to the edge:
`Re φ_x(v + i(1/2 + u)) = (4π/3) u (F(v) - x) + R(v, u)` with `|R(v, u)| ≤ C₃ |u|³ / 6`. -/
lemma phiX_re_normal_taylor {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (hδ : 0 ≤ δ) (x v u : ℝ) (hu : |u| ≤ δ) :
    |(phiX Φ₀ x ((v : ℂ) + Complex.I * ((1 / 2 + u : ℝ) : ℂ))).re -
      (4 * Real.pi / 3) * u * (edgeF v - x)| ≤ C₃ * |u| ^ 3 / 6 := by
  let b₀ : ℂ := (v : ℂ) + Complex.I / 2
  have hC₃_nn : 0 ≤ C₃ := (norm_nonneg _).trans (hΦ.deriv3_bound b₀ (mem_edgeStrip_edge hδ v))
  have hmem : ∀ t ∈ uIcc 0 u, b₀ + (t : ℂ) * Complex.I ∈ edgeStrip δ := by
    intro t ht
    change |((b₀ + (t : ℂ) * Complex.I).im) - 1 / 2| ≤ δ
    have him : (b₀ + (t : ℂ) * Complex.I).im - 1 / 2 = t := by
      dsimp [b₀]; simp
    rw [him]
    rcases le_total 0 u with hu0 | hu0
    · rw [Set.uIcc_of_le hu0] at ht
      rw [abs_of_nonneg ht.1]
      exact ht.2.trans (by simpa [abs_of_nonneg hu0] using hu)
    · rw [Set.uIcc_of_ge hu0] at ht
      rw [abs_of_nonpos ht.2]
      have : -u ≤ δ := by simpa [abs_of_nonpos hu0] using hu
      linarith [ht.1]
  have hC₃ : ∀ t ∈ uIcc 0 u, ‖iteratedDeriv 3 (phiX Φ₀ x) (b₀ + (t : ℂ) * Complex.I)‖ ≤ C₃ :=
    fun t ht => iteratedDeriv3_phiX_bound hΦ x (hmem t ht)
  have h_lin := line_taylor_order2_le (phiX_analyticOnNhd hΦ x) Complex.norm_I hC₃_nn hmem hC₃
  have h_pt : b₀ + (u : ℂ) * Complex.I = (v : ℂ) + Complex.I * ((1 / 2 + u : ℝ) : ℂ) := by
    dsimp [b₀]; push_cast; ring
  have h_d1 : deriv (phiX Φ₀ x) b₀ * Complex.I * (u : ℂ) =
      (((4 * Real.pi / 3) * u * (edgeF v - x) : ℝ) : ℂ) := by
    dsimp [b₀]
    rw [deriv_phiX_edge hΦ hδ x v]
    push_cast
    have hI2 : Complex.I * Complex.I = -1 := by simp [Complex.I_mul_I]
    calc Complex.I * (4 * (Real.pi : ℂ) / 3) * ((x : ℂ) - (edgeF v : ℂ)) * Complex.I * (u : ℂ)
        = (Complex.I * Complex.I) * (4 * (Real.pi : ℂ) / 3) * ((x : ℂ) - (edgeF v : ℂ)) * (u : ℂ) := by ring
      _ = (-1) * (4 * (Real.pi : ℂ) / 3) * ((x : ℂ) - (edgeF v : ℂ)) * (u : ℂ) := by rw [hI2]
      _ = 4 * (Real.pi : ℂ) / 3 * (u : ℂ) * ((edgeF v : ℂ) - (x : ℂ)) := by ring
  have h_d2 : ((1 / 2 : ℂ) * iteratedDeriv 2 (phiX Φ₀ x) b₀ * Complex.I ^ 2 * (u : ℂ) ^ 2).re = 0 := by
    dsimp [b₀]
    rw [iteratedDeriv2_phiX_edge hΦ hδ x v, Complex.I_sq]
    have heq : (1 / 2 : ℂ) * (-Complex.I * ((4 * Real.pi / 3 * edgeF' v : ℝ) : ℂ)) * (-1) *
        (u : ℂ) ^ 2 = Complex.I * (((1 / 2 * (4 * Real.pi / 3 * edgeF' v) * u ^ 2 : ℝ)) : ℂ) := by
      push_cast; ring
    rw [heq]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_re_diff : (phiX Φ₀ x ((v : ℂ) + Complex.I * ((1 / 2 + u : ℝ) : ℂ))).re -
      (4 * Real.pi / 3) * u * (edgeF v - x) =
      (phiX Φ₀ x (b₀ + (u : ℂ) * Complex.I) - phiX Φ₀ x b₀ -
        deriv (phiX Φ₀ x) b₀ * Complex.I * (u : ℂ) -
        (1 / 2 : ℂ) * iteratedDeriv 2 (phiX Φ₀ x) b₀ * Complex.I ^ 2 * (u : ℂ) ^ 2).re := by
    rw [h_pt, Complex.sub_re, Complex.sub_re, Complex.sub_re, phiX_re_edge hΦ x v, sub_zero,
      h_d1, Complex.ofReal_re, h_d2, sub_zero]
  rw [h_re_diff]
  exact (Complex.abs_re_le_norm _).trans h_lin

private lemma norm_exp_neg_I_pi_div_four :
    ‖Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))‖ = 1 := by
  rw [show -Complex.I * (Real.pi / 4 : ℂ) = ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

private lemma exp_neg_I_pi_div_four_sq :
    Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) ^ 2 = -Complex.I := by
  rw [← Complex.exp_nat_mul]
  have h1 : ((2 : ℕ) : ℂ) * (-Complex.I * (Real.pi / 4 : ℂ)) =
      ((-Real.pi / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    show (-Real.pi / 2 : ℝ) = -(Real.pi / 2) by ring, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

private lemma local_line_mem_edgeStrip {δ x r : ℝ} (_hδ : 0 ≤ δ) (hr : |r| ≤ √2 * δ) :
    ∀ t ∈ uIcc 0 r, bX x + (t : ℂ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) ∈ edgeStrip δ := by
  intro t ht
  change |((bX x + (t : ℂ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))).im) - 1 / 2| ≤ δ
  have h_im_dir : (Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))).im = -(1 / √2) := by
    rw [show -Complex.I * (Real.pi / 4 : ℂ) = ((-Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_im, show -Real.pi / 4 = -(Real.pi / 4) by ring, Real.sin_neg,
      Real.sin_pi_div_four]
    have hsq : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
    have hs : √2 ≠ 0 := (Real.sqrt_pos.mpr zero_lt_two).ne'
    field_simp [hs]
    linarith [hsq]
  have him : (bX x + (t : ℂ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))).im - 1 / 2 =
      -t / √2 := by
    simp only [bX, Complex.add_im, Complex.ofReal_im, Complex.div_ofNat_im, Complex.I_im,
      Complex.im_ofReal_mul, zero_add]
    rw [h_im_dir]
    ring
  rw [him, abs_div, abs_neg, abs_of_pos (Real.sqrt_pos.mpr zero_lt_two)]
  have ht_abs : |t| ≤ |r| := by
    rcases le_total 0 r with hr0 | hr0
    · rw [Set.uIcc_of_le hr0] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg hr0]; exact ht.2
    · rw [Set.uIcc_of_ge hr0] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos hr0]; linarith [ht.1]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr zero_lt_two)]
  calc |t| ≤ |r| := ht_abs
    _ ≤ √2 * δ := hr
    _ = δ * √2 := mul_comm _ _

lemma phiX_local_quad_bound {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (hδ : 0 ≤ δ) {x r : ℝ} (hx : xiStar < x) (hr : |r| ≤ √2 * δ) :
    ‖phiX Φ₀ x (bX x + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))) -
      phiX Φ₀ x (bX x) + (1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2‖ ≤ C₃ * |r| ^ 3 / 6 := by
  let dir := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))
  have hC₃_nn : 0 ≤ C₃ := (norm_nonneg _).trans (hΦ.deriv3_bound (bX x) (bX_mem_edgeStrip hδ x))
  have hmem := local_line_mem_edgeStrip hδ (x := x) hr
  have hC₃ : ∀ t ∈ uIcc 0 r, ‖iteratedDeriv 3 (phiX Φ₀ x) (bX x + (t : ℂ) * dir)‖ ≤ C₃ :=
    fun t ht => iteratedDeriv3_phiX_bound hΦ x (hmem t ht)
  have h := line_taylor_order2_le (phiX_analyticOnNhd hΦ x) norm_exp_neg_I_pi_div_four hC₃_nn hmem hC₃
  rw [deriv_phiX_saddle hΦ hδ hx, iteratedDeriv2_phiX_saddle hΦ hδ x,
    exp_neg_I_pi_div_four_sq] at h
  have halg : phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x) -
      0 * dir * (r : ℂ) - (1 / 2 : ℂ) * (-Complex.I * (alphaX x : ℂ)) * (-Complex.I) * (r : ℂ) ^ 2 =
      phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x) +
        (1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2 := by
    linear_combination -(1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2 * Complex.I_sq
  rwa [halg] at h

lemma phiX_local_re_le {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (hδ : 0 ≤ δ) {x r : ℝ} (hx : xiStar < x) (hr : |r| ≤ √2 * δ)
    (h_small : C₃ * |r| ≤ alphaX x) :
    (phiX Φ₀ x (bX x + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))) -
      phiX Φ₀ x (bX x)).re ≤ -alphaX x * r ^ 2 / 3 := by
  have hq := phiX_local_quad_bound hΦ hδ hx hr
  have hre : (phiX Φ₀ x (bX x + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))) -
      phiX Φ₀ x (bX x) + (1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2).re ≤ C₃ * |r| ^ 3 / 6 :=
    (Complex.re_le_norm _).trans hq
  have hr2 : ((1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2).re = alphaX x * r ^ 2 / 2 := by
    have : (1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2 = ((alphaX x * r ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [Complex.add_re, hr2] at hre
  have h_cub : C₃ * |r| ^ 3 / 6 ≤ alphaX x * r ^ 2 / 6 := by
    have : |r| ^ 3 = |r| * r ^ 2 := by rw [pow_succ', sq_abs]
    rw [this]
    nlinarith [sq_nonneg r]
  linarith

lemma phiX_local_cubic_bound {δ C₃ C₄ : ℝ} {Φ₀ : ℂ → ℂ} (hΦ : EdgePhaseData δ C₃ C₄ Φ₀)
    (hδ : 0 ≤ δ) {x r : ℝ} (hx : xiStar < x) (hr : |r| ≤ √2 * δ) :
    ‖phiX Φ₀ x (bX x + (r : ℂ) * Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))) -
      phiX Φ₀ x (bX x) + (1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2 -
      (1 / 6 : ℂ) * iteratedDeriv 3 Φ₀ (bX x) *
        Complex.exp (-Complex.I * (Real.pi / 4 : ℂ)) ^ 3 * (r : ℂ) ^ 3‖ ≤ C₄ * r ^ 4 / 24 := by
  let dir := Complex.exp (-Complex.I * (Real.pi / 4 : ℂ))
  have hC₄_nn : 0 ≤ C₄ := (norm_nonneg _).trans (hΦ.deriv4_bound (bX x) (bX_mem_edgeStrip hδ x))
  have hmem := local_line_mem_edgeStrip hδ (x := x) hr
  have hC₄ : ∀ t ∈ uIcc 0 r, ‖iteratedDeriv 4 (phiX Φ₀ x) (bX x + (t : ℂ) * dir)‖ ≤ C₄ :=
    fun t ht => iteratedDeriv4_phiX_bound hΦ x (hmem t ht)
  have h := line_taylor_order3_le (phiX_analyticOnNhd hΦ x) norm_exp_neg_I_pi_div_four hC₄_nn hmem hC₄
  rw [deriv_phiX_saddle hΦ hδ hx, iteratedDeriv2_phiX_saddle hΦ hδ x,
    exp_neg_I_pi_div_four_sq,
    iteratedDeriv_succ_phiX_ge2 hΦ x (bX_mem_edgeStrip hδ x) 3 (by norm_num)] at h
  have halg : phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x) -
      0 * dir * (r : ℂ) - (1 / 2 : ℂ) * (-Complex.I * (alphaX x : ℂ)) * (-Complex.I) * (r : ℂ) ^ 2 -
      (1 / 6 : ℂ) * iteratedDeriv 3 Φ₀ (bX x) * dir ^ 3 * (r : ℂ) ^ 3 =
      phiX Φ₀ x (bX x + (r : ℂ) * dir) - phiX Φ₀ x (bX x) +
        (1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2 -
        (1 / 6 : ℂ) * iteratedDeriv 3 Φ₀ (bX x) * dir ^ 3 * (r : ℂ) ^ 3 := by
    linear_combination -(1 / 2 : ℂ) * (alphaX x : ℂ) * (r : ℂ) ^ 2 * Complex.I_sq
  rwa [halg] at h

/-! ### 6. Primitives on a horizontal strip and non-vacuity of `EdgePhaseData` -/

/-- Any holomorphic function on an open horizontal strip `|Im z - c₀| < r` has `wedgeIntegral`
from `c₀ * I` as a global primitive on that strip. -/
lemma hasDerivAt_wedgeIntegral_strip {f : ℂ → ℂ} {c₀ r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im - c₀| < r}) :
    ∀ z ∈ {z : ℂ | |z.im - c₀| < r},
      HasDerivAt (fun w => Complex.wedgeIntegral (Complex.I * (c₀ : ℂ)) w f) (f z) z := by
  let U : Set ℂ := {z : ℂ | |z.im - c₀| < r}
  let z₀ : ℂ := Complex.I * (c₀ : ℂ)
  intro z hz
  have hU_open : IsOpen U := isOpen_lt ((continuous_abs.comp (Complex.continuous_im.sub continuous_const)))
    continuous_const
  have hU_conv : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    change |((a • x + b • y : ℂ).im) - c₀| < r
    have him : (a • x + b • y : ℂ).im - c₀ = a * (x.im - c₀) + b * (y.im - c₀) := by
      simp [Complex.add_im, Complex.real_smul]
      calc a * x.im + b * y.im - c₀ = a * x.im + b * y.im - (a + b) * c₀ := by rw [hab, one_mul]
        _ = a * (x.im - c₀) + b * (y.im - c₀) := by ring
    rw [him]
    calc |a * (x.im - c₀) + b * (y.im - c₀)|
        ≤ a * |x.im - c₀| + b * |y.im - c₀| := by
          calc |a * (x.im - c₀) + b * (y.im - c₀)| ≤ |a * (x.im - c₀)| + |b * (y.im - c₀)| := abs_add_le _ _
            _ = a * |x.im - c₀| + b * |y.im - c₀| := by
                rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < a * r + b * r := by
          rcases eq_or_lt_of_le ha with rfl | ha'
          · simp only [zero_mul, zero_add] at hab ⊢
            subst hab
            rw [one_mul, one_mul]
            exact hy
          · have h1 : a * |x.im - c₀| < a * r := mul_lt_mul_of_pos_left hx ha'
            have h2 : b * |y.im - c₀| ≤ b * r := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
            linarith
      _ = r := by rw [← add_mul, hab, one_mul]
  let ρ : ℝ := r - |z.im - c₀|
  have hρ : 0 < ρ := sub_pos.mpr hz
  have hball_sub : ball z ρ ⊆ U := fun w hw => by
    have hdist : |w.im - z.im| < ρ := by
      calc |w.im - z.im| = |(w - z).im| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        _ < ρ := mem_ball_iff_norm.mp hw
    change |w.im - c₀| < r
    calc |w.im - c₀| ≤ |w.im - z.im| + |z.im - c₀| := by
          simpa [sub_add_sub_cancel] using abs_add_le (w.im - z.im) (z.im - c₀)
      _ < ρ + |z.im - c₀| := by linarith
      _ = r := by dsimp [ρ]; ring
  have hcons_U : Complex.IsConservativeOn f U := hf.isConservativeOn
  have hcons_ball : Complex.IsConservativeOn f (ball z ρ) := hcons_U.mono hball_sub
  have hd_wedge : HasDerivAt (fun w => Complex.wedgeIntegral z w f) (f z) z :=
    hcons_ball.hasDerivAt_wedgeIntegral (hf.continuousOn.mono hball_sub) (mem_ball_self hρ)
  have hev : (fun w => Complex.wedgeIntegral z₀ w f) =ᶠ[𝓝 z]
      (fun w => Complex.wedgeIntegral z₀ z f + Complex.wedgeIntegral z w f) := by
    refine eventually_nhds_iff_ball.mpr ⟨ρ, hρ, fun w hw => ?_⟩
    have hwU : w ∈ U := hball_sub hw
    have hz₀U : z₀ ∈ U := by
      change |z₀.im - c₀| < r
      simpa [z₀] using hr
    have h_hor (a₁ a₂ b : ℝ) (h1 : a₁ + b * Complex.I ∈ U) (_h2 : a₂ + b * Complex.I ∈ U) :
        IntervalIntegrable (fun x : ℝ => f (x + b * Complex.I)) volume a₁ a₂ := by
      refine (hf.continuousOn.comp (by fun_prop) fun x _ => ?_).intervalIntegrable
      have hb' : |b - c₀| < r := by simpa [U] using h1
      simpa [U] using hb'
    have h_ver (a b₁ b₂ : ℝ) (h1 : a + b₁ * Complex.I ∈ U) (h2 : a + b₂ * Complex.I ∈ U) :
        IntervalIntegrable (fun y : ℝ => f (a + y * Complex.I)) volume b₁ b₂ := by
      refine (hf.continuousOn.comp (by fun_prop) fun y hy => ?_).intervalIntegrable
      have h1' : |b₁ - c₀| < r := by simpa [U] using h1
      have h2' : |b₂ - c₀| < r := by simpa [U] using h2
      rw [abs_lt] at h1' h2'
      have hy_bd : |y - c₀| < r := by
        rw [abs_lt]
        rcases mem_uIcc.mp hy with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;> constructor <;> linarith
      simpa [U] using hy_bd
    have hre_z₀ : z₀.re = 0 := by simp [z₀]
    have him_z₀ : z₀.im = c₀ := by simp [z₀]
    have hz_z₀ : (z.re : ℂ) + (z₀.im : ℂ) * Complex.I ∈ U := by
      change |((z.re : ℂ) + (z₀.im : ℂ) * Complex.I).im - c₀| < r
      simpa [him_z₀] using hr
    have hw_z : (w.re : ℂ) + (z.im : ℂ) * Complex.I ∈ U := by
      change |((w.re : ℂ) + (z.im : ℂ) * Complex.I).im - c₀| < r
      simpa [U] using hz
    have hz_z : (z.re : ℂ) + (z.im : ℂ) * Complex.I ∈ U := by
      change |((z.re : ℂ) + (z.im : ℂ) * Complex.I).im - c₀| < r
      simpa [U] using hz
    have hw_z₀ : (w.re : ℂ) + (z₀.im : ℂ) * Complex.I ∈ U := by
      change |((w.re : ℂ) + (z₀.im : ℂ) * Complex.I).im - c₀| < r
      simpa [him_z₀] using hr
    have hw_w : (w.re : ℂ) + (w.im : ℂ) * Complex.I ∈ U := by
      change |((w.re : ℂ) + (w.im : ℂ) * Complex.I).im - c₀| < r
      simpa [U] using hwU
    have h_rect : Rectangle (z.re + z₀.im * Complex.I) (w.re + z.im * Complex.I) ⊆ U := by
      refine hU_conv.rectangle_subset ?_ ?_ ?_ ?_
      · simpa [Complex.add_re, Complex.add_im] using hz_z₀
      · simpa [Complex.add_re, Complex.add_im] using hw_z
      · simpa [Complex.add_re, Complex.add_im] using hz_z
      · simpa [Complex.add_re, Complex.add_im] using hw_z₀
    have h0 := hcons_U (z.re + z₀.im * Complex.I) (w.re + z.im * Complex.I) h_rect
    rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq] at h0
    set I₁ := ∫ x in z₀.re..w.re, f (x + z₀.im * Complex.I)
    set I₂ := Complex.I • ∫ y in z₀.im..w.im, f (w.re + y * Complex.I)
    set I₃ := ∫ x in z₀.re..z.re, f (x + z₀.im * Complex.I)
    set I₄ := Complex.I • ∫ y in z₀.im..z.im, f (z.re + y * Complex.I)
    set I₅ := ∫ x in z.re..w.re, f (x + z.im * Complex.I)
    set I₆ := Complex.I • ∫ y in z.im..w.im, f (w.re + y * Complex.I)
    set I₇ := ∫ x in z.re..w.re, f (x + z₀.im * Complex.I)
    set I₈ := Complex.I • ∫ y in z₀.im..z.im, f (w.re + y * Complex.I)
    have hI₁ : I₁ = I₃ + I₇ := by
      rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply h_hor
      · simpa [Complex.re_add_im] using hz₀U
      · exact hz_z₀
      · exact hz_z₀
      · exact hw_z₀
    have hI₂ : I₂ = I₈ + I₆ := by
      rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply h_ver
      · exact hw_z₀
      · exact hw_z
      · exact hw_z
      · exact hw_w
    have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
      simpa [I₄, I₅, I₇, I₈] using h0
    change I₁ + I₂ = I₃ + I₄ + (I₅ + I₆)
    linear_combination hI₁ + hI₂ + hI₀
  exact (hd_wedge.const_add _).congr_of_eventuallyEq hev

lemma isExactOn_strip {f : ℂ → ℂ} {c₀ r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im - c₀| < r}) :
    Complex.IsExactOn f {z : ℂ | |z.im - c₀| < r} :=
  ⟨_, hasDerivAt_wedgeIntegral_strip hr hf⟩

/-- Same primitive theorem for any open rectangle `{z | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}`. -/
lemma isExactOn_rect {f : ℂ → ℂ} {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hf : DifferentiableOn ℂ f {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}) :
    Complex.IsExactOn f {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d} := by
  let U : Set ℂ := {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}
  let z₀ : ℂ := ((a + b) / 2 : ℝ) + Complex.I * (((c + d) / 2 : ℝ) : ℂ)
  have hz₀U : z₀ ∈ U := by
    refine ⟨by dsimp [z₀]; simp; linarith, by dsimp [z₀]; simp; linarith,
      by dsimp [z₀]; simp; linarith, by dsimp [z₀]; simp; linarith⟩
  refine ⟨fun z => Complex.wedgeIntegral z₀ z f, fun z hz => ?_⟩
  have hU_conv : Convex ℝ U := by
    intro x hx y hy s t hs ht hst
    have hre : (s • x + t • y : ℂ).re = s * x.re + t * y.re := by simp [Complex.real_smul]
    have him : (s • x + t • y : ℂ).im = s * x.im + t * y.im := by simp [Complex.real_smul]
    rcases eq_or_lt_of_le hs with rfl | hs'
    · simp only [zero_add] at hst; subst hst; simpa [Complex.real_smul] using hy
    · have hxa : a < x.re := hx.1
      have hxb : x.re < b := hx.2.1
      have hxc : c < x.im := hx.2.2.1
      have hxd : x.im < d := hx.2.2.2
      have hya : a < y.re := hy.1
      have hyb : y.re < b := hy.2.1
      have hyc : c < y.im := hy.2.2.1
      have hyd : y.im < d := hy.2.2.2
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hre]
        calc a = s * a + t * a := by rw [← add_mul, hst, one_mul]
          _ < s * x.re + t * y.re := by
              have h1 : s * a < s * x.re := mul_lt_mul_of_pos_left hxa hs'
              have h2 : t * a ≤ t * y.re := mul_le_mul_of_nonneg_left hya.le ht
              linarith
      · rw [hre]
        calc s * x.re + t * y.re < s * b + t * b := by
              have h1 : s * x.re < s * b := mul_lt_mul_of_pos_left hxb hs'
              have h2 : t * y.re ≤ t * b := mul_le_mul_of_nonneg_left hyb.le ht
              linarith
          _ = b := by rw [← add_mul, hst, one_mul]
      · rw [him]
        calc c = s * c + t * c := by rw [← add_mul, hst, one_mul]
          _ < s * x.im + t * y.im := by
              have h1 : s * c < s * x.im := mul_lt_mul_of_pos_left hxc hs'
              have h2 : t * c ≤ t * y.im := mul_le_mul_of_nonneg_left hyc.le ht
              linarith
      · rw [him]
        calc s * x.im + t * y.im < s * d + t * d := by
              have h1 : s * x.im < s * d := mul_lt_mul_of_pos_left hxd hs'
              have h2 : t * y.im ≤ t * d := mul_le_mul_of_nonneg_left hyd.le ht
              linarith
          _ = d := by rw [← add_mul, hst, one_mul]
  let ρ : ℝ := min (min (z.re - a) (b - z.re)) (min (z.im - c) (d - z.im))
  have hρ : 0 < ρ := lt_min (lt_min (sub_pos.mpr hz.1) (sub_pos.mpr hz.2.1))
    (lt_min (sub_pos.mpr hz.2.2.1) (sub_pos.mpr hz.2.2.2))
  have hball_sub : ball z ρ ⊆ U := fun w hw => by
    have hre : |w.re - z.re| < ρ := (Complex.abs_re_le_norm (w - z)).trans_lt (mem_ball_iff_norm.mp hw)
    have him : |w.im - z.im| < ρ := (Complex.abs_im_le_norm (w - z)).trans_lt (mem_ball_iff_norm.mp hw)
    rw [abs_lt] at hre him
    have h1 : ρ ≤ z.re - a := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : ρ ≤ b - z.re := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : ρ ≤ z.im - c := (min_le_right _ _).trans (min_le_left _ _)
    have h4 : ρ ≤ d - z.im := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hcons_U : Complex.IsConservativeOn f U := hf.isConservativeOn
  have hd_wedge : HasDerivAt (fun w => Complex.wedgeIntegral z w f) (f z) z :=
    (hcons_U.mono hball_sub).hasDerivAt_wedgeIntegral (hf.continuousOn.mono hball_sub) (mem_ball_self hρ)
  have hev : (fun w => Complex.wedgeIntegral z₀ w f) =ᶠ[𝓝 z]
      (fun w => Complex.wedgeIntegral z₀ z f + Complex.wedgeIntegral z w f) := by
    refine eventually_nhds_iff_ball.mpr ⟨ρ, hρ, fun w hw => ?_⟩
    have hwU : w ∈ U := hball_sub hw
    have h_hor (a₁ a₂ y : ℝ) (h1 : a₁ + y * Complex.I ∈ U) (h2 : a₂ + y * Complex.I ∈ U) :
        IntervalIntegrable (fun x : ℝ => f (x + y * Complex.I)) volume a₁ a₂ := by
      refine (hf.continuousOn.comp (by fun_prop) fun x hx => ?_).intervalIntegrable
      have ha₁ : a < a₁ := by simpa using h1.1
      have ha₁' : a₁ < b := by simpa using h1.2.1
      have ha₂ : a < a₂ := by simpa using h2.1
      have ha₂' : a₂ < b := by simpa using h2.2.1
      have hyc : c < y := by simpa using h1.2.2.1
      have hyd : y < d := by simpa using h1.2.2.2
      refine ⟨?_, ?_, by simpa using hyc, by simpa using hyd⟩
      · rcases mem_uIcc.mp hx with ⟨hx1, _⟩ | ⟨hx1, _⟩ <;> simp <;> linarith
      · rcases mem_uIcc.mp hx with ⟨_, hx2⟩ | ⟨_, hx2⟩ <;> simp <;> linarith
    have h_ver (x b₁ b₂ : ℝ) (h1 : x + b₁ * Complex.I ∈ U) (h2 : x + b₂ * Complex.I ∈ U) :
        IntervalIntegrable (fun y : ℝ => f (x + y * Complex.I)) volume b₁ b₂ := by
      refine (hf.continuousOn.comp (by fun_prop) fun y hy => ?_).intervalIntegrable
      have hxa : a < x := by simpa using h1.1
      have hxb : x < b := by simpa using h1.2.1
      have hb₁ : c < b₁ := by simpa using h1.2.2.1
      have hb₁' : b₁ < d := by simpa using h1.2.2.2
      have hb₂ : c < b₂ := by simpa using h2.2.2.1
      have hb₂' : b₂ < d := by simpa using h2.2.2.2
      refine ⟨by simpa using hxa, by simpa using hxb, ?_, ?_⟩
      · rcases mem_uIcc.mp hy with ⟨hy1, _⟩ | ⟨hy1, _⟩ <;> simp <;> linarith
      · rcases mem_uIcc.mp hy with ⟨_, hy2⟩ | ⟨_, hy2⟩ <;> simp <;> linarith
    have hz_z₀ : (z.re : ℂ) + (z₀.im : ℂ) * Complex.I ∈ U :=
      ⟨by simpa using hz.1, by simpa using hz.2.1, by simpa using hz₀U.2.2.1,
        by simpa using hz₀U.2.2.2⟩
    have hw_z₀ : (w.re : ℂ) + (z₀.im : ℂ) * Complex.I ∈ U :=
      ⟨by simpa using hwU.1, by simpa using hwU.2.1, by simpa using hz₀U.2.2.1,
        by simpa using hz₀U.2.2.2⟩
    have hz_z : (z.re : ℂ) + (z.im : ℂ) * Complex.I ∈ U := by
      simpa [U, Complex.re_add_im] using hz
    have hw_z : (w.re : ℂ) + (z.im : ℂ) * Complex.I ∈ U :=
      ⟨by simpa using hwU.1, by simpa using hwU.2.1, by simpa using hz.2.2.1, by simpa using hz.2.2.2⟩
    have hw_w : (w.re : ℂ) + (w.im : ℂ) * Complex.I ∈ U := by
      simpa [U, Complex.re_add_im] using hwU
    have h_rect : Rectangle (z.re + z₀.im * Complex.I) (w.re + z.im * Complex.I) ⊆ U :=
      hU_conv.rectangle_subset
        (by simpa [Complex.add_re, Complex.add_im] using hz_z₀)
        (by simpa [Complex.add_re, Complex.add_im] using hw_z)
        (by simpa [Complex.add_re, Complex.add_im] using hz_z)
        (by simpa [Complex.add_re, Complex.add_im] using hw_z₀)
    have h0 := hcons_U (z.re + z₀.im * Complex.I) (w.re + z.im * Complex.I) h_rect
    rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq] at h0
    set I₁ := ∫ x in z₀.re..w.re, f (x + z₀.im * Complex.I)
    set I₂ := Complex.I • ∫ y in z₀.im..w.im, f (w.re + y * Complex.I)
    set I₃ := ∫ x in z₀.re..z.re, f (x + z₀.im * Complex.I)
    set I₄ := Complex.I • ∫ y in z₀.im..z.im, f (z.re + y * Complex.I)
    set I₅ := ∫ x in z.re..w.re, f (x + z.im * Complex.I)
    set I₆ := Complex.I • ∫ y in z.im..w.im, f (w.re + y * Complex.I)
    set I₇ := ∫ x in z.re..w.re, f (x + z₀.im * Complex.I)
    set I₈ := Complex.I • ∫ y in z₀.im..z.im, f (w.re + y * Complex.I)
    have hI₁ : I₁ = I₃ + I₇ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (h_hor z₀.re z.re z₀.im (by simpa using hz₀U) hz_z₀)
        (h_hor z.re w.re z₀.im hz_z₀ hw_z₀)).symm
    have hI₂ : I₂ = I₈ + I₆ := by
      rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals]
      · exact h_ver w.re z₀.im z.im hw_z₀ hw_z
      · exact h_ver w.re z.im w.im hw_z hw_w
    have hI₀ : I₇ - I₅ + I₈ - I₄ = 0 := by simpa [I₄, I₅, I₇, I₈] using h0
    change I₁ + I₂ = I₃ + I₄ + (I₅ + I₆)
    linear_combination hI₁ + hI₂ + hI₀
  exact (hd_wedge.const_add _).congr_of_eventuallyEq hev

private noncomputable def edgeFC (z : ℂ) : ℂ :=
  Complex.log (Complex.cosh ((Real.pi : ℂ) * z) +
    (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)) / (Real.pi : ℂ)

private noncomputable def edgeFC' (z : ℂ) : ℂ :=
  Complex.sinh ((Real.pi : ℂ) * z) /
    (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)

private lemma cpow_half_re_pos {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    0 < (w ^ (1 / 2 : ℂ)).re := by
  have hw_ne : w ≠ 0 := Complex.slitPlane_ne_zero hw
  have harg_le : w.arg ≤ Real.pi := Complex.arg_le_pi w
  have harg_gt : -Real.pi < w.arg := Complex.neg_pi_lt_arg w
  have harg_ne : w.arg ≠ Real.pi := by
    intro hpi
    have h1 := Complex.arg_eq_pi_iff.mp hpi
    rw [Complex.mem_slitPlane_iff] at hw
    rcases hw with hre | him
    · linarith
    · exact him h1.2
  have harg_lt : w.arg < Real.pi := lt_of_le_of_ne harg_le harg_ne
  have hpow : w ^ (1 / 2 : ℂ) = (‖w‖ ^ (1 / 2 : ℝ) : ℝ) * Complex.exp (Complex.I * ((w.arg / 2 : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hw_ne, Complex.log, add_mul, Complex.exp_add]
    have h1 : Complex.exp (↑(Real.log ‖w‖) * (1 / 2 : ℂ)) = ((‖w‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hw_ne), Complex.ofReal_exp]
      congr 1; push_cast; ring
    have h2 : Complex.exp ((↑w.arg * Complex.I) * (1 / 2 : ℂ)) =
        Complex.exp (Complex.I * ((w.arg / 2 : ℝ) : ℂ)) := by
      congr 1; push_cast; ring
    rw [h1, h2]
  rw [hpow, Complex.re_ofReal_mul, show Complex.I * ((w.arg / 2 : ℝ) : ℂ) =
    ((w.arg / 2 : ℝ) : ℂ) * Complex.I by ring, Complex.exp_ofReal_mul_I_re]
  have hcos : 0 < Real.cos (w.arg / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by linarith, by linarith⟩
  have hnr : 0 < ‖w‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hw_ne) _
  exact mul_pos hnr hcos

private lemma cosh_strip_re_pos {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < (Complex.cosh ((Real.pi : ℂ) * z)).re := by
  have hre : (Complex.cosh ((Real.pi : ℂ) * z)).re =
      Real.cosh (Real.pi * z.re) * Real.cos (Real.pi * z.im) := by
    have hmul : (Real.pi : ℂ) * z = ((Real.pi * z.re : ℝ) : ℂ) + ((Real.pi * z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hmul, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  rw [hre]
  have hcos : 0 < Real.cos (Real.pi * z.im) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [abs_lt] at hz
    have := Real.pi_pos
    exact ⟨by nlinarith, by nlinarith⟩
  exact mul_pos (Real.cosh_pos _) hcos

private lemma one_add_cosh_sq_mem_slitPlane {z : ℂ} (hz : |z.im| < 1 / 2) :
    1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2).im = 0
  · left
    have hmul : (Real.pi : ℂ) * z = ((Real.pi * z.re : ℝ) : ℂ) + ((Real.pi * z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    have him_eq : (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2).im =
        2 * (Complex.cosh ((Real.pi : ℂ) * z)).re * (Complex.cosh ((Real.pi : ℂ) * z)).im := by
      rw [Complex.add_im, Complex.one_im, zero_add, sq, Complex.mul_im]; ring
    rw [him_eq] at him
    have hre_pos : 0 < (Complex.cosh ((Real.pi : ℂ) * z)).re := cosh_strip_re_pos hz
    have him_zero : (Complex.cosh ((Real.pi : ℂ) * z)).im = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · linarith
      · exact h
    have hsq_re : (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2).re =
        1 + (Complex.cosh ((Real.pi : ℂ) * z)).re ^ 2 - (Complex.cosh ((Real.pi : ℂ) * z)).im ^ 2 := by
      rw [Complex.add_re, Complex.one_re, sq, Complex.mul_re]; ring
    rw [hsq_re, him_zero]
    nlinarith [sq_nonneg (Complex.cosh ((Real.pi : ℂ) * z)).re]
  · right; exact him

private lemma edgeFC_analyticOnNhd :
    AnalyticOnNhd ℂ edgeFC {z : ℂ | |z.im| < 1 / 2} := by
  intro z hz
  have h1 : 1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2 ∈ Complex.slitPlane :=
    one_add_cosh_sq_mem_slitPlane hz
  have h2_re : 0 < (Complex.cosh ((Real.pi : ℂ) * z) +
      (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)).re := by
    rw [Complex.add_re]
    exact add_pos (cosh_strip_re_pos hz) (cpow_half_re_pos h1)
  have h2 : Complex.cosh ((Real.pi : ℂ) * z) +
      (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl h2_re)
  have h_cosh : AnalyticAt ℂ (fun w : ℂ => Complex.cosh ((Real.pi : ℂ) * w)) z :=
    Complex.analyticAt_cosh.comp (analyticAt_const.mul analyticAt_id)
  have h_pow : AnalyticAt ℂ (fun w : ℂ => (1 + Complex.cosh ((Real.pi : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) z :=
    (analyticAt_const.add (h_cosh.pow 2)).cpow analyticAt_const h1
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  exact ((h_cosh.add h_pow).clog h2).div analyticAt_const hpi_ne

private lemma edgeFC_hasDerivAt {z : ℂ} (hz : |z.im| < 1 / 2) :
    HasDerivAt edgeFC (edgeFC' z) z := by
  have h1 : 1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2 ∈ Complex.slitPlane :=
    one_add_cosh_sq_mem_slitPlane hz
  have h1_ne : 1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2 ≠ 0 := Complex.slitPlane_ne_zero h1
  have h2_re : 0 < (Complex.cosh ((Real.pi : ℂ) * z) +
      (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)).re := by
    rw [Complex.add_re]
    exact add_pos (cosh_strip_re_pos hz) (cpow_half_re_pos h1)
  have h2 : Complex.cosh ((Real.pi : ℂ) * z) +
      (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl h2_re)
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have h_lin : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w) (Real.pi : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
  have h_cosh : HasDerivAt (fun w : ℂ => Complex.cosh ((Real.pi : ℂ) * w))
      (Complex.sinh ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z :=
    (Complex.hasDerivAt_cosh _).comp z h_lin
  have h_in : HasDerivAt (fun w : ℂ => 1 + Complex.cosh ((Real.pi : ℂ) * w) ^ 2)
      (2 * Complex.cosh ((Real.pi : ℂ) * z) * Complex.sinh ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z := by
    exact ((h_cosh.pow 2).const_add 1).congr_deriv (by ring)
  have h_sq_d : HasDerivAt (fun w : ℂ => (1 + Complex.cosh ((Real.pi : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ ((1 / 2 : ℂ) - 1) *
        (2 * Complex.cosh ((Real.pi : ℂ) * z) * Complex.sinh ((Real.pi : ℂ) * z) * (Real.pi : ℂ))) z :=
    h_in.cpow_const h1
  have h_sum := h_cosh.add h_sq_d
  have h_log := (h_sum.clog h2).div_const (Real.pi : ℂ)
  refine h_log.congr_deriv ?_
  set c := Complex.cosh ((Real.pi : ℂ) * z)
  set s := Complex.sinh ((Real.pi : ℂ) * z)
  set q := (1 + c ^ 2) ^ (1 / 2 : ℂ)
  have hq_ne : q ≠ 0 := by
    change (1 + c ^ 2) ^ (1 / 2 : ℂ) ≠ 0
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl h1_ne
  have hq_sq : q ^ 2 = 1 + c ^ 2 := by
    dsimp [q]; rw [← Complex.cpow_nat_mul]; norm_num
  have hq_inv : (1 + c ^ 2) ^ ((1 / 2 : ℂ) - 1) = q / (1 + c ^ 2) := by
    have hpow : (1 + c ^ 2) ^ ((1 / 2 : ℂ) - 1) = (1 + c ^ 2) ^ (1 / 2 : ℂ) * (1 + c ^ 2) ^ (-1 : ℂ) := by
      rw [sub_eq_add_neg]
      exact Complex.cpow_add _ _ h1_ne
    rw [hpow, Complex.cpow_neg_one]
    rfl
  change ((s * (Real.pi : ℂ) + (1 / 2 : ℂ) * (1 + c ^ 2) ^ ((1 / 2 : ℂ) - 1) *
    (2 * c * s * (Real.pi : ℂ))) / (c + q)) / (Real.pi : ℂ) = s / q
  rw [hq_inv]
  have hcq_ne : c + q ≠ 0 := Complex.slitPlane_ne_zero h2
  field_simp [hpi_ne, h1_ne, hq_ne, hcq_ne]
  rw [← hq_sq]
  ring

private lemma edgeFC_ofReal (v : ℝ) : edgeFC (v : ℂ) = (edgeF v : ℂ) := by
  unfold edgeFC edgeF
  have hcosh : Complex.cosh ((Real.pi : ℂ) * (v : ℂ)) = ((Real.cosh (Real.pi * v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_cosh]
  have h1pos : 0 < 1 + Real.cosh (Real.pi * v) ^ 2 := by positivity
  have hcpow : (1 + ((Real.cosh (Real.pi * v) : ℝ) : ℂ) ^ 2) ^ (1 / 2 : ℂ) =
      ((√(1 + Real.cosh (Real.pi * v) ^ 2) : ℝ) : ℂ) := by
    have h1c : 1 + ((Real.cosh (Real.pi * v) : ℝ) : ℂ) ^ 2 = ((1 + Real.cosh (Real.pi * v) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [h1c, hhalf, ← Complex.ofReal_cpow h1pos.le, ← Real.sqrt_eq_rpow]
  have harg_pos : 0 < Real.cosh (Real.pi * v) + √(1 + Real.cosh (Real.pi * v) ^ 2) := by positivity
  rw [hcosh, hcpow, ← Complex.ofReal_add, ← Complex.ofReal_log harg_pos.le]
  have h_arsinh : Real.arsinh (Real.cosh (Real.pi * v)) =
      Real.log (Real.cosh (Real.pi * v) + √(1 + Real.cosh (Real.pi * v) ^ 2)) := by
    apply Real.sinh_injective
    rw [Real.sinh_arsinh, Real.sinh_eq, Real.exp_log harg_pos]
    have hinv : (Real.cosh (Real.pi * v) + √(1 + Real.cosh (Real.pi * v) ^ 2))⁻¹ =
        √(1 + Real.cosh (Real.pi * v) ^ 2) - Real.cosh (Real.pi * v) := by
      have hsq : √(1 + Real.cosh (Real.pi * v) ^ 2) ^ 2 = 1 + Real.cosh (Real.pi * v) ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hdiff : (Real.cosh (Real.pi * v) + √(1 + Real.cosh (Real.pi * v) ^ 2)) *
          (√(1 + Real.cosh (Real.pi * v) ^ 2) - Real.cosh (Real.pi * v)) = 1 := by
        linarith
      exact inv_eq_of_mul_eq_one_right hdiff
    rw [Real.exp_neg, Real.exp_log harg_pos, hinv]
    ring
  rw [h_arsinh]
  push_cast
  rfl

private lemma edgeFC'_bounded_on_strip :
    ∃ M₁ ≥ 0, ∀ z : ℂ, |z.im| ≤ 3 / 8 → ‖edgeFC' z‖ ≤ M₁ := by
  let V₀ : ℝ := Real.arcosh 3 / Real.pi + 1
  have hV₀_pos : 0 < V₀ := by
    have h1 := Real.arcosh_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have hpi := Real.pi_pos
    positivity
  let K : Set ℂ := {z : ℂ | |z.re| ≤ V₀ ∧ |z.im| ≤ 3 / 8}
  have hK_compact : IsCompact K := by
    have hsub : K ⊆ Metric.closedBall (0 : ℂ) (V₀ + 1) := fun z hz => by
      rw [mem_closedBall_zero_iff]
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      linarith [hz.1, hz.2]
    have hcl : IsClosed K := by
      refine IsClosed.inter ?_ ?_
      · exact isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
      · exact isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    exact (isCompact_closedBall (0 : ℂ) (V₀ + 1)).of_isClosed_subset hcl hsub
  have hcont : ContinuousOn (fun z : ℂ => ‖edgeFC' z‖) K := by
    refine ContinuousOn.norm ?_
    intro z hz
    have hz_open : |z.im| < 1 / 2 := hz.2.trans_lt (by norm_num)
    have h_lin : ContinuousAt (fun w : ℂ => (Real.pi : ℂ) * w) z := by fun_prop
    have h_num : ContinuousAt (fun w : ℂ => Complex.sinh ((Real.pi : ℂ) * w)) z :=
      Complex.continuous_sinh.continuousAt.comp h_lin
    have h1 : 1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2 ∈ Complex.slitPlane :=
      one_add_cosh_sq_mem_slitPlane hz_open
    have h_den : ContinuousAt (fun w : ℂ => (1 + Complex.cosh ((Real.pi : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) z :=
      ((analyticAt_const.add ((Complex.analyticAt_cosh.comp (analyticAt_const.mul analyticAt_id)).pow 2)).cpow
        analyticAt_const h1).continuousAt
    have h_den_ne : (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]; exact Or.inl (Complex.slitPlane_ne_zero h1)
    exact (h_num.div h_den h_den_ne).continuousWithinAt
  have hne : K.Nonempty := ⟨0, by simp [K, hV₀_pos.le]; norm_num⟩
  obtain ⟨zmax, _, hzmax⟩ := hK_compact.exists_isMaxOn hne hcont
  let M₁ : ℝ := max 2 (‖edgeFC' zmax‖)
  refine ⟨M₁, by positivity, fun z hz => ?_⟩
  by_cases hre : |z.re| ≤ V₀
  · exact (hzmax ⟨hre, hz⟩).trans (le_max_right _ _)
  · push Not at hre
    have hsinh_gt : 2 ≤ Real.sinh (Real.pi * |z.re|) := by
      have hpi := Real.pi_pos
      have h1 : Real.arcosh 3 / Real.pi < |z.re| := by linarith
      have h2 : Real.arcosh 3 < Real.pi * |z.re| := by
        calc Real.arcosh 3
            = Real.pi * (Real.arcosh 3 / Real.pi) := by field_simp [hpi.ne']
          _ < Real.pi * |z.re| := mul_lt_mul_of_pos_left h1 hpi
      have hcosh : 3 < Real.cosh (Real.pi * |z.re|) := by
        have hlt := Real.cosh_strictMonoOn (Real.arcosh_nonneg (by norm_num))
          (mul_nonneg hpi.le (abs_nonneg z.re)) h2
        rwa [Real.cosh_arcosh (by norm_num)] at hlt
      have hsq : Real.cosh (Real.pi * |z.re|) ^ 2 - 1 = Real.sinh (Real.pi * |z.re|) ^ 2 := by
        linarith [Real.cosh_sq_sub_sinh_sq (Real.pi * |z.re|)]
      have h_ge : 2 ^ 2 ≤ Real.sinh (Real.pi * |z.re|) ^ 2 := by nlinarith
      nlinarith [Real.sinh_nonneg_iff.mpr (mul_nonneg hpi.le (abs_nonneg z.re))]
    have h_sinh_ub : ‖Complex.sinh ((Real.pi : ℂ) * z)‖ ≤ Real.cosh (Real.pi * |z.re|) := by
      have hmul : (Real.pi : ℂ) * z = ((Real.pi * z.re : ℝ) : ℂ) + ((Real.pi * z.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      have hnorm_sq : ‖((Real.sinh (Real.pi * z.re) : ℝ) : ℂ) * ((Real.cos (Real.pi * z.im) : ℝ) : ℂ) +
          ((Real.cosh (Real.pi * z.re) : ℝ) : ℂ) * (((Real.sin (Real.pi * z.im) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
          Real.sinh (Real.pi * z.re) ^ 2 + Real.sin (Real.pi * z.im) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        have h1 := Real.cosh_sq_sub_sinh_sq (Real.pi * z.re)
        have h2 := Real.sin_sq_add_cos_sq (Real.pi * z.im)
        nlinarith
      have hsq_le : ‖Complex.sinh ((Real.pi : ℂ) * z)‖ ^ 2 ≤ Real.cosh (Real.pi * |z.re|) ^ 2 := by
        rw [hmul, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          hnorm_sq]
        have hcosh_abs : Real.cosh (Real.pi * |z.re|) ^ 2 = Real.cosh (Real.pi * z.re) ^ 2 := by
          rcases le_total 0 z.re with hz0 | hz0
          · rw [abs_of_nonneg hz0]
          · rw [abs_of_nonpos hz0, mul_neg, Real.cosh_neg]
        rw [hcosh_abs]
        have h1 : Real.cosh (Real.pi * z.re) ^ 2 = Real.sinh (Real.pi * z.re) ^ 2 + 1 := by
          linarith [Real.cosh_sq_sub_sinh_sq (Real.pi * z.re)]
        nlinarith [Real.sin_sq_le_one (Real.pi * z.im)]
      exact le_of_sq_le_sq hsq_le (Real.cosh_pos _).le
    have h_cosh_sq : Real.sinh (Real.pi * |z.re|) ^ 2 ≤ ‖Complex.cosh ((Real.pi : ℂ) * z)‖ ^ 2 := by
      have hmul : (Real.pi : ℂ) * z = ((Real.pi * z.re : ℝ) : ℂ) + ((Real.pi * z.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hmul, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
        ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have hsinh_abs : Real.sinh (Real.pi * |z.re|) ^ 2 = Real.sinh (Real.pi * z.re) ^ 2 := by
        rcases le_total 0 z.re with hz0 | hz0
        · rw [abs_of_nonneg hz0]
        · rw [abs_of_nonpos hz0, mul_neg, Real.sinh_neg, neg_sq]
      rw [hsinh_abs]
      have h1 : Real.cosh (Real.pi * z.re) ^ 2 = Real.sinh (Real.pi * z.re) ^ 2 + 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq (Real.pi * z.re)]
      have h2 := Real.sin_sq_add_cos_sq (Real.pi * z.im)
      nlinarith [Real.sin_sq_le_one (Real.pi * z.im)]
    have h_den_sq : (1 / 4 : ℝ) * Real.cosh (Real.pi * |z.re|) ^ 2 ≤
        ‖1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2‖ := by
      have htri : ‖Complex.cosh ((Real.pi : ℂ) * z) ^ 2‖ - 1 ≤
          ‖1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2‖ := by
        have := norm_sub_le (1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) (1 : ℂ)
        simp only [add_sub_cancel_left, norm_one] at this
        linarith
      rw [norm_pow] at htri
      have h_ch : Real.cosh (Real.pi * |z.re|) ^ 2 = Real.sinh (Real.pi * |z.re|) ^ 2 + 1 := by
        linarith [Real.cosh_sq_sub_sinh_sq (Real.pi * |z.re|)]
      nlinarith
    have h_cpow_norm : ‖(1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)‖ =
        √‖1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2‖ := by
      have h1 : 1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2 ≠ 0 :=
        Complex.slitPlane_ne_zero (one_add_cosh_sq_mem_slitPlane (hz.trans_lt (by norm_num)))
      have hsq : ‖(1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)‖ ^ 2 =
          ‖1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2‖ := by
        rw [← norm_pow, ← Complex.cpow_nat_mul]
        norm_num
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    have h_den_lb : (1 / 2 : ℝ) * Real.cosh (Real.pi * |z.re|) ≤
        ‖(1 + Complex.cosh ((Real.pi : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)‖ := by
      rw [h_cpow_norm]
      have hrt := Real.sqrt_le_sqrt h_den_sq
      have heq : √((1 / 4 : ℝ) * Real.cosh (Real.pi * |z.re|) ^ 2) =
          (1 / 2 : ℝ) * Real.cosh (Real.pi * |z.re|) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (Real.cosh_pos _).le]
        norm_num
      linarith
    have h_div : ‖edgeFC' z‖ ≤ 2 := by
      dsimp [edgeFC']
      rw [norm_div]
      rw [div_le_iff₀ (by linarith [Real.cosh_pos (Real.pi * |z.re|)])]
      linarith
    exact h_div.trans (le_max_left _ _)

/-- Explicit non-vacuity witness for `EdgePhaseData δ C₃ C₄ Φ₀` on `0 < δ ≤ 1/4`. -/
private noncomputable def edgePhi0Model (b : ℂ) : ℂ :=
  Complex.wedgeIntegral (Complex.I * ((1 / 2 : ℝ) : ℂ)) b
    (fun z => -(4 * (Real.pi : ℂ) * Complex.I / 3) * edgeFC (z - Complex.I / 2))

lemma edgePhaseData_nonvacuous {δ : ℝ} (_hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C₃ C₄ Φ₀, EdgePhaseData δ C₃ C₄ Φ₀ := by
  let S_open : Set ℂ := {z : ℂ | |z.im - 1 / 2| < 1 / 2}
  let H : ℂ → ℂ := fun z => -(4 * (Real.pi : ℂ) * Complex.I / 3) * edgeFC (z - Complex.I / 2)
  have hH_an : AnalyticOnNhd ℂ H S_open := by
    intro z hz
    have hz_shift : |(z - Complex.I / 2).im| < 1 / 2 := by simpa [S_open] using hz
    have hsub_an : AnalyticAt ℂ (fun w : ℂ => w - Complex.I / 2) z :=
      analyticAt_id.sub analyticAt_const
    exact analyticAt_const.mul ((edgeFC_analyticOnNhd _ hz_shift).comp_of_eq hsub_an rfl)
  have hH_diff : DifferentiableOn ℂ H S_open := hH_an.differentiableOn
  have hderiv : ∀ b ∈ S_open, HasDerivAt edgePhi0Model (H b) b :=
    hasDerivAt_wedgeIntegral_strip (c₀ := 1 / 2) (r := 1 / 2) (by norm_num) hH_diff
  have hS_sub : edgeStrip δ ⊆ S_open := fun b hb => by
    change |b.im - 1 / 2| < 1 / 2
    exact hb.trans_lt (hδ1.trans_lt (by norm_num))
  have hPhi_diff : DifferentiableOn ℂ edgePhi0Model S_open :=
    fun b hb => (hderiv b hb).differentiableAt.differentiableWithinAt
  have hS_open : IsOpen S_open :=
    isOpen_lt (continuous_abs.comp (Complex.continuous_im.sub continuous_const)) continuous_const
  have hPhi_an : AnalyticOnNhd ℂ edgePhi0Model (edgeStrip δ) :=
    (hPhi_diff.analyticOnNhd hS_open).mono hS_sub
  obtain ⟨M₁, hM₁_nn, hM₁⟩ := edgeFC'_bounded_on_strip
  let K : ℝ := (4 * Real.pi / 3) * M₁
  have hK_nn : 0 ≤ K := by positivity [Real.pi_pos]
  let R : ℝ := 1 / 8
  have hR_pos : 0 < R := by norm_num
  let C₃ : ℝ := 1 * K / R ^ 1
  let C₄ : ℝ := 2 * K / R ^ 2
  refine ⟨C₃, C₄, edgePhi0Model, ?_⟩
  have h_deriv_eq : EqOn (deriv edgePhi0Model) H S_open := fun b hb => (hderiv b hb).deriv
  have h_iter2_eq : ∀ b ∈ S_open, iteratedDeriv 2 edgePhi0Model b = deriv H b := fun b hb => by
    have hev : (deriv edgePhi0Model) =ᶠ[𝓝 b] H :=
      Filter.eventually_of_mem (hS_open.mem_nhds hb) h_deriv_eq
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact Filter.EventuallyEq.deriv_eq hev
  have h_derivH_eq : ∀ b ∈ S_open, deriv H b =
      -(4 * (Real.pi : ℂ) * Complex.I / 3) * edgeFC' (b - Complex.I / 2) := fun b hb => by
    have hz_shift : |(b - Complex.I / 2).im| < 1 / 2 := by simpa [S_open] using hb
    have hlin : HasDerivAt (fun w : ℂ => w - Complex.I / 2) 1 b :=
      (hasDerivAt_id b).sub_const _
    have hc := (edgeFC_hasDerivAt hz_shift).comp b hlin
    exact (hc.const_mul (-(4 * (Real.pi : ℂ) * Complex.I / 3))).deriv.trans (by ring)
  have h_iter3_eq : ∀ b ∈ S_open,
      iteratedDeriv 3 edgePhi0Model b = iteratedDeriv 1 (fun z => deriv H z) b := fun b hb => by
    have hev : iteratedDeriv 2 edgePhi0Model =ᶠ[𝓝 b] (fun z => deriv H z) :=
      Filter.eventually_of_mem (hS_open.mem_nhds hb) h_iter2_eq
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact Filter.EventuallyEq.deriv_eq hev
  have h_iter4_eq : ∀ b ∈ S_open,
      iteratedDeriv 4 edgePhi0Model b = iteratedDeriv 2 (fun z => deriv H z) b := fun b hb => by
    have hev : iteratedDeriv 3 edgePhi0Model =ᶠ[𝓝 b] iteratedDeriv 1 (fun z => deriv H z) :=
      Filter.eventually_of_mem (hS_open.mem_nhds hb) h_iter3_eq
    conv_lhs => rw [iteratedDeriv_succ]
    conv_rhs => rw [iteratedDeriv_succ]
    exact Filter.EventuallyEq.deriv_eq hev
  have h_ball_sub : ∀ b ∈ edgeStrip δ, closedBall b R ⊆ S_open := fun b hb w hw => by
    change |w.im - 1 / 2| < 1 / 2
    have him : |w.im - b.im| ≤ R :=
      (Complex.abs_im_le_norm (w - b)).trans (mem_closedBall_iff_norm.mp hw)
    have h1 : |b.im - 1 / 2| ≤ 1 / 4 := hb.trans hδ1
    calc |w.im - 1 / 2| ≤ |w.im - b.im| + |b.im - 1 / 2| := by
          simpa [sub_add_sub_cancel] using abs_add_le (w.im - b.im) (b.im - 1 / 2)
      _ ≤ R + 1 / 4 := add_le_add him h1
      _ < 1 / 2 := by dsimp [R]; norm_num
  have h_derivH_bd : ∀ b ∈ edgeStrip δ, ∀ w ∈ sphere b R, ‖deriv H w‖ ≤ K := fun b hb w hw => by
    have hw_cl : w ∈ closedBall b R := sphere_subset_closedBall hw
    have hw_S : w ∈ S_open := h_ball_sub b hb hw_cl
    rw [h_derivH_eq w hw_S, norm_mul]
    have h_const_norm : ‖-(4 * (Real.pi : ℂ) * Complex.I / 3)‖ = 4 * Real.pi / 3 := by
      have h1 : -(4 * (Real.pi : ℂ) * Complex.I / 3) =
          Complex.I * (((-(4 * Real.pi / 3) : ℝ)) : ℂ) := by push_cast; ring
      rw [h1, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_pos (by positivity [Real.pi_pos])]
    have hw_strip : |(w - Complex.I / 2).im| ≤ 3 / 8 := by
      have him : |w.im - b.im| ≤ R :=
        (Complex.abs_im_le_norm (w - b)).trans (mem_closedBall_iff_norm.mp hw_cl)
      have h1 : |b.im - 1 / 2| ≤ 1 / 4 := hb.trans hδ1
      have him_eq : (w - Complex.I / 2).im = w.im - 1 / 2 := by simp
      rw [him_eq]
      calc |w.im - 1 / 2| ≤ |w.im - b.im| + |b.im - 1 / 2| := by
            simpa [sub_add_sub_cancel] using abs_add_le (w.im - b.im) (b.im - 1 / 2)
        _ ≤ R + 1 / 4 := add_le_add him h1
        _ = 3 / 8 := by dsimp [R]; norm_num
    rw [h_const_norm]
    exact mul_le_mul_of_nonneg_left (hM₁ _ hw_strip) (by positivity [Real.pi_pos])
  have h_diff_cl : ∀ b ∈ edgeStrip δ, DiffContOnCl ℂ (fun z => deriv H z) (ball b R) :=
    fun b hb => ((hH_an.deriv.mono ((closure_ball_subset_closedBall).trans (h_ball_sub b hb))).differentiableOn).diffContOnCl
  refine ⟨hPhi_an, ?_, ?_, ?_, ?_⟩
  · intro v
    have h_eq : edgePhi0Model ((v : ℂ) + Complex.I / 2) =
        ∫ x in (0 : ℝ)..v, H ((x : ℂ) + Complex.I / 2) := by
      unfold edgePhi0Model Complex.wedgeIntegral
      have hz₀_re : (Complex.I * ((1 / 2 : ℝ) : ℂ)).re = 0 := by simp
      have hz₀_im : (Complex.I * ((1 / 2 : ℝ) : ℂ)).im = 1 / 2 := by simp
      have hv_re : ((v : ℂ) + Complex.I / 2).re = v := by simp
      have hv_im : ((v : ℂ) + Complex.I / 2).im = 1 / 2 := by simp
      rw [hz₀_re, hz₀_im, hv_re, hv_im, intervalIntegral.integral_same, smul_zero, add_zero]
      refine intervalIntegral.integral_congr fun x _ => ?_
      congr 1; apply Complex.ext <;> simp
    rw [h_eq]
    have h_integrand : ∀ x : ℝ, (H ((x : ℂ) + Complex.I / 2)).re = 0 := fun x => by
      dsimp [H]
      have hsub : ((x : ℂ) + Complex.I / 2) - Complex.I / 2 = (x : ℂ) := by ring
      rw [hsub, edgeFC_ofReal]
      have hmul : -(4 * (Real.pi : ℂ) * Complex.I / 3) * (edgeF x : ℂ) =
          Complex.I * (((-(4 * Real.pi / 3 * edgeF x) : ℝ)) : ℂ) := by push_cast; ring
      rw [hmul, Complex.mul_re]
      simp
    have hc_H : IntervalIntegrable (fun x : ℝ => H ((x : ℂ) + Complex.I / 2)) volume 0 v := by
      refine (hH_diff.continuousOn.comp (by fun_prop) fun x _ => ?_).intervalIntegrable
      change |((x : ℂ) + Complex.I / 2).im - 1 / 2| < 1 / 2
      simp
    have hcomm := Complex.reCLM.intervalIntegral_comp_comm hc_H
    rw [← Complex.reCLM_apply, ← hcomm]
    simp [h_integrand]
  · intro v
    have hv_S : (v : ℂ) + Complex.I / 2 ∈ S_open := by
      change |((v : ℂ) + Complex.I / 2).im - 1 / 2| < 1 / 2
      simp
    rw [(hderiv _ hv_S).deriv]
    dsimp [H]
    have hsub : ((v : ℂ) + Complex.I / 2) - Complex.I / 2 = (v : ℂ) := by ring
    rw [hsub, edgeFC_ofReal]
  · intro b hb
    rw [h_iter3_eq b (hS_sub hb)]
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR_pos
      (h_diff_cl b hb) (h_derivH_bd b hb)
    simpa [C₃] using h
  · intro b hb
    rw [h_iter4_eq b (hS_sub hb)]
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR_pos
      (h_diff_cl b hb) (h_derivH_bd b hb)
    simpa [C₄] using h

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.mX_uniform_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.mX_uniform_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.phiX_re_normal_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.phiX_re_normal_taylor

/-- info: 'FormalResearch.ModularBootstrap.Upper.Saddle.edgePhaseData_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Saddle.edgePhaseData_nonvacuous

end FormalResearch.ModularBootstrap.Upper.Saddle

