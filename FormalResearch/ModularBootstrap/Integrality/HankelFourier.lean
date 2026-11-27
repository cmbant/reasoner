module

public import FormalResearch.ModularBootstrap.Integrality.WeberLaplace
public import FormalResearch.ModularBootstrap.Integrality.RadialConcentration
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Hankel–Fourier Radial Correspondence (`int:sonine`)

Relates the `2w`-dimensional Fourier transform of a compactly supported continuous radial lift
`x ↦ φ(‖x‖² / 2)` (`φ ∈ C_c((0, b])`) to the weighted Hankel transform on `dm_w(t) = t^{w-1} dt`
restricted to `(0, B]`:
* `hankelBandMeasure w B`: `(hankelMeasure w).restrict (Ioc 0 B)`, proved finite (`IsFiniteMeasure`).
* `fourier_radial_exp`: computes `𝓕 (radialLift w (exp (-2π β ·)))` from `fourier_gaussian_innerProductSpace`.
* `fourier_radialLift_eq_hankelTransform`: proves
  `𝓕 (radialLift w φ) ξ = kerTransform (hankelMeasure w) (hankelKernel w) φ (‖ξ‖² / 2)` (`ξ ≠ 0`)
  using `[0, 1]` Weierstrass approximation and `weber_laplace`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set
open scoped FourierTransform ENNReal

namespace FormalResearch.ModularBootstrap.Integrality

open FormalResearch.ModularBootstrap.Crossing

/-! ### Section 1: Band measure `dm_w |_{(0, B]}` -/

/-- The weighted Hankel measure restricted to `(0, B]`. -/
noncomputable def hankelBandMeasure (w : ℕ) (B : ℝ) : Measure ℝ :=
  (hankelMeasure w).restrict (Ioc 0 B)

lemma hankelBandMeasure_eq (w : ℕ) (B : ℝ) :
    hankelBandMeasure w B =
      (volume.restrict (Ioc 0 B)).withDensity (fun t => ENNReal.ofReal (t ^ (w - 1))) := by
  unfold hankelBandMeasure hankelMeasure
  ext s hs
  rw [Measure.restrict_apply hs, withDensity_apply _ (hs.inter measurableSet_Ioc),
    withDensity_apply _ hs]
  change ∫⁻ a, ENNReal.ofReal (a ^ (w - 1)) ∂((volume.restrict (Ioi 0)).restrict (s ∩ Ioc 0 B)) =
    ∫⁻ a, ENNReal.ofReal (a ^ (w - 1)) ∂((volume.restrict (Ioc 0 B)).restrict s)
  rw [Measure.restrict_restrict (hs.inter measurableSet_Ioc), Measure.restrict_restrict hs,
    show (s ∩ Ioc 0 B) ∩ Ioi 0 = s ∩ Ioc 0 B from by
      ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; tauto]

instance isFiniteMeasure_hankelBandMeasure (w : ℕ) (B : ℝ) :
    IsFiniteMeasure (hankelBandMeasure w B) := by
  refine ⟨?_⟩
  rw [hankelBandMeasure_eq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hle : ∫⁻ t in Ioc 0 B, ENNReal.ofReal (t ^ (w - 1)) ≤
      ∫⁻ _t in Ioc 0 B, ENNReal.ofReal ((max B 0) ^ (w - 1)) := by
    refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.1.le (ht.2.trans (le_max_left _ _)) _)
  refine hle.trans_lt ?_
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ioc_lt_top

lemma integral_hankelBandMeasure_eq {w : ℕ} {B : ℝ} (f : ℝ → ℝ) :
    ∫ t, f t ∂(hankelBandMeasure w B) = ∫ t in Ioc (0 : ℝ) B, t ^ (w - 1) * f t := by
  rw [hankelBandMeasure_eq, integral_withDensity_eq_integral_toReal_smul (by fun_prop)]
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [smul_eq_mul, ENNReal.toReal_ofReal (pow_nonneg ht.1.le _)]
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

lemma integrable_hankelBandMeasure_iff {w : ℕ} {B : ℝ} (f : ℝ → ℝ) :
    Integrable f (hankelBandMeasure w B) ↔
      IntegrableOn (fun t => t ^ (w - 1) * f t) (Ioc 0 B) := by
  rw [hankelBandMeasure_eq,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [smul_eq_mul, ENNReal.toReal_ofReal (pow_nonneg ht.1.le _)]

/-! ### Section 2: Fourier transform of radial exponentials and `[0, 1]` Weierstrass -/

lemma fourier_radial_exp (w : ℕ) {β : ℝ} (hβ : 0 < β)
    (ξ : EuclideanSpace ℝ (Fin (2 * w))) :
    𝓕 (radialLift w (fun t => Real.exp (-2 * π * β * t))) ξ =
      ((β ^ (-(w : ℝ)) * Real.exp (-2 * π * (‖ξ‖ ^ 2 / 2) / β) : ℝ) : ℂ) := by
  let b : ℂ := ((π * β : ℝ) : ℂ)
  have hb : 0 < b.re := by simp [b, mul_pos Real.pi_pos hβ]
  have hfun : radialLift w (fun t => Real.exp (-2 * π * β * t)) =
      fun x : EuclideanSpace ℝ (Fin (2 * w)) => Complex.exp (-b * ‖x‖ ^ 2) := by
    ext x
    dsimp [radialLift]
    rw [Complex.ofReal_exp]
    congr 1
    simp only [b]
    push_cast
    ring
  rw [hfun, fourier_gaussian_innerProductSpace hb ξ]
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * w))) : ℂ) / 2 = (w : ℂ) := by
    rw [finrank_euclideanSpace_fin]
    push_cast
    ring
  have hbase : (π : ℂ) / b = ((β⁻¹ : ℝ) : ℂ) := by
    simp only [b]
    push_cast
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi]
  have hpow : (π / b) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * w))) / 2 : ℂ) =
      ((β ^ (-(w : ℝ)) : ℝ) : ℂ) := by
    rw [hdim, hbase, Complex.cpow_natCast, ← Complex.ofReal_pow, inv_pow,
      ← Real.rpow_natCast, ← Real.rpow_neg hβ.le]
  have hexp : Complex.exp (-((π : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2) / b) =
      ((Real.exp (-2 * π * (‖ξ‖ ^ 2 / 2) / β) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    simp only [b]
    push_cast
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi]
  rw [hpow]
  have hexp' : Complex.exp (-↑π ^ 2 * ↑‖ξ‖ ^ 2 / b) =
      ((Real.exp (-2 * π * (‖ξ‖ ^ 2 / 2) / β) : ℝ) : ℂ) := by
    simpa [neg_mul] using hexp
  rw [hexp', ← Complex.ofReal_mul]

lemma integrable_radialLift_exp (w : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (radialLift w (fun t => Real.exp (-2 * π * β * t))) volume := by
  let b : ℂ := ((π * β : ℝ) : ℂ)
  have hb : 0 < b.re := by simp [b, mul_pos Real.pi_pos hβ]
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := EuclideanSpace ℝ (Fin (2 * w))) hb 0 0
  refine h.congr (Eventually.of_forall fun x => ?_)
  dsimp [radialLift]
  rw [Complex.ofReal_exp]
  congr 1
  simp only [b, zero_mul, add_zero]
  push_cast
  ring

private lemma exists_expPoly_approx {b : ℝ} (_hb : 0 < b) {φ : ℝ → ℝ}
    (hφ_cont : Continuous φ) (hφ_supp : ∀ t, t ∉ Ioc 0 b → φ t = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (c : ℕ → ℝ), ∀ s : ℝ, 0 ≤ s →
      |(∑ k ∈ Finset.range N, c k * Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * s)) - φ s| ≤
        ε * Real.exp (-2 * π * s) := by
  let ψ : ℝ → ℝ := fun u => if u ≤ 0 then 0 else φ (-Real.log u / (2 * π)) / u
  have hψ_cont : Continuous ψ := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu0 : 0 < u
    · have hcon : ContinuousOn (fun v : ℝ => φ (-Real.log v / (2 * π)) / v) (Ioi 0) := by
        refine (hφ_cont.continuousOn.comp ?_ (mapsTo_univ _ _)).div continuousOn_id
          fun v hv => (mem_Ioi.mp hv).ne'
        exact ((Real.continuousOn_log.mono fun v hv => (mem_Ioi.mp hv).ne').neg).div_const _
      have heq : ψ =ᶠ[𝓝 u] fun v => φ (-Real.log v / (2 * π)) / v := by
        filter_upwards [Ioi_mem_nhds hu0] with v hv
        simp [ψ, not_le.mpr (mem_Ioi.mp hv)]
      exact (hcon.continuousAt (Ioi_mem_nhds hu0)).congr heq.symm
    · have hub : u < Real.exp (-2 * π * b) := (not_lt.mp hu0).trans_lt (Real.exp_pos _)
      have heq : ψ =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hub] with v hv
        by_cases hv0 : v ≤ 0
        · simp [ψ, hv0]
        · have hv_pos : 0 < v := not_le.mp hv0
          have hlog : Real.log v < -2 * π * b := by
            simpa [Real.log_exp] using Real.log_lt_log hv_pos (mem_Iio.mp hv)
          have hgt : b < -Real.log v / (2 * π) := by
            rw [lt_div_iff₀ (by positivity)]
            linarith
          have hnot : -Real.log v / (2 * π) ∉ Ioc 0 b := fun hmem => not_le.mpr hgt hmem.2
          simp [ψ, hv0, hφ_supp _ hnot]
      exact continuousAt_const.congr heq.symm
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 ψ hψ_cont.continuousOn ε hε
  refine ⟨p.natDegree + 1, fun k => p.coeff k, fun s hs => ?_⟩
  let u : ℝ := Real.exp (-2 * π * s)
  have hu_pos : 0 < u := Real.exp_pos _
  have hu_mem : u ∈ Icc (0 : ℝ) 1 := ⟨hu_pos.le, Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])⟩
  have hp_u := hp u hu_mem
  have hψ_u : u * ψ u = φ s := by
    simp only [ψ, not_le.mpr hu_pos, ↓reduceIte]
    have hs_eq : -Real.log u / (2 * π) = s := by
      simp only [u, Real.log_exp]
      field_simp [Real.pi_ne_zero]
    rw [hs_eq, mul_div_cancel₀ _ hu_pos.ne']
  have hsum_eq : ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * s) = u * p.eval u := by
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hexp_k : Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * s) = u * u ^ k := by
      have hk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hk]
      have hpow : u ^ k = Real.exp (-2 * π * (k : ℝ) * s) := by
        simp only [u, ← Real.exp_nat_mul]
        congr 1; ring
      rw [hpow, ← Real.exp_add]
      congr 1; ring
    rw [hexp_k]
    ring
  rw [hsum_eq, ← hψ_u, ← mul_sub, abs_mul, abs_of_pos hu_pos]
  calc u * |p.eval u - ψ u| ≤ u * ε := mul_le_mul_of_nonneg_left hp_u.le hu_pos.le
    _ = ε * Real.exp (-2 * π * s) := mul_comm _ _

lemma integrableOn_rpow_mul_exp {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ => t ^ r * Real.exp (-2 * π * t)) (Ioi 0) := by
  let N : ℕ := Nat.ceil r
  have hrN : r ≤ (N : ℝ) := Nat.le_ceil r
  have hdom : IntegrableOn (fun t : ℝ =>
      (1 + ((Nat.factorial N : ℝ) / π ^ N)) * Real.exp (-π * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr Real.pi_pos : -π < 0) 0).const_mul _
  refine hdom.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := mem_Ioi.mp ht
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)]
  have hrpow : t ^ r ≤ 1 + t ^ N := by
    rcases le_or_gt t 1 with ht1 | ht1
    · linarith [Real.rpow_le_one ht0.le ht1 hr, pow_nonneg ht0.le N]
    · have h1 := Real.rpow_le_rpow_of_exponent_le ht1.le hrN
      rw [Real.rpow_natCast] at h1
      linarith
  have hpowN : t ^ N ≤ ((Nat.factorial N : ℝ) / π ^ N) * Real.exp (π * t) := by
    have hx := Real.pow_div_factorial_le_exp (π * t) (by positivity) N
    have hfac : (0 : ℝ) < (Nat.factorial N : ℝ) := by positivity
    have hpiN : (0 : ℝ) < π ^ N := by positivity
    calc t ^ N = (π ^ N)⁻¹ * (π * t) ^ N := by
          rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ hpiN.ne', one_mul]
      _ ≤ (π ^ N)⁻¹ * ((Nat.factorial N : ℝ) * Real.exp (π * t)) := by
          gcongr; simpa [mul_comm] using (div_le_iff₀ hfac).mp hx
      _ = ((Nat.factorial N : ℝ) / π ^ N) * Real.exp (π * t) := by ring
  have h1exp : (1 : ℝ) ≤ Real.exp (π * t) := Real.one_le_exp (by positivity)
  calc t ^ r * Real.exp (-2 * π * t)
      ≤ (1 + t ^ N) * Real.exp (-2 * π * t) := mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le
    _ ≤ (Real.exp (π * t) + ((Nat.factorial N : ℝ) / π ^ N) * Real.exp (π * t)) *
          Real.exp (-2 * π * t) := by gcongr
    _ = (1 + ((Nat.factorial N : ℝ) / π ^ N)) * (Real.exp (π * t) * Real.exp (-2 * π * t)) := by ring
    _ = (1 + ((Nat.factorial N : ℝ) / π ^ N)) * Real.exp (-π * t) := by
        rw [← Real.exp_add]; congr 2; ring

/-- Fourier transform of a compactly supported continuous radial lift on `ℝ^{2w}` equals its
Hankel transform for all `ξ ≠ 0` (`int:sonine`). -/
theorem fourier_radialLift_eq_hankelTransform {w : ℕ} (hw : 1 ≤ w) {b : ℝ} (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ_cont : Continuous φ) (hφ_supp : ∀ t, t ∉ Ioc 0 b → φ t = 0)
    {ξ : EuclideanSpace ℝ (Fin (2 * w))} (hξ : ξ ≠ 0) :
    𝓕 (radialLift w φ) ξ =
      ((kerTransform (hankelMeasure w) (hankelKernel w) φ (‖ξ‖ ^ 2 / 2) : ℝ) : ℂ) := by
  let F : EuclideanSpace ℝ (Fin (2 * w)) → ℂ := radialLift w φ
  have hF_im : (𝓕 F ξ).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    change star (𝓕 F ξ) = 𝓕 F ξ
    rw [Real.fourier_eq']
    simp_rw [Complex.star_def]
    rw [← integral_conj]
    have h_conj : ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
        (starRingEnd ℂ) (Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • F v) =
        ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
          Complex.exp (↑(-2 * π * inner ℝ (-v) ξ) * Complex.I) • F (-v) := by
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp only [smul_eq_mul, map_mul, F, radialLift, Complex.conj_ofReal, ← Complex.exp_conj,
        Complex.conj_I, norm_neg, inner_neg_left]
      congr 2
      push_cast; ring
    rw [h_conj]
    have hmp := (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin (2 * w)))).measurePreserving
    have heq_neg : ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
        Complex.exp (↑(-2 * π * inner ℝ (-v) ξ) * Complex.I) • F (-v) =
        ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
          Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • F v :=
      hmp.integral_comp (LinearIsometryEquiv.neg ℝ).toHomeomorph.measurableEmbedding
        (fun v => Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • F v)
    rw [heq_neg]
  have hφ_supp' : ∀ x : EuclideanSpace ℝ (Fin (2 * w)), Real.sqrt (2 * b) < ‖x‖ → F x = 0 := by
    intro x hx
    have hgt : b < ‖x‖ ^ 2 / 2 := by
      have hsq : 2 * b < ‖x‖ ^ 2 := by
        calc 2 * b = (Real.sqrt (2 * b)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
          _ < ‖x‖ ^ 2 := by gcongr
      linarith
    simp [F, radialLift, hφ_supp _ fun hm => not_le.mpr hgt hm.2]
  have hF_cont : Continuous F := by
    refine Complex.continuous_ofReal.comp (hφ_cont.comp ?_)
    fun_prop
  have hF_cs : HasCompactSupport F := by
    refine HasCompactSupport.of_support_subset_isCompact
      (ProperSpace.isCompact_closedBall 0 (Real.sqrt (2 * b))) fun x hx => ?_
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! hlt
    exact hx (hφ_supp' x hlt)
  have hF_int : Integrable F volume := hF_cont.integrable_of_hasCompactSupport hF_cs
  let s₀ : ℝ := ‖ξ‖ ^ 2 / 2
  have hs₀ : 0 < s₀ := div_pos (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hξ)) two_pos
  have hdiff_le : ∀ {ε : ℝ}, 0 < ε →
      |(𝓕 F ξ).re - kerTransform (hankelMeasure w) (hankelKernel w) φ s₀| ≤
        ε * (((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) *
            (∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t)) +
          2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
            ∫ t in Ioi 0, t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-2 * π * t)) := by
    intro ε hε
    obtain ⟨N, c, hc⟩ := exists_expPoly_approx hb hφ_cont hφ_supp hε
    let p_exp : ℝ → ℝ := fun t =>
      ∑ k ∈ Finset.range N, c k * Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t)
    have hp_fourier : (𝓕 (radialLift w p_exp) ξ).re =
        kerTransform (hankelMeasure w) (hankelKernel w) p_exp s₀ := by
      have hterm_int : ∀ k ∈ Finset.range N,
          Integrable (fun x : EuclideanSpace ℝ (Fin (2 * w)) =>
            (c k : ℂ) * radialLift w (fun t => Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t)) x) volume :=
        fun k _ => (integrable_radialLift_exp w (by positivity : (0 : ℝ) < (k + 1 : ℕ))).const_mul _
      have hlift_sum : radialLift w p_exp =
          fun x => ∑ k ∈ Finset.range N,
            (c k : ℂ) * radialLift w (fun t => Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t)) x := by
        ext x; simp [radialLift, p_exp]
      have hF_sum : 𝓕 (radialLift w p_exp) ξ =
          ∑ k ∈ Finset.range N, (c k : ℂ) *
            𝓕 (radialLift w (fun t => Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t))) ξ := by
        rw [hlift_sum, Real.fourier_eq']
        have heq_s : ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
            Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) •
              (∑ k ∈ Finset.range N,
                (c k : ℂ) * radialLift w (fun t => Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t)) v) =
            ∫ v : EuclideanSpace ℝ (Fin (2 * w)),
              ∑ k ∈ Finset.range N, (c k : ℂ) *
                (Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) •
                  radialLift w (fun t => Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t)) v) := by
          refine integral_congr_ae (Eventually.of_forall fun v => ?_)
          simp only [smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [heq_s, integral_finsetSum]
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_const_mul, Real.fourier_eq']
        · intro k hk
          have h_exp_int := integrable_radialLift_exp w (by positivity : (0 : ℝ) < (k + 1 : ℕ))
          refine ((h_exp_int.norm.const_mul ‖(c k : ℂ)‖)).mono' ?_ ?_
          · have hc_meas : AEStronglyMeasurable (fun v : EuclideanSpace ℝ (Fin (2 * w)) =>
                (c k : ℂ) * Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I)) volume :=
              (Continuous.aestronglyMeasurable (by fun_prop))
            exact (hc_meas.mul h_exp_int.aestronglyMeasurable).congr
              (Eventually.of_forall fun v => by simp only [Pi.mul_apply, smul_eq_mul, mul_assoc])
          · refine Eventually.of_forall fun v => ?_
            have h1 : ‖Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I)‖ = 1 :=
              Complex.norm_exp_ofReal_mul_I _
            rw [smul_eq_mul, norm_mul, norm_mul, h1, one_mul]
      have hU_sum : kerTransform (hankelMeasure w) (hankelKernel w) p_exp s₀ =
          ∑ k ∈ Finset.range N, c k *
            kerTransform (hankelMeasure w) (hankelKernel w)
              (fun t => Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t)) s₀ := by
        unfold kerTransform
        rw [integral_hankelMeasure_eq]
        have heq_k : ∫ t in Ioi (0 : ℝ), t ^ (w - 1) * (hankelKernel w s₀ t * p_exp t) =
            ∫ t in Ioi (0 : ℝ), ∑ k ∈ Finset.range N, c k *
              (Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t) * (t ^ (w - 1) * hankelKernel w t s₀)) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          simp only [p_exp, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hankelKernel_symm w s₀ t]; ring
        rw [heq_k, integral_finsetSum]
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_const_mul, integral_hankelMeasure_eq]
          congr 1
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
          rw [hankelKernel_symm w s₀ t]; ring
        · intro k _
          exact (weber_laplace hw s₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ))).1.const_mul _
      have hre_sum : ∀ (s : Finset ℕ) (f : ℕ → ℂ), (∑ k ∈ s, f k).re = ∑ k ∈ s, (f k).re := by
        intro s f
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert k s hks ih => simp [Finset.sum_insert hks, ih]
      rw [hF_sum, hU_sum, hre_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [fourier_radial_exp w (by positivity : (0 : ℝ) < (k + 1 : ℕ)) ξ]
      change ((c k : ℂ) * (((((k + 1 : ℕ) : ℝ) ^ (-(w : ℝ)) *
        Real.exp (-2 * π * s₀ / ((k + 1 : ℕ) : ℝ)) : ℝ) : ℂ))).re = _
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
      congr 1
      unfold kerTransform
      rw [integral_hankelMeasure_eq]
      have hw_k := (weber_laplace hw s₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ))).2
      rw [← hw_k]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [hankelKernel_symm w s₀ t]; ring
    have hp_int_F : Integrable (radialLift w p_exp) volume := by
      have hlift_sum : radialLift w p_exp =
          fun x => ∑ k ∈ Finset.range N,
            (c k : ℂ) * radialLift w (fun t => Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t)) x := by
        ext x; simp [radialLift, p_exp]
      rw [hlift_sum]
      classical
      have h_ind : ∀ s : Finset ℕ, Integrable (fun x : EuclideanSpace ℝ (Fin (2 * w)) =>
          ∑ k ∈ s, (c k : ℂ) * radialLift w (fun t => Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t)) x)
          volume := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert k s hks ih =>
            simp_rw [Finset.sum_insert hks]
            exact ((integrable_radialLift_exp w (by positivity : (0 : ℝ) < (k + 1 : ℕ))).const_mul _).add ih
      exact h_ind (Finset.range N)
    have hp_F_bound : |(𝓕 F ξ).re - (𝓕 (radialLift w p_exp) ξ).re| ≤
        ε * (((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) *
          ∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t)) := by
      have hnorm_e : ∀ v : EuclideanSpace ℝ (Fin (2 * w)),
          ‖Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I)‖ = 1 := fun v =>
        Complex.norm_exp_ofReal_mul_I _
      have hre_le : |(𝓕 F ξ).re - (𝓕 (radialLift w p_exp) ξ).re| ≤
          ‖𝓕 (F - radialLift w p_exp) ξ‖ := by
        have hsub : 𝓕 F ξ - 𝓕 (radialLift w p_exp) ξ = 𝓕 (F - radialLift w p_exp) ξ := by
          rw [Real.fourier_eq', Real.fourier_eq', Real.fourier_eq', ← integral_sub]
          · refine integral_congr_ae (Eventually.of_forall fun v => ?_)
            simp only [Pi.sub_apply, smul_sub]
          · refine hF_int.norm.mono' ?_ ?_
            · exact (Continuous.aestronglyMeasurable (by fun_prop) : AEStronglyMeasurable
                (fun v => Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I)) volume).smul
                hF_int.aestronglyMeasurable
            · refine Eventually.of_forall fun v => ?_
              rw [smul_eq_mul, norm_mul, hnorm_e, one_mul]
          · refine hp_int_F.norm.mono' ?_ ?_
            · exact (Continuous.aestronglyMeasurable (by fun_prop) : AEStronglyMeasurable
                (fun v => Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I)) volume).smul
                hp_int_F.aestronglyMeasurable
            · refine Eventually.of_forall fun v => ?_
              rw [smul_eq_mul, norm_mul, hnorm_e, one_mul]
        rw [← Complex.sub_re, hsub]
        exact Complex.abs_re_le_norm _
      have hfourier_le : ‖𝓕 (F - radialLift w p_exp) ξ‖ ≤
          ∫ x : EuclideanSpace ℝ (Fin (2 * w)), ‖(F - radialLift w p_exp) x‖ := by
        rw [Real.fourier_eq']
        calc ‖∫ v, Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • (F - radialLift w p_exp) v‖
            ≤ ∫ v, ‖Complex.exp (↑(-2 * π * inner ℝ v ξ) * Complex.I) • (F - radialLift w p_exp) v‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ v, ‖(F - radialLift w p_exp) v‖ := by
              refine integral_congr_ae (Eventually.of_forall fun v => ?_)
              dsimp only
              rw [smul_eq_mul, norm_mul, hnorm_e, one_mul]
      have hrad : ∫ x : EuclideanSpace ℝ (Fin (2 * w)), ‖(F - radialLift w p_exp) x‖ =
          ((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) * ∫ t in Ioi 0, t ^ (w - 1) * |p_exp t - φ t| := by
        have heq_f : (fun x : EuclideanSpace ℝ (Fin (2 * w)) => ‖(F - radialLift w p_exp) x‖) =
            fun x => |p_exp (‖x‖ ^ 2 / 2) - φ (‖x‖ ^ 2 / 2)| := by
          ext x
          simp only [F, Pi.sub_apply, radialLift, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_sub_comm]
        rw [heq_f, integral_radialLiftReal hw (fun t => |p_exp t - φ t|)]
      have hint_exp : IntegrableOn (fun t => t ^ (w - 1) * (ε * Real.exp (-2 * π * t))) (Ioi 0) := by
        have heq : (fun t : ℝ => t ^ (w - 1) * (ε * Real.exp (-2 * π * t))) =
            fun t => ε * (t ^ ((w - 1 : ℕ) : ℝ) * Real.exp (-2 * π * t)) := by
          ext t; rw [Real.rpow_natCast]; ring
        rw [heq]
        exact (integrableOn_rpow_mul_exp (Nat.cast_nonneg _)).const_mul ε
      have hint_abs : IntegrableOn (fun t => t ^ (w - 1) * |p_exp t - φ t|) (Ioi 0) := by
        refine hint_exp.mono' ((by fun_prop : Continuous fun t : ℝ =>
          t ^ (w - 1) * |p_exp t - φ t|).aestronglyMeasurable) ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 := mem_Ioi.mp ht
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht0.le _) (abs_nonneg _))]
        exact mul_le_mul_of_nonneg_left (hc t ht0.le) (pow_nonneg ht0.le _)
      have hmono : ∫ t in Ioi 0, t ^ (w - 1) * |p_exp t - φ t| ≤
          ε * ∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t) := by
        calc ∫ t in Ioi 0, t ^ (w - 1) * |p_exp t - φ t|
            ≤ ∫ t in Ioi 0, ε * (t ^ (w - 1) * Real.exp (-2 * π * t)) := by
              refine setIntegral_mono_on hint_abs (hint_exp.congr_fun (fun t _ => by ring)
                measurableSet_Ioi) measurableSet_Ioi fun t ht => ?_
              have ht0 := mem_Ioi.mp ht
              calc t ^ (w - 1) * |p_exp t - φ t| ≤ t ^ (w - 1) * (ε * Real.exp (-2 * π * t)) :=
                    mul_le_mul_of_nonneg_left (hc t ht0.le) (pow_nonneg ht0.le _)
                _ = ε * (t ^ (w - 1) * Real.exp (-2 * π * t)) := by ring
          _ = ε * ∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t) := integral_const_mul _ _
      calc |(𝓕 F ξ).re - (𝓕 (radialLift w p_exp) ξ).re|
          ≤ ((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) * ∫ t in Ioi 0, t ^ (w - 1) * |p_exp t - φ t| :=
            hre_le.trans (hfourier_le.trans_eq hrad)
        _ ≤ ((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) *
              (ε * ∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t)) := by gcongr
        _ = ε * (((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) *
              ∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t)) := by ring
    have hp_U_bound : |kerTransform (hankelMeasure w) (hankelKernel w) p_exp s₀ -
          kerTransform (hankelMeasure w) (hankelKernel w) φ s₀| ≤
        ε * (2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
          ∫ t in Ioi 0, t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-2 * π * t)) := by
      unfold kerTransform
      rw [integral_hankelMeasure_eq, integral_hankelMeasure_eq]
      have hker_dom : ∀ {t : ℝ}, 0 < t →
          t ^ (w - 1) * |hankelKernel w s₀ t| ≤
            2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * t ^ (((w - 1 : ℕ) : ℝ) / 2) := by
        intro t ht
        have hk := hankelKernel_abs_le w hs₀ ht
        have hsqrt : t ^ (w - 1) * (1 / Real.sqrt (s₀ * t)) ^ (w - 1) =
            s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * t ^ (((w - 1 : ℕ) : ℝ) / 2) := by
          rw [Real.sqrt_mul hs₀.le, one_div, mul_inv, mul_pow]
          have hst : (Real.sqrt t) ^ (w - 1) ≠ 0 := (pow_pos (Real.sqrt_pos.mpr ht) _).ne'
          have hs0' : (Real.sqrt s₀) ^ (w - 1) ≠ 0 := (pow_pos (Real.sqrt_pos.mpr hs₀) _).ne'
          have ht_pow : t ^ (w - 1) = (Real.sqrt t) ^ (w - 1) * (Real.sqrt t) ^ (w - 1) := by
            rw [← mul_pow, Real.mul_self_sqrt ht.le]
          have hr_t : t ^ (((w - 1 : ℕ) : ℝ) / 2) = (Real.sqrt t) ^ (w - 1) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (t ^ (1 / 2 : ℝ)) (w - 1),
              ← Real.rpow_mul ht.le]
            congr 1; ring
          have hr_s : s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) = ((Real.sqrt s₀) ^ (w - 1))⁻¹ := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (s₀ ^ (1 / 2 : ℝ)) (w - 1),
              ← Real.rpow_mul hs₀.le, ← Real.rpow_neg hs₀.le]
            congr 1; ring
          rw [hr_t, hr_s, ht_pow]
          simp only [inv_pow]
          field_simp [hst, hs0']
        calc t ^ (w - 1) * |hankelKernel w s₀ t|
            ≤ t ^ (w - 1) * (2 * π * (1 / Real.sqrt (s₀ * t)) ^ (w - 1)) :=
              mul_le_mul_of_nonneg_left hk (pow_nonneg ht.le _)
          _ = 2 * π * (t ^ (w - 1) * (1 / Real.sqrt (s₀ * t)) ^ (w - 1)) := by ring
          _ = 2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * t ^ (((w - 1 : ℕ) : ℝ) / 2) := by
              rw [hsqrt]; ring
      have hint_dom : IntegrableOn (fun t =>
          2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
            (ε * (t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-2 * π * t)))) (Ioi 0) :=
        ((integrableOn_rpow_mul_exp (by positivity)).const_mul ε).const_mul _
      have hint_p : IntegrableOn (fun t => t ^ (w - 1) * (hankelKernel w s₀ t * p_exp t)) (Ioi 0) := by
        have heq_p : (fun t => t ^ (w - 1) * (hankelKernel w s₀ t * p_exp t)) =
            fun t => ∑ k ∈ Finset.range N, c k * (Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t) *
              (t ^ (w - 1) * hankelKernel w t s₀)) := by
          ext t
          simp only [p_exp, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hankelKernel_symm w s₀ t]; ring
        rw [heq_p]
        classical
        have h_ind : ∀ s : Finset ℕ, IntegrableOn (fun t => ∑ k ∈ s, c k *
            (Real.exp (-2 * π * ((k + 1 : ℕ) : ℝ) * t) * (t ^ (w - 1) * hankelKernel w t s₀))) (Ioi 0) := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp
          | insert k s hks ih =>
              simp_rw [Finset.sum_insert hks]
              exact ((weber_laplace hw s₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ))).1.const_mul _).add ih
        exact h_ind (Finset.range N)
      have hint_φ : IntegrableOn (fun t => t ^ (w - 1) * (hankelKernel w s₀ t * φ t)) (Ioi 0) := by
        have hcont_φ : Continuous fun t : ℝ => t ^ (w - 1) * (hankelKernel w s₀ t * φ t) :=
          (continuous_pow _).mul (((continuous_hankelKernel w).comp
            (continuous_const.prodMk continuous_id)).mul hφ_cont)
        have hcs : IntegrableOn (fun t => t ^ (w - 1) * (hankelKernel w s₀ t * φ t)) (Ioc 0 b) :=
          hcont_φ.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
        have heq_ind : Set.EqOn (fun t => t ^ (w - 1) * (hankelKernel w s₀ t * φ t))
            ((Ioc 0 b).indicator (fun t => t ^ (w - 1) * (hankelKernel w s₀ t * φ t))) (Ioi 0) := by
          intro t _
          by_cases hm : t ∈ Ioc 0 b
          · simp [hm]
          · simp [hm, hφ_supp t hm]
        exact (hcs.integrable_indicator measurableSet_Ioc).integrableOn.congr_fun
          (fun t ht => (heq_ind ht).symm) measurableSet_Ioi
      rw [← integral_sub hint_p hint_φ]
      calc |∫ t in Ioi 0, (t ^ (w - 1) * (hankelKernel w s₀ t * p_exp t) -
              t ^ (w - 1) * (hankelKernel w s₀ t * φ t))|
          = |∫ t in Ioi 0, t ^ (w - 1) * (hankelKernel w s₀ t * (p_exp t - φ t))| := by
            congr 1
            refine setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
        _ = ‖∫ t in Ioi 0, t ^ (w - 1) * (hankelKernel w s₀ t * (p_exp t - φ t))‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ t in Ioi 0, ‖t ^ (w - 1) * (hankelKernel w s₀ t * (p_exp t - φ t))‖ :=
            norm_integral_le_integral_norm _
        _ = ∫ t in Ioi 0, |t ^ (w - 1) * (hankelKernel w s₀ t * (p_exp t - φ t))| := by
            simp only [Real.norm_eq_abs]
        _ ≤ ∫ t in Ioi 0, 2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
              (ε * (t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-2 * π * t))) := by
            have hint_sub_abs : IntegrableOn (fun t =>
                |t ^ (w - 1) * (hankelKernel w s₀ t * (p_exp t - φ t))|) (Ioi 0) :=
              IntegrableOn.congr_fun (hint_p.sub hint_φ).norm (fun t _ => by
                simp only [Pi.sub_apply, Real.norm_eq_abs]; congr 1; ring) measurableSet_Ioi
            refine setIntegral_mono_on hint_sub_abs hint_dom measurableSet_Ioi fun t ht => ?_
            · have ht0 := mem_Ioi.mp ht
              rw [abs_mul, abs_of_nonneg (pow_nonneg ht0.le _), abs_mul]
              calc t ^ (w - 1) * (|hankelKernel w s₀ t| * |p_exp t - φ t|)
                  = (t ^ (w - 1) * |hankelKernel w s₀ t|) * |p_exp t - φ t| := by ring
                _ ≤ (2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) * t ^ (((w - 1 : ℕ) : ℝ) / 2)) *
                      (ε * Real.exp (-2 * π * t)) :=
                    mul_le_mul (hker_dom ht0) (hc t ht0.le) (abs_nonneg _) (by positivity)
                _ = _ := by ring
        _ = ε * (2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
              ∫ t in Ioi 0, t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-2 * π * t)) := by
            rw [integral_const_mul, integral_const_mul]
            ring
    calc |(𝓕 F ξ).re - kerTransform (hankelMeasure w) (hankelKernel w) φ s₀|
        = |((𝓕 F ξ).re - (𝓕 (radialLift w p_exp) ξ).re) +
            (kerTransform (hankelMeasure w) (hankelKernel w) p_exp s₀ -
              kerTransform (hankelMeasure w) (hankelKernel w) φ s₀)| := by
          rw [hp_fourier]; congr 1; ring
      _ ≤ |(𝓕 F ξ).re - (𝓕 (radialLift w p_exp) ξ).re| +
            |kerTransform (hankelMeasure w) (hankelKernel w) p_exp s₀ -
              kerTransform (hankelMeasure w) (hankelKernel w) φ s₀| := abs_add_le _ _
      _ ≤ ε * (((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) *
            (∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t)) +
          2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
            ∫ t in Ioi 0, t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-2 * π * t)) := by
          linarith [hp_F_bound, hp_U_bound]
  have hre : (𝓕 F ξ).re = kerTransform (hankelMeasure w) (hankelKernel w) φ s₀ := by
    by_contra hne
    set D : ℝ := |(𝓕 F ξ).re - kerTransform (hankelMeasure w) (hankelKernel w) φ s₀|
    have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr hne)
    set Ctot : ℝ := (((2 * π) ^ w / (Nat.factorial (w - 1) : ℝ)) *
        (∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t)) +
      2 * π * s₀ ^ (-((w - 1 : ℕ) : ℝ) / 2) *
        ∫ t in Ioi 0, t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-2 * π * t))
    have hCtot : 0 ≤ Ctot := by
      have hi1 : 0 ≤ ∫ t in Ioi 0, t ^ (w - 1) * Real.exp (-2 * π * t) :=
        setIntegral_nonneg measurableSet_Ioi fun t ht =>
          mul_nonneg (pow_nonneg (mem_Ioi.mp ht).le _) (Real.exp_pos _).le
      have hi2 : 0 ≤ ∫ t in Ioi 0, t ^ (((w - 1 : ℕ) : ℝ) / 2) * Real.exp (-2 * π * t) :=
        setIntegral_nonneg measurableSet_Ioi fun t ht =>
          mul_nonneg (Real.rpow_nonneg (mem_Ioi.mp ht).le _) (Real.exp_pos _).le
      positivity
    have hε := hdiff_le (ε := D / (2 * (Ctot + 1))) (by positivity)
    have hlt : D / (2 * (Ctot + 1)) * Ctot < D := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    exact not_le.mpr hlt hε
  exact Complex.ext hre hF_im

end FormalResearch.ModularBootstrap.Integrality
