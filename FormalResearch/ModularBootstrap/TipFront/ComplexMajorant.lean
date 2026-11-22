module

public import FormalResearch.ModularBootstrap.PoissonJensen.HarmonicMajorant
public import FormalResearch.ModularBootstrap.Blowup.PotentialAndWeight

/-!
# Complex Harmonic Majorant at the Tip (Lemma T2 / `LemmaGPotentialInput`)

Constructs the concrete Virasoro witness `lemmaGPotentialInput_virasoro : LemmaGPotentialInput`
with `U := PoissonJensen.majorant2D` (`blowup_limit.tex`, Lemma `bl:T2`;
`lower_o1_two_edge.tex`, Lemma G):

Near `ξ_*`,
`PoissonJensen.majorant2D b + (tipL b).re = (-KTip * ((ξ_* : ℂ) - b) ^ (3 / 2 : ℂ) * A (b - ξ_*)).re`
for an analytic function `A` on `ball 0 r_A` with `A 0 = 1` and `A(ℝ) ⊆ ℝ`.

## Proof summary
1. Write `1 - sinh(π(ξ_* + w)) = (-w) * φ w` with `φ = -dslope (fun w => 1 - sinh(π(ξ_* + w))) 0`,
   entire, real on `ℝ`, and `φ 0 = π √2 > 0`.
2. Define the holomorphic integral `arcEven z := ∫ t in (0 : ℝ)..1, (1 - t^2 z)^(-1/2)` on
   `ball 0 1` (`arcEven ((u^2 : ℝ) : ℂ) = arcsin u / u` for `u ∈ (0, 1)` and `arcEven 0 = 1`).
3. On a small ball `ball 0 r_A` where `Re(φ w / 2) > 0`, `‖(1 - sinh(π(ξ_* + w))) / 2‖ < 1`,
   and `(ξ_* : ℂ) + w ∈ slitStrip` off the cut `[0, ∞)`:
   `Θ w := (4 / π) * (φ w / 2)^(1/2) * arcEven ((1 - sinh(π(ξ_* + w))) / 2)` is analytic,
   real on `ℝ`, nonzero at `0`, and by the identity principle on the star-shaped cut disk
   satisfies `(-w)^(1/2) * Θ w = 1 - 2 i pMap (ξ_* + w)`.
4. Setting `A w := (3/2) ∫₀¹ t^(1/2) (Θ (t w) / Θ 0) dt`, differentiation under the integral
   sign and integration by parts show that `-KTip * (-w)^(3/2) * A w` and
   `tipL(ξ_* + w) - i * majorantHolomorphic(ξ_* + w)` have the same derivative on the cut disk,
   hence differ by a constant, which vanishes by taking `w = -δ → 0⁻`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.TipFront

open PoissonJensen

private lemma analyticOnNhd_cpow_const (c : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => z ^ c) slitPlane :=
  (DifferentiableOn.cpow_const differentiableOn_id fun _ h => h).analyticOnNhd
    Complex.isOpen_slitPlane

/-! ### Step 1: Smooth factorization of `1 - sinh(π(ξ_* + w))` -/

private noncomputable def sinhTipDefect (w : ℂ) : ℂ :=
  1 - Complex.sinh ((π : ℂ) * ((xiStar : ℂ) + w))

private noncomputable def sinhTipFactor (w : ℂ) : ℂ :=
  -dslope sinhTipDefect 0 w

private lemma differentiable_sinhTipDefect : Differentiable ℂ sinhTipDefect := fun w =>
  (differentiableAt_const _).sub
    ((Complex.differentiableAt_sinh).comp w
      ((differentiableAt_const _).mul ((differentiableAt_const _).add differentiableAt_id)))

private lemma sinhTipDefect_zero : sinhTipDefect 0 = 0 := by
  unfold sinhTipDefect
  rw [add_zero, ← Complex.ofReal_mul, ← Complex.ofReal_sinh, sinh_pi_mul_xiStar]
  simp

private lemma hasDerivAt_sinhTipDefect_zero :
    HasDerivAt sinhTipDefect (-((π * √2 : ℝ) : ℂ)) 0 := by
  have hlin : HasDerivAt (fun w : ℂ => (π : ℂ) * ((xiStar : ℂ) + w)) (π : ℂ) 0 := by
    have h1 : HasDerivAt (fun w : ℂ => (xiStar : ℂ) + w) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_add (xiStar : ℂ)
    simpa using h1.const_mul (π : ℂ)
  have hsinh : HasDerivAt (fun w : ℂ => Complex.sinh ((π : ℂ) * ((xiStar : ℂ) + w)))
      (Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + 0)) * (π : ℂ)) 0 :=
    (Complex.hasDerivAt_sinh _).comp 0 hlin
  have hsub : HasDerivAt sinhTipDefect
      (-(Complex.cosh ((π : ℂ) * ((xiStar : ℂ) + 0)) * (π : ℂ))) 0 :=
    (hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub hsinh |>.congr_deriv (by simp)
  refine hsub.congr_deriv ?_
  have hcosh_sq : Real.cosh (π * xiStar) ^ 2 = 2 := by
    have h := Real.cosh_sq (π * xiStar)
    rw [sinh_pi_mul_xiStar] at h
    linarith
  have hcosh_eq : Real.cosh (π * xiStar) = √2 := by
    rw [← Real.sqrt_sq (Real.cosh_pos _).le, hcosh_sq]
  rw [add_zero, ← Complex.ofReal_mul, ← Complex.ofReal_cosh, hcosh_eq]
  push_cast
  ring

private lemma differentiable_sinhTipFactor : Differentiable ℂ sinhTipFactor := by
  have hd : DifferentiableOn ℂ (dslope sinhTipDefect 0) univ :=
    (Complex.differentiableOn_dslope univ_mem).mpr differentiable_sinhTipDefect.differentiableOn
  exact (differentiableOn_univ.mp hd).neg

private lemma sinhTipDefect_eq (w : ℂ) :
    sinhTipDefect w = -w * sinhTipFactor w := by
  by_cases hw : w = 0
  · subst hw
    rw [sinhTipDefect_zero, neg_zero, zero_mul]
  · unfold sinhTipFactor
    rw [dslope_of_ne _ hw, slope, sinhTipDefect_zero, sub_zero, vsub_eq_sub, sub_zero,
      smul_eq_mul]
    field_simp [hw]

private lemma sinhTipFactor_zero : sinhTipFactor 0 = ((π * √2 : ℝ) : ℂ) := by
  unfold sinhTipFactor
  rw [dslope_same, hasDerivAt_sinhTipDefect_zero.deriv]
  simp

private lemma sinhTipDefect_ofReal (x : ℝ) :
    sinhTipDefect (x : ℂ) = ((1 - Real.sinh (π * (xiStar + x)) : ℝ) : ℂ) := by
  unfold sinhTipDefect
  rw [← Complex.ofReal_add, ← Complex.ofReal_mul, ← Complex.ofReal_sinh]
  push_cast
  rfl

private lemma sinhTipFactor_ofReal_im (x : ℝ) : (sinhTipFactor (x : ℂ)).im = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Complex.ofReal_zero, sinhTipFactor_zero, Complex.ofReal_im]
  · unfold sinhTipFactor
    rw [dslope_of_ne _ (Complex.ofReal_ne_zero.mpr hx), slope, sinhTipDefect_ofReal,
      sinhTipDefect_zero, sub_zero, vsub_eq_sub, sub_zero, smul_eq_mul,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_im]

/-! ### Step 2: Analytic normalized arcsine `arcEven z = ∫₀¹ (1 - t² z)^(-1/2) dt` -/

private noncomputable def arcEven (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (1 - ((t : ℂ) ^ 2) * z) ^ (-(1 / 2 : ℂ))

private lemma one_sub_sq_mul_mem_slitPlane {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    1 - ((t : ℂ) ^ 2) * z ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hre : ((1 - ((t : ℂ) ^ 2) * z)).re = 1 - t ^ 2 * z.re := by
    simp [pow_two]
  rw [hre]
  have h1 : t ^ 2 * z.re ≤ t ^ 2 * ‖z‖ :=
    mul_le_mul_of_nonneg_left (Complex.re_le_norm z) (sq_nonneg t)
  have h2 : t ^ 2 ≤ 1 := by nlinarith
  have h3 : t ^ 2 * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) h2
  linarith

private lemma differentiableOn_arcEven : DifferentiableOn ℂ arcEven (ball (0 : ℂ) 1) := by
  intro z₀ hz₀
  rw [Metric.mem_ball, dist_zero_right] at hz₀
  let r₁ : ℝ := (1 - ‖z₀‖) / 2
  have hr₁_pos : 0 < r₁ := by dsimp [r₁]; linarith
  have hcb_sub : closedBall z₀ r₁ ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have htr := norm_add_le (z - z₀) z₀
    have heq : z = (z - z₀) + z₀ := by ring
    rw [← heq] at htr
    dsimp [r₁] at hz
    linarith
  let F : ℂ → ℝ → ℂ := fun z t => (1 - ((t : ℂ) ^ 2) * z) ^ (-(1 / 2 : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z t =>
    ((1 / 2 : ℂ) * ((t : ℂ) ^ 2)) * (1 - ((t : ℂ) ^ 2) * z) ^ (-(3 / 2 : ℂ))
  have h_slit : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ closedBall z₀ r₁,
      1 - ((p.1 : ℂ) ^ 2) * p.2 ∈ slitPlane := fun p hp =>
    one_sub_sq_mul_mem_slitPlane hp.1.1 hp.1.2 (by simpa [mem_ball, dist_zero_right] using hcb_sub hp.2)
  have h_arg_cont : ContinuousOn (fun p : ℝ × ℂ => 1 - ((p.1 : ℂ) ^ 2) * p.2)
      (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ r₁) :=
    (continuous_const.sub ((Complex.continuous_ofReal.comp continuous_fst).pow 2 |>.mul
      continuous_snd)).continuousOn
  have hF'_cont : ContinuousOn (fun p : ℝ × ℂ => F' p.2 p.1) (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ r₁) := by
    have hpow : ContinuousOn
        (fun p : ℝ × ℂ => (1 - ((p.1 : ℂ) ^ 2) * p.2) ^ (-(3 / 2 : ℂ)))
        (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ r₁) :=
      ContinuousOn.cpow_const h_arg_cont fun p hp => h_slit p hp
    exact ((continuous_const.mul ((Complex.continuous_ofReal.comp continuous_fst).pow 2)).continuousOn).mul
      hpow
  have hK_compact : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ r₁) :=
    isCompact_Icc.prod (isCompact_closedBall z₀ r₁)
  have hK_ne : (Icc (0 : ℝ) 1 ×ˢ closedBall z₀ r₁).Nonempty :=
    ⟨(0, z₀), ⟨le_rfl, zero_le_one⟩, Metric.mem_closedBall_self hr₁_pos.le⟩
  obtain ⟨p_max, _, hp_max⟩ := hK_compact.exists_isMaxOn hK_ne hF'_cont.norm
  let M_bd : ℝ := ‖F' p_max.2 p_max.1‖
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) (volume.restrict (Ι 0 1)) := by
    filter_upwards [Metric.ball_mem_nhds z₀ hr₁_pos] with z hz
    have hm : ContinuousOn (F z) (Icc 0 1) := by
      refine ContinuousOn.cpow_const ?_ fun t ht =>
        one_sub_sq_mul_mem_slitPlane ht.1 ht.2
          (by simpa [mem_ball, dist_zero_right] using hcb_sub (Metric.ball_subset_closedBall hz))
      exact (continuous_const.sub ((Complex.continuous_ofReal.pow 2).mul continuous_const)).continuousOn
    rw [Set.uIoc_of_le zero_le_one]
    exact (hm.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hF_int : IntervalIntegrable (F z₀) volume 0 1 := by
    have hm : ContinuousOn (F z₀) (Icc 0 1) := by
      refine ContinuousOn.cpow_const ?_ fun t ht =>
        one_sub_sq_mul_mem_slitPlane ht.1 ht.2 hz₀
      exact (continuous_const.sub ((Complex.continuous_ofReal.pow 2).mul continuous_const)).continuousOn
    exact hm.intervalIntegrable_of_Icc zero_le_one
  have hF'_meas : AEStronglyMeasurable (F' z₀) (volume.restrict (Ι 0 1)) := by
    rw [Set.uIoc_of_le zero_le_one]
    have hm : ContinuousOn (F' z₀) (Icc 0 1) := by
      refine ((continuous_const.mul (Complex.continuous_ofReal.pow 2)).continuousOn).mul ?_
      refine ContinuousOn.cpow_const ?_ fun t ht =>
        one_sub_sq_mul_mem_slitPlane ht.1 ht.2 hz₀
      exact (continuous_const.sub ((Complex.continuous_ofReal.pow 2).mul continuous_const)).continuousOn
    exact (hm.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ z ∈ Metric.ball z₀ r₁, ‖F' z t‖ ≤ M_bd :=
    Eventually.of_forall fun t ht z hz => by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact @hp_max (t, z) ⟨Ioc_subset_Icc_self ht, Metric.ball_subset_closedBall hz⟩
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ z ∈ Metric.ball z₀ r₁,
      HasDerivAt (fun w => F w t) (F' z t) z := by
    refine Eventually.of_forall fun t ht z hz => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hmem_z : ‖z‖ < 1 := by
      simpa [mem_ball, dist_zero_right] using hcb_sub (Metric.ball_subset_closedBall hz)
    have hsp := one_sub_sq_mul_mem_slitPlane ht.1.le ht.2 hmem_z
    have hd_lin : HasDerivAt (fun w : ℂ => 1 - ((t : ℂ) ^ 2) * w) (-((t : ℂ) ^ 2)) z := by
      have h1 : HasDerivAt (fun w : ℂ => ((t : ℂ) ^ 2) * w) ((t : ℂ) ^ 2) z := by
        simpa using (hasDerivAt_id z).const_mul ((t : ℂ) ^ 2)
      exact ((hasDerivAt_const z (1 : ℂ)).sub h1).congr_deriv (by ring)
    have hd_cp := hd_lin.cpow_const (c := -(1 / 2 : ℂ)) hsp
    refine hd_cp.congr_deriv ?_
    dsimp [F']
    rw [show -(1 / 2 : ℂ) - 1 = -(3 / 2 : ℂ) by norm_num]
    ring
  have hderiv := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ hr₁_pos) hF_meas hF_int hF'_meas h_bound intervalIntegrable_const h_diff).2
  exact hderiv.differentiableAt.differentiableWithinAt

private lemma analyticOnNhd_arcEven : AnalyticOnNhd ℂ arcEven (ball (0 : ℂ) 1) :=
  differentiableOn_arcEven.analyticOnNhd isOpen_ball

private lemma arcEven_zero : arcEven 0 = 1 := by
  unfold arcEven
  simp

private lemma arcEven_ofReal_im {x : ℝ} (hx : |x| < 1) : (arcEven (x : ℂ)).im = 0 := by
  unfold arcEven
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
      (1 - ((t : ℂ) ^ 2) * (x : ℂ)) ^ (-(1 / 2 : ℂ)) =
        ((((1 - t ^ 2 * x) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hpos : 0 < 1 - t ^ 2 * x := by
      have h1 : t ^ 2 * x ≤ t ^ 2 * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) (sq_nonneg t)
      have h2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      have h3 : t ^ 2 * |x| ≤ |x| := mul_le_of_le_one_left (abs_nonneg x) h2
      linarith
    rw [show 1 - ((t : ℂ) ^ 2) * (x : ℂ) = ((1 - t ^ 2 * x : ℝ) : ℂ) by push_cast; ring,
      show -(1 / 2 : ℂ) = (((-(1 / 2 : ℝ) : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hpos.le]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal, Complex.ofReal_im]

private lemma arcEven_sq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    arcEven ((u ^ 2 : ℝ) : ℂ) = ((Real.arcsin u / u : ℝ) : ℂ) := by
  unfold arcEven
  have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
      (1 - ((t : ℂ) ^ 2) * ((u ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ)) =
        (((1 / √(1 - (t * u) ^ 2) : ℝ)) : ℂ) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have htu_nn : 0 ≤ t * u := mul_nonneg ht.1 hu0.le
    have htu_le : t * u ≤ u := mul_le_of_le_one_left hu0.le ht.2
    have htu : (t * u) ^ 2 < 1 := by nlinarith
    have hpos : 0 < 1 - (t * u) ^ 2 := sub_pos.mpr htu
    rw [show 1 - ((t : ℂ) ^ 2) * ((u ^ 2 : ℝ) : ℂ) = ((1 - (t * u) ^ 2 : ℝ) : ℂ) by
        push_cast; ring,
      show -(1 / 2 : ℂ) = (((-(1 / 2 : ℝ) : ℝ)) : ℂ) by norm_num,
      ← Complex.ofReal_cpow hpos.le]
    congr 1
    rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, one_div]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal]
  congr 1
  have hsub : ∫ t in (0 : ℝ)..1, 1 / √(1 - (t * u) ^ 2) =
      u⁻¹ * ∫ s in (0 : ℝ)..u, 1 / √(1 - s ^ 2) := by
    simpa [Function.comp, zero_mul, one_mul] using
      (intervalIntegral.integral_comp_mul_right (fun s : ℝ => 1 / √(1 - s ^ 2)) hu0.ne'
        (a := 0) (b := 1))
  have hftc : ∫ s in (0 : ℝ)..u, 1 / √(1 - s ^ 2) = Real.arcsin u := by
    have hcont : ContinuousOn Real.arcsin (Icc 0 u) := Real.continuous_arcsin.continuousOn
    have hderiv : ∀ s ∈ Ioo 0 u, HasDerivAt Real.arcsin (1 / √(1 - s ^ 2)) s := fun s hs => by
      simpa [one_div] using Real.hasDerivAt_arcsin (by linarith [hs.1]) (by linarith [hs.2])
    have hint : IntervalIntegrable (fun s : ℝ => 1 / √(1 - s ^ 2)) volume 0 u := by
      refine ContinuousOn.intervalIntegrable_of_Icc hu0.le ?_
      refine ContinuousOn.div continuousOn_const
        (ContinuousOn.sqrt (Continuous.continuousOn (by fun_prop))) fun s hs => ?_
      have hs2 : s ^ 2 < 1 := by nlinarith [hs.1, hs.2]
      exact (Real.sqrt_pos.mpr (sub_pos.mpr hs2)).ne'
    simpa [Real.arcsin_zero, sub_zero] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu0.le hcont hderiv hint
  rw [hsub, hftc]
  ring

/-! ### Step 3: Elementary cut geometry & local representation `1 - 2 i pMap (ξ_* + w)` -/

private lemma cutBall_preconnected (r : ℝ) :
    IsPreconnected {w : ℂ | w ∈ ball (0 : ℂ) r ∧ ¬(w.im = 0 ∧ 0 ≤ w.re)} := by
  by_cases hr : r ≤ 0
  · have hemp : {w : ℂ | w ∈ ball (0 : ℂ) r ∧ ¬(w.im = 0 ∧ 0 ≤ w.re)} = ∅ := by
      ext w
      simp [Metric.ball_eq_empty.mpr hr]
    rw [hemp]
    exact isPreconnected_empty
  have hr_pos : 0 < r := lt_of_not_ge hr
  let S : Set ℂ := {w : ℂ | w ∈ ball (0 : ℂ) r ∧ ¬(w.im = 0 ∧ 0 ≤ w.re)}
  let p₀ : ℂ := ((-(r / 2) : ℝ) : ℂ)
  have hp₀ : p₀ ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith)]
      linarith
    · intro h
      have hre : p₀.re = -(r / 2) := Complex.ofReal_re _
      linarith [h.2]
  have hstar : StarConvex ℝ p₀ S := by
    intro w hw a b ha hb hab
    refine ⟨convex_ball (0 : ℂ) r hp₀.1 hw.1 ha hb hab, ?_⟩
    rintro ⟨him, hre⟩
    have him_eq : (a • p₀ + b • w).im = b * w.im := by
      simp [p₀, Complex.add_im, Complex.real_smul]
    rw [him_eq] at him
    rcases mul_eq_zero.mp him with rfl | hwim
    · have ha1 : a = 1 := by linarith
      rw [ha1, zero_smul, add_zero, one_smul] at hre
      have hre_p₀ : p₀.re = -(r / 2) := Complex.ofReal_re _
      linarith [hre_p₀]
    · have hwre : w.re < 0 := by
        by_contra hle
        exact hw.2 ⟨hwim, not_lt.mp hle⟩
      have hre_eq : (a • p₀ + b • w).re = a * (-(r / 2)) + b * w.re := by
        simp [p₀, Complex.add_re, Complex.real_smul]
      rw [hre_eq] at hre
      rcases eq_or_lt_of_le ha with rfl | ha_pos
      · have hb1 : b = 1 := by linarith
        rw [hb1] at hre
        linarith
      · have h1 : a * (-(r / 2)) < 0 := mul_neg_of_pos_of_neg ha_pos (by linarith)
        have h2 : b * w.re ≤ 0 := by nlinarith
        linarith
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  let seg : ℂ → ℝ → ℂ := fun z t => (1 - t) • p₀ + t • z
  have hseg_sub : ∀ z ∈ S, seg z '' Icc 0 1 ⊆ S := by
    rintro z hz _ ⟨t, ht, rfl⟩
    exact hstar hz (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hseg_pre : ∀ z : ℂ, IsPreconnected (seg z '' Icc 0 1) := fun z =>
    isPreconnected_Icc.image (seg z)
      (by fun_prop : Continuous fun t : ℝ => (1 - t) • p₀ + t • z).continuousOn
  refine ⟨seg x '' Icc 0 1 ∪ seg y '' Icc 0 1,
    Set.union_subset (hseg_sub x hx) (hseg_sub y hy),
    Or.inl ⟨1, right_mem_Icc.mpr zero_le_one, by simp [seg]⟩,
    Or.inr ⟨1, right_mem_Icc.mpr zero_le_one, by simp [seg]⟩,
    (hseg_pre x).union p₀ ⟨0, left_mem_Icc.mpr zero_le_one, by simp [seg]⟩
      ⟨0, left_mem_Icc.mpr zero_le_one, by simp [seg]⟩ (hseg_pre y)⟩

private lemma neg_mem_slitPlane_iff (w : ℂ) : (-w) ∈ slitPlane ↔ ¬(w.im = 0 ∧ 0 ≤ w.re) := by
  rw [Complex.mem_slitPlane_iff]
  simp only [Complex.neg_re, Complex.neg_im, neg_ne_zero, neg_pos, not_and, not_le]
  constructor
  · rintro (h | h) him
    · exact h
    · exact False.elim (h him)
  · intro h
    by_cases him : w.im = 0
    · exact Or.inl (h him)
    · exact Or.inr him

private lemma tip_add_mem_slitStrip {w : ℂ} (hw : w ∈ ball (0 : ℂ) (min (xiStar / 2) (1 / 4)))
    (hcut : ¬(w.im = 0 ∧ 0 ≤ w.re)) :
    (xiStar : ℂ) + w ∈ slitStrip := by
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hw_lt1 : ‖w‖ < xiStar / 2 := lt_of_lt_of_le hw (min_le_left _ _)
  have hw_lt2 : ‖w‖ < 1 / 4 := lt_of_lt_of_le hw (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · change |((xiStar : ℂ) + w).im| < 1 / 2
    rw [Complex.add_im, Complex.ofReal_im, zero_add]
    linarith [abs_im_le_norm w]
  · rintro ⟨him, hre⟩
    rw [Complex.add_im, Complex.ofReal_im, zero_add] at him
    have hw_neg : w.re < 0 := by
      by_contra h
      exact hcut ⟨him, not_lt.mp h⟩
    have hre_eq : ((xiStar : ℂ) + w).re = xiStar + w.re := by simp
    rw [hre_eq] at hre
    have hre_bound : -xiStar < xiStar + w.re := by
      have : -‖w‖ ≤ w.re := neg_le_of_abs_le (abs_re_le_norm w)
      linarith [xiStar_pos]
    have habs_lt : |xiStar + w.re| < xiStar := abs_lt.mpr ⟨hre_bound, by linarith⟩
    linarith

private lemma four_thirds_inv_pi_arcsin_eq (y : ℝ) (hy0 : -1 ≤ y) (hy1 : y ≤ 1) :
    1 - (2 / π) * Real.arcsin y = (4 / π) * Real.arcsin √((1 - y) / 2) := by
  have hy_nonneg : 0 ≤ (1 - y) / 2 := by linarith
  have hy_le_one : (1 - y) / 2 ≤ 1 := by linarith
  let s : ℝ := √((1 - y) / 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hy_le_one
  let θ : ℝ := Real.arcsin s
  have hθ0 : 0 ≤ θ := Real.arcsin_nonneg.mpr hs0
  have hθ_le : θ ≤ π / 2 := Real.arcsin_le_pi_div_two s
  have hsin : Real.sin θ = s := Real.sin_arcsin (by linarith) hs1
  have hcos : Real.cos (2 * θ) = y := by
    rw [Real.cos_two_mul, Real.cos_sq', hsin]
    dsimp [s]
    rw [Real.sq_sqrt hy_nonneg]
    ring
  have hsin_eq : Real.arcsin y = π / 2 - 2 * θ := by
    calc Real.arcsin y
        = Real.arcsin (Real.cos (2 * θ)) := by rw [hcos]
      _ = Real.arcsin (Real.sin (π / 2 - 2 * θ)) := by rw [Real.sin_pi_div_two_sub]
      _ = π / 2 - 2 * θ := Real.arcsin_sin (by linarith) (by linarith)
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  rw [hsin_eq]
  field_simp
  ring

/-! ### Step 4: Construction of `Θ`, `A`, and `lemmaGPotentialInput_virasoro` -/

private lemma tip_prefactor_identity :
    (3 / 2 : ℝ) * KTip = (2 * π / 3) * (4 / π * √(π * √2 / 2)) := by
  have hpi : 0 < π := Real.pi_pos
  have hK : 0 < (3 / 2 : ℝ) * KTip := mul_pos (by norm_num) KTip_pos
  have hR : 0 < (2 * π / 3) * (4 / π * √(π * √2 / 2)) := by positivity
  rw [← Real.sqrt_sq hK.le, ← Real.sqrt_sq hR.le]
  congr 1
  have hsq1 : ((3 / 2 : ℝ) * KTip) ^ 2 = 32 * π * √2 / 9 := by
    unfold KTip kTip
    have h2 : ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = 2 * √2 := by
      rw [sq, ← Real.rpow_add (by norm_num), show (3 / 4 : ℝ) + (3 / 4 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hsqrtpi : (√π) ^ 2 = π := Real.sq_sqrt hpi.le
    calc ((3 / 2 : ℝ) * (2 * π * (4 * 2 ^ (3 / 4 : ℝ) / (9 * √π)))) ^ 2
        = (16 * π ^ 2 / 9) * ((2 : ℝ) ^ (3 / 4 : ℝ)) ^ 2 / (√π) ^ 2 := by ring
      _ = (16 * π ^ 2 / 9) * (2 * √2) / π := by rw [h2, hsqrtpi]
      _ = 32 * π * √2 / 9 := by field_simp [hpi.ne']; ring
  have hsq2 : ((2 * π / 3) * (4 / π * √(π * √2 / 2))) ^ 2 = 32 * π * √2 / 9 := by
    have hnn : 0 ≤ π * √2 / 2 := by positivity
    rw [show (2 * π / 3) * (4 / π * √(π * √2 / 2)) = (8 / 3 : ℝ) * √(π * √2 / 2) by
        field_simp [hpi.ne']; ring,
      mul_pow, Real.sq_sqrt hnn]
    ring
  rw [hsq1, hsq2]

private noncomputable def tipPotentialHolo (b : ℂ) : ℂ :=
  tipL b - Complex.I * majorantHolomorphic b

private lemma tipPotentialHolo_re (b : ℂ) :
    (tipPotentialHolo b).re = (tipL b).re + majorant2D b := by
  unfold tipPotentialHolo majorant2D
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub]
  ring

private lemma hasDerivAt_tipPotentialHolo {b : ℂ} (hb : b ∈ slitStrip) :
    HasDerivAt tipPotentialHolo (((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap b)) b := by
  unfold tipPotentialHolo
  have hL : tipL = fun b : ℂ => ((2 * π / 3 : ℝ) : ℂ) * b := rfl
  have hdL : HasDerivAt tipL ((2 * π / 3 : ℝ) : ℂ) b := by
    rw [hL]
    simpa using (hasDerivAt_id b).const_mul ((2 * π / 3 : ℝ) : ℂ)
  have hdM := (hasDerivAt_majorantHolomorphic hb).const_mul Complex.I
  have hd := hdL.sub hdM
  refine hd.congr_deriv ?_
  push_cast
  ring

/-- Concrete **`LemmaGPotentialInput`** witness with `U := PoissonJensen.majorant2D`
(`blowup_limit.tex`, Lemma `bl:T2`; `lower_o1_two_edge.tex`, Lemma G). -/
theorem lemmaGPotentialInput_virasoro_exists :
    ∃ inp : LemmaGPotentialInput, inp.U = majorant2D := by
  have hf_cont : ContinuousAt (fun w : ℂ => (sinhTipFactor w / 2).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      ((differentiable_sinhTipFactor 0).continuousAt.div_const 2)
  have hf_pos0 : 0 < (sinhTipFactor 0 / 2).re := by
    rw [sinhTipFactor_zero, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div,
      Complex.ofReal_re]
    positivity
  have hev_re : ∀ᶠ w in 𝓝 (0 : ℂ), 0 < (sinhTipFactor w / 2).re :=
    hf_cont.eventually (Ioi_mem_nhds hf_pos0)
  have hev_def : ∀ᶠ w in 𝓝 (0 : ℂ), sinhTipDefect w / 2 ∈ ball (0 : ℂ) 1 := by
    have hcont : ContinuousAt (fun w : ℂ => sinhTipDefect w / 2) 0 :=
      (differentiable_sinhTipDefect 0).continuousAt.div_const 2
    have h0 : sinhTipDefect 0 / 2 ∈ ball (0 : ℂ) 1 := by
      rw [sinhTipDefect_zero, zero_div]
      exact mem_ball_self one_pos
    exact hcont.eventually (isOpen_ball.mem_nhds h0)
  obtain ⟨r₁, hr₁, hb₁⟩ := Metric.mem_nhds_iff.mp hev_re
  obtain ⟨r₂, hr₂, hb₂⟩ := Metric.mem_nhds_iff.mp hev_def
  let r_A : ℝ := min (min r₁ r₂) (min (xiStar / 2) (1 / 4))
  have hr_A_pos : 0 < r_A := by
    have := xiStar_pos
    exact lt_min (lt_min hr₁ hr₂) (lt_min (by positivity) (by norm_num))
  let Θ : ℂ → ℂ := fun w =>
    ((4 / π : ℝ) : ℂ) * (sinhTipFactor w / 2) ^ (1 / 2 : ℂ) * arcEven (sinhTipDefect w / 2)
  have hΘ_slit : ∀ w ∈ ball (0 : ℂ) r_A, sinhTipFactor w / 2 ∈ slitPlane := fun w hw => by
    have hw1 : w ∈ ball (0 : ℂ) r₁ :=
      ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hw
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (hb₁ hw1))
  have hΘ_def_ball : ∀ w ∈ ball (0 : ℂ) r_A, sinhTipDefect w / 2 ∈ ball (0 : ℂ) 1 := fun w hw =>
    hb₂ (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hw)
  have hΘ_an : AnalyticOnNhd ℂ Θ (ball (0 : ℂ) r_A) := by
    intro w hw
    have hfac_an : AnalyticOnNhd ℂ sinhTipFactor univ :=
      differentiable_sinhTipFactor.differentiableOn.analyticOnNhd isOpen_univ
    have hdef_an : AnalyticOnNhd ℂ sinhTipDefect univ :=
      differentiable_sinhTipDefect.differentiableOn.analyticOnNhd isOpen_univ
    have h1 : AnalyticAt ℂ (fun z => (sinhTipFactor z / 2) ^ (1 / 2 : ℂ)) w :=
      AnalyticAt.comp (f := fun z => sinhTipFactor z / 2) (g := fun u : ℂ => u ^ (1 / 2 : ℂ))
        (analyticOnNhd_cpow_const (1 / 2 : ℂ) _ (hΘ_slit w hw))
        (AnalyticAt.div (hfac_an w (mem_univ w)) analyticAt_const (by norm_num : (2 : ℂ) ≠ 0))
    have h2 : AnalyticAt ℂ (fun z => arcEven (sinhTipDefect z / 2)) w :=
      AnalyticAt.comp (f := fun z => sinhTipDefect z / 2) (g := arcEven)
        (analyticOnNhd_arcEven _ (hΘ_def_ball w hw))
        (AnalyticAt.div (hdef_an w (mem_univ w)) analyticAt_const (by norm_num : (2 : ℂ) ≠ 0))
    exact (analyticAt_const.mul h1).mul h2
  have hΘ_0 : Θ 0 = ((4 / π * √(π * √2 / 2) : ℝ) : ℂ) := by
    have hpow_half : ((π * √2 / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√(π * √2 / 2) : ℝ) : ℂ) := by
      have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      rw [hhalf, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]
    have hdiv2 : ((π * √2 : ℝ) : ℂ) / 2 = ((π * √2 / 2 : ℝ) : ℂ) := by push_cast; rfl
    dsimp [Θ]
    rw [sinhTipFactor_zero, sinhTipDefect_zero, zero_div, arcEven_zero, mul_one,
      hdiv2, hpow_half]
    push_cast
    rfl
  have hΘ_0_ne : Θ 0 ≠ 0 := by
    rw [hΘ_0, Complex.ofReal_ne_zero]
    positivity
  have hΘ_real : ∀ x : ℝ, |x| < r_A → (Θ (x : ℂ)).im = 0 := fun x hx => by
    have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) r_A := by
      simpa [Metric.mem_ball, dist_zero_right] using hx
    have h_pos : 0 < (sinhTipFactor (x : ℂ) / 2).re :=
      hb₁ (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hx_ball)
    have h_im : (sinhTipFactor (x : ℂ) / 2).im = 0 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im,
        sinhTipFactor_ofReal_im, zero_div]
    have h_fac_eq : sinhTipFactor (x : ℂ) / 2 = (((sinhTipFactor (x : ℂ) / 2).re : ℝ) : ℂ) :=
      Complex.ext rfl h_im
    have h_cpow_im : ((sinhTipFactor (x : ℂ) / 2) ^ (1 / 2 : ℂ)).im = 0 := by
      rw [h_fac_eq, show (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow h_pos.le, Complex.ofReal_im]
    have h_def_norm : |((1 - Real.sinh (π * (xiStar + x))) / 2 : ℝ)| < 1 := by
      have hb := hΘ_def_ball (x : ℂ) hx_ball
      rw [sinhTipDefect_ofReal, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_div, Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs] at hb
      exact hb
    have h_arc_im : (arcEven (sinhTipDefect (x : ℂ) / 2)).im = 0 := by
      rw [sinhTipDefect_ofReal, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_div]
      exact arcEven_ofReal_im h_def_norm
    have h1 : (((sinhTipFactor (x : ℂ) / 2) ^ (1 / 2 : ℂ)) *
        arcEven (sinhTipDefect (x : ℂ) / 2)).im = 0 := by
      rw [Complex.mul_im, h_cpow_im, h_arc_im]
      ring
    have h2 : (((sinhTipFactor (x : ℂ) / 2) ^ (1 / 2 : ℂ)) *
        arcEven (sinhTipDefect (x : ℂ) / 2)) =
        ((((((sinhTipFactor (x : ℂ) / 2) ^ (1 / 2 : ℂ)) *
          arcEven (sinhTipDefect (x : ℂ) / 2)).re : ℝ) : ℂ)) :=
      Complex.ext rfl h1
    dsimp [Θ]
    rw [mul_assoc, h2, ← Complex.ofReal_mul, Complex.ofReal_im]
  let Ω : Set ℂ := {w : ℂ | w ∈ ball (0 : ℂ) r_A ∧ ¬(w.im = 0 ∧ 0 ≤ w.re)}
  have hΩ_open : IsOpen Ω := by
    have heq : Ω = ball (0 : ℂ) r_A ∩ (- ·) ⁻¹' slitPlane := by
      ext w
      simp [Ω, neg_mem_slitPlane_iff]
    rw [heq]
    exact isOpen_ball.inter (Complex.isOpen_slitPlane.preimage continuous_neg)
  have hΩ_conn : IsPreconnected Ω := cutBall_preconnected r_A
  have hΩ_sub_slit : ∀ w ∈ Ω, (xiStar : ℂ) + w ∈ slitStrip := fun w hw =>
    tip_add_mem_slitStrip (ball_subset_ball (min_le_right _ _) hw.1) hw.2
  have h_half_eq : ∀ w ∈ Ω, (-w) ^ (1 / 2 : ℂ) * Θ w = 1 - 2 * Complex.I * pMap ((xiStar : ℂ) + w) := by
    let lhs : ℂ → ℂ := fun w => (-w) ^ (1 / 2 : ℂ) * Θ w
    let rhs : ℂ → ℂ := fun w => 1 - 2 * Complex.I * pMap ((xiStar : ℂ) + w)
    have hlhs_an : AnalyticOnNhd ℂ lhs Ω := fun w hw => by
      have hnw : (-w) ∈ slitPlane := (neg_mem_slitPlane_iff w).mpr hw.2
      have hc : AnalyticAt ℂ (fun z : ℂ => (-z) ^ (1 / 2 : ℂ)) w :=
        (analyticOnNhd_cpow_const (1 / 2 : ℂ) _ hnw).comp analyticAt_id.neg
      exact hc.mul (hΘ_an w hw.1)
    have hrhs_an : AnalyticOnNhd ℂ rhs Ω := by
      intro w hw
      have hp_an : AnalyticOnNhd ℂ pMap slitStrip :=
        differentiableOn_pMap_slitStrip.analyticOnNhd isOpen_slitStrip
      have hadd : AnalyticAt ℂ (fun z : ℂ => (xiStar : ℂ) + z) w :=
        analyticAt_const.add analyticAt_id
      exact analyticAt_const.sub (analyticAt_const.mul ((hp_an _ (hΩ_sub_slit w hw)).comp hadd))
    let w₀ : ℂ := ((-(r_A / 2) : ℝ) : ℂ)
    have hw₀_mem : w₀ ∈ Ω := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_neg (by linarith)]
        linarith
      · rintro ⟨_, hre⟩
        have h1 : w₀.re = -(r_A / 2) := Complex.ofReal_re _
        linarith
    have hfreq : ∃ᶠ w in 𝓝[≠] w₀, lhs w = rhs w := by
      rw [Filter.frequently_iff]
      intro U hU
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
      obtain ⟨V, hV, hVU⟩ := hU
      obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp hV
      let d : ℝ := min (δ / 2) (r_A / 4)
      have hd_pos : 0 < d := lt_min (by positivity) (by positivity)
      let x : ℝ := -(r_A / 2) + d
      let w : ℂ := (x : ℂ)
      have hw_ne : w ≠ w₀ := fun he => by
        have := congrArg Complex.re he
        simp [w, w₀, x] at this
        linarith
      have hw_ball : w ∈ ball w₀ δ := by
        rw [Metric.mem_ball, dist_eq_norm, show w - w₀ = (d : ℂ) by simp [w, w₀, x],
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd_pos]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      refine ⟨w, hVU ⟨hball hw_ball, hw_ne⟩, ?_⟩
      have hx_neg : x < 0 := by dsimp [x, d]; linarith [min_le_right (δ / 2) (r_A / 4)]
      have hx_gt : -r_A < x := by dsimp [x]; linarith [hd_pos]
      have hx_ball : w ∈ ball (0 : ℂ) r_A := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_neg hx_neg]
        linarith
      have h_xi_add_x : xiStar + x ∈ Ioo 0 xiStar := by
        have : r_A ≤ xiStar / 2 := (min_le_right _ _).trans (min_le_left _ _)
        refine ⟨by linarith, by linarith⟩
      have h_fac_pos : 0 < (sinhTipFactor w / 2).re :=
        hb₁ (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hx_ball)
      have h_fac_im : (sinhTipFactor w / 2).im = 0 := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_im]
        dsimp [w]
        rw [sinhTipFactor_ofReal_im, zero_div]
      have h_fac_eq : sinhTipFactor w / 2 = (((sinhTipFactor w / 2).re : ℝ) : ℂ) :=
        Complex.ext rfl h_fac_im
      have h_def_eq : sinhTipDefect w / 2 = (((-x * (sinhTipFactor w / 2).re : ℝ) : ℂ)) := by
        rw [sinhTipDefect_eq w, mul_div_assoc, h_fac_eq]
        simp [w]
      have h_sinh_eq : (-x) * (sinhTipFactor w / 2).re =
          (1 - Real.sinh (π * (xiStar + x))) / 2 := by
        have hre := congrArg Complex.re h_def_eq
        dsimp only [w] at hre
        have h_def_re : (sinhTipDefect (x : ℂ) / 2).re =
            (1 - Real.sinh (π * (xiStar + x))) / 2 := by
          rw [sinhTipDefect_ofReal, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
            ← Complex.ofReal_div, Complex.ofReal_re]
        rw [h_def_re, Complex.ofReal_re] at hre
        exact hre.symm
      have h_sinh_lt1 : Real.sinh (π * (xiStar + x)) < 1 := by
        rw [← sinh_pi_mul_xiStar]
        exact Real.sinh_strictMono (mul_lt_mul_of_pos_left h_xi_add_x.2 Real.pi_pos)
      have h_sinh_pos : 0 < Real.sinh (π * (xiStar + x)) :=
        Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos h_xi_add_x.1)
      let u : ℝ := √((1 - Real.sinh (π * (xiStar + x))) / 2)
      have hu_pos : 0 < u := Real.sqrt_pos.mpr (by linarith)
      have hu_lt1 : u < 1 := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
      have hu_sq : u ^ 2 = (-x) * (sinhTipFactor w / 2).re := by
        rw [Real.sq_sqrt (by linarith), h_sinh_eq]
      have hu_prod : √(-x) * √((sinhTipFactor w / 2).re) = u := by
        rw [← Real.sqrt_mul (by linarith), h_sinh_eq]
      have hlhs_val : lhs w = ((4 / π * Real.arcsin u : ℝ) : ℂ) := by
        have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
        dsimp [lhs, Θ]
        rw [show -w = ((-x : ℝ) : ℂ) by simp [w], h_fac_eq, h_def_eq, ← hu_sq,
          arcEven_sq hu_pos hu_lt1, hhalf, ← Complex.ofReal_cpow (by linarith : 0 ≤ -x),
          ← Complex.ofReal_cpow h_fac_pos.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        norm_cast
        calc √(-x) * (4 / π * √((sinhTipFactor w / 2).re) * (Real.arcsin u / u))
            = (4 / π) * ((√(-x) * √((sinhTipFactor w / 2).re)) * (Real.arcsin u / u)) := by ring
          _ = (4 / π) * (u * (Real.arcsin u / u)) := by rw [hu_prod]
          _ = 4 / π * Real.arcsin u := by field_simp [hu_pos.ne']
      have hrhs_val : rhs w = ((4 / π * Real.arcsin u : ℝ) : ℂ) := by
        dsimp [rhs]
        rw [show (xiStar : ℂ) + w = ((xiStar + x : ℝ) : ℂ) by push_cast [w]; rfl]
        rw [pMap_ofReal (by rw [abs_of_pos h_xi_add_x.1]; exact h_xi_add_x.2.le)]
        have h_ident := four_thirds_inv_pi_arcsin_eq (Real.sinh (π * (xiStar + x)))
          (by linarith) (by linarith)
        calc 1 - 2 * Complex.I * (((-arcsinSinh (xiStar + x) / π : ℝ) : ℂ) * Complex.I)
            = 1 - 2 * ((-arcsinSinh (xiStar + x) / π : ℝ) : ℂ) * (Complex.I * Complex.I) := by ring
          _ = ((1 - (2 / π) * arcsinSinh (xiStar + x) : ℝ) : ℂ) := by
                rw [Complex.I_mul_I]; push_cast; ring
          _ = ((4 / π * Real.arcsin u : ℝ) : ℂ) := by
                unfold arcsinSinh; exact congrArg Complex.ofReal h_ident
      exact hlhs_val.trans hrhs_val.symm
    exact fun w hw => AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      hlhs_an hrhs_an hΩ_conn hw₀_mem hfreq hw
  let Θ₀ : ℂ → ℂ := fun w => Θ w / Θ 0
  have hΘ₀_an : AnalyticOnNhd ℂ Θ₀ (ball (0 : ℂ) r_A) := fun w hw =>
    AnalyticAt.div (hΘ_an w hw) analyticAt_const hΘ_0_ne
  have hΘ₀_0 : Θ₀ 0 = 1 := div_self hΘ_0_ne
  let A : ℂ → ℂ := fun w =>
    ((3 / 2 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)
  have h_mem_tb : ∀ {t : ℝ}, 0 ≤ t → t ≤ 1 → ∀ {w : ℂ}, w ∈ ball (0 : ℂ) r_A →
      (t : ℂ) * w ∈ ball (0 : ℂ) r_A := fun ht0 ht1 w hw => by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0]
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg w) ht1) hw
  have hA_hasDeriv : ∀ w₀ ∈ ball (0 : ℂ) r_A,
      HasDerivAt A
        (((3 / 2 : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
          ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * deriv Θ₀ ((t : ℂ) * w₀)) w₀ := by
    intro w₀ hw₀
    rw [Metric.mem_ball, dist_zero_right] at hw₀
    let δ : ℝ := (r_A - ‖w₀‖) / 2
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    have hcb_sub : closedBall w₀ δ ⊆ ball (0 : ℂ) r_A := fun w hw => by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      rw [Metric.mem_ball, dist_zero_right]
      have htr := norm_add_le (w - w₀) w₀
      have heq : w = (w - w₀) + w₀ := by ring
      rw [← heq] at htr
      dsimp [δ] at hw
      linarith
    let F : ℂ → ℝ → ℂ := fun w t => ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)
    let F' : ℂ → ℝ → ℂ := fun w t => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * deriv Θ₀ ((t : ℂ) * w)
    have hcont_mul : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) :=
      (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
    have hm_set : MapsTo (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2)
        (Icc (0 : ℝ) 1 ×ˢ closedBall w₀ δ) (ball 0 r_A) := fun p hp =>
      h_mem_tb hp.1.1 hp.1.2 (hcb_sub hp.2)
    have hF'_cont : ContinuousOn (fun p : ℝ × ℂ => F' p.2 p.1)
        (Icc (0 : ℝ) 1 ×ˢ closedBall w₀ δ) := by
      have hpow : Continuous (fun p : ℝ × ℂ => ((p.1 ^ (3 / 2 : ℝ) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_fst.rpow_const fun _ => Or.inr (by norm_num))
      exact hpow.continuousOn.mul (hΘ₀_an.deriv.continuousOn.comp hcont_mul.continuousOn hm_set)
    have hK_compact : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall w₀ δ) :=
      isCompact_Icc.prod (isCompact_closedBall w₀ δ)
    have hK_ne : (Icc (0 : ℝ) 1 ×ˢ closedBall w₀ δ).Nonempty :=
      ⟨(0, w₀), ⟨le_rfl, zero_le_one⟩, Metric.mem_closedBall_self hδ_pos.le⟩
    obtain ⟨p_max, _, hp_max⟩ := hK_compact.exists_isMaxOn hK_ne hF'_cont.norm
    let M_bd : ℝ := ‖F' p_max.2 p_max.1‖
    have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) (volume.restrict (Ι 0 1)) := by
      filter_upwards [Metric.ball_mem_nhds w₀ hδ_pos] with w hw
      have hw_ball : w ∈ ball (0 : ℂ) r_A := hcb_sub (Metric.ball_subset_closedBall hw)
      have hm : ContinuousOn (F w) (Icc 0 1) := by
        have hpow : Continuous fun t : ℝ => ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (continuous_id.rpow_const fun _ => Or.inr (by norm_num))
        exact hpow.continuousOn.mul
          (hΘ₀_an.continuousOn.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
            fun t ht => h_mem_tb ht.1 ht.2 hw_ball)
      rw [Set.uIoc_of_le zero_le_one]
      exact (hm.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    have hF_int : IntervalIntegrable (F w₀) volume 0 1 := by
      have hw_ball : w₀ ∈ ball (0 : ℂ) r_A := by simpa [Metric.mem_ball, dist_zero_right] using hw₀
      have hm : ContinuousOn (F w₀) (Icc 0 1) := by
        have hpow : Continuous fun t : ℝ => ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (continuous_id.rpow_const fun _ => Or.inr (by norm_num))
        exact hpow.continuousOn.mul
          (hΘ₀_an.continuousOn.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
            fun t ht => h_mem_tb ht.1 ht.2 hw_ball)
      exact hm.intervalIntegrable_of_Icc zero_le_one
    have hF'_meas : AEStronglyMeasurable (F' w₀) (volume.restrict (Ι 0 1)) := by
      have hw_ball : w₀ ∈ ball (0 : ℂ) r_A := by simpa [Metric.mem_ball, dist_zero_right] using hw₀
      have hm : ContinuousOn (F' w₀) (Icc 0 1) := by
        have hpow : Continuous fun t : ℝ => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (continuous_id.rpow_const fun _ => Or.inr (by norm_num))
        exact hpow.continuousOn.mul
          (hΘ₀_an.deriv.continuousOn.comp
            (Complex.continuous_ofReal.mul continuous_const).continuousOn
            fun t ht => h_mem_tb ht.1 ht.2 hw_ball)
      rw [Set.uIoc_of_le zero_le_one]
      exact (hm.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    have h_bound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ Metric.ball w₀ δ, ‖F' w t‖ ≤ M_bd :=
      Eventually.of_forall fun t ht w hw => by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact @hp_max (t, w) ⟨Ioc_subset_Icc_self ht, Metric.ball_subset_closedBall hw⟩
    have h_diff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ w ∈ Metric.ball w₀ δ,
        HasDerivAt (fun z => F z t) (F' w t) w :=
      Eventually.of_forall fun t ht w hw => by
        rw [Set.uIoc_of_le zero_le_one] at ht
        have hmem_tw : (t : ℂ) * w ∈ ball (0 : ℂ) r_A :=
          h_mem_tb ht.1.le ht.2 (hcb_sub (Metric.ball_subset_closedBall hw))
        have hd_lin : HasDerivAt (fun z : ℂ => (t : ℂ) * z) (t : ℂ) w := by
          simpa using (hasDerivAt_id w).const_mul (t : ℂ)
        have hd_Θ : HasDerivAt (fun z : ℂ => Θ₀ ((t : ℂ) * z))
            (deriv Θ₀ ((t : ℂ) * w) * (t : ℂ)) w :=
          (hΘ₀_an.differentiableOn _ hmem_tw).differentiableAt
            (isOpen_ball.mem_nhds hmem_tw) |>.hasDerivAt.comp w hd_lin
        have hd_mul := hd_Θ.const_mul ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ)
        refine hd_mul.congr_deriv ?_
        dsimp [F']
        have htpow : t ^ (1 / 2 : ℝ) * t = t ^ (3 / 2 : ℝ) := by
          conv_lhs => rhs; rw [← Real.rpow_one t]
          rw [← Real.rpow_add ht.1, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
        rw [show ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (deriv Θ₀ ((t : ℂ) * w) * (t : ℂ)) =
            (((t ^ (1 / 2 : ℝ) * t : ℝ) : ℂ)) * deriv Θ₀ ((t : ℂ) * w) by push_cast; ring,
          htpow]
    have hderiv := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds w₀ hδ_pos) hF_meas hF_int hF'_meas h_bound intervalIntegrable_const
      h_diff).2
    exact hderiv.const_mul ((3 / 2 : ℝ) : ℂ)
  have hA_an : AnalyticOnNhd ℂ A (ball (0 : ℂ) r_A) :=
    DifferentiableOn.analyticOnNhd
      (fun w hw => (hA_hasDeriv w hw).differentiableAt.differentiableWithinAt) isOpen_ball
  have hA_0 : A 0 = 1 := by
    dsimp [A]
    simp only [mul_zero, hΘ₀_0, mul_one, intervalIntegral.integral_ofReal]
    have hftc : ∫ t in (0 : ℝ)..1, t ^ (1 / 2 : ℝ) = 2 / 3 := by
      have hcont : ContinuousOn (fun t : ℝ => (2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) (Icc 0 1) :=
        (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (by norm_num))).continuousOn
      have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
          HasDerivAt (fun t : ℝ => (2 / 3 : ℝ) * t ^ (3 / 2 : ℝ)) (t ^ (1 / 2 : ℝ)) t := fun t ht => by
        have hd := (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ)) (Or.inl ht.1.ne')).const_mul (2 / 3 : ℝ)
        refine hd.congr_deriv ?_
        norm_num
        ring
      have hint : IntervalIntegrable (fun t : ℝ => t ^ (1 / 2 : ℝ)) volume 0 1 :=
        (continuous_id.rpow_const fun _ => Or.inr (by norm_num)).intervalIntegrable 0 1
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
      norm_num at h
      exact h
    rw [hftc]
    norm_cast
    norm_num
  have hA_real : ∀ x : ℝ, |x| < r_A → (A (x : ℂ)).im = 0 := fun x hx => by
    dsimp [A]
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
        ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * (x : ℂ)) =
          (((t ^ (1 / 2 : ℝ) * (Θ₀ ((t : ℂ) * (x : ℂ))).re : ℝ)) : ℂ) := fun t ht => by
      rw [Set.uIcc_of_le zero_le_one] at ht
      have htx : |t * x| < r_A := by
        rw [abs_mul, abs_of_nonneg ht.1]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg x) ht.2) hx
      have him_Θ : (Θ ((t * x : ℝ) : ℂ)).im = 0 := hΘ_real (t * x) htx
      have him_Θ0 : (Θ 0).im = 0 := by rw [hΘ_0, Complex.ofReal_im]
      have hΘ_eq : Θ ((t * x : ℝ) : ℂ) = (((Θ ((t * x : ℝ) : ℂ)).re : ℝ) : ℂ) :=
        Complex.ext rfl him_Θ
      have hΘ0_eq : Θ 0 = (((Θ 0).re : ℝ) : ℂ) := Complex.ext rfl him_Θ0
      have him_Θ₀ : (Θ₀ ((t : ℂ) * (x : ℂ))).im = 0 := by
        rw [show (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) by push_cast; rfl]
        dsimp [Θ₀]
        rw [hΘ_eq, hΘ0_eq, ← Complex.ofReal_div, Complex.ofReal_im]
      have heq : Θ₀ ((t : ℂ) * (x : ℂ)) = (((Θ₀ ((t : ℂ) * (x : ℂ))).re : ℝ) : ℂ) :=
        Complex.ext rfl him_Θ₀
      conv_lhs => rhs; rw [heq]
      push_cast; rfl
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_ofReal, ← Complex.ofReal_mul,
      Complex.ofReal_im]
  have hA_ode : ∀ w ∈ ball (0 : ℂ) r_A,
      ((3 / 2 : ℝ) : ℂ) * A w + w * deriv A w = ((3 / 2 : ℝ) : ℂ) * Θ₀ w := by
    intro w hw
    have hderivA := (hA_hasDeriv w hw).deriv
    rw [hderivA]
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1,
        w * (((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * deriv Θ₀ ((t : ℂ) * w)) +
          ((3 / 2 : ℝ) : ℂ) * (((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)) =
          ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (w * deriv Θ₀ ((t : ℂ) * w)) +
          ((3 / 2 * t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w) := fun t _ => by
      push_cast; ring
    let G : ℝ → ℂ := fun t => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)
    have hG_cont : ContinuousOn G (Icc 0 1) := by
      have hpow : Continuous fun t : ℝ => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_id.rpow_const fun _ => Or.inr (by norm_num))
      exact hpow.continuousOn.mul
        (hΘ₀_an.continuousOn.comp (Complex.continuous_ofReal.mul continuous_const).continuousOn
          fun t ht => h_mem_tb ht.1 ht.2 hw)
    have hG_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt G
          (((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (w * deriv Θ₀ ((t : ℂ) * w)) +
            ((3 / 2 * t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)) t := fun t ht => by
      have hd1_r := (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ)) (Or.inl ht.1.ne')).ofReal_comp
      have hd1 : HasDerivAt (fun t : ℝ => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ))
          ((3 / 2 * t ^ (1 / 2 : ℝ) : ℝ) : ℂ) t := by
        refine hd1_r.congr_deriv ?_
        norm_num
      have htw : (t : ℂ) * w ∈ ball (0 : ℂ) r_A := h_mem_tb ht.1.le ht.2.le hw
      have hd_lin : HasDerivAt (fun s : ℝ => (s : ℂ) * w) w t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
      have hd2 : HasDerivAt (fun s : ℝ => Θ₀ ((s : ℂ) * w)) (deriv Θ₀ ((t : ℂ) * w) * w) t := by
        have h := ((hΘ₀_an.differentiableOn _ htw).differentiableAt (isOpen_ball.mem_nhds htw)).hasDerivAt.scomp
          t hd_lin
        refine h.congr_deriv ?_
        rw [smul_eq_mul, mul_comm]
      refine (hd1.mul hd2).congr_deriv ?_
      ring
    have hint1 : IntervalIntegrable
        (fun t : ℝ => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * deriv Θ₀ ((t : ℂ) * w)) volume 0 1 := by
      have hm : ContinuousOn
          (fun t : ℝ => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * deriv Θ₀ ((t : ℂ) * w)) (Icc 0 1) := by
        have hpow : Continuous fun t : ℝ => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (continuous_id.rpow_const fun _ => Or.inr (by norm_num))
        exact hpow.continuousOn.mul
          (hΘ₀_an.deriv.continuousOn.comp
            (Complex.continuous_ofReal.mul continuous_const).continuousOn
            fun t ht => h_mem_tb ht.1 ht.2 hw)
      exact hm.intervalIntegrable_of_Icc zero_le_one
    have hint2 : IntervalIntegrable
        (fun t : ℝ => ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)) volume 0 1 := by
      have hm : ContinuousOn
          (fun t : ℝ => ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)) (Icc 0 1) := by
        have hpow : Continuous fun t : ℝ => ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (continuous_id.rpow_const fun _ => Or.inr (by norm_num))
        exact hpow.continuousOn.mul
          (hΘ₀_an.continuousOn.comp
            (Complex.continuous_ofReal.mul continuous_const).continuousOn
            fun t ht => h_mem_tb ht.1 ht.2 hw)
      exact hm.intervalIntegrable_of_Icc zero_le_one
    have hint : IntervalIntegrable (fun t : ℝ =>
        ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (w * deriv Θ₀ ((t : ℂ) * w)) +
          ((3 / 2 * t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)) volume 0 1 := by
      have hm1 : ContinuousOn
          (fun t : ℝ => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * (w * deriv Θ₀ ((t : ℂ) * w))) (Icc 0 1) := by
        have hpow : Continuous fun t : ℝ => ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (continuous_id.rpow_const fun _ => Or.inr (by norm_num))
        exact hpow.continuousOn.mul (continuousOn_const.mul
          (hΘ₀_an.deriv.continuousOn.comp
            (Complex.continuous_ofReal.mul continuous_const).continuousOn
            fun t ht => h_mem_tb ht.1 ht.2 hw))
      have hm2 : ContinuousOn
          (fun t : ℝ => ((3 / 2 * t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)) (Icc 0 1) := by
        have hpow : Continuous fun t : ℝ => ((3 / 2 * t ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp
            (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (by norm_num)))
        exact hpow.continuousOn.mul
          (hΘ₀_an.continuousOn.comp
            (Complex.continuous_ofReal.mul continuous_const).continuousOn
            fun t ht => h_mem_tb ht.1 ht.2 hw)
      exact (hm1.add hm2).intervalIntegrable_of_Icc zero_le_one
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hG_cont hG_deriv hint
    have hG1 : G 1 = Θ₀ w := by simp [G]
    have hG0 : G 0 = 0 := by simp [G]
    rw [hG1, hG0, sub_zero] at hftc
    have heq_int :
        w * (∫ t in (0 : ℝ)..1, ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) * deriv Θ₀ ((t : ℂ) * w)) +
          ((3 / 2 : ℝ) : ℂ) * (∫ t in (0 : ℝ)..1, ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Θ₀ ((t : ℂ) * w)) =
        Θ₀ w := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_add (hint1.const_mul w) (hint2.const_mul _)]
      rw [intervalIntegral.integral_congr hcongr]
      exact hftc
    dsimp [A]
    linear_combination ((3 / 2 : ℝ) : ℂ) * heq_int
  let Φ : ℂ → ℂ := fun w => -((KTip : ℂ) * (-w) ^ (3 / 2 : ℂ) * A w)
  let Ψ : ℂ → ℂ := fun w => tipPotentialHolo ((xiStar : ℂ) + w)
  have hΦ_deriv : ∀ w ∈ Ω,
      HasDerivAt Φ (((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((xiStar : ℂ) + w))) w := by
    intro w hw
    have hnw : (-w) ∈ slitPlane := (neg_mem_slitPlane_iff w).mpr hw.2
    have hnw_ne : (-w) ≠ 0 := Complex.slitPlane_ne_zero hnw
    have hd1 : HasDerivAt (fun z : ℂ => (-z) ^ (3 / 2 : ℂ))
        ((3 / 2 : ℂ) * (-w) ^ (1 / 2 : ℂ) * (-1)) w := by
      have hc := ((hasDerivAt_id w).neg).cpow_const (c := (3 / 2 : ℂ)) hnw
      refine hc.congr_deriv ?_
      norm_num
    have hd2 : HasDerivAt A (deriv A w) w :=
      (hA_hasDeriv w hw.1).congr_deriv (hA_hasDeriv w hw.1).deriv.symm
    have hd := ((hd1.const_mul (KTip : ℂ)).mul hd2).neg
    have hcpow_split : (-w) ^ (3 / 2 : ℂ) = (-w) ^ (1 / 2 : ℂ) * (-w) := by
      conv_rhs => rhs; rw [← Complex.cpow_one (-w)]
      rw [← Complex.cpow_add _ _ hnw_ne, show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
    have hode := hA_ode w hw.1
    have hpref : ((3 / 2 : ℝ) : ℂ) * (KTip : ℂ) = ((2 * π / 3 : ℝ) : ℂ) * Θ 0 := by
      rw [hΘ_0]
      exact_mod_cast tip_prefactor_identity
    refine hd.congr_deriv ?_
    calc -((KTip : ℂ) * ((3 / 2 : ℂ) * (-w) ^ (1 / 2 : ℂ) * -1) * A w +
            (KTip : ℂ) * (-w) ^ (3 / 2 : ℂ) * deriv A w)
        = (KTip : ℂ) * (-w) ^ (1 / 2 : ℂ) * (((3 / 2 : ℝ) : ℂ) * A w + w * deriv A w) := by
            rw [hcpow_split]; norm_num; ring
      _ = (KTip : ℂ) * (-w) ^ (1 / 2 : ℂ) * (((3 / 2 : ℝ) : ℂ) * Θ₀ w) := by rw [hode]
      _ = (((3 / 2 : ℝ) : ℂ) * (KTip : ℂ)) * ((-w) ^ (1 / 2 : ℂ) * (Θ w / Θ 0)) := by
            dsimp [Θ₀]; ring
      _ = ((2 * π / 3 : ℝ) : ℂ) * Θ 0 * ((-w) ^ (1 / 2 : ℂ) * (Θ w / Θ 0)) := by rw [hpref]
      _ = ((2 * π / 3 : ℝ) : ℂ) * ((-w) ^ (1 / 2 : ℂ) * Θ w) := by
            field_simp [hΘ_0_ne]
      _ = ((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((xiStar : ℂ) + w)) := by
            rw [h_half_eq w hw]
  have hΨ_deriv : ∀ w ∈ Ω,
      HasDerivAt Ψ (((2 * π / 3 : ℝ) : ℂ) * (1 - 2 * Complex.I * pMap ((xiStar : ℂ) + w))) w := by
    intro w hw
    have hadd : HasDerivAt (fun z : ℂ => (xiStar : ℂ) + z) 1 w := by
      simpa using (hasDerivAt_id w).const_add (xiStar : ℂ)
    exact ((hasDerivAt_tipPotentialHolo (hΩ_sub_slit w hw)).comp w hadd).congr_deriv (by ring)
  have hdiff_deriv : ∀ w ∈ Ω, HasDerivAt (fun z => Ψ z - Φ z) 0 w := fun w hw =>
    ((hΨ_deriv w hw).sub (hΦ_deriv w hw)).congr_deriv (sub_self _)
  let seq : ℕ → ℂ := fun n => ((-(r_A / (n + 2 : ℝ)) : ℝ) : ℂ)
  have hseq_mem : ∀ n : ℕ, seq n ∈ Ω := fun n => by
    refine ⟨?_, ?_⟩
    · have hneg : -(r_A / (n + 2 : ℝ)) < 0 := neg_lt_zero.mpr (div_pos hr_A_pos (by positivity))
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg,
        neg_neg]
      have hn : (1 : ℝ) < (n + 2 : ℝ) := by exact_mod_cast (by omega : 1 < n + 2)
      exact div_lt_self hr_A_pos hn
    · rintro ⟨_, hre⟩
      have : (seq n).re = -(r_A / (n + 2 : ℝ)) := Complex.ofReal_re _
      linarith [show (0 : ℝ) < r_A / (n + 2 : ℝ) by positivity]
  have hconst : ∀ w ∈ Ω, Ψ w - Φ w = Ψ (seq 0) - Φ (seq 0) := by
    have hdiff_an : AnalyticOnNhd ℂ (fun z => Ψ z - Φ z) Ω :=
      DifferentiableOn.analyticOnNhd
        (fun w hw => (hdiff_deriv w hw).differentiableAt.differentiableWithinAt) hΩ_open
    obtain ⟨δ, hδ_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open (seq 0) (hseq_mem 0)
    have hev_eq : (fun z => Ψ z - Φ z) =ᶠ[𝓝 (seq 0)] (fun _ => Ψ (seq 0) - Φ (seq 0)) := by
      filter_upwards [Metric.ball_mem_nhds (seq 0) hδ_pos] with z hz
      refine (convex_ball (seq 0) δ).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
        (fun w hw => (hdiff_deriv w (hball_sub hw)).differentiableAt.differentiableWithinAt)
        (fun w hw => ?_) hz (mem_ball_self hδ_pos)
      rw [(hdiff_deriv w (hball_sub hw)).differentiableAt.fderivWithin
          (isOpen_ball.uniqueDiffWithinAt hw),
        (hdiff_deriv w (hball_sub hw)).hasFDerivAt.fderiv]
      ext; simp
    exact fun w hw => AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hdiff_an analyticOnNhd_const hΩ_conn (hseq_mem 0) hev_eq hw
  have hlim_zero : Tendsto seq atTop (𝓝 (0 : ℂ)) := by
    have hre : Tendsto (fun n : ℕ => -(r_A / (n + 2 : ℝ))) atTop (𝓝 0) := by
      have h := tendsto_const_nhds (x := r_A) |>.div_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ) |>.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
      simpa using h.neg
    have hcomp : Tendsto (Complex.ofReal ∘ fun n : ℕ => -(r_A / (n + 2 : ℝ))) atTop (𝓝 0) := by
      simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hre
    exact hcomp
  have hlim_Φ : Tendsto (fun n => (Φ (seq n)).re) atTop (𝓝 0) := by
    have hcont_re : ContinuousAt (fun z : ℂ => (Φ z).re) 0 := by
      refine Complex.continuous_re.continuousAt.comp ?_
      have h1 : ContinuousAt (fun z : ℂ => (-z) ^ (3 / 2 : ℂ)) 0 :=
        (Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp))
          (by norm_num : (0 : ℝ) < (3 / 2 : ℂ).re)).comp continuous_neg.continuousAt
      exact ((continuousAt_const.mul h1).mul ((hA_an 0 (mem_ball_self hr_A_pos)).continuousAt)).neg
    have h0 : (Φ 0).re = 0 := by
      dsimp [Φ]
      rw [neg_zero, Complex.zero_cpow (by norm_num)]
      simp
    have hcomp : Tendsto ((fun z : ℂ => (Φ z).re) ∘ seq) atTop (𝓝 0) := by
      simpa [h0] using hcont_re.tendsto.comp hlim_zero
    exact hcomp
  have hlim_Ψ : Tendsto (fun n => (Ψ (seq n)).re) atTop (𝓝 0) := by
    have h_eq' : ∀ n : ℕ, (Ψ (seq n)).re =
        slitL (xiStar - r_A / (n + 2 : ℝ)) + majorantReal (xiStar - r_A / (n + 2 : ℝ)) := by
      intro n
      dsimp [Ψ]
      rw [tipPotentialHolo_re]
      have hx_eq : (xiStar : ℂ) + seq n = ((xiStar - r_A / (n + 2 : ℝ) : ℝ) : ℂ) := by
        push_cast [seq]; ring
      have hx_mem : xiStar - r_A / (n + 2 : ℝ) ∈ Icc 0 xiStar := by
        have hlt1 : r_A ≤ xiStar / 2 := (min_le_right _ _).trans (min_le_left _ _)
        have hlt2 : r_A / (n + 2 : ℝ) ≤ r_A / 2 := by gcongr; exact_mod_cast (by omega : 2 ≤ n + 2)
        refine ⟨by linarith [xiStar_pos], by linarith [show (0 : ℝ) < r_A / (n + 2 : ℝ) by positivity]⟩
      have habs : |xiStar - r_A / (n + 2 : ℝ)| ≤ xiStar := by
        rw [abs_of_nonneg hx_mem.1]; exact hx_mem.2
      have hL : (tipL ((xiStar - r_A / (n + 2 : ℝ) : ℝ) : ℂ)).re =
          slitL (xiStar - r_A / (n + 2 : ℝ)) := by
        unfold tipL slitL
        rw [abs_of_nonneg hx_mem.1, ← Complex.ofReal_mul, Complex.ofReal_re]
        ring
      rw [hx_eq, majorant2D_ofReal habs, hL]
    simp_rw [h_eq']
    have h_ten : Tendsto (fun n : ℕ => xiStar - r_A / (n + 2 : ℝ)) atTop (𝓝 xiStar) := by
      have h := tendsto_const_nhds (x := r_A) |>.div_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ) |>.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))
      simpa using tendsto_const_nhds.sub h
    have hcont : ContinuousAt (fun x : ℝ =>
        2 * π * x / 3 + (majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..x, arcsinSinh s)) xiStar := by
      refine (by fun_prop : Continuous fun x : ℝ => 2 * π * x / 3).continuousAt.add ?_
      refine continuousAt_const.sub (continuousAt_const.mul ?_)
      exact (intervalIntegral.continuous_primitive (fun a b => intervalIntegrable_arcsinSinh a b) 0).continuousAt
    have h_ev : ∀ n : ℕ,
        slitL (xiStar - r_A / (n + 2 : ℝ)) + majorantReal (xiStar - r_A / (n + 2 : ℝ)) =
        2 * π * (xiStar - r_A / (n + 2 : ℝ)) / 3 +
          (majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..(xiStar - r_A / (n + 2 : ℝ)), arcsinSinh s) := by
      intro n
      have hx_mem : xiStar - r_A / (n + 2 : ℝ) ∈ Icc 0 xiStar := by
        have hlt1 : r_A ≤ xiStar / 2 := (min_le_right _ _).trans (min_le_left _ _)
        have hlt2 : r_A / (n + 2 : ℝ) ≤ r_A / 2 := by gcongr; exact_mod_cast (by omega : 2 ≤ n + 2)
        refine ⟨by linarith [xiStar_pos], by linarith [show (0 : ℝ) < r_A / (n + 2 : ℝ) by positivity]⟩
      have habs : |xiStar - r_A / (n + 2 : ℝ)| = xiStar - r_A / (n + 2 : ℝ) :=
        abs_of_nonneg hx_mem.1
      unfold slitL
      rw [majorantReal_of_abs_le (by rw [habs]; exact hx_mem.2), habs]
    simp_rw [h_ev]
    have hlim_val : 2 * π * xiStar / 3 + (majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..xiStar, arcsinSinh s) = 0 := by
      have hL : slitL xiStar = 2 * π * xiStar / 3 := by unfold slitL; rw [abs_of_pos xiStar_pos]
      have hM : majorantReal xiStar = majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..xiStar, arcsinSinh s := by
        rw [majorantReal_of_abs_le (by rw [abs_of_pos xiStar_pos]), abs_of_pos xiStar_pos]
      rw [← hL, ← hM, majorantReal_xiStar]
      ring
    have ht : Tendsto (fun n : ℕ =>
        2 * π * (xiStar - r_A / (n + 2 : ℝ)) / 3 +
          (majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..(xiStar - r_A / (n + 2 : ℝ)), arcsinSinh s))
        atTop (𝓝 (2 * π * xiStar / 3 +
          (majorantU0 - (4 / 3) * ∫ s in (0 : ℝ)..xiStar, arcsinSinh s))) :=
      hcont.tendsto.comp h_ten
    simpa [hlim_val] using ht
  refine ⟨{
    U := majorant2D
    A := A
    r_A := r_A
    hr_A_pos := hr_A_pos
    hA_an := hA_an
    hA_0 := hA_0
    hA_real := hA_real
    U_add_L_near_tip := fun b hb hcut => ?_
  }, rfl⟩
  let w : ℂ := b - (xiStar : ℂ)
  have hw_mem : w ∈ Ω := by
    refine ⟨?_, ?_⟩
    · simpa [w, Metric.mem_ball, dist_eq_norm] using hb
    · rintro ⟨him, hre⟩
      apply hcut
      refine ⟨?_, ?_⟩
      · simpa [w, Complex.sub_im, Complex.ofReal_im] using him
      · have : w.re = b.re - xiStar := by simp [w]
        linarith
  have hconst_w := congrArg Complex.re (hconst w hw_mem)
  have hre_0 : (Ψ (seq 0) - Φ (seq 0)).re = 0 := by
    have h_const_seq : ∀ n : ℕ, (Ψ (seq n) - Φ (seq n)).re = (Ψ (seq 0) - Φ (seq 0)).re :=
      fun n => congrArg Complex.re (hconst (seq n) (hseq_mem n))
    have hlim_diff : Tendsto (fun n => (Ψ (seq n) - Φ (seq n)).re) atTop (𝓝 (0 - 0)) := by
      simpa [Complex.sub_re] using hlim_Ψ.sub hlim_Φ
    have hlim_const : Tendsto (fun n => (Ψ (seq n) - Φ (seq n)).re) atTop
        (𝓝 (Ψ (seq 0) - Φ (seq 0)).re) := by
      simp [h_const_seq]
    simpa using tendsto_nhds_unique hlim_const hlim_diff
  rw [hre_0, Complex.sub_re, sub_eq_zero] at hconst_w
  have hb_eq : (xiStar : ℂ) + w = b := by dsimp [w]; ring
  have hw_neg : -w = (xiStar : ℂ) - b := by dsimp [w]; ring
  calc majorant2D b + (tipL b).re
      = (tipL b).re + majorant2D b := add_comm _ _
    _ = (Ψ w).re := by dsimp [Ψ]; rw [hb_eq, tipPotentialHolo_re]
    _ = (Φ w).re := hconst_w
    _ = (-KTip * ((xiStar : ℂ) - b) ^ (3 / 2 : ℂ) * A (b - (xiStar : ℂ))).re := by
          dsimp [Φ, w]
          rw [← Complex.neg_re, hw_neg]
          congr 1
          ring

/-- Canonical concrete `LemmaGPotentialInput` with `U = PoissonJensen.majorant2D`. -/
noncomputable def lemmaGPotentialInput_virasoro : LemmaGPotentialInput :=
  lemmaGPotentialInput_virasoro_exists.choose

@[simp] theorem lemmaGPotentialInput_virasoro_U :
    lemmaGPotentialInput_virasoro.U = majorant2D :=
  lemmaGPotentialInput_virasoro_exists.choose_spec

/--
info: 'FormalResearch.ModularBootstrap.TipFront.lemmaGPotentialInput_virasoro_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lemmaGPotentialInput_virasoro_exists

end FormalResearch.ModularBootstrap.TipFront
