module

public import Mathlib

/-!
# Analytic divided-difference and Cauchy-estimate toolkit for `FineOrderSigned`

Provides holomorphic divided differences `divQ h R c q = (2πi)⁻¹ ∮_{|ζ|=R} h(ζ)/((ζ-q)(ζ-c)) dζ`,
Cauchy derivative and Lipschitz bounds, real-symmetry preservation on real intervals, and
parametric holomorphicity under circle integrals. Used by `FineOrderSigned` (`fs:half-cubic`).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real Interval

namespace FormalResearch.SignUncertainty.FineOrderSigned

/-- Cauchy integral formula for derivatives: for `0 < R'' < R'`, `f` holomorphic on `ball 0 R'`,
and `‖z‖ < R''`, `deriv f z = (2πi)⁻¹ • ∮ ζ in C(0, R''), (ζ - z) ^ (-2 : ℤ) • f ζ`. -/
theorem cauchy_deriv_formula {f : ℂ → ℂ} {R'' R' : ℝ} {z : ℂ}
    (hR : 0 < R'') (hRR : R'' < R') (hf : DifferentiableOn ℂ f (ball 0 R')) (hz : ‖z‖ < R'') :
    deriv f z = (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R''), (ζ - z) ^ (-2 : ℤ) • f ζ := by
  have hfc : ContinuousOn f (sphere 0 R'') :=
    hf.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hRR))
  have hint : CircleIntegrable f 0 R'' := hfc.circleIntegrable hR.le
  have hzs : z ∉ sphere (0 : ℂ) |R''| := by
    rw [abs_of_pos hR]; simp only [mem_sphere_zero_iff_norm]; linarith
  have hT := (hasDerivAt_circleIntegral_sub_inv_smul hint hzs).const_smul ((2 * π * I : ℂ)⁻¹)
  have hev : (fun w => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R''), (ζ - w)⁻¹ • f ζ) =ᶠ[𝓝 z] f := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
    have hci := DifferentiableOn.circleIntegral_sub_inv_smul (hf.mono (closedBall_subset_ball hRR)) hw
    rw [hci, inv_smul_smul₀ (by simp [Real.pi_ne_zero])]
  exact (hT.congr_of_eventuallyEq hev.symm).deriv

/-- Cauchy derivative bound on concentric discs: if `f` is holomorphic on `ball 0 R'`,
`0 ≤ r < R'' < R'`, `‖z‖ ≤ r`, and `∀ ζ ∈ sphere 0 R'', ‖f ζ‖ ≤ M`, then
`‖deriv f z‖ ≤ R'' * M / (R'' - r) ^ 2`. -/
theorem cauchy_deriv_bound {f : ℂ → ℂ} {r R'' R' M : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hrR : r < R'') (hRR : R'' < R') (hf : DifferentiableOn ℂ f (ball 0 R'))
    (hz : ‖z‖ ≤ r) (hM : ∀ ζ ∈ sphere (0 : ℂ) R'', ‖f ζ‖ ≤ M) :
    ‖deriv f z‖ ≤ R'' * M / (R'' - r) ^ 2 := by
  have hR : 0 < R'' := hr.trans_lt hrR
  have hz' : ‖z‖ < R'' := hz.trans_lt hrR
  rw [cauchy_deriv_formula hR hRR hf hz']
  have hM0 : 0 ≤ M := (norm_nonneg (f (R'' : ℂ))).trans (hM R'' (by simp [abs_of_pos hR]))
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (C := M / (R'' - r) ^ 2) fun ζ hζ => ?_).trans_eq (by ring)
  have hζR : ‖ζ‖ = R'' := mem_sphere_zero_iff_norm.1 hζ
  have hdist : R'' - r ≤ ‖ζ - z‖ := by
    have := norm_sub_norm_le ζ z
    linarith only [this, hζR, hz]
  have hpos : 0 < R'' - r := sub_pos.2 hrR
  rw [norm_smul, norm_zpow, zpow_neg, zpow_two, div_eq_inv_mul]
  exact mul_le_mul (inv_anti₀ (sq_pos_of_pos hpos) (by nlinarith only [hdist, hpos]))
    (hM ζ hζ) (norm_nonneg _) (by positivity)

/-- Uniform Lipschitz bound on `closedBall 0 r` for a bounded holomorphic function on `ball 0 ρ`. -/
theorem holo_lipschitz_ball {f : ℂ → ℂ} {r ρ M : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ)
    (hf : DifferentiableOn ℂ f (ball 0 ρ)) (hM : ∀ z ∈ ball (0 : ℂ) ρ, ‖f z‖ ≤ M)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ closedBall (0 : ℂ) r) (hz₂ : z₂ ∈ closedBall (0 : ℂ) r) :
    ‖f z₁ - f z₂‖ ≤ ((r + ρ) / 2 * M / ((ρ - r) / 2) ^ 2) * ‖z₁ - z₂‖ := by
  set r' : ℝ := (r + ρ) / 2
  have hrr' : r < r' := by dsimp [r']; linarith
  have hr'ρ : r' < ρ := by dsimp [r']; linarith
  have hdiff : ∀ z ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ f z := fun z hz =>
    hf.differentiableAt (isOpen_ball.mem_nhds (closedBall_subset_ball hrρ hz))
  have hC : ∀ z ∈ closedBall (0 : ℂ) r, ‖deriv f z‖ ≤ r' * M / ((ρ - r) / 2) ^ 2 := by
    intro z hz
    have hbd := cauchy_deriv_bound hr hrr' hr'ρ hf (mem_closedBall_zero_iff.1 hz) fun ζ hζ =>
      hM ζ (mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ hr'ρ))
    refine hbd.trans_eq ?_
    have hr'eq : r' - r = (ρ - r) / 2 := by dsimp [r']; ring
    rw [hr'eq]
  have hconv : Convex ℝ (closedBall (0 : ℂ) r) := convex_closedBall 0 r
  exact hconv.norm_image_sub_le_of_norm_deriv_le hdiff hC hz₂ hz₁

/-- A holomorphic function that is real-valued on the real diameter has real derivative there. -/
theorem real_im_deriv {f : ℂ → ℂ} {ρ : ℝ} (hf : DifferentiableOn ℂ f (ball 0 ρ))
    (hreal : ∀ x : ℝ, |x| < ρ → (f x).im = 0) {x : ℝ} (hx : |x| < ρ) :
    (deriv f x).im = 0 := by
  have hx_mem : (x : ℂ) ∈ ball (0 : ℂ) ρ := by simpa [mem_ball_zero_iff] using hx
  have hd : HasDerivAt f (deriv f x) x := (hf.differentiableAt (isOpen_ball.mem_nhds hx_mem)).hasDerivAt
  have hdR : HasDerivAt (fun t : ℝ => f t) (deriv f x) x := hd.comp_ofReal
  have him : HasDerivAt (fun t : ℝ => (f t).im) (deriv f x).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hdR
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
  have hev : (fun t : ℝ => (f t).im) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds x (sub_pos.2 hx)] with t ht
    have htρ : |t| < ρ := by
      have : |t - x| < ρ - |x| := by simpa [Real.dist_eq] using ht
      linarith [abs_sub_abs_le_abs_sub t x]
    exact hreal t htρ
  exact him.unique (hzero.congr_of_eventuallyEq hev)

/-- Holomorphic divided difference `(h q - h c) / (q - c)` represented on `‖ζ‖ = R`. -/
noncomputable def divQ (h : ℂ → ℂ) (R : ℝ) (c q : ℂ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), h ζ / ((ζ - q) * (ζ - c))

/-- Exact divided-difference identity `h q - h c = (q - c) * divQ h R c q` for `c, q ∈ ball 0 R`. -/
theorem divQ_eq {h : ℂ → ℂ} {R ρ : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hh : DifferentiableOn ℂ h (ball 0 ρ)) {c q : ℂ} (hc : c ∈ ball (0 : ℂ) R) (hq : q ∈ ball (0 : ℂ) R) :
    h q - h c = (q - c) * divQ h R c q := by
  by_cases hqc : q = c
  · subst hqc; simp
  have hcl : DifferentiableOn ℂ h (closedBall 0 R) := hh.mono (closedBall_subset_ball hRρ)
  have hcont_h : ContinuousOn h (sphere 0 R) := hcl.continuousOn.mono sphere_subset_closedBall
  have hint_inv : ∀ w ∈ ball (0 : ℂ) R, CircleIntegrable (fun ζ => (ζ - w)⁻¹ • h ζ) 0 R := fun w hw => by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine ContinuousOn.smul ((continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => ?_) hcont_h
    have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
    have hwR : ‖w‖ < R := mem_ball_zero_iff.1 hw
    intro h0
    have : ζ = w := sub_eq_zero.1 h0
    rw [this] at hζR; linarith
  have hp : ∀ ζ ∈ sphere (0 : ℂ) R,
      (q - c) * (h ζ / ((ζ - q) * (ζ - c))) = (ζ - q)⁻¹ • h ζ - (ζ - c)⁻¹ • h ζ := by
    intro ζ hζ
    have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
    have hq_ne : ζ - q ≠ 0 := by
      intro h0; have : ‖ζ‖ = ‖q‖ := by rw [sub_eq_zero.1 h0]
      linarith [mem_ball_zero_iff.1 hq]
    have hc_ne : ζ - c ≠ 0 := by
      intro h0; have : ‖ζ‖ = ‖c‖ := by rw [sub_eq_zero.1 h0]
      linarith [mem_ball_zero_iff.1 hc]
    rw [smul_eq_mul, smul_eq_mul]
    field_simp [hq_ne, hc_ne]
    ring
  unfold divQ
  rw [mul_smul_comm, ← circleIntegral.integral_const_mul, circleIntegral.integral_congr hR.le hp,
    circleIntegral.integral_sub (hint_inv q hq) (hint_inv c hc)]
  have hCq := hcl.circleIntegral_sub_inv_smul hq
  have hCc := hcl.circleIntegral_sub_inv_smul hc
  rw [smul_sub, hCq, hCc, inv_smul_smul₀ (by simp [Real.pi_ne_zero]),
    inv_smul_smul₀ (by simp [Real.pi_ne_zero])]

/-- Uniform norm bound on `divQ h R c q` for `‖c‖, ‖q‖ ≤ r < R`. -/
theorem norm_divQ_le {h : ℂ → ℂ} {R r M : ℝ} (hR : 0 < R) (hrR : r < R)
    (hM : ∀ ζ ∈ sphere (0 : ℂ) R, ‖h ζ‖ ≤ M) {c q : ℂ} (hc : ‖c‖ ≤ r) (hq : ‖q‖ ≤ r) :
    ‖divQ h R c q‖ ≤ R * M / (R - r) ^ 2 := by
  have hpos : 0 < R - r := sub_pos.2 hrR
  have hM0 : 0 ≤ M := (norm_nonneg (h (R : ℂ))).trans (hM R (by simp [abs_of_pos hR]))
  unfold divQ
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (C := M / (R - r) ^ 2) fun ζ hζ => ?_).trans_eq (by ring)
  have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
  have hq_dist : R - r ≤ ‖ζ - q‖ := by linarith only [norm_sub_norm_le ζ q, hζR, hq]
  have hc_dist : R - r ≤ ‖ζ - c‖ := by linarith only [norm_sub_norm_le ζ c, hζR, hc]
  rw [norm_div, norm_mul]
  refine div_le_div₀ hM0 (hM ζ hζ) (sq_pos_of_pos hpos) ?_
  nlinarith only [hq_dist, hc_dist, hpos]

/-- `divQ h R c` is holomorphic on `ball 0 R` when `c ∈ ball 0 R`. -/
theorem differentiableOn_divQ_fst {h : ℂ → ℂ} {R ρ : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hh : DifferentiableOn ℂ h (ball 0 ρ)) {c : ℂ} (hc : c ∈ ball (0 : ℂ) R) :
    DifferentiableOn ℂ (divQ h R c) (ball 0 R) := by
  have hhc : ContinuousOn h (sphere 0 R) :=
    hh.continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hRρ))
  have hcR : ‖c‖ < R := mem_ball_zero_iff.1 hc
  intro q₀ hq₀
  have hq₀R : ‖q₀‖ < R := mem_ball_zero_iff.1 hq₀
  set r₀ : ℝ := max ‖q₀‖ ‖c‖ + (R - max ‖q₀‖ ‖c‖) / 2
  have hmr : max ‖q₀‖ ‖c‖ < R := max_lt hq₀R hcR
  have hr₀_gt : max ‖q₀‖ ‖c‖ < r₀ := by dsimp [r₀]; linarith
  have hq₀r : ‖q₀‖ < r₀ := (le_max_left _ _).trans_lt hr₀_gt
  have hr₀_lt : r₀ < R := by dsimp [r₀]; linarith
  set δ : ℝ := (r₀ - ‖q₀‖) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hd_mem : ball q₀ δ ⊆ ball (0 : ℂ) r₀ := fun q hq => by
    rw [mem_ball_zero_iff]; rw [mem_ball] at hq
    have htri : ‖q‖ ≤ ‖q - q₀‖ + ‖q₀‖ := by
      calc ‖q‖ = ‖(q - q₀) + q₀‖ := by ring_nf
        _ ≤ ‖q - q₀‖ + ‖q₀‖ := norm_add_le _ _
    have hqd : ‖q - q₀‖ < δ := by simpa [dist_eq_norm] using hq
    dsimp [δ] at hqd; linarith
  have hint_fn : ∀ q ∈ ball q₀ δ,
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), h ζ / ((ζ - q) * (ζ - c)) =
        ((2 * π * I : ℂ)⁻¹ * (Complex.I * R)) *
          ∫ θ in (0 : ℝ)..(2 * π),
            Complex.exp (θ * Complex.I) * (h (circleMap 0 R θ) /
              ((circleMap 0 R θ - q) * (circleMap 0 R θ - c))) := by
    intro q _
    have h1 : ∮ ζ in C(0, R), h ζ / ((ζ - q) * (ζ - c)) = (Complex.I * R) *
        ∫ θ in (0 : ℝ)..(2 * π), Complex.exp (θ * Complex.I) * (h (circleMap 0 R θ) /
          ((circleMap 0 R θ - q) * (circleMap 0 R θ - c))) := by
      unfold circleIntegral; simp only [deriv_circleMap, smul_eq_mul]
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only [circleMap_zero]; ring
    rw [smul_eq_mul, h1]; ring
  set F : ℂ → ℝ → ℂ := fun q θ =>
    Complex.exp (θ * Complex.I) * (h (circleMap 0 R θ) /
      ((circleMap 0 R θ - q) * (circleMap 0 R θ - c)))
  set F' : ℂ → ℝ → ℂ := fun q θ =>
    Complex.exp (θ * Complex.I) * (h (circleMap 0 R θ) /
      ((circleMap 0 R θ - q) ^ 2 * (circleMap 0 R θ - c)))
  obtain ⟨M_bd, hM_bd⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn hhc
  set B : ℝ := max M_bd 0 / ((R - r₀) ^ 2 * (R - ‖c‖))
  have hB_int : IntervalIntegrable (fun _ : ℝ => B) volume 0 (2 * π) := intervalIntegrable_const
  have hF_meas : ∀ᶠ q in 𝓝 q₀, AEStronglyMeasurable (F q) (volume.restrict (Ι 0 (2 * π))) := by
    filter_upwards [Metric.ball_mem_nhds q₀ hδ] with q hq
    have hqR : ‖q‖ < r₀ := mem_ball_zero_iff.1 (hd_mem hq)
    refine Continuous.aestronglyMeasurable ?_
    have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
    have hc_den : ∀ θ : ℝ, (circleMap 0 R θ - q) * (circleMap 0 R θ - c) ≠ 0 := fun θ => by
      have hsph : ‖circleMap 0 R θ‖ = R := by simp [circleMap, abs_of_pos hR]
      refine mul_ne_zero (sub_ne_zero.2 fun h0 => ?_) (sub_ne_zero.2 fun h0 => ?_)
      · rw [h0] at hsph; linarith
      · rw [h0] at hsph; linarith
    exact he.mul ((hhc.comp_continuous (continuous_circleMap 0 R)
      (fun θ => mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR]))).div
      (((continuous_circleMap 0 R).sub continuous_const).mul
        ((continuous_circleMap 0 R).sub continuous_const)) hc_den)
  have hF_int : IntervalIntegrable (F q₀) volume 0 (2 * π) := by
    have hq₀' : ‖q₀‖ < r₀ := by
      have : ‖q₀‖ ≤ max ‖q₀‖ ‖c‖ := le_max_left _ _; linarith
    have hc_den : ∀ θ : ℝ, (circleMap 0 R θ - q₀) * (circleMap 0 R θ - c) ≠ 0 := fun θ => by
      have hsph : ‖circleMap 0 R θ‖ = R := by simp [circleMap, abs_of_pos hR]
      exact mul_ne_zero (sub_ne_zero.2 fun h0 => by rw [h0] at hsph; linarith)
        (sub_ne_zero.2 fun h0 => by rw [h0] at hsph; linarith)
    refine Continuous.intervalIntegrable ?_ _ _
    have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
    exact he.mul ((hhc.comp_continuous (continuous_circleMap 0 R)
      (fun θ => mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR]))).div
      (((continuous_circleMap 0 R).sub continuous_const).mul
        ((continuous_circleMap 0 R).sub continuous_const)) hc_den)
  have hF'_meas : AEStronglyMeasurable (F' q₀) (volume.restrict (Ι 0 (2 * π))) := by
    have hc_den : ∀ θ : ℝ, (circleMap 0 R θ - q₀) ^ 2 * (circleMap 0 R θ - c) ≠ 0 := fun θ => by
      have hsph : ‖circleMap 0 R θ‖ = R := by simp [circleMap, abs_of_pos hR]
      exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.2 fun h0 => by rw [h0] at hsph; linarith))
        (sub_ne_zero.2 fun h0 => by rw [h0] at hsph; linarith)
    refine Continuous.aestronglyMeasurable ?_
    have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
    exact he.mul ((hhc.comp_continuous (continuous_circleMap 0 R)
      (fun θ => mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR]))).div
      ((((continuous_circleMap 0 R).sub continuous_const).pow 2).mul
        ((continuous_circleMap 0 R).sub continuous_const)) hc_den)
  have hbd : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * π) → ∀ q ∈ ball q₀ δ, ‖F' q θ‖ ≤ B := by
    refine ae_of_all _ fun θ _ q hq => ?_
    have hqR : ‖q‖ < r₀ := mem_ball_zero_iff.1 (hd_mem hq)
    have hsph : ‖circleMap 0 R θ‖ = R := by simp [circleMap, abs_of_pos hR]
    have hmem : circleMap 0 R θ ∈ sphere (0 : ℂ) R := mem_sphere_zero_iff_norm.2 hsph
    have h1 : R - r₀ ≤ ‖circleMap 0 R θ - q‖ := by linarith [norm_sub_norm_le (circleMap 0 R θ) q]
    have h2 : R - ‖c‖ ≤ ‖circleMap 0 R θ - c‖ := by linarith [norm_sub_norm_le (circleMap 0 R θ) c]
    have hexp : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    dsimp [F']
    rw [norm_mul, hexp, one_mul, norm_div, norm_mul, norm_pow]
    refine div_le_div₀ (by positivity) ((hM_bd (circleMap 0 R θ) hmem).trans (le_max_left _ _))
      (mul_pos (sq_pos_of_pos (sub_pos.2 hr₀_lt)) (sub_pos.2 hcR)) ?_
    exact mul_le_mul (pow_le_pow_left₀ (sub_nonneg.2 hr₀_lt.le) h1 2) h2 (sub_nonneg.2 hcR.le) (by positivity)
  have hderiv : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * π) → ∀ q ∈ ball q₀ δ,
      HasDerivAt (fun x => F x θ) (F' q θ) q := by
    refine ae_of_all _ fun θ _ q hq => ?_
    have hqR : ‖q‖ < r₀ := mem_ball_zero_iff.1 (hd_mem hq)
    have hsph : ‖circleMap 0 R θ‖ = R := by simp [circleMap, abs_of_pos hR]
    have hnq : circleMap 0 R θ - q ≠ 0 := sub_ne_zero.2 fun h0 => by rw [h0] at hsph; linarith
    have hnc : circleMap 0 R θ - c ≠ 0 := sub_ne_zero.2 fun h0 => by rw [h0] at hsph; linarith
    have hd1 : HasDerivAt (fun x : ℂ => circleMap 0 R θ - x) (-1) q :=
      ((hasDerivAt_const q (circleMap 0 R θ)).sub (hasDerivAt_id q)).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun x : ℂ => (circleMap 0 R θ - x)⁻¹)
        (-(-1) / (circleMap 0 R θ - q) ^ 2) q := hd1.inv hnq
    have hd3 := hd2.const_mul (Complex.exp (θ * Complex.I) * (h (circleMap 0 R θ) / (circleMap 0 R θ - c)))
    refine (hd3.congr_of_eventuallyEq (Eventually.of_forall fun x => by
      dsimp [F]; simp only [div_eq_mul_inv, mul_inv]; ring)).congr_deriv ?_
    dsimp [F']; field_simp [hnq, hnc]
  have hint_deriv := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds q₀ hδ) hF_meas hF_int hF'_meas hbd hB_int hderiv).2.const_mul
    ((2 * π * I : ℂ)⁻¹ * (Complex.I * R))
  have hev_eq : divQ h R c =ᶠ[𝓝 q₀] fun q =>
      ((2 * π * I : ℂ)⁻¹ * (Complex.I * R)) * ∫ θ in (0 : ℝ)..(2 * π), F q θ := by
    filter_upwards [Metric.ball_mem_nhds q₀ hδ] with q hq
    exact hint_fn q hq
  exact (hint_deriv.congr_of_eventuallyEq hev_eq).differentiableAt.differentiableWithinAt

/-- Real-valuedness of `divQ h R c q` on the real diameter `(-R, R)` for real `c`. -/
theorem divQ_im_zero {h : ℂ → ℂ} {R ρ : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hh : DifferentiableOn ℂ h (ball 0 ρ)) (hreal : ∀ x : ℝ, |x| < ρ → (h x).im = 0)
    {c : ℝ} (hc : |c| < R) {x : ℝ} (hx : |x| < R) :
    (divQ h R (c : ℂ) (x : ℂ)).im = 0 := by
  have hc_ball : (c : ℂ) ∈ ball (0 : ℂ) R := by simpa [mem_ball_zero_iff] using hc
  by_cases hxc : x = c
  · subst hxc
    have hcont : ContinuousAt (fun q => (divQ h R (x : ℂ) q).im) (x : ℂ) :=
      Complex.continuous_im.continuousAt.comp
        ((differentiableOn_divQ_fst hR hRρ hh hc_ball).differentiableAt
          (isOpen_ball.mem_nhds hc_ball)).continuousAt
    have hd_seq : Tendsto (fun n : ℕ => ((x + (R - |x|) / (n + 2 : ℝ) : ℝ) : ℂ))
        atTop (𝓝 (x : ℂ)) := by
      have ht : Tendsto (fun n : ℕ => x + (R - |x|) / (n + 2 : ℝ)) atTop (𝓝 x) := by
        have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
        simpa using (tendsto_const_nhds (x := x)).add
          ((tendsto_const_nhds (x := R - |x|)).div_atTop hden)
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp ht
    have hlim : Tendsto (fun n : ℕ => (divQ h R (x : ℂ) ((x + (R - |x|) / (n + 2 : ℝ) : ℝ) : ℂ)).im)
        atTop (𝓝 (divQ h R (x : ℂ) (x : ℂ)).im) := hcont.tendsto.comp hd_seq
    refine tendsto_nhds_unique hlim (Tendsto.congr (fun n => ?_) (tendsto_const_nhds (x := (0 : ℝ))))
    have hRx : 0 < R - |x| := sub_pos.2 hx
    have hstep_pos : 0 < (R - |x|) / ((n : ℝ) + 2) := div_pos hRx (by positivity)
    have hstep_lt : (R - |x|) / ((n : ℝ) + 2) < R - |x| :=
      div_lt_self hRx (by linarith)
    have hy_lt : |x + (R - |x|) / ((n : ℝ) + 2)| < R := by
      calc |x + (R - |x|) / ((n : ℝ) + 2)| ≤ |x| + |(R - |x|) / ((n : ℝ) + 2)| := abs_add_le _ _
        _ = |x| + (R - |x|) / ((n : ℝ) + 2) := by rw [abs_of_pos hstep_pos]
        _ < |x| + (R - |x|) := by linarith
        _ = R := by ring
    have hne : x + (R - |x|) / ((n : ℝ) + 2) ≠ x := by linarith
    have heq := divQ_eq hR hRρ hh hc_ball (by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hy_lt :
      ((x + (R - |x|) / ((n : ℝ) + 2) : ℝ) : ℂ) ∈ ball (0 : ℂ) R)
    have hnum : (h ((x + (R - |x|) / ((n : ℝ) + 2) : ℝ) : ℂ) - h (x : ℂ)).im = 0 := by
      rw [Complex.sub_im, hreal _ (hy_lt.trans hRρ), hreal _ (hx.trans hRρ), sub_zero]
    have hmul : (((x + (R - |x|) / ((n : ℝ) + 2) - x : ℝ) : ℂ) *
        divQ h R (x : ℂ) ((x + (R - |x|) / ((n : ℝ) + 2) : ℝ) : ℂ)).im = 0 := by
      rw [← show ((x + (R - |x|) / ((n : ℝ) + 2) : ℝ) : ℂ) - (x : ℂ) =
        ((x + (R - |x|) / ((n : ℝ) + 2) - x : ℝ) : ℂ) by push_cast; ring, ← heq]
      exact hnum
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hmul
    exact ((mul_eq_zero.1 hmul).resolve_left (sub_ne_zero.2 hne)).symm
  · have hx_ball : (x : ℂ) ∈ ball (0 : ℂ) R := by simpa [mem_ball_zero_iff] using hx
    have heq := divQ_eq hR hRρ hh hc_ball hx_ball
    have hmul : (((x - c : ℝ) : ℂ) * divQ h R (c : ℂ) (x : ℂ)).im = 0 := by
      rw [← show (x : ℂ) - (c : ℂ) = ((x - c : ℝ) : ℂ) by push_cast; ring, ← heq,
        Complex.sub_im, hreal x (hx.trans hRρ), hreal c (hc.trans hRρ), sub_zero]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hmul
    exact (mul_eq_zero.1 hmul).resolve_left (sub_ne_zero.2 hxc)

/-- Parametric holomorphicity under Cauchy circle integrals `(2πi)⁻¹ ∮_{|ζ|=R} Φ ζ a dζ`. -/
theorem differentiableOn_circleIntegral_param {Φ : ℂ → ℂ → ℂ} {R r_a M : ℝ} (hR : 0 < R)
    (hcont : ∀ a ∈ ball (0 : ℂ) r_a, ContinuousOn (fun ζ => Φ ζ a) (sphere 0 R))
    (hdiff : ∀ ζ ∈ sphere (0 : ℂ) R, DifferentiableOn ℂ (Φ ζ) (ball 0 r_a))
    (hbd : ∀ ζ ∈ sphere (0 : ℂ) R, ∀ a ∈ ball (0 : ℂ) r_a, ‖Φ ζ a‖ ≤ M) :
    DifferentiableOn ℂ (fun a => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), Φ ζ a) (ball 0 r_a) := by
  intro a₀ ha₀
  have ha₀_norm : ‖a₀‖ < r_a := mem_ball_zero_iff.1 ha₀
  set r'' : ℝ := ‖a₀‖ + (r_a - ‖a₀‖) * 2 / 3
  set r_mid : ℝ := ‖a₀‖ + (r_a - ‖a₀‖) / 3
  have hr_a_pos : 0 < r_a := (norm_nonneg a₀).trans_lt ha₀_norm
  have h1 : ‖a₀‖ < r_mid := by dsimp [r_mid]; linarith
  have h2 : r_mid < r'' := by dsimp [r_mid, r'']; linarith
  have h3 : r'' < r_a := by dsimp [r'']; linarith
  have hr_mid0 : 0 ≤ r_mid := (norm_nonneg a₀).trans h1.le
  set δ : ℝ := (r_mid - ‖a₀‖) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hd_mem : ball a₀ δ ⊆ ball (0 : ℂ) r_mid := fun a ha => by
    rw [mem_ball_zero_iff]; rw [mem_ball] at ha
    have htri : ‖a‖ ≤ ‖a - a₀‖ + ‖a₀‖ := by
      calc ‖a‖ = ‖(a - a₀) + a₀‖ := by ring_nf
        _ ≤ ‖a - a₀‖ + ‖a₀‖ := norm_add_le _ _
    have had : ‖a - a₀‖ < δ := by simpa [dist_eq_norm] using ha
    dsimp [δ] at had; linarith
  have hM0 : 0 ≤ M := (norm_nonneg (Φ R a₀)).trans
    (hbd R (mem_sphere_zero_iff_norm.2 (by simp [abs_of_pos hR])) a₀ ha₀)
  set B : ℝ := r'' * max M 0 / (r'' - r_mid) ^ 2
  have hB_int : IntervalIntegrable (fun _ : ℝ => B) volume 0 (2 * π) := intervalIntegrable_const
  set F : ℂ → ℝ → ℂ := fun a θ => Complex.exp (θ * Complex.I) * Φ (circleMap 0 R θ) a
  set F' : ℂ → ℝ → ℂ := fun a θ =>
    Complex.exp (θ * Complex.I) * deriv (Φ (circleMap 0 R θ)) a
  have hint_fn : ∀ a ∈ ball a₀ δ,
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), Φ ζ a =
        ((2 * π * I : ℂ)⁻¹ * (Complex.I * R)) * ∫ θ in (0 : ℝ)..(2 * π), F a θ := by
    intro a _
    have h1 : ∮ ζ in C(0, R), Φ ζ a = (Complex.I * R) * ∫ θ in (0 : ℝ)..(2 * π), F a θ := by
      unfold circleIntegral; simp only [deriv_circleMap, smul_eq_mul]
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      dsimp [F]; simp only [circleMap_zero]; ring
    rw [smul_eq_mul, h1]; ring
  have hF_meas : ∀ᶠ a in 𝓝 a₀, AEStronglyMeasurable (F a) (volume.restrict (Ι 0 (2 * π))) := by
    filter_upwards [Metric.ball_mem_nhds a₀ hδ] with a ha
    have ha_mem : a ∈ ball (0 : ℂ) r_a := ball_subset_ball (h2.trans h3).le (hd_mem ha)
    refine Continuous.aestronglyMeasurable ?_
    have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    exact he.mul ((hcont a ha_mem).comp_continuous (continuous_circleMap 0 R)
      (fun θ => mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR])))
  have hF_int : IntervalIntegrable (F a₀) volume 0 (2 * π) := by
    refine Continuous.intervalIntegrable ?_ _ _
    have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    exact he.mul ((hcont a₀ ha₀).comp_continuous (continuous_circleMap 0 R)
      (fun θ => mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR])))
  have hF'_meas : AEStronglyMeasurable (F' a₀) (volume.restrict (Ι 0 (2 * π))) := by
    obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
    have hN0 : ∀ n : ℕ, 0 < ((N + n + 1 : ℕ) : ℝ) := fun n => by positivity
    set G_seq : ℕ → ℝ → ℂ := fun n θ =>
      (((N + n + 1 : ℕ) : ℝ) : ℂ) * (F (a₀ + (((((N + n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)) θ - F a₀ θ)
    have hGm : ∀ n : ℕ, AEStronglyMeasurable (G_seq n) (volume.restrict (Ι 0 (2 * π))) := fun n => by
      have hn : ‖((((N + n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)‖ < δ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (hN0 n).le)]
        have hgt : δ⁻¹ < ((N + n + 1 : ℕ) : ℝ) := by
          have : (N : ℝ) ≤ ((N + n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ N + n + 1)
          linarith
        exact inv_lt_of_inv_lt₀ hδ hgt
      have ha_mem : a₀ + (((((N + n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) ∈ ball (0 : ℂ) r_a :=
        ball_subset_ball (h2.trans h3).le (hd_mem (by simpa [mem_ball, dist_eq_norm] using hn))
      refine Continuous.aestronglyMeasurable ?_
      have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) :=
        Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
      have hc1 := he.mul ((hcont _ ha_mem).comp_continuous (continuous_circleMap 0 R)
        (fun θ => mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR])))
      have hc0 := he.mul ((hcont a₀ ha₀).comp_continuous (continuous_circleMap 0 R)
        (fun θ => mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR])))
      exact continuous_const.mul (hc1.sub hc0)
    have hlim : ∀ᵐ θ ∂(volume.restrict (Ι (0 : ℝ) (2 * π))),
        Tendsto (fun n => G_seq n θ) atTop (𝓝 (F' a₀ θ)) := by
      refine ae_of_all _ fun θ => ?_
      have hmem : circleMap 0 R θ ∈ sphere (0 : ℂ) R :=
        mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR])
      have hd_a₀ : HasDerivAt (Φ (circleMap 0 R θ)) (deriv (Φ (circleMap 0 R θ)) a₀) a₀ :=
        ((hdiff _ hmem).differentiableAt (isOpen_ball.mem_nhds ha₀)).hasDerivAt
      have hd_F : HasDerivAt (fun a => F a θ) (F' a₀ θ) a₀ := by
        simpa [F, F'] using hd_a₀.const_mul (Complex.exp ((θ : ℂ) * Complex.I))
      have hslope := hd_F.tendsto_slope_zero
      have hseq : Tendsto (fun n : ℕ => (((((N + n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have ht : Tendsto (fun n : ℕ => (((N + n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
            tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp
              ((tendsto_add_atTop_nat (N + 1)).congr fun n => by omega))
          have htC : Tendsto (fun n : ℕ => (((((N + n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
            Complex.continuous_ofReal.continuousAt.tendsto.comp ht
          simpa using htC
        · exact Complex.ofReal_ne_zero.2 (inv_ne_zero (hN0 n).ne')
      refine (hslope.comp hseq).congr fun n => ?_
      dsimp [G_seq, slope_def_module, vsub_eq_sub]
      rw [Complex.ofReal_inv, inv_inv]
      push_cast; rfl
    exact aestronglyMeasurable_of_tendsto_ae atTop hGm hlim
  have hbd : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * π) → ∀ a ∈ ball a₀ δ, ‖F' a θ‖ ≤ B := by
    refine ae_of_all _ fun θ _ a ha => ?_
    have ha_norm : ‖a‖ ≤ r_mid := (mem_ball_zero_iff.1 (hd_mem ha)).le
    have hmem : circleMap 0 R θ ∈ sphere (0 : ℂ) R :=
      mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR])
    have hc_bd := cauchy_deriv_bound hr_mid0 h2 h3 (hdiff _ hmem) ha_norm fun ζ hζ =>
      (hbd (circleMap 0 R θ) hmem ζ (mem_ball_zero_iff.2
        ((mem_sphere_zero_iff_norm.1 hζ).symm ▸ h3))).trans (le_max_left M 0)
    dsimp [F']
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact hc_bd
  have hderiv : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * π) → ∀ a ∈ ball a₀ δ,
      HasDerivAt (fun x => F x θ) (F' a θ) a := by
    refine ae_of_all _ fun θ _ a ha => ?_
    have ha_mem : a ∈ ball (0 : ℂ) r_a := ball_subset_ball (h2.trans h3).le (hd_mem ha)
    have hmem : circleMap 0 R θ ∈ sphere (0 : ℂ) R :=
      mem_sphere_zero_iff_norm.2 (by simp [circleMap, abs_of_pos hR])
    have hd_a : HasDerivAt (Φ (circleMap 0 R θ)) (deriv (Φ (circleMap 0 R θ)) a) a :=
      ((hdiff _ hmem).differentiableAt (isOpen_ball.mem_nhds ha_mem)).hasDerivAt
    simpa [F, F'] using hd_a.const_mul (Complex.exp ((θ : ℂ) * Complex.I))
  have hint_deriv := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds a₀ hδ) hF_meas hF_int hF'_meas hbd hB_int hderiv).2.const_mul
    ((2 * π * I : ℂ)⁻¹ * (Complex.I * R))
  have hev_eq : (fun a => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), Φ ζ a) =ᶠ[𝓝 a₀] fun a =>
      ((2 * π * I : ℂ)⁻¹ * (Complex.I * R)) * ∫ θ in (0 : ℝ)..(2 * π), F a θ := by
    filter_upwards [Metric.ball_mem_nhds a₀ hδ] with a ha
    exact hint_fn a ha
  exact (hint_deriv.congr_of_eventuallyEq hev_eq).differentiableAt.differentiableWithinAt

/-- Parametric holomorphicity of `a ↦ divQ (H · a) R (c a) (q a)`. -/
theorem differentiableOn_divQ_param {H : ℂ → ℂ → ℂ} {c q : ℂ → ℂ} {R r_q r_a r_c M : ℝ}
    (hR : 0 < R) (hRr : R < r_q) (hcR : r_c < R)
    (hHq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => H ζ a) (ball 0 r_q))
    (hHa : ∀ ζ ∈ sphere (0 : ℂ) R, DifferentiableOn ℂ (H ζ) (ball 0 r_a))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) R, ∀ a ∈ ball (0 : ℂ) r_a, ‖H ζ a‖ ≤ M)
    (hc_diff : DifferentiableOn ℂ c (ball 0 r_a)) (hc_bd : ∀ a ∈ ball (0 : ℂ) r_a, ‖c a‖ ≤ r_c)
    (hq_diff : DifferentiableOn ℂ q (ball 0 r_a)) (hq_bd : ∀ a ∈ ball (0 : ℂ) r_a, ‖q a‖ ≤ r_c) :
    DifferentiableOn ℂ (fun a => divQ (fun ζ => H ζ a) R (c a) (q a)) (ball 0 r_a) := by
  by_cases hra : 0 < r_a
  · have hrc0 : 0 ≤ r_c := (norm_nonneg (c 0)).trans (hc_bd 0 (mem_ball_self hra))
    have hpos : 0 < R - r_c := sub_pos.2 hcR
    have hM0 : 0 ≤ M := (norm_nonneg (H (R : ℂ) 0)).trans
      (hM (R : ℂ) (mem_sphere_zero_iff_norm.2 (by simp [abs_of_pos hR])) 0 (mem_ball_self hra))
    have hcont : ∀ a ∈ ball (0 : ℂ) r_a,
        ContinuousOn (fun ζ => H ζ a / ((ζ - q a) * (ζ - c a))) (sphere 0 R) := fun a ha => by
      have hH_cont : ContinuousOn (fun ζ => H ζ a) (sphere 0 R) :=
        (hHq a ha).continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hRr))
      refine hH_cont.div (((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_id.sub continuousOn_const))) fun ζ hζ => ?_
      have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
      exact mul_ne_zero
        (sub_ne_zero.2 fun h0 => by linarith [hq_bd a ha, h0 ▸ hζR])
        (sub_ne_zero.2 fun h0 => by linarith [hc_bd a ha, h0 ▸ hζR])
    have hdiff_a : ∀ ζ ∈ sphere (0 : ℂ) R,
        DifferentiableOn ℂ (fun a => H ζ a / ((ζ - q a) * (ζ - c a))) (ball 0 r_a) := fun ζ hζ => by
      have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
      exact (hHa ζ hζ).div (((differentiableOn_const ζ).sub hq_diff).mul
        ((differentiableOn_const ζ).sub hc_diff)) fun a ha =>
        mul_ne_zero (sub_ne_zero.2 fun h0 => by linarith [hq_bd a ha, h0 ▸ hζR])
          (sub_ne_zero.2 fun h0 => by linarith [hc_bd a ha, h0 ▸ hζR])
    have hbd_a : ∀ ζ ∈ sphere (0 : ℂ) R, ∀ a ∈ ball (0 : ℂ) r_a,
        ‖H ζ a / ((ζ - q a) * (ζ - c a))‖ ≤ M / (R - r_c) ^ 2 := fun ζ hζ a ha => by
      have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
      have h1 : R - r_c ≤ ‖ζ - q a‖ := by linarith [norm_sub_norm_le ζ (q a), hq_bd a ha]
      have h2 : R - r_c ≤ ‖ζ - c a‖ := by linarith [norm_sub_norm_le ζ (c a), hc_bd a ha]
      rw [norm_div, norm_mul]
      exact div_le_div₀ hM0 (hM ζ hζ a ha) (sq_pos_of_pos hpos)
        (by nlinarith only [h1, h2, hpos])
    simpa [divQ] using differentiableOn_circleIntegral_param hR hcont hdiff_a hbd_a
  · rw [ball_eq_empty.2 (not_lt.1 hra)]; exact fun _ hx => False.elim hx

/-- Parametric holomorphicity of `a ↦ deriv (fun z => H z a) (q a)`. -/
theorem differentiableOn_deriv_param {H : ℂ → ℂ → ℂ} {q : ℂ → ℂ} {R r_q r_a r_c M : ℝ}
    (hR : 0 < R) (hRr : R < r_q) (hcR : r_c < R)
    (hHq : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => H ζ a) (ball 0 r_q))
    (hHa : ∀ ζ ∈ sphere (0 : ℂ) R, DifferentiableOn ℂ (H ζ) (ball 0 r_a))
    (hM : ∀ ζ ∈ sphere (0 : ℂ) R, ∀ a ∈ ball (0 : ℂ) r_a, ‖H ζ a‖ ≤ M)
    (hq_diff : DifferentiableOn ℂ q (ball 0 r_a)) (hq_bd : ∀ a ∈ ball (0 : ℂ) r_a, ‖q a‖ ≤ r_c) :
    DifferentiableOn ℂ (fun a => deriv (fun z => H z a) (q a)) (ball 0 r_a) := by
  by_cases hra : 0 < r_a
  · have hpos : 0 < R - r_c := sub_pos.2 hcR
    have hM0 : 0 ≤ M := (norm_nonneg (H (R : ℂ) 0)).trans
      (hM (R : ℂ) (mem_sphere_zero_iff_norm.2 (by simp [abs_of_pos hR])) 0 (mem_ball_self hra))
    have heq : Set.EqOn (fun a => deriv (fun z => H z a) (q a))
        (fun a => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - q a) ^ (-2 : ℤ) • H ζ a) (ball 0 r_a) := by
      intro a ha
      have hqR : ‖q a‖ < R := (hq_bd a ha).trans_lt hcR
      exact cauchy_deriv_formula hR hRr (hHq a ha) hqR
    refine (differentiableOn_circleIntegral_param (M := M / (R - r_c) ^ 2) hR ?_ ?_ ?_).congr heq
    · intro a ha
      have hH_cont : ContinuousOn (fun ζ => H ζ a) (sphere 0 R) :=
        (hHq a ha).continuousOn.mono (sphere_subset_closedBall.trans (closedBall_subset_ball hRr))
      have hSubC : ContinuousOn (fun ζ : ℂ => ζ - q a) (sphere 0 R) := continuousOn_id.sub continuousOn_const
      have hPow : ContinuousOn (fun ζ : ℂ => (ζ - q a) ^ (-2 : ℤ)) (sphere 0 R) :=
        hSubC.zpow₀ (-2) fun ζ hζ => Or.inl (sub_ne_zero.2 fun h0 => by
          have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
          have := hq_bd a ha; rw [← h0, hζR] at this; linarith)
      exact hPow.smul hH_cont
    · intro ζ hζ
      have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
      have hSub : DifferentiableOn ℂ (fun a : ℂ => ζ - q a) (ball 0 r_a) :=
        (differentiableOn_const ζ).sub hq_diff
      have hPow : DifferentiableOn ℂ (fun a : ℂ => (ζ - q a) ^ (-2 : ℤ)) (ball 0 r_a) :=
        hSub.zpow (m := (-2 : ℤ)) (Or.inl fun a ha => sub_ne_zero.2 fun h0 => by
          have := hq_bd a ha; rw [← h0, hζR] at this; linarith)
      exact hPow.smul (hHa ζ hζ)
    · intro ζ hζ a ha
      have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.1 hζ
      have h1 : R - r_c ≤ ‖ζ - q a‖ := by linarith [norm_sub_norm_le ζ (q a), hq_bd a ha]
      rw [norm_smul, norm_zpow, zpow_neg, zpow_two, div_eq_inv_mul]
      exact mul_le_mul (inv_anti₀ (sq_pos_of_pos hpos) (by nlinarith only [h1, hpos]))
        (hM ζ hζ a ha) (norm_nonneg _) (by positivity)
  · rw [ball_eq_empty.2 (not_lt.1 hra)]; exact fun _ hx => False.elim hx

-- Info check: no custom axioms.
/-- info: 'FormalResearch.SignUncertainty.FineOrderSigned.differentiableOn_divQ_param' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_divQ_param

end FineOrderSigned

end FormalResearch.SignUncertainty
