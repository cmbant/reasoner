module

public import FormalResearch.SignUncertainty.AiryCauchyBounds
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Smooth Regularization in the Airy Class (`lem:al-smooth`)

Source: `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex` (lines 47–77):
For `H ∈ 𝒢` and `ε ∈ (0, 1]`, `m_ε(z) = ∫_{-1}^1 φ(t) cosh(ε t √z) dt`, `M_ε = m_ε^2`, and
`H_ε(z) = M_ε(z) H(z + 2ε)` give `H_ε ∈ 𝒢 ∩ 𝓢(ℝ)` with locally uniform convergence on `ℂ`,
weighted `L¹(e^{Y max(u, 0)} du)` convergence for every `Y ≥ 0`, uniform `L¹` norm bound, and
`|ℒ_y(H_ε(· + s))| ≤ C_H e^{-s y}` (`(eq:al-shift-bound)`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric FormalResearch.Special
open scoped Real Nat ContDiff Uniformity

namespace FormalResearch.SignUncertainty

/-! ### Section 2: Smooth Regularization in the Airy Class (`lem:al-smooth`) -/

noncomputable def airyRawBump : ContDiffBump (0 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma integral_airyRawBump_pos : 0 < ∫ s : ℝ, airyRawBump s := by
  have hcont : Continuous airyRawBump := (airyRawBump.contDiff (n := (⊤ : ℕ∞))).continuous
  have hsupp : HasCompactSupport airyRawBump := airyRawBump.hasCompactSupport
  have hint : Integrable airyRawBump := hcont.integrable_of_hasCompactSupport hsupp
  have h1 : ∀ s ∈ Icc (-1 / 4 : ℝ) (1 / 4), (1 : ℝ) ≤ airyRawBump s := by
    intro s hs
    have hmem : s ∈ closedBall (0 : ℝ) airyRawBump.rIn := by
      change |s - 0| ≤ 1 / 4
      rw [sub_zero, abs_le]
      exact ⟨by linarith [hs.1], hs.2⟩
    rw [airyRawBump.one_of_mem_closedBall hmem]
  have hsub := setIntegral_mono_on (continuousOn_const.integrableOn_Icc) hint.integrableOn
    measurableSet_Icc h1
  have hval : (∫ _ in Icc (-1 / 4 : ℝ) (1 / 4), (1 : ℝ)) = 1 / 2 := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
    norm_num
  have hle_all : (∫ s in Icc (-1 / 4 : ℝ) (1 / 4), airyRawBump s) ≤ ∫ s : ℝ, airyRawBump s :=
    setIntegral_le_integral hint (Eventually.of_forall fun s => airyRawBump.nonneg' s)
  linarith

/-- Fixed normalized even smooth bump `φ ∈ C_c^∞(-1, 1)` (`supp φ ⊆ [-1/2, 1/2]`) with `φ ≥ 0`
and `∫_{-1}^1 φ = 1`. -/
noncomputable def airySmoothPhi (t : ℝ) : ℝ :=
  airyRawBump t / ∫ s : ℝ, airyRawBump s

lemma contDiff_airySmoothPhi : ContDiff ℝ (⊤ : ℕ∞) airySmoothPhi :=
  (airyRawBump.contDiff (n := (⊤ : ℕ∞))).div_const _

lemma airySmoothPhi_even (t : ℝ) : airySmoothPhi (-t) = airySmoothPhi t := by
  unfold airySmoothPhi
  rw [airyRawBump.neg]

lemma airySmoothPhi_nonneg (t : ℝ) : 0 ≤ airySmoothPhi t :=
  div_nonneg (airyRawBump.nonneg' t) integral_airyRawBump_pos.le

lemma airySmoothPhi_eq_zero_of_le_abs {t : ℝ} (ht : 1 / 2 ≤ |t|) : airySmoothPhi t = 0 := by
  have h0 : airyRawBump t = 0 := by
    by_contra hne
    have hmem : t ∈ Function.support airyRawBump := hne
    rw [airyRawBump.support_eq] at hmem
    change |t - 0| < 1 / 2 at hmem
    rw [sub_zero] at hmem
    linarith
  unfold airySmoothPhi
  rw [h0, zero_div]

lemma iteratedDeriv_airySmoothPhi_eq_zero_of_gt {t : ℝ} (ht : 1 / 2 < |t|) (m : ℕ) :
    iteratedDeriv m airySmoothPhi t = 0 := by
  have hev : airySmoothPhi =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
    have hopen : IsOpen {s : ℝ | 1 / 2 < |s|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact airySmoothPhi_eq_zero_of_le_abs (le_of_lt hs)
  rw [hev.iteratedDeriv_eq]
  rcases m with _ | m <;> simp

lemma integral_airySmoothPhi_univ : (∫ t : ℝ, airySmoothPhi t) = 1 := by
  unfold airySmoothPhi
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, mul_inv_cancel₀ integral_airyRawBump_pos.ne']

lemma intervalIntegral_airySmoothPhi : (∫ t in (-1 : ℝ)..1, airySmoothPhi t) = 1 := by
  have hsupp : Function.support airySmoothPhi ⊆ Ioc (-1 : ℝ) 1 := by
    intro t ht
    by_contra hnot
    apply ht
    apply airySmoothPhi_eq_zero_of_le_abs
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hnot
    rcases hnot with h1 | h2
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have heq : (∫ t in Ioc (-1 : ℝ) 1, airySmoothPhi t) = ∫ t : ℝ, airySmoothPhi t := by
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Ioc (-1 : ℝ) 1
    · exact indicator_of_mem ht _
    · rw [indicator_of_notMem ht]
      by_contra hne
      exact ht (hsupp (Ne.symm hne))
  rw [heq, integral_airySmoothPhi_univ]

/-- The entire cosine-cosh kernel `m_ε(z) = ∫_{-1}^1 φ(t) cosh(ε t √z) dt` (`(eq:al-smooth)`). -/
noncomputable def airySmoothM (ε : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) *
    Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))

/-- The squared multiplier `M_ε(z) = m_ε(z)^2` (`(eq:al-smooth)`). -/
noncomputable def airySmoothMSq (ε : ℝ) (z : ℂ) : ℂ :=
  airySmoothM ε z ^ 2

/-- The regularized Airy-class function `H_ε(z) = M_ε(z) H(z + 2ε)` (`(eq:al-smooth)`). -/
noncomputable def airySmoothReg (H : ℂ → ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  airySmoothMSq ε z * H (z + ((2 * ε : ℝ) : ℂ))

/-- Power series `∑' k, w^{2k} / (2k)! * z^k` equal to `cosh(w √z)` everywhere on `ℂ`. -/
noncomputable def airyCoshSeries (w : ℝ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, (((w ^ (2 * k) / (2 * k)! : ℝ) : ℂ) * z ^ k)

lemma cosh_mul_cpow_half_eq_series (w : ℝ) (z : ℂ) :
    Complex.cosh ((w : ℂ) * z ^ (1 / 2 : ℂ)) = airyCoshSeries w z := by
  rw [Complex.cosh_eq_tsum, airyCoshSeries]
  congr 1; ext k
  have hpow : ((w : ℂ) * z ^ (1 / 2 : ℂ)) ^ (2 * k) = (w : ℂ) ^ (2 * k) * z ^ k := by
    rw [mul_pow, pow_mul (z ^ (1 / 2 : ℂ)) 2 k, cpow_half_sq]
  rw [hpow]
  push_cast
  ring

private lemma summable_cosh_majorant (R : ℝ) :
    Summable (fun k : ℕ => R ^ (2 * k) / ((2 * k)! : ℝ)) :=
  (Real.hasSum_cosh R).summable

private lemma norm_cosh_series_term_le {w : ℝ} {z : ℂ} {W Z : ℝ}
    (hw : |w| ≤ W) (hz : ‖z‖ ≤ Z) (hW : 0 ≤ W) (hZ : 0 ≤ Z) (k : ℕ) :
    ‖(((w ^ (2 * k) / (2 * k)! : ℝ) : ℂ) * z ^ k)‖ ≤
      (W * (Z + 1)) ^ (2 * k) / ((2 * k)! : ℝ) := by
  have hfac : |((2 * k)! : ℝ)| = ((2 * k)! : ℝ) :=
    abs_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos (2 * k)))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, abs_div, abs_pow, hfac]
  have hZ1 : Z ^ k ≤ (Z + 1) ^ (2 * k) := by
    calc Z ^ k ≤ (Z + 1) ^ k := pow_le_pow_left₀ hZ (by linarith) k
      _ ≤ (Z + 1) ^ (2 * k) := pow_le_pow_right₀ (by linarith) (by omega)
  have hmul : |w| ^ (2 * k) * ‖z‖ ^ k ≤ (W * (Z + 1)) ^ (2 * k) := by
    calc |w| ^ (2 * k) * ‖z‖ ^ k
        ≤ W ^ (2 * k) * Z ^ k :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hw _)
            (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity) (by positivity)
      _ ≤ W ^ (2 * k) * (Z + 1) ^ (2 * k) :=
          mul_le_mul_of_nonneg_left hZ1 (pow_nonneg hW _)
      _ = (W * (Z + 1)) ^ (2 * k) := (mul_pow _ _ _).symm
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hmul (Nat.cast_nonneg _)

private lemma differentiable_airyCoshSeries (w : ℝ) :
    Differentiable ℂ (airyCoshSeries w) := by
  intro z₀
  set Z : ℝ := ‖z₀‖ + 1
  have hU : IsOpen (ball (0 : ℂ) Z) := isOpen_ball
  have hdiffOn : DifferentiableOn ℂ (airyCoshSeries w) (ball (0 : ℂ) Z) := by
    refine differentiableOn_tsum_of_summable_norm
      (summable_cosh_majorant (|w| * (Z + 1))) ?_ hU ?_
    · intro k; fun_prop
    · intro k z hz
      exact norm_cosh_series_term_le le_rfl (mem_ball_zero_iff.mp hz).le (abs_nonneg w)
        (by positivity) k
  exact hdiffOn.differentiableAt (hU.mem_nhds (by simp [Z]))

private lemma norm_deriv_airyCoshSeries_le {w : ℝ} {z : ℂ} {W Z : ℝ}
    (hw : |w| ≤ W) (hz : ‖z‖ ≤ Z) (hW : 0 ≤ W) (hZ : 0 ≤ Z) :
    ‖deriv (airyCoshSeries w) z‖ ≤ Real.cosh (W * (Z + 2)) := by
  have hsphere : ∀ ζ ∈ sphere z 1, ‖airyCoshSeries w ζ‖ ≤ Real.cosh (W * (Z + 2)) := by
    intro ζ hζ
    have hζ_le : ‖ζ‖ ≤ Z + 1 := by
      have h1 : ‖ζ - z‖ = 1 := mem_sphere_iff_norm.mp hζ
      calc ‖ζ‖ = ‖(ζ - z) + z‖ := by ring_nf
        _ ≤ ‖ζ - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 + Z := by linarith
        _ = Z + 1 := add_comm _ _
    have hsum_maj := summable_cosh_majorant (W * ((Z + 1) + 1))
    calc ‖airyCoshSeries w ζ‖
        ≤ ∑' k : ℕ, ‖(((w ^ (2 * k) / (2 * k)! : ℝ) : ℂ) * ζ ^ k)‖ :=
          norm_tsum_le_tsum_norm (hsum_maj.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun k => norm_cosh_series_term_le hw hζ_le hW (by linarith) k))
      _ ≤ ∑' k : ℕ, (W * ((Z + 1) + 1)) ^ (2 * k) / ((2 * k)! : ℝ) :=
          Summable.tsum_le_tsum
            (fun k => norm_cosh_series_term_le hw hζ_le hW (by linarith) k)
            (hsum_maj.of_nonneg_of_le (fun _ => norm_nonneg _)
              (fun k => norm_cosh_series_term_le hw hζ_le hW (by linarith) k))
            hsum_maj
      _ = Real.cosh (W * (Z + 2)) := by
          rw [show (Z + 1) + 1 = Z + 2 by ring, ← Real.cosh_eq_tsum]
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 zero_lt_one
    (differentiable_airyCoshSeries w).differentiableOn.diffContOnCl hsphere
  simpa using hc

private lemma continuous_uncurry_airyCoshSeries :
    Continuous (fun p : ℝ × ℂ => airyCoshSeries p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro ⟨w₀, z₀⟩
  set W : ℝ := |w₀| + 1
  set Z : ℝ := ‖z₀‖ + 1
  let U : Set (ℝ × ℂ) := ball (w₀, z₀) 1
  have hU_open : IsOpen U := isOpen_ball
  have hmem : (w₀, z₀) ∈ U := mem_ball_self zero_lt_one
  have hbd : ∀ k : ℕ, ∀ p ∈ U,
      ‖(((p.1 ^ (2 * k) / (2 * k)! : ℝ) : ℂ) * p.2 ^ k)‖ ≤
        (W * (Z + 1)) ^ (2 * k) / ((2 * k)! : ℝ) := by
    intro k ⟨w, z⟩ hp
    have hmax : max (dist w w₀) (dist z z₀) < 1 := by simpa [U, Prod.dist_eq] using hp
    have h1 : dist w w₀ < 1 := lt_of_le_of_lt (le_max_left _ _) hmax
    have h2 : dist z z₀ < 1 := lt_of_le_of_lt (le_max_right _ _) hmax
    have hw : |w| ≤ W := by
      rw [Real.dist_eq] at h1
      calc |w| = |(w - w₀) + w₀| := by ring_nf
        _ ≤ |w - w₀| + |w₀| := abs_add_le _ _
        _ ≤ W := by dsimp [W]; linarith
    have hz : ‖z‖ ≤ Z := by
      rw [dist_eq_norm] at h2
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ Z := by dsimp [Z]; linarith
    exact norm_cosh_series_term_le hw hz (by positivity) (by positivity) k
  have hcontOn : ContinuousOn (fun p : ℝ × ℂ => airyCoshSeries p.1 p.2) U := by
    refine (tendstoUniformlyOn_tsum (summable_cosh_majorant (W * (Z + 1))) hbd).continuousOn ?_
    refine Frequently.of_forall fun s => Continuous.continuousOn ?_
    classical
    induction s using Finset.induction_on with
    | empty => simp [continuous_const]
    | insert k s hk ih =>
      simp_rw [Finset.sum_insert hk]
      exact ((Complex.continuous_ofReal.comp ((continuous_fst.pow (2 * k)).div_const _)).mul
        (continuous_snd.pow k)).add ih
  exact hcontOn.continuousAt (hU_open.mem_nhds hmem)

lemma airySmoothM_eq_series_integral (ε : ℝ) (z : ℂ) :
    airySmoothM ε z = ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) z := by
  unfold airySmoothM
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [cosh_mul_cpow_half_eq_series]

theorem differentiable_airySmoothM (ε : ℝ) : Differentiable ℂ (airySmoothM ε) := by
  have hfun : airySmoothM ε = fun z =>
      ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) z :=
    funext (airySmoothM_eq_series_integral ε)
  rw [hfun]
  intro z₀
  set Z : ℝ := ‖z₀‖ + 1
  set W : ℝ := |ε|
  have hcont_phi : Continuous (fun t : ℝ => (airySmoothPhi t : ℂ)) :=
    Complex.continuous_ofReal.comp contDiff_airySmoothPhi.continuous
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hcont_phi.continuousOn
  set B : ℝ := max Mφ 0 * Real.cosh (W * (Z + 2))
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable
      (fun t : ℝ => (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) z)
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    refine Eventually.of_forall fun z => ?_
    refine Continuous.aestronglyMeasurable ?_
    exact hcont_phi.mul (continuous_uncurry_airyCoshSeries.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const))
  have hF_int : IntervalIntegrable
      (fun t : ℝ => (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) z₀) volume (-1) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact hcont_phi.mul (continuous_uncurry_airyCoshSeries.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const))
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => (airySmoothPhi t : ℂ) * deriv (airyCoshSeries (ε * t)) z₀)
      (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    let δ_seq : ℕ → ℂ := fun n => (((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
    have hlim : ∀ t : ℝ, Tendsto (fun n : ℕ =>
        (airySmoothPhi t : ℂ) * ((airyCoshSeries (ε * t) (z₀ + δ_seq n) -
          airyCoshSeries (ε * t) z₀) / δ_seq n)) atTop
        (𝓝 ((airySmoothPhi t : ℂ) * deriv (airyCoshSeries (ε * t)) z₀)) := by
      intro t
      refine Filter.Tendsto.const_mul _ ?_
      have hd := (differentiable_airyCoshSeries (ε * t) z₀).hasDerivAt
      have hseq : Tendsto δ_seq atTop (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have hr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
            tendsto_inv_atTop_zero.comp
              (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          exact ((Complex.continuous_ofReal.tendsto 0).comp hr).congr fun _ => rfl
        · rw [mem_compl_singleton_iff]
          exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (by positivity))
      have hsl := hd.tendsto_slope_zero.comp hseq
      refine hsl.congr fun n => ?_
      dsimp only [Function.comp_def]
      rw [smul_eq_mul, div_eq_inv_mul]
    refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => ?_) (Eventually.of_forall hlim)
    refine Continuous.aestronglyMeasurable ?_
    exact hcont_phi.mul (((continuous_uncurry_airyCoshSeries.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const)).sub
      (continuous_uncurry_airyCoshSeries.comp
        ((continuous_const.mul continuous_id).prodMk continuous_const))).div_const _)
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (-1 : ℝ) 1 → ∀ z ∈ ball z₀ 1,
      ‖(airySmoothPhi t : ℂ) * deriv (airyCoshSeries (ε * t)) z‖ ≤ B := by
    refine Eventually.of_forall fun t ht z hz => ?_
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    have ht_abs : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have hw : |ε * t| ≤ W := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg ε) ht_abs
    have hz_le : ‖z‖ ≤ Z := by
      have h1 : ‖z - z₀‖ < 1 := mem_ball_iff_norm.mp hz
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ Z := by dsimp [Z]; linarith
    have hphi_le : ‖(airySmoothPhi t : ℂ)‖ ≤ max Mφ 0 :=
      (hMφ t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _)
    rw [norm_mul]
    exact mul_le_mul hphi_le (norm_deriv_airyCoshSeries_le hw hz_le (abs_nonneg ε) (by positivity))
      (norm_nonneg _) (le_max_right _ _)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z₀ zero_lt_one) hF_meas hF_int hF'_meas h_bound
    intervalIntegrable_const
    (Eventually.of_forall fun t _ z _ =>
      ((differentiable_airyCoshSeries (ε * t) z).hasDerivAt.const_mul _))).2.differentiableAt

theorem differentiable_airySmoothMSq (ε : ℝ) : Differentiable ℂ (airySmoothMSq ε) :=
  (differentiable_airySmoothM ε).pow 2

lemma continuous_uncurry_airySmoothM :
    Continuous (fun p : ℝ × ℂ => airySmoothM p.1 p.2) := by
  have hfun : (fun p : ℝ × ℂ => airySmoothM p.1 p.2) = fun p : ℝ × ℂ =>
      ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) * airyCoshSeries (p.1 * t) p.2 :=
    funext fun p => airySmoothM_eq_series_integral p.1 p.2
  rw [hfun]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ (-1) 1
  exact (Complex.continuous_ofReal.comp (contDiff_airySmoothPhi.continuous.comp continuous_snd)).mul
    (continuous_uncurry_airyCoshSeries.comp
      ((continuous_fst.fst.mul continuous_snd).prodMk continuous_fst.snd))

lemma airySmoothM_zero (z : ℂ) : airySmoothM 0 z = 1 := by
  unfold airySmoothM
  have hcongr : (∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) *
      Complex.cosh (((0 * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))) =
      ∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp
  rw [hcongr, intervalIntegral.integral_ofReal, intervalIntegral_airySmoothPhi, Complex.ofReal_one]

lemma airySmoothMSq_zero (z : ℂ) : airySmoothMSq 0 z = 1 := by
  simp [airySmoothMSq, airySmoothM_zero]

lemma airySmoothM_ofReal_im (ε u : ℝ) : (airySmoothM ε (u : ℂ)).im = 0 := by
  rw [airySmoothM_eq_series_integral]
  have hreal : ∀ t : ℝ, (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) (u : ℂ) =
      ((airySmoothPhi t * ∑' k : ℕ, ((ε * t) ^ (2 * k) / (2 * k)!) * u ^ k : ℝ) : ℂ) := by
    intro t
    unfold airyCoshSeries
    rw [Complex.ofReal_mul, Complex.ofReal_tsum]
    simp
  have hc : (∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) * airyCoshSeries (ε * t) (u : ℂ)) =
      ∫ t in (-1 : ℝ)..1,
        ((airySmoothPhi t * ∑' k : ℕ, ((ε * t) ^ (2 * k) / (2 * k)!) * u ^ k : ℝ) : ℂ) :=
    intervalIntegral.integral_congr fun t _ => hreal t
  rw [hc, intervalIntegral.integral_ofReal, Complex.ofReal_im]

lemma airySmoothMSq_ofReal_im_and_nonneg (ε u : ℝ) :
    (airySmoothMSq ε (u : ℂ)).im = 0 ∧ 0 ≤ (airySmoothMSq ε (u : ℂ)).re := by
  have him := airySmoothM_ofReal_im ε u
  have heq : airySmoothM ε (u : ℂ) = ((airySmoothM ε (u : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  unfold airySmoothMSq
  rw [heq, ← Complex.ofReal_pow]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact sq_nonneg _⟩

private lemma norm_cosh_le_exp_abs_re (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.cosh]
  have h1 : ‖Complex.exp z‖ = Real.exp z.re := Complex.norm_exp z
  have h2 : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by rw [Complex.norm_exp, Complex.neg_re]
  have he1 : Real.exp z.re ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (le_abs_self _)
  have he2 : Real.exp (-z.re) ≤ Real.exp |z.re| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖(Complex.exp z + Complex.exp (-z)) / 2‖
      = ‖Complex.exp z + Complex.exp (-z)‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
    _ ≤ (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ = (Real.exp z.re + Real.exp (-z.re)) / 2 := by rw [h1, h2]
    _ ≤ Real.exp |z.re| := by linarith

lemma norm_airySmoothM_le {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖airySmoothM ε z‖ ≤ Real.exp (ε * airySqrtRe z) := by
  unfold airySmoothM
  have hcont : Continuous (fun t : ℝ =>
      ‖(airySmoothPhi t : ℂ) * Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))‖) := by
    refine Continuous.norm ?_
    exact (Complex.continuous_ofReal.comp contDiff_airySmoothPhi.continuous).mul
      (Complex.continuous_cosh.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)).mul continuous_const))
  have hpt : ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖(airySmoothPhi t : ℂ) * Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))‖ ≤
        airySmoothPhi t * Real.exp (ε * airySqrtRe z) := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (airySmoothPhi_nonneg t)]
    refine mul_le_mul_of_nonneg_left ?_ (airySmoothPhi_nonneg t)
    refine (norm_cosh_le_exp_abs_re _).trans (Real.exp_le_exp.mpr ?_)
    have hre : (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ)).re = ε * t * airySqrtRe z := by
      simp [airySqrtRe, Complex.mul_re]
    rw [hre, abs_mul, abs_mul, abs_of_nonneg hε, abs_of_nonneg (airySqrtRe_nonneg z)]
    have ht_abs : |t| ≤ 1 := abs_le.mpr ht
    calc ε * |t| * airySqrtRe z
        ≤ ε * 1 * airySqrtRe z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht_abs hε) (airySqrtRe_nonneg z)
      _ = ε * airySqrtRe z := by ring
  calc ‖∫ t in (-1 : ℝ)..1, (airySmoothPhi t : ℂ) *
        Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))‖
      ≤ ∫ t in (-1 : ℝ)..1, ‖(airySmoothPhi t : ℂ) *
          Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ t in (-1 : ℝ)..1, airySmoothPhi t * Real.exp (ε * airySqrtRe z) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hcont.intervalIntegrable _ _)
          ((contDiff_airySmoothPhi.continuous.mul continuous_const).intervalIntegrable _ _)
          hpt
    _ = (∫ t in (-1 : ℝ)..1, airySmoothPhi t) * Real.exp (ε * airySqrtRe z) :=
        intervalIntegral.integral_mul_const _ _
    _ = Real.exp (ε * airySqrtRe z) := by rw [intervalIntegral_airySmoothPhi, one_mul]

lemma norm_airySmoothMSq_le {ε : ℝ} (hε : 0 ≤ ε) (z : ℂ) :
    ‖airySmoothMSq ε z‖ ≤ Real.exp (2 * ε * airySqrtRe z) := by
  unfold airySmoothMSq
  rw [norm_pow]
  calc ‖airySmoothM ε z‖ ^ 2
      ≤ (Real.exp (ε * airySqrtRe z)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_airySmoothM_le hε z) 2
    _ = Real.exp (2 * ε * airySqrtRe z) := by
        rw [sq, ← Real.exp_add]; congr 1; ring

lemma airySqrtRe_ofReal_nonpos {u : ℝ} (hu : u ≤ 0) : airySqrtRe (u : ℂ) = 0 := by
  have h1 := airySqrtRe_sq_sub (u : ℂ)
  have h2 := airySqrtRe_mul_im (u : ℂ)
  simp only [Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  rcases mul_eq_zero.mp h2 with h0 | him0
  · linarith
  · rw [him0] at h1
    have : airySqrtRe (u : ℂ) ^ 2 ≤ 0 := by linarith
    nlinarith [sq_nonneg (airySqrtRe (u : ℂ))]

lemma norm_airySmoothMSq_neg_le_one {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    ‖airySmoothMSq ε ((-x : ℝ) : ℂ)‖ ≤ 1 := by
  refine (norm_airySmoothMSq_le hε ((-x : ℝ) : ℂ)).trans ?_
  rw [airySqrtRe_ofReal_nonpos (by linarith), mul_zero, Real.exp_zero]

/-- Two-step integration by parts on `[-1, 1]` for any `ψ ∈ C^∞` vanishing near `±1`:
`∫_{-1}^1 ψ''(t) cosh(w t) dt = w^2 ∫_{-1}^1 ψ(t) cosh(w t) dt`. -/
private lemma cosh_ibp_two {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hvan : ∀ j : ℕ, iteratedDeriv j ψ (-1) = 0 ∧ iteratedDeriv j ψ 1 = 0) (w : ℂ) :
    (∫ t in (-1 : ℝ)..1, ((iteratedDeriv 2 ψ t : ℝ) : ℂ) * Complex.cosh (w * (t : ℂ))) =
      w ^ 2 * ∫ t in (-1 : ℝ)..1, (ψ t : ℂ) * Complex.cosh (w * (t : ℂ)) := by
  have hd0 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (ψ s : ℂ)) ((deriv ψ t : ℝ) : ℂ) t := fun t =>
    ((hψ.differentiable (by simp) t).hasDerivAt).ofReal_comp
  have hd1 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((deriv ψ s : ℝ) : ℂ))
      ((iteratedDeriv 2 ψ t : ℝ) : ℂ) t := fun t => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    have hcd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := hψ.iterate_deriv 1
    exact ((hcd1.differentiable (by simp) t).hasDerivAt).ofReal_comp
  have hcosh : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.cosh (w * (s : ℂ)))
      (w * Complex.sinh (w * (t : ℂ))) t := fun t => by
    have hlin_c : HasDerivAt (fun z : ℂ => w * z) w (t : ℂ) :=
      ((hasDerivAt_id' (t : ℂ)).const_mul w).congr_deriv (mul_one w)
    have hc : HasDerivAt (fun z : ℂ => Complex.cosh (w * z))
        (Complex.sinh (w * (t : ℂ)) * w) (t : ℂ) :=
      (Complex.hasDerivAt_cosh (w * (t : ℂ))).comp (t : ℂ) hlin_c
    exact (hc.congr_deriv (mul_comm _ _)).comp_ofReal
  have hsinh : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.sinh (w * (s : ℂ)))
      (w * Complex.cosh (w * (t : ℂ))) t := fun t => by
    have hlin_c : HasDerivAt (fun z : ℂ => w * z) w (t : ℂ) :=
      ((hasDerivAt_id' (t : ℂ)).const_mul w).congr_deriv (mul_one w)
    have hc : HasDerivAt (fun z : ℂ => Complex.sinh (w * z))
        (Complex.cosh (w * (t : ℂ)) * w) (t : ℂ) :=
      (Complex.hasDerivAt_sinh (w * (t : ℂ))).comp (t : ℂ) hlin_c
    exact (hc.congr_deriv (mul_comm _ _)).comp_ofReal
  have hcd_d1 : Continuous (deriv ψ) := (hψ.iterate_deriv 1).continuous
  have hcd_d2 : Continuous (iteratedDeriv 2 ψ) := by
    simpa [iteratedDeriv_eq_iterate] using (hψ.iterate_deriv 2).continuous
  have hibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -1) (b := 1)
    (u := fun t => Complex.cosh (w * (t : ℂ)))
    (u' := fun t => w * Complex.sinh (w * (t : ℂ)))
    (v := fun t => ((deriv ψ t : ℝ) : ℂ))
    (v' := fun t => ((iteratedDeriv 2 ψ t : ℝ) : ℂ))
    (fun t _ => hcosh t) (fun t _ => hd1 t)
    ((continuous_const.mul (Complex.continuous_sinh.comp
      (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _)
    ((Complex.continuous_ofReal.comp hcd_d2).intervalIntegrable _ _)
  have hb1_1 : deriv ψ 1 = 0 := by rw [← iteratedDeriv_one]; exact (hvan 1).2
  have hb1_m1 : deriv ψ (-1) = 0 := by rw [← iteratedDeriv_one]; exact (hvan 1).1
  simp only [hb1_1, hb1_m1, Complex.ofReal_zero, mul_zero, sub_zero, zero_sub] at hibp1
  have hibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -1) (b := 1)
    (u := fun t => Complex.sinh (w * (t : ℂ)))
    (u' := fun t => w * Complex.cosh (w * (t : ℂ)))
    (v := fun t => (ψ t : ℂ))
    (v' := fun t => ((deriv ψ t : ℝ) : ℂ))
    (fun t _ => hsinh t) (fun t _ => hd0 t)
    ((continuous_const.mul (Complex.continuous_cosh.comp
      (continuous_const.mul Complex.continuous_ofReal))).intervalIntegrable _ _)
    ((Complex.continuous_ofReal.comp hcd_d1).intervalIntegrable _ _)
  have hb0_1 : ψ 1 = 0 := (hvan 0).2
  have hb0_m1 : ψ (-1) = 0 := (hvan 0).1
  simp only [hb0_1, hb0_m1, Complex.ofReal_zero, mul_zero, sub_zero, zero_sub] at hibp2
  calc (∫ t in (-1 : ℝ)..1, ((iteratedDeriv 2 ψ t : ℝ) : ℂ) * Complex.cosh (w * (t : ℂ)))
      = ∫ t in (-1 : ℝ)..1, Complex.cosh (w * (t : ℂ)) * ((iteratedDeriv 2 ψ t : ℝ) : ℂ) := by
          refine intervalIntegral.integral_congr fun t _ => mul_comm _ _
    _ = -∫ t in (-1 : ℝ)..1, w * Complex.sinh (w * (t : ℂ)) * ((deriv ψ t : ℝ) : ℂ) := hibp1
    _ = -w * ∫ t in (-1 : ℝ)..1, Complex.sinh (w * (t : ℂ)) * ((deriv ψ t : ℝ) : ℂ) := by
          simp_rw [mul_assoc]; rw [intervalIntegral.integral_const_mul, neg_mul]
    _ = -w * (-∫ t in (-1 : ℝ)..1, w * Complex.cosh (w * (t : ℂ)) * (ψ t : ℂ)) := by
          rw [hibp2]
    _ = w ^ 2 * ∫ t in (-1 : ℝ)..1, (ψ t : ℂ) * Complex.cosh (w * (t : ℂ)) := by
          have hmul : (∫ t in (-1 : ℝ)..1, w * Complex.cosh (w * (t : ℂ)) * (ψ t : ℂ)) =
              w * ∫ t in (-1 : ℝ)..1, (ψ t : ℂ) * Complex.cosh (w * (t : ℂ)) := by
            have hc : ∀ t : ℝ, w * Complex.cosh (w * (t : ℂ)) * (ψ t : ℂ) =
                w * ((ψ t : ℂ) * Complex.cosh (w * (t : ℂ))) := fun t => by ring
            simp_rw [hc]
            exact intervalIntegral.integral_const_mul _ _
          rw [hmul]; ring

private lemma iteratedDeriv_comp_iteratedDeriv (j k : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    iteratedDeriv j (iteratedDeriv k f) x = iteratedDeriv (j + k) f x := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

private lemma airySmoothM_ibp_iter (ε : ℝ) (z : ℂ) (m : ℕ) :
    (((ε : ℂ) ^ 2 * z) ^ m) * airySmoothM ε z =
      ∫ t in (-1 : ℝ)..1, ((iteratedDeriv (2 * m) airySmoothPhi t : ℝ) : ℂ) *
        Complex.cosh (((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ)) := by
  set w : ℂ := (ε : ℂ) * z ^ (1 / 2 : ℂ)
  have hw2 : w ^ 2 = (ε : ℂ) ^ 2 * z := by
    dsimp [w]; rw [mul_pow, cpow_half_sq]
  have harg : ∀ t : ℝ, ((ε * t : ℝ) : ℂ) * z ^ (1 / 2 : ℂ) = w * (t : ℂ) := fun t => by
    dsimp [w]; push_cast; ring
  unfold airySmoothM
  simp_rw [harg, ← hw2, ← pow_mul]
  induction m with
  | zero => simp
  | succ m ih =>
    have hcd_m : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv (2 * m) airySmoothPhi) := by
      rw [iteratedDeriv_eq_iterate]
      exact contDiff_airySmoothPhi.iterate_deriv (2 * m)
    have hstep := cosh_ibp_two (ψ := iteratedDeriv (2 * m) airySmoothPhi) hcd_m
      (fun j => by
        rw [iteratedDeriv_comp_iteratedDeriv, iteratedDeriv_comp_iteratedDeriv]
        exact ⟨iteratedDeriv_airySmoothPhi_eq_zero_of_gt (by norm_num) _,
          iteratedDeriv_airySmoothPhi_eq_zero_of_gt (by norm_num) _⟩)
      w
    have hiter : ∀ t : ℝ, iteratedDeriv 2 (iteratedDeriv (2 * m) airySmoothPhi) t =
        iteratedDeriv (2 * (m + 1)) airySmoothPhi t := fun t => by
      rw [iteratedDeriv_comp_iteratedDeriv, show 2 + 2 * m = 2 * (m + 1) by omega]
    simp_rw [hiter] at hstep
    rw [hstep, ← ih, ← mul_assoc, ← pow_add, show 2 + 2 * m = 2 * (m + 1) by omega]

/-- Uniform polynomial-decay bound on `‖airySmoothMSq ε ζ‖` on any circle `sphere (u : ℂ) r`
(`0 < r ≤ 1`) around `u ≤ -4`. -/
lemma norm_airySmoothMSq_le_on_neg_sphere {ε : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1) (m : ℕ) :
    ∃ C_m : ℝ, 0 ≤ C_m ∧ ∀ {u r : ℝ}, u ≤ -4 → 0 < r → r ≤ 1 →
      ∀ ζ ∈ sphere (u : ℂ) r, ‖airySmoothMSq ε ζ‖ ≤ C_m * (|u|⁻¹) ^ (2 * m) := by
  have hcont_phi_m : Continuous (iteratedDeriv (2 * m) airySmoothPhi) := by
    rw [iteratedDeriv_eq_iterate]
    exact (contDiff_airySmoothPhi.iterate_deriv (2 * m)).continuous
  obtain ⟨Bφ, hBφ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-1 : ℝ) 1) hcont_phi_m.continuousOn
  set Kφ : ℝ := 2 * max Bφ 0 * Real.exp 1
  refine ⟨(Kφ * (2 / ε ^ 2) ^ m) ^ 2, sq_nonneg _, fun {u r} hu _hr0 hr1 ζ hζ => ?_⟩
  have h_abs_u : 4 ≤ |u| := by rw [abs_of_neg (by linarith)]; linarith
  have hnorm_sub : ‖ζ - (u : ℂ)‖ = r := mem_sphere_iff_norm.mp hζ
  have hζ_re : ζ.re ≤ -3 := by
    have h1 := Complex.abs_re_le_norm (ζ - (u : ℂ))
    rw [hnorm_sub, Complex.sub_re, Complex.ofReal_re] at h1
    linarith [(abs_le.mp h1).2]
  have hζ_im : |ζ.im| ≤ 1 := by
    have h1 := Complex.abs_im_le_norm (ζ - (u : ℂ))
    rw [hnorm_sub, Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
    exact h1.trans hr1
  have ha_le : airySqrtRe ζ ≤ 1 / 2 := by
    have h1 := airySqrtRe_sq_sub ζ
    have h2 := airySqrtRe_mul_im ζ
    have hb_ge : 1 ≤ |(ζ ^ (1 / 2 : ℂ)).im| := by
      have : 1 ≤ (ζ ^ (1 / 2 : ℂ)).im ^ 2 := by nlinarith [sq_nonneg (airySqrtRe ζ)]
      nlinarith [sq_abs (ζ ^ (1 / 2 : ℂ)).im, abs_nonneg (ζ ^ (1 / 2 : ℂ)).im]
    have hmul : 2 * airySqrtRe ζ * |(ζ ^ (1 / 2 : ℂ)).im| ≤ 1 := by
      calc 2 * airySqrtRe ζ * |(ζ ^ (1 / 2 : ℂ)).im|
          = |2 * airySqrtRe ζ * (ζ ^ (1 / 2 : ℂ)).im| := by
            rw [abs_mul, abs_mul, Nat.abs_ofNat, abs_of_nonneg (airySqrtRe_nonneg ζ)]
        _ = |ζ.im| := by rw [h2]
        _ ≤ 1 := hζ_im
    nlinarith [airySqrtRe_nonneg ζ]
  have hζ_norm_ge : |u| / 2 ≤ ‖ζ‖ := by
    have htri : |(u : ℂ).re| ≤ ‖ζ - (u : ℂ)‖ + ‖ζ‖ := by
      calc |(u : ℂ).re| ≤ ‖(u : ℂ)‖ := Complex.abs_re_le_norm _
        _ = ‖(u : ℂ) - ζ + ζ‖ := by ring_nf
        _ ≤ ‖(u : ℂ) - ζ‖ + ‖ζ‖ := norm_add_le _ _
        _ = ‖ζ - (u : ℂ)‖ + ‖ζ‖ := by rw [norm_sub_rev]
    rw [Complex.ofReal_re, hnorm_sub] at htri
    linarith
  have hibp := airySmoothM_ibp_iter ε ζ m
  have hint_le : ‖∫ t in (-1 : ℝ)..1, ((iteratedDeriv (2 * m) airySmoothPhi t : ℝ) : ℂ) *
      Complex.cosh (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ))‖ ≤ Kφ := by
    calc ‖∫ t in (-1 : ℝ)..1, ((iteratedDeriv (2 * m) airySmoothPhi t : ℝ) : ℂ) *
          Complex.cosh (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ))‖
        ≤ ∫ t in (-1 : ℝ)..1, ‖((iteratedDeriv (2 * m) airySmoothPhi t : ℝ) : ℂ) *
            Complex.cosh (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ ≤ ∫ _ in (-1 : ℝ)..1, max Bφ 0 * Real.exp 1 := by
          refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const
            fun t ht => ?_
          · refine Continuous.intervalIntegrable (Continuous.norm ?_) _ _
            exact (Complex.continuous_ofReal.comp hcont_phi_m).mul
              (Complex.continuous_cosh.comp ((Complex.continuous_ofReal.comp
                (continuous_const.mul continuous_id)).mul continuous_const))
          · rw [norm_mul, Complex.norm_real]
            have hphi_b : ‖iteratedDeriv (2 * m) airySmoothPhi t‖ ≤ max Bφ 0 :=
              (hBφ t ht).trans (le_max_left _ _)
            have hcosh_b : ‖Complex.cosh (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ))‖ ≤ Real.exp 1 := by
              refine (norm_cosh_le_exp_abs_re _).trans (Real.exp_le_exp.mpr ?_)
              have hre : (((ε * t : ℝ) : ℂ) * ζ ^ (1 / 2 : ℂ)).re = ε * t * airySqrtRe ζ := by
                simp [airySqrtRe, Complex.mul_re]
              rw [hre, abs_mul, abs_mul, abs_of_pos hε, abs_of_nonneg (airySqrtRe_nonneg ζ)]
              have ht_abs : |t| ≤ 1 := abs_le.mpr ht
              have hεt : ε * |t| ≤ 1 := by nlinarith [abs_nonneg t]
              nlinarith [airySqrtRe_nonneg ζ]
            exact mul_le_mul hphi_b hcosh_b (norm_nonneg _) (le_max_right _ _)
      _ = Kφ := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          dsimp [Kφ]; ring
  have hM_le : ‖airySmoothM ε ζ‖ ≤ (Kφ * (2 / ε ^ 2) ^ m) * (|u|⁻¹) ^ m := by
    have h1 : ((ε ^ 2 * (|u| / 2)) ^ m) * ‖airySmoothM ε ζ‖ ≤ Kφ := by
      calc ((ε ^ 2 * (|u| / 2)) ^ m) * ‖airySmoothM ε ζ‖
          ≤ ((ε ^ 2 * ‖ζ‖) ^ m) * ‖airySmoothM ε ζ‖ :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (by positivity)
                (mul_le_mul_of_nonneg_left hζ_norm_ge (sq_nonneg ε)) m)
              (norm_nonneg _)
        _ = ‖(((ε : ℂ) ^ 2 * ζ) ^ m) * airySmoothM ε ζ‖ := by
            rw [norm_mul, norm_pow, norm_mul, norm_pow, Complex.norm_real,
              Real.norm_eq_abs, sq_abs]
        _ ≤ Kφ := by rw [hibp]; exact hint_le
    have hpos : 0 < (ε ^ 2 * (|u| / 2)) ^ m := pow_pos (by positivity) m
    have hinv : ((ε ^ 2 * (|u| / 2)) ^ m)⁻¹ = (2 / ε ^ 2) ^ m * (|u|⁻¹) ^ m := by
      rw [← inv_pow, ← mul_pow]; congr 1
      field_simp [hε.ne', (by linarith : |u| ≠ 0)]
    rw [← le_div_iff₀' hpos, div_eq_mul_inv, hinv] at h1
    exact le_trans h1 (le_of_eq (by ring))
  unfold airySmoothMSq
  rw [norm_pow]
  calc ‖airySmoothM ε ζ‖ ^ 2
      ≤ ((Kφ * (2 / ε ^ 2) ^ m) * (|u|⁻¹) ^ m) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hM_le 2
    _ = (Kφ * (2 / ε ^ 2) ^ m) ^ 2 * (|u|⁻¹) ^ (2 * m) := by
        rw [mul_pow, ← pow_mul, mul_comm m 2]

/-- Rapid decay of `M_ε(u)` and all its derivatives on `(-∞, 0]`. -/
theorem airySmoothMSq_neg_rapid_decay {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u ≤ 0 →
      |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothMSq ε (x : ℂ)).re) u| ≤ C := by
  have hcont_iter := (contDiff_re_of_differentiable (differentiable_airySmoothMSq ε)).2 n
  have hcont_d : Continuous (fun u : ℝ =>
      |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothMSq ε (x : ℂ)).re) u|) :=
    (continuous_abs.pow k).mul (continuous_abs.comp hcont_iter)
  obtain ⟨M_loc, hM_loc⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-4 : ℝ) 0) hcont_d.continuousOn
  obtain ⟨C_k, hCk_nn, hCk⟩ := norm_airySmoothMSq_le_on_neg_sphere hε hε1 k
  refine ⟨max (max M_loc 0) (n.factorial * C_k), by positivity, fun u hu => ?_⟩
  by_cases hu4 : -4 ≤ u
  · have h1 := hM_loc u ⟨hu4, hu⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    exact h1.trans ((le_max_left M_loc 0).trans (le_max_left _ _))
  · push Not at hu4
    have hu_abs : 4 < |u| := by rw [abs_of_neg (by linarith)]; linarith
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n zero_lt_one
      (differentiable_airySmoothMSq ε).differentiableOn.diffContOnCl
      (fun ζ hζ => hCk hu4.le zero_lt_one le_rfl ζ hζ)
    rw [one_pow, div_one] at hcauchy
    have hderiv_le : |iteratedDeriv n (fun x : ℝ => (airySmoothMSq ε (x : ℂ)).re) u| ≤
        n.factorial * (C_k * (|u|⁻¹) ^ (2 * k)) := by
      rw [iteratedDeriv_re_of_differentiable (differentiable_airySmoothMSq ε)]
      exact (Complex.abs_re_le_norm _).trans hcauchy
    have hpow_le : |u| ^ k * (|u|⁻¹) ^ (2 * k) ≤ 1 := by
      rw [show 2 * k = k + k by omega, pow_add, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ (by linarith), one_pow, one_mul]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
    calc |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothMSq ε (x : ℂ)).re) u|
        ≤ |u| ^ k * (n.factorial * (C_k * (|u|⁻¹) ^ (2 * k))) :=
          mul_le_mul_of_nonneg_left hderiv_le (by positivity)
      _ = (n.factorial * C_k) * (|u| ^ k * (|u|⁻¹) ^ (2 * k)) := by ring
      _ ≤ (n.factorial * C_k) * 1 :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
      _ ≤ max (max M_loc 0) (n.factorial * C_k) := by rw [mul_one]; exact le_max_right _ _

private lemma pow_mul_exp_neg_le (N : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ N * Real.exp (-x) ≤ N.factorial := by
  have hterm : x ^ N / (N.factorial : ℝ) ≤ Real.exp x := by
    rw [Real.exp_eq_exp_ℝ]
    have hsum := NormedSpace.expSeries_div_hasSum_exp x
    have h := Summable.le_tsum hsum.summable N (fun k _ => by positivity)
    simpa [← hsum.tsum_eq] using h
  have hfac_pos : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  rw [div_le_iff₀ hfac_pos] at hterm
  calc x ^ N * Real.exp (-x)
      ≤ (Real.exp x * N.factorial) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hterm (Real.exp_pos _).le
    _ = N.factorial * (Real.exp x * Real.exp (-x)) := by ring
    _ = N.factorial := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]


private lemma airySmoothReg_zero (H : ℂ → ℂ) (z : ℂ) : airySmoothReg H 0 z = H z := by
  simp [airySmoothReg, airySmoothMSq_zero]

private lemma differentiable_airySmoothReg {H : ℂ → ℂ} (hH : Differentiable ℂ H) (ε : ℝ) :
    Differentiable ℂ (airySmoothReg H ε) :=
  (differentiable_airySmoothMSq ε).mul (hH.comp (differentiable_id.add (differentiable_const _)))

private lemma airySmoothReg_im_zero {H : ℂ → ℂ} (hH_im : ∀ u : ℝ, (H (u : ℂ)).im = 0)
    (ε : ℝ) (u : ℝ) : (airySmoothReg H ε (u : ℂ)).im = 0 := by
  unfold airySmoothReg
  have hm_im := (airySmoothMSq_ofReal_im_and_nonneg ε u).1
  have hcast : (u : ℂ) + ((2 * ε : ℝ) : ℂ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.mul_im, hm_im, hH_im (u + 2 * ε)]
  ring

private lemma airyEnv_ofReal_nonneg_eq {u : ℝ} (hu : 0 ≤ u) :
    airyEnv (u : ℂ) = Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) := by
  unfold airyEnv
  congr 2
  have hc := (Complex.ofReal_cpow hu (3 / 2 : ℝ)).symm
  push_cast at hc
  rw [hc, Complex.ofReal_re]

private lemma airySmoothReg_growth {H : ℂ → ℂ} {C₀ ν₀ : ℝ} (hC₀_nn : 0 ≤ C₀)
    (hb₀ : ∀ z : ℂ, ‖H z‖ ≤ C₀ * (1 + ‖z‖) ^ ν₀ * airyEnv z)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (z : ℂ) :
    ‖airySmoothReg H ε z‖ ≤ (C₀ * 3 ^ |ν₀|) * (1 + ‖z‖) ^ ν₀ * airyEnv z := by
  set K_shift : ℝ := 3 ^ |ν₀|
  have hK_pos : 0 < K_shift := by positivity
  unfold airySmoothReg
  rw [norm_mul]
  have hM := norm_airySmoothMSq_le hε0 z
  have hHz := hb₀ (z + ((2 * ε : ℝ) : ℂ))
  have henv_shift := airyEnv_add_real_le z (2 * ε)
  have hprod_env : Real.exp (2 * ε * airySqrtRe z) * airyEnv (z + ((2 * ε : ℝ) : ℂ)) ≤ airyEnv z := by
    calc Real.exp (2 * ε * airySqrtRe z) * airyEnv (z + ((2 * ε : ℝ) : ℂ))
        ≤ Real.exp (2 * ε * airySqrtRe z) *
            (airyEnv z * Real.exp (-2 * (2 * ε) * airySqrtRe z)) :=
          mul_le_mul_of_nonneg_left henv_shift (Real.exp_pos _).le
      _ = airyEnv z * Real.exp (-2 * ε * airySqrtRe z) := by
          rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
          congr 2; ring
      _ ≤ airyEnv z * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (by nlinarith [airySqrtRe_nonneg z])) (airyEnv_pos z).le
      _ = airyEnv z := mul_one _
  have hpoly : (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ ≤ K_shift * (1 + ‖z‖) ^ ν₀ := by
    have hz_pos : 0 < 1 + ‖z‖ := by positivity
    have hzs_pos : 0 < 1 + ‖z + ((2 * ε : ℝ) : ℂ)‖ := by positivity
    rcases le_or_gt 0 ν₀ with hν | hν
    · have hup : 1 + ‖z + ((2 * ε : ℝ) : ℂ)‖ ≤ 3 * (1 + ‖z‖) := by
        have htri := norm_add_le z ((2 * ε : ℝ) : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at htri
        nlinarith [norm_nonneg z]
      dsimp [K_shift]
      rw [abs_of_nonneg hν, ← Real.mul_rpow (by norm_num) hz_pos.le]
      exact Real.rpow_le_rpow hzs_pos.le hup hν
    · have hlow : (1 + ‖z‖) / 3 ≤ 1 + ‖z + ((2 * ε : ℝ) : ℂ)‖ := by
        by_cases hz2 : ‖z‖ ≤ 2
        · have : (1 + ‖z‖) / 3 ≤ 1 := by linarith
          linarith [norm_nonneg (z + ((2 * ε : ℝ) : ℂ))]
        · push Not at hz2
          have htri : ‖z‖ ≤ ‖z + ((2 * ε : ℝ) : ℂ)‖ + 2 * ε := by
            calc ‖z‖ = ‖(z + ((2 * ε : ℝ) : ℂ)) - ((2 * ε : ℝ) : ℂ)‖ := by ring_nf
              _ ≤ ‖z + ((2 * ε : ℝ) : ℂ)‖ + ‖((2 * ε : ℝ) : ℂ)‖ := norm_sub_le _ _
              _ = ‖z + ((2 * ε : ℝ) : ℂ)‖ + 2 * ε := by
                  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith [norm_nonneg (z + ((2 * ε : ℝ) : ℂ))]
      have hneg : 0 ≤ -ν₀ := by linarith
      have h1 : (1 + ‖z‖) ^ (-ν₀) ≤ (3 * (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖)) ^ (-ν₀) :=
        Real.rpow_le_rpow hz_pos.le (by linarith) hneg
      rw [Real.mul_rpow (by norm_num) hzs_pos.le] at h1
      have hp1 : 0 < (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ (-ν₀) := Real.rpow_pos_of_pos hzs_pos _
      have hp2 : 0 < (1 + ‖z‖) ^ (-ν₀) := Real.rpow_pos_of_pos hz_pos _
      have h2 : (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ = ((1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ (-ν₀))⁻¹ := by
        rw [Real.rpow_neg hzs_pos.le, inv_inv]
      have h3 : (1 + ‖z‖) ^ ν₀ = ((1 + ‖z‖) ^ (-ν₀))⁻¹ := by
        rw [Real.rpow_neg hz_pos.le, inv_inv]
      dsimp [K_shift]
      rw [abs_of_neg hν, h2, h3, inv_le_iff_one_le_mul₀' hp1]
      calc (1 : ℝ) = (1 + ‖z‖) ^ (-ν₀) * ((1 + ‖z‖) ^ (-ν₀))⁻¹ := (mul_inv_cancel₀ hp2.ne').symm
        _ ≤ (3 ^ (-ν₀) * (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ (-ν₀)) * ((1 + ‖z‖) ^ (-ν₀))⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hp2.le)
        _ = (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ (-ν₀) *
              (3 ^ (-ν₀) * ((1 + ‖z‖) ^ (-ν₀))⁻¹) := by ring
  calc ‖airySmoothMSq ε z‖ * ‖H (z + ((2 * ε : ℝ) : ℂ))‖
      ≤ Real.exp (2 * ε * airySqrtRe z) *
          (C₀ * (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ * airyEnv (z + ((2 * ε : ℝ) : ℂ))) :=
        mul_le_mul hM hHz (norm_nonneg _) (Real.exp_pos _).le
    _ = C₀ * (1 + ‖z + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ *
          (Real.exp (2 * ε * airySqrtRe z) * airyEnv (z + ((2 * ε : ℝ) : ℂ))) := by ring
    _ ≤ C₀ * (K_shift * (1 + ‖z‖) ^ ν₀) * airyEnv z :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpoly hC₀_nn) hprod_env
          (mul_nonneg (Real.exp_pos _).le (airyEnv_pos _).le)
          (mul_nonneg hC₀_nn (mul_nonneg hK_pos.le (Real.rpow_nonneg (by positivity) _)))
    _ = (C₀ * K_shift) * (1 + ‖z‖) ^ ν₀ * airyEnv z := by ring
-- Helper for `airyEnv (u : ℂ)` on `u ≥ 0`


private lemma integrableOn_airySmooth_pos_maj {C₀ ν₀ : ℝ} (hC₀_nn : 0 ≤ C₀) {Y : ℝ} (hY : 0 ≤ Y) :
    IntegrableOn (fun u : ℝ => (C₀ * 3 ^ |ν₀|) * (1 + |u|) ^ ν₀ *
      airyEnv (u : ℂ) * Real.exp (Y * u)) (Ioi 0) := by
  set K_shift : ℝ := 3 ^ |ν₀|
  have hK_pos : 0 < K_shift := by positivity
  have hairyEnv_nonneg_eq : ∀ u : ℝ, 0 ≤ u →
      airyEnv (u : ℂ) = Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) :=
    fun u hu => airyEnv_ofReal_nonneg_eq hu
  have hcontOn_airyEnv_Ici : ContinuousOn (fun u : ℝ => airyEnv (u : ℂ)) (Ici 0) := by
    refine (Continuous.continuousOn ?_).congr fun u (hu : 0 ≤ u) => hairyEnv_nonneg_eq u hu
    exact Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr (by norm_num)))
  set R₀ : ℝ := max 5 ((3 * (Y + 1)) ^ 2)
  have hR₀_ge5 : 5 ≤ R₀ := le_max_left _ _
  have hmid : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
      airyEnv (u : ℂ) * Real.exp (Y * u)) (Icc 0 R₀) := by
    refine ContinuousOn.integrableOn_Icc ?_
    refine (((continuousOn_const.mul ?_).mul ?_).mul ?_)
    · refine ContinuousOn.rpow_const (continuousOn_const.add continuous_abs.continuousOn) ?_
      intro x _; left; positivity
    · exact hcontOn_airyEnv_Ici.mono (fun x hx => hx.1)
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have htail : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
      airyEnv (u : ℂ) * Real.exp (Y * u)) (Ioi R₀) := by
    set Np : ℕ := ⌈|ν₀|⌉₊
    have hdom : IntegrableOn (fun u : ℝ =>
        ((C₀ * K_shift) * Real.exp 1 * Np.factorial) * Real.exp (-u)) (Ioi R₀) := by
      have hexp : IntegrableOn (fun u : ℝ => Real.exp (-1 * u)) (Ioi R₀) :=
        integrableOn_exp_mul_Ioi (by norm_num) R₀
      have hexp' : IntegrableOn (fun u : ℝ => Real.exp (-u)) (Ioi R₀) :=
        hexp.congr_fun (fun u _ => by ring_nf) measurableSet_Ioi
      exact hexp'.const_mul ((C₀ * K_shift) * Real.exp 1 * Np.factorial)
    refine hdom.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : R₀ < u) => ?_)
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine (((continuousOn_const.mul ?_).mul ?_).mul ?_)
      · refine ContinuousOn.rpow_const (continuousOn_const.add continuous_abs.continuousOn) ?_
        intro x _; left; positivity
      · exact hcontOn_airyEnv_Ici.mono (fun x (hx : R₀ < x) => show 0 ≤ x by linarith)
      · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · have hu_pos : 0 < u := by linarith
      have henv_eq := hairyEnv_nonneg_eq u hu_pos.le
      have hsqrt_ge : 3 * (Y + 1) ≤ Real.sqrt u := by
        have hsq : (3 * (Y + 1)) ^ 2 ≤ u := (le_max_right _ _).trans hu.le
        exact Real.le_sqrt_of_sq_le hsq
      have hu32 : u * Real.sqrt u = u ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hu_pos.le (by norm_num)]
        norm_num
      have hexp_le : airyEnv (u : ℂ) * Real.exp (Y * u) ≤ Real.exp (-2 * u) := by
        rw [henv_eq, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 : 3 * (Y + 1) * u ≤ u ^ (3 / 2 : ℝ) := by
          rw [← hu32]; nlinarith
        nlinarith
      have hrpow_le : (1 + |u|) ^ ν₀ ≤ (1 + u) ^ Np := by
        rw [abs_of_pos hu_pos, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith)
          ((le_abs_self ν₀).trans (Nat.le_ceil |ν₀|))
      have hpow_exp : (1 + u) ^ Np * Real.exp (-2 * u) ≤
          Real.exp 1 * Np.factorial * Real.exp (-u) := by
        have hpe := pow_mul_exp_neg_le Np (x := 1 + u) (by positivity)
        calc (1 + u) ^ Np * Real.exp (-2 * u)
            = ((1 + u) ^ Np * Real.exp (-(1 + u))) * Real.exp (1 - u) := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
          _ ≤ Np.factorial * Real.exp (1 - u) :=
              mul_le_mul_of_nonneg_right hpe (Real.exp_pos _).le
          _ = Real.exp 1 * Np.factorial * Real.exp (-u) := by
              rw [sub_eq_add_neg, Real.exp_add]; ring
      have henv_u_nn : 0 ≤ airyEnv (u : ℂ) := (airyEnv_pos (u : ℂ)).le
      have hterm_nn : 0 ≤ (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀_nn hK_pos.le)
          (Real.rpow_nonneg (by positivity) _)) henv_u_nn) (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_of_nonneg hterm_nn]
      calc (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u)
          = (C₀ * K_shift) * ((1 + |u|) ^ ν₀ * (airyEnv (u : ℂ) * Real.exp (Y * u))) := by ring
        _ ≤ (C₀ * K_shift) * ((1 + u) ^ Np * Real.exp (-2 * u)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hrpow_le hexp_le
                (mul_nonneg henv_u_nn (Real.exp_pos _).le) (by positivity))
              (by positivity)
        _ ≤ (C₀ * K_shift) * (Real.exp 1 * Np.factorial * Real.exp (-u)) :=
            mul_le_mul_of_nonneg_left hpow_exp (by positivity)
        _ = ((C₀ * K_shift) * Real.exp 1 * Np.factorial) * Real.exp (-u) := by ring
  have hIci : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
      airyEnv (u : ℂ) * Real.exp (Y * u)) (Ici 0) := by
    rw [← Icc_union_Ioi_eq_Ici (by positivity : (0 : ℝ) ≤ R₀)]
    exact hmid.union htail
  exact hIci.mono_set Ioi_subset_Ici_self
-- Uniform L¹ bound `C_H` for `airySmoothReg H ε` (`ε ∈ [0, 1]`).


private lemma airySmoothReg_int_and_l1 {H : ℂ → ℂ} (hH : InAiryClass H)
    {C₀ ν₀ : ℝ} (hC₀_nn : 0 ≤ C₀) (hb₀ : ∀ z : ℂ, ‖H z‖ ≤ C₀ * (1 + ‖z‖) ^ ν₀ * airyEnv z) :
    ∃ C_H : ℝ, 0 ≤ C_H ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      Integrable (fun u : ℝ => airySmoothReg H ε (u : ℂ)) ∧
      (∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖) ≤ C_H := by
  set K_shift : ℝ := 3 ^ |ν₀|
  have hK_pos : 0 < K_shift := by positivity
  have hReg_diff : ∀ ε : ℝ, Differentiable ℂ (airySmoothReg H ε) :=
    differentiable_airySmoothReg hH.1
  have hReg_growth : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ z : ℂ,
      ‖airySmoothReg H ε z‖ ≤ (C₀ * K_shift) * (1 + ‖z‖) ^ ν₀ * airyEnv z :=
    fun ε h0 h1 z => airySmoothReg_growth hC₀_nn hb₀ h0 h1 z
  have hpos_maj_int : ∀ Y : ℝ, 0 ≤ Y →
      IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
        airyEnv (u : ℂ) * Real.exp (Y * u)) (Ioi 0) :=
    fun Y hY => integrableOn_airySmooth_pos_maj hC₀_nn hY
  obtain ⟨M_mid, hM_mid⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2 : ℝ) 2) (hH.1.continuous.comp Complex.continuous_ofReal).continuousOn
  set I_H : ℝ := ∫ v : ℝ, ‖H (v : ℂ)‖
  set I_pos0 : ℝ := ∫ u in Ioi (0 : ℝ), (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)
  set C_H : ℝ := I_H + 2 * max M_mid 0 + I_pos0
  have hI_H_nn : 0 ≤ I_H := integral_nonneg fun _ => norm_nonneg _
  have hI_pos0_nn : 0 ≤ I_pos0 := setIntegral_nonneg measurableSet_Ioi fun u _ =>
    mul_nonneg (mul_nonneg (mul_nonneg hC₀_nn hK_pos.le) (Real.rpow_nonneg (by positivity) _))
      (airyEnv_pos (u : ℂ)).le
  have hC_H_nn : 0 ≤ C_H := by positivity
  have hReg_int_and_l1 : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      Integrable (fun u : ℝ => airySmoothReg H ε (u : ℂ)) ∧
      (∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖) ≤ C_H := by
    intro ε hε0 hε1
    have hmeas : AEStronglyMeasurable (fun u : ℝ => airySmoothReg H ε (u : ℂ)) volume :=
      ((hReg_diff ε).continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
    -- Integrability and bound on `Ioi 0`
    have hint_pos : IntegrableOn (fun u : ℝ => airySmoothReg H ε (u : ℂ)) (Ioi 0) := by
      have hdom0 : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ))
          (Ioi 0) := by
        simpa [zero_mul, Real.exp_zero, mul_one] using hpos_maj_int 0 le_rfl
      refine hdom0.mono' hmeas.restrict
        (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_)
      simpa [Complex.norm_real, Real.norm_eq_abs] using hReg_growth ε hε0 hε1 (u : ℂ)
    have hbd_pos : (∫ u in Ioi (0 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) ≤ I_pos0 := by
      have hdom0 : IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ))
          (Ioi 0) := by
        simpa [zero_mul, Real.exp_zero, mul_one] using hpos_maj_int 0 le_rfl
      refine setIntegral_mono_on hint_pos.norm hdom0 measurableSet_Ioi fun u _ => ?_
      simpa [Complex.norm_real, Real.norm_eq_abs] using hReg_growth ε hε0 hε1 (u : ℂ)
    -- Integrability and bound on `Ioc (-2) 0`
    have hint_mid : IntegrableOn (fun u : ℝ => airySmoothReg H ε (u : ℂ)) (Ioc (-2) 0) :=
      (((hReg_diff ε).continuous.comp Complex.continuous_ofReal).continuousOn.integrableOn_Icc).mono_set
        Ioc_subset_Icc_self
    have hbd_mid : (∫ u in Ioc (-2 : ℝ) 0, ‖airySmoothReg H ε (u : ℂ)‖) ≤ 2 * max M_mid 0 := by
      have hpt : ∀ u ∈ Ioc (-2 : ℝ) 0, ‖airySmoothReg H ε (u : ℂ)‖ ≤ max M_mid 0 := by
        intro u hu
        unfold airySmoothReg
        rw [norm_mul]
        have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
          have := norm_airySmoothMSq_neg_le_one hε0 (x := -u) (by linarith [hu.2])
          simpa using this
        have hcast : (u : ℂ) + (2 * ε : ℝ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
        rw [hcast]
        have hH1 : ‖H ((u + 2 * ε : ℝ) : ℂ)‖ ≤ max M_mid 0 :=
          (hM_mid (u + 2 * ε) ⟨by linarith [hu.1], by linarith [hu.2]⟩).trans (le_max_left _ _)
        nlinarith [norm_nonneg (H ((u + 2 * ε : ℝ) : ℂ))]
      calc (∫ u in Ioc (-2 : ℝ) 0, ‖airySmoothReg H ε (u : ℂ)‖)
          ≤ ∫ _ in Ioc (-2 : ℝ) 0, max M_mid 0 :=
            setIntegral_mono_on hint_mid.norm
              (continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              measurableSet_Ioc hpt
        _ = 2 * max M_mid 0 := by
            rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
            ring
    -- Integrability and bound on `Iic (-2)`
    have hint_far : IntegrableOn (fun u : ℝ => airySmoothReg H ε (u : ℂ)) (Iic (-2)) := by
      have hdom_shift : IntegrableOn (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖) (Iic (-2)) :=
        (hH.2.1.norm.comp_add_right (2 * ε)).integrableOn
      refine hdom_shift.mono' hmeas.restrict
        (ae_restrict_of_forall_mem measurableSet_Iic fun u (hu : u ≤ -2) => ?_)
      unfold airySmoothReg
      rw [norm_mul]
      have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
        have := norm_airySmoothMSq_neg_le_one hε0 (x := -u) (by linarith)
        simpa using this
      have hcast : (u : ℂ) + (2 * ε : ℝ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast]
      exact mul_le_of_le_one_left (norm_nonneg _) hM1
    have hbd_far : (∫ u in Iic (-2 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) ≤ I_H := by
      have hdom_shift : Integrable (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖) :=
        hH.2.1.norm.comp_add_right (2 * ε)
      have hmono := setIntegral_mono_on hint_far.norm hdom_shift.integrableOn
        measurableSet_Iic fun u (hu : u ≤ -2) => by
          unfold airySmoothReg
          rw [norm_mul]
          have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
            have := norm_airySmoothMSq_neg_le_one hε0 (x := -u) (by linarith)
            simpa using this
          have hcast : (u : ℂ) + (2 * ε : ℝ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
          rw [hcast]
          exact mul_le_of_le_one_left (norm_nonneg _) hM1
      refine hmono.trans ?_
      calc (∫ u in Iic (-2 : ℝ), ‖H ((u + 2 * ε : ℝ) : ℂ)‖)
          ≤ ∫ u : ℝ, ‖H ((u + 2 * ε : ℝ) : ℂ)‖ :=
            setIntegral_le_integral hdom_shift (Eventually.of_forall fun _ => norm_nonneg _)
        _ = I_H := integral_add_right_eq_self (fun v : ℝ => ‖H (v : ℂ)‖) (2 * ε)
    have hint_Iic0 : IntegrableOn (fun u : ℝ => airySmoothReg H ε (u : ℂ)) (Iic 0) := by
      rw [← Iic_union_Ioc_eq_Iic (by norm_num : (-2 : ℝ) ≤ 0)]
      exact hint_far.union hint_mid
    have hint_univ : Integrable (fun u : ℝ => airySmoothReg H ε (u : ℂ)) := by
      rw [← integrableOn_univ, ← Iic_union_Ioi]
      exact hint_Iic0.union hint_pos
    refine ⟨hint_univ, ?_⟩
    have hsplit1 : (∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖) =
        (∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) +
          ∫ u in Ioi (0 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖ := by
      rw [← setIntegral_univ, ← Iic_union_Ioi,
        setIntegral_union (Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2)
          measurableSet_Ioi hint_Iic0.norm hint_pos.norm]
    have hsplit2 : (∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) =
        (∫ u in Iic (-2 : ℝ), ‖airySmoothReg H ε (u : ℂ)‖) +
          ∫ u in Ioc (-2 : ℝ) 0, ‖airySmoothReg H ε (u : ℂ)‖ := by
      have hdisj : Disjoint (Iic (-2 : ℝ)) (Ioc (-2 : ℝ) 0) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2.1
      rw [← Iic_union_Ioc_eq_Iic (by norm_num : (-2 : ℝ) ≤ 0),
        setIntegral_union hdisj measurableSet_Ioc hint_far.norm hint_mid.norm]
    rw [hsplit1, hsplit2]
    dsimp [C_H]
    linarith
  exact ⟨C_H, hC_H_nn, hReg_int_and_l1⟩

private lemma airySmoothReg_schwartz {H : ℂ → ℂ} (hH : InAiryClass H)
    {C₀ ν₀ : ℝ} (hC₀_nn : 0 ≤ C₀) (hb₀ : ∀ z : ℂ, ‖H z‖ ≤ C₀ * (1 + ‖z‖) ^ ν₀ * airyEnv z)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ S_ε : SchwartzMap ℝ ℝ, ∀ u : ℝ, S_ε u = (airySmoothReg H ε (u : ℂ)).re := by
  set K_shift : ℝ := 3 ^ |ν₀|
  have hReg_diff : ∀ ε' : ℝ, Differentiable ℂ (airySmoothReg H ε') :=
    differentiable_airySmoothReg hH.1
  have hReg_growth : ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ 1 → ∀ z : ℂ,
      ‖airySmoothReg H ε' z‖ ≤ (C₀ * K_shift) * (1 + ‖z‖) ^ ν₀ * airyEnv z :=
    fun ε' h0 h1 z => airySmoothReg_growth hC₀_nn hb₀ h0 h1 z
  have hairyEnv_nonneg_eq : ∀ u : ℝ, 0 ≤ u →
      airyEnv (u : ℂ) = Real.exp (-(4 / 3) * u ^ (3 / 2 : ℝ)) :=
    fun u hu => airyEnv_ofReal_nonneg_eq hu
  obtain ⟨hsmooth_re, hcont_iter_re⟩ := contDiff_re_of_differentiable (hReg_diff ε)
  refine ⟨{
    toFun := fun u => (airySmoothReg H ε (u : ℂ)).re
    smooth' := hsmooth_re
    decay' := fun k n => ?_
  }, fun _ => rfl⟩
  have hcont_kn : Continuous (fun u : ℝ =>
      |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u|) :=
    (continuous_abs.pow k).mul (continuous_abs.comp (hcont_iter_re n))
  obtain ⟨M_box, hM_box⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-5 : ℝ) 5) hcont_kn.continuousOn
  set Nν : ℕ := ⌈|ν₀|⌉₊
  set m_ord : ℕ := k + n + Nν + 1
  obtain ⟨C_m, hCm_nn, hCm⟩ := norm_airySmoothMSq_le_on_neg_sphere hε0 hε1 m_ord
  -- Left tail `u < -5`:
  set C_left : ℝ := n.factorial * C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ (n + Nν)
  -- Right tail `5 < u`:
  set N_right : ℕ := k + n + Nν
  set C_right : ℝ := n.factorial * (C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 41 * N_right.factorial
  refine ⟨max (max M_box 0) (max C_left C_right), fun u => ?_⟩
  rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  by_cases hu_mid : -5 ≤ u ∧ u ≤ 5
  · have h1 := hM_box u hu_mid
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    exact h1.trans ((le_max_left M_box 0).trans (le_max_left _ _))
  · rw [not_and_or, not_le, not_le] at hu_mid
    set r_u : ℝ := (1 + |u|) ^ (-(1 / 2 : ℝ))
    have hu1_pos : 0 < 1 + |u| := by positivity
    have hru_pos : 0 < r_u := Real.rpow_pos_of_pos hu1_pos _
    have hru_le1 : r_u ≤ 1 := by
      have h1 : (1 : ℝ) ≤ 1 + |u| := by linarith [abs_nonneg u]
      have h2 := Real.rpow_le_rpow_of_nonpos zero_lt_one h1 (by norm_num : -(1 / 2 : ℝ) ≤ 0)
      rwa [Real.one_rpow] at h2
    have hru_pow_inv : (r_u ^ n)⁻¹ ≤ (1 + |u|) ^ n := by
      have hinv : r_u⁻¹ = (1 + |u|) ^ (1 / 2 : ℝ) := by
        dsimp [r_u]; rw [Real.rpow_neg hu1_pos.le, inv_inv]
      rw [← inv_pow, hinv, ← Real.rpow_natCast ((1 + |u|) ^ (1 / 2 : ℝ)),
        ← Real.rpow_mul hu1_pos.le, ← Real.rpow_natCast (1 + |u|) n]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rcases hu_mid with hu_lt | hu_gt
    · -- `u < -5`
      have hu_abs : 5 < |u| := by rw [abs_of_neg (by linarith)]; linarith
      have hsphere_neg : ∀ ζ ∈ sphere (u : ℂ) r_u,
          ‖airySmoothReg H ε ζ‖ ≤
            (C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ Nν) *
              (|u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord)) := by
        intro ζ hζ
        have hnorm_sub : ‖ζ - (u : ℂ)‖ = r_u := mem_sphere_iff_norm.mp hζ
        have hM_s := hCm (by linarith : u ≤ -4) hru_pos hru_le1 ζ hζ
        set w_u : ℂ := ((u + 2 * ε : ℝ) : ℂ)
        have hw_eq : (u : ℂ) + ((2 * ε : ℝ) : ℂ) = w_u := by dsimp [w_u]; push_cast; rfl
        have hsub_w : (ζ + ((2 * ε : ℝ) : ℂ)) - w_u = ζ - (u : ℂ) := by
          rw [← hw_eq]; ring
        have hrw_le : r_u ≤ 2 * (1 + ‖w_u‖) ^ (-(1 / 2 : ℝ)) := by
          have hw_le : 1 + ‖w_u‖ ≤ 1 + |u| := by
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_neg (by linarith : u + 2 * ε < 0), abs_of_neg (by linarith : u < 0)]
            linarith
          have h2 : (1 + |u|) ^ (-(1 / 2 : ℝ)) ≤ (1 + ‖w_u‖) ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hw_le (by norm_num)
          linarith [Real.rpow_pos_of_pos (by positivity : 0 < 1 + ‖w_u‖) (-(1 / 2 : ℝ))]
        have henv_w : airyEnv w_u = 1 := by
          unfold airyEnv
          have hre0 : (w_u ^ (3 / 2 : ℂ)).re = 0 := by
            rw [re_cpow_three_halves_eq_ab w_u]
            have ha0 : airySqrtRe w_u = 0 :=
              airySqrtRe_ofReal_nonpos (by linarith : u + 2 * ε ≤ 0)
            simp [ha0]
          simp [hre0]
        have henv_s : airyEnv (ζ + ((2 * ε : ℝ) : ℂ)) ≤ Real.exp 40 := by
          have h := airyEnv_ball_le (w := w_u) (ζ := ζ + ((2 * ε : ℝ) : ℂ))
            (by rw [hsub_w, hnorm_sub]; exact hrw_le)
          rwa [henv_w, mul_one] at h
        have hpoly_s : (1 + ‖ζ + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ ≤ 4 ^ |ν₀| * (4 * |u|) ^ Nν := by
          have h1 := one_add_norm_rpow_ball_le ν₀ (w := w_u) (ζ := ζ + ((2 * ε : ℝ) : ℂ))
            (by rw [hsub_w, hnorm_sub]; exact hru_le1)
          have hw_le : 1 + ‖w_u‖ ≤ 4 * |u| := by
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_neg (by linarith : u + 2 * ε < 0)]
            linarith [abs_of_neg (by linarith : u < 0)]
          have h2 : (1 + ‖w_u‖) ^ ν₀ ≤ (4 * |u|) ^ Nν := by
            calc (1 + ‖w_u‖) ^ ν₀
                ≤ (1 + ‖w_u‖) ^ (Nν : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg w_u])
                    ((le_abs_self ν₀).trans (Nat.le_ceil |ν₀|))
              _ = (1 + ‖w_u‖) ^ Nν := Real.rpow_natCast _ _
              _ ≤ (4 * |u|) ^ Nν := pow_le_pow_left₀ (by positivity) hw_le Nν
          exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
        have hH_s : ‖H (ζ + ((2 * ε : ℝ) : ℂ))‖ ≤
            C₀ * (4 ^ |ν₀| * (4 * |u|) ^ Nν) * Real.exp 40 := by
          calc ‖H (ζ + ((2 * ε : ℝ) : ℂ))‖
              ≤ C₀ * (1 + ‖ζ + ((2 * ε : ℝ) : ℂ)‖) ^ ν₀ * airyEnv (ζ + ((2 * ε : ℝ) : ℂ)) := hb₀ _
            _ ≤ C₀ * (4 ^ |ν₀| * (4 * |u|) ^ Nν) * Real.exp 40 :=
                mul_le_mul (mul_le_mul_of_nonneg_left hpoly_s hC₀_nn) henv_s
                  (airyEnv_pos _).le (by positivity)
        unfold airySmoothReg
        rw [norm_mul]
        calc ‖airySmoothMSq ε ζ‖ * ‖H (ζ + ((2 * ε : ℝ) : ℂ))‖
            ≤ (C_m * (|u|⁻¹) ^ (2 * m_ord)) *
                (C₀ * (4 ^ |ν₀| * (4 * |u|) ^ Nν) * Real.exp 40) :=
              mul_le_mul hM_s hH_s (norm_nonneg _) (by positivity)
          _ = (C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ Nν) *
                (|u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord)) := by
              rw [mul_pow]; ring
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hru_pos
        (hReg_diff ε).differentiableOn.diffContOnCl hsphere_neg
      have hd_re : |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u| ≤
          ‖iteratedDeriv n (airySmoothReg H ε) (u : ℂ)‖ := by
        rw [iteratedDeriv_re_of_differentiable (hReg_diff ε)]
        exact Complex.abs_re_le_norm _
      have h1_plus : (1 + |u|) ^ n ≤ 4 ^ n * |u| ^ n := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) n
      have hpow_collapse : |u| ^ k * |u| ^ n * |u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord) ≤ 1 := by
        have htot : |u| ^ k * |u| ^ n * |u| ^ Nν = |u| ^ (k + n + Nν) := by
          rw [← pow_add, ← pow_add, add_assoc]
        rw [htot]
        have hle_m : k + n + Nν ≤ 2 * m_ord := by dsimp [m_ord]; omega
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle_m
        rw [hd, pow_add (|u|⁻¹) (k + n + Nν) d, ← mul_assoc (|u| ^ (k + n + Nν)), ← mul_pow,
          mul_inv_cancel₀ (by linarith), one_pow, one_mul]
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
      have hbound_u : |u| ^ k *
          |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u| ≤ C_left := by
        calc |u| ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u|
            ≤ |u| ^ k * (n.factorial *
                ((C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ Nν) *
                  (|u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord))) * (r_u ^ n)⁻¹) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact hd_re.trans (by rwa [div_eq_mul_inv] at hcauchy)
          _ ≤ |u| ^ k * (n.factorial *
                ((C_m * C₀ * 4 ^ |ν₀| * Real.exp 40 * 4 ^ Nν) *
                  (|u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord))) * (4 ^ n * |u| ^ n)) := by
              refine mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (hru_pow_inv.trans h1_plus) (by positivity))
                (by positivity)
          _ = C_left * (|u| ^ k * |u| ^ n * |u| ^ Nν * (|u|⁻¹) ^ (2 * m_ord)) := by
              dsimp [C_left]; rw [pow_add]; ring
          _ ≤ C_left * 1 := mul_le_mul_of_nonneg_left hpow_collapse (by positivity)
          _ = C_left := mul_one _
      exact hbound_u.trans ((le_max_left C_left C_right).trans (le_max_right _ _))
    · -- `5 < u`
      have hu_pos : 0 < u := by linarith
      have hsphere_pos : ∀ ζ ∈ sphere (u : ℂ) r_u,
          ‖airySmoothReg H ε ζ‖ ≤
            ((C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
              (1 + u) ^ Nν * Real.exp (-u) := by
        intro ζ hζ
        have hnorm_sub : ‖ζ - (u : ℂ)‖ = r_u := mem_sphere_iff_norm.mp hζ
        have h1 := hReg_growth ε hε0.le hε1 ζ
        have hpoly_s : (1 + ‖ζ‖) ^ ν₀ ≤ 4 ^ |ν₀| * (1 + u) ^ Nν := by
          have hp1 := one_add_norm_rpow_ball_le ν₀ (w := (u : ℂ)) (ζ := ζ)
            (by rw [hnorm_sub]; exact hru_le1)
          have hnorm_u : ‖(u : ℂ)‖ = u := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
          rw [hnorm_u] at hp1
          have hp2 : (1 + u) ^ ν₀ ≤ (1 + u) ^ Nν := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith)
              ((le_abs_self ν₀).trans (Nat.le_ceil |ν₀|))
          exact hp1.trans (mul_le_mul_of_nonneg_left hp2 (by positivity))
        have henv_s : airyEnv ζ ≤ Real.exp 40 * Real.exp (-u) := by
          have hnorm_u : ‖(u : ℂ)‖ = |u| := by rw [Complex.norm_real, Real.norm_eq_abs]
          have he1 := airyEnv_ball_le (w := (u : ℂ)) (ζ := ζ) (by
            rw [hnorm_sub, hnorm_u]; linarith)
          have he2 : airyEnv (u : ℂ) ≤ Real.exp (-u) := by
            rw [hairyEnv_nonneg_eq u hu_pos.le]
            apply Real.exp_le_exp.mpr
            have hu_ge1 : u ^ (1 : ℝ) ≤ u ^ (3 / 2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
            rw [Real.rpow_one] at hu_ge1
            linarith
          exact he1.trans (mul_le_mul_of_nonneg_left he2 (Real.exp_pos _).le)
        calc ‖airySmoothReg H ε ζ‖
            ≤ (C₀ * K_shift) * (1 + ‖ζ‖) ^ ν₀ * airyEnv ζ := h1
          _ ≤ (C₀ * K_shift) * (4 ^ |ν₀| * (1 + u) ^ Nν) * (Real.exp 40 * Real.exp (-u)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hpoly_s (by positivity)) henv_s
                (airyEnv_pos _).le (by positivity)
          _ = ((C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) * (1 + u) ^ Nν * Real.exp (-u) := by
              ring
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hru_pos
        (hReg_diff ε).differentiableOn.diffContOnCl hsphere_pos
      have hcauchy' : ‖iteratedDeriv n (airySmoothReg H ε) (u : ℂ)‖ ≤
          n.factorial * (((C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
            (1 + u) ^ Nν * Real.exp (-u)) * (r_u ^ n)⁻¹ := by
        rwa [div_eq_mul_inv] at hcauchy
      have hd_re : |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u| ≤
          ‖iteratedDeriv n (airySmoothReg H ε) (u : ℂ)‖ := by
        rw [iteratedDeriv_re_of_differentiable (hReg_diff ε)]
        exact Complex.abs_re_le_norm _
      have hu_abs_eq : |u| = u := abs_of_pos hu_pos
      have hpow_exp : (1 + u) ^ N_right * Real.exp (-u) ≤ Real.exp 1 * N_right.factorial := by
        have hpe := pow_mul_exp_neg_le N_right (x := 1 + u) (by positivity)
        calc (1 + u) ^ N_right * Real.exp (-u)
            = ((1 + u) ^ N_right * Real.exp (-(1 + u))) * Real.exp 1 := by
              rw [mul_assoc, ← Real.exp_add]; congr 2; ring
          _ ≤ N_right.factorial * Real.exp 1 :=
              mul_le_mul_of_nonneg_right hpe (Real.exp_pos _).le
          _ = Real.exp 1 * N_right.factorial := mul_comm _ _
      have hbound_u : |u| ^ k *
          |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u| ≤ C_right := by
        rw [hu_abs_eq]
        have hru_u : (r_u ^ n)⁻¹ ≤ (1 + u) ^ n := by rwa [hu_abs_eq] at hru_pow_inv
        have huk_le : u ^ k ≤ (1 + u) ^ k := pow_le_pow_left₀ hu_pos.le (by linarith) k
        calc u ^ k * |iteratedDeriv n (fun x : ℝ => (airySmoothReg H ε (x : ℂ)).re) u|
            ≤ (1 + u) ^ k * (n.factorial *
                (((C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
                  (1 + u) ^ Nν * Real.exp (-u)) * (1 + u) ^ n) := by
              refine mul_le_mul huk_le ?_ (abs_nonneg _) (by positivity)
              exact hd_re.trans (hcauchy'.trans
                (mul_le_mul_of_nonneg_left hru_u (by positivity)))
          _ = (n.factorial * (C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
                ((1 + u) ^ N_right * Real.exp (-u)) := by
              dsimp [N_right]; rw [pow_add, pow_add]; ring
          _ ≤ (n.factorial * (C₀ * K_shift) * 4 ^ |ν₀| * Real.exp 40) *
                (Real.exp 1 * N_right.factorial) :=
              mul_le_mul_of_nonneg_left hpow_exp (by positivity)
          _ = C_right := by
              dsimp [C_right]
              have hexp41 : Real.exp 40 * Real.exp 1 = Real.exp 41 := by
                rw [← Real.exp_add]; norm_num
              rw [← hexp41]; ring
      exact hbound_u.trans ((le_max_right C_left C_right).trans (le_max_right _ _))

private lemma airySmoothReg_locUnif {H : ℂ → ℂ} (hH : InAiryClass H) :
    TendstoLocallyUniformly (fun ε z => airySmoothReg H ε z) H (𝓝[>] 0) := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro z₀
  have hcont_reg : Continuous (fun p : ℝ × ℂ => airySmoothReg H p.1 p.2) := by
    unfold airySmoothReg airySmoothMSq
    exact (continuous_uncurry_airySmoothM.pow 2).mul
      (hH.1.continuous.comp (continuous_snd.add
        (Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst))))
  rw [Filter.tendsto_iff_forall_eventually_mem]
  intro V hV
  obtain ⟨δ, hδ, hVδ⟩ := Metric.mem_uniformity_dist.mp hV
  have hcont_dist : Continuous (fun p : ℝ × ℂ => dist (H p.2) (airySmoothReg H p.1 p.2)) :=
    (hH.1.continuous.comp continuous_snd).dist hcont_reg
  have hat0 : dist (H z₀) (airySmoothReg H 0 z₀) < δ := by
    simp [airySmoothReg, airySmoothMSq_zero, hδ]
  have hev : ∀ᶠ p : ℝ × ℂ in 𝓝 (0, z₀),
      p ∈ {q : ℝ × ℂ | dist (H q.2) (airySmoothReg H q.1 q.2) < δ} :=
    hcont_dist.continuousAt.preimage_mem_nhds (Iio_mem_nhds hat0)
  rw [nhds_prod_eq] at hev
  filter_upwards [hev.filter_mono (Filter.prod_mono_left _ nhdsWithin_le_nhds)] with p hp
  exact hVδ hp

private lemma continuous_fst_apply (G : ℝ → ℝ → ℂ)
    (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2)) (u : ℝ) :
    Continuous (fun ε : ℝ => G ε u) :=
  hG.comp (continuous_id'.prodMk continuous_const)

private lemma continuous_snd_apply (G : ℝ → ℝ → ℂ)
    (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2)) (ε : ℝ) :
    Continuous (fun u : ℝ => G ε u) :=
  hG.comp (continuous_const.prodMk continuous_id')

private lemma airySmoothReg_weighted_l1_tendsto {H : ℂ → ℂ} (hH : InAiryClass H)
    {C₀ ν₀ : ℝ} (hC₀_nn : 0 ≤ C₀) (hb₀ : ∀ z : ℂ, ‖H z‖ ≤ C₀ * (1 + ‖z‖) ^ ν₀ * airyEnv z)
    (hReg_int : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → Integrable (fun u : ℝ => airySmoothReg H ε (u : ℂ)))
    {Y : ℝ} (hY : 0 ≤ Y) :
    Tendsto (fun ε : ℝ =>
      ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
      (𝓝[>] 0) (𝓝 0) := by
  set K_shift : ℝ := 3 ^ |ν₀|
  have hReg_growth : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ z : ℂ,
      ‖airySmoothReg H ε z‖ ≤ (C₀ * K_shift) * (1 + ‖z‖) ^ ν₀ * airyEnv z :=
    fun ε h0 h1 z => airySmoothReg_growth hC₀_nn hb₀ h0 h1 z
  have hpos_maj_int : ∀ Y' : ℝ, 0 ≤ Y' →
      IntegrableOn (fun u : ℝ => (C₀ * K_shift) * (1 + |u|) ^ ν₀ *
        airyEnv (u : ℂ) * Real.exp (Y' * u)) (Ioi 0) :=
    fun Y' hY' => integrableOn_airySmooth_pos_maj hC₀_nn hY'
  have hcont_reg_R : Continuous (fun p : ℝ × ℝ => airySmoothReg H p.1 (p.2 : ℂ)) := by
    unfold airySmoothReg airySmoothMSq
    exact ((continuous_uncurry_airySmoothM.comp
      (continuous_fst.prodMk (Complex.continuous_ofReal.comp continuous_snd))).pow 2).mul
      (hH.1.continuous.comp ((Complex.continuous_ofReal.comp continuous_snd).add
        (Complex.continuous_ofReal.comp (continuous_const.mul continuous_fst))))
  have hK_ge1 : 1 ≤ K_shift :=
    Real.one_le_rpow (by norm_num) (abs_nonneg ν₀)
  have h_pos_tendsto : Tendsto (fun ε : ℝ =>
      ∫ u in Ioi (0 : ℝ), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
      (𝓝[>] 0) (𝓝 0) := by
    have hdom : IntegrableOn (fun u : ℝ =>
        2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u))) (Ioi 0) :=
      (hpos_maj_int Y hY).const_mul 2
    have hconv := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun ε u => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
      (f := fun _ => (0 : ℝ))
      (bound := fun u =>
        2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u)))
      (Eventually.of_forall fun ε => by
        refine Continuous.aestronglyMeasurable ?_
        exact ((continuous_snd_apply (fun ε' u' => airySmoothReg H ε' (u' : ℂ)) hcont_reg_R ε).sub
          (hH.1.continuous.comp Complex.continuous_ofReal)).norm.mul
          (Real.continuous_exp.comp (continuous_const.mul (continuous_id.max continuous_const))))
      (Filter.eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε =>
        ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), max_eq_left hu.le]
          have h1 : ‖airySmoothReg H ε (u : ℂ)‖ ≤
              (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
            simpa [Complex.norm_real, Real.norm_eq_abs] using
              hReg_growth ε hε.1.le hε.2 (u : ℂ)
          have h2 : ‖H (u : ℂ)‖ ≤ (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
            have hb_u : ‖H (u : ℂ)‖ ≤ C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
              simpa [Complex.norm_real, Real.norm_eq_abs] using hb₀ (u : ℂ)
            exact hb_u.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC₀_nn hK_ge1) (by positivity))
              (airyEnv_pos _).le)
          calc ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * u)
              ≤ (‖airySmoothReg H ε (u : ℂ)‖ + ‖H (u : ℂ)‖) * Real.exp (Y * u) :=
                mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le
            _ ≤ 2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)) * Real.exp (Y * u) :=
                mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
            _ = 2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u)) := by
                ring)
      hdom
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => by
        have ht : Tendsto (fun ε : ℝ => airySmoothReg H ε (u : ℂ)) (𝓝 0) (𝓝 (H (u : ℂ))) := by
          have hc_fn : Continuous (fun ε : ℝ => airySmoothReg H ε (u : ℂ)) :=
            continuous_fst_apply (fun ε' u' => airySmoothReg H ε' (u' : ℂ)) hcont_reg_R u
          rw [← airySmoothReg_zero H (u : ℂ)]; exact (hc_fn.continuousAt (x := 0)).tendsto
        have ht_sub := (ht.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).sub_const (H (u : ℂ))
        rw [sub_self] at ht_sub
        have ht_mul := ht_sub.norm.mul_const (Real.exp (Y * max u 0))
        rw [norm_zero, zero_mul] at ht_mul
        exact ht_mul)
    rw [integral_zero] at hconv
    exact hconv
  -- Negative half-line `Iic 0` (`max u 0 = 0`, `exp (Y * max u 0) = 1`)
  have h_neg_tendsto : Tendsto (fun ε : ℝ =>
      ∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
      (𝓝[>] 0) (𝓝 0) := by
    have htail_H : Tendsto (fun R : ℝ => ∫ v in Iic (-R + 2), ‖H (v : ℂ)‖) atTop (𝓝 0) := by
      have hconv := tendsto_integral_filter_of_dominated_convergence
        (l := atTop) (μ := volume)
        (F := fun (R : ℝ) (v : ℝ) => (Iic (-R + 2)).indicator (fun x => ‖H (x : ℂ)‖) v)
        (f := fun _ => (0 : ℝ))
        (bound := fun v => ‖H (v : ℂ)‖)
        (Eventually.of_forall fun R =>
          (hH.2.1.norm.aestronglyMeasurable.indicator measurableSet_Iic))
        (Eventually.of_forall fun R => Eventually.of_forall fun v => by
          by_cases hv : v ∈ Iic (-R + 2)
          · simp [indicator_of_mem hv]
          · simp [indicator_of_notMem hv])
        hH.2.1.norm
        (Eventually.of_forall fun v => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [Filter.eventually_gt_atTop (2 - v)] with R hR
          have hv_not : v ∉ Iic (-R + 2) := by rw [mem_Iic]; linarith
          simp [indicator_of_notMem hv_not])
      simpa [integral_indicator measurableSet_Iic] using hconv
    rw [Metric.tendsto_nhds]
    intro δ hδ
    have htail_ev := (Metric.tendsto_nhds.mp htail_H (δ / 4) (by positivity)).and
      (Filter.eventually_ge_atTop (2 : ℝ))
    obtain ⟨R, hR_int, hR_ge2⟩ := htail_ev.exists
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (setIntegral_nonneg measurableSet_Iic
      fun _ _ => norm_nonneg _)] at hR_int
    obtain ⟨M_win, hM_win⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (s := Icc (-R) 2) (hH.1.continuous.comp Complex.continuous_ofReal).continuousOn
    have hwin_tendsto : Tendsto (fun ε : ℝ =>
        ∫ u in Ioc (-R) 0, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) (𝓝[>] 0) (𝓝 0) := by
      have hdom_win : IntegrableOn (fun _ : ℝ => 2 * max M_win 0) (Ioc (-R) 0) :=
        continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have hconv := tendsto_integral_filter_of_dominated_convergence
        (l := 𝓝[>] 0) (μ := volume.restrict (Ioc (-R) 0))
        (F := fun ε u => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖)
        (f := fun _ => (0 : ℝ))
        (bound := fun _ => 2 * max M_win 0)
        (Eventually.of_forall fun ε =>
          (((continuous_snd_apply (fun ε' u' => airySmoothReg H ε' (u' : ℂ)) hcont_reg_R ε).sub
            (hH.1.continuous.comp Complex.continuous_ofReal)).norm).aestronglyMeasurable)
        (Filter.eventually_of_mem (Ioc_mem_nhdsGT zero_lt_one) fun ε hε =>
          ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => by
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
            have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
              have := norm_airySmoothMSq_neg_le_one hε.1.le (x := -u) (by linarith [hu.2])
              simpa using this
            have hreg_le : ‖airySmoothReg H ε (u : ℂ)‖ ≤ max M_win 0 := by
              unfold airySmoothReg
              rw [norm_mul]
              have hcast : (u : ℂ) + ((2 * ε : ℝ) : ℂ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
              rw [hcast]
              have hh : ‖H ((u + 2 * ε : ℝ) : ℂ)‖ ≤ max M_win 0 :=
                (hM_win (u + 2 * ε) ⟨by linarith [hu.1, hε.1],
                  by linarith [hu.2, hε.2]⟩).trans (le_max_left M_win 0)
              nlinarith [norm_nonneg (H ((u + 2 * ε : ℝ) : ℂ))]
            have hh0 : ‖H (u : ℂ)‖ ≤ max M_win 0 :=
              (hM_win u ⟨hu.1.le, by linarith [hu.2]⟩).trans (le_max_left _ _)
            calc ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖
                ≤ ‖airySmoothReg H ε (u : ℂ)‖ + ‖H (u : ℂ)‖ := norm_sub_le _ _
              _ ≤ 2 * max M_win 0 := by linarith)
        hdom_win
        (ae_restrict_of_forall_mem measurableSet_Ioc fun u _ => by
          have ht : Tendsto (fun ε : ℝ => airySmoothReg H ε (u : ℂ)) (𝓝 0) (𝓝 (H (u : ℂ))) := by
            have hc_fn : Continuous (fun ε : ℝ => airySmoothReg H ε (u : ℂ)) :=
              continuous_fst_apply (fun ε' u' => airySmoothReg H ε' (u' : ℂ)) hcont_reg_R u
            rw [← airySmoothReg_zero H (u : ℂ)]; exact (hc_fn.continuousAt (x := 0)).tendsto
          have ht_sub := (ht.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))).sub_const (H (u : ℂ))
          rw [sub_self] at ht_sub
          have htn := ht_sub.norm
          rw [norm_zero] at htn
          exact htn)
      rw [integral_zero] at hconv
      exact hconv
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one,
      Metric.tendsto_nhds.mp hwin_tendsto (δ / 2) (by positivity)] with ε hε hwin_lt
    rw [Real.dist_eq, sub_zero] at hwin_lt ⊢
    have hnn_int : 0 ≤ ∫ u in Iic (0 : ℝ),
        ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0) :=
      setIntegral_nonneg measurableSet_Iic fun _ _ => by positivity
    rw [abs_of_nonneg hnn_int]
    have heq_Iic : (∫ u in Iic (0 : ℝ),
        ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0)) =
        ∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ := by
      refine setIntegral_congr_fun measurableSet_Iic fun u (hu : u ≤ 0) => ?_
      rw [max_eq_right hu, mul_zero, Real.exp_zero, mul_one]
    rw [heq_Iic]
    have hint_diff : Integrable (fun u : ℝ => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) :=
      ((hReg_int ε hε.1.le hε.2).sub hH.2.1).norm
    have hsplit : (∫ u in Iic (0 : ℝ), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) =
        (∫ u in Iic (-R), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) +
          ∫ u in Ioc (-R) 0, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ := by
      have hdisj : Disjoint (Iic (-R)) (Ioc (-R) 0) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2.1
      rw [← Iic_union_Ioc_eq_Iic (by linarith : -R ≤ 0),
        setIntegral_union hdisj measurableSet_Ioc hint_diff.integrableOn hint_diff.integrableOn]
    have hfar_lt : (∫ u in Iic (-R), ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) < δ / 2 := by
      have hpt_le : ∀ u ≤ -R, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ ≤
          ‖H ((u + 2 * ε : ℝ) : ℂ)‖ + ‖H (u : ℂ)‖ := by
        intro u hu
        have hM1 : ‖airySmoothMSq ε (u : ℂ)‖ ≤ 1 := by
          have := norm_airySmoothMSq_neg_le_one hε.1.le (x := -u) (by linarith)
          simpa using this
        have hcast : (u : ℂ) + ((2 * ε : ℝ) : ℂ) = ((u + 2 * ε : ℝ) : ℂ) := by push_cast; rfl
        have hmul1 : ‖airySmoothMSq ε (u : ℂ)‖ * ‖H ((u + 2 * ε : ℝ) : ℂ)‖ ≤
            ‖H ((u + 2 * ε : ℝ) : ℂ)‖ :=
          mul_le_of_le_one_left (norm_nonneg _) hM1
        unfold airySmoothReg
        rw [hcast]
        exact (norm_sub_le _ _).trans (by rw [norm_mul]; linarith)
      have hdom1 : Integrable (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖) :=
        hH.2.1.norm.comp_add_right (2 * ε)
      have hmono := setIntegral_mono_on hint_diff.integrableOn
        (show IntegrableOn (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖ + ‖H (u : ℂ)‖) (Iic (-R))
          from hdom1.integrableOn.add hH.2.1.norm.integrableOn)
        measurableSet_Iic hpt_le
      rw [integral_add hdom1.integrableOn hH.2.1.norm.integrableOn] at hmono
      have hshift_eq : (∫ u in Iic (-R), ‖H ((u + 2 * ε : ℝ) : ℂ)‖) =
          ∫ v in Iic (-R + 2 * ε), ‖H (v : ℂ)‖ := by
        rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
        have hind : (Iic (-R)).indicator (fun u : ℝ => ‖H ((u + 2 * ε : ℝ) : ℂ)‖) =
            fun u : ℝ => (Iic (-R + 2 * ε)).indicator (fun v : ℝ => ‖H (v : ℂ)‖) (u + 2 * ε) := by
          ext u
          by_cases hu : u ≤ -R
          · have hv : u + 2 * ε ≤ -R + 2 * ε := by linarith
            rw [indicator_of_mem hu, indicator_of_mem hv]
          · have hv : ¬ (u + 2 * ε ≤ -R + 2 * ε) := by linarith
            rw [indicator_of_notMem hu, indicator_of_notMem hv]
        rw [hind]
        exact integral_add_right_eq_self
          (fun v : ℝ => (Iic (-R + 2 * ε)).indicator (fun x => ‖H (x : ℂ)‖) v) (2 * ε)
      have hsub1 : (∫ v in Iic (-R + 2 * ε), ‖H (v : ℂ)‖) ≤ ∫ v in Iic (-R + 2), ‖H (v : ℂ)‖ :=
        setIntegral_mono_set hH.2.1.norm.integrableOn
          (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall fun v (hv : v ≤ -R + 2 * ε) => by
            change v ≤ -R + 2; linarith [hε.2])
      have hsub2 : (∫ u in Iic (-R), ‖H (u : ℂ)‖) ≤ ∫ v in Iic (-R + 2), ‖H (v : ℂ)‖ :=
        setIntegral_mono_set hH.2.1.norm.integrableOn
          (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall fun v (hv : v ≤ -R) => by
            change v ≤ -R + 2; linarith)
      rw [hshift_eq] at hmono
      linarith
    have hwin_lt' : (∫ u in Ioc (-R) 0, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖) < δ / 2 :=
      (le_abs_self _).trans_lt hwin_lt
    rw [hsplit]
    linarith
  -- Combine `Iic 0` and `Ioi 0`
  have hsum := h_neg_tendsto.add h_pos_tendsto
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
  have hint_neg : IntegrableOn
      (fun u : ℝ => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0)) (Iic 0) := by
    refine (((hReg_int ε hε.1.le hε.2).sub hH.2.1).norm.integrableOn).congr_fun
      (fun u (hu : u ≤ 0) => ?_) measurableSet_Iic
    dsimp only [Pi.sub_apply]
    rw [max_eq_right hu, mul_zero, Real.exp_zero, mul_one]
  have hint_pos : IntegrableOn
      (fun u : ℝ => ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0)) (Ioi 0) := by
    refine ((hpos_maj_int Y hY).const_mul 2).mono' ?_
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) => ?_)
    · refine Continuous.aestronglyMeasurable ?_ |>.restrict
      exact ((continuous_snd_apply (fun ε' u' => airySmoothReg H ε' (u' : ℂ)) hcont_reg_R ε).sub
        (hH.1.continuous.comp Complex.continuous_ofReal)).norm.mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_id.max continuous_const)))
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), max_eq_left hu.le]
      have h1 : ‖airySmoothReg H ε (u : ℂ)‖ ≤
          (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using hReg_growth ε hε.1.le hε.2 (u : ℂ)
      have h2 : ‖H (u : ℂ)‖ ≤ (C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
        have hb_u : ‖H (u : ℂ)‖ ≤ C₀ * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) := by
          simpa [Complex.norm_real, Real.norm_eq_abs] using hb₀ (u : ℂ)
        exact hb_u.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC₀_nn hK_ge1) (by positivity))
          (airyEnv_pos _).le)
      calc ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * u)
          ≤ (‖airySmoothReg H ε (u : ℂ)‖ + ‖H (u : ℂ)‖) * Real.exp (Y * u) :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le
        _ ≤ 2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ)) * Real.exp (Y * u) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
        _ = 2 * ((C₀ * K_shift) * (1 + |u|) ^ ν₀ * airyEnv (u : ℂ) * Real.exp (Y * u)) := by ring
  have hdisj0 : Disjoint (Iic (0 : ℝ)) (Ioi (0 : ℝ)) :=
    Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
  rw [← setIntegral_union hdisj0 measurableSet_Ioi hint_neg hint_pos,
    Iic_union_Ioi, setIntegral_univ]

/-- **Lemma `lem:al-smooth`** (`ce_airy_lp_proofs.tex` lines 47–77):
smooth regularization `H_ε(z) = M_ε(z) H(z + 2ε)` inside `𝒢 ∩ 𝓢(ℝ)`. -/
theorem lem_al_smooth {H : ℂ → ℂ} (hH : InAiryClass H) :
    (∀ ε ∈ Ioc (0 : ℝ) 1,
      Differentiable ℂ (airySmoothMSq ε) ∧
      (∀ u : ℝ, (airySmoothMSq ε (u : ℂ)).im = 0 ∧ 0 ≤ (airySmoothMSq ε (u : ℂ)).re) ∧
      (∀ x : ℝ, 0 ≤ x → ‖airySmoothMSq ε ((-x : ℝ) : ℂ)‖ ≤ 1) ∧
      (∀ z : ℂ, ‖airySmoothMSq ε z‖ ≤ Real.exp (2 * ε * airySqrtRe z)) ∧
      InAiryClass (airySmoothReg H ε) ∧
      ((∀ u : ℝ, (H (u : ℂ)).im = 0) → ∀ u : ℝ, (airySmoothReg H ε (u : ℂ)).im = 0) ∧
      ∃ S_ε : SchwartzMap ℝ ℝ, ∀ u : ℝ, S_ε u = (airySmoothReg H ε (u : ℂ)).re) ∧
    TendstoLocallyUniformly (fun ε z => airySmoothReg H ε z) H (𝓝[>] 0) ∧
    (∀ Y : ℝ, 0 ≤ Y →
      Tendsto (fun ε : ℝ =>
        ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ) - H (u : ℂ)‖ * Real.exp (Y * max u 0))
        (𝓝[>] 0) (𝓝 0)) ∧
    ∃ C_H : ℝ, 0 ≤ C_H ∧
      (∀ ε ∈ Ioc (0 : ℝ) 1, (∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖) ≤ C_H) ∧
      ∀ s : ℝ, 0 < s → ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ y : ℝ, 0 ≤ y →
        |airyLaplace (fun u => (airySmoothReg H ε ((u + s : ℝ) : ℂ)).re) y| ≤
          C_H * Real.exp (-s * y) := by
  obtain ⟨C₀, ν₀, hC₀_nn, hb₀⟩ := hH.2.2.1
  set K_shift : ℝ := 3 ^ |ν₀|
  have hK_pos : 0 < K_shift := by positivity
  obtain ⟨C_H, hC_H_nn, hReg_int_and_l1⟩ := airySmoothReg_int_and_l1 hH hC₀_nn hb₀
  have hReg_diff : ∀ ε : ℝ, Differentiable ℂ (airySmoothReg H ε) :=
    differentiable_airySmoothReg hH.1
  have hReg_im_zero : ∀ ε : ℝ, ∀ u : ℝ, (airySmoothReg H ε (u : ℂ)).im = 0 :=
    airySmoothReg_im_zero hH.2.2.2
  refine ⟨?_, airySmoothReg_locUnif hH,
    fun Y hY => airySmoothReg_weighted_l1_tendsto hH hC₀_nn hb₀
      (fun ε h0 h1 => (hReg_int_and_l1 ε h0 h1).1) hY,
    C_H, hC_H_nn, fun ε hε => (hReg_int_and_l1 ε hε.1.le hε.2).2, ?_⟩
  · intro ε ⟨hε0, hε1⟩
    have hcl : InAiryClass (airySmoothReg H ε) :=
      ⟨hReg_diff ε, (hReg_int_and_l1 ε hε0.le hε1).1,
        ⟨C₀ * K_shift, ν₀, by positivity, airySmoothReg_growth hC₀_nn hb₀ hε0.le hε1⟩,
        hReg_im_zero ε⟩
    exact ⟨differentiable_airySmoothMSq ε, airySmoothMSq_ofReal_im_and_nonneg ε,
      fun x hx => norm_airySmoothMSq_neg_le_one hε0.le hx,
      norm_airySmoothMSq_le hε0.le, hcl, fun _ => hReg_im_zero ε,
      airySmoothReg_schwartz hH hC₀_nn hb₀ hε0 hε1⟩
  · -- Part 4b: `(eq:al-shift-bound)`
    intro s hs ε hε y hy
    have hcl_ε : InAiryClass (airySmoothReg H ε) :=
      ⟨hReg_diff ε, (hReg_int_and_l1 ε hε.1.le hε.2).1,
        ⟨C₀ * K_shift, ν₀, by positivity, airySmoothReg_growth hC₀_nn hb₀ hε.1.le hε.2⟩,
        hReg_im_zero ε⟩
    have hshift_lap : airyLaplace (fun u => (airySmoothReg H ε ((u + s : ℝ) : ℂ)).re) y =
        Real.exp (-s * y) * airyLaplace (fun u => (airySmoothReg H ε (u : ℂ)).re) y := by
      unfold airyLaplace
      have hlin : ∀ u : ℝ, (airySmoothReg H ε ((u + s : ℝ) : ℂ)).re * Real.exp (y * u) =
          Real.exp (-s * y) *
            ((airySmoothReg H ε ((u + s : ℝ) : ℂ)).re * Real.exp (y * (u + s))) := by
        intro u
        rw [mul_comm (Real.exp (-s * y)), mul_assoc, ← Real.exp_add]
        congr 2; ring
      simp_rw [hlin]
      rw [integral_const_mul, integral_add_right_eq_self
        (fun v : ℝ => (airySmoothReg H ε (v : ℂ)).re * Real.exp (y * v)) s]
      ring
    have hub1 : airyLaplace (fun u => (airySmoothReg H ε (u : ℂ)).re) y ≤
        ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖ :=
      airyLaplace_re_le_l1 hcl_ε hy
    have hub2 : -airyLaplace (fun u => (airySmoothReg H ε (u : ℂ)).re) y ≤
        ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖ := by
      have hneg := airyLaplace_re_le_l1 hcl_ε.neg hy
      have heq_neg : airyLaplace (fun u => ((-airySmoothReg H ε (u : ℂ)).re)) y =
          -airyLaplace (fun u => (airySmoothReg H ε (u : ℂ)).re) y := by
        unfold airyLaplace
        simp only [Complex.neg_re, neg_mul, integral_neg, mul_neg]
      have hnorm_neg : (∫ u : ℝ, ‖-airySmoothReg H ε (u : ℂ)‖) =
          ∫ u : ℝ, ‖airySmoothReg H ε (u : ℂ)‖ := by simp
      rwa [heq_neg, hnorm_neg] at hneg
    have hl1_le := (hReg_int_and_l1 ε hε.1.le hε.2).2
    rw [hshift_lap, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, hub1.trans hl1_le⟩)
      (Real.exp_pos _).le

/-- info: 'FormalResearch.SignUncertainty.lem_al_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_al_smooth


end FormalResearch.SignUncertainty
