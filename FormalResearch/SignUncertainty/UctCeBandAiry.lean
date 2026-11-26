module

public import FormalResearch.SignUncertainty.UctCeBandRef
public import FormalResearch.SignUncertainty.UctCeBandFarRef
public import FormalResearch.SignUncertainty.StripAdmissLift
public import FormalResearch.SignUncertainty.StripGExpansion
public import FormalResearch.SignUncertainty.CtOuter
public import FormalResearch.CohnElkies.ComplexEdgePhase
public import FormalResearch.CohnElkies.PreEdgeAndSplineFloor

/-!
# `uct:ce-band` (1): Airy-window lower bound

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:ce-band` (1),
Airy-window clause (`-U ≤ S_eff(L) ≤ S_w`, `h_norm^{ĥ}(L) ≥ -C_U c^{-4/3}`).

Main results:
* `half_disc_zero_of_real_segment_zero`: boundary uniqueness on a closed lower half-disc
  `{z | ‖z‖ ≤ r ∧ z.im ≤ 0}` for functions continuous on the half-disc, holomorphic on its
  interior, and vanishing on `[-r, r]`.
* `uct_hhat_ref_shifted`: shifting `(uct:hhat-ref-id)` from `u ∈ ℝ` to `u = v - i`.
* `uct_ce_band_airy`: under the hypotheses of Lemma `uct:ce-band` (1), on the Airy window
  `-U ≤ c^{2/3} L / π² ≤ S_w`, `h_norm^{ĥ}(L)` is real and satisfies
  `(uctHnormCE c L A).re ≥ -C_U c^{-4/3}` uniformly in `c ≥ 60`, `L`, `W`, `A`, `A_ext`.

Class: proved, unconditional.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-! ### Section 1: Lower half-disc boundary uniqueness -/

/-- Differentiating a Cauchy-type segment integral `w ↦ ∫ t in a..b, g t / (γ t - w)` under the
integral sign at any `w` off the image `γ '' uIcc a b`. -/
private lemma hasDerivAt_cauchy_seg {a b : ℝ} {g γ : ℝ → ℂ} {w : ℂ}
    (hg : ContinuousOn g (uIcc a b)) (hγ : ContinuousOn γ (uIcc a b))
    (hne : ∀ t ∈ uIcc a b, γ t ≠ w) :
    HasDerivAt (fun z : ℂ => ∫ t in a..b, g t / (γ t - z))
      (∫ t in a..b, g t / (γ t - w) ^ 2) w := by
  have hcomp : IsCompact (uIcc a b) := isCompact_uIcc
  have hdist : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ uIcc a b, δ ≤ ‖γ t - w‖ := by
    have hcont : ContinuousOn (fun t => ‖γ t - w‖) (uIcc a b) :=
      (hγ.sub continuousOn_const).norm
    obtain ⟨t₀, ht₀, hmin⟩ := hcomp.exists_isMinOn nonempty_uIcc hcont
    exact ⟨‖γ t₀ - w‖, norm_pos_iff.mpr (sub_ne_zero.mpr (hne t₀ ht₀)), fun t ht => hmin ht⟩
  obtain ⟨δ, hδ_pos, hδ⟩ := hdist
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hg
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM a left_mem_uIcc)
  have hdist_ball : ∀ t ∈ uIcc a b, ∀ z ∈ Metric.ball w (δ / 2), δ / 2 ≤ ‖γ t - z‖ := by
    intro t ht z hz
    have hzw : ‖z - w‖ < δ / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h1 := hδ t ht
    have h2 : ‖γ t - w‖ ≤ ‖γ t - z‖ + ‖z - w‖ := by
      simpa [sub_add_sub_cancel] using norm_add_le (γ t - z) (z - w)
    linarith
  have h1 := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := a) (b := b) (μ := volume)
    (F := fun z t => g t / (γ t - z))
    (F' := fun z t => g t / (γ t - z) ^ 2)
    (s := Metric.ball w (δ / 2)) (x₀ := w)
    (bound := fun _ => M / (δ / 2) ^ 2)
    (Metric.ball_mem_nhds w (half_pos hδ_pos))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds w (half_pos hδ_pos)) fun z hz => by
      have hcont_z : ContinuousOn (fun t => g t / (γ t - z)) (uIcc a b) :=
        hg.div (hγ.sub continuousOn_const) fun t ht =>
          norm_pos_iff.mp (lt_of_lt_of_le (half_pos hδ_pos) (hdist_ball t ht z hz))
      exact (hcont_z.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
    ((hg.div (hγ.sub continuousOn_const) fun t ht => sub_ne_zero.mpr (hne t ht)).intervalIntegrable)
    (((hg.div ((hγ.sub continuousOn_const).pow 2) fun t ht =>
      pow_ne_zero 2 (sub_ne_zero.mpr (hne t ht))).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
      measurableSet_uIoc)
    (Eventually.of_forall fun t ht z hz => by
      have htu : t ∈ uIcc a b := Set.uIoc_subset_uIcc ht
      rw [norm_div, norm_pow]
      have hd : δ / 2 ≤ ‖γ t - z‖ := hdist_ball t htu z hz
      exact div_le_div₀ hM_nn (hM t htu) (pow_pos (half_pos hδ_pos) 2)
        (pow_le_pow_left₀ (half_pos hδ_pos).le hd 2))
    intervalIntegrable_const
    (Eventually.of_forall fun t ht z hz => by
      have htu : t ∈ uIcc a b := Set.uIoc_subset_uIcc ht
      have hne_z : γ t - z ≠ 0 :=
        norm_pos_iff.mp (lt_of_lt_of_le (half_pos hδ_pos) (hdist_ball t htu z hz))
      have hsub : HasDerivAt (fun u : ℂ => γ t - u) (-1) z := (hasDerivAt_id z).const_sub (γ t)
      have hinv := hsub.inv hne_z
      have hmul := hinv.const_mul (g t)
      refine hmul.congr_deriv ?_
      simp [div_eq_mul_inv, _root_.sq])
  exact h1.2

/-- Boundary uniqueness on a closed lower half-disc `{z | ‖z‖ ≤ r ∧ z.im ≤ 0}`:
a function continuous on the closed lower half-disc, holomorphic on its open interior, and
vanishing on the real diameter `[-r, r]` vanishes identically on the open lower half-disc. -/
theorem half_disc_zero_of_real_segment_zero {r : ℝ} (hr : 0 < r) {F : ℂ → ℂ}
    (hcont : ContinuousOn F {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0})
    (hhol : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < r ∧ z.im < 0})
    (hreal : ∀ x : ℝ, |x| ≤ r → F (x : ℂ) = 0) :
    ∀ z : ℂ, ‖z‖ < r → z.im < 0 → F z = 0 := by
  intro z₀ hz₀_norm hz₀_im
  set δ : ℝ := min ((r - ‖z₀‖) / 4) ((-z₀.im) / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ (r - ‖z₀‖) / 4 := min_le_left _ _
  have hδ2 : δ ≤ (-z₀.im) / 2 := min_le_right _ _
  set a : ℝ := z₀.re - δ
  set b : ℝ := z₀.re + δ
  set c : ℝ := z₀.im - δ
  set d : ℝ := δ
  have hab : a < b := by dsimp [a, b]; linarith
  have hc_lt : c < z₀.im := by dsimp [c]; linarith
  have hrect_ball : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, ‖(x : ℂ) + (y : ℂ) * Complex.I‖ < r := by
    intro x hx y hy
    have hx' : |x - z₀.re| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hy' : |y| ≤ |z₀.im| + δ := by
      rw [abs_of_neg hz₀_im, abs_le]
      constructor <;> linarith [hy.1, hy.2, hδ2]
    have hnorm_sq : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖z₀‖ + 2 * δ := by
      have h1 : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖((x - z₀.re : ℝ) : ℂ)‖ + ‖(z₀.re : ℂ) + (y : ℂ) * Complex.I‖ := by
        rw [show (x : ℂ) + (y : ℂ) * Complex.I = ((x - z₀.re : ℝ) : ℂ) + ((z₀.re : ℂ) + (y : ℂ) * Complex.I) by push_cast; ring]
        exact norm_add_le _ _
      have h2 : ‖((x - z₀.re : ℝ) : ℂ)‖ ≤ δ := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hx'
      have h3 : ‖(z₀.re : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖z₀‖ + δ := by
        have hsq : ‖(z₀.re : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 ≤ (‖z₀‖ + δ) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
            Complex.mul_im, zero_add]
          have hz_sq : z₀.re ^ 2 + z₀.im ^ 2 = ‖z₀‖ ^ 2 := by
            rw [Complex.sq_norm, Complex.normSq_apply]; ring
          have hy_sq : y ^ 2 ≤ (|z₀.im| + δ) ^ 2 := by
            rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) hy' 2
          have him_le : |z₀.im| ≤ ‖z₀‖ := Complex.abs_im_le_norm z₀
          nlinarith [sq_abs z₀.im, hz_sq, hy_sq, him_le, hδ_pos]
        nlinarith [norm_nonneg ((z₀.re : ℂ) + (y : ℂ) * Complex.I), norm_nonneg z₀, hδ_pos]
      linarith
    linarith
  have hrect_half : ∀ x ∈ Icc a b, ∀ y ∈ Icc c 0,
      ((x : ℂ) + (y : ℂ) * Complex.I) ∈ {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0} := by
    intro x hx y hy
    exact ⟨(hrect_ball x hx y ⟨hy.1, hy.2.trans hδ_pos.le⟩).le, by simpa using hy.2⟩
  -- Define the 3-sided Cauchy integral `H(w)` on the open rectangle `U = (a, b) × (c, d)`:
  let H : ℂ → ℂ := fun w =>
    (∫ x in a..b, F ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I - w)) +
    Complex.I * (∫ y in c..0, F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - w)) -
    Complex.I * (∫ y in c..0, F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - w))
  let U : Set ℂ := {w : ℂ | a < w.re ∧ w.re < b ∧ c < w.im ∧ w.im < d}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hU_conv : Convex ℝ U := by
    intro u hu v hv s t hs ht hst
    obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
    obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
    have hst_lt : ∀ x y z : ℝ, z < x → z < y → z < s * x + t * y := fun x y z h1 h2 => by
      rcases eq_or_lt_of_le hs with rfl | hs'
      · simp at hst; subst hst; simpa using h2
      · have hsz : s * z < s * x := mul_lt_mul_of_pos_left h1 hs'
        have htz : t * z ≤ t * y := mul_le_mul_of_nonneg_left h2.le ht
        have hz : s * z + t * z = z := by linear_combination z * hst
        linarith
    have hst_gt : ∀ x y z : ℝ, x < z → y < z → s * x + t * y < z := fun x y z h1 h2 => by
      rcases eq_or_lt_of_le hs with rfl | hs'
      · simp at hst; subst hst; simpa using h2
      · have hsz : s * x < s * z := mul_lt_mul_of_pos_left h1 hs'
        have htz : t * y ≤ t * z := mul_le_mul_of_nonneg_left h2.le ht
        have hz : s * z + t * z = z := by linear_combination z * hst
        linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact hst_lt u.re v.re a hu1 hv1
    · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      exact hst_gt u.re v.re b hu2 hv2
    · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      exact hst_lt u.im v.im c hu3 hv3
    · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      exact hst_gt u.im v.im d hu4 hv4
  have hH_diff : DifferentiableOn ℂ H U := fun w hw => by
    have hbot : HasDerivAt (fun z => ∫ x in a..b, F ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I - z)) _ w :=
      hasDerivAt_cauchy_seg
        (hcont.comp (by fun_prop) fun x hx => by
          rw [uIcc_of_le hab.le] at hx; exact hrect_half x hx c ⟨le_rfl, by linarith⟩)
        (by fun_prop)
        (fun x _ h0 => by have := congrArg Complex.im h0; simp at this; linarith [hw.2.2.1])
    have hright : HasDerivAt (fun z => ∫ y in c..0, F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z)) _ w :=
      hasDerivAt_cauchy_seg
        (hcont.comp (by fun_prop) fun y hy => by
          rw [uIcc_of_le (by linarith : c ≤ 0)] at hy; exact hrect_half b ⟨hab.le, le_rfl⟩ y hy)
        (by fun_prop)
        (fun y _ h0 => by have := congrArg Complex.re h0; simp at this; linarith [hw.2.1])
    have hleft : HasDerivAt (fun z => ∫ y in c..0, F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z)) _ w :=
      hasDerivAt_cauchy_seg
        (hcont.comp (by fun_prop) fun y hy => by
          rw [uIcc_of_le (by linarith : c ≤ 0)] at hy; exact hrect_half a ⟨le_rfl, hab.le⟩ y hy)
        (by fun_prop)
        (fun y _ h0 => by have := congrArg Complex.re h0; simp at this; linarith [hw.1])
    exact ((hbot.add (hright.const_mul Complex.I)).sub (hleft.const_mul Complex.I)).differentiableAt.differentiableWithinAt
  -- For `w ∈ U` with `0 < w.im`, `H w = 0` by Cauchy-Goursat on `[a, b] × [c, 0]`:
  have hH_upper : ∀ w ∈ U, 0 < w.im → H w = 0 := fun w _ hw_im => by
    let z₁ : ℂ := ⟨a, c⟩
    let z₂ : ℂ := ⟨b, 0⟩
    have hrec_eq : uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im = {z : ℂ | z.re ∈ Icc a b ∧ z.im ∈ Icc c 0} := by
      ext z; simp [z₁, z₂, Complex.mem_reProdIm, uIcc_of_le hab.le, uIcc_of_le (by linarith : c ≤ 0)]
    have hne_rec : ∀ z ∈ uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im, z - w ≠ 0 := by
      intro z hz h0
      rw [hrec_eq] at hz
      have := congrArg Complex.im (sub_eq_zero.mp h0)
      linarith [hz.2.2]
    have hCG := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      (f := fun z => F z / (z - w)) z₁ z₂
      ((hcont.mono fun z hz => by
        rw [hrec_eq] at hz
        have := hrect_half z.re hz.1 z.im hz.2
        simpa [Complex.re_add_im] using this).div
        (continuousOn_id.sub continuousOn_const) hne_rec)
      ((hhol.mono fun z hz => by
        rw [Complex.mem_reProdIm] at hz
        have hre_oo : z.re ∈ Ioo a b := by
          have h1 : z.re ∈ uIoo a b := hz.1
          rwa [uIoo_of_lt hab] at h1
        have him_oo : z.im ∈ Ioo c 0 := by
          have h2 : z.im ∈ uIoo c 0 := hz.2
          rwa [uIoo_of_lt (by linarith : c < 0)] at h2
        exact ⟨by simpa [Complex.re_add_im] using hrect_ball z.re ⟨hre_oo.1.le, hre_oo.2.le⟩ z.im ⟨him_oo.1.le, him_oo.2.le.trans hδ_pos.le⟩, him_oo.2⟩).div
        (differentiableOn_id.sub (differentiableOn_const w))
        (fun z hz => hne_rec z (by
          rw [Complex.mem_reProdIm] at hz ⊢
          have hre_oo : z.re ∈ Ioo a b := by
            have h1 : z.re ∈ uIoo a b := hz.1
            rwa [uIoo_of_lt hab] at h1
          have him_oo : z.im ∈ Ioo c 0 := by
            have h2 : z.im ∈ uIoo c 0 := hz.2
            rwa [uIoo_of_lt (by linarith : c < 0)] at h2
          exact ⟨by show z.re ∈ uIcc a b; rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hre_oo,
                 by show z.im ∈ uIcc c 0; rw [uIcc_of_le (by linarith : c ≤ 0)]; exact Ioo_subset_Icc_self him_oo⟩)))
    have htop : ∫ x in a..b, F ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - w) = 0 := by
      have h0 : ∫ x in a..b, F ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I - w) =
          ∫ _ in a..b, (0 : ℂ) := intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le hab.le] at hx
        have hx_le : |x| ≤ r := by
          have := hrect_ball x hx 0 ⟨by linarith, hδ_pos.le⟩
          simpa [Complex.norm_real, Real.norm_eq_abs] using this.le
        simp [hreal x hx_le]
      rw [h0, intervalIntegral.integral_zero]
    simp only [z₁, z₂, smul_eq_mul] at hCG
    rw [htop, sub_zero] at hCG
    exact hCG
  -- By identity theorem on the open convex rectangle `U`, `H z₀ = 0`:
  have hHz₀ : H z₀ = 0 := by
    let w₁ : ℂ := ⟨z₀.re, δ / 2⟩
    have hw₁_U : w₁ ∈ U := ⟨by simp [w₁, a]; linarith, by simp [w₁, b]; linarith,
      by simp [w₁, c]; linarith, by simp [w₁, d]; linarith⟩
    have hz₀_U : z₀ ∈ U := ⟨by simp [a]; linarith, by simp [b]; linarith, hc_lt, by dsimp [d]; linarith⟩
    have hev : H =ᶠ[𝓝 w₁] (fun _ => 0) := by
      have hopen2 : IsOpen (U ∩ {w : ℂ | 0 < w.im}) := hU_open.inter (isOpen_lt continuous_const Complex.continuous_im)
      filter_upwards [hopen2.mem_nhds ⟨hw₁_U, by simp [w₁]; linarith⟩] with w hw
      exact hH_upper w hw.1 hw.2
    exact (hH_diff.analyticOnNhd hU_open).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hU_conv.isPreconnected hw₁_U hev hz₀_U
  -- For `0 < ε < δ / 2`, Cauchy-Goursat on `R_ε = [a, b] × [c, -ε]` applied to `dslope F z₀`:
  have hcauchy_eps : ∀ ε : ℝ, 0 < ε → ε < δ / 2 →
      F z₀ * ((∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - z₀)⁻¹) -
              (∫ x in a..b, ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)⁻¹) +
              Complex.I * (∫ y in c..(-ε), ((b : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹) -
              Complex.I * (∫ y in c..(-ε), ((a : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹)) =
      (∫ x in a..b, F ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I - z₀)) -
      (∫ x in a..b, F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)) +
      Complex.I * (∫ y in c..(-ε), F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z₀)) -
      Complex.I * (∫ y in c..(-ε), F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z₀)) := by
    intro ε hε0 hε1
    let z₁ : ℂ := ⟨a, c⟩
    let z₂ : ℂ := ⟨b, -ε⟩
    have hc_le_neg : c ≤ -ε := by dsimp [c]; linarith
    have hsub_open : uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im ⊆ {z : ℂ | ‖z‖ < r ∧ z.im < 0} := by
      intro z hz
      simp only [z₁, z₂, Complex.mem_reProdIm, uIcc_of_le hab.le, uIcc_of_le hc_le_neg] at hz
      refine ⟨by simpa [Complex.re_add_im] using hrect_ball z.re hz.1 z.im ⟨hz.2.1, by linarith [hz.2.2]⟩,
        by linarith [hz.2.2]⟩
    have hopen_hd : IsOpen {z : ℂ | ‖z‖ < r ∧ z.im < 0} :=
      (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt Complex.continuous_im continuous_const)
    have hdslope_diff : DifferentiableOn ℂ (dslope F z₀) {z : ℂ | ‖z‖ < r ∧ z.im < 0} :=
      (differentiableOn_dslope (hopen_hd.mem_nhds ⟨hz₀_norm, hz₀_im⟩)).mpr hhol
    have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (f := dslope F z₀) z₁ z₂ (hdslope_diff.mono hsub_open)
    have hdslope_eq : ∀ z : ℂ, z ≠ z₀ → dslope F z₀ z = F z / (z - z₀) - F z₀ * (z - z₀)⁻¹ := fun z hz => by
      rw [dslope_of_ne _ hz, slope_def_field]; ring
    have hbot_eq : ∫ x in a..b, dslope F z₀ ((x : ℂ) + (c : ℂ) * Complex.I) =
        (∫ x in a..b, F ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I - z₀)) -
        F z₀ * (∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - z₀)⁻¹) := by
      have hne : ∀ x ∈ uIcc a b, (x : ℂ) + (c : ℂ) * Complex.I ≠ z₀ := fun x _ h0 => by
        have := congrArg Complex.im h0; simp at this; linarith
      have hi1 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I - z₀)) volume a b :=
        ((hcont.comp (by fun_prop) fun x hx => by rw [uIcc_of_le hab.le] at hx; exact hrect_half x hx c ⟨le_rfl, by linarith⟩).div
          (by fun_prop) (fun x hx => sub_ne_zero.mpr (hne x hx))).intervalIntegrable
      have hi2 : IntervalIntegrable (fun x : ℝ => F z₀ * ((x : ℂ) + (c : ℂ) * Complex.I - z₀)⁻¹) volume a b :=
        (continuousOn_const.mul ((by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I - z₀) (uIcc a b)).inv₀
          (fun x hx => sub_ne_zero.mpr (hne x hx)))).intervalIntegrable
      rw [intervalIntegral.integral_congr fun x hx => hdslope_eq _ (hne x hx),
        intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
    have htop_eq : ∫ x in a..b, dslope F z₀ ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) =
        (∫ x in a..b, F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)) -
        F z₀ * (∫ x in a..b, ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)⁻¹) := by
      have hne : ∀ x ∈ uIcc a b, (x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I ≠ z₀ := fun x _ h0 => by
        have := congrArg Complex.im h0; simp at this; linarith [hδ2]
      have hi1 : IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)) volume a b :=
        ((hcont.comp (by fun_prop) fun x hx => by rw [uIcc_of_le hab.le] at hx; exact hrect_half x hx (-ε) ⟨hc_le_neg, by linarith⟩).div
          (by fun_prop) (fun x hx => sub_ne_zero.mpr (hne x hx))).intervalIntegrable
      have hi2 : IntervalIntegrable (fun x : ℝ => F z₀ * ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)⁻¹) volume a b :=
        (continuousOn_const.mul ((by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀) (uIcc a b)).inv₀
          (fun x hx => sub_ne_zero.mpr (hne x hx)))).intervalIntegrable
      rw [intervalIntegral.integral_congr fun x hx => hdslope_eq _ (hne x hx),
        intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
    have hright_eq : ∫ y in c..(-ε), dslope F z₀ ((b : ℂ) + (y : ℂ) * Complex.I) =
        (∫ y in c..(-ε), F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z₀)) -
        F z₀ * (∫ y in c..(-ε), ((b : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹) := by
      have hne : ∀ y ∈ uIcc c (-ε), (b : ℂ) + (y : ℂ) * Complex.I ≠ z₀ := fun y _ h0 => by
        have := congrArg Complex.re h0; simp [b] at this; linarith
      have hi1 : IntervalIntegrable (fun y : ℝ => F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z₀)) volume c (-ε) :=
        ((hcont.comp (by fun_prop) fun y hy => by rw [uIcc_of_le hc_le_neg] at hy; exact hrect_half b ⟨hab.le, le_rfl⟩ y ⟨hy.1, by linarith [hy.2]⟩).div
          (by fun_prop) (fun y hy => sub_ne_zero.mpr (hne y hy))).intervalIntegrable
      have hi2 : IntervalIntegrable (fun y : ℝ => F z₀ * ((b : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹) volume c (-ε) :=
        (continuousOn_const.mul ((by fun_prop : ContinuousOn (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I - z₀) (uIcc c (-ε))).inv₀
          (fun y hy => sub_ne_zero.mpr (hne y hy)))).intervalIntegrable
      rw [intervalIntegral.integral_congr fun y hy => hdslope_eq _ (hne y hy),
        intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
    have hleft_eq : ∫ y in c..(-ε), dslope F z₀ ((a : ℂ) + (y : ℂ) * Complex.I) =
        (∫ y in c..(-ε), F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z₀)) -
        F z₀ * (∫ y in c..(-ε), ((a : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹) := by
      have hne : ∀ y ∈ uIcc c (-ε), (a : ℂ) + (y : ℂ) * Complex.I ≠ z₀ := fun y _ h0 => by
        have := congrArg Complex.re h0; simp [a] at this; linarith
      have hi1 : IntervalIntegrable (fun y : ℝ => F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z₀)) volume c (-ε) :=
        ((hcont.comp (by fun_prop) fun y hy => by rw [uIcc_of_le hc_le_neg] at hy; exact hrect_half a ⟨le_rfl, hab.le⟩ y ⟨hy.1, by linarith [hy.2]⟩).div
          (by fun_prop) (fun y hy => sub_ne_zero.mpr (hne y hy))).intervalIntegrable
      have hi2 : IntervalIntegrable (fun y : ℝ => F z₀ * ((a : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹) volume c (-ε) :=
        (continuousOn_const.mul ((by fun_prop : ContinuousOn (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I - z₀) (uIcc c (-ε))).inv₀
          (fun y hy => sub_ne_zero.mpr (hne y hy)))).intervalIntegrable
      rw [intervalIntegral.integral_congr fun y hy => hdslope_eq _ (hne y hy),
        intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
    simp only [z₁, z₂, smul_eq_mul] at hCG
    rw [hbot_eq, htop_eq, hright_eq, hleft_eq] at hCG
    linear_combination -hCG
  -- Lower bound `1 ≤ ‖∮_{∂R_ε} (z - z₀)⁻¹ dz‖` via its imaginary part:
  have hwind_ge : ∀ ε : ℝ, 0 < ε → ε < δ / 2 →
      1 ≤ ‖(∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - z₀)⁻¹) -
            (∫ x in a..b, ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)⁻¹) +
            Complex.I * (∫ y in c..(-ε), ((b : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹) -
            Complex.I * (∫ y in c..(-ε), ((a : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹)‖ := by
    intro ε hε0 hε1
    have hc_le_neg : c ≤ -ε := by dsimp [c]; linarith
    refine le_trans ?_ (Complex.im_le_norm _)
    have him_eq : ((∫ x in a..b, ((x : ℂ) + (c : ℂ) * Complex.I - z₀)⁻¹) -
        (∫ x in a..b, ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)⁻¹) +
        Complex.I * (∫ y in c..(-ε), ((b : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹) -
        Complex.I * (∫ y in c..(-ε), ((a : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹)).im =
        (∫ x in a..b, (((x : ℂ) + (c : ℂ) * Complex.I - z₀)⁻¹).im) +
        (∫ x in a..b, (-(((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)⁻¹)).im) +
        (∫ y in c..(-ε), (((b : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹).re) +
        (∫ y in c..(-ε), (-(((a : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹)).re) := by
      simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_add, Complex.neg_im, Complex.neg_re, intervalIntegral.integral_neg]
      have h1 := (Complex.imCLM.intervalIntegral_comp_comm (((by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I - z₀) (uIcc a b)).inv₀
        (fun x _ h0 => by have := congrArg Complex.im (sub_eq_zero.mp h0); simp at this; linarith)).intervalIntegrable (μ := volume)))
      have h2 := (Complex.imCLM.intervalIntegral_comp_comm (((by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀) (uIcc a b)).inv₀
        (fun x _ h0 => by have := congrArg Complex.im (sub_eq_zero.mp h0); simp at this; linarith [hδ2])).intervalIntegrable (μ := volume)))
      have h3 := (Complex.reCLM.intervalIntegral_comp_comm (((by fun_prop : ContinuousOn (fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I - z₀) (uIcc c (-ε))).inv₀
        (fun y _ h0 => by have := congrArg Complex.re (sub_eq_zero.mp h0); simp [b] at this; linarith)).intervalIntegrable (μ := volume)))
      have h4 := (Complex.reCLM.intervalIntegral_comp_comm (((by fun_prop : ContinuousOn (fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I - z₀) (uIcc c (-ε))).inv₀
        (fun y _ h0 => by have := congrArg Complex.re (sub_eq_zero.mp h0); simp [a] at this; linarith)).intervalIntegrable (μ := volume)))
      simp only [Complex.imCLM_apply, Complex.reCLM_apply, Pi.inv_apply] at h1 h2 h3 h4
      rw [h1, h2, h3, h4]; ring
    rw [him_eq]
    have hbot_ge : 1 ≤ ∫ x in a..b, (((x : ℂ) + (c : ℂ) * Complex.I - z₀)⁻¹).im := by
      have h1 : (1 : ℝ) = ∫ _ in a..b, (1 / (2 * δ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, show b - a = 2 * δ by dsimp [a, b]; ring]
        field_simp [hδ_pos.ne']; exact (div_self hδ_pos.ne').symm
      rw [h1]
      refine intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
        ((Complex.continuous_im.comp_continuousOn ((by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (c : ℂ) * Complex.I - z₀) (Icc a b)).inv₀
          (fun x _ h0 => by have := congrArg Complex.im (sub_eq_zero.mp h0); simp at this; linarith))).intervalIntegrable_of_Icc hab.le)
        fun x hx => ?_
      rw [Complex.inv_im, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero,
        Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add]
      have hcx : c - z₀.im = -δ := by dsimp [c]; ring
      rw [hcx, neg_neg]
      have hns_le : (x - z₀.re) * (x - z₀.re) + (-δ) * (-δ) ≤ 2 * δ ^ 2 := by
        have hx1 : -δ ≤ x - z₀.re := by linarith [hx.1]
        have hx2 : x - z₀.re ≤ δ := by linarith [hx.2]
        nlinarith
      rw [div_le_div_iff₀ (by positivity) (by nlinarith [sq_nonneg (x - z₀.re), sq_pos_of_pos hδ_pos])]
      nlinarith
    have htop_nn : 0 ≤ ∫ x in a..b, (-(((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)⁻¹)).im :=
      intervalIntegral.integral_nonneg hab.le fun x _ => by
        rw [Complex.neg_im, Complex.inv_im]
        have hpos : 0 < (-ε - z₀.im) := by linarith [hδ2]
        have hns : 0 ≤ Complex.normSq ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀) := Complex.normSq_nonneg _
        have him : (((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)).im = -ε - z₀.im := by simp
        rw [him, neg_div, neg_neg]
        exact div_nonneg hpos.le hns
    have hright_nn : 0 ≤ ∫ y in c..(-ε), (((b : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹).re :=
      intervalIntegral.integral_nonneg hc_le_neg fun y _ => by
        rw [Complex.inv_re]
        have hre : (((b : ℂ) + (y : ℂ) * Complex.I - z₀)).re = δ := by simp [b]
        rw [hre]
        exact div_nonneg hδ_pos.le (Complex.normSq_nonneg _)
    have hleft_nn : 0 ≤ ∫ y in c..(-ε), (-(((a : ℂ) + (y : ℂ) * Complex.I - z₀)⁻¹)).re :=
      intervalIntegral.integral_nonneg hc_le_neg fun y _ => by
        rw [Complex.neg_re, Complex.inv_re]
        have hre : (((a : ℂ) + (y : ℂ) * Complex.I - z₀)).re = -δ := by simp [a]
        rw [hre, neg_div, neg_neg]
        exact div_nonneg hδ_pos.le (Complex.normSq_nonneg _)
    linarith
  -- Show the RHS of `hcauchy_eps` tends to `H z₀ = 0` as `ε → 0+`:
  have htend_top : Tendsto (fun ε : ℝ =>
      ∫ x in a..b, F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀))
      (𝓝[>] 0) (𝓝 0) := by
    have hcomp_rect : IsCompact (Icc a b ×ℂ Icc c 0) :=
      (isCompact_Icc (a := a) (b := b)).reProdIm (isCompact_Icc (a := c) (b := 0))
    obtain ⟨M, hM⟩ := hcomp_rect.exists_bound_of_continuousOn
      (hcont.mono fun z hz => by
        rw [Complex.mem_reProdIm] at hz
        simpa [Complex.re_add_im] using hrect_half z.re hz.1 z.im hz.2)
    have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM ⟨a, c⟩ (by
      rw [Complex.mem_reProdIm]; exact ⟨⟨le_rfl, hab.le⟩, ⟨le_rfl, by linarith⟩⟩))
    have heq_set : ∀ ε : ℝ,
        (∫ x in a..b, F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)) =
        ∫ x in Ioc a b, F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀) :=
      fun ε => intervalIntegral.integral_of_le hab.le
    simp_rw [heq_set]
    have h0 : (0 : ℂ) = ∫ _ in Ioc a b, (0 : ℂ) := by simp
    rw [h0]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => M / δ) ?_ ?_
      (integrableOn_const (by simp)) ?_
    · filter_upwards [Ioo_mem_nhdsGT (half_pos hδ_pos)] with ε hε
      have hc_le : c ≤ -ε := by dsimp [c]; linarith [hε.2]
      refine ((hcont.comp (by fun_prop) fun x hx =>
        hrect_half x (Ioc_subset_Icc_self hx) (-ε) ⟨hc_le, by linarith [hε.1]⟩).div
        (by fun_prop) (fun x _ h0 => by
          have := congrArg Complex.im (sub_eq_zero.mp h0); simp at this; linarith [hε.2, hδ2])).aestronglyMeasurable
        measurableSet_Ioc
    · filter_upwards [Ioo_mem_nhdsGT (half_pos hδ_pos)] with ε hε
      refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
      have hmem : ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) ∈ Icc a b ×ℂ Icc c 0 := by
        rw [Complex.mem_reProdIm]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨Ioc_subset_Icc_self hx, ⟨by dsimp [c]; linarith [hε.2], by linarith [hε.1]⟩⟩
      have hden : δ ≤ ‖(x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀‖ := by
        have him : (((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)).im = -ε - z₀.im := by simp
        have h1 : δ ≤ |-ε - z₀.im| := by rw [abs_of_pos (by linarith [hε.2, hδ2])]; linarith [hε.2, hδ2]
        exact h1.trans (him ▸ Complex.abs_im_le_norm _)
      rw [norm_div]
      exact div_le_div₀ hM_nn (hM _ hmem) hδ_pos hden
    · refine (ae_restrict_mem measurableSet_Ioc).mono fun x hx => ?_
      have hx_le : |x| ≤ r := by
        have := hrect_ball x (Ioc_subset_Icc_self hx) 0 ⟨by linarith, hδ_pos.le⟩
        simpa [Complex.norm_real, Real.norm_eq_abs] using this.le
      have hlim_arg : Tendsto (fun ε : ℝ => (x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
        have h1 : Continuous fun ε : ℝ => (x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I := by fun_prop
        simpa using (h1.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      have hmaps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) ∈ {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0} := by
        filter_upwards [Ioo_mem_nhdsGT (half_pos hδ_pos)] with ε hε
        exact hrect_half x (Ioc_subset_Icc_self hx) (-ε) ⟨by dsimp [c]; linarith [hε.2], by linarith [hε.1]⟩
      have hlim_F : Tendsto (fun ε : ℝ => F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 (F (x : ℂ))) :=
        (hcont (x : ℂ) ⟨by simpa [Complex.norm_real, Real.norm_eq_abs] using hx_le, by simp⟩).tendsto.comp
          (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlim_arg hmaps)
      have hne0 : (x : ℂ) - z₀ ≠ 0 := fun h0 => by
        have := congrArg Complex.im (sub_eq_zero.mp h0); simp at this; linarith
      have hlim_div := hlim_F.div (hlim_arg.sub tendsto_const_nhds) hne0
      rw [hreal x hx_le, zero_div] at hlim_div
      exact hlim_div.congr fun _ => rfl
  have htend_right : Tendsto (fun ε : ℝ =>
      ∫ y in c..(-ε), F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z₀))
      (𝓝[>] 0) (𝓝 (∫ y in c..0, F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z₀))) := by
    have hcont_g : ContinuousOn (fun y : ℝ => F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z₀)) (Icc c 0) :=
      (hcont.comp (by fun_prop) fun y hy => hrect_half b ⟨hab.le, le_rfl⟩ y hy).div
        (by fun_prop) (fun y _ h0 => by have := congrArg Complex.re (sub_eq_zero.mp h0); simp [b] at this; linarith)
    have hcont_int := intervalIntegral.continuousOn_primitive_interval (a := c) (b := (0 : ℝ)) (μ := volume)
      (by rw [uIcc_of_le (by linarith : c ≤ 0)]; exact hcont_g.integrableOn_compact isCompact_Icc)
    rw [uIcc_of_le (by linarith : c ≤ 0)] at hcont_int
    have hlim : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[Icc c 0] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [Ioo_mem_nhdsGT (half_pos hδ_pos)] with ε hε
      exact ⟨by dsimp [c]; linarith [hε.2], by linarith [hε.1]⟩
    exact (hcont_int 0 ⟨by linarith, le_rfl⟩).tendsto.comp hlim
  have htend_left : Tendsto (fun ε : ℝ =>
      ∫ y in c..(-ε), F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z₀))
      (𝓝[>] 0) (𝓝 (∫ y in c..0, F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z₀))) := by
    have hcont_g : ContinuousOn (fun y : ℝ => F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z₀)) (Icc c 0) :=
      (hcont.comp (by fun_prop) fun y hy => hrect_half a ⟨le_rfl, hab.le⟩ y hy).div
        (by fun_prop) (fun y _ h0 => by have := congrArg Complex.re (sub_eq_zero.mp h0); simp [a] at this; linarith)
    have hcont_int := intervalIntegral.continuousOn_primitive_interval (a := c) (b := (0 : ℝ)) (μ := volume)
      (by rw [uIcc_of_le (by linarith : c ≤ 0)]; exact hcont_g.integrableOn_compact isCompact_Icc)
    rw [uIcc_of_le (by linarith : c ≤ 0)] at hcont_int
    have hlim : Tendsto (fun ε : ℝ => -ε) (𝓝[>] 0) (𝓝[Icc c 0] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [Ioo_mem_nhdsGT (half_pos hδ_pos)] with ε hε
      exact ⟨by dsimp [c]; linarith [hε.2], by linarith [hε.1]⟩
    exact (hcont_int 0 ⟨by linarith, le_rfl⟩).tendsto.comp hlim
  have htend_rhs : Tendsto (fun ε : ℝ =>
      ‖(∫ x in a..b, F ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I - z₀)) -
       (∫ x in a..b, F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)) +
       Complex.I * (∫ y in c..(-ε), F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z₀)) -
       Complex.I * (∫ y in c..(-ε), F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z₀))‖)
      (𝓝[>] 0) (𝓝 0) := by
    have hlim := ((((tendsto_const_nhds (x := ∫ x in a..b,
        F ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I - z₀))).sub htend_top).add
        (htend_right.const_mul Complex.I)).sub (htend_left.const_mul Complex.I)).norm
    simpa [sub_zero, H, hHz₀] using hlim
  have hle_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖F z₀‖ ≤
      ‖(∫ x in a..b, F ((x : ℂ) + (c : ℂ) * Complex.I) / ((x : ℂ) + (c : ℂ) * Complex.I - z₀)) -
       (∫ x in a..b, F ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I) / ((x : ℂ) + ((-ε : ℝ) : ℂ) * Complex.I - z₀)) +
       Complex.I * (∫ y in c..(-ε), F ((b : ℂ) + (y : ℂ) * Complex.I) / ((b : ℂ) + (y : ℂ) * Complex.I - z₀)) -
       Complex.I * (∫ y in c..(-ε), F ((a : ℂ) + (y : ℂ) * Complex.I) / ((a : ℂ) + (y : ℂ) * Complex.I - z₀))‖ := by
    filter_upwards [Ioo_mem_nhdsGT (half_pos hδ_pos)] with ε hε
    rw [← hcauchy_eps ε hε.1 hε.2, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (hwind_ge ε hε.1 hε.2)
  have hnorm_le : ‖F z₀‖ ≤ 0 := ge_of_tendsto htend_rhs hle_ev
  exact norm_eq_zero.mp (le_antisymm hnorm_le (norm_nonneg _))

/-! ### Section 2: Analytic phase bounds and shifted Airy-square reference -/

/-- `c_s * β_1 = π²`, where `c_s = (π² / 3)^{1/3}` and `β_1 = (π² √3)^{2/3}`. -/
private lemma ceCs_mul_ceBeta1' : ceCs * ceBeta1 = π ^ 2 := by
  unfold ceCs ceBeta1
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [Real.div_rpow (sq_nonneg π) h3.le, Real.mul_rpow (sq_nonneg π) (Real.sqrt_nonneg 3),
    Real.sqrt_eq_rpow, ← Real.rpow_mul h3.le, show (1 / 2 : ℝ) * (2 / 3 : ℝ) = 1 / 3 by norm_num]
  have h3ne : (3 : ℝ) ^ (1 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos h3 _).ne'
  calc (π ^ 2) ^ (1 / 3 : ℝ) / 3 ^ (1 / 3 : ℝ) * ((π ^ 2) ^ (2 / 3 : ℝ) * 3 ^ (1 / 3 : ℝ))
      = ((π ^ 2) ^ (1 / 3 : ℝ) * (π ^ 2) ^ (2 / 3 : ℝ)) * (3 ^ (1 / 3 : ℝ) / 3 ^ (1 / 3 : ℝ)) := by ring
    _ = (π ^ 2) ^ ((1 / 3 : ℝ) + (2 / 3 : ℝ)) * 1 := by
        rw [← Real.rpow_add (sq_pos_of_pos hpi), div_self h3ne]
    _ = π ^ 2 := by norm_num

/-- Holomorphic extension `Θ` of `outerTheta (-1)` on `ball 0 (1 / 2)` with the quadratic
remainder bound `‖Θ z - θ_1^- z‖ ≤ M_θ ‖z‖²` on `‖z‖ ≤ 1 / 4`. -/
private lemma theta_hol_quadratic_bound :
    ∃ (Θ : ℂ → ℂ) (M_θ : ℝ), 0 ≤ M_θ ∧
      DifferentiableOn ℂ Θ (Metric.ball 0 (1 / 2)) ∧
      (∀ τ : ℝ, |τ| < 1 / 2 → Θ (τ : ℂ) = (CtOuter.outerTheta (-1) τ : ℂ)) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 / 4 → ‖Θ z - (CtOuter.ctTheta1 (-1) : ℂ) * z‖ ≤ M_θ * ‖z‖ ^ 2) := by
  obtain ⟨_, hodd, _, Θ, hΘ_diff, hΘ_eq⟩ := CtOuter.ct_outer_part2_structure (Or.inr rfl)
  have hΘ_contDiff : ContDiffOn ℂ (⊤ : ℕ∞) Θ (Metric.ball 0 (1 / 2)) :=
    (hΘ_diff.analyticOnNhd isOpen_ball).contDiffOn isOpen_ball.uniqueDiffOn
  have hΘ0 : Θ 0 = 0 := by
    have h0 := hodd 0
    have hval : CtOuter.outerTheta (-1) 0 = 0 := by simp at h0; linarith
    simpa [hval] using hΘ_eq 0 (by norm_num)
  have hdΘ0 : deriv Θ 0 = (CtOuter.ctTheta1 (-1) : ℂ) := by
    have hda : HasDerivAt Θ (deriv Θ 0) 0 :=
      (hΘ_diff.differentiableAt (isOpen_ball.mem_nhds (by simp))).hasDerivAt
    have hreal_d : HasDerivAt (fun t : ℝ => Θ (t : ℂ)) (deriv Θ 0) 0 := hda.comp_ofReal
    have hev : (fun t : ℝ => Θ (t : ℂ)) =ᶠ[𝓝 (0 : ℝ)] fun t : ℝ => (CtOuter.outerTheta (-1) t : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact hΘ_eq t ht
    have hreal_d2 : HasDerivAt (fun t : ℝ => (CtOuter.outerTheta (-1) t : ℂ))
        ((CtOuter.ctTheta1 (-1) : ℝ) : ℂ) 0 := by
      have hd := ((CtOuter.contDiff_outerTheta (-1)).differentiable (by simp) 0).hasDerivAt
      rw [CtOuter.deriv_outerTheta_zero_eq_ctTheta1 (Or.inr rfl)] at hd
      exact hd.ofReal_comp
    exact (hreal_d.congr_of_eventuallyEq hev.symm).unique hreal_d2
  have hd1_diff : DifferentiableOn ℂ (deriv Θ) (Metric.ball 0 (1 / 2)) := by
    have h := hΘ_contDiff.differentiableOn_iteratedDerivWithin (m := 1) (by decide) isOpen_ball.uniqueDiffOn
    refine h.congr fun z hz => ?_
    rw [iteratedDerivWithin_of_isOpen isOpen_ball hz, iteratedDeriv_one]
  have hd2_cont : ContinuousOn (deriv (deriv Θ)) (Metric.closedBall 0 (1 / 4)) := by
    have h := hΘ_contDiff.continuousOn_iteratedDerivWithin (m := 2) (by decide) isOpen_ball.uniqueDiffOn
    refine (h.mono (Metric.closedBall_subset_ball (by norm_num))).congr fun z hz => ?_
    have hz' : z ∈ Metric.ball (0 : ℂ) (1 / 2) := Metric.closedBall_subset_ball (by norm_num) hz
    rw [iteratedDerivWithin_of_isOpen isOpen_ball hz', iteratedDeriv_succ, iteratedDeriv_one]
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall (0 : ℂ) (1 / 4)).exists_bound_of_continuousOn hd2_cont
  have hM₂_nn : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ 0 (by simp))
  refine ⟨Θ, M₂, hM₂_nn, hΘ_diff, hΘ_eq, fun z hz => ?_⟩
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) * z ∈ Metric.closedBall (0 : ℂ) (1 / 4) := fun s hs => by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg z]
  have hmem_open : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) * z ∈ Metric.ball (0 : ℂ) (1 / 2) := fun s hs =>
    Metric.closedBall_subset_ball (by norm_num) (hmem s hs)
  have hd1_sub : ∀ s ∈ Icc (0 : ℝ) 1, ‖deriv Θ ((s : ℂ) * z) - deriv Θ 0‖ ≤ M₂ * ‖z‖ := fun s hs => by
    have hderiv : ∀ u ∈ uIcc (0 : ℝ) s,
        HasDerivAt (fun t : ℝ => deriv Θ ((t : ℂ) * z)) (deriv (deriv Θ) ((u : ℂ) * z) * z) u := fun u hu => by
      rw [uIcc_of_le hs.1] at hu
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z u := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const z
      have h2 := (hd1_diff.differentiableAt (isOpen_ball.mem_nhds (hmem_open u ⟨hu.1, hu.2.trans hs.2⟩))).hasDerivAt
      exact h2.comp u h1
    have hcont : ContinuousOn (fun u : ℝ => deriv (deriv Θ) ((u : ℂ) * z) * z) (Icc 0 s) :=
      (ContinuousOn.comp (t := Metric.closedBall (0 : ℂ) (1 / 4)) hd2_cont
        (Continuous.continuousOn (by fun_prop))
        (fun u (hu : u ∈ Icc (0 : ℝ) s) => hmem u ⟨hu.1, hu.2.trans hs.2⟩)).mul continuousOn_const
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hs.1)
    simp only [Complex.ofReal_zero, zero_mul] at hftc
    rw [← hftc]
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
      (f := fun u : ℝ => deriv (deriv Θ) ((u : ℂ) * z) * z) (C := M₂ * ‖z‖)
      (fun u hu => by
        rw [uIoc_of_le hs.1] at hu
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM₂ _ (hmem u ⟨hu.1.le, hu.2.trans hs.2⟩)) (norm_nonneg z))
    rw [sub_zero, abs_of_nonneg hs.1] at hbd
    exact hbd.trans (mul_le_of_le_one_right (by positivity) hs.2)
  have hderiv0 : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Θ ((t : ℂ) * z) - (CtOuter.ctTheta1 (-1) : ℂ) * ((t : ℂ) * z))
        ((deriv Θ ((s : ℂ) * z) - deriv Θ 0) * z) s := fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const z
    have h2 := (hΘ_diff.differentiableAt (isOpen_ball.mem_nhds (hmem_open s hs))).hasDerivAt.comp s h1
    have h3 := h1.const_mul (CtOuter.ctTheta1 (-1) : ℂ)
    exact (h2.sub h3).congr_deriv (by rw [hdΘ0]; ring)
  have hcont0 : ContinuousOn (fun s : ℝ => (deriv Θ ((s : ℂ) * z) - deriv Θ 0) * z) (Icc 0 1) :=
    (((hd1_diff.continuousOn.comp (by fun_prop) hmem_open).sub continuousOn_const).mul continuousOn_const)
  have hftc0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv0 (hcont0.intervalIntegrable_of_Icc zero_le_one)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, mul_zero, sub_self, hΘ0, sub_zero] at hftc0
  rw [← hftc0]
  have hbd0 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ => (deriv Θ ((s : ℂ) * z) - deriv Θ 0) * z) (C := M₂ * ‖z‖ ^ 2)
    (fun s hs => by
      rw [uIoc_of_le zero_le_one] at hs
      rw [norm_mul, _root_.sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hd1_sub s ⟨hs.1.le, hs.2⟩) (norm_nonneg z))
  simpa using hbd0

/-- Elementary bound `‖exp z - 1‖ ≤ exp M * ‖z‖` whenever `‖z‖ ≤ M`. -/
private lemma norm_exp_sub_one_le {z : ℂ} {M : ℝ} (hz : ‖z‖ ≤ M) :
    ‖Complex.exp z - 1‖ ≤ Real.exp M * ‖z‖ := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * z)) (Complex.exp ((t : ℂ) * z) * z) t :=
    fun t _ => by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z
      exact (Complex.hasDerivAt_exp _).comp t h1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => Complex.exp ((s : ℂ) * z) * z).intervalIntegrable 0 1)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hftc
  rw [← hftc]
  have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => Complex.exp ((t : ℂ) * z) * z) (C := Real.exp M * ‖z‖)
    (fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      rw [norm_mul, Complex.norm_exp]
      have hre : ((t : ℂ) * z).re ≤ M := by
        calc ((t : ℂ) * z).re ≤ ‖(t : ℂ) * z‖ := Complex.re_le_norm _
          _ = t * ‖z‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1.le]
          _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)
          _ = ‖z‖ := one_mul _
          _ ≤ M := hz
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) (norm_nonneg z))
  simpa using hbd

/-- Shifted version of `(uct:hhat-ref-id)` along `u = v - i` (`v ∈ ℝ`):
`(2π)⁻¹ ∫_ℝ (1 + ς² + i v)^{-1/2} exp((π²/36)(1 + ς² + i v)³ - i c_s x (v - i)) dv`
equals `(2√π / √c_s) e^{c_s c^{-2/3} x} Ai(x)² ≥ 0`. -/
theorem uct_hhat_ref_shifted {c : ℝ} (hc : 0 < c) (x : ℝ) :
    let ς : ℝ := c ^ (-(1 / 3 : ℝ))
    ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ v : ℝ, (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
            Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)) =
      ((2 * √π / √ceCs * Real.exp (ceCs * c ^ (-(2 / 3 : ℝ)) * x) * airyAi x ^ 2 : ℝ) : ℂ) := by
  intro ς
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc _
  have hς2_eq : ς ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  have hς2_pos : 0 < ς ^ 2 := sq_pos_of_pos hς_pos
  -- Holomorphic integrand `g(u) = (ς² + i u)^{-1/2} exp((π²/36)(ς² + i u)³ - i c_s x u)` on `Im u < ς²`:
  let g : ℂ → ℂ := fun u =>
    ((ς ^ 2 : ℂ) + Complex.I * u) ^ (-(1 / 2 : ℂ)) *
      Complex.exp ((π ^ 2 / 36 : ℂ) * ((ς ^ 2 : ℂ) + Complex.I * u) ^ 3 -
        Complex.I * ((ceCs * x : ℝ) : ℂ) * u)
  have hg_diff : DifferentiableOn ℂ g {u : ℂ | u.im < ς ^ 2} := fun u hu => by
    have hu' : u.im < ς ^ 2 := hu
    have hre : 0 < ((ς ^ 2 : ℂ) + Complex.I * u).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, one_mul, zero_sub, ← Complex.ofReal_pow]
      linarith
    have hlin : DifferentiableAt ℂ (fun w : ℂ => (ς ^ 2 : ℂ) + Complex.I * w) u := by fun_prop
    have hpow : DifferentiableAt ℂ (fun w : ℂ => ((ς ^ 2 : ℂ) + Complex.I * w) ^ (-(1 / 2 : ℂ))) u :=
      hlin.cpow_const (Or.inl hre)
    have hexp : DifferentiableAt ℂ (fun w : ℂ =>
        Complex.exp ((π ^ 2 / 36 : ℂ) * ((ς ^ 2 : ℂ) + Complex.I * w) ^ 3 -
          Complex.I * ((ceCs * x : ℝ) : ℂ) * w)) u := by fun_prop
    exact (hpow.mul hexp).differentiableWithinAt
  -- Uniform Gaussian bound on the horizontal strip `Im u ∈ [-1, 0]`:
  have hg_strip_bound : ∀ u : ℂ, -1 ≤ u.im → u.im ≤ 0 →
      ‖g u‖ ≤ (ς ^ 2) ^ (-(1 / 2 : ℝ)) *
        Real.exp (π ^ 2 / 36 * (1 + ς ^ 2) ^ 3 + |ceCs * x|) *
        Real.exp (-(π ^ 2 / 12 * ς ^ 2) * u.re ^ 2) := fun u hu1 hu2 => by
    set a : ℝ := ς ^ 2 - u.im
    have ha_ge : ς ^ 2 ≤ a := by dsimp [a]; linarith
    have ha_le : a ≤ 1 + ς ^ 2 := by dsimp [a]; linarith
    have ha_pos : 0 < a := lt_of_lt_of_le hς2_pos ha_ge
    have hw_eq : (ς ^ 2 : ℂ) + Complex.I * u = (a : ℂ) + (u.re : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [a, ← Complex.ofReal_pow] <;> ring
    have hpow_le : ‖((ς ^ 2 : ℂ) + Complex.I * u) ^ (-(1 / 2 : ℂ))‖ ≤ (ς ^ 2) ^ (-(1 / 2 : ℝ)) := by
      rw [hw_eq]
      have hne : (a : ℂ) + (u.re : ℂ) * Complex.I ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0; simp at this; linarith
      have hnorm_ge : ς ^ 2 ≤ ‖(a : ℂ) + (u.re : ℂ) * Complex.I‖ :=
        ha_ge.trans (by simpa using Complex.re_le_norm ((a : ℂ) + (u.re : ℂ) * Complex.I))
      rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp,
        show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re,
        ← Real.rpow_def_of_pos (lt_of_lt_of_le hς2_pos hnorm_ge)]
      exact Real.rpow_le_rpow_of_nonpos hς2_pos hnorm_ge (by norm_num)
    have hexp_le : ‖Complex.exp ((π ^ 2 / 36 : ℂ) * ((ς ^ 2 : ℂ) + Complex.I * u) ^ 3 -
          Complex.I * ((ceCs * x : ℝ) : ℂ) * u)‖ ≤
        Real.exp (π ^ 2 / 36 * (1 + ς ^ 2) ^ 3 + |ceCs * x|) *
        Real.exp (-(π ^ 2 / 12 * ς ^ 2) * u.re ^ 2) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      rw [hw_eq]
      have hre_cube : (((π ^ 2 / 36 : ℂ) * ((a : ℂ) + (u.re : ℂ) * Complex.I) ^ 3)).re =
          π ^ 2 / 36 * (a ^ 3 - 3 * a * u.re ^ 2) := by
        have h : ((a : ℂ) + (u.re : ℂ) * Complex.I) ^ 3 =
            ((a ^ 3 - 3 * a * u.re ^ 2 : ℝ) : ℂ) + ((3 * a ^ 2 * u.re - u.re ^ 3 : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq, Complex.I_pow_three]; ring
        rw [h, show (π ^ 2 / 36 : ℂ) = ((π ^ 2 / 36 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      have hre_lin : (Complex.I * ((ceCs * x : ℝ) : ℂ) * u).re = -(ceCs * x * u.im) := by
        simp [Complex.mul_re]
      rw [Complex.sub_re, hre_cube, hre_lin]
      have ha3 : a ^ 3 ≤ (1 + ς ^ 2) ^ 3 := pow_le_pow_left₀ ha_pos.le ha_le 3
      have hau : ς ^ 2 * u.re ^ 2 ≤ a * u.re ^ 2 := mul_le_mul_of_nonneg_right ha_ge (sq_nonneg _)
      have hlin : ceCs * x * u.im ≤ |ceCs * x| := by
        calc ceCs * x * u.im ≤ |ceCs * x * u.im| := le_abs_self _
          _ = |ceCs * x| * |u.im| := abs_mul _ _
          _ ≤ |ceCs * x| * 1 := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hu1, by linarith⟩) (abs_nonneg _)
          _ = |ceCs * x| := mul_one _
      have hpi2 : 0 ≤ π ^ 2 := sq_nonneg π
      nlinarith
    dsimp only [g]
    rw [norm_mul]
    calc ‖((ς ^ 2 : ℂ) + Complex.I * u) ^ (-(1 / 2 : ℂ))‖ *
          ‖Complex.exp ((π ^ 2 / 36 : ℂ) * ((ς ^ 2 : ℂ) + Complex.I * u) ^ 3 -
            Complex.I * ((ceCs * x : ℝ) : ℂ) * u)‖
        ≤ (ς ^ 2) ^ (-(1 / 2 : ℝ)) *
          (Real.exp (π ^ 2 / 36 * (1 + ς ^ 2) ^ 3 + |ceCs * x|) *
            Real.exp (-(π ^ 2 / 12 * ς ^ 2) * u.re ^ 2)) :=
          mul_le_mul hpow_le hexp_le (norm_nonneg _) (by positivity)
      _ = _ := by ring
  -- Integrability on `Im u = 0` and `Im u = -1`:
  let C_g : ℝ := (ς ^ 2) ^ (-(1 / 2 : ℝ)) * Real.exp (π ^ 2 / 36 * (1 + ς ^ 2) ^ 3 + |ceCs * x|)
  have hg_int_0 : Integrable (fun v : ℝ => g (v : ℂ)) := by
    have hcont : Continuous (fun v : ℝ => g (v : ℂ)) :=
      hg_diff.continuousOn.comp_continuous Complex.continuous_ofReal fun v => by simp [hς2_pos]
    exact ((integrable_exp_neg_mul_sq (by positivity : 0 < π ^ 2 / 12 * ς ^ 2)).const_mul C_g).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun v => by simpa [C_g] using hg_strip_bound (v : ℂ) (by simp) (by simp))
  have hg_int_neg1 : Integrable (fun v : ℝ => g ((v : ℂ) - Complex.I)) := by
    have hcont : Continuous (fun v : ℝ => g ((v : ℂ) - Complex.I)) :=
      hg_diff.continuousOn.comp_continuous (Complex.continuous_ofReal.sub continuous_const) fun v => by
        simp; linarith [hς2_pos]
    exact ((integrable_exp_neg_mul_sq (by positivity : 0 < π ^ 2 / 12 * ς ^ 2)).const_mul C_g).mono'
      hcont.aestronglyMeasurable (Eventually.of_forall fun v => by
        simpa [C_g] using hg_strip_bound ((v : ℂ) - Complex.I) (by simp) (by simp))
  -- Cauchy-Goursat on `[-R, R] × [-1, 0]` and let `R → ∞`:
  have hshift : ∫ v : ℝ, g ((v : ℂ) - Complex.I) = ∫ v : ℝ, g (v : ℂ) := by
    have hrect : ∀ R : ℝ, 0 < R →
        (∫ v in (-R)..R, g ((v : ℂ) - Complex.I)) - (∫ v in (-R)..R, g (v : ℂ)) =
        Complex.I * (∫ y in (-1 : ℝ)..0, g ((-R : ℝ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y in (-1 : ℝ)..0, g ((R : ℝ) + (y : ℂ) * Complex.I)) := fun R hR => by
      have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨-R, -1⟩ ⟨R, 0⟩
        (hg_diff.mono fun u hu => by
          simp only [Complex.mem_reProdIm, uIcc_of_le (by linarith : (-1 : ℝ) ≤ 0)] at hu
          exact lt_of_le_of_lt hu.2.2 hς2_pos)
      simp only [smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
        Complex.ofReal_zero, zero_mul, add_zero] at hCG
      have hbot : (fun x : ℝ => g ((x : ℂ) + -Complex.I)) = fun x : ℝ => g ((x : ℂ) - Complex.I) :=
        funext fun x => by congr 1
      have hleft_arg : (fun y : ℝ => g (-(R : ℂ) + (y : ℂ) * Complex.I)) =
          fun y : ℝ => g (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I) :=
        funext fun y => by simp
      rw [hbot, hleft_arg] at hCG
      linear_combination hCG
    have hlim_lhs : Tendsto (fun R : ℝ => (∫ v in (-R)..R, g ((v : ℂ) - Complex.I)) - (∫ v in (-R)..R, g (v : ℂ)))
        atTop (𝓝 ((∫ v : ℝ, g ((v : ℂ) - Complex.I)) - (∫ v : ℝ, g (v : ℂ)))) :=
      (intervalIntegral_tendsto_integral hg_int_neg1 tendsto_neg_atTop_atBot tendsto_id).sub
        (intervalIntegral_tendsto_integral hg_int_0 tendsto_neg_atTop_atBot tendsto_id)
    have hlim_side : ∀ s : ℝ, s = 1 ∨ s = -1 →
        Tendsto (fun R : ℝ => ∫ y in (-1 : ℝ)..0, g (((s * R : ℝ) : ℂ) + (y : ℂ) * Complex.I)) atTop (𝓝 0) := by
      intro s hs
      refine squeeze_zero_norm' (a := fun R => C_g * Real.exp (-(π ^ 2 / 12 * ς ^ 2) * R ^ 2)) ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R _
        have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 0)
          (C := C_g * Real.exp (-(π ^ 2 / 12 * ς ^ 2) * R ^ 2))
          (fun y hy => by
            rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hy
            have h1 := hg_strip_bound (((s * R : ℝ) : ℂ) + (y : ℂ) * Complex.I) (by simp [hy.1.le]) (by simp [hy.2])
            have hs2 : (s * R) ^ 2 = R ^ 2 := by rcases hs with rfl | rfl <;> ring
            simpa [C_g, hs2] using h1)
        simpa using hbd
      · have h1 : Tendsto (fun R : ℝ => -(π ^ 2 / 12 * ς ^ 2) * R ^ 2) atTop atBot :=
          (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr (by positivity))
            (tendsto_pow_atTop (by norm_num : 2 ≠ 0)))
        simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C_g
    have hlim_rhs : Tendsto (fun R : ℝ =>
        Complex.I * (∫ y in (-1 : ℝ)..0, g ((-R : ℝ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y in (-1 : ℝ)..0, g ((R : ℝ) + (y : ℂ) * Complex.I))) atTop (𝓝 0) := by
      have h1 := (hlim_side (-1) (Or.inr rfl)).const_mul Complex.I
      have h2 := (hlim_side 1 (Or.inl rfl)).const_mul Complex.I
      simpa using h1.sub h2
    have heq_ev : (fun R : ℝ => (∫ v in (-R)..R, g ((v : ℂ) - Complex.I)) - (∫ v in (-R)..R, g (v : ℂ))) =ᶠ[atTop]
        fun R : ℝ => Complex.I * (∫ y in (-1 : ℝ)..0, g ((-R : ℝ) + (y : ℂ) * Complex.I)) -
          Complex.I * (∫ y in (-1 : ℝ)..0, g ((R : ℝ) + (y : ℂ) * Complex.I)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR using hrect R hR
    exact sub_eq_zero.mp (tendsto_nhds_unique (hlim_lhs.congr' heq_ev) hlim_rhs)
  -- Identify `∫ v, g (v - I)` with our LHS and `∫ v, g v` with `uct_hhat_ref_id`:
  have hlhs_eq : ∫ v : ℝ, (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
          Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)) =
      ∫ v : ℝ, g ((v : ℂ) - Complex.I) := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have hw : ((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I = (ς ^ 2 : ℂ) + Complex.I * ((v : ℂ) - Complex.I) := by
      push_cast; rw [mul_sub, Complex.I_mul_I]; ring
    dsimp only [g]; rw [hw]
  rw [hlhs_eq, hshift]
  have hrhs_eq : ((1 / (2 * π) : ℝ) : ℂ) * ∫ v : ℝ, g (v : ℂ) =
      ((2 * √π / √ceCs * Real.exp (ceCs * c ^ (-(2 / 3 : ℝ)) * x) * airyAi x ^ 2 : ℝ) : ℂ) := by
    have href := (uct_hhat_ref_id hc x).1
    rw [← href]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only [g]
    rw [← hς2_eq]; symm; rw [mul_assoc, ← Complex.exp_add]
    congr 1
    · congr 1; dsimp [ς]; push_cast; ring
    · congr 1; dsimp [ς]; push_cast; ring_nf; simp [Complex.I_sq, Complex.I_pow_three]; ring
  exact hrhs_eq

/-! ### Section 3: Airy-window core difference (`|v| ≤ ς^{-2/5}`) -/

/-- Elementary Gaussian-polynomial integrability: `v ↦ (1 + |v|)^k * exp(-a v²)` is integrable on `ℝ`
for any `a > 0` and `k : ℕ`. -/
private lemma integrable_one_add_abs_pow_mul_exp_neg_sq {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun v : ℝ => (1 + |v|) ^ k * Real.exp (-a * v ^ 2)) := by
  have hcont : Continuous (fun v : ℝ => (1 + |v|) ^ k * Real.exp (-a * v ^ 2)) := by fun_prop
  -- Bound `(1 + |v|)^k ≤ C * exp((a/2) * v²)` via `Real.sum_le_exp_of_nonneg`:
  have hexp_dom : ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, (1 + |v|) ^ k ≤ C * Real.exp ((a / 2) * v ^ 2) := by
    refine ⟨(2 : ℝ) ^ k * (2 + (k.factorial : ℝ) / (a / 2) ^ k), by positivity, fun v => ?_⟩
    have h1 : (1 + |v|) ^ k ≤ (2 : ℝ) ^ k * (1 + |v| ^ k) := by
      rcases le_total |v| 1 with hv | hv
      · calc (1 + |v|) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
          _ = (2 : ℝ) ^ k * 1 := (mul_one _).symm
          _ ≤ (2 : ℝ) ^ k * (1 + |v| ^ k) := by gcongr; linarith [pow_nonneg (abs_nonneg v) k]
      · calc (1 + |v|) ^ k ≤ (2 * |v|) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
          _ = (2 : ℝ) ^ k * |v| ^ k := mul_pow 2 |v| k
          _ ≤ (2 : ℝ) ^ k * (1 + |v| ^ k) := by gcongr; linarith
    have h2 : |v| ^ k ≤ 1 + (k.factorial : ℝ) / (a / 2) ^ k * Real.exp ((a / 2) * v ^ 2) := by
      rcases le_total |v| 1 with hv | hv
      · have hle : |v| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg v) hv
        linarith [show (0 : ℝ) ≤ (k.factorial : ℝ) / (a / 2) ^ k * Real.exp ((a / 2) * v ^ 2) by positivity]
      · have hv_le : |v| ≤ v ^ 2 := by rw [← sq_abs v]; nlinarith [abs_nonneg v]
        have hu_nn : 0 ≤ (a / 2) * v ^ 2 := by positivity
        have hsum := Real.sum_le_exp_of_nonneg hu_nn (k + 1)
        have hterm : ((a / 2) * v ^ 2) ^ k / (k.factorial : ℝ) ≤ Real.exp ((a / 2) * v ^ 2) :=
          (Finset.single_le_sum (f := fun i => ((a / 2) * v ^ 2) ^ i / (i.factorial : ℝ))
            (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans hsum
        have hpow : |v| ^ k ≤ (v ^ 2) ^ k := pow_le_pow_left₀ (abs_nonneg v) hv_le k
        have hfact : (0 : ℝ) < (k.factorial : ℝ) := by positivity
        have hdiv : (v ^ 2) ^ k ≤ (k.factorial : ℝ) / (a / 2) ^ k * Real.exp ((a / 2) * v ^ 2) := by
          rw [mul_pow] at hterm
          have h3 : (a / 2) ^ k * (v ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp ((a / 2) * v ^ 2) := by
            simpa [mul_comm] using (div_le_iff₀ hfact).mp hterm
          calc (v ^ 2) ^ k = ((a / 2) ^ k * (v ^ 2) ^ k) / (a / 2) ^ k := by field_simp [(pow_pos (half_pos ha) k).ne']
            _ ≤ ((k.factorial : ℝ) * Real.exp ((a / 2) * v ^ 2)) / (a / 2) ^ k := div_le_div_of_nonneg_right h3 (by positivity)
            _ = (k.factorial : ℝ) / (a / 2) ^ k * Real.exp ((a / 2) * v ^ 2) := by ring
        linarith
    have hexp_ge1 : 1 ≤ Real.exp ((a / 2) * v ^ 2) := Real.one_le_exp (by positivity)
    have h12 : 1 + |v| ^ k ≤ (2 + (k.factorial : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * v ^ 2) := by
      calc 1 + |v| ^ k ≤ 2 + (k.factorial : ℝ) / (a / 2) ^ k * Real.exp ((a / 2) * v ^ 2) := by linarith
        _ ≤ 2 * Real.exp ((a / 2) * v ^ 2) + (k.factorial : ℝ) / (a / 2) ^ k * Real.exp ((a / 2) * v ^ 2) := by linarith
        _ = (2 + (k.factorial : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * v ^ 2) := by ring
    calc (1 + |v|) ^ k ≤ (2 : ℝ) ^ k * (1 + |v| ^ k) := h1
      _ ≤ (2 : ℝ) ^ k * ((2 + (k.factorial : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * v ^ 2)) := by gcongr
      _ = (2 : ℝ) ^ k * (2 + (k.factorial : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * v ^ 2) := by ring
  obtain ⟨C, _, hC⟩ := hexp_dom
  refine ((integrable_exp_neg_mul_sq (half_pos ha)).const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  calc (1 + |v|) ^ k * Real.exp (-a * v ^ 2)
      ≤ (C * Real.exp ((a / 2) * v ^ 2)) * Real.exp (-a * v ^ 2) :=
        mul_le_mul_of_nonneg_right (hC v) (Real.exp_pos _).le
    _ = C * Real.exp (-(a / 2) * v ^ 2) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Elementary exponential decay bound: `exp(-u) ≤ k! / u^k` for `u > 0` and `k : ℕ`. -/
private lemma exp_neg_le_factorial_div {u : ℝ} (hu : 0 < u) (k : ℕ) :
    Real.exp (-u) ≤ (k.factorial : ℝ) / u ^ k := by
  have hsum := Real.sum_le_exp_of_nonneg hu.le (k + 1)
  have hterm : u ^ k / (k.factorial : ℝ) ≤ Real.exp u :=
    (Finset.single_le_sum (f := fun i => u ^ i / (i.factorial : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans hsum
  have hfact : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  rw [Real.exp_neg, le_div_iff₀ (pow_pos hu k)]
  have h1 : u ^ k ≤ (k.factorial : ℝ) * Real.exp u := by
    simpa [mul_comm] using (div_le_iff₀ hfact).mp hterm
  calc (Real.exp u)⁻¹ * u ^ k ≤ (Real.exp u)⁻¹ * ((k.factorial : ℝ) * Real.exp u) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Real.exp_pos _).le)
    _ = (k.factorial : ℝ) := by field_simp [(Real.exp_pos u).ne']

/-- Scaling `((r : ℂ) * w) ^ s = (r : ℂ) ^ s * w ^ s` for `r > 0` and `w ≠ 0`. -/
private lemma ofReal_mul_cpow_of_pos' {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ((r : ℂ) * w) ^ s = (r : ℂ) ^ s * w ^ s := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hrC hw), Complex.cpow_def_of_ne_zero hrC,
    Complex.cpow_def_of_ne_zero hw, Complex.log_ofReal_mul hr hw, ← Complex.ofReal_log hr.le,
    add_mul, Complex.exp_add]

set_option maxHeartbeats 400000 in
/-- Core Airy-window difference (`|v| ≤ ς^{-2/5}`): analytic continuation of `(uct:KW-hhat-edge)`
to the lower half-disc plus Taylor expansion of `edgePhiC`, `Θ`, `A_ext`, and the reference's
extra exponential yields `O_{U, S_w, C_A}(c^{-4/3})`. -/
private lemma airy_window_core_diff {U S_w r₀ C_A : ℝ}
    (hU : 1 ≤ U) (hSw : 0 < S_w) (hr₀ : 0 < r₀) (hCA : 0 ≤ C_A) :
    ∃ (c₁ C_core : ℝ), 60 ≤ c₁ ∧ 0 < C_core ∧
      ∀ {c L : ℝ} {W A_ext : ℂ → ℂ} {A : ℝ → ℂ} {η_W : ℝ},
        c₁ ≤ c → 0 < η_W → StripW1 η_W W →
        -(π ^ 2 * U) ≤ c ^ (2 / 3 : ℝ) * L → c ^ (2 / 3 : ℝ) * L ≤ π ^ 2 * S_w →
        (∀ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) (Real.exp L / π ^ 2) * W ((τ : ℂ) * Complex.I) =
          ((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
            A τ * regSqrt (1 / c) τ) →
        ContinuousOn A_ext {z : ℂ | ‖z‖ ≤ r₀ ∧ z.im ≤ 0} →
        DifferentiableOn ℂ A_ext {z : ℂ | ‖z‖ < r₀ ∧ z.im < 0} →
        (∀ τ : ℝ, |τ| ≤ r₀ → A_ext (τ : ℂ) = A τ) →
        (∀ z : ℂ, ‖z‖ ≤ r₀ → z.im ≤ 0 →
          ‖A_ext z - 1‖ ≤ C_A * (c ^ (-(2 / 3 : ℝ)) * ‖z‖ + ‖z‖ ^ 2)) →
        let ς : ℝ := c ^ (-(1 / 3 : ℝ))
        let V : ℝ := ς ^ (-(2 / 5 : ℝ))
        let x : ℝ := -ceBeta1 * (c ^ (2 / 3 : ℝ) * L / π ^ 2) + ceBeta1 * (CtOuter.ctTheta1 (-1) / π ^ 2) * ς
        ‖((c ^ (1 / 3 : ℝ) / (2 * π) : ℝ) : ℂ) *
            (∫ t in Icc (-(ς * V)) (ς * V),
              mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) (Real.exp L / π ^ 2) *
                W ((ς : ℂ) + (t : ℂ) * Complex.I)) -
          ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
            (((1 / (2 * π) : ℝ) : ℂ) *
              ∫ v in Icc (-V) V,
                (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
                  Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
                    Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)))‖ ≤
          C_core * c ^ (-(4 / 3 : ℝ)) := by
  obtain ⟨Θ, M_θ, hMθ_nn, hΘ_diff, hΘ_eq, hΘ_quad⟩ := theta_hol_quadratic_bound
  set r : ℝ := min r₀ (1 / 4)
  have hr_pos : 0 < r := lt_min hr₀ (by norm_num)
  have hr_le_r₀ : r ≤ r₀ := min_le_left _ _
  have hr_le_q : r ≤ 1 / 4 := min_le_right _ _
  set c₁ : ℝ := max 60 ((4 / r) ^ (5 : ℝ) + 1)
  have hc₁_ge60 : 60 ≤ c₁ := le_max_left _ _
  -- Gaussian-polynomial integral constant:
  have hI5_int : Integrable (fun v : ℝ => (1 + |v|) ^ 5 * Real.exp (-(π ^ 2 / 12) * v ^ 2)) :=
    integrable_one_add_abs_pow_mul_exp_neg_sq (by positivity) 5
  set I5 : ℝ := ∫ v : ℝ, (1 + |v|) ^ 5 * Real.exp (-(π ^ 2 / 12) * v ^ 2)
  have hI5_nn : 0 ≤ I5 := integral_nonneg fun v => by positivity
  set M_dp : ℝ := 32 * (10 + M_θ)
  set C_pt : ℝ := Real.exp (π ^ 2 / 36 + π ^ 2 * S_w + |CtOuter.ctTheta1 (-1)|) *
    (Real.exp M_dp * (2 * C_A + (10 + M_θ)) + Real.exp 64 * 2)
  set C_core : ℝ := max 1 ((π ^ 2 / 4 * |uctCAi|) / (2 * π) * C_pt * I5)
  refine ⟨c₁, C_core, hc₁_ge60, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro c L W A_ext A η_W hc hηW hW hL_lo hL_hi hfac hAext_cont hAext_hol hAext_real hAext_bd
  intro ς V x
  have hc60 : 60 ≤ c := hc₁_ge60.trans hc
  have hc0 : 0 < c := by linarith
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le1 : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hς2_eq : ς ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hcς3 : c * ς ^ 3 = 1 := by
    dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, show -(1 / 3 : ℝ) * (3 : ℕ) = -1 by norm_num,
      Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
  have hcς_eq : c * ς = c ^ (2 / 3 : ℝ) := by
    dsimp [ς]; conv_lhs => arg 1; rw [← Real.rpow_one c]
    rw [← Real.rpow_add hc0]; norm_num
  have hV_pos : 0 < V := Real.rpow_pos_of_pos hς_pos _
  have hV_ge1 : 1 ≤ V := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hς_pos hς_le1 (by norm_num)
  -- Show `2 * ς * V < r`:
  have h2ςV_lt : 2 * (ς * V) < r := by
    have hςV : ς * V = c ^ (-(1 / 5 : ℝ)) := by
      dsimp [V]
      conv_lhs => arg 1; rw [← Real.rpow_one ς]
      rw [← Real.rpow_add hς_pos]; dsimp [ς]; rw [← Real.rpow_mul hc0.le]; norm_num
    rw [hςV]
    have hc_gt : (4 / r) ^ (5 : ℝ) < c := lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans hc)
    have hpow : c ^ (-(1 / 5 : ℝ)) < r / 4 := by
      have h1 : ((4 / r) ^ (5 : ℝ)) ^ (1 / 5 : ℝ) < c ^ (1 / 5 : ℝ) :=
        Real.rpow_lt_rpow (by positivity) hc_gt (by norm_num)
      rw [← Real.rpow_mul (by positivity), show (5 : ℝ) * (1 / 5 : ℝ) = 1 by norm_num, Real.rpow_one] at h1
      rw [Real.rpow_neg hc0.le, inv_lt_comm₀ (Real.rpow_pos_of_pos hc0 _) (by positivity)]
      simpa [div_eq_mul_inv] using h1
    linarith
  set ξ : ℝ := Real.exp L / π ^ 2
  have hξ_pos : 0 < ξ := by positivity
  -- Analytic continuation of `(uct:KW-hhat-edge)` to `{z | ‖z‖ < r ∧ z.im < 0}`:
  let F : ℂ → ℂ := fun z =>
    mellinK0 c (Complex.I * z) ξ * W (Complex.I * z) -
    ((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((c : ℂ) * edgePhiC L z - Θ z)) *
      A_ext z * (((1 / c : ℝ) : ℂ) + Complex.I * z) ^ (-(1 / 2 : ℂ))
  have hF_zero : ∀ z : ℂ, ‖z‖ < r → z.im < 0 → F z = 0 := by
    refine half_disc_zero_of_real_segment_zero hr_pos ?_ ?_ ?_
    · -- ContinuousOn F {z | ‖z‖ ≤ r ∧ z.im ≤ 0}
      have hK_cont : ContinuousOn (fun z : ℂ => mellinK0 c (Complex.I * z) ξ) {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0} :=
        (differentiableOn_mellinK0 hc0 ξ).continuousOn.comp (continuousOn_const.mul continuousOn_id)
          fun z hz => by
            have h1 : |(Complex.I * z).re| ≤ ‖Complex.I * z‖ := Complex.abs_re_le_norm _
            rw [norm_mul, Complex.norm_I, one_mul] at h1
            exact lt_of_le_of_lt (h1.trans (hz.1.trans hr_le_q)) (by norm_num)
      have hW_cont : ContinuousOn (fun z : ℂ => W (Complex.I * z)) {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0} :=
        hW.cont.comp (continuousOn_const.mul continuousOn_id) fun z hz => by
          obtain ⟨hz1, hz2⟩ := hz
          change 0 ≤ (Complex.I * z).re ∧ (Complex.I * z).re ≤ 1
          have hre : (Complex.I * z).re = -z.im := by simp
          rw [hre]
          refine ⟨by linarith, ?_⟩
          have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
          rw [abs_of_nonpos hz2] at h1
          linarith [hr_le_q]
      have hPhi_cont : ContinuousOn (edgePhiC L) {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0} :=
        fun z hz => ((hasDerivAt_edgePhiC L (lt_of_le_of_lt (hz.1.trans hr_le_q) (by norm_num))).continuousAt).continuousWithinAt
      have hΘ_cont : ContinuousOn Θ {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0} :=
        hΘ_diff.continuousOn.mono fun z hz => by
          rw [Metric.mem_ball, dist_zero_right]; linarith [hz.1, hr_le_q]
      have hA_cont : ContinuousOn A_ext {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0} :=
        hAext_cont.mono fun z hz => ⟨hz.1.trans hr_le_r₀, hz.2⟩
      have hR_cont : ContinuousOn (fun z : ℂ => (((1 / c : ℝ) : ℂ) + Complex.I * z) ^ (-(1 / 2 : ℂ)))
          {z : ℂ | ‖z‖ ≤ r ∧ z.im ≤ 0} := by
        refine ContinuousOn.cpow (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
          continuousOn_const fun z hz => Or.inl ?_
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
          Complex.I_im, one_mul, zero_sub]
        have : 0 < 1 / c := by positivity
        linarith [hz.2]
      exact (hK_cont.mul hW_cont).sub
        (((continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn
          (continuousOn_const.mul ((continuousOn_const.mul hPhi_cont).sub hΘ_cont)))).mul hA_cont).mul hR_cont)
    · -- DifferentiableOn ℂ F {z | ‖z‖ < r ∧ z.im < 0}
      have hK_hol : DifferentiableOn ℂ (fun z : ℂ => mellinK0 c (Complex.I * z) ξ) {z : ℂ | ‖z‖ < r ∧ z.im < 0} :=
        (differentiableOn_mellinK0 hc0 ξ).comp ((differentiableOn_const Complex.I).mul differentiableOn_id)
          fun z hz => by
            obtain ⟨hz1, _⟩ := hz
            change |(Complex.I * z).re| < 1
            have h1 : |(Complex.I * z).re| ≤ ‖Complex.I * z‖ := Complex.abs_re_le_norm _
            rw [norm_mul, Complex.norm_I, one_mul] at h1
            linarith [hr_le_q]
      have hW_hol : DifferentiableOn ℂ (fun z : ℂ => W (Complex.I * z)) {z : ℂ | ‖z‖ < r ∧ z.im < 0} :=
        hW.hol.comp ((differentiableOn_const Complex.I).mul differentiableOn_id) fun z hz => by
          obtain ⟨hz1, hz2⟩ := hz
          change 0 < (Complex.I * z).re ∧ (Complex.I * z).re < 1
          have hre : (Complex.I * z).re = -z.im := by simp
          rw [hre]
          refine ⟨by linarith, ?_⟩
          have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
          rw [abs_of_neg hz2] at h1
          linarith [hr_le_q]
      have hPhi_hol : DifferentiableOn ℂ (edgePhiC L) {z : ℂ | ‖z‖ < r ∧ z.im < 0} :=
        fun z hz => (hasDerivAt_edgePhiC L (lt_trans hz.1 (lt_of_le_of_lt hr_le_q (by norm_num)))).differentiableAt.differentiableWithinAt
      have hΘ_hol : DifferentiableOn ℂ Θ {z : ℂ | ‖z‖ < r ∧ z.im < 0} :=
        hΘ_diff.mono fun z hz => by
          rw [Metric.mem_ball, dist_zero_right]; linarith [hz.1, hr_le_q]
      have hA_hol : DifferentiableOn ℂ A_ext {z : ℂ | ‖z‖ < r ∧ z.im < 0} :=
        hAext_hol.mono fun z hz => ⟨lt_of_lt_of_le hz.1 hr_le_r₀, hz.2⟩
      have hR_hol : DifferentiableOn ℂ (fun z : ℂ => (((1 / c : ℝ) : ℂ) + Complex.I * z) ^ (-(1 / 2 : ℂ)))
          {z : ℂ | ‖z‖ < r ∧ z.im < 0} := fun z hz => by
        have hlin : DifferentiableAt ℂ (fun w : ℂ => ((1 / c : ℝ) : ℂ) + Complex.I * w) z := by fun_prop
        have hre : 0 < (((1 / c : ℝ) : ℂ) + Complex.I * z).re := by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
            Complex.I_im, one_mul, zero_sub]
          have : 0 < 1 / c := by positivity
          linarith [hz.2]
        exact (hlin.cpow_const (Or.inl hre)).differentiableWithinAt
      exact (hK_hol.mul hW_hol).sub
        (((((differentiableOn_const _).mul (((differentiableOn_const Complex.I).mul
          (((differentiableOn_const (c : ℂ)).mul hPhi_hol).sub hΘ_hol)).cexp)).mul hA_hol)).mul hR_hol)
    · -- Real diameter `F (t : ℂ) = 0` for `|t| ≤ r`
      intro t ht
      dsimp only [F]
      have ht_lt : |t| < 1 / 2 := lt_of_le_of_lt (ht.trans hr_le_q) (by norm_num)
      rw [mul_comm Complex.I (t : ℂ), hfac t, edgePhiC_ofReal L (by linarith : |t| < 1), hΘ_eq t ht_lt,
        hAext_real t (ht.trans hr_le_r₀)]
      unfold regSqrt
      have h1 : ((c : ℂ) * (edgePhi L t : ℂ) - (CtOuter.outerTheta (-1) t : ℂ)) =
          ((c * edgePhi L t - CtOuter.outerTheta (-1) t : ℝ) : ℂ) := by push_cast; ring
      have h2 : ((1 / c : ℝ) : ℂ) + (t : ℂ) * Complex.I = ((1 / c : ℝ) : ℂ) + (t : ℂ) * Complex.I := rfl
      rw [h1, sub_self]
  -- Change of variable `t = ς * v` in the actual core integral:
  have hcov : ((c ^ (1 / 3 : ℝ) / (2 * π) : ℝ) : ℂ) *
        (∫ t in Icc (-(ς * V)) (ς * V),
          mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) =
      ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ v in Icc (-V) V,
          mellinK0 c ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) ξ * W ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) := by
    have hch : ∫ t in Icc (-(ς * V)) (ς * V),
          mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I) =
        (ς : ℂ) * ∫ v in Icc (-V) V,
          mellinK0 c ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) ξ * W ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by nlinarith : -(ς * V) ≤ ς * V),
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -V ≤ V)]
      have hsm := intervalIntegral.integral_comp_mul_left
        (f := fun t : ℝ => mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I))
        (a := -V) (b := V) hς_pos.ne'
      simp only [mul_neg, smul_eq_mul] at hsm
      rw [show (ς : ℂ) * ∫ v in (-V)..V, mellinK0 c ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) ξ *
            W ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) =
          (ς : ℂ) * ((ς⁻¹ : ℝ) • ∫ t in (-(ς * V))..(ς * V),
            mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) by
            rw [← hsm]]
      rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hς_pos.ne',
        Complex.ofReal_one, one_mul]
    rw [hch, ← mul_assoc, ← Complex.ofReal_mul]
    have hc13ς : c ^ (1 / 3 : ℝ) * ς = 1 := by
      dsimp [ς]; rw [← Real.rpow_add hc0]; norm_num
    congr 1
    rw [show c ^ (1 / 3 : ℝ) / (2 * π) * ς = (c ^ (1 / 3 : ℝ) * ς) / (2 * π) by ring, hc13ς]
  rw [hcov]
  -- Rewrite the difference as a single integral over `Icc (-V) V` with prefactor `(π²/4)|C_Ai| c^{-2/3} / (2π)`:
  let P_pref : ℂ := ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) / (2 * π) : ℝ) : ℂ)
  let R_v : ℝ → ℂ := fun v => (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))
  let P₀ : ℝ → ℂ := fun v =>
    (π ^ 2 / 36 : ℂ) * (1 + (v : ℂ) * Complex.I) ^ 3 +
    ((c * ς * L - CtOuter.ctTheta1 (-1) * ς : ℝ) : ℂ) * (1 + (v : ℂ) * Complex.I)
  let ΔR : ℝ → ℂ := fun v =>
    (π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
    (π ^ 2 / 36 : ℂ) * (1 + (v : ℂ) * Complex.I) ^ 3
  -- Pointwise identification on `v ∈ Icc (-V) V`:
  have hpt_eq : ∀ v ∈ Icc (-V) V,
      let τ : ℂ := ((ς * v : ℝ) : ℂ) - (ς : ℂ) * Complex.I
      let ΔP : ℂ := (c : ℂ) * (stripS0Tilde (Complex.I * τ) - (π ^ 2 / 36 : ℂ) * (Complex.I * τ) ^ 3) -
        Complex.I * (Θ τ - (CtOuter.ctTheta1 (-1) : ℂ) * τ)
      mellinK0 c ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) ξ * W ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) -
        ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
          (R_v v * Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
            Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))) =
      ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
        (R_v v * Complex.exp (P₀ v) * (Complex.exp ΔP * A_ext τ - Complex.exp (ΔR v))) := by
    intro v hv τ ΔP
    have hv_abs : |v| ≤ V := abs_le.mpr hv
    have hτ_norm : ‖τ‖ ≤ ς * (1 + |v|) := by
      dsimp [τ]
      calc ‖((ς * v : ℝ) : ℂ) - (ς : ℂ) * Complex.I‖
          ≤ ‖((ς * v : ℝ) : ℂ)‖ + ‖(ς : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ = ς * |v| + ς := by rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hς_pos,
            norm_mul, Complex.norm_real, Real.norm_of_nonneg hς_pos.le, Complex.norm_I, mul_one]
        _ = ς * (1 + |v|) := by ring
    have hτ_lt : ‖τ‖ < r := by
      calc ‖τ‖ ≤ ς * (1 + |v|) := hτ_norm
        _ ≤ ς * (1 + V) := by gcongr
        _ ≤ ς * (V + V) := by gcongr
        _ = 2 * (ς * V) := by ring
        _ < r := h2ςV_lt
    have hτ_im : τ.im < 0 := by simp [τ, hς_pos]
    have hIτ : Complex.I * τ = (ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [τ] <;> ring
    have hKW := sub_eq_zero.mp (hF_zero τ hτ_lt hτ_im)
    rw [hIτ] at hKW
    -- Factor `(1/c + I * τ)^{-1/2} = ς^{-1/2} * R_v v`:
    have hreg : (((1 / c : ℝ) : ℂ) + Complex.I * τ) ^ (-(1 / 2 : ℂ)) =
        ((ς ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * R_v v := by
      have harg : ((1 / c : ℝ) : ℂ) + Complex.I * τ = (ς : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) := by
        rw [hIτ]; push_cast
        have h1c : (1 / c : ℂ) = (ς : ℂ) ^ 3 := by
          have : ((1 / c : ℝ) : ℂ) = ((ς ^ 3 : ℝ) : ℂ) := by
            congr 1; rw [one_div]; exact (eq_inv_of_mul_eq_one_right hcς3).symm
          simpa using this
        rw [h1c]; ring
      have hw_ne : ((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.zero_re] at this
        nlinarith [sq_nonneg ς]
      rw [harg, ofReal_mul_cpow_of_pos' hς_pos hw_ne]
      congr 1
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hς_pos.ne'), ← Complex.ofReal_log hς_pos.le,
        show ((Real.log ς : ℝ) : ℂ) * -(1 / 2 : ℂ) = ((Real.log ς * -(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hς_pos]
    -- Phase equality `I * (c * edgePhiC L τ - Θ τ) = P₀ v + ΔP`:
    have hph_act : Complex.I * ((c : ℂ) * edgePhiC L τ - Θ τ) = P₀ v + ΔP := by
      unfold edgePhiC
      have hIτ_lt1 : ‖Complex.I * τ‖ < 1 := by
        rw [norm_mul, Complex.norm_I, one_mul]; exact lt_trans hτ_lt (lt_of_le_of_lt hr_le_q (by norm_num))
      rw [← stripS0Tilde_eq_edgePrim hIτ_lt1]
      have hIτ_sc : Complex.I * τ = (ς : ℂ) * (1 + (v : ℂ) * Complex.I) := by rw [hIτ]; push_cast; ring
      have hcube : (c : ℂ) * ((π ^ 2 / 36 : ℂ) * (Complex.I * τ) ^ 3) = (π ^ 2 / 36 : ℂ) * (1 + (v : ℂ) * Complex.I) ^ 3 := by
        rw [hIτ_sc, mul_pow]
        have hcς3C : (c : ℂ) * (ς : ℂ) ^ 3 = 1 := by exact_mod_cast hcς3
        calc (c : ℂ) * ((π ^ 2 / 36 : ℂ) * ((ς : ℂ) ^ 3 * (1 + (v : ℂ) * Complex.I) ^ 3))
            = ((c : ℂ) * (ς : ℂ) ^ 3) * ((π ^ 2 / 36 : ℂ) * (1 + (v : ℂ) * Complex.I) ^ 3) := by ring
          _ = (π ^ 2 / 36 : ℂ) * (1 + (v : ℂ) * Complex.I) ^ 3 := by rw [hcς3C, one_mul]
      have hlin : (c : ℂ) * ((L : ℂ) * (Complex.I * τ)) - Complex.I * ((CtOuter.ctTheta1 (-1) : ℂ) * τ) =
          ((c * ς * L - CtOuter.ctTheta1 (-1) * ς : ℝ) : ℂ) * (1 + (v : ℂ) * Complex.I) := by
        rw [show Complex.I * ((CtOuter.ctTheta1 (-1) : ℂ) * τ) = (CtOuter.ctTheta1 (-1) : ℂ) * (Complex.I * τ) by ring,
          hIτ_sc]; push_cast; ring
      dsimp only [P₀, ΔP]
      calc Complex.I * ((c : ℂ) * ((L : ℂ) * τ - Complex.I * stripS0Tilde (Complex.I * τ)) - Θ τ)
          = (c : ℂ) * ((L : ℂ) * (Complex.I * τ)) + (c : ℂ) * stripS0Tilde (Complex.I * τ) - Complex.I * Θ τ := by
            ring_nf; simp [Complex.I_sq]
        _ = ((c : ℂ) * ((π ^ 2 / 36 : ℂ) * (Complex.I * τ) ^ 3) +
              ((c : ℂ) * ((L : ℂ) * (Complex.I * τ)) - Complex.I * ((CtOuter.ctTheta1 (-1) : ℂ) * τ))) +
            ((c : ℂ) * (stripS0Tilde (Complex.I * τ) - (π ^ 2 / 36 : ℂ) * (Complex.I * τ) ^ 3) -
              Complex.I * (Θ τ - (CtOuter.ctTheta1 (-1) : ℂ) * τ)) := by ring
        _ = _ := by rw [hcube, hlin]
    -- Reference phase equality:
    have hph_ref : (π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
        Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I) = P₀ v + ΔR v := by
      have hcsx : ceCs * x = -(c * ς * L - CtOuter.ctTheta1 (-1) * ς) := by
        calc ceCs * x = -(ceCs * ceBeta1) * (c ^ (2 / 3 : ℝ) * L / π ^ 2) +
              (ceCs * ceBeta1) * (CtOuter.ctTheta1 (-1) / π ^ 2) * ς := by dsimp [x]; ring
          _ = -(π ^ 2) * (c ^ (2 / 3 : ℝ) * L / π ^ 2) + π ^ 2 * (CtOuter.ctTheta1 (-1) / π ^ 2) * ς := by
              rw [ceCs_mul_ceBeta1']
          _ = -(c * ς * L - CtOuter.ctTheta1 (-1) * ς) := by
              rw [← hcς_eq]; field_simp [Real.pi_ne_zero]; ring
      have hlin : -Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I) =
          ((c * ς * L - CtOuter.ctTheta1 (-1) * ς : ℝ) : ℂ) * (1 + (v : ℂ) * Complex.I) := by
        rw [hcsx]; push_cast
        calc -Complex.I * -((c : ℂ) * (ς : ℂ) * (L : ℂ) - (CtOuter.ctTheta1 (-1) : ℂ) * (ς : ℂ)) * ((v : ℂ) - Complex.I)
            = ((c : ℂ) * (ς : ℂ) * (L : ℂ) - (CtOuter.ctTheta1 (-1) : ℂ) * (ς : ℂ)) * (Complex.I * (v : ℂ) - Complex.I * Complex.I) := by ring
          _ = ((c : ℂ) * (ς : ℂ) * (L : ℂ) - (CtOuter.ctTheta1 (-1) : ℂ) * (ς : ℂ)) * (1 + (v : ℂ) * Complex.I) := by
              rw [Complex.I_mul_I]; ring
      dsimp only [P₀, ΔR]
      linear_combination hlin
    -- Combine prefactor `c^{-5/6} * ς^{-1/2} = c^{-2/3}`:
    have hc_pref : c ^ (-(5 / 6 : ℝ)) * ς ^ (-(1 / 2 : ℝ)) = c ^ (-(2 / 3 : ℝ)) := by
      dsimp [ς]; rw [← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]; norm_num
    rw [hKW, ← hIτ, hreg, hph_act, hph_ref, Complex.exp_add (P₀ v) ΔP, Complex.exp_add (P₀ v) (ΔR v)]
    have hmul_pref : ((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) * ((ς ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
        ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]; congr 1; rw [mul_assoc, hc_pref]
    calc ((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) *
            (Complex.exp (P₀ v) * Complex.exp ΔP) * A_ext τ * (((ς ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * R_v v) -
          ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
            (R_v v * (Complex.exp (P₀ v) * Complex.exp (ΔR v)))
        = (((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) * ((ς ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
            (R_v v * Complex.exp (P₀ v) * (Complex.exp ΔP * A_ext τ)) -
          ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
            (R_v v * Complex.exp (P₀ v) * Complex.exp (ΔR v)) := by ring
      _ = _ := by rw [hmul_pref]; ring
  -- Pointwise norm bound on `Icc (-V) V`:
  have hpt_bd : ∀ v ∈ Icc (-V) V,
      ‖mellinK0 c ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) ξ * W ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) -
        ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
          (R_v v * Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
            Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)))‖ ≤
      (π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) *
        (C_pt * ς ^ 2 * ((1 + |v|) ^ 5 * Real.exp (-(π ^ 2 / 12) * v ^ 2))) := by
    intro v hv
    rw [hpt_eq v hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    set τ : ℂ := ((ς * v : ℝ) : ℂ) - (ς : ℂ) * Complex.I
    set ΔP : ℂ := (c : ℂ) * (stripS0Tilde (Complex.I * τ) - (π ^ 2 / 36 : ℂ) * (Complex.I * τ) ^ 3) -
      Complex.I * (Θ τ - (CtOuter.ctTheta1 (-1) : ℂ) * τ)
    have hv_abs : |v| ≤ V := abs_le.mpr hv
    have h1v_ge1 : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
    have hτ_norm : ‖τ‖ ≤ ς * (1 + |v|) := by
      dsimp [τ]
      calc ‖((ς * v : ℝ) : ℂ) - (ς : ℂ) * Complex.I‖
          ≤ ‖((ς * v : ℝ) : ℂ)‖ + ‖(ς : ℂ) * Complex.I‖ := norm_sub_le _ _
        _ = ς * |v| + ς := by rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hς_pos,
            norm_mul, Complex.norm_real, Real.norm_of_nonneg hς_pos.le, Complex.norm_I, mul_one]
        _ = ς * (1 + |v|) := by ring
    have hτ_lt : ‖τ‖ < r := by
      calc ‖τ‖ ≤ ς * (1 + |v|) := hτ_norm
        _ ≤ ς * (V + V) := by gcongr
        _ = 2 * (ς * V) := by ring
        _ < r := h2ςV_lt
    have hRv_le1 : ‖R_v v‖ ≤ 1 := by
      dsimp [R_v]
      have hne : ((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.zero_re] at this
        nlinarith [sq_nonneg ς]
      have hge1 : 1 ≤ ‖((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I‖ := by
        have := Complex.re_le_norm (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero] at this
        linarith [sq_nonneg ς]
      rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp,
        show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re,
        ← Real.rpow_def_of_pos (lt_of_lt_of_le one_pos hge1)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hge1 (by norm_num)
    have hP₀_le : ‖Complex.exp (P₀ v)‖ ≤ Real.exp (π ^ 2 / 36 + π ^ 2 * S_w + |CtOuter.ctTheta1 (-1)|) *
        Real.exp (-(π ^ 2 / 12) * v ^ 2) := by
      rw [Complex.norm_exp, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hre : (P₀ v).re = π ^ 2 / 36 - π ^ 2 / 12 * v ^ 2 + (c * ς * L - CtOuter.ctTheta1 (-1) * ς) := by
        dsimp only [P₀]
        have hc3 : (1 + (v : ℂ) * Complex.I) ^ 3 =
            ((1 - 3 * v ^ 2 : ℝ) : ℂ) + ((3 * v - v ^ 3 : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq, Complex.I_pow_three]; ring
        rw [Complex.add_re, hc3, show (π ^ 2 / 36 : ℂ) = ((π ^ 2 / 36 : ℝ) : ℂ) by push_cast; ring,
          Complex.re_ofReal_mul, Complex.re_ofReal_mul]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.one_re]
        ring
      rw [hre, hcς_eq]
      have hθ_le : -CtOuter.ctTheta1 (-1) * ς ≤ |CtOuter.ctTheta1 (-1)| := by
        calc -CtOuter.ctTheta1 (-1) * ς ≤ |-CtOuter.ctTheta1 (-1) * ς| := le_abs_self _
          _ = |CtOuter.ctTheta1 (-1)| * ς := by rw [abs_mul, abs_neg, abs_of_pos hς_pos]
          _ ≤ |CtOuter.ctTheta1 (-1)| * 1 := mul_le_mul_of_nonneg_left hς_le1 (abs_nonneg _)
          _ = |CtOuter.ctTheta1 (-1)| := mul_one _
      linarith
    have hς2_1v5 : ς ^ 2 * (1 + |v|) ^ 5 ≤ 32 := by
      have h1 : 1 + |v| ≤ 2 * V := by linarith
      have h2 : (1 + |v|) ^ 5 ≤ 32 * V ^ 5 := by
        calc (1 + |v|) ^ 5 ≤ (2 * V) ^ 5 := pow_le_pow_left₀ (by positivity) h1 5
          _ = 32 * V ^ 5 := by ring
      have hς2V5 : ς ^ 2 * V ^ 5 = 1 := by
        dsimp [V]
        rw [← Real.rpow_natCast ς 2, ← Real.rpow_natCast _ 5, ← Real.rpow_mul hς_pos.le,
          ← Real.rpow_add hς_pos]; norm_num
      calc ς ^ 2 * (1 + |v|) ^ 5 ≤ ς ^ 2 * (32 * V ^ 5) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = 32 * (ς ^ 2 * V ^ 5) := by ring
        _ = 32 := by rw [hς2V5, mul_one]
    have hΔP_le : ‖ΔP‖ ≤ (10 + M_θ) * (ς ^ 2 * (1 + |v|) ^ 5) := by
      have hIτ_le : ‖Complex.I * τ‖ ≤ 1 / 4 := by
        rw [norm_mul, Complex.norm_I, one_mul]; exact hτ_lt.le.trans hr_le_q
      have h1 := stripS0Tilde_sub_le hIτ_le
      rw [norm_mul, Complex.norm_I, one_mul] at h1
      have h2 := hΘ_quad τ (hτ_lt.le.trans hr_le_q)
      have hcτ5 : c * ‖τ‖ ^ 5 ≤ ς ^ 2 * (1 + |v|) ^ 5 := by
        calc c * ‖τ‖ ^ 5 ≤ c * (ς * (1 + |v|)) ^ 5 := by gcongr
          _ = (c * ς ^ 3) * (ς ^ 2 * (1 + |v|) ^ 5) := by ring
          _ = ς ^ 2 * (1 + |v|) ^ 5 := by rw [hcς3, one_mul]
      have hτ2 : ‖τ‖ ^ 2 ≤ ς ^ 2 * (1 + |v|) ^ 5 := by
        have hpow : (1 + |v|) ^ 2 ≤ (1 + |v|) ^ 5 := pow_le_pow_right₀ h1v_ge1 (by norm_num)
        calc ‖τ‖ ^ 2 ≤ (ς * (1 + |v|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hτ_norm 2
          _ = ς ^ 2 * (1 + |v|) ^ 2 := mul_pow _ _ 2
          _ ≤ ς ^ 2 * (1 + |v|) ^ 5 := by gcongr
      calc ‖ΔP‖ ≤ ‖(c : ℂ) * (stripS0Tilde (Complex.I * τ) - (π ^ 2 / 36 : ℂ) * (Complex.I * τ) ^ 3)‖ +
            ‖Complex.I * (Θ τ - (CtOuter.ctTheta1 (-1) : ℂ) * τ)‖ := norm_sub_le _ _
        _ ≤ c * (10 * ‖τ‖ ^ 5) + M_θ * ‖τ‖ ^ 2 := by
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le, norm_mul, Complex.norm_I, one_mul]
            exact add_le_add (mul_le_mul_of_nonneg_left h1 hc0.le) h2
        _ ≤ 10 * (ς ^ 2 * (1 + |v|) ^ 5) + M_θ * (ς ^ 2 * (1 + |v|) ^ 5) := by
            have : c * (10 * ‖τ‖ ^ 5) = 10 * (c * ‖τ‖ ^ 5) := by ring
            rw [this]
            exact add_le_add (mul_le_mul_of_nonneg_left hcτ5 (by norm_num))
              (mul_le_mul_of_nonneg_left hτ2 hMθ_nn)
        _ = (10 + M_θ) * (ς ^ 2 * (1 + |v|) ^ 5) := by ring
    have hΔP_M : ‖ΔP‖ ≤ M_dp := hΔP_le.trans (by dsimp [M_dp]; nlinarith [hMθ_nn, hς2_1v5])
    have hΔR_le : ‖ΔR v‖ ≤ 2 * (ς ^ 2 * (1 + |v|) ^ 5) := by
      have hid : ΔR v = (π ^ 2 / 36 : ℂ) * ((ς ^ 2 : ℂ) *
          (3 * (1 + (v : ℂ) * Complex.I) ^ 2 + 3 * (ς ^ 2 : ℂ) * (1 + (v : ℂ) * Complex.I) + (ς ^ 2 : ℂ) ^ 2)) := by
        dsimp [ΔR]; push_cast; ring
      rw [hid, norm_mul, norm_mul]
      have hpi36 : ‖(π ^ 2 / 36 : ℂ)‖ ≤ 2 / 7 := by
        rw [show (π ^ 2 / 36 : ℂ) = ((π ^ 2 / 36 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        have : π < 3.15 := Real.pi_lt_d2
        nlinarith [Real.pi_pos]
      have hw : ‖1 + (v : ℂ) * Complex.I‖ ≤ 1 + |v| := by
        calc ‖1 + (v : ℂ) * Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = 1 + |v| := by rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      have hς2_le1 : ς ^ 2 ≤ 1 := by nlinarith [hς_pos, hς_le1]
      have hς2_norm : ‖(ς ^ 2 : ℂ)‖ = ς ^ 2 := by
        rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      have hsum_le : ‖3 * (1 + (v : ℂ) * Complex.I) ^ 2 + 3 * (ς ^ 2 : ℂ) * (1 + (v : ℂ) * Complex.I) + (ς ^ 2 : ℂ) ^ 2‖ ≤
          7 * (1 + |v|) ^ 5 := by
        have h1 : ‖3 * (1 + (v : ℂ) * Complex.I) ^ 2‖ ≤ 3 * (1 + |v|) ^ 5 := by
          rw [norm_mul, norm_pow, show ‖(3 : ℂ)‖ = 3 by norm_num]
          have : ‖1 + (v : ℂ) * Complex.I‖ ^ 2 ≤ (1 + |v|) ^ 5 :=
            (pow_le_pow_left₀ (norm_nonneg _) hw 2).trans (pow_le_pow_right₀ h1v_ge1 (by norm_num))
          linarith
        have h2 : ‖3 * (ς ^ 2 : ℂ) * (1 + (v : ℂ) * Complex.I)‖ ≤ 3 * (1 + |v|) ^ 5 := by
          rw [norm_mul, norm_mul, show ‖(3 : ℂ)‖ = 3 by norm_num, hς2_norm]
          have h15 : 1 + |v| ≤ (1 + |v|) ^ 5 := by simpa using pow_le_pow_right₀ h1v_ge1 (show 1 ≤ 5 by norm_num)
          have hwn : ‖1 + (v : ℂ) * Complex.I‖ ≤ (1 + |v|) ^ 5 := hw.trans h15
          have hς2_nn : 0 ≤ ς ^ 2 := sq_nonneg ς
          nlinarith only [hς2_le1, hς2_nn, hwn, norm_nonneg (1 + (v : ℂ) * Complex.I)]
        have h3 : ‖(ς ^ 2 : ℂ) ^ 2‖ ≤ (1 + |v|) ^ 5 := by
          rw [norm_pow, hς2_norm]
          have h15 : 1 ≤ (1 + |v|) ^ 5 := one_le_pow₀ h1v_ge1
          have hς2_nn : 0 ≤ ς ^ 2 := sq_nonneg ς
          nlinarith only [hς2_le1, hς2_nn, h15]
        calc ‖_‖ ≤ ‖3 * (1 + (v : ℂ) * Complex.I) ^ 2 + 3 * (ς ^ 2 : ℂ) * (1 + (v : ℂ) * Complex.I)‖ + ‖(ς ^ 2 : ℂ) ^ 2‖ := norm_add_le _ _
          _ ≤ (‖3 * (1 + (v : ℂ) * Complex.I) ^ 2‖ + ‖3 * (ς ^ 2 : ℂ) * (1 + (v : ℂ) * Complex.I)‖) + ‖(ς ^ 2 : ℂ) ^ 2‖ :=
              add_le_add (norm_add_le _ _) le_rfl
          _ ≤ 7 * (1 + |v|) ^ 5 := by linarith
      rw [hς2_norm]
      calc ‖(π ^ 2 / 36 : ℂ)‖ * (ς ^ 2 * ‖3 * (1 + (v : ℂ) * Complex.I) ^ 2 + 3 * (ς ^ 2 : ℂ) * (1 + (v : ℂ) * Complex.I) + (ς ^ 2 : ℂ) ^ 2‖)
          ≤ (2 / 7) * (ς ^ 2 * (7 * (1 + |v|) ^ 5)) := by gcongr
        _ = 2 * (ς ^ 2 * (1 + |v|) ^ 5) := by ring
    have hΔR_16 : ‖ΔR v‖ ≤ 64 := hΔR_le.trans (by linarith [hς2_1v5])
    have hA_diff : ‖A_ext τ - 1‖ ≤ 2 * C_A * (ς ^ 2 * (1 + |v|) ^ 5) := by
      have hτ_im : τ.im ≤ 0 := by simp [τ, hς_pos.le]
      have hA := hAext_bd τ (hτ_lt.le.trans hr_le_r₀) hτ_im
      rw [← hς2_eq] at hA
      have h1 : ς ^ 2 * ‖τ‖ ≤ ς ^ 2 * (1 + |v|) ^ 5 := by
        have h1' : ‖τ‖ ≤ 1 + |v| := hτ_norm.trans (mul_le_of_le_one_left (by positivity) hς_le1)
        have h2' : 1 + |v| ≤ (1 + |v|) ^ 5 := by simpa using pow_le_pow_right₀ h1v_ge1 (show 1 ≤ 5 by norm_num)
        exact mul_le_mul_of_nonneg_left (h1'.trans h2') (sq_nonneg ς)
      have h2 : ‖τ‖ ^ 2 ≤ ς ^ 2 * (1 + |v|) ^ 5 := by
        have hpow : (1 + |v|) ^ 2 ≤ (1 + |v|) ^ 5 := pow_le_pow_right₀ h1v_ge1 (by norm_num)
        calc ‖τ‖ ^ 2 ≤ (ς * (1 + |v|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hτ_norm 2
          _ = ς ^ 2 * (1 + |v|) ^ 2 := mul_pow _ _ 2
          _ ≤ ς ^ 2 * (1 + |v|) ^ 5 := by gcongr
      calc ‖A_ext τ - 1‖ ≤ C_A * (ς ^ 2 * ‖τ‖ + ‖τ‖ ^ 2) := hA
        _ ≤ C_A * (ς ^ 2 * (1 + |v|) ^ 5 + ς ^ 2 * (1 + |v|) ^ 5) := by gcongr
        _ = 2 * C_A * (ς ^ 2 * (1 + |v|) ^ 5) := by ring
    have hdiff_factor : ‖Complex.exp ΔP * A_ext τ - Complex.exp (ΔR v)‖ ≤
        (Real.exp M_dp * (2 * C_A + (10 + M_θ)) + Real.exp 64 * 2) * (ς ^ 2 * (1 + |v|) ^ 5) := by
      have hdecomp : Complex.exp ΔP * A_ext τ - Complex.exp (ΔR v) =
          Complex.exp ΔP * (A_ext τ - 1) + (Complex.exp ΔP - 1) - (Complex.exp (ΔR v) - 1) := by ring
      rw [hdecomp]
      have he1 : ‖Complex.exp ΔP‖ ≤ Real.exp M_dp := by
        rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hΔP_M)
      have he2 : ‖Complex.exp ΔP - 1‖ ≤ Real.exp M_dp * ((10 + M_θ) * (ς ^ 2 * (1 + |v|) ^ 5)) :=
        (norm_exp_sub_one_le hΔP_M).trans (mul_le_mul_of_nonneg_left hΔP_le (Real.exp_pos _).le)
      have he3 : ‖Complex.exp (ΔR v) - 1‖ ≤ Real.exp 64 * (2 * (ς ^ 2 * (1 + |v|) ^ 5)) :=
        (norm_exp_sub_one_le hΔR_16).trans (mul_le_mul_of_nonneg_left hΔR_le (Real.exp_pos _).le)
      calc ‖Complex.exp ΔP * (A_ext τ - 1) + (Complex.exp ΔP - 1) - (Complex.exp (ΔR v) - 1)‖
          ≤ ‖Complex.exp ΔP * (A_ext τ - 1)‖ + ‖Complex.exp ΔP - 1‖ + ‖Complex.exp (ΔR v) - 1‖ :=
            (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ Real.exp M_dp * (2 * C_A * (ς ^ 2 * (1 + |v|) ^ 5)) +
            Real.exp M_dp * ((10 + M_θ) * (ς ^ 2 * (1 + |v|) ^ 5)) +
            Real.exp 64 * (2 * (ς ^ 2 * (1 + |v|) ^ 5)) := by
            rw [norm_mul]
            exact add_le_add (add_le_add (mul_le_mul he1 hA_diff (norm_nonneg _) (Real.exp_pos _).le) he2) he3
        _ = _ := by ring
    -- Note: `C_pt` used `Real.exp 16` instead of `Real.exp 64`! Let's fix `C_pt` to `Real.exp 64` in the definition above?
    -- Wait: let's finish the `calc` using `C_pt` (we'll change `16` to `64` in `C_pt` right away).
    have hR1 : ‖R_v v‖ * ‖Complex.exp (P₀ v)‖ ≤ Real.exp (π ^ 2 / 36 + π ^ 2 * S_w + |CtOuter.ctTheta1 (-1)|) *
        Real.exp (-(π ^ 2 / 12) * v ^ 2) :=
      (mul_le_of_le_one_left (norm_nonneg _) hRv_le1).trans hP₀_le
    calc ‖R_v v‖ * ‖Complex.exp (P₀ v)‖ * ‖Complex.exp ΔP * A_ext τ - Complex.exp (ΔR v)‖
        ≤ (Real.exp (π ^ 2 / 36 + π ^ 2 * S_w + |CtOuter.ctTheta1 (-1)|) * Real.exp (-(π ^ 2 / 12) * v ^ 2)) *
          ((Real.exp M_dp * (2 * C_A + (10 + M_θ)) + Real.exp 64 * 2) * (ς ^ 2 * (1 + |v|) ^ 5)) :=
          mul_le_mul hR1 hdiff_factor (norm_nonneg _) (by positivity)
      _ = (Real.exp (π ^ 2 / 36 + π ^ 2 * S_w + |CtOuter.ctTheta1 (-1)|) *
            (Real.exp M_dp * (2 * C_A + (10 + M_θ)) + Real.exp 64 * 2)) *
          ς ^ 2 * ((1 + |v|) ^ 5 * Real.exp (-(π ^ 2 / 12) * v ^ 2)) := by ring
  -- Integrate over `Icc (-V) V`:
  have hcont_act : ContinuousOn (fun v : ℝ =>
      mellinK0 c ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) ξ * W ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I)) (Icc (-V) V) := by
    have hline : ContinuousOn (fun v : ℝ => (ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) (Icc (-V) V) := by fun_prop
    have hK := (differentiableOn_mellinK0 hc0 ξ).continuousOn.comp hline fun v _ => by
      change |((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I).re| < 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      rw [abs_of_pos hς_pos]
      have hς_lt1 : ς < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
      exact hς_lt1
    have hW' := hW.cont.comp hline fun v _ => by
      change 0 ≤ ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I).re ∧
        ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I).re ≤ 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      exact ⟨hς_pos.le, hς_le1⟩
    exact hK.mul hW'
  have hcont_ref : ContinuousOn (fun v : ℝ =>
      ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
        (R_v v * Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
          Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)))) (Icc (-V) V) := by
    have hR : ContinuousOn R_v (Icc (-V) V) :=
      ContinuousOn.cpow (by fun_prop) continuousOn_const fun v _ => Or.inl (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
        linarith [sq_nonneg ς])
    exact continuousOn_const.mul (hR.mul (by fun_prop))
  have hcomb : ((1 / (2 * π) : ℝ) : ℂ) *
        (∫ v in Icc (-V) V,
          mellinK0 c ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) ξ * W ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I)) -
      ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
        (((1 / (2 * π) : ℝ) : ℂ) *
          ∫ v in Icc (-V) V,
            R_v v * Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
              Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))) =
      ((1 / (2 * π) : ℝ) : ℂ) *
        ∫ v in Icc (-V) V,
          (mellinK0 c ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) ξ * W ((ς : ℂ) + ((ς * v : ℝ) : ℂ) * Complex.I) -
            ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
              (R_v v * Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
                Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)))) := by
    rw [integral_sub (hcont_act.integrableOn_compact isCompact_Icc) (hcont_ref.integrableOn_compact isCompact_Icc),
      integral_const_mul, mul_sub]
    ring
  rw [hcomb, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hc43 : c ^ (-(2 / 3 : ℝ)) * ς ^ 2 = c ^ (-(4 / 3 : ℝ)) := by
    rw [hς2_eq, ← Real.rpow_add hc0]; norm_num
  calc (1 / (2 * π)) * ‖∫ v in Icc (-V) V, _‖
      ≤ (1 / (2 * π)) * ∫ v in Icc (-V) V, ‖_‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (1 / (2 * π)) * ∫ v in Icc (-V) V,
          (π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) *
            (C_pt * ς ^ 2 * ((1 + |v|) ^ 5 * Real.exp (-(π ^ 2 / 12) * v ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (setIntegral_mono_on
          ((hcont_act.sub hcont_ref).norm.integrableOn_compact isCompact_Icc)
          ((hI5_int.const_mul _).const_mul _).integrableOn measurableSet_Icc hpt_bd) (by positivity)
    _ = (1 / (2 * π)) * ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) * (C_pt * ς ^ 2)) *
          ∫ v in Icc (-V) V, (1 + |v|) ^ 5 * Real.exp (-(π ^ 2 / 12) * v ^ 2) := by
        rw [integral_const_mul, integral_const_mul]; ring
    _ ≤ (1 / (2 * π)) * ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) * (C_pt * ς ^ 2)) * I5 := by
        refine mul_le_mul_of_nonneg_left (setIntegral_le_integral hI5_int (Eventually.of_forall fun v => by positivity))
          (by positivity)
    _ = ((π ^ 2 / 4 * |uctCAi|) / (2 * π) * C_pt * I5) * (c ^ (-(2 / 3 : ℝ)) * ς ^ 2) := by ring
    _ = ((π ^ 2 / 4 * |uctCAi|) / (2 * π) * C_pt * I5) * c ^ (-(4 / 3 : ℝ)) := by rw [hc43]
    _ ≤ C_core * c ^ (-(4 / 3 : ℝ)) := by gcongr; exact le_max_right _ _

/-! ### Section 4: Airy-window tails (`|v| > ς^{-2/5}`) -/

/-- Reference tail on `|v| > ς^{-2/5}`: Gaussian decay gives `O_{S_w}(c^{-4/3})`. -/
private lemma airy_window_ref_tail {U S_w : ℝ} (hU : 1 ≤ U) (hSw : 0 < S_w) :
    ∃ C_rt : ℝ, 0 < C_rt ∧ ∀ {c L : ℝ},
      60 ≤ c → -(π ^ 2 * U) ≤ c ^ (2 / 3 : ℝ) * L → c ^ (2 / 3 : ℝ) * L ≤ π ^ 2 * S_w →
      let ς : ℝ := c ^ (-(1 / 3 : ℝ))
      let V : ℝ := ς ^ (-(2 / 5 : ℝ))
      let x : ℝ := -ceBeta1 * (c ^ (2 / 3 : ℝ) * L / π ^ 2) + ceBeta1 * (CtOuter.ctTheta1 (-1) / π ^ 2) * ς
      ‖((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
          (((1 / (2 * π) : ℝ) : ℂ) *
            ∫ v in (Icc (-V) V)ᶜ,
              (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
                Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
                  Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)))‖ ≤
        C_rt * c ^ (-(4 / 3 : ℝ)) := by
  have hG_int : Integrable (fun v : ℝ => Real.exp (-(π ^ 2 / 24) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  set IG : ℝ := ∫ v : ℝ, Real.exp (-(π ^ 2 / 24) * v ^ 2)
  have hIG_nn : 0 ≤ IG := integral_nonneg fun v => (Real.exp_pos _).le
  set K_exp : ℝ := Real.exp (π ^ 2 / 36 * 8 + π ^ 2 * S_w + |CtOuter.ctTheta1 (-1)|)
  set K_tail : ℝ := (Nat.factorial 5 : ℝ) / (π ^ 2 / 24) ^ 5
  set C_rt : ℝ := max 1 ((π ^ 2 / 4 * |uctCAi|) / (2 * π) * K_exp * K_tail * IG)
  refine ⟨C_rt, lt_of_lt_of_le one_pos (le_max_left _ _), fun {c L} hc hL_lo hL_hi => ?_⟩
  intro ς V x
  have hc0 : 0 < c := by linarith
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le1 : ς ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hς2_eq : ς ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
    dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hcς_eq : c * ς = c ^ (2 / 3 : ℝ) := by
    dsimp [ς]; conv_lhs => arg 1; rw [← Real.rpow_one c]
    rw [← Real.rpow_add hc0]; norm_num
  have hV_pos : 0 < V := Real.rpow_pos_of_pos hς_pos _
  have hcsx : ceCs * x = -(c ^ (2 / 3 : ℝ) * L - CtOuter.ctTheta1 (-1) * ς) := by
    calc ceCs * x = -(ceCs * ceBeta1) * (c ^ (2 / 3 : ℝ) * L / π ^ 2) +
          (ceCs * ceBeta1) * (CtOuter.ctTheta1 (-1) / π ^ 2) * ς := by dsimp [x]; ring
      _ = -(π ^ 2) * (c ^ (2 / 3 : ℝ) * L / π ^ 2) + π ^ 2 * (CtOuter.ctTheta1 (-1) / π ^ 2) * ς := by
          rw [ceCs_mul_ceBeta1']
      _ = -(c ^ (2 / 3 : ℝ) * L - CtOuter.ctTheta1 (-1) * ς) := by field_simp [Real.pi_ne_zero]; ring
  have hpt : ∀ v ∈ (Icc (-V) V)ᶜ,
      ‖(((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
          Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))‖ ≤
      K_exp * (K_tail * ς ^ 2) * Real.exp (-(π ^ 2 / 24) * v ^ 2) := by
    intro v hv
    have hv_gt : V < |v| := by
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hv
      rcases hv with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hv2_ge : V ^ 2 ≤ v ^ 2 := by rw [← sq_abs v]; exact pow_le_pow_left₀ hV_pos.le hv_gt.le 2
    have hR_le1 : ‖(((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
      have hne : ((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I ≠ 0 := fun h0 => by
        have := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.zero_re] at this
        nlinarith [sq_nonneg ς]
      have hge1 : 1 ≤ ‖((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I‖ := by
        have := Complex.re_le_norm (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero] at this
        linarith [sq_nonneg ς]
      rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp,
        show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re,
        ← Real.rpow_def_of_pos (lt_of_lt_of_le one_pos hge1)]
      exact Real.rpow_le_one_of_one_le_of_nonpos hge1 (by norm_num)
    have hexp_le : ‖Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
          Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))‖ ≤
        K_exp * Real.exp (-(π ^ 2 / 24) * V ^ 2) * Real.exp (-(π ^ 2 / 24) * v ^ 2) := by
      rw [Complex.norm_exp, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      set a : ℝ := 1 + ς ^ 2
      have ha_ge1 : 1 ≤ a := by dsimp [a]; linarith [sq_nonneg ς]
      have ha_le2 : a ≤ 2 := by dsimp [a]; nlinarith [hς_pos, hς_le1]
      have hre_cube : ((π ^ 2 / 36 : ℂ) * ((a : ℂ) + (v : ℂ) * Complex.I) ^ 3).re =
          π ^ 2 / 36 * (a ^ 3 - 3 * a * v ^ 2) := by
        have h : ((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 =
            ((a ^ 3 - 3 * a * v ^ 2 : ℝ) : ℂ) + ((3 * a ^ 2 * v - v ^ 3 : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq, Complex.I_pow_three]; ring
        rw [h, show (π ^ 2 / 36 : ℂ) = ((π ^ 2 / 36 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      have hre_lin : (Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)).re = ceCs * x := by
        simp [Complex.mul_re]
      rw [Complex.sub_re, hre_cube, hre_lin, hcsx]
      have ha3 : a ^ 3 ≤ 8 := by
        calc a ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) ha_le2 3
          _ = 8 := by norm_num
      have hav : v ^ 2 ≤ a * v ^ 2 := by nlinarith [sq_nonneg v]
      have hθ_le : -CtOuter.ctTheta1 (-1) * ς ≤ |CtOuter.ctTheta1 (-1)| := by
        calc -CtOuter.ctTheta1 (-1) * ς ≤ |-CtOuter.ctTheta1 (-1) * ς| := le_abs_self _
          _ = |CtOuter.ctTheta1 (-1)| * ς := by rw [abs_mul, abs_neg, abs_of_pos hς_pos]
          _ ≤ |CtOuter.ctTheta1 (-1)| * 1 := mul_le_mul_of_nonneg_left hς_le1 (abs_nonneg _)
          _ = |CtOuter.ctTheta1 (-1)| := mul_one _
      have hpi2 : 0 ≤ π ^ 2 := sq_nonneg π
      nlinarith
    have htail_exp : Real.exp (-(π ^ 2 / 24) * V ^ 2) ≤ K_tail * ς ^ 2 := by
      have hu : 0 < (π ^ 2 / 24) * V ^ 2 := by positivity
      have h1 := exp_neg_le_factorial_div hu 5
      rw [neg_mul]
      have hV10 : (V ^ 2) ^ 5 = ς ^ (-(4 : ℝ)) := by
        dsimp [V]
        rw [← pow_mul, ← Real.rpow_natCast _ 10, ← Real.rpow_mul hς_pos.le]; norm_num
      have hς4_le : ς ^ (4 : ℝ) ≤ ς ^ 2 := by
        rw [← Real.rpow_natCast ς 2]
        exact Real.rpow_le_rpow_of_exponent_ge hς_pos hς_le1 (by norm_num)
      calc Real.exp (-((π ^ 2 / 24) * V ^ 2))
          ≤ (Nat.factorial 5 : ℝ) / ((π ^ 2 / 24) * V ^ 2) ^ 5 := h1
        _ = K_tail * ((V ^ 2) ^ 5)⁻¹ := by dsimp [K_tail]; rw [mul_pow]; ring
        _ = K_tail * ς ^ (4 : ℝ) := by rw [hV10, ← Real.rpow_neg hς_pos.le, neg_neg]
        _ ≤ K_tail * ς ^ 2 := mul_le_mul_of_nonneg_left hς4_le (by dsimp [K_tail]; positivity)
    rw [norm_mul]
    calc ‖_‖ * ‖_‖ ≤ 1 * (K_exp * Real.exp (-(π ^ 2 / 24) * V ^ 2) * Real.exp (-(π ^ 2 / 24) * v ^ 2)) :=
          mul_le_mul hR_le1 hexp_le (norm_nonneg _) zero_le_one
      _ ≤ K_exp * (K_tail * ς ^ 2) * Real.exp (-(π ^ 2 / 24) * v ^ 2) := by
          rw [one_mul]
          have hK_nn : 0 ≤ K_exp := (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail_exp hK_nn) (Real.exp_pos _).le
  have hcont_ref : Continuous (fun v : ℝ =>
      (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
        Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
          Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))) := by
    have hR : Continuous (fun v : ℝ => (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))) :=
      Continuous.cpow (by fun_prop) continuous_const fun v => Or.inl (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
        linarith [sq_nonneg ς])
    exact hR.mul (by fun_prop)
  have hc43 : c ^ (-(2 / 3 : ℝ)) * ς ^ 2 = c ^ (-(4 / 3 : ℝ)) := by
    rw [hς2_eq, ← Real.rpow_add hc0]; norm_num
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc (π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) * ((1 / (2 * π)) * ‖∫ v in (Icc (-V) V)ᶜ, _‖)
      ≤ (π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) * ((1 / (2 * π)) * ∫ v in (Icc (-V) V)ᶜ, ‖_‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)) (by positivity)
    _ ≤ (π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) *
          ((1 / (2 * π)) * ∫ v in (Icc (-V) V)ᶜ, K_exp * (K_tail * ς ^ 2) * Real.exp (-(π ^ 2 / 24) * v ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        have hint_lhs : IntegrableOn (fun v : ℝ => ‖(((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
              Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
                Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))‖) (Icc (-V) V)ᶜ :=
          ((hG_int.const_mul (K_exp * (K_tail * ς ^ 2))).integrableOn).mono'
            (hcont_ref.norm.aestronglyMeasurable) ((ae_restrict_mem measurableSet_Icc.compl).mono fun v hv => by
              rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt v hv)
        exact setIntegral_mono_on hint_lhs ((hG_int.const_mul _).integrableOn) measurableSet_Icc.compl hpt
    _ = (π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) *
          ((1 / (2 * π)) * (K_exp * (K_tail * ς ^ 2) * ∫ v in (Icc (-V) V)ᶜ, Real.exp (-(π ^ 2 / 24) * v ^ 2))) := by
        rw [integral_const_mul]
    _ ≤ (π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) * ((1 / (2 * π)) * (K_exp * (K_tail * ς ^ 2) * IG)) := by
        gcongr
        exact setIntegral_le_integral hG_int (Eventually.of_forall fun v => (Real.exp_pos _).le)
    _ = ((π ^ 2 / 4 * |uctCAi|) / (2 * π) * K_exp * K_tail * IG) * (c ^ (-(2 / 3 : ℝ)) * ς ^ 2) := by ring
    _ = ((π ^ 2 / 4 * |uctCAi|) / (2 * π) * K_exp * K_tail * IG) * c ^ (-(4 / 3 : ℝ)) := by rw [hc43]
    _ ≤ C_rt * c ^ (-(4 / 3 : ℝ)) := by gcongr; exact le_max_right _ _

set_option maxHeartbeats 400000 in
/-- Actual tail on `|t| > ς^{3/5}` (i.e. `|v| > ς^{-2/5}`): vertical-line phase decay from
`MellinPhaseBounds` (`integral_im_stripG_ge`, `re_mellinPhi_real_le`, `binetDiff_norm_le`) plus
the polynomial bound `‖W(ς + i t)‖ ≤ C_W c^N (1 + |t|)^N` yields `O(c^{-4/3})`. -/
private lemma airy_window_actual_tail {U S_w C_W : ℝ} {N : ℕ}
    (hU : 1 ≤ U) (hSw : 0 < S_w) (hCW : 0 ≤ C_W) :
    ∃ (c₂ C_at : ℝ), 60 ≤ c₂ ∧ 0 < C_at ∧
      ∀ {c L : ℝ} {W : ℂ → ℂ} {η_W : ℝ},
        c₂ ≤ c → 0 < η_W → StripW1 η_W W →
        -(π ^ 2 * U) ≤ c ^ (2 / 3 : ℝ) * L → c ^ (2 / 3 : ℝ) * L ≤ π ^ 2 * S_w →
        (∀ t : ℝ, ‖W (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_W * c ^ N * (1 + |t|) ^ N) →
        let ς : ℝ := c ^ (-(1 / 3 : ℝ))
        let V : ℝ := ς ^ (-(2 / 5 : ℝ))
        ‖((c ^ (1 / 3 : ℝ) / (2 * π) : ℝ) : ℂ) *
            ∫ t in (Icc (-(ς * V)) (ς * V))ᶜ,
              mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) (Real.exp L / π ^ 2) *
                W ((ς : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C_at * c ^ (-(4 / 3 : ℝ)) := by
  -- Choose `c₂` large enough that `(3 / 28) * c^{2/3} ≥ N + 2`:
  set c₂ : ℝ := max 60 ((10 * ((N : ℝ) + 2)) ^ (3 / 2 : ℝ) + 1)
  have hc₂_ge60 : 60 ≤ c₂ := le_max_left _ _
  set k : ℕ := 4 * N + 7
  set κ : ℝ := 3 / 56
  have hκ_pos : 0 < κ := by dsimp [κ]; norm_num
  set K_base : ℝ := 2 * Real.exp (1 + π ^ 2 * S_w) * C_W * (2 : ℝ) ^ N
  set K_fac : ℝ := (k.factorial : ℝ) / κ ^ k
  set C_at : ℝ := max 1 ((1 / (2 * π)) * K_base * (2 + 2) * K_fac)
  refine ⟨c₂, C_at, hc₂_ge60, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro c L W η_W hc hηW hW hL_lo hL_hi hW_poly
  intro ς V
  have hc60 : 60 ≤ c := hc₂_ge60.trans hc
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_le_half : ς ≤ 1 / 2 := by
    have h8 : (8 : ℝ) ≤ c := by linarith
    calc ς = c ^ (-(1 / 3 : ℝ)) := rfl
      _ ≤ (8 : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) h8 (by norm_num)
      _ = 1 / 2 := by
          rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hς_lt1 : ς < 1 := by linarith
  have hcς3 : c * ς ^ 3 = 1 := by
    dsimp [ς]; rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, show -(1 / 3 : ℝ) * (3 : ℕ) = -1 by norm_num,
      Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
  have hcς_eq : c * ς = c ^ (2 / 3 : ℝ) := by
    dsimp [ς]; conv_lhs => arg 1; rw [← Real.rpow_one c]
    rw [← Real.rpow_add hc0]; norm_num
  have hςV_eq : ς * V = c ^ (-(1 / 5 : ℝ)) := by
    dsimp [V]
    conv_lhs => arg 1; rw [← Real.rpow_one ς]
    rw [← Real.rpow_add hς_pos]; dsimp [ς]; rw [← Real.rpow_mul hc0.le]; norm_num
  have hςV_pos : 0 < ς * V := by rw [hςV_eq]; positivity
  set ξ : ℝ := Real.exp L / π ^ 2
  have hξ_pos : 0 < ξ := by positivity
  have hlogξ : Real.log (π ^ 2 * ξ) = L := by
    dsimp [ξ]; rw [mul_div_cancel₀ _ (sq_pos_of_pos Real.pi_pos).ne', Real.log_exp]
  -- Lower bound `(3 / 28) * c^{2/3} ≥ N + 2`:
  have hexp_ge : (N : ℝ) + 2 ≤ 2 * κ * c ^ (2 / 3 : ℝ) := by
    have h1 : (10 * ((N : ℝ) + 2)) ^ (3 / 2 : ℝ) ≤ c := le_trans (by linarith) ((le_max_right _ _).trans hc)
    have h2 : 10 * ((N : ℝ) + 2) ≤ c ^ (2 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 2 / 3)
      rw [← Real.rpow_mul (by positivity), show (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 by norm_num, Real.rpow_one] at this
      exact this
    dsimp [κ]; linarith
  -- Vertical bound on `‖mellinK0 c (ς + i t) ξ‖` for all `t : ℝ`:
  have hK0_bd : ∀ t : ℝ, ‖mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ‖ ≤
      2 * Real.exp (1 + π ^ 2 * S_w) *
        Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log |t|)))) := by
    have hnonneg : ∀ t : ℝ, 0 ≤ t →
        ‖mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ‖ ≤
          2 * Real.exp (1 + π ^ 2 * S_w) *
            Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t)))) := by
      intro t ht
      set ζ : ℂ := (ς : ℂ) + (t : ℂ) * Complex.I
      have hre : ζ.re = ς := by simp [ζ]
      have hpow : ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ ≤ 2 := by
        have h1 := norm_one_sub_cpow_neg_half_le (s := ς) (τ := t) hς_le_half
        have h2 : (1 + |t|) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg t]) (by norm_num)
        linarith
      have hbin : ‖Complex.exp (FormalResearch.Asymptotics.binetDiff c ζ)‖ ≤ Real.exp (1 / 4) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
        have h1 := FormalResearch.Asymptotics.binetDiff_norm_le hc0 (ζ := ζ) (by rw [hre]; exact hς_lt1)
        rw [hre] at h1
        have hinv : 1 / (1 - ς) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        refine h1.trans ?_
        calc 1 / (12 * c) * (1 / (1 - ς) + 1) ≤ 1 / (12 * 1) * (2 + 1) := by gcongr
          _ = 1 / 4 := by norm_num
      have hphi := mellinPhi_re_vertical (σ := ς) (ξ := ξ) (τ := t) hς_pos hς_lt1 hξ_pos
      have hφ0 := re_mellinPhi_real_le hς_pos hς_le_half hξ_pos
      rw [hlogξ] at hφ0
      have hU_ge : 2 * κ * ς * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t)) ≤ vertUpsilon ς t := by
        rcases eq_or_lt_of_le ht with rfl | htpos
        · simp [vertUpsilon]
        · have hge := integral_im_stripG_ge hς_pos hς_le_half htpos
          simpa [vertUpsilon, κ, mul_assoc] using hge
      have hexpphi : ‖Complex.exp ((c : ℂ) * mellinPhi ζ ξ)‖ ≤
          Real.exp (1 / 2 + π ^ 2 * S_w) *
            Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t)))) := by
        rw [Complex.norm_exp, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        rw [Complex.re_ofReal_mul]
        have h1 : (mellinPhi ζ ξ).re = (mellinPhi (ς : ℂ) ξ).re - vertUpsilon ς t := by
          have := hphi; rw [Complex.sub_re] at this; linarith
        rw [h1]
        have hreal : c * (mellinPhi (ς : ℂ) ξ).re ≤ 1 / 2 + π ^ 2 * S_w := by
          have := mul_le_mul_of_nonneg_left hφ0 hc0.le
          have h3 : c * (ς ^ 3 / 2 + ς * L) = 1 / 2 + c ^ (2 / 3 : ℝ) * L := by
            calc c * (ς ^ 3 / 2 + ς * L) = (c * ς ^ 3) / 2 + (c * ς) * L := by ring
              _ = 1 / 2 + c ^ (2 / 3 : ℝ) * L := by rw [hcς3, hcς_eq]
          linarith
        have hvert : 2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t)) ≤ c * vertUpsilon ς t := by
          have := mul_le_mul_of_nonneg_left hU_ge hc0.le
          calc 2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t))
              = c * (2 * κ * ς * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t))) := by rw [← hcς_eq]; ring
            _ ≤ c * vertUpsilon ς t := this
        linarith
      unfold mellinK0
      rw [norm_mul, norm_mul]
      calc ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (FormalResearch.Asymptotics.binetDiff c ζ)‖ *
            ‖Complex.exp ((c : ℂ) * mellinPhi ζ ξ)‖
          ≤ 2 * Real.exp (1 / 4) *
              (Real.exp (1 / 2 + π ^ 2 * S_w) *
                Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t))))) := by
            gcongr
        _ = 2 * (Real.exp (1 / 4) * Real.exp (1 / 2 + π ^ 2 * S_w)) *
              Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t)))) := by ring
        _ ≤ 2 * Real.exp (1 + π ^ 2 * S_w) *
              Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t)))) := by
            rw [← Real.exp_add]
            have : Real.exp (1 / 4 + (1 / 2 + π ^ 2 * S_w)) ≤ Real.exp (1 + π ^ 2 * S_w) :=
              Real.exp_le_exp.mpr (by linarith)
            gcongr
    intro t
    rcases le_total 0 t with ht | ht
    · simpa [abs_of_nonneg ht] using hnonneg t ht
    · have hconj : (ς : ℂ) + (t : ℂ) * Complex.I =
          starRingEnd ℂ ((ς : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
      have hre : ((ς : ℂ) + ((-t : ℝ) : ℂ) * Complex.I).re = ς := by simp
      rw [hconj, mellinK0_conj hξ_pos (by rw [hre]; exact hς_pos) (by rw [hre]; exact hς_lt1), Complex.norm_conj]
      simpa [abs_of_nonpos ht] using hnonneg (-t) (neg_nonneg.mpr ht)
  -- Exponential decay factor `c^{N + 1/3} * exp(-κ * c^{4/15}) ≤ K_fac * c^{-4/3}`:
  have hexp_decay : c ^ (1 / 3 : ℝ) * c ^ N * Real.exp (-(κ * c ^ (4 / 15 : ℝ))) ≤ K_fac * c ^ (-(4 / 3 : ℝ)) := by
    have hu : 0 < κ * c ^ (4 / 15 : ℝ) := by positivity
    have h1 := exp_neg_le_factorial_div hu k
    have hpow : (c ^ (4 / 15 : ℝ)) ^ k = c ^ ((4 / 15 : ℝ) * k) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    have hcomb : c ^ (1 / 3 : ℝ) * c ^ N * (c ^ ((4 / 15 : ℝ) * k))⁻¹ ≤ c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast c N, ← Real.rpow_neg hc0.le, ← Real.rpow_add hc0, ← Real.rpow_add hc0]
      refine Real.rpow_le_rpow_of_exponent_le hc1 ?_
      dsimp [k]; push_cast; linarith
    calc c ^ (1 / 3 : ℝ) * c ^ N * Real.exp (-(κ * c ^ (4 / 15 : ℝ)))
        ≤ c ^ (1 / 3 : ℝ) * c ^ N * ((k.factorial : ℝ) / (κ * c ^ (4 / 15 : ℝ)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K_fac * (c ^ (1 / 3 : ℝ) * c ^ N * (c ^ ((4 / 15 : ℝ) * k))⁻¹) := by
          dsimp [K_fac]; rw [mul_pow, hpow]; ring
      _ ≤ K_fac * c ^ (-(4 / 3 : ℝ)) := mul_le_mul_of_nonneg_left hcomb (by dsimp [K_fac]; positivity)
  -- Pointwise integrable majorant `M_at(t)` on `|t| > ς * V`:
  let M_at : ℝ → ℝ := fun t =>
    K_base * c ^ N * Real.exp (-(κ * c ^ (4 / 15 : ℝ))) * (if |t| ≤ 1 then 1 else |t| ^ (-(2 : ℝ)))
  have hpt_at : ∀ t ∈ (Icc (-(ς * V)) (ς * V))ᶜ,
      ‖mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M_at t := by
    intro t ht
    have ht_gt : ς * V < |t| := by
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hK := hK0_bd t
    have hW' := hW_poly t
    rw [norm_mul]
    by_cases ht1 : |t| ≤ 1
    · have h1t : (1 + |t|) ^ N ≤ (2 : ℝ) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      have ht2_ge : c ^ (-(2 / 5 : ℝ)) ≤ t ^ 2 := by
        rw [← sq_abs t]
        calc c ^ (-(2 / 5 : ℝ)) = (c ^ (-(1 / 5 : ℝ))) ^ 2 := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
          _ = (ς * V) ^ 2 := by rw [hςV_eq]
          _ ≤ |t| ^ 2 := pow_le_pow_left₀ hςV_pos.le ht_gt.le 2
      have hmin : min (t ^ 2) 1 = t ^ 2 := min_eq_left (by rw [← sq_abs t]; nlinarith [abs_nonneg t])
      have hexp_ge' : κ * c ^ (4 / 15 : ℝ) ≤ 2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log |t|)) := by
        rw [hmin]
        have hmax : (0 : ℝ) ≤ max 0 (Real.log |t|) := le_max_left _ _
        have hmul : c ^ (4 / 15 : ℝ) = c ^ (2 / 3 : ℝ) * c ^ (-(2 / 5 : ℝ)) := by
          rw [← Real.rpow_add hc0]; norm_num
        have h1 : c ^ (4 / 15 : ℝ) ≤ c ^ (2 / 3 : ℝ) * t ^ 2 := by
          rw [hmul]; exact mul_le_mul_of_nonneg_left ht2_ge (by positivity)
        have h2 : κ * c ^ (4 / 15 : ℝ) ≤ κ * (c ^ (2 / 3 : ℝ) * t ^ 2) := mul_le_mul_of_nonneg_left h1 hκ_pos.le
        have h3 : 0 ≤ 2 * κ * c ^ (2 / 3 : ℝ) * max 0 (Real.log |t|) := by positivity
        linarith
      have hexp_le : Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log |t|)))) ≤
          Real.exp (-(κ * c ^ (4 / 15 : ℝ))) := Real.exp_le_exp.mpr (by linarith)
      dsimp only [M_at, K_base]
      rw [if_pos ht1, mul_one]
      calc ‖mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ‖ * ‖W ((ς : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (2 * Real.exp (1 + π ^ 2 * S_w) * Real.exp (-(κ * c ^ (4 / 15 : ℝ)))) * (C_W * c ^ N * (2 : ℝ) ^ N) := by
            exact mul_le_mul (hK.trans (mul_le_mul_of_nonneg_left hexp_le (by positivity)))
              (hW'.trans (mul_le_mul_of_nonneg_left h1t (by positivity))) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · have ht_gt1 : 1 < |t| := not_le.mp ht1
      have h1t : (1 + |t|) ^ N ≤ (2 : ℝ) ^ N * |t| ^ N := by
        calc (1 + |t|) ^ N ≤ (2 * |t|) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
          _ = (2 : ℝ) ^ N * |t| ^ N := mul_pow 2 |t| N
      have hmin : min (t ^ 2) 1 = 1 := min_eq_right (by rw [← sq_abs t]; nlinarith)
      have hlog_nn : 0 ≤ Real.log |t| := Real.log_nonneg ht_gt1.le
      have hmax : max 0 (Real.log |t|) = Real.log |t| := max_eq_right hlog_nn
      have hc415_le : c ^ (4 / 15 : ℝ) ≤ c ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
      have hpow_log : Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * Real.log |t|)) ≤ |t| ^ (-((N : ℝ) + 2)) := by
        rw [Real.rpow_def_of_pos (lt_trans one_pos ht_gt1)]
        refine Real.exp_le_exp.mpr ?_
        have := mul_le_mul_of_nonneg_right hexp_ge hlog_nn
        linarith
      have hcancel : |t| ^ (-((N : ℝ) + 2)) * |t| ^ N = |t| ^ (-(2 : ℝ)) := by
        rw [← Real.rpow_natCast |t| N, ← Real.rpow_add (lt_trans one_pos ht_gt1)]; congr 1; ring
      have hexp_le : Real.exp (-(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log |t|)))) ≤
          Real.exp (-(κ * c ^ (4 / 15 : ℝ))) * |t| ^ (-((N : ℝ) + 2)) := by
        rw [hmin, hmax]
        have hsplit : -(2 * κ * c ^ (2 / 3 : ℝ) * ((1 / 2 : ℝ) * 1 + Real.log |t|)) =
            -(κ * c ^ (2 / 3 : ℝ)) + -(2 * κ * c ^ (2 / 3 : ℝ) * Real.log |t|) := by ring
        rw [hsplit, Real.exp_add]
        exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) hpow_log (Real.exp_pos _).le (Real.exp_pos _).le
      dsimp only [M_at, K_base]
      rw [if_neg ht1]
      calc ‖mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ‖ * ‖W ((ς : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (2 * Real.exp (1 + π ^ 2 * S_w) * (Real.exp (-(κ * c ^ (4 / 15 : ℝ))) * |t| ^ (-((N : ℝ) + 2)))) *
              (C_W * c ^ N * ((2 : ℝ) ^ N * |t| ^ N)) :=
            mul_le_mul (hK.trans (mul_le_mul_of_nonneg_left hexp_le (by positivity)))
              (hW'.trans (mul_le_mul_of_nonneg_left h1t (by positivity))) (norm_nonneg _) (by positivity)
        _ = 2 * Real.exp (1 + π ^ 2 * S_w) * C_W * 2 ^ N * c ^ N * Real.exp (-(κ * c ^ (4 / 15 : ℝ))) *
              (|t| ^ (-((N : ℝ) + 2)) * |t| ^ N) := by ring
        _ = _ := by rw [hcancel]
  -- Integrate `t ↦ if |t| ≤ 1 then 1 else |t|^{-2}` over `ℝ`:
  have hbase_int : Integrable (fun t : ℝ => if |t| ≤ 1 then (1 : ℝ) else |t| ^ (-(2 : ℝ))) ∧
      ∫ t : ℝ, (if |t| ≤ 1 then (1 : ℝ) else |t| ^ (-(2 : ℝ))) ≤ 4 := by
    have hsplit_eq : (fun t : ℝ => if |t| ≤ 1 then (1 : ℝ) else |t| ^ (-(2 : ℝ))) =
        (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) +
        (Set.Ioi (1 : ℝ)).indicator (fun t => t ^ (-(2 : ℝ))) +
        (Set.Iio (-1 : ℝ)).indicator (fun t => (-t) ^ (-(2 : ℝ))) := by
      ext t
      by_cases h1 : |t| ≤ 1
      · have hmem : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp h1
        have hni : t ∉ Ioi (1 : ℝ) := fun h => by linarith [hmem.2, Set.mem_Ioi.mp h]
        have hnj : t ∉ Iio (-1 : ℝ) := fun h => by linarith [hmem.1, Set.mem_Iio.mp h]
        simp [h1, hmem, hni, hnj]
      · have hnm : t ∉ Icc (-1 : ℝ) 1 := fun h => h1 (abs_le.mpr h)
        have h1' : 1 < |t| := not_le.mp h1
        rcases lt_or_gt_of_ne (show t ≠ 0 by rintro rfl; exact h1 (by simp)) with ht | ht
        · have hlt : t < -1 := by rw [abs_of_neg ht] at h1'; linarith
          have hni : t ∉ Ioi (1 : ℝ) := fun h => by linarith [Set.mem_Ioi.mp h]
          have hnj : t ∈ Iio (-1 : ℝ) := hlt
          rw [ite_eq_right_iff.mpr (fun h => absurd h h1)]
          simp only [Pi.add_apply, Set.indicator_of_notMem hnm, Set.indicator_of_notMem hni,
            Set.indicator_of_mem hnj, zero_add, abs_of_neg ht]
        · have hgt : 1 < t := by rw [abs_of_pos ht] at h1'; linarith
          have hni : t ∈ Ioi (1 : ℝ) := hgt
          have hnj : t ∉ Iio (-1 : ℝ) := fun h => by linarith [Set.mem_Iio.mp h]
          rw [ite_eq_right_iff.mpr (fun h => absurd h h1)]
          simp only [Pi.add_apply, Set.indicator_of_notMem hnm, Set.indicator_of_mem hni,
            Set.indicator_of_notMem hnj, zero_add, add_zero, abs_of_pos ht]
    have hi1 : Integrable ((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
      (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
    have hi2 : Integrable ((Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-(2 : ℝ)))) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).integrable_indicator measurableSet_Ioi
    have hi3 : Integrable ((Set.Iio (-1 : ℝ)).indicator (fun t : ℝ => (-t) ^ (-(2 : ℝ)))) := by
      have hcomp := hi2.comp_neg
      refine hcomp.congr (Eventually.of_forall fun t => ?_)
      by_cases h : t < -1
      · have h1 : 1 < -t := by linarith
        simp [Set.indicator_of_mem (show t ∈ Iio (-1 : ℝ) from h),
          Set.indicator_of_mem (show -t ∈ Ioi (1 : ℝ) from h1)]
      · have h1 : -t ∉ Ioi (1 : ℝ) := fun hm => h (by linarith [Set.mem_Ioi.mp hm])
        simp [Set.indicator_of_notMem (show t ∉ Iio (-1 : ℝ) from h), Set.indicator_of_notMem h1]
    refine ⟨by rw [hsplit_eq]; exact (hi1.add hi2).add hi3, ?_⟩
    have hint_eq' : ∫ t : ℝ, (if |t| ≤ 1 then (1 : ℝ) else |t| ^ (-(2 : ℝ))) =
        (∫ t : ℝ, (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t) +
        (∫ t : ℝ, (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-(2 : ℝ))) t) +
        (∫ t : ℝ, (Set.Iio (-1 : ℝ)).indicator (fun t : ℝ => (-t) ^ (-(2 : ℝ))) t) := by
      calc ∫ t : ℝ, (if |t| ≤ 1 then (1 : ℝ) else |t| ^ (-(2 : ℝ)))
          = ∫ t : ℝ, (((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) +
              (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-(2 : ℝ)))) t +
              (Set.Iio (-1 : ℝ)).indicator (fun t : ℝ => (-t) ^ (-(2 : ℝ))) t) :=
            integral_congr_ae (Eventually.of_forall fun t => congrFun hsplit_eq t)
        _ = (∫ t : ℝ, ((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t +
              (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-(2 : ℝ))) t)) +
            (∫ t : ℝ, (Set.Iio (-1 : ℝ)).indicator (fun t : ℝ => (-t) ^ (-(2 : ℝ))) t) :=
            integral_add (hi1.add hi2) hi3
        _ = _ := by rw [integral_add hi1 hi2]
    rw [hint_eq']
    have hv1 : ∫ t : ℝ, (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t = 2 := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul, mul_one,
        Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]; norm_num
    have hv2 : ∫ t : ℝ, (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-(2 : ℝ))) t = 1 := by
      rw [integral_indicator measurableSet_Ioi, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]; norm_num
    have hv3 : ∫ t : ℝ, (Set.Iio (-1 : ℝ)).indicator (fun t : ℝ => (-t) ^ (-(2 : ℝ))) t = 1 := by
      have h1 : ∫ t : ℝ, (Set.Ioi (1 : ℝ)).indicator (fun u : ℝ => u ^ (-(2 : ℝ))) (-t) =
          ∫ t : ℝ, (Set.Ioi (1 : ℝ)).indicator (fun u : ℝ => u ^ (-(2 : ℝ))) t := by
        simpa using Measure.integral_comp_mul_left (a := (-1 : ℝ))
          (fun t : ℝ => (Set.Ioi (1 : ℝ)).indicator (fun u : ℝ => u ^ (-(2 : ℝ))) t)
      have heq : (fun t : ℝ => (Set.Iio (-1 : ℝ)).indicator (fun u : ℝ => (-u) ^ (-(2 : ℝ))) t) =
          fun t : ℝ => (Set.Ioi (1 : ℝ)).indicator (fun u : ℝ => u ^ (-(2 : ℝ))) (-t) := funext fun t => by
        by_cases h : t < -1
        · have h1' : (1 : ℝ) < -t := by linarith
          simp only [Set.indicator_of_mem (show t ∈ Iio (-1 : ℝ) from h),
            Set.indicator_of_mem (show -t ∈ Ioi (1 : ℝ) from h1')]
        · simp only [Set.indicator_of_notMem (show t ∉ Iio (-1 : ℝ) from h),
            Set.indicator_of_notMem (show -t ∉ Ioi (1 : ℝ) from fun hm => h (by linarith [Set.mem_Ioi.mp hm]))]
      rw [heq, h1, hv2]
    linarith
  have hcont_act : Continuous (fun t : ℝ =>
      mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) := by
    have hline : Continuous (fun t : ℝ => (ς : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have hK := (differentiableOn_mellinK0 hc0 ξ).continuousOn.comp_continuous hline fun t => by
      change |((ς : ℂ) + (t : ℂ) * Complex.I).re| < 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      rw [abs_of_pos hς_pos]; exact hς_lt1
    have hW' := hW.cont.comp_continuous hline fun t => by
      change 0 ≤ ((ς : ℂ) + (t : ℂ) * Complex.I).re ∧ ((ς : ℂ) + (t : ℂ) * Complex.I).re ≤ 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      exact ⟨hς_pos.le, hς_lt1.le⟩
    exact hK.mul hW'
  have hM_int : Integrable M_at := hbase_int.1.const_mul _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc (c ^ (1 / 3 : ℝ) / (2 * π)) * ‖∫ t in (Icc (-(ς * V)) (ς * V))ᶜ, _‖
      ≤ (c ^ (1 / 3 : ℝ) / (2 * π)) * ∫ t in (Icc (-(ς * V)) (ς * V))ᶜ, ‖_‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ ≤ (c ^ (1 / 3 : ℝ) / (2 * π)) * ∫ t in (Icc (-(ς * V)) (ς * V))ᶜ, M_at t := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hint_lhs : IntegrableOn (fun t : ℝ =>
              ‖mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)‖)
            (Icc (-(ς * V)) (ς * V))ᶜ :=
          hM_int.integrableOn.mono' hcont_act.norm.aestronglyMeasurable
            ((ae_restrict_mem measurableSet_Icc.compl).mono fun t ht => by
              rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt_at t ht)
        exact setIntegral_mono_on hint_lhs hM_int.integrableOn measurableSet_Icc.compl hpt_at
    _ ≤ (c ^ (1 / 3 : ℝ) / (2 * π)) * ∫ t : ℝ, M_at t := by
        refine mul_le_mul_of_nonneg_left (setIntegral_le_integral hM_int (Eventually.of_forall fun t => ?_)) (by positivity)
        dsimp [M_at, K_base]; split_ifs <;> positivity
    _ = (c ^ (1 / 3 : ℝ) / (2 * π)) * (K_base * c ^ N * Real.exp (-(κ * c ^ (4 / 15 : ℝ))) *
          ∫ t : ℝ, (if |t| ≤ 1 then (1 : ℝ) else |t| ^ (-(2 : ℝ)))) := by
        dsimp [M_at]; rw [integral_const_mul]
    _ ≤ (c ^ (1 / 3 : ℝ) / (2 * π)) * (K_base * c ^ N * Real.exp (-(κ * c ^ (4 / 15 : ℝ))) * 4) := by
        gcongr; exact hbase_int.2
    _ = ((1 / (2 * π)) * K_base * 4) * (c ^ (1 / 3 : ℝ) * c ^ N * Real.exp (-(κ * c ^ (4 / 15 : ℝ)))) := by ring
    _ ≤ ((1 / (2 * π)) * K_base * 4) * (K_fac * c ^ (-(4 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp_decay (by dsimp [K_base]; positivity)
    _ = ((1 / (2 * π)) * K_base * (2 + 2) * K_fac) * c ^ (-(4 / 3 : ℝ)) := by ring
    _ ≤ C_at * c ^ (-(4 / 3 : ℝ)) := by gcongr; exact le_max_right _ _

/-! ### Section 5: Main Airy-window lower bound (`uct:ce-band` (1)) -/

set_option maxHeartbeats 400000 in
/-- **Lemma `uct:ce-band` (1), Airy-window lower bound** (`CFT/sign_uncertainty/paper/constant_terms_upper.tex`,
lines 620–635, used by Proposition `fct:ce-band` in `constant_terms_five.tex`):

For any fixed `U ≥ 1`, `S_w > 0`, `r₀ > 0`, `η > 0`, `C₀, C_A, C_W ≥ 0`, `N : ℕ`, there exists
`C_U > 0` (independent of `c, L, W, A, A_ext`) such that for every `c ≥ 60`, every `L` in the
Airy window `-U ≤ c^{2/3} L / π² ≤ S_w`, every admissible multiplier `W` (`StripW1 η_W W` for some
`η_W > 0`, implied by `StripM1 W`) obeying the shifted-line polynomial bound
`‖W(ς + i t)‖ ≤ C_W c^N (1 + |t|)^N` (`ς = c^{-1/3}`) and the imaginary-edge factorization
`(uct:KW-hhat-edge)` at `ξ = e^L / π²` with combined amplitude `A` extending continuously to the
closed lower half-disc `{‖z‖ ≤ r₀ ∧ z.im ≤ 0}` and holomorphically to its interior with
`‖A_ext z - 1‖ ≤ C_A (c^{-2/3} ‖z‖ + ‖z‖²)` and `‖A τ‖ ≤ C₀ e^{-η|τ|}` on `ℝ`, the normalized
density `h_norm^{ĥ}(L) = uctHnormCE c L A` is real (`im = 0`) and satisfies
`-(C_U * c ^ (-(4 / 3 : ℝ))) ≤ (uctHnormCE c L A).re`.

Scope: complete for the Airy-window clause of Lemma `uct:ce-band` (1). Notice that the paper's
real-axis derivative bounds `|A^{(j)}(τ)| ≤ C_j e^{-η|τ|}` (`j = 1, 2`) are not needed for the
Airy-window bound (only `j = 0` is used for the finite-`c` fallback `60 ≤ c < c_0`). -/
theorem uct_ce_band_airy {U S_w r₀ η C₀ C_A C_W : ℝ} {N : ℕ}
    (hU : 1 ≤ U) (hSw : 0 < S_w) (hr₀ : 0 < r₀) (hη : 0 < η)
    (hC₀ : 0 ≤ C₀) (hCA : 0 ≤ C_A) (hCW : 0 ≤ C_W) :
    ∃ C_U : ℝ, 0 < C_U ∧
      ∀ {c L : ℝ} {W A_ext : ℂ → ℂ} {A : ℝ → ℂ} {η_W : ℝ},
        60 ≤ c → 0 < η_W → StripW1 η_W W →
        -(π ^ 2 * U) ≤ c ^ (2 / 3 : ℝ) * L → c ^ (2 / 3 : ℝ) * L ≤ π ^ 2 * S_w →
        (∀ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) (Real.exp L / π ^ 2) * W ((τ : ℂ) * Complex.I) =
          ((π ^ 2 / 4 * |uctCAi| * c ^ (-(5 / 6 : ℝ)) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((c * edgePhi L τ - CtOuter.outerTheta (-1) τ : ℝ) : ℂ)) *
            A τ * regSqrt (1 / c) τ) →
        Continuous A →
        (∀ τ : ℝ, ‖A τ‖ ≤ C₀ * Real.exp (-η * |τ|)) →
        ContinuousOn A_ext {z : ℂ | ‖z‖ ≤ r₀ ∧ z.im ≤ 0} →
        DifferentiableOn ℂ A_ext {z : ℂ | ‖z‖ < r₀ ∧ z.im < 0} →
        (∀ τ : ℝ, |τ| ≤ r₀ → A_ext (τ : ℂ) = A τ) →
        (∀ z : ℂ, ‖z‖ ≤ r₀ → z.im ≤ 0 →
          ‖A_ext z - 1‖ ≤ C_A * (c ^ (-(2 / 3 : ℝ)) * ‖z‖ + ‖z‖ ^ 2)) →
        (∀ t : ℝ, ‖W (((c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C_W * c ^ N * (1 + |t|) ^ N) →
        (uctHnormCE c L A).im = 0 ∧ -(C_U * c ^ (-(4 / 3 : ℝ))) ≤ (uctHnormCE c L A).re := by
  obtain ⟨c₁, C_core, hc₁60, hC_core, hcore⟩ := airy_window_core_diff hU hSw hr₀ hCA
  obtain ⟨C_rt, hC_rt, hrt⟩ := airy_window_ref_tail hU hSw
  obtain ⟨c₂, C_at, hc₂60, hC_at, hat⟩ := airy_window_actual_tail hU hSw hCW (N := N)
  set c₀ : ℝ := max c₁ c₂
  have hc₀60 : 60 ≤ c₀ := hc₁60.trans (le_max_left _ _)
  set C_large : ℝ := C_core + C_rt + C_at
  set C_fin : ℝ := (π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) * c₀ ^ (5 / 6 : ℝ)
  refine ⟨max C_large (max 1 C_fin), lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_right _ _)), ?_⟩
  intro c L W A_ext A η_W hc hηW hW hL_lo hL_hi hfac hA_cont hA0 hAext_cont hAext_hol hAext_real hAext_bd hW_poly
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  set ξ : ℝ := Real.exp L / π ^ 2
  have hξ_pos : 0 < ξ := by positivity
  set ς : ℝ := c ^ (-(1 / 3 : ℝ))
  have hς_pos : 0 < ς := Real.rpow_pos_of_pos hc0 _
  have hς_lt1 : ς < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)
  -- Identify `uctHnormCE c L A` with the vertical integral at `σ = 0` and at `σ = ς`, and prove it is real:
  have hrep0 := admiss_vert_rep_of_W1 hc1 hηW hW le_rfl one_pos hξ_pos
  have hrepς := admiss_vert_rep_of_W1 hc1 hηW hW hς_pos.le hς_lt1 hξ_pos
  have hH_eq0 : uctHnormCE c L A = ((c ^ (1 / 3 : ℝ) / (2 * π) : ℝ) : ℂ) *
      ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I) :=
    (uctHnormCE_eq_mellin hc0 hfac).symm
  have hH_real : uctHnormCE c L A =
      (((c ^ (1 / 3 : ℝ) * ξ * (hankelRho0 c (c * ξ) * admissLift c W (c * ξ))) : ℝ) : ℂ) := by
    rw [hH_eq0]
    have h0' : (∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I)) =
        ((2 * π * ξ : ℝ) : ℂ) * (((hankelRho0 c (c * ξ) * admissLift c W (c * ξ) : ℝ)) : ℂ) := by
      have h0 := hrep0
      simp only [Complex.ofReal_zero, zero_add] at h0
      rw [h0, ← mul_assoc, ← Complex.ofReal_mul]
      have h2piξ : 2 * π * ξ ≠ 0 := by positivity
      rw [mul_one_div_cancel h2piξ, Complex.ofReal_one, one_mul]
    rw [h0', ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1; field_simp [Real.pi_ne_zero]
  have hIm : (uctHnormCE c L A).im = 0 := by rw [hH_real, Complex.ofReal_im]
  refine ⟨hIm, ?_⟩
  by_cases hc_big : c₀ ≤ c
  · -- Large `c ≥ c₀ = max c₁ c₂`: compare shifted vertical integral against shifted Airy-square reference!
    have hint_eq : ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I) =
        ∫ t : ℝ, mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I) := by
      have h1 : ((1 / (2 * π * ξ) : ℝ) : ℂ) *
            ∫ τ : ℝ, mellinK0 c ((τ : ℂ) * Complex.I) ξ * W ((τ : ℂ) * Complex.I) =
          ((1 / (2 * π * ξ) : ℝ) : ℂ) *
            ∫ t : ℝ, mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I) := by
        simpa using hrep0.symm.trans hrepς
      exact mul_left_cancel₀ (by exact_mod_cast (by positivity : (0 : ℝ) < 1 / (2 * π * ξ)).ne') h1
    set V : ℝ := ς ^ (-(2 / 5 : ℝ))
    set x : ℝ := -ceBeta1 * (c ^ (2 / 3 : ℝ) * L / π ^ 2) + ceBeta1 * (CtOuter.ctTheta1 (-1) / π ^ 2) * ς
    let RefVal : ℝ := (π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ))) *
      (2 * √π / √ceCs * Real.exp (ceCs * c ^ (-(2 / 3 : ℝ)) * x) * airyAi x ^ 2)
    have hRefVal_nn : 0 ≤ RefVal := by
      dsimp [RefVal]; have := ceCs_pos; positivity
    have hRef_eq : (RefVal : ℂ) =
        ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
          (((1 / (2 * π) : ℝ) : ℂ) *
            ∫ v : ℝ, (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
              Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
                Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))) := by
      rw [uct_hhat_ref_shifted hc0 x, ← Complex.ofReal_mul]
    -- Split actual and reference integrals into `Icc` core and complement tail:
    have hact_int : Integrable (fun t : ℝ =>
        mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) := by
      obtain ⟨K, hK_nn, hK⟩ := norm_mellinK0_half_strip_decay hc0 hξ_pos
      obtain ⟨CW', hCW'⟩ := hW.bound
      have hς_half : ς ≤ 1 / 2 := by
        have h8 : (8 : ℝ) ≤ c := by linarith
        calc ς = c ^ (-(1 / 3 : ℝ)) := rfl
          _ ≤ (8 : ℝ) ^ (-(1 / 3 : ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num) h8 (by norm_num)
          _ = 1 / 2 := by rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      have hline : Continuous (fun t : ℝ => (ς : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
      have hcont : Continuous (fun t : ℝ =>
          mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) := by
        have h1 := (differentiableOn_mellinK0 hc0 ξ).continuousOn.comp_continuous hline fun t => by
          change |((ς : ℂ) + (t : ℂ) * Complex.I).re| < 1
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
          rw [abs_of_pos hς_pos]; exact hς_lt1
        have h2 := hW.cont.comp_continuous hline fun t => by
          change 0 ≤ ((ς : ℂ) + (t : ℂ) * Complex.I).re ∧ ((ς : ℂ) + (t : ℂ) * Complex.I).re ≤ 1
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
          exact ⟨hς_pos.le, hς_lt1.le⟩
        exact h1.mul h2
      have hdecay : Integrable (fun t : ℝ => (1 + |t|) ^ (-(1 + η_W))) := by
        have h1_ind : Integrable ((Ioi (1 : ℝ)).indicator (fun u : ℝ => u ^ (-(1 + η_W)))) :=
          (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).integrable_indicator measurableSet_Ioi
        have hpos_ind : Integrable ((Ioi (0 : ℝ)).indicator (fun t : ℝ => (1 + t) ^ (-(1 + η_W)))) := by
          refine (h1_ind.comp_add_right 1).congr (Eventually.of_forall fun t => ?_)
          by_cases h : 0 < t
          · have hm1 : t + 1 ∈ Ioi (1 : ℝ) := by show (1 : ℝ) < t + 1; linarith
            have hm2 : t ∈ Ioi (0 : ℝ) := h
            simp only [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2, add_comm]
          · have hm1 : t + 1 ∉ Ioi (1 : ℝ) := fun hm => h (by linarith [Set.mem_Ioi.mp hm])
            have hm2 : t ∉ Ioi (0 : ℝ) := h
            simp only [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]
        have hneg_ind : Integrable ((Iio (0 : ℝ)).indicator (fun t : ℝ => (1 - t) ^ (-(1 + η_W)))) := by
          refine hpos_ind.comp_neg.congr (Eventually.of_forall fun t => ?_)
          by_cases h : t < 0
          · have hm1 : t ∈ Iio (0 : ℝ) := h
            have hm2 : -t ∈ Ioi (0 : ℝ) := by show (0 : ℝ) < -t; linarith
            simp only [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2, sub_eq_add_neg]
          · have hm1 : t ∉ Iio (0 : ℝ) := h
            have hm2 : -t ∉ Ioi (0 : ℝ) := fun hm => h (by linarith [Set.mem_Ioi.mp hm])
            simp only [Set.indicator_of_notMem hm1, Set.indicator_of_notMem hm2]
        refine (hpos_ind.add hneg_ind).congr ?_
        filter_upwards [ae_iff.mpr (show volume {t : ℝ | ¬ t ≠ 0} = 0 by simp)] with t ht
        rcases lt_or_gt_of_ne ht with h | h
        · have hm1 : t ∈ Iio (0 : ℝ) := h
          have hm2 : t ∉ Ioi (0 : ℝ) := fun hm => by linarith [Set.mem_Ioi.mp hm]
          simp only [Pi.add_apply, Set.indicator_of_mem hm1, Set.indicator_of_notMem hm2,
            zero_add, abs_of_neg h, sub_eq_add_neg]
        · have hm1 : t ∈ Ioi (0 : ℝ) := h
          have hm2 : t ∉ Iio (0 : ℝ) := fun hm => by linarith [Set.mem_Iio.mp hm]
          simp only [Pi.add_apply, Set.indicator_of_mem hm1, Set.indicator_of_notMem hm2,
            add_zero, abs_of_pos h]
      refine (hdecay.const_mul (K * max CW' 0)).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
      rw [norm_mul]
      have h1 := hK ς t hς_pos.le hς_half
      have h2 := hCW' ((ς : ℂ) + (t : ℂ) * Complex.I) (by simp [hς_pos.le]) (by simp [hς_lt1.le])
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, mul_zero,
        Complex.ofReal_re, Complex.I_im, mul_one, zero_add, add_zero] at h2
      have h2' : ‖W ((ς : ℂ) + (t : ℂ) * Complex.I)‖ ≤ max CW' 0 * (1 + |t|) ^ (-(1 / 2 + η_W)) :=
        h2.trans (mul_le_mul_of_nonneg_right (le_max_left CW' (0 : ℝ)) (by positivity))
      calc ‖mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ‖ * ‖W ((ς : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (K * (1 + |t|) ^ (-(1 / 2 : ℝ))) * (max CW' 0 * (1 + |t|) ^ (-(1 / 2 + η_W))) :=
            mul_le_mul h1 h2' (norm_nonneg _) (by positivity)
        _ = K * max CW' 0 * ((1 + |t|) ^ (-(1 / 2 : ℝ)) * (1 + |t|) ^ (-(1 / 2 + η_W))) := by ring
        _ = K * max CW' 0 * (1 + |t|) ^ (-(1 + η_W)) := by
            rw [← Real.rpow_add (by linarith [abs_nonneg t])]; congr 2; ring
    have href_int : Integrable (fun v : ℝ =>
        (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
            Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))) := by
      have hcont : Continuous (fun v : ℝ =>
          (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
            Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
              Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))) :=
        (Continuous.cpow (by fun_prop) continuous_const fun v => Or.inl (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
          linarith [sq_nonneg ς])).mul (by fun_prop)
      refine ((integrable_exp_neg_mul_sq (by positivity : 0 < π ^ 2 / 12)).const_mul
        (Real.exp (π ^ 2 / 36 * (1 + ς ^ 2) ^ 3 + |ceCs * x|))).mono' hcont.aestronglyMeasurable
        (Eventually.of_forall fun v => ?_)
      rw [norm_mul, Complex.norm_exp, ← Real.exp_add]
      have hR1 : ‖(((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ))‖ ≤ 1 := by
        have hne : ((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I ≠ 0 := fun h0 => by
          have := congrArg Complex.re h0
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.zero_re] at this
          nlinarith [sq_nonneg ς]
        have hge1 : 1 ≤ ‖((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I‖ := by
          have := Complex.re_le_norm (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero] at this
          linarith [sq_nonneg ς]
        rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp,
          show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; ring,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.log_re,
          ← Real.rpow_def_of_pos (lt_of_lt_of_le one_pos hge1)]
        exact Real.rpow_le_one_of_one_le_of_nonpos hge1 (by norm_num)
      refine (mul_le_of_le_one_left (Real.exp_pos _).le hR1).trans (Real.exp_le_exp.mpr ?_)
      set a : ℝ := 1 + ς ^ 2
      have ha1 : 1 ≤ a := by dsimp [a]; linarith [sq_nonneg ς]
      have hre_cube : ((π ^ 2 / 36 : ℂ) * ((a : ℂ) + (v : ℂ) * Complex.I) ^ 3).re =
          π ^ 2 / 36 * (a ^ 3 - 3 * a * v ^ 2) := by
        have h : ((a : ℂ) + (v : ℂ) * Complex.I) ^ 3 =
            ((a ^ 3 - 3 * a * v ^ 2 : ℝ) : ℂ) + ((3 * a ^ 2 * v - v ^ 3 : ℝ) : ℂ) * Complex.I := by
          push_cast; ring_nf; simp [Complex.I_sq, Complex.I_pow_three]; ring
        rw [h, show (π ^ 2 / 36 : ℂ) = ((π ^ 2 / 36 : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
      have hre_lin : (Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)).re = ceCs * x := by
        simp [Complex.mul_re]
      rw [Complex.sub_re, hre_cube, hre_lin]
      have hlin : -(ceCs * x) ≤ |ceCs * x| := neg_le_abs _
      have hav : v ^ 2 ≤ a * v ^ 2 := by nlinarith [sq_nonneg v]
      have hpi2 : 0 ≤ π ^ 2 := sq_nonneg π
      nlinarith
    have hsplit_act : ∫ t : ℝ, mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I) =
        (∫ t in Icc (-(ς * V)) (ς * V), mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) +
        (∫ t in (Icc (-(ς * V)) (ς * V))ᶜ, mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) :=
      (integral_add_compl measurableSet_Icc hact_int).symm
    have hsplit_ref : ∫ v : ℝ, (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
            Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)) =
        (∫ v in Icc (-V) V, (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
            Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))) +
        (∫ v in (Icc (-V) V)ᶜ, (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
            Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I))) :=
      (integral_add_compl measurableSet_Icc href_int).symm
    have hdiff_bd : ‖uctHnormCE c L A - (RefVal : ℂ)‖ ≤ C_large * c ^ (-(4 / 3 : ℝ)) := by
      have hdecomp : uctHnormCE c L A - (RefVal : ℂ) =
          (((c ^ (1 / 3 : ℝ) / (2 * π) : ℝ) : ℂ) *
              (∫ t in Icc (-(ς * V)) (ς * V),
                mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) -
            ((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
              (((1 / (2 * π) : ℝ) : ℂ) *
                ∫ v in Icc (-V) V,
                  (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
                    Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
                      Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)))) +
          (((c ^ (1 / 3 : ℝ) / (2 * π) : ℝ) : ℂ) *
            ∫ t in (Icc (-(ς * V)) (ς * V))ᶜ,
              mellinK0 c ((ς : ℂ) + (t : ℂ) * Complex.I) ξ * W ((ς : ℂ) + (t : ℂ) * Complex.I)) -
          (((π ^ 2 / 4 * |uctCAi| * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) *
            (((1 / (2 * π) : ℝ) : ℂ) *
              ∫ v in (Icc (-V) V)ᶜ,
                (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ (-(1 / 2 : ℂ)) *
                  Complex.exp ((π ^ 2 / 36 : ℂ) * (((1 + ς ^ 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) ^ 3 -
                    Complex.I * ((ceCs * x : ℝ) : ℂ) * ((v : ℂ) - Complex.I)))) := by
        rw [hH_eq0, hint_eq, hsplit_act, hRef_eq, hsplit_ref]; ring
      rw [hdecomp]
      have h1 := hcore ((le_max_left _ _).trans hc_big) hηW hW hL_lo hL_hi hfac hAext_cont hAext_hol hAext_real hAext_bd
      have h2 := hat ((le_max_right _ _).trans hc_big) hηW hW hL_lo hL_hi hW_poly
      have h3 := hrt hc hL_lo hL_hi
      calc ‖_‖ ≤ ‖_ + _‖ + ‖_‖ := norm_sub_le _ _
        _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ (C_core * c ^ (-(4 / 3 : ℝ)) + C_at * c ^ (-(4 / 3 : ℝ))) + C_rt * c ^ (-(4 / 3 : ℝ)) :=
            add_le_add (add_le_add h1 h2) h3
        _ = C_large * c ^ (-(4 / 3 : ℝ)) := by dsimp [C_large]; ring
    have hre_sub : |(uctHnormCE c L A).re - RefVal| ≤ C_large * c ^ (-(4 / 3 : ℝ)) := by
      have : (uctHnormCE c L A - (RefVal : ℂ)).re = (uctHnormCE c L A).re - RefVal := by simp
      rw [← this]
      exact (Complex.abs_re_le_norm _).trans hdiff_bd
    have hle_max : C_large ≤ max C_large (max 1 C_fin) := le_max_left _ _
    have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := by positivity
    have h1 := (abs_le.mp hre_sub).1
    nlinarith
  · -- Finite range `60 ≤ c < c₀`: trivial from `uct_ce_band_global_bound`!
    have hc_lt : c < c₀ := not_le.mp hc_big
    have hglob := (uct_ce_band_global_bound hC₀ hη hA_cont hA0 hc0 L).2
    have hpow_le : c ^ (-(1 / 2 : ℝ)) ≤ c₀ ^ (5 / 6 : ℝ) * c ^ (-(4 / 3 : ℝ)) := by
      have hc56 : c ^ (5 / 6 : ℝ) ≤ c₀ ^ (5 / 6 : ℝ) := Real.rpow_le_rpow hc0.le hc_lt.le (by norm_num)
      calc c ^ (-(1 / 2 : ℝ)) = c ^ (5 / 6 : ℝ) * c ^ (-(4 / 3 : ℝ)) := by
            rw [← Real.rpow_add hc0]; norm_num
        _ ≤ c₀ ^ (5 / 6 : ℝ) * c ^ (-(4 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hc56 (by positivity)
    have hbd : ‖uctHnormCE c L A‖ ≤ C_fin * c ^ (-(4 / 3 : ℝ)) := by
      calc ‖uctHnormCE c L A‖ ≤ (π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) * c ^ (-(1 / 2 : ℝ)) := hglob
        _ ≤ (π ^ (3 / 2 : ℝ) * |uctCAi| * C₀ / (4 * √η)) * (c₀ ^ (5 / 6 : ℝ) * c ^ (-(4 / 3 : ℝ))) :=
            mul_le_mul_of_nonneg_left hpow_le (by positivity)
        _ = C_fin * c ^ (-(4 / 3 : ℝ)) := by dsimp [C_fin]; ring
    have hre_ge : -(C_fin * c ^ (-(4 / 3 : ℝ))) ≤ (uctHnormCE c L A).re := by
      have := (Complex.abs_re_le_norm (uctHnormCE c L A)).trans hbd
      exact (abs_le.mp this).1
    have hle_max : C_fin ≤ max C_large (max 1 C_fin) := (le_max_right _ _).trans (le_max_right _ _)
    have hc43_nn : 0 ≤ c ^ (-(4 / 3 : ℝ)) := by positivity
    nlinarith

/-- info: 'FormalResearch.SignUncertainty.half_disc_zero_of_real_segment_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms half_disc_zero_of_real_segment_zero

/-- info: 'FormalResearch.SignUncertainty.uct_hhat_ref_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_hhat_ref_shifted

/-- info: 'FormalResearch.SignUncertainty.uct_ce_band_airy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_ce_band_airy

end FormalResearch.SignUncertainty
