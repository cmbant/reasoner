module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3Strip
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3Bdry
public import FormalResearch.Complex.SchwarzReflection

/-!
# FIVE-S, S3 (step 2): construction of `Ee` on `{|Im b| < 1/2}` (`cts:smooth-env` (2))

Constructs the stripped envelope `Ee δ : ℂ → ℂ` for `δ ∈ (0, 1/4)` on the symmetric strip
`{|Im b| < 1/2}` by extending `Estripped δ` continuously to `Im b = 0` via `EeBdry δ` and
applying Schwarz reflection (`FormalResearch.Complex.schwarzReflection`) across `Im b = 0`.

Main results:
* `differentiableOn_Ee_symmStrip`: `DifferentiableOn ℂ (Ee δ) {b : ℂ | |b.im| < 1 / 2}`.
* `Ee_ne_zero_symmStrip`: `Ee δ b ≠ 0` for `|b.im| < 1 / 2`.
* `Ee_neg`: `Ee δ (-b) = Ee δ b` for all `b : ℂ`.
* `Ee_real_pos`: `0 < (Ee δ (x : ℂ)).re ∧ (Ee δ (x : ℂ)).im = 0` for all `x : ℝ`.
* `Ee_eq_Estripped`: `Ee δ b = Estripped δ b` for `0 < b.im < 1 / 2`.
* `Ee_modulus_identity`: `‖Ee δ (x : ℂ)‖ * Real.exp (DeltaPhi δ (x : ℂ)).re = ‖fDelta Gout δ (I * yOfX x)‖`
  for `xiStar ≤ x`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.Complex
open FormalResearch.ModularBootstrap.FiveTerm

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- The open half-strip `{0 < Im b < 1/2}`. -/
def outerS3HalfStrip : Set ℂ := {b : ℂ | 0 < b.im ∧ b.im < 1 / 2}

/-- The open symmetric strip `{|Im b| < 1/2}`. -/
def symmStrip : Set ℂ := {b : ℂ | |b.im| < 1 / 2}

lemma isOpen_outerS3HalfStrip : IsOpen outerS3HalfStrip :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

lemma isOpen_symmStrip : IsOpen symmStrip :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-! ### 1. Holomorphicity and non-vanishing of `Estripped δ` on `outerS3HalfStrip` -/

private lemma zetaD_w_mem_slitPlane {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2) :
    (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) ≠ 0 ∧
      ((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) ∈
        Complex.slitPlane := by
  have hpi := Real.pi_pos
  set c := Complex.cosh ((π : ℂ) * b) with hcdef
  have hcre : 0 < c.re := by
    rw [hcdef, re_cosh']
    have hch : 0 < Real.cosh ((π : ℂ) * b).re := Real.cosh_pos _
    have hcos : 0 < Real.cos ((π : ℂ) * b).im := by
      apply Real.cos_pos_of_mem_Ioo
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact ⟨by nlinarith, by nlinarith⟩
    exact mul_pos hch hcos
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (√2 : ℂ) + c ≠ 0 := by
    intro h
    have : ((√2 : ℂ) + c).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.ofReal_re] at this
    linarith
  refine ⟨hden, ?_⟩
  rw [Complex.mem_slitPlane_iff]
  by_cases hre0 : b.re = 0
  · left
    have hcos : Real.cos (π * b.im) < 1 := by
      rw [← Real.cos_zero]
      exact Real.strictAntiOn_cos ⟨le_refl 0, Real.pi_pos.le⟩ ⟨by positivity, by nlinarith⟩ (by positivity)
    have hc_eq : c = ((Real.cos (π * b.im) : ℝ) : ℂ) := by
      have hb_eq : ((b.im : ℂ) * Complex.I) = b := by apply Complex.ext <;> simp [hre0]
      rw [hcdef, ← hb_eq, show (π : ℂ) * ((b.im : ℂ) * Complex.I) = ((π * b.im : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.cosh_mul_I, ← Complex.ofReal_cos]
      simp
    rw [hc_eq, ← Complex.ofReal_sub, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
    have h1 : 1 < √2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    exact div_pos (by linarith) (by linarith [Real.cos_pos_of_mem_Ioo (⟨by nlinarith, by nlinarith⟩ : π * b.im ∈ Ioo (-(π / 2)) (π / 2))])
  · right
    have him_c : c.im ≠ 0 := by
      rw [hcdef, im_cosh']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      exact mul_ne_zero (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hre0))
        (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)).ne'
    have him_w : (((√2 : ℂ) - c) / ((√2 : ℂ) + c)).im ≠ 0 := by
      rw [Complex.div_im]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_sub, zero_add]
      have hn : 0 < Complex.normSq ((√2 : ℂ) + c) := Complex.normSq_pos.mpr hden
      have hnum : (-c.im) * (√2 + c.re) - (√2 - c.re) * c.im = -(2 * √2 * c.im) := by ring
      rw [← sub_div, hnum]
      exact div_ne_zero (by intro h; apply him_c; nlinarith) hn.ne'
    exact him_w

lemma differentiableOn_zetaD_outerS3HalfStrip : DifferentiableOn ℂ zetaD outerS3HalfStrip := by
  intro b hb
  obtain ⟨hden, hw_slit⟩ := zetaD_w_mem_slitPlane hb.1 hb.2
  have hc : DifferentiableAt ℂ (fun z : ℂ => Complex.cosh ((π : ℂ) * z)) b :=
    Complex.differentiableAt_cosh.comp b ((differentiableAt_const _).mul differentiableAt_id)
  have hw : DifferentiableAt ℂ (fun z : ℂ =>
      ((√2 : ℂ) - Complex.cosh ((π : ℂ) * z)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * z))) b :=
    ((differentiableAt_const _).sub hc).div ((differentiableAt_const _).add hc) hden
  exact (hw.cpow (differentiableAt_const _) hw_slit).differentiableWithinAt

lemma differentiableOn_Estripped_outerS3HalfStrip {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    DifferentiableOn ℂ (Estripped δ) outerS3HalfStrip := by
  intro b hb
  have hzeta_mem : zetaD b ∈ halfDisc := zetaD_mem_halfDisc hb.1 hb.2
  have hf_diff : DifferentiableAt ℂ (fDelta Gout δ) (zetaD b) :=
    (fDelta_hAdm gout_outerDatum_g1Out hδ0 (by linarith)).diff.differentiableAt
      (isOpen_halfDisc.mem_nhds hzeta_mem)
  have hzeta_diff : DifferentiableAt ℂ zetaD b :=
    differentiableOn_zetaD_outerS3HalfStrip.differentiableAt (isOpen_outerS3HalfStrip.mem_nhds hb)
  have hdp_diff : DifferentiableAt ℂ (DeltaPhi δ) b :=
    (differentiableOn_DeltaPhi_imStrip hδ0 hδ1).differentiableAt
      (isOpen_imStrip.mem_nhds ⟨hb.1, by linarith [hb.2]⟩)
  exact ((hf_diff.comp b hzeta_diff).mul hdp_diff.neg.cexp).differentiableWithinAt

lemma Estripped_ne_zero_outerS3HalfStrip {δ : ℝ} (_hδ0 : 0 < δ) (_hδ1 : δ < 1 / 4)
    {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2) : Estripped δ b ≠ 0 := by
  unfold Estripped
  have hzeta_mem : zetaD b ∈ halfDisc := zetaD_mem_halfDisc hb0 hb1
  have hf_ne : fDelta Gout δ (zetaD b) ≠ 0 :=
    fDelta_ne_zero gout_outerDatum_g1Out ⟨subset_closure hzeta_mem, not_mem_singPts_of_halfDisc hzeta_mem⟩
  exact mul_ne_zero hf_ne (Complex.exp_ne_zero _)

/-! ### 2. Conjugation-negation symmetry `b ↦ -conj b` -/

private lemma neBot_nhdsWithin_upperHalf (x : ℝ) : NeBot (𝓝[upperHalf] (x : ℂ)) := by
  refine mem_closure_iff_nhdsWithin_neBot.mp ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  exact ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, by simp [upperHalf]; positivity,
    by rw [dist_eq_norm]; simp; rw [abs_of_pos hε]; exact half_lt_self hε⟩

private lemma cosh_conj (z : ℂ) : Complex.cosh (starRingEnd ℂ z) = starRingEnd ℂ (Complex.cosh z) := by
  apply Complex.ext
  · simp [re_cosh']
  · simp [im_cosh']

private lemma sinh_conj (z : ℂ) : Complex.sinh (starRingEnd ℂ z) = starRingEnd ℂ (Complex.sinh z) := by
  apply Complex.ext
  · simp [re_sinh']
  · simp [im_sinh']

private lemma zetaD_neg_conj {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2) :
    zetaD (-starRingEnd ℂ b) = starRingEnd ℂ (zetaD b) := by
  obtain ⟨hden, hw_slit⟩ := zetaD_w_mem_slitPlane hb0 hb1
  have hcosh : Complex.cosh ((π : ℂ) * (-starRingEnd ℂ b)) =
      starRingEnd ℂ (Complex.cosh ((π : ℂ) * b)) := by
    rw [show (π : ℂ) * (-starRingEnd ℂ b) = -(starRingEnd ℂ ((π : ℂ) * b)) by
        rw [map_mul, Complex.conj_ofReal]; ring,
      Complex.cosh_neg, cosh_conj]
  have hw : ((√2 : ℂ) - Complex.cosh ((π : ℂ) * (-starRingEnd ℂ b))) /
      ((√2 : ℂ) + Complex.cosh ((π : ℂ) * (-starRingEnd ℂ b))) =
      starRingEnd ℂ (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) /
        ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))) := by
    rw [hcosh, map_div₀, map_sub, map_add, Complex.conj_ofReal]
  have harg : (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) /
      ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))).arg ≠ π := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    rw [Complex.mem_slitPlane_iff] at hw_slit
    rcases hw_slit with hpos | him
    · linarith [h.1]
    · exact him h.2
  unfold zetaD
  rw [hw]
  have hc := Complex.cpow_conj (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) /
    ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))) (1 / 2 : ℂ) harg
  have hhalf : starRingEnd ℂ (1 / 2 : ℂ) = (1 / 2 : ℂ) := by rw [one_div, map_inv₀, map_ofNat]
  rw [hhalf] at hc
  have h := congrArg (starRingEnd ℂ) hc
  simpa using h.symm

private lemma phiYDeriv_neg_conj (y : ℝ) (b : ℂ) :
    phiYDeriv y (-starRingEnd ℂ b) = -starRingEnd ℂ (phiYDeriv y b) := by
  unfold phiYDeriv
  have h1 : Complex.sinh ((π : ℂ) * (-starRingEnd ℂ b - (y : ℂ))) =
      -starRingEnd ℂ (Complex.sinh ((π : ℂ) * (b + (y : ℂ)))) := by
    have he : (π : ℂ) * (-starRingEnd ℂ b - (y : ℂ)) = -(starRingEnd ℂ ((π : ℂ) * (b + (y : ℂ)))) := by
      rw [map_mul, Complex.conj_ofReal, map_add, Complex.conj_ofReal]; ring
    rw [he, Complex.sinh_neg, sinh_conj]
  have h2 : Complex.sinh ((π : ℂ) * (-starRingEnd ℂ b + (y : ℂ))) =
      -starRingEnd ℂ (Complex.sinh ((π : ℂ) * (b - (y : ℂ)))) := by
    have he : (π : ℂ) * (-starRingEnd ℂ b + (y : ℂ)) = -(starRingEnd ℂ ((π : ℂ) * (b - (y : ℂ)))) := by
      rw [map_mul, Complex.conj_ofReal, map_sub, Complex.conj_ofReal]; ring
    rw [he, Complex.sinh_neg, sinh_conj]
  rw [h1, h2, map_mul, Complex.conj_ofReal, map_add, map_div₀, map_div₀, map_one, one_div, one_div]
  ring

private lemma phiY_neg_conj (y : ℝ) {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1) :
    phiY y (-starRingEnd ℂ b) = starRingEnd ℂ (phiY y b) := by
  unfold phiY
  have heq : ∀ t : ℝ, phiYDeriv y (Complex.I / 2 + (t : ℂ) * (-starRingEnd ℂ b - Complex.I / 2)) *
      (-starRingEnd ℂ b - Complex.I / 2) =
      starRingEnd ℂ (phiYDeriv y (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)) * (b - Complex.I / 2)) := by
    intro t
    have hz1 : Complex.I / 2 + (t : ℂ) * (-starRingEnd ℂ b - Complex.I / 2) =
        -starRingEnd ℂ (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)) := by
      rw [map_add, map_mul, Complex.conj_ofReal, map_sub, map_div₀, Complex.conj_I, map_ofNat]
      ring
    have hz2 : -starRingEnd ℂ b - Complex.I / 2 = -starRingEnd ℂ (b - Complex.I / 2) := by
      rw [map_sub, map_div₀, Complex.conj_I, map_ofNat]; ring
    rw [hz1, hz2, phiYDeriv_neg_conj, map_mul, neg_mul_neg]
  simp_rw [heq]
  have hcont : ContinuousOn (fun t : ℝ => phiYDeriv y (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)) * (b - Complex.I / 2))
      (Icc 0 1) := by
    have hline : Continuous (fun t : ℝ => Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hphi_cont : ContinuousOn (phiYDeriv y) {z : ℂ | 0 < z.im ∧ z.im < 1} := by
      intro z hz
      have hpi := Real.pi_pos
      have hzm1 : ((π : ℂ) * (z - (y : ℂ))).im = π * z.im := by simp
      have hzm2 : ((π : ℂ) * (z + (y : ℂ))).im = π * z.im := by simp
      have hsn1 : Complex.sinh ((π : ℂ) * (z - (y : ℂ))) ≠ 0 :=
        sinh_ne_zero_of (by rw [hzm1]; exact mul_pos hpi hz.1) (by rw [hzm1]; nlinarith [hz.2])
      have hsn2 : Complex.sinh ((π : ℂ) * (z + (y : ℂ))) ≠ 0 :=
        sinh_ne_zero_of (by rw [hzm2]; exact mul_pos hpi hz.1) (by rw [hzm2]; nlinarith [hz.2])
      have hc : ContinuousAt (phiYDeriv y) z := by
        unfold phiYDeriv
        exact ContinuousAt.mul continuousAt_const ((continuousAt_const.div (Complex.continuous_sinh.continuousAt.comp
          (ContinuousAt.mul continuousAt_const (continuousAt_id.sub continuousAt_const))) hsn1).add
          (continuousAt_const.div (Complex.continuous_sinh.continuousAt.comp
            (ContinuousAt.mul continuousAt_const (continuousAt_id.add continuousAt_const))) hsn2))
      exact hc.continuousWithinAt
    refine (hphi_cont.comp hline.continuousOn fun t ht => ?_).mul continuousOn_const
    simp only [mem_ofPred_eq, Complex.add_im, Complex.div_ofNat_im, Complex.I_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.sub_re, zero_mul, add_zero]
    exact ⟨by nlinarith [ht.1, ht.2], by nlinarith [ht.1, ht.2]⟩
  have hint_t : IntervalIntegrable
      (fun t : ℝ => phiYDeriv y (Complex.I / 2 + (t : ℂ) * (b - Complex.I / 2)) * (b - Complex.I / 2))
      volume 0 1 :=
    (hcont.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using
    (Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint_t)

private lemma DeltaPhi_neg_conj {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1) :
    DeltaPhi δ (-starRingEnd ℂ b) = starRingEnd ℂ (DeltaPhi δ b) := by
  unfold DeltaPhi
  rw [map_mul, show starRingEnd ℂ (1 / (π : ℂ)) = (1 / (π : ℂ)) by simp]
  congr 1
  set ε := min (b.im / 2) ((1 - b.im) / 2)
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε < 1 / 2 := by
    have : ε ≤ (b.im / 2 + (1 - b.im) / 2) / 2 := by
      have h1 : ε ≤ b.im / 2 := min_le_left _ _
      have h2 : ε ≤ (1 - b.im) / 2 := min_le_right _ _
      linarith
    linarith
  have hbε : b ∈ stripEps ε := ⟨by linarith [min_le_left (b.im / 2) ((1 - b.im) / 2)],
    by linarith [min_le_right (b.im / 2) ((1 - b.im) / 2)]⟩
  have hint : IntegrableOn (fun y : ℝ => ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) (Ioi xiStar) :=
    integrable_param (integrableOn_dphi_deriv hδ0 hδ1) (continuous_phiY_y ⟨hb0, hb1⟩)
      (fun y => norm_phiY_le_of_stripEps hε0 hε1 hbε)
  have heq : (fun y : ℝ => ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y (-starRingEnd ℂ b)) =
      fun y : ℝ => starRingEnd ℂ (((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b) := by
    funext y
    rw [phiY_neg_conj y hb0 hb1, map_mul, Complex.conj_ofReal]
  rw [heq]
  simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using
    (Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hint)

lemma Estripped_neg_conj {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2) :
    Estripped δ (-starRingEnd ℂ b) = starRingEnd ℂ (Estripped δ b) := by
  unfold Estripped
  rw [zetaD_neg_conj hb0 hb1, DeltaPhi_neg_conj hδ0 hδ1 hb0 (by linarith)]
  rw [fDelta_conj gout_outerDatum_g1Out hδ0 (by linarith) (zetaD_mem_halfDisc hb0 hb1)]
  rw [← map_neg, Complex.exp_conj, map_mul]

/-! ### 3. Real-axis boundary values and positivity for all `x : ℝ` -/

private lemma fDelta_real_pos {δ r : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (hr0 : 0 < r) (hr1 : r < 1) :
    0 < (fDelta Gout δ (r : ℂ)).re ∧ (fDelta Gout δ (r : ℂ)).im = 0 := by
  have hr_hd : (r : ℂ) ∈ halfDisc := ⟨by simpa [abs_of_pos hr0] using hr1, by simpa using hr0⟩
  have hconj := fDelta_conj gout_outerDatum_g1Out hδ0 (by linarith) hr_hd
  rw [Complex.conj_ofReal] at hconj
  have him : (fDelta Gout δ (r : ℂ)).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  refine ⟨?_, him⟩
  by_contra hle
  push Not at hle
  have hsub : ∀ s ∈ Icc (0 : ℝ) r, (s : ℂ) ∈ closure halfDisc \ singPts := by
    intro s hs
    refine ⟨mem_closure_halfDisc (by simpa [abs_of_nonneg hs.1] using hs.2.trans hr1.le)
      (by simpa using hs.1), ?_⟩
    rw [mem_singPts_iff]
    rintro (h | h | h)
    · have := congrArg Complex.im h; simp at this
    · have := congrArg Complex.im h; simp at this
    · have := congrArg Complex.re h; simp at this; linarith [hs.2, hr1]
  have hcont : ContinuousOn (fun s : ℝ => (fDelta Gout δ (s : ℂ)).re) (Icc 0 r) :=
    (Complex.continuous_re.comp_continuousOn
      ((fDelta_hAdm gout_outerDatum_g1Out hδ0 (by linarith)).cont.comp
        Complex.continuous_ofReal.continuousOn hsub))
  have h0 : (fDelta Gout δ ((0 : ℝ) : ℂ)).re = 1 := by
    rw [Complex.ofReal_zero, fDelta_zero gout_outerDatum_g1Out hδ0 (by linarith), Complex.one_re]
  obtain ⟨s, hs, hs_eq⟩ := intermediate_value_Icc' hr0.le hcont ⟨hle, by linarith⟩
  have hs_im : (fDelta Gout δ (s : ℂ)).im = 0 := by
    rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
    · rw [Complex.ofReal_zero, fDelta_zero gout_outerDatum_g1Out hδ0 (by linarith), Complex.one_im]
    · have hs_hd : (s : ℂ) ∈ halfDisc :=
        ⟨by simpa [abs_of_pos hs_pos] using hs.2.trans_lt hr1, by simpa using hs_pos⟩
      have hc := fDelta_conj gout_outerDatum_g1Out hδ0 (by linarith) hs_hd
      rw [Complex.conj_ofReal] at hc
      have := congrArg Complex.im hc
      simp only [Complex.conj_im] at this
      linarith
  have hzero : fDelta Gout δ (s : ℂ) = 0 := Complex.ext hs_eq hs_im
  exact fDelta_ne_zero gout_outerDatum_g1Out (hsub s hs) hzero

theorem tendsto_Estripped_real_abs_lt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : |x| < xiStar) :
    Tendsto (Estripped δ) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (fDelta Gout δ (zetaDReal x : ℂ) * ((Real.exp (-(DeltaPhi δ (x : ℂ)).re) : ℝ) : ℂ))) := by
  have hmem := zetaDReal_mem hx
  have hz_hd : (zetaDReal x : ℂ) ∈ closure halfDisc \ singPts :=
    ⟨subset_closure ⟨by simpa [abs_of_pos hmem.1] using hmem.2, by simpa using hmem.1⟩,
      not_mem_singPts_of_halfDisc ⟨by simpa [abs_of_pos hmem.1] using hmem.2, by simpa using hmem.1⟩⟩
  have hcont := (fDelta_hAdm gout_outerDatum_g1Out hδ0 (by linarith)).cont
  have hev_mem : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), zetaD b ∈ closure halfDisc \ singPts := by
    have h1 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), 0 < b.im := self_mem_nhdsWithin
    have h2 : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b.im < 1 / 2 :=
      nhdsWithin_le_nhds ((Complex.continuous_im.tendsto (x : ℂ)).eventually (gt_mem_nhds (by simp : (x : ℂ).im < 1 / 2)))
    filter_upwards [h1, h2] with b hb0 hb1
    have hm := zetaD_mem_halfDisc hb0 hb1
    exact ⟨subset_closure hm, not_mem_singPts_of_halfDisc hm⟩
  have hf_lim : Tendsto (fun b => fDelta Gout δ (zetaD b)) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (fDelta Gout δ (zetaDReal x : ℂ))) :=
    (hcont _ hz_hd).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨tendsto_zetaD_real hx, hev_mem⟩)
  have hexp_lim : Tendsto (fun b => Complex.exp (-DeltaPhi δ b)) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (Complex.exp (-DeltaPhi δ (x : ℂ)))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_DeltaPhi_real hδ0 hδ1 x).neg
  have hmul := hf_lim.mul hexp_lim
  have him0 : (DeltaPhi δ (x : ℂ)).im = 0 := im_DeltaPhi_real_abs_lt hδ0 hδ1 hx
  have h_delta : -DeltaPhi δ (x : ℂ) = ((-(DeltaPhi δ (x : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him0]
  rwa [h_delta, ← Complex.ofReal_exp] at hmul

theorem tendsto_Estripped_real_le_neg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : x ≤ -xiStar) :
    Tendsto (Estripped δ) (𝓝[upperHalf] (x : ℂ)) (𝓝 (EeBdry δ (-x))) := by
  have hx_ge : xiStar ≤ -x := by linarith
  have h_pos_lim : Tendsto (Estripped δ) (𝓝[upperHalf] ((-x : ℝ) : ℂ)) (𝓝 (EeBdry δ (-x))) := by
    have hne := neBot_nhdsWithin_upperHalf (-x)
    rcases eq_or_lt_of_le hx_ge with h_eq | hx_gt
    · have h1 := tendsto_Estripped_real_xiStar hδ0 hδ1
      rw [h_eq] at h1
      rwa [← h1.limUnder_eq] at h1
    · have h1 := tendsto_Estripped_real_gt hδ0 hδ1 hx_gt
      rwa [← h1.limUnder_eq] at h1
  have hmap : Tendsto (fun b : ℂ => -starRingEnd ℂ b) (𝓝[upperHalf] (x : ℂ)) (𝓝[upperHalf] ((-x : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun b : ℂ => -starRingEnd ℂ b) := Complex.continuous_conj.neg
      have h0 : -starRingEnd ℂ (x : ℂ) = ((-x : ℝ) : ℂ) := by simp [Complex.conj_ofReal]
      rw [← h0]
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with b hb
      simpa [upperHalf] using hb
  have h_conj_lim : Tendsto (fun b : ℂ => starRingEnd ℂ (Estripped δ (-starRingEnd ℂ b)))
      (𝓝[upperHalf] (x : ℂ)) (𝓝 (starRingEnd ℂ (EeBdry δ (-x)))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp (h_pos_lim.comp hmap)
  have h_real : starRingEnd ℂ (EeBdry δ (-x)) = EeBdry δ (-x) :=
    Complex.conj_eq_iff_im.mpr (EeBdry_modulus_identity hδ0 hδ1 hx_ge).2.1
  rw [h_real] at h_conj_lim
  refine h_conj_lim.congr' ?_
  have hb_small : ∀ᶠ b in 𝓝[upperHalf] (x : ℂ), b.im < 1 / 2 :=
    nhdsWithin_le_nhds ((Complex.continuous_im.tendsto (x : ℂ)).eventually (gt_mem_nhds (by simp : (x : ℂ).im < 1 / 2)))
  filter_upwards [self_mem_nhdsWithin, hb_small] with b hb0 hb1
  have hsym := Estripped_neg_conj hδ0 hδ1 (by simpa [upperHalf] using hb0 : 0 < (-starRingEnd ℂ b).im)
    (by simpa using hb1 : (-starRingEnd ℂ b).im < 1 / 2)
  have hinv : -starRingEnd ℂ (-starRingEnd ℂ b) = b := by simp
  rw [hinv] at hsym
  exact hsym.symm

lemma tendsto_Estripped_real_all {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (x : ℝ) :
    Tendsto (Estripped δ) (𝓝[upperHalf] (x : ℂ)) (𝓝 (EeBdry δ x)) := by
  have hne : NeBot (𝓝[upperHalf] (x : ℂ)) := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, by simp [upperHalf]; positivity,
      by rw [dist_eq_norm]; simp; rw [abs_of_pos hε]; exact half_lt_self hε⟩
  rcases le_or_gt xiStar x with hx_ge | hx_lt
  · rcases eq_or_lt_of_le hx_ge with rfl | hx_gt
    · have h := tendsto_Estripped_real_xiStar hδ0 hδ1
      rwa [← h.limUnder_eq] at h
    · have h := tendsto_Estripped_real_gt hδ0 hδ1 hx_gt
      rwa [← h.limUnder_eq] at h
  · rcases lt_or_ge (-xiStar) x with hx_gt_neg | hx_le_neg
    · have h := tendsto_Estripped_real_abs_lt hδ0 hδ1 (abs_lt.mpr ⟨hx_gt_neg, hx_lt⟩)
      rwa [← h.limUnder_eq] at h
    · have h := tendsto_Estripped_real_le_neg hδ0 hδ1 hx_le_neg
      rwa [← h.limUnder_eq] at h

lemma EeBdry_pos_real {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (x : ℝ) :
    0 < (EeBdry δ x).re ∧ (EeBdry δ x).im = 0 := by
  have hne : NeBot (𝓝[upperHalf] (x : ℂ)) := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    exact ⟨(x : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, by simp [upperHalf]; positivity,
      by rw [dist_eq_norm]; simp; rw [abs_of_pos hε]; exact half_lt_self hε⟩
  rcases le_or_gt xiStar x with hx_ge | hx_lt
  · exact ⟨(EeBdry_modulus_identity hδ0 hδ1 hx_ge).1, (EeBdry_modulus_identity hδ0 hδ1 hx_ge).2.1⟩
  · rcases lt_or_ge (-xiStar) x with hx_gt_neg | hx_le_neg
    · have hx_abs : |x| < xiStar := abs_lt.mpr ⟨hx_gt_neg, hx_lt⟩
      have h := tendsto_Estripped_real_abs_lt hδ0 hδ1 hx_abs
      have hEe : EeBdry δ x = fDelta Gout δ (zetaDReal x : ℂ) * ((Real.exp (-(DeltaPhi δ (x : ℂ)).re) : ℝ) : ℂ) :=
        h.limUnder_eq
      rw [hEe]
      have hmem := zetaDReal_mem hx_abs
      obtain ⟨hf_pos, hf_im⟩ := fDelta_real_pos hδ0 hδ1 hmem.1 hmem.2
      have hf_eq : fDelta Gout δ (zetaDReal x : ℂ) = (((fDelta Gout δ (zetaDReal x : ℂ)).re : ℝ) : ℂ) :=
        Complex.ext rfl hf_im
      rw [hf_eq, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨mul_pos hf_pos (Real.exp_pos _), rfl⟩
    · have h := tendsto_Estripped_real_le_neg hδ0 hδ1 hx_le_neg
      have hEe : EeBdry δ x = EeBdry δ (-x) := h.limUnder_eq
      rw [hEe]
      have hmod := EeBdry_modulus_identity hδ0 hδ1 (by linarith : xiStar ≤ -x)
      exact ⟨hmod.1, hmod.2.1⟩

/-! ### 4. Continuous extension, Schwarz reflection, and the 5 properties of `Ee` -/

/-- Continuous extension of `Estripped δ` to the closed upper half-strip `{0 ≤ Im b < 1/2}`. -/
noncomputable def Eext (δ : ℝ) (b : ℂ) : ℂ :=
  if 0 < b.im then Estripped δ b else EeBdry δ b.re

/-- The even zero-free holomorphic extension `Ee δ` on `{|Im b| < 1/2}` (`cts:smooth-env` (2)),
defined by Schwarz reflection across `Im b = 0` inside `symmStrip` and `0` outside. -/
noncomputable def Ee (δ : ℝ) (b : ℂ) : ℂ :=
  if |b.im| < 1 / 2 then schwarzReflect 0 (Eext δ) b else 0

private lemma continuousOn_Eext {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    ContinuousOn (Eext δ) (symmStrip ∩ {b : ℂ | 0 ≤ b.im}) := by
  intro b₀ hb₀
  rcases lt_or_eq_of_le (show (0 : ℝ) ≤ b₀.im from hb₀.2) with hb_pos | hb_zero
  · have hopen : IsOpen outerS3HalfStrip := isOpen_outerS3HalfStrip
    have hmem : b₀ ∈ outerS3HalfStrip := ⟨hb_pos, (abs_lt.mp hb₀.1).2⟩
    have hcont : ContinuousAt (Estripped δ) b₀ :=
      ((differentiableOn_Estripped_outerS3HalfStrip hδ0 hδ1).continuousOn.continuousAt (hopen.mem_nhds hmem))
    have hev : Estripped δ =ᶠ[𝓝 b₀] Eext δ := by
      filter_upwards [hopen.mem_nhds hmem] with b hb
      simp [Eext, hb.1]
    exact (hcont.congr hev).continuousWithinAt
  · have hx_eq : b₀ = (b₀.re : ℂ) := Complex.ext rfl hb_zero.symm
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hlim := tendsto_Estripped_real_all hδ0 hδ1 b₀.re
    rw [Metric.tendsto_nhdsWithin_nhds] at hlim
    obtain ⟨r, hr0, hr⟩ := hlim (ε / 2) (half_pos hε)
    refine ⟨r / 2, half_pos hr0, fun b hb_mem hdist => ?_⟩
    rw [← hx_eq] at hr
    have hE0 : Eext δ b₀ = EeBdry δ b₀.re := by simp [Eext, ← hb_zero]
    rw [hE0]
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ b.im from hb_mem.2) with hb_pos | hb_zero'
    · have hE : Eext δ b = Estripped δ b := by simp [Eext, hb_pos]
      rw [hE]
      exact (hr hb_pos (lt_trans hdist (half_lt_self hr0))).trans (half_lt_self hε)
    · have hE : Eext δ b = EeBdry δ b.re := by simp [Eext, ← hb_zero']
      rw [hE]
      have hlim_y := tendsto_Estripped_real_all hδ0 hδ1 b.re
      rw [Metric.tendsto_nhdsWithin_nhds] at hlim_y
      obtain ⟨s, hs0, hs⟩ := hlim_y (ε / 2) (half_pos hε)
      set t : ℝ := min (s / 2) (r / 4)
      have ht0 : 0 < t := lt_min (half_pos hs0) (by positivity)
      set w : ℂ := (b.re : ℂ) + (t : ℂ) * Complex.I
      have hw_uh : w ∈ upperHalf := by simp [w, upperHalf, ht0]
      have hw_b : dist w (b.re : ℂ) < s := by
        rw [dist_eq_norm, show w - (b.re : ℂ) = (t : ℂ) * Complex.I by simp [w],
          norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
        exact (min_le_left (s / 2) (r / 4)).trans_lt (half_lt_self hs0)
      have hw_b0 : dist w b₀ < r := by
        have h1' : dist w b ≤ r / 4 := by
          have hb_eq : b = (b.re : ℂ) := Complex.ext rfl hb_zero'.symm
          rw [hb_eq, dist_eq_norm, show w - (b.re : ℂ) = (t : ℂ) * Complex.I by simp [w],
            norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
          exact min_le_right (s / 2) (r / 4)
        calc dist w b₀ ≤ dist w b + dist b b₀ := dist_triangle w b b₀
          _ < r / 4 + r / 2 := add_lt_add_of_le_of_lt h1' hdist
          _ < r := by linarith
      have hd1 : dist (Estripped δ w) (EeBdry δ b.re) < ε / 2 := hs hw_uh hw_b
      have hd2 : dist (Estripped δ w) (EeBdry δ b₀.re) < ε / 2 := hr hw_uh hw_b0
      calc dist (EeBdry δ b.re) (EeBdry δ b₀.re)
          ≤ dist (EeBdry δ b.re) (Estripped δ w) + dist (Estripped δ w) (EeBdry δ b₀.re) :=
            dist_triangle _ _ _
        _ = dist (Estripped δ w) (EeBdry δ b.re) + dist (Estripped δ w) (EeBdry δ b₀.re) := by
            rw [dist_comm (EeBdry δ b.re)]
        _ < ε / 2 + ε / 2 := add_lt_add hd1 hd2
        _ = ε := add_halves ε

/-- **`Ee δ` is holomorphic on `{|Im b| < 1/2}`** (`cts:smooth-env` (2)). -/
theorem differentiableOn_Ee_symmStrip {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    DifferentiableOn ℂ (Ee δ) {b : ℂ | |b.im| < 1 / 2} := by
  have hsymm : ∀ z ∈ symmStrip, reflHoriz 0 z ∈ symmStrip := by
    intro z hz
    change |(reflHoriz 0 z).im| < 1 / 2
    rw [reflHoriz_im, two_mul, zero_add, zero_sub, abs_neg]
    exact hz
  have h_holo : DifferentiableOn ℂ (Eext δ) (symmStrip ∩ {z : ℂ | 0 < z.im}) := by
    have hsub : symmStrip ∩ {z : ℂ | 0 < z.im} ⊆ outerS3HalfStrip := by
      intro z hz
      exact ⟨hz.2, (abs_lt.mp hz.1).2⟩
    refine (differentiableOn_Estripped_outerS3HalfStrip hδ0 hδ1 |>.mono hsub).congr fun z hz => ?_
    have hz2 : 0 < z.im := hz.2
    simp only [Eext, ite_eq_left_iff]
    intro h; exact absurd hz2 h
  have h_real : ∀ z ∈ symmStrip, z.im = 0 → (Eext δ z).im = 0 := by
    intro z _ hzim
    simp only [Eext, hzim, lt_self_iff_false, ↓reduceIte]
    exact (EeBdry_pos_real hδ0 hδ1 z.re).2
  have hrefl := schwarzReflection isOpen_symmStrip hsymm (continuousOn_Eext hδ0 hδ1) h_holo h_real
  refine hrefl.congr fun z hz => ?_
  have hz' : |z.im| < 1 / 2 := hz
  rw [Ee, ite_eq_left_iff]
  intro h; exact absurd hz' h

/-- **`Ee δ` is zero-free on `{|Im b| < 1/2}`** (`cts:smooth-env` (2)). -/
theorem Ee_ne_zero_symmStrip {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb : |b.im| < 1 / 2) : Ee δ b ≠ 0 := by
  simp only [Ee, hb, ↓reduceIte, schwarzReflect]
  rcases lt_trichotomy b.im 0 with hlt | heq | hgt
  · have hle : ¬ (0 ≤ b.im) := not_le.mpr hlt
    simp only [hle, ↓reduceIte]
    have him_pos : 0 < (reflHoriz 0 b).im := by rw [reflHoriz_im]; linarith
    have him_lt : (reflHoriz 0 b).im < 1 / 2 := by rw [reflHoriz_im]; linarith [(abs_lt.mp hb).1]
    simp only [Eext, him_pos, ↓reduceIte]
    exact (map_ne_zero (starRingEnd ℂ)).mpr (Estripped_ne_zero_outerS3HalfStrip hδ0 hδ1 him_pos him_lt)
  · simp only [heq, le_refl, ↓reduceIte, Eext, lt_self_iff_false]
    intro hzero
    have := (EeBdry_pos_real hδ0 hδ1 b.re).1
    rw [hzero, Complex.zero_re] at this
    linarith
  · simp only [hgt.le, ↓reduceIte, Eext, hgt]
    exact Estripped_ne_zero_outerS3HalfStrip hδ0 hδ1 hgt (abs_lt.mp hb).2

/-- **`Ee δ` is even**: `Ee δ (-b) = Ee δ b` for all `b : ℂ` (`cts:smooth-env` (2)). -/
theorem Ee_neg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (b : ℂ) : Ee δ (-b) = Ee δ b := by
  by_cases hb : |b.im| < 1 / 2
  · have hnb : |(-b).im| < 1 / 2 := by simpa using hb
    simp only [Ee, hb, hnb, ↓reduceIte, schwarzReflect]
    rcases lt_trichotomy b.im 0 with hlt | heq | hgt
    · have h1 : ¬ (0 ≤ b.im) := not_le.mpr hlt
      have h2 : 0 ≤ (-b).im := by simp; linarith
      have h3 : 0 < (-b).im := by simp; linarith
      simp only [h1, h2, h3, ↓reduceIte, Eext]
      have hrefl : reflHoriz 0 b = starRingEnd ℂ b := by unfold reflHoriz; simp
      have him_pos : 0 < (starRingEnd ℂ b).im := by simp; linarith
      have him_lt : (starRingEnd ℂ b).im < 1 / 2 := by simp; linarith [(abs_lt.mp hb).1]
      rw [hrefl]
      simp only [him_pos, ↓reduceIte]
      have hsym := Estripped_neg_conj hδ0 hδ1 him_pos him_lt
      have hinv : -starRingEnd ℂ (starRingEnd ℂ b) = -b := by simp
      rw [hinv] at hsym
      exact hsym
    · have hne1 := neBot_nhdsWithin_upperHalf b.re
      have hne2 := neBot_nhdsWithin_upperHalf (-b.re)
      have h1 : 0 ≤ b.im := heq.ge
      have h2 : 0 ≤ (-b).im := by simp [heq]
      have hb0' : ¬ 0 < (-b).im := by simp [heq]
      have hb0'' : ¬ 0 < b.im := by simp [heq]
      rw [ite_eq_left_iff.mpr (fun h => absurd h2 h), ite_eq_left_iff.mpr (fun h => absurd h1 h),
        Eext, ite_eq_right_iff.mpr (fun h => absurd h hb0'),
        Eext, ite_eq_right_iff.mpr (fun h => absurd h hb0''),
        show (-b).re = -b.re by simp]
      rcases le_or_gt xiStar b.re with hx_ge | hx_lt
      · have hlim := (tendsto_Estripped_real_le_neg hδ0 hδ1 (by linarith : -b.re ≤ -xiStar)).limUnder_eq
        rwa [neg_neg] at hlim
      · rcases lt_or_ge (-xiStar) b.re with hx_gt_neg | hx_le_neg
        · have hx_abs : |b.re| < xiStar := abs_lt.mpr ⟨hx_gt_neg, hx_lt⟩
          have h1' := (tendsto_Estripped_real_abs_lt hδ0 hδ1 hx_abs).limUnder_eq
          have h2' := (tendsto_Estripped_real_abs_lt hδ0 hδ1 (by simpa using hx_abs : |-b.re| < xiStar)).limUnder_eq
          have hz_eq : zetaDReal (-b.re) = zetaDReal b.re := by unfold zetaDReal; simp
          have hd_eq : (DeltaPhi δ ((-b.re : ℝ) : ℂ)).re = (DeltaPhi δ (b.re : ℂ)).re := by
            rw [re_DeltaPhi_real hδ0 hδ1 (-b.re), re_DeltaPhi_real hδ0 hδ1 b.re]
            congr 1
            refine setIntegral_congr_ae measurableSet_Ioi (ae_of_all _ fun y _ => ?_)
            have he1 : Real.tanh (π * (-b.re - y) / 2) = -Real.tanh (π * (b.re + y) / 2) := by
              rw [show π * (-b.re - y) / 2 = -(π * (b.re + y) / 2) by ring, Real.tanh_neg]
            have he2 : Real.tanh (π * (-b.re + y) / 2) = -Real.tanh (π * (b.re - y) / 2) := by
              rw [show π * (-b.re + y) / 2 = -(π * (b.re - y) / 2) by ring, Real.tanh_neg]
            rw [he1, he2, neg_mul_neg, mul_comm (Real.tanh (π * (b.re + y) / 2))]
          unfold EeBdry
          rw [h2', h1', hz_eq, hd_eq]
        · exact ((tendsto_Estripped_real_le_neg hδ0 hδ1 hx_le_neg).limUnder_eq).symm
    · have h1 : 0 ≤ b.im := hgt.le
      have h2 : ¬ (0 ≤ (-b).im) := by simp; linarith
      simp only [h1, h2, ↓reduceIte, Eext, hgt]
      have hrefl : reflHoriz 0 (-b) = -starRingEnd ℂ b := by unfold reflHoriz; simp
      have him_pos : 0 < (-starRingEnd ℂ b).im := by simp; linarith
      have him_lt : (-starRingEnd ℂ b).im < 1 / 2 := by simp; linarith [(abs_lt.mp hb).2]
      rw [hrefl]
      simp only [him_pos, ↓reduceIte]
      rw [Estripped_neg_conj hδ0 hδ1 hgt (by linarith [(abs_lt.mp hb).2]), Complex.conj_conj]
  · rw [Ee, ite_eq_right_iff.mpr (fun h => absurd (by simpa using h) hb),
      Ee, ite_eq_right_iff.mpr (fun h => absurd h hb)]

/-- **`Ee δ` is real and strictly positive on `ℝ`** (`cts:smooth-env` (2)). -/
theorem Ee_real_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) (x : ℝ) :
    0 < (Ee δ (x : ℂ)).re ∧ (Ee δ (x : ℂ)).im = 0 := by
  have hx : |(x : ℂ).im| < 1 / 2 := by simp
  have hEe : Ee δ (x : ℂ) = EeBdry δ x := by
    simp [Ee, schwarzReflect, Eext]
  rw [hEe]
  exact EeBdry_pos_real hδ0 hδ1 x

/-- **`Ee δ` agrees with `Estripped δ` on `0 < Im b < 1/2`** (`cts:smooth-env` (2)). -/
theorem Ee_eq_Estripped {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2) :
    Ee δ b = Estripped δ b := by
  have hb : |b.im| < 1 / 2 := abs_lt.mpr ⟨by linarith, hb1⟩
  rw [Ee, ite_eq_left_iff.mpr (fun h => absurd hb h), schwarzReflect,
    ite_eq_left_iff.mpr (fun h => absurd hb0.le h), Eext, ite_eq_left_iff.mpr (fun h => absurd hb0 h)]

/-- **`Ee δ` modulus identity on `x ≥ ξ_*`** (`cts:smooth-env` (2)):
`‖Ee δ x‖ * exp(Re ΔΦ_δ(x)) = ‖F_δ(i y(x))‖`. -/
theorem Ee_modulus_identity {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {x : ℝ} (hx : xiStar ≤ x) :
    ‖Ee δ (x : ℂ)‖ * Real.exp (DeltaPhi δ (x : ℂ)).re =
      ‖fDelta Gout δ (Complex.I * (yOfX x : ℂ))‖ := by
  have hx' : |(x : ℂ).im| < 1 / 2 := by simp
  have hEe : Ee δ (x : ℂ) = EeBdry δ x := by
    simp [Ee, schwarzReflect, Eext]
  rw [hEe]
  exact (EeBdry_modulus_identity hδ0 hδ1 hx).2.2

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_Ee_symmStrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_Ee_symmStrip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_ne_zero_symmStrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_ne_zero_symmStrip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_neg

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_real_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_real_pos

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_eq_Estripped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_eq_Estripped

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_modulus_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.Ee_modulus_identity
