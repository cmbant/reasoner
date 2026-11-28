module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerDualMap
public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasGrowthBase
public import FormalResearch.ModularBootstrap.FiveTerm.StripCauchy
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroDatum
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroAmpDeriv
public import FormalResearch.ModularBootstrap.FiveTerm.LowerEdgeAsymp
public import FormalResearch.Complex.SchwarzReflection

/-!
# Cauchy Strip Integrand & Fixed-`η` Contour Identity (`cts:cauchy-dual` Step 1, Part A)

Constructs the Schwartz-reflected unit-strip integrand `lowerDualIntegrand` for `cts:cauchy-dual` Step 1:
* `dualPhi0Strip`: continuous extension of `dualPhi0 ∘ dualBStrip` to `unitStripMinusCl \ {0, 1}`.
* `gout_global_bound`: `‖Gout z‖ ≤ C_G ‖1 + z²‖^{-5/4}` uniformly on `closure halfDisc \ singPts`.
* `lowerDualPsi`: the strip integrand on `unitStripMinusCl \ {0, 1}`.
* `lowerDualIntegrand`: Schwarz reflection across `Im s = 0`, holomorphic on `unitStrip`,
  continuous on `unitStripCl \ {0, 1}`, and exponentially decaying for `η > 0`.
* `lowerDual_contour_eq_eta`: `StripCauchy.strip_edge_cauchy` gives equality of the two half-edge
  real-part integrals for every `η > 0`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set Metric intervalIntegral
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.PoissonJensen
open FormalResearch.ModularBootstrap.FixedWeightTip
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Saddle
open FormalResearch.Complex

noncomputable section

/-! ### 1. Basic geometry of `sTan`, `xT`, and `dualPhi0Strip` -/

private lemma arsinh_lt_of_lt {a b : ℝ} (hab : a < b) : Real.arsinh a < Real.arsinh b := by
  by_contra hle
  have hle' := Real.sinh_le_sinh.mpr (not_lt.mp hle)
  rw [Real.sinh_arsinh, Real.sinh_arsinh] at hle'
  linarith

lemma xT_gt_xiStar {τ : ℝ} (hτ : 0 < τ) : xiStar < xT τ := by
  unfold xT xiStar
  have hpi := Real.pi_pos
  have hch : 1 < Real.cosh (π * τ) := Real.one_lt_cosh.mpr (mul_pos hpi hτ).ne'
  have hsqrt : 1 < √(Real.cosh (π * τ)) := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one hch
  exact div_lt_div_of_pos_right (arsinh_lt_of_lt hsqrt) hpi

lemma xT_strictMonoOn_Ici : StrictMonoOn xT (Ici 0) := fun a ha b _ hab => by
  unfold xT
  have hpi := Real.pi_pos
  have ha0 : 0 ≤ π * a := mul_nonneg hpi.le (mem_Ici.mp ha)
  have hlt : π * a < π * b := mul_lt_mul_of_pos_left hab hpi
  have hch : Real.cosh (π * a) < Real.cosh (π * b) := by
    rcases (mem_Ici.mp ha).eq_or_lt with rfl | _
    · simpa using Real.one_lt_cosh.mpr (mul_pos hpi hab).ne'
    · exact Real.cosh_lt_cosh.mpr (by rw [abs_of_nonneg ha0, abs_of_pos (by linarith)]; exact hlt)
  exact div_lt_div_of_pos_right
    (arsinh_lt_of_lt (Real.sqrt_lt_sqrt (Real.cosh_pos _).le hch)) hpi

lemma xD_pos (τ : ℝ) (hτ : 0 < τ) : 0 < xD τ := by
  unfold xD
  have hsh : 0 < Real.sinh (π * τ) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hτ)
  have hc : 0 < Real.cosh (π * τ) := Real.cosh_pos _
  positivity

lemma continuous_xT_local : Continuous xT := by
  unfold xT
  exact (Real.continuous_arsinh.comp (Real.continuous_sqrt.comp
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id)))).div_const π

lemma sTan_mem_cl_diff_singPts {s : ℂ} (hs : s ∈ unitStripCl \ {0, 1}) :
    sTan s ∈ closure halfDisc \ singPts := by
  refine ⟨sTan_mem_closure hs.1, fun h => ?_⟩
  have hc := cos_ne_zero_of_cl hs.1
  have h1s := one_add_sTan_sq hs.1
  have hne_i : sTan s ≠ Complex.I := by
    intro heq; rw [heq, Complex.I_sq, add_neg_cancel] at h1s
    exact inv_ne_zero (pow_ne_zero 2 hc) h1s.symm
  have hne_mi : sTan s ≠ -Complex.I := by
    intro heq; rw [heq, neg_sq, Complex.I_sq, add_neg_cancel] at h1s
    exact inv_ne_zero (pow_ne_zero 2 hc) h1s.symm
  have hne_1 : sTan s ≠ 1 := by
    intro heq
    have hs1 : sInv (sTan s) = sInv 1 := congrArg sInv heq
    rw [sInv_sTan hs.1, sInv_one] at hs1
    exact hs.2 (by simp [hs1])
  simp only [singPts, mem_insert_iff, mem_singleton_iff] at h
  tauto

lemma gout_conj_closure {z : ℂ} (hz : z ∈ closure halfDisc \ singPts) :
    Gout (starRingEnd ℂ z) = starRingEnd ℂ (Gout z) := by
  have hz_bar : starRingEnd ℂ z ∈ closure halfDisc \ singPts := by
    refine ⟨closure_halfDisc_conj hz.1, fun h => ?_⟩
    simp only [singPts, mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h | h
    · have h1 := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, Complex.conj_I] at h1
      exact hz.2 (by simp [singPts, h1])
    · have h1 := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, map_neg, Complex.conj_I, neg_neg] at h1
      exact hz.2 (by simp [singPts, h1])
    · have h1 := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, map_one] at h1
      exact hz.2 (by simp [singPts, h1])
  have h_mem_diff : ∀ w ∈ halfDisc, w ∈ closure halfDisc \ singPts := fun w hw => by
    refine ⟨subset_closure hw, fun hs => ?_⟩
    simp only [singPts, mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · have := hw.1; simp at this
    · have := hw.1; simp at this
    · have := hw.1; simp at this
  have hne : (𝓝[halfDisc] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz.1
  have ht1 : Tendsto Gout (𝓝[halfDisc] z) (𝓝 (Gout z)) :=
    (gout_cont z hz).tendsto.mono_left (nhdsWithin_mono z h_mem_diff)
  have ht2 : Tendsto (fun w : ℂ => starRingEnd ℂ (Gout w)) (𝓝[halfDisc] z)
      (𝓝 (starRingEnd ℂ (Gout z))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp ht1
  have hmap : Tendsto (starRingEnd ℂ : ℂ → ℂ) (𝓝[halfDisc] z)
      (𝓝[closure halfDisc \ singPts] (starRingEnd ℂ z)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨Complex.continuous_conj.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw using h_mem_diff _ (halfDisc_conj hw)
  have ht3 : Tendsto (fun w : ℂ => Gout (starRingEnd ℂ w)) (𝓝[halfDisc] z)
      (𝓝 (Gout (starRingEnd ℂ z))) :=
    (gout_cont (starRingEnd ℂ z) hz_bar).tendsto.comp hmap
  have hev : (fun w : ℂ => Gout (starRingEnd ℂ w)) =ᶠ[𝓝[halfDisc] z]
      (fun w : ℂ => starRingEnd ℂ (Gout w)) := by
    filter_upwards [self_mem_nhdsWithin] with w hw using gout_conj hw
  exact tendsto_nhds_unique (ht3.congr' hev) ht2

/-- The strip potential `Φ₀(b(s))` extended continuously to `unitStripMinusCl \ {0, 1}`. -/
def dualPhi0Strip (s : ℂ) : ℂ :=
  if s.re = 0 ∧ s.im < 0 then
    -((Bessel.besselL (xT (-s.im)) : ℝ) : ℂ) - Complex.I * ((2 * π * cumulN (xT (-s.im)) : ℝ) : ℂ)
  else if 1 / 4 < (dualBStrip s).im then
    edgePhi0Blaschke (dualBStrip s)
  else
    dualPhi0 (dualBStrip s)

lemma dualPhi0Strip_of_open {s : ℂ} (hs : s ∈ unitStripMinusOpen) :
    dualPhi0Strip s = dualPhi0 (dualBStrip s) := by
  have hre : ¬ (s.re = 0 ∧ s.im < 0) := fun h => hs.1.ne' h.1
  obtain ⟨_, _, _, hbim1⟩ := dualBStrip_mem_slitStrip hs
  unfold dualPhi0Strip
  simp only [hre, ↓reduceIte]
  split_ifs with h14
  · exact (dualPhi0_eq_edgePhi0Blaschke h14 hbim1).symm
  · rfl

lemma dualPhi0Strip_imag_neg {τ : ℝ} (hτ : 0 < τ) :
    dualPhi0Strip (-((τ : ℂ) * Complex.I)) =
      -((Bessel.besselL (xT τ) : ℝ) : ℂ) - Complex.I * ((2 * π * cumulN (xT τ) : ℝ) : ℂ) := by
  unfold dualPhi0Strip
  have hcond : (-((τ : ℂ) * Complex.I)).re = 0 ∧ (-((τ : ℂ) * Complex.I)).im < 0 := by
    simp [hτ]
  simp only [hcond]
  simp

lemma dualPhi0Strip_one_add_imag_neg {τ : ℝ} (hτ : 0 < τ) :
    dualPhi0Strip (1 - (τ : ℂ) * Complex.I) =
      edgePhi0Blaschke ((vT τ : ℂ) + Complex.I / 2) := by
  unfold dualPhi0Strip
  have hnot : ¬ ((1 - (τ : ℂ) * Complex.I).re = 0 ∧ (1 - (τ : ℂ) * Complex.I).im < 0) := by
    intro h; simp at h
  simp only [hnot, ↓reduceIte, dualBStrip_one_add_imag_neg hτ]
  have him : 1 / 4 < ((vT τ : ℂ) + Complex.I / 2).im := by simp; norm_num
  simp only [him, ↓reduceIte]

lemma dualPhi0Strip_ofReal_eq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    dualPhi0Strip (x : ℂ) = dualPhi0 (dualBStrip (x : ℂ)) := by
  unfold dualPhi0Strip
  have hnot : ¬ ((x : ℂ).re = 0 ∧ (x : ℂ).im < 0) := by simp [hx0.ne']
  simp only [hnot, ↓reduceIte]
  obtain ⟨_, him_abs, _, _⟩ := dualBStrip_ofReal_prop hx0 hx1
  have him1 : (dualBStrip (x : ℂ)).im < 1 / 2 := (abs_lt.mp him_abs).2
  split_ifs with h14
  · exact (dualPhi0_eq_edgePhi0Blaschke h14 him1).symm
  · rfl

lemma dualPhi0Strip_ofReal_im_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (dualPhi0Strip (x : ℂ)).im = 0 := by
  rw [dualPhi0Strip_ofReal_eq hx0 hx1]
  exact dualBStrip_ofReal_phi0_im_zero hx0 hx1

lemma dualBStrip_im_le_half {s : ℂ} (hs : s ∈ unitStripMinusCl \ {0, 1}) :
    0 ≤ (dualBStrip s).im ∧ (dualBStrip s).im ≤ 1 / 2 := by
  have hscl := hs.1
  rcases lt_or_eq_of_le hscl.2.2 with him_neg | him0
  · rcases lt_or_eq_of_le hscl.1 with hre_pos | hre0
    · rcases lt_or_eq_of_le hscl.2.1 with hre_lt | hre1
      · obtain ⟨_, _, h1, h2⟩ := dualBStrip_mem_slitStrip ⟨hre_pos, hre_lt, him_neg⟩
        exact ⟨h1.le, h2.le⟩
      · have hs_eq : s = 1 - ((-s.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext
          · simp [hre1]
          · simp
        rw [hs_eq, dualBStrip_one_add_imag_neg (by linarith)]
        simp
    · have hs_eq : s = -(((-s.im : ℝ) : ℂ) * Complex.I) := by
        apply Complex.ext
        · simp [← hre0]
        · simp
      rw [hs_eq, dualBStrip_imag_neg (by linarith)]
      simp
  · have hx0 : 0 < s.re := by
      rcases lt_or_eq_of_le hscl.1 with h | h
      · exact h
      · exfalso; apply hs.2; left; exact Complex.ext h.symm him0
    have hx1 : s.re < 1 := by
      rcases lt_or_eq_of_le hscl.2.1 with h | h
      · exact h
      · exfalso; apply hs.2; right; exact Complex.ext h him0
    have hs_eq : s = (s.re : ℂ) := Complex.ext rfl him0
    rw [hs_eq]
    obtain ⟨hmem, _, hcase, _⟩ := dualBStrip_ofReal_prop hx0 hx1
    have hmem1 : |(dualBStrip (s.re : ℂ)).im| < 1 / 2 := hmem.1
    have hbd := abs_lt.mp hmem1
    rcases hcase with h0 | hre_b0
    · rw [h0]; norm_num
    · -- `(dualBStrip x).im ≥ 0` on `(0, 1)` when `(dualBStrip x).re = 0` (`dualWStrip x < 1`)
      have him_nn : 0 ≤ (dualBStrip (s.re : ℂ)).im := by
        have hw_re : (dualWStrip (s.re : ℂ)).re = √2 * Real.cos (π * s.re / 2) := by
          have := (dualWStrip_re_im (s.re : ℂ)).1
          simpa using this
        have hw_im : (dualWStrip (s.re : ℂ)).im = 0 := by
          have := (dualWStrip_re_im (s.re : ℂ)).2
          simpa using this
        set w0 := √2 * Real.cos (π * s.re / 2)
        have hcos_pos : 0 < Real.cos (π * s.re / 2) :=
          Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
        have hw0_pos : 0 < w0 := by positivity
        rcases eq_or_lt_of_le (show w0 ≤ 1 by
            by_contra hlt
            have hw0_gt : 1 < w0 := not_le.mp hlt
            have hsq : 0 < w0 ^ 2 - 1 := by nlinarith
            have hc : ((w0 : ℂ) ^ 2 - 1) ^ (1 / 2 : ℂ) = ((√(w0 ^ 2 - 1) : ℝ) : ℂ) := by
              rw [show ((w0 : ℂ) ^ 2 - 1) = ((w0 ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
                show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
                ← Complex.ofReal_cpow hsq.le, Real.sqrt_eq_rpow]
            have hw_eq : dualWStrip (s.re : ℂ) = (w0 : ℂ) := Complex.ext hw_re hw_im
            have hb_re_pos : 0 < (dualBStrip (s.re : ℂ)).re := by
              unfold dualBStrip
              rw [hw_eq, hc, ← Complex.ofReal_add, div_ofReal_re, ← Complex.ofReal_log (by positivity),
                Complex.ofReal_re]
              exact div_pos (Real.log_pos (by nlinarith [Real.sqrt_pos.mpr hsq])) Real.pi_pos
            linarith) with hw1 | hw0_lt
        · have hw_eq : dualWStrip (s.re : ℂ) = 1 := Complex.ext (by simp [hw_re, hw1]) (by simp [hw_im])
          have hb0 : dualBStrip (s.re : ℂ) = 0 := by
            unfold dualBStrip; rw [hw_eq, one_pow, sub_self, Complex.zero_cpow (by norm_num),
              add_zero, Complex.log_one, zero_div]
          rw [hb0]; simp
        · have hneg : 0 < 1 - w0 ^ 2 := by nlinarith
          have hw2_eq : (w0 : ℂ) ^ 2 - 1 = ((-(1 - w0 ^ 2) : ℝ) : ℂ) := by push_cast; ring
          have hne : ((-(1 - w0 ^ 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
          have hc : ((w0 : ℂ) ^ 2 - 1) ^ (1 / 2 : ℂ) = ((√(1 - w0 ^ 2) : ℝ) : ℂ) * Complex.I := by
            rw [hw2_eq, Complex.cpow_def_of_ne_zero hne]
            have hnorm : ‖((-(1 - w0 ^ 2) : ℝ) : ℂ)‖ = 1 - w0 ^ 2 := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
            have harg : Complex.arg ((-(1 - w0 ^ 2) : ℝ) : ℂ) = π :=
              Complex.arg_ofReal_of_neg (by linarith)
            have hlog : Complex.log ((-(1 - w0 ^ 2) : ℝ) : ℂ) * (1 / 2 : ℂ) =
                ((Real.log (1 - w0 ^ 2) * (1 / 2) : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * Complex.I := by
              rw [Complex.log, hnorm, harg]; push_cast; ring
            rw [hlog, Complex.exp_add, ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hneg,
              ← Real.sqrt_eq_rpow, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
              Real.cos_pi_div_two, Real.sin_pi_div_two]
            push_cast; ring
          have hw_eq : dualWStrip (s.re : ℂ) = (w0 : ℂ) := Complex.ext hw_re hw_im
          unfold dualBStrip
          rw [hw_eq, hc, div_ofReal_im, Complex.log_im]
          exact div_nonneg (Complex.arg_nonneg_iff.mpr (by simp)) Real.pi_pos.le
      exact ⟨him_nn, by linarith [hbd.2]⟩

private lemma continuousWithinAt_dualPhi0Strip_left (τ₀ : ℝ) (hτ₀ : 0 < τ₀) :
    ContinuousWithinAt dualPhi0Strip (unitStripMinusCl \ {0, 1}) (-((τ₀ : ℂ) * Complex.I)) := by
  set s₀ : ℂ := -((τ₀ : ℂ) * Complex.I)
  have hs₀ : s₀ ∈ unitStripMinusCl \ {0, 1} := by
    refine ⟨⟨by simp [s₀], by simp [s₀], by simp [s₀]; exact hτ₀.le⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => by have := congrArg Complex.im h; simp [s₀] at this; linarith,
      fun h => by have := congrArg Complex.re h; simp [s₀] at this⟩
  have hb0 : dualBStrip s₀ = (xT τ₀ : ℂ) := dualBStrip_imag_neg hτ₀
  have hcw : ContinuousWithinAt dualBStrip (unitStripMinusCl \ {0, 1}) s₀ :=
    (continuousOn_dualBStrip s₀ hs₀.1).mono sdiff_subset
  have hx_lt : xiStar < xT τ₀ := xT_gt_xiStar hτ₀
  have hval0 : dualPhi0Strip s₀ = -(((2 * π / 3 * xT τ₀ : ℝ) : ℂ)) -
      Complex.I * ((2 * π * cumulN (xT τ₀) : ℝ) : ℂ) := by
    rw [dualPhi0Strip_imag_neg hτ₀]
    unfold Bessel.besselL
    ring_nf
  rw [ContinuousWithinAt, hval0, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hf_edge : ContinuousAt (fun s : ℂ =>
      -(((2 * π / 3 * xT (-s.im) : ℝ) : ℂ)) - Complex.I * ((2 * π * cumulN (xT (-s.im)) : ℝ) : ℂ)) s₀ := by
    have hxt : Continuous (fun s : ℂ => xT (-s.im)) :=
      continuous_xT_local.comp Complex.continuous_im.neg
    have hxt_s0 : xT (-s₀.im) = xT τ₀ := by simp [s₀]
    have hcum_ca : ContinuousAt (fun s : ℂ => cumulN (xT (-s.im))) s₀ := by
      have hc0 : ContinuousWithinAt cumulN (Ioi xiStar) (xT (-s₀.im)) :=
        (continuousOn_cumulN _ (by rw [hxt_s0]; exact hx_lt.le)).mono Ioi_subset_Ici_self
      have hmap : Tendsto (fun s : ℂ => xT (-s.im)) (𝓝 s₀) (𝓝[Ioi xiStar] (xT (-s₀.im))) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨hxt.continuousAt.tendsto, ?_⟩
        have hlt : ∀ᶠ s : ℂ in 𝓝 s₀, s.im < 0 :=
          Complex.continuous_im.continuousAt.tendsto.eventually (Iio_mem_nhds (by simp [s₀]; exact hτ₀))
        exact hlt.mono fun s hs => xT_gt_xiStar (by linarith)
      exact hc0.tendsto.comp hmap
    have hL : ContinuousAt (fun s : ℂ => -(((2 * π / 3 * xT (-s.im) : ℝ) : ℂ))) s₀ :=
      (Complex.continuous_ofReal.comp (continuous_const.mul hxt)).neg.continuousAt
    have hR : ContinuousAt (fun s : ℂ => Complex.I * ((2 * π * cumulN (xT (-s.im)) : ℝ) : ℂ)) s₀ :=
      continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul hcum_ca))
    have hsub : ContinuousAt (fun s : ℂ =>
        -(((2 * π / 3 * xT (-s.im) : ℝ) : ℂ)) - Complex.I * ((2 * π * cumulN (xT (-s.im)) : ℝ) : ℂ)) s₀ :=
      hL.sub hR
    exact hsub
  obtain ⟨δ1, hδ1, hbd1⟩ := Metric.continuousAt_iff.mp hf_edge ε hε
  have ht_slit := tendsto_dualPhi0_slit hx_lt
  rw [Metric.tendsto_nhdsWithin_nhds] at ht_slit
  obtain ⟨δ2, hδ2, hbd2⟩ := ht_slit ε hε
  rw [ContinuousWithinAt, hb0, Metric.tendsto_nhdsWithin_nhds] at hcw
  obtain ⟨δ3, hδ3, hbd3⟩ := hcw (min δ2 (1 / 4)) (lt_min hδ2 (by norm_num))
  refine ⟨min (min δ1 δ3) (min (1 / 2) (τ₀ / 2)), lt_min (lt_min hδ1 hδ3) (by positivity),
    fun s hs hdist => ?_⟩
  have hd1 : dist s s₀ < δ1 := hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hd3 : dist s s₀ < δ3 := hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hre_lt : s.re < 1 := by
    have hhalf : dist s s₀ < 1 / 2 := hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    rw [dist_eq_norm] at hhalf
    have hre := (Complex.abs_re_le_norm (s - s₀)).trans_lt hhalf
    have : (s - s₀).re = s.re := by simp [s₀]
    rw [this] at hre
    linarith [(abs_lt.mp hre).2]
  have him_neg : s.im < 0 := by
    have htau : dist s s₀ < τ₀ / 2 := hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rw [dist_eq_norm] at htau
    have him := (Complex.abs_im_le_norm (s - s₀)).trans_lt htau
    have : (s - s₀).im = s.im + τ₀ := by simp [s₀]
    rw [this] at him
    linarith [(abs_lt.mp him).2]
  by_cases hre0 : s.re = 0
  · have hcond : s.re = 0 ∧ s.im < 0 := ⟨hre0, him_neg⟩
    change dist (dualPhi0Strip s) _ < ε
    have hs_eq : dualPhi0Strip s =
        -((Bessel.besselL (xT (-s.im)) : ℝ) : ℂ) - Complex.I * ((2 * π * cumulN (xT (-s.im)) : ℝ) : ℂ) := by
      unfold dualPhi0Strip
      simp only [hcond]
      rfl
    rw [hs_eq]
    have hs0_im : -s₀.im = τ₀ := by simp [s₀]
    have h1 := hbd1 hd1
    rw [hs0_im] at h1
    simpa only [Bessel.besselL, show 2 * π * xT (-s.im) / 3 = 2 * π / 3 * xT (-s.im) by ring] using h1
  · have hopen : s ∈ unitStripMinusOpen :=
      ⟨lt_of_le_of_ne hs.1.1 (Ne.symm hre0), hre_lt, him_neg⟩
    rw [dualPhi0Strip_of_open hopen]
    obtain ⟨_, _, hbim_pos, _⟩ := dualBStrip_mem_slitStrip hopen
    have hdb := hbd3 hs hd3
    exact hbd2 hbim_pos (hdb.trans_le (min_le_left _ _))

theorem continuousOn_dualPhi0Strip : ContinuousOn dualPhi0Strip (unitStripMinusCl \ {0, 1}) := by
  intro s₀ hs₀
  have hscl := hs₀.1
  by_cases hleft : s₀.re = 0
  · have him_neg : s₀.im < 0 := by
      rcases lt_or_eq_of_le hscl.2.2 with h | h
      · exact h
      · exfalso; apply hs₀.2; left; exact Complex.ext hleft h
    have heq : s₀ = -(((-s₀.im : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp [hleft]
      · simp
    rw [heq]
    exact continuousWithinAt_dualPhi0Strip_left (-s₀.im) (by linarith)
  · by_cases hright : s₀.re = 1
    · have him_neg : s₀.im < 0 := by
        rcases lt_or_eq_of_le hscl.2.2 with h | h
        · exact h
        · exfalso; apply hs₀.2; right; exact Complex.ext hright h
      have heq_s : s₀ = 1 - ((-s₀.im : ℝ) : ℂ) * Complex.I := by apply Complex.ext <;> simp [hright]
      have hb_im : (dualBStrip s₀).im = 1 / 2 := by
        rw [heq_s, dualBStrip_one_add_imag_neg (by linarith)]; simp
      have hcw : ContinuousWithinAt dualBStrip (unitStripMinusCl \ {0, 1}) s₀ :=
        (continuousOn_dualBStrip s₀ hscl).mono sdiff_subset
      have hev : ∀ᶠ s in 𝓝[unitStripMinusCl \ {0, 1}] s₀,
          dualPhi0Strip s = edgePhi0Blaschke (dualBStrip s) := by
        have h1 : ∀ᶠ s in 𝓝[unitStripMinusCl \ {0, 1}] s₀, 0 < s.re :=
          (Complex.continuous_re.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
            (Ioi_mem_nhds (by linarith : (0 : ℝ) < s₀.re))
        have h2 : ∀ᶠ s in 𝓝[unitStripMinusCl \ {0, 1}] s₀, 1 / 4 < (dualBStrip s).im := by
          have := Complex.continuous_im.continuousAt.tendsto.comp hcw
          rw [hb_im] at this
          exact this.eventually (Ioi_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))
        refine (h1.and h2).mono fun s hs => ?_
        unfold dualPhi0Strip
        simp only [show ¬ (s.re = 0 ∧ s.im < 0) from fun h => hs.1.ne' h.1, ↓reduceIte, hs.2]
      have hb_mem : dualBStrip s₀ ∈ combNMid := by
        rw [heq_s, dualBStrip_one_add_imag_neg (by linarith)]
        change |(vT (-s₀.im) + Complex.I / 2).im - 1 / 2| < 17 / 64
        simp
      have hca : ContinuousAt edgePhi0Blaschke (dualBStrip s₀) :=
        (edgePhi0Blaschke_analyticOnNhd _ hb_mem).continuousAt
      have heq0 : dualPhi0Strip s₀ = edgePhi0Blaschke (dualBStrip s₀) := by
        conv_lhs => rw [heq_s]
        conv_rhs => rw [heq_s]
        rw [dualPhi0Strip_one_add_imag_neg (by linarith), dualBStrip_one_add_imag_neg (by linarith)]
      exact (hca.comp_continuousWithinAt hcw).congr_of_eventuallyEq hev heq0
    · have hre0 : 0 < s₀.re := lt_of_le_of_ne hscl.1 (Ne.symm hleft)
      have hre1 : s₀.re < 1 := lt_of_le_of_ne hscl.2.1 hright
      have hev : ∀ᶠ s in 𝓝[unitStripMinusCl \ {0, 1}] s₀,
          dualPhi0Strip s = dualPhi0 (dualBStrip s) := by
        have h01 : ∀ᶠ s in 𝓝[unitStripMinusCl \ {0, 1}] s₀, s.re ∈ Ioo (0 : ℝ) 1 :=
          (Complex.continuous_re.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
            (isOpen_Ioo.mem_nhds ⟨hre0, hre1⟩)
        refine (h01.and self_mem_nhdsWithin).mono fun s ⟨hs01, hscl'⟩ => ?_
        rcases lt_or_eq_of_le hscl'.1.2.2 with him_neg | him0
        · exact dualPhi0Strip_of_open ⟨hs01.1, hs01.2, him_neg⟩
        · rw [show s = (s.re : ℂ) from Complex.ext rfl him0]
          exact dualPhi0Strip_ofReal_eq hs01.1 hs01.2
      have hb_mem : dualBStrip s₀ ∈ slitStrip := by
        rcases lt_or_eq_of_le hscl.2.2 with him_neg | him0
        · exact (dualBStrip_mem_slitStrip ⟨hre0, hre1, him_neg⟩).1
        · rw [show s₀ = (s₀.re : ℂ) from Complex.ext rfl him0]
          exact (dualBStrip_ofReal_prop hre0 hre1).1
      have hca : ContinuousAt dualPhi0 (dualBStrip s₀) :=
        differentiableOn_dualPhi0.continuousOn.continuousAt (isOpen_slitStrip.mem_nhds hb_mem)
      have hcw : ContinuousWithinAt dualBStrip (unitStripMinusCl \ {0, 1}) s₀ :=
        (continuousOn_dualBStrip s₀ hscl).mono sdiff_subset
      have hs0_eq : dualPhi0Strip s₀ = dualPhi0 (dualBStrip s₀) := by
        rcases lt_or_eq_of_le hscl.2.2 with him_neg | him0
        · exact dualPhi0Strip_of_open ⟨hre0, hre1, him_neg⟩
        · rw [show s₀ = (s₀.re : ℂ) from Complex.ext rfl him0]
          exact dualPhi0Strip_ofReal_eq hre0 hre1
      exact (hca.comp_continuousWithinAt hcw).congr_of_eventuallyEq hev hs0_eq

/-! ### 2. Global `Gout` growth and unit-strip exponential decay (`η > 0`) -/

lemma gout_global_bound :
    ∃ C_G : ℝ, 0 < C_G ∧ ∀ z ∈ closure halfDisc \ singPts,
      ‖Gout z‖ ≤ C_G * ‖1 + z ^ 2‖ ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨C1, c1, r1, _, hr1, hnear1⟩ := gout_near_one
  obtain ⟨CI, cI, rI, _, hrI, hnearI⟩ := gout_near_I
  let K : Set ℂ := closure halfDisc ∩
    {z : ℂ | rI ≤ ‖z - Complex.I‖ ∧ rI ≤ ‖z + Complex.I‖ ∧ r1 ≤ ‖z - 1‖}
  have hK_cl : IsClosed K :=
    isClosed_closure.inter
      ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
        ((isClosed_le continuous_const (continuous_id.add continuous_const).norm).inter
          (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)))
  have hK_bdd : Bornology.IsBounded K :=
    (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : ℂ) 1)).subset fun z hz => by
      simpa [Metric.mem_closedBall, dist_zero_right] using (closure_halfDisc_subset hz.1).1
  have hK_cmp : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_cl hK_bdd
  have hK_sub : K ⊆ closure halfDisc \ singPts := fun z hz => ⟨hz.1, fun hs => by
    simp only [singPts, mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · have : ‖(Complex.I : ℂ) - Complex.I‖ = 0 := by simp
      linarith [hz.2.1]
    · have : ‖-(Complex.I : ℂ) + Complex.I‖ = 0 := by simp
      linarith [hz.2.2.1]
    · have : ‖(1 : ℂ) - 1‖ = 0 := by simp
      linarith [hz.2.2.2]⟩
  obtain ⟨CK, hCK⟩ := hK_cmp.exists_bound_of_continuousOn (gout_cont.mono hK_sub)
  let Cbase : ℝ := max (max (max CI (C1 * √2)) CK) 1
  have hCbase : 0 < Cbase := by positivity
  refine ⟨Cbase * (2 : ℝ) ^ (5 / 4 : ℝ), by positivity, fun z hz => ?_⟩
  have h1z2_le : ‖1 + z ^ 2‖ ≤ 2 := by
    calc ‖1 + z ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2‖ := norm_add_le _ _
      _ = 1 + ‖z‖ ^ 2 := by rw [norm_one, norm_pow]
      _ ≤ 1 + 1 ^ 2 := by nlinarith [(closure_halfDisc_subset hz.1).1, norm_nonneg z]
      _ = 2 := by norm_num
  have h1z2_pos : 0 < ‖1 + z ^ 2‖ := by
    rw [norm_one_add_sq_eq]
    exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (ne_of_mem_sing hz).1))
      (norm_pos_iff.mpr (fun h => (ne_of_mem_sing hz).2.1 (eq_neg_of_add_eq_zero_left h)))
  have hpow_ge : 1 ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4 : ℝ)) := by
    have hr := Real.rpow_le_rpow h1z2_pos.le h1z2_le (by norm_num : (0 : ℝ) ≤ 5 / 4)
    have hpos54 : 0 < ‖1 + z ^ 2‖ ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos h1z2_pos _
    have h2_pos54 : (0 : ℝ) < (2 : ℝ) ^ (5 / 4 : ℝ) := by positivity
    rw [Real.rpow_neg h1z2_pos.le]
    calc (1 : ℝ) = (2 : ℝ) ^ (5 / 4 : ℝ) * ((2 : ℝ) ^ (5 / 4 : ℝ))⁻¹ := (mul_inv_cancel₀ h2_pos54.ne').symm
      _ ≤ (2 : ℝ) ^ (5 / 4 : ℝ) * (‖1 + z ^ 2‖ ^ (5 / 4 : ℝ))⁻¹ := by gcongr
  by_cases hI : ‖z - Complex.I‖ < rI ∨ ‖z + Complex.I‖ < rI
  · have hb := (hnearI z hz.1 (ne_of_mem_sing hz).1 (ne_of_mem_sing hz).2.1 hI).2
    have hCI : CI ≤ Cbase * (2 : ℝ) ^ (5 / 4 : ℝ) := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      have h2 : CI ≤ Cbase := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
      nlinarith
    exact hb.trans (mul_le_mul_of_nonneg_right hCI (Real.rpow_nonneg h1z2_pos.le _))
  · push Not at hI
    have hgz_le : ‖Gout z‖ ≤ Cbase := by
      by_cases h1 : ‖z - 1‖ < r1
      · have hb := (hnear1 z hz.1 (ne_of_mem_sing hz).2.2 h1).2
        have hnz1 : ‖z - 1‖ ≤ 2 := by
          calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ ≤ 2 := by rw [norm_one]; linarith [(closure_halfDisc_subset hz.1).1]
        have hsq : ‖z - 1‖ ^ (1 / 2 : ℝ) ≤ √2 := by
          rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt hnz1
        have hC1 : C1 * ‖z - 1‖ ^ (1 / 2 : ℝ) ≤ Cbase := by
          by_cases hC10 : 0 ≤ C1
          · exact (mul_le_mul_of_nonneg_left hsq hC10).trans
              (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
          · exact (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hC10).le
              (Real.rpow_nonneg (norm_nonneg _) _)).trans hCbase.le
        exact hb.trans hC1
      · exact (hCK z ⟨hz.1, hI.1, hI.2, not_lt.mp h1⟩).trans
          (le_trans (le_max_right _ _) (le_max_left _ _))
    calc ‖Gout z‖ ≤ Cbase * 1 := by linarith
      _ ≤ Cbase * ((2 : ℝ) ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hpow_ge hCbase.le
      _ = _ := by ring

lemma inv_one_add_sTan_sq_norm_le {s : ℂ} (hs : s ∈ unitStripCl) :
    ‖1 + sTan s ^ 2‖⁻¹ ≤ 2 * Real.exp (π * |s.im| / 2) := by
  rw [norm_one_add_sTan_sq hs, inv_inv, norm_cos_sq', re_pi_mul_div_four, im_pi_mul_div_four]
  have hcos : Real.cos (π * s.re / 4) ^ 2 ≤ 1 := Real.cos_sq_le_one _
  have hsh : Real.sinh (π * s.im / 4) ^ 2 ≤ Real.exp (π * |s.im| / 2) := by
    rw [← sq_abs (Real.sinh (π * s.im / 4))]
    have hab : |Real.sinh (π * s.im / 4)| ≤ Real.exp (π * |s.im| / 4) := by
      have : |Real.sinh (π * s.im / 4)| = Real.sinh (π * |s.im| / 4) := by
        rcases abs_cases s.im with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
        · rw [h, show π * -s.im / 4 = -(π * s.im / 4) by ring, Real.sinh_neg, abs_of_nonpos]
          exact Real.sinh_nonpos_iff.mpr (by nlinarith [Real.pi_pos])
      rw [this, Real.sinh_eq]
      have he := Real.exp_pos (-(π * |s.im| / 4))
      have ha := Real.exp_pos (π * |s.im| / 4)
      linarith
    calc |Real.sinh (π * s.im / 4)| ^ 2 ≤ Real.exp (π * |s.im| / 4) ^ 2 := by gcongr
      _ = Real.exp (π * |s.im| / 2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have he1 : 1 ≤ Real.exp (π * |s.im| / 2) := Real.one_le_exp (by positivity)
  linarith

/-- The unit-strip integrand on `Im s ≤ 0` (`s ∈ unitStripMinusCl \ {0, 1}`). -/
def lowerDualPsi (c' ε η : ℝ) (g : ℝ → ℝ) (s : ℂ) : ℂ :=
  let z := sTan s
  z * hankelContinuation c' g (dualBStrip s) * Complex.exp (-((c' : ℂ) * dualPhi0Strip s)) *
    Gout z * lowerMt ε z ^ 2 * lowerMt η z ^ (Nat.ceil c' + 2) *
    (((π / 4 : ℝ) : ℂ) * (1 + z ^ 2))

lemma lowerDualPsi_differentiableOn {c' ε η : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hε : 0 < ε) (hη : 0 ≤ η) :
    DifferentiableOn ℂ (lowerDualPsi c' ε η g) unitStripMinusOpen := by
  intro s hs
  have hscl : s ∈ unitStripCl := unitStrip_subset_cl ⟨hs.1, hs.2.1⟩
  have hz_d : DifferentiableAt ℂ sTan s :=
    (differentiableOn_sTan.mono unitStrip_subset_cl).differentiableAt (isOpen_unitStrip.mem_nhds ⟨hs.1, hs.2.1⟩)
  have hb_d : DifferentiableAt ℂ dualBStrip s :=
    differentiableOn_dualBStrip.differentiableAt (isOpen_unitStripMinusOpen.mem_nhds hs)
  obtain ⟨hb_mem, _, hbim_pos, hbim_lt⟩ := dualBStrip_mem_slitStrip hs
  have hG_d : DifferentiableAt ℂ (hankelContinuation c' g) (dualBStrip s) :=
    (differentiableOn_hankelContinuation hc' hg).differentiableAt
      ((isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds (show |(dualBStrip s).im| < 1 / 2 by
        rw [abs_of_pos hbim_pos]; exact hbim_lt))
  have hΦ_d : DifferentiableAt ℂ dualPhi0 (dualBStrip s) :=
    differentiableOn_dualPhi0.differentiableAt (isOpen_slitStrip.mem_nhds hb_mem)
  have hzs : sTan s ∈ halfDisc := sTan_mem_halfDisc ⟨hs.1, hs.2.1⟩
  have hGout_d : DifferentiableAt ℂ Gout (sTan s) :=
    gout_diff.differentiableAt (isOpen_halfDisc.mem_nhds hzs)
  have hMε_d : DifferentiableAt ℂ (lowerMt ε) (sTan s) :=
    (differentiableOn_lowerMt hε).differentiableAt (isOpen_halfDisc.mem_nhds hzs)
  have hMη_d : DifferentiableAt ℂ (lowerMt η) (sTan s) := by
    by_cases hη0 : η = 0
    · subst hη0
      have hne : 1 + sTan s ^ 2 ≠ 0 := by
        rw [one_add_sTan_sq hscl]; exact inv_ne_zero (pow_ne_zero 2 (cos_ne_zero_of_cl hscl))
      have hev : lowerMt 0 =ᶠ[𝓝 (sTan s)] fun _ => (1 : ℂ) := by
        filter_upwards [(continuousAt_const.add (continuousAt_id.pow 2)).eventually_ne hne] with w hw
        unfold lowerMt
        have hw' : 1 + w ^ 2 ≠ 0 := hw
        simp [hw']
      exact (differentiableAt_const (1 : ℂ)).congr_of_eventuallyEq hev
    · exact (differentiableOn_lowerMt (lt_of_le_of_ne hη (Ne.symm hη0))).differentiableAt
        (isOpen_halfDisc.mem_nhds hzs)
  have hev_eq : (fun w => Complex.exp (-((c' : ℂ) * dualPhi0Strip w))) =ᶠ[𝓝 s]
      (fun w => Complex.exp (-((c' : ℂ) * dualPhi0 (dualBStrip w)))) := by
    filter_upwards [isOpen_unitStripMinusOpen.mem_nhds hs] with w hw
    rw [dualPhi0Strip_of_open hw]
  have hexp_d : DifferentiableAt ℂ (fun w => Complex.exp (-((c' : ℂ) * dualPhi0Strip w))) s :=
    ((((hΦ_d.comp s hb_d).const_mul (c' : ℂ)).neg).cexp).congr_of_eventuallyEq hev_eq
  exact ((((((hz_d.mul (hG_d.comp s hb_d)).mul hexp_d).mul
    (hGout_d.comp s hz_d)).mul ((hMε_d.comp s hz_d).pow 2)).mul
    ((hMη_d.comp s hz_d).pow (Nat.ceil c' + 2))).mul
    (((differentiableAt_const (1 : ℂ)).add (hz_d.pow 2)).const_mul ((π / 4 : ℝ) : ℂ))).differentiableWithinAt

lemma lowerDualPsi_continuousOn {c' ε η : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hε : 0 < ε) (hη : 0 ≤ η) :
    ContinuousOn (lowerDualPsi c' ε η g) (unitStripMinusCl \ {0, 1}) := by
  have hz_c : ContinuousOn sTan (unitStripMinusCl \ {0, 1}) :=
    continuousOn_sTan.mono (sdiff_subset.trans fun _ h => ⟨h.1, h.2.1⟩)
  have hb_c : ContinuousOn dualBStrip (unitStripMinusCl \ {0, 1}) :=
    continuousOn_dualBStrip.mono sdiff_subset
  have hG_c : ContinuousOn (fun s => hankelContinuation c' g (dualBStrip s)) (unitStripMinusCl \ {0, 1}) :=
    (continuousOn_hankelContinuation hc' hg).comp hb_c fun s hs => by
      have hm := dualBStrip_im_le_half hs
      show |(dualBStrip s).im| ≤ 1 / 2
      rw [abs_of_nonneg hm.1]; exact hm.2
  have hΦ_c : ContinuousOn (fun s => Complex.exp (-((c' : ℂ) * dualPhi0Strip s))) (unitStripMinusCl \ {0, 1}) :=
    (continuousOn_dualPhi0Strip.const_mul (c' : ℂ)).neg.cexp
  have hGout_c : ContinuousOn (fun s => Gout (sTan s)) (unitStripMinusCl \ {0, 1}) :=
    gout_cont.comp hz_c fun _ hs => sTan_mem_cl_diff_singPts ⟨⟨hs.1.1, hs.1.2.1⟩, hs.2⟩
  have hMε_c : ContinuousOn (fun s => lowerMt ε (sTan s) ^ 2) (unitStripMinusCl \ {0, 1}) :=
    ((continuousOn_lowerMt hε).comp hz_c fun _ hs =>
      (sTan_mem_cl_diff_singPts ⟨⟨hs.1.1, hs.1.2.1⟩, hs.2⟩).1).pow 2
  have hMη_c : ContinuousOn (fun s => lowerMt η (sTan s) ^ (Nat.ceil c' + 2))
      (unitStripMinusCl \ {0, 1}) := by
    by_cases hη0 : η = 0
    · subst hη0
      refine ContinuousOn.congr (f := fun _ : ℂ => (1 : ℂ)) continuousOn_const fun s hs => ?_
      have hne : 1 + sTan s ^ 2 ≠ 0 := by
        rw [one_add_sTan_sq ⟨hs.1.1, hs.1.2.1⟩]
        exact inv_ne_zero (pow_ne_zero 2 (cos_ne_zero_of_cl ⟨hs.1.1, hs.1.2.1⟩))
      unfold lowerMt
      simp [hne]
    · exact ((continuousOn_lowerMt (lt_of_le_of_ne hη (Ne.symm hη0))).comp hz_c fun _ hs =>
        (sTan_mem_cl_diff_singPts ⟨⟨hs.1.1, hs.1.2.1⟩, hs.2⟩).1).pow (Nat.ceil c' + 2)
  exact (((((hz_c.mul hG_c).mul hΦ_c).mul hGout_c).mul hMε_c).mul hMη_c).mul
    ((continuousOn_const.add (hz_c.pow 2)).const_mul ((π / 4 : ℝ) : ℂ))

lemma lowerDualPsi_ofReal_im_zero {c' ε η : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (lowerDualPsi c' ε η g (x : ℂ)).im = 0 := by
  have hx_mem : (x : ℂ) ∈ unitStripCl \ {0, 1} := ⟨⟨hx0.le, hx1.le⟩, fun h => by
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h <;> have := congrArg Complex.re h <;> simp at this <;> linarith⟩
  have hzt : ∃ z₀ : ℝ, sTan (x : ℂ) = (z₀ : ℂ) := by
    refine ⟨Real.tan (π * x / 4), ?_⟩
    unfold sTan
    rw [show (π : ℂ) * (x : ℂ) / 4 = ((π * x / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_tan]
  obtain ⟨z₀, hz₀⟩ := hzt
  have hG_real : (hankelContinuation c' g (dualBStrip (x : ℂ))).im = 0 := by
    obtain ⟨hb_mem, hb_im, hcase, _⟩ := dualBStrip_ofReal_prop hx0 hx1
    have hbd_le : |(dualBStrip (x : ℂ)).im| ≤ 1 / 2 := hb_im.le
    have hconj := hankelContinuation_conj hc' hg (b := dualBStrip (x : ℂ)) hbd_le
    rcases hcase with him0 | hre0
    · have hst : starRingEnd ℂ (dualBStrip (x : ℂ)) = dualBStrip (x : ℂ) :=
        Complex.conj_eq_iff_im.mpr him0
      rw [hst] at hconj
      exact Complex.conj_eq_iff_im.mp hconj.symm
    · have hst : starRingEnd ℂ (dualBStrip (x : ℂ)) = -dualBStrip (x : ℂ) := by
        apply Complex.ext <;> simp [hre0]
      rw [hst, hankelContinuation_neg] at hconj
      exact Complex.conj_eq_iff_im.mp hconj.symm
  have hΦ_real : (Complex.exp (-((c' : ℂ) * dualPhi0Strip (x : ℂ)))).im = 0 := by
    have him := dualPhi0Strip_ofReal_im_zero hx0 hx1
    have hex_eq : -((c' : ℂ) * dualPhi0Strip (x : ℂ)) =
        (((-(c' * (dualPhi0Strip (x : ℂ)).re) : ℝ) : ℂ)) := by
      apply Complex.ext
      · simp
      · simp [him]
    rw [hex_eq, ← Complex.ofReal_exp, Complex.ofReal_im]
  have hGout_real : (Gout (z₀ : ℂ)).im = 0 := by
    have hc := gout_conj_closure (sTan_mem_cl_diff_singPts hx_mem)
    rw [hz₀, Complex.conj_ofReal] at hc
    exact Complex.conj_eq_iff_im.mp hc.symm
  have hMt_real : ∀ α : ℝ, (lowerMt α (z₀ : ℂ)).im = 0 := fun α => by
    have heq : lowerMt α (z₀ : ℂ) =
        (((1 + α) * (1 + z₀ ^ 2) / (1 + z₀ ^ 2 + α * (1 + z₀)) : ℝ) : ℂ) := by
      unfold lowerMt; push_cast; ring
    rw [heq, Complex.ofReal_im]
  have h_eq : ∀ u : ℂ, u.im = 0 → ∃ r : ℝ, u = (r : ℂ) := fun u hu => ⟨u.re, Complex.ext rfl hu⟩
  obtain ⟨rG, hrG⟩ := h_eq _ hG_real
  obtain ⟨rΦ, hrΦ⟩ := h_eq _ hΦ_real
  obtain ⟨rO, hrO⟩ := h_eq _ hGout_real
  obtain ⟨rE, hrE⟩ := h_eq _ (hMt_real ε)
  obtain ⟨rH, hrH⟩ := h_eq _ (hMt_real η)
  have hpsi_eq : lowerDualPsi c' ε η g (x : ℂ) =
      (((z₀ * rG * rΦ * rO * rE ^ 2 * rH ^ (Nat.ceil c' + 2) * ((π / 4) * (1 + z₀ ^ 2)) : ℝ) : ℂ)) := by
    dsimp only [lowerDualPsi]
    rw [hz₀, hrG, hrΦ, hrO, hrE, hrH]
    push_cast
    ring
  rw [hpsi_eq, Complex.ofReal_im]

lemma lowerDualPsi_decay {c' ε η : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ unitStripMinusOpen,
      ‖lowerDualPsi c' ε η g s‖ ≤ C * Real.exp (-(π / 4 * |s.im|)) := by
  obtain ⟨C_G, hCG, hG_bd⟩ := gout_global_bound
  let M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
  let N : ℕ := Nat.ceil c' + 2
  have hN_ge : c' ≤ (N : ℝ) - 2 := by
    have h1 := Nat.le_ceil c'
    have h2 : ((Nat.ceil c' : ℕ) : ℝ) + 2 = (N : ℝ) := by simp [N]
    linarith
  have hc0 : 0 < c' := by linarith
  have hpi := Real.pi_pos
  let Ctot : ℝ := (4 * π * Real.exp 92 * c' ^ 2 * M) *
      Real.exp (-c' * majorantU0 + c' * (2 * π / 3)) *
      (C_G * (π / 4) * (2 : ℝ) ^ (1 / 4 : ℝ)) * (1 + ε) ^ 2 *
      (((1 + η) / η) * 4) ^ N
  refine ⟨max Ctot 0, le_max_right _ _, fun s hs => ?_⟩
  have hscl : s ∈ unitStripCl := unitStrip_subset_cl ⟨hs.1, hs.2.1⟩
  have hsd : s ∈ unitStripCl \ {0, 1} := ⟨hscl, fun h => by
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h <;> have := congrArg Complex.im h <;> simp at this <;> linarith [hs.2.2]⟩
  have hzs : sTan s ∈ halfDisc := sTan_mem_halfDisc ⟨hs.1, hs.2.1⟩
  have hzs_cl : sTan s ∈ closure halfDisc := subset_closure hzs
  have h1 : ‖sTan s‖ ≤ 1 := hzs.1.le
  obtain ⟨hb_mem, hb_re, hb_im0, hb_im1⟩ := dualBStrip_mem_slitStrip hs
  have h2 : ‖hankelContinuation c' g (dualBStrip s)‖ ≤ 4 * π * Real.exp 92 * c' ^ 2 * M :=
    lemmaB_d_sup hc' hg (by rw [abs_of_pos hb_im0]; exact hb_im1.le)
  have h3 : ‖Complex.exp (-((c' : ℂ) * dualPhi0Strip s))‖ ≤
      Real.exp (-c' * majorantU0 + c' * (2 * π / 3)) * Real.exp (c' * π / 3 * |s.im|) := by
    rw [dualPhi0Strip_of_open hs, Complex.norm_exp]
    have hre_ge := re_dualPhi0_ge hb_re.le hb_im0 hb_im1
    have hbre_le := dualBStrip_re_le ⟨hs.1.le, hs.2.1.le, hs.2.2.le⟩
    have harg_le : (-((c' : ℂ) * dualPhi0 (dualBStrip s))).re ≤
        -c' * majorantU0 + c' * (2 * π / 3) + c' * π / 3 * |s.im| := by
      have h1 := mul_le_mul_of_nonneg_left hre_ge hc0.le
      have h2 := mul_le_mul_of_nonneg_left hbre_le (by positivity : 0 ≤ c' * (2 * π / 3))
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith
    calc Real.exp (-((c' : ℂ) * dualPhi0 (dualBStrip s))).re
        ≤ Real.exp (-c' * majorantU0 + c' * (2 * π / 3) + c' * π / 3 * |s.im|) :=
          Real.exp_le_exp.mpr harg_le
      _ = Real.exp (-c' * majorantU0 + c' * (2 * π / 3)) * Real.exp (c' * π / 3 * |s.im|) :=
          Real.exp_add _ _
  have h1z2_pos : 0 < ‖1 + sTan s ^ 2‖ := by
    rw [norm_one_add_sTan_sq hscl]; exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (cos_ne_zero_of_cl hscl)) 2)
  have h4 : ‖Gout (sTan s) * (((π / 4 : ℝ) : ℂ) * (1 + sTan s ^ 2))‖ ≤
      C_G * (π / 4) * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * |s.im|) := by
    have hgb := hG_bd (sTan s) (sTan_mem_cl_diff_singPts hsd)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hcomb : ‖1 + sTan s ^ 2‖ ^ (-(5 / 4 : ℝ)) * ‖1 + sTan s ^ 2‖ =
        (‖1 + sTan s ^ 2‖⁻¹) ^ (1 / 4 : ℝ) := by
      rw [Real.inv_rpow h1z2_pos.le, ← Real.rpow_neg h1z2_pos.le, ← Real.rpow_add_one h1z2_pos.ne']
      congr 1; norm_num
    have hinv_le := inv_one_add_sTan_sq_norm_le hscl
    have hinv4 : (‖1 + sTan s ^ 2‖⁻¹) ^ (1 / 4 : ℝ) ≤
        (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * |s.im|) := by
      calc (‖1 + sTan s ^ 2‖⁻¹) ^ (1 / 4 : ℝ)
          ≤ (2 * Real.exp (π * |s.im| / 2)) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (inv_nonneg.mpr h1z2_pos.le) hinv_le (by norm_num)
        _ = (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * |s.im|) := by
            rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
            congr 2; ring
    calc ‖Gout (sTan s)‖ * (π / 4 * ‖1 + sTan s ^ 2‖)
        ≤ (C_G * ‖1 + sTan s ^ 2‖ ^ (-(5 / 4 : ℝ))) * (π / 4 * ‖1 + sTan s ^ 2‖) := by gcongr
      _ = C_G * (π / 4) * (‖1 + sTan s ^ 2‖ ^ (-(5 / 4 : ℝ)) * ‖1 + sTan s ^ 2‖) := by ring
      _ = C_G * (π / 4) * (‖1 + sTan s ^ 2‖⁻¹) ^ (1 / 4 : ℝ) := by rw [hcomb]
      _ ≤ C_G * (π / 4) * ((2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * |s.im|)) := by gcongr
      _ = _ := by ring
  have h5 : ‖lowerMt ε (sTan s) ^ 2‖ ≤ (1 + ε) ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_lowerMt_le hε.le hzs_cl) 2
  have h6 : ‖lowerMt η (sTan s) ^ N‖ ≤ (((1 + η) / η) * 4) ^ N * Real.exp (-(N * π / 2 * |s.im|)) := by
    rw [norm_pow]
    have hM := (norm_lowerMt_decay hη hzs_cl).trans
      (mul_le_mul_of_nonneg_left (norm_one_add_sTan_sq_le hscl) (by positivity))
    calc ‖lowerMt η (sTan s)‖ ^ N
        ≤ (((1 + η) / η) * 4 * Real.exp (-(π * |s.im| / 2))) ^ N :=
          pow_le_pow_left₀ (norm_nonneg _) (hM.trans_eq (by ring)) N
      _ = (((1 + η) / η) * 4) ^ N * (Real.exp (-(π * |s.im| / 2))) ^ N := mul_pow _ _ N
      _ = (((1 + η) / η) * 4) ^ N * Real.exp (-(N * π / 2 * |s.im|)) := by
          rw [← Real.exp_nat_mul]; congr 2; ring
  have hexp_sum : Real.exp (c' * π / 3 * |s.im|) * Real.exp (π / 8 * |s.im|) *
      Real.exp (-(N * π / 2 * |s.im|)) ≤ Real.exp (-(π / 4 * |s.im|)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hcoef : c' * π / 3 + π / 8 - (N : ℝ) * π / 2 ≤ -(π / 4) := by
      have : (c' * π / 3 - (N : ℝ) * π / 2) ≤ -π := by
        nlinarith [hN_ge, Real.pi_pos, hc0]
      linarith [Real.pi_pos]
    nlinarith [abs_nonneg s.im]
  have hM_nn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg (by rw [virasoroProblem_totalShift]; linarith) g
  have hnorm_all : ‖lowerDualPsi c' ε η g s‖ ≤ Ctot * Real.exp (-(π / 4 * |s.im|)) := by
    unfold lowerDualPsi
    simp only [norm_mul]
    calc ‖sTan s‖ * ‖hankelContinuation c' g (dualBStrip s)‖ *
          ‖Complex.exp (-((c' : ℂ) * dualPhi0Strip s))‖ * ‖Gout (sTan s)‖ *
          ‖lowerMt ε (sTan s) ^ 2‖ * ‖lowerMt η (sTan s) ^ N‖ *
          (‖((π / 4 : ℝ) : ℂ)‖ * ‖1 + sTan s ^ 2‖)
        = ‖sTan s‖ * (‖hankelContinuation c' g (dualBStrip s)‖ *
            (‖Complex.exp (-((c' : ℂ) * dualPhi0Strip s))‖ *
              (‖Gout (sTan s) * (((π / 4 : ℝ) : ℂ) * (1 + sTan s ^ 2))‖ *
                (‖lowerMt ε (sTan s) ^ 2‖ * ‖lowerMt η (sTan s) ^ N‖)))) := by
          rw [norm_mul (Gout (sTan s)), norm_mul ((π / 4 : ℝ) : ℂ)]; ring
      _ ≤ 1 * ((4 * π * Real.exp 92 * c' ^ 2 * M) *
            ((Real.exp (-c' * majorantU0 + c' * (2 * π / 3)) * Real.exp (c' * π / 3 * |s.im|)) *
              ((C_G * (π / 4) * (2 : ℝ) ^ (1 / 4 : ℝ) * Real.exp (π / 8 * |s.im|)) *
                ((1 + ε) ^ 2 * ((((1 + η) / η) * 4) ^ N * Real.exp (-(N * π / 2 * |s.im|))))))) := by
          gcongr
      _ = Ctot * (Real.exp (c' * π / 3 * |s.im|) * Real.exp (π / 8 * |s.im|) *
            Real.exp (-(N * π / 2 * |s.im|))) := by dsimp [Ctot]; ring
      _ ≤ Ctot * Real.exp (-(π / 4 * |s.im|)) := by gcongr
  exact hnorm_all.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-! ### 3. Schwarz reflection to `unitStrip` and Cauchy contour identity for `η > 0` -/

/-- Schwarz-reflected integrand on `unitStripCl \ {0, 1}`: `lowerDualPsi` on `Im s ≤ 0`,
and `conj (lowerDualPsi (conj s))` on `Im s > 0`. -/
def lowerDualIntegrand (c' ε η : ℝ) (g : ℝ → ℝ) (s : ℂ) : ℂ :=
  if s.im ≤ 0 then lowerDualPsi c' ε η g s
  else starRingEnd ℂ (lowerDualPsi c' ε η g (starRingEnd ℂ s))

lemma lowerDualIntegrand_neg_im {c' ε η : ℝ} (g : ℝ → ℝ) {s : ℂ} (hs : s.im ≤ 0) :
    lowerDualIntegrand c' ε η g s = lowerDualPsi c' ε η g s := by
  unfold lowerDualIntegrand; simp [hs]

lemma lowerDualIntegrand_pos_im {c' ε η : ℝ} (g : ℝ → ℝ) {s : ℂ} (hs : 0 < s.im) :
    lowerDualIntegrand c' ε η g s = starRingEnd ℂ (lowerDualPsi c' ε η g (starRingEnd ℂ s)) := by
  unfold lowerDualIntegrand; simp [not_le.mpr hs]

private lemma hasDerivAt_conj_conj_local {f : ℂ → ℂ} {z d : ℂ}
    (hf : HasDerivAt f d (starRingEnd ℂ z)) :
    HasDerivAt (fun w : ℂ => starRingEnd ℂ (f (starRingEnd ℂ w))) (starRingEnd ℂ d) z := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hf ⊢
  have hcont : Continuous fun t : ℂ => starRingEnd ℂ t := Complex.continuous_conj
  have htend : Tendsto (fun t : ℂ => starRingEnd ℂ t) (𝓝[≠] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun t (ht : t ≠ 0) => by simpa using ht⟩
  refine ((hcont.tendsto d).comp (hf.comp htend)).congr' (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, smul_eq_mul]
  rw [map_mul, map_inv₀, Complex.conj_conj, map_sub, map_add]

lemma lowerDualIntegrand_continuousOn {c' ε η : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hε : 0 < ε) (hη : 0 ≤ η) :
    ContinuousOn (lowerDualIntegrand c' ε η g) (unitStripCl \ {0, 1}) := by
  let S_lo : Set ℂ := (unitStripCl \ {0, 1}) ∩ {s : ℂ | s.im ≤ 0}
  let S_hi : Set ℂ := (unitStripCl \ {0, 1}) ∩ {s : ℂ | 0 ≤ s.im}
  have hS_lo : S_lo = unitStripMinusCl \ {0, 1} := by
    ext s
    simp only [S_lo, unitStripCl, unitStripMinusCl, mem_inter_iff, Set.mem_sdiff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hne⟩, h3⟩; exact ⟨⟨h1, h2, h3⟩, hne⟩
    · rintro ⟨⟨h1, h2, h3⟩, hne⟩; exact ⟨⟨⟨h1, h2⟩, hne⟩, h3⟩
  have hlo : ContinuousOn (lowerDualIntegrand c' ε η g) S_lo := by
    refine (lowerDualPsi_continuousOn hc' hg hε hη).congr ?_ |>.mono (by rw [hS_lo])
    intro s hs
    have hsim : s.im ≤ 0 := (by rw [← hS_lo] at hs; exact hs.2)
    rw [lowerDualIntegrand_neg_im g hsim]
  have hhi_eq : EqOn (lowerDualIntegrand c' ε η g)
      (fun s => starRingEnd ℂ (lowerDualPsi c' ε η g (starRingEnd ℂ s))) S_hi := by
    intro s hs
    have him_ge : 0 ≤ s.im := hs.2
    rcases lt_or_eq_of_le him_ge with him | him0
    · exact lowerDualIntegrand_pos_im g him
    · rw [lowerDualIntegrand_neg_im g him0.symm.le]
      have hx_mem : s.re ∈ Ioo (0 : ℝ) 1 := by
        have h1 := hs.1.1
        rcases h1.1.eq_or_lt with h0 | h0
        · exfalso; apply hs.1.2; left; exact Complex.ext h0.symm him0.symm
        · rcases h1.2.eq_or_lt with h2 | h2
          · exfalso; apply hs.1.2; right; exact Complex.ext h2 him0.symm
          · exact ⟨h0, h2⟩
      have hs_eq : s = (s.re : ℂ) := Complex.ext rfl him0.symm
      rw [hs_eq]
      dsimp only
      rw [Complex.conj_ofReal]
      exact (Complex.conj_eq_iff_im.mpr (lowerDualPsi_ofReal_im_zero hc' hg hx_mem.1 hx_mem.2)).symm
  have hhi : ContinuousOn (lowerDualIntegrand c' ε η g) S_hi := by
    refine ContinuousOn.congr ?_ hhi_eq
    refine Complex.continuous_conj.comp_continuousOn ?_
    refine (lowerDualPsi_continuousOn hc' hg hε hη).comp Complex.continuous_conj.continuousOn ?_
    intro s hs
    refine ⟨⟨by simpa using hs.1.1.1, by simpa using hs.1.1.2, by simpa using hs.2⟩, fun h => ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h
    · apply hs.1.2; left; rw [← Complex.conj_conj s, h]; simp
    · apply hs.1.2; right; rw [← Complex.conj_conj s, h]; simp
  have hunion : unitStripCl \ {0, 1} = S_lo ∪ S_hi := by
    ext s; simp only [S_lo, S_hi, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro h; rcases le_total s.im 0 with hi | hi <;> [exact Or.inl ⟨h, hi⟩; exact Or.inr ⟨h, hi⟩]
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  rw [hunion]
  intro s hs
  rcases hs with h | h
  · have him_le : s.im ≤ 0 := h.2
    rcases lt_or_eq_of_le him_le with him | him0
    · rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hbd⟩ := Metric.continuousWithinAt_iff.mp (hlo s h) ε hε
      refine ⟨min δ (-s.im), lt_min hδ (by linarith), fun w hw hdw => ?_⟩
      have him_w : w.im < 0 := by
        have h1 := (Complex.abs_im_le_norm (w - s)).trans_lt (by simpa [dist_eq_norm] using hdw.trans_le (min_le_right _ _))
        rw [Complex.sub_im] at h1
        linarith [(abs_lt.mp h1).2]
      have hw_lo : w ∈ S_lo := ⟨hw.elim And.left And.left, him_w.le⟩
      exact hbd hw_lo (hdw.trans_le (min_le_left _ _))
    · exact (hlo s h).union (hhi s ⟨h.1, (him0.ge : 0 ≤ s.im)⟩)
  · have him_ge : 0 ≤ s.im := h.2
    rcases lt_or_eq_of_le him_ge with him | him0
    · rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hbd⟩ := Metric.continuousWithinAt_iff.mp (hhi s h) ε hε
      refine ⟨min δ s.im, lt_min hδ him, fun w hw hdw => ?_⟩
      have him_w : 0 < w.im := by
        have h1 := (Complex.abs_im_le_norm (w - s)).trans_lt (by simpa [dist_eq_norm] using hdw.trans_le (min_le_right _ _))
        rw [Complex.sub_im] at h1
        linarith [(abs_lt.mp h1).1]
      have hw_hi : w ∈ S_hi := ⟨hw.elim And.left And.left, him_w.le⟩
      exact hbd hw_hi (hdw.trans_le (min_le_left _ _))
    · exact (hlo s ⟨h.1, (him0.symm.le : s.im ≤ 0)⟩).union (hhi s h)

lemma lowerDualIntegrand_differentiableOn {c' ε η : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hε : 0 < ε) (hη : 0 ≤ η) :
    DifferentiableOn ℂ (lowerDualIntegrand c' ε η g) unitStrip := by
  refine differentiableOn_of_continuousOn_off_horizLine (a := 0) isOpen_unitStrip ?_ ?_
  · exact (lowerDualIntegrand_continuousOn hc' hg hε hη).mono fun s hs => ⟨unitStrip_subset_cl hs, fun h => by
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with h0 | h1
      · have := congrArg Complex.re h0; simp at this; linarith [hs.1]
      · have := congrArg Complex.re h1; simp at this; linarith [hs.2]⟩
  · intro s hs
    have him_ne : s.im ≠ 0 := hs.2
    rcases lt_or_gt_of_ne him_ne with him_neg | him_pos
    · have hopen : IsOpen (unitStrip ∩ {w : ℂ | w.im < 0}) :=
        isOpen_unitStrip.inter (isOpen_lt Complex.continuous_im continuous_const)
      have hev : lowerDualPsi c' ε η g =ᶠ[𝓝 s] lowerDualIntegrand c' ε η g := by
        filter_upwards [hopen.mem_nhds ⟨hs.1, him_neg⟩] with w hw
        exact (lowerDualIntegrand_neg_im g hw.2.le).symm
      have hdiff := (lowerDualPsi_differentiableOn hc' hg hε hη).differentiableAt
        (isOpen_unitStripMinusOpen.mem_nhds ⟨hs.1.1, hs.1.2, him_neg⟩)
      exact (hdiff.congr_of_eventuallyEq hev.symm).differentiableWithinAt
    · have hopen : IsOpen (unitStrip ∩ {w : ℂ | 0 < w.im}) :=
        isOpen_unitStrip.inter (isOpen_lt continuous_const Complex.continuous_im)
      have hs_conj : starRingEnd ℂ s ∈ unitStripMinusOpen :=
        ⟨by simpa using hs.1.1, by simpa using hs.1.2, by simpa using him_pos⟩
      have hdiff_c := ((lowerDualPsi_differentiableOn hc' hg hε hη).differentiableAt
        (isOpen_unitStripMinusOpen.mem_nhds hs_conj)).hasDerivAt
      have hd_refl := (hasDerivAt_conj_conj_local hdiff_c).differentiableAt
      have hev : (fun w : ℂ => starRingEnd ℂ (lowerDualPsi c' ε η g (starRingEnd ℂ w))) =ᶠ[𝓝 s]
          lowerDualIntegrand c' ε η g := by
        filter_upwards [hopen.mem_nhds ⟨hs.1, him_pos⟩] with w hw
        exact (lowerDualIntegrand_pos_im g hw.2).symm
      exact (hd_refl.congr_of_eventuallyEq hev.symm).differentiableWithinAt

lemma lowerDualIntegrand_decay {c' ε η : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ unitStrip,
      ‖lowerDualIntegrand c' ε η g s‖ ≤ C * Real.exp (-(π / 4 * |s.im|)) := by
  obtain ⟨C, hC_nn, hC⟩ := lowerDualPsi_decay hc' hg hε hη
  refine ⟨C, hC_nn, fun s hs => ?_⟩
  rcases le_or_gt s.im 0 with him | him
  · rw [lowerDualIntegrand_neg_im g him]
    rcases him.eq_or_lt with him0 | him_neg
    · have hmem : s ∈ unitStripMinusCl \ {0, 1} := ⟨⟨hs.1.le, hs.2.le, him⟩, fun h => by
        simp only [mem_insert_iff, mem_singleton_iff] at h
        rcases h with h0 | h1
        · have := congrArg Complex.re h0; simp at this; linarith [hs.1]
        · have := congrArg Complex.re h1; simp at this; linarith [hs.2]⟩
      have hs0 : s = (s.re : ℂ) := Complex.ext rfl him0
      have hmap : Tendsto (fun δ : ℝ => (s.re : ℂ) - ((δ : ℝ) : ℂ) * Complex.I) (𝓝[>] 0)
          (𝓝[unitStripMinusCl \ {0, 1}] s) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hc : Continuous fun δ : ℝ => (s.re : ℂ) - ((δ : ℝ) : ℂ) * Complex.I := by fun_prop
          have h0 : Tendsto (fun δ : ℝ => (s.re : ℂ) - ((δ : ℝ) : ℂ) * Complex.I) (𝓝[>] 0) (𝓝 s) := by
            simpa [← hs0] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
          exact h0
        · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
          refine ⟨⟨by simp [hs.1.le], by simp [hs.2.le], by simp [hδ.le]⟩, fun h => ?_⟩
          simp only [mem_insert_iff, mem_singleton_iff] at h
          rcases h with h | h
          · have := congrArg Complex.re h; simp at this; linarith [hs.1]
          · have := congrArg Complex.re h; simp at this; linarith [hs.2]
      have hct := ((lowerDualPsi_continuousOn hc' hg hε hη.le s hmem).tendsto.comp hmap).norm
      refine le_of_tendsto hct ?_
      filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      have hopen : (s.re : ℂ) - ((δ : ℝ) : ℂ) * Complex.I ∈ unitStripMinusOpen :=
        ⟨by simp [hs.1], by simp [hs.2], by simp [hδ]⟩
      have hbd := hC _ hopen
      have him_eq : |((s.re : ℂ) - ((δ : ℝ) : ℂ) * Complex.I).im| = δ := by
        simp [abs_of_pos hδ]
      rw [him_eq] at hbd
      have hle : Real.exp (-(π / 4 * δ)) ≤ Real.exp (-(π / 4 * |s.im|)) := by
        rw [him0, abs_zero, mul_zero, neg_zero, Real.exp_zero, Real.exp_le_one_iff]
        nlinarith [Real.pi_pos, hδ]
      exact hbd.trans (mul_le_mul_of_nonneg_left hle hC_nn)
    · exact hC s ⟨hs.1, hs.2, him_neg⟩
  · rw [lowerDualIntegrand_pos_im g him, Complex.norm_conj]
    have hbd := hC (starRingEnd ℂ s) ⟨by simpa using hs.1, by simpa using hs.2, by simpa using him⟩
    simpa [abs_neg] using hbd

theorem lowerDual_contour_eq_eta {c' ε η : ℝ} (hc' : 1000 ≤ c')
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem (c' / 12) g)
    (hε : 0 < ε) (hη : 0 < η) :
    ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε η g (-((τ : ℂ) * Complex.I))).re =
      ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε η g (1 - (τ : ℂ) * Complex.I)).re := by
  obtain ⟨C, _, hC⟩ := lowerDualIntegrand_decay hc' hg hε hη
  have hcau := strip_edge_cauchy
    (lowerDualIntegrand_differentiableOn hc' hg hε hη.le) (by positivity : 0 < π / 4)
    (lowerDualIntegrand_continuousOn hc' hg hε hη.le) hC
  have hre : ∫ τ : ℝ, (lowerDualIntegrand c' ε η g ((τ : ℂ) * Complex.I)).re =
      ∫ τ : ℝ, (lowerDualIntegrand c' ε η g (1 + (τ : ℂ) * Complex.I)).re := by
    have h := congrArg Complex.re hcau.2.2
    have h1 := Complex.reCLM.integral_comp_comm hcau.1
    have h2 := Complex.reCLM.integral_comp_comm hcau.2.1
    simp only [Complex.reCLM_apply] at h1 h2
    linarith
  have hre_int1 : Integrable (fun τ : ℝ => (lowerDualIntegrand c' ε η g ((τ : ℂ) * Complex.I)).re) :=
    Complex.reCLM.integrable_comp hcau.1
  have hre_int2 : Integrable (fun τ : ℝ => (lowerDualIntegrand c' ε η g (1 + (τ : ℂ) * Complex.I)).re) :=
    Complex.reCLM.integrable_comp hcau.2.1
  have hsplit : ∀ (f : ℝ → ℝ), Integrable f → (∀ τ > 0, f (-τ) = f τ) →
      ∫ τ : ℝ, f τ = 2 * ∫ τ in Ioi (0 : ℝ), f τ := fun f hf heven => by
    rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hf.integrableOn hf.integrableOn]
    have hneg : ∫ τ in Iic (0 : ℝ), f τ = ∫ τ in Ioi (0 : ℝ), f τ := by
      have h1 : ∫ τ in Ioi (0 : ℝ), f (-τ) = ∫ τ in Iic (0 : ℝ), f τ := by
        simp [integral_comp_neg_Ioi (0 : ℝ) f]
      rw [← h1]
      exact setIntegral_congr_fun measurableSet_Ioi fun τ hτ => heven τ (mem_Ioi.mp hτ)
    rw [hneg, two_mul]
  have hL := hsplit _ hre_int1 fun τ hτ => by
    have h1 : ((-τ : ℝ) : ℂ) * Complex.I = -((τ : ℂ) * Complex.I) := by push_cast; ring
    have h2 : ((τ : ℂ) * Complex.I).im = τ := by simp
    have h3 : (-((τ : ℂ) * Complex.I)).im = -τ := by simp
    rw [h1, lowerDualIntegrand_neg_im g (by linarith [h3]), lowerDualIntegrand_pos_im g (by linarith [h2])]
    simp
  have hR := hsplit _ hre_int2 fun τ hτ => by
    have h1 : (1 : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I = 1 - (τ : ℂ) * Complex.I := by push_cast; ring
    have h2 : (1 + (τ : ℂ) * Complex.I).im = τ := by simp
    have h3 : (1 - (τ : ℂ) * Complex.I).im = -τ := by simp
    have hconj : starRingEnd ℂ (1 + (τ : ℂ) * Complex.I) = 1 - (τ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [h1, lowerDualIntegrand_neg_im g (by linarith [h3]), lowerDualIntegrand_pos_im g (by linarith [h2]), hconj]
    simp
  have hL_eq : ∫ τ in Ioi (0 : ℝ), (lowerDualIntegrand c' ε η g ((τ : ℂ) * Complex.I)).re =
      ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε η g (-((τ : ℂ) * Complex.I))).re := by
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have h2 : ((τ : ℂ) * Complex.I).im = τ := by simp
    rw [lowerDualIntegrand_pos_im g (by linarith [mem_Ioi.mp hτ, h2])]
    simp
  have hR_eq : ∫ τ in Ioi (0 : ℝ), (lowerDualIntegrand c' ε η g (1 + (τ : ℂ) * Complex.I)).re =
      ∫ τ in Ioi (0 : ℝ), (lowerDualPsi c' ε η g (1 - (τ : ℂ) * Complex.I)).re := by
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have h2 : (1 + (τ : ℂ) * Complex.I).im = τ := by simp
    have hconj : starRingEnd ℂ (1 + (τ : ℂ) * Complex.I) = 1 - (τ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [lowerDualIntegrand_pos_im g (by linarith [mem_Ioi.mp hτ, h2]), hconj]
    simp
  rw [hL, hR, hL_eq, hR_eq] at hre
  linarith

end

end FormalResearch.ModularBootstrap.FiveTerm
