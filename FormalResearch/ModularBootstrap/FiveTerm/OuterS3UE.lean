module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3a
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS3Bdry
public import FormalResearch.ModularBootstrap.FiveTerm.OuterS4b

/-!
# FIVE-S, S3 (step 3a): `ζ_D`, `η_δ`, `R4` on the strip, and the boundary potential `u_E`

Prepares the explicit analytic ingredients for extending `Ee` across `E_+ = {Im b = 1/2}`
up to `{|Im b| < 1/2 + η_δ}` (Paper II, Lemma C10 / `cts:smooth-env` (2)):

* `differentiableOn_zetaD_imStrip`: `ζ_D` is holomorphic and zero-free on the full strip `0 < Im b < 1`.
* `one_sub_one_sub_delta_zetaD_mem_slitPlane`: for `δ ∈ (0, 1/4)` and `0 < Im b < 1/2 + η_δ`,
  `1 - (1 - δ) ζ_D(b) ∈ slitPlane`, so `(1 - (1 - δ) ζ_D(b))^{-1/2}` is holomorphic and zero-free there.
* `R4cStrip`: explicit holomorphic zero-free extension of `R4c ∘ ζ_D` to `bandUpper (1/4)`, agreeing
  with `R4c (ζ_D b)` on `1/4 < Im b < 1/2`, with `‖R4cStrip (v + i/2)‖ = (v² + 1/4)^{1/4} / √ξ_*`.
* `uE`: explicit even holomorphic function on `{|Im w| < 1/8}`, real on `ℝ`, whose real part at
  `v = vOf y` equals `log ‖Ĝ(e^{-iψ(y)})‖`.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-! ### 1. `zetaD` on the full strip `imStrip = {0 < Im b < 1}` -/

lemma zetaD_w_mem_slitPlane_imStrip {b : ℂ} (hb : b ∈ imStrip) :
    (√2 : ℂ) + Complex.cosh ((π : ℂ) * b) ≠ 0 ∧
      ((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) ∈
        Complex.slitPlane := by
  have hpi := Real.pi_pos
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h1s2 : (1 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  set c := Complex.cosh ((π : ℂ) * b) with hcdef
  have hsin : 0 < Real.sin (π * b.im) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hb.1) (by nlinarith [hb.2])
  by_cases hre0 : b.re = 0
  · have hb_eq : ((b.im : ℂ) * Complex.I) = b := by apply Complex.ext <;> simp [hre0]
    have hc_eq : c = ((Real.cos (π * b.im) : ℝ) : ℂ) := by
      rw [hcdef, ← hb_eq,
        show (π : ℂ) * ((b.im : ℂ) * Complex.I) = ((π * b.im : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.cosh_mul_I, ← Complex.ofReal_cos]
      simp
    have hcos_le : Real.cos (π * b.im) ≤ 1 := Real.cos_le_one _
    have hcos_ge : -1 ≤ Real.cos (π * b.im) := Real.neg_one_le_cos _
    have hden_r : 0 < √2 + Real.cos (π * b.im) := by linarith
    have hnum_r : 0 < √2 - Real.cos (π * b.im) := by linarith
    have hden : (√2 : ℂ) + c ≠ 0 := by
      rw [hc_eq, ← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr hden_r.ne'
    refine ⟨hden, ?_⟩
    rw [Complex.mem_slitPlane_iff]
    left
    rw [hc_eq, ← Complex.ofReal_sub, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
    exact div_pos hnum_r hden_r
  · have him_c : c.im ≠ 0 := by
      rw [hcdef, im_cosh']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      exact mul_ne_zero (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hre0)) hsin.ne'
    have hden : (√2 : ℂ) + c ≠ 0 := by
      intro h
      have : ((√2 : ℂ) + c).im = 0 := by rw [h]; simp
      simp at this
      exact him_c this
    refine ⟨hden, ?_⟩
    rw [Complex.mem_slitPlane_iff]
    right
    rw [Complex.div_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_sub, zero_add]
    have hn : 0 < Complex.normSq ((√2 : ℂ) + c) := Complex.normSq_pos.mpr hden
    have hnum : (-c.im) * (√2 + c.re) - (√2 - c.re) * c.im = -(2 * √2 * c.im) := by ring
    rw [← sub_div, hnum]
    exact div_ne_zero (by intro h; apply him_c; nlinarith) hn.ne'

lemma differentiableOn_zetaD_imStrip : DifferentiableOn ℂ zetaD imStrip := by
  intro b hb
  obtain ⟨hden, hw_slit⟩ := zetaD_w_mem_slitPlane_imStrip hb
  have hc : DifferentiableAt ℂ (fun z : ℂ => Complex.cosh ((π : ℂ) * z)) b :=
    Complex.differentiableAt_cosh.comp b ((differentiableAt_const _).mul differentiableAt_id)
  have hw : DifferentiableAt ℂ (fun z : ℂ =>
      ((√2 : ℂ) - Complex.cosh ((π : ℂ) * z)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * z))) b :=
    ((differentiableAt_const _).sub hc).div ((differentiableAt_const _).add hc) hden
  exact (hw.cpow (differentiableAt_const _) hw_slit).differentiableWithinAt

lemma zetaD_ne_zero_imStrip {b : ℂ} (hb : b ∈ imStrip) : zetaD b ≠ 0 := by
  obtain ⟨_, hw_slit⟩ := zetaD_w_mem_slitPlane_imStrip hb
  unfold zetaD
  rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hw_slit)]
  exact Complex.exp_ne_zero _

lemma zetaD_sq_eq_imStrip {b : ℂ} (_hb : b ∈ imStrip) :
    zetaD b ^ 2 = ((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) := by
  unfold zetaD
  have := Complex.cpow_nat_inv_pow
    (((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)))
    (n := 2) (by norm_num)
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact this

lemma one_add_zetaD_sq_eq {b : ℂ} (hb : b ∈ imStrip) :
    1 + zetaD b ^ 2 = 2 * (√2 : ℂ) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) := by
  obtain ⟨hden, _⟩ := zetaD_w_mem_slitPlane_imStrip hb
  rw [zetaD_sq_eq_imStrip hb]
  field_simp
  ring

lemma one_add_zetaD_sq_ne_zero_imStrip {b : ℂ} (hb : b ∈ imStrip) : 1 + zetaD b ^ 2 ≠ 0 := by
  obtain ⟨hden, _⟩ := zetaD_w_mem_slitPlane_imStrip hb
  rw [one_add_zetaD_sq_eq hb]
  have hs2 : (√2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  exact div_ne_zero (mul_ne_zero two_ne_zero hs2) hden

lemma cosh_pi_edge (v : ℝ) :
    Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)) = ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [re_cosh']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.div_ofNat_re,
      Complex.I_re, Complex.mul_im, Complex.add_im, Complex.div_ofNat_im, Complex.I_im,
      zero_mul, sub_zero, add_zero, zero_add, zero_div, mul_zero]
    rw [show π * (1 / 2) = π / 2 by ring, Real.cos_pi_div_two, mul_zero]
  · rw [im_cosh']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.div_ofNat_re,
      Complex.I_re, Complex.mul_im, Complex.add_im, Complex.div_ofNat_im, Complex.I_im,
      zero_mul, sub_zero, add_zero, zero_add, zero_div, mul_zero, mul_one]
    rw [show π * (1 / 2) = π / 2 by ring, Real.sin_pi_div_two, mul_one]

lemma zetaD_edge_mem_closure (v : ℝ) :
    zetaD ((v : ℂ) + Complex.I / 2) ∈ closure halfDisc \ {Complex.I, -Complex.I} := by
  have hb : ((v : ℂ) + Complex.I / 2) ∈ imStrip := by
    simp [imStrip]; norm_num
  have hsq := zetaD_sq_eq_imStrip hb
  rw [cosh_pi_edge v] at hsq
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hden : (√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.zero_re] at this
    linarith
  have hw_norm : ‖((√2 : ℂ) - ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I) /
      ((√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)]
    have h1 : Complex.normSq ((√2 : ℂ) - ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I) =
        Complex.normSq ((√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I) := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero, zero_add]
      ring
    rw [Complex.norm_def, Complex.norm_def, h1]
  have hnorm : ‖zetaD ((v : ℂ) + Complex.I / 2)‖ = 1 := by
    have h2 : ‖zetaD ((v : ℂ) + Complex.I / 2)‖ ^ 2 = 1 := by
      rw [← norm_pow, hsq, hw_norm]
    nlinarith [norm_nonneg (zetaD ((v : ℂ) + Complex.I / 2))]
  have hre : 0 < (zetaD ((v : ℂ) + Complex.I / 2)).re := by
    obtain ⟨_, hw_slit⟩ := zetaD_w_mem_slitPlane_imStrip hb
    unfold zetaD
    set w := ((√2 : ℂ) - Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2))) /
      ((√2 : ℂ) + Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)))
    have hw_ne : w ≠ 0 := Complex.slitPlane_ne_zero hw_slit
    rw [Complex.cpow_def_of_ne_zero hw_ne, Complex.exp_re]
    have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by
      simp [Complex.log_im]; ring
    rw [him]
    have harg1 : -π < w.arg := Complex.neg_pi_lt_arg w
    have harg2 : w.arg < π := lt_of_le_of_ne (Complex.arg_le_pi w) (Complex.slitPlane_arg_ne_pi hw_slit)
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  refine ⟨mem_closure_halfDisc hnorm.le hre.le, ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · intro h; rw [h] at hre; simp at hre
  · intro h; rw [h] at hre; simp at hre

lemma zetaD_edge_eq_conj_wPt {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    zetaD ((vOf y : ℂ) + Complex.I / 2) = starRingEnd ℂ (wPt y) := by
  have hy1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hy2 : 0 < 1 + y ^ 2 := by positivity
  have hsh : Real.sinh (π * vOf y) = 2 * √2 * y / (1 - y ^ 2) := by
    unfold vOf
    rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.sinh_arsinh]
    have hu : uSlit y - 1 = (2 * √2 * y / (1 - y ^ 2)) ^ 2 := by
      unfold uSlit
      have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith [hs2]
    rw [hu, Real.sqrt_sq (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hy.1.le) hy1.le)]
  have hb : ((vOf y : ℂ) + Complex.I / 2) ∈ imStrip := by simp [imStrip]; norm_num
  have hsq := zetaD_sq_eq_imStrip hb
  rw [cosh_pi_edge (vOf y), hsh] at hsq
  have hw_eq : (((√2 : ℂ) - ((2 * √2 * y / (1 - y ^ 2) : ℝ) : ℂ) * Complex.I) /
      ((√2 : ℂ) + ((2 * √2 * y / (1 - y ^ 2) : ℝ) : ℂ) * Complex.I)) =
      (starRingEnd ℂ (wPt y)) ^ 2 := by
    have h1 : starRingEnd ℂ (wPt y) = (1 - Complex.I * (y : ℂ)) / (1 + Complex.I * (y : ℂ)) := by
      rw [wPt_eq, map_div₀, map_add, map_sub, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [h1]
    have hs2 : (√2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    have h1y : (1 - (y : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hy1.ne'
    have hd1 : (1 + Complex.I * (y : ℂ)) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have hd2 : (√2 : ℂ) + ((2 * √2 * y / (1 - y ^ 2) : ℝ) : ℂ) * Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.zero_re] at this
      linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
    rw [div_pow, div_eq_div_iff hd2 (pow_ne_zero 2 hd1)]
    push_cast
    field_simp
    ring_nf
    rw [show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring, Complex.I_sq]
    ring
  rw [hw_eq] at hsq
  have hpm : zetaD ((vOf y : ℂ) + Complex.I / 2) = starRingEnd ℂ (wPt y) ∨
      zetaD ((vOf y : ℂ) + Complex.I / 2) = -starRingEnd ℂ (wPt y) := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  rcases hpm with h | h
  · exact h
  · exfalso
    have hre1 : 0 < (zetaD ((vOf y : ℂ) + Complex.I / 2)).re := by
      obtain ⟨_, hw_slit⟩ := zetaD_w_mem_slitPlane_imStrip hb
      unfold zetaD
      set w := ((√2 : ℂ) - Complex.cosh ((π : ℂ) * ((vOf y : ℂ) + Complex.I / 2))) /
        ((√2 : ℂ) + Complex.cosh ((π : ℂ) * ((vOf y : ℂ) + Complex.I / 2)))
      rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hw_slit), Complex.exp_re]
      have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by simp [Complex.log_im]; ring
      rw [him]
      have harg1 : -π < w.arg := Complex.neg_pi_lt_arg w
      have harg2 : w.arg < π := lt_of_le_of_ne (Complex.arg_le_pi w) (Complex.slitPlane_arg_ne_pi hw_slit)
      exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
    have hre2 : 0 < (starRingEnd ℂ (wPt y)).re := by
      rw [Complex.conj_re, re_wPt]; exact div_pos hy1 hy2
    rw [h, Complex.neg_re] at hre1
    linarith

/-! ### 2. `etaDelta` and `1 - (1 - δ) ζ_D(b) ∈ slitPlane` on `0 < Im b < 1/2 + η_δ` -/

private lemma etaDelta_arg_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    0 < √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) ∧
      √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) < 1 := by
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2_lt : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hnum : 0 < 2 * δ - δ ^ 2 := by nlinarith
  have hden : 0 < 2 - 2 * δ + δ ^ 2 := by nlinarith
  refine ⟨div_pos (mul_pos hs2 hnum) hden, (div_lt_one hden).mpr ?_⟩
  nlinarith

lemma etaDelta_mem {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    0 < etaDelta δ ∧ etaDelta δ < 1 / 2 := by
  obtain ⟨ha0, ha1⟩ := etaDelta_arg_bounds hδ0 hδ1
  unfold etaDelta
  have hpi := Real.pi_pos
  constructor
  · exact div_pos (Real.arcsin_pos.mpr ha0) hpi
  · rw [div_lt_iff₀ hpi]
    have : Real.arcsin (√2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2)) < Real.arcsin 1 :=
      Real.arcsin_lt_arcsin (by linarith) ha1 le_rfl
    rw [Real.arcsin_one] at this
    linarith

lemma sin_pi_etaDelta {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    Real.sin (π * etaDelta δ) = √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) := by
  obtain ⟨ha0, ha1⟩ := etaDelta_arg_bounds hδ0 hδ1
  unfold etaDelta
  rw [mul_div_cancel₀ _ Real.pi_ne_zero]
  exact Real.sin_arcsin (by linarith) ha1.le

lemma etaDelta_lt_one_sixteenth {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) :
    etaDelta δ < 1 / 16 := by
  have hpi := Real.pi_pos
  have hs2_lt : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have harg_lt : √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) < 1 / 6 := by
    have hden : 0 < 2 - 2 * δ + δ ^ 2 := by nlinarith
    have hnum : 0 < 2 * δ - δ ^ 2 := by nlinarith
    rw [div_lt_iff₀ hden]
    nlinarith [mul_lt_mul_of_pos_right hs2_lt hnum]
  have hsin_gt : (1 : ℝ) / 6 < Real.sin (π / 16) := by
    have h1 : π / 16 - (π / 16) ^ 3 / 6 < Real.sin (π / 16) :=
      Real.sin_gt_sub_cube (by positivity)
    have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
    have hpi4 : π < 3.2 := by linarith [Real.pi_lt_d2]
    nlinarith [sq_nonneg (π / 16)]
  unfold etaDelta
  rw [div_lt_iff₀ hpi]
  obtain ⟨ha0, _⟩ := etaDelta_arg_bounds hδ0 (by linarith)
  have hlt : √2 * (2 * δ - δ ^ 2) / (2 - 2 * δ + δ ^ 2) < Real.sin (π / 16) := lt_trans harg_lt hsin_gt
  have h2 := Real.arcsin_lt_arcsin (by linarith) hlt (Real.sin_le_one _)
  rw [Real.arcsin_sin (by linarith) (by linarith)] at h2
  linarith

/-- For `δ ∈ (0, 1/4)` and `0 < Im b < 1/2 + η_δ`, `1 - (1 - δ) ζ_D(b) ∈ slitPlane`. -/
theorem one_sub_one_sub_delta_zetaD_mem_slitPlane {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb0 : 0 < b.im) (hb1 : b.im < 1 / 2 + etaDelta δ) :
    1 - ((1 - δ : ℝ) : ℂ) * zetaD b ∈ Complex.slitPlane := by
  have heta := etaDelta_mem hδ0 hδ1
  have hb_strip : b ∈ imStrip := ⟨hb0, by linarith [heta.2]⟩
  obtain ⟨hden, hw_slit⟩ := zetaD_w_mem_slitPlane_imStrip hb_strip
  have hpi := Real.pi_pos
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h1s2 : (1 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  rw [Complex.mem_slitPlane_iff]
  by_cases hre0 : b.re = 0
  · left
    have hb_eq : ((b.im : ℂ) * Complex.I) = b := by apply Complex.ext <;> simp [hre0]
    have hc_eq : Complex.cosh ((π : ℂ) * b) = ((Real.cos (π * b.im) : ℝ) : ℂ) := by
      rw [← hb_eq,
        show (π : ℂ) * ((b.im : ℂ) * Complex.I) = ((π * b.im : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.cosh_mul_I, ← Complex.ofReal_cos]
      simp
    have hcos_le : Real.cos (π * b.im) ≤ 1 := Real.cos_le_one _
    have hcos_ge : -1 ≤ Real.cos (π * b.im) := Real.neg_one_le_cos _
    set q : ℝ := (√2 - Real.cos (π * b.im)) / (√2 + Real.cos (π * b.im))
    have hq_pos : 0 < q := div_pos (by linarith) (by linarith)
    have hzeta_eq : zetaD b = ((√q : ℝ) : ℂ) := by
      unfold zetaD
      rw [hc_eq, ← Complex.ofReal_sub, ← Complex.ofReal_add, ← Complex.ofReal_div]
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hq_pos.le,
        ← Real.sqrt_eq_rpow]
    rw [hzeta_eq, ← Complex.ofReal_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_re]
    rw [sub_pos]
    have hcos_eq : Real.cos (π * b.im) = -Real.sin (π * (b.im - 1 / 2)) := by
      rw [show π * (b.im - 1 / 2) = π * b.im - π / 2 by ring, Real.sin_sub_pi_div_two]
      ring
    have hsin_lt : Real.sin (π * (b.im - 1 / 2)) < Real.sin (π * etaDelta δ) := by
      apply Real.strictMonoOn_sin
      · exact ⟨by nlinarith, by nlinarith [heta.2]⟩
      · exact ⟨by nlinarith [heta.1], by nlinarith [heta.2]⟩
      · nlinarith
    rw [sin_pi_etaDelta hδ0 hδ1] at hsin_lt
    have hq_lt : (1 - δ) ^ 2 * q < 1 := by
      have hden_q : 0 < √2 + Real.cos (π * b.im) := by linarith
      have hden_d : 0 < 2 - 2 * δ + δ ^ 2 := by nlinarith
      rw [show q = (√2 - Real.cos (π * b.im)) / (√2 + Real.cos (π * b.im)) from rfl,
        mul_div_assoc', div_lt_one hden_q, hcos_eq]
      rw [lt_div_iff₀ hden_d] at hsin_lt
      nlinarith
    have hsq_lt : ((1 - δ) * √q) ^ 2 < 1 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hq_pos.le, one_pow]; exact hq_lt
    nlinarith [mul_pos (show 0 < 1 - δ by linarith) (Real.sqrt_pos.mpr hq_pos)]
  · right
    have him_c : (Complex.cosh ((π : ℂ) * b)).im ≠ 0 := by
      rw [im_cosh']
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero]
      exact mul_ne_zero (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hre0))
        (Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hb0) (by nlinarith [heta.2])).ne'
    set w := ((√2 : ℂ) - Complex.cosh ((π : ℂ) * b)) / ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b))
    have him_w : w.im ≠ 0 := by
      rw [Complex.div_im]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_sub, zero_add]
      have hn : 0 < Complex.normSq ((√2 : ℂ) + Complex.cosh ((π : ℂ) * b)) := Complex.normSq_pos.mpr hden
      have hnum : (-(Complex.cosh ((π : ℂ) * b)).im) * (√2 + (Complex.cosh ((π : ℂ) * b)).re) -
          (√2 - (Complex.cosh ((π : ℂ) * b)).re) * (Complex.cosh ((π : ℂ) * b)).im =
          -(2 * √2 * (Complex.cosh ((π : ℂ) * b)).im) := by ring
      rw [← sub_div, hnum]
      exact div_ne_zero (by intro h; apply him_c; nlinarith) hn.ne'
    have him_z : (zetaD b).im ≠ 0 := by
      unfold zetaD
      rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hw_slit), Complex.exp_im]
      have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by simp [Complex.log_im]; ring
      rw [him]
      have harg_ne0 : w.arg ≠ 0 := by
        intro h
        have := Complex.arg_eq_zero_iff.mp h
        exact him_w this.2
      have harg1 : -π < w.arg := Complex.neg_pi_lt_arg w
      have harg2 : w.arg < π := lt_of_le_of_ne (Complex.arg_le_pi w) (Complex.slitPlane_arg_ne_pi hw_slit)
      have hsin_ne : Real.sin (w.arg / 2) ≠ 0 := by
        rcases lt_or_gt_of_ne harg_ne0 with hlt | hgt
        · exact (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).ne
        · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
      exact mul_ne_zero (Real.exp_pos _).ne' hsin_ne
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, zero_sub, neg_ne_zero]
    exact mul_ne_zero (by linarith) him_z

/-! ### 3. Explicit holomorphic extension `R4cStrip` of `R4c ∘ ζ_D` to `bandUpper (1/4)` -/

lemma pi_mul_div_sinh_mem_slitPlane {b : ℂ} (hb : b ∈ imStrip) :
    (π : ℂ) * b / Complex.sinh ((π : ℂ) * b) ∈ Complex.slitPlane := by
  have hpi := Real.pi_pos
  have hsin : 0 < Real.sin (π * b.im) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hb.1) (by nlinarith [hb.2])
  have him_sh : 0 < (Complex.sinh ((π : ℂ) * b)).im := by
    rw [im_sinh']
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.mul_im, add_zero]
    exact mul_pos (Real.cosh_pos _) hsin
  have hsh_ne : Complex.sinh ((π : ℂ) * b) ≠ 0 := by
    intro h; rw [h] at him_sh; simp at him_sh
  rw [Complex.mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  obtain ⟨hre, him⟩ := hnot
  set r := ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)).re
  have hreal : (π : ℂ) * b / Complex.sinh ((π : ℂ) * b) = (r : ℂ) := Complex.ext rfl him
  have hmul : (π : ℂ) * b = (r : ℂ) * Complex.sinh ((π : ℂ) * b) := by
    rw [← hreal, div_mul_cancel₀ _ hsh_ne]
  have him_eq := congrArg Complex.im hmul
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at him_eq
  nlinarith [mul_pos hpi hb.1]

private lemma bandUpper_mem_imStrip {b : ℂ} (hb : b ∈ bandUpper (1 / 4)) : b ∈ imStrip :=
  ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 4 from hb)).1],
    by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 4 from hb)).2]⟩

private lemma arg_mem_Ioo_of_re_pos {z : ℂ} (hre : 0 < z.re) : -π / 2 < z.arg ∧ z.arg < π / 2 := by
  have hne : z ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hcos : 0 < Real.cos z.arg := by
    rw [Complex.cos_arg hne]; exact div_pos hre (norm_pos_iff.mpr hne)
  have hle : z.arg ≤ π := Complex.arg_le_pi z
  have hgt : -π < z.arg := Complex.neg_pi_lt_arg z
  constructor
  · by_contra h; push Not at h
    have : Real.cos z.arg ≤ 0 := by
      have h1 : Real.cos z.arg = -Real.cos (z.arg + π) := by rw [Real.cos_add_pi]; ring
      rw [h1, neg_nonpos]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    linarith
  · by_contra h; push Not at h
    have : Real.cos z.arg ≤ 0 := by
      have h1 : Real.cos z.arg = -Real.cos (z.arg - π) := by rw [Real.cos_sub_pi]; ring
      rw [h1, neg_nonpos]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    linarith

lemma r4c_alg_factor_mem_slitPlane {b : ℂ} (hb : b ∈ bandUpper (1 / 4)) :
    (1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2) ∈ Complex.slitPlane := by
  have hb_strip : b ∈ imStrip := bandUpper_mem_imStrip hb
  obtain ⟨hden, _⟩ := zetaD_w_mem_slitPlane_imStrip hb_strip
  have h1sq : 1 + zetaD b ^ 2 ≠ 0 := one_add_zetaD_sq_ne_zero_imStrip hb_strip
  have hpi := Real.pi_pos
  have hs2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2_ne : (√2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs2.ne'
  set c := Complex.cosh ((π : ℂ) * b) with hcdef
  have hden' : (√2 : ℂ) + c ≠ 0 := hden
  have hform : (1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2) =
      (c + zetaD b * ((√2 : ℂ) + c)) / (√2 : ℂ) := by
    have h1 : 1 + zetaD b ^ 2 = 2 * (√2 : ℂ) / ((√2 : ℂ) + c) := one_add_zetaD_sq_eq hb_strip
    have h2 : 1 - zetaD b ^ 2 = 2 * c / ((√2 : ℂ) + c) := by
      rw [zetaD_sq_eq_imStrip hb_strip, ← hcdef]; field_simp; ring
    rw [show 1 + 2 * zetaD b - zetaD b ^ 2 = (1 - zetaD b ^ 2) + 2 * zetaD b by ring, h1, h2]
    field_simp
  rw [hform, Complex.mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  obtain ⟨hre, him⟩ := hnot
  set t : ℝ := -((c + zetaD b * ((√2 : ℂ) + c)) / (√2 : ℂ)).re
  have ht0 : 0 ≤ t := by simp only [t]; linarith
  have heq : (c + zetaD b * ((√2 : ℂ) + c)) / (√2 : ℂ) = ((-t : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [t]
    · simpa using him
  have hmul : zetaD b * ((√2 : ℂ) + c) = -(c + ((t * √2 : ℝ) : ℂ)) := by
    have h1 : c + zetaD b * ((√2 : ℂ) + c) = ((-t : ℝ) : ℂ) * (√2 : ℂ) := by
      rw [← heq, div_mul_cancel₀ _ hs2_ne]
    push_cast at h1 ⊢
    linear_combination h1
  have hsq : zetaD b ^ 2 * ((√2 : ℂ) + c) ^ 2 = (c + ((t * √2 : ℝ) : ℂ)) ^ 2 := by
    have h1 := congrArg (· ^ 2) hmul
    rw [mul_pow, neg_sq] at h1
    exact h1
  have hlhs : zetaD b ^ 2 * ((√2 : ℂ) + c) ^ 2 = (2 : ℂ) - c ^ 2 := by
    rw [zetaD_sq_eq_imStrip hb_strip, ← hcdef]
    have hs2sq : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    linear_combination hs2sq
  rw [hlhs] at hsq
  have hpoly : c ^ 2 + ((t * √2 : ℝ) : ℂ) * c + (((t ^ 2 - 1 : ℝ)) : ℂ) = 0 := by
    have hs2sq : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    push_cast at hsq ⊢
    linear_combination -(1 / 2 : ℂ) * hsq - (t : ℂ) ^ 2 * (1 / 2 : ℂ) * hs2sq
  have hpoly_im := congrArg Complex.im hpoly
  have hpoly_re := congrArg Complex.re hpoly
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    sq, Complex.zero_im, Complex.add_re, Complex.mul_re, sub_zero, Complex.zero_re] at hpoly_im hpoly_re
  by_cases him0 : c.im = 0
  · -- c is real, so b.re = 0
    have hsin : 0 < Real.sin (π * b.im) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi hb_strip.1) (by nlinarith [hb_strip.2])
    have hbre0 : b.re = 0 := by
      rw [hcdef, im_cosh'] at him0
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero] at him0
      have hsh0 : Real.sinh (π * b.re) = 0 := (mul_eq_zero.mp him0).resolve_right hsin.ne'
      exact (mul_eq_zero.mp (Real.sinh_eq_zero.mp hsh0)).resolve_left Real.pi_ne_zero
    have hb_eq : ((b.im : ℂ) * Complex.I) = b := by apply Complex.ext <;> simp [hbre0]
    have hc_eq : c = ((Real.cos (π * b.im) : ℝ) : ℂ) := by
      rw [hcdef, ← hb_eq,
        show (π : ℂ) * ((b.im : ℂ) * Complex.I) = ((π * b.im : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.cosh_mul_I, ← Complex.ofReal_cos]
      simp
    have hcos_gt : -1 < Real.cos (π * b.im) := by
      have : Real.cos (π * b.im) > Real.cos π := by
        apply Real.strictAntiOn_cos ⟨(mul_pos hpi hb_strip.1).le, by nlinarith [hb_strip.2]⟩
          ⟨hpi.le, le_rfl⟩
        nlinarith [hb_strip.2]
      rw [Real.cos_pi] at this; linarith
    have hcos_lt : Real.cos (π * b.im) < 1 := by
      rw [← Real.cos_zero]
      exact Real.strictAntiOn_cos ⟨le_rfl, hpi.le⟩ ⟨(mul_pos hpi hb_strip.1).le, by nlinarith [hb_strip.2]⟩
        (mul_pos hpi hb_strip.1)
    have h1s2 : (1 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    have hq_pos : 0 < (√2 - Real.cos (π * b.im)) / (√2 + Real.cos (π * b.im)) :=
      div_pos (by linarith) (by linarith)
    have hzeta_eq : zetaD b = ((√((√2 - Real.cos (π * b.im)) / (√2 + Real.cos (π * b.im))) : ℝ) : ℂ) := by
      unfold zetaD
      rw [← hcdef, hc_eq, ← Complex.ofReal_sub, ← Complex.ofReal_add, ← Complex.ofReal_div]
      rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num, ← Complex.ofReal_cpow hq_pos.le,
        ← Real.sqrt_eq_rpow]
    have hre_pos : 0 < (c + zetaD b * ((√2 : ℂ) + c)).re := by
      rw [hc_eq, hzeta_eq]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have hprod : √((√2 - Real.cos (π * b.im)) / (√2 + Real.cos (π * b.im))) * (√2 + Real.cos (π * b.im)) =
          √(2 - Real.cos (π * b.im) ^ 2) := by
        have hpos1 : 0 < √2 + Real.cos (π * b.im) := by linarith
        have hpos2 : 0 < √2 - Real.cos (π * b.im) := by linarith
        have hsq1 : √(√2 + Real.cos (π * b.im)) ^ 2 = √2 + Real.cos (π * b.im) := Real.sq_sqrt hpos1.le
        have hne1 : √(√2 + Real.cos (π * b.im)) ≠ 0 := (Real.sqrt_pos.mpr hpos1).ne'
        rw [Real.sqrt_div hpos2.le]
        have hstep : √(√2 - Real.cos (π * b.im)) / √(√2 + Real.cos (π * b.im)) * (√2 + Real.cos (π * b.im)) =
            √(√2 - Real.cos (π * b.im)) * √(√2 + Real.cos (π * b.im)) := by
          field_simp; rw [hsq1]
        rw [hstep, ← Real.sqrt_mul hpos2.le]
        congr 1; nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hprod]
      have : 1 < √(2 - Real.cos (π * b.im) ^ 2) := by
        rw [Real.lt_sqrt (by norm_num)]; nlinarith
      linarith
    have hre_neg : (c + zetaD b * ((√2 : ℂ) + c)).re ≤ 0 := by
      have h1 : (c + zetaD b * ((√2 : ℂ) + c)).re = -t * √2 := by
        have h2 := congrArg Complex.re (show c + zetaD b * ((√2 : ℂ) + c) = ((-t : ℝ) : ℂ) * (√2 : ℂ) by
          rw [← heq, div_mul_cancel₀ _ hs2_ne])
        simpa using h2
      nlinarith
    linarith
  · -- c.im ≠ 0: then 2 c.re + t √2 = 0, so c.re^2 - c.im^2 = 1, contradicting |b.im - 1/2| < 1/4!
    have hcre : 2 * c.re + t * √2 = 0 := by
      have : c.im * (2 * c.re + t * √2) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left him0
    have hdiff_eq : c.re ^ 2 - c.im ^ 2 = 1 := by
      have hs2sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have ht2 : (t * √2) ^ 2 = 2 * t ^ 2 := by rw [mul_pow, hs2sq]; ring
      have hsq_cre : (t * √2) ^ 2 = 4 * c.re ^ 2 := by linear_combination (t * √2 - 2 * c.re) * hcre
      have ht_eq : t ^ 2 = 2 * c.re ^ 2 := by linarith [ht2, hsq_cre]
      have hcr_eq : t * √2 * c.re = -2 * c.re ^ 2 := by linear_combination c.re * hcre
      linarith [hpoly_re, ht_eq, hcr_eq]
    have hcre_val : c.re = Real.cosh (π * b.re) * Real.cos (π * b.im) := by
      rw [hcdef, re_cosh']; simp
    have hcim_val : c.im = Real.sinh (π * b.re) * Real.sin (π * b.im) := by
      rw [hcdef, im_cosh']; simp
    have hdiff_lt : c.re ^ 2 - c.im ^ 2 < 1 := by
      rw [hcre_val, hcim_val]
      have hcs := Real.cosh_sq (π * b.re)
      have hsc := Real.sin_sq_add_cos_sq (π * b.im)
      have hbim := abs_lt.mp (show |b.im - 1 / 2| < 1 / 4 from hb)
      have hcos2 : Real.cos (2 * (π * b.im)) < 0 := by
        have h1 : π / 2 < 2 * (π * b.im) := by nlinarith [hbim.1]
        have h2 : 2 * (π * b.im) < 3 * π / 2 := by nlinarith [hbim.2]
        rw [show 2 * (π * b.im) = (2 * (π * b.im) - π) + π by ring, Real.cos_add_pi, neg_lt_zero]
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
      have hcos2_eq : Real.cos (2 * (π * b.im)) = 2 * Real.cos (π * b.im) ^ 2 - 1 :=
        Real.cos_two_mul _
      have hsin_lt1 : Real.sin (π * b.im) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (Real.cos (π * b.im))]
      have hch_ge1 : 1 ≤ Real.cosh (π * b.re) ^ 2 := by nlinarith [Real.one_le_cosh (π * b.re)]
      have halg : (Real.cosh (π * b.re) * Real.cos (π * b.im)) ^ 2 -
          (Real.sinh (π * b.re) * Real.sin (π * b.im)) ^ 2 =
          Real.cosh (π * b.re) ^ 2 * Real.cos (2 * (π * b.im)) + Real.sin (π * b.im) ^ 2 := by
        have hsh2 : Real.sinh (π * b.re) ^ 2 = Real.cosh (π * b.re) ^ 2 - 1 := by linarith [hcs]
        have hcs2 : Real.cos (π * b.im) ^ 2 = 1 - Real.sin (π * b.im) ^ 2 := by linarith [hsc]
        rw [hcos2_eq, mul_pow, mul_pow, hsh2, hcs2]; ring
      rw [halg]
      have hprod_neg : Real.cosh (π * b.re) ^ 2 * Real.cos (2 * (π * b.im)) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hcos2
      linarith
    linarith

/-- Explicit holomorphic zero-free extension of `R4c ∘ ζ_D` to `bandUpper (1/4)`. -/
noncomputable def R4cStrip (b : ℂ) : ℂ :=
  ((1 + 2 * zetaD b - zetaD b ^ 2) / (1 + zetaD b ^ 2)) ^ (1 / 2 : ℂ) *
    ((π : ℂ) * b / Complex.sinh ((π : ℂ) * b)) ^ (1 / 2 : ℂ) / (kap : ℂ)

lemma differentiableOn_R4cStrip : DifferentiableOn ℂ R4cStrip (bandUpper (1 / 4)) := by
  intro b hb
  have hb_strip : b ∈ imStrip := bandUpper_mem_imStrip hb
  have hzeta : DifferentiableAt ℂ zetaD b :=
    differentiableOn_zetaD_imStrip.differentiableAt (isOpen_imStrip.mem_nhds hb_strip)
  have h1sq : 1 + zetaD b ^ 2 ≠ 0 := one_add_zetaD_sq_ne_zero_imStrip hb_strip
  have hf1 : DifferentiableAt ℂ (fun z => (1 + 2 * zetaD z - zetaD z ^ 2) / (1 + zetaD z ^ 2)) b :=
    (((differentiableAt_const _).add ((differentiableAt_const _).mul hzeta)).sub (hzeta.pow 2)).div
      ((differentiableAt_const _).add (hzeta.pow 2)) h1sq
  have hsh_ne : Complex.sinh ((π : ℂ) * b) ≠ 0 := by
    have h := pi_mul_div_sinh_mem_slitPlane hb_strip
    intro h0; rw [h0, div_zero] at h; exact Complex.slitPlane_ne_zero h rfl
  have hf2 : DifferentiableAt ℂ (fun z => (π : ℂ) * z / Complex.sinh ((π : ℂ) * z)) b :=
    ((differentiableAt_const _).mul differentiableAt_id).div
      (Complex.differentiableAt_sinh.comp b ((differentiableAt_const _).mul differentiableAt_id)) hsh_ne
  unfold R4cStrip
  exact (((hf1.cpow_const (r4c_alg_factor_mem_slitPlane hb)).mul
    (hf2.cpow_const (pi_mul_div_sinh_mem_slitPlane hb_strip))).div_const _).differentiableWithinAt

lemma R4cStrip_ne_zero {b : ℂ} (hb : b ∈ bandUpper (1 / 4)) : R4cStrip b ≠ 0 := by
  have hb_strip : b ∈ imStrip := bandUpper_mem_imStrip hb
  unfold R4cStrip
  have hk : ((kap : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr kap_pos.ne'
  refine div_ne_zero (mul_ne_zero ?_ ?_) hk
  · rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (r4c_alg_factor_mem_slitPlane hb))]
    exact Complex.exp_ne_zero _
  · rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (pi_mul_div_sinh_mem_slitPlane hb_strip))]
    exact Complex.exp_ne_zero _

private lemma R4cStrip_eq_R4c_imag {y : ℝ} (hy0 : 1 / 4 < y) (hy1 : y < 1 / 2) :
    R4cStrip ((y : ℂ) * Complex.I) = R4c (zetaD ((y : ℂ) * Complex.I)) := by
  have hpi := Real.pi_pos
  have hb : ((y : ℂ) * Complex.I) ∈ bandUpper (1 / 4) := by
    change |((y : ℂ) * Complex.I).im - 1 / 2| < 1 / 4
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    rw [abs_lt]; constructor <;> linarith
  have hb_strip : ((y : ℂ) * Complex.I) ∈ imStrip := by
    simp [imStrip]; exact ⟨by linarith, by linarith⟩
  have hcos_pos : 0 < Real.cos (π * y) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
  have hcos_lt : Real.cos (π * y) < 1 := by
    rw [← Real.cos_zero]
    exact Real.strictAntiOn_cos ⟨le_rfl, hpi.le⟩ ⟨by positivity, by nlinarith⟩ (by positivity)
  have hsin_pos : 0 < Real.sin (π * y) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hsin_lt : Real.sin (π * y) < 1 := by
    rw [← Real.sin_pi_div_two]
    exact Real.strictMonoOn_sin ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, le_rfl⟩ (by nlinarith)
  have hs2 : (1 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  set r : ℝ := √((√2 - Real.cos (π * y)) / (√2 + Real.cos (π * y))) with hrdef
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
  have hr_lt : r < 1 := by
    rw [hrdef, Real.sqrt_lt' one_pos, one_pow, div_lt_one (by linarith)]; linarith
  have hzeta_eq : zetaD ((y : ℂ) * Complex.I) = (r : ℂ) := by
    unfold zetaD
    have hc : Complex.cosh ((π : ℂ) * ((y : ℂ) * Complex.I)) = ((Real.cos (π * y) : ℝ) : ℂ) := by
      rw [show (π : ℂ) * ((y : ℂ) * Complex.I) = ((π * y : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.cosh_mul_I, ← Complex.ofReal_cos]
    rw [hc, ← Complex.ofReal_sub, ← Complex.ofReal_add, ← Complex.ofReal_div,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (div_pos (by linarith) (by linarith)).le, ← Real.sqrt_eq_rpow]
  -- Both sides are positive reals and have the same 4th power!
  have hR4_pos := R4c_real_pos ⟨hr_pos, hr_lt⟩
  have hR4_real : R4c (r : ℂ) = (((R4c (r : ℂ)).re : ℝ) : ℂ) := Complex.ext rfl hR4_pos.2
  have ha_pos : 0 < (1 + 2 * r - r ^ 2) / (1 + r ^ 2) := div_pos (by nlinarith) (by positivity)
  have hb_pos : 0 < π * y / Real.sin (π * y) := div_pos (by positivity) hsin_pos
  have hsh : (π : ℂ) * ((y : ℂ) * Complex.I) / Complex.sinh ((π : ℂ) * ((y : ℂ) * Complex.I)) =
      ((π * y / Real.sin (π * y) : ℝ) : ℂ) := by
    rw [show (π : ℂ) * ((y : ℂ) * Complex.I) = ((π * y : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.sinh_mul_I, ← Complex.ofReal_sin]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hs : ((Real.sin (π * y) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsin_pos.ne'
    push_cast; field_simp
  have hStrip_eq : R4cStrip ((y : ℂ) * Complex.I) =
      ((√((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) * √(π * y / Real.sin (π * y)) / kap : ℝ) : ℂ) := by
    unfold R4cStrip
    rw [hzeta_eq, hsh]
    rw [show (1 + 2 * (r : ℂ) - (r : ℂ) ^ 2) / (1 + (r : ℂ) ^ 2) =
        (((1 + 2 * r - r ^ 2) / (1 + r ^ 2) : ℝ) : ℂ) by push_cast; ring]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow ha_pos.le, ← Complex.ofReal_cpow hb_pos.le,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    push_cast; ring
  rw [hzeta_eq, hStrip_eq]
  -- Compare 4th powers of positive reals:
  have hpow4 : (√((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) * √(π * y / Real.sin (π * y)) / kap) ^ 4 =
      (R4c (r : ℂ)).re ^ 4 := by
    have hH3 : (R4c (r : ℂ) ^ 4).re = (H3 (r : ℂ)).re := by rw [R4c_pow_four]
    have hR4_pow : (R4c (r : ℂ) ^ 4).re = (R4c (r : ℂ)).re ^ 4 := by
      conv_lhs => rw [hR4_real, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [← hR4_pow, hH3]
    -- Compute H3 (r : ℂ) explicitly:
    have huC : uC (r : ℂ) = -(((Real.sin (π * y) ^ 2 : ℝ)) : ℂ) := by
      unfold uC
      have hr2 : r ^ 2 = (√2 - Real.cos (π * y)) / (√2 + Real.cos (π * y)) :=
        Real.sq_sqrt (div_pos (by linarith) (by linarith)).le
      have h1 : ((1 - 6 * r ^ 2 + r ^ 4) / (1 + r ^ 2) ^ 2 : ℝ) = -Real.sin (π * y) ^ 2 := by
        have hs2sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hden : √2 + Real.cos (π * y) ≠ 0 := by linarith
        have h1r : 1 + r ^ 2 ≠ 0 := by positivity
        rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2]
        field_simp
        nlinarith [hs2sq, Real.sin_sq_add_cos_sq (π * y)]
      exact_mod_cast h1
    have hsInt_eq : sInt (uC (r : ℂ)) = ((π * y / Real.sin (π * y) : ℝ) : ℂ) := by
      rw [huC, sInt_neg_real (by positivity) (by nlinarith), Real.sqrt_sq hsin_pos.le,
        Real.arcsin_sin (by nlinarith) (by nlinarith)]
    have hsin_sInv : 1 + Complex.sin ((π : ℂ) * sInv (r : ℂ)) =
        ((((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) ^ 2 : ℝ) : ℂ) := by
      have htan : Real.tan (Real.arctan r) = r := Real.tan_arctan r
      have h1 : Complex.sin ((π : ℂ) * sInv (r : ℂ)) = ((Real.sin (4 * Real.arctan r) : ℝ) : ℂ) := by
        unfold sInv
        have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        rw [← mul_assoc, mul_div_cancel₀ _ hπ, ← Complex.ofReal_arctan,
          show (4 : ℂ) * ((Real.arctan r : ℝ) : ℂ) = ((4 * Real.arctan r : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_sin]
      rw [h1, ← Complex.ofReal_one, ← Complex.ofReal_add]
      congr 1
      have hcos_ne : Real.cos (Real.arctan r) ≠ 0 := (Real.cos_arctan_pos r).ne'
      have hsin4 : Real.sin (4 * Real.arctan r) = 4 * r * (1 - r ^ 2) / (1 + r ^ 2) ^ 2 := by
        have h2a : Real.sin (2 * Real.arctan r) = 2 * Real.sin (Real.arctan r) * Real.cos (Real.arctan r) :=
          Real.sin_two_mul _
        have hc2a : Real.cos (2 * Real.arctan r) = Real.cos (Real.arctan r) ^ 2 - Real.sin (Real.arctan r) ^ 2 :=
          Real.cos_two_mul' _
        have h4a : Real.sin (4 * Real.arctan r) = 2 * Real.sin (2 * Real.arctan r) * Real.cos (2 * Real.arctan r) := by
          rw [show 4 * Real.arctan r = 2 * (2 * Real.arctan r) by ring, Real.sin_two_mul]
        rw [h4a, h2a, hc2a, Real.sin_arctan, Real.cos_arctan]
        have hsq : √(1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
        have hsq4 : √(1 + r ^ 2) ^ 4 = (1 + r ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
        have hsq_ne : √(1 + r ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
        field_simp
        rw [hsq4]; ring
      rw [hsin4]
      field_simp
      ring
    have hH3_val : (H3 (r : ℂ)).re =
        ((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) ^ 2 * (π * y / Real.sin (π * y)) ^ 2 / (π ^ 2 * xiStar ^ 2) := by
      unfold H3
      rw [hsin_sInv, hsInt_eq]
      rw [show ((((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) ^ 2 : ℝ) : ℂ) *
          ((π * y / Real.sin (π * y) : ℝ) : ℂ) ^ 2 / ((π : ℂ) ^ 2 * (xiStar : ℂ) ^ 2) =
          ((((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) ^ 2 * (π * y / Real.sin (π * y)) ^ 2 /
            (π ^ 2 * xiStar ^ 2) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    rw [hH3_val, div_pow, mul_pow, kap_pow4]
    have h1 : √((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) ^ 4 = ((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt ha_pos.le]
    have h2 : √(π * y / Real.sin (π * y)) ^ 4 = (π * y / Real.sin (π * y)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hb_pos.le]
    rw [h1, h2]
  have hre_eq : √((1 + 2 * r - r ^ 2) / (1 + r ^ 2)) * √(π * y / Real.sin (π * y)) / kap = (R4c (r : ℂ)).re :=
    (pow_left_inj₀ (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) kap_pos.le)
      hR4_pos.1.le (by norm_num : 4 ≠ 0)).mp hpow4
  rw [hre_eq, ← hR4_real]

/-- `R4cStrip` agrees with `R4c ∘ ζ_D` on `1/4 < Im b < 1/2`. -/
theorem R4cStrip_eq_R4c {b : ℂ} (hb : b ∈ bandUpper (1 / 4)) (hb_lt : b.im < 1 / 2) :
    R4cStrip b = R4c (zetaD b) := by
  set U : Set ℂ := {z : ℂ | 1 / 4 < z.im ∧ z.im < 1 / 2}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const)
  have hU_conn : IsPreconnected U := by
    have hconv : Convex ℝ U := by
      intro x hx y hy t1 t2 ht1 ht2 htab
      change 1 / 4 < (t1 • x + t2 • y).im ∧ (t1 • x + t2 • y).im < 1 / 2
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      rcases eq_or_lt_of_le ht1 with rfl | ht1'
      · exact ⟨by nlinarith [hy.1, htab], by nlinarith [hy.2, htab]⟩
      · exact ⟨by nlinarith [hx.1, hy.1, ht1', ht2, htab], by nlinarith [hx.2, hy.2, ht1', ht2, htab]⟩
    exact hconv.isPreconnected
  have hU_sub : U ⊆ bandUpper (1 / 4) := fun z hz => by
    change |z.im - 1 / 2| < 1 / 4; rw [abs_lt]; constructor <;> linarith [hz.1, hz.2]
  have hU_strip : U ⊆ imStrip := fun z hz => ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have han1 : AnalyticOnNhd ℂ R4cStrip U := (differentiableOn_R4cStrip.mono hU_sub).analyticOnNhd hU_open
  have han2 : AnalyticOnNhd ℂ (fun z => R4c (zetaD z)) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hU_open
    intro z hz
    have hzm : zetaD z ∈ halfDisc := zetaD_mem_halfDisc (by linarith [hz.1]) hz.2
    exact ((differentiableOn_R4c.differentiableAt (isOpen_halfDisc.mem_nhds hzm)).comp z
      (differentiableOn_zetaD_imStrip.differentiableAt (isOpen_imStrip.mem_nhds (hU_strip hz)))).differentiableWithinAt
  set z₀ : ℂ := ((3 / 8 : ℝ) : ℂ) * Complex.I
  have hz₀ : z₀ ∈ U := by
    change 1 / 4 < z₀.im ∧ z₀.im < 1 / 2
    simp only [z₀, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    norm_num
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, R4cStrip z = R4c (zetaD z) := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [mem_nhdsWithin] at hs
    obtain ⟨t, ht_open, hz₀t, hts⟩ := hs
    obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.mp ht_open z₀ hz₀t
    set δ := min (r / 2) (1 / 16)
    have hδ0 : 0 < δ := lt_min (half_pos hr0) (by norm_num)
    set w : ℂ := ((3 / 8 + δ : ℝ) : ℂ) * Complex.I
    have hw_ne : w ≠ z₀ := by
      intro h; have := congrArg Complex.im h; simp [w, z₀] at this; linarith
    have hw_ball : w ∈ ball z₀ r := by
      rw [mem_ball, dist_eq_norm, show w - z₀ = ((δ : ℝ) : ℂ) * Complex.I by simp [w, z₀]; ring,
        norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hδ0]
      exact (min_le_left _ _).trans_lt (half_lt_self hr0)
    refine ⟨w, hts ⟨hball hw_ball, hw_ne⟩, ?_⟩
    exact R4cStrip_eq_R4c_imag (by linarith [min_le_right (r / 2) (1 / 16)])
      (by linarith [min_le_right (r / 2) (1 / 16)])
  have heq := han1.eqOn_of_preconnected_of_frequently_eq han2 hU_conn hz₀ hfreq
  exact heq ⟨by linarith [(abs_lt.mp (show |b.im - 1 / 2| < 1 / 4 from hb)).1], hb_lt⟩

lemma norm_R4cStrip_edge (v : ℝ) :
    ‖R4cStrip ((v : ℂ) + Complex.I / 2)‖ = (v ^ 2 + 1 / 4) ^ (1 / 4 : ℝ) / √xiStar := by
  have hb : ((v : ℂ) + Complex.I / 2) ∈ bandUpper (1 / 4) := by
    change |((v : ℂ) + Complex.I / 2).im - 1 / 2| < 1 / 4; simp
  have hb_strip : ((v : ℂ) + Complex.I / 2) ∈ imStrip := by simp [imStrip]; norm_num
  have hpi := Real.pi_pos
  have hch : 0 < Real.cosh (π * v) := Real.cosh_pos _
  -- Factor 1 norm: |(1 + 2 z - z^2)/(1 + z^2)| = cosh(π v)
  have hn1 : ‖(1 + 2 * zetaD ((v : ℂ) + Complex.I / 2) - zetaD ((v : ℂ) + Complex.I / 2) ^ 2) /
      (1 + zetaD ((v : ℂ) + Complex.I / 2) ^ 2)‖ = Real.cosh (π * v) := by
    set c := Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)) with hcdef
    have hsq : zetaD ((v : ℂ) + Complex.I / 2) ^ 2 = ((√2 : ℂ) - c) / ((√2 : ℂ) + c) :=
      zetaD_sq_eq_imStrip hb_strip
    have h1 : 1 + zetaD ((v : ℂ) + Complex.I / 2) ^ 2 = 2 * (√2 : ℂ) / ((√2 : ℂ) + c) :=
      one_add_zetaD_sq_eq hb_strip
    have hden : (√2 : ℂ) + c ≠ 0 := (zetaD_w_mem_slitPlane_imStrip hb_strip).1
    have hs2_ne : (√2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    have h2 : 1 - zetaD ((v : ℂ) + Complex.I / 2) ^ 2 = 2 * c / ((√2 : ℂ) + c) := by
      rw [hsq]; field_simp; ring
    have hform : (1 + 2 * zetaD ((v : ℂ) + Complex.I / 2) - zetaD ((v : ℂ) + Complex.I / 2) ^ 2) /
        (1 + zetaD ((v : ℂ) + Complex.I / 2) ^ 2) =
        (c + zetaD ((v : ℂ) + Complex.I / 2) * ((√2 : ℂ) + c)) / (√2 : ℂ) := by
      rw [show 1 + 2 * zetaD ((v : ℂ) + Complex.I / 2) - zetaD ((v : ℂ) + Complex.I / 2) ^ 2 =
          (1 - zetaD ((v : ℂ) + Complex.I / 2) ^ 2) + 2 * zetaD ((v : ℂ) + Complex.I / 2) by ring, h1, h2]
      field_simp
    have hc_val : c = ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I := cosh_pi_edge v
    rw [hform, hc_val]
    -- z * (√2 + i sinh(π v)) has square (√2 - i sinh)(√2 + i sinh) = 2 + sinh^2 = 1 + cosh^2 > 0, and Re > 0!
    set A : ℂ := zetaD ((v : ℂ) + Complex.I / 2) * ((√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I)
    have hA_sq : A ^ 2 = ((1 + Real.cosh (π * v) ^ 2 : ℝ) : ℂ) := by
      have hs2sq : (√2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have hcs' : ((Real.cosh (π * v) : ℝ) : ℂ) ^ 2 = ((Real.sinh (π * v) : ℝ) : ℂ) ^ 2 + 1 := by
        exact_mod_cast Real.cosh_sq (π * v)
      have hden' : (√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I ≠ 0 := by
        rwa [← hc_val]
      rw [show A ^ 2 = zetaD ((v : ℂ) + Complex.I / 2) ^ 2 *
          ((√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I) ^ 2 by ring, hsq, hc_val]
      field_simp
      rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow, hcs',
        show (((√2 : ℂ) - ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I) *
          ((√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I)) =
          (√2 : ℂ) ^ 2 - ((Real.sinh (π * v) : ℝ) : ℂ) ^ 2 * Complex.I ^ 2 by ring,
        hs2sq, Complex.I_sq]
      ring
    have hA_pm : A = ((√(1 + Real.cosh (π * v) ^ 2) : ℝ) : ℂ) ∨
        A = -((√(1 + Real.cosh (π * v) ^ 2) : ℝ) : ℂ) := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      rw [hA_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    have hA_eq : A = ((√(1 + Real.cosh (π * v) ^ 2) : ℝ) : ℂ) := by
      rcases hA_pm with h | h
      · exact h
      · exfalso
        have hA_re : 0 < A.re := by
          have h1 : A.re = (zetaD ((v : ℂ) + Complex.I / 2)).re * √2 -
              (zetaD ((v : ℂ) + Complex.I / 2)).im * Real.sinh (π * v) := by
            simp only [A, Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im,
              Complex.mul_im, zero_add]
          rw [h1]
          have hz_re : 0 < (zetaD ((v : ℂ) + Complex.I / 2)).re := by
            obtain ⟨_, hw_slit⟩ := zetaD_w_mem_slitPlane_imStrip hb_strip
            unfold zetaD
            set w := ((√2 : ℂ) - Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2))) /
              ((√2 : ℂ) + Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)))
            rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hw_slit), Complex.exp_re]
            have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by simp [Complex.log_im]; ring
            rw [him]
            exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo
              ⟨by linarith [Complex.neg_pi_lt_arg w],
                by linarith [lt_of_le_of_ne (Complex.arg_le_pi w) (Complex.slitPlane_arg_ne_pi hw_slit)]⟩)
          have hprod_nonpos : (zetaD ((v : ℂ) + Complex.I / 2)).im * Real.sinh (π * v) ≤ 0 := by
            obtain ⟨_, hw_slit⟩ := zetaD_w_mem_slitPlane_imStrip hb_strip
            set w := ((√2 : ℂ) - Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2))) /
              ((√2 : ℂ) + Complex.cosh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)))
            have him_z : (zetaD ((v : ℂ) + Complex.I / 2)).im =
                Real.exp ((Complex.log w * (1 / 2 : ℂ)).re) * Real.sin (w.arg / 2) := by
              unfold zetaD
              rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero hw_slit), Complex.exp_im]
              have him : (Complex.log w * (1 / 2 : ℂ)).im = w.arg / 2 := by simp [Complex.log_im]; ring
              rw [him]
            have him_w : w.im = -(2 * √2 * Real.sinh (π * v)) /
                Complex.normSq ((√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I) := by
              simp only [w, cosh_pi_edge v, Complex.div_im, Complex.sub_re, Complex.sub_im,
                Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
                Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
                sub_zero, add_zero, zero_sub, zero_add]
              ring
            rw [him_z]
            have hden_pos : 0 < Complex.normSq ((√2 : ℂ) + ((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I) := by
              rw [Complex.normSq_pos]; rwa [← hc_val]
            rcases lt_trichotomy (Real.sinh (π * v)) 0 with hs_neg | hs_zero | hs_pos
            · have hw_im_pos : 0 < w.im := by rw [him_w]; exact div_pos (by nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]) hden_pos
              have hsin_w : 0 < Real.sin w.arg := by
                rw [Complex.sin_arg]; exact div_pos hw_im_pos (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hw_slit))
              have harg_pos : 0 < w.arg := by
                by_contra hle; push Not at hle
                have : Real.sin w.arg ≤ 0 := by
                  rcases eq_or_lt_of_le hle with h0 | hlt
                  · rw [h0, Real.sin_zero]
                  · exact (Real.sin_neg_of_neg_of_neg_pi_lt hlt (Complex.neg_pi_lt_arg w)).le
                linarith
              have harg_lt : w.arg < π := lt_of_le_of_ne (Complex.arg_le_pi w) (Complex.slitPlane_arg_ne_pi hw_slit)
              have hsin_pos : 0 < Real.sin (w.arg / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
              nlinarith [mul_pos (Real.exp_pos (Complex.log w * (1 / 2 : ℂ)).re) hsin_pos]
            · rw [hs_zero, mul_zero]
            · have hw_im_neg : w.im < 0 := by rw [him_w]; exact div_neg_of_neg_of_pos (by nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]) hden_pos
              have harg_neg : w.arg < 0 := Complex.arg_neg_iff.mpr hw_im_neg
              have harg_gt : -π < w.arg := Complex.neg_pi_lt_arg w
              have hsin_neg : Real.sin (w.arg / 2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
              nlinarith [mul_neg_of_pos_of_neg (Real.exp_pos (Complex.log w * (1 / 2 : ℂ)).re) hsin_neg]
          nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
        rw [h] at hA_re
        simp only [Complex.neg_re, Complex.ofReal_re] at hA_re
        linarith [Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + Real.cosh (π * v) ^ 2)]
    rw [hA_eq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by norm_num))]
    have hnum_norm : ‖((Real.sinh (π * v) : ℝ) : ℂ) * Complex.I + ((√(1 + Real.cosh (π * v) ^ 2) : ℝ) : ℂ)‖ =
        √2 * Real.cosh (π * v) := by
      rw [add_comm, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
      have hcs := Real.cosh_sq (π * v)
      rw [show 1 + Real.cosh (π * v) ^ 2 + Real.sinh (π * v) ^ 2 = 2 * Real.cosh (π * v) ^ 2 by nlinarith,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq hch.le]
    rw [hnum_norm, mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (by norm_num)).ne']
  -- Factor 2 norm: |π(v + i/2) / sinh(π(v + i/2))| = π √(v^2 + 1/4) / cosh(π v)
  have hn2 : ‖(π : ℂ) * ((v : ℂ) + Complex.I / 2) / Complex.sinh ((π : ℂ) * ((v : ℂ) + Complex.I / 2))‖ =
      π * √(v ^ 2 + 1 / 4) / Real.cosh (π * v) := by
    have hsh : Complex.sinh ((π : ℂ) * ((v : ℂ) + Complex.I / 2)) = ((Real.cosh (π * v) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · rw [re_sinh']
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.div_ofNat_re,
          Complex.I_re, Complex.mul_im, Complex.add_im, Complex.div_ofNat_im, Complex.I_im,
          zero_mul, sub_zero, add_zero, zero_add, zero_div, mul_zero]
        rw [show π * (1 / 2) = π / 2 by ring, Real.cos_pi_div_two, mul_zero]
      · rw [im_sinh']
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.div_ofNat_re,
          Complex.I_re, Complex.mul_im, Complex.add_im, Complex.div_ofNat_im, Complex.I_im,
          zero_mul, sub_zero, add_zero, zero_add, zero_div, mul_zero, mul_one]
        rw [show π * (1 / 2) = π / 2 by ring, Real.sin_pi_div_two, mul_one]
    rw [hsh, norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpi, abs_of_pos hch]
    have hv : ‖(v : ℂ) + Complex.I / 2‖ = √(v ^ 2 + 1 / 4) := by
      rw [show (v : ℂ) + Complex.I / 2 = (v : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_add_mul_I]
      congr 1; ring
    rw [hv]
  -- Combine into R4cStrip:
  unfold R4cStrip
  have hnorm_cpow_half : ∀ z : ℂ, z ≠ 0 → ‖z ^ (1 / 2 : ℂ)‖ = √‖z‖ := by
    intro z hz
    rw [Complex.cpow_def_of_ne_zero hz, Complex.norm_exp, Complex.mul_re, Complex.log_re]
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, Complex.inv_im,
      Complex.im_ofNat, neg_zero, zero_div, mul_zero, sub_zero, Complex.log_im]
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
    congr 1; ring
  rw [norm_div, norm_mul,
    hnorm_cpow_half _ (Complex.slitPlane_ne_zero (r4c_alg_factor_mem_slitPlane hb)),
    hnorm_cpow_half _ (Complex.slitPlane_ne_zero (pi_mul_div_sinh_mem_slitPlane hb_strip)),
    hn1, hn2, Complex.norm_real, Real.norm_eq_abs, abs_of_pos kap_pos]
  rw [← Real.sqrt_mul hch.le, mul_div_cancel₀ _ hch.ne']
  unfold kap
  rw [Real.sqrt_mul hpi.le, Real.sqrt_mul hpi.le, mul_div_mul_left _ _ (Real.sqrt_pos.mpr hpi).ne']
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

/-! ### 4. The holomorphic boundary potential `uE` on `{|Im w| < 1/8}` -/

/-- Complexified `F(w) = (1/π) arsinh(cosh(π w))` on `{|Im w| < 1/8}`. -/
noncomputable def FcUE (w : ℂ) : ℂ :=
  Complex.log (Complex.cosh ((π : ℂ) * w) + (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)) / (π : ℂ)

/-- Explicit holomorphic boundary potential `u_E(w)` on `{|Im w| < 1/8}` (`cts:smooth-env` (2)). -/
noncomputable def uE (w : ℂ) : ℂ :=
  (Utilde0 : ℂ) +
    (3 / 8 : ℂ) * Complex.log (1 + Complex.cosh ((π : ℂ) * w) ^ 2) +
    (1 / 4 : ℂ) * Complex.log ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ)) -
    (1 / 4 : ℂ) * Complex.log 2 -
    Complex.log (Complex.cosh ((π : ℂ) * w)) +
    2 * Complex.log (1 - Complex.exp (-(4 : ℂ) * (π : ℂ) * FcUE w))

private lemma cosh_re_pos_eighth {w : ℂ} (hw : |w.im| < 1 / 8) :
    1 / 2 < (Complex.cosh ((π : ℂ) * w)).re := by
  have hpi := Real.pi_pos
  rw [re_cosh']
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.mul_im, add_zero]
  have h1 : 1 ≤ Real.cosh (π * w.re) := Real.one_le_cosh _
  have hcos : 1 / 2 < Real.cos (π * w.im) := by
    have hlt : |π * w.im| < π / 3 := by
      rw [abs_mul, abs_of_pos hpi]; nlinarith
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos ⟨abs_nonneg _, by linarith⟩ ⟨by positivity, by linarith⟩ hlt
  nlinarith

private lemma one_add_cosh_sq_re_pos_eighth {w : ℂ} (hw : |w.im| < 1 / 8) :
    1 < (1 + Complex.cosh ((π : ℂ) * w) ^ 2).re := by
  have hpi := Real.pi_pos
  have hre : (1 + Complex.cosh ((π : ℂ) * w) ^ 2).re =
      1 + (Complex.cosh ((π : ℂ) * w)).re ^ 2 - (Complex.cosh ((π : ℂ) * w)).im ^ 2 := by
    simp [sq]; ring
  rw [hre, re_cosh', im_cosh']
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.mul_im, add_zero]
  have hcs := Real.cosh_sq (π * w.re)
  have hsc := Real.sin_sq_add_cos_sq (π * w.im)
  have hcos2 : 0 < Real.cos (2 * (π * w.im)) := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by nlinarith [(abs_lt.mp hw).1], by nlinarith [(abs_lt.mp hw).2]⟩
  have hcos2_eq : Real.cos (2 * (π * w.im)) = 2 * Real.cos (π * w.im) ^ 2 - 1 :=
    Real.cos_two_mul _
  have halg : (Real.cosh (π * w.re) * Real.cos (π * w.im)) ^ 2 -
      (Real.sinh (π * w.re) * Real.sin (π * w.im)) ^ 2 =
      Real.cosh (π * w.re) ^ 2 * Real.cos (2 * (π * w.im)) + Real.sin (π * w.im) ^ 2 := by
    nlinarith [hcs, hsc, hcos2_eq]
  rw [show 1 + (Real.cosh (π * w.re) * Real.cos (π * w.im)) ^ 2 -
      (Real.sinh (π * w.re) * Real.sin (π * w.im)) ^ 2 =
      1 + ((Real.cosh (π * w.re) * Real.cos (π * w.im)) ^ 2 -
      (Real.sinh (π * w.re) * Real.sin (π * w.im)) ^ 2) by ring, halg]
  nlinarith [sq_nonneg (Real.sin (π * w.im)), Real.cosh_pos (π * w.re)]

private lemma sqrt_one_add_cosh_sq_re_pos_eighth {w : ℂ} (hw : |w.im| < 1 / 8) :
    1 / 2 < ((1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)).re := by
  set z := 1 + Complex.cosh ((π : ℂ) * w) ^ 2
  have hz_re : 1 < z.re := one_add_cosh_sq_re_pos_eighth hw
  have hz_ne : z ≠ 0 := by intro h; rw [h] at hz_re; simp at hz_re; linarith
  have hz_norm : 1 < ‖z‖ := lt_of_lt_of_le hz_re (Complex.re_le_norm z)
  have harg := arg_mem_Ioo_of_re_pos (by linarith : 0 < z.re)
  rw [Complex.cpow_def_of_ne_zero hz_ne, Complex.exp_re]
  have him : (Complex.log z * (1 / 2 : ℂ)).im = z.arg / 2 := by simp [Complex.log_im]; ring
  have hre : (Complex.log z * (1 / 2 : ℂ)).re = Real.log ‖z‖ / 2 := by
    simp [Complex.log_re]; ring
  rw [him, hre]
  have hexp : 1 < Real.exp (Real.log ‖z‖ / 2) := by
    rw [Real.one_lt_exp_iff]
    exact div_pos (Real.log_pos hz_norm) two_pos
  have hcos : 1 / 2 < Real.cos (z.arg / 2) := by
    have hlt : |z.arg / 2| < π / 3 := by
      rw [abs_lt]; constructor <;> linarith [harg.1, harg.2, Real.pi_pos]
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.strictAntiOn_cos ⟨abs_nonneg _, by linarith [Real.pi_pos]⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩ hlt
  nlinarith

private lemma one_sub_exp_FcUE_re_pos_eighth {w : ℂ} (hw : |w.im| < 1 / 8) :
    0 < (1 - Complex.exp (-(4 : ℂ) * (π : ℂ) * FcUE w)).re := by
  have hc_re := cosh_re_pos_eighth hw
  have hs_re := sqrt_one_add_cosh_sq_re_pos_eighth hw
  set A := Complex.cosh ((π : ℂ) * w) + (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ)
  have hA_re : 1 < A.re := by simp only [A, Complex.add_re]; linarith
  have hA_norm : 1 < ‖A‖ := lt_of_lt_of_le hA_re (Complex.re_le_norm A)
  have hlog_pos : 0 < Real.log ‖A‖ := Real.log_pos hA_norm
  have hFc : -(4 : ℂ) * (π : ℂ) * FcUE w = -(4 : ℂ) * Complex.log A := by
    unfold FcUE
    simp only [A]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hnorm_lt : ‖Complex.exp (-(4 : ℂ) * (π : ℂ) * FcUE w)‖ < 1 := by
    rw [hFc, Complex.norm_exp]
    have hre : (-(4 : ℂ) * Complex.log A).re = -4 * Real.log ‖A‖ := by
      simp [Complex.log_re]
    rw [hre, Real.exp_lt_one_iff]
    linarith
  have hre_le : (Complex.exp (-(4 : ℂ) * (π : ℂ) * FcUE w)).re ≤
      ‖Complex.exp (-(4 : ℂ) * (π : ℂ) * FcUE w)‖ := Complex.re_le_norm _
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- **`uE` is holomorphic on `{|Im w| < 1/8}`** (`cts:smooth-env` (2)). -/
theorem differentiableOn_uE : DifferentiableOn ℂ uE {w : ℂ | |w.im| < 1 / 8} := by
  intro w hw
  have hhw : |w.im| < 1 / 8 := hw
  have hc_diff : DifferentiableAt ℂ (fun z => Complex.cosh ((π : ℂ) * z)) w :=
    Complex.differentiableAt_cosh.comp w ((differentiableAt_const _).mul differentiableAt_id)
  have h1c_diff : DifferentiableAt ℂ (fun z => 1 + Complex.cosh ((π : ℂ) * z) ^ 2) w :=
    (differentiableAt_const _).add (hc_diff.pow 2)
  have h1c_slit : 1 + Complex.cosh ((π : ℂ) * w) ^ 2 ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [one_add_cosh_sq_re_pos_eighth hhw]))
  have hsq_diff : DifferentiableAt ℂ (fun z => (1 + Complex.cosh ((π : ℂ) * z) ^ 2) ^ (1 / 2 : ℂ)) w :=
    h1c_diff.cpow_const h1c_slit
  have hA_slit : Complex.cosh ((π : ℂ) * w) + (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) ∈
      Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by
      simp only [Complex.add_re]; linarith [cosh_re_pos_eighth hhw, sqrt_one_add_cosh_sq_re_pos_eighth hhw]))
  have hFc_diff : DifferentiableAt ℂ FcUE w :=
    ((hc_diff.add hsq_diff).clog hA_slit).div_const _
  have hsum_slit : (1 + Complex.cosh ((π : ℂ) * w) ^ 2) ^ (1 / 2 : ℂ) + (√2 : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [sqrt_one_add_cosh_sq_re_pos_eighth hhw, Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]))
  have hc_slit : Complex.cosh ((π : ℂ) * w) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [cosh_re_pos_eighth hhw]))
  have hexp_slit : 1 - Complex.exp (-(4 : ℂ) * (π : ℂ) * FcUE w) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (one_sub_exp_FcUE_re_pos_eighth hhw))
  unfold uE
  refine ((((((differentiableAt_const _).add ((differentiableAt_const _).mul (h1c_diff.clog h1c_slit))).add
    ((differentiableAt_const _).mul ((hsq_diff.add (differentiableAt_const _)).clog hsum_slit))).sub
    (differentiableAt_const _)).sub (hc_diff.clog hc_slit)).add
    ((differentiableAt_const _).mul (((differentiableAt_const _).sub
      (((differentiableAt_const _).mul hFc_diff).cexp)).clog hexp_slit))).differentiableWithinAt

lemma uE_neg (w : ℂ) : uE (-w) = uE w := by
  unfold uE FcUE
  simp only [mul_neg, Complex.cosh_neg]

private lemma ofReal_one_add_sq_cpow (a : ℝ) :
    (1 + (a : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((√(1 + a ^ 2) : ℝ) : ℂ) := by
  rw [show (1 + (a : ℂ) ^ 2) = ((1 + a ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]

lemma FcUE_real (v : ℝ) : FcUE (v : ℂ) = ((Real.arsinh (Real.cosh (π * v)) / π : ℝ) : ℂ) := by
  unfold FcUE
  have hch : 0 < Real.cosh (π * v) := Real.cosh_pos _
  have h1 : Complex.cosh ((π : ℂ) * (v : ℂ)) = ((Real.cosh (π * v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_cosh]
  rw [h1, ofReal_one_add_sq_cpow, ← Complex.ofReal_add, ← Complex.ofReal_log (by positivity), ← Complex.ofReal_div]
  rfl

/-- **`uE` is real on `ℝ`** (`cts:smooth-env` (2)). -/
theorem im_uE_real (v : ℝ) : (uE (v : ℂ)).im = 0 := by
  have hch : 0 < Real.cosh (π * v) := Real.cosh_pos _
  have hF_pos : 0 < Real.arsinh (Real.cosh (π * v)) / π :=
    div_pos (Real.arsinh_pos_iff.mpr hch) Real.pi_pos
  have h1e : 0 < 1 - Real.exp (-(4 * π * (Real.arsinh (Real.cosh (π * v)) / π))) := by
    rw [sub_pos, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have h1 : Complex.cosh ((π : ℂ) * (v : ℂ)) = ((Real.cosh (π * v) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_cosh]
  have hu_real : uE (v : ℂ) =
      ((Utilde0 + (3 / 8) * Real.log (1 + Real.cosh (π * v) ^ 2) +
        (1 / 4) * Real.log (√(1 + Real.cosh (π * v) ^ 2) + √2) -
        (1 / 4) * Real.log 2 - Real.log (Real.cosh (π * v)) +
        2 * Real.log (1 - Real.exp (-(4 * π * (Real.arsinh (Real.cosh (π * v)) / π)))) : ℝ) : ℂ) := by
    unfold uE
    rw [h1, ofReal_one_add_sq_cpow, FcUE_real]
    rw [show (1 + ((Real.cosh (π * v) : ℝ) : ℂ) ^ 2) = ((1 + Real.cosh (π * v) ^ 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity), ← Complex.ofReal_add,
      ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log hch.le,
      show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (1 : ℂ) - Complex.exp (-(4 : ℂ) * (π : ℂ) * ((Real.arsinh (Real.cosh (π * v)) / π : ℝ) : ℂ)) =
        ((1 - Real.exp (-(4 * π * (Real.arsinh (Real.cosh (π * v)) / π))) : ℝ) : ℂ) by
      rw [show -(4 : ℂ) * (π : ℂ) * ((Real.arsinh (Real.cosh (π * v)) / π : ℝ) : ℂ) =
          ((-(4 * π * (Real.arsinh (Real.cosh (π * v)) / π)) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]; push_cast; ring]
    rw [← Complex.ofReal_log h1e.le]
    push_cast; ring
  rw [hu_real, Complex.ofReal_im]

/-- **`Re uE(v_y) = log ‖Ĝ(e^{-iψ(y)})‖`** (`cts:smooth-env` (2)). -/
theorem re_uE_eq_log_norm_Ghat {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    (uE (vOf y : ℂ)).re =
      Real.log ‖(1 - starRingEnd ℂ (wPt y)) ^ (-(1 / 2 : ℂ)) *
        ((1 + (starRingEnd ℂ (wPt y)) ^ 2) * Gout (starRingEnd ℂ (wPt y)) /
          R4cStrip ((vOf y : ℂ) + Complex.I / 2))‖ := by
  have hy0 : 0 < y := hy.1
  have hy1 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hy2 : 0 < 1 + y ^ 2 := by positivity
  have hP : 0 < 1 + 6 * y ^ 2 + y ^ 4 := by positivity
  have hx := xOf_pos hy
  have hxi := xiStar_pos
  -- Step A: compute cosh(π vOf y) = √(uSlit y) and FcUE(vOf y) = xOf y
  have hch_eq : Real.cosh (π * vOf y) = √(uSlit y) := by
    have hsh : Real.sinh (π * vOf y) = √(uSlit y - 1) := by
      unfold vOf; rw [mul_div_cancel₀ _ Real.pi_ne_zero, Real.sinh_arsinh]
    have hcs := Real.cosh_sq (π * vOf y)
    have hu1 : 1 < uSlit y := uSlit_gt_one hy.1 hy.2
    have hsq : Real.cosh (π * vOf y) ^ 2 = uSlit y := by
      rw [hsh, Real.sq_sqrt (by linarith)] at hcs; linarith
    rw [← Real.sqrt_sq (Real.cosh_pos _).le, hsq]
  have hF_eq : Real.arsinh (Real.cosh (π * vOf y)) / π = xOf y := by
    rw [hch_eq]; rfl
  -- Step B: compute (uE (vOf y)).re explicitly in terms of y
  have h1e_x : 0 < 1 - Real.exp (-(4 * π * xOf y)) := by
    rw [sub_pos, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have h1e_xi : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
    rw [sub_pos, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have huE_re : (uE (vOf y : ℂ)).re =
      Real.log (((1 - Real.exp (-(4 * π * xOf y))) / (1 - Real.exp (-(4 * π * xiStar)))) ^ 2 *
        (1 + y ^ 2) ^ (3 / 4 : ℝ) / (2 * √(1 + 6 * y ^ 2 + y ^ 4))) := by
    have h1 : Complex.cosh ((π : ℂ) * (vOf y : ℂ)) = ((Real.cosh (π * vOf y) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Complex.ofReal_cosh]
    have hre1 : (uE (vOf y : ℂ)).re =
        Utilde0 + (3 / 8) * Real.log (1 + Real.cosh (π * vOf y) ^ 2) +
          (1 / 4) * Real.log (√(1 + Real.cosh (π * vOf y) ^ 2) + √2) -
          (1 / 4) * Real.log 2 - Real.log (Real.cosh (π * vOf y)) +
          2 * Real.log (1 - Real.exp (-(4 * π * xOf y))) := by
      unfold uE
      rw [h1, ofReal_one_add_sq_cpow, FcUE_real, hF_eq]
      rw [show (1 + ((Real.cosh (π * vOf y) : ℝ) : ℂ) ^ 2) = ((1 + Real.cosh (π * vOf y) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (by positivity), ← Complex.ofReal_add,
        ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log (Real.cosh_pos _).le,
        show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (1 : ℂ) - Complex.exp (-(4 : ℂ) * (π : ℂ) * ((xOf y : ℝ) : ℂ)) =
          ((1 - Real.exp (-(4 * π * xOf y)) : ℝ) : ℂ) by
        rw [show -(4 : ℂ) * (π : ℂ) * ((xOf y : ℝ) : ℂ) = ((-(4 * π * xOf y) : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_exp]; push_cast; ring]
      rw [← Complex.ofReal_log h1e_x.le]
      simp [Complex.ofReal_re, Complex.log_re]
    rw [hre1, hch_eq]
    have hu_pos : 0 < uSlit y := by linarith [uSlit_gt_one hy.1 hy.2]
    have h1u : 1 + uSlit y = 2 * (1 + y ^ 2) ^ 2 / (1 - y ^ 2) ^ 2 := by
      unfold uSlit; field_simp; ring
    have hs1u : √(1 + uSlit y) = √2 * (1 + y ^ 2) / (1 - y ^ 2) := by
      rw [h1u, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num),
        Real.sqrt_sq hy2.le, Real.sqrt_sq hy1.le]
    have hs1u_add : √(1 + uSlit y) + √2 = 2 * √2 / (1 - y ^ 2) := by
      rw [hs1u]; field_simp; ring
    rw [Real.sq_sqrt hu_pos.le, hs1u_add, h1u]
    conv_rhs =>
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_div h1e_x.ne' h1e_xi.ne', Real.log_rpow hy2,
        Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hP).ne', Real.log_sqrt hP.le]
    conv_lhs =>
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_div (by positivity) hy1.ne',
        Real.log_mul (by norm_num) (Real.sqrt_pos.mpr (by norm_num)).ne',
        Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.log_sqrt hu_pos.le]
    have hlog_u : Real.log (uSlit y) = Real.log (1 + 6 * y ^ 2 + y ^ 4) - 2 * Real.log (1 - y ^ 2) := by
      unfold uSlit
      rw [Real.log_div hP.ne' (by positivity), Real.log_pow]
      push_cast; ring
    rw [hlog_u]
    unfold Utilde0
    push_cast
    ring
  -- Step C: compute the RHS norm via gout_coupling, norm_R4cStrip_edge, norm_one_add_sq_edge
  rw [huE_re]
  congr 1
  -- Compute ‖Gout (conj (wPt y))‖ from gout_coupling:
  have hGout_edge : ‖Gout (starRingEnd ℂ (wPt y))‖ =
      Wslit y * ‖Kedge y‖ * (1 + y ^ 2) / (2 * y ^ 2) := by
    have hc := gout_coupling hy
    have hn := congrArg norm hc
    rw [norm_mul, norm_mul, norm_mul, gout_modulus hy, norm_wPt, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hn
    field_simp at hn ⊢
    linarith
  have hKedge_norm : ‖Kedge y‖ =
      ((vOf y ^ 2 + 1 / 4) ^ (1 / 4 : ℝ) / √(xOf y * (2 * y / (1 + y ^ 2)))) * y ^ 3 := by
    unfold Kedge
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_wPt, one_pow, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    congr 1
    set z := (((vOf y : ℝ) : ℂ) + Complex.I / 2) / ((xOf y * (2 * y / (1 + y ^ 2)) : ℝ) : ℂ)
    have hden_pos : 0 < xOf y * (2 * y / (1 + y ^ 2)) := by positivity
    have hz_ne : z ≠ 0 := by
      apply div_ne_zero
      · intro h; have := congrArg Complex.im h; simp at this
      · exact Complex.ofReal_ne_zero.mpr hden_pos.ne'
    rw [Complex.cpow_def_of_ne_zero hz_ne, Complex.norm_exp, Complex.mul_re, Complex.log_re]
    simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, Complex.inv_im,
      Complex.im_ofNat, neg_zero, zero_div, mul_zero, sub_zero, Complex.log_im]
    norm_num
    rw [← Real.rpow_def_of_pos (norm_pos_iff.mpr hz_ne), ← Real.sqrt_eq_rpow]
    have hzn : ‖z‖ = √(vOf y ^ 2 + 1 / 4) / (xOf y * (2 * y / (1 + y ^ 2))) := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden_pos,
        show ((vOf y : ℝ) : ℂ) + Complex.I / 2 = ((vOf y : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_add_mul_I]
      congr 2; ring
    rw [hzn, Real.sqrt_div (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]
    norm_num
  have h1sub_norm : ‖(1 - starRingEnd ℂ (wPt y)) ^ (-(1 / 2 : ℂ))‖ =
      (1 + y ^ 2) ^ (1 / 4 : ℝ) / √(2 * y) := by
    have h1sub_eq : ‖1 - starRingEnd ℂ (wPt y)‖ = 2 * y / √(1 + y ^ 2) := by
      have hsq : ‖1 - starRingEnd ℂ (wPt y)‖ ^ 2 = (2 * y / √(1 + y ^ 2)) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
          Complex.one_im, Complex.conj_re, Complex.conj_im, re_wPt, im_wPt, div_pow, Real.sq_sqrt hy2.le]
        field_simp; ring
      nlinarith [norm_nonneg (1 - starRingEnd ℂ (wPt y)), div_pos (by positivity : (0 : ℝ) < 2 * y) (Real.sqrt_pos.mpr hy2)]
    have hne : 1 - starRingEnd ℂ (wPt y) ≠ 0 := by
      rw [← norm_ne_zero_iff, h1sub_eq]; positivity
    rw [Complex.cpow_def_of_ne_zero hne, Complex.norm_exp, Complex.mul_re, Complex.log_re]
    simp only [Complex.neg_re, one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      Complex.neg_im, Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div, mul_zero, sub_zero,
      Complex.log_im]
    rw [show Real.log ‖1 - starRingEnd ℂ (wPt y)‖ * -(2 / (2 * 2) : ℝ) =
        Real.log ‖1 - starRingEnd ℂ (wPt y)‖ * (-(1 / 2 : ℝ)) by ring,
      ← Real.rpow_def_of_pos (norm_pos_iff.mpr hne), h1sub_eq,
      Real.div_rpow (by positivity) (Real.sqrt_pos.mpr hy2).le,
      Real.rpow_neg (by positivity), Real.rpow_neg (Real.sqrt_pos.mpr hy2).le,
      div_inv_eq_mul, inv_mul_eq_div, Real.sqrt_eq_rpow, ← Real.rpow_mul hy2.le,
      ← Real.sqrt_eq_rpow]
    norm_num
  have h1add_norm : ‖1 + (starRingEnd ℂ (wPt y)) ^ 2‖ = 2 * ((1 - y ^ 2) / (1 + y ^ 2)) :=
    norm_one_add_sq_arc hy.2 hy.1
  rw [norm_mul, norm_div, norm_mul, h1sub_norm, h1add_norm, hGout_edge, hKedge_norm,
    norm_R4cStrip_edge (vOf y)]
  unfold Wslit
  have hsq_x : √(xOf y / xiStar) = √(xOf y) / √xiStar := Real.sqrt_div hx.le xiStar
  have hsq_k : √(xOf y * (2 * y / (1 + y ^ 2))) = √(xOf y) * √(2 * y) / √(1 + y ^ 2) := by
    rw [Real.sqrt_mul hx.le, Real.sqrt_div (by positivity), mul_div_assoc]
  rw [hsq_x, hsq_k]
  have h1y_r : (1 + y ^ 2) ^ (3 / 4 : ℝ) = (1 + y ^ 2) ^ (1 / 4 : ℝ) * √(1 + y ^ 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy2]; norm_num
  have h2y_sq : √(2 * y) * √(2 * y) = 2 * y := Real.mul_self_sqrt (by positivity)
  have hxi_ne : √xiStar ≠ 0 := (Real.sqrt_pos.mpr hxi).ne'
  have hx_ne : √(xOf y) ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have h2y_ne : √(2 * y) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have h1y_ne : √(1 + y ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hy2).ne'
  have hv_ne : (vOf y ^ 2 + 1 / 4) ^ (1 / 4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hP_ne : √(1 + 6 * y ^ 2 + y ^ 4) ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  rw [h1y_r]
  field_simp
  rw [show √(y * 2) ^ 2 = y * 2 from Real.sq_sqrt (by positivity)]

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.one_sub_one_sub_delta_zetaD_mem_slitPlane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.one_sub_one_sub_delta_zetaD_mem_slitPlane

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.R4cStrip_eq_R4c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.R4cStrip_eq_R4c

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_uE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_uE

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.im_uE_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.im_uE_real

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.re_uE_eq_log_norm_Ghat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.re_uE_eq_log_norm_Ghat
