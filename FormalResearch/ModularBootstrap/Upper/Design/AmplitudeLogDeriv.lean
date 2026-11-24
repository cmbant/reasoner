module

public import FormalResearch.ModularBootstrap.Upper.Design.HankelEpsDeriv
public import FormalResearch.ModularBootstrap.Upper.Saddle.SDV
public import FormalResearch.ModularBootstrap.Upper.Hankel.EdgeExample
public import FormalResearch.ModularBootstrap.Upper.Comb.EdgePhase

/-!
# The saddle amplitude `A_x(b) = ℰ(b) e^{Φ₁(b)} b^{1/2} (1 + ε_H(kb))` for `ℰ = sech²(π b/2)`

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, Lemma `SD_V` (`esd:lemma`): hypotheses on
the nonvanishing amplitude `A_x`.  For an arbitrary `Φ₁`, holomorphic on the strip
`|Im b - 1/2| < 17/64` with bounded `Φ₁'`, `Φ₁''` on `𝒩_δ`, `δ = 1/8`, and `k = 4π n x/3 ≥ 8`,
`sdvAmplitude x n sechSqProfile Φ₁ hankelEps` is analytic and nonvanishing on `𝒩_δ`, and
`|(log A_x)'| ≤ M_0 + B₁`, `|(log A_x)''| ≤ M_0' + B₂`, where `M_0, M_0'` are absolute constants
(`amplitude_logDeriv_bounds`).  The Hankel expansion `H₀¹(z) = (2/(πz))^{1/2} e^{i(z-π/4)}
(1 + ε_H(z))` is `hankel0_eq_leading_mul`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex Metric Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Design

open FormalResearch.ModularBootstrap.Upper.Hankel FormalResearch.ModularBootstrap.Upper.Saddle
  FormalResearch.ModularBootstrap.Upper.Comb

/-- The constant `cos(5π/16) > 0` bounding `cos` from below on `[0, 5π/16]`. -/
noncomputable def cosC : ℝ := Real.cos (5 * π / 16)

lemma cosC_pos : 0 < cosC := by
  unfold cosC
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

/-- For `0 ≤ y ≤ 5π/16`, `cos y ≥ cosC`. -/
lemma cosC_le_cos {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 5 * π / 16) : cosC ≤ Real.cos y :=
  Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]) h1

lemma im_pi_mul_div_two_mem {b : ℂ} (hb : |b.im - 1 / 2| ≤ 1 / 8) :
    0 ≤ ((π : ℂ) * b / 2).im ∧ ((π : ℂ) * b / 2).im ≤ 5 * π / 16 := by
  have h := abs_le.mp hb
  have him : ((π : ℂ) * b / 2).im = π * b.im / 2 := by simp [Complex.mul_im]
  rw [him]
  have hpi := Real.pi_pos
  constructor <;> nlinarith

/-- `‖cosh z‖ ≥ cos(y) cosh(x)`-type lower bound on the strip `0 ≤ Im z ≤ 5π/16`. -/
lemma cosC_mul_cosh_le_norm_cosh {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ 5 * π / 16) :
    cosC * Real.cosh z.re ≤ ‖Complex.cosh z‖ := by
  have hc := cosC_le_cos h0 h1
  have hcpos := cosC_pos
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
  have hns : ‖Complex.cosh z‖ ^ 2 = Real.cosh z.re ^ 2 - Real.sin z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    conv_lhs => rw [hz]
    exact complex_cosh_normSq _ _
  have hsq : (cosC * Real.cosh z.re) ^ 2 ≤ ‖Complex.cosh z‖ ^ 2 := by
    rw [hns]
    have hch := Real.cosh_sq z.re
    have hsn := Real.sin_sq_add_cos_sq z.im
    have h2 : cosC ^ 2 ≤ Real.cos z.im ^ 2 := pow_le_pow_left₀ hcpos.le hc 2
    nlinarith [sq_nonneg (Real.sinh z.re), Real.cosh_pos z.re,
      mul_nonneg (sq_nonneg (Real.sinh z.re)) (sub_nonneg.mpr h2)]
  exact le_of_sq_le_sq (by simpa using hsq) (norm_nonneg _)

lemma norm_sinh_le_cosh_re (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := Complex.ext (by simp) (by simp)
  have hns : ‖Complex.sinh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.sin z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    conv_lhs => rw [hz]
    exact complex_sinh_normSq _ _
  have : ‖Complex.sinh z‖ ^ 2 ≤ Real.cosh z.re ^ 2 := by
    rw [hns]; nlinarith [Real.cosh_sq z.re, Real.sin_sq_le_one z.im]
  exact le_of_sq_le_sq (by simpa using this) (Real.cosh_pos _).le

/-- On `|Im b - 1/2| ≤ 1/8`: `‖cosh(πb/2)‖ ≥ cosC`. -/
lemma cosC_le_norm_cosh {b : ℂ} (hb : |b.im - 1 / 2| ≤ 1 / 8) :
    cosC ≤ ‖Complex.cosh ((π : ℂ) * b / 2)‖ := by
  obtain ⟨h0, h1⟩ := im_pi_mul_div_two_mem hb
  have := cosC_mul_cosh_le_norm_cosh h0 h1
  have h2 := Real.one_le_cosh ((π : ℂ) * b / 2).re
  have hcpos := cosC_pos
  nlinarith

lemma norm_tanh_le {b : ℂ} (hb : |b.im - 1 / 2| ≤ 1 / 8) :
    ‖Complex.tanh ((π : ℂ) * b / 2)‖ ≤ 1 / cosC := by
  obtain ⟨h0, h1⟩ := im_pi_mul_div_two_mem hb
  have hcpos := cosC_pos
  have hl := cosC_mul_cosh_le_norm_cosh h0 h1
  have hs := norm_sinh_le_cosh_re ((π : ℂ) * b / 2)
  have hch := Real.cosh_pos ((π : ℂ) * b / 2).re
  have hn : 0 < ‖Complex.cosh ((π : ℂ) * b / 2)‖ := lt_of_lt_of_le (by positivity) hl
  rw [Complex.tanh_eq_sinh_div_cosh, norm_div, div_le_div_iff₀ hn hcpos]
  nlinarith

/-! ### The four factors of the amplitude -/

/-- The Hankel factor `1 + ε_H(k z)`. -/
noncomputable def ampF4 (k : ℝ) (z : ℂ) : ℂ := 1 + hankelEps ((k : ℂ) * z)

lemma ampF4_eq (k : ℝ) (z : ℂ) :
    ampF4 k z = hankelR (-Complex.I * ((k : ℂ) * z)) / ((√π : ℝ) : ℂ) := by
  unfold ampF4; exact one_add_hankelEps

lemma sqrtPi_ne : ((√π : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'

lemma hasDerivAt_ampF4 {k : ℝ} {z : ℂ} (hz : 0 < k * z.im) :
    HasDerivAt (ampF4 k) (((-Complex.I * (k : ℂ)) * deriv hankelR (-Complex.I * ((k : ℂ) * z))) /
      ((√π : ℝ) : ℂ)) z := by
  have h := (hasDerivAt_hankelR_comp hz).div_const ((√π : ℝ) : ℂ)
  have e : ampF4 k = fun z => hankelR (-Complex.I * ((k : ℂ) * z)) / ((√π : ℝ) : ℂ) :=
    funext (ampF4_eq k)
  rw [e]; exact h

lemma ampF4_ne_zero {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : 0 < z.im) (hkz : 1 ≤ ‖(k : ℂ) * z‖) :
    ampF4 k z ≠ 0 := by
  have him : 0 < ((k : ℂ) * z).im := by rw [Complex.im_ofReal_mul]; positivity
  have h1 := norm_hankelEps_le him
  have h2 : 1 / (4 * ‖(k : ℂ) * z‖) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  intro h
  unfold ampF4 at h
  have : ‖hankelEps ((k : ℂ) * z)‖ = 1 := by
    have : hankelEps ((k : ℂ) * z) = -1 := by linear_combination h
    rw [this]; simp
  linarith

lemma logDeriv_ampF4 {k : ℝ} {z : ℂ} (hz : 0 < k * z.im) :
    logDeriv (ampF4 k) z = hankelLogD k z := by
  rw [logDeriv_apply, (hasDerivAt_ampF4 hz).deriv, ampF4_eq]
  unfold hankelLogD
  have := sqrtPi_ne
  field_simp

lemma cosh_ne_zero_of_mem {z : ℂ} (hz : z ∈ combNMid) : Complex.cosh ((π : ℂ) * z / 2) ≠ 0 := by
  apply complex_cosh_ne_zero_of_abs_im_lt_pi_div_two
  have h := abs_lt.mp (show |z.im - 1 / 2| < 17 / 64 from hz)
  have him : ((π : ℂ) * z / 2).im = π * z.im / 2 := by simp [Complex.mul_im]
  rw [him, abs_lt]
  have hpi := Real.pi_pos
  constructor <;> nlinarith

lemma hasDerivAt_cosh_pi_half (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.cosh ((π : ℂ) * z / 2))
      (Complex.sinh ((π : ℂ) * z / 2) * ((π : ℂ) / 2)) z := by
  have hlin : HasDerivAt (fun z : ℂ => (π : ℂ) * z / 2) ((π : ℂ) / 2) z := by
    simpa [mul_div_assoc] using ((hasDerivAt_id z).const_mul (π : ℂ)).div_const (2 : ℂ)
  exact (Complex.hasDerivAt_cosh _).comp z hlin

lemma hasDerivAt_sinh_pi_half (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.sinh ((π : ℂ) * z / 2))
      (Complex.cosh ((π : ℂ) * z / 2) * ((π : ℂ) / 2)) z := by
  have hlin : HasDerivAt (fun z : ℂ => (π : ℂ) * z / 2) ((π : ℂ) / 2) z := by
    simpa [mul_div_assoc] using ((hasDerivAt_id z).const_mul (π : ℂ)).div_const (2 : ℂ)
  exact (Complex.hasDerivAt_sinh _).comp z hlin

lemma hasDerivAt_sechSq {z : ℂ} (hz : z ∈ combNMid) :
    HasDerivAt sechSqProfile
      (-(π : ℂ) * (Complex.sinh ((π : ℂ) * z / 2) / Complex.cosh ((π : ℂ) * z / 2)) *
        (1 / Complex.cosh ((π : ℂ) * z / 2) ^ 2)) z := by
  have hne := cosh_ne_zero_of_mem hz
  have h := ((hasDerivAt_cosh_pi_half z).pow 2).inv (pow_ne_zero 2 hne)
  have e : sechSqProfile = fun z : ℂ => ((Complex.cosh ((π : ℂ) * z / 2)) ^ 2)⁻¹ := by
    funext w; unfold sechSqProfile; simp
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  field_simp
  ring

lemma sechSq_ne_zero {z : ℂ} (hz : z ∈ combNMid) : sechSqProfile z ≠ 0 := by
  unfold sechSqProfile
  exact one_div_ne_zero (pow_ne_zero 2 (cosh_ne_zero_of_mem hz))

lemma logDeriv_sechSq {z : ℂ} (hz : z ∈ combNMid) :
    logDeriv sechSqProfile z =
      -(π : ℂ) * (Complex.sinh ((π : ℂ) * z / 2) / Complex.cosh ((π : ℂ) * z / 2)) := by
  rw [logDeriv_apply, (hasDerivAt_sechSq hz).deriv]
  have := sechSq_ne_zero hz
  have hne := cosh_ne_zero_of_mem hz
  unfold sechSqProfile at this ⊢
  field_simp

lemma hasDerivAt_logSech {z : ℂ} (hz : z ∈ combNMid) :
    HasDerivAt (fun z : ℂ => -(π : ℂ) *
        (Complex.sinh ((π : ℂ) * z / 2) / Complex.cosh ((π : ℂ) * z / 2)))
      (-(π : ℂ) * ((π : ℂ) / 2) / Complex.cosh ((π : ℂ) * z / 2) ^ 2) z := by
  have hne := cosh_ne_zero_of_mem hz
  have h := ((hasDerivAt_sinh_pi_half z).div (hasDerivAt_cosh_pi_half z) hne).const_mul (-(π : ℂ))
  refine h.congr_deriv ?_
  have hsq : Complex.cosh ((π : ℂ) * z / 2) ^ 2 - Complex.sinh ((π : ℂ) * z / 2) ^ 2 = 1 := by
    simpa [sq] using Complex.cosh_sq_sub_sinh_sq ((π : ℂ) * z / 2)
  calc _ = -(π : ℂ) * (((π : ℂ) / 2) * (Complex.cosh ((π : ℂ) * z / 2) ^ 2 -
        Complex.sinh ((π : ℂ) * z / 2) ^ 2) / Complex.cosh ((π : ℂ) * z / 2) ^ 2) := by ring
    _ = _ := by rw [hsq]; ring

/-- The square-root factor. -/
lemma hasDerivAt_sqrt_factor {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ((1 / 2 : ℂ) * z ^ (1 / 2 - 1 : ℂ)) z := by
  have hs : z ∈ Complex.slitPlane := Or.inr (ne_of_gt hz)
  exact (hasDerivAt_id z).cpow_const hs |>.congr_deriv (by simp)

lemma sqrt_factor_ne_zero {z : ℂ} (hz : 0 < z.im) : z ^ (1 / 2 : ℂ) ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl hz0)

lemma logDeriv_sqrt_factor {z : ℂ} (hz : 0 < z.im) :
    logDeriv (fun z : ℂ => z ^ (1 / 2 : ℂ)) z = 1 / (2 * z) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [logDeriv_apply, (hasDerivAt_sqrt_factor hz).deriv, Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  have := sqrt_factor_ne_zero hz
  field_simp

/-- The exponential factor. -/
lemma logDeriv_exp_comp {Φ₁ : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ Φ₁ z) :
    logDeriv (fun z => Complex.exp (Φ₁ z)) z = deriv Φ₁ z := by
  rw [logDeriv_apply, h.hasDerivAt.cexp.deriv]
  have := Complex.exp_ne_zero (Φ₁ z)
  field_simp

/-! ### The logarithmic derivative of the amplitude -/

/-- The explicit logarithmic derivative of the amplitude. -/
noncomputable def ampLogD (Φ₁ : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℂ :=
  -(π : ℂ) * (Complex.sinh ((π : ℂ) * z / 2) / Complex.cosh ((π : ℂ) * z / 2)) + deriv Φ₁ z +
    1 / (2 * z) + hankelLogD k z

lemma im_pos_of_mem_combNMid {z : ℂ} (hz : z ∈ combNMid) : 15 / 64 < z.im ∧ z.im < 49 / 64 := by
  have h := abs_lt.mp (show |z.im - 1 / 2| < 17 / 64 from hz)
  constructor <;> linarith [h.1, h.2]

lemma one_le_norm_mul_of_mem_combNMid {k : ℝ} (hk : 8 ≤ k) {z : ℂ} (hz : z ∈ combNMid) :
    1 ≤ ‖(k : ℂ) * z‖ ∧ 0 < k * z.im := by
  have h := (im_pos_of_mem_combNMid hz).1
  have h1 : k * z.im ≤ ‖(k : ℂ) * z‖ := by
    have := Complex.abs_im_le_norm ((k : ℂ) * z)
    rw [Complex.im_ofReal_mul, abs_of_pos (by nlinarith)] at this
    exact this
  exact ⟨by nlinarith, by nlinarith⟩

/-- Pointwise facts for the four factors of the amplitude at `z ∈ 𝒩`. -/
lemma amplitude_logDeriv_eq {Φ₁ : ℂ → ℂ} {k : ℝ} (hk : 8 ≤ k) (hΦ : DifferentiableOn ℂ Φ₁ combNMid)
    {z : ℂ} (hz : z ∈ combNMid) :
    logDeriv (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ) * ampF4 k b) z =
      ampLogD Φ₁ k z := by
  have him := (im_pos_of_mem_combNMid hz).1
  have him0 : 0 < z.im := by linarith
  obtain ⟨hkz, hkpos⟩ := one_le_norm_mul_of_mem_combNMid hk hz
  have hΦd : DifferentiableAt ℂ Φ₁ z := (hΦ z hz).differentiableAt (isOpen_combNMid.mem_nhds hz)
  have d1 : DifferentiableAt ℂ sechSqProfile z := (hasDerivAt_sechSq hz).differentiableAt
  have d2 : DifferentiableAt ℂ (fun b => Complex.exp (Φ₁ b)) z := hΦd.cexp
  have d3 : DifferentiableAt ℂ (fun b : ℂ => b ^ (1 / 2 : ℂ)) z :=
    (hasDerivAt_sqrt_factor him0).differentiableAt
  have d4 : DifferentiableAt ℂ (ampF4 k) z := (hasDerivAt_ampF4 hkpos).differentiableAt
  have n1 := sechSq_ne_zero hz
  have n2 := Complex.exp_ne_zero (Φ₁ z)
  have n3 := sqrt_factor_ne_zero him0
  have n4 := ampF4_ne_zero (by linarith) him0 hkz
  have h12 := logDeriv_fun_mul (f := sechSqProfile) (g := fun b => Complex.exp (Φ₁ b)) z n1 n2 d1 d2
  have h123 := logDeriv_fun_mul (f := fun b => sechSqProfile b * Complex.exp (Φ₁ b))
    (g := fun b : ℂ => b ^ (1 / 2 : ℂ)) z (mul_ne_zero n1 n2) n3 (d1.mul d2) d3
  have h1234 := logDeriv_fun_mul
    (f := fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ)) (g := ampF4 k) z
    (mul_ne_zero (mul_ne_zero n1 n2) n3) n4 ((d1.mul d2).mul d3) d4
  rw [h1234, h123, h12, logDeriv_sechSq hz, logDeriv_exp_comp hΦd, logDeriv_sqrt_factor him0,
    logDeriv_ampF4 hkpos]
  unfold ampLogD
  ring

lemma hasDerivAt_ampLogD {Φ₁ : ℂ → ℂ} {k : ℝ} (hk : 8 ≤ k) (hΦ : DifferentiableOn ℂ Φ₁ combNMid)
    {b : ℂ} (hb : b ∈ combNMid) :
    HasDerivAt (ampLogD Φ₁ k)
      (-(π : ℂ) * ((π : ℂ) / 2) / Complex.cosh ((π : ℂ) * b / 2) ^ 2 + deriv (deriv Φ₁) b +
        (-1 / (2 * b ^ 2)) +
        (-Complex.I * (k : ℂ)) ^ 2 *
          (deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * b)) /
              hankelR (-Complex.I * ((k : ℂ) * b)) -
            (deriv hankelR (-Complex.I * ((k : ℂ) * b)) /
              hankelR (-Complex.I * ((k : ℂ) * b))) ^ 2)) b := by
  have him := (im_pos_of_mem_combNMid hb).1
  have him0 : 0 < b.im := by linarith
  have hb0 : b ≠ 0 := fun h => by simp [h] at him0
  obtain ⟨hkz, hkpos⟩ := one_le_norm_mul_of_mem_combNMid hk hb
  have hopen := isOpen_combNMid
  have hΦa : AnalyticOnNhd ℂ Φ₁ combNMid := hΦ.analyticOnNhd hopen
  have hd2 : HasDerivAt (deriv Φ₁) (deriv (deriv Φ₁) b) b :=
    ((hΦa.deriv b hb).differentiableAt).hasDerivAt
  have hne : hankelR (-Complex.I * ((k : ℂ) * b)) ≠ 0 := by
    have := ampF4_ne_zero (by linarith) him0 hkz
    rw [ampF4_eq] at this
    intro h; apply this; rw [h]; simp
  have h1 := hasDerivAt_logSech hb
  have h3 : HasDerivAt (fun z : ℂ => 1 / (2 * z)) (-1 / (2 * b ^ 2)) b := by
    have := ((hasDerivAt_id b).const_mul (2 : ℂ)).inv (mul_ne_zero two_ne_zero hb0)
    have e : (fun z : ℂ => 1 / (2 * z)) = fun z : ℂ => (2 * id z)⁻¹ := by
      funext z; simp
    rw [e]
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  have h4 := hasDerivAt_hankelLogD hkpos hne
  have := ((h1.add hd2).add h3).add h4
  unfold ampLogD
  exact this

lemma hankel_part_numeric {k t : ℝ} (hk : 8 ≤ k) (ht : 3 / 8 ≤ t) :
    4 * k / (3 * (k * t) ^ 2) ≤ 2 ∧
      k ^ 2 * (32 / (3 * (k * t) ^ 3) + 16 / (9 * (k * t) ^ 4)) ≤ 28 := by
  have hk0 : 0 < k := by linarith
  have ht0 : 0 < t := by linarith
  have hkt : 3 ≤ k * t := by nlinarith
  have hkt0 : 0 < k * t := by positivity
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hk0 ht0]
  · have e : k ^ 2 * (32 / (3 * (k * t) ^ 3) + 16 / (9 * (k * t) ^ 4)) =
        32 / (3 * k * t ^ 3) + 16 / (9 * k ^ 2 * t ^ 4) := by
      field_simp
    rw [e]
    have h1 : 32 / (3 * k * t ^ 3) ≤ 26 := by
      rw [div_le_iff₀ (by positivity)]
      have : 27 / 64 ≤ k * t ^ 3 := by
        have h3 : (27 / 512 : ℝ) ≤ t ^ 3 := by
          calc (27 / 512 : ℝ) = (3 / 8) ^ 3 := by norm_num
            _ ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht 3
        nlinarith
      nlinarith
    have h2 : 16 / (9 * k ^ 2 * t ^ 4) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h4 : (81 / 4096 : ℝ) ≤ t ^ 4 := by
        calc (81 / 4096 : ℝ) = (3 / 8) ^ 4 := by norm_num
          _ ≤ t ^ 4 := pow_le_pow_left₀ (by norm_num) ht 4
      have h5 : (64 : ℝ) ≤ k ^ 2 := by nlinarith
      nlinarith [mul_le_mul h5 h4 (by norm_num) (by positivity)]
    linarith

/-! ### The Hankel-free amplitude `A₀^∘ = ℰ e^{Φ₁} b^{1/2}` -/

/-- The explicit logarithmic derivative of the Hankel-free amplitude `ℰ e^{Φ₁} b^{1/2}`. -/
noncomputable def circLogD (Φ₁ : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(π : ℂ) * (Complex.sinh ((π : ℂ) * z / 2) / Complex.cosh ((π : ℂ) * z / 2)) + deriv Φ₁ z +
    1 / (2 * z)

lemma ampLogD_eq_circLogD_add (Φ₁ : ℂ → ℂ) (k : ℝ) (z : ℂ) :
    ampLogD Φ₁ k z = circLogD Φ₁ z + hankelLogD k z := by
  unfold ampLogD circLogD; ring

lemma circ_logDeriv_eq {Φ₁ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ₁ combNMid) {z : ℂ}
    (hz : z ∈ combNMid) :
    logDeriv (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ)) z =
      circLogD Φ₁ z := by
  have him := (im_pos_of_mem_combNMid hz).1
  have him0 : 0 < z.im := by linarith
  have hΦd : DifferentiableAt ℂ Φ₁ z := (hΦ z hz).differentiableAt (isOpen_combNMid.mem_nhds hz)
  have d1 : DifferentiableAt ℂ sechSqProfile z := (hasDerivAt_sechSq hz).differentiableAt
  have d2 : DifferentiableAt ℂ (fun b => Complex.exp (Φ₁ b)) z := hΦd.cexp
  have d3 : DifferentiableAt ℂ (fun b : ℂ => b ^ (1 / 2 : ℂ)) z :=
    (hasDerivAt_sqrt_factor him0).differentiableAt
  have n1 := sechSq_ne_zero hz
  have n2 := Complex.exp_ne_zero (Φ₁ z)
  have n3 := sqrt_factor_ne_zero him0
  have h12 := logDeriv_fun_mul (f := sechSqProfile) (g := fun b => Complex.exp (Φ₁ b)) z n1 n2 d1 d2
  have h123 := logDeriv_fun_mul (f := fun b => sechSqProfile b * Complex.exp (Φ₁ b))
    (g := fun b : ℂ => b ^ (1 / 2 : ℂ)) z (mul_ne_zero n1 n2) n3 (d1.mul d2) d3
  rw [h123, h12, logDeriv_sechSq hz, logDeriv_exp_comp hΦd, logDeriv_sqrt_factor him0]
  unfold circLogD
  ring

lemma hasDerivAt_circLogD {Φ₁ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ₁ combNMid) {b : ℂ}
    (hb : b ∈ combNMid) :
    HasDerivAt (circLogD Φ₁)
      (-(π : ℂ) * ((π : ℂ) / 2) / Complex.cosh ((π : ℂ) * b / 2) ^ 2 + deriv (deriv Φ₁) b +
        (-1 / (2 * b ^ 2))) b := by
  have him := (im_pos_of_mem_combNMid hb).1
  have him0 : 0 < b.im := by linarith
  have hb0 : b ≠ 0 := fun h => by simp [h] at him0
  have hΦa : AnalyticOnNhd ℂ Φ₁ combNMid := hΦ.analyticOnNhd isOpen_combNMid
  have hd2 : HasDerivAt (deriv Φ₁) (deriv (deriv Φ₁) b) b :=
    ((hΦa.deriv b hb).differentiableAt).hasDerivAt
  have h1 := hasDerivAt_logSech hb
  have h3 : HasDerivAt (fun z : ℂ => 1 / (2 * z)) (-1 / (2 * b ^ 2)) b := by
    have := ((hasDerivAt_id b).const_mul (2 : ℂ)).inv (mul_ne_zero two_ne_zero hb0)
    have e : (fun z : ℂ => 1 / (2 * z)) = fun z : ℂ => (2 * id z)⁻¹ := by
      funext z; simp
    rw [e]
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  have := (h1.add hd2).add h3
  unfold circLogD
  exact this

/-- `‖(log A₀^∘)'‖ ≤ π/cos(5π/16) + B₁ + 2` on `𝒩_{1/8}`. -/
lemma norm_circLogD_le {Φ₁ : ℂ → ℂ} {B1 : ℝ} (hB1 : ∀ b ∈ edgeStrip (1 / 8), ‖deriv Φ₁ b‖ ≤ B1)
    {b : ℂ} (hb : b ∈ edgeStrip (1 / 8)) : ‖circLogD Φ₁ b‖ ≤ π / cosC + B1 + 2 := by
  have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
  have hcpos := cosC_pos
  have him : 3 / 8 ≤ b.im := by linarith [(abs_le.mp hb').1]
  have hnb : (1 / 4 : ℝ) ≤ ‖b‖ := mem_edgeStrip_norm_ge_quarter (by norm_num) hb
  have htanh := norm_tanh_le hb'
  have t1 : ‖-(π : ℂ) * (Complex.sinh ((π : ℂ) * b / 2) / Complex.cosh ((π : ℂ) * b / 2))‖ ≤
      π / cosC := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have := htanh
    rw [Complex.tanh_eq_sinh_div_cosh] at this
    calc π * ‖Complex.sinh ((π : ℂ) * b / 2) / Complex.cosh ((π : ℂ) * b / 2)‖ ≤ π * (1 / cosC) := by
          gcongr
      _ = π / cosC := by ring
  have t3 : ‖(1 : ℂ) / (2 * b)‖ ≤ 2 := by
    rw [norm_div, norm_one, norm_mul]
    simp only [Complex.norm_ofNat]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  unfold circLogD
  calc _ ≤ ‖-(π : ℂ) * (Complex.sinh ((π : ℂ) * b / 2) / Complex.cosh ((π : ℂ) * b / 2))‖ +
        ‖deriv Φ₁ b‖ + ‖(1 : ℂ) / (2 * b)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ π / cosC + B1 + 2 := by gcongr; exact hB1 b hb

/-- `‖(log A₀^∘)''‖ ≤ π²/(2cos²(5π/16)) + B₂ + 8` on `𝒩_{1/8}`. -/
lemma norm_circLogD'_le {Φ₁ : ℂ → ℂ} {B2 : ℝ}
    (hB2 : ∀ b ∈ edgeStrip (1 / 8), ‖deriv (deriv Φ₁) b‖ ≤ B2) {b : ℂ}
    (hb : b ∈ edgeStrip (1 / 8)) :
    ‖-(π : ℂ) * ((π : ℂ) / 2) / Complex.cosh ((π : ℂ) * b / 2) ^ 2 + deriv (deriv Φ₁) b +
        (-1 / (2 * b ^ 2))‖ ≤ π ^ 2 / (2 * cosC ^ 2) + B2 + 8 := by
  have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
  have hcpos := cosC_pos
  have hnb : (1 / 4 : ℝ) ≤ ‖b‖ := mem_edgeStrip_norm_ge_quarter (by norm_num) hb
  have hcosh := cosC_le_norm_cosh hb'
  have t1 : ‖-(π : ℂ) * ((π : ℂ) / 2) / Complex.cosh ((π : ℂ) * b / 2) ^ 2‖ ≤
      π ^ 2 / (2 * cosC ^ 2) := by
    rw [norm_div, norm_pow, norm_mul, norm_neg, Complex.norm_real, norm_div,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp only [Complex.norm_ofNat]
    calc π * (π / 2) / ‖Complex.cosh ((π : ℂ) * b / 2)‖ ^ 2 ≤ π * (π / 2) / cosC ^ 2 := by
          gcongr
      _ = π ^ 2 / (2 * cosC ^ 2) := by field_simp
  have t3 : ‖(-1 : ℂ) / (2 * b ^ 2)‖ ≤ 8 := by
    rw [norm_div, norm_neg, norm_one, norm_mul, norm_pow]
    simp only [Complex.norm_ofNat]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc _ ≤ ‖-(π : ℂ) * ((π : ℂ) / 2) / Complex.cosh ((π : ℂ) * b / 2) ^ 2‖ +
        ‖deriv (deriv Φ₁) b‖ + ‖(-1 : ℂ) / (2 * b ^ 2)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ π ^ 2 / (2 * cosC ^ 2) + B2 + 8 := by gcongr; exact hB2 b hb

/-- Absolute constants in the log-derivative bounds. -/
noncomputable def ampM0 : ℝ := π / cosC + 4

noncomputable def ampM0' : ℝ := π ^ 2 / (2 * cosC ^ 2) + 8 + 28

theorem amplitude_logDeriv_bounds {Φ₁ : ℂ → ℂ} {k B1 B2 : ℝ} (hk : 8 ≤ k)
    (hB1 : ∀ b ∈ edgeStrip (1 / 8), ‖deriv Φ₁ b‖ ≤ B1)
    (hB2 : ∀ b ∈ edgeStrip (1 / 8), ‖deriv (deriv Φ₁) b‖ ≤ B2) {b : ℂ}
    (hb : b ∈ edgeStrip (1 / 8)) :
    ‖ampLogD Φ₁ k b‖ ≤ ampM0 + B1 ∧
    ‖(-(π : ℂ) * ((π : ℂ) / 2) / Complex.cosh ((π : ℂ) * b / 2) ^ 2 + deriv (deriv Φ₁) b +
        (-1 / (2 * b ^ 2)) +
        (-Complex.I * (k : ℂ)) ^ 2 *
          (deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * b)) /
              hankelR (-Complex.I * ((k : ℂ) * b)) -
            (deriv hankelR (-Complex.I * ((k : ℂ) * b)) /
              hankelR (-Complex.I * ((k : ℂ) * b))) ^ 2))‖ ≤ ampM0' + B2 := by
  have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
  have hbm : b ∈ combNMid := by
    change |b.im - 1 / 2| < 17 / 64
    exact lt_of_le_of_lt hb' (by norm_num)
  have him : 3 / 8 ≤ b.im := by linarith [(abs_le.mp hb').1]
  obtain ⟨hkz, hkpos⟩ := one_le_norm_mul_of_mem_combNMid hk hbm
  have hnum := hankel_part_numeric hk him
  have hHlog := (norm_hankelLogD_le (by linarith : 0 < k) hkpos hkz).trans hnum.1
  have hHlog2 := (norm_deriv_hankelLogD_le (by linarith : 0 < k) hkpos hkz).trans hnum.2
  constructor
  · rw [ampLogD_eq_circLogD_add]
    calc _ ≤ ‖circLogD Φ₁ b‖ + ‖hankelLogD k b‖ := norm_add_le _ _
      _ ≤ π / cosC + B1 + 2 + 2 := add_le_add (norm_circLogD_le hB1 hb) hHlog
      _ = ampM0 + B1 := by unfold ampM0; ring
  · calc _ ≤ ‖-(π : ℂ) * ((π : ℂ) / 2) / Complex.cosh ((π : ℂ) * b / 2) ^ 2 +
          deriv (deriv Φ₁) b + (-1 / (2 * b ^ 2))‖ +
          ‖(-Complex.I * (k : ℂ)) ^ 2 *
          (deriv (deriv hankelR) (-Complex.I * ((k : ℂ) * b)) /
              hankelR (-Complex.I * ((k : ℂ) * b)) -
            (deriv hankelR (-Complex.I * ((k : ℂ) * b)) /
              hankelR (-Complex.I * ((k : ℂ) * b))) ^ 2)‖ := norm_add_le _ _
      _ ≤ π ^ 2 / (2 * cosC ^ 2) + B2 + 8 + 28 := add_le_add (norm_circLogD'_le hB2 hb) hHlog2
      _ = ampM0' + B2 := by unfold ampM0'; ring

lemma edgeStrip_eighth_subset : edgeStrip (1 / 8) ⊆ combNMid := fun b hb => by
  have hb' : |b.im - 1 / 2| ≤ 1 / 8 := hb
  change |b.im - 1 / 2| < 17 / 64
  exact lt_of_le_of_lt hb' (by norm_num)

/-- **`SD_V'`-type amplitude fields for the Hankel-free amplitude** `A₀^∘ = ℰ e^{Φ₁} b^{1/2}`
(`ℰ = sech²(π b/2)`; `fw:SDp`, hypothesis (c)): for `Φ₁` holomorphic on `|Im b - 1/2| < 17/64` with
`‖Φ₁'‖ ≤ B₁`, `‖Φ₁''‖ ≤ B₂` on `𝒩_{1/8}`, `A₀^∘` is analytic and nonvanishing on `𝒩_{1/8}`,
`|(log A₀^∘)'| ≤ 𝒜₀ + B₁` and `|(log A₀^∘)''| ≤ 𝒜₀' + B₂`. -/
theorem circAmplitude_fields {Φ₁ : ℂ → ℂ} {B1 B2 : ℝ} (hΦ : DifferentiableOn ℂ Φ₁ combNMid)
    (hB1 : ∀ b ∈ edgeStrip (1 / 8), ‖deriv Φ₁ b‖ ≤ B1)
    (hB2 : ∀ b ∈ edgeStrip (1 / 8), ‖deriv (deriv Φ₁) b‖ ≤ B2) :
    AnalyticOnNhd ℂ (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ))
      (edgeStrip (1 / 8)) ∧
    (∀ b ∈ edgeStrip (1 / 8), sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ) ≠ 0) ∧
    (∀ b ∈ edgeStrip (1 / 8),
      ‖deriv (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ)) b /
        (sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ))‖ ≤ ampM0 + B1) ∧
    (∀ b ∈ edgeStrip (1 / 8),
      ‖deriv (fun z => deriv (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ)) z /
        (sechSqProfile z * Complex.exp (Φ₁ z) * z ^ (1 / 2 : ℂ))) b‖ ≤ ampM0' + B2) := by
  have hdiff : ∀ z ∈ combNMid, DifferentiableAt ℂ
      (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ)) z := by
    intro z hz
    have him0 : 0 < z.im := by linarith [(im_pos_of_mem_combNMid hz).1]
    have hΦd : DifferentiableAt ℂ Φ₁ z := (hΦ z hz).differentiableAt (isOpen_combNMid.mem_nhds hz)
    exact ((hasDerivAt_sechSq hz).differentiableAt.mul hΦd.cexp).mul
      (hasDerivAt_sqrt_factor him0).differentiableAt
  have hne : ∀ z ∈ combNMid, sechSqProfile z * Complex.exp (Φ₁ z) * z ^ (1 / 2 : ℂ) ≠ 0 := by
    intro z hz
    have him0 : 0 < z.im := by linarith [(im_pos_of_mem_combNMid hz).1]
    exact mul_ne_zero (mul_ne_zero (sechSq_ne_zero hz) (Complex.exp_ne_zero _))
      (sqrt_factor_ne_zero him0)
  have hc := cosC_pos
  refine ⟨?_, fun b hb => hne b (edgeStrip_eighth_subset hb), fun b hb => ?_, fun b hb => ?_⟩
  · have hD : DifferentiableOn ℂ
        (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ)) combNMid :=
      fun z hz => (hdiff z hz).differentiableWithinAt
    exact (hD.analyticOnNhd isOpen_combNMid).mono edgeStrip_eighth_subset
  · have hbm := edgeStrip_eighth_subset hb
    have := circ_logDeriv_eq hΦ hbm
    rw [logDeriv_apply] at this
    rw [this]
    refine (norm_circLogD_le hB1 hb).trans ?_
    unfold ampM0; linarith
  · have hbm := edgeStrip_eighth_subset hb
    have hev : (fun z => deriv (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ)) z /
        (sechSqProfile z * Complex.exp (Φ₁ z) * z ^ (1 / 2 : ℂ))) =ᶠ[𝓝 b] circLogD Φ₁ := by
      filter_upwards [isOpen_combNMid.mem_nhds hbm] with z hz
      have := circ_logDeriv_eq hΦ hz
      rw [logDeriv_apply] at this
      exact this
    rw [hev.deriv_eq, (hasDerivAt_circLogD hΦ hbm).deriv]
    refine (norm_circLogD'_le hB2 hb).trans ?_
    unfold ampM0'; linarith

/-- **The hypotheses of `SD_V` on the amplitude** (`esd:lemma`): for `Φ₁` holomorphic on
`|Im b - 1/2| < 17/64` with `‖Φ₁'‖ ≤ B₁`, `‖Φ₁''‖ ≤ B₂` on `𝒩_δ` (`δ = 1/8`) and `k = 4πnx/3 ≥ 8`,
the amplitude `A_x = ℰ e^{Φ₁} b^{1/2} (1 + ε_H(kb))` with `ℰ = sech²(π b/2)` is analytic and
nonvanishing on `𝒩_δ`, `|(log A_x)'| ≤ M₀ + B₁` and `|(log A_x)''| ≤ M₀' + B₂` with absolute
`M₀, M₀'`. -/
theorem sdvAmplitude_fields {Φ₁ : ℂ → ℂ} {x n B1 B2 : ℝ} (hk : 8 ≤ sdvWave n x)
    (hΦ : DifferentiableOn ℂ Φ₁ combNMid)
    (hB1 : ∀ b ∈ edgeStrip (1 / 8), ‖deriv Φ₁ b‖ ≤ B1)
    (hB2 : ∀ b ∈ edgeStrip (1 / 8), ‖deriv (deriv Φ₁) b‖ ≤ B2) :
    AnalyticOnNhd ℂ (sdvAmplitude x n sechSqProfile Φ₁ hankelEps) (edgeStrip (1 / 8)) ∧
    (∀ b ∈ edgeStrip (1 / 8), sdvAmplitude x n sechSqProfile Φ₁ hankelEps b ≠ 0) ∧
    (∀ b ∈ edgeStrip (1 / 8),
      ‖deriv (sdvAmplitude x n sechSqProfile Φ₁ hankelEps) b /
        sdvAmplitude x n sechSqProfile Φ₁ hankelEps b‖ ≤ ampM0 + B1) ∧
    (∀ b ∈ edgeStrip (1 / 8),
      ‖deriv (fun z => deriv (sdvAmplitude x n sechSqProfile Φ₁ hankelEps) z /
        sdvAmplitude x n sechSqProfile Φ₁ hankelEps z) b‖ ≤ ampM0' + B2) := by
  set k := sdvWave n x with hk_def
  have hA : sdvAmplitude x n sechSqProfile Φ₁ hankelEps =
      fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ) * ampF4 k b := by
    funext b; rfl
  have hdiff : ∀ z ∈ combNMid, DifferentiableAt ℂ
      (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ) * ampF4 k b) z := by
    intro z hz
    have him0 : 0 < z.im := by linarith [(im_pos_of_mem_combNMid hz).1]
    obtain ⟨_, hkpos⟩ := one_le_norm_mul_of_mem_combNMid hk hz
    have hΦd : DifferentiableAt ℂ Φ₁ z := (hΦ z hz).differentiableAt (isOpen_combNMid.mem_nhds hz)
    exact (((hasDerivAt_sechSq hz).differentiableAt.mul hΦd.cexp).mul
      (hasDerivAt_sqrt_factor him0).differentiableAt).mul (hasDerivAt_ampF4 hkpos).differentiableAt
  have hne : ∀ z ∈ combNMid,
      sechSqProfile z * Complex.exp (Φ₁ z) * z ^ (1 / 2 : ℂ) * ampF4 k z ≠ 0 := by
    intro z hz
    have him0 : 0 < z.im := by linarith [(im_pos_of_mem_combNMid hz).1]
    obtain ⟨hkz, _⟩ := one_le_norm_mul_of_mem_combNMid hk hz
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (sechSq_ne_zero hz) (Complex.exp_ne_zero _))
      (sqrt_factor_ne_zero him0)) (ampF4_ne_zero (by linarith) him0 hkz)
  rw [hA]
  refine ⟨?_, fun b hb => hne b (edgeStrip_eighth_subset hb), fun b hb => ?_, fun b hb => ?_⟩
  · have hD : DifferentiableOn ℂ
        (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ) * ampF4 k b) combNMid :=
      fun z hz => (hdiff z hz).differentiableWithinAt
    exact (hD.analyticOnNhd isOpen_combNMid).mono edgeStrip_eighth_subset
  · have hbm := edgeStrip_eighth_subset hb
    have := amplitude_logDeriv_eq hk hΦ hbm
    rw [logDeriv_apply] at this
    rw [this]
    exact (amplitude_logDeriv_bounds hk hB1 hB2 hb).1
  · have hbm := edgeStrip_eighth_subset hb
    have hev : (fun z => deriv (fun b => sechSqProfile b * Complex.exp (Φ₁ b) * b ^ (1 / 2 : ℂ) *
          ampF4 k b) z /
        (sechSqProfile z * Complex.exp (Φ₁ z) * z ^ (1 / 2 : ℂ) * ampF4 k z)) =ᶠ[𝓝 b]
        ampLogD Φ₁ k := by
      filter_upwards [isOpen_combNMid.mem_nhds hbm] with z hz
      have := amplitude_logDeriv_eq hk hΦ hz
      rw [logDeriv_apply] at this
      exact this
    rw [hev.deriv_eq, (hasDerivAt_ampLogD hk hΦ hbm).deriv]
    exact (amplitude_logDeriv_bounds hk hB1 hB2 hb).2

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.sdvAmplitude_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sdvAmplitude_fields

/-- info: 'FormalResearch.ModularBootstrap.Upper.Design.amplitude_logDeriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms amplitude_logDeriv_bounds

end FormalResearch.ModularBootstrap.Upper.Design
