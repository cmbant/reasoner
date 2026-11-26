module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroSlopeIBP

/-!
# The derivative of the amplitude `a` (FIVE-0, `ctu:jets`, step 2'')

Explicit derivatives of `x_T`, `v_T`, `b_T`, `Λ_T` and `a`, and the decomposition of `a'(τ)/sinh(πτ)`, `τ > 0`, into
`x_A/8 + v_A/8 + π(1/c + 1/(1+c) - 2/√(c(1+c))) + (π tanh(πτ/4) ·5/8 + π tanh(πτ/2)·3/8 - π tanh(πτ)/2)/sinh(πτ)`,
`c = cosh(πτ)`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma hasDerivAt_arg (k t : ℝ) : HasDerivAt (fun t : ℝ => π * t / k) (π / k) t := by
  simpa using ((hasDerivAt_id t).const_mul π).div_const k

lemma hasDerivAt_cosh_arg (k t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.cosh (π * t / k)) (Real.sinh (π * t / k) * (π / k)) t :=
  (hasDerivAt_arg k t).cosh

lemma hasDerivAt_sinh_arg (k t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sinh (π * t / k)) (Real.cosh (π * t / k) * (π / k)) t :=
  (hasDerivAt_arg k t).sinh

/-- `x_T'(τ) = sinh(πτ)/(2 √c √(1+c))`. -/
noncomputable def xD (t : ℝ) : ℝ :=
  Real.sinh (π * t) / (2 * (√(Real.cosh (π * t)) * √(1 + Real.cosh (π * t))))

lemma hasDerivAt_xT (t : ℝ) : HasDerivAt xT (xD t) t := by
  have hpi := Real.pi_pos
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have h1 : HasDerivAt (fun t : ℝ => Real.cosh (π * t)) (Real.sinh (π * t) * π) t := by
    simpa using hasDerivAt_cosh_arg 1 t
  have h2 := (h1.sqrt hc.ne').arsinh.div_const π
  have hq : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr hc
  have hqq : √(Real.cosh (π * t)) ^ 2 = Real.cosh (π * t) := Real.sq_sqrt hc.le
  have hp : 0 < √(1 + Real.cosh (π * t)) := Real.sqrt_pos.mpr (by linarith)
  refine h2.congr_deriv ?_
  rw [hqq, smul_eq_mul]
  unfold xD
  field_simp

/-- `v_T'(τ) = √2 cosh(πτ/2)/(2√c)`. -/
noncomputable def vD (t : ℝ) : ℝ := √2 * Real.cosh (π * t / 2) / (2 * √(Real.cosh (π * t)))

lemma one_add_two_sinh_sq (t : ℝ) : 1 + (√2 * Real.sinh (π * t / 2)) ^ 2 = Real.cosh (π * t) := by
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have h : π * t = 2 * (π * t / 2) := by ring
  rw [h, Real.cosh_two_mul, ← h]
  have := Real.cosh_sq (π * t / 2)
  nlinarith

lemma hasDerivAt_vT (t : ℝ) : HasDerivAt vT (vD t) t := by
  have hpi := Real.pi_pos
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have h1 : HasDerivAt (fun t : ℝ => √2 * Real.sinh (π * t / 2)) (√2 * (Real.cosh (π * t / 2) * (π / 2))) t :=
    (hasDerivAt_sinh_arg 2 t).const_mul _
  have h2 := h1.arsinh.div_const π
  refine h2.congr_deriv ?_
  rw [one_add_two_sinh_sq, smul_eq_mul]
  unfold vD
  have hq : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr hc
  field_simp

lemma hasDerivAt_bT (t : ℝ) : HasDerivAt bT (vT t * vD t / bT t) t := by
  have h1 : HasDerivAt (fun t : ℝ => vT t ^ 2 + 1 / 4) (2 * vT t * vD t) t := by
    have := ((hasDerivAt_vT t).pow 2).add_const (1 / 4)
    simpa using this
  have hne : vT t ^ 2 + 1 / 4 ≠ 0 := by positivity
  have h2 := h1.sqrt hne
  refine h2.congr_deriv ?_
  have : √(vT t ^ 2 + 1 / 4) = bT t := rfl
  rw [this]
  have hb := bT_pos t
  field_simp

/-- `Λ_T'` -/
noncomputable def lD (t : ℝ) : ℝ :=
  Real.exp (-(4 * π * xT t)) * (4 * π * xD t) / (1 - Real.exp (-(4 * π * xiStar)))

lemma hasDerivAt_lamT (t : ℝ) : HasDerivAt lamT (lD t) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(4 * π * xT t)) (-(4 * π * xD t)) t :=
    ((hasDerivAt_xT t).const_mul (4 * π)).neg
  have h2 := ((h1.exp).const_sub 1).div_const (1 - Real.exp (-(4 * π * xiStar)))
  refine h2.congr_deriv ?_
  unfold lD
  ring

/-- The derivative of the amplitude. -/
noncomputable def aD (t : ℝ) : ℝ :=
  (1 / 4) * (xD t / xT t) + (1 / 4) * (vT t * vD t / bT t / bT t) +
    2 * (lD t / lamT t) + (5 / 2) * (Real.sinh (π * t / 4) * (π / 4) / Real.cosh (π * t / 4)) +
    (3 / 4) * (Real.sinh (π * t / 2) * (π / 2) / Real.cosh (π * t / 2)) -
    (1 / 2) * (Real.sinh (π * t) * π / Real.cosh (π * t))

lemma hasDerivAt_aAmp (t : ℝ) : HasDerivAt aAmp (aD t) t := by
  have hlog4 := (hasDerivAt_cosh_arg 4 t).log (Real.cosh_pos _).ne'
  have hlog2 := (hasDerivAt_cosh_arg 2 t).log (Real.cosh_pos _).ne'
  have hlog1 : HasDerivAt (fun t : ℝ => Real.log (Real.cosh (π * t)))
      (Real.sinh (π * t) * π / Real.cosh (π * t)) t := by
    have := (hasDerivAt_cosh_arg 1 t).log (Real.cosh_pos _).ne'
    simpa using this
  have hx := ((hasDerivAt_xT t).log (xT_pos t).ne').const_mul (1 / 4)
  have hb := ((hasDerivAt_bT t).log (bT_pos t).ne').const_mul (1 / 4)
  have hl := ((hasDerivAt_lamT t).log (lamT_pos t).ne').const_mul 2
  have h := ((((((hx.add hb).sub_const ((1 / 2) * Real.log xiStar)).add hl).add
    (hlog4.const_mul (5 / 2))).add (hlog2.const_mul (3 / 4))).sub (hlog1.const_mul (1 / 2)))
  unfold aAmp aD
  convert h using 1

lemma sinh_arg_ne {t : ℝ} (ht : t ≠ 0) (k : ℝ) (hk : 0 < k) : Real.sinh (π * t / k) ≠ 0 := by
  intro h
  have := Real.sinh_eq_zero.mp h
  have hpi := Real.pi_pos
  apply ht
  field_simp at this
  nlinarith

lemma sinh_double (t : ℝ) : Real.sinh (π * t) = 2 * Real.sinh (π * t / 2) * Real.cosh (π * t / 2) := by
  rw [← Real.sinh_two_mul]; congr 1; ring

lemma sinh_double' (t : ℝ) : Real.sinh (π * t / 2) = 2 * Real.sinh (π * t / 4) * Real.cosh (π * t / 4) := by
  rw [← Real.sinh_two_mul]; congr 1; ring

lemma cosh_double (t : ℝ) : Real.cosh (π * t) = 2 * Real.cosh (π * t / 2) ^ 2 - 1 := by
  have h2 : Real.cosh (π * t) = Real.cosh (2 * (π * t / 2)) := by congr 1; ring
  rw [h2, Real.cosh_two_mul]
  nlinarith [Real.cosh_sq (π * t / 2)]

/-- (1) the `x`-part -/
lemma piece_x {t : ℝ} (ht : t ≠ 0) :
    (1 / 4) * (xD t / xT t) / Real.sinh (π * t) = xA t / 8 := by
  have hs : Real.sinh (π * t) ≠ 0 := by simpa using sinh_arg_ne ht 1 one_pos
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hq : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr hc
  have hp : 0 < √(1 + Real.cosh (π * t)) := Real.sqrt_pos.mpr (by linarith)
  have hx := xT_pos t
  unfold xD xA
  rw [Real.sqrt_mul hc.le]
  field_simp
  norm_num

/-- (2) the `b`-part -/
lemma piece_b {t : ℝ} (ht : t ≠ 0) :
    (1 / 4) * (vT t * vD t / bT t / bT t) / Real.sinh (π * t) = vA t / 8 := by
  have hs : Real.sinh (π * t) ≠ 0 := by simpa using sinh_arg_ne ht 1 one_pos
  have hs2 : Real.sinh (π * t / 2) ≠ 0 := sinh_arg_ne ht 2 two_pos
  have hc : 0 < Real.cosh (π * t) := Real.cosh_pos _
  have hq : 0 < √(Real.cosh (π * t)) := Real.sqrt_pos.mpr hc
  have hch : 0 < Real.cosh (π * t / 2) := Real.cosh_pos _
  have h2 : 0 < √2 := by positivity
  have hb : bT t ^ 2 = vT t ^ 2 + 1 / 4 := Real.sq_sqrt (by positivity)
  have hbp := bT_pos t
  have hv : 0 < vT t ^ 2 + 1 / 4 := by positivity
  have hsq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold vD vA
  rw [sinh_double t, ← hb]
  field_simp
  have h22 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [h22]; ring

/-- (3) the `Λ`-part. -/
lemma piece_lam {t : ℝ} (ht : t ≠ 0) :
    2 * (lD t / lamT t) / Real.sinh (π * t) =
      π / Real.cosh (π * t) + π / (1 + Real.cosh (π * t)) -
        2 * (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t)))) := by
  have hpi := Real.pi_pos
  have hs : Real.sinh (π * t) ≠ 0 := by simpa using sinh_arg_ne ht 1 one_pos
  set c := Real.cosh (π * t) with hcdef
  have hc : 0 < c := Real.cosh_pos _
  set s := √c with hsdef
  set w := √(1 + c) with hwdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hc
  have hw0 : 0 < w := Real.sqrt_pos.mpr (by linarith)
  have hss : s * s = c := Real.mul_self_sqrt hc.le
  have hww : w * w = 1 + c := Real.mul_self_sqrt (by linarith)
  have hX : π * xT t = Real.arsinh s := by
    rw [show xT t = Real.arsinh s / π from rfl]; field_simp
  have hE : Real.exp (-(4 * π * xT t)) = ((s + w)⁻¹) ^ 4 := by
    have h1 : -(4 * π * xT t) = -(4 * (π * xT t)) := by ring
    rw [h1, hX, Real.exp_neg, show 4 * Real.arsinh s = ((4 : ℕ) : ℝ) * Real.arsinh s by norm_num,
      Real.exp_nat_mul, Real.exp_arsinh, inv_pow]
    have e : √(1 + s ^ 2) = w := by rw [sq, hss]
    rw [e]
  have hden : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
    rw [sub_pos, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr
    have := xiStar_pos; nlinarith
  have hdp : 1 - Real.exp (-(4 * π * xT t)) ≠ 0 := by
    rw [hE]
    have : ((s + w)⁻¹) ^ 4 < 1 := by
      have h1 : 1 < s + w := by nlinarith
      exact pow_lt_one₀ (by positivity) ((inv_lt_one₀ (by positivity)).mpr h1) (by norm_num)
    linarith
  have hlam : lD t / lamT t = Real.exp (-(4 * π * xT t)) * (4 * π * xD t) / (1 - Real.exp (-(4 * π * xT t))) := by
    unfold lD lamT
    field_simp
  rw [hlam, hE]
  have hxD : xD t = Real.sinh (π * t) / (2 * (s * w)) := rfl
  rw [hxD, Real.sqrt_mul hc.le, ← hsdef, ← hwdef]
  have hsw : s + w ≠ 0 := by positivity
  have hwa : w * w - s * s = 1 := by linarith
  have hp1 : ((s + w)⁻¹) ^ 4 ≠ 1 := by
    intro h
    have : ((s + w)⁻¹) ^ 4 < 1 := by
      have h1 : 1 < s + w := by nlinarith
      exact pow_lt_one₀ (by positivity) ((inv_lt_one₀ (by positivity)).mpr h1) (by norm_num)
    linarith
  rw [show 1 + c = w * w from hww.symm, show c = s * s from hss.symm]
  field_simp
  have h1 : 1 < s + w := by nlinarith
  have h4 : 1 < (s + w) ^ 4 := one_lt_pow₀ h1 (by norm_num)
  have hp4 : (s + w) ^ 4 - 1 ≠ 0 := by linarith
  rw [div_eq_iff hp4]
  linear_combination (-(w * w - s * s + 1) * (s + w) ^ 2) * hwa

/-- `π/(4 cosh(πt/2) cosh²(πt/4))`. -/
noncomputable def g4 (t : ℝ) : ℝ := (π / 4) / (Real.cosh (π * t / 2) * Real.cosh (π * t / 4) ^ 2)

/-- `π/(2 cosh²(πt/2))`. -/
noncomputable def g5 (t : ℝ) : ℝ := (π / 2) / Real.cosh (π * t / 2) ^ 2

lemma piece_4 {t : ℝ} (ht : t ≠ 0) :
    (5 / 2) * (Real.sinh (π * t / 4) * (π / 4) / Real.cosh (π * t / 4)) / Real.sinh (π * t) =
      (5 / 8) * g4 t := by
  have hs4 : Real.sinh (π * t / 4) ≠ 0 := sinh_arg_ne ht 4 (by norm_num)
  have h4 := Real.cosh_pos (π * t / 4)
  have h2 := Real.cosh_pos (π * t / 2)
  unfold g4
  rw [sinh_double t, sinh_double' t]
  have : Real.sinh (π * t / 2) ≠ 0 := sinh_arg_ne ht 2 two_pos
  field_simp
  ring

lemma piece_5 {t : ℝ} (ht : t ≠ 0) :
    (3 / 4) * (Real.sinh (π * t / 2) * (π / 2) / Real.cosh (π * t / 2)) / Real.sinh (π * t) =
      (3 / 8) * g5 t := by
  have h2 := Real.cosh_pos (π * t / 2)
  have : Real.sinh (π * t / 2) ≠ 0 := sinh_arg_ne ht 2 two_pos
  unfold g5
  rw [sinh_double t]
  field_simp
  ring

lemma piece_6 {t : ℝ} (ht : t ≠ 0) :
    (1 / 2) * (Real.sinh (π * t) * π / Real.cosh (π * t)) / Real.sinh (π * t) =
      (1 / 2) * (π / Real.cosh (π * t)) := by
  have hs : Real.sinh (π * t) ≠ 0 := by simpa using sinh_arg_ne ht 1 one_pos
  have := Real.cosh_pos (π * t)
  field_simp

/-- **Decomposition of `a'(τ)/sinh(πτ)`**. -/
lemma aD_div {t : ℝ} (ht : t ≠ 0) :
    aD t / Real.sinh (π * t) = xA t / 8 + vA t / 8 +
      ((1 / 2) * (π / Real.cosh (π * t)) + π / (1 + Real.cosh (π * t)) -
        2 * (π / √(Real.cosh (π * t) * (1 + Real.cosh (π * t)))) +
        (5 / 8) * g4 t + (3 / 8) * g5 t) := by
  have e1 := piece_x ht
  have e2 := piece_b ht
  have e3 := piece_lam ht
  have e4 := piece_4 ht
  have e5 := piece_5 ht
  have e6 := piece_6 ht
  unfold aD
  rw [sub_div, add_div, add_div, add_div, add_div, e1, e2, e3, e4, e5, e6]
  ring

end FormalResearch.ModularBootstrap.FiveTerm
