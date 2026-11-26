module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterTheta
public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroSlit

/-!
# FIVE-S, S1 (bridge): `G_outer(iy) = W_slit(y) e^{iθ_out(y)}` and the soft properties of `θ_out`

The modulus is `gout_modulus` (`VirasoroSlit`).  Here: the phase.  Each factor of `Gout` at `z = iy` is put in polar form
(`polar_re_pos`, `cpow_polar`): `(1 - iy)^{1/2}` has phase `-(1/2) arctan y`, `(1 + iy)^{-2}` has phase `-2 arctan y`,
`slitVal^{-1/4}` has phase `+(1/4) arctan(2 v_x)`, and `exp h̄_a(iτ)` has phase `Im h̄_a(iτ)`; the total is `thetaOutT τ`
(`τ = slitTau y`).  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- Polar form of a complex number with positive real part. -/
lemma polar_re_pos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ((a : ℂ) + (b : ℂ) * Complex.I) =
      ((√(a ^ 2 + b ^ 2) : ℝ) : ℂ) * Complex.exp (((Real.arctan (b / a) : ℝ) : ℂ) * Complex.I) := by
  have hq : 0 < 1 + (b / a) ^ 2 := by positivity
  have hs : 0 < √(1 + (b / a) ^ 2) := Real.sqrt_pos.mpr hq
  have hc : Real.cos (Real.arctan (b / a)) = 1 / √(1 + (b / a) ^ 2) := Real.cos_arctan _
  have hsn : Real.sin (Real.arctan (b / a)) = (b / a) / √(1 + (b / a) ^ 2) := Real.sin_arctan _
  have hr : √(a ^ 2 + b ^ 2) = a * √(1 + (b / a) ^ 2) := by
    rw [show a ^ 2 + b ^ 2 = a ^ 2 * (1 + (b / a) ^ 2) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq ha.le]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hsn, hr]
  have hs' : (√(1 + (b / a) ^ 2) : ℝ) ≠ 0 := hs.ne'
  apply Complex.ext
  · simp
    field_simp
  · simp
    field_simp

/-- Real powers of a number in polar form with argument in `(-π, π]`. -/
lemma cpow_polar {r φ : ℝ} (hr : 0 < r) (hφ : -π < φ) (hφ' : φ ≤ π) (c : ℝ) :
    ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ^ (c : ℂ) =
      ((r ^ c : ℝ) : ℂ) * Complex.exp (((φ * c : ℝ) : ℂ) * Complex.I) := by
  have hne : ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ≠ 0 := by
    apply mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
  have harg : Complex.arg ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) = φ := by
    rw [Complex.arg_real_mul _ hr, Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨hφ, hφ'⟩
  have hnorm : ‖(r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hr]
  have hlog : Complex.log ((r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((Real.log r : ℝ) : ℂ) + (φ : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.log_re, hnorm]; simp
    · rw [Complex.log_im, harg]; simp
  rw [Complex.cpow_def_of_ne_zero hne, hlog, add_mul, Complex.exp_add, Real.rpow_def_of_pos hr]
  push_cast
  rw [mul_comm (Real.log r : ℂ) (c : ℂ), mul_comm ((φ : ℂ) * Complex.I) (c : ℂ)]
  ring_nf

lemma thetaOut_eq_thetaOutT {y : ℝ} : thetaOut y = thetaOutT (slitTau y) := rfl

/-- **`OuterS1` (1), bridge** (`cts:main` Piece 3): `G_outer(iy) = W_slit(y) e^{iθ_out(y)}` on `(0,1)`.
Class: proved. -/
theorem gout_polar {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Gout (Complex.I * (y : ℂ)) = (Wslit y : ℂ) * Complex.exp (Complex.I * (thetaOut y : ℂ)) := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  set τ : ℝ := slitTau y with hτ
  have hτ0 : 0 ≤ τ := slitTau_nonneg hy0.le
  have htanh : Real.tanh (π * τ / 4) = y := tanh_slitTau hy'
  have hv : vT τ = vOf y := by rw [← htanh, vOf_tanh hτ0]
  have hsI : sInv (Complex.I * (y : ℂ)) = (τ : ℂ) * Complex.I := sInv_slit hy'
  set N : ℂ := hbarA aAmp ((τ : ℂ) * Complex.I) with hN
  have hth : thetaOut y = N.im - (5 / 2) * Real.arctan y + (1 / 4) * Real.arctan (2 * vOf y) := by
    show thetaOutT τ = _
    unfold thetaOutT
    rw [htanh, hv]
  have hx := xOf_pos hy'
  have hpi := Real.pi_pos
  have h1y : (0 : ℝ) < 1 + y ^ 2 := by positivity
  have hs1 : 0 < √(1 + y ^ 2) := Real.sqrt_pos.mpr h1y
  -- polar forms of the three factors
  have hB : (1 : ℂ) - Complex.I * (y : ℂ) =
      ((√(1 + y ^ 2) : ℝ) : ℂ) * Complex.exp (((-Real.arctan y : ℝ) : ℂ) * Complex.I) := by
    have := polar_re_pos (a := 1) one_pos (-y)
    rw [div_one, Real.arctan_neg] at this
    simp only [sq] at this ⊢
    rw [show (1 : ℂ) - Complex.I * (y : ℂ) = ((1 : ℝ) : ℂ) + (((-y : ℝ)) : ℂ) * Complex.I by
      push_cast; ring]
    convert this using 3
    ring_nf
  have hC : (1 : ℂ) + Complex.I * (y : ℂ) =
      ((√(1 + y ^ 2) : ℝ) : ℂ) * Complex.exp (((Real.arctan y : ℝ) : ℂ) * Complex.I) := by
    have := polar_re_pos (a := 1) one_pos y
    rw [div_one] at this
    rw [show (1 : ℂ) + Complex.I * (y : ℂ) = ((1 : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    convert this using 3
    simp [sq]
  -- slitVal
  set A : ℝ := Real.arsinh (√(uSlit y - 1)) with hA
  set B : ℝ := Real.arsinh (√(uSlit y)) with hB'
  have hBpos : 0 < B := by
    have := uSlit_gt_one hy0 hy1
    exact Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr (by linarith))
  have hvA : vOf y = A / π := rfl
  have hsl : slitVal y = ((√((π / 2) ^ 2 + (-A) ^ 2) / B : ℝ) : ℂ) *
      Complex.exp (((-Real.arctan (2 * vOf y) : ℝ) : ℂ) * Complex.I) := by
    have h := polar_re_pos (a := π / 2) (by positivity) (-A)
    have hat : Real.arctan (-A / (π / 2)) = -Real.arctan (2 * vOf y) := by
      rw [← Real.arctan_neg]; congr 1; rw [hvA]; field_simp
    rw [hat] at h
    unfold slitVal
    rw [← hA, ← hB']
    have hnum : ((π : ℂ) / 2 - Complex.I * (A : ℂ)) = (((π / 2 : ℝ) : ℂ) + ((-A : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [hnum, h]
    push_cast
    field_simp
  set ρ : ℝ := √((π / 2) ^ 2 + (-A) ^ 2) / B with hρ
  have hρpos : 0 < ρ := by
    have : 0 < (π / 2) ^ 2 + (-A) ^ 2 := by positivity
    exact div_pos (Real.sqrt_pos.mpr this) hBpos
  have harc : |Real.arctan (2 * vOf y)| < π / 2 := by
    rw [abs_lt]; exact ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have harc' : |Real.arctan y| < π / 2 := by
    rw [abs_lt]; exact ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hacy := abs_lt.mp harc'
  have hacv := abs_lt.mp harc
  -- powers
  have e1 : ((1 : ℂ) - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ) =
      (((√(1 + y ^ 2)) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp ((((-Real.arctan y) * (1 / 2) : ℝ) : ℂ) * Complex.I) := by
    have := cpow_polar hs1 (φ := -Real.arctan y) (by linarith) (by linarith) (1 / 2)
    rw [hB]
    simpa using this
  have e3 : (qBd (Complex.I * (y : ℂ))) ^ (-(1 / 4 : ℂ)) =
      ((ρ ^ (-(1 / 4) : ℝ) : ℝ) : ℂ) *
        Complex.exp ((((-Real.arctan (2 * vOf y)) * (-(1 / 4)) : ℝ) : ℂ) * Complex.I) := by
    have := cpow_polar hρpos (φ := -Real.arctan (2 * vOf y)) (by linarith) (by linarith) (-(1 / 4))
    rw [qBd_slit hy', hsl]
    simpa using this
  have e2 : ((1 : ℂ) + Complex.I * (y : ℂ)) ^ 2 =
      (((√(1 + y ^ 2)) ^ 2 : ℝ) : ℂ) * Complex.exp (((2 * Real.arctan y : ℝ) : ℂ) * Complex.I) := by
    rw [hC, mul_pow, ← Complex.exp_nat_mul]
    push_cast
    congr 2; ring
  have hexpN : Complex.exp N = ((Real.exp N.re : ℝ) : ℂ) * Complex.exp ((N.im : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.re_add_im N, Complex.exp_add]
    rw [Complex.ofReal_exp]
  -- assemble
  set P : ℝ := Real.exp N.re * (√(1 + y ^ 2)) ^ (1 / 2 : ℝ) / (√(1 + y ^ 2)) ^ 2 * ρ ^ (-(1 / 4) : ℝ)
    with hP
  have hG : Gout (Complex.I * (y : ℂ)) = (P : ℂ) * Complex.exp (Complex.I * (thetaOut y : ℂ)) := by
    unfold Gout
    rw [hsI, ← hN, e1, e2, e3, hexpN]
    have hexpθ : Complex.exp (Complex.I * (thetaOut y : ℂ)) =
        Complex.exp ((N.im : ℂ) * Complex.I) * Complex.exp ((((-Real.arctan y) * (1 / 2) : ℝ) : ℂ) * Complex.I) /
          Complex.exp (((2 * Real.arctan y : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((((-Real.arctan (2 * vOf y)) * (-(1 / 4)) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_sub, ← Complex.exp_add]
      congr 1
      rw [hth]; push_cast; ring
    have hnz : (((√(1 + y ^ 2)) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos hs1 2).ne'
    rw [hexpθ, hP]
    push_cast
    field_simp
  rw [hG]
  have hnorm : ‖Gout (Complex.I * (y : ℂ))‖ = Wslit y := gout_modulus hy'
  have hPnn : 0 ≤ P := by
    rw [hP]; have := Real.exp_pos N.re
    positivity
  have : P = Wslit y := by
    rw [← hnorm, hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hPnn]
    have : ‖Complex.exp (Complex.I * (thetaOut y : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one]
  rw [this]

private lemma artanh_odd (y : ℝ) : Real.artanh (-y) = -Real.artanh y := by
  by_cases hy : y ∈ Ioo (-1 : ℝ) 1
  · have h1 : -y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    rw [Real.artanh_eq_half_log h1, Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩]
    have : (1 + -y) / (1 - -y) = ((1 + y) / (1 - y))⁻¹ := by
      rw [inv_div]; ring_nf
    rw [this, Real.log_inv]; ring
  · have h0 : Real.artanh y = 0 := by
      rw [Real.artanh_eq_zero_iff]
      simp only [mem_Ioo, not_and_or, not_lt] at hy
      rcases hy with h | h
      · left; exact h
      · right; right; exact h
    have h0' : Real.artanh (-y) = 0 := by
      rw [Real.artanh_eq_zero_iff]
      simp only [mem_Ioo, not_and_or, not_lt] at hy
      rcases hy with h | h
      · right; right; linarith
      · left; linarith
    rw [h0, h0']; simp

private lemma continuousOn_artanh : ContinuousOn Real.artanh (Ioo (-1 : ℝ) 1) := by
  intro x hx
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have h2 : 0 < (1 + x) / (1 - x) := div_pos (by linarith [hx.1]) h1
  unfold Real.artanh
  have hc : ContinuousAt (fun x : ℝ => Real.log √((1 + x) / (1 - x))) x := by
    apply ContinuousAt.log
    · exact (continuousAt_const.add continuousAt_id |>.div (continuousAt_const.sub continuousAt_id) h1.ne').sqrt
    · exact (Real.sqrt_pos.mpr h2).ne'
  exact hc.continuousWithinAt

/-- **`OuterS1` (1), soft properties**: `θ_out` is odd, vanishes at `0` and is continuous on `(-1,1)`.
Class: proved. -/
theorem thetaOut_soft :
    thetaOut 0 = 0 ∧ (∀ y, thetaOut (-y) = -thetaOut y) ∧ ContinuousOn thetaOut (Ioo (-1 : ℝ) 1) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold thetaOut; rw [Real.artanh_zero, mul_zero]; exact thetaOutT_zero
  · intro y
    unfold thetaOut
    rw [artanh_odd, mul_neg]; exact thetaOutT_neg _
  · obtain ⟨C, -, Θ1, -, hd1, -⟩ := thetaOutT_data
    have hc : Continuous thetaOutT := continuous_iff_continuousAt.mpr fun τ => (hd1 τ).continuousAt
    exact hc.comp_continuousOn (continuousOn_artanh.const_smul (4 / π))

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.thetaOut_soft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms thetaOut_soft

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.gout_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gout_polar

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip
