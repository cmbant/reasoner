module

public import FormalResearch.ModularBootstrap.Upper.Hankel.HankelLaplace

/-!
# Large-argument expansion of `H₀¹`, uniform on the upper half-plane

Source: `CFT/modular_bootstrap/paper/edge_transform_sd.tex`, proof of Lemma `SD_G` (the "standard
uniform large-argument Hankel estimate"); plan item A3 (`UPPER_PLAN.md`), order `p = 0`.

For `Im z > 0`:

`hankel0 z = (2/(π z))^{1/2} e^{i(z - π/4)} (1 + hankelEps z)`, `‖hankelEps z‖ ≤ 1/(4‖z‖)`.

The bound holds for every `z` in the open upper half-plane (not only `|z| ≥ 1`), uniformly up to the
real axis.  Consequently `‖hankel0 z‖ ≤ √(2/π) ‖z‖^{-1/2} e^{-Im z}` for every `z` with `Im z > 0`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Hankel

lemma arg_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < z.arg := by
  rcases (Complex.arg_nonneg_iff.mpr hz.le).lt_or_eq with h | h
  · exact h
  · exfalso
    have := Complex.arg_eq_zero_iff.mp h.symm
    linarith [this.2]

lemma arg_ne_pi_of_im_pos {z : ℂ} (hz : 0 < z.im) : z.arg ≠ π := by
  intro h
  have := (Complex.arg_eq_pi_iff.mp h).2
  linarith

/-- The leading factor `(2/(π z))^{1/2} e^{i(z - π/4)}` of the expansion. -/
noncomputable def hankelLeading (z : ℂ) : ℂ :=
  (2 / ((π : ℂ) * z)) ^ (1 / 2 : ℂ) * Complex.exp (I * (z - (π : ℂ) / 4))

/-- The relative remainder `ε_H(z)` of the large-argument expansion of `H₀¹`. -/
noncomputable def hankelEps (z : ℂ) : ℂ := (hankelR (-I * z) - (√π : ℝ)) / (√π : ℝ)

/-- Prefactor identity (principal branches). -/
lemma hankel_prefactor {z : ℂ} (hz : 0 < z.im) :
    (2 / ((π : ℂ) * I)) * (2 * (-I * z)) ^ (-(1 / 2 : ℂ)) * (√π : ℝ) =
      (2 / ((π : ℂ) * z)) ^ (1 / 2 : ℂ) * Complex.exp (-(I * (π : ℂ) / 4)) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hargp := arg_pos_of_im_pos hz
  have hargpi : z.arg < π := lt_of_le_of_ne (Complex.arg_le_pi z) (arg_ne_pi_of_im_pos hz)
  have hnI : (-I : ℂ) ≠ 0 := by simp
  have hu0 : -I * z ≠ 0 := mul_ne_zero hnI hz0
  have hlog1 : Complex.log (-I * z) = Complex.log z - I * (π / 2) := by
    rw [mul_comm, Complex.log_mul_eq_add_log_iff hz0 hnI |>.mpr, Complex.log_neg_I]
    · ring
    · rw [Complex.arg_neg_I]
      constructor <;> linarith [Real.pi_pos]
  have hlog2 : Complex.log (2 * (-I * z)) = (Real.log 2 : ℂ) + Complex.log (-I * z) := by
    have := Complex.log_ofReal_mul (r := 2) (by norm_num) hu0
    simpa using this
  have hlog3 : Complex.log (2 / ((π : ℂ) * z)) = (Real.log (2 / π) : ℂ) - Complex.log z := by
    have e : (2 : ℂ) / ((π : ℂ) * z) = ((2 / π : ℝ) : ℂ) * z⁻¹ := by
      push_cast; field_simp
    rw [e, Complex.log_ofReal_mul (by positivity) (inv_ne_zero hz0),
      Complex.log_inv _ (arg_ne_pi_of_im_pos hz)]
    ring
  have h2u : (2 : ℂ) * (-I * z) ≠ 0 := mul_ne_zero two_ne_zero hu0
  have h2z : (2 : ℂ) / ((π : ℂ) * z) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact div_ne_zero two_ne_zero (mul_ne_zero this hz0)
  rw [Complex.cpow_def_of_ne_zero h2u, Complex.cpow_def_of_ne_zero h2z, hlog2, hlog1, hlog3]
  have hs2 : Real.exp (-(1 / 2) * Real.log 2) = (√2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_neg]
    congr 1; ring
  have hs3 : Real.exp ((1 / 2) * Real.log (2 / π)) = √(2 / π) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2 / π)]
    congr 1; ring
  have e1 : ((Real.log 2 : ℂ) + (Complex.log z - I * (π / 2))) * (-(1 / 2 : ℂ)) =
      (((-(1 / 2) * Real.log 2 : ℝ)) : ℂ) + (-(1 / 2) * Complex.log z) + I * (π / 4) := by
    push_cast; ring
  have e2 : ((Real.log (2 / π) : ℂ) - Complex.log z) * (1 / 2 : ℂ) =
      (((1 / 2 * Real.log (2 / π) : ℝ)) : ℂ) + (-(1 / 2) * Complex.log z) := by
    push_cast; ring
  have hI : Complex.exp (-(I * π / 2)) = -I := by
    rw [show -(I * (π : ℂ) / 2) = (-(π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [e1, e2]
  simp only [Complex.exp_add]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, hs2, hs3]
  have hsc : (2 / π) * (√2)⁻¹ * √π = √(2 / π) := by
    have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
    rw [Real.sqrt_div (by norm_num)]
    have h2' : (2 : ℝ) = √2 ^ 2 := (Real.sq_sqrt (by norm_num)).symm
    have h3' : π = √π ^ 2 := (Real.sq_sqrt Real.pi_pos.le).symm
    field_simp
    nlinarith [h2', h3']
  have hsc' : ((2 / π : ℝ) : ℂ) * (((√2)⁻¹ : ℝ) : ℂ) * ((√π : ℝ) : ℂ) = ((√(2 / π) : ℝ) : ℂ) := by
    exact_mod_cast hsc
  have hfac : (2 / ((π : ℂ) * I)) = ((2 / π : ℝ) : ℂ) * (-I) := by
    push_cast; field_simp; simp
  calc (2 / ((π : ℂ) * I)) * (((√2)⁻¹ : ℝ) * Complex.exp (-(1 / 2) * Complex.log z) *
        Complex.exp (I * (π / 4)) : ℂ) * ((√π : ℝ) : ℂ)
      = (((2 / π : ℝ) : ℂ) * (((√2)⁻¹ : ℝ) : ℂ) * ((√π : ℝ) : ℂ)) * (-I) *
        Complex.exp (I * (π / 4)) * Complex.exp (-(1 / 2) * Complex.log z) := by
        rw [hfac]; ring
    _ = _ := by
        rw [hsc', ← hI]
        have : Complex.exp (-(I * π / 2)) * Complex.exp (I * ((π : ℂ) / 4)) =
            Complex.exp (-(I * π / 4)) := by
          rw [← Complex.exp_add]; congr 1; ring
        rw [mul_assoc (((√(2 / π) : ℝ) : ℂ)), this]
        ring

lemma neg_I_mul_re {z : ℂ} : (-I * z).re = z.im := by simp

lemma hankel0_eq_leading_mul {z : ℂ} (hz : 0 < z.im) :
    hankel0 z = hankelLeading z * (1 + hankelEps z) := by
  have hw : 0 < (-I * z).re := by rw [neg_I_mul_re]; exact hz
  have hsp : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpf := hankel_prefactor hz
  unfold hankel0 hankelLeading hankelEps
  rw [besselK0_eq hw]
  have e1 : -(-I * z) = I * z := by ring
  have e2 : Complex.exp (I * (z - (π : ℂ) / 4)) =
      Complex.exp (I * z) * Complex.exp (-(I * (π : ℂ) / 4)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2]
  have key : (2 / ((π : ℂ) * I)) * (2 * (-I * z)) ^ (-(1 / 2 : ℂ)) =
      (2 / ((π : ℂ) * z)) ^ (1 / 2 : ℂ) * Complex.exp (-(I * (π : ℂ) / 4)) / ((√π : ℝ) : ℂ) := by
    rw [eq_div_iff hsp]; exact hpf
  calc 2 / (↑π * I) * (Complex.exp (I * z) * (2 * (-I * z)) ^ (-(1 / 2 : ℂ)) * hankelR (-I * z))
      = Complex.exp (I * z) * ((2 / ((π : ℂ) * I)) * (2 * (-I * z)) ^ (-(1 / 2 : ℂ))) *
        hankelR (-I * z) := by ring
    _ = _ := by
        rw [key]
        field_simp
        ring

/-- **Large-argument expansion bound**: `‖ε_H(z)‖ ≤ 1/(4‖z‖)` for every `z` with `Im z > 0`. -/
theorem norm_hankelEps_le {z : ℂ} (hz : 0 < z.im) : ‖hankelEps z‖ ≤ 1 / (4 * ‖z‖) := by
  have hw : 0 ≤ (-I * z).re := by rw [neg_I_mul_re]; exact hz.le
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hw0 : -I * z ≠ 0 := mul_ne_zero (by simp) hz0
  have hnorm : ‖-I * z‖ = ‖z‖ := by simp
  have h := norm_hankelR_sub_le hw hw0
  rw [hnorm] at h
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  unfold hankelEps
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hsp.le, div_le_iff₀ hsp]
  calc _ ≤ √π / (4 * ‖z‖) := h
    _ = _ := by field_simp

lemma norm_hankelLeading {z : ℂ} (hz : 0 < z.im) :
    ‖hankelLeading z‖ = √(2 / π) * ‖z‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-z.im) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2z : (2 : ℂ) / ((π : ℂ) * z) ≠ 0 := div_ne_zero two_ne_zero (mul_ne_zero hpi hz0)
  unfold hankelLeading
  rw [norm_mul, Complex.norm_cpow_of_ne_zero h2z, Complex.norm_exp]
  have hn : ‖(2 : ℂ) / ((π : ℂ) * z)‖ = 2 / (π * ‖z‖) := by
    rw [norm_div, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [hn]
  have him : ((1 / 2 : ℂ)).im = 0 := by simp
  have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by simp
  rw [him, mul_zero, Real.exp_zero, div_one, hre]
  have : (I * (z - (π : ℂ) / 4)).re = -z.im := by simp
  rw [this]
  congr 1
  rw [Real.div_rpow (by norm_num) (by positivity), Real.mul_rpow Real.pi_pos.le hzn.le,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num), Real.rpow_neg hzn.le]
  field_simp

lemma one_add_hankelEps {z : ℂ} : 1 + hankelEps z = hankelR (-I * z) / (√π : ℝ) := by
  have hsp : ((√π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  unfold hankelEps
  field_simp
  ring

lemma norm_one_add_hankelEps_le {z : ℂ} (hz : 0 < z.im) : ‖1 + hankelEps z‖ ≤ 1 := by
  have hw : 0 ≤ (-I * z).re := by rw [neg_I_mul_re]; exact hz.le
  have hsp : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [one_add_hankelEps, norm_div, Complex.norm_real, Real.norm_of_nonneg hsp.le, div_le_one hsp]
  exact norm_hankelR_le hw

/-- **Uniform bound on `H₀¹` on the upper half-plane**:
`‖H₀¹(z)‖ ≤ √(2/π) ‖z‖^{-1/2} e^{-Im z}` for every `z` with `Im z > 0`. -/
theorem norm_hankel0_le {z : ℂ} (hz : 0 < z.im) :
    ‖hankel0 z‖ ≤ √(2 / π) * ‖z‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-z.im) := by
  rw [hankel0_eq_leading_mul hz, norm_mul, norm_hankelLeading hz]
  calc _ ≤ √(2 / π) * ‖z‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-z.im) * 1 :=
        mul_le_mul_of_nonneg_left (norm_one_add_hankelEps_le hz) (by positivity)
    _ = _ := mul_one _

/-- **Large-argument expansion of `H₀¹`** (order `0`), uniform on the open upper half-plane:
`H₀¹(z) = (2/(π z))^{1/2} e^{i(z - π/4)} (1 + ε_H(z))`, `‖ε_H(z)‖ ≤ 1/(4‖z‖)`. -/
theorem hankel0_expansion :
    ∃ ε : ℂ → ℂ, (∀ z : ℂ, 0 < z.im →
        hankel0 z = (2 / ((π : ℂ) * z)) ^ (1 / 2 : ℂ) * Complex.exp (I * (z - (π : ℂ) / 4)) * (1 + ε z)) ∧
      ∀ z : ℂ, 0 < z.im → ‖ε z‖ ≤ 1 / (4 * ‖z‖) :=
  ⟨hankelEps, fun _ hz => hankel0_eq_leading_mul hz, fun _ hz => norm_hankelEps_le hz⟩

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hankel0_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel0_expansion

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.norm_hankel0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_hankel0_le

end FormalResearch.ModularBootstrap.Upper.Hankel
