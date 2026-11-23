module

public import FormalResearch.ModularBootstrap.FixedWeightBand.StirlingW
public import FormalResearch.ModularBootstrap.ComplexBessel.LemmaS2

/-!
# Modulus of the Mellin Kernel at Weight `w` (`vlo:S2`, kernel identity)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, Lemma S2 (`vlo:S2`), first display
of the proof: "adding `B + Re J + L(x)` in `vlo:stirling`, the kernel of `e^{-c'B} m_g` against
`g V dt` has modulus `|S|^{-1} |2π/(3ω)|^{(w-1)/2} A₂(x) e^{-c' D(x_*, x)}`".

For `z = w/2 + c' ω`, `Re ω > 0`, `t > 0` and `x = √(3t/c')`:

* `norm_kernel_eq_W`: `|(2π)^z t^{z-1} / Γ(z)| = |S^{(w)}_{c'}(ω)|^{-1} (2π x²/(3|ω|))^{(w-1)/2}
  t^{-1/2} e^{c' (B(ω) + L(x) - D(3 Re ω/π, x))}` (exact; `D` is the Legendre divergence).
* `kernel_div_eq_W`: if `V = ρ (2x)^{w-1} A_s(c' L(x))` (the Cardy asymptote shape) then
  `|(2π)^z t^{z-1} / Γ(z)| / V = |S|^{-1} (π/(6|ω|))^{(w-1)/2} e^{c' B} e^{-c' D(3 Re ω/π, x)} (2π/(√x ρ))`:
  the factor `(2x)^{w-1}` of `V` cancels the `x^{w-1}` of the Stirling prefactor identically.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open ComplexBessel

/-! ### Exponent bookkeeping (weight free) -/

lemma re_stirlingJ_ofReal_W {ω : ℂ} {x : ℝ} (hx : 0 < x) :
    (stirlingJ ω (x : ℂ)).re =
      ω.re * (Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log x) -
        ω.im * ω.arg := by
  have hr_pos : 0 < 3 / (2 * Real.pi * Real.exp 1) := by positivity
  have harg_eq : (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))).arg = ω.arg := by
    rw [show 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) =
        ((3 / (2 * Real.pi * Real.exp 1) : ℝ) : ℂ) * ω by push_cast; ring]
    exact Complex.arg_real_mul ω hr_pos
  have hnorm_eq : ‖3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))‖ =
      3 * ‖ω‖ / (2 * Real.pi * Real.exp 1) := by
    simp only [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg (Real.exp_pos 1).le]
  have hlog1_re : (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)))).re =
      Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) := by
    rw [Complex.log_re, hnorm_eq]
  have hlog1_im : (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)))).im = ω.arg := by
    rw [Complex.log_im, harg_eq]
  have hlog2 : Complex.log (x : ℂ) = (Real.log x : ℂ) := (Complex.ofReal_log hx.le).symm
  unfold stirlingJ
  rw [Complex.mul_re, Complex.sub_re, Complex.sub_im, hlog1_re, hlog1_im, hlog2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul, add_zero]

/-- `B(ω) + Re J(ω; x) + L(x) = D(3 Re ω/π, x)` for `x > 0` (weight free). -/
lemma exponent_identity_W {ω : ℂ} (hω_re : 0 < ω.re) {x : ℝ} (hx : 0 < x) :
    crudeExponentB ω + (stirlingJ ω (x : ℂ)).re + Bessel.besselL x =
      crudeDivergenceD (3 * ω.re / Real.pi) x := by
  rw [re_stirlingJ_ofReal_W hx]
  unfold crudeExponentB Bessel.besselL crudeDivergenceD
  have hω_norm : 0 < ‖ω‖ := lt_of_lt_of_le hω_re (Complex.re_le_norm ω)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hexp1 : 0 < Real.exp 1 := Real.exp_pos 1
  have hlog_sum : Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) +
      Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log x =
      2 * Real.log ((3 * ω.re / Real.pi) / x) - 1 := by
    have hprod : (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) * (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) =
        (3 * ω.re / Real.pi) ^ 2 / Real.exp 1 := by
      field_simp [hpi.ne', hω_norm.ne', hexp1.ne']
      ring
    rw [← Real.log_mul (by positivity) (by positivity), hprod,
      Real.log_div (by positivity) hexp1.ne', Real.log_exp,
      Real.log_pow, Real.log_div (by positivity) hx.ne']
    push_cast; ring
  have hlog_neg : Real.log (x / (3 * ω.re / Real.pi)) =
      -Real.log ((3 * ω.re / Real.pi) / x) := by
    rw [← Real.log_inv, inv_div]
  rw [hlog_neg]
  calc ω.re * Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) - ω.re + ω.im * ω.arg +
        (ω.re * (Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log x) -
          ω.im * ω.arg) + 2 * Real.pi * x / 3
      = ω.re * (Real.log (6 * ω.re ^ 2 / (Real.pi * ‖ω‖)) +
          Real.log (3 * ‖ω‖ / (2 * Real.pi * Real.exp 1)) - 2 * Real.log x) - ω.re +
          2 * Real.pi * x / 3 := by ring
    _ = ω.re * (2 * Real.log ((3 * ω.re / Real.pi) / x) - 1) - ω.re +
          2 * Real.pi * x / 3 := by rw [hlog_sum]
    _ = (2 * Real.pi / 3) * (x - 3 * ω.re / Real.pi -
          3 * ω.re / Real.pi * -Real.log ((3 * ω.re / Real.pi) / x)) := by
        field_simp [hpi.ne']; ring

/-! ### Modulus of the Stirling prefactor -/

lemma norm_stirlingPrefW_inv {w : ℕ} {ω : ℂ} (hω : ω ≠ 0) {x : ℝ} (hx : 0 < x) :
    ‖(stirlingPrefW w ω (x : ℂ))⁻¹‖ =
      (2 * Real.pi * x ^ 2 / (3 * ‖ω‖)) ^ (((w : ℝ) - 1) / 2) := by
  have hbase_ne : 3 * ω / (2 * (Real.pi : ℂ) * (x : ℂ) ^ 2) ≠ 0 := by
    have : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    exact div_ne_zero (mul_ne_zero three_ne_zero hω)
      (mul_ne_zero (mul_ne_zero two_ne_zero hpi) (pow_ne_zero 2 this))
  have hnorm_base : ‖3 * ω / (2 * (Real.pi : ℂ) * (x : ℂ) ^ 2)‖ =
      3 * ‖ω‖ / (2 * Real.pi * x ^ 2) := by
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hx.le]
  unfold stirlingPrefW
  rw [norm_inv, Complex.norm_cpow_of_ne_zero hbase_ne, hnorm_base]
  have hre : ((((w : ℂ) - 1) / 2 : ℂ)).re = ((w : ℝ) - 1) / 2 := by
    simp
  have him : ((((w : ℂ) - 1) / 2 : ℂ)).im = 0 := by simp
  rw [hre, him, mul_zero, Real.exp_zero, div_one, ← Real.inv_rpow (by positivity), inv_div]

/-! ### The kernel modulus -/

/-- **Kernel modulus at weight `w`** (`vlo:S2`, proof, first display): for `c' > 0`, `Re ω > 0`,
`t > 0`, `x = √(3t/c')`,
`|(2π)^z t^{z-1}/Γ(z)| = |S^{-1}| (2π x²/(3|ω|))^{(w-1)/2} t^{-1/2} e^{c'(B + L(x) - D(x_*, x))}`
with `z = w/2 + c' ω`, `x_* = 3 Re ω/π`. -/
theorem norm_kernel_eq_W {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 < ω.re) {t : ℝ} (ht : 0 < t) :
    ‖(2 * (Real.pi : ℂ)) ^ ((w : ℂ) / 2 + (c' : ℂ) * ω) *
        (t : ℂ) ^ ((w : ℂ) / 2 + (c' : ℂ) * ω - 1) /
        Complex.Gamma ((w : ℂ) / 2 + (c' : ℂ) * ω)‖ =
      ‖(stirlingSW w c' ω)⁻¹‖ *
        (2 * Real.pi * (√(3 * t / c')) ^ 2 / (3 * ‖ω‖)) ^ (((w : ℝ) - 1) / 2) *
        (1 / √t) * Real.exp (c' * crudeExponentB ω) *
        Real.exp (c' * Bessel.besselL (√(3 * t / c'))) *
        Real.exp (-c' * crudeDivergenceD (3 * ω.re / Real.pi) (√(3 * t / c'))) := by
  set z : ℂ := (w : ℂ) / 2 + (c' : ℂ) * ω with hz_def
  set x : ℝ := √(3 * t / c') with hx_def
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have ht_eq : t = c' * x ^ 2 / 3 := by
    rw [hx_def, Real.sq_sqrt (by positivity)]; field_simp [hc'.ne']
  have ht_c_eq : (t : ℂ) = (c' : ℂ) * (x : ℂ) ^ 2 / 3 := by exact_mod_cast ht_eq
  have hω_ne : ω ≠ 0 := by intro h; rw [h, Complex.zero_re] at hω_re; exact lt_irrefl 0 hω_re
  have hb_arg : |(x : ℂ).arg| < Real.pi / 4 := by
    rw [Complex.arg_ofReal_of_nonneg hx_pos.le, abs_zero]; positivity
  have hst := gamma_mul_two_pi_t_cpow_neg_W hw hc' hω_re.le hω_ne
    (show 0 < (x : ℂ).re by simpa using hx_pos) hb_arg
  dsimp only at hst
  rw [← ht_c_eq] at hst
  have hw_pos : (0 : ℝ) < w := by exact_mod_cast hw
  have hz_re : 0 < z.re := by
    simp only [hz_def, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
      Complex.re_ofReal_mul]
    nlinarith [mul_pos hc' hω_re]
  have hgam_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero (fun n hn => by
      have : z.re = -(n : ℝ) := by rw [hn]; simp
      linarith [Nat.cast_nonneg (α := ℝ) n])
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hcpow_num : (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) =
      (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z * (t : ℂ)⁻¹ := by
    have hmul : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z = (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ z := by
      simpa [Complex.ofReal_mul] using
        ofReal_mul_cpow (by positivity : (0 : ℝ) < 2 * Real.pi) (t : ℂ) z
    have hsub : (t : ℂ) ^ (z - 1) = (t : ℂ) ^ z * (t : ℂ)⁻¹ := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ ht_ne, Complex.cpow_neg_one]
    rw [hmul, hsub]; ring
  have hcpow_neg : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (-z) =
      ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹ :=
    Complex.cpow_neg _ _
  have hS_ne : stirlingSW w c' ω ≠ 0 := Complex.exp_ne_zero _
  have hpref_ne : stirlingPrefW w ω (x : ℂ) ≠ 0 := by
    intro h0
    have := norm_stirlingPrefW_inv (w := w) hω_ne hx_pos
    rw [show stirlingPrefW w ω (x : ℂ) = 0 from h0, inv_zero, norm_zero] at this
    have hpos : 0 < (2 * Real.pi * x ^ 2 / (3 * ‖ω‖)) ^ (((w : ℝ) - 1) / 2) :=
      Real.rpow_pos_of_pos (by have := norm_pos_iff.mpr hω_ne; positivity) _
    linarith
  have ht_half_ne : (t : ℂ) ^ (-(1 / 2 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl ht_ne)
  have hexp_J_ne : Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hratio : (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z =
      (stirlingPrefW w ω (x : ℂ))⁻¹ * (stirlingSW w c' ω)⁻¹ * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
    have hinv : Complex.Gamma z * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹ =
        stirlingPrefW w ω (x : ℂ) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
          Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) * stirlingSW w c' ω := by
      rwa [hcpow_neg] at hst
    have hgam_eq : ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z) / Complex.Gamma z =
        (stirlingPrefW w ω (x : ℂ))⁻¹ * (stirlingSW w c' ω)⁻¹ *
          ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
          Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
      rw [Complex.exp_neg]
      have h2pit_ne : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero h2pi_ne ht_ne))
      calc (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z / Complex.Gamma z
          = (Complex.Gamma z * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹)⁻¹ := by
            field_simp [hgam_ne, h2pit_ne]
        _ = (stirlingPrefW w ω (x : ℂ) * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
              Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) * stirlingSW w c' ω)⁻¹ := by
            rw [hinv]
        _ = (stirlingPrefW w ω (x : ℂ))⁻¹ * (stirlingSW w c' ω)⁻¹ *
              ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
              (Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)))⁻¹ := by
            field_simp [hS_ne, ht_half_ne, hexp_J_ne, hpref_ne]
    have hthalf_inv : ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * (t : ℂ)⁻¹ = (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [← Complex.cpow_neg, neg_neg, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ ht_ne]
      congr 1; norm_num
    rw [hcpow_num, mul_div_right_comm, hgam_eq]
    calc (stirlingPrefW w ω (x : ℂ))⁻¹ * (stirlingSW w c' ω)⁻¹ *
          ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
          Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) * (t : ℂ)⁻¹
        = (stirlingPrefW w ω (x : ℂ))⁻¹ * (stirlingSW w c' ω)⁻¹ *
            (((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * (t : ℂ)⁻¹) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by ring
      _ = (stirlingPrefW w ω (x : ℂ))⁻¹ * (stirlingSW w c' ω)⁻¹ * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by rw [hthalf_inv]
  have hthalf_norm : ‖(t : ℂ) ^ (-(1 / 2 : ℂ))‖ = 1 / √t := by
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow ht.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, Real.sqrt_eq_rpow, one_div]
    norm_num
  have hexp_J_norm : ‖Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ)))‖ =
      Real.exp (c' * crudeExponentB ω + c' * Bessel.besselL x -
        c' * crudeDivergenceD (3 * ω.re / Real.pi) x) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.neg_re, Complex.re_ofReal_mul]
    have hid := exponent_identity_W hω_re hx_pos
    calc -(c' * (stirlingJ ω (x : ℂ)).re)
        = c' * (crudeExponentB ω + Bessel.besselL x -
            (crudeExponentB ω + (stirlingJ ω (x : ℂ)).re + Bessel.besselL x)) := by ring
      _ = c' * crudeExponentB ω + c' * Bessel.besselL x -
            c' * crudeDivergenceD (3 * ω.re / Real.pi) x := by rw [hid]; ring
  rw [hratio, norm_mul, norm_mul, norm_mul, norm_stirlingPrefW_inv hω_ne hx_pos, hthalf_norm,
    hexp_J_norm, Real.exp_sub, Real.exp_add]
  rw [show -c' * crudeDivergenceD (3 * ω.re / Real.pi) x =
      -(c' * crudeDivergenceD (3 * ω.re / Real.pi) x) by ring, Real.exp_neg]
  ring

/-! ### Kernel over `V` -/

lemma sqrt_two_pi_mul_div_sqrt {c' x : ℝ} (hc' : 0 < c') (hx : 0 < x) :
    √(2 * Real.pi * (c' * Bessel.besselL x)) / √(c' * x ^ 2 / 3) = 2 * Real.pi / √x := by
  rw [← Real.sqrt_div (by unfold Bessel.besselL; positivity)]
  have : 2 * Real.pi * (c' * Bessel.besselL x) / (c' * x ^ 2 / 3) = (2 * Real.pi) ^ 2 / x := by
    unfold Bessel.besselL; field_simp
  rw [this, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]

lemma pow_nat_eq_rpow_sq {x : ℝ} (hx : 0 < x) {w : ℕ} (hw : 1 ≤ w) :
    (2 * x) ^ (w - 1) = (4 * x ^ 2) ^ (((w : ℝ) - 1) / 2) := by
  have hcast : ((w : ℝ) - 1) = ((w - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hw]; simp
  rw [hcast, show (4 * x ^ 2 : ℝ) = (2 * x) ^ (2 : ℝ) by
    rw [Real.rpow_two]; ring, ← Real.rpow_mul (by positivity)]
  rw [show (2 : ℝ) * (((w - 1 : ℕ) : ℝ) / 2) = ((w - 1 : ℕ) : ℝ) by ring, Real.rpow_natCast]

/-- **Kernel over `V`, weight `w`** (`vlo:S2`, proof): if `V(t) = ρ (2x)^{w-1} A_s(c' L(x))` with
`ρ > 0`, `x = √(3t/c')`, `A_s(y) = e^y/√(2π y)`, then
`|(2π)^z t^{z-1}/Γ(z)| / V(t) = |S|^{-1} (π/(6|ω|))^{(w-1)/2} e^{c' B(ω)} e^{-c' D(3 Re ω/π, x)}
  · (2π/(√x ρ))`. -/
theorem kernel_div_eq_W {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 < ω.re) {t V ρ : ℝ} (ht : 0 < t) (hρ : 0 < ρ)
    (hV : V = ρ * ((2 * √(3 * t / c')) ^ (w - 1) *
      Bessel.besselAs (c' * Bessel.besselL (√(3 * t / c'))))) :
    ‖(2 * (Real.pi : ℂ)) ^ ((w : ℂ) / 2 + (c' : ℂ) * ω) *
        (t : ℂ) ^ ((w : ℂ) / 2 + (c' : ℂ) * ω - 1) /
        Complex.Gamma ((w : ℂ) / 2 + (c' : ℂ) * ω)‖ / V =
      ‖(stirlingSW w c' ω)⁻¹‖ * (Real.pi / (6 * ‖ω‖)) ^ (((w : ℝ) - 1) / 2) *
        Real.exp (c' * crudeExponentB ω) *
        Real.exp (-c' * crudeDivergenceD (3 * ω.re / Real.pi) (√(3 * t / c'))) *
        (2 * Real.pi / (√(√(3 * t / c')) * ρ)) := by
  rw [norm_kernel_eq_W hw hc' hω_re ht, hV]
  set x : ℝ := √(3 * t / c') with hx_def
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have ht_eq : t = c' * x ^ 2 / 3 := by
    rw [hx_def, Real.sq_sqrt (by positivity)]; field_simp [hc'.ne']
  have hω_norm : 0 < ‖ω‖ := lt_of_lt_of_le hω_re (Complex.re_le_norm ω)
  have hL_pos : 0 < c' * Bessel.besselL x := by unfold Bessel.besselL; positivity
  have hsqrt_t : 0 < √t := Real.sqrt_pos.mpr ht
  have hAs : Bessel.besselAs (c' * Bessel.besselL x) =
      Real.exp (c' * Bessel.besselL x) / √(2 * Real.pi * (c' * Bessel.besselL x)) := rfl
  have hpow_ratio : (2 * Real.pi * x ^ 2 / (3 * ‖ω‖)) ^ (((w : ℝ) - 1) / 2) =
      (Real.pi / (6 * ‖ω‖)) ^ (((w : ℝ) - 1) / 2) * (2 * x) ^ (w - 1) := by
    rw [pow_nat_eq_rpow_sq hx_pos hw, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hsq := sqrt_two_pi_mul_div_sqrt hc' hx_pos
  rw [← ht_eq] at hsq
  rw [hpow_ratio, hAs]
  have hpow_pos : 0 < (2 * x) ^ (w - 1) := by positivity
  have hexpL_pos : 0 < Real.exp (c' * Bessel.besselL x) := Real.exp_pos _
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx_pos
  have hsq' : √(2 * Real.pi * (c' * Bessel.besselL x)) = 2 * Real.pi / √x * √t :=
    (div_eq_iff hsqrt_t.ne').mp hsq
  rw [hsq']
  field_simp

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.norm_kernel_eq_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_kernel_eq_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.kernel_div_eq_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernel_div_eq_W

end FormalResearch.ModularBootstrap.FixedWeightBand
