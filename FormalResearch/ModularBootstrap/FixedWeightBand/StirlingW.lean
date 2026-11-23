module

public import FormalResearch.ModularBootstrap.ComplexBessel.StirlingOmega

/-!
# Stirling expansion at weight `w` (`vlo:stirling`, fixed-weight version)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, eq. `vlo:stirling`.

For a natural weight `w ≥ 1`, `c' > 0`, `ω` with `Re ω ≥ 0`, `ω ≠ 0`, `h = c' ω`, `z = w/2 + h`,
and `t = c' b^2 / 3` (`Re b > 0`), the paper's Stirling factor is
`S^{(w)}_{c'}(ω) = Γ(z) / (√(2π) h^{(w-1)/2 + h} e^{-h})
  = exp(((w-1)/2 + h) log(1 + w/(2h)) - w/2 + R(w/2 + h))`
with `R` the Stirling remainder (`Asymptotics.binetRem`), and
`Γ(z) (2π t)^{-z} = (3ω/(2π b^2))^{(w-1)/2} t^{-1/2} e^{c' J(ω; b)} S^{(w)}_{c'}(ω)`.

## Main definitions and results
* `stirlingFW`, `stirlingLogSW`, `stirlingSW`, `stirlingPrefW`: `F_w(h)`, `log S^{(w)}_{c'}`, `S^{(w)}_{c'}`
  and the prefactor `(3ω/(2π b^2))^{(w-1)/2}`.
* `stirlingLogSW_one`, `stirlingSW_one`, `stirlingPrefW_one`: the weight-one specialisation recovers
  `ComplexBessel.stirlingLogS`, `stirlingS` and prefactor `1`.
* `gamma_mul_two_pi_t_cpow_neg_W`: the exact factorisation (`|arg b| < π/4`, which covers `b > 0`
  and `b` near `ξ*`).
* `norm_stirlingLogSW_le_of_ge`, `norm_deriv_stirlingLogSW_le_of_ge`: explicit constants
  `(w²+2)/(c'|ω|)` and `(w²+1)/(c'|ω|²)` once `c'|ω| ≥ w`.
* `norm_stirlingLogSW_le`, `hasDerivAt_stirlingLogSW`, `norm_deriv_stirlingLogSW_le`,
  `norm_stirlingSW_le`, `norm_stirlingSW_inv_le`, `norm_stirlingSW_sub_one_le`: the bounds
  `|log S| ≤ C_w/(c'|ω|)`, `|∂_ω log S| ≤ C_w/(c'|ω|²)`, `|S^{±1}| ≤ e^{C_w}`,
  `|S - 1| ≤ 2 C_w e^{C_w}/(c'|ω|)` with `C_w = 7 w⁴` depending only on `w`, for every
  `c'|ω| ≥ 1` (in particular for the paper's `c'|ω| ≥ 48`, where the paper's `C_w` and `C` depend on `w`).
* `norm_stirlingSW_abs_bounds`, `norm_stirlingSW_le_two_of_le_four`: an absolute bound `|S^{±1}| ≤ 2`
  needs `c'|ω| ≥ max(w, 2(w²+2))`; the paper's threshold `48` suffices exactly for `w ≤ 4`.
-/

@[expose] public section

open Complex Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open FormalResearch.ModularBootstrap.ComplexBessel

/-! ### Definitions -/

/-- The exponent `F_w(h) = ((w-1)/2 + h) log(1 + w/(2h)) - w/2 + R(w/2 + h)` of `S^{(w)}`
as a function of `h = c' ω`. -/
noncomputable def stirlingFW (w : ℕ) (h : ℂ) : ℂ :=
  (((w : ℂ) - 1) / 2 + h) * Complex.log (1 + (w : ℂ) / (2 * h)) - (w : ℂ) / 2 +
    FormalResearch.Asymptotics.binetRem ((w : ℂ) / 2 + h)

/-- `log S^{(w)}_{c'}(ω)` (`lower_o1_two_edge.tex`, §J2). -/
noncomputable def stirlingLogSW (w : ℕ) (c' : ℝ) (ω : ℂ) : ℂ :=
  stirlingFW w ((c' : ℂ) * ω)

/-- `S^{(w)}_{c'}(ω) = exp (log S^{(w)}_{c'}(ω))`. -/
noncomputable def stirlingSW (w : ℕ) (c' : ℝ) (ω : ℂ) : ℂ :=
  Complex.exp (stirlingLogSW w c' ω)

/-- The prefactor `(3ω/(2π b^2))^{(w-1)/2}` of `vlo:stirling` (principal power). -/
noncomputable def stirlingPrefW (w : ℕ) (ω b : ℂ) : ℂ :=
  (3 * ω / (2 * (Real.pi : ℂ) * b ^ 2)) ^ (((w : ℂ) - 1) / 2)

/-- The constant `C_w = 7 w^4` used in the uniform bounds. -/
def stirlingConstW (w : ℕ) : ℝ := 7 * (w : ℝ) ^ 4

theorem stirlingConstW_pos {w : ℕ} (hw : 1 ≤ w) : 0 < stirlingConstW w := by
  have : (0 : ℝ) < w := by exact_mod_cast hw
  unfold stirlingConstW; positivity

/-! ### Weight one -/

theorem stirlingLogSW_one (c' : ℝ) (ω : ℂ) : stirlingLogSW 1 c' ω = stirlingLogS c' ω := by
  unfold stirlingLogSW stirlingFW stirlingLogS
  have h2 : (2 : ℂ) * ((c' : ℂ) * ω) = 2 * (c' : ℂ) * ω := by ring
  simp only [Nat.cast_one, sub_self, zero_div, zero_add, h2]

theorem stirlingSW_one (c' : ℝ) (ω : ℂ) : stirlingSW 1 c' ω = stirlingS c' ω := by
  unfold stirlingSW stirlingS; rw [stirlingLogSW_one]

theorem stirlingPrefW_one (ω b : ℂ) : stirlingPrefW 1 ω b = 1 := by
  simp [stirlingPrefW]

/-! ### Branch identities -/

private lemma log_ofReal_pos_mul_W {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) :
    Complex.log ((r : ℂ) * w) = (Real.log r : ℂ) + Complex.log w := by
  have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have harg : (r : ℂ).arg + w.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le, zero_add]
    exact ⟨Complex.neg_pi_lt_arg w, Complex.arg_le_pi w⟩
  rw [Complex.log_mul hr_c hw harg, ← Complex.ofReal_log hr.le]

private lemma re_u_nonneg {h : ℂ} (hh : 0 ≤ h.re) (w : ℕ) : 0 ≤ ((w : ℂ) / (2 * h)).re := by
  have hdiv : ((w : ℂ) / (2 * h)) = ((w : ℝ) : ℂ) * (2 * h)⁻¹ := by
    rw [div_eq_mul_inv]; rfl
  rw [hdiv, Complex.re_ofReal_mul, Complex.inv_re, Complex.mul_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero]
  exact mul_nonneg (Nat.cast_nonneg w) (div_nonneg (by linarith) (Complex.normSq_nonneg _))

private lemma one_le_re_one_add_u {h : ℂ} (hh : 0 ≤ h.re) (w : ℕ) :
    1 ≤ (1 + (w : ℂ) / (2 * h)).re := by
  rw [Complex.add_re, Complex.one_re]
  linarith [re_u_nonneg hh w]

private lemma log_half_add_eq {w : ℕ} {h : ℂ} (hh : 0 ≤ h.re) (hne : h ≠ 0) :
    Complex.log ((w : ℂ) / 2 + h) = Complex.log h + Complex.log (1 + (w : ℂ) / (2 * h)) := by
  have hre_u : 0 < (1 + (w : ℂ) / (2 * h)).re := lt_of_lt_of_le one_pos (one_le_re_one_add_u hh w)
  have hu_ne : 1 + (w : ℂ) / (2 * h) ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hre_u; exact lt_irrefl 0 hre_u
  have harg_h : |h.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hh
  have harg_u : |(1 + (w : ℂ) / (2 * h)).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_u)
  have harg_mem : h.arg + (1 + (w : ℂ) / (2 * h)).arg ∈ Ioc (-Real.pi) Real.pi := by
    have h1 := abs_le.mp harg_h
    have h2 := abs_lt.mp harg_u
    exact ⟨by linarith, by linarith⟩
  have hmul_eq : (w : ℂ) / 2 + h = h * (1 + (w : ℂ) / (2 * h)) := by
    field_simp [hne]
    ring
  rw [hmul_eq, Complex.log_mul hne hu_ne harg_mem]

private lemma log_sq_of_re_pos_W {b : ℂ} (hb : 0 < b.re) :
    Complex.log (b ^ 2) = 2 * Complex.log b := by
  have hb_ne : b ≠ 0 := by intro h; rw [h, Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have harg_lt : |b.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have harg_mem : b.arg + b.arg ∈ Ioc (-Real.pi) Real.pi := by
    have := abs_lt.mp harg_lt
    exact ⟨by linarith, by linarith⟩
  rw [sq, Complex.log_mul hb_ne hb_ne harg_mem, two_mul]

/-- For `Re ω ≥ 0`, `ω ≠ 0`, `Re b > 0` and `|arg b| < π/4`: `log (ω / b²) = log ω - 2 log b`. -/
private lemma log_div_sq_eq {ω b : ℂ} (hω_re : 0 ≤ ω.re) (hω_ne : ω ≠ 0) (hb_re : 0 < b.re)
    (hb : |b.arg| < Real.pi / 4) :
    Complex.log (ω / b ^ 2) = Complex.log ω - 2 * Complex.log b := by
  have hsq := log_sq_of_re_pos_W hb_re
  have harg_sq : (b ^ 2).arg = 2 * b.arg := by
    have := congrArg Complex.im hsq
    simpa [Complex.log_im] using this
  have hb2_lt : |(b ^ 2).arg| < Real.pi / 2 := by
    rw [harg_sq, abs_mul]; norm_num; linarith
  have hne_pi : (b ^ 2).arg ≠ Real.pi := by
    intro h; rw [h] at hb2_lt; rw [abs_of_pos Real.pi_pos] at hb2_lt; linarith [Real.pi_pos]
  have hb2_ne : b ^ 2 ≠ 0 := by
    intro h; rw [h, Complex.arg_zero] at harg_sq
    have : b ^ 2 = 0 := h
    have hb_ne : b ≠ 0 := by intro h0; rw [h0, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
    exact hb_ne ((pow_eq_zero_iff two_ne_zero).mp this)
  have hinv_ne : (b ^ 2)⁻¹ ≠ 0 := inv_ne_zero hb2_ne
  have harg_inv : ((b ^ 2)⁻¹).arg = -(b ^ 2).arg := by
    rw [Complex.arg_inv]; simp [hne_pi]
  have harg_ω : |ω.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hω_re
  have harg_mem : ω.arg + ((b ^ 2)⁻¹).arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [harg_inv]
    have h1 := abs_le.mp harg_ω
    have h2 := abs_lt.mp hb2_lt
    exact ⟨by linarith, by linarith⟩
  rw [div_eq_mul_inv, Complex.log_mul hω_ne hinv_ne harg_mem, Complex.log_inv _ hne_pi, hsq]
  ring

/-! ### Exact factorisation -/

/-- **Stirling factorisation at weight `w`** (`lower_o1_two_edge.tex`, eq. `vlo:stirling`):
for `w ≥ 1`, `c' > 0`, `Re ω ≥ 0`, `ω ≠ 0`, `Re b > 0` and `|arg b| < π/4` (so `b > 0` and `b` near the
positive axis are covered), with `z = w/2 + c' ω` and `t = c' b²/3`,
`Γ(z) (2π t)^{-z} = (3ω/(2π b²))^{(w-1)/2} t^{-1/2} e^{c' J(ω; b)} S^{(w)}_{c'}(ω)`. -/
theorem gamma_mul_two_pi_t_cpow_neg_W {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω b : ℂ}
    (hω_re : 0 ≤ ω.re) (hω_ne : ω ≠ 0) (hb_re : 0 < b.re) (hb : |b.arg| < Real.pi / 4) :
    let z : ℂ := (w : ℂ) / 2 + (c' : ℂ) * ω
    let t : ℂ := (c' : ℂ) * b ^ 2 / 3
    Complex.Gamma z * (2 * (Real.pi : ℂ) * t) ^ (-z) =
      stirlingPrefW w ω b * t ^ (-(1 / 2 : ℂ)) * Complex.exp ((c' : ℂ) * stirlingJ ω b) *
        stirlingSW w c' ω := by
  intro z t
  have hc'_c : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc'.ne'
  have hb_ne : b ≠ 0 := by intro h; rw [h, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
  have ht_ne : t ≠ 0 := by
    dsimp [t]; exact div_ne_zero (mul_ne_zero hc'_c (pow_ne_zero 2 hb_ne)) three_ne_zero
  have h2pit_ne : 2 * (Real.pi : ℂ) * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) ht_ne
  set h : ℂ := (c' : ℂ) * ω with hh_def
  have hh_re : 0 ≤ h.re := by
    dsimp [h]; rw [Complex.re_ofReal_mul]; exact mul_nonneg hc'.le hω_re
  have hh_ne : h ≠ 0 := mul_ne_zero hc'_c hω_ne
  have hw_pos : (0 : ℝ) < w := by exact_mod_cast hw
  have hz_re : 0 < z.re := by
    simp only [z, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    have : 0 ≤ ((c' : ℂ) * ω).re := by rw [Complex.re_ofReal_mul]; exact mul_nonneg hc'.le hω_re
    linarith
  have hgam : Complex.Gamma z = Complex.exp ((z - 1 / 2) * Complex.log z - z +
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + FormalResearch.Asymptotics.binetRem z) :=
    (FormalResearch.CohnElkies.exp_stirling_add_binetRem_eq_gamma hz_re).symm
  have hcpow_t : (2 * (Real.pi : ℂ) * t) ^ (-z) =
      Complex.exp (-z * Complex.log (2 * (Real.pi : ℂ) * t)) :=
    (Complex.cpow_def_of_ne_zero h2pit_ne (-z)).trans (by rw [mul_comm])
  have hcpow_t_half : t ^ (-(1 / 2 : ℂ)) = Complex.exp (-(1 / 2 : ℂ) * Complex.log t) :=
    (Complex.cpow_def_of_ne_zero ht_ne _).trans (by rw [mul_comm])
  have h3ω_ne : 3 * ω / (2 * (Real.pi : ℂ) * b ^ 2) ≠ 0 :=
    div_ne_zero (mul_ne_zero three_ne_zero hω_ne)
      (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'))
        (pow_ne_zero 2 hb_ne))
  have hcpow_pref : stirlingPrefW w ω b = Complex.exp
      (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * b ^ 2)) * (((w : ℂ) - 1) / 2)) :=
    Complex.cpow_def_of_ne_zero h3ω_ne _
  have hlog_pref : Complex.log (3 * ω / (2 * (Real.pi : ℂ) * b ^ 2)) =
      (Real.log (3 / (2 * Real.pi)) : ℂ) + (Complex.log ω - 2 * Complex.log b) := by
    have heq : 3 * ω / (2 * (Real.pi : ℂ) * b ^ 2) =
        ((3 / (2 * Real.pi) : ℝ) : ℂ) * (ω / b ^ 2) := by push_cast; ring
    have hne : ω / b ^ 2 ≠ 0 := div_ne_zero hω_ne (pow_ne_zero 2 hb_ne)
    rw [heq, log_ofReal_pos_mul_W (by positivity) hne, log_div_sq_eq hω_re hω_ne hb_re hb]
  have hlog_2pit : Complex.log (2 * (Real.pi : ℂ) * t) =
      (Real.log (2 * Real.pi) : ℂ) + Complex.log t := by
    simpa [Complex.ofReal_mul] using
      log_ofReal_pos_mul_W (by positivity : (0 : ℝ) < 2 * Real.pi) ht_ne
  have hlog_t : Complex.log t = (Real.log (c' / 3) : ℂ) + 2 * Complex.log b := by
    have ht_eq : t = ((c' / 3 : ℝ) : ℂ) * b ^ 2 := by dsimp [t]; push_cast; ring
    rw [ht_eq, log_ofReal_pos_mul_W (by positivity : (0 : ℝ) < c' / 3) (pow_ne_zero 2 hb_ne),
      log_sq_of_re_pos_W hb_re]
  have hz_eq : z = (w : ℂ) / 2 + h := rfl
  have hlog_z : Complex.log z = Complex.log h + Complex.log (1 + (w : ℂ) / (2 * h)) :=
    log_half_add_eq hh_re hh_ne
  have hlog_h : Complex.log h = (Real.log c' : ℂ) + Complex.log ω :=
    log_ofReal_pos_mul_W hc' hω_ne
  have hlog_J : Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) =
      (Real.log (3 / (2 * Real.pi)) - 1 : ℝ) + Complex.log ω := by
    have hr_pos : 0 < 3 / (2 * Real.pi * Real.exp 1) := by positivity
    have heq : 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) =
        ((3 / (2 * Real.pi * Real.exp 1) : ℝ) : ℂ) * ω := by push_cast; ring
    rw [heq, log_ofReal_pos_mul_W hr_pos hω_ne,
      Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (Real.exp_pos 1).ne',
      Real.log_exp]
    have hsub : Real.log (3 : ℝ) - (Real.log (2 * Real.pi) + 1) =
        Real.log (3 / (2 * Real.pi)) - 1 := by
      rw [Real.log_div (by norm_num) (by positivity)]; ring
    rw [hsub]
  have hr1 : (Real.log (c' / 3) : ℂ) = (Real.log c' : ℂ) - (Real.log 3 : ℂ) := by
    rw [Real.log_div hc'.ne' (by norm_num)]; push_cast; ring
  have hr2 : (Real.log (3 / (2 * Real.pi)) : ℂ) = (Real.log 3 : ℂ) - (Real.log (2 * Real.pi) : ℂ) := by
    rw [Real.log_div (by norm_num) (by positivity)]; push_cast; ring
  unfold stirlingSW stirlingLogSW stirlingFW stirlingJ
  rw [hgam, hcpow_t, hcpow_t_half, hcpow_pref, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hlog_2pit, hlog_t, hlog_z, hlog_h, hlog_J, hlog_pref]
  have h2pi_half : ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) =
      (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ) := by push_cast; ring
  simp only [hh_def, z, Complex.ofReal_sub, Complex.ofReal_one, hr1, hr2, h2pi_half]
  ring

/-! ### Elementary estimates -/

private lemma norm_half_add_ge_W {w : ℕ} {h : ℂ} (hh : 0 ≤ h.re) :
    ‖h‖ ≤ ‖(w : ℂ) / 2 + h‖ := by
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hsq : ‖h‖ ^ 2 ≤ ‖(w : ℂ) / 2 + h‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, Complex.add_im,
      Complex.div_ofNat_im, Complex.natCast_im, zero_div, zero_add]
    nlinarith
  have h1 : √(‖h‖ ^ 2) ≤ √(‖(w : ℂ) / 2 + h‖ ^ 2) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

private lemma re_half_add_pos {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re) :
    0 < ((w : ℂ) / 2 + h).re := by
  have hw0 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
  linarith

private lemma norm_a_W {w : ℕ} (hw : 1 ≤ w) : ‖((w : ℂ) - 1) / 2‖ = ((w : ℝ) - 1) / 2 := by
  have hw0 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have : ((w : ℂ) - 1) / 2 = ((((w : ℝ) - 1) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]

private lemma norm_u_W (w : ℕ) {h : ℂ} : ‖(w : ℂ) / (2 * h)‖ = (w : ℝ) / (2 * ‖h‖) := by
  rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]

private lemma one_le_norm_one_add_u {h : ℂ} (hh : 0 ≤ h.re) (w : ℕ) :
    1 ≤ ‖1 + (w : ℂ) / (2 * h)‖ :=
  (one_le_re_one_add_u hh w).trans (Complex.re_le_norm _)

private lemma one_add_u_ne {h : ℂ} (hh : 0 ≤ h.re) (w : ℕ) : 1 + (w : ℂ) / (2 * h) ≠ 0 := by
  intro h0
  have := one_le_norm_one_add_u hh w
  rw [h0, norm_zero] at this
  linarith

private lemma norm_log_one_add_le {u : ℂ} (hu : 1 ≤ (1 + u).re) : ‖Complex.log (1 + u)‖ ≤ ‖u‖ + 2 := by
  have hx1 : 1 ≤ ‖1 + u‖ := hu.trans (Complex.re_le_norm _)
  have hx_ne : 1 + u ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hu; linarith
  have hre : (Complex.log (1 + u)).re = Real.log ‖1 + u‖ := Complex.log_re _
  have him : (Complex.log (1 + u)).im = (1 + u).arg := Complex.log_im _
  have hlog_nn : 0 ≤ Real.log ‖1 + u‖ := Real.log_nonneg hx1
  have hlog_le : Real.log ‖1 + u‖ ≤ ‖u‖ := by
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < ‖1 + u‖)
    have h2 : ‖1 + u‖ ≤ 1 + ‖u‖ := by simpa using norm_add_le (1 : ℂ) u
    linarith
  have harg : |(1 + u).arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (by linarith)
  have h4 := Real.pi_le_four
  calc ‖Complex.log (1 + u)‖ ≤ |(Complex.log (1 + u)).re| + |(Complex.log (1 + u)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ‖u‖ + 2 := by
      rw [hre, him, abs_of_nonneg hlog_nn]
      linarith

private lemma norm_log_sub_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) :
    ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
  have hu_lt1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have h1 := Complex.norm_log_one_add_sub_self_le hu_lt1
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (sub_pos.mpr hu_lt1) two_pos]; linarith
  calc ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 := h1
    _ ≤ ‖u‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖u‖ ^ 2 := by ring

private lemma norm_binetRem_le_W {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re) (hpos : 0 < ‖h‖) :
    ‖FormalResearch.Asymptotics.binetRem ((w : ℂ) / 2 + h)‖ ≤ 2 / ‖h‖ := by
  have hz_re := re_half_add_pos hw hh
  rw [FormalResearch.CohnElkies.binetRem_eq_binetB hz_re]
  calc ‖FormalResearch.Special.ComplexStirling.binetB ((w : ℂ) / 2 + h)‖
      ≤ 2 / ‖(w : ℂ) / 2 + h‖ := FormalResearch.Special.ComplexStirling.norm_binetB_le_div hz_re
    _ ≤ 2 / ‖h‖ := div_le_div_of_nonneg_left (by norm_num) hpos (norm_half_add_ge_W hh)

private lemma norm_binetI_le_W {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re) (hpos : 0 < ‖h‖) :
    ‖FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖ ≤ 1 / ‖h‖ ^ 2 := by
  have hz_re := re_half_add_pos hw hh
  calc ‖FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖
      ≤ 1 / ‖(w : ℂ) / 2 + h‖ ^ 2 := FormalResearch.Special.ComplexStirling.norm_binetI_le_div hz_re
    _ ≤ 1 / ‖h‖ ^ 2 := by
      have := norm_half_add_ge_W (w := w) hh
      gcongr

private lemma aux_A (w x : ℝ) (hw : 1 ≤ w) (hx : w ≤ x) :
    ((w - 1) / 2 + x) * (w / (2 * x)) ^ 2 + (w - 1) / 2 * (w / (2 * x)) + 2 / x ≤
      (w ^ 2 + 2) / x := by
  have hx0 : 0 < x := by linarith
  have heq : ((w - 1) / 2 + x) * (w / (2 * x)) ^ 2 + (w - 1) / 2 * (w / (2 * x)) + 2 / x =
      (((w - 1) / 2 + x) * w ^ 2 / (4 * x) + (w - 1) * w / 4 + 2) / x := by
    field_simp; ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ hx0.le
  have h1 : ((w - 1) / 2 + x) * w ^ 2 / (4 * x) ≤ 3 * w ^ 2 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg w]
  nlinarith [sq_nonneg w]

private lemma aux_dA (w x : ℝ) (hw : 1 ≤ w) (hx : 0 < x) :
    (w / (2 * x)) ^ 2 + (w / (2 * x)) ^ 2 + (w - 1) / 2 * (w / (2 * x)) / x + 1 / x ^ 2 ≤
      (w ^ 2 + 1) / x ^ 2 := by
  have heq : (w / (2 * x)) ^ 2 + (w / (2 * x)) ^ 2 + (w - 1) / 2 * (w / (2 * x)) / x + 1 / x ^ 2 =
      (w ^ 2 / 2 + (w - 1) * w / 4 + 1) / x ^ 2 := by
    field_simp; ring
  rw [heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg w]

/-! ### The exponent `F_w` and its bounds -/

/-- A closed form for `F_w'(h)`: `log(1+u) - (a+h) (w/(2h²)) / (1+u) - binetI(w/2 + h)` with
`u = w/(2h)`, `a = (w-1)/2`. -/
noncomputable def stirlingDFW (w : ℕ) (h : ℂ) : ℂ :=
  Complex.log (1 + (w : ℂ) / (2 * h)) -
    (((w : ℂ) - 1) / 2 + h) * ((w : ℂ) / (2 * h ^ 2)) / (1 + (w : ℂ) / (2 * h)) -
    FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)

/-- Large-argument bound with explicit constant: `‖F_w(h)‖ ≤ (w²+2)/‖h‖` once `w ≤ ‖h‖`. -/
theorem norm_stirlingFW_le_of_ge {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re)
    (hge : (w : ℝ) ≤ ‖h‖) : ‖stirlingFW w h‖ ≤ ((w : ℝ) ^ 2 + 2) / ‖h‖ := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hpos : 0 < ‖h‖ := by linarith
  have hne : h ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
  set u : ℂ := (w : ℂ) / (2 * h) with hu_def
  set a : ℂ := ((w : ℂ) - 1) / 2 with ha_def
  have hu_norm : ‖u‖ = (w : ℝ) / (2 * ‖h‖) := norm_u_W w
  have hu_le : ‖u‖ ≤ 1 / 2 := by
    rw [hu_norm, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hhu : h * u = (w : ℂ) / 2 := by
    rw [hu_def]; field_simp
  have hid : stirlingFW w h =
      (a + h) * (Complex.log (1 + u) - u) + a * u +
        FormalResearch.Asymptotics.binetRem ((w : ℂ) / 2 + h) := by
    unfold stirlingFW
    rw [← hu_def, ← ha_def]
    linear_combination hhu
  have ha_norm : ‖a‖ = ((w : ℝ) - 1) / 2 := norm_a_W hw
  have h1 : ‖(a + h) * (Complex.log (1 + u) - u)‖ ≤ (((w : ℝ) - 1) / 2 + ‖h‖) * ‖u‖ ^ 2 := by
    rw [norm_mul]
    have := norm_add_le a h
    rw [ha_norm] at this
    exact mul_le_mul this (norm_log_sub_le hu_le) (norm_nonneg _) (by positivity)
  have h2 : ‖a * u‖ = ((w : ℝ) - 1) / 2 * ‖u‖ := by rw [norm_mul, ha_norm]
  have h3 := norm_binetRem_le_W hw hh hpos
  rw [hid]
  calc _ ≤ ‖(a + h) * (Complex.log (1 + u) - u)‖ + ‖a * u‖ +
        ‖FormalResearch.Asymptotics.binetRem ((w : ℂ) / 2 + h)‖ := norm_add₃_le
    _ ≤ (((w : ℝ) - 1) / 2 + ‖h‖) * (w / (2 * ‖h‖)) ^ 2 + ((w : ℝ) - 1) / 2 * (w / (2 * ‖h‖)) +
        2 / ‖h‖ := by
      rw [h2, hu_norm] at *
      gcongr
    _ ≤ _ := aux_A w ‖h‖ hw1 hge

/-- Crude bound for `1 ≤ ‖h‖ ≤ w`: `‖F_w(h)‖ ≤ 7 w³ / ‖h‖`. -/
theorem norm_stirlingFW_le_crude {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re)
    (h1 : 1 ≤ ‖h‖) (hlt : ‖h‖ ≤ w) : ‖stirlingFW w h‖ ≤ 7 * (w : ℝ) ^ 3 / ‖h‖ := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hpos : 0 < ‖h‖ := by linarith
  have hne : h ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
  have hu_norm : ‖(w : ℂ) / (2 * h)‖ = (w : ℝ) / (2 * ‖h‖) := norm_u_W w
  have hu_le : ‖(w : ℂ) / (2 * h)‖ ≤ w / 2 := by
    rw [hu_norm, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hlog := norm_log_one_add_le (u := (w : ℂ) / (2 * h)) (one_le_re_one_add_u hh w)
  have ha_norm := norm_a_W hw
  have hR := norm_binetRem_le_W hw hh hpos
  have hR2 : 2 / ‖h‖ ≤ 2 := by
    rw [div_le_iff₀ hpos]; linarith
  have hnorm_w2 : ‖(w : ℂ) / 2‖ = w / 2 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_ofNat]
  have hsum : ‖(((w : ℂ) - 1) / 2 + h)‖ ≤ 3 * w / 2 := by
    have := norm_add_le (((w : ℂ) - 1) / 2) h
    rw [ha_norm] at this
    linarith
  have hbound : ‖stirlingFW w h‖ ≤ 7 * (w : ℝ) ^ 2 := by
    unfold stirlingFW
    calc _ ≤ ‖(((w : ℂ) - 1) / 2 + h) * Complex.log (1 + (w : ℂ) / (2 * h))‖ + ‖(w : ℂ) / 2‖ +
          ‖FormalResearch.Asymptotics.binetRem ((w : ℂ) / 2 + h)‖ := (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ (3 * w / 2) * ((w : ℝ) / 2 + 2) + w / 2 + 2 := by
        rw [norm_mul, hnorm_w2]
        have h5 : ‖Complex.log (1 + (w : ℂ) / (2 * h))‖ ≤ w / 2 + 2 := by linarith
        have h6 := mul_le_mul hsum h5 (norm_nonneg _) (by positivity)
        linarith
      _ ≤ 7 * (w : ℝ) ^ 2 := by nlinarith
  calc ‖stirlingFW w h‖ ≤ 7 * (w : ℝ) ^ 2 := hbound
    _ ≤ 7 * (w : ℝ) ^ 3 / ‖h‖ := by
      rw [le_div_iff₀ hpos]; nlinarith [sq_nonneg (w : ℝ)]

/-- Uniform bound for every `‖h‖ ≥ 1`, `Re h ≥ 0`: `‖F_w(h)‖ ≤ C_w / ‖h‖`, `C_w = 7 w⁴`. -/
theorem norm_stirlingFW_le {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re) (h1 : 1 ≤ ‖h‖) :
    ‖stirlingFW w h‖ ≤ stirlingConstW w / ‖h‖ := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hpos : 0 < ‖h‖ := by linarith
  unfold stirlingConstW
  by_cases hge : (w : ℝ) ≤ ‖h‖
  · refine (norm_stirlingFW_le_of_ge hw hh hge).trans ?_
    apply div_le_div_of_nonneg_right _ hpos.le
    have hw2 : (1 : ℝ) ≤ (w : ℝ) ^ 2 := one_le_pow₀ hw1
    have hw4 : (w : ℝ) ^ 2 ≤ (w : ℝ) ^ 4 := by nlinarith
    linarith
  · refine (norm_stirlingFW_le_crude hw hh h1 (le_of_not_ge hge)).trans ?_
    apply div_le_div_of_nonneg_right _ hpos.le
    nlinarith [sq_nonneg ((w : ℝ) ^ 2), sq_nonneg (w : ℝ), pow_pos (by linarith : (0 : ℝ) < w) 3]

/-! ### Derivative -/

theorem hasDerivAt_stirlingFW {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re) (hne : h ≠ 0) :
    HasDerivAt (stirlingFW w) (stirlingDFW w h) h := by
  have h1u_slit : 1 + (w : ℂ) / (2 * h) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le one_pos (one_le_re_one_add_u hh w)))
  have h1u_ne := one_add_u_ne hh w
  have hz_re := re_half_add_pos hw hh
  have hd_den : HasDerivAt (fun x : ℂ => 2 * x) 2 h := by
    simpa using (hasDerivAt_id h).const_mul (2 : ℂ)
  have hd_u : HasDerivAt (fun x : ℂ => (w : ℂ) / (2 * x)) (-((w : ℂ) / (2 * h ^ 2))) h := by
    have := (hasDerivAt_const h (w : ℂ)).div hd_den (mul_ne_zero two_ne_zero hne)
    refine this.congr_deriv ?_
    field_simp
    ring
  have hd_1u : HasDerivAt (fun x : ℂ => 1 + (w : ℂ) / (2 * x)) (-((w : ℂ) / (2 * h ^ 2))) h :=
    hd_u.const_add 1
  have hd_log := hd_1u.clog h1u_slit
  have hd_a : HasDerivAt (fun x : ℂ => ((w : ℂ) - 1) / 2 + x) 1 h :=
    (hasDerivAt_id h).const_add _
  have hd_prod := (hd_a.mul hd_log).sub_const ((w : ℂ) / 2)
  have hb : HasDerivAt FormalResearch.Asymptotics.binetRem
      (-FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h))
      ((fun x : ℂ => (w : ℂ) / 2 + x) h) := by
    have hopen : IsOpen {x : ℂ | 0 < x.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : FormalResearch.Asymptotics.binetRem =ᶠ[𝓝 ((w : ℂ) / 2 + h)]
        FormalResearch.Special.ComplexStirling.binetB := by
      filter_upwards [hopen.mem_nhds hz_re] with x hx
      exact FormalResearch.CohnElkies.binetRem_eq_binetB hx
    exact (FormalResearch.Special.ComplexStirling.hasDerivAt_binetB hz_re).congr_of_eventuallyEq hev
  have hd_bin : HasDerivAt
      (fun x : ℂ => FormalResearch.Asymptotics.binetRem ((w : ℂ) / 2 + x))
      (-FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h) * 1) h :=
    hb.comp h ((hasDerivAt_id h).const_add ((w : ℂ) / 2))
  refine (hd_prod.add hd_bin).congr_deriv ?_
  unfold stirlingDFW
  ring

/-- Derivative bound once `w ≤ ‖h‖`: `‖F_w'(h)‖ ≤ (w²+1)/‖h‖²`. -/
theorem norm_stirlingDFW_le_of_ge {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re)
    (hge : (w : ℝ) ≤ ‖h‖) : ‖stirlingDFW w h‖ ≤ ((w : ℝ) ^ 2 + 1) / ‖h‖ ^ 2 := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hpos : 0 < ‖h‖ := by linarith
  have hne : h ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
  set u : ℂ := (w : ℂ) / (2 * h) with hu_def
  set a : ℂ := ((w : ℂ) - 1) / 2 with ha_def
  have h1u_ne : 1 + u ≠ 0 := one_add_u_ne hh w
  have hu_norm : ‖u‖ = (w : ℝ) / (2 * ‖h‖) := norm_u_W w
  have hu_le : ‖u‖ ≤ 1 / 2 := by
    rw [hu_norm, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hge1 : 1 ≤ ‖1 + u‖ := one_le_norm_one_add_u hh w
  have hw2 : (w : ℂ) / (2 * h ^ 2) = u / h := by
    rw [hu_def]; field_simp
  have hid : stirlingDFW w h =
      (Complex.log (1 + u) - u) + u ^ 2 / (1 + u) - a * u / (h * (1 + u)) -
        FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h) := by
    unfold stirlingDFW
    rw [← hu_def, ← ha_def, hw2]
    field_simp
    ring
  have ha_norm : ‖a‖ = ((w : ℝ) - 1) / 2 := norm_a_W hw
  have t1 := norm_log_sub_le hu_le
  have t2 : ‖u ^ 2 / (1 + u)‖ ≤ ‖u‖ ^ 2 := by
    rw [norm_div, norm_pow]
    exact div_le_self (by positivity) hge1
  have t3 : ‖a * u / (h * (1 + u))‖ ≤ ((w : ℝ) - 1) / 2 * ‖u‖ / ‖h‖ := by
    rw [norm_div, norm_mul, norm_mul, ha_norm]
    have : ‖h‖ ≤ ‖h‖ * ‖1 + u‖ := le_mul_of_one_le_right hpos.le hge1
    exact div_le_div_of_nonneg_left (by positivity) hpos this
  have t4 := norm_binetI_le_W hw hh hpos
  rw [hid]
  have e1 : ‖(Complex.log (1 + u) - u) + u ^ 2 / (1 + u) - a * u / (h * (1 + u)) -
      FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖ ≤
      ‖Complex.log (1 + u) - u‖ + ‖u ^ 2 / (1 + u)‖ + ‖a * u / (h * (1 + u))‖ +
        ‖FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖ := by
    calc _ ≤ ‖(Complex.log (1 + u) - u) + u ^ 2 / (1 + u) - a * u / (h * (1 + u))‖ +
          ‖FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖ := norm_sub_le _ _
      _ ≤ (‖(Complex.log (1 + u) - u) + u ^ 2 / (1 + u)‖ + ‖a * u / (h * (1 + u))‖) +
          ‖FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖ := by
        gcongr; exact norm_sub_le _ _
      _ ≤ ((‖Complex.log (1 + u) - u‖ + ‖u ^ 2 / (1 + u)‖) + ‖a * u / (h * (1 + u))‖) +
          ‖FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖ := by
        gcongr; exact norm_add_le _ _
  refine e1.trans ?_
  have hfin := aux_dA w ‖h‖ hw1 hpos
  rw [← hu_norm] at hfin
  have t4' : ‖FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖ ≤ 1 / ‖h‖ ^ 2 := t4
  have t3' : ‖a * u / (h * (1 + u))‖ ≤ ((w : ℝ) - 1) / 2 * ‖u‖ / ‖h‖ := t3
  linarith

/-- Crude derivative bound for `1 ≤ ‖h‖ ≤ w`: `‖F_w'(h)‖ ≤ 5 w⁴ / ‖h‖²`. -/
theorem norm_stirlingDFW_le_crude {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re)
    (h1 : 1 ≤ ‖h‖) (hlt : ‖h‖ ≤ w) : ‖stirlingDFW w h‖ ≤ 5 * (w : ℝ) ^ 4 / ‖h‖ ^ 2 := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hpos : 0 < ‖h‖ := by linarith
  have hne : h ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
  have h1u_ne : 1 + (w : ℂ) / (2 * h) ≠ 0 := one_add_u_ne hh w
  have hu_norm : ‖(w : ℂ) / (2 * h)‖ = (w : ℝ) / (2 * ‖h‖) := norm_u_W w
  have hu_le : ‖(w : ℂ) / (2 * h)‖ ≤ w / 2 := by
    rw [hu_norm, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hge1 := one_le_norm_one_add_u hh w
  have hlog := norm_log_one_add_le (u := (w : ℂ) / (2 * h)) (one_le_re_one_add_u hh w)
  have ha_norm := norm_a_W hw
  have hsum : ‖(((w : ℂ) - 1) / 2 + h)‖ ≤ 3 * w / 2 := by
    have := norm_add_le (((w : ℂ) - 1) / 2) h
    rw [ha_norm] at this
    linarith
  have hI := norm_binetI_le_W hw hh hpos
  have hI1 : 1 / ‖h‖ ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hq : ‖((w : ℂ) / (2 * h ^ 2))‖ ≤ w / 2 := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_ofNat,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    have hh2 : 1 ≤ ‖h‖ ^ 2 := one_le_pow₀ h1
    nlinarith
  have hmid : ‖(((w : ℂ) - 1) / 2 + h) * ((w : ℂ) / (2 * h ^ 2)) / (1 + (w : ℂ) / (2 * h))‖ ≤
      3 * (w : ℝ) ^ 2 / 4 := by
    rw [norm_div, norm_mul]
    calc _ ≤ ‖(((w : ℂ) - 1) / 2 + h)‖ * ‖((w : ℂ) / (2 * h ^ 2))‖ / 1 := by
          apply div_le_div_of_nonneg_left (by positivity) one_pos hge1
      _ ≤ (3 * w / 2) * (w / 2) / 1 := by
          gcongr
      _ = 3 * (w : ℝ) ^ 2 / 4 := by ring
  have hbound : ‖stirlingDFW w h‖ ≤ 5 * (w : ℝ) ^ 2 := by
    unfold stirlingDFW
    calc _ ≤ ‖Complex.log (1 + (w : ℂ) / (2 * h))‖ +
          ‖(((w : ℂ) - 1) / 2 + h) * ((w : ℂ) / (2 * h ^ 2)) / (1 + (w : ℂ) / (2 * h))‖ +
          ‖FormalResearch.Special.ComplexStirling.binetI ((w : ℂ) / 2 + h)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ ((w : ℝ) / 2 + 2) + 3 * (w : ℝ) ^ 2 / 4 + 1 := by linarith
      _ ≤ 5 * (w : ℝ) ^ 2 := by nlinarith
  calc ‖stirlingDFW w h‖ ≤ 5 * (w : ℝ) ^ 2 := hbound
    _ ≤ 5 * (w : ℝ) ^ 4 / ‖h‖ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : ‖h‖ ^ 2 ≤ (w : ℝ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (w : ℝ)]

/-- Uniform derivative bound for every `‖h‖ ≥ 1`, `Re h ≥ 0`: `‖F_w'(h)‖ ≤ C_w / ‖h‖²`. -/
theorem norm_stirlingDFW_le {w : ℕ} (hw : 1 ≤ w) {h : ℂ} (hh : 0 ≤ h.re) (h1 : 1 ≤ ‖h‖) :
    ‖stirlingDFW w h‖ ≤ stirlingConstW w / ‖h‖ ^ 2 := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hpos : 0 < ‖h‖ := by linarith
  unfold stirlingConstW
  have hw2 : (1 : ℝ) ≤ (w : ℝ) ^ 2 := one_le_pow₀ hw1
  have hw4 : (w : ℝ) ^ 2 ≤ (w : ℝ) ^ 4 := by nlinarith
  by_cases hge : (w : ℝ) ≤ ‖h‖
  · refine (norm_stirlingDFW_le_of_ge hw hh hge).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  · refine (norm_stirlingDFW_le_crude hw hh h1 (le_of_not_ge hge)).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

/-! ### Transfer to `c' ω` -/

private lemma norm_cmul_W {c' : ℝ} (hc' : 0 < c') (ω : ℂ) : ‖(c' : ℂ) * ω‖ = c' * ‖ω‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'.le]

private lemma re_cmul_nonneg_W {c' : ℝ} (hc' : 0 < c') {ω : ℂ} (hω_re : 0 ≤ ω.re) :
    0 ≤ ((c' : ℂ) * ω).re := by
  rw [Complex.re_ofReal_mul]; exact mul_nonneg hc'.le hω_re

/-- `ω`-derivative of `log S^{(w)}_{c'}`. -/
theorem hasDerivAt_stirlingLogSW {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (hω_ne : ω ≠ 0) :
    HasDerivAt (stirlingLogSW w c') (stirlingDFW w ((c' : ℂ) * ω) * (c' : ℂ)) ω := by
  have hc'_c : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc'.ne'
  have hd_h : HasDerivAt (fun x : ℂ => (c' : ℂ) * x) (c' : ℂ) ω := by
    simpa using (hasDerivAt_id ω).const_mul (c' : ℂ)
  exact (hasDerivAt_stirlingFW hw (re_cmul_nonneg_W hc' hω_re) (mul_ne_zero hc'_c hω_ne)).comp ω hd_h

/-- **Bounds on `log S^{(w)}_{c'}`** (`vlo:stirling`): for `Re ω ≥ 0` and `c' ‖ω‖ ≥ 1`,
`‖log S‖ ≤ C_w / (c' ‖ω‖)`, `C_w = 7 w⁴`. -/
theorem norm_stirlingLogSW_le {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h_large : 1 ≤ c' * ‖ω‖) :
    ‖stirlingLogSW w c' ω‖ ≤ stirlingConstW w / (c' * ‖ω‖) := by
  have := norm_stirlingFW_le hw (re_cmul_nonneg_W hc' hω_re) (by rwa [norm_cmul_W hc'])
  rwa [norm_cmul_W hc'] at this

/-- `‖log S‖ ≤ (w²+2) / (c' ‖ω‖)` once `c' ‖ω‖ ≥ w`. -/
theorem norm_stirlingLogSW_le_of_ge {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h_large : (w : ℝ) ≤ c' * ‖ω‖) :
    ‖stirlingLogSW w c' ω‖ ≤ ((w : ℝ) ^ 2 + 2) / (c' * ‖ω‖) := by
  have := norm_stirlingFW_le_of_ge hw (re_cmul_nonneg_W hc' hω_re) (by rwa [norm_cmul_W hc'])
  rwa [norm_cmul_W hc'] at this

/-- **`ω`-derivative bound** (`vlo:stirling`): `‖∂_ω log S‖ ≤ C_w / (c' ‖ω‖²)` for `Re ω ≥ 0`,
`c' ‖ω‖ ≥ 1`. -/
theorem norm_deriv_stirlingLogSW_le {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h_large : 1 ≤ c' * ‖ω‖) :
    ‖deriv (stirlingLogSW w c') ω‖ ≤ stirlingConstW w / (c' * ‖ω‖ ^ 2) := by
  have hω_pos : 0 < ‖ω‖ := by
    by_contra hcon
    have h0 : ‖ω‖ = 0 := le_antisymm (not_lt.mp hcon) (norm_nonneg _)
    rw [h0, mul_zero] at h_large
    linarith
  have hω_ne : ω ≠ 0 := norm_ne_zero_iff.mp hω_pos.ne'
  rw [(hasDerivAt_stirlingLogSW hw hc' hω_re hω_ne).deriv, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hc'.le]
  have hb := norm_stirlingDFW_le hw (re_cmul_nonneg_W hc' hω_re) (by rwa [norm_cmul_W hc'])
  rw [norm_cmul_W hc'] at hb
  calc ‖stirlingDFW w ((c' : ℂ) * ω)‖ * c' ≤ stirlingConstW w / (c' * ‖ω‖) ^ 2 * c' :=
        mul_le_mul_of_nonneg_right hb hc'.le
    _ = stirlingConstW w / (c' * ‖ω‖ ^ 2) := by field_simp

/-- `‖∂_ω log S‖ ≤ (w²+1) / (c' ‖ω‖²)` once `c' ‖ω‖ ≥ w`. -/
theorem norm_deriv_stirlingLogSW_le_of_ge {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h_large : (w : ℝ) ≤ c' * ‖ω‖) :
    ‖deriv (stirlingLogSW w c') ω‖ ≤ ((w : ℝ) ^ 2 + 1) / (c' * ‖ω‖ ^ 2) := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hω_pos : 0 < ‖ω‖ := by
    by_contra hcon
    have h0 : ‖ω‖ = 0 := le_antisymm (not_lt.mp hcon) (norm_nonneg _)
    rw [h0, mul_zero] at h_large
    linarith
  have hω_ne : ω ≠ 0 := norm_ne_zero_iff.mp hω_pos.ne'
  rw [(hasDerivAt_stirlingLogSW hw hc' hω_re hω_ne).deriv, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hc'.le]
  have hb := norm_stirlingDFW_le_of_ge hw (re_cmul_nonneg_W hc' hω_re) (by rwa [norm_cmul_W hc'])
  rw [norm_cmul_W hc'] at hb
  calc ‖stirlingDFW w ((c' : ℂ) * ω)‖ * c' ≤ ((w : ℝ) ^ 2 + 1) / (c' * ‖ω‖) ^ 2 * c' :=
        mul_le_mul_of_nonneg_right hb hc'.le
    _ = ((w : ℝ) ^ 2 + 1) / (c' * ‖ω‖ ^ 2) := by field_simp

/-! ### Bounds on `S^{(w)}` -/

private lemma norm_exp_sub_one_le_W (z : ℂ) : ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ * Real.exp ‖z‖ := by
  by_cases hz : ‖z‖ ≤ 1
  · calc ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := Complex.norm_exp_sub_one_le hz
      _ = 2 * ‖z‖ * 1 := by ring
      _ ≤ 2 * ‖z‖ * Real.exp ‖z‖ := by
        gcongr; exact Real.one_le_exp (norm_nonneg _)
  · have hz1 : 1 ≤ ‖z‖ := le_of_not_ge hz
    have hexp : ‖Complex.exp z‖ ≤ Real.exp ‖z‖ := by
      rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (Complex.re_le_norm _)
    have h1 : 1 ≤ Real.exp ‖z‖ := Real.one_le_exp (norm_nonneg _)
    calc ‖Complex.exp z - 1‖ ≤ ‖Complex.exp z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.exp ‖z‖ + 1 := by rw [norm_one]; linarith
      _ ≤ 2 * Real.exp ‖z‖ := by linarith
      _ ≤ 2 * ‖z‖ * Real.exp ‖z‖ := by nlinarith [Real.exp_pos ‖z‖]

/-- `‖S‖ ≤ exp C_w` for `Re ω ≥ 0`, `c' ‖ω‖ ≥ 1`. -/
theorem norm_stirlingSW_le {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h_large : 1 ≤ c' * ‖ω‖) :
    ‖stirlingSW w c' ω‖ ≤ Real.exp (stirlingConstW w) := by
  have hF := norm_stirlingLogSW_le hw hc' hω_re h_large
  have hK : stirlingConstW w / (c' * ‖ω‖) ≤ stirlingConstW w := by
    apply div_le_self (stirlingConstW_pos hw).le h_large
  unfold stirlingSW
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hF.trans hK))

/-- `‖S⁻¹‖ ≤ exp C_w` for `Re ω ≥ 0`, `c' ‖ω‖ ≥ 1`. -/
theorem norm_stirlingSW_inv_le {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h_large : 1 ≤ c' * ‖ω‖) :
    ‖(stirlingSW w c' ω)⁻¹‖ ≤ Real.exp (stirlingConstW w) := by
  have hF := norm_stirlingLogSW_le hw hc' hω_re h_large
  have hK : stirlingConstW w / (c' * ‖ω‖) ≤ stirlingConstW w := by
    apply div_le_self (stirlingConstW_pos hw).le h_large
  unfold stirlingSW
  rw [← Complex.exp_neg, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
  rw [norm_neg]
  exact hF.trans hK

/-- `‖S - 1‖ ≤ 2 C_w e^{C_w} / (c' ‖ω‖)` for `Re ω ≥ 0`, `c' ‖ω‖ ≥ 1`
(`S = 1 + O_w((c' |ω|)^{-1})`). -/
theorem norm_stirlingSW_sub_one_le {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h_large : 1 ≤ c' * ‖ω‖) :
    ‖stirlingSW w c' ω - 1‖ ≤
      2 * stirlingConstW w * Real.exp (stirlingConstW w) / (c' * ‖ω‖) := by
  have hF := norm_stirlingLogSW_le hw hc' hω_re h_large
  have hK : stirlingConstW w / (c' * ‖ω‖) ≤ stirlingConstW w := by
    apply div_le_self (stirlingConstW_pos hw).le h_large
  have hpos : 0 < c' * ‖ω‖ := by linarith
  unfold stirlingSW
  calc _ ≤ 2 * ‖stirlingLogSW w c' ω‖ * Real.exp ‖stirlingLogSW w c' ω‖ :=
        norm_exp_sub_one_le_W _
    _ ≤ 2 * (stirlingConstW w / (c' * ‖ω‖)) * Real.exp (stirlingConstW w) := by
        have e1 : Real.exp ‖stirlingLogSW w c' ω‖ ≤ Real.exp (stirlingConstW w) :=
          Real.exp_le_exp.mpr (hF.trans hK)
        exact mul_le_mul (by linarith [hF]) e1 (Real.exp_pos _).le
          (by have := stirlingConstW_pos hw; positivity)
    _ = _ := by ring

/-- Absolute bounds `‖S‖ ≤ 2`, `‖S⁻¹‖ ≤ 2` and `‖S - 1‖ ≤ 2 (w²+2)/(c' ‖ω‖)`: these need
`c' ‖ω‖ ≥ max (w, 2 (w²+2))`. The paper's threshold `48` suffices exactly for `w ≤ 4`. -/
theorem norm_stirlingSW_abs_bounds {w : ℕ} (hw : 1 ≤ w) {c' : ℝ} (hc' : 0 < c') {ω : ℂ}
    (hω_re : 0 ≤ ω.re) (h_w : (w : ℝ) ≤ c' * ‖ω‖) (h_two : 2 * ((w : ℝ) ^ 2 + 2) ≤ c' * ‖ω‖) :
    ‖stirlingSW w c' ω‖ ≤ 2 ∧ ‖(stirlingSW w c' ω)⁻¹‖ ≤ 2 ∧
      ‖stirlingSW w c' ω - 1‖ ≤ 2 * ((w : ℝ) ^ 2 + 2) / (c' * ‖ω‖) := by
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hpos : 0 < c' * ‖ω‖ := by nlinarith
  have hF := norm_stirlingLogSW_le_of_ge hw hc' hω_re h_w
  have hhalf : ((w : ℝ) ^ 2 + 2) / (c' * ‖ω‖) ≤ 1 / 2 := by
    rw [div_le_iff₀ hpos]; linarith
  have hF2 : ‖stirlingLogSW w c' ω‖ ≤ 1 / 2 := hF.trans hhalf
  have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have h1 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h2 := Real.exp_one_lt_d9
    have h3 := Real.exp_pos (1 / 2 : ℝ)
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · unfold stirlingSW
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hF2)).trans hexp
  · unfold stirlingSW
    rw [← Complex.exp_neg, Complex.norm_exp]
    refine (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)).trans hexp
    rw [norm_neg]; exact hF2
  · unfold stirlingSW
    calc _ ≤ 2 * ‖stirlingLogSW w c' ω‖ := Complex.norm_exp_sub_one_le (by linarith)
      _ ≤ 2 * (((w : ℝ) ^ 2 + 2) / (c' * ‖ω‖)) := by gcongr
      _ = _ := by ring

/-- For `w ≤ 4` the paper's threshold `c' ‖ω‖ ≥ 48` gives `‖S^{(w)}‖, ‖S^{(w)-1}‖ ≤ 2`. -/
theorem norm_stirlingSW_le_two_of_le_four {w : ℕ} (hw : 1 ≤ w) (hw4 : w ≤ 4) {c' : ℝ}
    (hc' : 0 < c') {ω : ℂ} (hω_re : 0 ≤ ω.re) (h_large : 48 ≤ c' * ‖ω‖) :
    ‖stirlingSW w c' ω‖ ≤ 2 ∧ ‖(stirlingSW w c' ω)⁻¹‖ ≤ 2 := by
  have hw4' : (w : ℝ) ≤ 4 := by exact_mod_cast hw4
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have := norm_stirlingSW_abs_bounds hw hc' hω_re (by linarith) (by nlinarith)
  exact ⟨this.1, this.2.1⟩

/-! ### Axiom verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.gamma_mul_two_pi_t_cpow_neg_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gamma_mul_two_pi_t_cpow_neg_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.norm_stirlingLogSW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_stirlingLogSW_le

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.norm_deriv_stirlingLogSW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_deriv_stirlingLogSW_le

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.norm_stirlingSW_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_stirlingSW_sub_one_le

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.norm_stirlingSW_abs_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_stirlingSW_abs_bounds

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.stirlingLogSW_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stirlingLogSW_one

end FormalResearch.ModularBootstrap.FixedWeightBand
