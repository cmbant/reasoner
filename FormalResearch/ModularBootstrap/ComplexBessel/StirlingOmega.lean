module

public import FormalResearch.Asymptotics.BinetRemainder
public import FormalResearch.CohnElkies.MellinKernel
public import FormalResearch.Special.ComplexStirlingKernel
public import FormalResearch.Special.ComplexStirlingRemainder
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Stirling Expansion with `ω`-Derivative (`vlo:stirling`, R11)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2, eq. `vlo:stirling` (around
lines 356–369) and recalled input R11.

For `ω = μ + i ν` (`Re ω ≥ 0`, `ω ≠ 0`), `z = 1/2 + c' ω`, `t = c' b^2 / 3` (`Re b > 0`),
and `J(ω; b) = ω (log(3ω/(2πe)) - 2 log b)` (principal logarithms):
`Γ(z) (2π t)^{-z} = t^{-1/2} e^{c' J(ω; b)} S_{c'}(ω)`,
where `S_{c'}(ω) = exp(c' ω log(1 + 1/(2 c' ω)) - 1/2 + B_Bin(z))` satisfies:
* `S_{c'}(ω) = 1 + O((c' |ω|)^{-1})` uniformly for `Re ω ≥ 0`, `c' |ω| ≥ 1`;
* `|∂_ω log S_{c'}(ω)| ≤ (7/4) c'^{-1} |ω|^{-2}` uniformly for `Re ω ≥ 0`, `c' |ω| ≥ 1`,
  proved via `ComplexStirling.norm_binetB_le_div` and `ComplexStirling.norm_binetI_le_div`
  (note: `Asymptotics.binetRem_iteratedDeriv_norm_le` alone gives `O((Re z)^{-2})`, which is
  `O(1)` on the imaginary axis `Re ω = 0`, whereas `ComplexStirling.norm_binetI_le_div` gives
  the full `O(‖z‖^{-2})` bound on `Re z > 0`).

## Main definitions and results
* `stirlingJ`, `stirlingLogS`, `stirlingS`: `J(ω; b)`, `log S_{c'}(ω)`, and `S_{c'}(ω)`.
* `gamma_mul_two_pi_t_cpow_neg`: exact Stirling factorization `vlo:stirling`.
* `norm_stirlingLogS_le`, `norm_stirlingS_sub_one_le`, `norm_stirlingS_inv_le`: uniform bounds
  on `log S_{c'}`, `S_{c'} - 1`, and `S_{c'}^{-1}`.
* `hasDerivAt_stirlingLogS`, `norm_deriv_stirlingLogS_le`: `ω`-derivative of `log S_{c'}`
  and the `O(c'^{-1} |ω|^{-2})` bound.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.ComplexBessel

/-! ### Section 1: Definitions and branch identities -/

/-- Principal-branch Stirling phase `J(ω; b) = ω (log(3ω / (2π e)) - 2 log b)` (`lower_o1_two_edge.tex`,
§J2). -/
noncomputable def stirlingJ (ω b : ℂ) : ℂ :=
  ω * (Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) - 2 * Complex.log b)

/-- Logarithm of the Stirling correction `log S_{c'}(ω) = h log(1 + 1/(2h)) - 1/2 + B_Bin(1/2 + h)`
for `h = c' ω` (`lower_o1_two_edge.tex`, §J2, line 368). -/
noncomputable def stirlingLogS (c' : ℝ) (ω : ℂ) : ℂ :=
  ((c' : ℂ) * ω) * Complex.log (1 + 1 / (2 * (c' : ℂ) * ω)) - 1 / 2 +
    FormalResearch.Asymptotics.binetRem (1 / 2 + (c' : ℂ) * ω)

/-- Stirling correction factor `S_{c'}(ω) = exp(log S_{c'}(ω))`. -/
noncomputable def stirlingS (c' : ℝ) (ω : ℂ) : ℂ :=
  Complex.exp (stirlingLogS c' ω)

private lemma log_ofReal_pos_mul {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) :
    Complex.log ((r : ℂ) * w) = (Real.log r : ℂ) + Complex.log w := by
  have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have harg : (r : ℂ).arg + w.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hr.le, zero_add]
    exact ⟨Complex.neg_pi_lt_arg w, Complex.arg_le_pi w⟩
  rw [Complex.log_mul hr_c hw harg, ← Complex.ofReal_log hr.le]

private lemma log_sq_of_re_pos {b : ℂ} (hb : 0 < b.re) :
    Complex.log (b ^ 2) = 2 * Complex.log b := by
  have hb_ne : b ≠ 0 := by intro h; rw [h, Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have harg_lt : |b.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have harg_mem : b.arg + b.arg ∈ Ioc (-Real.pi) Real.pi := by
    have := abs_lt.mp harg_lt
    exact ⟨by linarith, by linarith⟩
  rw [sq, Complex.log_mul hb_ne hb_ne harg_mem, two_mul]

private lemma re_one_add_inv_two_mul_pos {h : ℂ} (hh : 0 ≤ h.re) (hne : h ≠ 0) :
    0 < (1 + 1 / (2 * h)).re := by
  have hnorm_sq_pos : 0 < Complex.normSq (2 * h) :=
    Complex.normSq_pos.mpr (mul_ne_zero two_ne_zero hne)
  have hdiv_re : (1 / (2 * h)).re = (2 * h.re) / Complex.normSq (2 * h) := by
    rw [one_div, Complex.inv_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [Complex.add_re, Complex.one_re, hdiv_re]
  have hnn : 0 ≤ (2 * h.re) / Complex.normSq (2 * h) := by positivity
  linarith

private lemma log_add_half_eq {h : ℂ} (hh : 0 ≤ h.re) (hne : h ≠ 0) :
    Complex.log (h + 1 / 2) = Complex.log h + Complex.log (1 + 1 / (2 * h)) := by
  have hre_u : 0 < (1 + 1 / (2 * h)).re := re_one_add_inv_two_mul_pos hh hne
  have hu_ne : 1 + 1 / (2 * h) ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hre_u; exact lt_irrefl 0 hre_u
  have harg_h : |h.arg| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr hh
  have harg_u : |(1 + 1 / (2 * h)).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_u)
  have harg_mem : h.arg + (1 + 1 / (2 * h)).arg ∈ Ioc (-Real.pi) Real.pi := by
    have h1 := abs_le.mp harg_h
    have h2 := abs_lt.mp harg_u
    exact ⟨by linarith, by linarith⟩
  have hmul_eq : h + 1 / 2 = h * (1 + 1 / (2 * h)) := by
    field_simp [hne]
  rw [hmul_eq, Complex.log_mul hne hu_ne harg_mem]

/-- **Stirling factorization (`lower_o1_two_edge.tex`, eq. `vlo:stirling`)**:
for `c' > 0`, `Re ω ≥ 0`, `ω ≠ 0`, `Re b > 0`, `z = 1/2 + c' ω`, `t = c' b^2 / 3`,
`Γ(z) (2π t)^{-z} = t^{-1/2} e^{c' J(ω; b)} S_{c'}(ω)`. -/
theorem gamma_mul_two_pi_t_cpow_neg {c' : ℝ} (hc' : 0 < c') {ω b : ℂ}
    (hω_re : 0 ≤ ω.re) (hω_ne : ω ≠ 0) (hb_re : 0 < b.re) :
    let z : ℂ := 1 / 2 + (c' : ℂ) * ω
    let t : ℂ := (c' : ℂ) * b ^ 2 / 3
    Complex.Gamma z * (2 * (Real.pi : ℂ) * t) ^ (-z) =
      t ^ (-(1 / 2 : ℂ)) * Complex.exp ((c' : ℂ) * stirlingJ ω b) * stirlingS c' ω := by
  intro z t
  have hc'_c : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc'.ne'
  have hb_ne : b ≠ 0 := by intro h; rw [h, Complex.zero_re] at hb_re; exact lt_irrefl 0 hb_re
  have ht_ne : t ≠ 0 := by
    dsimp [t]; exact div_ne_zero (mul_ne_zero hc'_c (pow_ne_zero 2 hb_ne)) three_ne_zero
  have h2pit_ne : 2 * (Real.pi : ℂ) * t ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) ht_ne
  set h : ℂ := (c' : ℂ) * ω
  have hh_re : 0 ≤ h.re := by
    dsimp [h]; rw [Complex.re_ofReal_mul]; exact mul_nonneg hc'.le hω_re
  have hh_ne : h ≠ 0 := mul_ne_zero hc'_c hω_ne
  have hz_re : 0 < z.re := by
    simp only [z, Complex.add_re, Complex.re_ofReal_mul]
    norm_num
    linarith [mul_nonneg hc'.le hω_re]
  have hgam : Complex.Gamma z = Complex.exp ((z - 1 / 2) * Complex.log z - z +
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + FormalResearch.Asymptotics.binetRem z) :=
    (FormalResearch.CohnElkies.exp_stirling_add_binetRem_eq_gamma hz_re).symm
  have hcpow_t : (2 * (Real.pi : ℂ) * t) ^ (-z) =
      Complex.exp (-z * Complex.log (2 * (Real.pi : ℂ) * t)) :=
    (Complex.cpow_def_of_ne_zero h2pit_ne (-z)).trans (by rw [mul_comm])
  have hcpow_t_half : t ^ (-(1 / 2 : ℂ)) = Complex.exp (-(1 / 2 : ℂ) * Complex.log t) :=
    (Complex.cpow_def_of_ne_zero ht_ne _).trans (by rw [mul_comm])
  have hlog_2pit : Complex.log (2 * (Real.pi : ℂ) * t) =
      (Real.log (2 * Real.pi) : ℂ) + Complex.log t := by
    simpa [Complex.ofReal_mul] using log_ofReal_pos_mul (by positivity : (0 : ℝ) < 2 * Real.pi) ht_ne
  have hlog_t : Complex.log t = (Real.log (c' / 3) : ℂ) + 2 * Complex.log b := by
    have ht_eq : t = ((c' / 3 : ℝ) : ℂ) * b ^ 2 := by dsimp [t]; push_cast; ring
    rw [ht_eq, log_ofReal_pos_mul (by positivity : (0 : ℝ) < c' / 3) (pow_ne_zero 2 hb_ne),
      log_sq_of_re_pos hb_re]
  have hz_eq : z = h + 1 / 2 := by dsimp [z, h]; ring
  have hlog_z : Complex.log z = Complex.log h + Complex.log (1 + 1 / (2 * h)) := by
    rw [hz_eq]; exact log_add_half_eq hh_re hh_ne
  have hlog_h : Complex.log h = (Real.log c' : ℂ) + Complex.log ω :=
    log_ofReal_pos_mul hc' hω_ne
  have hlog_J : Complex.log (3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ))) =
      (Real.log (3 / (2 * Real.pi)) - 1 : ℝ) + Complex.log ω := by
    have hr_pos : 0 < 3 / (2 * Real.pi * Real.exp 1) := by positivity
    have heq : 3 * ω / (2 * (Real.pi : ℂ) * (Real.exp 1 : ℂ)) =
        ((3 / (2 * Real.pi * Real.exp 1) : ℝ) : ℂ) * ω := by push_cast; ring
    rw [heq, log_ofReal_pos_mul hr_pos hω_ne,
      Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (Real.exp_pos 1).ne',
      Real.log_exp]
    have hsub : Real.log (3 : ℝ) - (Real.log (2 * Real.pi) + 1) = Real.log (3 / (2 * Real.pi)) - 1 := by
      rw [Real.log_div (by norm_num) (by positivity)]; ring
    rw [hsub]
  have hreal_logs : Real.log c' - Real.log (2 * Real.pi) - Real.log (c' / 3) - 1 =
      Real.log (3 / (2 * Real.pi)) - 1 := by
    rw [Real.log_div hc'.ne' (by norm_num), Real.log_div (by norm_num) (by positivity)]
    ring
  unfold stirlingS stirlingLogS stirlingJ
  rw [hgam, hcpow_t, hcpow_t_half, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [hlog_2pit, hlog_t, hlog_z, hlog_h, hlog_J]
  have hz_sub : z - 1 / 2 = h := by dsimp [z, h]; ring
  have hz_neg : -z = -(1 / 2 : ℂ) - h := by dsimp [z, h]; ring
  have h2pi_half : ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) =
      (1 / 2 : ℂ) * (Real.log (2 * Real.pi) : ℂ) := by push_cast; ring
  have hz_arg : 1 / 2 + (c' : ℂ) * ω = z := rfl
  rw [hz_sub, hz_arg, h2pi_half]
  -- Cancel the 1/2 log t, 1/2 log(2π), and compare the remaining h-terms
  have hlog_id : (Real.log c' : ℂ) - (Real.log (2 * Real.pi) : ℂ) - (Real.log (c' / 3) : ℂ) - 1 =
      ((Real.log (3 / (2 * Real.pi)) - 1 : ℝ) : ℂ) := by
    exact_mod_cast hreal_logs
  calc h * (↑(Real.log c') + Complex.log ω + Complex.log (1 + 1 / (2 * h))) - z +
        1 / 2 * ↑(Real.log (2 * Real.pi)) + Asymptotics.binetRem z +
        -z * (↑(Real.log (2 * Real.pi)) + (↑(Real.log (c' / 3)) + 2 * Complex.log b))
      = -(1 / 2 : ℂ) * (↑(Real.log (c' / 3)) + 2 * Complex.log b) +
          h * ((↑(Real.log c') - ↑(Real.log (2 * Real.pi)) - ↑(Real.log (c' / 3)) - 1) +
            Complex.log ω - 2 * Complex.log b) +
          (h * Complex.log (1 + 1 / (2 * h)) - 1 / 2 + Asymptotics.binetRem z) := by
        dsimp [z, h]; ring
    _ = -(1 / 2 : ℂ) * (↑(Real.log (c' / 3)) + 2 * Complex.log b) +
          (c' : ℂ) * (ω * (↑(Real.log (3 / (2 * Real.pi)) - 1) + Complex.log ω - 2 * Complex.log b)) +
          ((c' : ℂ) * ω * Complex.log (1 + 1 / (2 * (c' : ℂ) * ω)) - 1 / 2 + Asymptotics.binetRem z) := by
        rw [hlog_id]; dsimp [h]; ring_nf

/-! ### Section 2: Uniform bounds on `S_{c'}(ω)` and its `ω`-derivative -/

private lemma norm_half_add_ge {h : ℂ} (hh : 0 ≤ h.re) : ‖h‖ ≤ ‖1 / 2 + h‖ := by
  have hsq : ‖h‖ ^ 2 ≤ ‖1 / 2 + h‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.add_im,
      Complex.div_ofNat_im, Complex.one_im, zero_div, zero_add]
    nlinarith
  have h1 : √(‖h‖ ^ 2) ≤ √(‖1 / 2 + h‖ ^ 2) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

/-- `‖log S_{c'}(ω)‖ ≤ (9/4) / (c' ‖ω‖)` uniformly for `Re ω ≥ 0` and `c' ‖ω‖ ≥ 1`. -/
theorem norm_stirlingLogS_le {c' : ℝ} (hc' : 0 < c') {ω : ℂ} (hω_re : 0 ≤ ω.re)
    (h_large : 1 ≤ c' * ‖ω‖) :
    ‖stirlingLogS c' ω‖ ≤ (9 / 4 : ℝ) / (c' * ‖ω‖) := by
  set h : ℂ := (c' : ℂ) * ω
  have hh_norm : ‖h‖ = c' * ‖ω‖ := by
    dsimp [h]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'.le]
  have hh_pos : 0 < ‖h‖ := by rw [hh_norm]; linarith
  have hh_re : 0 ≤ h.re := by dsimp [h]; rw [Complex.re_ofReal_mul]; exact mul_nonneg hc'.le hω_re
  have hz_re : 0 < (1 / 2 + h).re := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  set u : ℂ := 1 / (2 * h)
  have hu_norm : ‖u‖ = 1 / (2 * ‖h‖) := by
    dsimp [u]; rw [one_div, norm_inv, norm_mul, Complex.norm_ofNat, one_div]
  have hu_le : ‖u‖ ≤ 1 / 2 := by
    rw [hu_norm, hh_norm, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hu_lt1 : ‖u‖ < 1 := lt_of_le_of_lt hu_le (by norm_num)
  have hlog_err : ‖h * Complex.log (1 + u) - 1 / 2‖ ≤ 1 / (4 * ‖h‖) := by
    have hhu : h * u = 1 / 2 := by
      have hh_ne : h ≠ 0 := norm_ne_zero_iff.mp hh_pos.ne'
      dsimp [u]; field_simp [hh_ne]
    have hid : h * Complex.log (1 + u) - 1 / 2 = h * (Complex.log (1 + u) - u) := by
      rw [mul_sub, hhu]
    rw [hid, norm_mul]
    have h1 : ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 :=
      Complex.norm_log_one_add_sub_self_le hu_lt1
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (sub_pos.mpr hu_lt1) two_pos]; linarith
    have h2 : ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
      calc ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 := h1
        _ ≤ ‖u‖ ^ 2 * 2 / 2 := by gcongr
        _ = ‖u‖ ^ 2 := by ring
    calc ‖h‖ * ‖Complex.log (1 + u) - u‖ ≤ ‖h‖ * ‖u‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖h‖ * (1 / (2 * ‖h‖)) ^ 2 := by rw [hu_norm]
      _ = 1 / (4 * ‖h‖) := by field_simp [hh_pos.ne']; ring
  have hbin_err : ‖FormalResearch.Asymptotics.binetRem (1 / 2 + h)‖ ≤ 2 / ‖h‖ := by
    rw [FormalResearch.CohnElkies.binetRem_eq_binetB hz_re]
    calc ‖FormalResearch.Special.ComplexStirling.binetB (1 / 2 + h)‖
        ≤ 2 / ‖1 / 2 + h‖ := FormalResearch.Special.ComplexStirling.norm_binetB_le_div hz_re
      _ ≤ 2 / ‖h‖ := div_le_div_of_nonneg_left (by norm_num) hh_pos (norm_half_add_ge hh_re)
  have hlog_eq : stirlingLogS c' ω =
      (h * Complex.log (1 + u) - 1 / 2) + FormalResearch.Asymptotics.binetRem (1 / 2 + h) := by
    unfold stirlingLogS; dsimp [h, u]; ring_nf
  rw [hlog_eq]
  calc ‖(h * Complex.log (1 + u) - 1 / 2) + FormalResearch.Asymptotics.binetRem (1 / 2 + h)‖
      ≤ ‖h * Complex.log (1 + u) - 1 / 2‖ + ‖FormalResearch.Asymptotics.binetRem (1 / 2 + h)‖ :=
        norm_add_le _ _
    _ ≤ 1 / (4 * ‖h‖) + 2 / ‖h‖ := add_le_add hlog_err hbin_err
    _ = (9 / 4 : ℝ) / (c' * ‖ω‖) := by rw [hh_norm]; ring

/-- Uniform Stirling asymptotic `‖S_{c'}(ω) - 1‖ ≤ (24 / (c' ‖ω‖))` for `Re ω ≥ 0` and
`c' ‖ω‖ ≥ 1` (`vlo:stirling`: `S_{c'}(ω) = 1 + O((c' |ω|)^{-1})`). -/
theorem norm_stirlingS_sub_one_le {c' : ℝ} (hc' : 0 < c') {ω : ℂ} (hω_re : 0 ≤ ω.re)
    (h_large : 1 ≤ c' * ‖ω‖) :
    ‖stirlingS c' ω - 1‖ ≤ 24 / (c' * ‖ω‖) := by
  have hlog := norm_stirlingLogS_le hc' hω_re h_large
  have hle_exp : ‖stirlingLogS c' ω‖ ≤ 9 / 4 := by
    calc ‖stirlingLogS c' ω‖ ≤ (9 / 4 : ℝ) / (c' * ‖ω‖) := hlog
      _ ≤ (9 / 4 : ℝ) / 1 := by gcongr
      _ = 9 / 4 := by ring
  by_cases h1 : ‖stirlingLogS c' ω‖ ≤ 1
  · calc ‖stirlingS c' ω - 1‖ = ‖Complex.exp (stirlingLogS c' ω) - 1‖ := rfl
      _ ≤ 2 * ‖stirlingLogS c' ω‖ := Complex.norm_exp_sub_one_le h1
      _ ≤ 2 * ((9 / 4 : ℝ) / (c' * ‖ω‖)) := by gcongr
      _ = (9 / 2 : ℝ) / (c' * ‖ω‖) := by ring
      _ ≤ 24 / (c' * ‖ω‖) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  · have hge1 : 1 ≤ ‖stirlingLogS c' ω‖ := le_of_not_ge h1
    have hinv_ge : 4 / 9 ≤ 1 / (c' * ‖ω‖) := by
      have hdiv : (1 : ℝ) ≤ (9 / 4 : ℝ) / (c' * ‖ω‖) := hge1.trans hlog
      rw [le_div_iff₀ (by positivity)] at hdiv
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    have hexp_94 : Real.exp (9 / 4 : ℝ) ≤ 9.6 := by
      have hb := Real.exp_bound' (x := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (n := 5) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        Nat.factorial] at hb
      norm_num at hb
      have h34 : Real.exp (3 / 4 : ℝ) ≤ 2.12 := by linarith
      have h3 : Real.exp (9 / 4 : ℝ) = Real.exp (3 / 4 : ℝ) ^ 3 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num
      rw [h3]
      calc Real.exp (3 / 4 : ℝ) ^ 3 ≤ (2.12 : ℝ) ^ 3 := by gcongr
        _ ≤ 9.6 := by norm_num
    have hexp_bd : ‖Complex.exp (stirlingLogS c' ω)‖ ≤ 9.6 := by
      rw [Complex.norm_exp]
      exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hle_exp)).trans hexp_94
    calc ‖stirlingS c' ω - 1‖ = ‖Complex.exp (stirlingLogS c' ω) - 1‖ := rfl
      _ ≤ ‖Complex.exp (stirlingLogS c' ω)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 9.6 + 1 := by rw [norm_one]; linarith
      _ ≤ 24 * (4 / 9) := by norm_num
      _ ≤ 24 * (1 / (c' * ‖ω‖)) := by gcongr
      _ = 24 / (c' * ‖ω‖) := by ring

/-- Lower and reciprocal bound `‖S_{c'}(ω)⁻¹‖ ≤ 2` for `Re ω ≥ 0` and `c' ‖ω‖ ≥ 48`. -/
theorem norm_stirlingS_inv_le {c' : ℝ} (hc' : 0 < c') {ω : ℂ} (hω_re : 0 ≤ ω.re)
    (h_large : 48 ≤ c' * ‖ω‖) :
    ‖(stirlingS c' ω)⁻¹‖ ≤ 2 := by
  have h1 : 1 ≤ c' * ‖ω‖ := by linarith
  have hsub : ‖stirlingS c' ω - 1‖ ≤ 1 / 2 := by
    calc ‖stirlingS c' ω - 1‖ ≤ 24 / (c' * ‖ω‖) := norm_stirlingS_sub_one_le hc' hω_re h1
      _ ≤ 24 / 48 := by gcongr
      _ = 1 / 2 := by norm_num
  have hge : 1 / 2 ≤ ‖stirlingS c' ω‖ := by
    have := norm_sub_norm_le (1 : ℂ) (stirlingS c' ω)
    rw [norm_one, norm_sub_rev] at this
    linarith
  rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

private lemma hasDerivAt_binetRem {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt FormalResearch.Asymptotics.binetRem
      (-FormalResearch.Special.ComplexStirling.binetI z) z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : FormalResearch.Asymptotics.binetRem =ᶠ[𝓝 z]
      FormalResearch.Special.ComplexStirling.binetB := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact FormalResearch.CohnElkies.binetRem_eq_binetB hw
  exact (FormalResearch.Special.ComplexStirling.hasDerivAt_binetB hz).congr_of_eventuallyEq hev

/-- Derivative of `log S_{c'}(ω)` with respect to `ω` for `Re ω ≥ 0`, `ω ≠ 0`, `c' > 0`
(and `1 + 1 / (2 c' ω) ∈ slitPlane`, which holds unconditionally for `Re ω ≥ 0, ω ≠ 0`). -/
theorem hasDerivAt_stirlingLogS {c' : ℝ} (hc' : 0 < c') {ω : ℂ} (hω_re : 0 ≤ ω.re)
    (hω_ne : ω ≠ 0) :
    let h : ℂ := (c' : ℂ) * ω
    let u : ℂ := 1 / (2 * h)
    HasDerivAt (stirlingLogS c')
      ((c' : ℂ) * (Complex.log (1 + u) - u / (1 + u)) -
        (c' : ℂ) * FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h)) ω := by
  intro h u
  have hc'_c : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc'.ne'
  have hh_ne : h ≠ 0 := mul_ne_zero hc'_c hω_ne
  have hh_re : 0 ≤ h.re := by dsimp [h]; rw [Complex.re_ofReal_mul]; exact mul_nonneg hc'.le hω_re
  have h1u_re : 0 < (1 + u).re := re_one_add_inv_two_mul_pos hh_re hh_ne
  have h1u_slit : 1 + u ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl h1u_re)
  have h1u_ne : 1 + u ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at h1u_re; exact lt_irrefl 0 h1u_re
  have hz_re : 0 < (1 / 2 + h).re := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  have hd_h : HasDerivAt (fun w : ℂ => (c' : ℂ) * w) (c' : ℂ) ω := by
    simpa using (hasDerivAt_id ω).const_mul (c' : ℂ)
  have hd_u : HasDerivAt (fun w : ℂ => 1 / (2 * ((c' : ℂ) * w)))
      (-(c' : ℂ) / (2 * h ^ 2)) ω := by
    have h2cw : HasDerivAt (fun w : ℂ => 2 * ((c' : ℂ) * w)) (2 * (c' : ℂ)) ω :=
      hd_h.const_mul 2
    have hinv := (h2cw.inv (mul_ne_zero two_ne_zero hh_ne)).congr_deriv (g' := -(c' : ℂ) / (2 * h ^ 2)) (by
      dsimp [h]; field_simp [two_ne_zero, hc'_c, hω_ne])
    convert hinv using 1
    ext w
    rw [one_div]
    rfl
  have hd_1u : HasDerivAt (fun w : ℂ => 1 + 1 / (2 * ((c' : ℂ) * w)))
      (-(c' : ℂ) / (2 * h ^ 2)) ω := by
    simpa using hd_u.const_add 1
  have hd_log : HasDerivAt (fun w : ℂ => Complex.log (1 + 1 / (2 * ((c' : ℂ) * w))))
      ((-(c' : ℂ) / (2 * h ^ 2)) / (1 + u)) ω :=
    hd_1u.clog h1u_slit
  have hd_prod : HasDerivAt
      (fun w : ℂ => ((c' : ℂ) * w) * Complex.log (1 + 1 / (2 * (c' : ℂ) * w)) - 1 / 2)
      ((c' : ℂ) * Complex.log (1 + u) + h * ((-(c' : ℂ) / (2 * h ^ 2)) / (1 + u))) ω := by
    have heq : (fun w : ℂ => ((c' : ℂ) * w) * Complex.log (1 + 1 / (2 * (c' : ℂ) * w)) - 1 / 2) =
        fun w : ℂ => ((c' : ℂ) * w) * Complex.log (1 + 1 / (2 * ((c' : ℂ) * w))) - 1 / 2 := by
      ext w; ring_nf
    rw [heq]
    exact ((hd_h.mul hd_log).sub_const (1 / 2 : ℂ))
  have hd_bin : HasDerivAt
      (fun w : ℂ => FormalResearch.Asymptotics.binetRem (1 / 2 + (c' : ℂ) * w))
      (-FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h) * (c' : ℂ)) ω := by
    have hb : HasDerivAt FormalResearch.Asymptotics.binetRem
        (-FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h))
        ((fun w : ℂ => 1 / 2 + (c' : ℂ) * w) ω) := hasDerivAt_binetRem hz_re
    exact hb.comp ω (hd_h.const_add (1 / 2 : ℂ))
  refine (hd_prod.add hd_bin).congr_deriv ?_
  dsimp [u]
  field_simp [hh_ne, h1u_ne]
  ring

/-- **Uniform `ω`-derivative bound for `log S_{c'}(ω)`** (`lower_o1_two_edge.tex`, §J2, line 368):
for `c' > 0`, `Re ω ≥ 0`, `c' ‖ω‖ ≥ 1`,
`‖∂_ω log S_{c'}(ω)‖ ≤ (7 / 4) / (c' ‖ω‖^2)`. -/
theorem norm_deriv_stirlingLogS_le {c' : ℝ} (hc' : 0 < c') {ω : ℂ} (hω_re : 0 ≤ ω.re)
    (h_large : 1 ≤ c' * ‖ω‖) :
    ‖deriv (stirlingLogS c') ω‖ ≤ (7 / 4 : ℝ) / (c' * ‖ω‖ ^ 2) := by
  have hω_pos : 0 < ‖ω‖ := by
    by_contra h
    have h0 : ‖ω‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0, mul_zero] at h_large
    linarith
  have hω_ne : ω ≠ 0 := norm_ne_zero_iff.mp hω_pos.ne'
  have hd := hasDerivAt_stirlingLogS hc' hω_re hω_ne
  rw [hd.deriv]
  set h : ℂ := (c' : ℂ) * ω
  set u : ℂ := 1 / (2 * h)
  have hh_norm : ‖h‖ = c' * ‖ω‖ := by
    dsimp [h]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'.le]
  have hh_pos : 0 < ‖h‖ := by rw [hh_norm]; linarith
  have hh_re : 0 ≤ h.re := by dsimp [h]; rw [Complex.re_ofReal_mul]; exact mul_nonneg hc'.le hω_re
  have hz_re : 0 < (1 / 2 + h).re := by
    rw [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  have hu_norm : ‖u‖ = 1 / (2 * ‖h‖) := by
    dsimp [u]; rw [one_div, norm_inv, norm_mul, Complex.norm_ofNat, one_div]
  have hu_le : ‖u‖ ≤ 1 / 2 := by
    rw [hu_norm, hh_norm, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hu_lt1 : ‖u‖ < 1 := lt_of_le_of_lt hu_le (by norm_num)
  have h1u_ge : 1 / 2 ≤ ‖1 + u‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-u)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have h1u_pos : 0 < ‖1 + u‖ := by linarith
  have hid : Complex.log (1 + u) - u / (1 + u) =
      (Complex.log (1 + u) - u) + u ^ 2 / (1 + u) := by
    have h1u_ne : 1 + u ≠ 0 := norm_ne_zero_iff.mp h1u_pos.ne'
    field_simp [h1u_ne]; ring
  have hlog_bd : ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 := by
    have h1 := Complex.norm_log_one_add_sub_self_le hu_lt1
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (sub_pos.mpr hu_lt1) two_pos]; linarith
    calc ‖Complex.log (1 + u) - u‖ ≤ ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 := h1
      _ ≤ ‖u‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖u‖ ^ 2 := by ring
  have hrem_bd : ‖u ^ 2 / (1 + u)‖ ≤ 2 * ‖u‖ ^ 2 := by
    rw [norm_div, norm_pow]
    calc ‖u‖ ^ 2 / ‖1 + u‖ ≤ ‖u‖ ^ 2 / (1 / 2) := by gcongr
      _ = 2 * ‖u‖ ^ 2 := by ring
  have hterm1 : ‖(c' : ℂ) * (Complex.log (1 + u) - u / (1 + u))‖ ≤
      (3 / 4 : ℝ) / (c' * ‖ω‖ ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'.le, hid]
    have hsum : ‖(Complex.log (1 + u) - u) + u ^ 2 / (1 + u)‖ ≤ 3 * ‖u‖ ^ 2 :=
      (norm_add_le _ _).trans (by linarith)
    calc c' * ‖(Complex.log (1 + u) - u) + u ^ 2 / (1 + u)‖
        ≤ c' * (3 * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hsum hc'.le
      _ = c' * (3 * (1 / (2 * (c' * ‖ω‖))) ^ 2) := by rw [hu_norm, hh_norm]
      _ = (3 / 4 : ℝ) / (c' * ‖ω‖ ^ 2) := by field_simp [hc'.ne', hω_pos.ne']; ring
  have hterm2 : ‖(c' : ℂ) * FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h)‖ ≤
      1 / (c' * ‖ω‖ ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc'.le]
    have hbin := FormalResearch.Special.ComplexStirling.norm_binetI_le_div hz_re
    have hnorm_ge := norm_half_add_ge hh_re
    have hbin2 : ‖FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h)‖ ≤
        1 / (c' * ‖ω‖) ^ 2 := by
      calc ‖FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h)‖
          ≤ 1 / ‖1 / 2 + h‖ ^ 2 := hbin
        _ ≤ 1 / ‖h‖ ^ 2 := by gcongr
        _ = 1 / (c' * ‖ω‖) ^ 2 := by rw [hh_norm]
    calc c' * ‖FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h)‖
        ≤ c' * (1 / (c' * ‖ω‖) ^ 2) := mul_le_mul_of_nonneg_left hbin2 hc'.le
      _ = 1 / (c' * ‖ω‖ ^ 2) := by field_simp [hc'.ne', hω_pos.ne']
  calc ‖(c' : ℂ) * (Complex.log (1 + u) - u / (1 + u)) -
          (c' : ℂ) * FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h)‖
      ≤ ‖(c' : ℂ) * (Complex.log (1 + u) - u / (1 + u))‖ +
          ‖(c' : ℂ) * FormalResearch.Special.ComplexStirling.binetI (1 / 2 + h)‖ :=
        norm_sub_le _ _
    _ ≤ (3 / 4 : ℝ) / (c' * ‖ω‖ ^ 2) + 1 / (c' * ‖ω‖ ^ 2) := add_le_add hterm1 hterm2
    _ = (7 / 4 : ℝ) / (c' * ‖ω‖ ^ 2) := by ring

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.gamma_mul_two_pi_t_cpow_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gamma_mul_two_pi_t_cpow_neg

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.norm_stirlingS_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_stirlingS_sub_one_le

/-- info: 'FormalResearch.ModularBootstrap.ComplexBessel.norm_deriv_stirlingLogS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_deriv_stirlingLogS_le

end FormalResearch.ModularBootstrap.ComplexBessel