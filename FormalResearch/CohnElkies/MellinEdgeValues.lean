module

public import FormalResearch.CohnElkies.MellinKernel

/-!
# Left-Edge Value of the Strip Function `ℋ` and the Γ-Ratio Bound on the Edge

Source: `general_theorems.tex`, `gt:7.4(2)`: the value of the Mellin-strip function `ℋ` on the
imaginary axis `ζ = i τ`, and the resulting Γ-ratio bound on the edge `Re ζ = 0`.

## Main results
* `re_stripH_imag`: `Re ℋ(i τ) = τ arctan τ - (1/2) log (1 + τ²)` for every real `τ`
  (proved, exact; from `stripH_eq` and `stripS0Tilde_imag`).
* `gamma_ratio_edge_le`: for `c > 0` and real `τ`,
  `Γ(c) / ‖Γ(c (1 - i τ))‖ ≤ (1 + τ²)^{1/4} exp(c Re ℋ(i τ) + 1/(6c))`
  (proved, exact; from `mellin_strip_kernel_eq`, `norm_mellinK0_imag_le` and
  `Asymptotics.binetDiff_norm_le_left`).

## Scope
Both statements hold for all real `τ` and all real `c > 0`, with no extra hypotheses. They are
exact statements about the imaginary edge only; no bound on the interior of the strip is claimed here.
The helpers `mellinEdge_*` are private bookkeeping for the arctangent and logarithm of `1 - i τ`.
-/

@[expose] public section

namespace FormalResearch.CohnElkies

/-- Real part of `1 - i τ` is `1`. -/
lemma mellinEdge_re_one_sub (τ : ℝ) : (1 - (τ : ℂ) * Complex.I).re = 1 := by
  simp

/-- Imaginary part of `1 - i τ` is `-τ`. -/
lemma mellinEdge_im_one_sub (τ : ℝ) : (1 - (τ : ℂ) * Complex.I).im = -τ := by
  simp

/-- Modulus of `1 - i τ` is `√(1 + τ²)`. -/
lemma mellinEdge_norm_one_sub (τ : ℝ) :
    ‖1 - (τ : ℂ) * Complex.I‖ = Real.sqrt (1 + τ ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, mellinEdge_re_one_sub, mellinEdge_im_one_sub]
  congr 1
  ring

/-- Argument of `1 - i τ` is `-arctan τ`. -/
lemma mellinEdge_arg_one_sub (τ : ℝ) :
    Complex.arg (1 - (τ : ℂ) * Complex.I) = -Real.arctan τ := by
  have hre : 0 ≤ (1 - (τ : ℂ) * Complex.I).re := by
    rw [mellinEdge_re_one_sub]
    norm_num
  rw [Complex.arg_of_re_nonneg hre, mellinEdge_im_one_sub, mellinEdge_norm_one_sub,
    Real.arctan_eq_arcsin, ← Real.arcsin_neg]
  congr 1
  rw [neg_div]

/-- Real part of `log (1 - i τ)` is `(1/2) log (1 + τ²)`. -/
lemma mellinEdge_re_log_one_sub (τ : ℝ) :
    (Complex.log (1 - (τ : ℂ) * Complex.I)).re = (1 / 2) * Real.log (1 + τ ^ 2) := by
  rw [Complex.log_re, mellinEdge_norm_one_sub, Real.log_sqrt (by positivity)]
  ring

/-- Imaginary part of `log (1 - i τ)` is `-arctan τ`. -/
lemma mellinEdge_im_log_one_sub (τ : ℝ) :
    (Complex.log (1 - (τ : ℂ) * Complex.I)).im = -Real.arctan τ := by
  rw [Complex.log_im, mellinEdge_arg_one_sub]

/-- `Im log(π/2) = 0`, so `ζ log(π/2)` has zero real part on the imaginary axis. -/
lemma mellinEdge_im_log_pi_div_two : (Complex.log ((Real.pi : ℂ) / 2)).im = 0 := by
  have h : (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.log_im, Complex.arg_ofReal_of_nonneg (by positivity)]

/-- `Re S̃₀(i τ) = 0`. -/
lemma mellinEdge_re_stripS0Tilde_imag (τ : ℝ) :
    (FormalResearch.CohnElkies.stripS0Tilde ((τ : ℂ) * Complex.I)).re = 0 := by
  rw [stripS0Tilde_imag]
  simp

/-- Left-edge value of `ℋ` on the imaginary axis (`gt:7.4(2)`): `Re ℋ(i τ) = τ arctan τ - (1/2) log (1 + τ²)`. -/
theorem re_stripH_imag (τ : ℝ) :
    (stripH ((τ : ℂ) * Complex.I)).re = τ * Real.arctan τ - (1 / 2) * Real.log (1 + τ ^ 2) := by
  have hζ0 : 0 ≤ ((τ : ℂ) * Complex.I).re := by simp
  have hζ1 : ((τ : ℂ) * Complex.I).re < 1 := by simp
  have hζre : ((τ : ℂ) * Complex.I).re = 0 := by simp
  have hζim : ((τ : ℂ) * Complex.I).im = τ := by simp
  rw [stripH_eq hζ0 hζ1]
  simp only [Complex.add_re, Complex.neg_re, Complex.mul_re, mellinEdge_re_one_sub,
    mellinEdge_im_one_sub, mellinEdge_re_log_one_sub, mellinEdge_im_log_one_sub,
    mellinEdge_re_stripS0Tilde_imag, mellinEdge_im_log_pi_div_two, hζre, hζim]
  ring

/-- info: 'FormalResearch.CohnElkies.re_stripH_imag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.re_stripH_imag

/-- Γ-ratio bound on the left edge (`gt:7.4(2)`): for `c > 0`,
`Γ(c) / ‖Γ(c (1 - i τ))‖ ≤ (1 + τ²)^{1/4} exp(c Re ℋ(i τ) + 1/(6c))`. -/
theorem gamma_ratio_edge_le {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    Real.Gamma c / ‖Complex.Gamma ((c : ℂ) * (1 - (τ : ℂ) * Complex.I))‖ ≤
      (1 + τ ^ 2) ^ (1 / 4 : ℝ) *
        Real.exp (c * (τ * Real.arctan τ - (1 / 2) * Real.log (1 + τ ^ 2)) + 1 / (6 * c)) := by
  have hζ0 : 0 ≤ ((τ : ℂ) * Complex.I).re := by simp
  have hζ1 : ((τ : ℂ) * Complex.I).re < 1 := by simp
  have hξ : (0 : ℝ) < 1 / (2 * Real.pi * c) := by positivity
  have hker := mellin_strip_kernel_eq hc hξ hζ0 hζ1
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hπ' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hbase : (2 * (Real.pi : ℂ) * (c : ℂ) * ((1 / (2 * Real.pi * c) : ℝ) : ℂ)) = 1 := by
    push_cast
    field_simp
  rw [hbase, Complex.one_cpow, mul_one, Complex.Gamma_ofReal] at hker
  have hg : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hg0 : Real.Gamma c ≠ 0 := hg.ne'
  have hK := (norm_mellinK0_imag_le hc hξ τ).1
  -- norms of the kernel identity
  have h1 := congrArg norm hker
  rw [norm_mul, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hg.le,
    Complex.re_ofReal_mul, hK, re_stripH_imag] at h1
  set G := ‖Complex.Gamma ((c : ℂ) * (1 - (τ : ℂ) * Complex.I))‖ with hGdef
  set P : ℝ := (1 + τ ^ 2) ^ (1 / 4 : ℝ) with hPdef
  have hP : 0 < P := by positivity
  have hneg : (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) = P⁻¹ :=
    Real.rpow_neg (by positivity) (1 / 4 : ℝ)
  rw [hneg] at h1
  have hGpos : 0 < G := by
    by_contra hn
    have hG0 : G = 0 := le_antisymm (not_lt.mp hn) (norm_nonneg _)
    rw [hG0, zero_div, zero_mul] at h1
    have : 0 < P⁻¹ * Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re := by positivity
    linarith
  have hG' : G = Real.Gamma c * (P⁻¹ * Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re) /
      Real.exp (c * (τ * Real.arctan τ - (1 / 2) * Real.log (1 + τ ^ 2))) := by
    rw [eq_div_iff (Real.exp_pos _).ne']
    calc G * Real.exp (c * (τ * Real.arctan τ - (1 / 2) * Real.log (1 + τ ^ 2)))
        = (G / Real.Gamma c * Real.exp (c * (τ * Real.arctan τ - (1 / 2) * Real.log (1 + τ ^ 2))))
          * Real.Gamma c := by field_simp
      _ = (P⁻¹ * Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re) * Real.Gamma c := by rw [h1]
      _ = Real.Gamma c * (P⁻¹ * Real.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re) := by ring
  have hratio : Real.Gamma c / G = P * Real.exp
      (c * (τ * Real.arctan τ - (1 / 2) * Real.log (1 + τ ^ 2)) -
        (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re) := by
    rw [Real.exp_sub, hG']
    field_simp
  -- the real part of the Binet difference on the edge is at least `-1/(6c)`
  have hbd : ‖FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)‖ ≤ 1 / (6 * c) :=
    FormalResearch.Asymptotics.binetDiff_norm_le_left hc (by simp)
  have hB : -(FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re ≤ 1 / (6 * c) := by
    have h2 := Complex.abs_re_le_norm (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I))
    have h3 := neg_le_abs (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)).re
    linarith
  rw [hratio]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hP.le

/-- info: 'FormalResearch.CohnElkies.gamma_ratio_edge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.gamma_ratio_edge_le

end FormalResearch.CohnElkies
