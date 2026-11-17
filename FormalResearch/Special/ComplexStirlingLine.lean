module

public import FormalResearch.Special.ComplexStirlingBinet

/-!
# Stirling on the critical line `Re z = 1/2`

Put `z = 1/2 + i s`, `s ∈ ℝ`.  All statements follow from the Binet bounds
(`ComplexStirlingBinet`, `ComplexStirlingRemainder`):

* `norm_sq_Gamma_half_line` : `|Γ(1/2 + is)|² = π / cosh(π s)` (Euler's reflection formula, Mathlib
  `Complex.Gamma_mul_Gamma_one_sub`, and `Γ(z̄) = conj Γ(z)`);
* `re_digamma_half_line` : for `s ≠ 0`, `|Re ψ(1/2 + is) - log |s|| ≤ 11/(8 s²)`;
* `im_binetLogGamma_half_line` : `Im log Γ(1/2 + is) = s log |s| - s + O(1/|s|)`, explicitly
  `|Im log Γ(1/2+is) - (s log |s| - s)| ≤ 17/(8|s|)`, where `log Γ` is the branch
  `binetLogGamma` (real on `(0,∞)`, `= arg Γ` modulo `2π`).  There is **no** constant term (the
  `(x - 1/2) arg z → (x-1/2)π/2` offset vanishes at `x = 1/2`); numerically
  `Im log Γ(1/2+is) - (s log s - s) ≈ 1/(24 s)` (mpmath, `s ∈ {0.5,1,3,10,50}`: `0.096, 0.045, 0.0140,
  0.00417, 0.00083`).

Not formalised: the exact formula `Im ψ(1/2+is) = (π/2) tanh(π s)` (checked numerically), arguments `s`
near `0` beyond the stated (non-sharp) bounds, the identification of `binetLogGamma` with
`Complex.arg ∘ Γ` up to `2π k(s)`.
-/

@[expose] public section

namespace FormalResearch.Special.ComplexStirling

open MeasureTheory Set Filter Topology Complex

/-- The point `1/2 + i s` of the critical line. -/
noncomputable def halfLine (s : ℝ) : ℂ := 1 / 2 + (s : ℂ) * I

lemma halfLine_re (s : ℝ) : (halfLine s).re = 1 / 2 := by simp [halfLine]

lemma halfLine_im (s : ℝ) : (halfLine s).im = s := by simp [halfLine]

lemma halfLine_re_pos (s : ℝ) : 0 < (halfLine s).re := by rw [halfLine_re]; norm_num

lemma halfLine_norm_sq (s : ℝ) : ‖halfLine s‖ ^ 2 = 1 / 4 + s ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, halfLine_re, halfLine_im]; ring

/-- `|Γ(1/2 + is)|² = π / cosh (π s)`. -/
theorem norm_sq_Gamma_half_line (s : ℝ) :
    ‖Complex.Gamma (halfLine s)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * s) := by
  set z : ℂ := halfLine s with hz
  have h1 : (1 : ℂ) - z = (starRingEnd ℂ) z := by
    simp only [hz, halfLine, map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  have h2 := Complex.Gamma_mul_Gamma_one_sub z
  rw [h1, Complex.Gamma_conj, Complex.mul_conj] at h2
  have h3 : Complex.sin (Real.pi * z) = (Real.cosh (Real.pi * s) : ℂ) := by
    have : (Real.pi : ℂ) * z = (Real.pi * s : ℝ) * I + Real.pi / 2 := by
      simp [hz, halfLine]; ring
    rw [this, Complex.sin_add_pi_div_two, Complex.cos_mul_I]; norm_cast
  rw [h3, Complex.normSq_eq_norm_sq] at h2
  have : ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) = ((Real.pi / Real.cosh (Real.pi * s) : ℝ) : ℂ) := by
    rw [h2]; push_cast; rfl
  exact Complex.ofReal_injective this

lemma log_norm_halfLine_sub {s : ℝ} (hs : s ≠ 0) :
    0 ≤ Real.log ‖halfLine s‖ - Real.log |s| ∧
      Real.log ‖halfLine s‖ - Real.log |s| ≤ 1 / (8 * s ^ 2) := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hq : ‖halfLine s‖ ^ 2 = 1 / 4 + s ^ 2 := halfLine_norm_sq s
  have hn : 0 < ‖halfLine s‖ := by
    refine norm_pos_iff.2 (fun h => ?_)
    have := halfLine_re_pos s
    rw [h] at this; simp at this
  have hl1 : Real.log (‖halfLine s‖ ^ 2) = 2 * Real.log ‖halfLine s‖ := by
    rw [Real.log_pow]; norm_num
  have hl2 : Real.log (|s| ^ 2) = 2 * Real.log |s| := by
    rw [Real.log_pow]; norm_num
  have habs : 0 < |s| := abs_pos.2 hs
  have hsq : |s| ^ 2 = s ^ 2 := sq_abs s
  constructor
  · have : Real.log (|s| ^ 2) ≤ Real.log (‖halfLine s‖ ^ 2) :=
      Real.log_le_log (by positivity) (by rw [hq, hsq]; linarith)
    linarith
  · have h := Real.log_le_sub_one_of_pos (x := ‖halfLine s‖ ^ 2 / |s| ^ 2) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), hl1, hl2, hq, hsq] at h
    have e : (1 / 4 + s ^ 2) / s ^ 2 - 1 = 1 / (4 * s ^ 2) := by field_simp; ring
    rw [e] at h
    have e2 : 1 / (8 * s ^ 2) = 1 / (4 * s ^ 2) / 2 := by field_simp; ring
    rw [e2]; linarith

/-- `|Re ψ(1/2 + is) - log |s|| ≤ 11/(8 s²)` for `s ≠ 0`. -/
theorem re_digamma_half_line {s : ℝ} (hs : s ≠ 0) :
    |(Complex.digamma (halfLine s)).re - Real.log (|s|)| ≤ 11 / 8 / s ^ 2 := by
  have hz := halfLine_re_pos s
  have hs2 : 0 < s ^ 2 := by positivity
  have hq : ‖halfLine s‖ ^ 2 = 1 / 4 + s ^ 2 := halfLine_norm_sq s
  obtain ⟨hA0, hA1⟩ := log_norm_halfLine_sub hs
  have hre : (Complex.digamma (halfLine s)).re = Real.log ‖halfLine s‖ -
      1 / 2 * ((1 / 2) / (1 / 4 + s ^ 2)) - (binetI (halfLine s)).re := by
    rw [digamma_eq_binet hz]
    simp only [Complex.sub_re, Complex.log_re, Complex.mul_re, Complex.inv_re, Complex.normSq_apply,
      halfLine_re, halfLine_im]
    simp
    field_simp
    ring
  have hB : (0 : ℝ) ≤ 1 / 2 * ((1 / 2) / (1 / 4 + s ^ 2)) ∧
      1 / 2 * ((1 / 2) / (1 / 4 + s ^ 2)) ≤ 1 / 4 / s ^ 2 := by
    constructor
    · positivity
    · have e : 1 / 2 * ((1 / 2) / (1 / 4 + s ^ 2)) = 1 / 4 / (1 / 4 + s ^ 2) := by ring
      rw [e]
      exact div_le_div_of_nonneg_left (by norm_num) hs2 (by linarith)
  have hC : |(binetI (halfLine s)).re| ≤ 1 / s ^ 2 := by
    have h1 := (Complex.abs_re_le_norm (binetI (halfLine s))).trans (norm_binetI_le_div hz)
    refine h1.trans ?_
    rw [hq]
    exact div_le_div_of_nonneg_left (by norm_num) hs2 (by linarith)
  rw [hre]
  have hC' := abs_le.1 hC
  rw [abs_le]
  have e : 11 / 8 / s ^ 2 = 1 / (8 * s ^ 2) + 1 / 4 / s ^ 2 + 1 / s ^ 2 := by field_simp; ring
  constructor <;> nlinarith [hC'.1, hC'.2, hB.1, hB.2, hA0, hA1]

/-- `Im binetLogGamma (1/2 + is) = s log ‖z‖ - s + Im binetB z`. -/
lemma im_binetLogGamma_half_line_eq (s : ℝ) :
    (binetLogGamma (halfLine s)).im =
      s * Real.log ‖halfLine s‖ - s + (binetB (halfLine s)).im := by
  have h1 : (halfLine s - 1 / 2).re = 0 := by simp [halfLine]
  have h2 : (halfLine s - 1 / 2).im = s := by simp [halfLine]
  have key : binetLogGamma (halfLine s) = (halfLine s - 1 / 2) * Complex.log (halfLine s) -
      halfLine s + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + binetB (halfLine s) := rfl
  rw [key, Complex.add_im, Complex.add_im, Complex.sub_im, Complex.mul_im, h1, h2, Complex.log_re,
    Complex.ofReal_im, halfLine_im]
  ring

/-- `|Im log Γ(1/2 + is) - (s log |s| - s)| ≤ 17/(8|s|)` for `s ≠ 0`, with `log Γ = binetLogGamma`. -/
theorem im_binetLogGamma_half_line {s : ℝ} (hs : s ≠ 0) :
    |(binetLogGamma (halfLine s)).im - (s * Real.log |s| - s)| ≤ 17 / 8 / |s| := by
  have hz := halfLine_re_pos s
  have habs : 0 < |s| := abs_pos.2 hs
  obtain ⟨hA0, hA1⟩ := log_norm_halfLine_sub hs
  rw [im_binetLogGamma_half_line_eq]
  have h1 : |s * (Real.log ‖halfLine s‖ - Real.log |s|)| ≤ 1 / 8 / |s| := by
    rw [abs_mul, abs_of_nonneg hA0]
    have : |s| * (Real.log ‖halfLine s‖ - Real.log |s|) ≤ |s| * (1 / (8 * s ^ 2)) :=
      mul_le_mul_of_nonneg_left hA1 habs.le
    refine this.trans (le_of_eq ?_)
    rw [← sq_abs s]; field_simp
  have hn : |s| ≤ ‖halfLine s‖ := by
    have := Complex.abs_im_le_norm (halfLine s)
    rwa [halfLine_im] at this
  have h2 : |(binetB (halfLine s)).im| ≤ 2 / |s| := by
    refine (Complex.abs_im_le_norm _).trans ((norm_binetB_le_div hz).trans ?_)
    exact div_le_div_of_nonneg_left (by norm_num) habs hn
  have e : (s * Real.log ‖halfLine s‖ - s + (binetB (halfLine s)).im) - (s * Real.log |s| - s) =
      s * (Real.log ‖halfLine s‖ - Real.log |s|) + (binetB (halfLine s)).im := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have e2 : (17 : ℝ) / 8 / |s| = 1 / 8 / |s| + 2 / |s| := by field_simp; ring
  rw [e2]
  exact add_le_add h1 h2

end FormalResearch.Special.ComplexStirling
