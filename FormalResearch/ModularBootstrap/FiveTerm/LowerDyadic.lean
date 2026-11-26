module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Exponent bookkeeping of `ctl:dyadic`, `ctl:pass2`, `ctl:freeze`, `cts:boas` (FIVE-L)

Source: `CFT/modular_bootstrap/paper/constant_term_lower_log.tex` (Proposition C7a, Lemma C7b, Lemma C8a) and
`constant_term_slit_strip.tex` (Lemma C8, Step 3); the checks of `verify_constant_term_lower_log.py`, section [1].
All statements are proved and unconditional (`prob`-free).

* `pass2_exponents`, `boas_window_exponents`: every error term of the sharpened Pass-2 dual identity and of the Boas
  freezing/window bookkeeping has `c'`-exponent `≤ -4/3`; the old Boas exponent `-25/21` is not (`old_boas_exponent`).
* `gauss_window_exponents`: for `W² = 2 log c'`, `L₀ = 8 log c'`, `H = 2 log c'`: `e^{-L₀²/2W²} = c'^{-16}`,
  `e^{H²/2W²} = c'`, `e^{-(L₀²-H²)/2W²} = c'^{-15}`; `top_edge_exponent`: `3 - 4π < -19/2`.
* `gauss_re_sq`, `gauss_top_le`, `gauss_vert_le`: the modulus of the Gaussian window `e^{-(ζ-ζ₀)²/(2W²)}` on the top edge
  (`≤ e^{H²/2W²}`) and on the vertical sides (`≤ e^{-(L₀²-H²)/2W²}`).
* `dyadic_term_le`: `(1 + 2^{j+1} r₀)^{1/2} r_j^{-1/2} ≤ 3` for `r_j ∈ [2^j r₀ - 1, 2^j r₀]`, `r₀ ≥ 2`, the term bound
  of the dyadic sum of `ctl:dyadic`(2).
* `markov_select`: the Markov selection of a good radius (last line of `ctl:pass2`): a nonnegative function with small integral on a
  set of positive measure is small somewhere on the set.

**Not here**: the decay/variation estimates themselves (they need `cts:cauchy-dual`/`cts:rosc-uncond`); the measure of
`{r ∈ [r₀,2r₀] : |sin(2r³/3 + π/4)| ≥ 1/2}`.
-/

@[expose] public section

open Real MeasureTheory Set

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- Exponent bookkeeping of the sharpened Pass-2 dual identity (`ctl:pass2`): the listed `c'`-exponents are `≤ -4/3`
(the `η_R` term is exactly `-4/3`; the `R'`-term is `-1/3`, feeding `η`). -/
theorem pass2_exponents :
    (-1 : ℚ) + 2 / 3 = -1 / 3 ∧ (-1 : ℚ) + (-1 / 3) = -4 / 3 ∧ (-1 : ℚ) + (-1 / 3) ≤ -4 / 3 ∧
    (-1 : ℚ) + (-2 / 3) + 1 / 3 ≤ -4 / 3 ∧ (-1 : ℚ) + (-1 / 3) ≤ -4 / 3 ∧ (-4 / 3 : ℚ) ≤ -4 / 3 ∧
    (-8 / 3 : ℚ) + 2 / 3 ≤ -4 / 3 ∧ (-3 / 2 : ℚ) ≤ -4 / 3 := by
  norm_num

/-- Exponent bookkeeping of the Boas window/freezing step (`ctl:freeze`, `cts:boas`). -/
theorem boas_window_exponents :
    (-1 / 3 : ℚ) + (-4 / 3) + 1 / 3 ≤ -4 / 3 ∧ (-1 : ℚ) + (-2 / 3) + 1 / 3 ≤ -4 / 3 ∧
    (-1 : ℚ) + (-1 / 3) ≤ -4 / 3 ∧ (-29 / 21 : ℚ) ≤ -4 / 3 := by
  norm_num

/-- The old Boas freezing exponent `-25/21` does *not* reach `-4/3` (it needed the weighted repair). -/
theorem old_boas_exponent : ¬ ((-25 / 21 : ℚ) ≤ -4 / 3) := by norm_num

/-- `u`-level to `Δ`-level scaling: `c_*c'^{1/3} · c'^{-4/3} = c'^{-1}` at exponent level. -/
theorem level_scaling : (1 / 3 : ℚ) + (-4 / 3) = -1 := by norm_num

/-- Monotonicity in the exponent: `c'^{a} ≤ c'^{b}` for `c' ≥ 1`, `a ≤ b`. -/
theorem rpow_exponent_mono {c a b : ℝ} (hc : 1 ≤ c) (hab : a ≤ b) : c ^ a ≤ c ^ b :=
  Real.rpow_le_rpow_of_exponent_le hc hab

/-- Gaussian window exponents of the Boas rectangle, `W² = 2 log c'`, `L₀ = 8 log c'`, `H = 2 log c'`. -/
theorem gauss_window_exponents {c : ℝ} (hc : 1 < c) :
    Real.exp (-((8 * Real.log c) ^ 2 / (2 * (2 * Real.log c)))) = c ^ (-16 : ℝ) ∧
    Real.exp ((2 * Real.log c) ^ 2 / (2 * (2 * Real.log c))) = c ∧
    Real.exp (-(((8 * Real.log c) ^ 2 - (2 * Real.log c) ^ 2) / (2 * (2 * Real.log c)))) =
      c ^ (-15 : ℝ) := by
  have hl : 0 < Real.log c := Real.log_pos hc
  have hc0 : 0 < c := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hc0]; congr 1; field_simp; ring
  · have : (2 * Real.log c) ^ 2 / (2 * (2 * Real.log c)) = Real.log c := by field_simp
    rw [this, Real.exp_log hc0]
  · rw [Real.rpow_def_of_pos hc0]; congr 1; field_simp; ring

/-- The top-edge exponent of the Boas rectangle: `2 + 1 - 4π < -19/2` (`c'² · c' · c'^{-4π}`). -/
theorem top_edge_exponent : 3 - 4 * π < -19 / 2 := by
  have := Real.pi_gt_d2
  linarith

/-- `Re (s + iH)² = s² - H²`. -/
theorem gauss_re_sq (s H : ℝ) : (((s : ℂ) + H * Complex.I) ^ 2).re = s ^ 2 - H ^ 2 := by
  simp [sq, Complex.mul_re, Complex.mul_im]

/-- Modulus of the Gaussian window `e^{-ζ²/(2W²)}` at `ζ = s + iH`. -/
theorem gauss_norm (s H W : ℝ) :
    ‖Complex.exp (-(((s : ℂ) + H * Complex.I) ^ 2) / (2 * (W : ℂ) ^ 2))‖ =
      Real.exp (-(s ^ 2 - H ^ 2) / (2 * W ^ 2)) := by
  rw [Complex.norm_exp]
  have h : (2 * (W : ℂ) ^ 2) = ((2 * W ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.div_ofReal_re, Complex.neg_re, gauss_re_sq]

/-- Top edge: the Gaussian window is at most `e^{H²/(2W²)}`. -/
theorem gauss_top_le (s H W : ℝ) :
    ‖Complex.exp (-(((s : ℂ) + H * Complex.I) ^ 2) / (2 * (W : ℂ) ^ 2))‖ ≤
      Real.exp (H ^ 2 / (2 * W ^ 2)) := by
  rw [gauss_norm]
  refine Real.exp_le_exp.2 ?_
  have : -(s ^ 2 - H ^ 2) / (2 * W ^ 2) = H ^ 2 / (2 * W ^ 2) - s ^ 2 / (2 * W ^ 2) := by ring
  rw [this]
  have : 0 ≤ s ^ 2 / (2 * W ^ 2) := by positivity
  linarith

/-- Vertical sides: for `|s| ≥ L₀`, `0 ≤ y ≤ H`, the Gaussian window is at most `e^{-(L₀²-H²)/(2W²)}`. -/
theorem gauss_vert_le (s y H L₀ W : ℝ) (hy : y ≤ H) (hy0 : 0 ≤ y) (hs : L₀ ≤ |s|) (hL : 0 ≤ L₀) :
    ‖Complex.exp (-(((s : ℂ) + y * Complex.I) ^ 2) / (2 * (W : ℂ) ^ 2))‖ ≤
      Real.exp (-(L₀ ^ 2 - H ^ 2) / (2 * W ^ 2)) := by
  rw [gauss_norm]
  refine Real.exp_le_exp.2 ?_
  have hW : 0 ≤ 2 * W ^ 2 := by positivity
  have h1 : L₀ ^ 2 ≤ s ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg s]) hs
    nlinarith [sq_abs s]
  have h2 : y ^ 2 ≤ H ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right (by linarith) hW

/-- Term bound of the dyadic sum in `ctl:dyadic`(2): for `r₀ ≥ 2` and `r_j ∈ [2^j r₀ - 1, 2^j r₀]`,
`(1 + 2^{j+1} r₀)^{1/2} · r_j^{-1/2} ≤ 3` (`j ≥ 1`). -/
theorem dyadic_term_le {r₀ rj : ℝ} (hr₀ : 2 ≤ r₀) {j : ℕ} (hj : 1 ≤ j)
    (hlo : 2 ^ j * r₀ - 1 ≤ rj) (_hhi : rj ≤ 2 ^ j * r₀) :
    Real.sqrt (1 + 2 ^ (j + 1) * r₀) * (Real.sqrt rj)⁻¹ ≤ 3 := by
  have h2j : (2 : ℝ) ≤ 2 ^ j := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hP : 2 * r₀ ≤ 2 ^ j * r₀ := by nlinarith
  have hrj : 2 ^ j * r₀ / 2 ≤ rj := by nlinarith
  have hrj0 : 0 < rj := by nlinarith
  rw [← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.2 hrj0)]
  have hl : 1 + 2 ^ (j + 1) * r₀ ≤ 9 * rj := by
    have : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
    rw [this]; nlinarith
  calc Real.sqrt (1 + 2 ^ (j + 1) * r₀) ≤ Real.sqrt (9 * rj) := Real.sqrt_le_sqrt hl
    _ = 3 * Real.sqrt rj := by
        rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]

/-- **Markov selection** (last step of `ctl:pass2`): if `F ≥ 0` is integrable on `E` of positive measure with
`∫_E F ≤ A`, some `r ∈ E` has `F r ≤ A / |E|`. -/
theorem markov_select {E : Set ℝ} (hE : MeasurableSet E) (hpos : 0 < volume.real E) (hfin : volume E ≠ ⊤)
    {F : ℝ → ℝ} (hF : IntegrableOn F E) {A : ℝ}
    (hA : ∫ r in E, F r ≤ A) : ∃ r ∈ E, F r ≤ A / volume.real E := by
  by_contra hcon
  push Not at hcon
  have hint : IntegrableOn (fun _ : ℝ => A / volume.real E) E := integrableOn_const hfin
  have hG : IntegrableOn (fun r => F r - A / volume.real E) E := hF.sub hint
  have hE0 : volume E ≠ 0 := by
    intro h; rw [Measure.real, h] at hpos; simp at hpos
  have hG0 : 0 ≤ᵐ[volume.restrict E] fun r => F r - A / volume.real E := by
    refine (ae_restrict_iff' hE).2 (Filter.Eventually.of_forall fun r hr => ?_)
    exact (sub_pos.2 (hcon r hr)).le
  have hpos' := (setIntegral_pos_iff_support_of_nonneg_ae hG0 hG).2 (by
    have : Function.support (fun r => F r - A / volume.real E) ∩ E = E := by
      ext r
      simp only [Set.mem_inter_iff, Function.mem_support]
      exact ⟨fun h => h.2, fun hr => ⟨(sub_pos.2 (hcon r hr)).ne', hr⟩⟩
    rw [this]; exact pos_iff_ne_zero.2 hE0)
  rw [integral_sub hF hint, setIntegral_const] at hpos'
  have : volume.real E • (A / volume.real E) = A := by
    rw [smul_eq_mul, mul_div_cancel₀ _ hpos.ne']
  linarith

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.pass2_exponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.pass2_exponents

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gauss_window_exponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gauss_window_exponents

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.top_edge_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.top_edge_exponent

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gauss_top_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gauss_top_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.gauss_vert_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.gauss_vert_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.dyadic_term_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.dyadic_term_le

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.markov_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.markov_select
