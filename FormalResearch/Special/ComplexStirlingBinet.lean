module

public import FormalResearch.Special.ComplexStirlingRemainder
public import FormalResearch.Special.BarnesDigamma
public import Interval.EulerMaclaurin.Gamma

/-!
# Binet's formulas on the right half-plane

Notation: `ψ = Complex.digamma`, `binetI z = ∫_0^∞ (1/2 - 1/t + 1/(e^t-1)) e^{-tz} dt`,
`binetB z = ∫_0^∞ (1/2 - 1/t + 1/(e^t-1)) e^{-tz}/t dt` (`ComplexStirlingKernel`).

* `digamma_eq_binet` (DLMF 5.9.16): for `Re z > 0`, `ψ(z) = log z - 1/(2z) - binetI z`.
  Proof: `D(z) = ψ(z) - log z + 1/(2z) + binetI z` is holomorphic on `Re z > 0` and 1-periodic
  (`ψ(z+1) = ψ(z) + 1/z` from Mathlib, `binetI_sub_succ`); for real `x > 0`, `D(x) = D(x+n+1)` and
  `|ψ(y) - log y| ≤ 1/(y-1)` (convexity of `log Γ`, Barnes `deriv_logGammaR_bounds`) gives
  `‖D(x)‖ ≤ 2/(x+n) → 0`; the identity theorem on the half-plane gives `D ≡ 0`.
* `binetLogGamma z = (z - 1/2) log z - z + (1/2) log(2π) + binetB z` (the right-hand side of Binet's
  second formula, DLMF 5.9.? / 5.11.?): it is holomorphic on `Re z > 0`, with derivative `ψ`
  (`hasDerivAt_binetLogGamma`) and satisfies `exp (binetLogGamma z) = Γ z` (`exp_binetLogGamma`): the
  quotient `Γ e^{-Λ}` has zero derivative and its value is `1` by Stirling's formula along the integers
  (Mathlib `Stirling.tendsto_stirlingSeq_sqrt_pi` via the vendored `tendsto_log_gamma_stirling`).
* `binetLogGamma_ofReal`: for real `x > 0` it equals the real `log Γ(x)`, so `binetLogGamma` is the
  continuous branch of `log Γ` that is real on the positive axis; `eq_binetLogGamma_of_differentiable`:
  any holomorphic `L` on `Re z > 0` with `exp L = Γ` and `L 1 = 0` equals it.
* Remainders (from `ComplexStirlingRemainder`): `‖ψ(z) - (log z - 1/(2z))‖ ≤ 1/‖z‖²`,
  `‖ψ'(z) - 1/z - 1/(2z²)‖ ≤ (2/3)/‖z‖³`,
  `‖binetLogGamma z - ((z-1/2) log z - z + (1/2) log 2π)‖ ≤ 2/‖z‖` for `Re z > 0`.

Not formalised: Binet's formulas off the right half-plane, the Weierstrass-product form of `log Γ`.
-/

@[expose] public section

namespace FormalResearch.Special.ComplexStirling

open MeasureTheory Set Filter Topology Complex

lemma re_pos_ne_zero {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := fun h => by simp [h] at hz

lemma re_pos_ne_neg_nat {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := fun h => by
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma re_one_add_inv_pos {z : ℂ} (hz : 0 < z.re) : 0 < (1 + 1 / z).re := by
  have : 0 < (1 / z).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos hz (Complex.normSq_pos.2 (re_pos_ne_zero hz))
  simp only [Complex.add_re, Complex.one_re]
  linarith

lemma log_add_one_eq {z : ℂ} (hz : 0 < z.re) :
    Complex.log (z + 1) = Complex.log z + Complex.log (1 + 1 / z) := by
  have hz0 := re_pos_ne_zero hz
  have hw := re_one_add_inv_pos hz
  have hw0 : (1 + 1 / z) ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1 : z + 1 = z * (1 + 1 / z) := by field_simp
  have ha := (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz))
  have hb := (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw))
  rw [abs_lt] at ha hb
  rw [h1, Complex.log_mul hz0 hw0 ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩]

/-- The auxiliary function `D = ψ - log z + 1/(2z) + binetI`. -/
noncomputable def binetD (z : ℂ) : ℂ :=
  Complex.digamma z - Complex.log z + 1 / 2 * z⁻¹ + binetI z

lemma binetD_succ {z : ℂ} (hz : 0 < z.re) : binetD (z + 1) = binetD z := by
  have hz0 := re_pos_ne_zero hz
  have h1 := Complex.digamma_apply_add_one z (re_pos_ne_neg_nat hz)
  have h2 := log_add_one_eq hz
  have h3 := binetI_sub_succ hz
  unfold binetD
  rw [h1, h2]
  linear_combination -h3

lemma binetD_add_nat {z : ℂ} (hz : 0 < z.re) (n : ℕ) : binetD (z + n) = binetD z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hzn : 0 < (z + n).re := by simp; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [show z + ((n + 1 : ℕ) : ℂ) = (z + n) + 1 by push_cast; ring, binetD_succ hzn, ih]

lemma differentiableOn_binetD : DifferentiableOn ℂ binetD rhp := by
  intro z hz
  have hzr : 0 < z.re := hz
  have hl : DifferentiableAt ℂ Complex.log z :=
    differentiableAt_log (Complex.mem_slitPlane_iff.2 (Or.inl hzr))
  have hi : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 * w⁻¹) z :=
    (differentiableAt_inv (re_pos_ne_zero hzr)).const_mul _ |>.congr_of_eventuallyEq
      (by exact Filter.Eventually.of_forall fun w => rfl)
  have hb : DifferentiableAt ℂ binetI z := (hasDerivAt_binetI hzr).differentiableAt
  have hd' : DifferentiableAt ℂ Complex.digamma z :=
    Barnes.differentiableOn_digamma_rhp.differentiableAt (Barnes.isOpen_rhp.mem_nhds hzr)
  exact ((hd'.sub hl).add hi |>.add hb).differentiableWithinAt

lemma norm_binetD_real_le {x : ℝ} (hx : 0 < x) (n : ℕ) : ‖binetD (x : ℂ)‖ ≤ 2 / (x + n) := by
  have hxn : 0 < x + n := by positivity
  have hy1 : 1 < x + n + 1 := by linarith
  have hy : 0 < x + n + 1 := by linarith
  have hxr : 0 < (x : ℂ).re := by simpa using hx
  have e : (x : ℂ) + ((n + 1 : ℕ) : ℂ) = ((x + n + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [← binetD_add_nat hxr (n + 1), e]
  set y : ℝ := x + n + 1 with hy_def
  have hyr : 0 < ((y : ℝ) : ℂ).re := by simpa using hy
  -- the real part of the structure
  have hdig : Complex.digamma (y : ℂ) = ((deriv Barnes.logGammaR y : ℝ) : ℂ) :=
    Barnes.digamma_ofReal hy
  have hlog : Complex.log (y : ℂ) = ((Real.log y : ℝ) : ℂ) := (Complex.ofReal_log hy.le).symm
  obtain ⟨hb1, hb2⟩ := Barnes.deriv_logGammaR_bounds hy1
  have hdiff : ‖Complex.digamma (y : ℂ) - Complex.log (y : ℂ)‖ ≤ 1 / (x + n) := by
    rw [hdig, hlog, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hyy : y - 1 = x + n := by rw [hy_def]; ring
    have h1 : Real.log y - Real.log (y - 1) ≤ 1 / (x + n) := by
      rw [← Real.log_div hy.ne' (by linarith)]
      have := Real.log_le_sub_one_of_pos (x := y / (y - 1)) (by positivity)
      have e2 : y / (y - 1) - 1 = 1 / (x + n) := by
        rw [hyy]; field_simp; rw [hy_def]; ring
      linarith
    constructor <;> linarith
  have hinv : ‖(1 / 2 : ℂ) * (y : ℂ)⁻¹‖ ≤ 1 / 2 / (x + n) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    have : (‖(1 / 2 : ℂ)‖ : ℝ) = 1 / 2 := by simp
    rw [this, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) hxn (by rw [hy_def]; linarith)
  have hI : ‖binetI (y : ℂ)‖ ≤ 1 / 2 / (x + n) := by
    refine (norm_binetI_le (by simpa using hy)).trans ?_
    simp only [Complex.ofReal_re]
    exact div_le_div_of_nonneg_left (by norm_num) hxn (by rw [hy_def]; linarith)
  unfold binetD
  calc ‖Complex.digamma (y : ℂ) - Complex.log (y : ℂ) + 1 / 2 * (y : ℂ)⁻¹ + binetI (y : ℂ)‖
      ≤ ‖Complex.digamma (y : ℂ) - Complex.log (y : ℂ)‖ + ‖(1 / 2 : ℂ) * (y : ℂ)⁻¹‖ +
          ‖binetI (y : ℂ)‖ := norm_add₃_le
    _ ≤ 1 / (x + n) + 1 / 2 / (x + n) + 1 / 2 / (x + n) := add_le_add (add_le_add hdiff hinv) hI
    _ = 2 / (x + n) := by field_simp; ring

lemma binetD_real {x : ℝ} (hx : 0 < x) : binetD (x : ℂ) = 0 := by
  have : ‖binetD (x : ℂ)‖ ≤ 0 :=
    le_of_forall_nat (f := fun n : ℕ => 2 / (x + n)) (tendsto_div_add_nat hx 2)
      fun n => by simpa using norm_binetD_real_le hx n
  exact norm_le_zero_iff.1 this

lemma binetD_eq_zero {z : ℂ} (hz : 0 < z.re) : binetD z = 0 := by
  have hA : AnalyticOnNhd ℂ binetD rhp := differentiableOn_binetD.analyticOnNhd isOpen_rhp
  have h1 : (1 : ℂ) ∈ rhp := by simp [rhp]
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), binetD w = 0 := by
    have hlim : Tendsto (fun n : ℕ => (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
        simp only [add_zero] at h
        have h2 : Tendsto (fun n : ℕ => (((1 + 1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop
            (𝓝 ((1 : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto 1).comp h
        rwa [Complex.ofReal_one] at h2
      · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have h' := Complex.ofReal_injective (h.trans Complex.ofReal_one.symm)
        linarith
    refine hlim.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => ?_))
    exact binetD_real (by positivity)
  exact hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_rhp h1 hfreq hz

/-- **Binet's formula for `ψ`** (DLMF 5.9.16): for `Re z > 0`,
`ψ(z) = log z - 1/(2z) - ∫_0^∞ (1/2 - 1/t + 1/(e^t-1)) e^{-tz} dt`. -/
theorem digamma_eq_binet {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = Complex.log z - 1 / 2 * z⁻¹ - binetI z := by
  have := binetD_eq_zero hz
  unfold binetD at this
  linear_combination this

end FormalResearch.Special.ComplexStirling
