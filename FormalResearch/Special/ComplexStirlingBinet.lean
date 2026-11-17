module

public import FormalResearch.Special.ComplexStirlingRemainder
public import FormalResearch.Special.BarnesDigamma
public import Interval.EulerMaclaurin.Gamma

/-!
# Binet's formulas on the right half-plane

Notation: `ψ = Complex.digamma`, `binetI z = ∫_0^∞ (1/2 - 1/t + 1/(e^t-1)) e^{-tz} dt`,
`binetB z = ∫_0^∞ (1/2 - 1/t + 1/(e^t-1)) e^{-tz}/t dt` (`ComplexStirlingKernel`).

* `digamma_eq_binet` (the `z`-derivative of Binet's formula for `Ln Γ`, DLMF §5.9(ii) (5.9.10_2); the
  formula for `ψ` is not numbered separately there): for `Re z > 0`, `ψ(z) = log z - 1/(2z) - binetI z`.
  Proof: `D(z) = ψ(z) - log z + 1/(2z) + binetI z` is holomorphic on `Re z > 0` and 1-periodic
  (`ψ(z+1) = ψ(z) + 1/z` from Mathlib, `binetI_sub_succ`); for real `x > 0`, `D(x) = D(x+n+1)` and
  `|ψ(y) - log y| ≤ 1/(y-1)` (convexity of `log Γ`, Barnes `deriv_logGammaR_bounds`) gives
  `‖D(x)‖ ≤ 2/(x+n) → 0`; the identity theorem on the half-plane gives `D ≡ 0`.
* `binetLogGamma z = (z - 1/2) log z - z + (1/2) log(2π) + binetB z` (the right-hand side of Binet's
  formula for `Ln Γ`, DLMF (5.9.10_2)): it is holomorphic on `Re z > 0`, with derivative `ψ`
  (`hasDerivAt_binetLogGamma`) and satisfies `exp (binetLogGamma z) = Γ z` (`exp_binetLogGamma`): the
  quotient `Γ e^{-Λ}` has zero derivative and its value is `1` by Stirling's formula along the integers
  (Mathlib `Stirling.tendsto_stirlingSeq_sqrt_pi` via the vendored `tendsto_log_gamma_stirling`).
* `binetLogGamma_ofReal`: for real `x > 0` it equals the real `log Γ(x)`, so `binetLogGamma` is the
  continuous branch of `log Γ` that is real on the positive axis; `eq_binetLogGamma_of_differentiableOn`:
  any holomorphic `L` on `Re z > 0` with `exp L = Γ` and `L 1 = 0` equals it.
* `exists_int_im_binetLogGamma`: `Im binetLogGamma z = arg Γ(z) + 2π n` for some integer `n`.
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

/-- **Binet's formula for `ψ`** (the `z`-derivative of DLMF (5.9.10_2)): for `Re z > 0`,
`ψ(z) = log z - 1/(2z) - ∫_0^∞ (1/2 - 1/t + 1/(e^t-1)) e^{-tz} dt`. -/
theorem digamma_eq_binet {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z = Complex.log z - 1 / 2 * z⁻¹ - binetI z := by
  have := binetD_eq_zero hz
  unfold binetD at this
  linear_combination this

/-! ### The logarithm of `Γ` -/

/-- The Stirling main term plus Binet's remainder:
`(z - 1/2) log z - z + (1/2) log (2π) + ∫_0^∞ (1/2 - 1/t + 1/(e^t-1)) e^{-tz}/t dt`. -/
noncomputable def binetLogGamma (z : ℂ) : ℂ :=
  (z - 1 / 2) * Complex.log z - z + ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) + binetB z

lemma hasDerivAt_binetLogGamma {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt binetLogGamma (Complex.digamma z) z := by
  have hz0 := re_pos_ne_zero hz
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl hz)
  have h1 := (((hasDerivAt_id z).sub_const (1 / 2 : ℂ)).mul (Complex.hasDerivAt_log hslit))
  have h2 := ((h1.sub (hasDerivAt_id z)).add_const (((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ))).add
    (hasDerivAt_binetB hz)
  refine h2.congr_deriv ?_
  rw [digamma_eq_binet hz]
  simp only [id]
  field_simp
  ring

lemma hasDerivAt_Gamma_digamma {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.Gamma (Complex.digamma z * Complex.Gamma z) z := by
  have hd := (Complex.differentiableAt_Gamma z (re_pos_ne_neg_nat hz)).hasDerivAt
  have hne := Complex.Gamma_ne_zero (re_pos_ne_neg_nat hz)
  have : Complex.digamma z * Complex.Gamma z = deriv Complex.Gamma z := by
    rw [Complex.digamma_def, logDeriv_apply]; field_simp
  rwa [← this] at hd

/-- `log Γ(N) - ((N - 1/2) log N - N + (1/2) log 2π)` at `N = n + 1`. -/
noncomputable def stirlingRemSeq (n : ℕ) : ℝ :=
  Real.log (Real.Gamma ((n + 1 : ℕ) : ℝ)) -
    ((((n + 1 : ℕ) : ℝ) - 1 / 2) * Real.log ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) +
      Real.log (2 * Real.pi) / 2)

/-- Stirling's constant along the integers: `stirlingRemSeq n → 0`. -/
lemma tendsto_stirlingRemSeq : Tendsto stirlingRemSeq atTop (𝓝 0) := by
  have h := tendsto_log_gamma_stirling.comp (tendsto_add_atTop_nat 1)
  have h2 := h.sub_const (Real.log (2 * Real.pi) / 2)
  simp only [sub_self] at h2
  refine h2.congr (fun n => ?_)
  simp only [Function.comp, stirlingRemSeq]
  have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [this]; ring

lemma tendsto_binetB_nat :
    Tendsto (fun n : ℕ => binetB (((n + 1 : ℕ) : ℝ) : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => 1 / 6 / ((((n + 1 : ℕ) : ℝ)))) atTop (𝓝 0) := by
    have := (tendsto_div_add_nat (x := 1) one_pos (1 / 6))
    refine this.congr (fun n => ?_)
    push_cast; ring_nf
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have := norm_binetB_le (z := (((n + 1 : ℕ) : ℝ) : ℂ)) (by simpa using hn)
  simpa only [Complex.ofReal_re] using this

lemma Gamma_exp_neg_binetLogGamma_nat (n : ℕ) (G : ℂ → ℂ)
    (hG : G = fun w => Complex.Gamma w * Complex.exp (-binetLogGamma w))
    (hconst : ∀ w ∈ rhp, G w = G 1) :
    G 1 = Complex.exp ((stirlingRemSeq n : ℂ) - binetB (((n + 1 : ℕ) : ℝ) : ℂ)) := by
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hNr : (N : ℂ) ∈ rhp := by simpa [rhp] using hNpos
  rw [← hconst _ hNr]
  simp only [hG, binetLogGamma, stirlingRemSeq]
  rw [← hN]
  rw [Complex.Gamma_ofReal, ← Complex.ofReal_log hNpos.le]
  have hΓ : ((Real.Gamma N : ℝ) : ℂ) = Complex.exp ((Real.log (Real.Gamma N) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (Real.Gamma_pos_of_pos hNpos)]
  rw [hΓ, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `exp (binetLogGamma z) = Γ z` on `Re z > 0`. -/
theorem exp_binetLogGamma {z : ℂ} (hz : 0 < z.re) :
    Complex.exp (binetLogGamma z) = Complex.Gamma z := by
  set G : ℂ → ℂ := fun w => Complex.Gamma w * Complex.exp (-binetLogGamma w) with hG
  have hGd : ∀ w ∈ rhp, HasDerivAt G 0 w := by
    intro w hw
    have hwr : 0 < w.re := hw
    have h1 := hasDerivAt_Gamma_digamma hwr
    have h2 := ((hasDerivAt_binetLogGamma hwr).neg).cexp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    ring
  have hconst : ∀ w ∈ rhp, G w = G 1 := fun w hw =>
    isOpen_rhp.is_const_of_deriv_eq_zero isPreconnected_rhp
      (fun x hx => (hGd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => (hGd x hx).deriv) hw (by simp [rhp])
  have hG1 : G 1 = 1 := by
    have h0 : Tendsto (fun n : ℕ => Complex.exp ((stirlingRemSeq n : ℂ) -
        binetB (((n + 1 : ℕ) : ℝ) : ℂ))) atTop (𝓝 (Complex.exp (((0 : ℝ) : ℂ) - 0))) := by
      refine (Complex.continuous_exp.tendsto _).comp ?_
      exact ((Complex.continuous_ofReal.tendsto 0).comp tendsto_stirlingRemSeq).sub
        tendsto_binetB_nat
    simp only [Complex.ofReal_zero, sub_zero, Complex.exp_zero] at h0
    have hlim : Tendsto (fun n : ℕ => G 1) atTop (𝓝 1) :=
      h0.congr (fun n => (Gamma_exp_neg_binetLogGamma_nat n G hG hconst).symm)
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  have := hconst z hz
  rw [hG1] at this
  simp only [hG] at this
  rw [Complex.exp_neg] at this
  have hne := Complex.exp_ne_zero (binetLogGamma z)
  field_simp at this
  exact this.symm

lemma binetLogGamma_real_form {x : ℝ} (hx : 0 < x) :
    binetLogGamma (x : ℂ) = (((x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 +
      ∫ t in Ioi (0 : ℝ), binetKernel t / t * Real.exp (-(t * x)) : ℝ) : ℂ) := by
  have hB : binetB (x : ℂ) =
      ((∫ t in Ioi (0 : ℝ), binetKernel t / t * Real.exp (-(t * x)) : ℝ) : ℂ) := lap_ofReal x
  unfold binetLogGamma
  rw [hB, ← Complex.ofReal_log hx.le]
  push_cast
  ring

/-- On the positive axis `binetLogGamma` is the real `log Γ`. -/
theorem binetLogGamma_ofReal {x : ℝ} (hx : 0 < x) :
    binetLogGamma (x : ℂ) = ((Real.log (Real.Gamma x) : ℝ) : ℂ) := by
  have hxr : 0 < (x : ℂ).re := by simpa using hx
  have h := exp_binetLogGamma hxr
  rw [binetLogGamma_real_form hx, Complex.Gamma_ofReal, ← Complex.ofReal_exp] at h
  have h' := Complex.ofReal_injective h
  rw [binetLogGamma_real_form hx, ← h', Real.log_exp]

/-- Real Binet formula: for `x > 0`,
`log Γ(x) = (x - 1/2) log x - x + (1/2) log 2π + ∫_0^∞ (1/2 - 1/t + 1/(e^t-1)) e^{-tx}/t dt`. -/
theorem log_Gamma_eq_binet {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) = (x - 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 +
      ∫ t in Ioi (0 : ℝ), binetKernel t / t * Real.exp (-(t * x)) := by
  have h := binetLogGamma_ofReal hx
  rw [binetLogGamma_real_form hx] at h
  exact (Complex.ofReal_injective h).symm

lemma binetLogGamma_one : binetLogGamma 1 = 0 := by
  have := binetLogGamma_ofReal (x := 1) one_pos
  simpa using this

/-- Uniqueness of the branch: a holomorphic `L` on `Re z > 0` with `exp L = Γ` and `L 1 = 0`
equals `binetLogGamma`. -/
theorem eq_binetLogGamma_of_differentiableOn {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L rhp)
    (hexp : ∀ z ∈ rhp, Complex.exp (L z) = Complex.Gamma z) (h1 : L 1 = 0) :
    ∀ z ∈ rhp, L z = binetLogGamma z := by
  have hderiv : ∀ w ∈ rhp, HasDerivAt L (Complex.digamma w) w := by
    intro w hw
    have hwr : 0 < w.re := hw
    have hLd : HasDerivAt L (deriv L w) w :=
      (hL.differentiableAt (isOpen_rhp.mem_nhds hw)).hasDerivAt
    have h1' := hLd.cexp
    have h2' : HasDerivAt (fun v => Complex.exp (L v)) (Complex.digamma w * Complex.Gamma w) w :=
      (hasDerivAt_Gamma_digamma hwr).congr_of_eventuallyEq (by
        filter_upwards [isOpen_rhp.mem_nhds hw] with v hv using hexp v hv)
    have := h1'.unique h2'
    rw [hexp w hw] at this
    have hne := Complex.Gamma_ne_zero (re_pos_ne_neg_nat hwr)
    have : deriv L w = Complex.digamma w := mul_left_cancel₀ hne (by linear_combination this)
    rwa [← this]
  intro z hz
  set H : ℂ → ℂ := fun w => L w - binetLogGamma w with hH
  have hHd : ∀ w ∈ rhp, HasDerivAt H 0 w := fun w hw => by
    exact ((hderiv w hw).sub (hasDerivAt_binetLogGamma (show 0 < w.re from hw))).congr_deriv
      (sub_self _)
  have hconst := isOpen_rhp.is_const_of_deriv_eq_zero isPreconnected_rhp
    (fun x hx => (hHd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hHd x hx).deriv) hz (by simp [rhp] : (1 : ℂ) ∈ rhp)
  simp only [hH, h1, binetLogGamma_one, sub_zero] at hconst
  exact sub_eq_zero.1 hconst


/-- `Im binetLogGamma z = arg Γ(z) + 2π n` for some integer `n` (continuous `arg Γ`). -/
theorem exists_int_im_binetLogGamma {z : ℂ} (hz : 0 < z.re) :
    ∃ n : ℤ, (binetLogGamma z).im = Complex.arg (Complex.Gamma z) + 2 * Real.pi * n := by
  have hne := Complex.Gamma_ne_zero (re_pos_ne_neg_nat hz)
  have h : Complex.exp (binetLogGamma z) = Complex.exp (Complex.log (Complex.Gamma z)) := by
    rw [exp_binetLogGamma hz, Complex.exp_log hne]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  rw [Complex.log_im] at this
  linarith

/-- `ψ' = 1/z + 1/(2z²) + binetI'(z)`. -/
lemma hasDerivAt_digamma_binet {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.digamma (z⁻¹ + 1 / 2 * (z ^ 2)⁻¹ + binetI' z) z := by
  have hz0 := re_pos_ne_zero hz
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl hz)
  have h1 := (((Complex.hasDerivAt_log hslit).sub ((hasDerivAt_inv hz0).const_mul (1 / 2 : ℂ))).sub
    (hasDerivAt_binetI hz))
  refine (h1.congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp
    ring
  · filter_upwards [isOpen_rhp.mem_nhds (show z ∈ rhp from hz)] with w hw
    exact digamma_eq_binet hw

/-- `‖ψ(z) - (log z - 1/(2z))‖ ≤ 1/‖z‖²` on `Re z > 0` (Stirling remainder for `ψ`). -/
theorem norm_digamma_sub_le {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.digamma z - (Complex.log z - 1 / 2 * z⁻¹)‖ ≤ 1 / ‖z‖ ^ 2 := by
  have : Complex.digamma z - (Complex.log z - 1 / 2 * z⁻¹) = -binetI z := by
    rw [digamma_eq_binet hz]; ring
  rw [this, norm_neg]
  exact norm_binetI_le_div hz

/-- `‖ψ'(z) - 1/z - 1/(2z²)‖ ≤ (2/3)/‖z‖³` on `Re z > 0`. -/
theorem norm_deriv_digamma_sub_le {z : ℂ} (hz : 0 < z.re) :
    ‖deriv Complex.digamma z - (z⁻¹ + 1 / 2 * (z ^ 2)⁻¹)‖ ≤ 2 / 3 / ‖z‖ ^ 3 := by
  rw [(hasDerivAt_digamma_binet hz).deriv]
  simpa using norm_binetI'_le_div hz

/-- `‖log Γ(z) - ((z - 1/2) log z - z + (1/2) log 2π)‖ ≤ 2/‖z‖` for the branch `binetLogGamma`. -/
theorem norm_binetLogGamma_sub_le {z : ℂ} (hz : 0 < z.re) :
    ‖binetLogGamma z - ((z - 1 / 2) * Complex.log z - z +
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ))‖ ≤ 2 / ‖z‖ := by
  have : binetLogGamma z - ((z - 1 / 2) * Complex.log z - z +
      ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ)) = binetB z := by
    unfold binetLogGamma; ring
  rw [this]
  exact norm_binetB_le_div hz


/-- info: 'FormalResearch.Special.ComplexStirling.digamma_eq_binet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.digamma_eq_binet

/-- info: 'FormalResearch.Special.ComplexStirling.exp_binetLogGamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.exp_binetLogGamma

/-- info: 'FormalResearch.Special.ComplexStirling.binetLogGamma_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.binetLogGamma_ofReal

/-- info: 'FormalResearch.Special.ComplexStirling.log_Gamma_eq_binet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.log_Gamma_eq_binet

/-- info: 'FormalResearch.Special.ComplexStirling.eq_binetLogGamma_of_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.eq_binetLogGamma_of_differentiableOn

/-- info: 'FormalResearch.Special.ComplexStirling.norm_digamma_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_digamma_sub_le

/-- info: 'FormalResearch.Special.ComplexStirling.norm_deriv_digamma_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_deriv_digamma_sub_le

/-- info: 'FormalResearch.Special.ComplexStirling.norm_binetLogGamma_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.norm_binetLogGamma_sub_le

/-- info: 'FormalResearch.Special.ComplexStirling.exists_int_im_binetLogGamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ComplexStirling.exists_int_im_binetLogGamma

end FormalResearch.Special.ComplexStirling
