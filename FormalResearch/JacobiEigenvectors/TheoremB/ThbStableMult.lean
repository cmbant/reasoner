module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremB.ThbStableSchur

/-!
# Paper J, Theorem B, L3.D step 2 (concrete multiplier): `f = chi(x)/x` has an integrable frequency profile

Source: Paper J `thmB.tex`, Corollary `cor:thb-stable`, proof: "Fix an even `chi in C^infty` with `chi = 0` on `[-1/4, 1/4]`
and `chi = 1` outside `(-1/2, 1/2)`, and put `f(x) = chi(x)/x`; then `f, f' in L^2`, so `fhat in L^1`.  With
`f_gamma(x) = gamma^{-1} f(x/gamma)`, `||fhat_gamma||_1 = gamma^{-1} ||fhat||_1`."

Claim class: **proved** (no hypothesis, no new axiom).

## Proved here (axiom-pinned)

* `chi`: the cutoff `Real.smoothTransition (16 x^2 - 1)`: smooth (`chi_contDiff`), even, `0` on `|x| <= 1/4`
  (`chi_zero`), `1` on `|x| >= 1/2` (`chi_one`), even (`chi_neg`).  `fR x = chi x / x`, `fC` its complex-valued version (the paper's `f`).
* `fC_rep`: there is an integrable `g : R -> C` (the paper's `fhat`) with
  `f(u) = (2 pi)^{-1} int g(t) e^{itu} dt` for **every** real `u` (the hypothesis `hrep` of `thb_schur_fourier_norm_le`).
* `fG gamma x = gamma^{-1} f(x/gamma)`, with `fG_of_large` (`= 1/x` for `|x| >= gamma/2`) and `fG_of_small`
  (`= 0` for `|x| <= gamma/4`).
* `thb_multiplier_bound`: an absolute constant `cf >= 0` with
  `||(f_gamma(x_j - y_k) E_jk)||_op <= (cf / gamma) ||E||_op` for all `gamma > 0`, all `x, y, E`.  (`cf` is the paper's
  `c_f = ||fhat||_1 / (2 pi)`; it depends on `chi` alone.)

## The route (shortest available in this Mathlib pin)

`f` is in `L^2` but not in `L^1` (it is `1/x` at infinity) and this pin has no `L^2` Fourier inversion, so the route
through `f, f' in L^2` is not available.  Instead `f = f_0 + r` with `f_0(x) = x/(1+x^2)` and `r = f - f_0`:

* `f_0` has the explicit profile `g_0(t) = -i pi sgn(t) e^{-|t|}` (`integral_g0`, two exponential integrals).
* `r` is smooth and for `|x| >= 1/2` equals `1/(x(1+x^2))`, so `r, r', r''` are `O((1+x^2)^{-1})`
  (`rR_bounds`, explicit derivatives `rho, rho1, rho2`, compactness inside `|x| <= 1/2`), hence integrable;
  Mathlib's `Real.one_add_sq_mul_norm_fourier_le` gives `(1+u^2) |rhat(u)| <= B`, so `rhat` is integrable
  (`fourier_rC_integrable`), and `thb_fourier_inv_angular` (`ThbStableSchur.lean`) is the inversion for `r`.
* `g = g_0 + rhat((2 pi)^{-1} .)` (`fC_rep`).

## Differences from the paper

* The paper argues `f, f' in L^2 => fhat in L^1`; this file proves the representation `hrep` with an explicit `g`
  instead (the constant `cf` is not computed).  The cutoff is `chi(x) = smoothTransition(16 x^2 - 1)`, which is
  admissible for the paper's conditions (even, smooth, `0` on `[-1/4,1/4]`, `1` outside `(-1/2,1/2)`).
* `fG_of_large` is stated for `|x| >= gamma/2` and `fG_of_small` for `|x| <= gamma/4`, the only two facts about
  `f_gamma` the paper's proof uses.

## Not formalised

`||fhat_gamma||_1 = gamma^{-1} ||fhat||_1` is used in the form of the scaling inside `thb_multiplier_bound`; the numerical
value of `c_f`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology
open scoped Matrix.Norms.L2Operator

namespace FormalResearch.JacobiEigenvectors.TheoremB.ThbMult

/-- cutoff -/
noncomputable def chi (x : ℝ) : ℝ := Real.smoothTransition (16 * x ^ 2 - 1)

lemma chi_contDiff : ContDiff ℝ (⊤ : ℕ∞) chi := by
  unfold chi
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma chi_neg (x : ℝ) : chi (-x) = chi x := by simp [chi]

lemma chi_zero {x : ℝ} (h : |x| ≤ 1/4) : chi x = 0 := by
  unfold chi
  apply Real.smoothTransition.zero_of_nonpos
  have : x ^ 2 ≤ (1/4) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith

lemma chi_one {x : ℝ} (h : 1/2 ≤ |x|) : chi x = 1 := by
  unfold chi
  apply Real.smoothTransition.one_of_one_le
  have : (1/2) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
  rw [sq_abs] at this
  nlinarith

/-- multiplier real -/
noncomputable def fR (x : ℝ) : ℝ := chi x / x

lemma fR_contDiff : ContDiff ℝ (⊤ : ℕ∞) fR := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have : fR =ᶠ[𝓝 0] fun _ => (0:ℝ) := by
      have : Set.Ioo (-(1/4:ℝ)) (1/4) ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [this] with y hy
      unfold fR
      rw [chi_zero (by rw [abs_le]; constructor <;> linarith [hy.1, hy.2])]
      simp
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · exact (chi_contDiff.contDiffAt).div contDiffAt_id hx


/-- the explicit odd function with explicit Fourier representation -/
noncomputable def f0R (x : ℝ) : ℝ := x / (1 + x ^ 2)

noncomputable def rR (x : ℝ) : ℝ := fR x - f0R x

lemma f0R_contDiff : ContDiff ℝ (⊤ : ℕ∞) f0R := by
  unfold f0R
  refine contDiff_id.div (by fun_prop) (fun x => by positivity)

lemma rR_contDiff : ContDiff ℝ (⊤ : ℕ∞) rR := fR_contDiff.sub f0R_contDiff

/-- tail rational function -/
noncomputable def rho (x : ℝ) : ℝ := 1 / (x * (1 + x ^ 2))
noncomputable def rho1 (x : ℝ) : ℝ := -(1 + 3 * x ^ 2) / (x * (1 + x ^ 2)) ^ 2
noncomputable def rho2 (x : ℝ) : ℝ :=
  -(6 * x) / (x * (1 + x ^ 2)) ^ 2 + 2 * (1 + 3 * x ^ 2) ^ 2 / (x * (1 + x ^ 2)) ^ 3

lemma rR_eq_rho {x : ℝ} (h : 1/2 ≤ |x|) : rR x = rho x := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0] at h; simp at h; linarith
  unfold rR fR f0R rho
  rw [chi_one h]
  have : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma rR_eventuallyEq_rho {x : ℝ} (h : 1/2 < |x|) : rR =ᶠ[𝓝 x] rho := by
  have : {y : ℝ | 1/2 < |y|} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds h
  filter_upwards [this] with y hy
  exact rR_eq_rho (le_of_lt hy)

lemma hasDerivAt_u (x : ℝ) : HasDerivAt (fun y : ℝ => y * (1 + y ^ 2)) (1 + 3 * x ^ 2) x := by
  have h := (hasDerivAt_id' x).fun_mul (((hasDerivAt_id' x).fun_pow 2).const_add 1)
  convert h using 1
  simp; ring

lemma hasDerivAt_rho {x : ℝ} (hx : x ≠ 0) : HasDerivAt rho (rho1 x) x := by
  have hne : x * (1 + x ^ 2) ≠ 0 := by positivity
  have := (hasDerivAt_const x (1:ℝ)).fun_div (hasDerivAt_u x) hne
  unfold rho rho1
  convert this using 1
  simp

lemma hasDerivAt_rho1 {x : ℝ} (hx : x ≠ 0) : HasDerivAt rho1 (rho2 x) x := by
  have hne : x * (1 + x ^ 2) ≠ 0 := by positivity
  have h2 : HasDerivAt (fun y : ℝ => -(1 + 3 * y ^ 2)) (-(6 * x)) x := by
    have h := ((((hasDerivAt_id' x).fun_pow 2).const_mul 3).const_add 1).neg
    convert h using 1
    simp; ring
  have h3 := (hasDerivAt_u x).fun_pow 2
  have := h2.fun_div h3 (pow_ne_zero 2 hne)
  unfold rho1 rho2
  convert this using 1
  field_simp
  ring


lemma sq_ge_quarter {x : ℝ} (h : 1/2 ≤ |x|) : 1/4 ≤ x ^ 2 := by
  have : (1/2) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
  rw [sq_abs] at this
  nlinarith

lemma rho_bound {x : ℝ} (h : 1/2 ≤ |x|) : |rho x| * (1 + x ^ 2) ≤ 2 := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0] at h; simp at h; linarith
  have hp : 0 < 1 + x ^ 2 := by positivity
  unfold rho
  rw [abs_div, abs_one, abs_mul, abs_of_pos hp]
  have : 0 < |x| := abs_pos.2 hx
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

lemma rho1_bound {x : ℝ} (h : 1/2 ≤ |x|) : |rho1 x| * (1 + x ^ 2) ≤ 12 := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0] at h; simp at h; linarith
  have hq := sq_ge_quarter h
  have hp : 0 < 1 + x ^ 2 := by positivity
  unfold rho1
  have hd : 0 < (x * (1 + x ^ 2)) ^ 2 := by positivity
  rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 + 3 * x ^ 2), abs_of_pos hd,
    div_mul_eq_mul_div, div_le_iff₀ hd]
  have : (x * (1 + x ^ 2)) ^ 2 = x ^ 2 * (1 + x ^ 2) ^ 2 := by ring
  rw [this]
  nlinarith [mul_pos hp hp, mul_nonneg (sub_nonneg.2 hq) hp.le, mul_nonneg (mul_nonneg (sub_nonneg.2 hq) hp.le) hp.le]

lemma rho2_bound {x : ℝ} (h : 1/2 ≤ |x|) : |rho2 x| * (1 + x ^ 2) ≤ 160 := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0] at h; simp at h; linarith
  have hq := sq_ge_quarter h
  have hp : 0 < 1 + x ^ 2 := by positivity
  have hu : 0 < |x| * (1 + x ^ 2) := by have := abs_pos.2 hx; positivity
  unfold rho2
  have e1 : |-(6 * x) / (x * (1 + x ^ 2)) ^ 2| * (1 + x ^ 2) ≤ 12 := by
    rw [abs_div, abs_neg, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6), abs_pow, abs_mul,
      abs_of_pos hp]
    have ha : 0 < |x| := abs_pos.2 hx
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have : |x| ^ 2 = x ^ 2 := sq_abs x
    have h1 : 1/2 ≤ |x| := h
    nlinarith [mul_pos hp hp, mul_pos ha hp, mul_pos (mul_pos ha hp) hp]
  have e2 : |2 * (1 + 3 * x ^ 2) ^ 2 / (x * (1 + x ^ 2)) ^ 3| * (1 + x ^ 2) ≤ 148 := by
    have ha : 0 < |x| := abs_pos.2 hx
    rw [abs_div, abs_mul, abs_pow, abs_pow, abs_mul, abs_of_pos hp,
      abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos (by positivity : (0:ℝ) < 1 + 3 * x ^ 2)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h3 : |x| ^ 3 ≥ 1/8 := by
      have := pow_le_pow_left₀ (by norm_num) h 3
      nlinarith
    have hs : 1 + 3 * x ^ 2 ≤ 3 * (1 + x ^ 2) := by nlinarith
    have hs2 : (1 + 3 * x ^ 2) ^ 2 ≤ 9 * (1 + x ^ 2) ^ 2 := by nlinarith [sq_nonneg (1 + 3 * x ^ 2)]
    have hp3 : 0 < (1 + x ^ 2) ^ 3 := by positivity
    nlinarith [mul_pos hp hp, mul_pos hp3 ha, mul_le_mul_of_nonneg_left hs2 (by positivity : (0:ℝ) ≤ 2 * (1 + x ^ 2)),
      mul_le_mul_of_nonneg_left h3 hp3.le]
  calc |-(6 * x) / (x * (1 + x ^ 2)) ^ 2 + 2 * (1 + 3 * x ^ 2) ^ 2 / (x * (1 + x ^ 2)) ^ 3| * (1 + x ^ 2)
      ≤ (|-(6 * x) / (x * (1 + x ^ 2)) ^ 2| + |2 * (1 + 3 * x ^ 2) ^ 2 / (x * (1 + x ^ 2)) ^ 3|) * (1 + x ^ 2) :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) hp.le
    _ ≤ 160 := by nlinarith


lemma ne_zero_of_half {x : ℝ} (h : 1/2 < |x|) : x ≠ 0 := by
  intro h0; rw [h0] at h; simp at h; linarith

lemma deriv_rR_ext {x : ℝ} (h : 1/2 < |x|) : deriv rR x = rho1 x := by
  rw [(rR_eventuallyEq_rho h).deriv_eq]
  exact (hasDerivAt_rho (ne_zero_of_half h)).deriv

lemma deriv2_rR_ext {x : ℝ} (h : 1/2 < |x|) : deriv (deriv rR) x = rho2 x := by
  have h1 : deriv rR =ᶠ[𝓝 x] rho1 := by
    have : {y : ℝ | 1/2 < |y|} ∈ 𝓝 x :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds h
    filter_upwards [this] with y hy
    exact deriv_rR_ext hy
  rw [h1.deriv_eq]
  exact (hasDerivAt_rho1 (ne_zero_of_half h)).deriv

lemma bound_of_ext {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (h : ∀ x, 1/2 < |x| → |g x| * (1 + x ^ 2) ≤ C) : ∃ C', ∀ x, |g x| * (1 + x ^ 2) ≤ C' := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-(1/2:ℝ))) (b := 1/2)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C (M * (5/4)), fun x => ?_⟩
  by_cases hx : 1/2 < |x|
  · exact (h x hx).trans (le_max_left _ _)
  · replace hx := not_lt.1 hx
    have hx' : x ∈ Set.Icc (-(1/2:ℝ)) (1/2) := by rw [abs_le] at hx; exact ⟨hx.1, hx.2⟩
    have h1 := hM x hx'
    rw [Real.norm_eq_abs] at h1
    have h2 : x ^ 2 ≤ 1/4 := by
      have : |x| ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
      rw [sq_abs] at this; linarith
    refine le_trans ?_ (le_max_right _ _)
    have : 0 ≤ M := (abs_nonneg _).trans h1
    nlinarith [abs_nonneg (g x)]

lemma rR_cd (n : ℕ) : ContDiff ℝ n rR :=
  rR_contDiff.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

lemma rR_bounds : ∃ C, ∀ x, |rR x| * (1 + x ^ 2) ≤ C ∧ |deriv rR x| * (1 + x ^ 2) ≤ C ∧
    |deriv (deriv rR) x| * (1 + x ^ 2) ≤ C := by
  have hc : ContDiff ℝ 2 rR := rR_cd 2
  have h0 : Continuous rR := hc.continuous
  have h1 : Continuous (deriv rR) := hc.continuous_deriv (by norm_num)
  have h2 : Continuous (deriv (deriv rR)) := by
    have h1 : ContDiff ℝ (1 + 1) (deriv rR) := (contDiff_succ_iff_deriv.1 (rR_cd 3)).2.2
    exact (contDiff_succ_iff_deriv.1 h1).2.2.continuous
  obtain ⟨C0, hC0⟩ := bound_of_ext (C := 2) h0 (fun x hx => by
    rw [rR_eq_rho hx.le]; exact rho_bound hx.le)
  obtain ⟨C1, hC1⟩ := bound_of_ext (C := 12) h1 (fun x hx => by
    rw [deriv_rR_ext hx]; exact rho1_bound hx.le)
  obtain ⟨C2, hC2⟩ := bound_of_ext (C := 160) h2 (fun x hx => by
    rw [deriv2_rR_ext hx]; exact rho2_bound hx.le)
  exact ⟨max C0 (max C1 C2), fun x => ⟨(hC0 x).trans (le_max_left _ _),
    (hC1 x).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hC2 x).trans ((le_max_right _ _).trans (le_max_right _ _))⟩⟩


open FourierTransform in
/-- complex version -/
noncomputable def rC (x : ℝ) : ℂ := (rR x : ℂ)

lemma rC_cd : ContDiff ℝ 2 rC :=
  Complex.ofRealCLM.contDiff.comp (rR_cd 2)

lemma deriv_rC : deriv rC = fun x => ((deriv rR x : ℝ) : ℂ) := by
  funext x
  have hd : DifferentiableAt ℝ rR x := ((rR_cd 1).differentiable (by norm_num)) x
  exact (hd.hasDerivAt.ofReal_comp).deriv

lemma deriv2_rC : deriv (deriv rC) = fun x => ((deriv (deriv rR) x : ℝ) : ℂ) := by
  rw [deriv_rC]
  funext x
  have hd : DifferentiableAt ℝ (deriv rR) x := by
    have h1 : ContDiff ℝ 1 (deriv rR) := (contDiff_succ_iff_deriv.1 (rR_cd 2)).2.2
    exact (h1.differentiable (by norm_num)) x
  exact (hd.hasDerivAt.ofReal_comp).deriv

lemma integrable_of_bound {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ}
    (h : ∀ x, ‖g x‖ * (1 + x ^ 2) ≤ C) : Integrable g := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hg.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hp : 0 < 1 + x ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  exact h x

lemma rC_integrable : ∀ k ≤ 2, Integrable (iteratedDeriv k rC) := by
  obtain ⟨C, hC⟩ := rR_bounds
  have h0 : Continuous rC := rC_cd.continuous
  intro k hk
  interval_cases k
  · rw [iteratedDeriv_zero]
    exact integrable_of_bound h0 (C := C) fun x => by
      simpa [rC, Complex.norm_real] using (hC x).1
  · rw [iteratedDeriv_one, deriv_rC]
    refine integrable_of_bound (C := C) ?_ fun x => by
      simpa [Complex.norm_real] using (hC x).2.1
    exact Complex.continuous_ofReal.comp ((rR_cd 2).continuous_deriv (by norm_num))
  · rw [iteratedDeriv_succ, iteratedDeriv_one, deriv2_rC]
    refine integrable_of_bound (C := C) ?_ fun x => by
      simpa [Complex.norm_real] using (hC x).2.2
    have h1 : ContDiff ℝ (1 + 1) (deriv rR) := (contDiff_succ_iff_deriv.1 (rR_cd 3)).2.2
    have h2 : ContDiff ℝ 1 (deriv (deriv rR)) := (contDiff_succ_iff_deriv.1 h1).2.2
    exact Complex.continuous_ofReal.comp h2.continuous

open FourierTransform in
lemma fourier_rC_integrable : Integrable (𝓕 rC) := by
  have hc : ContDiff ℝ 2 rC := rC_cd
  have hb := fun u => Real.one_add_sq_mul_norm_fourier_le hc rC_integrable u
  set B := (∫ v, ‖rC v‖) + (4 * Real.pi ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 rC v‖ with hB
  have hcont : Continuous (𝓕 rC) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ (by simpa using rC_integrable 0 (by norm_num))
  exact integrable_of_bound hcont (C := B) fun x => by rw [mul_comm]; exact hb x


/-- The explicit frequency profile of `x / (1 + x^2)`: `-i pi sgn(t) e^{-|t|}`. -/
noncomputable def g0 (t : ℝ) : ℂ :=
  if 0 < t then -((Real.pi : ℂ) * Complex.I) * Complex.exp (-(t : ℂ))
  else ((Real.pi : ℂ) * Complex.I) * Complex.exp (t : ℂ)

lemma exp_mul_exp_eq (a : ℂ) (t u : ℝ) :
    Complex.exp (a * (t : ℂ)) * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) =
      Complex.exp ((a + Complex.I * u) * (t : ℂ)) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma g0_mul_pos {t : ℝ} (ht : 0 < t) (u : ℝ) :
    g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) =
      -((Real.pi : ℂ) * Complex.I) * Complex.exp ((-1 + Complex.I * u) * (t : ℂ)) := by
  simp only [g0, ht, ↓reduceIte]
  rw [mul_assoc]
  have := exp_mul_exp_eq (-1) t u
  rw [show -(t : ℂ) = (-1) * (t : ℂ) by ring, this]

lemma g0_mul_nonpos {t : ℝ} (ht : ¬ 0 < t) (u : ℝ) :
    g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) =
      ((Real.pi : ℂ) * Complex.I) * Complex.exp ((1 + Complex.I * u) * (t : ℂ)) := by
  simp only [g0, ht, ↓reduceIte]
  rw [mul_assoc]
  have := exp_mul_exp_eq 1 t u
  rw [show (t : ℂ) = 1 * (t : ℂ) by ring, this]
  simp

lemma integrableOn_g0_Ioi (u : ℝ) :
    IntegrableOn (fun t : ℝ => g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ))) (Set.Ioi 0) := by
  have h := (integrableOn_exp_mul_complex_Ioi (a := -1 + Complex.I * u) (by simp) 0).const_mul
    (-((Real.pi : ℂ) * Complex.I))
  exact IntegrableOn.congr_fun h (fun t ht => (g0_mul_pos ht u).symm) measurableSet_Ioi

lemma integrableOn_g0_Iic (u : ℝ) :
    IntegrableOn (fun t : ℝ => g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ))) (Set.Iic 0) := by
  have h := (integrableOn_exp_mul_complex_Iic (a := 1 + Complex.I * u) (by simp) 0).const_mul
    (((Real.pi : ℂ) * Complex.I))
  exact IntegrableOn.congr_fun h (fun t ht => (g0_mul_nonpos (not_lt.2 ht) u).symm) measurableSet_Iic

lemma integrable_g0_mul (u : ℝ) :
    Integrable (fun t : ℝ => g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ))) := by
  have := (integrableOn_g0_Iic u).union (integrableOn_g0_Ioi u)
  rwa [Set.Iic_union_Ioi, integrableOn_univ] at this

lemma integrable_g0 : Integrable g0 := by
  simpa using integrable_g0_mul 0

lemma integral_g0 (u : ℝ) :
    ∫ t : ℝ, g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) =
      2 * Real.pi * ((u / (1 + u ^ 2) : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (integrableOn_g0_Iic u) (integrableOn_g0_Ioi u)]
  have h1 : ∫ t : ℝ in Set.Ioi 0, g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) =
      -((Real.pi : ℂ) * Complex.I) * (-Complex.exp ((-1 + Complex.I * u) * ((0:ℝ):ℂ)) /
        (-1 + Complex.I * u)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => g0_mul_pos ht u),
      integral_const_mul, integral_exp_mul_complex_Ioi (by simp)]
  have h2 : ∫ t : ℝ in Set.Iic 0, g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) =
      ((Real.pi : ℂ) * Complex.I) * (Complex.exp ((1 + Complex.I * u) * ((0:ℝ):ℂ)) /
        (1 + Complex.I * u)) := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun t ht => g0_mul_nonpos (not_lt.2 ht) u),
      integral_const_mul, integral_exp_mul_complex_Iic (by simp)]
  rw [h1, h2]
  have hu1 : (1 + Complex.I * u) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hu2 : (-1 + Complex.I * u) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hp : (1 + (u : ℂ) ^ 2) ≠ 0 := by
    have : (1 + u ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring


lemma integrable_mul_phase {g : ℝ → ℂ} (hg : Integrable g) (u : ℝ) :
    Integrable (fun t : ℝ => g t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ))) := by
  refine Integrable.mono' hg.norm (hg.aestronglyMeasurable.mul (by fun_prop)) (ae_of_all _ fun t => ?_)
  simp [Complex.norm_exp]

/-- The multiplier `f = chi(x)/x` (Paper J, `cor:thb-stable`, step 2). -/
noncomputable def fC (x : ℝ) : ℂ := ((fR x : ℝ) : ℂ)

lemma fC_eq : ∀ x, fC x = ((f0R x : ℝ) : ℂ) + rC x := by
  intro x; unfold fC rC rR; push_cast; ring

open FourierTransform in
/-- **`f = chi/x` has an integrable frequency profile.** -/
theorem fC_rep : ∃ g : ℝ → ℂ, Integrable g ∧ ∀ u : ℝ, fC u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
    ∫ t : ℝ, g t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) := by
  have hint0 : Integrable rC := by simpa using rC_integrable 0 (by norm_num)
  have hF := fourier_rC_integrable
  set h : ℝ → ℂ := fun t => 𝓕 rC ((2 * Real.pi)⁻¹ * t) with hh
  have hhint : Integrable h := hF.comp_mul_left' (R := (2 * Real.pi)⁻¹) (by positivity)
  refine ⟨fun t => g0 t + h t, integrable_g0.add hhint, fun u => ?_⟩
  have e1 : ((f0R u : ℝ) : ℂ) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, g0 t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) := by
    rw [integral_g0]
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    unfold f0R
    push_cast
    field_simp
  have e2 : rC u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, h t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) :=
    thb_fourier_inv_angular rC rC_cd.continuous hint0 hF u
  rw [fC_eq, e1, e2, ← mul_add]
  congr 1
  rw [← integral_add (integrable_g0_mul u) (integrable_mul_phase hhint u)]
  congr 1; funext t; ring

/-- the scaled multiplier `f_gamma(x) = gamma^{-1} f(x/gamma)` -/
noncomputable def fG (γ x : ℝ) : ℂ := ((γ⁻¹ : ℝ) : ℂ) * fC (x / γ)

lemma fG_of_large {γ x : ℝ} (hγ : 0 < γ) (h : γ / 2 ≤ |x|) : fG γ x = (x : ℂ)⁻¹ := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0] at h; simp at h; linarith
  have h1 : 1/2 ≤ |x / γ| := by
    rw [abs_div, abs_of_pos hγ, le_div_iff₀ hγ]; linarith
  unfold fG fC fR
  rw [chi_one h1]
  have : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  push_cast
  field_simp

lemma fG_of_small {γ x : ℝ} (hγ : 0 < γ) (h : |x| ≤ γ / 4) : fG γ x = 0 := by
  have h1 : |x / γ| ≤ 1/4 := by
    rw [abs_div, abs_of_pos hγ, div_le_iff₀ hγ]; linarith
  unfold fG fC fR
  rw [chi_zero h1]
  simp

/-- **The Fourier--Schur bound for `f_gamma`**: `‖(f_gamma(x_j - y_k) E_jk)‖ <= (c_f / gamma) ‖E‖` with an
absolute constant `c_f` (Paper J: `c_f = ‖fhat‖_1 / (2 pi)`). -/
theorem thb_multiplier_bound : ∃ cf : ℝ, 0 ≤ cf ∧ ∀ γ : ℝ, 0 < γ → ∀ {n m : ℕ} (x : Fin n → ℝ)
    (y : Fin m → ℝ) (E : Matrix (Fin n) (Fin m) ℂ),
    ‖Matrix.of fun j k => fG γ (x j - y k) * E j k‖ ≤ cf / γ * ‖E‖ := by
  obtain ⟨g, hg, hrep⟩ := fC_rep
  refine ⟨(2 * Real.pi)⁻¹ * ∫ t, ‖g t‖, by positivity, fun γ hγ n m x y E => ?_⟩
  have hγ0 : γ ≠ 0 := hγ.ne'
  set gγ : ℝ → ℂ := fun s => g (γ * s) with hgγ
  have hgγint : Integrable gγ := hg.comp_mul_left' (R := γ) hγ0
  have hrepγ : ∀ u : ℝ, fG γ u = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ, gγ t * Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) := by
    intro u
    have hs := MeasureTheory.Measure.integral_comp_mul_left
      (fun t : ℝ => g t * Complex.exp (Complex.I * ((t * (u / γ) : ℝ) : ℂ))) γ
    have hpt : ∀ s : ℝ, g (γ * s) * Complex.exp (Complex.I * ((γ * s * (u / γ) : ℝ) : ℂ)) =
        gγ s * Complex.exp (Complex.I * ((s * u : ℝ) : ℂ)) := by
      intro s
      have : γ * s * (u / γ) = s * u := by field_simp
      rw [this]
    simp only [hpt] at hs
    rw [abs_of_pos (inv_pos.2 hγ), Complex.real_smul] at hs
    unfold fG
    rw [hrep (u / γ), hs]
    ring
  have key := thb_schur_fourier_norm_le (fG γ) gγ hgγint hrepγ x y E
  refine key.trans (le_of_eq ?_)
  have hs := MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ => ‖g t‖) γ
  rw [abs_of_pos (inv_pos.2 hγ), smul_eq_mul] at hs
  have : (∫ t, ‖gγ t‖) = γ⁻¹ * ∫ t, ‖g t‖ := hs
  rw [this]
  field_simp


end FormalResearch.JacobiEigenvectors.TheoremB.ThbMult

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.ThbMult.fC_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.ThbMult.fC_rep

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.ThbMult.thb_multiplier_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.ThbMult.thb_multiplier_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.ThbMult.fG_of_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.ThbMult.fG_of_large

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.ThbMult.fG_of_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.ThbMult.fG_of_small
