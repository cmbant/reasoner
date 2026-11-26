module

public import FormalResearch.SignUncertainty.FctCompDPart1
public import FormalResearch.SignUncertainty.FctCompDCauchy
public import FormalResearch.SignUncertainty.UctStripIntegrals

/-!
# `fct:comp-D` Part (2a): cosine vacuum penalty `(fct:cos-pen)` and curvature-paired integrals `(fct:curv-p-int)`

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma FCT.3 (`fct:comp-D`), Part (2)
(lines 207–217, 251–265).

Proves:
* `fct_comp_D_cos_penalty`: `(fct:cos-pen)` first equation — for `H_*`, the exact nonnegative
  cosine identity `∫_0^∞ (I_osc^{DH_*}(L) - I_fl(L)) dL = α_osc ∫_0^∞ |H_*(it)| e^{v(t)} (1 - cos ϑ_D(t)) dt`
  and `O_{K_4}(τ₁^3)` bound; for `H_CE`, `-(π/2) α_osc + O_{K_4}(τ₁^3)`.
* `fct_comp_D_curv_p_int`: `(fct:curv-p-int)` for `p ∈ {0, 1, 2}` —
  `∫_0^∞ I_osc^{H_0}(L) Δ_curv(τ₀(L)) / L^p dL = O_{K_4}(c⁻¹)` and the cross-term bound
  `∫_0^{10τ₁} (|H_0(it)| / m(t)^p) |e^{v(t)} - 1| |Δ_curv(t)| dt = O_{K_4}(c⁻¹ τ₁^{-2p})`.
* `fct_comp_D_Dstar_int`: `(fct:cos-pen)` second equation —
  `∫_0^∞ D_*(L) dL = C_fl(H_0) + O_{K_4}(τ₁^3)`.

Class: proved, no hypotheses.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty.FctCompD

open FormalResearch.SignUncertainty
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.SignUncertainty.FctMoment
open FormalResearch.CohnElkies

/-! ### Part (2) envelope definitions -/

/-- Compensated oscillation envelope `I_osc^{DH_0}(L) = e^{v(τ₀(L))} I_osc^{H_0}(L)`. -/
noncomputable def stripIoscD (kind : StripKernelChoice) (v : ℝ → ℝ) (L : ℝ) : ℝ :=
  Real.exp (v (tau0 L)) * stripIosc kind L

/-- Curvature correction `Δ_curv(t) = (1/(2c)) (ϑ_{D₀}''(t)/m'(t) - ϑ_{D₀}'(t)/m(t))` on `t > 0`. -/
noncomputable def stripDeltaCurv (c : ℝ) (θ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / (2 * c)) * (iteratedDeriv 2 θ t / uctMderiv t - deriv θ t / uctM t)

/-- Compensated difference `D_*(L) = I_osc^{DH_0}(L)(1 + Δ_curv(τ₀(L))) - I_fl(L)`. -/
noncomputable def stripDstar (kind : StripKernelChoice) (c : ℝ) (v v0 : ℝ → ℝ) (L : ℝ) : ℝ :=
  stripIoscD kind v L * (1 + stripDeltaCurv c (fctThetaD v0) (tau0 L)) - uctIfl L

lemma norm_stripH0_star_imag {t : ℝ} (ht : 0 < t) :
    ‖stripH0 .star ((t : ℂ) * Complex.I)‖ =
      π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2) + π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) := by
  dsimp only [stripH0]
  have hnotint : ∀ n : ℤ, ((t : ℂ) * Complex.I) ≠ n := fun n h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [uct_H_split hnotint, uctHCE_imag]
  have h1sub : uctHCE (1 - (t : ℂ) * Complex.I) =
      ((π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) : ℝ) : ℂ) := by
    have h := uctHCE_one_add_imag (-t)
    rw [show (1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = 1 - (t : ℂ) * Complex.I by push_cast; ring,
      show π * -t / 2 = -(π * t / 2) by ring, Real.cosh_neg] at h
    exact h
  rw [h1sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    show -(π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2)) - π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) =
      -(π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2) + π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) by ring,
    abs_neg, abs_of_pos (by positivity)]

lemma norm_stripH0_ce_imag {t : ℝ} (ht : 0 < t) :
    ‖stripH0 .ce ((t : ℂ) * Complex.I)‖ = π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2) := by
  dsimp only [stripH0]; exact norm_uctHCE_imag ht

lemma uctMderiv_mul_stripIosc (kind : StripKernelChoice) {t : ℝ} (ht : 0 < t) :
    uctMderiv t * stripIosc kind (uctM t) = uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ := by
  cases kind
  · dsimp only [stripIosc]
    rw [uctIoscStar_eq (uctM_pos ht), mul_add, uctMderiv_mul_uctIoscCE ht, uctMderiv_mul_uctIoscH ht, ← mul_add,
      norm_stripH0_star_imag ht]
  · dsimp only [stripIosc]
    rw [uctMderiv_mul_uctIoscCE ht, norm_stripH0_ce_imag ht]

lemma uctMderiv_mul_stripIoscD (kind : StripKernelChoice) (v : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    uctMderiv t * stripIoscD kind v (uctM t) =
      uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * Real.exp (v t) := by
  unfold stripIoscD
  rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht]
  have h := uctMderiv_mul_stripIosc kind ht
  rw [show uctM t = ceEll (π * t / 2) from rfl] at h
  rw [show uctMderiv t * (Real.exp (v t) * stripIosc kind (ceEll (π * t / 2))) =
    (uctMderiv t * stripIosc kind (ceEll (π * t / 2))) * Real.exp (v t) by ring, h]

/-- Change of variables `L = m(t)` on `Ioi 0`: `∫ L in Ioi 0, g L = ∫ t in Ioi 0, m'(t) * g (m(t))`. -/
lemma uct_subst_zero (g : ℝ → ℝ) :
    ∫ L in Ioi (0 : ℝ), g L = ∫ t in Ioi (0 : ℝ), uctMderiv t * g (uctM t) := by
  have himg : uctM '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext L
    constructor
    · rintro ⟨t, ht, rfl⟩; exact uctM_pos ht
    · intro hL; exact ⟨tau0 L, tau0_pos hL, ceEll_tau0 hL⟩
  have hIoi : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
  conv_lhs => rw [← himg]
  rw [integral_image_eq_integral_abs_deriv_smul hIoi (f := uctM) (f' := uctMderiv)
    (fun t ht => (hasDerivAt_uctM ht).hasDerivWithinAt) uctM_strictMonoOn.injOn g]
  refine setIntegral_congr_fun hIoi fun t ht => ?_
  simp only [smul_eq_mul, abs_of_pos (uctMderiv_pos ht)]

lemma uct_subst_integrableOn_zero (g : ℝ → ℝ) :
    IntegrableOn g (Ioi (0 : ℝ)) ↔ IntegrableOn (fun t => uctMderiv t * g (uctM t)) (Ioi (0 : ℝ)) := by
  have himg : uctM '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext L
    constructor
    · rintro ⟨t, ht, rfl⟩; exact uctM_pos ht
    · intro hL; exact ⟨tau0 L, tau0_pos hL, ceEll_tau0 hL⟩
  have hIoi : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
  conv_lhs => rw [← himg]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hIoi (f := uctM) (f' := uctMderiv)
    (fun t ht => (hasDerivAt_uctM ht).hasDerivWithinAt) uctM_strictMonoOn.injOn g]
  refine integrableOn_congr_fun (fun t ht => ?_) hIoi
  simp only [smul_eq_mul, abs_of_pos (uctMderiv_pos ht)]

/-! ### Elementary bounds on `|H_0(it)|`, `m(t)`, `m'(t)` on `(0, ∞)` -/

lemma norm_stripH0_imag_le (kind : StripKernelChoice) {t : ℝ} (ht : 0 < t) :
    ‖stripH0 kind ((t : ℂ) * Complex.I)‖ ≤ (1 + π ^ 2 / 4) / t ^ 2 ∧
    (1 ≤ t → ‖stripH0 kind ((t : ℂ) * Complex.I)‖ ≤ 4 * π ^ 2 * Real.exp (-(π * t))) := by
  have hsh_ge : π * t / 2 ≤ Real.sinh (π * t / 2) := by
    have := Real.sinh_nonneg_iff.mpr (show 0 ≤ π * t / 2 by positivity)
    have h1 : ∀ x : ℝ, 0 ≤ x → x ≤ Real.sinh x := by
      intro x hx
      have hd : ∀ u : ℝ, HasDerivAt (fun s => Real.sinh s - s) (Real.cosh u - 1) u := fun u =>
        (Real.hasDerivAt_sinh u).sub (hasDerivAt_id u)
      have hmono : MonotoneOn (fun s => Real.sinh s - s) (Ici 0) :=
        monotoneOn_of_deriv_nonneg (convex_Ici 0)
          (Real.continuous_sinh.sub continuous_id).continuousOn
          (fun u _ => (hd u).differentiableAt.differentiableWithinAt)
          (fun u _ => by rw [(hd u).deriv]; linarith [Real.one_le_cosh u])
      have := hmono (le_rfl : (0 : ℝ) ∈ Ici 0) hx hx
      simp only [Real.sinh_zero, sub_self] at this; linarith
    exact h1 _ (by positivity)
  have hsh_term : π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2) ≤ 1 / t ^ 2 := by
    have hsq : (π * t / 2) ^ 2 ≤ Real.sinh (π * t / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsh_ge 2
    rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos ht)]
    nlinarith [Real.pi_pos]
  have hch_ge1 : (1 : ℝ) ≤ Real.cosh (π * t / 2) := Real.one_le_cosh _
  have hch_term : π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) ≤ π ^ 2 / 4 := by
    have hsq : (1 : ℝ) ≤ Real.cosh (π * t / 2) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hch_term_t2 : ∀ u : ℝ, 0 < u → π ^ 2 / (4 * Real.cosh (π * u / 2) ^ 2) ≤ (π ^ 2 / 4) / u ^ 2 := by
    intro u hu
    rcases le_or_gt u 1 with hu1 | hu1
    · have hu2 : u ^ 2 ≤ 1 := by nlinarith
      calc π ^ 2 / (4 * Real.cosh (π * u / 2) ^ 2) ≤ π ^ 2 / 4 := by
            have hsq : (1 : ℝ) ≤ Real.cosh (π * u / 2) ^ 2 := by nlinarith [Real.one_le_cosh (π * u / 2)]
            exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
        _ ≤ (π ^ 2 / 4) / u ^ 2 := by
            rw [le_div_iff₀ (sq_pos_of_pos hu)]; nlinarith [Real.pi_pos]
    · have hch_ge : π * u / 2 ≤ Real.cosh (π * u / 2) := by
        have hsq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ π * u / 2 by positivity)
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (-(π * u / 2)), sq_nonneg (π * u / 2 - 1)]
      have hsq : (π * u / 2) ^ 2 ≤ Real.cosh (π * u / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hch_ge 2
      have h1 : π ^ 2 / (4 * Real.cosh (π * u / 2) ^ 2) ≤ 1 / u ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hu)]; nlinarith [Real.pi_pos]
      have hpi2 : (1 : ℝ) ≤ π ^ 2 / 4 := by nlinarith [Real.pi_gt_three]
      calc π ^ 2 / (4 * Real.cosh (π * u / 2) ^ 2) ≤ 1 / u ^ 2 := h1
        _ ≤ (π ^ 2 / 4) / u ^ 2 := div_le_div_of_nonneg_right hpi2 (sq_nonneg u)
  constructor
  · cases kind
    · rw [norm_stripH0_star_imag ht]
      have := hch_term_t2 t ht
      linarith [show (1 + π ^ 2 / 4) / t ^ 2 = 1 / t ^ 2 + (π ^ 2 / 4) / t ^ 2 by ring]
    · rw [norm_stripH0_ce_imag ht]
      have : (0 : ℝ) ≤ (π ^ 2 / 4) / t ^ 2 := by positivity
      linarith [show (1 + π ^ 2 / 4) / t ^ 2 = 1 / t ^ 2 + (π ^ 2 / 4) / t ^ 2 by ring]
  · intro ht1
    -- For `t ≥ 1`, `π t / 2 ≥ π / 2 > 1`, so `e^{π t / 2} ≥ e > 2`, hence `sinh(π t / 2) ≥ (1/4) e^{π t / 2}`
    -- and `cosh(π t / 2) ≥ (1/2) e^{π t / 2}`!
    have hexp_ge2 : (2 : ℝ) ≤ Real.exp (π * t / 2) := by
      have : (1 : ℝ) ≤ π * t / 2 := by nlinarith [Real.pi_gt_three]
      linarith [Real.add_one_le_exp (π * t / 2)]
    have hsh_exp : (1 / 4 : ℝ) * Real.exp (π * t / 2) ≤ Real.sinh (π * t / 2) := by
      rw [Real.sinh_eq, Real.exp_neg]
      have hinv : (Real.exp (π * t / 2))⁻¹ ≤ (1 / 2 : ℝ) * Real.exp (π * t / 2) := by
        rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]; nlinarith
      linarith
    have hch_exp : (1 / 2 : ℝ) * Real.exp (π * t / 2) ≤ Real.cosh (π * t / 2) := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-(π * t / 2))]
    have hexp_sq : Real.exp (π * t / 2) ^ 2 = Real.exp (π * t) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hsh_bd : π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2) ≤ 4 * π ^ 2 * Real.exp (-(π * t)) := by
      have hsq : (1 / 16 : ℝ) * Real.exp (π * t) ≤ Real.sinh (π * t / 2) ^ 2 := by
        rw [← hexp_sq]; nlinarith [pow_le_pow_left₀ (by positivity) hsh_exp 2]
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (Real.exp_pos _)]
      nlinarith [Real.pi_pos]
    have hch_bd : π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) ≤ π ^ 2 * Real.exp (-(π * t)) := by
      have hsq : (1 / 4 : ℝ) * Real.exp (π * t) ≤ Real.cosh (π * t / 2) ^ 2 := by
        rw [← hexp_sq]; nlinarith [pow_le_pow_left₀ (by positivity) hch_exp 2]
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (Real.exp_pos _)]
      nlinarith [Real.pi_pos]
    cases kind
    · rw [norm_stripH0_star_imag ht]
      -- Wait: `4 + 1 = 5`, so let's bound `sinh` by `3`? Wait: `e^{π/2} > 1 + 1.5 + 1.125 = 3.625 > 3`, so `sinh ≥ (1/2)(1 - 1/9) e^x = (4/9) e^x`, giving `4 * (16/81) = 64/81` -> `81/64 < 2`!
      have hexp_ge3 : (3 : ℝ) ≤ Real.exp (π * t / 2) := by
        have hx : (3 / 2 : ℝ) ≤ π * t / 2 := by nlinarith [Real.pi_gt_three]
        have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ π * t / 2 by positivity)
        nlinarith
      have hsh_exp2 : (1 / 3 : ℝ) * Real.exp (π * t / 2) ≤ Real.sinh (π * t / 2) := by
        rw [Real.sinh_eq, Real.exp_neg]
        have hinv : (Real.exp (π * t / 2))⁻¹ ≤ (1 / 3 : ℝ) * Real.exp (π * t / 2) := by
          rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]; nlinarith
        linarith
      have hsh_bd2 : π ^ 2 / (4 * Real.sinh (π * t / 2) ^ 2) ≤ 3 * π ^ 2 * Real.exp (-(π * t)) := by
        have hsq : (1 / 9 : ℝ) * Real.exp (π * t) ≤ Real.sinh (π * t / 2) ^ 2 := by
          rw [← hexp_sq]; nlinarith [pow_le_pow_left₀ (by positivity) hsh_exp2 2]
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (Real.exp_pos _)]
        nlinarith [Real.pi_pos]
      linarith
    · rw [norm_stripH0_ce_imag ht]; exact hsh_bd

/-! ### Symmetric vertical contour shift `Re z = ε` to `Re z = 1 - ε` -/

lemma vertical_shift_strip_symm {F : ℂ → ℂ} {ε C : ℝ} (hε0 : 0 < ε) (hε12 : ε < 1 / 2)
    (hC : 0 ≤ C) (hdiff : DifferentiableOn ℂ F strip)
    (hbd : ∀ z : ℂ, ε ≤ z.re → z.re ≤ 1 - ε → ‖F z‖ ≤ C / (1 + z.im ^ 2)) :
    (∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ))) =
      ∫ t : ℝ, F (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
  have hle : ε ≤ 1 - ε := by linarith
  have hsub_strip : ∀ z : ℂ, ε ≤ z.re → z.re ≤ 1 - ε → z ∈ strip := fun z h1 h2 =>
    ⟨by linarith, by linarith⟩
  have hint_line : ∀ x : ℝ, ε ≤ x → x ≤ 1 - ε →
      Integrable (fun t : ℝ => F ((x : ℂ) + Complex.I * (t : ℂ))) := by
    intro x hx1 hx2
    have hcont : Continuous (fun t : ℝ => F ((x : ℂ) + Complex.I * (t : ℂ))) :=
      hdiff.continuousOn.comp_continuous (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
        fun t => hsub_strip _ (by simp [hx1]) (by simp [hx2])
    refine (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    have h := hbd ((x : ℂ) + Complex.I * (t : ℂ)) (by simp [hx1]) (by simp [hx2])
    simpa [div_eq_mul_inv] using h
  have hrect : ∀ L : ℝ, 0 < L →
      (∫ t in (-L)..L, F (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ))) -
      (∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ))) =
      Complex.I * ((∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ))) -
        ∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * (L : ℂ))) := by
    intro L hL
    have h0 := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
      ((ε : ℂ) + Complex.I * ((-L : ℝ) : ℂ)) (((1 - ε : ℝ) : ℂ) + Complex.I * (L : ℂ))
      (hdiff.mono fun z hz => by
        have hre : z.re ∈ uIcc ε (1 - ε) := by simpa using hz.1
        rw [uIcc_of_le hle] at hre
        exact hsub_strip z hre.1 hre.2)
    have hrew : ∀ (a b c d : ℂ), a - b + Complex.I * c - Complex.I * d = 0 →
        c - d = Complex.I * (a - b) := fun a b c d h => by
      have h1 : Complex.I * (c - d) = -(a - b) := by linear_combination h
      have h2 := congrArg (fun w => -Complex.I * w) h1
      simp only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul, mul_neg] at h2
      exact h2
    have h0' :
        (∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ))) -
        (∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * (L : ℂ))) +
        Complex.I * (∫ t in (-L)..L, F (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ))) -
        Complex.I * (∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ))) = 0 := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero,
        Complex.add_im, Complex.mul_im, one_mul, zero_add] at h0
      have e1 : (∫ x in ε..(1 - ε), F ((x : ℂ) + ((-L : ℝ) : ℂ) * Complex.I)) =
          ∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ)) :=
        intervalIntegral.integral_congr fun s _ => by congr 1; ring
      have e2 : (∫ x in ε..(1 - ε), F ((x : ℂ) + (L : ℂ) * Complex.I)) =
          ∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * (L : ℂ)) :=
        intervalIntegral.integral_congr fun s _ => by congr 1; ring
      have e3 : (∫ y in (-L)..L, F (((1 - ε : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
          ∫ y in (-L)..L, F (((1 - ε : ℝ) : ℂ) + Complex.I * (y : ℂ)) :=
        intervalIntegral.integral_congr fun s _ => by congr 1; ring
      have e4 : (∫ y in (-L)..L, F ((ε : ℂ) + (y : ℂ) * Complex.I)) =
          ∫ y in (-L)..L, F ((ε : ℂ) + Complex.I * (y : ℂ)) :=
        intervalIntegral.integral_congr fun s _ => by congr 1; ring
      rw [e1, e2, e3, e4] at h0
      exact h0
    exact hrew _ _ _ _ h0'
  have htend_lhs : Tendsto (fun L : ℝ =>
      (∫ t in (-L)..L, F (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ))) -
      (∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ)))) atTop
      (𝓝 ((∫ t : ℝ, F (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ))) -
        (∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ))))) := by
    have h1 := intervalIntegral_tendsto_integral (hint_line (1 - ε) hle le_rfl) tendsto_neg_atTop_atBot tendsto_id
    have h2 := intervalIntegral_tendsto_integral (hint_line ε le_rfl hle) tendsto_neg_atTop_atBot tendsto_id
    exact h1.sub h2
  have htend_rhs : Tendsto (fun L : ℝ =>
      (∫ t in (-L)..L, F (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ))) -
      (∫ t in (-L)..L, F ((ε : ℂ) + Complex.I * (t : ℂ)))) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (g := fun L : ℝ => 2 * C / (1 + L ^ 2)) (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [hrect L hL, norm_mul, Complex.norm_I, one_mul]
      have hseg : ∀ (s : ℝ), |s| = L →
          ‖∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * (s : ℂ))‖ ≤ C / (1 + L ^ 2) := by
        intro s hs
        calc ‖∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * (s : ℂ))‖
            ≤ ∫ x in ε..(1 - ε), ‖F ((x : ℂ) + Complex.I * (s : ℂ))‖ :=
              intervalIntegral.norm_integral_le_integral_norm hle
          _ ≤ ∫ x in ε..(1 - ε), C / (1 + L ^ 2) := by
              refine intervalIntegral.integral_mono_on hle ?_ intervalIntegrable_const fun x hx => ?_
              · have hcont_x : ContinuousOn (fun x : ℝ => ‖F ((x : ℂ) + Complex.I * (s : ℂ))‖) (Icc ε (1 - ε)) :=
                  (hdiff.continuousOn.comp
                    ((Complex.continuous_ofReal.add continuous_const).continuousOn)
                    (fun x hx => hsub_strip _ (by simp [hx.1]) (by simp [hx.2]))).norm
                exact hcont_x.intervalIntegrable_of_Icc hle
              · have := hbd ((x : ℂ) + Complex.I * (s : ℂ)) (by simp [hx.1]) (by simp [hx.2])
                simpa [← sq_abs s, hs] using this
          _ = ((1 - ε) - ε) * (C / (1 + L ^ 2)) := by rw [intervalIntegral.integral_const, smul_eq_mul]
          _ ≤ 1 * (C / (1 + L ^ 2)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = C / (1 + L ^ 2) := one_mul _
      calc ‖(∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ))) -
              ∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * (L : ℂ))‖
          ≤ ‖∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * ((-L : ℝ) : ℂ))‖ +
            ‖∫ x in ε..(1 - ε), F ((x : ℂ) + Complex.I * (L : ℂ))‖ := norm_sub_le _ _
        _ ≤ C / (1 + L ^ 2) + C / (1 + L ^ 2) := add_le_add (hseg (-L) (by rw [abs_neg, abs_of_pos hL])) (hseg L (abs_of_pos hL))
        _ = 2 * C / (1 + L ^ 2) := by ring
    · have h1 : Tendsto (fun L : ℝ => 1 + L ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (by norm_num))
      exact (tendsto_const_nhds (x := 2 * C)).div_atTop h1
  exact (sub_eq_zero.mp (tendsto_nhds_unique htend_lhs htend_rhs)).symm

/-! ### Quadratic vanishing of `g_D(ζ)` at `0` and `1` and contour identity for `H_0(ζ)(D(ζ) - 1)` -/

lemma stripCompGExt_one_sub {w : ℝ → ℝ} (hw_even : ∀ t, w (-t) = w t) {z : ℂ} (hz : z ∈ closedStrip) :
    stripCompGExt w (1 - z) = stripCompGExt w z := by
  by_cases hz_in : z ∈ strip
  · have h1z : 1 - z ∈ strip := ⟨by simp; linarith [hz_in.2], by simp; linarith [hz_in.1]⟩
    rw [stripCompGExt_eq_of_mem_strip h1z, stripCompGExt_eq_of_mem_strip hz_in, stripCompG_one_sub hw_even]
  · unfold stripCompGExt
    rcases le_or_gt z.re 0 with h0 | h0
    · have hre0 : z.re = 0 := le_antisymm h0 hz.1
      have h1re : (1 - z).re = 1 := by simp [hre0]
      have h1im : (1 - z).im = -z.im := by simp
      simp only [hre0, le_refl, ↓reduceIte, h1re, show ¬((1 : ℝ) ≤ 0) by norm_num, h1im,
        hw_even, fctThetaD_odd hw_even, Complex.ofReal_neg, mul_neg, sub_neg_eq_add]
    · have hre1 : z.re = 1 := le_antisymm hz.2 (not_lt.mp fun h => hz_in ⟨h0, h⟩)
      have h1re : (1 - z).re = 0 := by simp [hre1]
      have h1im : (1 - z).im = -z.im := by simp
      simp only [hre1, show ¬((1 : ℝ) ≤ 0) by norm_num, le_refl, ↓reduceIte, h1re, h1im,
        hw_even, fctThetaD_odd hw_even, Complex.ofReal_neg, mul_neg, ← sub_eq_add_neg]

/-- If `v` is even, `C_c^∞`, `v(0) = 0`, `ϑ_D'(0) = 0`, and `‖g_D''‖ ≤ M₂` on `closedStrip`,
then `‖stripCompGExt v z‖ ≤ (M₂ / 2) * ‖z‖²` and `‖stripCompGExt v z‖ ≤ (M₂ / 2) * ‖1 - z‖²` on `closedStrip`. -/
lemma stripCompGExt_quad_bound {v : ℝ → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hv_supp : HasCompactSupport v) (hv_even : ∀ t, v (-t) = v t)
    (hv0 : v 0 = 0) (hθ1 : deriv (fctThetaD v) 0 = 0)
    {M₂ : ℝ} (_hM₂_nn : 0 ≤ M₂)
    (hM₂ : ∀ z ∈ closedStrip, ‖(-Complex.I) ^ 2 * stripCompGExt (iteratedDeriv 2 v) z‖ ≤ M₂) :
    ∀ z ∈ closedStrip,
      ‖stripCompGExt v z‖ ≤ (M₂ / 2) * ‖z‖ ^ 2 ∧
      ‖stripCompGExt v z‖ ≤ (M₂ / 2) * ‖1 - z‖ ^ 2 := by
  have hv1 : deriv v 0 = 0 := by
    have h := iteratedDeriv_odd_zero hv_even 0
    simpa [iteratedDeriv_one] using h
  have hθ0 : fctThetaD v 0 = 0 := by
    have h := fctThetaD_odd hv_even 0; simp only [neg_zero] at h; linarith
  have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (deriv v) := by
    rw [show deriv v = iteratedDeriv 1 v by ext x; exact (congrFun (iteratedDeriv_one (f := v)) x).symm]
    exact contDiff_iteratedDeriv_infty hv 1
  have hv1_cs : HasCompactSupport (deriv v) := by
    rw [show deriv v = iteratedDeriv 1 v by ext x; exact (congrFun (iteratedDeriv_one (f := v)) x).symm]
    exact hasCompactSupport_iteratedDeriv hv_supp 1
  have hv2_cd : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 v) := contDiff_iteratedDeriv_infty hv 2
  have hv2_cs : HasCompactSupport (iteratedDeriv 2 v) := hasCompactSupport_iteratedDeriv hv_supp 2
  have hstrip_zero : ∀ z ∈ strip, ‖stripCompGExt v z‖ ≤ (M₂ / 2) * ‖z‖ ^ 2 := by
    intro z hz
    let φ : ℝ → ℂ := fun s => stripCompGExt v ((s : ℂ) * z)
    let φ1 : ℝ → ℂ := fun s => z * ((-Complex.I) * stripCompGExt (deriv v) ((s : ℂ) * z))
    let φ2 : ℝ → ℂ := fun s => z ^ 2 * ((-Complex.I) ^ 2 * stripCompGExt (iteratedDeriv 2 v) ((s : ℂ) * z))
    have hmem_cl : ∀ s ∈ Icc (0 : ℝ) 1, ((s : ℂ) * z) ∈ closedStrip := fun s hs => by
      simp only [closedStrip, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact ⟨mul_nonneg hs.1 hz.1.le, (mul_le_of_le_one_left hz.1.le hs.2).trans hz.2.le⟩
    have hmem_op : ∀ s ∈ Ioo (0 : ℝ) 1, ((s : ℂ) * z) ∈ strip := fun s hs => by
      simp only [strip, mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact ⟨mul_pos hs.1 hz.1, by nlinarith [hs.1, hs.2, hz.1, hz.2]⟩
    have hφ_cont : ContinuousOn φ (Icc 0 1) :=
      (continuousOn_stripCompGExt hv hv_supp).comp (Complex.continuous_ofReal.mul continuous_const).continuousOn hmem_cl
    have hφ1_cont : ContinuousOn φ1 (Icc 0 1) :=
      continuousOn_const.mul (continuousOn_const.mul
        ((continuousOn_stripCompGExt hv1_cd hv1_cs).comp
          (Complex.continuous_ofReal.mul continuous_const).continuousOn hmem_cl))
    have hφ2_cont : ContinuousOn φ2 (Icc 0 1) :=
      continuousOn_const.mul (continuousOn_const.mul
        ((continuousOn_stripCompGExt hv2_cd hv2_cs).comp
          (Complex.continuous_ofReal.mul continuous_const).continuousOn hmem_cl))
    have hφ_d : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (φ1 s) s := by
      intro s hs
      have hsz := hmem_op s hs
      have hd_g : HasDerivAt (stripCompG v) ((-Complex.I) * stripCompG (deriv v) ((s : ℂ) * z)) ((s : ℂ) * z) := by
        rw [← deriv_stripCompG hv hv_supp hsz]
        exact (differentiableOn_stripCompG hv.continuous hv_supp _ hsz).differentiableAt
          (isOpen_strip.mem_nhds hsz) |>.hasDerivAt
      have hline : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z s := by
        simpa using Complex.ofRealCLM.hasDerivAt.mul_const z
      have hcomp := (hd_g.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hline
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hcomp
      have hev : φ =ᶠ[𝓝 s] fun u : ℝ => stripCompG v ((u : ℂ) * z) := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
        exact stripCompGExt_eq_of_mem_strip (hmem_op u hu)
      refine (hcomp.congr_of_eventuallyEq hev).congr_deriv ?_
      dsimp only [φ1]; rw [stripCompGExt_eq_of_mem_strip hsz]
    have hφ1_d : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt φ1 (φ2 s) s := by
      intro s hs
      have hsz := hmem_op s hs
      have hd_g : HasDerivAt (stripCompG (deriv v)) ((-Complex.I) * stripCompG (deriv (deriv v)) ((s : ℂ) * z)) ((s : ℂ) * z) := by
        rw [← deriv_stripCompG hv1_cd hv1_cs hsz]
        exact (differentiableOn_stripCompG hv1_cd.continuous hv1_cs _ hsz).differentiableAt
          (isOpen_strip.mem_nhds hsz) |>.hasDerivAt
      have hline : HasDerivAt (fun u : ℝ => (u : ℂ) * z) z s := by
        simpa using Complex.ofRealCLM.hasDerivAt.mul_const z
      have hcomp := (hd_g.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hline
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hcomp
      have hev : φ1 =ᶠ[𝓝 s] fun u : ℝ => z * ((-Complex.I) * stripCompG (deriv v) ((u : ℂ) * z)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
        dsimp only [φ1]; rw [stripCompGExt_eq_of_mem_strip (hmem_op u hu)]
      have hmul := (hcomp.const_mul (-Complex.I)).const_mul z
      refine (hmul.congr_of_eventuallyEq hev).congr_deriv ?_
      dsimp only [φ2]
      rw [stripCompGExt_eq_of_mem_strip hsz, show deriv (deriv v) = iteratedDeriv 2 v by
        ext x; rw [iteratedDeriv_succ, iteratedDeriv_one]]
      ring
    have hφ0 : φ 0 = 0 := by
      dsimp only [φ]; rw [Complex.ofReal_zero, zero_mul]
      have h := stripCompGExt_left v 0
      simpa [hv0, hθ0] using h
    have hφ10 : φ1 0 = 0 := by
      dsimp only [φ1]; rw [Complex.ofReal_zero, zero_mul]
      have h := stripCompGExt_left (deriv v) 0
      have hθd : fctThetaD (deriv v) 0 = 0 := by
        have h1 := iteratedDeriv_fctThetaD hv hv_supp 1
        have h2 := congrFun h1 0
        rw [iteratedDeriv_one, iteratedDeriv_one] at h2
        rw [← h2]; exact hθ1
      simp only [Complex.ofReal_zero, zero_mul] at h
      rw [h, hv1, hθd]; simp
    have hφ1_bd : ∀ s ∈ Icc (0 : ℝ) 1, ‖φ1 s‖ ≤ M₂ * ‖z‖ ^ 2 * s := by
      intro s hs
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
        (hφ1_cont.mono (Icc_subset_Icc_right hs.2))
        (fun u hu => hφ1_d u ⟨hu.1, hu.2.trans_le hs.2⟩)
        ((hφ2_cont.mono (Icc_subset_Icc_right hs.2)).intervalIntegrable_of_Icc hs.1)
      rw [hφ10, sub_zero] at hftc
      rw [← hftc]
      calc ‖∫ u in (0 : ℝ)..s, φ2 u‖ ≤ ∫ u in (0 : ℝ)..s, ‖φ2 u‖ :=
            intervalIntegral.norm_integral_le_integral_norm hs.1
        _ ≤ ∫ u in (0 : ℝ)..s, M₂ * ‖z‖ ^ 2 := by
            refine intervalIntegral.integral_mono_on hs.1
              ((hφ2_cont.mono (Icc_subset_Icc_right hs.2)).norm.intervalIntegrable_of_Icc hs.1)
              intervalIntegrable_const fun u hu => ?_
            dsimp only [φ2]; rw [norm_mul, norm_pow]
            calc ‖z‖ ^ 2 * ‖(-Complex.I) ^ 2 * stripCompGExt (iteratedDeriv 2 v) ((u : ℂ) * z)‖
                ≤ ‖z‖ ^ 2 * M₂ := mul_le_mul_of_nonneg_left (hM₂ _ (hmem_cl u ⟨hu.1, hu.2.trans hs.2⟩)) (sq_nonneg _)
              _ = M₂ * ‖z‖ ^ 2 := mul_comm _ _
        _ = M₂ * ‖z‖ ^ 2 * s := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring
    have hftc0 := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hφ_cont
      hφ_d (hφ1_cont.intervalIntegrable_of_Icc zero_le_one)
    rw [hφ0, sub_zero] at hftc0
    have hφ1_eq : φ 1 = stripCompGExt v z := by dsimp only [φ]; simp
    rw [← hφ1_eq, ← hftc0]
    calc ‖∫ s in (0 : ℝ)..1, φ1 s‖ ≤ ∫ s in (0 : ℝ)..1, ‖φ1 s‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ s in (0 : ℝ)..1, M₂ * ‖z‖ ^ 2 * s :=
          intervalIntegral.integral_mono_on zero_le_one
            (hφ1_cont.norm.intervalIntegrable_of_Icc zero_le_one)
            ((continuous_const.mul continuous_id).intervalIntegrable _ _) hφ1_bd
      _ = (M₂ / 2) * ‖z‖ ^ 2 := by
          rw [intervalIntegral.integral_const_mul, integral_id]; norm_num; ring
  have hcl_zero : ∀ z ∈ closedStrip, ‖stripCompGExt v z‖ ≤ (M₂ / 2) * ‖z‖ ^ 2 := by
    intro z hz
    -- Approach `z` from `strip` via `z_n = (1 - 1/(n+2)) * z + (1/(n+2)) * (1/2 + I * z.im)`!
    let seq : ℕ → ℂ := fun n =>
      (((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ) * z) + ((1 / ((n : ℝ) + 2) : ℝ) : ℂ) * ((1 / 2 : ℂ) + Complex.I * (z.im : ℂ))
    have hseq_in : ∀ n, seq n ∈ strip := fun n => by
      have hε0 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      have hε1 : (1 / ((n : ℝ) + 2) : ℝ) < 1 := by
        rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hre : (seq n).re = (1 - 1 / ((n : ℝ) + 2)) * z.re + (1 / ((n : ℝ) + 2)) * (1 / 2) := by
        dsimp only [seq]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.div_ofNat_re, Complex.one_re, Complex.I_re, Complex.I_im, mul_zero, sub_self, add_zero]
      exact ⟨by rw [hre]; nlinarith [hz.1], by rw [hre]; nlinarith [hz.2]⟩
    have hseq_tend : Tendsto seq atTop (𝓝[closedStrip] z) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n =>
        ⟨(hseq_in n).1.le, (hseq_in n).2.le⟩⟩
      have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 2) : ℝ)) atTop (𝓝 0) := by
        have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
        refine h1.congr fun n => ?_
        dsimp only [Function.comp_apply]; push_cast; ring_nf
      have h1 : Tendsto (fun n : ℕ => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
        have h1r : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 : ℝ)) := by
          simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 1).comp h1r
      have h2 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
        simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h0
      simpa [seq] using (h1.mul tendsto_const_nhds).add (h2.mul tendsto_const_nhds)
    have hcont_l : Tendsto (fun n => ‖stripCompGExt v (seq n)‖) atTop (𝓝 ‖stripCompGExt v z‖) :=
      ((continuousOn_stripCompGExt hv hv_supp z hz).norm.tendsto).comp hseq_tend
    have hcont_r : Tendsto (fun n => (M₂ / 2) * ‖seq n‖ ^ 2) atTop (𝓝 ((M₂ / 2) * ‖z‖ ^ 2)) :=
      (((continuous_norm.pow 2).const_mul (M₂ / 2)).tendsto z).comp (tendsto_nhdsWithin_iff.mp hseq_tend).1
    exact le_of_tendsto_of_tendsto hcont_l hcont_r (Filter.Eventually.of_forall fun n => hstrip_zero _ (hseq_in n))
  intro z hz
  refine ⟨hcl_zero z hz, ?_⟩
  have h1z : 1 - z ∈ closedStrip := ⟨by simp; linarith [hz.2], by simp; linarith [hz.1]⟩
  rw [← stripCompGExt_one_sub hv_even hz]
  exact hcl_zero (1 - z) h1z

/-- Elementary bound `‖exp w - 1‖ ≤ exp M * ‖w‖` for `‖w‖ ≤ M`. -/
lemma norm_cexp_sub_one_le {w : ℂ} {M : ℝ} (hw : ‖w‖ ≤ M) :
    ‖Complex.exp w - 1‖ ≤ Real.exp M * ‖w‖ := by
  have hftc : Complex.exp w - 1 = ∫ s in (0 : ℝ)..1, w * Complex.exp ((s : ℂ) * w) := by
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => Complex.exp ((u : ℂ) * w)) (w * Complex.exp ((s : ℂ) * w)) s := by
      intro s _
      have hline : HasDerivAt (fun u : ℝ => (u : ℂ) * w) w s := by
        simpa using Complex.ofRealCLM.hasDerivAt.mul_const w
      have hcomp := (Complex.hasDerivAt_exp ((s : ℂ) * w)).hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt s hline
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hcomp
      exact hcomp
    have hcont : Continuous (fun s : ℝ => w * Complex.exp ((s : ℂ) * w)) :=
      continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)
    simpa using h.symm
  rw [hftc]
  calc ‖∫ s in (0 : ℝ)..1, w * Complex.exp ((s : ℂ) * w)‖
      ≤ ∫ s in (0 : ℝ)..1, ‖w * Complex.exp ((s : ℂ) * w)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ s in (0 : ℝ)..1, Real.exp M * ‖w‖ := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))).norm.intervalIntegrable _ _)
          intervalIntegrable_const fun s hs => ?_
        rw [norm_mul, Complex.norm_exp]
        have hre : ((s : ℂ) * w).re ≤ M := by
          calc ((s : ℂ) * w).re ≤ ‖(s : ℂ) * w‖ := Complex.re_le_norm _
            _ = s * ‖w‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
            _ ≤ 1 * M := mul_le_mul hs.2 hw (norm_nonneg _) zero_le_one
            _ = M := one_mul _
        calc ‖w‖ * Real.exp ((s : ℂ) * w).re ≤ ‖w‖ * Real.exp M :=
              mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (norm_nonneg _)
          _ = Real.exp M * ‖w‖ := mul_comm _ _
    _ = Real.exp M * ‖w‖ := by simp

/-! ### Contour identity for `H_0(ζ) (exp(g_D(ζ)) - 1)` around `∂S` -/

/-- Uniform bound on `‖H_0(z)‖` on `closedStrip` away from its poles (`0`, and `1` for `H_*`):
- `‖H_CE(z)‖ ≤ C_H / (‖z‖² * e^{π|Im z| / 2})`? Even simpler:
  for `z ∈ closedStrip`, `‖sin(π z / 2)‖ ≥ c_0 * min 1 ‖z‖ * e^{π |Im z| / 2}` (and for `H_*`,
  `‖H_*(z)‖ ≤ ‖H_CE(z)‖ + ‖H_CE(1 - z)‖`!).
Let's prove the elementary lower bound on `‖sin(π z / 2)‖` for `z ∈ closedStrip`! -/
lemma norm_sin_pi_div_two_ge {z : ℂ} (hz : z ∈ closedStrip) :
    (1 / 2 : ℝ) * min 1 ‖z‖ ≤ ‖Complex.sin (π * z / 2)‖ ∧
    (1 ≤ |z.im| → (1 / 4 : ℝ) * Real.exp (π * |z.im| / 2) ≤ ‖Complex.sin (π * z / 2)‖) := by
  have hnorm_sq : ‖Complex.sin (π * z / 2)‖ ^ 2 = Real.sin (π * z.re / 2) ^ 2 + Real.sinh (π * z.im / 2) ^ 2 := by
    have hz_eq : (π : ℂ) * z / 2 = ((π * z.re / 2 : ℝ) : ℂ) + ((π * z.im / 2 : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hz_eq, Complex.sin_add_mul_I, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      mul_one, sub_zero, add_zero, zero_add]
    have hch := Real.cosh_sq (π * z.im / 2)
    have hsc := Real.sin_sq_add_cos_sq (π * z.re / 2)
    nlinarith
  constructor
  · -- `sin(π x / 2) ≥ x` for `x ∈ [0, 1]` (concavity of `sin` on `[0, π/2]`) and `|sinh(π y / 2)| ≥ π |y| / 2 ≥ |y|`
    have hsin_ge : z.re ≤ Real.sin (π * z.re / 2) := by
      have h1 := Real.mul_le_sin (show 0 ≤ π * z.re / 2 by nlinarith [Real.pi_pos, hz.1])
        (show π * z.re / 2 ≤ π / 2 by nlinarith [Real.pi_pos, hz.2])
      have : (2 / π) * (π * z.re / 2) = z.re := by field_simp [Real.pi_ne_zero]
      linarith
    have hsinh_ge : |z.im| ≤ |Real.sinh (π * z.im / 2)| := by
      have hge : ∀ u : ℝ, 0 ≤ u → u ≤ Real.sinh u := fun u hu => by
        have hd : ∀ s : ℝ, HasDerivAt (fun x => Real.sinh x - x) (Real.cosh s - 1) s := fun s =>
          (Real.hasDerivAt_sinh s).sub (hasDerivAt_id s)
        have hm := monotoneOn_of_deriv_nonneg (f := fun x => Real.sinh x - x) (convex_Ici 0)
          (Real.continuous_sinh.sub continuous_id).continuousOn
          (fun s _ => (hd s).differentiableAt.differentiableWithinAt)
          (fun s _ => by rw [(hd s).deriv]; linarith [Real.one_le_cosh s])
        have := hm (le_rfl : (0 : ℝ) ∈ Ici 0) hu hu; simp only [Real.sinh_zero, sub_self] at this; linarith
      have habs : |Real.sinh (π * z.im / 2)| = Real.sinh (π * |z.im| / 2) := by
        rcases le_or_gt 0 z.im with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
        · rw [abs_of_neg h, show π * -z.im / 2 = -(π * z.im / 2) by ring, Real.sinh_neg,
            abs_of_neg (Real.sinh_neg_iff.mpr (by nlinarith [Real.pi_pos]))]
      rw [habs]
      calc |z.im| ≤ π * |z.im| / 2 := by nlinarith [Real.pi_gt_three, abs_nonneg z.im]
        _ ≤ Real.sinh (π * |z.im| / 2) := hge _ (by positivity)
    have hsq_le : ((1 / 2 : ℝ) * ‖z‖) ^ 2 ≤ ‖Complex.sin (π * z / 2)‖ ^ 2 := by
      have hnz : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_nonneg hz.1] at hnz
      have h1 : ‖z‖ ^ 2 ≤ 2 * (z.re ^ 2 + |z.im| ^ 2) := by
        nlinarith [sq_nonneg (z.re - |z.im|), hnz, norm_nonneg z]
      have h2 : z.re ^ 2 ≤ Real.sin (π * z.re / 2) ^ 2 := pow_le_pow_left₀ hz.1 hsin_ge 2
      have h3 : |z.im| ^ 2 ≤ Real.sinh (π * z.im / 2) ^ 2 := by
        rw [← sq_abs (Real.sinh _)]; exact pow_le_pow_left₀ (abs_nonneg _) hsinh_ge 2
      rw [hnorm_sq]; nlinarith
    have hmin_le : (1 / 2 : ℝ) * min 1 ‖z‖ ≤ (1 / 2 : ℝ) * ‖z‖ :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
    have hle_norm : (1 / 2 : ℝ) * ‖z‖ ≤ ‖Complex.sin (π * z / 2)‖ := by
      nlinarith [norm_nonneg (Complex.sin (π * z / 2)), norm_nonneg z]
    exact hmin_le.trans hle_norm
  · intro him1
    have hexp2 : (2 : ℝ) ≤ Real.exp (π * |z.im| / 2) := by
      have : (1 : ℝ) ≤ π * |z.im| / 2 := by nlinarith [Real.pi_gt_three]
      linarith [Real.add_one_le_exp (π * |z.im| / 2)]
    have hsh : (1 / 4 : ℝ) * Real.exp (π * |z.im| / 2) ≤ |Real.sinh (π * z.im / 2)| := by
      have habs : |Real.sinh (π * z.im / 2)| = Real.sinh (π * |z.im| / 2) := by
        rcases le_or_gt 0 z.im with h | h
        · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
        · rw [abs_of_neg h, show π * -z.im / 2 = -(π * z.im / 2) by ring, Real.sinh_neg,
            abs_of_neg (Real.sinh_neg_iff.mpr (by nlinarith [Real.pi_pos]))]
      rw [habs, Real.sinh_eq, Real.exp_neg]
      have hinv : (Real.exp (π * |z.im| / 2))⁻¹ ≤ (1 / 2 : ℝ) * Real.exp (π * |z.im| / 2) := by
        rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]; nlinarith
      linarith
    have hsq : ((1 / 4 : ℝ) * Real.exp (π * |z.im| / 2)) ^ 2 ≤ ‖Complex.sin (π * z / 2)‖ ^ 2 := by
      rw [hnorm_sq]
      have h1 : ((1 / 4 : ℝ) * Real.exp (π * |z.im| / 2)) ^ 2 ≤ |Real.sinh (π * z.im / 2)| ^ 2 :=
        pow_le_pow_left₀ (by positivity) hsh 2
      rw [sq_abs] at h1
      nlinarith [sq_nonneg (Real.sin (π * z.re / 2))]
    nlinarith [norm_nonneg (Complex.sin (π * z / 2)), Real.exp_pos (π * |z.im| / 2)]

set_option maxHeartbeats 400000 in
/-- Contour identity around `∂S` for `H_0(ζ) (exp(g_D(ζ)) - 1)`:
- for `H_*`: `∫_0^∞ |H_*(it)| (e^{v(t)} cos ϑ_D(t) - 1) dt = 0`;
- for `H_CE`: `∫_0^∞ |H_CE(it)| (e^{v(t)} cos ϑ_D(t) - 1) dt = -∫_0^∞ (π²/(4 cosh²(πt/2))) (e^{v(t)} cos ϑ_D(t) - 1) dt`. -/
lemma contour_H0_exp_sub_one (kind : StripKernelChoice) {v : ℝ → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hv_supp : HasCompactSupport v) (hv_even : ∀ t, v (-t) = v t)
    (hv0 : v 0 = 0) (hθ1 : deriv (fctThetaD v) 0 = 0)
    {M₀ M₂ : ℝ} (_hM₀_nn : 0 ≤ M₀) (hM₂_nn : 0 ≤ M₂)
    (hM₀ : ∀ z ∈ closedStrip, ‖stripCompGExt v z‖ ≤ M₀)
    (hM₂ : ∀ z ∈ closedStrip, ‖(-Complex.I) ^ 2 * stripCompGExt (iteratedDeriv 2 v) z‖ ≤ M₂) :
    IntegrableOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
      (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) (Ioi 0) ∧
    match kind with
    | .star =>
      (∫ t in Ioi (0 : ℝ), ‖stripH0 .star ((t : ℂ) * Complex.I)‖ *
        (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) = 0
    | .ce =>
      IntegrableOn (fun t : ℝ => (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) *
        (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), ‖stripH0 .ce ((t : ℂ) * Complex.I)‖ *
        (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) =
      -(∫ t in Ioi (0 : ℝ), (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) *
        (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) := by
  let F : ℂ → ℂ := fun z => stripH0 kind z * (Complex.exp (stripCompGExt v z) - 1)
  have hquad := stripCompGExt_quad_bound hv hv_supp hv_even hv0 hθ1 hM₂_nn hM₂
  -- Uniform bound `‖F z‖ ≤ C_F / (1 + z.im ^ 2)` on `closedStrip \ {0, 1}`!
  set C_small : ℝ := 4 * π ^ 2 * Real.exp M₀ * M₂
  set C_large : ℝ := 16 * π ^ 2 * (Real.exp M₀ + 1)
  -- Wait: for `|z.im| ≥ 1`, `e^{-π |z.im|} ≤ 2 / (1 + z.im^2)` (since `e^{π u} ≥ 1 + (π u)^2/2 ≥ (1 + u^2)/2`).
  have hexp_inv_sq : ∀ u : ℝ, Real.exp (-(π * |u|)) ≤ 2 / (1 + u ^ 2) := by
    intro u
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ π * |u| by positivity)
    have hpi : (1 : ℝ) ≤ π ^ 2 / 2 := by nlinarith [Real.pi_gt_three]
    have hsq : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [sq_nonneg u, Real.pi_pos, abs_nonneg u]
  set C_F : ℝ := max (2 * C_small) (2 * C_large)
  have hCF_nn : 0 ≤ C_F := le_trans (by positivity) (le_max_left _ _)
  have hF_bd : ∀ z ∈ closedStrip, z ≠ 0 → z ≠ 1 → ‖F z‖ ≤ C_F / (1 + z.im ^ 2) := by
    intro z hz hz0 hz1
    have hH_le : ‖stripH0 kind z‖ ≤ ‖uctHCE z‖ + ‖uctHCE (1 - z)‖ := by
      cases kind
      · dsimp only [stripH0]
        have hnotint : ∀ n : ℤ, z ≠ n := fun n h => by
          have hre := congrArg Complex.re h; simp at hre
          have h0 : (0 : ℝ) ≤ (n : ℝ) := by linarith [hz.1]
          have h1 : (n : ℝ) ≤ 1 := by linarith [hz.2]
          have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast h0
          have hn1 : n ≤ (1 : ℤ) := by exact_mod_cast h1
          have : n = 0 ∨ n = 1 := by omega
          rcases this with rfl | rfl
          · exact hz0 (by simpa using h)
          · exact hz1 (by simpa using h)
        rw [uct_H_split hnotint]; exact norm_sub_le _ _
      · dsimp only [stripH0]; linarith [norm_nonneg (uctHCE (1 - z))]
    have h1z : 1 - z ∈ closedStrip := ⟨by simp; linarith [hz.2], by simp; linarith [hz.1]⟩
    have h1z_im : |(1 - z).im| = |z.im| := by simp
    rcases le_or_gt |z.im| 1 with him1 | him1
    · -- `|z.im| ≤ 1`, so `1 + z.im^2 ≤ 2`
      have hHCE_z : ‖uctHCE z‖ * ‖Complex.exp (stripCompGExt v z) - 1‖ ≤ (1 / 2) * C_small := by
        have hs := (norm_sin_pi_div_two_ge hz).1
        have hmin2 : ‖z‖ / 2 ≤ min 1 ‖z‖ := by
          have hnz : ‖z‖ ≤ 2 := by
            have := Complex.norm_le_abs_re_add_abs_im z
            rw [abs_of_nonneg hz.1] at this; linarith [hz.2]
          exact le_min (by linarith) (by linarith [norm_nonneg z])
        have hsin_ge2 : (1 / 4 : ℝ) * ‖z‖ ≤ ‖Complex.sin (π * z / 2)‖ := by linarith
        have hsin_pos : 0 < ‖Complex.sin (π * z / 2)‖ := lt_of_lt_of_le (by positivity) hsin_ge2
        have hH_bd2 : ‖uctHCE z‖ ≤ 4 * π ^ 2 / ‖z‖ ^ 2 := by
          unfold uctHCE; rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, show ‖(4 : ℂ)‖ = 4 by simp]
          have hsq : (1 / 16 : ℝ) * ‖z‖ ^ 2 ≤ ‖Complex.sin (π * z / 2)‖ ^ 2 := by
            nlinarith [pow_le_pow_left₀ (by positivity) hsin_ge2 2]
          rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos (norm_pos_iff.mpr hz0))]
          nlinarith [Real.pi_pos]
        have hexp_bd : ‖Complex.exp (stripCompGExt v z) - 1‖ ≤ Real.exp M₀ * ((M₂ / 2) * ‖z‖ ^ 2) :=
          (norm_cexp_sub_one_le (hM₀ z hz)).trans (mul_le_mul_of_nonneg_left (hquad z hz).1 (Real.exp_pos _).le)
        calc ‖uctHCE z‖ * ‖Complex.exp (stripCompGExt v z) - 1‖
            ≤ (4 * π ^ 2 / ‖z‖ ^ 2) * (Real.exp M₀ * ((M₂ / 2) * ‖z‖ ^ 2)) :=
              mul_le_mul hH_bd2 hexp_bd (norm_nonneg _) (by positivity)
          _ = (1 / 2) * C_small := by dsimp only [C_small]; field_simp [(norm_pos_iff.mpr hz0).ne']
      have hHCE_1z : ‖uctHCE (1 - z)‖ * ‖Complex.exp (stripCompGExt v z) - 1‖ ≤ (1 / 2) * C_small := by
        have h1z_ne : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
        have hs := (norm_sin_pi_div_two_ge h1z).1
        have hmin2 : ‖1 - z‖ / 2 ≤ min 1 ‖1 - z‖ := by
          have hnz : ‖1 - z‖ ≤ 2 := by
            have := Complex.norm_le_abs_re_add_abs_im (1 - z)
            rw [abs_of_nonneg h1z.1, h1z_im] at this; linarith [h1z.2]
          exact le_min (by linarith) (by linarith [norm_nonneg (1 - z)])
        have hsin_ge2 : (1 / 4 : ℝ) * ‖1 - z‖ ≤ ‖Complex.sin (π * (1 - z) / 2)‖ := by linarith
        have hsin_pos : 0 < ‖Complex.sin (π * (1 - z) / 2)‖ := lt_of_lt_of_le (by positivity) hsin_ge2
        have hH_bd2 : ‖uctHCE (1 - z)‖ ≤ 4 * π ^ 2 / ‖1 - z‖ ^ 2 := by
          unfold uctHCE; rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos, show ‖(4 : ℂ)‖ = 4 by simp]
          have hsq : (1 / 16 : ℝ) * ‖1 - z‖ ^ 2 ≤ ‖Complex.sin (π * (1 - z) / 2)‖ ^ 2 := by
            nlinarith [pow_le_pow_left₀ (by positivity) hsin_ge2 2]
          rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos (norm_pos_iff.mpr h1z_ne))]
          nlinarith [Real.pi_pos]
        have hexp_bd : ‖Complex.exp (stripCompGExt v z) - 1‖ ≤ Real.exp M₀ * ((M₂ / 2) * ‖1 - z‖ ^ 2) :=
          (norm_cexp_sub_one_le (hM₀ z hz)).trans (mul_le_mul_of_nonneg_left (hquad z hz).2 (Real.exp_pos _).le)
        calc ‖uctHCE (1 - z)‖ * ‖Complex.exp (stripCompGExt v z) - 1‖
            ≤ (4 * π ^ 2 / ‖1 - z‖ ^ 2) * (Real.exp M₀ * ((M₂ / 2) * ‖1 - z‖ ^ 2)) :=
              mul_le_mul hH_bd2 hexp_bd (norm_nonneg _) (by positivity)
          _ = (1 / 2) * C_small := by dsimp only [C_small]; field_simp [(norm_pos_iff.mpr h1z_ne).ne']
      have h1im2 : 1 + z.im ^ 2 ≤ 2 := by nlinarith [sq_abs z.im, him1, abs_nonneg z.im]
      dsimp only [F]; rw [norm_mul]
      calc ‖stripH0 kind z‖ * ‖Complex.exp (stripCompGExt v z) - 1‖
          ≤ (‖uctHCE z‖ + ‖uctHCE (1 - z)‖) * ‖Complex.exp (stripCompGExt v z) - 1‖ :=
            mul_le_mul_of_nonneg_right hH_le (norm_nonneg _)
        _ = ‖uctHCE z‖ * ‖Complex.exp (stripCompGExt v z) - 1‖ +
            ‖uctHCE (1 - z)‖ * ‖Complex.exp (stripCompGExt v z) - 1‖ := add_mul _ _ _
        _ ≤ C_small := by linarith
        _ ≤ (2 * C_small) / (1 + z.im ^ 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith [show 0 ≤ C_small by positivity]
        _ ≤ C_F / (1 + z.im ^ 2) := div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    · -- `1 < |z.im|`: `‖H_CE(z)‖, ‖H_CE(1-z)‖ ≤ 4 π^2 e^{-π |z.im|}` and `‖exp g_D - 1‖ ≤ e^{M₀} + 1`!
      have hHCE_exp : ∀ w ∈ closedStrip, 1 ≤ |w.im| → ‖uctHCE w‖ ≤ 4 * π ^ 2 * Real.exp (-(π * |w.im|)) := by
        intro w hw hw1
        have hs := (norm_sin_pi_div_two_ge hw).2 hw1
        have hsin_pos : 0 < ‖Complex.sin (π * w / 2)‖ := lt_of_lt_of_le (by positivity) hs
        have hexp_sq : Real.exp (π * |w.im| / 2) ^ 2 = Real.exp (π * |w.im|) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have hsq : (1 / 16 : ℝ) * Real.exp (π * |w.im|) ≤ ‖Complex.sin (π * w / 2)‖ ^ 2 := by
          rw [← hexp_sq]; nlinarith [pow_le_pow_left₀ (by positivity) hs 2]
        unfold uctHCE; rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, show ‖(4 : ℂ)‖ = 4 by simp, Real.exp_neg, ← div_eq_mul_inv,
          div_le_div_iff₀ (by positivity) (Real.exp_pos _)]
        nlinarith [Real.pi_pos]
      have hH1 := hHCE_exp z hz him1.le
      have hH2 := hHCE_exp (1 - z) h1z (by rw [h1z_im]; exact him1.le)
      rw [h1z_im] at hH2
      have hexp_bd : ‖Complex.exp (stripCompGExt v z) - 1‖ ≤ Real.exp M₀ + 1 := by
        calc ‖Complex.exp (stripCompGExt v z) - 1‖ ≤ ‖Complex.exp (stripCompGExt v z)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = Real.exp (stripCompGExt v z).re + 1 := by rw [Complex.norm_exp, norm_one]
          _ ≤ Real.exp M₀ + 1 := add_le_add (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hM₀ z hz))) le_rfl
      dsimp only [F]; rw [norm_mul]
      calc ‖stripH0 kind z‖ * ‖Complex.exp (stripCompGExt v z) - 1‖
          ≤ (8 * π ^ 2 * Real.exp (-(π * |z.im|))) * (Real.exp M₀ + 1) :=
            mul_le_mul (by linarith) hexp_bd (norm_nonneg _) (by positivity)
        _ ≤ (8 * π ^ 2 * (2 / (1 + z.im ^ 2))) * (Real.exp M₀ + 1) := by
            have := hexp_inv_sq z.im
            gcongr
        _ = C_large / (1 + z.im ^ 2) := by dsimp only [C_large]; ring
        _ ≤ (2 * C_large) / (1 + z.im ^ 2) := div_le_div_of_nonneg_right (by linarith [show 0 ≤ C_large by positivity]) (by positivity)
        _ ≤ C_F / (1 + z.im ^ 2) := div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  -- Holomorphicity of `F` on `strip`
  have hF_diff : DifferentiableOn ℂ F strip := by
    have hH_diff : DifferentiableOn ℂ (stripH0 kind) strip := by
      have hnotint : ∀ z ∈ strip, ∀ n : ℤ, z ≠ n := fun z hz n h => by
        have hre := congrArg Complex.re h; simp at hre
        have : (0 : ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 := ⟨by linarith [hz.1], by linarith [hz.2]⟩
        have h1 : (0 : ℤ) < n := Int.cast_pos.mp this.1
        have h2 : n < (1 : ℤ) := Int.cast_lt.mp (by simpa using this.2)
        omega
      have hsin_ne : ∀ z ∈ strip, Complex.sin (π * z) ≠ 0 := fun z hz => sin_pi_ne_zero (hnotint z hz)
      have hsin2_ne : ∀ z ∈ strip, Complex.sin (π * z / 2) ≠ 0 := fun z hz h => by
        apply hsin_ne z hz
        rw [show (π : ℂ) * z = 2 * (π * z / 2) by ring, Complex.sin_two_mul, h]; ring
      cases kind
      · dsimp only [stripH0]; unfold uctHstar
        refine (differentiableOn_const _ |>.mul (Complex.differentiable_cos.comp
          (differentiable_const _ |>.mul differentiable_id) |>.differentiableOn)).div
          ((Complex.differentiable_sin.comp (differentiable_const _ |>.mul differentiable_id) |>.pow 2).differentiableOn)
          fun z hz => pow_ne_zero 2 (hsin_ne z hz)
      · dsimp only [stripH0]; unfold uctHCE
        refine (differentiableOn_const _).div
          ((differentiable_const _ |>.mul ((Complex.differentiable_sin.comp
            ((differentiable_const _ |>.mul differentiable_id).div_const 2)).pow 2)).differentiableOn)
          fun z hz => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hsin2_ne z hz))
    have hg_diff : DifferentiableOn ℂ (stripCompGExt v) strip :=
      (differentiableOn_stripCompG hv.continuous hv_supp).congr fun z hz => stripCompGExt_eq_of_mem_strip hz
    exact hH_diff.mul ((hg_diff.cexp).sub (differentiableOn_const 1))
  -- Contour shift for every `0 < ε < 1/2`: `∫ F(ε + it) dt = ∫ F((1 - ε) + it) dt`
  have hshift : ∀ {ε : ℝ}, 0 < ε → ε < 1 / 2 →
      (∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ))) =
        ∫ t : ℝ, F (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
    intro ε hε0 hε12
    refine vertical_shift_strip_symm hε0 hε12 hCF_nn hF_diff fun z hz1 hz2 => ?_
    exact hF_bd z ⟨by linarith, by linarith⟩
      (fun h => by subst h; simp at hz1; linarith)
      (fun h => by subst h; simp at hz2; linarith)
  -- Pass to `ε ↓ 0` by DCT on BOTH sides!
  have hlim_L : Tendsto (fun ε : ℝ => ∫ t : ℝ, F ((ε : ℂ) + Complex.I * (t : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ, F (Complex.I * (t : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => C_F / (1 + t ^ 2)) ?_ ?_
      (by simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C_F) ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      exact (hF_diff.continuousOn.comp_continuous (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
        fun t => ⟨by simp [hε.1], by simp; linarith [hε.2]⟩).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      refine Filter.Eventually.of_forall fun t => ?_
      have h := hF_bd ((ε : ℂ) + Complex.I * (t : ℂ)) ⟨by simp [hε.1.le], by simp; linarith [hε.2]⟩
        (fun h0 => by have := congrArg Complex.re h0; simp at this; linarith [hε.1])
        (fun h1 => by have := congrArg Complex.re h1; simp at this; linarith [hε.2])
      simpa using h
    · filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by rw [ae_iff]; simp] with t ht
      have hcont_H : ContinuousAt (stripH0 kind) (Complex.I * (t : ℂ)) := by
        have hnotint : ∀ n : ℤ, Complex.I * (t : ℂ) ≠ n := fun n h => by
          have := congrArg Complex.im h; simp at this; exact ht this
        have hsin_ne : Complex.sin (π * (Complex.I * (t : ℂ))) ≠ 0 := sin_pi_ne_zero hnotint
        have hsin2_ne : Complex.sin (π * (Complex.I * (t : ℂ)) / 2) ≠ 0 := fun h => by
          apply hsin_ne; rw [show (π : ℂ) * (Complex.I * (t : ℂ)) = 2 * (π * (Complex.I * (t : ℂ)) / 2) by ring,
            Complex.sin_two_mul, h]; ring
        cases kind
        · dsimp only [stripH0]; unfold uctHstar
          exact (continuousAt_const.mul (Complex.continuous_cos.comp
            (continuous_const.mul continuous_id) |>.continuousAt)).div
            ((Complex.continuous_sin.comp (continuous_const.mul continuous_id) |>.pow 2).continuousAt)
            (pow_ne_zero 2 hsin_ne)
        · dsimp only [stripH0]; unfold uctHCE
          exact continuousAt_const.div
            ((continuous_const.mul ((Complex.continuous_sin.comp
              ((continuous_const.mul continuous_id).div_const 2)).pow 2)).continuousAt)
            (mul_ne_zero (by norm_num) (pow_ne_zero 2 hsin2_ne))
      have hcont_F : ContinuousWithinAt F closedStrip (Complex.I * (t : ℂ)) :=
        hcont_H.continuousWithinAt.mul
          (((continuousOn_stripCompGExt hv hv_supp _ ⟨by simp, by simp⟩).cexp).sub continuousWithinAt_const)
      have hpath : Tendsto (fun ε : ℝ => (ε : ℂ) + Complex.I * (t : ℂ)) (𝓝[>] (0 : ℝ))
          (𝓝[closedStrip] (Complex.I * (t : ℂ))) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨by
          simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds).add tendsto_const_nhds, ?_⟩
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
        exact ⟨by simp [hε.1.le], by simp; linarith [hε.2]⟩
      exact hcont_F.tendsto.comp hpath
  have hlim_R : Tendsto (fun ε : ℝ => ∫ t : ℝ, F (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ))) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t : ℝ, F ((1 : ℂ) + Complex.I * (t : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => C_F / (1 + t ^ 2)) ?_ ?_
      (by simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C_F) ?_
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      exact (hF_diff.continuousOn.comp_continuous (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
        fun t => ⟨by simp; linarith [hε.2], by simp; linarith [hε.1]⟩).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      refine Filter.Eventually.of_forall fun t => ?_
      have h := hF_bd (((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ)) ⟨by simp; linarith [hε.2], by simp; linarith [hε.1]⟩
        (fun h0 => by have := congrArg Complex.re h0; simp at this; linarith [hε.2])
        (fun h1 => by have := congrArg Complex.re h1; simp at this; linarith [hε.1])
      simpa using h
    · filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by rw [ae_iff]; simp] with t ht
      have hcont_H : ContinuousAt (stripH0 kind) ((1 : ℂ) + Complex.I * (t : ℂ)) := by
        have hnotint : ∀ n : ℤ, (1 : ℂ) + Complex.I * (t : ℂ) ≠ n := fun n h => by
          have := congrArg Complex.im h; simp at this; exact ht this
        have hsin_ne : Complex.sin (π * ((1 : ℂ) + Complex.I * (t : ℂ))) ≠ 0 := sin_pi_ne_zero hnotint
        have hsin2_ne : Complex.sin (π * ((1 : ℂ) + Complex.I * (t : ℂ)) / 2) ≠ 0 := fun h => by
          apply hsin_ne; rw [show (π : ℂ) * ((1 : ℂ) + Complex.I * (t : ℂ)) = 2 * (π * ((1 : ℂ) + Complex.I * (t : ℂ)) / 2) by ring,
            Complex.sin_two_mul, h]; ring
        cases kind
        · dsimp only [stripH0]; unfold uctHstar
          exact (continuousAt_const.mul (Complex.continuous_cos.comp
            (continuous_const.mul continuous_id) |>.continuousAt)).div
            ((Complex.continuous_sin.comp (continuous_const.mul continuous_id) |>.pow 2).continuousAt)
            (pow_ne_zero 2 hsin_ne)
        · dsimp only [stripH0]; unfold uctHCE
          exact continuousAt_const.div
            ((continuous_const.mul ((Complex.continuous_sin.comp
              ((continuous_const.mul continuous_id).div_const 2)).pow 2)).continuousAt)
            (mul_ne_zero (by norm_num) (pow_ne_zero 2 hsin2_ne))
      have hcont_F : ContinuousWithinAt F closedStrip ((1 : ℂ) + Complex.I * (t : ℂ)) :=
        hcont_H.continuousWithinAt.mul
          (((continuousOn_stripCompGExt hv hv_supp _ ⟨by simp, by simp⟩).cexp).sub continuousWithinAt_const)
      have hpath : Tendsto (fun ε : ℝ => ((1 - ε : ℝ) : ℂ) + Complex.I * (t : ℂ)) (𝓝[>] (0 : ℝ))
          (𝓝[closedStrip] ((1 : ℂ) + Complex.I * (t : ℂ))) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have h1 : Tendsto (fun ε : ℝ => ((1 - ε : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
            have h1r : Tendsto (fun ε : ℝ => (1 : ℝ) - ε) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
              simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left nhdsWithin_le_nhds
            simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 1).comp h1r
          exact h1.add tendsto_const_nhds
        · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
          exact ⟨by simp; linarith [hε.2], by simp; linarith [hε.1]⟩
      exact hcont_F.tendsto.comp hpath
  have hshift_eq : (∫ t : ℝ, F (Complex.I * (t : ℂ))) = ∫ t : ℝ, F ((1 : ℂ) + Complex.I * (t : ℂ)) := by
    refine tendsto_nhds_unique hlim_L (hlim_R.congr' ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    exact (hshift hε.1 hε.2).symm
  -- Integrability of `t ↦ F (i t)` and `t ↦ F (1 + i t)` on `ℝ`
  have hF_L_int : Integrable (fun t : ℝ => F (Complex.I * (t : ℂ))) := by
    have hmeas_on : ContinuousOn (fun t : ℝ => F (Complex.I * (t : ℂ))) ({(0 : ℝ)}ᶜ) := by
      intro t ht
      have ht0 : t ≠ 0 := by simpa using ht
      have hnotint : ∀ n : ℤ, Complex.I * (t : ℂ) ≠ n := fun n h => by have := congrArg Complex.im h; simp at this; exact ht0 this
      have hsin_ne := sin_pi_ne_zero hnotint
      have hsin2_ne : Complex.sin (π * (Complex.I * (t : ℂ)) / 2) ≠ 0 := fun h => by
        apply hsin_ne; rw [show (π : ℂ) * (Complex.I * (t : ℂ)) = 2 * (π * (Complex.I * (t : ℂ)) / 2) by ring,
          Complex.sin_two_mul, h]; ring
      have hH_c : ContinuousAt (stripH0 kind) (Complex.I * (t : ℂ)) := by
        cases kind
        · dsimp only [stripH0]; unfold uctHstar
          exact (continuousAt_const.mul (Complex.continuous_cos.comp (continuous_const.mul continuous_id) |>.continuousAt)).div
            ((Complex.continuous_sin.comp (continuous_const.mul continuous_id) |>.pow 2).continuousAt) (pow_ne_zero 2 hsin_ne)
        · dsimp only [stripH0]; unfold uctHCE
          exact continuousAt_const.div ((continuous_const.mul ((Complex.continuous_sin.comp
            ((continuous_const.mul continuous_id).div_const 2)).pow 2)).continuousAt) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hsin2_ne))
      have hline_c : ContinuousAt (fun s : ℝ => Complex.I * (s : ℂ)) t :=
        (continuous_const.mul Complex.continuous_ofReal).continuousAt
      have hg_c : Continuous (fun s : ℝ => Complex.exp (stripCompGExt v (Complex.I * (s : ℂ))) - 1) :=
        ((continuousOn_stripCompGExt hv hv_supp).comp_continuous (continuous_const.mul Complex.continuous_ofReal)
          fun s => ⟨by simp, by simp⟩).cexp.sub continuous_const
      exact ((hH_c.comp (f := fun s : ℝ => Complex.I * (s : ℂ)) hline_c).mul hg_c.continuousAt).continuousWithinAt
    have hmeas : AEStronglyMeasurable (fun t : ℝ => F (Complex.I * (t : ℂ))) volume := by
      have h1 := hmeas_on.aestronglyMeasurable (μ := volume) isOpen_compl_singleton.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; simp)] at h1
    refine (by simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C_F : Integrable (fun t : ℝ => C_F / (1 + t ^ 2))).mono' hmeas ?_
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by rw [ae_iff]; simp] with t ht
    have h := hF_bd (Complex.I * (t : ℂ)) ⟨by simp, by simp⟩
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht))
      (fun h1 => by have := congrArg Complex.re h1; simp at this)
    simpa using h
  have hF_R_int : Integrable (fun t : ℝ => F ((1 : ℂ) + Complex.I * (t : ℂ))) := by
    have hmeas_on : ContinuousOn (fun t : ℝ => F ((1 : ℂ) + Complex.I * (t : ℂ))) ({(0 : ℝ)}ᶜ) := by
      intro t ht
      have ht0 : t ≠ 0 := by simpa using ht
      have hnotint : ∀ n : ℤ, (1 : ℂ) + Complex.I * (t : ℂ) ≠ n := fun n h => by have := congrArg Complex.im h; simp at this; exact ht0 this
      have hsin_ne := sin_pi_ne_zero hnotint
      have hsin2_ne : Complex.sin (π * ((1 : ℂ) + Complex.I * (t : ℂ)) / 2) ≠ 0 := fun h => by
        apply hsin_ne; rw [show (π : ℂ) * ((1 : ℂ) + Complex.I * (t : ℂ)) = 2 * (π * ((1 : ℂ) + Complex.I * (t : ℂ)) / 2) by ring,
          Complex.sin_two_mul, h]; ring
      have hH_c : ContinuousAt (stripH0 kind) ((1 : ℂ) + Complex.I * (t : ℂ)) := by
        cases kind
        · dsimp only [stripH0]; unfold uctHstar
          exact (continuousAt_const.mul (Complex.continuous_cos.comp (continuous_const.mul continuous_id) |>.continuousAt)).div
            ((Complex.continuous_sin.comp (continuous_const.mul continuous_id) |>.pow 2).continuousAt) (pow_ne_zero 2 hsin_ne)
        · dsimp only [stripH0]; unfold uctHCE
          exact continuousAt_const.div ((continuous_const.mul ((Complex.continuous_sin.comp
            ((continuous_const.mul continuous_id).div_const 2)).pow 2)).continuousAt) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hsin2_ne))
      have hline_c : ContinuousAt (fun s : ℝ => (1 : ℂ) + Complex.I * (s : ℂ)) t :=
        (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt
      have hg_c : Continuous (fun s : ℝ => Complex.exp (stripCompGExt v ((1 : ℂ) + Complex.I * (s : ℂ))) - 1) :=
        ((continuousOn_stripCompGExt hv hv_supp).comp_continuous (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))
          fun s => ⟨by simp, by simp⟩).cexp.sub continuous_const
      exact ((hH_c.comp (f := fun s : ℝ => (1 : ℂ) + Complex.I * (s : ℂ)) hline_c).mul hg_c.continuousAt).continuousWithinAt
    have hmeas : AEStronglyMeasurable (fun t : ℝ => F ((1 : ℂ) + Complex.I * (t : ℂ))) volume := by
      have h1 := hmeas_on.aestronglyMeasurable (μ := volume) isOpen_compl_singleton.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; simp)] at h1
    refine (by simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C_F : Integrable (fun t : ℝ => C_F / (1 + t ^ 2))).mono' hmeas ?_
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 0 by rw [ae_iff]; simp] with t ht
    have h := hF_bd ((1 : ℂ) + Complex.I * (t : ℂ)) ⟨by simp, by simp⟩
      (fun h0 => by have := congrArg Complex.re h0; simp at this)
      (fun h1 => by have := congrArg Complex.im h1; simp at this; exact ht this)
    simpa using h
  -- Take real parts of `hshift_eq`!
  have hre_eq : (∫ t : ℝ, (F (Complex.I * (t : ℂ))).re) = ∫ t : ℝ, (F ((1 : ℂ) + Complex.I * (t : ℂ))).re := by
    have h1 := Complex.reCLM.integral_comp_comm hF_L_int
    have h2 := Complex.reCLM.integral_comp_comm hF_R_int
    change (∫ t : ℝ, Complex.reCLM (F (Complex.I * (t : ℂ)))) = ∫ t : ℝ, Complex.reCLM (F ((1 : ℂ) + Complex.I * (t : ℂ)))
    rw [h1, h2, hshift_eq]
  -- Evaluate `Re(F (i t))` and `Re(F (1 + i t))` pointwise for `t ≠ 0`
  have hexp_re_L : ∀ t : ℝ, (Complex.exp (stripCompGExt v (Complex.I * (t : ℂ))) - 1).re =
      Real.exp (v t) * Real.cos (fctThetaD v t) - 1 := fun t => by
    rw [mul_comm Complex.I (t : ℂ), stripCompGExt_left, Complex.sub_re, Complex.one_re,
      Complex.exp_add, ← Complex.ofReal_exp, mul_comm Complex.I, Complex.exp_mul_I,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re,
      Complex.sin_ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  have hexp_re_R : ∀ t : ℝ, (Complex.exp (stripCompGExt v ((1 : ℂ) + Complex.I * (t : ℂ))) - 1).re =
      Real.exp (v t) * Real.cos (fctThetaD v t) - 1 := fun t => by
    rw [mul_comm Complex.I (t : ℂ), stripCompGExt_right, Complex.sub_re, Complex.one_re,
      show (v t : ℂ) - Complex.I * (fctThetaD v t : ℂ) = (v t : ℂ) + ((-fctThetaD v t : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re, Complex.cos_ofReal_re, Real.cos_neg, Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re,
      Complex.sin_ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  have hH_real_L : ∀ t : ℝ, 0 < t →
      stripH0 kind (Complex.I * (t : ℂ)) = ((-‖stripH0 kind ((t : ℂ) * Complex.I)‖ : ℝ) : ℂ) := by
    intro t ht
    rw [mul_comm Complex.I (t : ℂ)]
    cases kind
    · rw [norm_stripH0_star_imag ht]
      dsimp only [stripH0]
      have hnotint : ∀ n : ℤ, (t : ℂ) * Complex.I ≠ n := fun n h => by have := congrArg Complex.im h; simp at this; linarith
      rw [uct_H_split hnotint, uctHCE_imag]
      have h1sub : uctHCE (1 - (t : ℂ) * Complex.I) = ((π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) : ℝ) : ℂ) := by
        have h := uctHCE_one_add_imag (-t)
        rw [show (1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I = 1 - (t : ℂ) * Complex.I by push_cast; ring,
          show π * -t / 2 = -(π * t / 2) by ring, Real.cosh_neg] at h
        exact h
      rw [h1sub, ← Complex.ofReal_sub]; congr 1; ring
    · rw [norm_stripH0_ce_imag ht]; dsimp only [stripH0]; exact uctHCE_imag t
  -- Evenness of `(F (i t)).re` and `(F (1 + i t)).re`
  have hFL_even : ∀ t : ℝ, (F (Complex.I * ((-t : ℝ) : ℂ))).re = (F (Complex.I * (t : ℂ))).re := by
    intro t
    by_cases ht0 : t = 0
    · simp [ht0]
    · have hH_even : stripH0 kind (Complex.I * ((-t : ℝ) : ℂ)) = stripH0 kind (Complex.I * (t : ℂ)) := by
        cases kind
        · dsimp only [stripH0]; unfold uctHstar
          rw [Complex.ofReal_neg, mul_neg, mul_neg, Complex.cos_neg, Complex.sin_neg, neg_sq]
        · dsimp only [stripH0]; unfold uctHCE
          rw [Complex.ofReal_neg, mul_neg, mul_neg, neg_div, Complex.sin_neg, neg_sq]
      have hH_im : (stripH0 kind (Complex.I * (t : ℂ))).im = 0 := by
        rcases lt_or_gt_of_ne ht0 with h | h
        · rw [← hH_even, hH_real_L (-t) (neg_pos.mpr h), Complex.ofReal_im]
        · rw [hH_real_L t h, Complex.ofReal_im]
      dsimp only [F]
      rw [hH_even, Complex.mul_re, Complex.mul_re, hH_im, zero_mul, sub_zero, zero_mul, sub_zero,
        hexp_re_L, hexp_re_L, hv_even, fctThetaD_odd hv_even, Real.cos_neg]
  have hFL_re_pos : ∀ t : ℝ, 0 < t →
      (F (Complex.I * (t : ℂ))).re =
        -(‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) := by
    intro t ht
    dsimp only [F]
    rw [hH_real_L t ht, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hexp_re_L]
    ring
  have hFL_re_int : Integrable (fun t : ℝ => (F (Complex.I * (t : ℂ))).re) :=
    Complex.reCLM.integrable_comp hF_L_int
  have hFR_re_int : Integrable (fun t : ℝ => (F ((1 : ℂ) + Complex.I * (t : ℂ))).re) :=
    Complex.reCLM.integrable_comp hF_R_int
  have hL_Ioi_int : IntegrableOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
      (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) (Ioi 0) := by
    have h1 := hFL_re_int.neg.integrableOn (s := Ioi 0)
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.neg_apply, hFL_re_pos t ht, neg_neg]
  -- Helper: for any even integrable `g : ℝ → ℝ`, `∫ t : ℝ, g t = 2 * ∫ t in Ioi 0, g t`
  have heven_int : ∀ (g : ℝ → ℝ), Integrable g → (∀ t, g (-t) = g t) →
      (∫ t : ℝ, g t) = 2 * ∫ t in Ioi (0 : ℝ), g t := by
    intro g hg he
    have hsplit : (∫ t : ℝ, g t) = (∫ t in Iic (0 : ℝ), g t) + ∫ t in Ioi (0 : ℝ), g t := by
      rw [← setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [mem_Iic.mp h1, mem_Ioi.mp h2])
        measurableSet_Ioi hg.integrableOn hg.integrableOn, Iic_union_Ioi, setIntegral_univ]
    have hneg : (∫ t in Iic (0 : ℝ), g t) = ∫ t in Ioi (0 : ℝ), g t := by
      have h1 := integral_comp_neg_Ioi (0 : ℝ) g
      simp only [neg_zero] at h1
      rw [← h1]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => he t
    linarith
  have hθ0 : fctThetaD v 0 = 0 := by
    have h := fctThetaD_odd hv_even 0; simp only [neg_zero] at h; linarith
  refine ⟨hL_Ioi_int, ?_⟩
  cases kind
  · -- `H_*`: `F(1 + it) = -F(it)` for `Re`!
    have hFR_eq : ∀ t : ℝ, (F ((1 : ℂ) + Complex.I * (t : ℂ))).re = -(F (Complex.I * (t : ℂ))).re := by
      intro t
      by_cases ht0 : t = 0
      · have h0 : stripCompGExt v (0 : ℂ) = 0 := by
          have h := stripCompGExt_left v 0; simpa [hv0, hθ0] using h
        have h1 : stripCompGExt v (1 : ℂ) = 0 := by
          have h := stripCompGExt_right v 0; simpa [hv0, hθ0] using h
        simp [F, ht0, h0, h1]
      · have hH_neg : stripH0 .star ((1 : ℂ) + Complex.I * (t : ℂ)) = -stripH0 .star (Complex.I * (t : ℂ)) := by
          dsimp only [stripH0]; unfold uctHstar
          rw [show (π : ℂ) * ((1 : ℂ) + Complex.I * (t : ℂ)) = π * (Complex.I * (t : ℂ)) + π by ring,
            Complex.cos_add_pi, Complex.sin_add_pi, neg_sq]; ring
        have hH_im : (stripH0 .star (Complex.I * (t : ℂ))).im = 0 := by
          rcases lt_or_gt_of_ne ht0 with h | h
          · have h1 := hH_real_L (-t) (neg_pos.mpr h)
            have he : stripH0 .star (Complex.I * (t : ℂ)) = stripH0 .star (Complex.I * ((-t : ℝ) : ℂ)) := by
              dsimp only [stripH0]; unfold uctHstar
              rw [Complex.ofReal_neg, mul_neg, mul_neg, Complex.cos_neg, Complex.sin_neg, neg_sq]
            rw [he, h1, Complex.ofReal_im]
          · rw [hH_real_L t h, Complex.ofReal_im]
        dsimp only [F]
        rw [hH_neg, Complex.mul_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, hH_im, neg_zero,
          zero_mul, sub_zero, zero_mul, sub_zero, hexp_re_R, hexp_re_L]
        ring
    have hzero_R : (∫ t : ℝ, (F (Complex.I * (t : ℂ))).re) = 0 := by
      have h1 : (∫ t : ℝ, (F ((1 : ℂ) + Complex.I * (t : ℂ))).re) =
          -(∫ t : ℝ, (F (Complex.I * (t : ℂ))).re) := by
        simp_rw [hFR_eq]; rw [integral_neg]
      linarith [hre_eq]
    rw [heven_int _ hFL_re_int hFL_even] at hzero_R
    have hIoi0 : (∫ t in Ioi (0 : ℝ), (F (Complex.I * (t : ℂ))).re) = 0 := by linarith
    have hcongr : (∫ t in Ioi (0 : ℝ), (F (Complex.I * (t : ℂ))).re) =
        -(∫ t in Ioi (0 : ℝ), ‖stripH0 .star ((t : ℂ) * Complex.I)‖ *
          (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) := by
      rw [← integral_neg]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hFL_re_pos t ht
    linarith
  · -- `H_CE`: `H_CE(1 + it) = π² / (4 cosh²(πt/2))`!
    have hFR_re_eq : ∀ t : ℝ, (F ((1 : ℂ) + Complex.I * (t : ℂ))).re =
        (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) * (Real.exp (v t) * Real.cos (fctThetaD v t) - 1) := by
      intro t
      dsimp only [F, stripH0]
      rw [mul_comm Complex.I (t : ℂ), uctHCE_one_add_imag, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, mul_comm (t : ℂ) Complex.I, hexp_re_R]
    have hFR_even : ∀ t : ℝ, (F ((1 : ℂ) + Complex.I * ((-t : ℝ) : ℂ))).re =
        (F ((1 : ℂ) + Complex.I * (t : ℂ))).re := fun t => by
      rw [hFR_re_eq, hFR_re_eq, show π * -t / 2 = -(π * t / 2) by ring, Real.cosh_neg, hv_even,
        fctThetaD_odd hv_even, Real.cos_neg]
    have hR_Ioi_int : IntegrableOn (fun t : ℝ => (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) *
        (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) (Ioi 0) :=
      hFR_re_int.integrableOn.congr_fun (fun t _ => hFR_re_eq t) measurableSet_Ioi
    refine ⟨hR_Ioi_int, ?_⟩
    rw [heven_int _ hFL_re_int hFL_even, heven_int _ hFR_re_int hFR_even] at hre_eq
    have hL_eq : (∫ t in Ioi (0 : ℝ), (F (Complex.I * (t : ℂ))).re) =
        -(∫ t in Ioi (0 : ℝ), ‖stripH0 .ce ((t : ℂ) * Complex.I)‖ *
          (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) := by
      rw [← integral_neg]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hFL_re_pos t ht
    have hR_eq : (∫ t in Ioi (0 : ℝ), (F ((1 : ℂ) + Complex.I * (t : ℂ))).re) =
        ∫ t in Ioi (0 : ℝ), (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) *
          (Real.exp (v t) * Real.cos (fctThetaD v t) - 1) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => hFR_re_eq t
    linarith

/-! ### Part (2a) headline: cosine vacuum penalty `(fct:cos-pen)` first equation -/

lemma one_sub_cos_le_half_sq (x : ℝ) : 0 ≤ 1 - Real.cos x ∧ 1 - Real.cos x ≤ x ^ 2 / 2 := by
  refine ⟨by linarith [Real.cos_le_one x], ?_⟩
  have h := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith

set_option maxHeartbeats 400000 in
/-- **Part (2a) of `fct:comp-D`** (`(fct:cos-pen)`, first equation):
For `H_0 ∈ {H_*, H_CE}`, `I_osc^{DH_0} - I_fl` is integrable on `(0, ∞)` and satisfies
`|∫_0^∞ (I_osc^{DH_0}(L) - I_fl(L)) dL - C_fl(H_0)| ≤ C(K₄) τ₁^3`.
Moreover, for `H_*`, the integral equals the exact nonnegative cosine penalty
`α_osc ∫_0^∞ |H_*(it)| e^{v(t)} (1 - cos ϑ_D(t)) dt`. -/
theorem fct_comp_D_cos_penalty (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 20 ∧
      ∀ K4 : ℝ, 1 ≤ K4 → ∃ C ≥ 0,
        ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ → τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
          let v := vTotal kind K4 c α τ₁
          IntegrableOn (fun L : ℝ => stripIoscD kind v L - uctIfl L) (Ioi 0) ∧
          IntegrableOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
            Real.exp (v t) * (1 - Real.cos (fctThetaD v t))) (Ioi 0) ∧
          |(∫ L in Ioi (0 : ℝ), (stripIoscD kind v L - uctIfl L)) - stripCfl kind| ≤ C * τ₁ ^ 3 ∧
          (kind = .star →
            (∫ L in Ioi (0 : ℝ), (stripIoscD .star v L - uctIfl L)) =
              uctAlphaOsc * ∫ t in Ioi (0 : ℝ), ‖stripH0 .star ((t : ℂ) * Complex.I)‖ *
                Real.exp (v t) * (1 - Real.cos (fctThetaD v t))) := by
  obtain ⟨τ₀, hτ₀_pos, hτ₀_20, Cv0b, Cv0m, Cva, Cv1b, Cv1m,
    Cth0b, Cth0m, Ctha, Cth1b, Cth1m, CL1_0b, CL1_0m, CL1_a, CL1_1b, CL1_1m,
    C_tail, C_int, hCv_nn, hCth_nn, hCL1_nn, hCti_nn, hpart1⟩ := fct_comp_D_part1 kind
  refine ⟨τ₀, hτ₀_pos, hτ₀_20, fun K4 hK4 => ?_⟩
  have hK4_nn : 0 ≤ K4 := by linarith
  -- Constants depending only on `K4` (and `kind`)
  set M_v0 : ℝ := Cv0b 0 + K4 * Cv0m 0 + Cv1b 0 + K4 * Cv1m 0 + Cva 0
  set M_th0_in : ℝ := Cth0b 0 + K4 * Cth0m 0 + Cth1b 0 + K4 * Cth1m 0 + Ctha 0
  set M_L1 : ℝ := (CL1_0b + K4 * CL1_0m) + (CL1_1b + K4 * CL1_1m) + CL1_a
  set M_th0_tail : ℝ := C_tail 0 * M_L1
  set M_g0 : ℝ := M_v0 + max M_th0_in (M_th0_tail * (12 : ℝ) ^ (-1 : ℤ))
  set M_g2 : ℝ := (Cv0b 2 + K4 * Cv0m 2 + Cv1b 2 + K4 * Cv1m 2 + Cva 2) +
      max (Cth0b 2 + K4 * Cth0m 2 + Cth1b 2 + K4 * Cth1m 2 + Ctha 2)
        (C_tail 2 * M_L1 * (12 : ℝ) ^ (-3 : ℤ))
  have hMv0_nn : 0 ≤ M_v0 := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hCv_nn 0; positivity
  have hMth0_in_nn : 0 ≤ M_th0_in := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hCth_nn 0; positivity
  have hML1_nn : 0 ≤ M_L1 := by
    rcases hCL1_nn with ⟨h1, h2, h3, h4, h5⟩; positivity
  have hMth0_tail_nn : 0 ≤ M_th0_tail := mul_nonneg (hCti_nn 0).1 hML1_nn
  have hMg0_nn : 0 ≤ M_g0 := add_nonneg hMv0_nn (le_trans hMth0_in_nn (le_max_left _ _))
  have hMg2_nn : 0 ≤ M_g2 := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hCv_nn 2
    obtain ⟨g1, g2, g3, g4, g5⟩ := hCth_nn 2
    exact add_nonneg (by positivity) (le_trans (by positivity) (le_max_left _ _))
  -- Cosine penalty constant + CE right-edge constant
  set C_cos_in : ℝ := uctAlphaOsc * (1 + π ^ 2 / 4) * Real.exp M_v0 * (1 / 2) * M_th0_in ^ 2 * 12
  set C_cos_tail : ℝ := uctAlphaOsc * (1 + π ^ 2 / 4) * (1 / 2) * M_th0_tail ^ 2 * (1 / 12 ^ 3)
  set C_ce_in : ℝ := uctAlphaOsc * (π ^ 2 / 4) * (Real.exp M_v0 * M_v0 + (1 / 2) * M_th0_in ^ 2) * 10
  set C_ce_tail : ℝ := uctAlphaOsc * (π ^ 2 / 4) * (1 / 2) * (M_th0_in ^ 2 * 2 + M_th0_tail ^ 2 * (1 / 12))
  set C_tot : ℝ := C_cos_in + C_cos_tail + C_ce_in + C_ce_tail
  have hC_tot_nn : 0 ≤ C_tot := by
    have hαo : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
    positivity
  refine ⟨C_tot, hC_tot_nn, fun {c α τ₁} hc hτ₁ hτ₁_le hc_eq hα_le => ?_⟩
  obtain ⟨⟨_, _, _, _, _, hv_cd⟩, ⟨_, _, _, _, _, hv_even⟩, ⟨_, _, _, _, _, hv0⟩,
    ⟨_, _, _, _, _, hv_supp⟩, hmom, _, hderivs, _, hth_in, hth_tail, _, hg_cl, _⟩ :=
    hpart1 hK4 hc hτ₁ hτ₁_le hc_eq hα_le
  set v := vTotal kind K4 c α τ₁
  have hτ₁_20 : τ₁ ≤ 1 / 20 := hτ₁_le.trans hτ₀_20
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hv_cs : HasCompactSupport v := hasCompactSupport_of_support_Ioo hv_supp
  have hθ_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v) := contDiff_fctThetaD hv_cd hv_cs
  have hθ1 : deriv (fctThetaD v) 0 = 0 := by
    have h := (hmom 0 (by norm_num)).2.2.2.2.2.2.2
    simpa [iteratedDeriv_one] using h
  -- Bounds `|v t| ≤ M_v0 * τ₁^2`, `|ϑ_D t| ≤ M_th0_in * τ₁^2 * min 1 ((|t|/τ₁)^11)` on `|t| ≤ 12 τ₁`,
  -- and `|ϑ_D t| ≤ M_th0_tail * τ₁^3 * |t|^{-1} * e^{-(π/2)|t|}` on `|t| ≥ 12 τ₁`
  have hg0_bd : ∀ z ∈ closedStrip, ‖stripCompGExt v z‖ ≤ M_g0 := by
    intro z hz
    have h := hg_cl 0 z hz
    simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.cast_zero, sub_zero, zpow_two,
      show (1 + (0 : ℤ)) = 1 by rfl] at h
    exact h.trans (mul_le_of_le_one_right hMg0_nn (by rw [← sq]; exact pow_le_one₀ hτ₁.le hτ₁_1))
  have hg2_bd : ∀ z ∈ closedStrip, ‖(-Complex.I) ^ 2 * stripCompGExt (iteratedDeriv 2 v) z‖ ≤ M_g2 := by
    intro z hz
    have h := hg_cl 2 z hz
    simp only [Nat.cast_ofNat, sub_self, zpow_zero, mul_one,
      show -(1 + (2 : ℤ)) = -3 by norm_num] at h
    exact h
  have hv_abs_le : ∀ t : ℝ, |v t| ≤ M_v0 * τ₁ ^ 2 := by
    intro t
    have h := hg_cl 0 ((t : ℂ) * Complex.I) ⟨by simp, by simp⟩
    simp only [pow_zero, one_mul, iteratedDeriv_zero, Nat.cast_zero, sub_zero, zpow_two,
      stripCompGExt_left] at h
    -- Directly from `hderivs 0 t`!
    obtain ⟨d1, d2, d3, d4, d5⟩ := hderivs 0 t
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at d1 d2 d3 d4 d5
    have hc_inv : c⁻¹ = τ₁ ^ 4 := by
      rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
    have hα1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
    have hτ4 : τ₁ ^ (4 : ℤ) ≤ τ₁ ^ 2 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1b : c⁻¹ * τ₁ ^ (-1 : ℤ) ≤ τ₁ ^ 2 := by
      rw [hc_inv, zpow_neg_one, show τ₁ ^ 4 * τ₁⁻¹ = τ₁ ^ 3 by field_simp [hτ₁.ne']]
      exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1m : c⁻¹ * τ₁ ^ (1 : ℤ) ≤ τ₁ ^ 2 := by
      rw [hc_inv, zpow_one, ← pow_succ]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h2' : |v0Marg τ₁ t| ≤ Cv0m 0 * τ₁ ^ 2 := d2.trans (mul_le_mul_of_nonneg_left hτ4 (hCv_nn 0).2.1)
    have h3' : |vAlpha α τ₁ t| ≤ Cva 0 * τ₁ ^ 2 := d3.trans (by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
      have := mul_le_mul_of_nonneg_left hα1 (hCv_nn 0).2.2.1; rw [mul_one] at this
      exact mul_le_mul_of_nonneg_right this (sq_nonneg τ₁))
    have h4' : |v1Base kind c τ₁ t| ≤ Cv1b 0 * τ₁ ^ 2 := d4.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1b (hCv_nn 0).2.2.2.1)
    have h5' : |v1Marg c τ₁ t| ≤ Cv1m 0 * τ₁ ^ 2 := d5.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1m (hCv_nn 0).2.2.2.2)
    have d1' : |v0Base kind τ₁ t| ≤ Cv0b 0 * τ₁ ^ 2 := by simpa [zpow_two, ← sq] using d1
    have htri : |v t| ≤ |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t| + |v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t| + |vAlpha α τ₁ t| := by
      dsimp only [v]; unfold vTotal v0 v1
      have a1 := abs_add_le ((v0Base kind τ₁ t + K4 * v0Marg τ₁ t) + (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)) (vAlpha α τ₁ t)
      have a2 := abs_add_le (v0Base kind τ₁ t + K4 * v0Marg τ₁ t) (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)
      have a3 := abs_add_le (v0Base kind τ₁ t) (K4 * v0Marg τ₁ t)
      have a4 := abs_add_le (v1Base kind c τ₁ t) (K4 * v1Marg c τ₁ t)
      rw [abs_mul, abs_of_nonneg hK4_nn] at a3 a4; linarith
    have hm1 := mul_le_mul_of_nonneg_left h2' hK4_nn
    have hm2 := mul_le_mul_of_nonneg_left h5' hK4_nn
    calc |v t| ≤ |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t| + |v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t| + |vAlpha α τ₁ t| := htri
      _ ≤ Cv0b 0 * τ₁ ^ 2 + K4 * (Cv0m 0 * τ₁ ^ 2) + Cv1b 0 * τ₁ ^ 2 + K4 * (Cv1m 0 * τ₁ ^ 2) + Cva 0 * τ₁ ^ 2 :=
          add_le_add (add_le_add (add_le_add (add_le_add d1' hm1) h4') hm2) h3'
      _ = M_v0 * τ₁ ^ 2 := by dsimp only [M_v0]; ring
  have hv_exp_le : ∀ t : ℝ, Real.exp (v t) ≤ Real.exp M_v0 := fun t =>
    Real.exp_le_exp.mpr ((le_abs_self _).trans ((hv_abs_le t).trans (mul_le_of_le_one_right hMv0_nn (pow_le_one₀ hτ₁.le hτ₁_1))))
  have hθ_in_le : ∀ t : ℝ, |t| ≤ 12 * τ₁ → |fctThetaD v t| ≤ M_th0_in * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) := by
    intro t ht
    obtain ⟨t1, t2, t3, t4, t5⟩ := hth_in 0 t ht
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, Nat.sub_zero] at t1 t2 t3 t4 t5
    have hc_inv : c⁻¹ = τ₁ ^ 4 := by
      rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
    have hα1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
    have hmin_nn : 0 ≤ min (1 : ℝ) ((|t| / τ₁) ^ 11) := le_min zero_le_one (by positivity)
    have hτ4 : τ₁ ^ (4 : ℤ) ≤ τ₁ ^ 2 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1b : c⁻¹ * τ₁ ^ (-1 : ℤ) ≤ τ₁ ^ 2 := by
      rw [hc_inv, zpow_neg_one, show τ₁ ^ 4 * τ₁⁻¹ = τ₁ ^ 3 by field_simp [hτ₁.ne']]
      exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1m : c⁻¹ * τ₁ ^ (1 : ℤ) ≤ τ₁ ^ 2 := by
      rw [hc_inv, zpow_one, ← pow_succ]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    -- Linearity of `fctThetaD` on `v = v0 + v1 + vAlpha`
    have hθ_lin : fctThetaD v t = (fctThetaD (v0Base kind τ₁) t + K4 * fctThetaD (v0Marg τ₁) t) +
        (fctThetaD (v1Base kind c τ₁) t + K4 * fctThetaD (v1Marg c τ₁) t) + fctThetaD (vAlpha α τ₁) t := by
      obtain ⟨⟨hb0_cd, hm0_cd, ha0_cd, hb1_cd, hm1_cd, _⟩, _, _, ⟨hb0_s, hm0_s, ha0_s, hb1_s, hm1_s, _⟩, _⟩ :=
        hpart1 hK4 hc hτ₁ hτ₁_le hc_eq hα_le
      have hb0_cs := hasCompactSupport_of_support_Ioo hb0_s
      have hm0_cs := hasCompactSupport_of_support_Ioo hm0_s
      have ha0_cs := hasCompactSupport_of_support_Ioo ha0_s
      have hb1_cs := hasCompactSupport_of_support_Ioo hb1_s
      have hm1_cs := hasCompactSupport_of_support_Ioo hm1_s
      have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 kind K4 τ₁) := hb0_cd.add (contDiff_const.mul hm0_cd)
      have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (v1 kind K4 c τ₁) := hb1_cd.add (contDiff_const.mul hm1_cd)
      have hv0_cs : HasCompactSupport (v0 kind K4 τ₁) := hb0_cs.add (hm0_cs.mul_left)
      have hv1_cs : HasCompactSupport (v1 kind K4 c τ₁) := hb1_cs.add (hm1_cs.mul_left)
      have e0 : fctThetaD (v0 kind K4 τ₁) t = fctThetaD (v0Base kind τ₁) t + K4 * fctThetaD (v0Marg τ₁) t := by
        unfold v0; simpa only [one_mul] using fctThetaD_linear hb0_cd hb0_cs hm0_cd hm0_cs 1 K4 t
      have e1 : fctThetaD (v1 kind K4 c τ₁) t = fctThetaD (v1Base kind c τ₁) t + K4 * fctThetaD (v1Marg c τ₁) t := by
        unfold v1; simpa only [one_mul] using fctThetaD_linear hb1_cd hb1_cs hm1_cd hm1_cs 1 K4 t
      have e01 : fctThetaD (fun s => v0 kind K4 τ₁ s + v1 kind K4 c τ₁ s) t =
          fctThetaD (v0 kind K4 τ₁) t + fctThetaD (v1 kind K4 c τ₁) t := by
        simpa only [one_mul] using fctThetaD_linear hv0_cd hv0_cs hv1_cd hv1_cs 1 1 t
      have eall : fctThetaD v t = fctThetaD (fun s => v0 kind K4 τ₁ s + v1 kind K4 c τ₁ s) t + fctThetaD (vAlpha α τ₁) t := by
        dsimp only [v]; unfold vTotal
        simpa only [one_mul] using fctThetaD_linear (hv0_cd.add hv1_cd) (hv0_cs.add hv1_cs) ha0_cd ha0_cs 1 1 t
      rw [eall, e01, e0, e1]
    have t1' : |fctThetaD (v0Base kind τ₁) t| ≤ Cth0b 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) := by simpa [zpow_two, ← sq] using t1
    have t2' : |fctThetaD (v0Marg τ₁) t| ≤ Cth0m 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) :=
      t2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ4 (hCth_nn 0).2.1) hmin_nn)
    have t3' : |fctThetaD (vAlpha α τ₁) t| ≤ Ctha 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) :=
      t3.trans (mul_le_mul_of_nonneg_right (by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
        have := mul_le_mul_of_nonneg_left hα1 (hCth_nn 0).2.2.1; rw [mul_one] at this
        exact mul_le_mul_of_nonneg_right this (sq_nonneg τ₁)) hmin_nn)
    have t4' : |fctThetaD (v1Base kind c τ₁) t| ≤ Cth1b 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) :=
      t4.trans (mul_le_mul_of_nonneg_right (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1b (hCth_nn 0).2.2.2.1) hmin_nn)
    have t5' : |fctThetaD (v1Marg c τ₁) t| ≤ Cth1m 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) :=
      t5.trans (mul_le_mul_of_nonneg_right (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1m (hCth_nn 0).2.2.2.2) hmin_nn)
    rw [hθ_lin]
    have a1 := abs_add_le ((fctThetaD (v0Base kind τ₁) t + K4 * fctThetaD (v0Marg τ₁) t) +
      (fctThetaD (v1Base kind c τ₁) t + K4 * fctThetaD (v1Marg c τ₁) t)) (fctThetaD (vAlpha α τ₁) t)
    have a2 := abs_add_le (fctThetaD (v0Base kind τ₁) t + K4 * fctThetaD (v0Marg τ₁) t)
      (fctThetaD (v1Base kind c τ₁) t + K4 * fctThetaD (v1Marg c τ₁) t)
    have a3 := abs_add_le (fctThetaD (v0Base kind τ₁) t) (K4 * fctThetaD (v0Marg τ₁) t)
    have a4 := abs_add_le (fctThetaD (v1Base kind c τ₁) t) (K4 * fctThetaD (v1Marg c τ₁) t)
    rw [abs_mul, abs_of_nonneg hK4_nn] at a3 a4
    have hm1 := mul_le_mul_of_nonneg_left t2' hK4_nn
    have hm2 := mul_le_mul_of_nonneg_left t5' hK4_nn
    calc |fctThetaD (v0Base kind τ₁) t + K4 * fctThetaD (v0Marg τ₁) t +
            (fctThetaD (v1Base kind c τ₁) t + K4 * fctThetaD (v1Marg c τ₁) t) + fctThetaD (vAlpha α τ₁) t|
        ≤ |fctThetaD (v0Base kind τ₁) t| + K4 * |fctThetaD (v0Marg τ₁) t| +
            |fctThetaD (v1Base kind c τ₁) t| + K4 * |fctThetaD (v1Marg c τ₁) t| + |fctThetaD (vAlpha α τ₁) t| := by linarith
      _ ≤ Cth0b 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) + K4 * (Cth0m 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11)) +
            Cth1b 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) + K4 * (Cth1m 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11)) +
            Ctha 0 * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) :=
          add_le_add (add_le_add (add_le_add (add_le_add t1' hm1) t4') hm2) t3'
      _ = M_th0_in * τ₁ ^ 2 * min 1 ((|t| / τ₁) ^ 11) := by dsimp only [M_th0_in]; ring
  have hθ_tail_le : ∀ t : ℝ, 12 * τ₁ ≤ |t| →
      |fctThetaD v t| ≤ M_th0_tail * τ₁ ^ 3 * |t|⁻¹ * Real.exp (-(π / 2) * |t|) := by
    intro t ht
    obtain ⟨t0, t1, ta⟩ := hth_tail 0 t ht
    simp only [iteratedDeriv_zero, Nat.cast_zero, add_zero, zpow_neg_one] at t0 t1 ta
    have hc_inv : c⁻¹ ≤ τ₁ ^ 3 := by
      have : c⁻¹ = τ₁ ^ 4 := by rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
      rw [this]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have hα1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
    have hfac_nn : 0 ≤ |t|⁻¹ * Real.exp (-(π / 2) * |t|) := mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (Real.exp_pos _).le
    have hθ_lin : fctThetaD v t = fctThetaD (v0 kind K4 τ₁) t + fctThetaD (v1 kind K4 c τ₁) t + fctThetaD (vAlpha α τ₁) t := by
      obtain ⟨⟨hb0_cd, hm0_cd, ha0_cd, hb1_cd, hm1_cd, _⟩, _, _, ⟨hb0_s, hm0_s, ha0_s, hb1_s, hm1_s, _⟩, _⟩ :=
        hpart1 hK4 hc hτ₁ hτ₁_le hc_eq hα_le
      have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) (v0 kind K4 τ₁) := hb0_cd.add (contDiff_const.mul hm0_cd)
      have hv1_cd : ContDiff ℝ (⊤ : ℕ∞) (v1 kind K4 c τ₁) := hb1_cd.add (contDiff_const.mul hm1_cd)
      have hv0_cs : HasCompactSupport (v0 kind K4 τ₁) :=
        (hasCompactSupport_of_support_Ioo hb0_s).add (hasCompactSupport_of_support_Ioo hm0_s).mul_left
      have hv1_cs : HasCompactSupport (v1 kind K4 c τ₁) :=
        (hasCompactSupport_of_support_Ioo hb1_s).add (hasCompactSupport_of_support_Ioo hm1_s).mul_left
      have ha0_cs := hasCompactSupport_of_support_Ioo ha0_s
      have e01 : fctThetaD (fun s => v0 kind K4 τ₁ s + v1 kind K4 c τ₁ s) t =
          fctThetaD (v0 kind K4 τ₁) t + fctThetaD (v1 kind K4 c τ₁) t := by
        simpa only [one_mul] using fctThetaD_linear hv0_cd hv0_cs hv1_cd hv1_cs 1 1 t
      have eall : fctThetaD v t = fctThetaD (fun s => v0 kind K4 τ₁ s + v1 kind K4 c τ₁ s) t + fctThetaD (vAlpha α τ₁) t := by
        dsimp only [v]; unfold vTotal
        simpa only [one_mul] using fctThetaD_linear (hv0_cd.add hv1_cd) (hv0_cs.add hv1_cs) ha0_cd ha0_cs 1 1 t
      rw [eall, e01]
    have t1' : |fctThetaD (v1 kind K4 c τ₁) t| ≤
        C_tail 0 * (CL1_1b + K4 * CL1_1m) * τ₁ ^ 3 * |t|⁻¹ * Real.exp (-(π / 2) * |t|) := by
      refine t1.trans ?_
      have h1 : C_tail 0 * (CL1_1b + K4 * CL1_1m) * c⁻¹ ≤ C_tail 0 * (CL1_1b + K4 * CL1_1m) * τ₁ ^ 3 := by
        have := (hCti_nn 0).1; rcases hCL1_nn with ⟨_, _, _, h4, h5⟩
        exact mul_le_mul_of_nonneg_left hc_inv (by positivity)
      rw [mul_assoc (C_tail 0 * _ * c⁻¹), mul_assoc (C_tail 0 * _ * τ₁ ^ 3)]
      exact mul_le_mul_of_nonneg_right h1 hfac_nn
    have ta' : |fctThetaD (vAlpha α τ₁) t| ≤
        C_tail 0 * CL1_a * τ₁ ^ 3 * |t|⁻¹ * Real.exp (-(π / 2) * |t|) := by
      refine ta.trans ?_
      have h1 : C_tail 0 * CL1_a * |α| ≤ C_tail 0 * CL1_a := by
        have := (hCti_nn 0).1; rcases hCL1_nn with ⟨_, _, h3, _, _⟩
        have := mul_le_mul_of_nonneg_left hα1 (mul_nonneg this h3); rwa [mul_one] at this
      have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hτ₁.le 3)
      rw [mul_assoc (C_tail 0 * CL1_a * |α| * τ₁ ^ 3), mul_assoc (C_tail 0 * CL1_a * τ₁ ^ 3)]
      exact mul_le_mul_of_nonneg_right h2 hfac_nn
    rw [hθ_lin]
    calc |fctThetaD (v0 kind K4 τ₁) t + fctThetaD (v1 kind K4 c τ₁) t + fctThetaD (vAlpha α τ₁) t|
        ≤ |fctThetaD (v0 kind K4 τ₁) t| + |fctThetaD (v1 kind K4 c τ₁) t| + |fctThetaD (vAlpha α τ₁) t| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ C_tail 0 * (CL1_0b + K4 * CL1_0m) * τ₁ ^ 3 * |t|⁻¹ * Real.exp (-(π / 2) * |t|) +
            C_tail 0 * (CL1_1b + K4 * CL1_1m) * τ₁ ^ 3 * |t|⁻¹ * Real.exp (-(π / 2) * |t|) +
            C_tail 0 * CL1_a * τ₁ ^ 3 * |t|⁻¹ * Real.exp (-(π / 2) * |t|) :=
          add_le_add (add_le_add t0 t1') ta'
      _ = M_th0_tail * τ₁ ^ 3 * |t|⁻¹ * Real.exp (-(π / 2) * |t|) := by dsimp only [M_th0_tail, M_L1]; ring
  -- Step 1: Bound the cosine penalty integral `I_cos := α_osc ∫_0^∞ |H_0(it)| e^{v(t)} (1 - cos ϑ_D(t)) dt`
  let f_cos : ℝ → ℝ := fun t => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
    Real.exp (v t) * (1 - Real.cos (fctThetaD v t))
  have hf_cos_nn : ∀ t : ℝ, 0 < t → 0 ≤ f_cos t := fun t _ => by
    have hαo : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hαo (norm_nonneg _)) (Real.exp_pos _).le) (one_sub_cos_le_half_sq _).1
  have hf_cos_cont : ContinuousOn f_cos (Ioi 0) := by
    have hH_cont : ContinuousOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖) (Ioi 0) := by
      cases kind
      · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_star_imag ht
        refine (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
          ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
          fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')).add
          (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_cosh.comp
            ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
            fun t _ => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne'))
      · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_ce_imag ht
        exact continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
          ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
          fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (by have : 0 < t := ht; positivity)).ne')
    exact (((continuousOn_const.mul hH_cont).mul (Real.continuous_exp.comp hv_cd.continuous).continuousOn).mul
      (continuousOn_const.sub (Real.continuous_cos.comp hθ_cd.continuous).continuousOn))
  -- Integrability & bound on `Ioc 0 (12 τ₁)` and `Ioi (12 τ₁)`
  have hcos_in : IntegrableOn f_cos (Ioc 0 (12 * τ₁)) ∧
      (∫ t in Ioc 0 (12 * τ₁), f_cos t) ≤ C_cos_in * τ₁ ^ 3 := by
    have hαo : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
    have hpt : ∀ t ∈ Ioc (0 : ℝ) (12 * τ₁), ‖f_cos t‖ ≤
        uctAlphaOsc * (1 + π ^ 2 / 4) * Real.exp M_v0 * (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by
      intro t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_cos_nn t ht.1)]
      have hH := (norm_stripH0_imag_le kind ht.1).1
      have hexp := hv_exp_le t
      have hθ := hθ_in_le t (by rw [abs_of_pos ht.1]; exact ht.2)
      -- Split `t ≤ τ₁` (use `(t/τ₁)^11`) vs `τ₁ < t ≤ 12 τ₁` (use `1`, and `1/t² ≤ 1/τ₁²`)!
      have h1sub : (1 - Real.cos (fctThetaD v t)) / t ^ 2 ≤ (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by
        have hcos2 := (one_sub_cos_le_half_sq (fctThetaD v t)).2
        rcases le_or_gt t τ₁ with ht_le | ht_gt
        · have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 11) ≤ (t / τ₁) ^ 11 := by
            rw [abs_of_pos ht.1]; exact min_le_right _ _
          have hθ' : |fctThetaD v t| ≤ M_th0_in * τ₁ ^ 2 * (t / τ₁) ^ 11 :=
            hθ.trans (mul_le_mul_of_nonneg_left hmin (by positivity))
          have hsq : fctThetaD v t ^ 2 ≤ (M_th0_in * τ₁ ^ 2 * (t / τ₁) ^ 11) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ' 2
          have hrat : (t / τ₁) ^ 20 ≤ 1 := pow_le_one₀ (div_nonneg ht.1.le hτ₁.le) ((div_le_one hτ₁).mpr ht_le)
          rw [div_le_iff₀ (sq_pos_of_pos ht.1)]
          calc 1 - Real.cos (fctThetaD v t) ≤ fctThetaD v t ^ 2 / 2 := hcos2
            _ ≤ (M_th0_in * τ₁ ^ 2 * (t / τ₁) ^ 11) ^ 2 / 2 := by linarith
            _ = (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 * t ^ 2 * (t / τ₁) ^ 20 := by field_simp [hτ₁.ne']
            _ ≤ (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 * t ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left hrat (by positivity)
            _ = (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 * t ^ 2 := mul_one _
        · have hθ' : |fctThetaD v t| ≤ M_th0_in * τ₁ ^ 2 :=
            hθ.trans (mul_le_of_le_one_right (by positivity) (min_le_left _ _))
          have hsq : fctThetaD v t ^ 2 ≤ (M_th0_in * τ₁ ^ 2) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ' 2
          have ht2 : τ₁ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hτ₁.le ht_gt.le 2
          have hsq2 : fctThetaD v t ^ 2 / 2 ≤ (M_th0_in * τ₁ ^ 2) ^ 2 / 2 := by linarith
          calc (1 - Real.cos (fctThetaD v t)) / t ^ 2
              ≤ (fctThetaD v t ^ 2 / 2) / t ^ 2 := div_le_div_of_nonneg_right hcos2 (sq_nonneg t)
            _ ≤ ((M_th0_in * τ₁ ^ 2) ^ 2 / 2) / t ^ 2 := div_le_div_of_nonneg_right hsq2 (sq_nonneg t)
            _ ≤ ((M_th0_in * τ₁ ^ 2) ^ 2 / 2) / τ₁ ^ 2 := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hτ₁) ht2
            _ = (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by field_simp [hτ₁.ne']
      dsimp only [f_cos]
      calc uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * Real.exp (v t) * (1 - Real.cos (fctThetaD v t))
          ≤ uctAlphaOsc * ((1 + π ^ 2 / 4) / t ^ 2) * Real.exp M_v0 * (1 - Real.cos (fctThetaD v t)) := by
            gcongr
            exact (one_sub_cos_le_half_sq _).1
        _ = uctAlphaOsc * (1 + π ^ 2 / 4) * Real.exp M_v0 * ((1 - Real.cos (fctThetaD v t)) / t ^ 2) := by ring
        _ ≤ uctAlphaOsc * (1 + π ^ 2 / 4) * Real.exp M_v0 * ((1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2) :=
            mul_le_mul_of_nonneg_left h1sub (by positivity)
        _ = uctAlphaOsc * (1 + π ^ 2 / 4) * Real.exp M_v0 * (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by ring
    have hint : IntegrableOn f_cos (Ioc 0 (12 * τ₁)) :=
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
        ((hf_cos_cont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
    refine ⟨hint, ?_⟩
    have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hpt
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun t ht => hf_cos_nn t ht.1),
      Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)] at hbd
    refine hbd.trans (le_of_eq ?_); dsimp only [C_cos_in]; ring
  have hcos_tail : IntegrableOn f_cos (Ioi (12 * τ₁)) ∧
      (∫ t in Ioi (12 * τ₁), f_cos t) ≤ C_cos_tail * τ₁ ^ 3 := by
    have hαo : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
    have hdom_int := FctPhiKill.integrableOn_inv_pow_Ioi (ε := 12 * τ₁) (by positivity) (m := 4) (by norm_num)
    set K_t : ℝ := uctAlphaOsc * (1 + π ^ 2 / 4) * (1 / 2) * M_th0_tail ^ 2 * τ₁ ^ 6
    have hpt : ∀ t ∈ Ioi (12 * τ₁), ‖f_cos t‖ ≤ K_t * t ^ (-(4 : ℤ)) := by
      intro t ht
      have ht0 : 0 < t := lt_trans (by positivity) ht
      have hvt : v t = 0 := by
        by_contra hne
        have h := (hv_supp hne).2
        linarith [show 12 * τ₁ < t from ht]
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_cos_nn t ht0)]
      have hH := (norm_stripH0_imag_le kind ht0).1
      have hθ := hθ_tail_le t (by rw [abs_of_pos ht0]; exact le_of_lt ht)
      rw [abs_of_pos ht0] at hθ
      have hexp1 : Real.exp (-(π / 2) * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) ht0.le)
      have hθ' : |fctThetaD v t| ≤ M_th0_tail * τ₁ ^ 3 * t⁻¹ :=
        hθ.trans (mul_le_of_le_one_right (by positivity) hexp1)
      have hcos2 : 1 - Real.cos (fctThetaD v t) ≤ (1 / 2) * (M_th0_tail * τ₁ ^ 3 * t⁻¹) ^ 2 := by
        have hsq : fctThetaD v t ^ 2 ≤ (M_th0_tail * τ₁ ^ 3 * t⁻¹) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ' 2
        linarith [(one_sub_cos_le_half_sq (fctThetaD v t)).2]
      dsimp only [f_cos, K_t]
      rw [hvt, Real.exp_zero, mul_one, zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]
      calc uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (1 - Real.cos (fctThetaD v t))
          ≤ uctAlphaOsc * ((1 + π ^ 2 / 4) / t ^ 2) * ((1 / 2) * (M_th0_tail * τ₁ ^ 3 * t⁻¹) ^ 2) := by
            gcongr
            exact (one_sub_cos_le_half_sq _).1
        _ = uctAlphaOsc * (1 + π ^ 2 / 4) * (1 / 2) * M_th0_tail ^ 2 * τ₁ ^ 6 * (t ^ 4)⁻¹ := by
            field_simp [ht0.ne']
    have hint : IntegrableOn f_cos (Ioi (12 * τ₁)) :=
      (hdom_int.1.const_mul K_t).mono'
        ((hf_cos_cont.mono (fun t ht => lt_trans (by positivity) ht)).aestronglyMeasurable measurableSet_Ioi)
        (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
    refine ⟨hint, ?_⟩
    have hmono : (∫ t in Ioi (12 * τ₁), f_cos t) ≤ ∫ t in Ioi (12 * τ₁), K_t * t ^ (-(4 : ℤ)) :=
      setIntegral_mono_on hint (hdom_int.1.const_mul K_t) measurableSet_Ioi fun t ht => by
        have h := hpt t ht
        rwa [Real.norm_eq_abs, abs_of_nonneg (hf_cos_nn t (lt_trans (by positivity) ht))] at h
    have hdom_eq : (∫ t in Ioi (12 * τ₁), t ^ (-(4 : ℤ))) = (12 * τ₁) ^ (1 - (4 : ℤ)) / ((4 : ℝ) - 1) := by
      simpa using hdom_int.2
    rw [integral_const_mul, hdom_eq] at hmono
    refine hmono.trans ?_
    have hval : K_t * ((12 * τ₁) ^ (1 - (4 : ℤ)) / ((4 : ℝ) - 1)) =
        (1 / 3) * (C_cos_tail * τ₁ ^ 3) := by
      dsimp only [K_t, C_cos_tail]
      rw [show (1 : ℤ) - 4 = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
      field_simp [hτ₁.ne']; ring
    rw [hval]; linarith [show 0 ≤ C_cos_tail * τ₁ ^ 3 by positivity]
  have hcos_all_int : IntegrableOn f_cos (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 12 * τ₁ by positivity), integrableOn_union]
    exact ⟨hcos_in.1, hcos_tail.1⟩
  have hcos_all_bd : 0 ≤ (∫ t in Ioi (0 : ℝ), f_cos t) ∧
      (∫ t in Ioi (0 : ℝ), f_cos t) ≤ (C_cos_in + C_cos_tail) * τ₁ ^ 3 := by
    refine ⟨setIntegral_nonneg measurableSet_Ioi fun t ht => hf_cos_nn t ht, ?_⟩
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 12 * τ₁ by positivity),
      setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
        measurableSet_Ioi hcos_in.1 hcos_tail.1]
    linarith [hcos_in.2, hcos_tail.2]
  -- Step 2: Combine contour identity + `uct_strip_split_integrals`!
  have hcont_id := contour_H0_exp_sub_one kind hv_cd hv_cs hv_even hv0 hθ1 hMg0_nn hMg2_nn hg0_bd hg2_bd
  have hsplit := uct_strip_split_integrals
  -- `∫_0^∞ (I_osc^{H_0}(L) - I_fl(L)) dL = stripCfl kind`
  have hbase_int : IntegrableOn (fun L : ℝ => stripIosc kind L - uctIfl L) (Ioi 0) ∧
      (∫ L in Ioi (0 : ℝ), (stripIosc kind L - uctIfl L)) = stripCfl kind := by
    cases kind
    · exact ⟨hsplit.1.1, hsplit.1.2⟩
    · exact ⟨hsplit.2.1.1, hsplit.2.1.2⟩
  -- `I_osc^{DH_0}(L) - I_fl(L) = (I_osc^{H_0}(L) - I_fl(L)) + I_osc^{H_0}(L) (e^{v(τ₀(L))} - 1)`
  have hdiff_t_int : IntegrableOn (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1)) (Ioi 0) := by
    have hrew : (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1)) =
        fun t : ℝ => uctAlphaOsc * (‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) +
                 f_cos t := by
      ext t; dsimp only [f_cos]; ring
    rw [hrew]
    exact (hcont_id.1.const_mul uctAlphaOsc).add hcos_all_int
  have hdiff_L_int : IntegrableOn (fun L : ℝ => stripIoscD kind v L - stripIosc kind L) (Ioi 0) := by
    rw [uct_subst_integrableOn_zero]
    refine hdiff_t_int.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [mul_sub, uctMderiv_mul_stripIoscD kind v ht, uctMderiv_mul_stripIosc kind ht]; ring
  have htotal_int : IntegrableOn (fun L : ℝ => stripIoscD kind v L - uctIfl L) (Ioi 0) := by
    have hrew : (fun L : ℝ => stripIoscD kind v L - uctIfl L) =
        fun L => (stripIosc kind L - uctIfl L) + (stripIoscD kind v L - stripIosc kind L) := by
      ext L; ring
    rw [hrew]; exact hbase_int.1.add hdiff_L_int
  have htotal_eq : (∫ L in Ioi (0 : ℝ), (stripIoscD kind v L - uctIfl L)) - stripCfl kind =
      uctAlphaOsc * (∫ t in Ioi (0 : ℝ), ‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
        (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) +
      ∫ t in Ioi (0 : ℝ), f_cos t := by
    have hrew : (fun L : ℝ => stripIoscD kind v L - uctIfl L) =
        fun L => (stripIosc kind L - uctIfl L) + (stripIoscD kind v L - stripIosc kind L) := by
      ext L; ring
    rw [hrew, integral_add hbase_int.1 hdiff_L_int, hbase_int.2, add_sub_cancel_left, uct_subst_zero]
    have hsub : (∫ t in Ioi (0 : ℝ), uctMderiv t * (stripIoscD kind v (uctM t) - stripIosc kind (uctM t))) =
        ∫ t in Ioi (0 : ℝ), uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        rw [mul_sub, uctMderiv_mul_stripIoscD kind v ht, uctMderiv_mul_stripIosc kind ht]; ring
    rw [hsub]
    have hsplit_t : (fun t : ℝ => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1)) =
        fun t : ℝ => uctAlphaOsc * (‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)) +
                 f_cos t := by
      ext t; dsimp only [f_cos]; ring
    rw [hsplit_t, integral_add (hcont_id.1.const_mul uctAlphaOsc) hcos_all_int, integral_const_mul]
  refine ⟨htotal_int, hcos_all_int, ?_, ?_⟩
  · -- Bound `|∫ (I_osc^{DH_0} - I_fl) - C_fl(H_0)| ≤ C_tot * τ₁^3`
    rw [htotal_eq]
    cases kind
    · -- `H_*`: contour term is `0`!
      rw [hcont_id.2, mul_zero, zero_add, abs_of_nonneg hcos_all_bd.1]
      have hαo : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
      have : 0 ≤ (C_ce_in + C_ce_tail) * τ₁ ^ 3 := by positivity
      linarith [hcos_all_bd.2]
    · -- `H_CE`: contour term is `-α_osc ∫_0^∞ (π²/(4 cosh²(πt/2))) (e^{v(t)} cos ϑ_D(t) - 1) dt = O(τ₁^3)`!
      rw [hcont_id.2.2]
      let g_ce : ℝ → ℝ := fun t => (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) *
        (Real.exp (v t) * Real.cos (fctThetaD v t) - 1)
      have hg_int : IntegrableOn g_ce (Ioi 0) := hcont_id.2.1
      -- Split `Ioi 0 = Ioc 0 (10 τ₁) ∪ Ioc (10 τ₁) (12 τ₁) ∪ Ioi (12 τ₁)`
      have hg_in : |∫ t in Ioc 0 (10 * τ₁), g_ce t| ≤ (π ^ 2 / 4) * (Real.exp M_v0 * M_v0 + (1 / 2) * M_th0_in ^ 2) * 10 * τ₁ ^ 3 := by
        have hpt : ∀ t ∈ Ioc (0 : ℝ) (10 * τ₁), ‖g_ce t‖ ≤
            (π ^ 2 / 4) * (Real.exp M_v0 * M_v0 + (1 / 2) * M_th0_in ^ 2) * τ₁ ^ 2 := by
          intro t ht
          have hch : π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) ≤ π ^ 2 / 4 := by
            have hsq : (1 : ℝ) ≤ Real.cosh (π * t / 2) ^ 2 := one_le_pow₀ (Real.one_le_cosh _)
            exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
          have hdiff : |Real.exp (v t) * Real.cos (fctThetaD v t) - 1| ≤
              (Real.exp M_v0 * M_v0 + (1 / 2) * M_th0_in ^ 2) * τ₁ ^ 2 := by
            have hrew : Real.exp (v t) * Real.cos (fctThetaD v t) - 1 =
                (Real.exp (v t) - 1) * Real.cos (fctThetaD v t) - (1 - Real.cos (fctThetaD v t)) := by ring
            rw [hrew]
            have hexp1 : |Real.exp (v t) - 1| ≤ Real.exp M_v0 * (M_v0 * τ₁ ^ 2) := by
              have h1 := norm_cexp_sub_one_le (w := (v t : ℂ)) (M := M_v0) (by
                rw [Complex.norm_real, Real.norm_eq_abs]
                exact (hv_abs_le t).trans (mul_le_of_le_one_right hMv0_nn (pow_le_one₀ hτ₁.le hτ₁_1)))
              rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
                Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h1
              exact h1.trans (mul_le_mul_of_nonneg_left (hv_abs_le t) (Real.exp_pos _).le)
            have hcos1 : |1 - Real.cos (fctThetaD v t)| ≤ (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by
              rw [abs_of_nonneg (one_sub_cos_le_half_sq _).1]
              have hθ := (hθ_in_le t (by rw [abs_of_pos ht.1]; linarith [ht.2])).trans
                (mul_le_of_le_one_right (by positivity) (min_le_left _ _))
              have hsq : fctThetaD v t ^ 2 ≤ (M_th0_in * τ₁ ^ 2) ^ 2 := by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
              have hτ4 : τ₁ ^ 4 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
              calc 1 - Real.cos (fctThetaD v t) ≤ fctThetaD v t ^ 2 / 2 := (one_sub_cos_le_half_sq _).2
                _ ≤ (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 4 := by
                    linarith [show (M_th0_in * τ₁ ^ 2) ^ 2 = M_th0_in ^ 2 * τ₁ ^ 4 by ring]
                _ ≤ (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := mul_le_mul_of_nonneg_left hτ4 (by positivity)
            calc |(Real.exp (v t) - 1) * Real.cos (fctThetaD v t) - (1 - Real.cos (fctThetaD v t))|
                ≤ |(Real.exp (v t) - 1) * Real.cos (fctThetaD v t)| + |1 - Real.cos (fctThetaD v t)| := abs_sub _ _
              _ ≤ |Real.exp (v t) - 1| * 1 + |1 - Real.cos (fctThetaD v t)| := by
                  rw [abs_mul]; gcongr; exact Real.abs_cos_le_one _
              _ ≤ Real.exp M_v0 * (M_v0 * τ₁ ^ 2) + (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by linarith
              _ = (Real.exp M_v0 * M_v0 + (1 / 2) * M_th0_in ^ 2) * τ₁ ^ 2 := by ring
          dsimp only [g_ce]; rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
          calc (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) * |Real.exp (v t) * Real.cos (fctThetaD v t) - 1|
              ≤ (π ^ 2 / 4) * ((Real.exp M_v0 * M_v0 + (1 / 2) * M_th0_in ^ 2) * τ₁ ^ 2) :=
                mul_le_mul hch hdiff (abs_nonneg _) (by positivity)
            _ = (π ^ 2 / 4) * (Real.exp M_v0 * M_v0 + (1 / 2) * M_th0_in ^ 2) * τ₁ ^ 2 := by ring
        have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hpt
        rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)] at hbd
        refine hbd.trans (le_of_eq ?_); ring
      have hg_mid : |∫ t in Ioc (10 * τ₁) (12 * τ₁), g_ce t| ≤ (π ^ 2 / 4) * (1 / 2) * M_th0_in ^ 2 * 2 * τ₁ ^ 3 := by
        have hpt : ∀ t ∈ Ioc (10 * τ₁) (12 * τ₁), ‖g_ce t‖ ≤ (π ^ 2 / 4) * (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by
          intro t ht
          have hvt : v t = 0 := by by_contra hne; linarith [(hv_supp hne).2, ht.1]
          have hch : π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) ≤ π ^ 2 / 4 := by
            have hsq : (1 : ℝ) ≤ Real.cosh (π * t / 2) ^ 2 := one_le_pow₀ (Real.one_le_cosh _)
            exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
          have hθ := (hθ_in_le t (by rw [abs_of_pos (lt_trans (by positivity) ht.1)]; exact ht.2)).trans
            (mul_le_of_le_one_right (by positivity) (min_le_left _ _))
          have hcos1 : |Real.cos (fctThetaD v t) - 1| ≤ (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by
            rw [abs_sub_comm, abs_of_nonneg (one_sub_cos_le_half_sq _).1]
            have hsq : fctThetaD v t ^ 2 ≤ (M_th0_in * τ₁ ^ 2) ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ 2
            have hτ4 : τ₁ ^ 4 ≤ τ₁ ^ 2 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
            calc 1 - Real.cos (fctThetaD v t) ≤ fctThetaD v t ^ 2 / 2 := (one_sub_cos_le_half_sq _).2
              _ ≤ (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 4 := by
                  linarith [show (M_th0_in * τ₁ ^ 2) ^ 2 = M_th0_in ^ 2 * τ₁ ^ 4 by ring]
              _ ≤ (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := mul_le_mul_of_nonneg_left hτ4 (by positivity)
          dsimp only [g_ce]; rw [hvt, Real.exp_zero, one_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
          calc (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) * |Real.cos (fctThetaD v t) - 1|
              ≤ (π ^ 2 / 4) * ((1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2) := mul_le_mul hch hcos1 (abs_nonneg _) (by positivity)
            _ = (π ^ 2 / 4) * (1 / 2) * M_th0_in ^ 2 * τ₁ ^ 2 := by ring
        have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hpt
        rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)] at hbd
        refine hbd.trans (le_of_eq ?_); ring
      have hg_tail : |∫ t in Ioi (12 * τ₁), g_ce t| ≤ (π ^ 2 / 4) * (1 / 2) * M_th0_tail ^ 2 * (1 / 12) * τ₁ ^ 3 := by
        have hdom_int := FctPhiKill.integrableOn_inv_pow_Ioi (ε := 12 * τ₁) (by positivity) (m := 2) (by norm_num)
        set K_g : ℝ := (π ^ 2 / 4) * (1 / 2) * M_th0_tail ^ 2 * τ₁ ^ 6
        have hpt : ∀ t ∈ Ioi (12 * τ₁), ‖g_ce t‖ ≤ K_g * t ^ (-(2 : ℤ)) := by
          intro t ht
          have ht0 : 0 < t := lt_trans (by positivity) ht
          have hvt : v t = 0 := by by_contra hne; linarith [(hv_supp hne).2, show 12 * τ₁ < t from ht]
          have hch : π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2) ≤ π ^ 2 / 4 := by
            have hsq : (1 : ℝ) ≤ Real.cosh (π * t / 2) ^ 2 := one_le_pow₀ (Real.one_le_cosh _)
            exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
          have hθ := hθ_tail_le t (by rw [abs_of_pos ht0]; exact le_of_lt ht)
          rw [abs_of_pos ht0] at hθ
          have hθ' : |fctThetaD v t| ≤ M_th0_tail * τ₁ ^ 3 * t⁻¹ :=
            hθ.trans (mul_le_of_le_one_right (by positivity)
              (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) ht0.le)))
          have hcos1 : |Real.cos (fctThetaD v t) - 1| ≤ (1 / 2) * (M_th0_tail * τ₁ ^ 3 * t⁻¹) ^ 2 := by
            rw [abs_sub_comm, abs_of_nonneg (one_sub_cos_le_half_sq _).1]
            have hsq : fctThetaD v t ^ 2 ≤ (M_th0_tail * τ₁ ^ 3 * t⁻¹) ^ 2 := by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hθ' 2
            linarith [(one_sub_cos_le_half_sq (fctThetaD v t)).2]
          dsimp only [g_ce, K_g]
          rw [hvt, Real.exp_zero, one_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity),
            zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
          calc (π ^ 2 / (4 * Real.cosh (π * t / 2) ^ 2)) * |Real.cos (fctThetaD v t) - 1|
              ≤ (π ^ 2 / 4) * ((1 / 2) * (M_th0_tail * τ₁ ^ 3 * t⁻¹) ^ 2) := mul_le_mul hch hcos1 (abs_nonneg _) (by positivity)
            _ = (π ^ 2 / 4) * (1 / 2) * M_th0_tail ^ 2 * τ₁ ^ 6 * (t ^ 2)⁻¹ := by field_simp [ht0.ne']
        have h1 : |∫ t in Ioi (12 * τ₁), g_ce t| ≤ ∫ t in Ioi (12 * τ₁), K_g * t ^ (-(2 : ℤ)) :=
          (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
            (hg_int.mono_set (fun t ht => lt_trans (by positivity) ht)).norm
            (hdom_int.1.const_mul K_g) measurableSet_Ioi hpt)
        have hdom_eq : (∫ t in Ioi (12 * τ₁), t ^ (-(2 : ℤ))) = (12 * τ₁) ^ (1 - (2 : ℤ)) / ((2 : ℝ) - 1) := by
          simpa using hdom_int.2
        rw [integral_const_mul, hdom_eq] at h1
        refine h1.trans ?_
        have hval : K_g * ((12 * τ₁) ^ (1 - (2 : ℤ)) / ((2 : ℝ) - 1)) =
            (π ^ 2 / 4) * (1 / 2) * M_th0_tail ^ 2 * (1 / 12) * τ₁ ^ 5 := by
          dsimp only [K_g]; rw [show (1 : ℤ) - 2 = -1 by norm_num, zpow_neg_one]; field_simp [hτ₁.ne']; ring
        rw [hval]
        have hτ5 : τ₁ ^ 5 ≤ τ₁ ^ 3 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
        exact mul_le_mul_of_nonneg_left hτ5 (by positivity)
      have hg_split : (∫ t in Ioi (0 : ℝ), g_ce t) =
          (∫ t in Ioc 0 (10 * τ₁), g_ce t) + (∫ t in Ioc (10 * τ₁) (12 * τ₁), g_ce t) + ∫ t in Ioi (12 * τ₁), g_ce t := by
        have h12 : Ioi (0 : ℝ) = Ioc 0 (12 * τ₁) ∪ Ioi (12 * τ₁) := (Ioc_union_Ioi_eq_Ioi (by positivity)).symm
        have h10 : Ioc (0 : ℝ) (12 * τ₁) = Ioc 0 (10 * τ₁) ∪ Ioc (10 * τ₁) (12 * τ₁) :=
          (Ioc_union_Ioc_eq_Ioc (by positivity) (by linarith)).symm
        rw [h12, setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
            measurableSet_Ioi (hg_int.mono_set Ioc_subset_Ioi_self) (hg_int.mono_set fun x hx => lt_trans (by positivity) hx),
          h10, setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1])
            measurableSet_Ioc (hg_int.mono_set Ioc_subset_Ioi_self)
            (hg_int.mono_set fun x hx => lt_trans (by positivity) hx.1)]
      have hαo : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
      have hce_all : uctAlphaOsc * |∫ t in Ioi (0 : ℝ), g_ce t| ≤ (C_ce_in + C_ce_tail) * τ₁ ^ 3 := by
        rw [hg_split]
        have htri : |(∫ t in Ioc 0 (10 * τ₁), g_ce t) + (∫ t in Ioc (10 * τ₁) (12 * τ₁), g_ce t) + ∫ t in Ioi (12 * τ₁), g_ce t| ≤
            |∫ t in Ioc 0 (10 * τ₁), g_ce t| + |∫ t in Ioc (10 * τ₁) (12 * τ₁), g_ce t| + |∫ t in Ioi (12 * τ₁), g_ce t| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        have hsum := mul_le_mul_of_nonneg_left (htri.trans (add_le_add (add_le_add hg_in hg_mid) hg_tail)) hαo
        refine hsum.trans (le_of_eq ?_); dsimp only [C_ce_in, C_ce_tail]; ring
      calc |uctAlphaOsc * -(∫ t in Ioi (0 : ℝ), g_ce t) + ∫ t in Ioi (0 : ℝ), f_cos t|
          ≤ |uctAlphaOsc * -(∫ t in Ioi (0 : ℝ), g_ce t)| + |∫ t in Ioi (0 : ℝ), f_cos t| := abs_add_le _ _
        _ = uctAlphaOsc * |∫ t in Ioi (0 : ℝ), g_ce t| + ∫ t in Ioi (0 : ℝ), f_cos t := by
            rw [abs_mul, abs_of_nonneg hαo, abs_neg, abs_of_nonneg hcos_all_bd.1]
        _ ≤ (C_ce_in + C_ce_tail) * τ₁ ^ 3 + (C_cos_in + C_cos_tail) * τ₁ ^ 3 := add_le_add hce_all hcos_all_bd.2
        _ = C_tot * τ₁ ^ 3 := by dsimp only [C_tot]; ring
  · -- Exact cosine identity for `H_*`
    intro hkind
    subst hkind
    rw [stripCfl, sub_zero, hcont_id.2, mul_zero, zero_add] at htotal_eq
    rw [htotal_eq, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by dsimp only [f_cos]; ring

/-! ### Part (2b): Curvature-paired `p`-th moment integrals `(fct:curv-p-int)` and `∫_0^∞ D_*(L) dL` -/

/-- Even smooth Taylor expansion on `(-1/4, 1/4)`: if `g` is `C^∞` and even on `(-1/4, 1/4)`,
then for every `n : ℕ` there are constants `a_0, ..., a_{n-1}` and `C ≥ 0` such that
`|g(t) - ∑_{j < n} a_j t^{2j}| ≤ C * t^{2n}` on `[0, 1/8]`. -/
lemma even_smooth_taylor_bound {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Ioo (-1 / 4) (1 / 4)))
    (heven : ∀ t, |t| < 1 / 4 → g (-t) = g t) (n : ℕ) :
    ∃ (a : Fin n → ℝ) (C : ℝ), 0 ≤ C ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 8), |g t - ∑ j : Fin n, a j * t ^ (2 * j.1)| ≤ C * t ^ (2 * n) := by
  -- Use `taylor_mean_remainder_bound` on `[0, 1/8]` and the fact that odd derivatives of `g` at `0` vanish!
  have hodd : ∀ k : ℕ, iteratedDeriv (2 * k + 1) g 0 = 0 := by
    intro k
    have hev : (fun x => g (-x)) =ᶠ[𝓝 (0 : ℝ)] g := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 4 by norm_num)] with x hx
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
      exact heven x hx
    have hneg : iteratedDeriv (2 * k + 1) (fun x => g (-x)) 0 = -iteratedDeriv (2 * k + 1) g 0 := by
      have h := iteratedDeriv_comp_neg (2 * k + 1) g 0
      simp only [neg_zero, Odd.neg_one_pow (by exact ⟨k, rfl⟩ : Odd (2 * k + 1)), neg_one_smul] at h
      exact h
    have h1 : iteratedDeriv (2 * k + 1) (fun x => g (-x)) 0 = iteratedDeriv (2 * k + 1) g 0 :=
      (hev.iteratedDeriv (2 * k + 1)).eq_of_nhds
    linarith
  have hcd_2n : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv (2 * n) g) (Ioo (-1 / 4) (1 / 4)) := by
    have hall : ∀ k : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k g) (Ioo (-1 / 4) (1 / 4)) := by
      intro k; induction k with
      | zero => simpa using hg
      | succ k ih =>
        rw [show iteratedDeriv (k + 1) g = deriv (iteratedDeriv k g) by ext x; rw [iteratedDeriv_succ]]
        exact ih.deriv_of_isOpen isOpen_Ioo (by simp)
    exact hall (2 * n)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_bound_of_continuousOn
    (hcd_2n.continuousOn.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  set C : ℝ := max B 0
  refine ⟨fun j => iteratedDeriv (2 * j.1) g 0 / ((2 * j.1).factorial : ℝ), C, by positivity, fun t ht => ?_⟩
  rcases eq_or_lt_of_le ht.1 with rfl | ht0
  · rcases n with _ | n
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, mul_zero, pow_zero, mul_one, C]
      have h0 : |g 0| ≤ B := by simpa [Real.norm_eq_abs, iteratedDeriv_zero] using hB 0 ⟨le_rfl, by norm_num⟩
      exact h0.trans (le_max_left _ _)
    · have hsum0 : ∑ j : Fin (n + 1), (iteratedDeriv (2 * j.1) g 0 / ((2 * j.1).factorial : ℝ)) * (0 : ℝ) ^ (2 * j.1) = g 0 := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, mul_zero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, mul_one]
        have hrest : ∑ j : Fin n, (iteratedDeriv (2 * (j.succ : ℕ)) g 0 / ((2 * (j.succ : ℕ)).factorial : ℝ)) * (0 : ℝ) ^ (2 * (j.succ : ℕ)) = 0 :=
          Finset.sum_eq_zero fun j _ => by rw [zero_pow (by simp)]; ring
        rw [hrest, add_zero]
      rw [hsum0, sub_self, abs_zero, zero_pow (by omega), mul_zero]
  · rcases n with _ | n
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, mul_zero, pow_zero, mul_one, C]
      have h0 : |g t| ≤ B := by simpa [Real.norm_eq_abs, iteratedDeriv_zero] using hB t ht
      exact h0.trans (le_max_left _ _)
    · have htay := taylor_mean_remainder_bound (f := g) (a := 0) (b := t) (x := t) (n := 2 * n + 1)
        (C := max B 0)
        ((hg.mono fun x hx => ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩).of_le
          (WithTop.coe_le_coe.mpr le_top))
        ⟨ht.1, le_rfl⟩
        (fun x hx => by
          rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
          have h1 : |iteratedDeriv (2 * (n + 1)) g x| ≤ B := by
            simpa [Real.norm_eq_abs] using hB x ⟨hx.1, hx.2.trans ht.2⟩
          have hrew : iteratedDerivWithin (2 * (n + 1)) g (Icc 0 t) x = iteratedDeriv (2 * (n + 1)) g x :=
            iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht0)
              ((hg.contDiffAt (isOpen_Ioo.mem_nhds ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩)).of_le
                (WithTop.coe_le_coe.mpr le_top)) hx
          rw [hrew, Real.norm_eq_abs]; exact h1.trans (le_max_left _ _))
      -- Show `taylorWithinEval g (2*n + 1) (Icc 0 t) 0 t = ∑ j : Fin (n+1), a j * t^{2j}`
      have htay_eq : taylorWithinEval g (2 * n + 1) (Icc 0 t) 0 t =
          ∑ j : Fin (n + 1), (iteratedDeriv (2 * j.1) g 0 / ((2 * j.1).factorial : ℝ)) * t ^ (2 * j.1) := by
        rw [taylor_within_apply]
        have hterm : ∀ k ∈ Finset.range (2 * n + 1 + 1),
            ((k.factorial : ℝ)⁻¹ * (t - 0) ^ k) • iteratedDerivWithin k g (Icc 0 t) 0 =
            (iteratedDeriv k g 0 / (k.factorial : ℝ)) * t ^ k := fun k _ => by
          rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht0)
            (hg.contDiffAt (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4))) |>.of_le (by simp))
            ⟨le_rfl, ht.1⟩, sub_zero, smul_eq_mul]
          ring
        rw [Finset.sum_congr rfl hterm]
        -- Group `range (2*n + 2)` into even `2*j` and odd `2*j + 1` (which vanish by `hodd`)
        have hsum_split : ∀ m : ℕ, (∑ k ∈ Finset.range (2 * m), (iteratedDeriv k g 0 / (k.factorial : ℝ)) * t ^ k) =
            ∑ j : Fin m, (iteratedDeriv (2 * j.1) g 0 / ((2 * j.1).factorial : ℝ)) * t ^ (2 * j.1) := by
          intro m; induction m with
          | zero => simp
          | succ m ih =>
            rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
              hodd m, zero_div, zero_mul, add_zero, ih, Fin.sum_univ_castSucc]; rfl
        simpa [show 2 * (n + 1) = 2 * n + 1 + 1 by omega] using hsum_split (n + 1)
      rw [htay_eq, Real.norm_eq_abs, sub_zero, show 2 * n + 1 + 1 = 2 * (n + 1) by omega] at htay
      refine htay.trans (div_le_self (by positivity) ?_)
      exact_mod_cast Nat.factorial_pos (2 * n + 1)

set_option maxHeartbeats 1600000 in
/-- **Part (2b) of `fct:comp-D`** (`(fct:curv-p-int)` for `p ∈ {0, 1, 2}` + cross-term bound +
second equation of `(fct:cos-pen)`):
For `p ∈ {0, 1, 2}`:
- `|∫_0^∞ I_osc^{H_0}(L) Δ_curv(τ₀(L)) / L^p dL| ≤ C(K₄) c⁻¹`;
- `∫_0^{10τ₁} (|H_0(it)| / m(t)^p) |e^{v(t)} - 1| |Δ_curv(t)| dt ≤ C(K₄) c⁻¹ τ₁^{-2p}`;
- at `p = 0`, `|∫_0^∞ D_*(L) dL - C_fl(H_0)| ≤ C(K₄) τ₁^3`. -/
theorem fct_comp_D_curv_p_int (kind : StripKernelChoice) :
    ∃ τ₀ > 0, τ₀ ≤ 1 / 20 ∧
      ∀ K4 : ℝ, 1 ≤ K4 → ∃ C ≥ 0,
        ∀ {c α τ₁ : ℝ}, 0 < c → 0 < τ₁ → τ₁ ≤ τ₀ → τ₁ ^ 4 * c = 1 → |α| ≤ τ₁ ^ 2 →
          let v := vTotal kind K4 c α τ₁
          let v0' := v0 kind K4 τ₁
          (∀ p : ℕ, p ≤ 2 →
            IntegrableOn (fun L : ℝ => stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L) / L ^ p) (Ioi 0) ∧
            |∫ L in Ioi (0 : ℝ), stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L) / L ^ p| ≤ C * c⁻¹ ∧
            IntegrableOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p *
              |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) (Ioc 0 (10 * τ₁)) ∧
            (∫ t in Ioc 0 (10 * τ₁), ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p *
              |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) ≤ C * c⁻¹ * τ₁ ^ (-(2 * (p : ℤ)))) ∧
          IntegrableOn (fun L : ℝ => stripDstar kind c v v0' L) (Ioi 0) ∧
          |(∫ L in Ioi (0 : ℝ), stripDstar kind c v v0' L) - stripCfl kind| ≤ C * τ₁ ^ 3 := by
  obtain ⟨τ₀_p1, hτ₀_p1_pos, hτ₀_p1_20, Cv0b, Cv0m, Cva, Cv1b, Cv1m,
    Cth0b, Cth0m, Ctha, Cth1b, Cth1m, CL1_0b, CL1_0m, CL1_a, CL1_1b, CL1_1m,
    C_tail, C_int, hCv_nn, hCth_nn, hCL1_nn, hCti_nn, hpart1⟩ := fct_comp_D_part1 kind
  obtain ⟨τ₀_cos, hτ₀_cos_pos, hτ₀_cos_20, hcos_pen⟩ := fct_comp_D_cos_penalty kind
  -- Cauchy curvature constants for `m = 1, 2, 3`
  obtain ⟨C_c1_1, hCc1_1_nn, hCc1_1⟩ := fct_cauchy_curv_first (m := 1) (by norm_num)
  obtain ⟨C_c1_2, hCc1_2_nn, hCc1_2⟩ := fct_cauchy_curv_first (m := 2) (by norm_num)
  obtain ⟨C_c1_3, hCc1_3_nn, hCc1_3⟩ := fct_cauchy_curv_first (m := 3) (by norm_num)
  obtain ⟨C_c2_1, hCc2_1_nn, hCc2_1⟩ := fct_cauchy_curv_second (m := 1) (by norm_num)
  obtain ⟨C_c2_2, hCc2_2_nn, hCc2_2⟩ := fct_cauchy_curv_second (m := 2) (by norm_num)
  obtain ⟨C_c2_3, hCc2_3_nn, hCc2_3⟩ := fct_cauchy_curv_second (m := 3) (by norm_num)
  -- Smooth factor `hFac(t) = t^2 |H_0(it)|` on `(-1/4, 1/4)`
  let hFac : ℝ → ℝ := fun t =>
    let sQ := (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re
    match kind with
    | .ce => 1 / sQ ^ 2
    | .star => 1 / sQ ^ 2 + (π * t / 2) ^ 2 / Real.cosh (π * t / 2) ^ 2
  have hhFac_cd : ContDiffOn ℝ (⊤ : ℕ∞) hFac (Ioo (-1 / 4) (1 / 4)) := by
    have hsQ_cd : ContDiffOn ℝ (⊤ : ℕ∞) (fun t : ℝ => (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re) (Ioo (-1 / 4) (1 / 4)) := by
      have hana : AnalyticOnNhd ℂ CtOuter.sinhQ univ :=
        (CtOuter.differentiable_sinhQ.differentiableOn).analyticOnNhd isOpen_univ
      have hcd_C : ContDiff ℂ (⊤ : ℕ∞) CtOuter.sinhQ :=
        contDiffOn_univ.mp (hana.contDiffOn isOpen_univ.uniqueDiffOn)
      exact ((Complex.reCLM.contDiff.comp (hcd_C.restrict_scalars ℝ)).comp
        (Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).div_const 2))).contDiffOn
    have hsQ_ne : ∀ t ∈ Ioo (-1 / 4 : ℝ) (1 / 4), (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re ^ 2 ≠ 0 := fun t ht => by
      have hx2 : ‖((π * t / 2 : ℝ) : ℂ)‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos Real.pi_pos,
          show |(2 : ℝ)| = 2 by norm_num]
        have habs : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        nlinarith [Real.pi_lt_four, abs_nonneg t]
      exact pow_ne_zero 2 (CtOuter.re_sinhQ_pos hx2).ne'
    dsimp only [hFac]
    cases kind
    · refine (contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne).add ?_
      exact ((((contDiff_const.mul contDiff_id).div_const 2).pow 2).contDiffOn).div
        (((Real.contDiff_cosh.comp ((contDiff_const.mul contDiff_id).div_const 2)).pow 2).contDiffOn)
        fun t _ => pow_ne_zero 2 (Real.cosh_pos _).ne'
    · exact contDiffOn_const.div (hsQ_cd.pow 2) hsQ_ne
  have hhFac_even : ∀ t : ℝ, hFac (-t) = hFac t := fun t => by
    have hq : CtOuter.sinhQ ((π * -t / 2 : ℝ) : ℂ) = CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ) := by
      rw [show (π * -t / 2 : ℝ) = -(π * t / 2) by ring, Complex.ofReal_neg]
      unfold CtOuter.sinhQ; refine tsum_congr fun n => ?_; rw [(even_two_mul n).neg_pow]
    dsimp only [hFac]
    cases kind
    · rw [hq, show π * -t / 2 = -(π * t / 2) by ring, Real.cosh_neg, neg_sq]
    · rw [hq]
  have hhFac_eq : ∀ t : ℝ, 0 < t → ‖stripH0 kind ((t : ℂ) * Complex.I)‖ = hFac t / t ^ 2 := by
    intro t ht
    have hx : 0 < π * t / 2 := by positivity
    have hsQ : (CtOuter.sinhQ ((π * t / 2 : ℝ) : ℂ)).re = Real.sinh (π * t / 2) / (π * t / 2) := by
      rw [CtOuter.sinhQ_ofReal hx.ne', Complex.ofReal_re]
    have hsh : Real.sinh (π * t / 2) ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
    dsimp only [hFac]; rw [hsQ]
    cases kind
    · rw [norm_stripH0_star_imag ht]; field_simp [ht.ne', Real.pi_ne_zero, hsh, (Real.cosh_pos _).ne']; ring
    · rw [norm_stripH0_ce_imag ht]; field_simp [ht.ne', Real.pi_ne_zero, hsh]; ring
  -- Even smooth Taylor expansions for `gA p t = hFac t / (mQ t ^ p * mD t)` and `gB p t = hFac t / mQ t ^ (p + 1)`
  have hgA_tay : ∀ p : ℕ, ∃ (a : Fin (p + 1) → ℝ) (C_A : ℝ), 0 ≤ C_A ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 8),
        |hFac t / (mQ t ^ p * mD t) - ∑ j : Fin (p + 1), a j * t ^ (2 * j.1)| ≤ C_A * t ^ (2 * (p + 1)) := by
    intro p
    refine even_smooth_taylor_bound ?_ (fun t ht => by
      rw [hhFac_even, mQ_even, mD_even ht]) (p + 1)
    exact hhFac_cd.div ((contDiffOn_mQ.pow p).mul contDiffOn_mD) fun t ht =>
      mul_ne_zero (pow_ne_zero p (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne')
        (mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  have hgB_tay : ∀ p : ℕ, ∃ (b : Fin (p + 1) → ℝ) (C_B : ℝ), 0 ≤ C_B ∧
      ∀ t ∈ Icc (0 : ℝ) (1 / 8),
        |hFac t / mQ t ^ (p + 1) - ∑ j : Fin (p + 1), b j * t ^ (2 * j.1)| ≤ C_B * t ^ (2 * (p + 1)) := by
    intro p
    refine even_smooth_taylor_bound ?_ (fun t _ => by rw [hhFac_even, mQ_even]) (p + 1)
    exact hhFac_cd.div (contDiffOn_mQ.pow (p + 1)) fun t ht =>
      pow_ne_zero (p + 1) (mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)).ne'
  choose aA C_A hCA_nn hCA_bd using hgA_tay
  choose bB C_B hCB_nn hCB_bd using hgB_tay
  -- Lower bounds on `m(t)` and `m'(t)` for `t ≥ 1/8` (and `m(t) ≥ c_m * t^2` on `(0, 1/8]`)
  have hm_18 : 0 < uctM (1 / 8) := uctM_pos (by norm_num)
  have hmD_low : ∃ c_D > 0, ∀ t : ℝ, 1 / 8 ≤ t → c_D / (1 + t) ≤ uctMderiv t := by
    -- `m'(t) = (π/2)(1/(πt/2) - 2/sinh(πt)) = 1/t - π/sinh(πt) ≥ (1/2)/t` for `t ≥ 1/8`?
    -- Actually for all `x = π t / 2 ≥ π / 16`: `ℓ'(x) = 1/x - 2/sinh(2x) > 0`;
    -- for `x ≥ 1/2`, `sinh(2x) ≥ 2x + (2x)^3/6` so `2/sinh(2x) ≤ 2/(2x + 8x^3/6) = 1/(x(1 + 2x^2/3))`,
    -- hence `ℓ'(x) ≥ (1/x) * (2x^2/3)/(1 + 2x^2/3) ≥ c / x`!
    -- Even simpler: for `t ≥ 1/8`, `2x = π t ≥ π/8 > 3/8`, and `sinh u ≥ u + u^3/6` for `u ≥ 0`,
    -- so `1/x - 2/sinh(2x) = 2(sinh(2x) - 2x)/(2x * sinh(2x))`!
    -- Better: for `t ≥ 1/8`, `m'(t) ≥ (1/100) / (1 + t)` since `sinh(πt) ≥ πt + (πt)^3/6` gives
    -- `1/t - π/sinh(πt) ≥ (1/t) * ((πt)^2/6) / (1 + (πt)^2/6) ≥ (1/t) * ((π/8)^2/6)/(1 + (π/8)^2/6) ≥ (1/50)/t ≥ (1/50)/(1+t)`!
    refine ⟨1 / 50, by norm_num, fun t ht => ?_⟩
    have ht0 : 0 < t := by linarith
    have hu : 0 < π * t := by positivity
    have hsh_ge : π * t + (π * t) ^ 3 / 6 ≤ Real.sinh (π * t) := by
      -- `f(u) = sinh u - u - u^3/6` has `f(0)=0, f'(0)=0, f''(u) = sinh u - u ≥ 0`
      have h1 : ∀ u : ℝ, 0 ≤ u → u + u ^ 3 / 6 ≤ Real.sinh u := by
        intro u hu0
        have h_s : ∀ s : ℝ, 0 ≤ s → s ≤ Real.sinh s := fun s hs => by
          have hd : ∀ x, HasDerivAt (fun y => Real.sinh y - y) (Real.cosh x - 1) x := fun x =>
            (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
          have hm := monotoneOn_of_deriv_nonneg (f := fun y => Real.sinh y - y) (convex_Ici 0)
            (Real.continuous_sinh.sub continuous_id).continuousOn
            (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
            (fun x _ => by rw [(hd x).deriv]; linarith [Real.one_le_cosh x])
          have := hm (le_rfl : (0 : ℝ) ∈ Ici 0) hs hs; simp only [Real.sinh_zero, sub_self] at this; linarith
        have h_c : ∀ s : ℝ, 0 ≤ s → 1 + s ^ 2 / 2 ≤ Real.cosh s := fun s hs => by
          have hd : ∀ x, HasDerivAt (fun y => Real.cosh y - 1 - y ^ 2 / 2) (Real.sinh x - x) x := fun x =>
            (((Real.hasDerivAt_cosh x).sub (hasDerivAt_const x 1)).sub ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv (by simp)
          have hm := monotoneOn_of_deriv_nonneg (f := fun y => Real.cosh y - 1 - y ^ 2 / 2) (convex_Ici 0)
            ((Real.continuous_cosh.sub continuous_const).sub ((continuous_id.pow 2).div_const 2)).continuousOn
            (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
            (fun x hx => by
              rw [(hd x).deriv]
              have hx0 : 0 ≤ x := (interior_Ici (a := (0 : ℝ)) ▸ hx).le
              linarith [h_s x hx0])
          have := hm (le_rfl : (0 : ℝ) ∈ Ici 0) hs hs; simp only [Real.cosh_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_self] at this; linarith
        have hd : ∀ x, HasDerivAt (fun y => Real.sinh y - y - y ^ 3 / 6) (Real.cosh x - 1 - x ^ 2 / 2) x := fun x =>
          (((Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)).sub ((hasDerivAt_pow 3 x).div_const 6)).congr_deriv (by ring)
        have hm := monotoneOn_of_deriv_nonneg (f := fun y => Real.sinh y - y - y ^ 3 / 6) (convex_Ici 0)
          ((Real.continuous_sinh.sub continuous_id).sub ((continuous_id.pow 3).div_const 6)).continuousOn
          (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [(hd x).deriv]
            have hx0 : 0 ≤ x := (interior_Ici (a := (0 : ℝ)) ▸ hx).le
            linarith [h_c x hx0])
        have := hm (le_rfl : (0 : ℝ) ∈ Ici 0) hu0 hu0; simp only [Real.sinh_zero, zero_pow (by norm_num : 3 ≠ 0), zero_div, sub_self] at this; linarith
      exact h1 (π * t) hu.le
    have hmd_eq : uctMderiv t = 1 / t - π / Real.sinh (π * t) := by
      unfold uctMderiv uctEllDeriv; field_simp [Real.pi_ne_zero, ht0.ne']
    rw [hmd_eq]
    have hsh_pos : 0 < Real.sinh (π * t) := Real.sinh_pos_iff.mpr hu
    have h1 : π / Real.sinh (π * t) ≤ π / (π * t + (π * t) ^ 3 / 6) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hsh_ge
    have h2 : 1 / t - π / (π * t + (π * t) ^ 3 / 6) = (π ^ 2 * t / 6) / (1 + (π * t) ^ 2 / 6) := by
      field_simp [ht0.ne', Real.pi_ne_zero]; ring
    have h3 : (1 / 50 : ℝ) / (1 + t) ≤ (π ^ 2 * t / 6) / (1 + (π * t) ^ 2 / 6) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
      nlinarith [sq_nonneg t]
    linarith
  obtain ⟨c_D, hc_D_pos, hc_D_bd⟩ := hmD_low
  -- Lower bound on `mQ` on `[0, 1/8]`
  obtain ⟨mQ_min, hmQ_min_pos, hmQ_min_bd⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), c ≤ mQ t := by
    have hcont := contDiffOn_mQ.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn
      ⟨0, le_rfl, by norm_num⟩ hcont
    exact ⟨mQ t₀, mQ_pos_of_mem (abs_lt.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩), fun t ht => hmin ht⟩
  -- Lower bound on `mD` on `[0, 1/8]`
  obtain ⟨mD_min, hmD_min_pos, hmD_min_bd⟩ : ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) (1 / 8), c ≤ mD t := by
    have hcont := contDiffOn_mD.continuousOn.mono (show Icc (0 : ℝ) (1 / 8) ⊆ Ioo (-1 / 4) (1 / 4) from
      fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 8)).exists_isMinOn
      ⟨0, le_rfl, by norm_num⟩ hcont
    exact ⟨mD t₀, mD_pos_of_mem (abs_lt.mpr ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩), fun t ht => hmin ht⟩
  -- Fixed constants `f0Base^{(2m+2)}(0)` for `m = 1, 2, 3`
  set B_v0d : ℝ := max (|iteratedDeriv 4 (f0Base kind) 0|)
    (max (|iteratedDeriv 6 (f0Base kind) 0|) (|iteratedDeriv 8 (f0Base kind) 0|))
  refine ⟨min (min τ₀_p1 τ₀_cos) (1 / 100), lt_min (lt_min hτ₀_p1_pos hτ₀_cos_pos) (by norm_num),
    (min_le_right _ _).trans (by norm_num), fun K4 hK4 => ?_⟩
  obtain ⟨C_cos, hC_cos_nn, hcos_spec⟩ := hcos_pen K4 hK4
  have hK4_nn : 0 ≤ K4 := by linarith
  -- Assemble a single clean `K4`-dependent constant `C` for all `p ≤ 2` and `D_*`!
  set M_L1_0 : ℝ := CL1_0b + K4 * CL1_0m
  set M_v0_0 : ℝ := Cv0b 0 + K4 * Cv0m 0 + Cv1b 0 + K4 * Cv1m 0 + Cva 0
  set M_th0_1 : ℝ := Cth0b 1 + K4 * Cth0m 1
  set M_th0_2 : ℝ := Cth0b 2 + K4 * Cth0m 2
  set M_cauchy : ℝ := (π / 2) * (B_v0d + 24 * K4) + max C_c1_1 (max C_c1_2 (max C_c1_3 (max C_c2_1 (max C_c2_2 C_c2_3)))) * M_L1_0
  -- Sum of `|aA p j|`, `|bB p j|` over `p ≤ 2`
  set S_coeff : ℝ :=
    (∑ j : Fin 1, (|aA 0 j| + |bB 0 j|)) + (∑ j : Fin 2, (|aA 1 j| + |bB 1 j|)) + (∑ j : Fin 3, (|aA 2 j| + |bB 2 j|))
  set C_rem_small : ℝ := max (C_A 0 + C_B 0) (max (C_A 1 + C_B 1) (C_A 2 + C_B 2))
  -- Remainder integral bound on `(0, 1/8]` and `[1/8, ∞)`
  set C_p_curv : ℝ := (uctAlphaOsc / 2) * (S_coeff * (2 * M_cauchy) +
    C_rem_small * (12 * (M_th0_2 + M_th0_1) + (C_tail 2 + C_tail 1) * M_L1_0 * (1 / 12 ^ 2)) +
    32 * (72 * (1 + π ^ 2 / 4) * (1 / (min 1 (uctM (1 / 8)) ^ 2)) * (1 / c_D + 1 / uctM (1 / 8)) *
      (C_tail 2 + C_tail 1) * M_L1_0 +
      S_coeff * (C_tail 2 + C_tail 1) * M_L1_0 * (8 : ℝ) ^ 7))
  -- Cross-term bound on `(0, 10 τ₁]`
  set C_cross : ℝ := (1 + π ^ 2 / 4) * (1 / min 1 mQ_min ^ 2) * (Real.exp M_v0_0 * M_v0_0) *
    ((1 / 2) * (M_th0_2 / mD_min + M_th0_1 / mQ_min)) * 10
  set C_all : ℝ := max C_p_curv (max C_cross (C_cos + C_p_curv + uctAlphaOsc * C_cross))
  have hαo_nn : 0 ≤ uctAlphaOsc := by unfold uctAlphaOsc; positivity
  have hM_L1_0_nn : 0 ≤ M_L1_0 := by rcases hCL1_nn with ⟨h1, h2, _, _, _⟩; positivity
  have hM_v0_0_nn : 0 ≤ M_v0_0 := by obtain ⟨h1, h2, h3, h4, h5⟩ := hCv_nn 0; positivity
  have hM_th0_1_nn : 0 ≤ M_th0_1 := by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn 1; positivity
  have hM_th0_2_nn : 0 ≤ M_th0_2 := by obtain ⟨h1, h2, _, _, _⟩ := hCth_nn 2; positivity
  have hM_cauchy_nn : 0 ≤ M_cauchy := by
    have hB : 0 ≤ B_v0d := le_trans (abs_nonneg _) (le_max_left _ _)
    have hmax : 0 ≤ max C_c1_1 (max C_c1_2 (max C_c1_3 (max C_c2_1 (max C_c2_2 C_c2_3)))) :=
      le_trans hCc1_1_nn (le_max_left _ _)
    positivity
  have hS_coeff_nn : 0 ≤ S_coeff := by
    refine add_nonneg (add_nonneg ?_ ?_) ?_ <;> exact Finset.sum_nonneg fun _ _ => by positivity
  have hC_rem_nn : 0 ≤ C_rem_small := le_trans (add_nonneg (hCA_nn 0) (hCB_nn 0)) (le_max_left _ _)
  have hC_p_nn : 0 ≤ C_p_curv := by
    have h1 := (hCti_nn 1).1; have h2 := (hCti_nn 2).1; positivity
  have hC_cross_nn : 0 ≤ C_cross := by positivity
  have hC_all_nn : 0 ≤ C_all := le_trans hC_p_nn (le_max_left _ _)
  refine ⟨C_all, hC_all_nn, fun {c α τ₁} hc hτ₁ hτ₁_le hc_eq hα_le => ?_⟩
  have hτ₁_p1 : τ₁ ≤ τ₀_p1 := hτ₁_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hτ₁_cos : τ₁ ≤ τ₀_cos := hτ₁_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hτ₁_100 : τ₁ ≤ 1 / 100 := hτ₁_le.trans (min_le_right _ _)
  have hτ₁_1 : τ₁ ≤ 1 := by linarith
  have hc_inv : c⁻¹ = τ₁ ^ 4 := by
    rw [inv_eq_iff_eq_inv]; field_simp [hc.ne', hτ₁.ne'] at hc_eq ⊢; linarith
  obtain ⟨⟨hb0_cd, hm0_cd, ha0_cd, hb1_cd, hm1_cd, hv_cd⟩,
    ⟨hb0_even, hm0_even, ha0_even, hb1_even, hm1_even, hv_even⟩,
    ⟨hb0_0, hm0_0, _, _, _, hv0⟩,
    ⟨hb0_s, hm0_s, _, _, _, hv_s⟩, hmom, hinner, hderivs, ⟨hL1_0b, hL1_0m, _, _, _⟩,
    hth_in, hth_tail, _, _, _⟩ := hpart1 hK4 hc hτ₁ hτ₁_p1 hc_eq hα_le
  set v := vTotal kind K4 c α τ₁
  set v0' := v0 kind K4 τ₁
  have hv0_cd : ContDiff ℝ (⊤ : ℕ∞) v0' := hb0_cd.add (contDiff_const.mul hm0_cd)
  have hv0_even : ∀ t, v0' (-t) = v0' t := fun t => by dsimp only [v0']; unfold v0; rw [hb0_even, hm0_even]
  have hv0_0 : v0' 0 = 0 := by dsimp only [v0']; unfold v0; rw [hb0_0, hm0_0]; ring
  have hv0_s : Function.support v0' ⊆ Ioo (-(10 * τ₁)) (10 * τ₁) := by
    intro t ht; by_contra hnot
    have h1 : v0Base kind τ₁ t = 0 := by by_contra hne; exact hnot (by simpa only [neg_mul] using hb0_s hne)
    have h2 : v0Marg τ₁ t = 0 := by by_contra hne; exact hnot (by simpa only [neg_mul] using hm0_s hne)
    exact ht (by dsimp only [v0']; simp [v0, h1, h2])
  have hv0_cs : HasCompactSupport v0' := hasCompactSupport_of_support_Ioo hv0_s
  have hθ0_cd : ContDiff ℝ (⊤ : ℕ∞) (fctThetaD v0') := contDiff_fctThetaD hv0_cd hv0_cs
  have hL1_v0' : (∫ t : ℝ, |v0' t|) ≤ M_L1_0 * τ₁ ^ 3 := by
    have hb0_cs := hasCompactSupport_of_support_Ioo hb0_s
    have hm0_cs := hasCompactSupport_of_support_Ioo hm0_s
    have hi1 : Integrable (fun t => |v0Base kind τ₁ t|) := hb0_cd.continuous.abs.integrable_of_hasCompactSupport (hb0_cs.comp_left abs_zero)
    have hi2 : Integrable (fun t => |v0Marg τ₁ t|) := hm0_cd.continuous.abs.integrable_of_hasCompactSupport (hm0_cs.comp_left abs_zero)
    have hm : (∫ t : ℝ, |v0' t|) ≤ ∫ t : ℝ, (|v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t|) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hi1.add (hi2.const_mul K4))
        (Filter.Eventually.of_forall fun t => by
          dsimp only [v0']; unfold v0; refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_of_nonneg hK4_nn])
    rw [integral_add hi1 (hi2.const_mul K4), integral_const_mul] at hm
    have hτ5 : τ₁ ^ 5 ≤ τ₁ ^ 3 := pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h2 : K4 * (CL1_0m * τ₁ ^ 5) ≤ K4 * (CL1_0m * τ₁ ^ 3) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ5 hCL1_nn.2.1) hK4_nn
    have h1 := add_le_add hL1_0b (mul_le_mul_of_nonneg_left hL1_0m hK4_nn)
    dsimp only [M_L1_0]; linarith
  -- Derivatives `v0'^{(2m+2)}(0)` for `m = 1, 2, 3` (`|v0'^{(2m+2)}(0)| ≤ B_v0d + 24 * K4`)
  have hv0_deriv_0 : ∀ m : ℕ, 1 ≤ m → m ≤ 3 → |iteratedDeriv (2 * m + 2) v0' 0| ≤ B_v0d + 24 * K4 := by
    intro m hm1 hm3
    have hev : v0' =ᶠ[𝓝 (0 : ℝ)] fun t => f0Base kind t + K4 * (-(t ^ 4)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 2 * τ₁ by positivity)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      have hin := hinner t ht.le
      dsimp only [v0']; unfold v0; rw [hin.1, hin.2.1]
    rw [(hev.iteratedDeriv (2 * m + 2)).eq_of_nhds]
    have hcd_f0 : ContDiffAt ℝ ((2 * m + 2 : ℕ) : WithTop ℕ∞) (f0Base kind) 0 :=
      ((contDiffOn_f0Base kind).contDiffAt (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4) (1 / 4)))).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have hcd_p4 : ContDiffAt ℝ ((2 * m + 2 : ℕ) : WithTop ℕ∞) (fun t : ℝ => K4 * (-(t ^ 4))) 0 :=
      (contDiff_const.mul ((contDiff_id.pow 4).neg)).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    change |iteratedDeriv (2 * m + 2) (f0Base kind + fun t : ℝ => K4 * (-(t ^ 4))) 0| ≤ _
    rw [iteratedDeriv_add hcd_f0 hcd_p4, iteratedDeriv_const_mul_field,
      show (fun t : ℝ => -(t ^ 4)) = -fun t : ℝ => t ^ 4 from rfl, iteratedDeriv_neg]
    have hp4 : |iteratedDeriv (2 * m + 2) (fun t : ℝ => t ^ 4) 0| ≤ 24 := by
      have hd1 : iteratedDeriv 1 (fun s : ℝ => s ^ 4) = fun s => 4 * s ^ 3 := by
        ext s; rw [iteratedDeriv_one]; exact (hasDerivAt_pow 4 s).deriv
      have hd2 : iteratedDeriv 2 (fun s : ℝ => s ^ 4) = fun s => 12 * s ^ 2 := by
        ext s; rw [iteratedDeriv_succ, hd1]; convert ((hasDerivAt_pow 3 s).const_mul 4).deriv using 1; ring
      have hd3 : iteratedDeriv 3 (fun s : ℝ => s ^ 4) = fun s => 24 * s := by
        ext s; rw [iteratedDeriv_succ, hd2]; convert ((hasDerivAt_pow 2 s).const_mul 12).deriv using 1; ring
      have hd4 : iteratedDeriv 4 (fun s : ℝ => s ^ 4) = fun _ => (24 : ℝ) := by
        ext s; rw [iteratedDeriv_succ, hd3]; simp
      have hd5 : iteratedDeriv 5 (fun s : ℝ => s ^ 4) = 0 := by
        ext s; rw [iteratedDeriv_succ, hd4]; simp [deriv_const]
      interval_cases m
      · rw [show 2 * 1 + 2 = 4 by rfl, hd4]; norm_num
      · rw [show 2 * 2 + 2 = 1 + 5 by rfl, ← iteratedDeriv_iteratedDeriv_eq, hd5, iteratedDeriv_const_zero]; norm_num
      · rw [show 2 * 3 + 2 = 3 + 5 by rfl, ← iteratedDeriv_iteratedDeriv_eq, hd5, iteratedDeriv_const_zero]; norm_num
    have hf0_le : |iteratedDeriv (2 * m + 2) (f0Base kind) 0| ≤ B_v0d := by
      interval_cases m
      · exact le_max_left _ _
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · exact (le_max_right _ _).trans (le_max_right _ _)
    calc |iteratedDeriv (2 * m + 2) (f0Base kind) 0 + K4 * -iteratedDeriv (2 * m + 2) (fun t : ℝ => t ^ 4) 0|
        ≤ |iteratedDeriv (2 * m + 2) (f0Base kind) 0| + K4 * |iteratedDeriv (2 * m + 2) (fun t : ℝ => t ^ 4) 0| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_neg, abs_of_nonneg hK4_nn]
      _ ≤ B_v0d + K4 * 24 := add_le_add hf0_le (mul_le_mul_of_nonneg_left hp4 hK4_nn)
      _ = B_v0d + 24 * K4 := by ring
  -- Cauchy curvature bounds on `∫_0^∞ ϑ_0''(t) / t^{2m+1} dt` and `∫_0^∞ ϑ_0'(t) / t^{2m+2} dt` for `m = 1, 2, 3`
  have hcauchy_12 : ∀ m : ℕ, 1 ≤ m → m ≤ 3 →
      IntegrableOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1)) (Ioi 0) ∧
      |∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1)| ≤ M_cauchy ∧
      IntegrableOn (fun t : ℝ => deriv (fctThetaD v0') t / t ^ (2 * m + 2)) (Ioi 0) ∧
      |∫ t in Ioi (0 : ℝ), deriv (fctThetaD v0') t / t ^ (2 * m + 2)| ≤ M_cauchy := by
    intro m hm1 hm3
    have hmom_m : ∀ k ≤ m, fctMoment k v0' = 0 := fun k hk => (hmom k (by omega)).1
    have hR0 : (0 : ℝ) < 10 * τ₁ := by positivity
    have hR12 : 10 * τ₁ ≤ 1 / 2 := by linarith
    have hfac1 : (1 : ℝ) / ((2 * m).factorial : ℝ) ≤ 1 :=
      div_le_one_of_le₀ (by exact_mod_cast Nat.factorial_pos (2 * m)) (by positivity)
    have hfac2 : ((2 * m - 1 : ℝ)) / ((2 * m + 1).factorial : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have h1 : (2 * m - 1 : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
      have h2 : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * m + 1).factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial _
      exact h1.trans h2
    have hL1_le : (∫ t : ℝ, |v0' t|) ≤ M_L1_0 :=
      hL1_v0'.trans (mul_le_of_le_one_right hM_L1_0_nn (pow_le_one₀ hτ₁.le hτ₁_1))
    -- Obtain `I1` and `I2` from `fct_cauchy_curv_first` and `fct_cauchy_curv_second`
    have h12_spec : ∃ C1 C2, 0 ≤ C1 ∧ 0 ≤ C2 ∧
        C1 ≤ max C_c1_1 (max C_c1_2 (max C_c1_3 (max C_c2_1 (max C_c2_2 C_c2_3)))) ∧
        C2 ≤ max C_c1_1 (max C_c1_2 (max C_c1_3 (max C_c2_1 (max C_c2_2 C_c2_3)))) ∧
        IntegrableOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1)) (Ioi 0) ∧
        |(∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1)) -
          (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v0' 0)| ≤ C1 * (∫ t : ℝ, |v0' t|) ∧
        IntegrableOn (fun t : ℝ => iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1) -
          2 * deriv (fctThetaD v0') t / t ^ (2 * m + 2)) (Ioi 0) ∧
        |(∫ t in Ioi (0 : ℝ), (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1) -
          2 * deriv (fctThetaD v0') t / t ^ (2 * m + 2))) -
          (-(((2 * (m : ℝ) - 1) * π) / (2 * ((2 * m + 1).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v0' 0)| ≤
          C2 * (∫ t : ℝ, |v0' t|) := by
      interval_cases m
      · obtain ⟨hi1, hb1⟩ := hCc1_1 hv0_cd hv0_even hR0 hR12 hv0_s hv0_0 hmom_m
        obtain ⟨hi2, hb2⟩ := hCc2_1 hv0_cd hv0_even hR0 hR12 hv0_s hv0_0 hmom_m
        exact ⟨C_c1_1, C_c2_1, hCc1_1_nn, hCc2_1_nn, le_max_left _ _,
          (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
          hi1, hb1, hi2, hb2⟩
      · obtain ⟨hi1, hb1⟩ := hCc1_2 hv0_cd hv0_even hR0 hR12 hv0_s hv0_0 hmom_m
        obtain ⟨hi2, hb2⟩ := hCc2_2 hv0_cd hv0_even hR0 hR12 hv0_s hv0_0 hmom_m
        exact ⟨C_c1_2, C_c2_2, hCc1_2_nn, hCc2_2_nn, (le_max_left _ _).trans (le_max_right _ _),
          (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))),
          hi1, hb1, hi2, hb2⟩
      · obtain ⟨hi1, hb1⟩ := hCc1_3 hv0_cd hv0_even hR0 hR12 hv0_s hv0_0 hmom_m
        obtain ⟨hi2, hb2⟩ := hCc2_3 hv0_cd hv0_even hR0 hR12 hv0_s hv0_0 hmom_m
        exact ⟨C_c1_3, C_c2_3, hCc1_3_nn, hCc2_3_nn, (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
          (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))),
          hi1, hb1, hi2, hb2⟩
    obtain ⟨C1, C2, hC1_nn, hC2_nn, hC1_le, hC2_le, hi1, hb1, hi2, hb2⟩ := h12_spec
    have hI1_bd : |∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1)| ≤ M_cauchy := by
      have hlead : |(-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v0' 0)| ≤
          (π / 2) * (B_v0d + 24 * K4) := by
        rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
        calc π / (2 * ((2 * m).factorial : ℝ)) * |iteratedDeriv (2 * m + 2) v0' 0|
            = (π / 2) * (1 / ((2 * m).factorial : ℝ)) * |iteratedDeriv (2 * m + 2) v0' 0| := by ring
          _ ≤ (π / 2) * 1 * (B_v0d + 24 * K4) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hfac1 (by positivity)) (hv0_deriv_0 m hm1 hm3) (abs_nonneg _) (by positivity)
          _ = (π / 2) * (B_v0d + 24 * K4) := by ring
      have herr : C1 * (∫ t : ℝ, |v0' t|) ≤ max C_c1_1 (max C_c1_2 (max C_c1_3 (max C_c2_1 (max C_c2_2 C_c2_3)))) * M_L1_0 :=
        mul_le_mul hC1_le hL1_le (integral_nonneg fun _ => abs_nonneg _) (le_trans hCc1_1_nn (le_max_left _ _))
      have htri := abs_sub_abs_le_abs_sub (∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1))
        (-(π / (2 * ((2 * m).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v0' 0)
      dsimp only [M_cauchy]; linarith
    have hI2_bd : |∫ t in Ioi (0 : ℝ), (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1) -
        2 * deriv (fctThetaD v0') t / t ^ (2 * m + 2))| ≤ M_cauchy := by
      have hlead : |(-(((2 * (m : ℝ) - 1) * π) / (2 * ((2 * m + 1).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v0' 0)| ≤
          (π / 2) * (B_v0d + 24 * K4) := by
        have h2m1 : 0 < 2 * (m : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
          linarith
        rw [abs_mul, abs_neg, abs_of_pos (by positivity)]
        calc ((2 * (m : ℝ) - 1) * π) / (2 * ((2 * m + 1).factorial : ℝ)) * |iteratedDeriv (2 * m + 2) v0' 0|
            = (π / 2) * ((2 * (m : ℝ) - 1) / ((2 * m + 1).factorial : ℝ)) * |iteratedDeriv (2 * m + 2) v0' 0| := by ring
          _ ≤ (π / 2) * 1 * (B_v0d + 24 * K4) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hfac2 (by positivity)) (hv0_deriv_0 m hm1 hm3) (abs_nonneg _) (by positivity)
          _ = (π / 2) * (B_v0d + 24 * K4) := by ring
      have herr : C2 * (∫ t : ℝ, |v0' t|) ≤ max C_c1_1 (max C_c1_2 (max C_c1_3 (max C_c2_1 (max C_c2_2 C_c2_3)))) * M_L1_0 :=
        mul_le_mul hC2_le hL1_le (integral_nonneg fun _ => abs_nonneg _) (le_trans hCc1_1_nn (le_max_left _ _))
      have htri := abs_sub_abs_le_abs_sub
        (∫ t in Ioi (0 : ℝ), (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1) - 2 * deriv (fctThetaD v0') t / t ^ (2 * m + 2)))
        (-(((2 * (m : ℝ) - 1) * π) / (2 * ((2 * m + 1).factorial : ℝ))) * iteratedDeriv (2 * m + 2) v0' 0)
      dsimp only [M_cauchy]; linarith
    have hi_d1 : IntegrableOn (fun t : ℝ => deriv (fctThetaD v0') t / t ^ (2 * m + 2)) (Ioi 0) := by
      have hrew : (fun t : ℝ => deriv (fctThetaD v0') t / t ^ (2 * m + 2)) =
          fun t => (1 / 2 : ℝ) * ((iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1)) -
            (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1) - 2 * deriv (fctThetaD v0') t / t ^ (2 * m + 2))) := by
        ext t; ring
      rw [hrew]; exact (hi1.sub hi2).const_mul (1 / 2)
    have hI_d1_bd : |∫ t in Ioi (0 : ℝ), deriv (fctThetaD v0') t / t ^ (2 * m + 2)| ≤ M_cauchy := by
      have hrew : (fun t : ℝ => deriv (fctThetaD v0') t / t ^ (2 * m + 2)) =
          fun t => (1 / 2 : ℝ) * ((iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1)) -
            (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1) - 2 * deriv (fctThetaD v0') t / t ^ (2 * m + 2))) := by
        ext t; ring
      rw [hrew, integral_const_mul, integral_sub hi1 hi2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have htri := abs_sub (∫ t in Ioi (0 : ℝ), iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1))
        (∫ t in Ioi (0 : ℝ), (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * m + 1) - 2 * deriv (fctThetaD v0') t / t ^ (2 * m + 2)))
      linarith
    exact ⟨hi1, hI1_bd, hi_d1, hI_d1_bd⟩
  -- Phase derivative bounds for `ϑ_{D₀}` (`r = 1, 2`) on `|t| ≤ 12 τ₁` and `|t| ≥ 12 τ₁`
  have hθ0_in : ∀ t : ℝ, |t| ≤ 12 * τ₁ →
      |deriv (fctThetaD v0') t| ≤ M_th0_1 * τ₁ * min 1 ((|t| / τ₁) ^ 10) ∧
      |iteratedDeriv 2 (fctThetaD v0') t| ≤ M_th0_2 * min 1 ((|t| / τ₁) ^ 9) := by
    intro t ht
    have hb0_cs := hasCompactSupport_of_support_Ioo hb0_s
    have hm0_cs := hasCompactSupport_of_support_Ioo hm0_s
    have hθ0b_cd := contDiff_fctThetaD hb0_cd hb0_cs
    have hθ0m_cd := contDiff_fctThetaD hm0_cd hm0_cs
    have hlin : fctThetaD v0' = fun s => fctThetaD (v0Base kind τ₁) s + K4 * fctThetaD (v0Marg τ₁) s := by
      ext s; dsimp only [v0']; unfold v0
      simpa only [one_mul] using fctThetaD_linear hb0_cd hb0_cs hm0_cd hm0_cs 1 K4 s
    have h1 := hth_in 1 t ht
    have h2 := hth_in 2 t ht
    have hτ3 : τ₁ ^ ((4 : ℤ) - (1 : ℕ)) ≤ τ₁ := by
      rw [show (4 : ℤ) - (1 : ℕ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      simpa using pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num : 1 ≤ 3)
    have hτ2 : τ₁ ^ ((4 : ℤ) - (2 : ℕ)) ≤ 1 := by
      rw [show (4 : ℤ) - (2 : ℕ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact pow_le_one₀ hτ₁.le hτ₁_1
    constructor
    · rw [← iteratedDeriv_one, hlin]
      change |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t| ≤ _
      rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
        ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
        iteratedDeriv_const_mul_field]
      have htri : |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| ≤
          |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| :=
        (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK4_nn])
      have d1 : |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 1 * τ₁ * min 1 ((|t| / τ₁) ^ 10) := by
        simpa [show (2 : ℤ) - (1 : ℕ) = 1 by norm_num] using h1.1
      have d2 : |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m 1 * τ₁ * min 1 ((|t| / τ₁) ^ 10) :=
        h1.2.1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ3 (hCth_nn 1).2.1) (le_min zero_le_one (by positivity)))
      have hm := mul_le_mul_of_nonneg_left d2 hK4_nn
      calc |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t|
          ≤ |iteratedDeriv 1 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 1 (fctThetaD (v0Marg τ₁)) t| := htri
        _ ≤ Cth0b 1 * τ₁ * min 1 ((|t| / τ₁) ^ 10) + K4 * (Cth0m 1 * τ₁ * min 1 ((|t| / τ₁) ^ 10)) := add_le_add d1 hm
        _ = M_th0_1 * τ₁ * min 1 ((|t| / τ₁) ^ 10) := by dsimp only [M_th0_1]; ring
    · rw [hlin]
      change |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁) + fun s => K4 * fctThetaD (v0Marg τ₁) s) t| ≤ _
      rw [iteratedDeriv_add (hθ0b_cd.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
        ((contDiff_const.mul hθ0m_cd).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)),
        iteratedDeriv_const_mul_field]
      have htri : |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| ≤
          |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| :=
        (abs_add_le _ _).trans (by rw [abs_mul, abs_of_nonneg hK4_nn])
      have d1 : |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| ≤ Cth0b 2 * min 1 ((|t| / τ₁) ^ 9) := by
        simpa [show (2 : ℤ) - (2 : ℕ) = 0 by norm_num] using h2.1
      have d2 : |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| ≤ Cth0m 2 * min 1 ((|t| / τ₁) ^ 9) := by
        refine h2.2.1.trans ?_
        have := mul_le_mul_of_nonneg_left hτ2 (hCth_nn 2).2.1; rw [mul_one] at this
        exact mul_le_mul_of_nonneg_right this (le_min zero_le_one (by positivity))
      have hm := mul_le_mul_of_nonneg_left d2 hK4_nn
      calc |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t + K4 * iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t|
          ≤ |iteratedDeriv 2 (fctThetaD (v0Base kind τ₁)) t| + K4 * |iteratedDeriv 2 (fctThetaD (v0Marg τ₁)) t| := htri
        _ ≤ Cth0b 2 * min 1 ((|t| / τ₁) ^ 9) + K4 * (Cth0m 2 * min 1 ((|t| / τ₁) ^ 9)) := add_le_add d1 hm
        _ = M_th0_2 * min 1 ((|t| / τ₁) ^ 9) := by dsimp only [M_th0_2]; ring
  -- Now prove the `p ≤ 2` statement!
  have hp_main : ∀ p : ℕ, p ≤ 2 →
      IntegrableOn (fun L : ℝ => stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L) / L ^ p) (Ioi 0) ∧
      |∫ L in Ioi (0 : ℝ), stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L) / L ^ p| ≤ C_p_curv * c⁻¹ ∧
      IntegrableOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p *
        |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) (Ioc 0 (10 * τ₁)) ∧
      (∫ t in Ioc 0 (10 * τ₁), ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p *
        |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) ≤ C_cross * c⁻¹ * τ₁ ^ (-(2 * (p : ℤ))) := by
    intro p hp2
    -- 1. First, the curvature-paired integral on `(0, ∞)` via `L = m(t)`
    let fA : ℝ → ℝ := fun t => ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / (uctM t ^ p * uctMderiv t) * iteratedDeriv 2 (fctThetaD v0') t
    let fB : ℝ → ℝ := fun t => ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ (p + 1) * deriv (fctThetaD v0') t
    let sA : ℝ → ℝ := fun t => ∑ j : Fin (p + 1), aA p j * (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 1))
    let sB : ℝ → ℝ := fun t => ∑ j : Fin (p + 1), bB p j * (deriv (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 2))
    -- Integrability & Cauchy bound for `sA` and `sB` on `Ioi 0`
    have hsA_int : IntegrableOn sA (Ioi 0) ∧ |∫ t in Ioi (0 : ℝ), sA t| ≤ (∑ j : Fin (p + 1), |aA p j|) * M_cauchy := by
      have hterm : ∀ j : Fin (p + 1),
          IntegrableOn (fun t => aA p j * (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 1))) (Ioi 0) ∧
          |∫ t in Ioi (0 : ℝ), aA p j * (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 1))| ≤ |aA p j| * M_cauchy := by
        intro j
        have hm1 : 1 ≤ p + 1 - j.1 := by omega
        have hm3 : p + 1 - j.1 ≤ 3 := by omega
        have hc_j := hcauchy_12 (p + 1 - j.1) hm1 hm3
        refine ⟨hc_j.1.const_mul _, ?_⟩
        rw [integral_const_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left hc_j.2.1 (abs_nonneg _)
      have hfin : ∀ (s : Finset (Fin (p + 1))),
          IntegrableOn (fun t => ∑ j ∈ s, aA p j * (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 1))) (Ioi 0) ∧
          (∫ t in Ioi (0 : ℝ), ∑ j ∈ s, aA p j * (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 1))) =
          ∑ j ∈ s, ∫ t in Ioi (0 : ℝ), aA p j * (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 1)) := by
        intro s; induction s using Finset.cons_induction with
        | empty => exact ⟨by simp, by simp⟩
        | cons a s ha ih =>
          simp_rw [Finset.sum_cons]
          exact ⟨(hterm a).1.add ih.1, by rw [integral_add (hterm a).1 ih.1, ih.2]⟩
      refine ⟨(hfin Finset.univ).1, ?_⟩
      rw [(hfin Finset.univ).2]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => (hterm j).2
    have hsB_int : IntegrableOn sB (Ioi 0) ∧ |∫ t in Ioi (0 : ℝ), sB t| ≤ (∑ j : Fin (p + 1), |bB p j|) * M_cauchy := by
      have hterm : ∀ j : Fin (p + 1),
          IntegrableOn (fun t => bB p j * (deriv (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 2))) (Ioi 0) ∧
          |∫ t in Ioi (0 : ℝ), bB p j * (deriv (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 2))| ≤ |bB p j| * M_cauchy := by
        intro j
        have hm1 : 1 ≤ p + 1 - j.1 := by omega
        have hm3 : p + 1 - j.1 ≤ 3 := by omega
        have hc_j := hcauchy_12 (p + 1 - j.1) hm1 hm3
        refine ⟨hc_j.2.2.1.const_mul _, ?_⟩
        rw [integral_const_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left hc_j.2.2.2 (abs_nonneg _)
      have hfin : ∀ (s : Finset (Fin (p + 1))),
          IntegrableOn (fun t => ∑ j ∈ s, bB p j * (deriv (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 2))) (Ioi 0) ∧
          (∫ t in Ioi (0 : ℝ), ∑ j ∈ s, bB p j * (deriv (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 2))) =
          ∑ j ∈ s, ∫ t in Ioi (0 : ℝ), bB p j * (deriv (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 2)) := by
        intro s; induction s using Finset.cons_induction with
        | empty => exact ⟨by simp, by simp⟩
        | cons a s ha ih =>
          simp_rw [Finset.sum_cons]
          exact ⟨(hterm a).1.add ih.1, by rw [integral_add (hterm a).1 ih.1, ih.2]⟩
      refine ⟨(hfin Finset.univ).1, ?_⟩
      rw [(hfin Finset.univ).2]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ => (hterm j).2
    -- Continuity of `fA`, `fB`, `sA`, `sB` on `Ioi 0`
    have hH_cont : ContinuousOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖) (Ioi 0) := by
      cases kind
      · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_star_imag ht
        refine (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
          ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
          fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')).add
          (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_cosh.comp
            ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
            fun t _ => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne'))
      · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_ce_imag ht
        exact continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
          ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
          fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (by have : 0 < t := ht; positivity)).ne')
    have hm_cont : ContinuousOn uctM (Ioi 0) := fun t ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt
    have hmd_cont : ContinuousOn uctMderiv (Ioi 0) := by
      unfold uctMderiv uctEllDeriv
      refine continuousOn_const.mul ((continuousOn_const.div ((continuousOn_const.mul continuousOn_id).div_const 2)
        fun t (ht : t ∈ Ioi (0 : ℝ)) => (div_pos (mul_pos Real.pi_pos ht) two_pos).ne').sub
        (continuousOn_const.div (Real.continuous_sinh.comp (continuous_const.mul ((continuous_const.mul continuous_id).div_const 2))).continuousOn
          fun t (ht : t ∈ Ioi (0 : ℝ)) => (Real.sinh_pos_iff.mpr (mul_pos two_pos (div_pos (mul_pos Real.pi_pos ht) two_pos))).ne'))
    have hfA_cont : ContinuousOn fA (Ioi 0) :=
      (hH_cont.div ((hm_cont.pow p).mul hmd_cont) fun t ht => by
        have ht0 : 0 < t := ht; exact mul_ne_zero (pow_ne_zero p (uctM_pos ht0).ne') (uctMderiv_pos ht0).ne').mul
        (contDiff_iteratedDeriv_infty hθ0_cd 2).continuous.continuousOn
    have hfB_cont : ContinuousOn fB (Ioi 0) :=
      (hH_cont.div (hm_cont.pow (p + 1)) fun t ht => by
        have ht0 : 0 < t := ht; exact pow_ne_zero (p + 1) (uctM_pos ht0).ne').mul
        (hθ0_cd.continuous_deriv (by simp)).continuousOn
    have hsA_cont : ContinuousOn sA (Ioi 0) := by
      dsimp only [sA]
      have h1 : ∀ (s : Finset (Fin (p + 1))), ContinuousOn (fun t => ∑ j ∈ s, aA p j * (iteratedDeriv 2 (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 1))) (Ioi 0) := by
        intro s; induction s using Finset.cons_induction with
        | empty => simpa using continuousOn_const
        | cons a s ha ih =>
          simp_rw [Finset.sum_cons]
          exact (continuousOn_const.mul ((contDiff_iteratedDeriv_infty hθ0_cd 2).continuous.continuousOn.div
            (continuousOn_id.pow _) fun t ht => pow_ne_zero _ (mem_Ioi.mp ht).ne')).add ih
      exact h1 Finset.univ
    have hsB_cont : ContinuousOn sB (Ioi 0) := by
      dsimp only [sB]
      have h1 : ∀ (s : Finset (Fin (p + 1))), ContinuousOn (fun t => ∑ j ∈ s, bB p j * (deriv (fctThetaD v0') t / t ^ (2 * (p + 1 - j.1) + 2))) (Ioi 0) := by
        intro s; induction s using Finset.cons_induction with
        | empty => simpa using continuousOn_const
        | cons a s ha ih =>
          simp_rw [Finset.sum_cons]
          exact (continuousOn_const.mul ((hθ0_cd.continuous_deriv (by simp)).continuousOn.div
            (continuousOn_id.pow _) fun t ht => pow_ne_zero _ (mem_Ioi.mp ht).ne')).add ih
      exact h1 Finset.univ
    -- Remainder `rAB t = (fA t - sA t) - (fB t - sB t)` on `Ioc 0 (12 τ₁)`, `Ioc (12 τ₁) (1/8)`, `Ioi (1/8)`!
    let rA : ℝ → ℝ := fun t => fA t - sA t
    let rB : ℝ → ℝ := fun t => fB t - sB t
    have hrA_small : ∀ t ∈ Ioc (0 : ℝ) (1 / 8), |rA t| ≤ C_A p * |iteratedDeriv 2 (fctThetaD v0') t| / t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht14 : t < 1 / 4 := by linarith [ht.2]
      have hfac : fA t - sA t = (hFac t / (mQ t ^ p * mD t) - ∑ j : Fin (p + 1), aA p j * t ^ (2 * j.1)) /
          t ^ (2 * p + 3) * iteratedDeriv 2 (fctThetaD v0') t := by
        dsimp only [fA, sA]
        rw [hhFac_eq t ht0, uctM_eq_sq_mul_mQ ht0, uctMderiv_eq_mul_mD ht0 ht14, sub_div, sub_mul,
          Finset.sum_div, Finset.sum_mul]
        congr 1
        · rw [mul_pow, ← pow_mul]; field_simp [ht0.ne', (mQ_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)).ne',
            (mD_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)).ne']; ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          have hexp : 2 * p + 3 = 2 * j.1 + (2 * (p + 1 - j.1) + 1) := by omega
          rw [hexp, pow_add]; field_simp [ht0.ne']; ring
      dsimp only [rA]; rw [hfac, abs_mul, abs_div, abs_pow, abs_of_pos ht0]
      have h1 := hCA_bd p t ⟨ht0.le, ht.2⟩
      calc |hFac t / (mQ t ^ p * mD t) - ∑ j : Fin (p + 1), aA p j * t ^ (2 * j.1)| / t ^ (2 * p + 3) *
              |iteratedDeriv 2 (fctThetaD v0') t|
          ≤ (C_A p * t ^ (2 * (p + 1))) / t ^ (2 * p + 3) * |iteratedDeriv 2 (fctThetaD v0') t| :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h1 (by positivity)) (abs_nonneg _)
        _ = C_A p * |iteratedDeriv 2 (fctThetaD v0') t| / t := by
            rw [show 2 * p + 3 = 2 * (p + 1) + 1 by omega, pow_succ]; field_simp [ht0.ne']
    have hrB_small : ∀ t ∈ Ioc (0 : ℝ) (1 / 8), |rB t| ≤ C_B p * |deriv (fctThetaD v0') t| / t ^ 2 := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht14 : t < 1 / 4 := by linarith [ht.2]
      have hfac : fB t - sB t = (hFac t / mQ t ^ (p + 1) - ∑ j : Fin (p + 1), bB p j * t ^ (2 * j.1)) /
          t ^ (2 * p + 4) * deriv (fctThetaD v0') t := by
        dsimp only [fB, sB]
        rw [hhFac_eq t ht0, uctM_eq_sq_mul_mQ ht0, sub_div, sub_mul, Finset.sum_div, Finset.sum_mul]
        congr 1
        · rw [mul_pow, ← pow_mul]; field_simp [ht0.ne', (mQ_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)).ne']; ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          have hexp : 2 * p + 4 = 2 * j.1 + (2 * (p + 1 - j.1) + 2) := by omega
          rw [hexp, pow_add]; field_simp [ht0.ne']; ring
      dsimp only [rB]; rw [hfac, abs_mul, abs_div, abs_pow, abs_of_pos ht0]
      have h1 := hCB_bd p t ⟨ht0.le, ht.2⟩
      calc |hFac t / mQ t ^ (p + 1) - ∑ j : Fin (p + 1), bB p j * t ^ (2 * j.1)| / t ^ (2 * p + 4) *
              |deriv (fctThetaD v0') t|
          ≤ (C_B p * t ^ (2 * (p + 1))) / t ^ (2 * p + 4) * |deriv (fctThetaD v0') t| :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h1 (by positivity)) (abs_nonneg _)
        _ = C_B p * |deriv (fctThetaD v0') t| / t ^ 2 := by
            rw [show 2 * p + 4 = 2 * (p + 1) + 2 by omega, pow_add]; field_simp [ht0.ne']
    -- Bound `rA - rB` on `Ioc 0 (12 τ₁)` (`12 τ₁ ≤ 12/100 < 1/8`!)
    have h12_lt : 12 * τ₁ < 1 / 8 := by linarith
    have hr_1 : IntegrableOn (fun t => rA t - rB t) (Ioc 0 (12 * τ₁)) ∧
        |∫ t in Ioc 0 (12 * τ₁), (rA t - rB t)| ≤ C_rem_small * (12 * (M_th0_2 + M_th0_1)) := by
      have hpt : ∀ t ∈ Ioc (0 : ℝ) (12 * τ₁), ‖rA t - rB t‖ ≤ C_rem_small * (M_th0_2 + M_th0_1) / τ₁ := by
        intro t ht
        have ht18 : t ∈ Ioc (0 : ℝ) (1 / 8) := ⟨ht.1, ht.2.trans h12_lt.le⟩
        have hθ := hθ0_in t (by rw [abs_of_pos ht.1]; exact ht.2)
        have hA_t : |iteratedDeriv 2 (fctThetaD v0') t| / t ≤ M_th0_2 / τ₁ := by
          rcases le_or_gt t τ₁ with hle | hgt
          · have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 9) ≤ (t / τ₁) ^ 9 := by rw [abs_of_pos ht.1]; exact min_le_right _ _
            have h1 : |iteratedDeriv 2 (fctThetaD v0') t| ≤ M_th0_2 * (t / τ₁) ^ 9 :=
              hθ.2.trans (mul_le_mul_of_nonneg_left hmin hM_th0_2_nn)
            have hrat : (t / τ₁) ^ 8 ≤ 1 := pow_le_one₀ (div_nonneg ht.1.le hτ₁.le) ((div_le_one hτ₁).mpr hle)
            rw [div_le_iff₀ ht.1]
            calc |iteratedDeriv 2 (fctThetaD v0') t| ≤ M_th0_2 * (t / τ₁) ^ 9 := h1
              _ = (M_th0_2 / τ₁) * t * (t / τ₁) ^ 8 := by field_simp [hτ₁.ne']
              _ ≤ (M_th0_2 / τ₁) * t * 1 := mul_le_mul_of_nonneg_left hrat (mul_nonneg (div_nonneg hM_th0_2_nn hτ₁.le) ht.1.le)
              _ = M_th0_2 / τ₁ * t := mul_one _
          · have h1 := hθ.2.trans (mul_le_of_le_one_right hM_th0_2_nn (min_le_left _ _))
            exact (div_le_div_of_nonneg_right h1 ht.1.le).trans (div_le_div_of_nonneg_left hM_th0_2_nn hτ₁ hgt.le)
        have hB_t : |deriv (fctThetaD v0') t| / t ^ 2 ≤ M_th0_1 / τ₁ := by
          rcases le_or_gt t τ₁ with hle | hgt
          · have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 10) ≤ (t / τ₁) ^ 10 := by rw [abs_of_pos ht.1]; exact min_le_right _ _
            have h1 : |deriv (fctThetaD v0') t| ≤ M_th0_1 * τ₁ * (t / τ₁) ^ 10 :=
              hθ.1.trans (mul_le_mul_of_nonneg_left hmin (mul_nonneg hM_th0_1_nn hτ₁.le))
            have hrat : (t / τ₁) ^ 8 ≤ 1 := pow_le_one₀ (div_nonneg ht.1.le hτ₁.le) ((div_le_one hτ₁).mpr hle)
            rw [div_le_iff₀ (sq_pos_of_pos ht.1)]
            calc |deriv (fctThetaD v0') t| ≤ M_th0_1 * τ₁ * (t / τ₁) ^ 10 := h1
              _ = (M_th0_1 / τ₁) * t ^ 2 * (t / τ₁) ^ 8 := by field_simp [hτ₁.ne']
              _ ≤ (M_th0_1 / τ₁) * t ^ 2 * 1 := mul_le_mul_of_nonneg_left hrat (mul_nonneg (div_nonneg hM_th0_1_nn hτ₁.le) (sq_nonneg t))
              _ = M_th0_1 / τ₁ * t ^ 2 := mul_one _
          · have h1 := hθ.1.trans (mul_le_of_le_one_right (by positivity) (min_le_left _ _))
            have hsq : τ₁ ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hτ₁.le hgt.le 2
            calc |deriv (fctThetaD v0') t| / t ^ 2 ≤ (M_th0_1 * τ₁) / τ₁ ^ 2 :=
                  (div_le_div_of_nonneg_right h1 (sq_nonneg t)).trans (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hτ₁) hsq)
              _ = M_th0_1 / τ₁ := by field_simp [hτ₁.ne']
        have hCA_le : C_A p ≤ C_rem_small := by
          interval_cases p
          · exact le_trans (le_add_of_nonneg_right (hCB_nn 0)) (le_max_left _ _)
          · exact le_trans (le_add_of_nonneg_right (hCB_nn 1)) ((le_max_left _ _).trans (le_max_right _ _))
          · exact le_trans (le_add_of_nonneg_right (hCB_nn 2)) ((le_max_right _ _).trans (le_max_right _ _))
        have hCB_le : C_B p ≤ C_rem_small := by
          interval_cases p
          · exact le_trans (le_add_of_nonneg_left (hCA_nn 0)) (le_max_left _ _)
          · exact le_trans (le_add_of_nonneg_left (hCA_nn 1)) ((le_max_left _ _).trans (le_max_right _ _))
          · exact le_trans (le_add_of_nonneg_left (hCA_nn 2)) ((le_max_right _ _).trans (le_max_right _ _))
        rw [Real.norm_eq_abs]
        have h1 : |rA t| ≤ C_rem_small * (M_th0_2 / τ₁) := by
          refine (hrA_small t ht18).trans ?_
          rw [mul_div_assoc]; exact mul_le_mul hCA_le hA_t (div_nonneg (abs_nonneg _) ht.1.le) hC_rem_nn
        have h2 : |rB t| ≤ C_rem_small * (M_th0_1 / τ₁) := by
          refine (hrB_small t ht18).trans ?_
          rw [mul_div_assoc]; exact mul_le_mul hCB_le hB_t (div_nonneg (abs_nonneg _) (sq_nonneg t)) hC_rem_nn
        have htri := abs_sub (rA t) (rB t)
        calc |rA t - rB t| ≤ C_rem_small * (M_th0_2 / τ₁) + C_rem_small * (M_th0_1 / τ₁) := by linarith
          _ = C_rem_small * (M_th0_2 + M_th0_1) / τ₁ := by ring
      have hint : IntegrableOn (fun t => rA t - rB t) (Ioc 0 (12 * τ₁)) :=
        (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
          (((hfA_cont.sub hsA_cont).sub (hfB_cont.sub hsB_cont) |>.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
          (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
      refine ⟨hint, ?_⟩
      have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hpt
      rw [Real.norm_eq_abs, Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)] at hbd
      refine hbd.trans (le_of_eq ?_); field_simp [hτ₁.ne']
    -- Bound `rA - rB` on `Ioc (12 τ₁) (1/8)` using `(fct:th-tail)` (`|ϑ_0''| ≤ C_tail 2 * M_L1_0 * τ₁^3 * t^{-3}`, `|ϑ_0'| ≤ C_tail 1 * M_L1_0 * τ₁^3 * t^{-2}`)!
    have hr_2 : IntegrableOn (fun t => rA t - rB t) (Ioc (12 * τ₁) (1 / 8)) ∧
        |∫ t in Ioc (12 * τ₁) (1 / 8), (rA t - rB t)| ≤
          C_rem_small * ((C_tail 2 + C_tail 1) * M_L1_0 * (1 / 12 ^ 2)) := by
      have hdom_int := FctPhiKill.integrableOn_inv_pow_Ioi (ε := 12 * τ₁) (by positivity) (m := 4) (by norm_num)
      set K2 : ℝ := C_rem_small * (C_tail 2 + C_tail 1) * M_L1_0 * τ₁ ^ 3
      have hpt : ∀ t ∈ Ioc (12 * τ₁) (1 / 8), ‖rA t - rB t‖ ≤ K2 * t ^ (-(4 : ℤ)) := by
        intro t ht
        have ht0 : 0 < t := lt_trans (by positivity) ht.1
        have ht18 : t ∈ Ioc (0 : ℝ) (1 / 8) := ⟨ht0, ht.2⟩
        have htl2 := (hth_tail 2 t (by rw [abs_of_pos ht0]; exact ht.1.le)).1
        have htl1 := (hth_tail 1 t (by rw [abs_of_pos ht0]; exact ht.1.le)).1
        rw [abs_of_pos ht0] at htl2 htl1
        have hexp1 : Real.exp (-(π / 2) * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) ht0.le)
        have h2' : |iteratedDeriv 2 (fctThetaD v0') t| / t ≤ C_tail 2 * M_L1_0 * τ₁ ^ 3 * t ^ (-(4 : ℤ)) := by
          have h := htl2.trans (mul_le_of_le_one_right (by have := (hCti_nn 2).1; positivity) hexp1)
          rw [show -(1 + ((2 : ℕ) : ℤ)) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast] at h
          rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]
          calc |iteratedDeriv 2 (fctThetaD v0') t| / t
              ≤ (C_tail 2 * M_L1_0 * τ₁ ^ 3 * (t ^ 3)⁻¹) / t := div_le_div_of_nonneg_right h ht0.le
            _ = C_tail 2 * M_L1_0 * τ₁ ^ 3 * (t ^ 4)⁻¹ := by field_simp [ht0.ne']
        have h1' : |deriv (fctThetaD v0') t| / t ^ 2 ≤ C_tail 1 * M_L1_0 * τ₁ ^ 3 * t ^ (-(4 : ℤ)) := by
          rw [← iteratedDeriv_one]
          have h := htl1.trans (mul_le_of_le_one_right (by have := (hCti_nn 1).1; positivity) hexp1)
          rw [show -(1 + ((1 : ℕ) : ℤ)) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast] at h
          rw [zpow_neg, show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]
          calc |iteratedDeriv 1 (fctThetaD v0') t| / t ^ 2
              ≤ (C_tail 1 * M_L1_0 * τ₁ ^ 3 * (t ^ 2)⁻¹) / t ^ 2 := div_le_div_of_nonneg_right h (sq_nonneg t)
            _ = C_tail 1 * M_L1_0 * τ₁ ^ 3 * (t ^ 4)⁻¹ := by field_simp [ht0.ne']
        have hCA_le : C_A p ≤ C_rem_small := by
          interval_cases p
          · exact le_trans (le_add_of_nonneg_right (hCB_nn 0)) (le_max_left _ _)
          · exact le_trans (le_add_of_nonneg_right (hCB_nn 1)) ((le_max_left _ _).trans (le_max_right _ _))
          · exact le_trans (le_add_of_nonneg_right (hCB_nn 2)) ((le_max_right _ _).trans (le_max_right _ _))
        have hCB_le : C_B p ≤ C_rem_small := by
          interval_cases p
          · exact le_trans (le_add_of_nonneg_left (hCA_nn 0)) (le_max_left _ _)
          · exact le_trans (le_add_of_nonneg_left (hCA_nn 1)) ((le_max_left _ _).trans (le_max_right _ _))
          · exact le_trans (le_add_of_nonneg_left (hCA_nn 2)) ((le_max_right _ _).trans (le_max_right _ _))
        rw [Real.norm_eq_abs]
        have ha : |rA t| ≤ C_rem_small * (C_tail 2 * M_L1_0 * τ₁ ^ 3 * t ^ (-(4 : ℤ))) := by
          refine (hrA_small t ht18).trans ?_
          rw [mul_div_assoc]; exact mul_le_mul hCA_le h2' (div_nonneg (abs_nonneg _) ht0.le) hC_rem_nn
        have hb : |rB t| ≤ C_rem_small * (C_tail 1 * M_L1_0 * τ₁ ^ 3 * t ^ (-(4 : ℤ))) := by
          refine (hrB_small t ht18).trans ?_
          rw [mul_div_assoc]; exact mul_le_mul hCB_le h1' (div_nonneg (abs_nonneg _) (sq_nonneg t)) hC_rem_nn
        have htri := abs_sub (rA t) (rB t)
        dsimp only [K2]
        linarith [show C_rem_small * (C_tail 2 + C_tail 1) * M_L1_0 * τ₁ ^ 3 * t ^ (-(4 : ℤ)) =
          C_rem_small * (C_tail 2 * M_L1_0 * τ₁ ^ 3 * t ^ (-(4 : ℤ))) +
          C_rem_small * (C_tail 1 * M_L1_0 * τ₁ ^ 3 * t ^ (-(4 : ℤ))) by ring]
      have hint : IntegrableOn (fun t => rA t - rB t) (Ioc (12 * τ₁) (1 / 8)) :=
        ((hdom_int.1.mono_set Ioc_subset_Ioi_self).const_mul K2).mono'
          ((((hfA_cont.sub hsA_cont).sub (hfB_cont.sub hsB_cont)).mono
            (show Ioc (12 * τ₁) (1 / 8) ⊆ Ioi 0 from fun t ht => lt_trans (by positivity) ht.1)).aestronglyMeasurable measurableSet_Ioc)
          (ae_restrict_of_forall_mem measurableSet_Ioc hpt)
      refine ⟨hint, ?_⟩
      have hmono : |∫ t in Ioc (12 * τ₁) (1 / 8), (rA t - rB t)| ≤ ∫ t in Ioi (12 * τ₁), K2 * t ^ (-(4 : ℤ)) :=
        (norm_integral_le_integral_norm _).trans ((setIntegral_mono_on hint.norm
          ((hdom_int.1.mono_set Ioc_subset_Ioi_self).const_mul K2) measurableSet_Ioc hpt).trans
          (setIntegral_mono_set (hdom_int.1.const_mul K2)
            (Filter.Eventually.of_forall fun t => by
              have hK2 : 0 ≤ K2 := by have := (hCti_nn 1).1; have := (hCti_nn 2).1; positivity
              exact mul_nonneg hK2 (by
                rw [zpow_neg, zpow_natCast]
                exact inv_nonneg.mpr (even_iff_two_dvd.mpr ⟨2, rfl⟩ |>.pow_nonneg t)))
            (Filter.Eventually.of_forall Ioc_subset_Ioi_self)))
      have hdom_eq : (∫ t in Ioi (12 * τ₁), t ^ (-(4 : ℤ))) = (12 * τ₁) ^ (1 - (4 : ℤ)) / ((4 : ℝ) - 1) := by
        simpa using hdom_int.2
      rw [integral_const_mul, hdom_eq] at hmono
      refine hmono.trans ?_
      have hval : K2 * ((12 * τ₁) ^ (1 - (4 : ℤ)) / ((4 : ℝ) - 1)) =
          (1 / (3 * 12)) * (C_rem_small * ((C_tail 2 + C_tail 1) * M_L1_0 * (1 / 12 ^ 2))) := by
        dsimp only [K2]
        rw [show (1 : ℤ) - 4 = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
        field_simp [hτ₁.ne']; ring
      rw [hval]
      have hnn : 0 ≤ C_rem_small * ((C_tail 2 + C_tail 1) * M_L1_0 * (1 / 12 ^ 2)) := by
        have := (hCti_nn 1).1; have := (hCti_nn 2).1; positivity
      linarith
    -- Bound `rA - rB = (fA - fB) - (sA - sB)` on `Ioi (1/8)`!
    have hr_3 : IntegrableOn (fun t => rA t - rB t) (Ioi (1 / 8)) ∧
        |∫ t in Ioi (1 / 8), (rA t - rB t)| ≤
          32 * (72 * (1 + π ^ 2 / 4) * (1 / (min 1 (uctM (1 / 8)) ^ 2)) * (1 / c_D + 1 / uctM (1 / 8)) *
            (C_tail 2 + C_tail 1) * M_L1_0 +
            S_coeff * (C_tail 2 + C_tail 1) * M_L1_0 * (8 : ℝ) ^ 7) := by
      have hdom_int := FctPhiKill.integrableOn_inv_pow_Ioi (ε := 1 / 8) (by norm_num) (m := 3) (by norm_num)
      set K3 : ℝ := 72 * (1 + π ^ 2 / 4) * (1 / (min 1 (uctM (1 / 8)) ^ 2)) * (1 / c_D + 1 / uctM (1 / 8)) *
          (C_tail 2 + C_tail 1) * M_L1_0 + S_coeff * (C_tail 2 + C_tail 1) * M_L1_0 * (8 : ℝ) ^ 7
      have hK3_nn : 0 ≤ K3 := by
        have := (hCti_nn 1).1; have := (hCti_nn 2).1; positivity
      have hpt : ∀ t ∈ Ioi (1 / 8 : ℝ), ‖rA t - rB t‖ ≤ K3 * t ^ (-(3 : ℤ)) := by
        intro t ht
        have ht0 : 0 < t := lt_trans (by norm_num) ht
        have ht12 : 12 * τ₁ ≤ |t| := by rw [abs_of_pos ht0]; linarith [h12_lt, show 1 / 8 < t from ht]
        have htl2 := (hth_tail 2 t ht12).1
        have htl1 := (hth_tail 1 t ht12).1
        rw [abs_of_pos ht0] at htl2 htl1
        have hexp1 : Real.exp (-(π / 2) * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) ht0.le)
        have hτ3 : τ₁ ^ 3 ≤ 1 := pow_le_one₀ hτ₁.le hτ₁_1
        have hθ2_bd : |iteratedDeriv 2 (fctThetaD v0') t| ≤ C_tail 2 * M_L1_0 * t ^ (-(3 : ℤ)) := by
          have h := htl2.trans (mul_le_of_le_one_right (by have := (hCti_nn 2).1; positivity) hexp1)
          rw [show -(1 + ((2 : ℕ) : ℤ)) = (-3 : ℤ) by norm_num] at h
          refine h.trans (mul_le_mul_of_nonneg_right ?_ (zpow_nonneg ht0.le _))
          exact mul_le_of_le_one_right (mul_nonneg (hCti_nn 2).1 hM_L1_0_nn) hτ3
        have hθ1_bd : |deriv (fctThetaD v0') t| ≤ C_tail 1 * M_L1_0 * t ^ (-(2 : ℤ)) := by
          rw [← iteratedDeriv_one]
          have h := htl1.trans (mul_le_of_le_one_right (by have := (hCti_nn 1).1; positivity) hexp1)
          rw [show -(1 + ((1 : ℕ) : ℤ)) = (-2 : ℤ) by norm_num] at h
          refine h.trans (mul_le_mul_of_nonneg_right ?_ (zpow_nonneg ht0.le _))
          exact mul_le_of_le_one_right (mul_nonneg (hCti_nn 1).1 hM_L1_0_nn) hτ3
        have hm_ge : uctM (1 / 8) ≤ uctM t := uctM_strictMonoOn.monotoneOn (by norm_num) ht0 (le_of_lt ht)
        have hmp_ge : min 1 (uctM (1 / 8)) ^ 2 ≤ uctM t ^ p := by
          have h1 : min 1 (uctM (1 / 8)) ≤ uctM t := (min_le_right _ _).trans hm_ge
          have hmin_nn : 0 ≤ min 1 (uctM (1 / 8)) := le_min zero_le_one hm_18.le
          have hmin_le1 : min 1 (uctM (1 / 8)) ≤ 1 := min_le_left _ _
          exact (pow_le_pow_of_le_one hmin_nn hmin_le1 hp2).trans (pow_le_pow_left₀ hmin_nn h1 p)
        have hmp_pos : 0 < min 1 (uctM (1 / 8)) ^ 2 := sq_pos_of_pos (lt_min zero_lt_one hm_18)
        have hH := (norm_stripH0_imag_le kind ht0).1
        have hmd := hc_D_bd t (le_of_lt ht)
        have hinv_t : t⁻¹ ≤ 8 := by rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [show 1 / 8 < t from ht]
        have hfA_bd : |fA t| ≤ 72 * (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / c_D) *
            C_tail 2 * M_L1_0 * t ^ (-(3 : ℤ)) := by
          dsimp only [fA]; rw [abs_mul, abs_div, abs_of_nonneg (norm_nonneg _),
            abs_of_pos (mul_pos (pow_pos (uctM_pos ht0) p) (uctMderiv_pos ht0))]
          have h1t : (1 + t) / t ^ 2 ≤ 72 := by
            have ht18 : 1 / 8 < t := ht
            have h1 : 1 / t ≤ 8 := by rw [div_le_iff₀ ht0]; linarith
            have h2 : 1 / t ^ 2 ≤ 64 := by
              rw [div_le_iff₀ (sq_pos_of_pos ht0)]
              have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) ht18.le 2; linarith
            rw [add_div, show t / t ^ 2 = 1 / t by field_simp [ht0.ne']]; linarith
          calc ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / (uctM t ^ p * uctMderiv t) * |iteratedDeriv 2 (fctThetaD v0') t|
              ≤ ((1 + π ^ 2 / 4) / t ^ 2) / (min 1 (uctM (1 / 8)) ^ 2 * (c_D / (1 + t))) *
                  (C_tail 2 * M_L1_0 * t ^ (-(3 : ℤ))) := by
                refine mul_le_mul ?_ hθ2_bd (abs_nonneg _) (by positivity)
                exact div_le_div₀ (by positivity) hH (by positivity) (mul_le_mul hmp_ge hmd (by positivity) (pow_nonneg (uctM_pos ht0).le p))
            _ = (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / c_D) *
                  ((1 + t) / t ^ 2) * (C_tail 2 * M_L1_0 * t ^ (-(3 : ℤ))) := by
                field_simp [ht0.ne', hmp_pos.ne', hc_D_pos.ne']
            _ ≤ (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / c_D) *
                  72 * (C_tail 2 * M_L1_0 * t ^ (-(3 : ℤ))) := by
                have := (hCti_nn 2).1; gcongr
            _ = 72 * (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / c_D) *
                  C_tail 2 * M_L1_0 * t ^ (-(3 : ℤ)) := by ring
        have hfB_bd : |fB t| ≤ 72 * (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / uctM (1 / 8)) *
            C_tail 1 * M_L1_0 * t ^ (-(3 : ℤ)) := by
          dsimp only [fB]; rw [abs_mul, abs_div, abs_of_nonneg (norm_nonneg _),
            abs_of_pos (pow_pos (uctM_pos ht0) (p + 1))]
          have hpow1 : min 1 (uctM (1 / 8)) ^ 2 * uctM (1 / 8) ≤ uctM t ^ (p + 1) := by
            rw [pow_succ]; exact mul_le_mul hmp_ge hm_ge hm_18.le (pow_nonneg (uctM_pos ht0).le p)
          have ht4 : t ^ (-(2 : ℤ)) / t ^ 2 ≤ 72 * t ^ (-(3 : ℤ)) := by
            rw [zpow_neg, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl,
              zpow_natCast, zpow_natCast, div_eq_mul_inv]
            have h1 : (t ^ 2)⁻¹ * (t ^ 2)⁻¹ = t⁻¹ * (t ^ 3)⁻¹ := by field_simp [ht0.ne']
            rw [h1]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          calc ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ (p + 1) * |deriv (fctThetaD v0') t|
              ≤ ((1 + π ^ 2 / 4) / t ^ 2) / (min 1 (uctM (1 / 8)) ^ 2 * uctM (1 / 8)) *
                  (C_tail 1 * M_L1_0 * t ^ (-(2 : ℤ))) := by
                refine mul_le_mul ?_ hθ1_bd (abs_nonneg _) (by positivity)
                exact div_le_div₀ (by positivity) hH (by positivity) hpow1
            _ = (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / uctM (1 / 8)) *
                  C_tail 1 * M_L1_0 * (t ^ (-(2 : ℤ)) / t ^ 2) := by
                field_simp [ht0.ne', hmp_pos.ne', hm_18.ne']
            _ ≤ (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / uctM (1 / 8)) *
                  C_tail 1 * M_L1_0 * (72 * t ^ (-(3 : ℤ))) := by
                have := (hCti_nn 1).1; gcongr
            _ = 72 * (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / uctM (1 / 8)) *
                  C_tail 1 * M_L1_0 * t ^ (-(3 : ℤ)) := by ring
        have hS_p_le : (∑ j : Fin (p + 1), (|aA p j| + |bB p j|)) ≤ S_coeff := by
          dsimp only [S_coeff]
          have h0 : 0 ≤ ∑ j : Fin 1, (|aA 0 j| + |bB 0 j|) := Finset.sum_nonneg fun _ _ => by positivity
          have h1 : 0 ≤ ∑ j : Fin 2, (|aA 1 j| + |bB 1 j|) := Finset.sum_nonneg fun _ _ => by positivity
          have h2 : 0 ≤ ∑ j : Fin 3, (|aA 2 j| + |bB 2 j|) := Finset.sum_nonneg fun _ _ => by positivity
          interval_cases p <;> linarith
        have hsA_bd : |sA t| ≤ (∑ j : Fin (p + 1), |aA p j|) * C_tail 2 * M_L1_0 * (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) := by
          dsimp only [sA]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_div, abs_pow, abs_of_pos ht0]
          have hpow_le : (t ^ (2 * (p + 1 - j.1) + 1))⁻¹ ≤ (8 : ℝ) ^ 7 := by
            have hk : 2 * (p + 1 - j.1) + 1 ≤ 7 := by omega
            calc (t ^ (2 * (p + 1 - j.1) + 1))⁻¹ = (t⁻¹) ^ (2 * (p + 1 - j.1) + 1) := (inv_pow _ _).symm
              _ ≤ (8 : ℝ) ^ (2 * (p + 1 - j.1) + 1) := pow_le_pow_left₀ (by positivity) hinv_t _
              _ ≤ (8 : ℝ) ^ 7 := pow_le_pow_right₀ (by norm_num) hk
          rw [div_eq_mul_inv]
          calc |aA p j| * (|iteratedDeriv 2 (fctThetaD v0') t| * (t ^ (2 * (p + 1 - j.1) + 1))⁻¹)
              ≤ |aA p j| * ((C_tail 2 * M_L1_0 * t ^ (-(3 : ℤ))) * (8 : ℝ) ^ 7) := by
                have := (hCti_nn 2).1; gcongr
            _ = |aA p j| * C_tail 2 * M_L1_0 * (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) := by ring
        have hsB_bd : |sB t| ≤ (∑ j : Fin (p + 1), |bB p j|) * C_tail 1 * M_L1_0 * (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) := by
          dsimp only [sB]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_div, abs_pow, abs_of_pos ht0]
          have hpow_le : (t ^ (2 * (p + 1 - j.1) + 2))⁻¹ * t ^ (-(2 : ℤ)) ≤ (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) := by
            have hk : 2 * (p + 1 - j.1) + 1 ≤ 7 := by omega
            have h1 : (t ^ (2 * (p + 1 - j.1) + 2))⁻¹ * t ^ (-(2 : ℤ)) =
                (t⁻¹) ^ (2 * (p + 1 - j.1) + 1) * t ^ (-(3 : ℤ)) := by
              rw [zpow_neg, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl,
                zpow_natCast, zpow_natCast, inv_pow, show 2 * (p + 1 - j.1) + 2 = (2 * (p + 1 - j.1) + 1) + 1 by omega,
                pow_succ]; field_simp [ht0.ne']
            rw [h1]
            exact mul_le_mul_of_nonneg_right
              ((pow_le_pow_left₀ (by positivity) hinv_t _).trans (pow_le_pow_right₀ (by norm_num) hk))
              (zpow_nonneg ht0.le _)
          rw [div_eq_mul_inv]
          calc |bB p j| * (|deriv (fctThetaD v0') t| * (t ^ (2 * (p + 1 - j.1) + 2))⁻¹)
              ≤ |bB p j| * ((C_tail 1 * M_L1_0 * t ^ (-(2 : ℤ))) * (t ^ (2 * (p + 1 - j.1) + 2))⁻¹) := by
                have := (hCti_nn 1).1; gcongr
            _ = |bB p j| * C_tail 1 * M_L1_0 * ((t ^ (2 * (p + 1 - j.1) + 2))⁻¹ * t ^ (-(2 : ℤ))) := by ring
            _ ≤ |bB p j| * C_tail 1 * M_L1_0 * ((8 : ℝ) ^ 7 * t ^ (-(3 : ℤ))) := by
                have := (hCti_nn 1).1; gcongr
            _ = |bB p j| * C_tail 1 * M_L1_0 * (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) := by ring
        have htri : ‖rA t - rB t‖ ≤ |fA t| + |fB t| + |sA t| + |sB t| := by
          rw [Real.norm_eq_abs]; dsimp only [rA, rB]
          have a1 := abs_sub (fA t - sA t) (fB t - sB t)
          have a2 := abs_sub (fA t) (sA t)
          have a3 := abs_sub (fB t) (sB t)
          linarith
        have hsum_A : (∑ j : Fin (p + 1), |aA p j|) ≤ S_coeff :=
          (Finset.sum_le_sum fun j _ => le_add_of_nonneg_right (abs_nonneg (bB p j))).trans hS_p_le
        have hsum_B : (∑ j : Fin (p + 1), |bB p j|) ≤ S_coeff :=
          (Finset.sum_le_sum fun j _ => le_add_of_nonneg_left (abs_nonneg (aA p j))).trans hS_p_le
        have hC2_le : C_tail 2 ≤ C_tail 2 + C_tail 1 := le_add_of_nonneg_right (hCti_nn 1).1
        have hC1_le : C_tail 1 ≤ C_tail 2 + C_tail 1 := le_add_of_nonneg_left (hCti_nn 2).1
        have hfAB : |fA t| + |fB t| ≤ 72 * (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) *
            (1 / c_D + 1 / uctM (1 / 8)) * (C_tail 2 + C_tail 1) * M_L1_0 * t ^ (-(3 : ℤ)) := by
          have ha' : |fA t| ≤ 72 * (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / c_D) *
              (C_tail 2 + C_tail 1) * M_L1_0 * t ^ (-(3 : ℤ)) :=
            hfA_bd.trans (by gcongr)
          have hb' : |fB t| ≤ 72 * (1 + π ^ 2 / 4) * (1 / min 1 (uctM (1 / 8)) ^ 2) * (1 / uctM (1 / 8)) *
              (C_tail 2 + C_tail 1) * M_L1_0 * t ^ (-(3 : ℤ)) :=
            hfB_bd.trans (by gcongr)
          linarith
        have hsAB : |sA t| + |sB t| ≤ S_coeff * (C_tail 2 + C_tail 1) * M_L1_0 * (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) := by
          have h1 : (∑ j : Fin (p + 1), |aA p j|) * C_tail 2 + (∑ j : Fin (p + 1), |bB p j|) * C_tail 1 ≤
              S_coeff * (C_tail 2 + C_tail 1) := by
            have := mul_le_mul_of_nonneg_right hsum_A (hCti_nn 2).1
            have := mul_le_mul_of_nonneg_right hsum_B (hCti_nn 1).1
            linarith
          have h2 := mul_le_mul_of_nonneg_right h1
            (mul_nonneg hM_L1_0_nn (mul_nonneg (by positivity : (0 : ℝ) ≤ (8 : ℝ) ^ 7) (zpow_nonneg ht0.le (-(3 : ℤ)))))
          calc |sA t| + |sB t|
              ≤ (∑ j : Fin (p + 1), |aA p j|) * C_tail 2 * M_L1_0 * (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) +
                (∑ j : Fin (p + 1), |bB p j|) * C_tail 1 * M_L1_0 * (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) :=
                add_le_add hsA_bd hsB_bd
            _ = ((∑ j : Fin (p + 1), |aA p j|) * C_tail 2 + (∑ j : Fin (p + 1), |bB p j|) * C_tail 1) *
                (M_L1_0 * ((8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)))) := by ring
            _ ≤ S_coeff * (C_tail 2 + C_tail 1) * (M_L1_0 * ((8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)))) := h2
            _ = S_coeff * (C_tail 2 + C_tail 1) * M_L1_0 * (8 : ℝ) ^ 7 * t ^ (-(3 : ℤ)) := by ring
        dsimp only [K3]; linarith
      have hint : IntegrableOn (fun t => rA t - rB t) (Ioi (1 / 8)) :=
        (hdom_int.1.const_mul K3).mono'
          (((hfA_cont.sub hsA_cont).sub (hfB_cont.sub hsB_cont) |>.mono fun t ht => lt_trans (by norm_num) ht).aestronglyMeasurable measurableSet_Ioi)
          (ae_restrict_of_forall_mem measurableSet_Ioi hpt)
      refine ⟨hint, ?_⟩
      have hmono : |∫ t in Ioi (1 / 8 : ℝ), (rA t - rB t)| ≤ ∫ t in Ioi (1 / 8 : ℝ), K3 * t ^ (-(3 : ℤ)) :=
        (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hint.norm (hdom_int.1.const_mul K3) measurableSet_Ioi hpt)
      have hdom_eq : (∫ t in Ioi (1 / 8 : ℝ), t ^ (-(3 : ℤ))) = (1 / 8 : ℝ) ^ (1 - (3 : ℤ)) / ((3 : ℝ) - 1) := by
        simpa using hdom_int.2
      rw [integral_const_mul, hdom_eq] at hmono
      refine hmono.trans (le_of_eq ?_)
      have hval : ((1 / 8 : ℝ) ^ (1 - (3 : ℤ)) / ((3 : ℝ) - 1)) = 32 := by
        rw [show (1 : ℤ) - 3 = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]; norm_num
      rw [hval]; ring
    -- Combine `sA - sB` + `rA - rB` on `Ioi 0`!
    have hr_all_int : IntegrableOn (fun t => rA t - rB t) (Ioi 0) := by
      rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 / 8 by norm_num), integrableOn_union,
        ← Ioc_union_Ioc_eq_Ioc (show (0 : ℝ) ≤ 12 * τ₁ by positivity) h12_lt.le, integrableOn_union]
      exact ⟨⟨hr_1.1, hr_2.1⟩, hr_3.1⟩
    have hfAB_int : IntegrableOn (fun t => fA t - fB t) (Ioi 0) := by
      have hrew : (fun t => fA t - fB t) = fun t => (sA t - sB t) + (rA t - rB t) := by
        ext t; dsimp only [rA, rB]; ring
      rw [hrew]; exact (hsA_int.1.sub hsB_int.1).add hr_all_int
    have hfAB_bd : |∫ t in Ioi (0 : ℝ), (fA t - fB t)| ≤
        S_coeff * (2 * M_cauchy) +
        C_rem_small * (12 * (M_th0_2 + M_th0_1) + (C_tail 2 + C_tail 1) * M_L1_0 * (1 / 12 ^ 2)) +
        32 * (72 * (1 + π ^ 2 / 4) * (1 / (min 1 (uctM (1 / 8)) ^ 2)) * (1 / c_D + 1 / uctM (1 / 8)) *
          (C_tail 2 + C_tail 1) * M_L1_0 + S_coeff * (C_tail 2 + C_tail 1) * M_L1_0 * (8 : ℝ) ^ 7) := by
      have hrew : (fun t => fA t - fB t) = fun t => (sA t - sB t) + (rA t - rB t) := by
        ext t; dsimp only [rA, rB]; ring
      have hsAB_int : IntegrableOn (fun t => sA t - sB t) (Ioi 0) := hsA_int.1.sub hsB_int.1
      rw [hrew, integral_add hsAB_int hr_all_int,
        show (∫ t in Ioi (0 : ℝ), (sA t - sB t)) = (∫ t in Ioi (0 : ℝ), sA t) - ∫ t in Ioi (0 : ℝ), sB t from
          integral_sub hsA_int.1 hsB_int.1]
      have hr_split : (∫ t in Ioi (0 : ℝ), (rA t - rB t)) =
          (∫ t in Ioc 0 (12 * τ₁), (rA t - rB t)) + (∫ t in Ioc (12 * τ₁) (1 / 8), (rA t - rB t)) +
            ∫ t in Ioi (1 / 8), (rA t - rB t) := by
        rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 / 8 by norm_num),
          setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
            measurableSet_Ioi (hr_all_int.mono_set Ioc_subset_Ioi_self) hr_3.1,
          ← Ioc_union_Ioc_eq_Ioc (show (0 : ℝ) ≤ 12 * τ₁ by positivity) h12_lt.le,
          setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1])
            measurableSet_Ioc hr_1.1 hr_2.1]
      have hS_p_le : (∑ j : Fin (p + 1), |aA p j|) + (∑ j : Fin (p + 1), |bB p j|) ≤ S_coeff := by
        rw [← Finset.sum_add_distrib]
        dsimp only [S_coeff]
        have h0 : 0 ≤ ∑ j : Fin 1, (|aA 0 j| + |bB 0 j|) := Finset.sum_nonneg fun _ _ => by positivity
        have h1 : 0 ≤ ∑ j : Fin 2, (|aA 1 j| + |bB 1 j|) := Finset.sum_nonneg fun _ _ => by positivity
        have h2 : 0 ≤ ∑ j : Fin 3, (|aA 2 j| + |bB 2 j|) := Finset.sum_nonneg fun _ _ => by positivity
        interval_cases p <;> linarith
      have hs_bd : |(∫ t in Ioi (0 : ℝ), sA t) - ∫ t in Ioi (0 : ℝ), sB t| ≤ S_coeff * (2 * M_cauchy) := by
        have h1 := (abs_sub _ _).trans (add_le_add hsA_int.2 hsB_int.2)
        have h2 : (∑ j : Fin (p + 1), |aA p j|) * M_cauchy + (∑ j : Fin (p + 1), |bB p j|) * M_cauchy ≤
            S_coeff * M_cauchy := by
          rw [← add_mul]; exact mul_le_mul_of_nonneg_right hS_p_le hM_cauchy_nn
        have h3 : S_coeff * M_cauchy ≤ S_coeff * (2 * M_cauchy) := by
          have : 0 ≤ S_coeff * M_cauchy := mul_nonneg hS_coeff_nn hM_cauchy_nn; linarith
        linarith
      have hr_bd : |∫ t in Ioi (0 : ℝ), (rA t - rB t)| ≤
          C_rem_small * (12 * (M_th0_2 + M_th0_1) + (C_tail 2 + C_tail 1) * M_L1_0 * (1 / 12 ^ 2)) +
          32 * (72 * (1 + π ^ 2 / 4) * (1 / (min 1 (uctM (1 / 8)) ^ 2)) * (1 / c_D + 1 / uctM (1 / 8)) *
            (C_tail 2 + C_tail 1) * M_L1_0 + S_coeff * (C_tail 2 + C_tail 1) * M_L1_0 * (8 : ℝ) ^ 7) := by
        rw [hr_split]
        refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
        linarith [hr_1.2, hr_2.2, hr_3.2]
      exact (abs_add_le _ _).trans ((add_le_add hs_bd hr_bd).trans (le_of_eq (by ring)))
    -- Translate `fA - fB` back to `L`-integral `∫_0^∞ I_osc^{H_0}(L) Δ_curv(τ₀(L)) / L^p dL`!
    have hL_eq_t : ∀ t : ℝ, 0 < t →
        uctMderiv t * (stripIosc kind (uctM t) * stripDeltaCurv c (fctThetaD v0') (tau0 (uctM t)) / uctM t ^ p) =
          (uctAlphaOsc / (2 * c)) * (fA t - fB t) := by
      intro t ht
      rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht]
      have h1 := uctMderiv_mul_stripIosc kind ht
      rw [show uctM t = ceEll (π * t / 2) from rfl] at h1
      unfold stripDeltaCurv; dsimp only [fA, fB]
      have hm_ne : uctM t ≠ 0 := (uctM_pos ht).ne'
      have hmd_ne : uctMderiv t ≠ 0 := (uctMderiv_pos ht).ne'
      rw [show ceEll (π * t / 2) = uctM t from rfl] at h1 ⊢
      have hmul : uctMderiv t * (stripIosc kind (uctM t) *
          (1 / (2 * c) * (iteratedDeriv 2 (fctThetaD v0') t / uctMderiv t - deriv (fctThetaD v0') t / uctM t)) / uctM t ^ p) =
          (uctMderiv t * stripIosc kind (uctM t)) * (1 / (2 * c)) *
          ((iteratedDeriv 2 (fctThetaD v0') t / uctMderiv t - deriv (fctThetaD v0') t / uctM t) / uctM t ^ p) := by ring
      rw [hmul, h1, pow_succ]
      field_simp [hc.ne', hm_ne, hmd_ne]
    have hcurv_L_int : IntegrableOn (fun L : ℝ => stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L) / L ^ p) (Ioi 0) := by
      rw [uct_subst_integrableOn_zero]
      exact IntegrableOn.congr_fun (hfAB_int.const_mul (uctAlphaOsc / (2 * c))) (fun t ht => (hL_eq_t t ht).symm) measurableSet_Ioi
    have hcurv_L_bd : |∫ L in Ioi (0 : ℝ), stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L) / L ^ p| ≤ C_p_curv * c⁻¹ := by
      rw [uct_subst_zero, setIntegral_congr_fun measurableSet_Ioi hL_eq_t, integral_const_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ uctAlphaOsc / (2 * c))]
      have h1 := mul_le_mul_of_nonneg_left hfAB_bd (by positivity : 0 ≤ uctAlphaOsc / (2 * c))
      refine h1.trans (le_of_eq ?_); dsimp only [C_p_curv]; field_simp [hc.ne']
    -- 2. Cross-term bound on `Ioc 0 (10 τ₁)`!
    have hv_abs_0 : ∀ t : ℝ, |v t| ≤ M_v0_0 * τ₁ ^ 2 := by
      intro t
      obtain ⟨d1, d2, d3, d4, d5⟩ := hderivs 0 t
      simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at d1 d2 d3 d4 d5
      have hα1 : |α| ≤ 1 := hα_le.trans (pow_le_one₀ hτ₁.le hτ₁_1)
      have hτ4 : τ₁ ^ (4 : ℤ) ≤ τ₁ ^ 2 := by
        rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
      have h1b : c⁻¹ * τ₁ ^ (-1 : ℤ) ≤ τ₁ ^ 2 := by
        rw [hc_inv, zpow_neg_one, show τ₁ ^ 4 * τ₁⁻¹ = τ₁ ^ 3 by field_simp [hτ₁.ne']]
        exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
      have h1m : c⁻¹ * τ₁ ^ (1 : ℤ) ≤ τ₁ ^ 2 := by
        rw [hc_inv, zpow_one, ← pow_succ]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
      have d1' : |v0Base kind τ₁ t| ≤ Cv0b 0 * τ₁ ^ 2 := by simpa [zpow_two, ← sq] using d1
      have d2' : |v0Marg τ₁ t| ≤ Cv0m 0 * τ₁ ^ 2 := d2.trans (mul_le_mul_of_nonneg_left hτ4 (hCv_nn 0).2.1)
      have d3' : |vAlpha α τ₁ t| ≤ Cva 0 * τ₁ ^ 2 := d3.trans (by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
        have := mul_le_mul_of_nonneg_left hα1 (hCv_nn 0).2.2.1; rw [mul_one] at this
        exact mul_le_mul_of_nonneg_right this (sq_nonneg τ₁))
      have d4' : |v1Base kind c τ₁ t| ≤ Cv1b 0 * τ₁ ^ 2 := d4.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1b (hCv_nn 0).2.2.2.1)
      have d5' : |v1Marg c τ₁ t| ≤ Cv1m 0 * τ₁ ^ 2 := d5.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1m (hCv_nn 0).2.2.2.2)
      have htri : |v t| ≤ |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t| + |v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t| + |vAlpha α τ₁ t| := by
        dsimp only [v]; unfold vTotal v0 v1
        have a1 := abs_add_le ((v0Base kind τ₁ t + K4 * v0Marg τ₁ t) + (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)) (vAlpha α τ₁ t)
        have a2 := abs_add_le (v0Base kind τ₁ t + K4 * v0Marg τ₁ t) (v1Base kind c τ₁ t + K4 * v1Marg c τ₁ t)
        have a3 := abs_add_le (v0Base kind τ₁ t) (K4 * v0Marg τ₁ t)
        have a4 := abs_add_le (v1Base kind c τ₁ t) (K4 * v1Marg c τ₁ t)
        rw [abs_mul, abs_of_nonneg hK4_nn] at a3 a4; linarith
      have hm1 := mul_le_mul_of_nonneg_left d2' hK4_nn
      have hm2 := mul_le_mul_of_nonneg_left d5' hK4_nn
      calc |v t| ≤ |v0Base kind τ₁ t| + K4 * |v0Marg τ₁ t| + |v1Base kind c τ₁ t| + K4 * |v1Marg c τ₁ t| + |vAlpha α τ₁ t| := htri
        _ ≤ Cv0b 0 * τ₁ ^ 2 + K4 * (Cv0m 0 * τ₁ ^ 2) + Cv1b 0 * τ₁ ^ 2 + K4 * (Cv1m 0 * τ₁ ^ 2) + Cva 0 * τ₁ ^ 2 :=
            add_le_add (add_le_add (add_le_add (add_le_add d1' hm1) d4') hm2) d3'
        _ = M_v0_0 * τ₁ ^ 2 := by dsimp only [M_v0_0]; ring
    have hcross_pt : ∀ t ∈ Ioc (0 : ℝ) (10 * τ₁),
        ‖‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p * |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|‖ ≤
          (1 + π ^ 2 / 4) * (1 / min 1 mQ_min ^ 2) * (Real.exp M_v0_0 * M_v0_0) *
            ((1 / 2) * (M_th0_2 / mD_min + M_th0_1 / mQ_min)) * c⁻¹ * τ₁ ^ (-(2 * (p : ℤ)) - 1) := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have ht18 : t ≤ 1 / 8 := by linarith [ht.2, hτ₁_100]
      have ht14 : t < 1 / 4 := by linarith
      have hH := (norm_stripH0_imag_le kind ht0).1
      have hmQ_ge : mQ_min ≤ mQ t := hmQ_min_bd t ⟨ht0.le, ht18⟩
      have hmD_ge : mD_min ≤ mD t := hmD_min_bd t ⟨ht0.le, ht18⟩
      have hmp_ge : min 1 mQ_min ^ 2 * t ^ (2 * p) ≤ uctM t ^ p := by
        rw [uctM_eq_sq_mul_mQ ht0, mul_pow, ← pow_mul, mul_comm]
        have hmin_nn : 0 ≤ min 1 mQ_min := le_min zero_le_one hmQ_min_pos.le
        have h1 : min 1 mQ_min ^ 2 ≤ mQ t ^ p :=
          (pow_le_pow_of_le_one hmin_nn (min_le_left _ _) hp2).trans (pow_le_pow_left₀ hmin_nn ((min_le_right _ _).trans hmQ_ge) p)
        exact mul_le_mul_of_nonneg_left h1 (pow_nonneg ht0.le _)
      have hexp1 : |Real.exp (v t) - 1| ≤ Real.exp M_v0_0 * M_v0_0 * τ₁ ^ 2 := by
        have h1 := norm_cexp_sub_one_le (w := (v t : ℂ)) (M := M_v0_0) (by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact (hv_abs_0 t).trans (mul_le_of_le_one_right hM_v0_0_nn (pow_le_one₀ hτ₁.le hτ₁_1)))
        rw [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h1
        exact h1.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hv_abs_0 t) (Real.exp_pos _).le)
      -- Bound `|Δ_curv(t)| ≤ (1/(2c)) * (M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁⁻¹ * min 1 ((t/τ₁)^8)`!
      have hθ := hθ0_in t (by rw [abs_of_pos ht0]; linarith [ht.2])
      have hΔ_bd : |stripDeltaCurv c (fctThetaD v0') t| / t ^ (2 * p + 2) ≤
          (1 / (2 * c)) * (M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁ ^ (-(2 * (p : ℤ)) - 3) := by
        unfold stripDeltaCurv
        rw [uctMderiv_eq_mul_mD ht0 ht14, uctM_eq_sq_mul_mQ ht0, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * c))]
        have hmin8 : |iteratedDeriv 2 (fctThetaD v0') t| / (t * mD t) + |deriv (fctThetaD v0') t| / (t ^ 2 * mQ t) ≤
            (M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁⁻¹ * min 1 ((t / τ₁) ^ 8) := by
          rcases le_or_gt t τ₁ with hle | hgt
          · have h2 : |iteratedDeriv 2 (fctThetaD v0') t| / (t * mD t) ≤ (M_th0_2 / mD_min) * τ₁⁻¹ * (t / τ₁) ^ 8 := by
              have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 9) ≤ (t / τ₁) ^ 9 := by rw [abs_of_pos ht0]; exact min_le_right _ _
              have h : |iteratedDeriv 2 (fctThetaD v0') t| ≤ M_th0_2 * (t / τ₁) ^ 9 :=
                hθ.2.trans (mul_le_mul_of_nonneg_left hmin hM_th0_2_nn)
              calc |iteratedDeriv 2 (fctThetaD v0') t| / (t * mD t)
                  ≤ (M_th0_2 * (t / τ₁) ^ 9) / (t * mD_min) :=
                    div_le_div₀ (by positivity) h (by positivity) (mul_le_mul_of_nonneg_left hmD_ge ht0.le)
                _ = (M_th0_2 / mD_min) * τ₁⁻¹ * (t / τ₁) ^ 8 := by field_simp [ht0.ne', hτ₁.ne', hmD_min_pos.ne']
            have h1 : |deriv (fctThetaD v0') t| / (t ^ 2 * mQ t) ≤ (M_th0_1 / mQ_min) * τ₁⁻¹ * (t / τ₁) ^ 8 := by
              have hmin : min (1 : ℝ) ((|t| / τ₁) ^ 10) ≤ (t / τ₁) ^ 10 := by rw [abs_of_pos ht0]; exact min_le_right _ _
              have h : |deriv (fctThetaD v0') t| ≤ M_th0_1 * τ₁ * (t / τ₁) ^ 10 :=
                hθ.1.trans (mul_le_mul_of_nonneg_left hmin (mul_nonneg hM_th0_1_nn hτ₁.le))
              calc |deriv (fctThetaD v0') t| / (t ^ 2 * mQ t)
                  ≤ (M_th0_1 * τ₁ * (t / τ₁) ^ 10) / (t ^ 2 * mQ_min) :=
                    div_le_div₀ (by positivity) h (by positivity) (mul_le_mul_of_nonneg_left hmQ_ge (sq_nonneg t))
                _ = (M_th0_1 / mQ_min) * τ₁⁻¹ * (t / τ₁) ^ 8 := by field_simp [ht0.ne', hτ₁.ne', hmQ_min_pos.ne']
            have hmin_eq : min (1 : ℝ) ((t / τ₁) ^ 8) = (t / τ₁) ^ 8 :=
              min_eq_right (pow_le_one₀ (by positivity) ((div_le_one hτ₁).mpr hle))
            rw [hmin_eq]; linarith
          · have h2 : |iteratedDeriv 2 (fctThetaD v0') t| / (t * mD t) ≤ (M_th0_2 / mD_min) * τ₁⁻¹ := by
              have h := hθ.2.trans (mul_le_of_le_one_right hM_th0_2_nn (min_le_left _ _))
              calc |iteratedDeriv 2 (fctThetaD v0') t| / (t * mD t)
                  ≤ M_th0_2 / (τ₁ * mD_min) :=
                    div_le_div₀ hM_th0_2_nn h (by positivity) (mul_le_mul hgt.le hmD_ge hmD_min_pos.le ht0.le)
                _ = (M_th0_2 / mD_min) * τ₁⁻¹ := by field_simp [hτ₁.ne', hmD_min_pos.ne']
            have h1 : |deriv (fctThetaD v0') t| / (t ^ 2 * mQ t) ≤ (M_th0_1 / mQ_min) * τ₁⁻¹ := by
              have h := hθ.1.trans (mul_le_of_le_one_right (by positivity) (min_le_left _ _))
              calc |deriv (fctThetaD v0') t| / (t ^ 2 * mQ t)
                  ≤ (M_th0_1 * τ₁) / (τ₁ ^ 2 * mQ_min) :=
                    div_le_div₀ (by positivity) h (by positivity)
                      (mul_le_mul (pow_le_pow_left₀ hτ₁.le hgt.le 2) hmQ_ge hmQ_min_pos.le (sq_nonneg t))
                _ = (M_th0_1 / mQ_min) * τ₁⁻¹ := by field_simp [hτ₁.ne', hmQ_min_pos.ne']
            have hmin_eq : min (1 : ℝ) ((t / τ₁) ^ 8) = 1 :=
              min_eq_left (one_le_pow₀ ((one_le_div hτ₁).mpr hgt.le))
            rw [hmin_eq, mul_one]; linarith
        have hratio : min (1 : ℝ) ((t / τ₁) ^ 8) / t ^ (2 * p + 2) ≤ τ₁ ^ (-(2 * (p : ℤ)) - 2) := by
          rcases le_or_gt t τ₁ with hle | hgt
          · have hmin_le : min (1 : ℝ) ((t / τ₁) ^ 8) ≤ (t / τ₁) ^ 8 := min_le_right _ _
            have hrat : (t / τ₁) ^ (6 - 2 * p) ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hτ₁).mpr hle)
            have hexp : (t / τ₁) ^ 8 / t ^ (2 * p + 2) = τ₁ ^ (-(2 * (p : ℤ)) - 2) * (t / τ₁) ^ (6 - 2 * p) := by
              have h8 : 8 = (2 * p + 2) + (6 - 2 * p) := by omega
              have hneg : -(2 * (p : ℤ)) - 2 = -((2 * p + 2 : ℕ) : ℤ) := by omega
              rw [hneg, zpow_neg, zpow_natCast, h8, pow_add, div_pow, div_pow]
              field_simp [ht0.ne', hτ₁.ne']
            calc min (1 : ℝ) ((t / τ₁) ^ 8) / t ^ (2 * p + 2)
                ≤ (t / τ₁) ^ 8 / t ^ (2 * p + 2) := div_le_div_of_nonneg_right hmin_le (by positivity)
              _ = τ₁ ^ (-(2 * (p : ℤ)) - 2) * (t / τ₁) ^ (6 - 2 * p) := hexp
              _ ≤ τ₁ ^ (-(2 * (p : ℤ)) - 2) * 1 := mul_le_mul_of_nonneg_left hrat (zpow_nonneg hτ₁.le _)
              _ = τ₁ ^ (-(2 * (p : ℤ)) - 2) := mul_one _
          · have hneg : -(2 * (p : ℤ)) - 2 = -((2 * p + 2 : ℕ) : ℤ) := by omega
            rw [hneg, zpow_neg, zpow_natCast]
            calc min (1 : ℝ) ((t / τ₁) ^ 8) / t ^ (2 * p + 2)
                ≤ 1 / t ^ (2 * p + 2) := div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
              _ ≤ 1 / τ₁ ^ (2 * p + 2) := div_le_div_of_nonneg_left zero_le_one (by positivity) (pow_le_pow_left₀ hτ₁.le hgt.le _)
              _ = (τ₁ ^ (2 * p + 2))⁻¹ := one_div _
        have htri := abs_sub (iteratedDeriv 2 (fctThetaD v0') t / (t * mD t)) (deriv (fctThetaD v0') t / (t ^ 2 * mQ t))
        rw [abs_div, abs_div, abs_of_pos (mul_pos ht0 (mD_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14))),
          abs_of_pos (mul_pos (sq_pos_of_pos ht0) (mQ_pos_of_mem (by rw [abs_of_pos ht0]; exact ht14)))] at htri
        have hcomb : |iteratedDeriv 2 (fctThetaD v0') t / (t * mD t) - deriv (fctThetaD v0') t / (t ^ 2 * mQ t)| / t ^ (2 * p + 2) ≤
            (M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁ ^ (-(2 * (p : ℤ)) - 3) := by
          calc _ ≤ ((M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁⁻¹ * min 1 ((t / τ₁) ^ 8)) / t ^ (2 * p + 2) :=
                div_le_div_of_nonneg_right (htri.trans hmin8) (by positivity)
            _ = (M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁⁻¹ * (min 1 ((t / τ₁) ^ 8) / t ^ (2 * p + 2)) := by ring
            _ ≤ (M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁⁻¹ * τ₁ ^ (-(2 * (p : ℤ)) - 2) :=
                mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = (M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁ ^ (-(2 * (p : ℤ)) - 3) := by
                rw [mul_assoc, ← zpow_neg_one, ← zpow_add₀ hτ₁.ne']; congr 2; omega
        rw [mul_div_assoc, mul_assoc (1 / (2 * c))]
        exact mul_le_mul_of_nonneg_left hcomb (by positivity : (0 : ℝ) ≤ 1 / (2 * c))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg _) (pow_nonneg (uctM_pos ht0).le p)) (abs_nonneg _)) (abs_nonneg _))]
      have hmin_pos : 0 < min 1 mQ_min ^ 2 := sq_pos_of_pos (lt_min zero_lt_one hmQ_min_pos)
      have hpow_comb : τ₁ ^ 2 * τ₁ ^ (-(2 * (p : ℤ)) - 3) = τ₁ ^ (-(2 * (p : ℤ)) - 1) := by
        rw [← zpow_natCast τ₁ 2, ← zpow_add₀ hτ₁.ne']; congr 1; omega
      calc ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p * |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|
          ≤ ((1 + π ^ 2 / 4) / t ^ 2) / (min 1 mQ_min ^ 2 * t ^ (2 * p)) *
              (Real.exp M_v0_0 * M_v0_0 * τ₁ ^ 2) * |stripDeltaCurv c (fctThetaD v0') t| := by
            gcongr
        _ = (1 + π ^ 2 / 4) * (1 / min 1 mQ_min ^ 2) * (Real.exp M_v0_0 * M_v0_0) * τ₁ ^ 2 *
              (|stripDeltaCurv c (fctThetaD v0') t| / t ^ (2 * p + 2)) := by
            rw [pow_add]; field_simp [ht0.ne', hmin_pos.ne']
        _ ≤ (1 + π ^ 2 / 4) * (1 / min 1 mQ_min ^ 2) * (Real.exp M_v0_0 * M_v0_0) * τ₁ ^ 2 *
              ((1 / (2 * c)) * (M_th0_2 / mD_min + M_th0_1 / mQ_min) * τ₁ ^ (-(2 * (p : ℤ)) - 3)) := by
            gcongr
        _ = (1 + π ^ 2 / 4) * (1 / min 1 mQ_min ^ 2) * (Real.exp M_v0_0 * M_v0_0) *
              ((1 / 2) * (M_th0_2 / mD_min + M_th0_1 / mQ_min)) * c⁻¹ * (τ₁ ^ 2 * τ₁ ^ (-(2 * (p : ℤ)) - 3)) := by
            field_simp [hc.ne']
        _ = _ := by rw [hpow_comb]
    have hcross_cont : ContinuousOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p *
        |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) (Ioc 0 (10 * τ₁)) := by
      have hΔ_cont : ContinuousOn (stripDeltaCurv c (fctThetaD v0')) (Ioi 0) := by
        unfold stripDeltaCurv
        exact continuousOn_const.mul (((contDiff_iteratedDeriv_infty hθ0_cd 2).continuous.continuousOn.div hmd_cont
          fun t ht => (uctMderiv_pos ht).ne').sub ((hθ0_cd.continuous_deriv (by simp)).continuousOn.div hm_cont
          fun t ht => (uctM_pos ht).ne'))
      exact (((hH_cont.div (hm_cont.pow p) fun t ht => pow_ne_zero p (uctM_pos ht).ne').mul
        ((Real.continuous_exp.comp hv_cd.continuous).sub continuous_const).abs.continuousOn).mul
        hΔ_cont.abs).mono Ioc_subset_Ioi_self
    have hcross_int : IntegrableOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p *
        |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) (Ioc 0 (10 * τ₁)) :=
      (integrableOn_const (hs := measure_Ioc_lt_top.ne)).mono'
        (hcross_cont.aestronglyMeasurable measurableSet_Ioc) (ae_restrict_of_forall_mem measurableSet_Ioc hcross_pt)
    have hcross_bd : (∫ t in Ioc 0 (10 * τ₁), ‖stripH0 kind ((t : ℂ) * Complex.I)‖ / uctM t ^ p *
        |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) ≤ C_cross * c⁻¹ * τ₁ ^ (-(2 * (p : ℤ))) := by
      have hbd := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (hs := measure_Ioc_lt_top) hcross_pt
      rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun t ht =>
          mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg _) (pow_nonneg (uctM_pos ht.1).le p)) (abs_nonneg _)) (abs_nonneg _)),
        Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (by positivity)] at hbd
      refine hbd.trans (le_of_eq ?_)
      have hexp : τ₁ ^ (-(2 * (p : ℤ)) - 1) * τ₁ = τ₁ ^ (-(2 * (p : ℤ))) := by
        rw [mul_comm, ← zpow_one_add₀ hτ₁.ne']; congr 1; omega
      dsimp only [C_cross]
      calc (1 + π ^ 2 / 4) * (1 / min 1 mQ_min ^ 2) * (Real.exp M_v0_0 * M_v0_0) *
            ((1 / 2) * (M_th0_2 / mD_min + M_th0_1 / mQ_min)) * c⁻¹ * τ₁ ^ (-(2 * (p : ℤ)) - 1) * (10 * τ₁)
          = (1 + π ^ 2 / 4) * (1 / min 1 mQ_min ^ 2) * (Real.exp M_v0_0 * M_v0_0) *
            ((1 / 2) * (M_th0_2 / mD_min + M_th0_1 / mQ_min)) * 10 * c⁻¹ * (τ₁ ^ (-(2 * (p : ℤ)) - 1) * τ₁) := by ring
        _ = _ := by rw [hexp]
    exact ⟨hcurv_L_int, hcurv_L_bd, hcross_int, hcross_bd⟩
  -- Deduce `D_*(L)` integral bound at `p = 0`!
  obtain ⟨hcos_int, _, hcos_bd, _⟩ := hcos_spec hc hτ₁ hτ₁_cos hc_eq hα_le
  obtain ⟨hcurv0_int, hcurv0_bd, hcross0_int, hcross0_bd⟩ := hp_main 0 (by norm_num)
  simp only [pow_zero, div_one, Nat.cast_zero, mul_zero, neg_zero, zpow_zero, mul_one] at hcurv0_int hcurv0_bd hcross0_int hcross0_bd
  -- `D_*(L) = (I_osc^{DH_0}(L) - I_fl(L)) + I_osc^{H_0}(L) Δ_curv(τ₀(L)) + (I_osc^{DH_0}(L) - I_osc^{H_0}(L)) Δ_curv(τ₀(L))`
  have hcross0_L_int : IntegrableOn (fun L : ℝ => (stripIoscD kind v L - stripIosc kind L) * stripDeltaCurv c (fctThetaD v0') (tau0 L)) (Ioi 0) := by
    rw [uct_subst_integrableOn_zero]
    have hsupp_zero : ∀ t ∈ Ioi (10 * τ₁),
        uctMderiv t * ((stripIoscD kind v (uctM t) - stripIosc kind (uctM t)) * stripDeltaCurv c (fctThetaD v0') (tau0 (uctM t))) = 0 := by
      intro t ht
      have ht0 : 0 < t := lt_trans (by positivity) ht
      have hvt : v t = 0 := by by_contra hne; linarith [(hv_s hne).2, show 10 * τ₁ < t from ht]
      rw [← mul_assoc (uctMderiv t), mul_sub, uctMderiv_mul_stripIoscD kind v ht0,
        uctMderiv_mul_stripIosc kind ht0, hvt, Real.exp_zero, mul_one, sub_self, zero_mul]
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 10 * τ₁ by positivity), integrableOn_union]
    refine ⟨?_, (integrableOn_zero (μ := volume) (s := Ioi (10 * τ₁))).congr_fun (fun t ht => (hsupp_zero t ht).symm) measurableSet_Ioi⟩
    refine (hcross0_int.const_mul uctAlphaOsc).mono' ?_ ?_
    · have h1 : ContinuousOn (fun t : ℝ => uctMderiv t * ((stripIoscD kind v (uctM t) - stripIosc kind (uctM t)) *
          stripDeltaCurv c (fctThetaD v0') (tau0 (uctM t)))) (Ioc 0 (10 * τ₁)) := by
        have heq : EqOn (fun t : ℝ => uctMderiv t * ((stripIoscD kind v (uctM t) - stripIosc kind (uctM t)) *
              stripDeltaCurv c (fctThetaD v0') (tau0 (uctM t))))
            (fun t => uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1) *
              stripDeltaCurv c (fctThetaD v0') t) (Ioc 0 (10 * τ₁)) := fun t ht => by
          dsimp only
          rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht.1, show ceEll (π * t / 2) = uctM t from rfl,
            ← mul_assoc (uctMderiv t), mul_sub, uctMderiv_mul_stripIoscD kind v ht.1,
            uctMderiv_mul_stripIosc kind ht.1]; ring
        refine ContinuousOn.congr ?_ heq
        have hH_c : ContinuousOn (fun t : ℝ => ‖stripH0 kind ((t : ℂ) * Complex.I)‖) (Ioi 0) := by
          cases kind
          · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_star_imag ht
            refine (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
              ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
              fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')).add
              (continuousOn_const.div (continuousOn_const.mul ((Real.continuous_cosh.comp
                ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
                fun t _ => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne'))
          · refine ContinuousOn.congr ?_ fun t ht => norm_stripH0_ce_imag ht
            exact continuousOn_const.div (continuousOn_const.mul ((Real.continuous_sinh.comp
              ((continuous_const.mul continuous_id).div_const 2)).pow 2).continuousOn)
              fun t ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.sinh_pos_iff.mpr (div_pos (mul_pos Real.pi_pos ht) two_pos)).ne')
        have hm_c : ContinuousOn uctM (Ioi 0) := fun t ht => (hasDerivAt_uctM ht).continuousAt.continuousWithinAt
        have hmd_c : ContinuousOn uctMderiv (Ioi 0) := by
          unfold uctMderiv uctEllDeriv
          refine continuousOn_const.mul ((continuousOn_const.div ((continuousOn_const.mul continuousOn_id).div_const 2)
            fun t (ht : t ∈ Ioi (0 : ℝ)) => (div_pos (mul_pos Real.pi_pos ht) two_pos).ne').sub
            (continuousOn_const.div (Real.continuous_sinh.comp (continuous_const.mul ((continuous_const.mul continuous_id).div_const 2))).continuousOn
              fun t (ht : t ∈ Ioi (0 : ℝ)) => (Real.sinh_pos_iff.mpr (mul_pos two_pos (div_pos (mul_pos Real.pi_pos ht) two_pos))).ne'))
        have hΔ_c : ContinuousOn (stripDeltaCurv c (fctThetaD v0')) (Ioi 0) := by
          unfold stripDeltaCurv
          exact continuousOn_const.mul (((contDiff_iteratedDeriv_infty hθ0_cd 2).continuous.continuousOn.div hmd_c
            fun t ht => (uctMderiv_pos ht).ne').sub ((hθ0_cd.continuous_deriv (by simp)).continuousOn.div hm_c
            fun t ht => (uctM_pos ht).ne'))
        exact (((continuousOn_const.mul hH_c).mul ((Real.continuous_exp.comp hv_cd.continuous).sub continuous_const).continuousOn).mul
          hΔ_c).mono Ioc_subset_Ioi_self
      exact h1.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht.1, show ceEll (π * t / 2) = uctM t from rfl,
        ← mul_assoc (uctMderiv t), mul_sub, uctMderiv_mul_stripIoscD kind v ht.1,
        uctMderiv_mul_stripIosc kind ht.1,
        show (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * Real.exp (v t) -
          uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖) * stripDeltaCurv c (fctThetaD v0') t =
          uctAlphaOsc * (‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hαo_nn, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _)]
  have hcross0_L_bd : |∫ L in Ioi (0 : ℝ), (stripIoscD kind v L - stripIosc kind L) * stripDeltaCurv c (fctThetaD v0') (tau0 L)| ≤
      uctAlphaOsc * C_cross * c⁻¹ := by
    rw [uct_subst_zero]
    have hzero : (∫ t in Ioi (10 * τ₁), uctMderiv t * ((stripIoscD kind v (uctM t) - stripIosc kind (uctM t)) *
        stripDeltaCurv c (fctThetaD v0') (tau0 (uctM t)))) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      have ht0 : 0 < t := lt_trans (by positivity) ht
      have hvt : v t = 0 := by by_contra hne; linarith [(hv_s hne).2, show 10 * τ₁ < t from ht]
      rw [← mul_assoc (uctMderiv t), mul_sub, uctMderiv_mul_stripIoscD kind v ht0,
        uctMderiv_mul_stripIosc kind ht0, hvt, Real.exp_zero, mul_one, sub_self, zero_mul]
    have hint_t := (uct_subst_integrableOn_zero _).mp hcross0_L_int
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 10 * τ₁ by positivity),
      setIntegral_union (Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, mem_Ioi.mp h2])
        measurableSet_Ioi (hint_t.mono_set Ioc_subset_Ioi_self) (hint_t.mono_set fun x hx => lt_trans (by positivity) hx),
      hzero, add_zero]
    have h1 : |∫ t in Ioc 0 (10 * τ₁), uctMderiv t * ((stripIoscD kind v (uctM t) - stripIosc kind (uctM t)) *
        stripDeltaCurv c (fctThetaD v0') (tau0 (uctM t)))| ≤
        ∫ t in Ioc 0 (10 * τ₁), uctAlphaOsc * (‖stripH0 kind ((t : ℂ) * Complex.I)‖ *
          |Real.exp (v t) - 1| * |stripDeltaCurv c (fctThetaD v0') t|) := by
      refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on (hint_t.mono_set Ioc_subset_Ioi_self).norm
        (hcross0_int.const_mul uctAlphaOsc) measurableSet_Ioc fun t ht => ?_)
      rw [show uctM t = ceEll (π * t / 2) from rfl, tau0_ceEll ht.1, show ceEll (π * t / 2) = uctM t from rfl,
        ← mul_assoc (uctMderiv t), mul_sub, uctMderiv_mul_stripIoscD kind v ht.1,
        uctMderiv_mul_stripIosc kind ht.1,
        show (uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖ * Real.exp (v t) -
          uctAlphaOsc * ‖stripH0 kind ((t : ℂ) * Complex.I)‖) * stripDeltaCurv c (fctThetaD v0') t =
          uctAlphaOsc * (‖stripH0 kind ((t : ℂ) * Complex.I)‖ * (Real.exp (v t) - 1) * stripDeltaCurv c (fctThetaD v0') t) by ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hαo_nn, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _)]
    rw [integral_const_mul] at h1
    exact h1.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hcross0_bd hαo_nn)
  have hDstar_split : (fun L : ℝ => stripDstar kind c v v0' L) =
      fun L => (stripIoscD kind v L - uctIfl L) +
        stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L) +
        (stripIoscD kind v L - stripIosc kind L) * stripDeltaCurv c (fctThetaD v0') (tau0 L) := by
    ext L; unfold stripDstar; ring
  have h12_int : IntegrableOn (fun L : ℝ => (stripIoscD kind v L - uctIfl L) +
      stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L)) (Ioi 0) := hcos_int.add hcurv0_int
  have hDstar_int : IntegrableOn (fun L : ℝ => stripDstar kind c v v0' L) (Ioi 0) := by
    rw [hDstar_split]; exact h12_int.add hcross0_L_int
  have hDstar_bd : |(∫ L in Ioi (0 : ℝ), stripDstar kind c v v0' L) - stripCfl kind| ≤ C_all * τ₁ ^ 3 := by
    rw [hDstar_split, integral_add h12_int hcross0_L_int, integral_add hcos_int hcurv0_int]
    have hrew : ((∫ L in Ioi (0 : ℝ), (stripIoscD kind v L - uctIfl L)) +
        (∫ L in Ioi (0 : ℝ), stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L)) +
        ∫ L in Ioi (0 : ℝ), (stripIoscD kind v L - stripIosc kind L) * stripDeltaCurv c (fctThetaD v0') (tau0 L)) -
        stripCfl kind =
        ((∫ L in Ioi (0 : ℝ), (stripIoscD kind v L - uctIfl L)) - stripCfl kind) +
        (∫ L in Ioi (0 : ℝ), stripIosc kind L * stripDeltaCurv c (fctThetaD v0') (tau0 L)) +
        ∫ L in Ioi (0 : ℝ), (stripIoscD kind v L - stripIosc kind L) * stripDeltaCurv c (fctThetaD v0') (tau0 L) := by ring
    rw [hrew]
    have hc_le : c⁻¹ ≤ τ₁ ^ 3 := by rw [hc_inv]; exact pow_le_pow_of_le_one hτ₁.le hτ₁_1 (by norm_num)
    have h1 : C_p_curv * c⁻¹ ≤ C_p_curv * τ₁ ^ 3 := mul_le_mul_of_nonneg_left hc_le hC_p_nn
    have h2 : uctAlphaOsc * C_cross * c⁻¹ ≤ uctAlphaOsc * C_cross * τ₁ ^ 3 :=
      mul_le_mul_of_nonneg_left hc_le (mul_nonneg hαo_nn hC_cross_nn)
    have hC_le : C_cos + C_p_curv + uctAlphaOsc * C_cross ≤ C_all :=
      (le_max_right _ _).trans (le_max_right _ _)
    refine ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans ?_
    calc _ ≤ C_cos * τ₁ ^ 3 + C_p_curv * τ₁ ^ 3 + uctAlphaOsc * C_cross * τ₁ ^ 3 := by linarith
      _ = (C_cos + C_p_curv + uctAlphaOsc * C_cross) * τ₁ ^ 3 := by ring
      _ ≤ C_all * τ₁ ^ 3 := mul_le_mul_of_nonneg_right hC_le (pow_nonneg hτ₁.le 3)
  refine ⟨fun p hp => ?_, hDstar_int, hDstar_bd⟩
  obtain ⟨h1, h2, h3, h4⟩ := hp_main p hp
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hc.le)),
    h3, h4.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) (inv_nonneg.mpr hc.le)) (zpow_nonneg hτ₁.le _))⟩

end FormalResearch.SignUncertainty.FctCompD
