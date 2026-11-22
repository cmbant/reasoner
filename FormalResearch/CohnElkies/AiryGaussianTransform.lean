module

public import FormalResearch.CohnElkies.CardinalFractionalSource
public import FormalResearch.Special.AiryFourier
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Fractional Stieltjes Measure and Exact Airy-Square Gaussian Transform

Formalizes:
1. `CFT/sign_uncertainty/paper/ce_o1_route.tex`:
   * Theorem `O.11j` Stieltjes measure `dμ_p` and amplitude `Z_p`
     (`(ceo:O11j.3)`–`(ceo:O11j.4)`, `(ceo:O11j.cs)`).
   * Lemma `O.11n` (`ceo:O11n`): `𝒢_p`, `B_p` (`(ceo:O11n.1)`), the exact Airy-square Gaussian
     transform identity (`(ceo:O11n.2)`), and the `j = 0` uniform vertical-line bound
     (`(ceo:O11n.11)`).
2. `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`:
   * The exact Airy product Laplace identity (`(ceo:O11n.7)`) and Gaussian transform proof in
     `\subsection{Cancelled reflected symbol and Gaussian sectorial transition}`
     (`sec:proof-coherent-gaussian`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexInnerProductSpace FourierTransform

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Part 1: Fractional Stieltjes measure `dμ_p`, `Z_p`, `𝒢_p`, `B_p` -/

/-- Fractional Stieltjes measure density `dμ_p(s)/ds` (`ce_o1_route.tex` `(ceo:O11j.3)`). -/
noncomputable def fracMuDensity (p s : ℝ) : ℝ :=
  (Real.sin (π * p) / π) * (s ^ (p - 1) / (s ^ (2 * p) + 2 * s ^ p * Real.cos (π * p) + 1))

/-- Complex Stieltjes amplitude `Z_p(t) = ∫₀^∞ (1 - i √(s t))⁻¹ dμ_p(s)` (`(ceo:O11j.3)`). -/
noncomputable def fracZp (p t : ℝ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), (1 - Complex.I * ((√(s * t) : ℝ) : ℂ))⁻¹ * (fracMuDensity p s : ℂ)

/-- Sectorial limit transform `𝒢_p(z) = ∫₀^∞ (1 + z √s)⁻¹ dμ_p(s)` (`(ceo:O11n.1)`). -/
noncomputable def fracGp (p : ℝ) (z : ℂ) : ℂ :=
  ∫ s in Ioi (0 : ℝ), (1 + z * ((√s : ℝ) : ℂ))⁻¹ * (fracMuDensity p s : ℂ)

/-- Boundary-layer profile `B_p(x) = ∫₀^∞ (1 - e^{-x / √s}) dμ_p(s)` (`(ceo:O11n.1)`). -/
noncomputable def fracBp (p x : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), (1 - Real.exp (-x / √s)) * fracMuDensity p s

private lemma sin_pi_mul_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < Real.sin (π * p) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hp.1) (by nlinarith [Real.pi_pos, hp.2])

private lemma fracMu_denom_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : 0 ≤ s) :
    0 < s ^ (2 * p) + 2 * s ^ p * Real.cos (π * p) + 1 := by
  have hsq : s ^ (2 * p) = (s ^ p) ^ 2 := by
    rw [← Real.rpow_natCast (s ^ p) 2, ← Real.rpow_mul hs, Nat.cast_ofNat, mul_comm p 2]
  have hsc := Real.sin_sq_add_cos_sq (π * p)
  rw [show s ^ (2 * p) + 2 * s ^ p * Real.cos (π * p) + 1 =
    (s ^ p + Real.cos (π * p)) ^ 2 + Real.sin (π * p) ^ 2 by rw [hsq]; linear_combination -hsc]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (sin_pi_mul_pos hp))

lemma fracMuDensity_pos {p s : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) : 0 < fracMuDensity p s :=
  mul_pos (div_pos (sin_pi_mul_pos hp) Real.pi_pos) (div_pos (Real.rpow_pos_of_pos hs _) (fracMu_denom_pos hp hs.le))

private lemma integral_inv_quad_cos {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < π) :
    IntegrableOn (fun y : ℝ => Real.sin θ / (y ^ 2 + 2 * y * Real.cos θ + 1)) (Ioi (0 : ℝ)) ∧
      ∫ y in Ioi (0 : ℝ), Real.sin θ / (y ^ 2 + 2 * y * Real.cos θ + 1) = θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hquad : ∀ y : ℝ, Real.sin θ / (y ^ 2 + 2 * y * Real.cos θ + 1) =
      (1 + ((y + Real.cos θ) / Real.sin θ) ^ 2)⁻¹ * (Real.sin θ)⁻¹ := fun y => by
    have hsc := Real.sin_sq_add_cos_sq θ
    have hden : y ^ 2 + 2 * y * Real.cos θ + 1 = Real.sin θ ^ 2 * (1 + ((y + Real.cos θ) / Real.sin θ) ^ 2) := by
      have h1 : (y + Real.cos θ) ^ 2 + Real.sin θ ^ 2 = y ^ 2 + 2 * y * Real.cos θ + 1 := by
        linear_combination hsc
      rw [← h1]; field_simp [hsin.ne']; ring
    have hpos : 1 + ((y + Real.cos θ) / Real.sin θ) ^ 2 ≠ 0 := by positivity
    rw [hden]; field_simp [hsin.ne', hpos]
  let φ : ℝ → ℝ := fun y => (y + Real.cos θ) / Real.sin θ
  have himg : φ '' Ioi (0 : ℝ) = Ioi (Real.cos θ / Real.sin θ) := by
    ext u; simp only [mem_image, mem_Ioi, φ]
    refine ⟨fun ⟨y, hy, hu⟩ => hu ▸ by rw [add_div]; linarith [div_pos hy hsin], fun hu => ?_⟩
    refine ⟨u * Real.sin θ - Real.cos θ, ?_, by field_simp [hsin.ne']; ring⟩
    have h1 := mul_lt_mul_of_pos_right hu hsin
    rw [div_mul_cancel₀ _ hsin.ne'] at h1; linarith
  have hφ' : ∀ y ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (Real.sin θ)⁻¹ (Ioi 0) y := fun y _ =>
    HasDerivAt.hasDerivWithinAt
      (by simpa [φ, one_div] using ((hasDerivAt_id y).add_const (Real.cos θ)).div_const (Real.sin θ))
  have hinj : InjOn φ (Ioi (0 : ℝ)) := fun y₁ _ y₂ _ h => by
    have := congrArg (· * Real.sin θ) h; dsimp [φ] at this
    rw [div_mul_cancel₀ _ hsin.ne', div_mul_cancel₀ _ hsin.ne'] at this; linarith
  have hint_img : IntegrableOn (fun y : ℝ => (1 + (φ y) ^ 2)⁻¹ * (Real.sin θ)⁻¹) (Ioi (0 : ℝ)) :=
    ((integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hφ' hinj
      (fun u : ℝ => (1 + u ^ 2)⁻¹)).mp (by rw [himg]; exact integrable_inv_one_add_sq.integrableOn)).congr_fun
      (fun y _ => by simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hsin), mul_comm]) measurableSet_Ioi
  refine ⟨hint_img.congr_fun (fun y _ => (hquad y).symm) measurableSet_Ioi, ?_⟩
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hφ' hinj (fun u : ℝ => (1 + u ^ 2)⁻¹)
  rw [himg, integral_Ioi_inv_one_add_sq, show Real.cos θ / Real.sin θ = Real.tan (π / 2 - θ) by
    rw [Real.tan_pi_div_two_sub, Real.tan_eq_sin_div_cos, inv_div],
    Real.arctan_tan (by linarith) (by linarith)] at hcov
  have heq : ∫ y in Ioi (0 : ℝ), Real.sin θ / (y ^ 2 + 2 * y * Real.cos θ + 1) =
      ∫ y in Ioi (0 : ℝ), |(Real.sin θ)⁻¹| • (1 + φ y ^ 2)⁻¹ :=
    setIntegral_congr_fun measurableSet_Ioi fun y _ => by
      rw [smul_eq_mul, abs_of_pos (inv_pos.mpr hsin), hquad y, mul_comm]
  rw [heq, ← hcov]; ring

private lemma fracMuDensity_eq_rpow_deriv {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : 0 < s) :
    fracMuDensity p s = (π * p)⁻¹ *
      (p * s ^ (p - 1) * (Real.sin (π * p) / ((s ^ p) ^ 2 + 2 * s ^ p * Real.cos (π * p) + 1))) := by
  have hs2 : (s ^ p) ^ 2 = s ^ (2 * p) := by
    rw [← Real.rpow_natCast (s ^ p) 2, ← Real.rpow_mul hs.le, Nat.cast_ofNat, mul_comm p 2]
  unfold fracMuDensity; rw [hs2]
  field_simp [Real.pi_ne_zero, hp.1.ne', (fracMu_denom_pos hp hs.le).ne']

lemma fracMuDensity_integrable {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fracMuDensity p) (Ioi (0 : ℝ)) := by
  have hquad := (integral_inv_quad_cos (mul_pos Real.pi_pos hp.1) (by nlinarith [Real.pi_pos, hp.2])).1
  let f : ℝ → ℝ := fun s => s ^ p
  have himg : f '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext y; simp only [mem_image, mem_Ioi, f]
    exact ⟨fun ⟨s, hs, h⟩ => h ▸ Real.rpow_pos_of_pos hs p,
      fun hy => ⟨y ^ p⁻¹, Real.rpow_pos_of_pos hy _,
        by rw [← Real.rpow_mul hy.le, inv_mul_cancel₀ hp.1.ne', Real.rpow_one]⟩⟩
  have hf' : ∀ s ∈ Ioi (0 : ℝ), HasDerivWithinAt f (p * s ^ (p - 1)) (Ioi 0) s := fun s hs =>
    (Real.hasDerivAt_rpow_const (p := p) (Or.inl hs.ne')).hasDerivWithinAt
  have hinj : InjOn f (Ioi (0 : ℝ)) := fun s₁ h₁ s₂ h₂ h => by
    simpa [f, ← Real.rpow_mul h₁.le, ← Real.rpow_mul h₂.le, hp.1.ne'] using congrArg (· ^ p⁻¹) h
  have hi0 : IntegrableOn (fun x : ℝ => |p * x ^ (p - 1)| •
      (Real.sin (π * p) / ((f x) ^ 2 + 2 * (f x) * Real.cos (π * p) + 1))) (Ioi (0 : ℝ)) :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hf' hinj
      (fun y : ℝ => Real.sin (π * p) / (y ^ 2 + 2 * y * Real.cos (π * p) + 1))).mp (by rwa [himg])
  have hi : IntegrableOn (fun x : ℝ => (π * p)⁻¹ * (|p * x ^ (p - 1)| •
      (Real.sin (π * p) / ((f x) ^ 2 + 2 * (f x) * Real.cos (π * p) + 1)))) (Ioi (0 : ℝ)) :=
    hi0.const_mul (π * p)⁻¹
  refine hi.congr_fun (fun s (hs : 0 < s) => ?_) measurableSet_Ioi
  dsimp only
  rw [fracMuDensity_eq_rpow_deriv hp hs, smul_eq_mul,
    abs_of_pos (mul_pos hp.1 (Real.rpow_pos_of_pos hs _))]

/-- Mass normalization `∫₀^∞ dμ_p(s) = 1` (`ce_o1_route.tex` `(ceo:O11j.7)`). -/
theorem fracMuDensity_integral_one {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∫ s in Ioi (0 : ℝ), fracMuDensity p s = 1 := by
  have hquad := (integral_inv_quad_cos (mul_pos Real.pi_pos hp.1) (by nlinarith [Real.pi_pos, hp.2])).2
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun y : ℝ => Real.sin (π * p) / (y ^ 2 + 2 * y * Real.cos (π * p) + 1)) hp.1
  simp_rw [smul_eq_mul] at hsub
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => fracMuDensity_eq_rpow_deriv hp hs),
    integral_const_mul, hsub, hquad]
  field_simp [Real.pi_ne_zero, hp.1.ne']

private lemma norm_one_add_cexp_rpow_ge {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (x y : ℝ)
    (hy : |y| ≤ π) : Real.sin (π * p) ≤ ‖1 + Complex.exp ((p : ℂ) * (x + y * Complex.I))‖ := by
  have hθ0 : 0 < π * p := mul_pos Real.pi_pos hp.1
  have hθπ : π * p < π := by nlinarith [Real.pi_pos, hp.2]
  have he : Complex.exp ((p : ℂ) * (x + y * Complex.I)) =
      (Real.exp (p * x) : ℂ) * ((Real.cos (p * y) : ℂ) + (Real.sin (p * y) : ℂ) * Complex.I) := by
    rw [show (p : ℂ) * (x + y * Complex.I) = ((p * x : ℝ) : ℂ) + ((p * y : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_ofReal_mul_I, ← Complex.ofReal_exp]
  have hsq : ‖1 + Complex.exp ((p : ℂ) * (x + y * Complex.I))‖ ^ 2 =
      1 + 2 * Real.exp (p * x) * Real.cos (p * y) + Real.exp (p * x) ^ 2 := by
    rw [he, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_one, add_zero, zero_add]
    linear_combination Real.exp (p * x) ^ 2 * Real.sin_sq_add_cos_sq (p * y)
  have hcos_ge : Real.cos (π * p) ≤ Real.cos (p * y) := by
    rw [← Real.cos_abs (p * y)]
    exact Real.strictAntiOn_cos.antitoneOn ⟨abs_nonneg _, by rw [abs_mul, abs_of_pos hp.1]; nlinarith [Real.pi_pos]⟩
      ⟨hθ0.le, hθπ.le⟩ (by rw [abs_mul, abs_of_pos hp.1]; nlinarith)
  have h1 : 1 + 2 * Real.exp (p * x) * Real.cos (π * p) + Real.exp (p * x) ^ 2 =
      (Real.exp (p * x) + Real.cos (π * p)) ^ 2 + Real.sin (π * p) ^ 2 := by
    linear_combination -Real.sin_sq_add_cos_sq (π * p)
  exact le_of_sq_le_sq (by rw [hsq]; nlinarith [sq_nonneg (Real.exp (p * x) + Real.cos (π * p)), Real.exp_pos (p * x)])
    (norm_nonneg _)

private lemma one_sub_mul_cexp_ne_zero {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : |w.im| ≤ π)
    (hne : w ≠ (-Real.log t : ℂ)) : 1 - (t : ℂ) * Complex.exp w ≠ 0 := by
  intro h
  have he : ((t * Real.exp w.re : ℝ) : ℂ) * ((Real.cos w.im : ℂ) + (Real.sin w.im : ℂ) * Complex.I) = 1 := by
    have h1 : (t : ℂ) * Complex.exp w = 1 := by linear_combination -h
    rwa [← Complex.re_add_im w, Complex.exp_add, Complex.exp_ofReal_mul_I, ← Complex.ofReal_exp,
      ← mul_assoc, ← Complex.ofReal_mul] at h1
  have hre : t * Real.exp w.re * Real.cos w.im = 1 := by
    simpa [-Complex.ofReal_exp, -Complex.ofReal_cos, -Complex.ofReal_sin,
      Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im] using congrArg Complex.re he
  have him : t * Real.exp w.re * Real.sin w.im = 0 := by
    simpa [-Complex.ofReal_exp, -Complex.ofReal_cos, -Complex.ofReal_sin,
      Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im] using congrArg Complex.im he
  rcases Real.sin_eq_zero_iff_cos_eq.mp ((mul_eq_zero.mp him).resolve_left (mul_pos ht (Real.exp_pos _)).ne') with hcos | hcos
  · have hw0 : w.im = 0 := by
      by_contra hne0
      have hlt : Real.cos w.im < 1 := by
        rw [← Real.cos_abs w.im]
        calc Real.cos |w.im| < Real.cos 0 := Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨abs_nonneg _, hw⟩ (abs_pos.mpr hne0)
          _ = 1 := Real.cos_zero
      linarith
    rw [hcos, mul_one] at hre
    have hexp : Real.exp w.re = t⁻¹ := by field_simp [ht.ne'] at hre ⊢; linarith
    exact hne (Complex.ext (by rw [← Real.log_exp w.re, hexp, Real.log_inv]; simp) (by simpa using hw0))
  · rw [hcos] at hre; linarith [mul_pos ht (Real.exp_pos w.re)]

private lemma fracMu_stieltjes_integrable {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => (1 + s * t)⁻¹ * fracMuDensity p s) (Ioi (0 : ℝ)) := by
  refine (fracMuDensity_integrable hp).mono'
    ((Measurable.aestronglyMeasurable (by fun_prop : Measurable fun s : ℝ => (1 + s * t)⁻¹)).mul
      (fracMuDensity_integrable hp).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  have hden : 1 ≤ 1 + s * t := by linarith [mul_nonneg hs.le ht]
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (by linarith)) (fracMuDensity_pos hp hs).le)]
  exact mul_le_of_le_one_left (fracMuDensity_pos hp hs).le (inv_le_one_of_one_le₀ hden)

/-- **Lemma O.11j (`(ceo:O11j.7)`), Stieltjes representation:**
for `p ∈ (0, 1)` and `t ≥ 0`, `∫₀^∞ (1 + s t)⁻¹ dμ_p(s) = (1 + t^p)⁻¹`. -/
theorem fracMu_stieltjes_eq {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    ∫ s in Ioi (0 : ℝ), (1 + s * t)⁻¹ * fracMuDensity p s = ceVarphiP p t := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp only [mul_zero, add_zero, inv_one, one_mul, ceVarphiP, Real.zero_rpow hp.1.ne']
    exact (fracMuDensity_integral_one hp).trans (by norm_num)
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hsin_pos : 0 < Real.sin (π * p) := sin_pi_mul_pos hp
  let x₀ : ℝ := -Real.log t
  let C₀ : ℂ := (1 + ((t ^ (-p) : ℝ) : ℂ))⁻¹
  let G : ℂ → ℂ := fun w =>
    if w = (x₀ : ℂ) then C₀ ^ 2 * ((p : ℂ) * ((t ^ (-p) : ℝ) : ℂ))
    else (1 - (t : ℂ) * Complex.exp w)⁻¹ * ((1 + Complex.exp ((p : ℂ) * w))⁻¹ - C₀)
  have ht_rpow_eq : Complex.exp ((p : ℂ) * (x₀ : ℂ)) = ((t ^ (-p) : ℝ) : ℂ) := by
    rw [show (p : ℂ) * (x₀ : ℂ) = ((Real.log t * -p : ℝ) : ℂ) by dsimp [x₀]; push_cast; ring,
      ← Complex.ofReal_exp, Real.rpow_def_of_pos ht_pos]
  have hC₀_ne : 1 + ((t ^ (-p) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < 1 + t ^ (-p) := by positivity
    exact_mod_cast this.ne'
  have hG_diff : ∀ w : ℂ, |w.im| ≤ π → w ≠ (x₀ : ℂ) →
      DifferentiableAt ℂ (fun z => (1 - (t : ℂ) * Complex.exp z)⁻¹ *
        ((1 + Complex.exp ((p : ℂ) * z))⁻¹ - C₀)) w := by
    intro w hw hne
    have h1 := one_sub_mul_cexp_ne_zero ht_pos hw (by simpa [x₀] using hne)
    have h2 : 1 + Complex.exp ((p : ℂ) * w) ≠ 0 := fun h0 => by
      have := norm_one_add_cexp_rpow_ge hp w.re w.im hw
      rw [show (w.re : ℂ) + (w.im : ℂ) * Complex.I = w from Complex.re_add_im w, h0, norm_zero] at this
      linarith
    exact ((differentiableAt_const 1).sub (differentiableAt_id.cexp.const_mul (t : ℂ)) |>.inv h1).mul
      (((differentiableAt_const 1).add ((differentiableAt_id.const_mul (p : ℂ)).cexp) |>.inv h2).sub_const C₀)
  have hloc_eq : ∀ q : ℂ, q ≠ (x₀ : ℂ) → G =ᶠ[𝓝 q] fun u => (1 - (t : ℂ) * Complex.exp u)⁻¹ *
      ((1 + Complex.exp ((p : ℂ) * u))⁻¹ - C₀) := fun q hq => by
    filter_upwards [isOpen_ne.mem_nhds hq] with u hu
    dsimp only [G]; exact ite_eq_right_iff.mpr fun h => absurd h hu
  have hG_cont0 : ContinuousAt G (x₀ : ℂ) := by
    let φ : ℂ → ℂ := fun z => (1 + Complex.exp ((p : ℂ) * z))⁻¹
    let ψ : ℂ → ℂ := fun z => 1 - (t : ℂ) * Complex.exp z
    have hφ0 : φ (x₀ : ℂ) = C₀ := by simp [φ, ht_rpow_eq, C₀]
    have hψ0 : ψ (x₀ : ℂ) = 0 := by
      dsimp [ψ]; rw [← Complex.ofReal_exp, show Real.exp x₀ = t⁻¹ from by simp [x₀, Real.exp_neg, Real.exp_log ht_pos]]
      push_cast; field_simp [ht_pos.ne']; ring
    have hφd : HasDerivAt φ (-(C₀ ^ 2 * ((p : ℂ) * ((t ^ (-p) : ℝ) : ℂ)))) (x₀ : ℂ) := by
      have hpow : HasDerivAt (fun z : ℂ => 1 + Complex.exp ((p : ℂ) * z)) ((p : ℂ) * ((t ^ (-p) : ℝ) : ℂ)) (x₀ : ℂ) := by
        simpa [ht_rpow_eq, mul_comm] using (((hasDerivAt_id (x₀ : ℂ)).const_mul (p : ℂ)).cexp).const_add 1
      refine (hpow.inv (by rw [ht_rpow_eq]; exact hC₀_ne)).congr_deriv ?_
      rw [ht_rpow_eq]; dsimp [C₀]; field_simp [hC₀_ne]
    have hψd : HasDerivAt ψ (-1) (x₀ : ℂ) := by
      have h2 : (t : ℂ) * Complex.exp (x₀ : ℂ) = 1 := by
        rw [← Complex.ofReal_exp, show Real.exp x₀ = t⁻¹ from by simp [x₀, Real.exp_neg, Real.exp_log ht_pos]]
        push_cast; field_simp [ht_pos.ne']
      exact (((hasDerivAt_id (x₀ : ℂ)).cexp.const_mul (t : ℂ)).const_sub (1 : ℂ)).congr_deriv (by simp [h2])
    have hlim : Tendsto (fun z => slope φ (x₀ : ℂ) z / slope ψ (x₀ : ℂ) z) (𝓝[≠] (x₀ : ℂ)) (𝓝 (G (x₀ : ℂ))) := by
      simpa [G, neg_div_neg_eq, Pi.div_def] using hφd.tendsto_slope.div hψd.tendsto_slope (by norm_num)
    have hcongr : G =ᶠ[𝓝[≠] (x₀ : ℂ)] fun z => slope φ (x₀ : ℂ) z / slope ψ (x₀ : ℂ) z := by
      filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ (x₀ : ℂ))
      dsimp only [G]
      rw [ite_eq_right_iff.mpr fun h => absurd h hz, slope_def_field, slope_def_field, hφ0, hψ0, sub_zero,
        div_div_div_cancel_right₀ (sub_ne_zero.mpr hz), div_eq_inv_mul]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    exact hlim.congr' hcongr.symm
  have hG_contOn : ∀ R : ℝ, ContinuousOn G (uIcc (-R) R ×ℂ uIcc (-π) π) := fun R q hq => by
    have hq2 := hq.2; rw [uIcc_of_le (by linarith [Real.pi_pos])] at hq2
    by_cases hqx : q = (x₀ : ℂ)
    · subst hqx; exact hG_cont0.continuousWithinAt
    · exact ((hG_diff q (abs_le.mpr hq2) hqx).continuousAt.congr (hloc_eq q hqx).symm).continuousWithinAt
  have hrect : ∀ R : ℝ, (∫ x in -R..R, (G (x - π * Complex.I) - G (x + π * Complex.I))) +
      Complex.I * (∫ y in -π..π, G (R + y * Complex.I)) - Complex.I * (∫ y in -π..π, G (-R + y * Complex.I)) = 0 := fun R => by
    let z : ℂ := ((-R : ℝ) : ℂ) + ((-π : ℝ) : ℂ) * Complex.I
    let w : ℂ := (R : ℂ) + (π : ℂ) * Complex.I
    have hzw : z.re = -R ∧ w.re = R ∧ z.im = -π ∧ w.im = π := by simp [z, w]
    have Hc : ContinuousOn G (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
      simpa [hzw.1, hzw.2.1, hzw.2.2.1, hzw.2.2.2] using hG_contOn R
    have Hd : ∀ q ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ {(x₀ : ℂ)},
        DifferentiableAt ℂ G q := by
      rintro q ⟨hq, hqx⟩
      have h2 := hq.2
      rw [hzw.2.2.1, hzw.2.2.2, min_eq_left (by linarith [Real.pi_pos]), max_eq_right (by linarith [Real.pi_pos])] at h2
      exact (hG_diff q (abs_lt.mpr h2).le (by simpa using hqx)).congr_of_eventuallyEq (hloc_eq q (by simpa using hqx))
    have h0 := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable G z w {(x₀ : ℂ)} (countable_singleton _) Hc Hd
    have hi_horiz : ∀ ε : ℝ, |ε| ≤ π → IntervalIntegrable (fun x : ℝ => G ((x : ℂ) + (ε : ℂ) * Complex.I)) volume (-R) R :=
      fun ε hε => ((hG_contOn R).comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (ε : ℂ) * Complex.I).continuousOn
        fun x hx => ⟨by simpa using hx, by rw [uIcc_of_le (by linarith [Real.pi_pos])]; simpa using abs_le.mp hε⟩).intervalIntegrable
    have h1 : IntervalIntegrable (fun x : ℝ => G (x - π * Complex.I)) volume (-R) R := by
      simpa only [Complex.ofReal_neg, neg_mul, ← sub_eq_add_neg] using hi_horiz (-π) (by simp)
    have h2 : IntervalIntegrable (fun x : ℝ => G (x + π * Complex.I)) volume (-R) R := hi_horiz π (by simp)
    simp_rw [show ∀ x : ℝ, (x : ℂ) + (z.im : ℂ) * Complex.I = (x : ℂ) - π * Complex.I from fun x => by rw [hzw.2.2.1]; push_cast; ring,
      show ∀ x : ℝ, (x : ℂ) + (w.im : ℂ) * Complex.I = (x : ℂ) + π * Complex.I from fun x => by rw [hzw.2.2.2],
      hzw.1, hzw.2.1, hzw.2.2.1, hzw.2.2.2, Complex.ofReal_neg, smul_eq_mul] at h0
    rw [intervalIntegral.integral_sub h1 h2]; exact h0
  have hjump : ∀ x : ℝ, G (x - π * Complex.I) - G (x + π * Complex.I) =
      2 * π * Complex.I * ((1 + Real.exp x * t)⁻¹ * (Real.exp x * fracMuDensity p (Real.exp x)) : ℝ) := fun x => by
    have hx_ne1 : (x : ℂ) - π * Complex.I ≠ (x₀ : ℂ) := fun h => by have := congrArg Complex.im h; simp [Real.pi_ne_zero] at this
    have hx_ne2 : (x : ℂ) + π * Complex.I ≠ (x₀ : ℂ) := fun h => by have := congrArg Complex.im h; simp [Real.pi_ne_zero] at this
    have h1pm : ∀ ε : ℝ, ε = π ∨ ε = -π → 1 - (t : ℂ) * Complex.exp ((x : ℂ) + (ε : ℂ) * Complex.I) = ((1 + Real.exp x * t : ℝ) : ℂ) :=
      fun ε hε => by rw [Complex.exp_add, Complex.exp_ofReal_mul_I, ← Complex.ofReal_exp]; rcases hε with rfl | rfl <;> (simp [Real.cos_pi, Real.sin_pi]; ring)
    have h1m := h1pm (-π) (Or.inr rfl)
    rw [show (x : ℂ) + ((-π : ℝ) : ℂ) * Complex.I = (x : ℂ) - π * Complex.I by push_cast; ring] at h1m
    have h1p := h1pm π (Or.inl rfl)
    have hs_pos : 0 < Real.exp x := Real.exp_pos x
    have hspm : ∀ ε : ℝ, Complex.exp ((p : ℂ) * ((x : ℂ) + (ε : ℂ) * Complex.I)) =
        ((Real.exp x ^ p : ℝ) : ℂ) * ((Real.cos (p * ε) : ℂ) + (Real.sin (p * ε) : ℂ) * Complex.I) := fun ε => by
      rw [show (p : ℂ) * ((x : ℂ) + (ε : ℂ) * Complex.I) = ((p * x : ℝ) : ℂ) + ((p * ε : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_ofReal_mul_I, ← Complex.ofReal_exp, Real.rpow_def_of_pos hs_pos, Real.log_exp, mul_comm x p]
    have hsp : Complex.exp ((p : ℂ) * ((x : ℂ) + π * Complex.I)) =
        ((Real.exp x ^ p : ℝ) : ℂ) * ((Real.cos (π * p) : ℂ) + (Real.sin (π * p) : ℂ) * Complex.I) := by simpa [mul_comm] using hspm π
    have hsm : Complex.exp ((p : ℂ) * ((x : ℂ) - π * Complex.I)) =
        ((Real.exp x ^ p : ℝ) : ℂ) * ((Real.cos (π * p) : ℂ) - (Real.sin (π * p) : ℂ) * Complex.I) := by simpa [sub_eq_add_neg, mul_comm] using hspm (-π)
    have hden_ne : ∀ ε : ℝ, |ε| ≤ π → 1 + Complex.exp ((p : ℂ) * ((x : ℂ) + (ε : ℂ) * Complex.I)) ≠ 0 := fun ε hε h0 => by
      have h := norm_one_add_cexp_rpow_ge hp x ε hε; rw [h0, norm_zero] at h; linarith
    have hd1 : 1 + Complex.exp ((p : ℂ) * ((x : ℂ) - π * Complex.I)) ≠ 0 := by simpa [sub_eq_add_neg] using hden_ne (-π) (by simp)
    have hd2 : 1 + Complex.exp ((p : ℂ) * ((x : ℂ) + π * Complex.I)) ≠ 0 := hden_ne π (by simp)
    have h2p : ((Real.exp x ^ p : ℝ) : ℂ) ^ 2 = ((Real.exp x ^ (2 * p) : ℝ) : ℂ) := by
      exact_mod_cast (show (Real.exp x ^ p : ℝ) ^ 2 = Real.exp x ^ (2 * p) by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hs_pos.le, Nat.cast_ofNat, mul_comm p 2])
    have hprod : (1 + Complex.exp ((p : ℂ) * ((x : ℂ) - π * Complex.I))) * (1 + Complex.exp ((p : ℂ) * ((x : ℂ) + π * Complex.I))) =
        ((Real.exp x ^ (2 * p) + 2 * Real.exp x ^ p * Real.cos (π * p) + 1 : ℝ) : ℂ) := by
      rw [hsm, hsp]; have hsc : (Real.sin (π * p) : ℂ) ^ 2 + (Real.cos (π * p) : ℂ) ^ 2 = 1 := by exact_mod_cast Real.sin_sq_add_cos_sq (π * p)
      simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_one]
      linear_combination ((Real.exp x ^ p : ℝ) : ℂ) ^ 2 * hsc + h2p -
        (((Real.exp x ^ p : ℝ) : ℂ) * (Real.sin (π * p) : ℂ)) ^ 2 * Complex.I_sq
    have hdiff_inv : (1 + Complex.exp ((p : ℂ) * ((x : ℂ) - π * Complex.I)))⁻¹ - (1 + Complex.exp ((p : ℂ) * ((x : ℂ) + π * Complex.I)))⁻¹ =
        2 * Complex.I * (Real.sin (π * p) : ℂ) * ((Real.exp x ^ p : ℝ) : ℂ) / ((Real.exp x ^ (2 * p) + 2 * Real.exp x ^ p * Real.cos (π * p) + 1 : ℝ) : ℂ) := by
      rw [inv_sub_inv hd1 hd2, hprod, hsp, hsm]; congr 1; ring
    have hmu : Real.exp x * fracMuDensity p (Real.exp x) =
        (Real.sin (π * p) / π) * (Real.exp x ^ p / (Real.exp x ^ (2 * p) + 2 * Real.exp x ^ p * Real.cos (π * p) + 1)) := by
      unfold fracMuDensity
      rw [← mul_assoc, mul_comm (Real.exp x), mul_assoc, mul_div_assoc',
        show Real.exp x * Real.exp x ^ (p - 1) = Real.exp x ^ p from by nth_rw 1 [← Real.rpow_one (Real.exp x)]; rw [← Real.rpow_add hs_pos, add_sub_cancel]]
    dsimp only [G]
    rw [ite_eq_right_iff.mpr (fun h => absurd h hx_ne1), ite_eq_right_iff.mpr (fun h => absurd h hx_ne2), h1m, h1p, ← mul_sub,
      show ((1 + Complex.exp ((p : ℂ) * ((x : ℂ) - π * Complex.I)))⁻¹ - C₀) - ((1 + Complex.exp ((p : ℂ) * ((x : ℂ) + π * Complex.I)))⁻¹ - C₀) =
        (1 + Complex.exp ((p : ℂ) * ((x : ℂ) - π * Complex.I)))⁻¹ - (1 + Complex.exp ((p : ℂ) * ((x : ℂ) + π * Complex.I)))⁻¹ by ring,
      hdiff_inv, hmu]; push_cast
    have hdenC : ((Real.exp x ^ (2 * p) + 2 * Real.exp x ^ p * Real.cos (π * p) + 1 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (fracMu_denom_pos hp hs_pos.le).ne'
    have h1xt : ((1 + Real.exp x * t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity : 0 < 1 + Real.exp x * t).ne'
    field_simp [hpi, hdenC, h1xt]
  have himg : Real.exp '' univ = Ioi (0 : ℝ) := by
    ext s; simp only [mem_image, mem_univ, true_and, mem_Ioi]
    exact ⟨fun ⟨x, hx⟩ => hx ▸ Real.exp_pos x, fun hs => ⟨Real.log s, Real.exp_log hs⟩⟩
  have hint_real : Integrable (fun x : ℝ => (1 + Real.exp x * t)⁻¹ * (Real.exp x * fracMuDensity p (Real.exp x))) := by
    have hcov := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ (f := Real.exp) (f' := Real.exp)
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn (fun s => (1 + s * t)⁻¹ * fracMuDensity p s)).mp
      (by rw [himg]; exact fracMu_stieltjes_integrable hp ht)
    rw [integrableOn_univ] at hcov
    exact hcov.congr (Eventually.of_forall fun x => by simp only [smul_eq_mul, abs_of_pos (Real.exp_pos x)]; ring)
  have hcov_eq : ∫ x : ℝ, (1 + Real.exp x * t)⁻¹ * (Real.exp x * fracMuDensity p (Real.exp x)) =
      ∫ s in Ioi (0 : ℝ), (1 + s * t)⁻¹ * fracMuDensity p s := by
    have hcov := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ (f := Real.exp) (f' := Real.exp)
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn (fun s => (1 + s * t)⁻¹ * fracMuDensity p s)
    rw [show (fun x : ℝ => (1 + Real.exp x * t)⁻¹ * (Real.exp x * fracMuDensity p (Real.exp x))) =
      fun x : ℝ => |Real.exp x| • ((1 + Real.exp x * t)⁻¹ * fracMuDensity p (Real.exp x)) from
      funext fun x => by rw [smul_eq_mul, abs_of_pos (Real.exp_pos x)]; ring, ← setIntegral_univ, ← hcov, himg]
  have hC₀_bd : ‖C₀‖ ≤ 1 := by
    dsimp [C₀]; rw [show (1 + ((t ^ (-p) : ℝ) : ℂ)) = ((1 + t ^ (-p) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact inv_le_one_of_one_le₀ (by linarith [Real.rpow_nonneg ht_pos.le (-p)])
  have h_right : Tendsto (fun R : ℝ => Complex.I * ∫ y in -π..π, G (R + y * Complex.I)) atTop (𝓝 0) := by
    have hbd : ∀ᶠ R : ℝ in atTop, ‖Complex.I * ∫ y in -π..π, G (R + y * Complex.I)‖ ≤
        2 * π * (2 / t * ((Real.sin (π * p))⁻¹ + 1)) * Real.exp (-R) := by
      filter_upwards [eventually_ge_atTop (max (|x₀| + 1) (Real.log (2 / t)))] with R hR
      have hlt : |x₀| < R := by linarith [(le_max_left _ _).trans hR]
      have htR : 2 ≤ t * Real.exp R := by
        have h1 : 2 / t ≤ Real.exp R := (Real.exp_log (by positivity : 0 < 2 / t)).symm ▸ Real.exp_le_exp.mpr ((le_max_right _ _).trans hR)
        rw [mul_comm t]; rwa [div_le_iff₀ ht_pos] at h1
      have hnorm : ∀ y ∈ uIcc (-π) π, ‖G (R + y * Complex.I)‖ ≤ 2 / t * ((Real.sin (π * p))⁻¹ + 1) * Real.exp (-R) := fun y hy => by
        rw [uIcc_of_le (by linarith [Real.pi_pos])] at hy
        have hne : (R : ℂ) + y * Complex.I ≠ (x₀ : ℂ) := fun h => by have := congrArg Complex.re h; simp at this; linarith [(abs_lt.mp hlt).2]
        have hden1 : t * Real.exp R / 2 ≤ ‖1 - (t : ℂ) * Complex.exp (R + y * Complex.I)‖ := by
          have htri := norm_sub_norm_le ((t : ℂ) * Complex.exp (R + y * Complex.I)) 1
          rw [norm_sub_rev, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos,
            Complex.norm_exp, show ((R : ℂ) + y * Complex.I).re = R by simp] at htri; linarith
        have hinv1 : ‖1 - (t : ℂ) * Complex.exp (R + y * Complex.I)‖⁻¹ ≤ 2 / t * Real.exp (-R) := by
          rw [Real.exp_neg]; exact (inv_anti₀ (by positivity : 0 < t * Real.exp R / 2) hden1).trans_eq (by field_simp)
        have hinv_b : ‖(1 + Complex.exp ((p : ℂ) * (R + y * Complex.I)))⁻¹‖ ≤ (Real.sin (π * p))⁻¹ := by
          rw [norm_inv]; exact inv_anti₀ hsin_pos (norm_one_add_cexp_rpow_ge hp R y (abs_le.mpr hy))
        dsimp only [G]; rw [ite_eq_right_iff.mpr (fun h => absurd h hne), norm_mul, norm_inv]
        calc _ ≤ (2 / t * Real.exp (-R)) * ((Real.sin (π * p))⁻¹ + 1) :=
              mul_le_mul hinv1 ((norm_sub_le _ _).trans (add_le_add hinv_b hC₀_bd)) (norm_nonneg _) (by positivity)
          _ = _ := by ring
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => hnorm y (uIoc_subset_uIcc hy))
      rw [norm_mul, Complex.norm_I, one_mul]
      rw [show |π - -π| = 2 * π by rw [abs_of_pos (by linarith [Real.pi_pos])]; ring] at hint; linarith
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul _) (Eventually.of_forall fun _ => norm_nonneg _) hbd)
  have h_left : Tendsto (fun R : ℝ => Complex.I * ∫ y in -π..π, G (-R + y * Complex.I)) atTop (𝓝 (2 * π * Complex.I * (1 - C₀))) := by
    have hC₀1 : ‖1 - C₀‖ ≤ 1 := by
      have h1 : 0 < 1 + t ^ (-p) := by positivity
      have h2 : 1 - (1 + t ^ (-p))⁻¹ = t ^ (-p) / (1 + t ^ (-p)) := by field_simp; ring
      rw [show (1 : ℂ) - C₀ = ((1 - (1 + t ^ (-p))⁻¹ : ℝ) : ℂ) by push_cast [C₀]; rfl,
        Complex.norm_real, Real.norm_eq_abs, h2, abs_of_nonneg (by positivity)]
      exact div_le_one_of_le₀ (by linarith) h1.le
    have hdiff : Tendsto (fun R : ℝ => ∫ y in -π..π, (G (-R + y * Complex.I) - (1 - C₀))) atTop (𝓝 0) := by
      have hbd : ∀ᶠ R : ℝ in atTop, ‖∫ y in -π..π, (G (-R + y * Complex.I) - (1 - C₀))‖ ≤
          2 * π * (2 * t * Real.exp (-R) + 2 * (Real.sin (π * p))⁻¹ * Real.exp (-p * R)) := by
        filter_upwards [eventually_ge_atTop (max (|x₀| + 1) (Real.log (2 * t)))] with R hR
        have hlt : |x₀| < R := by linarith [(le_max_left _ _).trans hR]
        have htR : t * Real.exp (-R) ≤ 1 / 2 := by
          have h1 : 2 * t ≤ Real.exp R := (Real.exp_log (by positivity : 0 < 2 * t)).symm ▸ Real.exp_le_exp.mpr ((le_max_right _ _).trans hR)
          rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos R)]; linarith
        have hnorm : ∀ y ∈ uIcc (-π) π, ‖G (-R + y * Complex.I) - (1 - C₀)‖ ≤
            2 * t * Real.exp (-R) + 2 * (Real.sin (π * p))⁻¹ * Real.exp (-p * R) := fun y hy => by
          rw [uIcc_of_le (by linarith [Real.pi_pos])] at hy
          have hne : (-R : ℂ) + y * Complex.I ≠ (x₀ : ℂ) := fun h => by have := congrArg Complex.re h; simp at this; linarith [(abs_lt.mp hlt).1]
          let a : ℂ := (t : ℂ) * Complex.exp (-R + y * Complex.I)
          let b : ℂ := Complex.exp ((p : ℂ) * (-R + y * Complex.I))
          have ha : ‖a‖ = t * Real.exp (-R) := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht_pos, Complex.norm_exp]; simp
          have hb : ‖b‖ = Real.exp (-p * R) := by rw [Complex.norm_exp]; simp [neg_mul]
          have h1t : 1 / 2 ≤ ‖1 - a‖ := by have := norm_sub_norm_le (1 : ℂ) a; rw [norm_one, ha] at this; linarith
          have h1p : Real.sin (π * p) ≤ ‖1 + b‖ := by simpa [b] using norm_one_add_cexp_rpow_ge hp (-R) y (abs_le.mpr hy)
          have hA : ‖(1 - a)⁻¹ - 1‖ ≤ 2 * (t * Real.exp (-R)) := by
            rw [show (1 - a)⁻¹ - 1 = a / (1 - a) by field_simp [norm_pos_iff.mp (by linarith : 0 < ‖1 - a‖)]; ring, norm_div, ha]
            exact (div_le_div_of_nonneg_left (by positivity) (by norm_num) h1t).trans_eq (by ring)
          have hB : ‖(1 + b)⁻¹ - 1‖ ≤ (Real.sin (π * p))⁻¹ * Real.exp (-p * R) := by
            rw [show (1 + b)⁻¹ - 1 = -b / (1 + b) by field_simp [norm_pos_iff.mp (lt_of_lt_of_le hsin_pos h1p)]; ring, norm_div, norm_neg, hb]
            exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hsin_pos h1p).trans_eq (div_eq_inv_mul _ _)
          have hinvt : ‖(1 - a)⁻¹‖ ≤ 2 := by rw [norm_inv]; exact (inv_anti₀ (by norm_num) h1t).trans_eq (by norm_num)
          dsimp only [G]
          rw [ite_eq_right_iff.mpr (fun h => absurd h hne), show (1 - a)⁻¹ * ((1 + b)⁻¹ - C₀) - (1 - C₀) =
            ((1 - a)⁻¹ - 1) * (1 - C₀) + (1 - a)⁻¹ * ((1 + b)⁻¹ - 1) by ring]
          calc _ ≤ ‖(1 - a)⁻¹ - 1‖ * ‖1 - C₀‖ + ‖(1 - a)⁻¹‖ * ‖(1 + b)⁻¹ - 1‖ :=
                (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
            _ ≤ (2 * (t * Real.exp (-R))) * 1 + 2 * ((Real.sin (π * p))⁻¹ * Real.exp (-p * R)) :=
                add_le_add (mul_le_mul hA hC₀1 (norm_nonneg _) (by positivity)) (mul_le_mul hinvt hB (norm_nonneg _) (by positivity))
            _ = _ := by ring
        have hint := intervalIntegral.norm_integral_le_of_norm_le_const (fun y hy => hnorm y (uIoc_subset_uIcc hy))
        rw [show |π - -π| = 2 * π by rw [abs_of_pos (by linarith [Real.pi_pos])]; ring] at hint; linarith
      have h0 : Tendsto (fun R : ℝ => 2 * π * (2 * t * Real.exp (-R) + 2 * (Real.sin (π * p))⁻¹ * Real.exp (-p * R))) atTop (𝓝 0) := by
        simpa using (((Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (2 * t)).add
          ((Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.mpr hp.1))).const_mul _)).const_mul (2 * π)
      exact tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
        (Eventually.of_forall fun _ => norm_nonneg _) hbd)
    have h_lim := (hdiff.const_mul Complex.I).add_const (2 * π * Complex.I * (1 - C₀))
    rw [mul_zero, zero_add] at h_lim
    refine h_lim.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have hiG : IntervalIntegrable (fun y : ℝ => G (-R + y * Complex.I)) volume (-π) π :=
      ((hG_contOn R).comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
        fun y hy => ⟨by simp [Complex.add_re, Complex.mul_re], by simpa using hy⟩).intervalIntegrable
    rw [intervalIntegral.integral_sub hiG intervalIntegrable_const, intervalIntegral.integral_const,
      Complex.real_smul, show (π - -π : ℝ) = 2 * π by ring]; push_cast; ring
  have h_mid : Tendsto (fun R : ℝ => ∫ x in -R..R, (G (x - π * Complex.I) - G (x + π * Complex.I)))
      atTop (𝓝 (2 * π * Complex.I * ((∫ s in Ioi (0 : ℝ), (1 + s * t)⁻¹ * fracMuDensity p s : ℝ) : ℂ))) := by
    have htend := intervalIntegral_tendsto_integral hint_real tendsto_neg_atTop_atBot tendsto_id
    rw [hcov_eq] at htend
    refine ((Complex.continuous_ofReal.continuousAt.tendsto.comp htend).const_mul (2 * π * Complex.I)).congr fun R => ?_
    simp only [Function.comp_apply, id_eq]; simp_rw [hjump]; rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  have hzero : 2 * π * Complex.I * ((∫ s in Ioi (0 : ℝ), (1 + s * t)⁻¹ * fracMuDensity p s : ℝ) : ℂ) +
      0 - 2 * π * Complex.I * (1 - C₀) = 0 :=
    tendsto_nhds_unique ((h_mid.add h_right).sub h_left) (tendsto_const_nhds.congr fun R => (hrect R).symm)
  have h2piI : (2 * π * Complex.I : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hpi)) Complex.I_ne_zero
  have heqC : ((∫ s in Ioi (0 : ℝ), (1 + s * t)⁻¹ * fracMuDensity p s : ℝ) : ℂ) = 1 - C₀ := by
    apply mul_left_cancel₀ h2piI; linear_combination hzero
  have h1C₀_real : (1 : ℝ) - (1 + t ^ (-p))⁻¹ = (1 + t ^ p)⁻¹ := by
    rw [Real.rpow_neg ht_pos.le p]; have hpos : 0 < t ^ p := Real.rpow_pos_of_pos ht_pos p; field_simp; ring
  have h1C₀ : (1 : ℂ) - C₀ = ((ceVarphiP p t : ℝ) : ℂ) := by
    have := congrArg ((↑) : ℝ → ℂ) h1C₀_real; simpa [C₀, ceVarphiP] using this
  exact Complex.ofReal_injective (heqC.trans h1C₀)

lemma fracZp_integrable {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (_ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => (1 - Complex.I * ((√(s * t) : ℝ) : ℂ))⁻¹ * (fracMuDensity p s : ℂ)) (Ioi (0 : ℝ)) := by
  have hc : Continuous (fun s : ℝ => (1 - Complex.I * ((√(s * t) : ℝ) : ℂ))⁻¹) :=
    Continuous.inv₀ (by fun_prop) fun s h => by have := congrArg Complex.re h; simp at this
  refine (fracMuDensity_integrable hp).mono' (hc.aestronglyMeasurable.restrict.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (fracMuDensity_integrable hp).aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  have hnorm : 1 ≤ ‖1 - Complex.I * ((√(s * t) : ℝ) : ℂ)‖ :=
    (by simp : (1 : ℝ) ≤ (1 - Complex.I * ((√(s * t) : ℝ) : ℂ)).re).trans (Complex.re_le_norm _)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (fracMuDensity_pos hp hs)]
  exact mul_le_of_le_one_left (fracMuDensity_pos hp hs).le (inv_le_one_of_one_le₀ hnorm)

/-- Real part identity `Re Z_p(t) = (1 + t^p)⁻¹` (`(ceo:O11j.4)`). -/
theorem fracZp_re_eq {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    (fracZp p t).re = ceVarphiP p t := by
  have hint := fracZp_integrable hp ht
  unfold fracZp
  rw [← RCLike.re_eq_complex_re, ← integral_re hint, ← fracMu_stieltjes_eq hp ht]
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
  have hns : Complex.normSq (1 - Complex.I * ((√(s * t) : ℝ) : ℂ)) = 1 + s * t := by
    rw [Complex.normSq_apply]; simp; linarith [Real.sq_sqrt (mul_nonneg hs.le ht)]
  rw [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.inv_re, hns]; simp

/-- Pointwise norm bound `|Z_p(t)| ≤ ∫₀^∞ (1 + s t)^{-1/2} dμ_p(s)` (`(ceo:O11j.4)`). -/
theorem fracZp_norm_le_half_moment {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    ‖fracZp p t‖ ≤ ∫ s in Ioi (0 : ℝ), (1 + s * t) ^ (-(1 / 2 : ℝ)) * fracMuDensity p s := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_))
  have hden : 0 < 1 + s * t := by linarith [mul_nonneg hs.le ht]
  have hns : ‖1 - Complex.I * ((√(s * t) : ℝ) : ℂ)‖ = √(1 + s * t) := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp; congr 1; linarith [Real.sq_sqrt (mul_nonneg hs.le ht)]
  rw [norm_mul, norm_inv, hns, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (fracMuDensity_pos hp hs),
    Real.sqrt_eq_rpow, ← Real.rpow_neg hden.le]

/-- **Cauchy–Schwarz margin `(ceo:O11j.cs)`:** `‖Z_p(t)‖² ≤ (1 + t^p)⁻¹` for `t ≥ 0`. -/
theorem fracZp_norm_sq_le {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 ≤ t) :
    ‖fracZp p t‖ ^ 2 ≤ ceVarphiP p t := by
  let f : ℝ → ℝ := fun s => (1 + s * t) ^ (-(1 / 2 : ℝ))
  let a : ℝ := ∫ s in Ioi (0 : ℝ), f s * fracMuDensity p s
  have hf_le : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ f s ∧ f s ≤ 1 := fun s hs =>
    ⟨Real.rpow_nonneg (by linarith [mul_nonneg hs.le ht]) _,
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [mul_nonneg hs.le ht]) (by norm_num)⟩
  have hf_int : IntegrableOn (fun s => f s * fracMuDensity p s) (Ioi (0 : ℝ)) := by
    refine (fracMuDensity_integrable hp).mono'
      ((Measurable.aestronglyMeasurable (by fun_prop : Measurable f)).restrict.mul
        (fracMuDensity_integrable hp).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
    rw [Real.norm_of_nonneg (mul_nonneg (hf_le s hs).1 (fracMuDensity_pos hp hs).le)]
    exact mul_le_of_le_one_left (fracMuDensity_pos hp hs).le (hf_le s hs).2
  have hfsq_eq : ∀ s ∈ Ioi (0 : ℝ), f s ^ 2 * fracMuDensity p s = (1 + s * t)⁻¹ * fracMuDensity p s := fun s hs => by
    have hpos : 0 < 1 + s * t := by linarith [mul_nonneg hs.le ht]
    dsimp [f]; rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hpos.le, show -(1 / 2 : ℝ) * (2 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
  have hfsq_int : IntegrableOn (fun s => f s ^ 2 * fracMuDensity p s) (Ioi (0 : ℝ)) :=
    (fracMu_stieltjes_integrable hp ht).congr_fun (fun s hs => (hfsq_eq s hs).symm) measurableSet_Ioi
  let g1 : ℝ → ℝ := fun s => f s ^ 2 * fracMuDensity p s
  let g2 : ℝ → ℝ := fun s => 2 * a * (f s * fracMuDensity p s)
  let g3 : ℝ → ℝ := fun s => a ^ 2 * fracMuDensity p s
  have hsq_nonneg : 0 ≤ ∫ s in Ioi (0 : ℝ), (f s - a) ^ 2 * fracMuDensity p s :=
    setIntegral_nonneg measurableSet_Ioi fun s hs => mul_nonneg (sq_nonneg _) (fracMuDensity_pos hp hs).le
  have hexp : ∫ s in Ioi (0 : ℝ), (f s - a) ^ 2 * fracMuDensity p s = ceVarphiP p t - 2 * a * a + a ^ 2 * 1 := by
    calc ∫ s in Ioi (0 : ℝ), (f s - a) ^ 2 * fracMuDensity p s
        = ∫ s in Ioi (0 : ℝ), (g1 - g2 + g3) s :=
          setIntegral_congr_fun measurableSet_Ioi fun s _ => by simp only [Pi.add_apply, Pi.sub_apply, g1, g2, g3]; ring
      _ = (∫ s in Ioi (0 : ℝ), (g1 - g2) s) + ∫ s in Ioi (0 : ℝ), g3 s :=
          integral_add (hfsq_int.sub (hf_int.const_mul (2 * a))) ((fracMuDensity_integrable hp).const_mul (a ^ 2))
      _ = ((∫ s in Ioi (0 : ℝ), g1 s) - ∫ s in Ioi (0 : ℝ), g2 s) + ∫ s in Ioi (0 : ℝ), g3 s := by
          dsimp only [Pi.sub_apply, g1, g2]; rw [integral_sub hfsq_int (hf_int.const_mul (2 * a))]
      _ = ceVarphiP p t - 2 * a * a + a ^ 2 * 1 := by
          dsimp only [g1, g2, g3]
          rw [setIntegral_congr_fun measurableSet_Ioi hfsq_eq, fracMu_stieltjes_eq hp ht,
            integral_const_mul, integral_const_mul, fracMuDensity_integral_one hp]
  rw [hexp] at hsq_nonneg
  exact (pow_le_pow_left₀ (norm_nonneg _) (fracZp_norm_le_half_moment hp ht) 2).trans (by linarith)

/-- Strict contraction `‖Z_p(t)‖ < 1` for `t > 0` (`(ceo:O11j.4)`). -/
theorem fracZp_norm_lt_one {p t : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ht : 0 < t) : ‖fracZp p t‖ < 1 := by
  have hsq := fracZp_norm_sq_le hp ht.le
  have hlt : ceVarphiP p t < 1 := by unfold ceVarphiP; rw [inv_lt_one_iff₀]; right; linarith [Real.rpow_pos_of_pos ht p]
  nlinarith [norm_nonneg (fracZp p t)]

/-- Decay at infinity `Z_p(t) → 0` as `t → ∞` (`(ceo:O11j.4)`). -/
theorem fracZp_tendsto_zero {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : Tendsto (fracZp p) atTop (𝓝 0) := by
  have hphi : Tendsto (ceVarphiP p) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun t : ℝ => le_add_of_nonneg_left zero_le_one) (tendsto_rpow_atTop hp.1))
  have hsq := squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg ‖fracZp p _‖)
    (eventually_ge_atTop (0 : ℝ) |>.mono fun _ ht => fracZp_norm_sq_le hp ht) hphi
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt)

lemma fracGp_integrable {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun s : ℝ => (1 + z * ((√s : ℝ) : ℂ))⁻¹ * (fracMuDensity p s : ℂ)) (Ioi (0 : ℝ)) := by
  have hre : ∀ s : ℝ, 1 ≤ (1 + z * ((√s : ℝ) : ℂ)).re := fun s => by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    linarith [mul_nonneg hz.le (Real.sqrt_nonneg s)]
  have hc : Continuous (fun s : ℝ => (1 + z * ((√s : ℝ) : ℂ))⁻¹) :=
    Continuous.inv₀ (by fun_prop) fun s h => by have := hre s; rw [h, Complex.zero_re] at this; linarith
  refine (fracMuDensity_integrable hp).mono' (hc.aestronglyMeasurable.restrict.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (fracMuDensity_integrable hp).aestronglyMeasurable)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (fracMuDensity_pos hp hs)]
  exact mul_le_of_le_one_left (fracMuDensity_pos hp hs).le (inv_le_one_of_one_le₀ ((hre s).trans (Complex.re_le_norm _)))

/-- Positivity `0 < Re 𝒢_p(z)` on `Re z > 0` (`(ceo:O11n.1)`). -/
theorem fracGp_re_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {z : ℂ} (hz : 0 < z.re) : 0 < (fracGp p z).re := by
  have hint := fracGp_integrable hp hz
  unfold fracGp
  rw [← RCLike.re_eq_complex_re, ← integral_re hint]; simp_rw [RCLike.re_eq_complex_re]
  have hintegrand_pos : ∀ s ∈ Ioi (0 : ℝ),
      0 < (((1 + z * ((√s : ℝ) : ℂ))⁻¹ * (fracMuDensity p s : ℂ)) : ℂ).re := fun s hs => by
    have hre : 0 < (1 + z * ((√s : ℝ) : ℂ)).re := by simp; linarith [mul_nonneg hz.le (Real.sqrt_nonneg s)]
    have hns : 0 < Complex.normSq (1 + z * ((√s : ℝ) : ℂ)) :=
      Complex.normSq_pos.mpr fun h0 => by rw [h0, Complex.zero_re] at hre; exact lt_irrefl 0 hre
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.inv_re]
    exact mul_pos (div_pos hre hns) (fracMuDensity_pos hp hs)
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_mem measurableSet_Ioi).mono fun s hs => (hintegrand_pos s hs).le)
    (by simpa [RCLike.re_eq_complex_re] using hint.re)]
  have hsupp : Function.support (fun s : ℝ =>
      (((1 + z * ((√s : ℝ) : ℂ))⁻¹ * (fracMuDensity p s : ℂ)) : ℂ).re) ∩ Ioi 0 = Ioi 0 := by
    ext s; simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
    intro hs; exact (hintegrand_pos s hs).ne'
  rw [hsupp, Real.volume_Ioi]; simp

/-- Non-vanishing `𝒢_p(z) ≠ 0` on `Re z > 0` (`(ceo:O11n.1)`). -/
theorem fracGp_ne_zero {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {z : ℂ} (hz : 0 < z.re) : fracGp p z ≠ 0 := fun h => by
  have := fracGp_re_pos hp hz; rw [h, Complex.zero_re] at this; exact lt_irrefl 0 this

@[simp]
theorem fracBp_zero (p : ℝ) : fracBp p 0 = 0 := by simp [fracBp]

lemma fracBp_integrable {p x : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hx : 0 ≤ x) :
    IntegrableOn (fun s : ℝ => (1 - Real.exp (-x / √s)) * fracMuDensity p s) (Ioi (0 : ℝ)) := by
  refine (fracMuDensity_integrable hp).mono' (((Measurable.aestronglyMeasurable
    (by fun_prop : Measurable fun s : ℝ => 1 - Real.exp (-x / √s))).restrict).mul
      (fracMuDensity_integrable hp).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
  have h1 : Real.exp (-x / √s) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) (Real.sqrt_nonneg s))
  rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (fracMuDensity_pos hp hs).le)]
  exact mul_le_of_le_one_left (fracMuDensity_pos hp hs).le (by linarith [Real.exp_pos (-x / √s)])

/-- Bounds `0 ≤ B_p(x) < 1` for `x ≥ 0` (`(ceo:O11n.1)`). -/
theorem fracBp_nonneg_and_lt_one {p x : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hx : 0 ≤ x) :
    0 ≤ fracBp p x ∧ fracBp p x < 1 := by
  refine ⟨setIntegral_nonneg measurableSet_Ioi fun s hs => ?_, ?_⟩
  · have h1 : Real.exp (-x / √s) ≤ 1 := Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) (Real.sqrt_nonneg s))
    exact mul_nonneg (by linarith) (fracMuDensity_pos hp hs).le
  · have hrem_int : IntegrableOn (fun s : ℝ => Real.exp (-x / √s) * fracMuDensity p s) (Ioi (0 : ℝ)) :=
      ((fracMuDensity_integrable hp).sub (fracBp_integrable hp hx)).congr_fun
        (fun s _ => by simp [Pi.sub_apply]; ring) measurableSet_Ioi
    have hrem_pos : 0 < ∫ s in Ioi (0 : ℝ), Real.exp (-x / √s) * fracMuDensity p s := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae ((ae_restrict_mem measurableSet_Ioi).mono
        fun s hs => mul_nonneg (Real.exp_pos _).le (fracMuDensity_pos hp hs).le) hrem_int]
      have hsupp : Function.support (fun s : ℝ => Real.exp (-x / √s) * fracMuDensity p s) ∩ Ioi 0 = Ioi 0 := by
        ext s; simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
        intro hs; exact (mul_pos (Real.exp_pos _) (fracMuDensity_pos hp hs)).ne'
      rw [hsupp, Real.volume_Ioi]; simp
    have hsum : ∫ s in Ioi (0 : ℝ), Real.exp (-x / √s) * fracMuDensity p s = 1 - fracBp p x := by
      simp_rw [show ∀ s : ℝ, Real.exp (-x / √s) * fracMuDensity p s =
        fracMuDensity p s - (1 - Real.exp (-x / √s)) * fracMuDensity p s from fun s => by ring]
      rw [integral_sub (fracMuDensity_integrable hp) (fracBp_integrable hp hx), fracMuDensity_integral_one hp]; rfl
    linarith

/-- Asymptotic limit `B_p(x) → 1` as `x → ∞` (`(ceo:O11n.1)`). -/
theorem fracBp_tendsto_one {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : Tendsto (fracBp p) atTop (𝓝 1) := by
  have h_meas : ∀ᶠ x : ℝ in atTop, AEStronglyMeasurable
      (fun s : ℝ => (1 - Real.exp (-x / √s)) * fracMuDensity p s) (volume.restrict (Ioi (0 : ℝ))) :=
    eventually_ge_atTop (0 : ℝ) |>.mono fun x hx => (fracBp_integrable hp hx).aestronglyMeasurable
  have h_bound : ∀ᶠ x : ℝ in atTop, ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(1 - Real.exp (-x / √s)) * fracMuDensity p s‖ ≤ fracMuDensity p s :=
    (eventually_ge_atTop (0 : ℝ)).mono fun x hx => (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => by
      have h1 : Real.exp (-x / √s) ≤ 1 := Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) (Real.sqrt_nonneg s))
      rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (fracMuDensity_pos hp hs).le)]
      exact mul_le_of_le_one_left (fracMuDensity_pos hp hs).le (by linarith [Real.exp_pos (-x / √s)])
  have h_lim : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun x : ℝ => (1 - Real.exp (-x / √s)) * fracMuDensity p s) atTop (𝓝 (fracMuDensity p s)) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => by
      have hexp : Tendsto (fun x : ℝ => Real.exp (-x / √s)) atTop (𝓝 0) :=
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
          (neg_lt_zero.mpr (inv_pos.mpr (Real.sqrt_pos.mpr hs))))).congr fun x => by simp [div_eq_mul_inv, mul_comm]
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).mul_const (fracMuDensity p s)
  unfold fracBp
  simpa only [fracMuDensity_integral_one hp] using
    tendsto_integral_filter_of_dominated_convergence (fracMuDensity p) h_meas h_bound (fracMuDensity_integrable hp) h_lim

/-! ### Part 2: Dirichlet eigenfunctions, `L²` convergence, Parseval, and reproducing identity -/

/-- Normalized Dirichlet eigenfunctions `φ_n(t) = Ai(t + a_n) / Ai'(a_n)` on `(0, ∞)`
(`ce_o1_route.tex` `(ceo:O11n)`). -/
noncomputable def dirichletPhi (n : ℕ) (t : ℝ) : ℝ :=
  airyAi (t + airyZero (n + 1)) / airyAi' (airyZero (n + 1))

/-- `φ_n` as an element of `L²(ℝ; ℂ)` supported on `(0, ∞)`, equal to `A L_n`. -/
noncomputable def dirichletPhiL2 (n : ℕ) : AiryL2 :=
  airyA (cohnLL2 n)

/-- `v_b = ∑ b_n φ_n` in `L²(0, ∞)` for `b ∈ ℓ²` (`(ceo:O11n)`). -/
noncomputable def dirichletVL2 (b : ℕ → ℝ) : AiryL2 :=
  ∑' n : ℕ, (b n : ℂ) • dirichletPhiL2 n

/-- Real representative of `v_b` on `ℝ` (supported a.e. on `(0, ∞)`). -/
noncomputable def dirichletV (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  (dirichletVL2 b t).re

/-- Cardinal series `H_b(u) = ∑' n, b_n L_n(u)` on `ℝ` (`(ceo:O11n)`). -/
noncomputable def cardinalHb (b : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∑' n : ℕ, b n * cohnL n u

/-- Complex entire extension `H_b(z) = ∑' n, b_n L_n(z)` (`(ceo:O11n)`). -/
noncomputable def cardinalHbC (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (b n : ℂ) * cohnLC n z

/-- Coherent square `P_b(u) = H_b(u)²` (`(ceo:O11n)`). -/
noncomputable def cardinalPb (b : ℕ → ℝ) (u : ℝ) : ℝ :=
  cardinalHb b u ^ 2

/-- Complex entire extension `P_b(z) = H_b(z)²` (`(ceo:O11n)`). -/
noncomputable def cardinalPbC (b : ℕ → ℝ) (z : ℂ) : ℂ :=
  cardinalHbC b z ^ 2

private lemma dirichletPhiL2_eq_smul_airyHalf (n : ℕ) :
    dirichletPhiL2 n = (((airyAi' (airyZero (n + 1)))⁻¹ : ℝ) : ℂ) • airyHalf (airyZero (n + 1)) := by
  unfold dirichletPhiL2 cohnLL2 airyKerL2
  rw [map_smul, airyA_airyA]

private lemma dirichletPhiL2_ae (n : ℕ) :
    dirichletPhiL2 n =ᵐ[volume] fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (dirichletPhi n t : ℂ)) t := by
  rw [dirichletPhiL2_eq_smul_airyHalf]
  filter_upwards [Lp.coeFn_smul (((airyAi' (airyZero (n + 1)))⁻¹ : ℝ) : ℂ)
    (airyHalf (airyZero (n + 1))), airyHalf_coeFn (airyZero (n + 1))] with t h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · simp only [Set.indicator_of_mem ht, dirichletPhi]
    rw [add_comm t (airyZero (n + 1))]
    push_cast; ring
  · simp [ht]

lemma dirichletPhiL2_orthonormal : Orthonormal ℂ dirichletPhiL2 := by
  rw [orthonormal_iff_ite]
  intro n m
  unfold dirichletPhiL2
  rw [airyA_inner]
  exact (orthonormal_iff_ite.mp cohnLL2_orthonormal) n m

private lemma airyA_dirichletPhiL2 (n : ℕ) : airyA (dirichletPhiL2 n) = cohnLL2 n := by
  unfold dirichletPhiL2; exact airyA_airyA _

private lemma airyPL_dirichletPhiL2 (n : ℕ) : airyPL (dirichletPhiL2 n) = dirichletPhiL2 n := by
  rw [dirichletPhiL2_eq_smul_airyHalf, map_smul, airyPL_airyHalf]

private lemma l2_norm_sq_eq_integral_Ioi {G : AiryL2} {f : ℝ → ℝ}
    (hae : G =ᵐ[volume] fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (f t : ℂ)) t) :
    ‖G‖ ^ 2 = ∫ t in Ioi (0 : ℝ), f t ^ 2 := by
  have hin := MeasureTheory.L2.inner_def (𝕜 := ℂ) G G
  have h1 : inner ℂ G G = ((‖G‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; simp
  have h2 : ∫ t : ℝ, inner ℂ (G t) (G t) = ((∫ t in Ioi (0 : ℝ), f t ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (hae.mono fun t ht => ?_)
    dsimp; rw [ht]
    by_cases h : t ∈ Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem h, Complex.conj_ofReal]; push_cast; ring
    · simp [h]
  rw [h2] at hin
  exact Complex.ofReal_injective (hin.symm.trans h1).symm

private lemma dirichletVL2_eq_airyA {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2)) :
    dirichletVL2 b = airyA (∑' n : ℕ, (b n : ℂ) • cohnLL2 n) := by
  have hHasSum : HasSum (fun n : ℕ => (b n : ℂ) • dirichletPhiL2 n) (dirichletVL2 b) :=
    ((dirichletPhiL2_orthonormal.orthogonalFamily.summable_iff_norm_sq_summable (fun n => (b n : ℂ))).mpr
      (hb.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])).hasSum
  have hmap := (cardinal_series_of_sq_hasSum hb.hasSum).2.2.1.mapL airyAL
  rw [show (fun n : ℕ => airyAL ((b n : ℂ) • cohnLL2 n)) = fun n => (b n : ℂ) • dirichletPhiL2 n
    from funext fun n => by rw [airyAL_apply, map_smul]; rfl] at hmap
  exact hHasSum.unique hmap

/-- **`L²(0, ∞)` convergence of `v_b = ∑ b_n φ_n`:**
for `b ∈ ℓ²`, `∑ (b_n : ℂ) • φ_n` converges in `L²(ℝ)` to `dirichletVL2 b`, `dirichletVL2 b` is
supported a.e. on `(0, ∞)` and a.e. real with representative `dirichletV b`, and the partial sums
`∑_{n < N} b_n φ_n` converge in `L²(0, ∞)` to `dirichletV b`. -/
theorem dirichletV_L2_convergence {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2)) :
    HasSum (fun n : ℕ => (b n : ℂ) • dirichletPhiL2 n) (dirichletVL2 b) ∧
    (dirichletVL2 b =ᵐ[volume] fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (dirichletV b t : ℂ)) t) ∧
    IntegrableOn (fun t : ℝ => dirichletV b t ^ 2) (Ioi (0 : ℝ)) ∧
    Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ),
        (dirichletV b t - ∑ n ∈ Finset.range N, b n * dirichletPhi n t) ^ 2)
      atTop (𝓝 0) := by
  have hHasSum : HasSum (fun n : ℕ => (b n : ℂ) • dirichletPhiL2 n) (dirichletVL2 b) :=
    ((dirichletPhiL2_orthonormal.orthogonalFamily.summable_iff_norm_sq_summable (fun n => (b n : ℂ))).mpr
      (hb.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])).hasSum
  have hPL : airyPL (dirichletVL2 b) = dirichletVL2 b := by
    have hmap := hHasSum.mapL airyPL
    rw [show (fun n : ℕ => airyPL ((b n : ℂ) • dirichletPhiL2 n)) = fun n => (b n : ℂ) • dirichletPhiL2 n
      from funext fun n => by rw [map_smul, airyPL_dirichletPhiL2]] at hmap
    exact (hHasSum.unique hmap).symm
  let S : ℕ → AiryL2 := fun N => ∑ n ∈ Finset.range N, (b n : ℂ) • dirichletPhiL2 n
  have hS_ae : ∀ N : ℕ, S N =ᵐ[volume] fun t : ℝ =>
      (Ioi (0 : ℝ)).indicator (fun t => ((∑ n ∈ Finset.range N, b n * dirichletPhi n t : ℝ) : ℂ)) t := fun N => by
    have hsmul : ∀ n ∈ Finset.range N, ((b n : ℂ) • dirichletPhiL2 n : AiryL2) =ᵐ[volume]
        fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => ((b n * dirichletPhi n t : ℝ) : ℂ)) t := fun n _ => by
      filter_upwards [Lp.coeFn_smul (b n : ℂ) (dirichletPhiL2 n), dirichletPhiL2_ae n] with t h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]; by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht]
    filter_upwards [Lp.coeFn_finsetSum (Finset.range N) (fun n => (b n : ℂ) • dirichletPhiL2 n),
      (Finset.eventually_all (Finset.range N)).mpr hsmul] with t hu1 hu2
    rw [hu1, Finset.sum_apply, Finset.sum_congr rfl fun n hn => hu2 n hn]
    by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht]
  have hS_tend : Tendsto S atTop (𝓝 (dirichletVL2 b)) := hHasSum.tendsto_sum_nat
  have him_zero : ∀ᵐ t : ℝ, (dirichletVL2 b t).im = 0 := by
    have heLp : Tendsto (fun N => eLpNorm (⇑(S N) - ⇑(dirichletVL2 b)) 2 volume) atTop (𝓝 0) := by
      have hnorm : Tendsto (fun N => ENNReal.ofReal ‖S N - dirichletVL2 b‖) atTop (𝓝 0) := by
        simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hS_tend)
      refine hnorm.congr fun N => ?_
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      exact eLpNorm_congr_ae (Lp.coeFn_sub _ _)
    obtain ⟨φ, _, hφ_ae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero heLp).exists_seq_tendsto_ae
    have hS_im : ∀ k : ℕ, ∀ᵐ t : ℝ, (S (φ k) t).im = 0 := fun k =>
      (hS_ae (φ k)).mono fun t ht => by rw [ht]; by_cases h : t ∈ Ioi (0 : ℝ) <;> simp [h]
    filter_upwards [hφ_ae, ae_all_iff.mpr hS_im] with t ht_lim ht_im
    exact tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp ht_lim)
      (tendsto_const_nhds.congr fun k => (ht_im k).symm)
  have hae : dirichletVL2 b =ᵐ[volume]
      fun t : ℝ => (Ioi (0 : ℝ)).indicator (fun t => (dirichletV b t : ℂ)) t := by
    filter_upwards [(airyIndProj_eq_self_iff _ _).mp hPL, him_zero] with t hts hti
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem ht, dirichletV]; exact Complex.ext rfl hti
    · simp only [Set.indicator_of_notMem ht]; exact hts ht
  have hint_sq : IntegrableOn (fun t : ℝ => dirichletV b t ^ 2) (Ioi (0 : ℝ)) := by
    have hsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (dirichletVL2 b))).mp (Lp.memLp _)
    refine hsq.integrableOn.congr ?_
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioi] with t ht htm
    rw [ht]; simp [htm, Complex.norm_real, sq_abs]
  have hL2_tend : Tendsto (fun N : ℕ => ∫ t in Ioi (0 : ℝ),
      (dirichletV b t - ∑ n ∈ Finset.range N, b n * dirichletPhi n t) ^ 2) atTop (𝓝 0) := by
    have hnsq : Tendsto (fun N => ‖dirichletVL2 b - S N‖ ^ 2) atTop (𝓝 0) := by
      have h0 : Tendsto (fun N => ‖dirichletVL2 b - S N‖) atTop (𝓝 0) := by
        simpa [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp hS_tend
      have h2 := h0.pow 2
      rwa [zero_pow two_ne_zero] at h2
    refine hnsq.congr fun N => l2_norm_sq_eq_integral_Ioi ?_
    filter_upwards [Lp.coeFn_sub (dirichletVL2 b) (S N), hae, hS_ae N] with t hsub hV hSN
    rw [hsub, Pi.sub_apply, hV, hSN]; by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht]
  exact ⟨hHasSum, hae, hint_sq, hL2_tend⟩

/-- When `∑ b_n φ_n(t)` converges a.e. on `(0, ∞)`, its sum equals `dirichletV b t` a.e. -/
theorem dirichletV_eq_tsum_ae {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2))
    (hsum : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), Summable (fun n : ℕ => b n * dirichletPhi n t)) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), dirichletV b t = ∑' n : ℕ, b n * dirichletPhi n t := by
  have hL2 := (dirichletV_L2_convergence hb).2.2.2
  have heLp : Tendsto (fun N => eLpNorm (fun t =>
      (∑ n ∈ Finset.range N, b n * dirichletPhi n t) - dirichletV b t) 2 (volume.restrict (Ioi 0)))
      atTop (𝓝 0) := by
    have hL2s : Tendsto (fun N : ℕ => ENNReal.ofReal (√(∫ t in Ioi (0 : ℝ),
        (dirichletV b t - ∑ n ∈ Finset.range N, b n * dirichletPhi n t) ^ 2))) atTop (𝓝 0) := by
      simpa [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hL2.sqrt
    refine hL2s.congr fun N => ?_
    have hm1 : MemLp (dirichletV b) 2 (volume.restrict (Ioi 0)) :=
      (memLp_two_iff_integrable_sq_norm
        ((Complex.continuous_re.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).restrict)).mpr
        (by simpa only [IntegrableOn, dirichletV, Real.norm_eq_abs, sq_abs] using (dirichletV_L2_convergence hb).2.2.1)
    have hm2 : MemLp (fun t => ∑ n ∈ Finset.range N, b n * dirichletPhi n t) 2 (volume.restrict (Ioi 0)) := by
      rw [show (fun t => ∑ n ∈ Finset.range N, b n * dirichletPhi n t) =
          ∑ n ∈ Finset.range N, fun t => b n * dirichletPhi n t from
          funext fun t => (Finset.sum_apply t (Finset.range N) fun n t => b n * dirichletPhi n t).symm]
      refine memLp_finsetSum' _ fun n _ => ?_
      have : (fun t : ℝ => b n * dirichletPhi n t) =ᵐ[volume.restrict (Ioi 0)]
          fun t : ℝ => (((b n : ℂ) • dirichletPhiL2 n) t).re := by
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul (b n : ℂ) (dirichletPhiL2 n)),
          ae_restrict_of_ae (dirichletPhiL2_ae n), ae_restrict_mem measurableSet_Ioi] with t h1 h2 ht
        rw [h1, Pi.smul_apply, h2, smul_eq_mul, Set.indicator_of_mem ht, ← Complex.ofReal_mul, Complex.ofReal_re]
      exact (((Lp.memLp ((b n : ℂ) • dirichletPhiL2 n)).restrict (Ioi 0)).re).ae_eq this.symm
    rw [← Pi.sub_def, (hm2.sub hm1).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    congr 1; simp only [Pi.sub_apply, Real.norm_eq_abs, Real.sqrt_eq_rpow, norm_sub_rev]; norm_num
  obtain ⟨φ, hφ_mono, hφ_ae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero heLp).exists_seq_tendsto_ae
  filter_upwards [hsum, hφ_ae] with t hst ht_lim
  exact tendsto_nhds_unique ht_lim (hst.hasSum.tendsto_sum_nat.comp hφ_mono.tendsto_atTop)

/-- **Parseval identity:** `∫₀^∞ v_b(t)² dt = ∑_{n ≥ 1} b_n² = ∫_ℝ H_b(u)² du`
(`ce_o1_route.tex` `(ceo:O11n)`). -/
theorem dirichletV_parseval {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2)) :
    (∫ t in Ioi (0 : ℝ), dirichletV b t ^ 2 = ∑' n : ℕ, b n ^ 2) ∧
    (∑' n : ℕ, b n ^ 2 = ∫ u : ℝ, cardinalHb b u ^ 2) := by
  have hpack := cardinal_series_of_sq_hasSum hb.hasSum
  let F : AiryL2 := ∑' n : ℕ, (b n : ℂ) • cohnLL2 n
  have hV_norm : ‖dirichletVL2 b‖ ^ 2 = ∑' n : ℕ, b n ^ 2 := by
    rw [dirichletVL2_eq_airyA hb, airyA_norm, hpack.2.1]
  have hV_int : ∫ t in Ioi (0 : ℝ), dirichletV b t ^ 2 = ‖dirichletVL2 b‖ ^ 2 :=
    (l2_norm_sq_eq_integral_Ioi (dirichletV_L2_convergence hb).2.1).symm
  have hH_int : ∫ u : ℝ, cardinalHb b u ^ 2 = ‖F‖ ^ 2 := by
    have hin := MeasureTheory.L2.inner_def (𝕜 := ℂ) F F
    have h1 : inner ℂ F F = ((‖F‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]; simp
    have hae : (F : ℝ → ℂ) =ᵐ[volume] fun u : ℝ => (cardinalHb b u : ℂ) := by
      filter_upwards [airyPWFun_ae hpack.1] with u hu
      have hre := hpack.2.2.2.2.1 u
      unfold cardinalHb; rw [hu, hre.2, hre.1.tsum_eq]
    have h2 : ∫ u : ℝ, inner ℂ (F u) (F u) = ((∫ u : ℝ, cardinalHb b u ^ 2 : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (hae.mono fun u hu => ?_)
      dsimp; rw [hu, Complex.conj_ofReal]; push_cast; ring
    rw [h2] at hin
    exact Complex.ofReal_injective (hin.symm.trans h1)
  exact ⟨hV_int.trans hV_norm, (hH_int.trans hpack.2.1).symm⟩

/-- **Reproducing identity (complex):** `H_b(z) = ∫₀^∞ Ai(z + t) v_b(t) dt` (`(ceo:O11n)`). -/
theorem cardinalHbC_eq_reproducing {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2)) (z : ℂ) :
    cardinalHbC b z = ∫ t in Ioi (0 : ℝ), airyAiC (z + (t : ℂ)) * (dirichletV b t : ℂ) := by
  have hpack := cardinal_series_of_sq_hasSum hb.hasSum
  let F : AiryL2 := ∑' n : ℕ, (b n : ℂ) • cohnLL2 n
  have hHbC : cardinalHbC b z = airyPWFun F z := (hpack.2.2.2.1 z).tsum_eq
  have hinner : airyPWFun F z = airyPsiC (dirichletVL2 b) z := by
    rw [airyPW_eval_inner hpack.1 z, airyKerCL2]
    change inner ℂ (airyA (airyHalfC ((starRingEnd ℂ) z))) F = airyPsiC (dirichletVL2 b) z
    rw [airyA_inner_left, ← dirichletVL2_eq_airyA hb, airyPsiC_eq_inner]
  rw [hHbC, hinner]
  unfold airyPsiC
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [(dirichletV_L2_convergence hb).2.1] with t ht htm
  rw [ht, Set.indicator_of_mem htm, mul_comm]

/-- **Reproducing identity (real):** `H_b(u) = ∫₀^∞ Ai(u + t) v_b(t) dt` (`(ceo:O11n)`). -/
theorem cardinalHb_eq_reproducing {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2)) (u : ℝ) :
    cardinalHb b u = ∫ t in Ioi (0 : ℝ), airyAi (u + t) * dirichletV b t := by
  have hC := cardinalHbC_eq_reproducing hb (u : ℂ)
  have hpack := cardinal_series_of_sq_hasSum hb.hasSum
  have hHb : (cardinalHb b u : ℂ) = cardinalHbC b (u : ℂ) := by
    unfold cardinalHb cardinalHbC
    rw [(hpack.2.2.2.2.1 u).1.tsum_eq, ← (hpack.2.2.2.2.1 u).2, (hpack.2.2.2.1 (u : ℂ)).tsum_eq]
  have hintR : ∫ t in Ioi (0 : ℝ), airyAiC ((u : ℂ) + (t : ℂ)) * (dirichletV b t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), airyAi (u + t) * dirichletV b t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← Complex.ofReal_add, airyAiC_ofReal, Complex.ofReal_mul]
  exact Complex.ofReal_injective (hHb.trans (hC.trans hintR))

/-! ### Part 3: Exact Airy pair Laplace identity `(ceo:O11n.7)` and Gaussian transform `(ceo:O11n.2)` -/

/-- Complex-argument twisted Airy Laplace transform `X̃(i y) = k e^{-y³ / 12} ∫_ℝ X(u) e^{y u} du`
(`ce_o1_route.tex` `(ceo:O11n.2)`, `ce_rate.tex` `(cel:1.3)`). -/
noncomputable def airyTwistedLaplaceC (X : ℝ → ℝ) (y : ℂ) : ℂ :=
  (ceK : ℂ) * Complex.exp (-(y ^ 3) / 12) * ∫ u : ℝ, (X u : ℂ) * Complex.exp (y * (u : ℂ))

lemma airyTwistedLaplaceC_ofReal (X : ℝ → ℝ) (y : ℝ) :
    airyTwistedLaplaceC X (y : ℂ) = (airyTwistedLaplace X y : ℂ) := by
  unfold airyTwistedLaplaceC airyTwistedLaplace
  have hexp : Complex.exp (-((y : ℂ) ^ 3) / 12) = (Real.exp (-(y ^ 3) / 12) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  have hint : ∫ u : ℝ, (X u : ℂ) * Complex.exp ((y : ℂ) * (u : ℂ)) =
      ((∫ u : ℝ, X u * Real.exp (y * u) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      dsimp; rw [← Complex.ofReal_mul y u, ← Complex.ofReal_exp, ← Complex.ofReal_mul])
  rw [hexp, hint]; push_cast; rfl

lemma airyTwistedLaplaceC_eq_airyFtilde (X : ℝ → ℝ) {f : ℂ → ℂ}
    (hf : ∀ u : ℝ, f (u : ℂ) = (X u : ℂ)) (y : ℂ) :
    airyTwistedLaplaceC X y = airyFtilde f (Complex.I * y) := by
  unfold airyTwistedLaplaceC airyFtilde airyFhat
  have hk : (ceK : ℂ) = (airyPhiK : ℂ) := rfl
  have h1 : -(y ^ 3) / 12 = -(Complex.I * (Complex.I * y) ^ 3 / 12) := by
    rw [mul_pow, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]
    have hII : Complex.I * (-Complex.I) = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
    calc -(y ^ 3) / 12 = -(Complex.I * (-Complex.I) * y ^ 3 / 12) := by rw [hII]; ring
      _ = -(Complex.I * (-Complex.I * y ^ 3) / 12) := by ring
  have hint : ∫ u : ℝ, (X u : ℂ) * Complex.exp (y * (u : ℂ)) =
      ∫ u : ℝ, f (u : ℂ) * Complex.exp (-(Complex.I * (Complex.I * y) * (u : ℂ))) :=
    integral_congr_ae (Eventually.of_forall fun u => by
      dsimp; rw [← hf u, show -(Complex.I * (Complex.I * y) * (u : ℂ)) = y * (u : ℂ) by
        calc _ = -(Complex.I * Complex.I * y * (u : ℂ)) := by ring
          _ = _ := by rw [Complex.I_mul_I]; ring])
  rw [hk, h1, hint]

/-- **Exact Airy product Laplace identity (`u1c_estimate_proofs.tex` `(ceo:O11n.7)`):**
for `t, s : ℝ` and `Re y > 0`,
`∫_ℝ Ai(u + t) Ai(u + s) e^{y u} du = (4 π y)^{-1/2} exp(y³/12 - y(t+s)/2 - (t-s)²/(4y))`. -/
theorem airy_pair_laplace_eq (t s : ℝ) {y : ℂ} (hy : 0 < y.re) :
    Integrable (fun u : ℝ => (airyAi (u + t) : ℂ) * (airyAi (u + s) : ℂ) * Complex.exp (y * (u : ℂ))) ∧
    ∫ u : ℝ, (airyAi (u + t) : ℂ) * (airyAi (u + s) : ℂ) * Complex.exp (y * (u : ℂ)) =
      ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
        Complex.exp (y ^ 3 / 12 - y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) := by
  let c : ℝ := y.re / 2
  have hc : 0 < c := by positivity
  have hc_re : ((y - (c : ℂ)) : ℂ).re = c := by simp [c]; ring
  have hTilt_s : Integrable (fun u : ℝ => airyTilt c (u + s)) := (integrable_airyTilt hc).comp_add_right s
  let M : ℝ := (1 / (2 * π)) * (Real.exp ((2 * c) ^ 3 / 3) * √(π / (2 * c))) +
    (1 / (2 * π)) * (Real.exp ((c / 2) ^ 3 / 3) * √(π / (c / 2)))
  have hM : ∀ u : ℝ, ‖airyTilt c (u + t)‖ ≤ M := fun u =>
    (norm_airyTilt_le hc (u + t)).trans (mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (abs_nonneg _))))
  have hInt_prod : Integrable (fun u : ℝ =>
      (airyAi (u + t) : ℂ) * (airyAi (u + s) : ℂ) * Complex.exp (y * (u : ℂ))) := by
    refine (hTilt_s.norm.const_mul (M * Real.exp (-c * (t + s)))).mono' (by have := continuous_airyAi; fun_prop)
      (Eventually.of_forall fun u => ?_)
    have hexp_eq : Complex.exp (y * (u : ℂ)) = Complex.exp (-((c * (t + s) : ℝ) : ℂ)) *
        Complex.exp ((c : ℂ) * ((u + t : ℝ) : ℂ)) * Complex.exp ((c : ℂ) * ((u + s : ℝ) : ℂ)) *
        Complex.exp (((y.im * u : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]; congr 1
      nth_rw 1 [show y = ((2 * c : ℝ) : ℂ) + (y.im : ℂ) * Complex.I from Complex.ext (by simp [c]; ring) (by simp)]
      push_cast; ring
    have hnorm_fac : ‖Complex.exp (-((c * (t + s) : ℝ) : ℂ))‖ = Real.exp (-c * (t + s)) := by
      rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, neg_mul]
    rw [show (airyAi (u + t) : ℂ) * (airyAi (u + s) : ℂ) * Complex.exp (y * (u : ℂ)) =
      Complex.exp (-((c * (t + s) : ℝ) : ℂ)) * airyTilt c (u + t) * airyTilt c (u + s) *
        Complex.exp (((y.im * u : ℝ) : ℂ) * Complex.I) from by unfold airyTilt; rw [hexp_eq]; ring,
      norm_mul, norm_mul, norm_mul, hnorm_fac, Complex.norm_exp_ofReal_mul_I, mul_one]
    calc _ ≤ Real.exp (-c * (t + s)) * M * ‖airyTilt c (u + s)‖ := by gcongr; exact hM u
      _ = _ := by ring
  let F : ℝ × ℝ → ℂ := fun p => Complex.exp (-((c * t : ℝ) : ℂ)) *
    (Complex.exp (((-(2 * π * p.2 * (p.1 + t)) : ℝ) : ℂ) * Complex.I) * airyFourierH c p.2) *
    (airyAi (p.1 + s) : ℂ) * Complex.exp ((y - (c : ℂ)) * (p.1 : ℂ))
  have hF_cont : Continuous F := by have := continuous_airyAi; have := continuous_airyFourierH c; fun_prop
  have hF_int : Integrable F (volume.prod volume) := by
    refine (((hTilt_s.norm.const_mul (Real.exp (-c * (t + s)))).mul_prod (integrable_airyFourierH hc).norm)).mono'
      hF_cont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    have hnorm1 : ‖Complex.exp (-((c * t : ℝ) : ℂ))‖ = Real.exp (-c * t) := by
      rw [Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, neg_mul]
    have hnorm3 : ‖(airyAi (p.1 + s) : ℂ) * Complex.exp ((y - (c : ℂ)) * (p.1 : ℂ))‖ =
        Real.exp (-c * s) * ‖airyTilt c (p.1 + s)‖ := by
      rw [norm_mul, Complex.norm_exp, show ((y - (c : ℂ)) * (p.1 : ℂ)).re = c * p.1 by simp [Complex.mul_re, hc_re]]
      unfold airyTilt; rw [norm_mul, Complex.norm_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [← mul_assoc, mul_comm (Real.exp (-c * s)), mul_assoc, ← Real.exp_add]; congr 2; ring
    dsimp [F]
    rw [norm_mul, norm_mul, norm_mul, mul_assoc _ ‖(airyAi (p.1 + s) : ℂ)‖ _, ← norm_mul (airyAi _ : ℂ) _, hnorm3,
      norm_mul, hnorm1, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact le_of_eq (by rw [show -c * (t + s) = -c * t + -c * s by ring, Real.exp_add]; ring)
  have hF_u : ∀ u : ℝ, ∫ ξ : ℝ, F (u, ξ) = (airyAi (u + t) : ℂ) * (airyAi (u + s) : ℂ) * Complex.exp (y * (u : ℂ)) := fun u => by
    simp_rw [show ∀ ξ : ℝ, F (u, ξ) = (Complex.exp (-((c * t : ℝ) : ℂ)) * (airyAi (u + s) : ℂ) * Complex.exp ((y - (c : ℂ)) * (u : ℂ))) *
      (Complex.exp (-((2 * π * ξ * (u + t) : ℝ) : ℂ) * Complex.I) * airyFourierH c ξ) from fun ξ => by dsimp [F]; push_cast; ring,
      integral_const_mul, show (∫ ξ : ℝ, Complex.exp (-((2 * π * ξ * (u + t) : ℝ) : ℂ) * Complex.I) * airyFourierH c ξ) =
      airyTilt c (u + t) from by
        rw [airyTilt_eq_integral hc (u + t)]
        exact integral_congr_ae (Eventually.of_forall fun ξ =>
          congrArg (fun z : ℂ => Complex.exp z * airyFourierH c ξ) (by push_cast; ring))]
    unfold airyTilt
    have hce : Complex.exp (-((c * t : ℝ) : ℂ)) * Complex.exp ((c : ℂ) * ((u + t : ℝ) : ℂ)) *
        Complex.exp ((y - (c : ℂ)) * (u : ℂ)) = Complex.exp (y * (u : ℂ)) := by rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    linear_combination (airyAi (u + t) : ℂ) * (airyAi (u + s) : ℂ) * hce
  have hF_xi : ∀ ξ : ℝ, ∫ u : ℝ, F (u, ξ) =
      Complex.exp ((-4 * (π : ℂ) ^ 2 * y) * (ξ : ℂ) ^ 2 +
        (2 * (π : ℂ) * Complex.I * (2 * y * (c : ℂ) - (y ^ 2 + ((t - s : ℝ) : ℂ)))) * (ξ : ℂ) +
        (y * (c : ℂ) ^ 2 - (y ^ 2 + ((t - s : ℝ) : ℂ)) * (c : ℂ) + y ^ 3 / 3 - y * (s : ℂ))) := fun ξ => by
    let a : ℂ := (y - (c : ℂ)) - 2 * (π : ℂ) * Complex.I * (ξ : ℂ)
    have ha_re : 0 < a.re := by simpa [a, hc_re] using hc
    have hshift : ∫ u : ℝ, (airyAi (u + s) : ℂ) * Complex.exp (a * (u : ℂ)) =
        Complex.exp (-(a * (s : ℂ))) * Complex.exp (a ^ 3 / 3) := by
      simp_rw [show ∀ u : ℝ, (airyAi (u + s) : ℂ) * Complex.exp (a * (u : ℂ)) = Complex.exp (-(a * (s : ℂ))) *
        ((airyAi (u + s) : ℂ) * Complex.exp (a * ((u + s : ℝ) : ℂ))) from fun u => by rw [mul_left_comm, ← Complex.exp_add]; congr 2; push_cast; ring,
        integral_const_mul, integral_add_right_eq_self (fun u : ℝ => (airyAi u : ℂ) * Complex.exp (a * (u : ℂ))) s,
        integral_airyAi_mul_exp_complex ha_re]
    have hrew : ∀ u : ℝ, F (u, ξ) = (Complex.exp (-((c * t : ℝ) : ℂ)) * Complex.exp (-((2 * π * ξ * t : ℝ) : ℂ) * Complex.I) *
        airyFourierH c ξ) * ((airyAi (u + s) : ℂ) * Complex.exp (a * (u : ℂ))) := fun u => by
      dsimp [F, a]
      have hexp : Complex.exp (((-(2 * π * ξ * (u + t)) : ℝ) : ℂ) * Complex.I) * Complex.exp ((y - (c : ℂ)) * (u : ℂ)) =
          Complex.exp (-((2 * π * ξ * t : ℝ) : ℂ) * Complex.I) * Complex.exp (((y - (c : ℂ)) - 2 * (π : ℂ) * Complex.I * (ξ : ℂ)) * (u : ℂ)) := by
        rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
      linear_combination Complex.exp (-((c * t : ℝ) : ℂ)) * airyFourierH c ξ * (airyAi (u + s) : ℂ) * hexp
    simp_rw [hrew, integral_const_mul, hshift]
    unfold airyFourierH airyFourierSymbol airyLine
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; dsimp [a]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hswap := integral_integral_swap (f := fun u ξ => F (u, ξ)) hF_int
  have hquad := integral_cexp_quadratic (b := -4 * (π : ℂ) ^ 2 * y)
    (by rw [show -4 * (π : ℂ) ^ 2 * y = ((-4 * π ^ 2 : ℝ) : ℂ) * y by push_cast; ring,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith [Real.pi_pos, sq_pos_of_pos Real.pi_pos])
    (2 * (π : ℂ) * Complex.I * (2 * y * (c : ℂ) - (y ^ 2 + ((t - s : ℝ) : ℂ))))
    (y * (c : ℂ) ^ 2 - (y ^ 2 + ((t - s : ℝ) : ℂ)) * (c : ℂ) + y ^ 3 / 3 - y * (s : ℂ))
  have hlhs : ∫ u : ℝ, (airyAi (u + t) : ℂ) * (airyAi (u + s) : ℂ) * Complex.exp (y * (u : ℂ)) =
      ∫ ξ : ℝ, ∫ u : ℝ, F (u, ξ) := by
    rw [← hswap]; exact integral_congr_ae (Eventually.of_forall fun u => (hF_u u).symm)
  rw [hlhs]; simp_rw [hF_xi]; rw [hquad]
  have hy_ne : y ≠ 0 := fun h => by rw [h, Complex.zero_re] at hy; exact lt_irrefl 0 hy
  have hpiC : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcpow : ((π : ℂ) / -(-4 * (π : ℂ) ^ 2 * y)) ^ (1 / 2 : ℂ) = (4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)) := by
    have hdiv : (π : ℂ) / -(-4 * (π : ℂ) ^ 2 * y) = (4 * (π : ℂ) * y)⁻¹ := by field_simp [hpiC, hy_ne]
    have harg : (4 * (π : ℂ) * y).arg ≠ π := by
      have hre : 0 < (4 * (π : ℂ) * y).re := by simp [Complex.mul_re]; nlinarith [Real.pi_pos, hy]
      linarith [Real.pi_pos, (abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre))).2]
    rw [hdiv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  have hexp_alg : y * (c : ℂ) ^ 2 - (y ^ 2 + ((t - s : ℝ) : ℂ)) * (c : ℂ) + y ^ 3 / 3 - y * (s : ℂ) -
      (2 * (π : ℂ) * Complex.I * (2 * y * (c : ℂ) - (y ^ 2 + ((t - s : ℝ) : ℂ)))) ^ 2 / (4 * (-4 * (π : ℂ) ^ 2 * y)) =
      y ^ 3 / 12 - y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y) := by
    push_cast; field_simp [hpiC, hy_ne]; ring_nf; rw [Complex.I_sq]; ring
  rw [hcpow, hexp_alg]; exact ⟨hInt_prod, rfl⟩

/-- **Exact Airy-square Gaussian transform (`ce_o1_route.tex` `(ceo:O11n.2)`):**
for `b ∈ ℓ²` and `Re y > 0`,
`P̃_b(i y) = (k / √(4 π y)) ∫₀^∞ ∫₀^∞ v_b(t) v_b(s) exp(-y (t+s)/2 - (t-s)²/(4y)) dt ds`. -/
private lemma airySquare_gaussian_kernel_exp_le {y : ℂ} (hy : 0 < y.re) (t s : ℝ) :
    ‖Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))‖ ≤
      Real.exp (-(y.re / 2) * t) * Real.exp (-(y.re / 2) * s) := by
  rw [Complex.norm_exp, Complex.sub_re]
  have h1 : (-y * ((t + s : ℝ) : ℂ) / 2).re = -(y.re / 2) * (t + s) := by simp [Complex.mul_re]; ring
  have h2 : 0 ≤ (((t - s : ℝ) : ℂ) ^ 2 / (4 * y)).re := by
    rw [show ((t - s : ℝ) : ℂ) ^ 2 = (((t - s) ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by simp; linarith)) (Complex.normSq_nonneg _)
  rw [h1, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)

private lemma airySquare_gaussian_kernel_integrable {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2))
    {y : ℂ} (hy : 0 < y.re) :
    Integrable (fun p : ℝ × ℝ => ((dirichletV b p.1 * dirichletV b p.2 : ℝ) : ℂ) *
        Complex.exp (-y * ((p.1 + p.2 : ℝ) : ℂ) / 2 - ((p.1 - p.2 : ℝ) : ℂ) ^ 2 / (4 * y)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  have hv_meas : Measurable (dirichletV b) :=
    Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable (dirichletVL2 b)).measurable
  have hm_p : AEStronglyMeasurable (fun p : ℝ × ℝ => ((dirichletV b p.1 * dirichletV b p.2 : ℝ) : ℂ) *
      Complex.exp (-y * ((p.1 + p.2 : ℝ) : ℂ) / 2 - ((p.1 - p.2 : ℝ) : ℂ) ^ 2 / (4 * y))) (ν.prod ν) :=
    ((Complex.measurable_ofReal.comp ((hv_meas.comp measurable_fst).mul (hv_meas.comp measurable_snd))).mul
      (Complex.continuous_exp.measurable.comp (Measurable.sub
        ((measurable_const.mul (Complex.measurable_ofReal.comp (measurable_fst.add measurable_snd))).div_const 2)
        (((Complex.measurable_ofReal.comp (measurable_fst.sub measurable_snd)).pow_const 2).div_const _)))).aestronglyMeasurable
  have hv_exp_int : Integrable (fun t : ℝ => |dirichletV b t| * Real.exp (-(y.re / 2) * t)) ν := by
    have hm1 : AEStronglyMeasurable (fun t : ℝ => |dirichletV b t| * Real.exp (-(y.re / 2) * t)) ν :=
      (hv_meas.abs.mul (Real.continuous_exp.measurable.comp
        ((measurable_const (a := -(y.re / 2))).mul measurable_id))).aestronglyMeasurable
    refine (((dirichletV_L2_convergence hb).2.2.1.add (exp_neg_integrableOn_Ioi 0 hy)).div_const 2).mono' hm1 (ae_of_all _ fun t => ?_)
    dsimp; rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
    have hsq : Real.exp (-(y.re / 2) * t) ^ 2 = Real.exp (-y.re * t) := by rw [← Real.exp_nat_mul]; congr 1; ring
    nlinarith [sq_nonneg (|dirichletV b t| - Real.exp (-(y.re / 2) * t)), sq_abs (dirichletV b t), hsq]
  refine (hv_exp_int.mul_prod hv_exp_int).mono' hm_p (ae_of_all _ fun p => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc _ ≤ |dirichletV b p.1| * |dirichletV b p.2| * (Real.exp (-(y.re / 2) * p.1) * Real.exp (-(y.re / 2) * p.2)) := by
        gcongr; exact airySquare_gaussian_kernel_exp_le hy p.1 p.2
    _ = (|dirichletV b p.1| * Real.exp (-(y.re / 2) * p.1)) * (|dirichletV b p.2| * Real.exp (-(y.re / 2) * p.2)) := by ring

theorem airySquare_gaussian_transform {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2))
    {y : ℂ} (hy : 0 < y.re) :
    airyTwistedLaplaceC (cardinalPb b) y =
      (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
        ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
          Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let G : ℝ × ℝ × ℝ → ℂ := fun q => ((airyAi (q.1 + q.2.1) * dirichletV b q.2.1 : ℝ) : ℂ) *
    ((airyAi (q.1 + q.2.2) * dirichletV b q.2.2 : ℝ) : ℂ) * Complex.exp (y * (q.1 : ℂ))
  have hv_meas : Measurable (dirichletV b) :=
    Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable (dirichletVL2 b)).measurable
  have hG_meas : StronglyMeasurable G :=
    (((Complex.measurable_ofReal.comp ((continuous_airyAi.measurable.comp (measurable_fst.add
        (measurable_fst.comp measurable_snd))).mul (hv_meas.comp (measurable_fst.comp measurable_snd)))).mul
      (Complex.measurable_ofReal.comp ((continuous_airyAi.measurable.comp (measurable_fst.add
        (measurable_snd.comp measurable_snd))).mul (hv_meas.comp (measurable_snd.comp measurable_snd))))).mul
      (Complex.continuous_exp.measurable.comp (measurable_const.mul (Complex.measurable_ofReal.comp measurable_fst)))).stronglyMeasurable
  have hv_sq_int : Integrable (fun t : ℝ => dirichletV b t ^ 2) ν := (dirichletV_L2_convergence hb).2.2.1
  have hu_int : ∀ u : ℝ, Integrable (fun t : ℝ => airyAi (u + t) * dirichletV b t) ν := fun u => by
    refine ((integrableOn_airyAi_shift_sq u).add hv_sq_int).mono'
      (((continuous_airyAi.measurable.comp (measurable_const.add measurable_id)).mul hv_meas).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    dsimp; nlinarith [sq_nonneg (|airyAi (u + t)| - |dirichletV b t|),
      abs_mul (airyAi (u + t)) (dirichletV b t), sq_abs (airyAi (u + t)), sq_abs (dirichletV b t)]
  have hcs : ∀ u : ℝ, (∫ t : ℝ, |airyAi (u + t) * dirichletV b t| ∂ν) ^ 2 ≤
        airyKappa (u : ℂ) * (∫ t : ℝ, dirichletV b t ^ 2 ∂ν) := fun u => by
    let A : ℝ := airyKappa (u : ℂ)
    let B : ℝ := ∫ t : ℝ, dirichletV b t ^ 2 ∂ν
    let C : ℝ := ∫ t : ℝ, |airyAi (u + t) * dirichletV b t| ∂ν
    have hA_eq : A = ∫ t : ℝ, airyAi (u + t) ^ 2 ∂ν := by
      unfold A airyKappa
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [← Complex.ofReal_add, airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rcases eq_or_lt_of_le (integral_nonneg fun t => sq_nonneg (dirichletV b t) : 0 ≤ B) with hB0 | hB_pos
    · have hC0 : C = 0 := integral_eq_zero_of_ae (((integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hv_sq_int).mp hB0.symm).mono
        fun t ht => by simp only [Pi.zero_apply, sq_eq_zero_iff] at ht; simp [ht])
      change C ^ 2 ≤ A * B; rw [hC0, zero_pow two_ne_zero]; exact mul_nonneg (airyKappa_nonneg _) hB0.le
    · let lam : ℝ := C / B
      let g1 : ℝ → ℝ := fun t => airyAi (u + t) ^ 2
      let g2 : ℝ → ℝ := fun t => 2 * lam * ‖airyAi (u + t) * dirichletV b t‖
      let g3 : ℝ → ℝ := fun t => lam ^ 2 * dirichletV b t ^ 2
      have hq : 0 ≤ ∫ t : ℝ, (|airyAi (u + t)| - lam * |dirichletV b t|) ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
      have hexp : ∫ t : ℝ, (|airyAi (u + t)| - lam * |dirichletV b t|) ^ 2 ∂ν = A - 2 * lam * C + lam ^ 2 * B := by
        calc _ = ∫ t : ℝ, (g1 - g2 + g3) t ∂ν := integral_congr_ae (ae_of_all _ fun t => by
              simp only [Pi.add_apply, Pi.sub_apply, g1, g2, g3, Real.norm_eq_abs, abs_mul, sub_sq, sq_abs, mul_pow]; ring)
          _ = (∫ t : ℝ, (g1 - g2) t ∂ν) + ∫ t : ℝ, g3 t ∂ν :=
              integral_add ((integrableOn_airyAi_shift_sq u).sub ((hu_int u).norm.const_mul (2 * lam))) (hv_sq_int.const_mul (lam ^ 2))
          _ = ((∫ t : ℝ, g1 t ∂ν) - ∫ t : ℝ, g2 t ∂ν) + ∫ t : ℝ, g3 t ∂ν := by
              dsimp only [Pi.sub_apply, g1, g2]; rw [integral_sub (integrableOn_airyAi_shift_sq u) ((hu_int u).norm.const_mul (2 * lam))]
          _ = A - 2 * lam * C + lam ^ 2 * B := by
              dsimp only [g1, g2, g3]; simp only [Real.norm_eq_abs]; rw [integral_const_mul, integral_const_mul, ← hA_eq]
      rw [hexp] at hq
      have hmul := mul_le_mul_of_nonneg_right (show 2 * lam * C - lam ^ 2 * B ≤ A by linarith) hB_pos.le
      have hB_ne : B ≠ 0 := hB_pos.ne'
      have halg : (2 * lam * C - lam ^ 2 * B) * B = C ^ 2 := by dsimp [lam]; field_simp [hB_ne]; ring
      linarith
  have hExp_dom : Integrable (fun u : ℝ => airyKappa (u : ℂ) * Real.exp (y.re * u)) := by
    have hk_cont : Continuous (fun u : ℝ => airyKappa (u : ℂ)) := by
      have : (fun u : ℝ => airyKappa (u : ℂ)) = fun u => airyKer u u := funext fun u => by
        rw [← norm_airyHalf_sq, ← airyHalfC_ofReal, norm_airyHalfC_sq]
      rw [this]; exact continuous_airyKer_diag
    have hc : Continuous (fun u : ℝ => airyKappa (u : ℂ) * Real.exp (y.re * u)) :=
      hk_cont.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hk_le : ∀ u : ℝ, airyKappa (u : ℂ) ≤ 23 * (1 + |u|) * airyEnv (u : ℂ) := fun u => by
      have hk := airyKappa_le' (u : ℂ); rwa [Complex.norm_real, Real.norm_eq_abs] at hk
    have h_neg : IntegrableOn (fun u : ℝ => airyKappa (u : ℂ) * Real.exp (y.re * u)) (Iio (0 : ℝ)) := by
      have himg : Neg.neg '' Ioi (0 : ℝ) = Iio (0 : ℝ) := by
        ext x; simp only [mem_image, mem_Ioi, mem_Iio]; exact ⟨fun ⟨t, _, h⟩ => h ▸ by linarith, fun hx => ⟨-x, by linarith, by ring⟩⟩
      have hi_base : IntegrableOn (fun t : ℝ => 23 * ((1 + t) ^ 1 * Real.exp (-y.re * t))) (Ioi (0 : ℝ)) :=
        (airyPws_integrableOn_pow_mul_exp 1 hy).const_mul 23
      have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
        (f := Neg.neg) (f' := fun _ => -1) (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt)
        neg_injective.injOn (fun u : ℝ => 23 * ((1 + |u|) * Real.exp (y.re * u)))).mpr
        (hi_base.congr_fun (fun t ht => by simp only [smul_eq_mul, abs_neg, abs_one, one_mul, abs_of_pos ht, pow_one]; ring_nf) measurableSet_Ioi)
      rw [himg] at hi
      refine hi.mono' hc.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Iio] with u (hu : u < 0)
      rw [Real.norm_of_nonneg (mul_nonneg (airyKappa_nonneg _) (Real.exp_pos _).le)]
      calc _ ≤ 23 * (1 + |u|) * airyEnv (u : ℂ) * Real.exp (y.re * u) := mul_le_mul_of_nonneg_right (hk_le u) (Real.exp_pos _).le
        _ = 23 * ((1 + |u|) * Real.exp (y.re * u)) := by rw [airyEnv_ofReal_neg hu]; ring
    have h_pos : IntegrableOn (fun u : ℝ => airyKappa (u : ℂ) * Real.exp (y.re * u)) (Ici (0 : ℝ)) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      refine ((airyPws_integrableOn_pow_mul_exp 1 (by norm_num : (0 : ℝ) < 2 / 3)).const_mul
        (23 * Real.exp (y.re ^ 3 / 3 + 2 / 3))).mono' hc.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
      have he := exp_mul_airyEnv_le hy.le hu.le
      rw [Real.norm_of_nonneg (mul_nonneg (airyKappa_nonneg _) (Real.exp_pos _).le)]
      calc _ ≤ (23 * (1 + |u|) * airyEnv (u : ℂ)) * Real.exp (y.re * u) := mul_le_mul_of_nonneg_right (hk_le u) (Real.exp_pos _).le
        _ = 23 * (1 + u) * (Real.exp (y.re * u) * airyEnv (u : ℂ)) := by rw [abs_of_pos hu]; ring
        _ ≤ 23 * (1 + u) * (Real.exp (y.re ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u)) := by gcongr
        _ = 23 * Real.exp (y.re ^ 3 / 3 + 2 / 3) * ((1 + u) ^ 1 * Real.exp (-(2 / 3) * u)) := by ring
    rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union]; exact ⟨h_neg, h_pos⟩
  have hG_int : Integrable G (volume.prod (ν.prod ν)) := by
    rw [integrable_prod_iff hG_meas.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun u => (((hu_int u).ofReal.mul_const _).mul_prod (hu_int u).ofReal).congr
        (Eventually.of_forall fun p => by dsimp [G]; ring), ?_⟩
    have hnorm_eq : ∀ u : ℝ, ∫ p : ℝ × ℝ, ‖G (u, p)‖ ∂(ν.prod ν) =
        (∫ t : ℝ, |airyAi (u + t) * dirichletV b t| ∂ν) ^ 2 * Real.exp (y.re * u) := fun u => by
      simp_rw [show ∀ p : ℝ × ℝ, ‖G (u, p)‖ = (|airyAi (u + p.1) * dirichletV b p.1| * Real.exp (y.re * u)) *
        |airyAi (u + p.2) * dirichletV b p.2| from fun p => by
        dsimp [G]; rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, Complex.norm_exp]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring]
      rw [integral_prod_mul (f := fun t => |airyAi (u + t) * dirichletV b t| * Real.exp (y.re * u))
        (g := fun s => |airyAi (u + s) * dirichletV b s|), integral_mul_const]; ring
    refine (hExp_dom.const_mul (∑' n : ℕ, b n ^ 2)).mono' hG_meas.aestronglyMeasurable.norm.integral_prod_right' (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hnorm_eq u]
    have hcs_u := hcs u; rw [(dirichletV_parseval hb).1] at hcs_u
    calc _ ≤ (airyKappa (u : ℂ) * ∑' n : ℕ, b n ^ 2) * Real.exp (y.re * u) := mul_le_mul_of_nonneg_right hcs_u (Real.exp_pos _).le
      _ = (∑' n : ℕ, b n ^ 2) * (airyKappa (u : ℂ) * Real.exp (y.re * u)) := by ring
  have hL : ∫ u : ℝ, (∫ p : ℝ × ℝ, G (u, p) ∂(ν.prod ν)) = ∫ u : ℝ, (cardinalPb b u : ℂ) * Complex.exp (y * (u : ℂ)) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp_rw [show ∀ p : ℝ × ℝ, G (u, p) = (((airyAi (u + p.1) * dirichletV b p.1 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) *
      ((airyAi (u + p.2) * dirichletV b p.2 : ℝ) : ℂ) from fun p => by dsimp [G]; ring]
    rw [integral_prod_mul (f := fun t => ((airyAi (u + t) * dirichletV b t : ℝ) : ℂ) * Complex.exp (y * (u : ℂ)))
      (g := fun s => ((airyAi (u + s) * dirichletV b s : ℝ) : ℂ)), integral_mul_const,
      show ∫ t : ℝ, ((airyAi (u + t) * dirichletV b t : ℝ) : ℂ) ∂ν = (cardinalHb b u : ℂ) from by
        rw [integral_complex_ofReal, cardinalHb_eq_reproducing hb u]]
    unfold cardinalPb; push_cast; ring
  have hR : ∫ p : ℝ × ℝ, (∫ u : ℝ, G (u, p)) ∂(ν.prod ν) =
      ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) * Complex.exp (y ^ 3 / 12) *
        ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
            Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) := by
    have h_inner : ∀ p : ℝ × ℝ, ∫ u : ℝ, G (u, p) = ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) * Complex.exp (y ^ 3 / 12) *
        (((dirichletV b p.1 * dirichletV b p.2 : ℝ) : ℂ) *
          Complex.exp (-y * ((p.1 + p.2 : ℝ) : ℂ) / 2 - ((p.1 - p.2 : ℝ) : ℂ) ^ 2 / (4 * y))) := fun p => by
      simp_rw [show ∀ u : ℝ, G (u, p) = ((dirichletV b p.1 * dirichletV b p.2 : ℝ) : ℂ) *
        ((airyAi (u + p.1) : ℂ) * (airyAi (u + p.2) : ℂ) * Complex.exp (y * (u : ℂ))) from fun u => by dsimp [G]; push_cast; ring,
        integral_const_mul, (airy_pair_laplace_eq p.1 p.2 hy).2,
        show Complex.exp (y ^ 3 / 12 - y * ((p.1 + p.2 : ℝ) : ℂ) / 2 - ((p.1 - p.2 : ℝ) : ℂ) ^ 2 / (4 * y)) =
          Complex.exp (y ^ 3 / 12) * Complex.exp (-y * ((p.1 + p.2 : ℝ) : ℂ) / 2 - ((p.1 - p.2 : ℝ) : ℂ) ^ 2 / (4 * y)) by
          rw [← Complex.exp_add]; congr 1; ring]; ring
    simp_rw [h_inner]; rw [integral_const_mul, integral_prod _ (airySquare_gaussian_kernel_integrable hb hy)]
  have hswap := integral_integral_swap (f := fun u p => G (u, p)) hG_int
  rw [hL, hR] at hswap
  unfold airyTwistedLaplaceC; rw [hswap]
  have he : Complex.exp (-(y ^ 3) / 12) * Complex.exp (y ^ 3 / 12) = 1 := by
    rw [← Complex.exp_add, show -(y ^ 3) / 12 + y ^ 3 / 12 = 0 by ring, Complex.exp_zero]
  linear_combination ((ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
    ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
      Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))) * he

/-- Real-argument version of `(ceo:O11n.2)` in terms of `airyTwistedLaplace`. -/
theorem airySquare_gaussian_transform_real {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2)) {y : ℝ} (hy : 0 < y) :
    (airyTwistedLaplace (cardinalPb b) y : ℂ) =
      (ceK : ℂ) * ((4 * (π : ℂ) * (y : ℂ)) ^ (-(1 / 2 : ℂ))) *
        ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
          Complex.exp (-(y : ℂ) * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * (y : ℂ))) := by
  rw [← airyTwistedLaplaceC_ofReal]; exact airySquare_gaussian_transform hb (by simpa using hy)

/-- `airyFtilde` form of `(ceo:O11n.2)`: `F̃_{P_b}(i y) = P̃_b(i y)`. -/
theorem airyFtilde_cardinalPbC_eq {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2)) {y : ℂ} (hy : 0 < y.re) :
    airyFtilde (cardinalPbC b) (Complex.I * y) =
      (ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ))) *
        ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
          Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) := by
  have hpack := cardinal_series_of_sq_hasSum hb.hasSum
  have hf : ∀ u : ℝ, cardinalPbC b (u : ℂ) = (cardinalPb b u : ℂ) := fun u => by
    unfold cardinalPbC cardinalPb cardinalHbC cardinalHb
    rw [(hpack.2.2.2.1 (u : ℂ)).tsum_eq, (hpack.2.2.2.2.1 u).2, (hpack.2.2.2.2.1 u).1.tsum_eq]; push_cast; rfl
  rw [← airyTwistedLaplaceC_eq_airyFtilde (cardinalPb b) hf y]; exact airySquare_gaussian_transform hb hy

/-! ### Part 4: Uniform vertical-line bound `(ceo:O11n.11)` (`j = 0`) -/

/-- **Uniform line bound (`ce_o1_route.tex` `(ceo:O11n.11)`, `j = 0`):**
for `b ∈ ℓ²` with `|v_b(t)| ≤ M` a.e. on `(0, ∞)`, `x > 0`, `τ : ℝ`, and `y = c_s x (1 - i τ)`,
`‖P̃_b(i y)‖ ≤ (2 k c_s^{-5/2} / √π) M² x^{-5/2} (1 + τ²)^{-1/4}`. -/
theorem airySquare_uniform_line_bound {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2))
    {M : ℝ} (hM : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |dirichletV b t| ≤ M)
    {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    let y : ℂ := ((ceCs * x : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ))
    ‖airyTwistedLaplaceC (cardinalPb b) y‖ ≤
      (2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π) * M ^ 2 * x ^ (-(5 / 2 : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  intro y
  let ν := volume.restrict (Ioi (0 : ℝ))
  have : (ae ν).NeBot := ae_neBot.2 fun h => by have := congrArg (· (Ioi 0)) h; simp [ν, Measure.restrict_apply measurableSet_Ioi] at this
  have hM0 : 0 ≤ M := by obtain ⟨t, ht⟩ := hM.exists; exact (abs_nonneg _).trans ht
  have hy_re : y.re = ceCs * x := by simp [y, Complex.mul_re]
  have hy_pos : 0 < y.re := by rw [hy_re]; exact mul_pos ceCs_pos hx
  rw [airySquare_gaussian_transform hb hy_pos]
  have hnorm_y : ‖y‖ = ceCs * x * √(1 + τ ^ 2) := by
    have h1τ : ‖1 - Complex.I * (τ : ℂ)‖ = √(1 + τ ^ 2) := by rw [Complex.norm_def, Complex.normSq_apply]; simp [sq]
    dsimp [y]; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos ceCs_pos hx), h1τ]
  have hpref : ‖(ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)))‖ =
      (ceK / √(4 * π * ceCs)) * x ^ (-(1 / 2 : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
    have hcsx : 0 < 4 * π * ceCs := mul_pos (by positivity) ceCs_pos
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceK_pos,
      show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real,
      norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, hnorm_y,
      show (4 : ℝ) * π * (ceCs * x * √(1 + τ ^ 2)) = (4 * π * ceCs) * x * √(1 + τ ^ 2) by ring,
      Real.mul_rpow (mul_pos hcsx hx).le (Real.sqrt_nonneg _), Real.mul_rpow hcsx.le hx.le,
      Real.sqrt_eq_rpow (1 + τ ^ 2), ← Real.rpow_mul (by positivity : 0 ≤ 1 + τ ^ 2),
      show (1 / 2 : ℝ) * -(1 / 2 : ℝ) = -(1 / 4 : ℝ) by norm_num, Real.rpow_neg hcsx.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]; ring
  have ha_neg : -(ceCs * x / 2) < 0 := by linarith [mul_pos ceCs_pos hx]
  have hint_exp : Integrable (fun u : ℝ => Real.exp (-(ceCs * x / 2) * u)) ν := integrableOn_exp_mul_Ioi ha_neg 0
  have hint_exp_val : ∫ u in Ioi (0 : ℝ), Real.exp (-(ceCs * x / 2) * u) = 2 / (ceCs * x) := by
    rw [integral_exp_mul_Ioi ha_neg 0]; simp
  have hexp_bd : ∀ t s : ℝ, ‖Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))‖ ≤
      Real.exp (-(ceCs * x / 2) * t) * Real.exp (-(ceCs * x / 2) * s) := fun t s =>
    (airySquare_gaussian_kernel_exp_le hy_pos t s).trans_eq (by rw [hy_re])
  have hinner_bd : ∀ᵐ t ∂ν, ‖∫ s : ℝ, ((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
      Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) ∂ν‖ ≤
      M ^ 2 * (2 / (ceCs * x)) * Real.exp (-(ceCs * x / 2) * t) := by
    filter_upwards [hM] with t htM
    calc _ ≤ ∫ s : ℝ, ‖((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
          Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ s : ℝ, M ^ 2 * Real.exp (-(ceCs * x / 2) * t) * Real.exp (-(ceCs * x / 2) * s) ∂ν := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hint_exp.const_mul _) ?_
          filter_upwards [hM] with s hsM
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
          calc _ ≤ (M * M) * (Real.exp (-(ceCs * x / 2) * t) * Real.exp (-(ceCs * x / 2) * s)) :=
                mul_le_mul (mul_le_mul htM hsM (abs_nonneg _) hM0) (hexp_bd t s) (norm_nonneg _) (by positivity)
            _ = _ := by ring
      _ = M ^ 2 * (2 / (ceCs * x)) * Real.exp (-(ceCs * x / 2) * t) := by rw [integral_const_mul, hint_exp_val]; ring
  have hdouble_bd : ‖∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
      Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))‖ ≤ 4 * M ^ 2 / ceCs ^ 2 * x ^ (-2 : ℝ) := by
    calc _ ≤ ∫ t : ℝ, ‖∫ s : ℝ, ((dirichletV b t * dirichletV b s : ℝ) : ℂ) *
          Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y)) ∂ν‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, M ^ 2 * (2 / (ceCs * x)) * Real.exp (-(ceCs * x / 2) * t) ∂ν :=
          integral_mono_ae (airySquare_gaussian_kernel_integrable hb hy_pos).integral_prod_left.norm (hint_exp.const_mul _) hinner_bd
      _ = M ^ 2 * (2 / (ceCs * x)) * (2 / (ceCs * x)) := by rw [integral_const_mul, hint_exp_val]
      _ = 4 * M ^ 2 / ceCs ^ 2 * x ^ (-2 : ℝ) := by
          rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hx.le, Real.rpow_natCast]; field_simp [ceCs_pos.ne', hx.ne']; ring
  have hsqrt_4pi : √(4 * π * ceCs) = 2 * √π * √ceCs := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * π), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show √(4 : ℝ) = 2 by norm_num]
  have hcs_rpow : ceCs ^ (-(5 / 2 : ℝ)) = (√ceCs)⁻¹ * (ceCs ^ 2)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ceCs_pos.le, ← Real.rpow_natCast ceCs 2, ← Real.rpow_neg ceCs_pos.le, ← Real.rpow_add ceCs_pos]; norm_num
  have hx_rpow : x ^ (-(1 / 2 : ℝ)) * x ^ (-2 : ℝ) = x ^ (-(5 / 2 : ℝ)) := by rw [← Real.rpow_add hx]; norm_num
  calc _ = ‖(ceK : ℂ) * ((4 * (π : ℂ) * y) ^ (-(1 / 2 : ℂ)))‖ * ‖∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        ((dirichletV b t * dirichletV b s : ℝ) : ℂ) * Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))‖ := norm_mul _ _
    _ ≤ ((ceK / √(4 * π * ceCs)) * x ^ (-(1 / 2 : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ))) * (4 * M ^ 2 / ceCs ^ 2 * x ^ (-2 : ℝ)) := by
        rw [hpref]; exact mul_le_mul_of_nonneg_left hdouble_bd (hpref ▸ norm_nonneg _)
    _ = (2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π) * M ^ 2 * x ^ (-(5 / 2 : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
        rw [hsqrt_4pi, hcs_rpow, ← hx_rpow]
        field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne', (Real.sqrt_pos.mpr ceCs_pos).ne', ceCs_pos.ne']; ring

/-- Pointwise-bounded variant of `airySquare_uniform_line_bound` (`∀ t ≥ 0, |v_b(t)| ≤ M`). -/
theorem airySquare_uniform_line_bound_of_forall {b : ℕ → ℝ} (hb : Summable (fun n : ℕ => b n ^ 2))
    {M : ℝ} (hM : ∀ t : ℝ, 0 ≤ t → |dirichletV b t| ≤ M) {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    let y : ℂ := ((ceCs * x : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ))
    ‖airyTwistedLaplaceC (cardinalPb b) y‖ ≤
      (2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π) * M ^ 2 * x ^ (-(5 / 2 : ℝ)) * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) :=
  airySquare_uniform_line_bound hb ((ae_restrict_mem measurableSet_Ioi).mono fun _ ht => hM _ ht.le) hx τ

/-! ### Axiom verification -/

/-- info: 'FormalResearch.CohnElkies.fracMuDensity_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracMuDensity_pos
/-- info: 'FormalResearch.CohnElkies.fracMuDensity_integral_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracMuDensity_integral_one
/-- info: 'FormalResearch.CohnElkies.fracMu_stieltjes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracMu_stieltjes_eq
/-- info: 'FormalResearch.CohnElkies.fracZp_re_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracZp_re_eq
/-- info: 'FormalResearch.CohnElkies.fracZp_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracZp_norm_sq_le
/-- info: 'FormalResearch.CohnElkies.fracZp_norm_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracZp_norm_lt_one
/-- info: 'FormalResearch.CohnElkies.fracZp_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracZp_tendsto_zero
/-- info: 'FormalResearch.CohnElkies.fracGp_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracGp_re_pos
/-- info: 'FormalResearch.CohnElkies.fracGp_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracGp_ne_zero
/-- info: 'FormalResearch.CohnElkies.fracBp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracBp_zero
/-- info: 'FormalResearch.CohnElkies.fracBp_nonneg_and_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracBp_nonneg_and_lt_one
/-- info: 'FormalResearch.CohnElkies.fracBp_tendsto_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.fracBp_tendsto_one
/-- info: 'FormalResearch.CohnElkies.dirichletV_L2_convergence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_L2_convergence
/-- info: 'FormalResearch.CohnElkies.dirichletV_eq_tsum_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_eq_tsum_ae
/-- info: 'FormalResearch.CohnElkies.dirichletV_parseval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.dirichletV_parseval
/-- info: 'FormalResearch.CohnElkies.cardinalHbC_eq_reproducing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.cardinalHbC_eq_reproducing
/-- info: 'FormalResearch.CohnElkies.cardinalHb_eq_reproducing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.cardinalHb_eq_reproducing
/-- info: 'FormalResearch.CohnElkies.airy_pair_laplace_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airy_pair_laplace_eq
/-- info: 'FormalResearch.CohnElkies.airySquare_gaussian_transform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airySquare_gaussian_transform
/-- info: 'FormalResearch.CohnElkies.airySquare_gaussian_transform_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airySquare_gaussian_transform_real
/-- info: 'FormalResearch.CohnElkies.airyFtilde_cardinalPbC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airyFtilde_cardinalPbC_eq
/-- info: 'FormalResearch.CohnElkies.airySquare_uniform_line_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airySquare_uniform_line_bound
/-- info: 'FormalResearch.CohnElkies.airySquare_uniform_line_bound_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.airySquare_uniform_line_bound_of_forall
end FormalResearch.CohnElkies


