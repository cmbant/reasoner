module

public import FormalResearch.SignUncertainty.CtOuterPart3
public import FormalResearch.SignUncertainty.CtOuter
public import FormalResearch.SignUncertainty.CtOuterThird

/-!
# `ct:outer` (3): the case `ε = +1` and the global bounds

**Proved.**  `θ_+ = θ_- - ψ` with `ψ(τ) = 2 arctan tanh(πτ/2)`, `π/2 - ψ(τ) = 2 arctan e^{-πτ}` and
`|ψ^{(n)}(τ)| ≤ K_n e^{-π|τ|}` (`n ≥ 1`, `|τ| ≥ 1`).  Together with the bounds for `θ_-` this gives
the large-`τ` asymptotics and the derivative bounds of `ct:outer` (3).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty.CtOuter

lemma norm_cosh_ge (w : ℂ) : Real.sinh |w.re| ≤ ‖Complex.cosh w‖ := by
  have h := norm_sinh_ge (w + Complex.I * (π / 2 : ℝ))
  have e : Complex.sinh (w + Complex.I * (π / 2 : ℝ)) = Complex.cosh w * Complex.I := by
    have e1 : Complex.I * ((π / 2 : ℝ) : ℂ) = ((π / 2 : ℝ) : ℂ) * Complex.I := mul_comm _ _
    rw [e1, Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I]
    have hc : Complex.cos ((π / 2 : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_cos, Real.cos_pi_div_two]; simp
    have hs : Complex.sin ((π / 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_sin, Real.sin_pi_div_two]; simp
    rw [hc, hs]; ring
  rw [e, norm_mul, Complex.norm_I, mul_one] at h
  simpa using h

/-- `‖π / cosh(πz)‖ ≤ 4π e^{-π Re z}` for `Re z ≥ 1/2`. -/
lemma norm_sech_le {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖(π : ℂ) / Complex.cosh (π * z)‖ ≤ 4 * π * Real.exp (-π * z.re) := by
  have h := norm_cosh_ge ((π : ℂ) * z)
  have hre : ((π : ℂ) * z).re = π * z.re := by simp [Complex.mul_re]
  rw [hre, abs_of_nonneg (by positivity)] at h
  have h1 : 1 ≤ π * z.re := by nlinarith only [Real.pi_gt_three, hz]
  have h2 := exp_div_four_le_sinh h1
  have hpos : 0 < Real.exp (π * z.re) / 4 := by positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hc : Real.exp (π * z.re) / 4 ≤ ‖Complex.cosh (π * z)‖ := h2.trans h
  rw [div_le_iff₀ (hpos.trans_le hc)]
  calc π = 4 * π * Real.exp (-π * z.re) * (Real.exp (π * z.re) / 4) := by
        have : Real.exp (-π * z.re) * Real.exp (π * z.re) = 1 := by rw [← Real.exp_add]; simp
        calc π = π * (Real.exp (-π * z.re) * Real.exp (π * z.re)) := by rw [this, mul_one]
          _ = _ := by ring
    _ ≤ 4 * π * Real.exp (-π * z.re) * ‖Complex.cosh (π * z)‖ :=
        mul_le_mul_of_nonneg_left hc (by positivity)

lemma cosh_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.cosh (π * z) ≠ 0 := by
  intro h0
  have := norm_cosh_ge ((π : ℂ) * z)
  have hre : ((π : ℂ) * z).re = π * z.re := by simp [Complex.mul_re]
  rw [hre, abs_of_nonneg (by positivity), h0, norm_zero] at this
  have : 0 < Real.sinh (π * z.re) := Real.sinh_pos_iff.mpr (by positivity)
  linarith

/-- Cauchy estimates for `sech`: `|d^n/dτ^n (π / cosh(πτ))| ≤ K_n e^{-πτ}` for `τ ≥ 1`. -/
theorem sech_deriv_bound (n : ℕ) :
    ∃ K : ℝ, ∀ τ : ℝ, 1 ≤ τ → |iteratedDeriv n (fun x : ℝ => π / Real.cosh (π * x)) τ| ≤ K * Real.exp (-π * τ) := by
  refine ⟨n.factorial * (4 * π * Real.exp (π / 2)) / (1 / 2) ^ n, fun τ hτ => ?_⟩
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (π : ℂ) / Complex.cosh (π * z)) {z : ℂ | 0 < z.re} := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_const _).div (by fun_prop) (cosh_ne_zero_of_re_pos hz)
  have hsub : closedBall (τ : ℂ) (1 / 2) ⊆ {z : ℂ | 0 < z.re} := by
    intro z hz
    have hd : ‖z - τ‖ ≤ 1 / 2 := by simpa [mem_closedBall, dist_eq_norm] using hz
    have := Complex.abs_re_le_norm (z - τ)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    show 0 < z.re
    linarith [(abs_le.mp (this.trans hd)).1]
  have hM : ∀ z ∈ sphere (τ : ℂ) (1 / 2), ‖(π : ℂ) / Complex.cosh (π * z)‖ ≤
      4 * π * Real.exp (π / 2) * Real.exp (-π * τ) := by
    intro z hz
    have hd : ‖z - τ‖ = 1 / 2 := by simpa [dist_eq_norm] using hz
    have := Complex.abs_re_le_norm (z - τ)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    have hre : τ - 1 / 2 ≤ z.re := by linarith [(abs_le.mp (this.trans hd.le)).1]
    refine (norm_sech_le (by linarith)).trans ?_
    have : Real.exp (-π * z.re) ≤ Real.exp (π / 2) * Real.exp (-π * τ) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [Real.pi_pos, hre]
    calc 4 * π * Real.exp (-π * z.re) ≤ 4 * π * (Real.exp (π / 2) * Real.exp (-π * τ)) := by gcongr
      _ = _ := by ring
  have h := cauchy_real (f := fun x : ℝ => π / Real.cosh (π * x)) hU hdiff
    (fun t _ => by
      simp only [Complex.ofReal_div, Complex.ofReal_cosh, Complex.ofReal_mul])
    (by norm_num : (0 : ℝ) < 1 / 2) hsub hM n
  refine h.trans (le_of_eq ?_)
  ring

/-- `ψ(τ) = 2 arctan tanh(πτ/2)`. -/
noncomputable def psiF (τ : ℝ) : ℝ := 2 * Real.arctan (Real.tanh (π * τ / 2))

lemma deriv_psiF : deriv psiF = fun τ => π / Real.cosh (π * τ) := funext fun τ => (hasDerivAt_psi τ).deriv

lemma psiF_neg (x : ℝ) : psiF (-x) = -psiF x := by
  unfold psiF
  rw [show π * -x / 2 = -(π * x / 2) by ring, Real.tanh_neg, Real.arctan_neg]; ring

/-- `ψ = θ_- - θ_+`, hence `C^∞`. -/
lemma psiF_eq : psiF = fun τ => outerTheta (-1) τ - outerTheta 1 τ := by
  funext τ; rw [outerTheta_plus]; unfold psiF; ring

lemma contDiff_psiF (m : ℕ) : ContDiff ℝ m psiF := by
  rw [psiF_eq]
  exact ((contDiff_outerTheta (-1)).of_le le_top).sub ((contDiff_outerTheta 1).of_le le_top)

theorem psiF_deriv_bound {n : ℕ} (hn : 0 < n) :
    ∃ K : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |iteratedDeriv n psiF τ| ≤ K * Real.exp (-π * |τ|) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ := sech_deriv_bound m
  refine ⟨K, fun τ hτ => ?_⟩
  have hev : ∀ x : ℝ, iteratedDeriv (m + 1) psiF x = iteratedDeriv m (fun x : ℝ => π / Real.cosh (π * x)) x := by
    intro x; rw [iteratedDeriv_succ', deriv_psiF]
  rcases le_abs'.mp hτ with h1 | h1
  · have hn := abs_iteratedDeriv_neg (f := psiF) (c := -1) (by simp) (fun x => by rw [psiF_neg]; ring)
      (fun m => contDiff_psiF m) (m + 1) (-τ)
    rw [neg_neg] at hn
    rw [hn, hev, abs_of_nonpos (by linarith : τ ≤ 0)]
    exact hK (-τ) (by linarith)
  · rw [hev, abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ)]
    exact hK τ h1

/-- `π/2 - ψ(τ) = 2 arctan e^{-πτ}` for `τ ≥ 0`; hence `0 ≤ π/2 - ψ(τ) ≤ 2 e^{-πτ}`. -/
lemma psiF_asymp {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ π / 2 - psiF τ ∧ π / 2 - psiF τ ≤ 2 * Real.exp (-π * τ) := by
  set w : ℝ := Real.exp (-π * τ) with hw
  have hw0 : 0 < w := Real.exp_pos _
  have hw1 : w ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [Real.pi_pos, hτ])
  set a : ℝ := Real.exp (-(π * τ / 2)) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have haw : w = a ^ 2 := by
    rw [hw, ha, sq, ← Real.exp_add]; congr 1; ring
  have hx : Real.exp (π * τ / 2) = a⁻¹ := by
    rw [ha, Real.exp_neg, inv_inv]
  have hu : Real.tanh (π * τ / 2) = (1 - w) / (1 + w) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, hx, inv_inv, haw]
    have hne : a ≠ 0 := ha0.ne'
    field_simp
  have hlt : (1 - w) / (1 + w) * w < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one (by linarith)]
    nlinarith only [hw0, hw1]
  have hadd := Real.arctan_add hlt
  have h1 : ((1 - w) / (1 + w) + w) / (1 - (1 - w) / (1 + w) * w) = 1 := by
    have : (1 + w) ≠ 0 := by linarith
    have h2 : (1 - (1 - w) / (1 + w) * w) = (1 + w ^ 2) / (1 + w) := by field_simp; ring
    have h3 : ((1 - w) / (1 + w) + w) = (1 + w ^ 2) / (1 + w) := by field_simp; ring
    rw [h2, h3]; exact div_self (by positivity)
  rw [h1, Real.arctan_one] at hadd
  have hpsi : psiF τ = π / 2 - 2 * Real.arctan w := by
    unfold psiF; rw [hu]; linarith
  rw [hpsi]
  have hA0 : 0 ≤ Real.arctan w := Real.arctan_nonneg.mpr hw0.le
  have hA1 : Real.arctan w ≤ w := Real.arctan_le_self hw0.le
  constructor <;> linarith

lemma sq_le_two_mul {τ : ℝ} : (1 + |τ|) ^ 2 ≤ 2 * (1 + τ ^ 2) := by
  nlinarith only [sq_nonneg (|τ| - 1), sq_abs τ]

lemma outerTheta_one_eq : outerTheta 1 = fun τ => outerTheta (-1) τ - psiF τ := by
  funext τ; rw [outerTheta_plus]; rfl

/-- **`ct:outer` (3), asymptotics of `θ_-`** for `τ ≥ 1`. -/
theorem theta_neg_asymp_all : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ τ →
    |outerTheta (-1) τ + π / 2| ≤ C * ((1 + τ ^ 2) * Real.exp (-π * τ)) := by
  obtain ⟨C0, hC0⟩ := theta_neg_asymp
  have hcont : Continuous fun τ => outerTheta (-1) τ + π / 2 :=
    ((contDiff_outerTheta (-1)).continuous).add continuous_const
  obtain ⟨C, hC⟩ := ext_bound hcont (K := C0) (fun τ hτ => hC0 τ hτ)
  refine ⟨2 * |C|, fun τ hτ => ?_⟩
  have h := hC τ hτ
  have e := (sq_le_two_mul (τ := τ))
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ τ)] at e
  have hE := (Real.exp_pos (-π * τ)).le
  calc _ ≤ C * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := h
    _ ≤ |C| * ((1 + τ) ^ 2 * Real.exp (-π * τ)) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((2 * (1 + τ ^ 2)) * Real.exp (-π * τ)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        exact mul_le_mul_of_nonneg_right e hE
    _ = _ := by ring

/-- **`ct:outer` (3), asymptotics of `θ_+`** for `τ ≥ 1`. -/
theorem theta_pos_asymp_all : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ τ →
    |outerTheta 1 τ + π| ≤ C * ((1 + τ ^ 2) * Real.exp (-π * τ)) := by
  obtain ⟨C, hC⟩ := theta_neg_asymp_all
  refine ⟨C + 2, fun τ hτ => ?_⟩
  have h := hC τ hτ
  obtain ⟨h1, h2⟩ := psiF_asymp (by linarith : (0 : ℝ) ≤ τ)
  have hE := (Real.exp_pos (-π * τ)).le
  have e1 : Real.exp (-π * τ) ≤ (1 + τ ^ 2) * Real.exp (-π * τ) := by
    nlinarith only [sq_nonneg τ, hE]
  have : outerTheta 1 τ + π = (outerTheta (-1) τ + π / 2) + (π / 2 - psiF τ) := by
    rw [outerTheta_one_eq]; ring
  rw [this]
  calc _ ≤ |outerTheta (-1) τ + π / 2| + |π / 2 - psiF τ| := abs_add_le _ _
    _ ≤ C * ((1 + τ ^ 2) * Real.exp (-π * τ)) + 2 * Real.exp (-π * τ) := by
        rw [abs_of_nonneg h1]; exact add_le_add h h2
    _ ≤ C * ((1 + τ ^ 2) * Real.exp (-π * τ)) + 2 * ((1 + τ ^ 2) * Real.exp (-π * τ)) := by
        have := mul_le_mul_of_nonneg_left e1 (by norm_num : (0 : ℝ) ≤ 2)
        linarith only [this]
    _ = _ := by ring

/-- **`ct:outer` (3), exponential derivative bounds**: for `ε = ±1`, `j ≥ 1`,
`|θ_ε^{(j)}(τ)| ≤ C_j (1+τ²) e^{-π|τ|}` for `|τ| ≥ 1`. -/
theorem theta_deriv_exp {ε : ℝ} (hε : ε = -1 ∨ ε = 1) {n : ℕ} (hn : 0 < n) : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |iteratedDeriv n (outerTheta ε) τ| ≤ C * ((1 + τ ^ 2) * Real.exp (-π * |τ|)) := by
  obtain ⟨C, hC⟩ := theta_neg_deriv_bound hn
  have hC0 : ∀ τ : ℝ, 1 ≤ |τ| → |iteratedDeriv n (outerTheta (-1)) τ| ≤
      (2 * |C|) * ((1 + τ ^ 2) * Real.exp (-π * |τ|)) := by
    intro τ hτ
    have h := hC τ hτ
    have e := (sq_le_two_mul (τ := τ))
    have hE := (Real.exp_pos (-π * |τ|)).le
    calc _ ≤ C * ((1 + |τ|) ^ 2 * Real.exp (-π * |τ|)) := h
      _ ≤ |C| * ((1 + |τ|) ^ 2 * Real.exp (-π * |τ|)) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((2 * (1 + τ ^ 2)) * Real.exp (-π * |τ|)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          exact mul_le_mul_of_nonneg_right e hE
      _ = _ := by ring
  rcases hε with rfl | rfl
  · exact ⟨2 * |C|, hC0⟩
  · obtain ⟨K, hK⟩ := psiF_deriv_bound hn
    refine ⟨2 * |C| + |K|, fun τ hτ => ?_⟩
    have hθ : ContDiffAt ℝ (n : WithTop ℕ∞) (outerTheta (-1)) τ :=
      ((contDiff_outerTheta (-1)).of_le le_top).contDiffAt
    have hψ : ContDiffAt ℝ (n : WithTop ℕ∞) psiF τ := (contDiff_psiF n).contDiffAt
    have e : outerTheta 1 = (outerTheta (-1)) - psiF := outerTheta_one_eq
    rw [e, iteratedDeriv_sub hθ hψ]
    have hE := (Real.exp_pos (-π * |τ|)).le
    have e1 : Real.exp (-π * |τ|) ≤ (1 + τ ^ 2) * Real.exp (-π * |τ|) := by
      nlinarith only [sq_nonneg τ, hE]
    calc _ ≤ |iteratedDeriv n (outerTheta (-1)) τ| + |iteratedDeriv n psiF τ| := abs_sub _ _
      _ ≤ (2 * |C|) * ((1 + τ ^ 2) * Real.exp (-π * |τ|)) + K * Real.exp (-π * |τ|) :=
          add_le_add (hC0 τ hτ) (hK τ hτ)
      _ ≤ (2 * |C|) * ((1 + τ ^ 2) * Real.exp (-π * |τ|)) + |K| * ((1 + τ ^ 2) * Real.exp (-π * |τ|)) := by
          apply add_le_add le_rfl
          calc K * Real.exp (-π * |τ|) ≤ |K| * Real.exp (-π * |τ|) :=
                mul_le_mul_of_nonneg_right (le_abs_self K) hE
            _ ≤ _ := mul_le_mul_of_nonneg_left e1 (abs_nonneg K)
      _ = _ := by ring

lemma poly_exp_bdd (m : ℕ) : ∃ P : ℝ, ∀ x : ℝ, 0 ≤ x → (1 + x) ^ m * Real.exp (-π * x) ≤ P := by
  refine ⟨m.factorial * Real.exp 1, fun x hx => ?_⟩
  have h := Real.pow_div_factorial_le_exp (1 + x) (by linarith) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h2 : (1 + x) ^ m ≤ m.factorial * Real.exp (1 + x) := by
    rw [div_le_iff₀ hf] at h; linarith
  have h3 : Real.exp (1 + x) * Real.exp (-π * x) ≤ Real.exp 1 := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith only [Real.pi_gt_three, hx]
  calc (1 + x) ^ m * Real.exp (-π * x) ≤ (m.factorial * Real.exp (1 + x)) * Real.exp (-π * x) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = m.factorial * (Real.exp (1 + x) * Real.exp (-π * x)) := by ring
    _ ≤ m.factorial * Real.exp 1 := mul_le_mul_of_nonneg_left h3 hf.le

/-- **`ct:outer` (3), polynomial derivative bounds**: for `ε = ±1`, `j ≥ 1`,
`|θ_ε^{(j)}(τ)| ≤ C_j' (1+|τ|)^{-j-1}` for all `τ`. -/
theorem theta_deriv_poly {ε : ℝ} (hε : ε = -1 ∨ ε = 1) {n : ℕ} (hn : 0 < n) : ∃ C : ℝ, ∀ τ : ℝ,
    |iteratedDeriv n (outerTheta ε) τ| ≤ C / (1 + |τ|) ^ (n + 1) := by
  obtain ⟨C, hC⟩ := theta_deriv_exp hε hn
  obtain ⟨P, hP⟩ := poly_exp_bdd (n + 3)
  have hcd : ∀ m : ℕ, ContDiff ℝ m (outerTheta ε) := by
    rcases hε with rfl | rfl <;> exact fun m => (contDiff_outerTheta _).of_le le_top
  have hcont : Continuous (iteratedDeriv n (outerTheta ε)) := by
    rcases hε with rfl | rfl <;> exact (contDiff_outerTheta _).continuous_iteratedDeriv n le_top
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := iteratedDeriv n (outerTheta ε))
    (s := Icc (-1 : ℝ) 1) hcont.continuousOn
  refine ⟨|B| * 2 ^ (n + 1) + |C| * P, fun τ => ?_⟩
  have hpos : 0 < (1 + |τ|) ^ (n + 1) := by positivity
  rw [le_div_iff₀ hpos]
  by_cases h1 : 1 ≤ |τ|
  · have h := hC τ h1
    have hCa : C * ((1 + τ ^ 2) * Real.exp (-π * |τ|)) ≤ |C| * ((1 + τ ^ 2) * Real.exp (-π * |τ|)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have hq := hP |τ| (abs_nonneg τ)
    have e : (1 + τ ^ 2) * (1 + |τ|) ^ (n + 1) ≤ (1 + |τ|) ^ (n + 3) := by
      have : (1 + τ ^ 2) ≤ (1 + |τ|) ^ 2 := by nlinarith only [abs_nonneg τ, sq_abs τ]
      calc (1 + τ ^ 2) * (1 + |τ|) ^ (n + 1) ≤ (1 + |τ|) ^ 2 * (1 + |τ|) ^ (n + 1) :=
            mul_le_mul_of_nonneg_right this hpos.le
        _ = (1 + |τ|) ^ (n + 3) := by ring
    have hE := (Real.exp_pos (-π * |τ|)).le
    calc |iteratedDeriv n (outerTheta ε) τ| * (1 + |τ|) ^ (n + 1)
        ≤ (|C| * ((1 + τ ^ 2) * Real.exp (-π * |τ|))) * (1 + |τ|) ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (h.trans hCa) hpos.le
      _ = |C| * (((1 + τ ^ 2) * (1 + |τ|) ^ (n + 1)) * Real.exp (-π * |τ|)) := by ring
      _ ≤ |C| * ((1 + |τ|) ^ (n + 3) * Real.exp (-π * |τ|)) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
          exact mul_le_mul_of_nonneg_right e hE
      _ ≤ |C| * P := mul_le_mul_of_nonneg_left hq (abs_nonneg C)
      _ ≤ |B| * 2 ^ (n + 1) + |C| * P := by
          have : 0 ≤ |B| * 2 ^ (n + 1) := by positivity
          linarith only [this]
  · have ht : τ ∈ Icc (-1 : ℝ) 1 := abs_le.mp (not_le.mp h1).le
    have h := hB τ ht
    rw [Real.norm_eq_abs] at h
    have h2 : (1 + |τ|) ^ (n + 1) ≤ 2 ^ (n + 1) := by
      apply pow_le_pow_left₀ (by positivity); linarith [not_le.mp h1]
    have hCP : 0 ≤ |C| * P := by
      have := hP 0 le_rfl
      have hP0 : 0 ≤ P := by simpa using (le_trans (by positivity) this)
      positivity
    calc |iteratedDeriv n (outerTheta ε) τ| * (1 + |τ|) ^ (n + 1) ≤ |B| * 2 ^ (n + 1) :=
          mul_le_mul (h.trans (le_abs_self B)) h2 hpos.le (abs_nonneg B)
      _ ≤ _ := by linarith only [hCP]

/-- **`ct:outer` (3): large-`τ` asymptotics and derivative bounds** (`constant_terms_lower.tex`, `ct:outer`(3)).
As `τ → +∞`, `θ_-(τ) = -π/2 + O((1+τ²)e^{-πτ})` and `θ_+(τ) = -π + O((1+τ²)e^{-πτ})`; for every `j ≥ 1` and
`ε = ±1`, `|θ_ε^{(j)}(τ)| ≤ C_j (1+τ²) e^{-π|τ|}` for `|τ| ≥ 1` and `|θ_ε^{(j)}(τ)| ≤ C_j' (1+|τ|)^{-j-1}`
for all `τ`. -/
theorem ct_outer_part3 :
    (∃ C : ℝ, ∀ τ : ℝ, 1 ≤ τ →
      |outerTheta (-1) τ + π / 2| ≤ C * ((1 + τ ^ 2) * Real.exp (-π * τ)) ∧
      |outerTheta 1 τ + π| ≤ C * ((1 + τ ^ 2) * Real.exp (-π * τ))) ∧
    ∀ ε : ℝ, (ε = -1 ∨ ε = 1) → ∀ j : ℕ, 1 ≤ j →
      (∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
        |iteratedDeriv j (outerTheta ε) τ| ≤ C * ((1 + τ ^ 2) * Real.exp (-π * |τ|))) ∧
      (∃ C : ℝ, ∀ τ : ℝ, |iteratedDeriv j (outerTheta ε) τ| ≤ C / (1 + |τ|) ^ (j + 1)) := by
  refine ⟨?_, fun ε hε j hj => ⟨theta_deriv_exp hε hj, theta_deriv_poly hε hj⟩⟩
  obtain ⟨C1, h1⟩ := theta_neg_asymp_all
  obtain ⟨C2, h2⟩ := theta_pos_asymp_all
  refine ⟨max C1 C2, fun τ hτ => ⟨?_, ?_⟩⟩
  · exact (h1 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (h2 τ hτ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- info: 'FormalResearch.SignUncertainty.CtOuter.sech_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sech_deriv_bound

/-- info: 'FormalResearch.SignUncertainty.CtOuter.psiF_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psiF_asymp

/-- info: 'FormalResearch.SignUncertainty.CtOuter.ct_outer_part3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_part3

end FormalResearch.SignUncertainty.CtOuter
