module

public import FormalResearch.Special.LatticeBad

/-!
# Contour shift for `∫ w e^{±2πikτ₀}`

Source: `constants.tex`, proof of `lem:latticesum` (i): move the contour of
`J_k^± = ∫_{-X}^{X} φ e^{±2πikτ₀}` to `Im s = ±y₀`: since `±Im τ₀ ≥ m y` there,
`|e^{±2πikτ₀}| ≤ e^{-2πkmy}`, the horizontal side gives `(2C_w/κ) e^{-2πkmy₁}` and the vertical
sides `C_w e^{-κX} y₁` each.

`contour_shift_le` : `‖∫_{-X}^{X} w(u) exp(σ·2πik τ₀(u)) du‖ ≤ 2 C_w y₁ e^{-κX} + (2C_w/κ) e^{-2πkmy₁}`
for `σ = ±1`, `w` holomorphic on `|Re s| ≤ X, |Im s| ≤ y₁` with `|w| ≤ C_w e^{-κ|Re s|}`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

lemma integral_exp_neg_abs_le {κ : ℝ} (hκ : 0 < κ) {X : ℝ} (hX : 0 ≤ X) :
    ∫ x in (-X)..X, Real.exp (-κ * |x|) ≤ 2 / κ := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x => Real.exp (-κ * |x|)) volume a b := fun a b =>
    (Continuous.intervalIntegrable (by fun_prop) a b)
  have hsplit : ∫ x in (-X)..X, Real.exp (-κ * |x|) =
      (∫ x in (-X)..0, Real.exp (-κ * |x|)) + ∫ x in (0 : ℝ)..X, Real.exp (-κ * |x|) :=
    (integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have h1 : ∫ x in (0 : ℝ)..X, Real.exp (-κ * |x|) = (1 - Real.exp (-κ * X)) / κ := by
    have : ∫ x in (0 : ℝ)..X, Real.exp (-κ * |x|) = ∫ x in (0 : ℝ)..X, Real.exp (-κ * x) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [uIcc_of_le hX] at hx
      simp only [abs_of_nonneg hx.1]
    rw [this]
    have hd : ∀ x ∈ uIcc (0 : ℝ) X, HasDerivAt (fun x => -(Real.exp (-κ * x)) / κ)
        (Real.exp (-κ * x)) x := by
      intro x _
      have h2 : HasDerivAt (fun x => -(Real.exp (-κ * x)) / κ)
          ((-(Real.exp (-κ * x) * (-κ * 1))) / κ) x :=
        (((hasDerivAt_id x).const_mul (-κ)).exp.neg).div_const κ
      convert h2 using 1
      have := hκ.ne'
      field_simp
    rw [integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp; ring
  have h2 : ∫ x in (-X)..0, Real.exp (-κ * |x|) = (1 - Real.exp (-κ * X)) / κ := by
    have : ∫ x in (-X)..0, Real.exp (-κ * |x|) = ∫ x in (-X)..0, Real.exp (κ * x) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [uIcc_of_le (by linarith)] at hx
      simp only [abs_of_nonpos hx.2]; ring_nf
    rw [this]
    have hd : ∀ x ∈ uIcc (-X) (0 : ℝ), HasDerivAt (fun x => (Real.exp (κ * x)) / κ)
        (Real.exp (κ * x)) x := by
      intro x _
      have h2 : HasDerivAt (fun x => (Real.exp (κ * x)) / κ)
          (Real.exp (κ * x) * (κ * 1) / κ) x :=
        (((hasDerivAt_id x).const_mul κ).exp).div_const κ
      convert h2 using 1
      have := hκ.ne'
      field_simp
    rw [integral_eq_sub_of_hasDerivAt hd (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp; ring_nf
  rw [hsplit, h1, h2]
  have : 0 ≤ Real.exp (-κ * X) := (Real.exp_pos _).le
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ hκ.le
  linarith

namespace CalPhase

variable {τ0 : ℂ → ℂ} {X y0 m M K : ℝ}

/-- `σ Im τ₀(u + iσy) ≥ m y` for `σ = ±1`, `0 ≤ y ≤ y₀`. -/
lemma sigma_im_ge (h : CalPhase τ0 X y0 m M K) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {u y : ℝ}
    (hu : |u| ≤ X + 1) (hy0 : 0 ≤ y) (hy : y ≤ y0) :
    m * y ≤ σ * (τ0 (u + (σ * y : ℝ) * I)).im := by
  have hre := h.real u
  rcases hσ with rfl | rfl
  · have := h.im_ge hu (a := 0) (b := y) (by simp; exact h.hy0.le) (by rw [abs_of_nonneg hy0]; exact hy)
      hy0
    simp only [Complex.ofReal_zero, zero_mul, add_zero, hre, one_mul, sub_zero] at this ⊢
    exact this
  · have := h.im_ge hu (a := -y) (b := 0) (by rw [abs_neg, abs_of_nonneg hy0]; exact hy)
      (by simp; exact h.hy0.le) (by linarith)
    simp only [Complex.ofReal_zero, zero_mul, add_zero, hre, sub_zero, zero_sub] at this
    have e : ((-1 * y : ℝ) : ℂ) = ((-y : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    nlinarith

lemma norm_exp_le (h : CalPhase τ0 X y0 m M K) {σ k : ℝ} (hσ : σ = 1 ∨ σ = -1) (hk : 0 < k)
    {s : ℂ} (hs : |s.re| ≤ X + 1) {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ y0) (him : s.im = σ * y) :
    ‖Complex.exp (σ * (2 * Real.pi * I * k) * τ0 s)‖ ≤ Real.exp (-(2 * Real.pi * k * m * y)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hs' : s = (s.re : ℂ) + ((σ * y : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im s]
    rw [him]
  have := h.sigma_im_ge hσ hs hy0 hy
  rw [← hs'] at this
  have e : (σ * (2 * Real.pi * I * k) * τ0 s).re = -(σ * 2 * Real.pi * k * (τ0 s).im) := by
    have e0 : σ * (2 * Real.pi * I * k) * τ0 s = ((σ * 2 * Real.pi * k : ℝ) : ℂ) * (I * τ0 s) := by
      push_cast; ring
    rw [e0, Complex.re_ofReal_mul]
    simp
  rw [e]
  have hpk : 0 < Real.pi * k := mul_pos Real.pi_pos hk
  nlinarith

end CalPhase

/-- **Contour shift** for `J = ∫_{-X}^{X} w(u) e^{σ 2πik τ₀(u)} du`, `σ = ±1`. -/
theorem contour_shift_le {τ0 : ℂ → ℂ} {X y0 m M K : ℝ} (h : CalPhase τ0 X y0 m M K)
    {w : ℂ → ℂ} {Cw κ y1 k σ : ℝ} (hκ : 0 < κ) (hCw : 0 ≤ Cw) (hy1 : 0 < y1) (hy10 : y1 ≤ y0)
    (hk : 0 < k) (hσ : σ = 1 ∨ σ = -1)
    (hwd : DifferentiableOn ℂ w {s | |s.re| ≤ X ∧ |s.im| ≤ y1})
    (hwb : ∀ s : ℂ, |s.re| ≤ X → |s.im| ≤ y1 → ‖w s‖ ≤ Cw * Real.exp (-κ * |s.re|)) :
    ‖∫ x : ℝ in (-X)..X, w x * Complex.exp (σ * (2 * Real.pi * I * k) * τ0 x)‖ ≤
      2 * Cw * y1 * Real.exp (-κ * X) + 2 * Cw / κ * Real.exp (-(2 * Real.pi * k * m * y1)) := by
  have hX := h.hX
  set c : ℂ := σ * (2 * Real.pi * I * k) with hc
  set f : ℂ → ℂ := fun s => w s * Complex.exp (c * τ0 s) with hf
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  set R : Set ℂ := uIcc (-X) X ×ℂ uIcc 0 (σ * y1) with hR
  have hRsub : ∀ s ∈ R, |s.re| ≤ X ∧ |s.im| ≤ y1 := by
    intro s hs
    simp only [hR, reProdIm, mem_prod, mem_preimage] at hs
    obtain ⟨hre, him⟩ := hs
    have hre' : |s.re| ≤ X := by
      have : s.re ∈ uIcc (-X) X := hre
      rw [uIcc_of_le (by linarith)] at this; exact abs_le.mpr ⟨this.1, this.2⟩
    have him' : |s.im| ≤ y1 := by
      have : s.im ∈ uIcc 0 (σ * y1) := him
      rcases hσ with rfl | rfl
      · rw [uIcc_of_le (by linarith)] at this
        rw [abs_of_nonneg this.1]; simpa using this.2
      · rw [uIcc_of_ge (by linarith)] at this
        rw [abs_of_nonpos this.2]; linarith [this.1]
    exact ⟨hre', him'⟩
  have hdiff : DifferentiableOn ℂ f R := by
    refine (hwd.mono (fun s hs => hRsub s hs)).mul (fun s hs => ?_)
    obtain ⟨hre', him'⟩ := hRsub s hs
    have ht : DifferentiableAt ℂ τ0 s := h.diff s ⟨by linarith, him'.trans hy10⟩
    exact ((ht.const_mul c).cexp).differentiableWithinAt
  have hG := integral_boundary_rect_eq_zero_of_differentiableOn f ⟨-X, 0⟩ ⟨X, σ * y1⟩ hdiff
  simp only at hG
  have hexp1 : ∀ y' : ℝ, 0 ≤ y' → y' ≤ y1 → ∀ x : ℝ, |x| ≤ X →
      ‖f (x + (σ * y' : ℝ) * I)‖ ≤ Cw * Real.exp (-κ * |x|) * Real.exp (-(2 * Real.pi * k * m * y')) := by
    intro y' hy'0 hy'1 x hx
    have hs : (((x : ℂ) + ((σ * y' : ℝ) : ℂ) * I)).re = x := by simp
    have hs2 : (((x : ℂ) + ((σ * y' : ℝ) : ℂ) * I)).im = σ * y' := by simp
    have hw := hwb ((x : ℂ) + ((σ * y' : ℝ) : ℂ) * I) (by rw [hs]; exact hx)
      (by rw [hs2, abs_mul, hσ1, one_mul, abs_of_nonneg hy'0]; exact hy'1)
    rw [hs] at hw
    have he := h.norm_exp_le hσ hk (s := (x : ℂ) + ((σ * y' : ℝ) : ℂ) * I)
      (by rw [hs]; exact hx.trans (by linarith)) hy'0 (hy'1.trans hy10) hs2
    simp only [hf]
    rw [norm_mul]
    exact mul_le_mul hw he (norm_nonneg _) (by positivity)
  have hvert : ∀ x : ℝ, |x| = X → ‖∫ y : ℝ in 0..(σ * y1), f (x + y * I)‖ ≤
      Cw * Real.exp (-κ * X) * y1 := by
    intro x hx
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := σ * y1)
      (f := fun y : ℝ => f (x + y * I)) (C := Cw * Real.exp (-κ * X)) (fun y hy => ?_)
    · rw [sub_zero, abs_mul, hσ1, one_mul, abs_of_pos hy1] at this
      exact this
    · -- y between 0 and σ y1
      have hyI : |y| ≤ y1 := by
        rcases hσ with rfl | rfl
        · rw [uIoc_of_le (by linarith)] at hy
          rw [abs_of_pos hy.1]; simpa using hy.2
        · rw [uIoc_of_ge (by linarith)] at hy
          rw [abs_of_nonpos hy.2]; linarith [hy.1]
      have hy' : 0 ≤ σ * y := by
        rcases hσ with rfl | rfl
        · rw [uIoc_of_le (by linarith)] at hy; simpa using hy.1.le
        · rw [uIoc_of_ge (by linarith)] at hy; linarith [hy.2]
      have hy'1 : σ * y ≤ y1 := by
        calc σ * y ≤ |σ * y| := le_abs_self _
          _ = |y| := by rw [abs_mul, hσ1, one_mul]
          _ ≤ y1 := hyI
      have hyσ : y = σ * (σ * y) := by
        rcases hσ with rfl | rfl <;> ring
      have := hexp1 (σ * y) hy' hy'1 x hx.le
      rw [← hyσ, hx] at this
      refine this.trans ?_
      have h1 : Real.exp (-(2 * Real.pi * k * m * (σ * y))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := h.hm
        have : 0 ≤ 2 * Real.pi * k * m * (σ * y) := by positivity
        linarith
      calc Cw * Real.exp (-κ * X) * Real.exp (-(2 * Real.pi * k * m * (σ * y))) ≤
          Cw * Real.exp (-κ * X) * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := mul_one _
  have htop : ‖∫ x : ℝ in (-X)..X, f (x + ((σ * y1 : ℝ) : ℂ) * I)‖ ≤
      2 * Cw / κ * Real.exp (-(2 * Real.pi * k * m * y1)) := by
    have hg : IntervalIntegrable (fun x : ℝ => Cw * Real.exp (-(2 * Real.pi * k * m * y1)) *
        Real.exp (-κ * |x|)) volume (-X) X :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -X) (b := X)
      (f := fun x : ℝ => f (x + ((σ * y1 : ℝ) : ℂ) * I))
      (g := fun x : ℝ => Cw * Real.exp (-(2 * Real.pi * k * m * y1)) * Real.exp (-κ * |x|))
      (by linarith) (Filter.Eventually.of_forall (fun x hx => by
        have := hexp1 y1 hy1.le le_rfl x (abs_le.mpr ⟨hx.1.le, hx.2⟩)
        calc _ ≤ _ := this
          _ = _ := by ring)) hg
    refine h1.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have := integral_exp_neg_abs_le hκ hX.le
    have hn : 0 ≤ Cw * Real.exp (-(2 * Real.pi * k * m * y1)) := by positivity
    calc Cw * Real.exp (-(2 * Real.pi * k * m * y1)) * ∫ x in (-X)..X, Real.exp (-κ * |x|)
        ≤ Cw * Real.exp (-(2 * Real.pi * k * m * y1)) * (2 / κ) :=
          mul_le_mul_of_nonneg_left this hn
      _ = _ := by ring
  have hV1 := hvert X (abs_of_pos hX)
  have hV2 := hvert (-X) (by rw [abs_neg, abs_of_pos hX])
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hG
  set B := ∫ x : ℝ in (-X)..X, f x with hB
  set T := ∫ x : ℝ in (-X)..X, f (x + ((σ * y1 : ℝ) : ℂ) * I) with hT
  set V1 := ∫ y : ℝ in (0 : ℝ)..(σ * y1), f (X + y * I) with hV1d
  set V2 := ∫ y : ℝ in (0 : ℝ)..(σ * y1), f (((-X : ℝ) : ℂ) + y * I) with hV2d
  have hBeq : B = T - I • V1 + I • V2 := by
    have : B - T + I • V1 - I • V2 = 0 := hG
    linear_combination this
  have hnorm : ‖B‖ ≤ ‖T‖ + ‖V1‖ + ‖V2‖ := by
    rw [hBeq]
    calc ‖T - I • V1 + I • V2‖ ≤ ‖T - I • V1‖ + ‖I • V2‖ := norm_add_le _ _
      _ ≤ ‖T‖ + ‖I • V1‖ + ‖I • V2‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by simp [norm_smul]
  have : ‖B‖ ≤ 2 * Cw / κ * Real.exp (-(2 * Real.pi * k * m * y1)) + Cw * Real.exp (-κ * X) * y1 +
      Cw * Real.exp (-κ * X) * y1 := by
    linarith
  calc ‖B‖ ≤ _ := this
    _ = _ := by ring

end FormalResearch.Special.Lattice
