module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


/-!
# Local Boas residue identity (FIVE-L: abstract core of `cts:boas`, Step 3)

Source: `CFT/modular_bootstrap/paper/constant_term_slit_strip.tex`, Lemma C8 (`cts:boas`), Step 3
("Applying Cauchy's theorem on `R_+ = [ζ₀-L₀, ζ₀+L₀]×[0,H]` (indented above real poles `n+φ₀`) to
`g_{ζ₀}(ζ) K₊(ζ)`, `K₊ = q²/(1-q)`, `q = e^{2πi(ζ-φ₀)}`").

Statement (proved, unconditional, `prob`-free).  For `g` holomorphic on an open `U ⊇ [a,b]×[0,H]`, real on `[a,b]`,
with `a, b ∉ φ₀ + ℤ`:
`∫_a^b Re g(u)(1 + 2cos(2π(u-φ₀))) du = Σ_{a<n+φ₀<b} Re g(n+φ₀) - 2 Re(Top - i Right + i Left)`
(`boas_residue_identity`), hence `≥ -2(‖Top‖+‖Right‖+‖Left‖)` when `g ≥ 0` at the poles (`boas_local_lower`), with the
top-edge estimate `‖Top‖ ≤ 2 M e^{-4πH}(b-a)` (`boasTop_norm_le`).

**Differences from the paper**: no indentation is used.  The singular part is removed with `dslope`
(`g K₊ - (i/2π) g(p)/(ζ-p)` is holomorphic near a single pole `p`), the pole term is integrated by the primitive
`log(-i(ζ-p))`, and the general case is the glueing of one-pole rectangles split between consecutive poles.  What is
**not** here: the Gaussian weight `g_{ζ₀} = h e^{-(ζ-ζ₀)²/2W²}`, the strip bound `h-growth`, and the vertical-side bound
`‖K₊(x₀+iy)‖ ≤ C e^{-4πy}` away from the poles (consumers of these live in `cts:boas` Steps 1-2 and 3).
-/

@[expose] public section

open Complex MeasureTheory intervalIntegral Set Real
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

noncomputable section

/-- `q(ζ) = e^{2πi(ζ-φ₀)}`. -/
def boasQ (φ0 : ℝ) (ζ : ℂ) : ℂ := Complex.exp (2 * π * I * (ζ - φ0))

/-- Boas kernel `K₊(ζ) = q²/(1-q)`. -/
def boasK (φ0 : ℝ) (ζ : ℂ) : ℂ := boasQ φ0 ζ ^ 2 / (1 - boasQ φ0 ζ)

lemma boasQ_eq_one_iff (φ0 : ℝ) (ζ : ℂ) : boasQ φ0 ζ = 1 ↔ ∃ n : ℤ, ζ = n + φ0 := by
  unfold boasQ
  rw [Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  have h : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  constructor
  · intro hz
    have : (ζ - φ0) * (2 * π * I) = n * (2 * π * I) := by rw [← hz]; ring
    have := mul_right_cancel₀ h this
    linear_combination this
  · intro hz
    rw [hz]; ring

lemma boasQ_differentiable (φ0 : ℝ) : Differentiable ℂ (boasQ φ0) := by
  unfold boasQ; fun_prop

lemma boasQ_hasDerivAt (φ0 : ℝ) (ζ : ℂ) :
    HasDerivAt (boasQ φ0) (2 * π * I * boasQ φ0 ζ) ζ := by
  unfold boasQ
  have h1 : HasDerivAt (fun z : ℂ => 2 * (π : ℂ) * I * (z - φ0)) (2 * π * I) ζ := by
    simpa using ((hasDerivAt_id ζ).sub_const (φ0 : ℂ)).const_mul (2 * (π : ℂ) * I)
  have := h1.cexp
  simpa [mul_comm] using this

lemma boasK_differentiableAt (φ0 : ℝ) {ζ : ℂ} (h : boasQ φ0 ζ ≠ 1) :
    DifferentiableAt ℂ (boasK φ0) ζ := by
  unfold boasK
  have hq := (boasQ_differentiable φ0) ζ
  exact (hq.pow 2).div (by fun_prop) (sub_ne_zero.mpr (Ne.symm h))

/-- real part of the kernel on the real line -/
lemma boasK_re_real (φ0 : ℝ) (u : ℝ) (hu : boasQ φ0 u ≠ 1) :
    (boasK φ0 u).re = -(1 + 2 * Real.cos (2 * π * (u - φ0))) / 2 := by
  set θ : ℝ := 2 * π * (u - φ0) with hθ
  have hq : boasQ φ0 u = Complex.exp (θ * I) := by
    unfold boasQ; congr 1; rw [hθ]; push_cast; ring
  rw [hq] at hu
  have hc : Real.cos θ ≠ 1 := by
    intro h
    apply hu
    apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, h]
    have := Real.sin_sq_add_cos_sq θ
    rw [h] at this
    nlinarith only [this]
  have hne : (1 - Complex.exp (θ * I)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have key : boasK φ0 u = -1 - Complex.exp (θ * I) + 1 / (1 - Complex.exp (θ * I)) := by
    unfold boasK; rw [hq]; field_simp; ring
  rw [key]
  have hnorm : Complex.normSq (1 - Complex.exp (θ * I)) = 2 - 2 * Real.cos θ := by
    rw [Complex.normSq_apply]
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith only [Real.sin_sq_add_cos_sq θ]
  have h1 : (1 / (1 - Complex.exp (θ * I))).re = 1 / 2 := by
    rw [one_div, Complex.inv_re, hnorm]
    simp [Complex.exp_ofReal_mul_I_re]
    have : (2 - 2 * Real.cos θ) ≠ 0 := by intro h; apply hc; linarith
    field_simp
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.one_re, h1,
    Complex.exp_ofReal_mul_I_re]
  have : Real.cos (2 * π * (u - φ0)) = Real.cos θ := rfl
  rw [this]; ring


/-- Cauchy-Goursat on `[a,b] × [0,H]`, in the form used below. -/
lemma rect_boundary_zero (f : ℂ → ℂ) (a b H : ℝ)
    (hd : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc 0 H)) :
    (∫ x : ℝ in a..b, f x) - (∫ x : ℝ in a..b, f (x + H * I)) +
      I * (∫ y : ℝ in (0:ℝ)..H, f (b + y * I)) - I * (∫ y : ℝ in (0:ℝ)..H, f (a + y * I)) = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, 0⟩ ⟨b, H⟩
    (by simpa using hd)
  simpa using this


/-- Primitive `log(-i(ζ-p))` of `1/(ζ-p)` on the closed upper half-plane minus `p`. -/
def poleLog (p : ℝ) (ζ : ℂ) : ℂ := Complex.log (-I * (ζ - p))

lemma poleLog_hasDerivAt (p : ℝ) {ζ : ℂ} (hζ : 0 ≤ ζ.im) (hne : ζ ≠ p) :
    HasDerivAt (poleLog p) (1 / (ζ - p)) ζ := by
  have hslit : (-I * (ζ - p)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hy : ζ.im = 0
    · right
      simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, neg_zero, Complex.sub_re,
        Complex.ofReal_re, Complex.neg_im, Complex.I_im, Complex.sub_im, Complex.ofReal_im, hy]
      intro h
      apply hne
      apply Complex.ext
      · simp only [Complex.ofReal_re]; linarith
      · simp [hy]
    · left
      simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, neg_zero, Complex.sub_re,
        Complex.ofReal_re, Complex.neg_im, Complex.I_im, Complex.sub_im, Complex.ofReal_im]
      have : 0 < ζ.im := lt_of_le_of_ne hζ (Ne.symm hy)
      linarith
  have h1 : HasDerivAt (fun z : ℂ => -I * (z - p)) (-I) ζ := by
    simpa using ((hasDerivAt_id ζ).sub_const (p : ℂ)).const_mul (-I)
  have h2 := h1.clog hslit
  have hz : ζ - p ≠ 0 := sub_ne_zero.mpr hne
  have : -I / (-I * (ζ - p)) = 1 / (ζ - p) := by
    field_simp
  rw [this] at h2
  exact h2

lemma poleLog_top (p a b H : ℝ) (hH : 0 < H) :
    ∫ x : ℝ in a..b, 1 / ((x : ℂ) + H * I - p) = poleLog p (b + H * I) - poleLog p (a + H * I) := by
  have hne : ∀ x : ℝ, ((x : ℂ) + H * I) ≠ p := by
    intro x h
    have := congrArg Complex.im h
    simp at this; linarith
  refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => poleLog p ((x : ℂ) + H * I))
    (f' := fun x : ℝ => 1 / ((x : ℂ) + H * I - p)) (fun x _ => ?_) ?_
  · have h := poleLog_hasDerivAt p (ζ := (x : ℂ) + H * I) (by simp; exact hH.le) (hne x)
    have h2 : HasDerivAt (fun z : ℂ => z + (H : ℂ) * I) 1 (x : ℂ) := by
      simpa using (hasDerivAt_id (x : ℂ)).add_const ((H : ℂ) * I)
    have h3 := h.comp (x : ℂ) h2
    have := HasDerivAt.comp_ofReal (e := fun z : ℂ => poleLog p (z + H * I)) (z := x) h3
    simpa using this
  · apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) fun x => ?_
    exact sub_ne_zero.mpr (hne x)

lemma poleLog_side (p x0 H : ℝ) (hx : x0 ≠ p) (hH : 0 ≤ H) :
    I * ∫ y : ℝ in (0:ℝ)..H, 1 / ((x0 : ℂ) + y * I - p) =
      poleLog p (x0 + H * I) - poleLog p x0 := by
  have hne : ∀ y : ℝ, ((x0 : ℂ) + y * I) ≠ p := by
    intro y h
    have := congrArg Complex.re h
    simp at this; exact hx this
  rw [← intervalIntegral.integral_const_mul]
  have hfin : ∀ y ∈ uIcc (0:ℝ) H, HasDerivAt (fun y : ℝ => poleLog p (x0 + y * I))
      (I * (1 / ((x0 : ℂ) + y * I - p))) y := by
    intro y hy
    have hy0 : 0 ≤ y := by
      rw [Set.uIcc_of_le hH] at hy; exact hy.1
    have h := poleLog_hasDerivAt p (ζ := (x0 : ℂ) + y * I) (by simpa using hy0) (hne y)
    have h2 : HasDerivAt (fun z : ℂ => (x0 : ℂ) + z * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x0 : ℂ)
    have h3 := h.comp (y : ℂ) h2
    have h4 := HasDerivAt.comp_ofReal (e := fun z : ℂ => poleLog p ((x0 : ℂ) + z * I)) (z := y) h3
    simpa [mul_comm] using h4
  have := integral_eq_sub_of_hasDerivAt hfin (by
    apply Continuous.intervalIntegrable
    refine continuous_const.mul (continuous_const.div (by fun_prop) fun y => ?_)
    exact sub_ne_zero.mpr (hne y))
  simpa using this

/-- The three outer sides of `∮ dζ/(ζ-p)` over `[a,b]×[0,H]`, `a < p < b`. -/
lemma pole_sides (p a b H : ℝ) (hap : a < p) (hpb : p < b) (hH : 0 < H) :
    (∫ x : ℝ in a..b, 1 / ((x : ℂ) + H * I - p)) -
      I * (∫ y : ℝ in (0:ℝ)..H, 1 / ((b : ℂ) + y * I - p)) +
      I * (∫ y : ℝ in (0:ℝ)..H, 1 / ((a : ℂ) + y * I - p)) =
      ((Real.log (b - p) - Real.log (p - a) : ℝ) : ℂ) - π * I := by
  rw [poleLog_top p a b H hH, poleLog_side p b H (ne_of_gt hpb) hH.le,
    poleLog_side p a H (ne_of_lt hap) hH.le]
  have e : poleLog p (b + H * I) - poleLog p (a + H * I) -
      (poleLog p (b + H * I) - poleLog p b) + (poleLog p (a + H * I) - poleLog p a) =
      poleLog p b - poleLog p a := by ring
  rw [e]
  have hb : poleLog p b = ((Real.log (b - p) : ℝ) : ℂ) - (π / 2 : ℝ) * I := by
    unfold poleLog
    have : -I * ((b : ℂ) - p) = ((b - p : ℝ) : ℂ) * (-I) := by push_cast; ring
    rw [this]
    apply Complex.ext
    · rw [Complex.log_re]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg, Complex.norm_I, mul_one,
        abs_of_pos (sub_pos.mpr hpb)]
      simp
    · rw [Complex.log_im, Complex.arg_real_mul _ (sub_pos.mpr hpb), Complex.arg_neg_I]; simp
  have ha : poleLog p a = ((Real.log (p - a) : ℝ) : ℂ) + (π / 2 : ℝ) * I := by
    unfold poleLog
    have : -I * ((a : ℂ) - p) = ((p - a : ℝ) : ℂ) * I := by push_cast; ring
    rw [this]
    apply Complex.ext
    · rw [Complex.log_re]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
        abs_of_pos (sub_pos.mpr hap)]
      simp
    · rw [Complex.log_im, Complex.arg_real_mul _ (sub_pos.mpr hap), Complex.arg_I]; simp
  rw [hb, ha]; push_cast; ring


/-- Top-edge integral `∫ g K₊` over `Im ζ = H`. -/
def boasTop (g : ℂ → ℂ) (φ0 a b H : ℝ) : ℂ :=
  ∫ x : ℝ in a..b, g ((x : ℂ) + H * I) * boasK φ0 ((x : ℂ) + H * I)

/-- Vertical-edge integral `∫ g K₊` over `Re ζ = x0`, `0 ≤ Im ζ ≤ H`. -/
def boasVert (g : ℂ → ℂ) (φ0 x0 H : ℝ) : ℂ :=
  ∫ y : ℝ in (0:ℝ)..H, g ((x0 : ℂ) + y * I) * boasK φ0 ((x0 : ℂ) + y * I)

/-- The three outer sides: `Re (Top - i Right + i Left)`. -/
def boasEdge (g : ℂ → ℂ) (φ0 a b H : ℝ) : ℝ :=
  (boasTop g φ0 a b H - I * boasVert g φ0 b H + I * boasVert g φ0 a H).re

lemma re_intervalIntegral {F : ℝ → ℂ} {s t : ℝ} (hF : IntervalIntegrable F volume s t) :
    (∫ x : ℝ in s..t, F x).re = ∫ x : ℝ in s..t, (F x).re := by
  simpa using (Complex.reCLM.intervalIntegral_comp_comm hF).symm

lemma intervalIntegrable_edge {f : ℂ → ℂ} {S : Set ℂ} (hf : ContinuousOn f S) {γ : ℝ → ℂ}
    (hγ : Continuous γ) {s t : ℝ} (hmaps : ∀ x ∈ uIcc s t, γ x ∈ S) :
    IntervalIntegrable (fun x : ℝ => f (γ x)) volume s t :=
  (hf.comp hγ.continuousOn hmaps).intervalIntegrable

lemma mem_rect_iff {a b H : ℝ} {ζ : ℂ} :
    ζ ∈ Icc a b ×ℂ Icc 0 H ↔ ζ.re ∈ Icc a b ∧ ζ.im ∈ Icc 0 H := Complex.mem_reProdIm

/-- Zero-pole case: no pole `n + φ₀` on `[a,b]`. -/
lemma boas_residue_zero (g : ℂ → ℂ) (φ0 a b H : ℝ) (hab : a ≤ b) (hH : 0 ≤ H) {U : Set ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (hrect : Icc a b ×ℂ Icc 0 H ⊆ U)
    (hreal : ∀ u ∈ Icc a b, (g u).im = 0) (hnp : ∀ n : ℤ, (n : ℝ) + φ0 ∉ Icc a b) :
    ∫ u : ℝ in a..b, (g u).re * (1 + 2 * Real.cos (2 * π * (u - φ0))) =
      -2 * boasEdge g φ0 a b H := by
  have hQ : ∀ ζ ∈ Icc a b ×ℂ Icc 0 H, boasQ φ0 ζ ≠ 1 := by
    intro ζ hζ h
    obtain ⟨n, hn⟩ := (boasQ_eq_one_iff φ0 ζ).1 h
    have hre : ζ.re = n + φ0 := by rw [hn]; simp
    exact hnp n (hre ▸ (mem_rect_iff.1 hζ).1)
  set f : ℂ → ℂ := fun ζ => g ζ * boasK φ0 ζ with hf
  have hdiff : ∀ ζ ∈ Icc a b ×ℂ Icc 0 H, DifferentiableAt ℂ f ζ := fun ζ hζ =>
    (hg.differentiableAt (hU.mem_nhds (hrect hζ))).mul (boasK_differentiableAt φ0 (hQ ζ hζ))
  have hcont : ContinuousOn f (Icc a b ×ℂ Icc 0 H) := fun ζ hζ =>
    (hdiff ζ hζ).continuousAt.continuousWithinAt
  have hC := rect_boundary_zero f a b H (by
    rw [uIcc_of_le hab, uIcc_of_le hH]
    exact fun ζ hζ => (hdiff ζ hζ).differentiableWithinAt)
  have hI0 : IntervalIntegrable (fun x : ℝ => f (x : ℂ)) volume a b :=
    intervalIntegrable_edge hcont Complex.continuous_ofReal (fun x hx => by
      rw [uIcc_of_le hab] at hx
      exact mem_rect_iff.2 ⟨by simpa using hx, by simp [hH]⟩)
  have hIT : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + H * I)) volume a b :=
    intervalIntegrable_edge hcont (by fun_prop) (fun x hx => by
      rw [uIcc_of_le hab] at hx
      exact mem_rect_iff.2 ⟨by simpa using hx, by simp [hH]⟩)
  have hIR : ∀ x0 ∈ Icc a b, IntervalIntegrable (fun y : ℝ => f ((x0 : ℂ) + y * I)) volume 0 H :=
    fun x0 hx0 => intervalIntegrable_edge hcont (by fun_prop) (fun y hy => by
      rw [uIcc_of_le hH] at hy
      exact mem_rect_iff.2 ⟨by simpa using hx0, by simpa using hy⟩)
  have hre := congrArg Complex.re hC
  rw [Complex.sub_re, Complex.add_re, Complex.sub_re, re_intervalIntegral hI0] at hre
  have hbot : ∫ x : ℝ in a..b, (f (x : ℂ)).re =
      -(1 / 2) * ∫ u : ℝ in a..b, (g u).re * (1 + 2 * Real.cos (2 * π * (u - φ0))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [uIcc_of_le hab] at hx
    have hx' : boasQ φ0 (x : ℂ) ≠ 1 := hQ x (mem_rect_iff.2 ⟨by simpa using hx, by simp [hH]⟩)
    simp only [hf, Complex.mul_re, hreal x hx, zero_mul, sub_zero, boasK_re_real φ0 x hx']
    ring
  have hRe : ∀ F : ℝ → ℂ, (I * ∫ y : ℝ in (0:ℝ)..H, F y).re = -(∫ y : ℝ in (0:ℝ)..H, F y).im := by
    intro F; simp
  have hedge : boasEdge g φ0 a b H =
      (∫ x : ℝ in a..b, f ((x : ℂ) + H * I)).re + (boasVert g φ0 b H).im -
        (boasVert g φ0 a H).im := by
    unfold boasEdge boasTop boasVert
    simp only [hf]
    simp
    ring
  have hb := hRe (fun y : ℝ => f ((b : ℂ) + y * I))
  have ha := hRe (fun y : ℝ => f ((a : ℂ) + y * I))
  have hvb : boasVert g φ0 b H = ∫ y : ℝ in (0:ℝ)..H, f ((b : ℂ) + y * I) := rfl
  have hva : boasVert g φ0 a H = ∫ y : ℝ in (0:ℝ)..H, f ((a : ℂ) + y * I) := rfl
  rw [hvb, hva] at hedge
  simp only [Complex.zero_re] at hre
  rw [hedge]
  simp only [hb, ha] at hre
  linarith only [hre, hbot]


/-- One-pole case: exactly one pole `p = m + φ₀` on `[a,b]`, in the interior. -/
lemma boas_residue_one (g : ℂ → ℂ) (φ0 a b H : ℝ) (m : ℤ) (hap : a < (m : ℝ) + φ0)
    (hpb : (m : ℝ) + φ0 < b) (hH : 0 < H) {U : Set ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (hrect : Icc a b ×ℂ Icc 0 H ⊆ U)
    (hreal : ∀ u ∈ Icc a b, (g u).im = 0)
    (hnp : ∀ n : ℤ, n ≠ m → (n : ℝ) + φ0 ∉ Icc a b) :
    ∫ u : ℝ in a..b, (g u).re * (1 + 2 * Real.cos (2 * π * (u - φ0))) =
      (g ((m : ℝ) + φ0 : ℝ)).re - 2 * boasEdge g φ0 a b H := by
  set p : ℝ := (m : ℝ) + φ0 with hp
  have hab : a ≤ b := by linarith
  have hQp : boasQ φ0 (p : ℂ) = 1 := (boasQ_eq_one_iff φ0 _).2 ⟨m, by simp [hp]⟩
  have hQ : ∀ ζ ∈ Icc a b ×ℂ Icc 0 H, ζ ≠ p → boasQ φ0 ζ ≠ 1 := by
    intro ζ hζ hne h
    obtain ⟨n, hn⟩ := (boasQ_eq_one_iff φ0 ζ).1 h
    have hre : ζ.re = n + φ0 := by rw [hn]; simp
    by_cases hnm : n = m
    · apply hne
      have him : ζ.im = 0 := by rw [hn]; simp
      apply Complex.ext
      · simp [hre, hnm, hp]
      · simp [him]
    · exact hnp n hnm (hre ▸ (mem_rect_iff.1 hζ).1)
  set D : ℂ → ℂ := dslope (boasQ φ0) (p : ℂ) with hD
  have hDdiff : Differentiable ℂ D := by
    have := (differentiableOn_dslope (s := Set.univ) (c := (p : ℂ)) Filter.univ_mem).2
      (boasQ_differentiable φ0).differentiableOn
    exact differentiableOn_univ.1 this
  have hDp : D (p : ℂ) = 2 * π * I := by
    rw [hD, dslope_same, (boasQ_hasDerivAt φ0 (p : ℂ)).deriv, hQp, mul_one]
  have hDne : ∀ ζ ∈ Icc a b ×ℂ Icc 0 H, D ζ ≠ 0 := by
    intro ζ hζ
    by_cases hne : ζ = p
    · rw [hne, hDp]; simp [Real.pi_ne_zero]
    · rw [hD, dslope_of_ne _ hne, slope_def_field, hQp]
      exact div_ne_zero (sub_ne_zero.mpr (hQ ζ hζ hne)) (sub_ne_zero.mpr hne)
  set B : ℂ → ℂ := fun ζ => -(boasQ φ0 ζ ^ 2 * g ζ) / D ζ with hB
  set c : ℂ := (I / (2 * π)) * g p with hc
  set V : Set ℂ := U ∩ {ζ | D ζ ≠ 0} with hV
  have hVo : IsOpen V := hU.inter (isOpen_ne_fun hDdiff.continuous continuous_const)
  have hrV : Icc a b ×ℂ Icc 0 H ⊆ V := fun ζ hζ => ⟨hrect hζ, hDne ζ hζ⟩
  have hpmem : (p : ℂ) ∈ Icc a b ×ℂ Icc 0 H :=
    mem_rect_iff.2 ⟨by simp [hap.le, hpb.le], by simp [hH.le]⟩
  have hBdiff : DifferentiableOn ℂ B V := by
    intro ζ hζ
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ g ζ := hg.differentiableAt (hU.mem_nhds hζ.1)
    have h2 := (boasQ_differentiable φ0) ζ
    exact (((h2.pow 2).mul h1).neg).div (hDdiff ζ) hζ.2
  have hBp : B (p : ℂ) = c := by
    simp only [hB, hc, hDp, hQp]
    have h2 : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
    simp [Complex.I_sq]
  set Hf : ℂ → ℂ := dslope B (p : ℂ) with hHf
  have hHfdiff : DifferentiableOn ℂ Hf V :=
    (differentiableOn_dslope (hVo.mem_nhds (hrV hpmem))).2 hBdiff
  have hHfeq : ∀ ζ ∈ Icc a b ×ℂ Icc 0 H, ζ ≠ p →
      Hf ζ = g ζ * boasK φ0 ζ - c * (1 / (ζ - p)) := by
    intro ζ hζ hne
    have h1 := hQ ζ hζ hne
    have h1' : (1 - boasQ φ0 ζ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have h1'' : (boasQ φ0 ζ - 1) ≠ 0 := sub_ne_zero.mpr h1
    have h2 : ζ - (p : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    rw [hHf, dslope_of_ne _ hne, slope_def_field, hBp]
    have hDζ : D ζ = (boasQ φ0 ζ - 1) / (ζ - p) := by
      rw [hD, dslope_of_ne _ hne, slope_def_field, hQp]
    simp only [hB, hDζ, boasK]
    field_simp
    ring
  have hCau := rect_boundary_zero Hf a b H (by
    rw [uIcc_of_le hab, uIcc_of_le hH.le]
    exact fun ζ hζ => (hHfdiff ζ (hrV hζ)).mono hrV)
  have hHfcont : ContinuousOn Hf (Icc a b ×ℂ Icc 0 H) :=
    fun ζ hζ => ((hHfdiff ζ (hrV hζ)).continuousWithinAt).mono hrV
  have hgKcont : ContinuousOn (fun ζ => g ζ * boasK φ0 ζ)
      (Icc a b ×ℂ Icc 0 H \ {(p : ℂ)}) := by
    intro ζ hζ
    have hζ' := hζ.1
    have hne : ζ ≠ p := hζ.2
    exact ((hg.differentiableAt (hU.mem_nhds (hrect hζ'))).mul
      (boasK_differentiableAt φ0 (hQ ζ hζ' hne))).continuousAt.continuousWithinAt
  -- the pole term
  have hgp : g p = ((g p).re : ℂ) :=
    Complex.ext (by simp) (by simpa using hreal p ⟨hap.le, hpb.le⟩)
  have hcdecomp : c = (((g p).re / (2 * π) : ℝ) : ℂ) * I := by
    rw [hc]; conv_lhs => rw [hgp]
    push_cast; ring
  have hcre : c.re = 0 := by rw [hcdecomp, Complex.re_ofReal_mul]; simp
  -- vertical sides
  have hvert : ∀ x0 ∈ Icc a b, x0 ≠ p →
      ∫ y : ℝ in (0:ℝ)..H, Hf ((x0 : ℂ) + y * I) =
        boasVert g φ0 x0 H - c * ∫ y : ℝ in (0:ℝ)..H, 1 / ((x0 : ℂ) + y * I - p) := by
    intro x0 hx0 hne
    have hmem : ∀ y ∈ uIcc (0:ℝ) H, ((x0 : ℂ) + y * I) ∈ Icc a b ×ℂ Icc 0 H := by
      intro y hy
      rw [uIcc_of_le hH.le] at hy
      exact mem_rect_iff.2 ⟨by simpa using hx0, by simpa using hy⟩
    have hne' : ∀ y : ℝ, ((x0 : ℂ) + y * I) ≠ p := by
      intro y h
      have := congrArg Complex.re h
      simp at this; exact hne this
    have hi1 : IntervalIntegrable (fun y : ℝ => g ((x0 : ℂ) + y * I) * boasK φ0 ((x0 : ℂ) + y * I))
        volume 0 H :=
      intervalIntegrable_edge hgKcont (by fun_prop) (fun y hy => ⟨hmem y hy, hne' y⟩)
    have hi2 : IntervalIntegrable (fun y : ℝ => c * (1 / ((x0 : ℂ) + y * I - p))) volume 0 H := by
      apply Continuous.intervalIntegrable
      refine continuous_const.mul (continuous_const.div (by fun_prop) fun y => ?_)
      exact sub_ne_zero.mpr (hne' y)
    calc ∫ y : ℝ in (0:ℝ)..H, Hf ((x0 : ℂ) + y * I)
        = ∫ y : ℝ in (0:ℝ)..H, (g ((x0 : ℂ) + y * I) * boasK φ0 ((x0 : ℂ) + y * I) -
            c * (1 / ((x0 : ℂ) + y * I - p))) :=
          intervalIntegral.integral_congr (fun y hy => hHfeq _ (hmem y hy) (hne' y))
      _ = _ := by
          rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
          rfl
  have htop : ∫ x : ℝ in a..b, Hf ((x : ℂ) + H * I) =
      boasTop g φ0 a b H - c * ∫ x : ℝ in a..b, 1 / ((x : ℂ) + H * I - p) := by
    have hmem : ∀ x ∈ uIcc a b, ((x : ℂ) + H * I) ∈ Icc a b ×ℂ Icc 0 H := by
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact mem_rect_iff.2 ⟨by simpa using hx, by simp [hH.le]⟩
    have hne' : ∀ x : ℝ, ((x : ℂ) + H * I) ≠ p := by
      intro x h
      have := congrArg Complex.im h
      simp at this; linarith
    have hi1 : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + H * I) * boasK φ0 ((x : ℂ) + H * I))
        volume a b :=
      intervalIntegrable_edge hgKcont (by fun_prop) (fun x hx => ⟨hmem x hx, hne' x⟩)
    have hi2 : IntervalIntegrable (fun x : ℝ => c * (1 / ((x : ℂ) + H * I - p))) volume a b := by
      apply Continuous.intervalIntegrable
      refine continuous_const.mul (continuous_const.div (by fun_prop) fun x => ?_)
      exact sub_ne_zero.mpr (hne' x)
    calc ∫ x : ℝ in a..b, Hf ((x : ℂ) + H * I)
        = ∫ x : ℝ in a..b, (g ((x : ℂ) + H * I) * boasK φ0 ((x : ℂ) + H * I) -
            c * (1 / ((x : ℂ) + H * I - p))) :=
          intervalIntegral.integral_congr (fun x hx => hHfeq _ (hmem x hx) (hne' x))
      _ = _ := by
          rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
          rfl
  rw [htop, hvert b ⟨hab, le_rfl⟩ hpb.ne', hvert a ⟨le_rfl, hab⟩ hap.ne] at hCau
  have hpole := pole_sides p a b H hap hpb hH
  -- real part of the bottom integral
  have hHfint : IntervalIntegrable (fun x : ℝ => Hf (x : ℂ)) volume a b :=
    intervalIntegrable_edge hHfcont Complex.continuous_ofReal (fun x hx => by
      rw [uIcc_of_le hab] at hx
      exact mem_rect_iff.2 ⟨by simpa using hx, by simp [hH.le]⟩)
  have hbot : (∫ x : ℝ in a..b, Hf (x : ℂ)).re =
      -(1 / 2) * ∫ u : ℝ in a..b, (g u).re * (1 + 2 * Real.cos (2 * π * (u - φ0))) := by
    rw [re_intervalIntegral hHfint, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    have hae : ∀ᵐ x : ℝ ∂volume, x ≠ p := by
      have := (Set.countable_singleton p).ae_notMem (volume : Measure ℝ)
      filter_upwards [this] with x hx
      simpa using hx
    filter_upwards [hae] with x hx hxI
    rw [uIoc_of_le hab] at hxI
    have hxmem : (x : ℂ) ∈ Icc a b ×ℂ Icc 0 H :=
      mem_rect_iff.2 ⟨by simpa using Ioc_subset_Icc_self hxI, by simp [hH.le]⟩
    have hxne : (x : ℂ) ≠ p := by
      intro h; apply hx; exact_mod_cast h
    rw [hHfeq _ hxmem hxne]
    have hx' : boasQ φ0 (x : ℂ) ≠ 1 := hQ _ hxmem hxne
    have hdiv : c * (1 / ((x : ℂ) - p)) = c * (((1 / (x - p) : ℝ)) : ℂ) := by push_cast; rfl
    rw [Complex.sub_re, hdiv, Complex.re_mul_ofReal, hcre, zero_mul, sub_zero, Complex.mul_re,
      hreal x (Ioc_subset_Icc_self hxI), zero_mul, sub_zero, boasK_re_real φ0 x hx']
    ring
  have hRe : ∀ F : ℝ → ℂ, (I * ∫ y : ℝ in (0:ℝ)..H, F y).re = -(∫ y : ℝ in (0:ℝ)..H, F y).im := by
    intro F; simp
  have hcpole : (c * (((Real.log (b - p) - Real.log (p - a) : ℝ) : ℂ) - π * I)).re =
      (g p).re / 2 := by
    rw [hcdecomp]
    have : (((g p).re / (2 * π) : ℝ) : ℂ) * I *
        (((Real.log (b - p) - Real.log (p - a) : ℝ) : ℂ) - π * I) =
        ((((g p).re / (2 * π)) * (Real.log (b - p) - Real.log (p - a)) : ℝ) : ℂ) * I +
          (((g p).re / 2 : ℝ) : ℂ) := by
      have h2 : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      push_cast
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [this, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, zero_add,
      Complex.ofReal_re]
  -- assemble
  have hE : boasEdge g φ0 a b H = (boasTop g φ0 a b H - I * boasVert g φ0 b H +
      I * boasVert g φ0 a H).re := rfl
  have hCau' : (∫ x : ℝ in a..b, Hf (x : ℂ)) =
      (boasTop g φ0 a b H - I * boasVert g φ0 b H + I * boasVert g φ0 a H) -
        c * (((Real.log (b - p) - Real.log (p - a) : ℝ) : ℂ) - π * I) := by
    rw [← hpole]
    linear_combination hCau
  have hre := congrArg Complex.re hCau'
  rw [Complex.sub_re, hcpole, hbot, ← hE] at hre
  linarith only [hre]


/-- Sum of `Re g` over the poles `n + φ₀`, `m < n < M`. -/
def boasPoleSum (g : ℂ → ℂ) (φ0 : ℝ) (m M : ℤ) : ℝ :=
  ∑ n ∈ Finset.Ioo m M, (g (((n : ℝ) + φ0 : ℝ) : ℂ)).re

lemma boas_top_integrable (g : ℂ → ℂ) (φ0 a b H : ℝ) (hab : a ≤ b) (hH : 0 < H) {U : Set ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (hrect : Icc a b ×ℂ Icc 0 H ⊆ U) :
    IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + H * I) * boasK φ0 ((x : ℂ) + H * I))
      volume a b := by
  have hmem : ∀ x ∈ uIcc a b, ((x : ℂ) + H * I) ∈ Icc a b ×ℂ Icc 0 H := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact mem_rect_iff.2 ⟨by simpa using hx, by simp [hH.le]⟩
  have hQ : ∀ x : ℝ, boasQ φ0 ((x : ℂ) + H * I) ≠ 1 := by
    intro x h
    obtain ⟨n, hn⟩ := (boasQ_eq_one_iff φ0 _).1 h
    have := congrArg Complex.im hn
    simp at this; linarith
  have hcont : ContinuousOn (fun ζ => g ζ * boasK φ0 ζ)
      (Icc a b ×ℂ Icc 0 H ∩ {ζ | boasQ φ0 ζ ≠ 1}) := fun ζ hζ =>
    ((hg.differentiableAt (hU.mem_nhds (hrect hζ.1))).mul
      (boasK_differentiableAt φ0 hζ.2)).continuousAt.continuousWithinAt
  exact intervalIntegrable_edge hcont (by fun_prop) (fun x hx => ⟨hmem x hx, hQ x⟩)

/-- Gluing two adjacent rectangles: the three-sided edge functional is additive. -/
lemma boasEdge_add (g : ℂ → ℂ) (φ0 a c b H : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (hH : 0 < H)
    {U : Set ℂ} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hrect : Icc a b ×ℂ Icc 0 H ⊆ U) :
    boasEdge g φ0 a b H = boasEdge g φ0 a c H + boasEdge g φ0 c b H := by
  have h1 := boas_top_integrable g φ0 a c H hac hH hU hg
    (fun ζ hζ => hrect (by
      have := mem_rect_iff.1 hζ
      exact mem_rect_iff.2 ⟨⟨this.1.1, this.1.2.trans hcb⟩, this.2⟩))
  have h2 := boas_top_integrable g φ0 c b H hcb hH hU hg
    (fun ζ hζ => hrect (by
      have := mem_rect_iff.1 hζ
      exact mem_rect_iff.2 ⟨⟨hac.trans this.1.1, this.1.2⟩, this.2⟩))
  unfold boasEdge boasTop
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  simp only [Complex.add_re, Complex.sub_re, Complex.I_mul_re]
  ring


lemma boas_band_integrable (g : ℂ → ℂ) (φ0 a b H : ℝ) (hab : a ≤ b) (hH : 0 ≤ H) {U : Set ℂ}
    (hg : DifferentiableOn ℂ g U) (hrect : Icc a b ×ℂ Icc 0 H ⊆ U) :
    IntervalIntegrable (fun u : ℝ => (g u).re * (1 + 2 * Real.cos (2 * π * (u - φ0))))
      volume a b := by
  have hmem : ∀ u ∈ uIcc a b, (u : ℂ) ∈ U := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    exact hrect (mem_rect_iff.2 ⟨by simpa using hu, by simp [hH]⟩)
  have hc : ContinuousOn (fun u : ℝ => g (u : ℂ)) (uIcc a b) :=
    hg.continuousOn.comp Complex.continuous_ofReal.continuousOn hmem
  refine ContinuousOn.intervalIntegrable ?_
  exact (Complex.continuous_re.comp_continuousOn hc).mul (by fun_prop)

/-- Core induction: exactly the poles `m < n < M` lie in `[a,b]`. -/
theorem boas_residue_core (g : ℂ → ℂ) (φ0 H : ℝ) (hH : 0 < H) {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    ∀ (N : ℕ) (m M : ℤ) (a b : ℝ), M - m = (N : ℤ) + 1 → a < b →
      (m : ℝ) < a - φ0 → a - φ0 < m + 1 → (M : ℝ) - 1 < b - φ0 → b - φ0 < M →
      Icc a b ×ℂ Icc 0 H ⊆ U → (∀ u ∈ Icc a b, (g u).im = 0) →
      ∫ u : ℝ in a..b, (g u).re * (1 + 2 * Real.cos (2 * π * (u - φ0))) =
        boasPoleSum g φ0 m M - 2 * boasEdge g φ0 a b H := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro m M a b hMm hab ham ham1 hbM1 hbM hrect hreal
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · -- no pole
      have hM : M = m + 1 := by omega
      subst hM
      have hnp : ∀ n : ℤ, (n : ℝ) + φ0 ∉ Icc a b := by
        intro n hn
        have h1 : (m : ℝ) < n := by linarith [hn.1]
        have h2 : (n : ℝ) < m + 1 := by push_cast at hbM; linarith [hn.2]
        have h1' : m < n := by exact_mod_cast h1
        have h2' : n < m + 1 := by exact_mod_cast h2
        omega
      have := boas_residue_zero g φ0 a b H hab.le hH.le hU hg hrect hreal hnp
      rw [this]
      have hs : Finset.Ioo m (m + 1) = ∅ := by
        ext n; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
      simp [boasPoleSum, hs]
    · -- one pole `m + 1`
      have hM : M = m + 2 := by omega
      subst hM
      have hnp : ∀ n : ℤ, n ≠ m + 1 → (n : ℝ) + φ0 ∉ Icc a b := by
        intro n hne hn
        have h1 : (m : ℝ) < n := by linarith [hn.1]
        have h2 : (n : ℝ) < m + 2 := by push_cast at hbM; linarith [hn.2]
        have h1' : m < n := by exact_mod_cast h1
        have h2' : n < m + 2 := by exact_mod_cast h2
        omega
      have hap : a < ((m + 1 : ℤ) : ℝ) + φ0 := by push_cast; linarith
      have hpb : ((m + 1 : ℤ) : ℝ) + φ0 < b := by push_cast at hbM1 ⊢; linarith
      have := boas_residue_one g φ0 a b H (m + 1) hap hpb hH hU hg hrect hreal hnp
      rw [this]
      have hs : Finset.Ioo m (m + 2) = {m + 1} := by
        ext n; simp only [Finset.mem_Ioo, Finset.mem_singleton]; omega
      simp [boasPoleSum, hs]
  · -- split at `c = m + 3/2 + φ₀`
    set c : ℝ := (m : ℝ) + 3 / 2 + φ0 with hc
    have hM3 : m + 3 ≤ M := by omega
    have hM3' : (m : ℝ) + 3 ≤ M := by exact_mod_cast hM3
    have hac : a < c := by rw [hc]; linarith
    have hcb : c < b := by rw [hc]; linarith
    have hrL : Icc a c ×ℂ Icc 0 H ⊆ U := fun ζ hζ => hrect (by
      have := mem_rect_iff.1 hζ
      exact mem_rect_iff.2 ⟨⟨this.1.1, this.1.2.trans hcb.le⟩, this.2⟩)
    have hrR : Icc c b ×ℂ Icc 0 H ⊆ U := fun ζ hζ => hrect (by
      have := mem_rect_iff.1 hζ
      exact mem_rect_iff.2 ⟨⟨hac.le.trans this.1.1, this.1.2⟩, this.2⟩)
    have hL := ih 1 (by omega) m (m + 2) a c (by omega) hac ham ham1
      (by push_cast; rw [hc]; linarith) (by push_cast; rw [hc]; linarith) hrL
      (fun u hu => hreal u ⟨hu.1, hu.2.trans hcb.le⟩)
    have hR := ih (N - 1) (by omega) (m + 1) M c b (by omega) hcb
      (by push_cast; rw [hc]; linarith) (by push_cast; rw [hc]; linarith)
      hbM1 hbM hrR (fun u hu => hreal u ⟨hac.le.trans hu.1, hu.2⟩)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (boas_band_integrable g φ0 a c H hac.le hH.le hg (fun ζ hζ => hrL hζ))
      (boas_band_integrable g φ0 c b H hcb.le hH.le hg (fun ζ hζ => hrR hζ))
    rw [← hsplit, hL, hR, boasEdge_add g φ0 a c b H hac.le hcb.le hH hU hg hrect]
    have hsum : boasPoleSum g φ0 m M =
        boasPoleSum g φ0 m (m + 2) + boasPoleSum g φ0 (m + 1) M := by
      unfold boasPoleSum
      rw [← Finset.sum_union]
      · congr 1; ext n; simp only [Finset.mem_Ioo, Finset.mem_union]; omega
      · rw [Finset.disjoint_left]
        intro n h1 h2
        simp only [Finset.mem_Ioo] at h1 h2; omega
    rw [hsum]; ring


lemma ne_floor_of_ne {φ0 a : ℝ} (ha : ∀ n : ℤ, (n : ℝ) + φ0 ≠ a) : (⌊a - φ0⌋ : ℝ) < a - φ0 := by
  refine lt_of_le_of_ne (Int.floor_le _) fun h => ha ⌊a - φ0⌋ ?_
  linarith

lemma ceil_ne_of_ne {φ0 b : ℝ} (hb : ∀ n : ℤ, (n : ℝ) + φ0 ≠ b) : b - φ0 < (⌈b - φ0⌉ : ℝ) := by
  refine lt_of_le_of_ne (Int.le_ceil _) fun h => hb ⌈b - φ0⌉ ?_
  linarith

/-- **Local Boas residue identity** (`cts:boas`, Step 3, abstract core).  Let `g` be holomorphic on an open
`U ⊇ [a,b]×[0,H]`, real on `[a,b]`, and `a, b ∉ φ₀ + ℤ`.  Then
`∫_a^b Re g(u) (1 + 2cos(2π(u-φ₀))) du = Σ_{a<n+φ₀<b} Re g(n+φ₀) - 2 Re(Top - i Right + i Left)`,
with `Top = ∫ g K₊ (u+iH) du`, `Right/Left = ∫_0^H gK₊ (b/a + iv) dv`, `K₊ = q²/(1-q)`, `q = e^{2πi(ζ-φ₀)}`. -/
theorem boas_residue_identity (g : ℂ → ℂ) (φ0 a b H : ℝ) (hab : a < b) (hH : 0 < H) {U : Set ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (hrect : Icc a b ×ℂ Icc 0 H ⊆ U)
    (hreal : ∀ u ∈ Icc a b, (g u).im = 0)
    (ha : ∀ n : ℤ, (n : ℝ) + φ0 ≠ a) (hb : ∀ n : ℤ, (n : ℝ) + φ0 ≠ b) :
    ∫ u : ℝ in a..b, (g u).re * (1 + 2 * Real.cos (2 * π * (u - φ0))) =
      boasPoleSum g φ0 ⌊a - φ0⌋ ⌈b - φ0⌉ - 2 * boasEdge g φ0 a b H := by
  have h1 := ne_floor_of_ne ha
  have h2 := ceil_ne_of_ne hb
  have h3 : (⌊a - φ0⌋ : ℝ) < ⌈b - φ0⌉ := by linarith
  have h3' : ⌊a - φ0⌋ < ⌈b - φ0⌉ := by exact_mod_cast h3
  have hN : ⌈b - φ0⌉ - ⌊a - φ0⌋ = ((⌈b - φ0⌉ - ⌊a - φ0⌋ - 1).toNat : ℤ) + 1 := by omega
  refine boas_residue_core g φ0 H hH hU hg _ _ _ a b hN hab h1 ?_ ?_ h2 hrect hreal
  · have := Int.lt_floor_add_one (a - φ0); linarith
  · have := Int.ceil_lt_add_one (b - φ0); linarith

lemma mem_poles_iff {φ0 a b : ℝ} (ha : ∀ n : ℤ, (n : ℝ) + φ0 ≠ a) (hb : ∀ n : ℤ, (n : ℝ) + φ0 ≠ b)
    (n : ℤ) : n ∈ Finset.Ioo ⌊a - φ0⌋ ⌈b - φ0⌉ ↔ a < (n : ℝ) + φ0 ∧ (n : ℝ) + φ0 < b := by
  have h1 := ne_floor_of_ne ha
  have h2 := ceil_ne_of_ne hb
  simp only [Finset.mem_Ioo]
  constructor
  · rintro ⟨h3, h4⟩
    have h3' : (⌊a - φ0⌋ : ℝ) < n := by exact_mod_cast h3
    have h4' : (n : ℝ) < ⌈b - φ0⌉ := by exact_mod_cast h4
    have h5 : a - φ0 < n := by
      by_contra hcon
      have : n ≤ ⌊a - φ0⌋ := Int.le_floor.2 (not_lt.1 hcon)
      omega
    have h6 : (n : ℝ) < b - φ0 := by
      by_contra hcon
      have : ⌈b - φ0⌉ ≤ n := Int.ceil_le.2 (not_lt.1 hcon)
      omega
    constructor <;> linarith
  · rintro ⟨h3, h4⟩
    constructor
    · have : (⌊a - φ0⌋ : ℝ) < n := lt_of_le_of_lt (Int.floor_le _) (by linarith)
      exact_mod_cast this
    · have : (n : ℝ) < ⌈b - φ0⌉ := lt_of_lt_of_le (by linarith) (Int.le_ceil _)
      exact_mod_cast this

/-- **Local Boas positivity.**  If `g ≥ 0` at the poles in `(a,b)`, the oscillatory integral against
`1 + 2cos(2π(u-φ₀))` is at least `-2 Re(Top - i Right + i Left) ≥ -2(‖Top‖ + ‖Right‖ + ‖Left‖)`. -/
theorem boas_local_lower (g : ℂ → ℂ) (φ0 a b H : ℝ) (hab : a < b) (hH : 0 < H) {U : Set ℂ}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (hrect : Icc a b ×ℂ Icc 0 H ⊆ U)
    (hreal : ∀ u ∈ Icc a b, (g u).im = 0)
    (ha : ∀ n : ℤ, (n : ℝ) + φ0 ≠ a) (hb : ∀ n : ℤ, (n : ℝ) + φ0 ≠ b)
    (hpos : ∀ n : ℤ, a < (n : ℝ) + φ0 → (n : ℝ) + φ0 < b → 0 ≤ (g (((n : ℝ) + φ0 : ℝ) : ℂ)).re) :
    -2 * (‖boasTop g φ0 a b H‖ + ‖boasVert g φ0 b H‖ + ‖boasVert g φ0 a H‖) ≤
      ∫ u : ℝ in a..b, (g u).re * (1 + 2 * Real.cos (2 * π * (u - φ0))) := by
  rw [boas_residue_identity g φ0 a b H hab hH hU hg hrect hreal ha hb]
  have hs : 0 ≤ boasPoleSum g φ0 ⌊a - φ0⌋ ⌈b - φ0⌉ :=
    Finset.sum_nonneg fun n hn => by
      obtain ⟨h1, h2⟩ := (mem_poles_iff ha hb n).1 hn
      exact hpos n h1 h2
  have he : boasEdge g φ0 a b H ≤ ‖boasTop g φ0 a b H‖ + ‖boasVert g φ0 b H‖ + ‖boasVert g φ0 a H‖ := by
    unfold boasEdge
    refine (Complex.re_le_norm _).trans ?_
    calc ‖boasTop g φ0 a b H - I * boasVert g φ0 b H + I * boasVert g φ0 a H‖
        ≤ ‖boasTop g φ0 a b H - I * boasVert g φ0 b H‖ + ‖I * boasVert g φ0 a H‖ := norm_add_le _ _
      _ ≤ (‖boasTop g φ0 a b H‖ + ‖I * boasVert g φ0 b H‖) + ‖I * boasVert g φ0 a H‖ := by
          gcongr; exact norm_sub_le _ _
      _ = _ := by simp
  linarith only [hs, he]


lemma boasQ_norm (φ0 : ℝ) (ζ : ℂ) : ‖boasQ φ0 ζ‖ = Real.exp (-(2 * π * ζ.im)) := by
  unfold boasQ
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

lemma boasK_norm_le (φ0 : ℝ) (ζ : ℂ) (h : ‖boasQ φ0 ζ‖ ≤ 1 / 2) :
    ‖boasK φ0 ζ‖ ≤ 2 * ‖boasQ φ0 ζ‖ ^ 2 := by
  unfold boasK
  rw [norm_div, norm_pow]
  have h1 : 1 / 2 ≤ ‖1 - boasQ φ0 ζ‖ := by
    have := norm_sub_norm_le (1 : ℂ) (boasQ φ0 ζ)
    simp only [norm_one] at this
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith only [h1, sq_nonneg ‖boasQ φ0 ζ‖]

/-- Top edge: `‖Top‖ ≤ 2 M e^{-4πH} (b-a)` once `e^{-2πH} ≤ 1/2`, `‖g‖ ≤ M` on `Im ζ = H`. -/
theorem boasTop_norm_le (g : ℂ → ℂ) (φ0 a b H M : ℝ) (hab : a ≤ b)
    (hq : Real.exp (-(2 * π * H)) ≤ 1 / 2)
    (hM : ∀ x : ℝ, a ≤ x → x ≤ b → ‖g ((x : ℂ) + H * I)‖ ≤ M) :
    ‖boasTop g φ0 a b H‖ ≤ 2 * M * Real.exp (-(4 * π * H)) * (b - a) := by
  unfold boasTop
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := 2 * M * Real.exp (-(4 * π * H)))
    (f := fun x : ℝ => g ((x : ℂ) + H * I) * boasK φ0 ((x : ℂ) + H * I)) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      have hqn : ‖boasQ φ0 ((x : ℂ) + H * I)‖ = Real.exp (-(2 * π * H)) := by
        rw [boasQ_norm]; simp
      have hK := boasK_norm_le φ0 ((x : ℂ) + H * I) (by rw [hqn]; exact hq)
      rw [hqn, ← Real.exp_nat_mul] at hK
      have hexp : Real.exp ((2 : ℕ) * -(2 * π * H)) = Real.exp (-(4 * π * H)) := by
        congr 1; push_cast; ring
      rw [hexp] at hK
      rw [norm_mul]
      have hg0 := hM x hx.1.le hx.2
      have hge : 0 ≤ ‖g ((x : ℂ) + H * I)‖ := norm_nonneg _
      have hKn : 0 ≤ ‖boasK φ0 ((x : ℂ) + H * I)‖ := norm_nonneg _
      calc ‖g ((x : ℂ) + H * I)‖ * ‖boasK φ0 ((x : ℂ) + H * I)‖
          ≤ M * (2 * Real.exp (-(4 * π * H))) := mul_le_mul hg0 hK hKn (hge.trans hg0)
        _ = _ := by ring)
  rw [abs_of_nonneg (sub_nonneg.2 hab)] at hb
  linarith only [hb]

/-- Vertical edge: a bound `C` for `‖g K₊‖` on the side gives `‖Right‖ ≤ C H`. -/
theorem boasVert_norm_le (g : ℂ → ℂ) (φ0 x0 H C : ℝ) (hH : 0 ≤ H)
    (hC : ∀ y : ℝ, 0 ≤ y → y ≤ H → ‖g ((x0 : ℂ) + y * I) * boasK φ0 ((x0 : ℂ) + y * I)‖ ≤ C) :
    ‖boasVert g φ0 x0 H‖ ≤ C * H := by
  unfold boasVert
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := H) (C := C)
    (f := fun y : ℝ => g ((x0 : ℂ) + y * I) * boasK φ0 ((x0 : ℂ) + y * I)) (by
      intro y hy
      rw [uIoc_of_le hH] at hy
      exact hC y hy.1.le hy.2)
  rw [sub_zero, abs_of_nonneg hH] at hb
  exact hb

end
end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.boas_residue_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boas_residue_identity

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.boas_local_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boas_local_lower

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.boasTop_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boasTop_norm_le
