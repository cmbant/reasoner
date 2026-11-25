module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Twice differentiable functions with explicit bounds

Source: bookkeeping for `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4 (Piece 1: the pulled-back
amplitude `B(s) = Ã(t(s)) t'(s)` has uniformly bounded `C²` norm).  **Proved.**

`D2 I g g1 g2 K`: `g` has derivative `g1`, `g1` has derivative `g2` (continuous) on `I`, and `‖g‖, ‖g1‖, ‖g2‖ ≤ K` there.
Closure under real scalar multiplication (products), sums, reciprocals and square roots of functions bounded below, and
composition.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.SignUncertainty.CtOsc

/-- Two derivatives with explicit sup bounds on `I`. -/
structure D2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ) (g g1 g2 : ℝ → E) (K : ℝ) : Prop where
  d1 : ∀ y ∈ I, HasDerivAt g (g1 y) y
  d2 : ∀ y ∈ I, HasDerivAt g1 (g2 y) y
  c2 : ContinuousOn g2 I
  K0 : 0 ≤ K
  b0 : ∀ y ∈ I, ‖g y‖ ≤ K
  b1 : ∀ y ∈ I, ‖g1 y‖ ≤ K
  b2 : ∀ y ∈ I, ‖g2 y‖ ≤ K

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : Set ℝ}

lemma D2.mono {g g1 g2 : ℝ → E} {K K' : ℝ} (h : D2 I g g1 g2 K) (hK : K ≤ K') : D2 I g g1 g2 K' where
  d1 := h.d1
  d2 := h.d2
  c2 := h.c2
  K0 := h.K0.trans hK
  b0 y hy := (h.b0 y hy).trans hK
  b1 y hy := (h.b1 y hy).trans hK
  b2 y hy := (h.b2 y hy).trans hK

lemma D2.cont0 {g g1 g2 : ℝ → E} {K : ℝ} (h : D2 I g g1 g2 K) : ContinuousOn g I :=
  fun y hy => (h.d1 y hy).continuousAt.continuousWithinAt

lemma D2.cont1 {g g1 g2 : ℝ → E} {K : ℝ} (h : D2 I g g1 g2 K) : ContinuousOn g1 I :=
  fun y hy => (h.d2 y hy).continuousAt.continuousWithinAt

lemma nsm {x : ℝ} {v : E} {A B : ℝ} (hx : |x| ≤ A) (hv : ‖v‖ ≤ B) : ‖x • v‖ ≤ A * B := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul hx hv (norm_nonneg _) ((abs_nonneg _).trans hx)

lemma D2.contDiffOn (hI : IsOpen I) {g g1 g2 : ℝ → E} {K : ℝ} (h : D2 I g g1 g2 K) : ContDiffOn ℝ 2 g I := by
  have h2 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h2, contDiffOn_succ_iff_deriv_of_isOpen hI]
  refine ⟨fun y hy => (h.d1 y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  have h1 : ContDiffOn ℝ 1 g1 I := by
    have h1' : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
    rw [h1', contDiffOn_succ_iff_deriv_of_isOpen hI]
    refine ⟨fun y hy => (h.d2 y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact h.c2.congr (fun y hy => (h.d2 y hy).deriv)
  exact h1.congr (fun y hy => (h.d1 y hy).deriv)

lemma D2.iteratedDeriv_le (hI : IsOpen I) {g g1 g2 : ℝ → E} {K : ℝ} (h : D2 I g g1 g2 K) {x : ℝ} (hx : x ∈ I) :
    ∀ j ≤ 2, ‖iteratedDeriv j g x‖ ≤ K := by
  intro j hj
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · simpa using h.b0 x hx
  · simpa [iteratedDeriv_one, (h.d1 x hx).deriv] using h.b1 x hx
  · have hev : deriv g =ᶠ[𝓝 x] g1 := by
      filter_upwards [hI.mem_nhds hx] with y hy using (h.d1 y hy).deriv
    have : iteratedDeriv 2 g x = g2 x := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq, (h.d2 x hx).deriv]
    rw [this]; exact h.b2 x hx

/-- Product with a real function. -/
lemma D2.smul {a a1 a2 : ℝ → ℝ} {g g1 g2 : ℝ → E} {Ka Kg : ℝ} (ha : D2 I a a1 a2 Ka) (hg : D2 I g g1 g2 Kg) :
    D2 I (fun y => a y • g y) (fun y => a y • g1 y + a1 y • g y)
      (fun y => (a y • g2 y + a1 y • g1 y) + (a1 y • g1 y + a2 y • g y)) (4 * (Ka * Kg)) where
  d1 y hy := (ha.d1 y hy).smul (hg.d1 y hy)
  d2 y hy := ((ha.d1 y hy).smul (hg.d2 y hy)).add ((ha.d2 y hy).smul (hg.d1 y hy))
  c2 := by
    have h0 := ha.cont0
    have h1 := ha.cont1
    exact ((h0.smul hg.c2).add (h1.smul hg.cont1)).add ((h1.smul hg.cont1).add (ha.c2.smul hg.cont0))
  K0 := by have := ha.K0; have := hg.K0; positivity
  b0 y hy := by
    have := nsm (A := Ka) (B := Kg) (by simpa using ha.b0 y hy) (hg.b0 y hy)
    have h2 : 0 ≤ Ka * Kg := mul_nonneg ha.K0 hg.K0
    linarith
  b1 y hy := by
    have h1 := nsm (A := Ka) (B := Kg) (by simpa using ha.b0 y hy) (hg.b1 y hy)
    have h2 := nsm (A := Ka) (B := Kg) (by simpa using ha.b1 y hy) (hg.b0 y hy)
    have h3 : 0 ≤ Ka * Kg := mul_nonneg ha.K0 hg.K0
    exact (norm_add_le _ _).trans (by linarith)
  b2 y hy := by
    have h1 := nsm (A := Ka) (B := Kg) (by simpa using ha.b0 y hy) (hg.b2 y hy)
    have h2 := nsm (A := Ka) (B := Kg) (by simpa using ha.b1 y hy) (hg.b1 y hy)
    have h3 := nsm (A := Ka) (B := Kg) (by simpa using ha.b2 y hy) (hg.b0 y hy)
    have h4 : 0 ≤ Ka * Kg := mul_nonneg ha.K0 hg.K0
    refine (norm_add_le _ _).trans ?_
    have e1 := norm_add_le (a y • g2 y) (a1 y • g1 y)
    have e2 := norm_add_le (a1 y • g1 y) (a2 y • g y)
    linarith

lemma D2.add {g g1 g2 h h1 h2 : ℝ → E} {K K' : ℝ} (hg : D2 I g g1 g2 K) (hh : D2 I h h1 h2 K') :
    D2 I (fun y => g y + h y) (fun y => g1 y + h1 y) (fun y => g2 y + h2 y) (K + K') where
  d1 y hy := (hg.d1 y hy).add (hh.d1 y hy)
  d2 y hy := (hg.d2 y hy).add (hh.d2 y hy)
  c2 := hg.c2.add hh.c2
  K0 := add_nonneg hg.K0 hh.K0
  b0 y hy := (norm_add_le _ _).trans (add_le_add (hg.b0 y hy) (hh.b0 y hy))
  b1 y hy := (norm_add_le _ _).trans (add_le_add (hg.b1 y hy) (hh.b1 y hy))
  b2 y hy := (norm_add_le _ _).trans (add_le_add (hg.b2 y hy) (hh.b2 y hy))

/-- Composition. -/
lemma D2.comp {J : Set ℝ} {F F1 F2 : ℝ → E} {t t1 t2 : ℝ → ℝ} {KF Kt : ℝ} (hF : D2 J F F1 F2 KF)
    (ht : D2 I t t1 t2 Kt) (hmaps : ∀ y ∈ I, t y ∈ J) :
    D2 I (fun y => F (t y)) (fun y => t1 y • F1 (t y))
      (fun y => t1 y • (t1 y • F2 (t y)) + t2 y • F1 (t y)) (Kt * (Kt * KF) + 2 * (Kt * KF) + KF) where
  d1 y hy := (hF.d1 (t y) (hmaps y hy)).scomp y (ht.d1 y hy)
  d2 y hy := (ht.d2 y hy).smul ((hF.d2 (t y) (hmaps y hy)).scomp y (ht.d1 y hy))
  c2 := by
    have hc1 : ContinuousOn (fun y => F1 (t y)) I := hF.cont1.comp ht.cont0 hmaps
    have hc2 : ContinuousOn (fun y => F2 (t y)) I := hF.c2.comp ht.cont0 hmaps
    exact (ht.cont1.smul (ht.cont1.smul hc2)).add (ht.c2.smul hc1)
  K0 := by have := hF.K0; have := ht.K0; positivity
  b0 y hy := by
    have := hF.b0 (t y) (hmaps y hy)
    have := ht.K0; have := hF.K0
    nlinarith [mul_nonneg ‹0 ≤ Kt› ‹0 ≤ KF›, mul_nonneg ‹0 ≤ Kt› (mul_nonneg ‹0 ≤ Kt› ‹0 ≤ KF›)]
  b1 y hy := by
    have h1 := nsm (A := Kt) (B := KF) (by simpa using ht.b1 y hy) (hF.b1 (t y) (hmaps y hy))
    have := ht.K0; have := hF.K0
    nlinarith [mul_nonneg ‹0 ≤ Kt› ‹0 ≤ KF›, mul_nonneg ‹0 ≤ Kt› (mul_nonneg ‹0 ≤ Kt› ‹0 ≤ KF›)]
  b2 y hy := by
    have h1 := nsm (A := Kt) (B := KF) (by simpa using ht.b1 y hy) (hF.b2 (t y) (hmaps y hy))
    have h2 := nsm (A := Kt) (B := Kt * KF) (by simpa using ht.b1 y hy) h1
    have h3 := nsm (A := Kt) (B := KF) (by simpa using ht.b2 y hy) (hF.b1 (t y) (hmaps y hy))
    have := ht.K0; have := hF.K0
    refine (norm_add_le _ _).trans ?_
    nlinarith [mul_nonneg ‹0 ≤ Kt› ‹0 ≤ KF›]

end

section Real
variable {I : Set ℝ}

/-- Reciprocal of a function bounded below by `m > 0`. -/
lemma D2.inv {a a1 a2 : ℝ → ℝ} {K m : ℝ} (ha : D2 I a a1 a2 K) (hm : 0 < m) (hlo : ∀ y ∈ I, m ≤ a y) :
    D2 I (fun y => (a y)⁻¹) (fun y => -a1 y * ((a y)⁻¹) ^ 2)
      (fun y => -a2 y * ((a y)⁻¹) ^ 2 + 2 * (a1 y) ^ 2 * ((a y)⁻¹) ^ 3)
      (m⁻¹ + K * m⁻¹ ^ 2 + 2 * (K ^ 2 * m⁻¹ ^ 3)) where
  d1 y hy := by
    have hne : a y ≠ 0 := ne_of_gt (lt_of_lt_of_le hm (hlo y hy))
    refine ((ha.d1 y hy).inv hne).congr_deriv ?_
    field_simp
  d2 y hy := by
    have hne : a y ≠ 0 := ne_of_gt (lt_of_lt_of_le hm (hlo y hy))
    have hg : HasDerivAt (fun y => (a y)⁻¹) (-a1 y * ((a y)⁻¹) ^ 2) y := by
      refine ((ha.d1 y hy).inv hne).congr_deriv ?_
      field_simp
    have := ((ha.d2 y hy).neg.mul (hg.pow 2))
    refine this.congr_deriv ?_
    norm_num
    ring
  c2 := by
    have hne : ∀ y ∈ I, a y ≠ 0 := fun y hy => ne_of_gt (lt_of_lt_of_le hm (hlo y hy))
    have hi : ContinuousOn (fun y => (a y)⁻¹) I := ha.cont0.inv₀ hne
    exact (ha.c2.neg.mul (hi.pow 2)).add ((continuousOn_const.mul ((ha.cont1.pow 2))).mul (hi.pow 3))
  K0 := by
    have := ha.K0
    have : 0 < m⁻¹ := inv_pos.mpr hm
    positivity
  b0 y hy := by
    have h0 : 0 < (a y)⁻¹ := inv_pos.mpr (lt_of_lt_of_le hm (hlo y hy))
    have h1 : (a y)⁻¹ ≤ m⁻¹ := inv_anti₀ hm (hlo y hy)
    have := ha.K0
    have h3 : 0 < m⁻¹ := inv_pos.mpr hm
    rw [Real.norm_eq_abs, abs_of_pos h0]
    nlinarith [mul_nonneg ‹0 ≤ K› (sq_nonneg m⁻¹), mul_nonneg (sq_nonneg K) (pow_nonneg h3.le 3)]
  b1 y hy := by
    have h0 : 0 < (a y)⁻¹ := inv_pos.mpr (lt_of_lt_of_le hm (hlo y hy))
    have h1 : (a y)⁻¹ ≤ m⁻¹ := inv_anti₀ hm (hlo y hy)
    have hK := ha.K0
    have h3 : 0 < m⁻¹ := inv_pos.mpr hm
    have hb := ha.b1 y hy
    rw [Real.norm_eq_abs] at hb ⊢
    rw [abs_mul, abs_neg, abs_pow, abs_of_pos h0]
    have : |a1 y| * (a y)⁻¹ ^ 2 ≤ K * m⁻¹ ^ 2 :=
      mul_le_mul hb (pow_le_pow_left₀ h0.le h1 2) (by positivity) hK
    nlinarith [pow_nonneg h3.le 1, mul_nonneg (sq_nonneg K) (pow_nonneg h3.le 3)]
  b2 y hy := by
    have h0 : 0 < (a y)⁻¹ := inv_pos.mpr (lt_of_lt_of_le hm (hlo y hy))
    have h1 : (a y)⁻¹ ≤ m⁻¹ := inv_anti₀ hm (hlo y hy)
    have hK := ha.K0
    have h3 : 0 < m⁻¹ := inv_pos.mpr hm
    have hb1 := ha.b1 y hy
    have hb2 := ha.b2 y hy
    rw [Real.norm_eq_abs] at hb1 hb2 ⊢
    have e1 : |-a2 y * (a y)⁻¹ ^ 2| ≤ K * m⁻¹ ^ 2 := by
      rw [abs_mul, abs_neg, abs_pow, abs_of_pos h0]
      exact mul_le_mul hb2 (pow_le_pow_left₀ h0.le h1 2) (by positivity) hK
    have e2 : |2 * a1 y ^ 2 * (a y)⁻¹ ^ 3| ≤ 2 * (K ^ 2 * m⁻¹ ^ 3) := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos h0]
      have : |a1 y| ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb1 2
      have h4 : (a y)⁻¹ ^ 3 ≤ m⁻¹ ^ 3 := pow_le_pow_left₀ h0.le h1 3
      have := mul_le_mul this h4 (by positivity) (by positivity)
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have := (abs_add_le _ _).trans (add_le_add e1 e2)
    nlinarith [pow_nonneg h3.le 1]


lemma div_two_g_le {x K g μ : ℝ} (hx : |x| ≤ K) (hμ : 0 < μ) (hg : μ ≤ g) : |x / (2 * g)| ≤ K * μ⁻¹ := by
  have hg0 : 0 < g := lt_of_lt_of_le hμ hg
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * g), div_le_iff₀ (by positivity)]
  have h1 : 1 ≤ μ⁻¹ * g := by rw [← div_eq_inv_mul, le_div_iff₀ hμ]; linarith
  have hK : 0 ≤ K := (abs_nonneg _).trans hx
  nlinarith [mul_nonneg hK (sub_nonneg.2 h1)]

lemma sq_div_le {x K g μ : ℝ} (hx : |x| ≤ K) (hμ : 0 < μ) (hg : μ ≤ g) : |x ^ 2 / (4 * g ^ 3)| ≤ K ^ 2 * μ⁻¹ ^ 3 := by
  have hg0 : 0 < g := lt_of_lt_of_le hμ hg
  rw [abs_div, abs_pow, abs_of_pos (by positivity : 0 < 4 * g ^ 3), div_le_iff₀ (by positivity)]
  have h1 : 1 ≤ μ⁻¹ * g := by rw [← div_eq_inv_mul, le_div_iff₀ hμ]; linarith
  have h3 : 1 ≤ μ⁻¹ ^ 3 * g ^ 3 := by rw [← mul_pow]; exact one_le_pow₀ h1
  have hx2 : |x| ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
  nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.2 h3)]

/-- Square root of a function bounded below by `m > 0` and above by `K`. -/
lemma D2.sqrt {a a1 a2 : ℝ → ℝ} {K m : ℝ} (ha : D2 I a a1 a2 K) (hm : 0 < m) (hlo : ∀ y ∈ I, m ≤ a y) :
    D2 I (fun y => Real.sqrt (a y)) (fun y => a1 y / (2 * Real.sqrt (a y)))
      (fun y => a2 y / (2 * Real.sqrt (a y)) - (a1 y) ^ 2 / (4 * Real.sqrt (a y) ^ 3))
      ((K + 1) + K * (Real.sqrt m)⁻¹ + K ^ 2 * (Real.sqrt m)⁻¹ ^ 3) where
  d1 y hy := (ha.d1 y hy).sqrt (ne_of_gt (lt_of_lt_of_le hm (hlo y hy)))
  d2 y hy := by
    have hpos : 0 < a y := lt_of_lt_of_le hm (hlo y hy)
    have hg : HasDerivAt (fun y => Real.sqrt (a y)) (a1 y / (2 * Real.sqrt (a y))) y :=
      (ha.d1 y hy).sqrt (ne_of_gt hpos)
    have hs : 0 < Real.sqrt (a y) := Real.sqrt_pos.mpr hpos
    have := (ha.d2 y hy).div (hg.const_mul 2) (by positivity)
    refine this.congr_deriv ?_
    field_simp
    ring
  c2 := by
    have hne : ∀ y ∈ I, 0 < a y := fun y hy => lt_of_lt_of_le hm (hlo y hy)
    have hs : ContinuousOn (fun y => Real.sqrt (a y)) I := Real.continuous_sqrt.comp_continuousOn ha.cont0
    have hsne : ∀ y ∈ I, Real.sqrt (a y) ≠ 0 := fun y hy => (Real.sqrt_pos.mpr (hne y hy)).ne'
    refine ContinuousOn.sub (ha.c2.div (continuousOn_const.mul hs) (fun y hy => by have := hsne y hy; positivity))
      ((ha.cont1.pow 2).div (continuousOn_const.mul (hs.pow 3)) (fun y hy => by have := hsne y hy; positivity))
  K0 := by
    have := ha.K0
    have : 0 ≤ (Real.sqrt m)⁻¹ := by positivity
    positivity
  b0 y hy := by
    have hK := ha.K0
    have hpos : 0 < a y := lt_of_lt_of_le hm (hlo y hy)
    have hb := ha.b0 y hy
    rw [Real.norm_eq_abs] at hb
    have hle : a y ≤ K := (le_abs_self _).trans hb
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : Real.sqrt (a y) ≤ K + 1 := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have : 0 ≤ (Real.sqrt m)⁻¹ := by positivity
    nlinarith [mul_nonneg hK this, mul_nonneg (sq_nonneg K) (pow_nonneg this 3)]
  b1 y hy := by
    have hK := ha.K0
    have hμ : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
    have hg : Real.sqrt m ≤ Real.sqrt (a y) := Real.sqrt_le_sqrt (hlo y hy)
    have hb := ha.b1 y hy
    rw [Real.norm_eq_abs] at hb
    rw [Real.norm_eq_abs]
    have := div_two_g_le hb hμ hg
    have h2 : 0 ≤ (Real.sqrt m)⁻¹ := by positivity
    nlinarith [mul_nonneg (sq_nonneg K) (pow_nonneg h2 3)]
  b2 y hy := by
    have hK := ha.K0
    have hμ : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
    have hg : Real.sqrt m ≤ Real.sqrt (a y) := Real.sqrt_le_sqrt (hlo y hy)
    have hb1 := ha.b1 y hy
    have hb2 := ha.b2 y hy
    rw [Real.norm_eq_abs] at hb1 hb2
    rw [Real.norm_eq_abs]
    have e1 := div_two_g_le hb2 hμ hg
    have e2 := sq_div_le hb1 hμ hg
    have := (abs_sub _ _).trans (add_le_add e1 e2)
    have h2 : 0 ≤ (Real.sqrt m)⁻¹ := by positivity
    nlinarith

end Real

end FormalResearch.SignUncertainty.CtOsc
