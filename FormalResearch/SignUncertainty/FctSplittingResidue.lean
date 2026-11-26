/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Residue formula on a rectangle (the contour shift behind `fct:splitting` (2))

Paper I (`constant_terms_five.tex`), proof of `fct:splitting` (2): "shifting the contour ... with residue `F_-(ζ) - F_+(ζ) = K_sp(ζ,ζ)F(ζ)`".  Mathlib has Cauchy's
theorem for rectangles (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) but not the residue at an interior point.

* `rectInt g a b y0 y1`: the counter-clockwise boundary integral of `g` over `[a,b] × [y0,y1]`, in the shape of Mathlib's rectangle theorems.
* `rectInt_inv_sub`: `∮ dt/(t-ζ) = 2πi` for `ζ` in the open rectangle.  Proof: the primitives `log(-i(t-ζ))` (valid above `ζ`, off the downward ray) and `log(i(t-ζ))`
  (valid below `ζ`) give the four edge integrals; their sum is `[up - dn](L₀) - [up - dn](R₁) = iπ + iπ`.
* `rectInt_residue`: for `h` holomorphic near the closed rectangle and `ζ` in its interior, `∮ h(t)/(t-ζ) dt = 2πi h(ζ)` (`dslope` removes the pole).
* `rectInt_eq_zero_of_not_mem`: `∮ h(t)/(t-ζ) dt = 0` when `ζ` is outside the closed rectangle.

Class: proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The counter-clockwise boundary integral of `g` over `[a,b] × [y0,y1]`. -/
noncomputable def rectInt (g : ℂ → ℂ) (a b y0 y1 : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, g ((x : ℂ) + y0 * Complex.I)) - (∫ x : ℝ in a..b, g ((x : ℂ) + y1 * Complex.I)) +
    Complex.I * (∫ y : ℝ in y0..y1, g ((b : ℂ) + y * Complex.I)) - Complex.I * (∫ y : ℝ in y0..y1, g ((a : ℂ) + y * Complex.I))

/-- The closed rectangle `[a,b] × [y0,y1]` (`a ≤ b`, `y0 ≤ y1` or reversed). -/
def rectSet (a b y0 y1 : ℝ) : Set ℂ := {t : ℂ | t.re ∈ uIcc a b ∧ t.im ∈ uIcc y0 y1}

/-- The boundary of the rectangle. -/
def rectEdge (a b y0 y1 : ℝ) : Set ℂ := {t : ℂ | t ∈ rectSet a b y0 y1 ∧ (t.im = y0 ∨ t.im = y1 ∨ t.re = a ∨ t.re = b)}

lemma rectEdge_h {a b y0 y1 y : ℝ} (hy : y = y0 ∨ y = y1) {x : ℝ} (hx : x ∈ uIcc a b) (hy' : y ∈ uIcc y0 y1) :
    ((x : ℂ) + y * Complex.I) ∈ rectEdge a b y0 y1 := by
  refine ⟨⟨by simpa, by simpa⟩, ?_⟩
  rcases hy with h | h
  · left; simpa using h
  · right; left; simpa using h

lemma rectEdge_v {a b y0 y1 x : ℝ} (hx : x = a ∨ x = b) {y : ℝ} (hy : y ∈ uIcc y0 y1) (hx' : x ∈ uIcc a b) :
    ((x : ℂ) + y * Complex.I) ∈ rectEdge a b y0 y1 := by
  refine ⟨⟨by simpa, by simpa⟩, ?_⟩
  rcases hx with h | h
  · right; right; left; simpa using h
  · right; right; right; simpa using h

lemma rectInt_add {g1 g2 : ℂ → ℂ} {a b y0 y1 : ℝ} (h1 : ContinuousOn g1 (rectEdge a b y0 y1))
    (h2 : ContinuousOn g2 (rectEdge a b y0 y1)) :
    rectInt (fun t => g1 t + g2 t) a b y0 y1 = rectInt g1 a b y0 y1 + rectInt g2 a b y0 y1 := by
  have hb : b ∈ uIcc a b := right_mem_uIcc
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hy0 : y0 ∈ uIcc y0 y1 := left_mem_uIcc
  have hy1 : y1 ∈ uIcc y0 y1 := right_mem_uIcc
  have hH : ∀ {g : ℂ → ℂ}, ContinuousOn g (rectEdge a b y0 y1) → ∀ y : ℝ, (y = y0 ∨ y = y1) → y ∈ uIcc y0 y1 →
      IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + y * Complex.I)) volume a b := fun {g} hg y hy hy' =>
    (hg.comp (by fun_prop) fun x hx => rectEdge_h hy hx hy').intervalIntegrable
  have hV : ∀ {g : ℂ → ℂ}, ContinuousOn g (rectEdge a b y0 y1) → ∀ x : ℝ, (x = a ∨ x = b) → x ∈ uIcc a b →
      IntervalIntegrable (fun y : ℝ => g ((x : ℂ) + y * Complex.I)) volume y0 y1 := fun {g} hg x hx hx' =>
    (hg.comp (by fun_prop) fun y hy => rectEdge_v hx hy hx').intervalIntegrable
  unfold rectInt
  rw [intervalIntegral.integral_add (hH h1 _ (Or.inl rfl) hy0) (hH h2 _ (Or.inl rfl) hy0),
    intervalIntegral.integral_add (hH h1 _ (Or.inr rfl) hy1) (hH h2 _ (Or.inr rfl) hy1),
    intervalIntegral.integral_add (hV h1 _ (Or.inr rfl) hb) (hV h2 _ (Or.inr rfl) hb),
    intervalIntegral.integral_add (hV h1 _ (Or.inl rfl) ha) (hV h2 _ (Or.inl rfl) ha)]
  ring

lemma rectInt_congr {g1 g2 : ℂ → ℂ} {a b y0 y1 : ℝ} (h : ∀ t ∈ rectEdge a b y0 y1, g1 t = g2 t) :
    rectInt g1 a b y0 y1 = rectInt g2 a b y0 y1 := by
  have hy0 : y0 ∈ uIcc y0 y1 := left_mem_uIcc
  have hy1 : y1 ∈ uIcc y0 y1 := right_mem_uIcc
  unfold rectInt
  have e1 : ∫ x : ℝ in a..b, g1 ((x : ℂ) + y0 * Complex.I) = ∫ x : ℝ in a..b, g2 ((x : ℂ) + y0 * Complex.I) :=
    intervalIntegral.integral_congr fun x hx => h _ (rectEdge_h (Or.inl rfl) hx hy0)
  have e2 : ∫ x : ℝ in a..b, g1 ((x : ℂ) + y1 * Complex.I) = ∫ x : ℝ in a..b, g2 ((x : ℂ) + y1 * Complex.I) :=
    intervalIntegral.integral_congr fun x hx => h _ (rectEdge_h (Or.inr rfl) hx hy1)
  have e3 : ∫ y : ℝ in y0..y1, g1 ((b : ℂ) + y * Complex.I) = ∫ y : ℝ in y0..y1, g2 ((b : ℂ) + y * Complex.I) :=
    intervalIntegral.integral_congr fun y hy => h _ (rectEdge_v (Or.inr rfl) hy right_mem_uIcc)
  have e4 : ∫ y : ℝ in y0..y1, g1 ((a : ℂ) + y * Complex.I) = ∫ y : ℝ in y0..y1, g2 ((a : ℂ) + y * Complex.I) :=
    intervalIntegral.integral_congr fun y hy => h _ (rectEdge_v (Or.inl rfl) hy left_mem_uIcc)
  rw [e1, e2, e3, e4]

lemma rectInt_const_mul (k : ℂ) (g : ℂ → ℂ) (a b y0 y1 : ℝ) :
    rectInt (fun t => k * g t) a b y0 y1 = k * rectInt g a b y0 y1 := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Cauchy's theorem on a rectangle in the form `rectInt g = 0`. -/
lemma rectInt_eq_zero {g : ℂ → ℂ} {a b y0 y1 : ℝ} (hd : DifferentiableOn ℂ g (rectSet a b y0 y1)) :
    rectInt g a b y0 y1 = 0 := by
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨a, y0⟩ ⟨b, y1⟩
    hd
  simpa [rectInt, smul_eq_mul] using this

/-! ### The winding integral `∮ dt/(t-ζ)` -/

/-- `log (c (t - ζ))`, a primitive of `1/(t-ζ)` away from the ray `c (t - ζ) ∈ (-∞, 0]`. -/
noncomputable def logRot (c ζ t : ℂ) : ℂ := Complex.log (c * (t - ζ))

lemma logRot_hasDerivAt {c ζ t : ℂ} (hc : c ≠ 0) (hs : c * (t - ζ) ∈ Complex.slitPlane) :
    HasDerivAt (logRot c ζ) (1 / (t - ζ)) t := by
  have h1 : HasDerivAt (fun z : ℂ => c * (z - ζ)) c t := by
    simpa using ((hasDerivAt_id t).sub_const ζ).const_mul c
  have h2 := h1.clog hs
  have hz : t - ζ ≠ 0 := fun h => by
    rw [h, mul_zero] at hs
    exact Complex.slitPlane_ne_zero hs rfl
  have : c / (c * (t - ζ)) = 1 / (t - ζ) := by field_simp
  rw [this] at h2
  exact h2

lemma slit_up {u : ℂ} (h : 0 < u.im ∨ u.re ≠ 0) : -Complex.I * u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  rcases h with h | h
  · left; linarith
  · right; simpa using h

lemma slit_dn {u : ℂ} (h : u.im < 0 ∨ u.re ≠ 0) : Complex.I * u ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rcases h with h | h
  · left; linarith
  · right; simpa using h

lemma ne_zero_of_slit {z : ℂ} (hz : z ∈ Complex.slitPlane) : z ≠ 0 := Complex.slitPlane_ne_zero hz

lemma logRot_horiz {c ζ : ℂ} (hc : c ≠ 0) {a b y : ℝ}
    (hs : ∀ x ∈ uIcc a b, c * (((x : ℂ) + y * Complex.I) - ζ) ∈ Complex.slitPlane) :
    ∫ x : ℝ in a..b, 1 / (((x : ℂ) + y * Complex.I) - ζ) =
      logRot c ζ ((b : ℂ) + y * Complex.I) - logRot c ζ ((a : ℂ) + y * Complex.I) := by
  refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => logRot c ζ ((x : ℂ) + y * Complex.I))
    (f' := fun x : ℝ => 1 / (((x : ℂ) + y * Complex.I) - ζ)) (fun x hx => ?_) ?_
  · have h := logRot_hasDerivAt hc (hs x hx)
    have h2 : HasDerivAt (fun z : ℂ => z + (y : ℂ) * Complex.I) 1 (x : ℂ) := by
      simpa using (hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * Complex.I)
    have h3 := h.comp (x : ℂ) h2
    have := HasDerivAt.comp_ofReal (e := fun z : ℂ => logRot c ζ (z + y * Complex.I)) (z := x) h3
    simpa using this
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div (by fun_prop) fun x hx => ?_
    intro h0
    apply ne_zero_of_slit (hs x hx)
    rw [h0, mul_zero]

lemma logRot_vert {c ζ : ℂ} (hc : c ≠ 0) {x0 y0 y1 : ℝ}
    (hs : ∀ y ∈ uIcc y0 y1, c * (((x0 : ℂ) + y * Complex.I) - ζ) ∈ Complex.slitPlane) :
    Complex.I * ∫ y : ℝ in y0..y1, 1 / (((x0 : ℂ) + y * Complex.I) - ζ) =
      logRot c ζ ((x0 : ℂ) + y1 * Complex.I) - logRot c ζ ((x0 : ℂ) + y0 * Complex.I) := by
  rw [← intervalIntegral.integral_const_mul]
  have hfin : ∀ y ∈ uIcc y0 y1, HasDerivAt (fun y : ℝ => logRot c ζ ((x0 : ℂ) + y * Complex.I))
      (Complex.I * (1 / (((x0 : ℂ) + y * Complex.I) - ζ))) y := by
    intro y hy
    have h := logRot_hasDerivAt hc (hs y hy)
    have h2 : HasDerivAt (fun z : ℂ => (x0 : ℂ) + z * Complex.I) Complex.I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (x0 : ℂ)
    have h3 := h.comp (y : ℂ) h2
    have h4 := HasDerivAt.comp_ofReal (e := fun z : ℂ => logRot c ζ ((x0 : ℂ) + z * Complex.I)) (z := y) h3
    simpa [mul_comm] using h4
  refine integral_eq_sub_of_hasDerivAt hfin ?_
  refine ContinuousOn.intervalIntegrable ?_
  refine continuousOn_const.mul (continuousOn_const.div (by fun_prop) fun y hy => ?_)
  intro h0
  apply ne_zero_of_slit (hs y hy)
  rw [h0, mul_zero]

lemma log_neg_sub_log_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) - Complex.log z = -(π * Complex.I) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]

lemma log_neg_sub_log_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) - Complex.log z = π * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]

/-- **The winding integral**: `∮ dt/(t-ζ) = 2πi` over `[a,b] × [y0,y1]` for `ζ` in the open rectangle. -/
theorem rectInt_inv_sub {a b y0 y1 : ℝ} {ζ : ℂ} (ha : a < ζ.re) (hb : ζ.re < b) (h0 : y0 < ζ.im) (h1 : ζ.im < y1) :
    rectInt (fun t => 1 / (t - ζ)) a b y0 y1 = 2 * π * Complex.I := by
  have hab : a ≤ b := by linarith
  have hy01 : y0 ≤ y1 := by linarith
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hnI : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr hI
  -- the six pieces
  have hbot : ∫ x : ℝ in a..b, 1 / (((x : ℂ) + y0 * Complex.I) - ζ) =
      logRot Complex.I ζ ((b : ℂ) + y0 * Complex.I) - logRot Complex.I ζ ((a : ℂ) + y0 * Complex.I) :=
    logRot_horiz hI fun x _ => slit_dn (Or.inl (by simp; linarith))
  have htop : ∫ x : ℝ in a..b, 1 / (((x : ℂ) + y1 * Complex.I) - ζ) =
      logRot (-Complex.I) ζ ((b : ℂ) + y1 * Complex.I) - logRot (-Complex.I) ζ ((a : ℂ) + y1 * Complex.I) :=
    logRot_horiz hnI fun x _ => slit_up (Or.inl (by simp; linarith))
  have hright : Complex.I * ∫ y : ℝ in y0..y1, 1 / (((b : ℂ) + y * Complex.I) - ζ) =
      logRot Complex.I ζ ((b : ℂ) + y1 * Complex.I) - logRot Complex.I ζ ((b : ℂ) + y0 * Complex.I) :=
    logRot_vert hI fun y _ => slit_dn (Or.inr (by simp; linarith))
  have hleft : Complex.I * ∫ y : ℝ in y0..y1, 1 / (((a : ℂ) + y * Complex.I) - ζ) =
      logRot (-Complex.I) ζ ((a : ℂ) + y1 * Complex.I) - logRot (-Complex.I) ζ ((a : ℂ) + y0 * Complex.I) :=
    logRot_vert hnI fun y _ => slit_up (Or.inr (by simp; linarith))
  unfold rectInt
  rw [hbot, htop, hright, hleft]
  -- `up - dn` at the corners `L₀ = a + y0 i` and `R₁ = b + y1 i`
  have hL0 : logRot (-Complex.I) ζ ((a : ℂ) + y0 * Complex.I) - logRot Complex.I ζ ((a : ℂ) + y0 * Complex.I) =
      π * Complex.I := by
    unfold logRot
    rw [show -Complex.I * (((a : ℂ) + y0 * Complex.I) - ζ) = -(Complex.I * (((a : ℂ) + y0 * Complex.I) - ζ)) by ring]
    exact log_neg_sub_log_of_im_neg (by simp; linarith)
  have hR1 : logRot (-Complex.I) ζ ((b : ℂ) + y1 * Complex.I) - logRot Complex.I ζ ((b : ℂ) + y1 * Complex.I) =
      -(π * Complex.I) := by
    unfold logRot
    rw [show -Complex.I * (((b : ℂ) + y1 * Complex.I) - ζ) = -(Complex.I * (((b : ℂ) + y1 * Complex.I) - ζ)) by ring]
    exact log_neg_sub_log_of_im_pos (by simp; linarith)
  linear_combination hL0 - hR1

/-- **Residue formula on a rectangle**: `h` holomorphic on an open `U ⊇ [a,b] × [y0,y1]`, `ζ` in the open rectangle:
`∮ h(t)/(t-ζ) dt = 2πi h(ζ)`. -/
theorem rectInt_residue {h : ℂ → ℂ} {a b y0 y1 : ℝ} {ζ : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (hR : rectSet a b y0 y1 ⊆ U)
    (ha : a < ζ.re) (hb : ζ.re < b) (h0 : y0 < ζ.im) (h1 : ζ.im < y1) :
    rectInt (fun t => h t / (t - ζ)) a b y0 y1 = 2 * π * Complex.I * h ζ := by
  have hab : a ≤ b := by linarith
  have hy : y0 ≤ y1 := by linarith
  have hζR : ζ ∈ rectSet a b y0 y1 :=
    ⟨by rw [uIcc_of_le hab]; exact ⟨ha.le, hb.le⟩, by rw [uIcc_of_le hy]; exact ⟨h0.le, h1.le⟩⟩
  have hζU : ζ ∈ U := hR hζR
  have hq : DifferentiableOn ℂ (dslope h ζ) U := (Complex.differentiableOn_dslope (hU.mem_nhds hζU)).mpr hh
  have hne : ∀ t ∈ rectEdge a b y0 y1, t ≠ ζ := by
    rintro t ⟨-, ht⟩ rfl
    rcases ht with h | h | h | h <;> linarith
  have hEU : rectEdge a b y0 y1 ⊆ U := fun t ht => hR ht.1
  have hsplit : ∀ t ∈ rectEdge a b y0 y1, h t / (t - ζ) = dslope h ζ t + h ζ * (1 / (t - ζ)) := by
    intro t ht
    have hz : t - ζ ≠ 0 := sub_ne_zero.mpr (hne t ht)
    rw [dslope_of_ne _ (hne t ht), slope_def_field]
    field_simp
    ring
  have hc2 : ContinuousOn (fun t : ℂ => h ζ * (1 / (t - ζ))) (rectEdge a b y0 y1) :=
    continuousOn_const.mul (continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      fun t ht => sub_ne_zero.mpr (hne t ht))
  rw [rectInt_congr hsplit, rectInt_add (g1 := dslope h ζ) (g2 := fun t : ℂ => h ζ * (1 / (t - ζ)))
    (hq.continuousOn.mono hEU) hc2, rectInt_eq_zero (hq.mono hR), rectInt_const_mul (h ζ) (fun t : ℂ => 1 / (t - ζ)),
    rectInt_inv_sub ha hb h0 h1]
  ring

/-- **Cauchy's theorem for `h(t)/(t-ζ)`** when `ζ` is outside the closed rectangle. -/
theorem rectInt_eq_zero_of_not_mem {h : ℂ → ℂ} {a b y0 y1 : ℝ} {ζ : ℂ} {U : Set ℂ}
    (hh : DifferentiableOn ℂ h U) (hR : rectSet a b y0 y1 ⊆ U) (hζ : ζ ∉ rectSet a b y0 y1) :
    rectInt (fun t => h t / (t - ζ)) a b y0 y1 = 0 := by
  refine rectInt_eq_zero ((hh.mono hR).div (differentiableOn_id.sub (differentiableOn_const _)) fun t ht => ?_)
  exact sub_ne_zero.mpr fun h => hζ (h ▸ ht)


/-- info: 'FormalResearch.SignUncertainty.rectInt_inv_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rectInt_inv_sub

/-- info: 'FormalResearch.SignUncertainty.rectInt_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rectInt_residue

/-- info: 'FormalResearch.SignUncertainty.rectInt_eq_zero_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rectInt_eq_zero_of_not_mem

end FormalResearch.SignUncertainty
