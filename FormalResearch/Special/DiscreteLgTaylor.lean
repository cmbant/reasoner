module

public import Mathlib

/-!
# Discrete Liouville-Green, M1: Taylor remainders with explicit constants (Airy-free)

Elementary real-variable estimates for the bulk Liouville-Green layer `DiscreteLg*`:

* `dlg_lip`: a function whose derivative is bounded by `B` on a convex set is `B`-Lipschitz there;
* `dlg_taylor2`: `|f y - f x - (y-x) f'(x)| ≤ M (y-x)²` if `|f''| ≤ M` on a convex set containing `x, y`;
* `dlg_taylor3`: `|Θ y - Θ x - (y-x) Θ'(x) - (y-x)² Θ''(x)/2| ≤ M |y-x|³` if `|Θ'''| ≤ M`;
* `dlg_jet_mul`, `dlg_jet_div`: first-order jets of a product and of a ratio with explicit second-order remainder.

All derivatives are given by explicit functions (`HasDerivAt`), so the statements apply to `deriv` of a `C²` function on an open
set (`dlg_hasDeriv2`).  **Claim class: proved** (no hypothesis beyond those stated).  **Not formalised:** sharp constants.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- A function with derivative bounded by `B` on a convex set is `B`-Lipschitz there. -/
lemma dlg_lip {f f' : ℝ → ℝ} {S : Set ℝ} {B : ℝ} (hS : Convex ℝ S) (hd : ∀ t ∈ S, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ S, |f' t| ≤ B) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : |f y - f x| ≤ B * |y - x| := by
  have := hS.norm_image_sub_le_of_norm_hasDerivWithin_le (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => by simpa [Real.norm_eq_abs] using hb t ht) hx hy
  simpa [Real.norm_eq_abs] using this

/-- **Taylor, order 2.**  `|f''| ≤ M` on a convex set `U` containing `x, y`. -/
lemma dlg_taylor2 {f f1 f2 : ℝ → ℝ} {U : Set ℝ} {M : ℝ} (hU : Convex ℝ U)
    (h1 : ∀ t ∈ U, HasDerivAt f (f1 t) t) (h2 : ∀ t ∈ U, HasDerivAt f1 (f2 t) t) (hM : ∀ t ∈ U, |f2 t| ≤ M)
    {x y : ℝ} (hx : x ∈ U) (hy : y ∈ U) : |f y - f x - (y - x) * f1 x| ≤ M * (y - x) ^ 2 := by
  have hseg : uIcc x y ⊆ U := hU.ordConnected.uIcc_subset hx hy
  have hc : Convex ℝ (uIcc x y) := Set.ordConnected_uIcc.convex
  have hxs : x ∈ uIcc x y := left_mem_uIcc
  have hys : y ∈ uIcc x y := right_mem_uIcc
  have hd : ∀ t ∈ uIcc x y, HasDerivAt (fun s => f s - (s - x) * f1 x) (f1 t - f1 x) t := by
    intro t ht
    have := (h1 t (hseg ht)).sub (((hasDerivAt_id t).sub_const x).mul_const (f1 x))
    convert this using 1
    · ext s; simp
    · ring
  have hb : ∀ t ∈ uIcc x y, |f1 t - f1 x| ≤ M * |y - x| := by
    intro t ht
    have := dlg_lip hc (fun s hs => h2 s (hseg hs)) (fun s hs => hM s (hseg hs)) hxs ht
    refine this.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hM x hx))
    rw [Set.mem_uIcc] at ht
    rw [abs_le]
    rcases ht with ⟨a, b⟩ | ⟨a, b⟩
    · constructor <;> cases abs_cases (y - x) <;> linarith
    · constructor <;> cases abs_cases (y - x) <;> linarith
  have := dlg_lip hc hd hb hxs hys
  simp only [sub_self, zero_mul, sub_zero] at this
  calc |f y - f x - (y - x) * f1 x| = |f y - (y - x) * f1 x - f x| := by ring_nf
    _ ≤ M * |y - x| * |y - x| := this
    _ = M * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- **Taylor, order 3**: `|Θ'''| ≤ M` (`θ = Θ'`, `θ1 = θ'`, `θ2 = θ''`). -/
lemma dlg_taylor3 {Θ θ θ1 θ2 : ℝ → ℝ} {U : Set ℝ} {M : ℝ} (hU : Convex ℝ U)
    (h0 : ∀ t ∈ U, HasDerivAt Θ (θ t) t) (h1 : ∀ t ∈ U, HasDerivAt θ (θ1 t) t)
    (h2 : ∀ t ∈ U, HasDerivAt θ1 (θ2 t) t) (hM : ∀ t ∈ U, |θ2 t| ≤ M) {x y : ℝ} (hx : x ∈ U) (hy : y ∈ U) :
    |Θ y - Θ x - (y - x) * θ x - (y - x) ^ 2 * θ1 x / 2| ≤ M * |y - x| ^ 3 := by
  have hseg : uIcc x y ⊆ U := hU.ordConnected.uIcc_subset hx hy
  have hc : Convex ℝ (uIcc x y) := Set.ordConnected_uIcc.convex
  have hxs : x ∈ uIcc x y := left_mem_uIcc
  have hys : y ∈ uIcc x y := right_mem_uIcc
  have hd : ∀ t ∈ uIcc x y, HasDerivAt (fun s => Θ s - (s - x) * θ x - (s - x) ^ 2 * θ1 x / 2)
      (θ t - θ x - (t - x) * θ1 x) t := by
    intro t ht
    have a1 := (h0 t (hseg ht)).sub (((hasDerivAt_id t).sub_const x).mul_const (θ x))
    have a2 := ((((hasDerivAt_id t).sub_const x).pow 2).mul_const (θ1 x)).div_const 2
    have := a1.sub a2
    convert this using 1
    · ext s; simp
    · simp only [id, Nat.cast_ofNat, one_mul]
      ring
  have hb : ∀ t ∈ uIcc x y, |θ t - θ x - (t - x) * θ1 x| ≤ M * |y - x| ^ 2 := by
    intro t ht
    have := dlg_taylor2 hU (fun s hs => h1 s hs) (fun s hs => h2 s hs) hM hx (hseg ht)
    refine this.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hM x hx))
    rw [← sq_abs (t - x)]
    rw [Set.mem_uIcc] at ht
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_le]
    rcases ht with ⟨a, b⟩ | ⟨a, b⟩
    · constructor <;> cases abs_cases (y - x) <;> linarith
    · constructor <;> cases abs_cases (y - x) <;> linarith
  have := dlg_lip hc hd hb hxs hys
  simp only [sub_self, zero_mul, zero_pow two_ne_zero, zero_div, sub_zero] at this
  calc |Θ y - Θ x - (y - x) * θ x - (y - x) ^ 2 * θ1 x / 2|
      = |Θ y - (y - x) * θ x - (y - x) ^ 2 * θ1 x / 2 - Θ x| := by ring_nf
    _ ≤ M * |y - x| ^ 2 * |y - x| := this
    _ = M * |y - x| ^ 3 := by ring

/-- `C²` on an open set gives the two derivative relations for `deriv`. -/
lemma dlg_hasDeriv2 {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    (∀ t ∈ U, HasDerivAt f (deriv f t) t) ∧ (∀ t ∈ U, HasDerivAt (deriv f) (deriv (deriv f) t) t) := by
  have h1 : ContDiffOn ℝ 1 (deriv f) U := hf.deriv_of_isOpen hU (by norm_num)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · exact ((hf.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)).hasDerivAt
  · exact ((h1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)).hasDerivAt

/-- Product of absolute-value bounds. -/
lemma dlg_mul_le {x y a b : ℝ} (hx : |x| ≤ a) (hy : |y| ≤ b) : |x * y| ≤ a * b := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- **First-order jet of a product.**  If `x = x₀ + h x₁ + eₓ`, `y = y₀ + h y₁ + e_y` with `|eₓ| ≤ cx h²`, `|e_y| ≤ cy h²`,
all jets bounded by `m` and `0 < h ≤ 1`, then `x y = x₀ y₀ + h (x₀ y₁ + x₁ y₀) + O(h²)` with an explicit constant. -/
lemma dlg_jet_mul {x y x0 x1 y0 y1 h m cx cy : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (hx0 : |x0| ≤ m) (hx1 : |x1| ≤ m)
    (hy0 : |y0| ≤ m) (hy1 : |y1| ≤ m) (hx : |x - x0 - h * x1| ≤ cx * h ^ 2) (hy : |y - y0 - h * y1| ≤ cy * h ^ 2) :
    |x * y - x0 * y0 - h * (x0 * y1 + x1 * y0)| ≤ (m ^ 2 + cx * (2 * m + cy) + 2 * m * cy) * h ^ 2 := by
  have hm : 0 ≤ m := (abs_nonneg _).trans hx0
  have hcx : 0 ≤ cx := by
    by_contra hc; push Not at hc
    have := (abs_nonneg (x - x0 - h * x1)).trans hx
    nlinarith [sq_nonneg h, pow_pos hh 2]
  have hcy : 0 ≤ cy := by
    by_contra hc; push Not at hc
    have := (abs_nonneg (y - y0 - h * y1)).trans hy
    nlinarith [sq_nonneg h, pow_pos hh 2]
  have hh2 : h ^ 2 ≤ 1 := by nlinarith
  have hhh : h ≤ 1 := h1
  set ex := x - x0 - h * x1 with hex
  set ey := y - y0 - h * y1 with hey
  have e : x * y - x0 * y0 - h * (x0 * y1 + x1 * y0) = h ^ 2 * (x1 * y1) + ex * y + (x0 + h * x1) * ey := by
    simp only [hex, hey]; ring
  have hyb : |y| ≤ 2 * m + cy := by
    have : y = y0 + h * y1 + ey := by simp only [hey]; ring
    rw [this]
    calc |y0 + h * y1 + ey| ≤ |y0| + |h * y1| + |ey| := (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
      _ ≤ m + m + cy := by
          gcongr
          · rw [abs_mul, abs_of_pos hh]; nlinarith [abs_nonneg y1]
          · exact hy.trans (by nlinarith)
      _ = 2 * m + cy := by ring
  have hxb : |x0 + h * x1| ≤ 2 * m := by
    calc |x0 + h * x1| ≤ |x0| + |h * x1| := abs_add_le _ _
      _ ≤ m + m := by
          gcongr
          rw [abs_mul, abs_of_pos hh]; nlinarith [abs_nonneg x1]
      _ = 2 * m := by ring
  rw [e]
  have t1 : |h ^ 2 * (x1 * y1)| ≤ m ^ 2 * h ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg h), abs_mul]
    have := mul_le_mul hx1 hy1 (abs_nonneg _) hm
    nlinarith [sq_nonneg h]
  have t2 : |ex * y| ≤ (cx * h ^ 2) * (2 * m + cy) := dlg_mul_le hx hyb
  have t3 : |(x0 + h * x1) * ey| ≤ (2 * m) * (cy * h ^ 2) := dlg_mul_le hxb hy
  calc |h ^ 2 * (x1 * y1) + ex * y + (x0 + h * x1) * ey| ≤ |h ^ 2 * (x1 * y1)| + |ex * y| + |(x0 + h * x1) * ey| :=
        (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ m ^ 2 * h ^ 2 + (cx * h ^ 2) * (2 * m + cy) + (2 * m) * (cy * h ^ 2) := by linarith
    _ = (m ^ 2 + cx * (2 * m + cy) + 2 * m * cy) * h ^ 2 := by ring

end FormalResearch.Special
