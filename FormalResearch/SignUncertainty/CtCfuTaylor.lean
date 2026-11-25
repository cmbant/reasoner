module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Second-order Taylor bound with cubic remainder for a `C^4` germ (support for `ct:cfu`)  **Proved.**

If `g` is `C^4` on `(-ρ, ρ)` then `|g a - g 0 - g'(0) a - g''(0) a²/2| ≤ K |a|³` on `|a| < ρ/2`.
-/

@[expose] public section

open Filter Topology Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty.CtCfu

/-- MVT with a power bound on the derivative: `|f'(y)| ≤ M |y|^j` on `(-ρ,ρ)` implies `|f x - f 0| ≤ M |x|^{j+1}`. -/
lemma abs_sub_le_pow {f f' : ℝ → ℝ} {ρ M : ℝ} {j : ℕ} (hM : 0 ≤ M) (hd : ∀ y ∈ Ioo (-ρ) ρ, HasDerivAt f (f' y) y)
    (hb : ∀ y ∈ Ioo (-ρ) ρ, |f' y| ≤ M * |y| ^ j) {x : ℝ} (hx : x ∈ Ioo (-ρ) ρ) :
    |f x - f 0| ≤ M * |x| ^ (j + 1) := by
  have hρ : 0 < ρ := by linarith [hx.1, hx.2]
  have hax : |x| < ρ := abs_lt.mpr hx
  have hseg : ∀ y ∈ uIcc 0 x, y ∈ Ioo (-ρ) ρ ∧ |y| ≤ |x| := by
    intro y hy
    have hy' : |y| ≤ |x| := by
      rcases le_total 0 x with h | h
      · rw [uIcc_of_le h] at hy; rw [abs_of_nonneg hy.1, abs_of_nonneg h]; exact hy.2
      · rw [uIcc_of_ge h] at hy; rw [abs_of_nonpos hy.2, abs_of_nonpos h]; linarith [hy.1]
    exact ⟨abs_lt.mp (lt_of_le_of_lt hy' hax), hy'⟩
  have := (convex_uIcc 0 x).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (C := M * |x| ^ j)
    (fun y hy => (hd y (hseg y hy).1).hasDerivWithinAt)
    (fun y hy => by
      rw [Real.norm_eq_abs]
      calc |f' y| ≤ M * |y| ^ j := hb y (hseg y hy).1
        _ ≤ M * |x| ^ j := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hseg y hy).2 j) hM)
    (left_mem_uIcc) (right_mem_uIcc)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at this
  calc |f x - f 0| ≤ M * |x| ^ j * |x| := this
    _ = M * |x| ^ (j + 1) := by ring

/-- Cubic Taylor remainder for a function with three bounded derivatives on `(-ρ,ρ)`. -/
lemma taylor2_bound_of_derivs {g g1 g2 g3 : ℝ → ℝ} {ρ K : ℝ} (hK : 0 ≤ K)
    (h0 : ∀ y ∈ Ioo (-ρ) ρ, HasDerivAt g (g1 y) y) (h1 : ∀ y ∈ Ioo (-ρ) ρ, HasDerivAt g1 (g2 y) y)
    (h2 : ∀ y ∈ Ioo (-ρ) ρ, HasDerivAt g2 (g3 y) y) (hb : ∀ y ∈ Ioo (-ρ) ρ, |g3 y| ≤ K) {a : ℝ}
    (ha : a ∈ Ioo (-ρ) ρ) : |g a - g 0 - g1 0 * a - g2 0 * a ^ 2 / 2| ≤ K * |a| ^ 3 := by
  have hρ : 0 < ρ := by linarith [ha.1, ha.2]
  have h00 : (0 : ℝ) ∈ Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
  -- `e2 x = g2 x - g2 0`
  have he2 : ∀ x ∈ Ioo (-ρ) ρ, |g2 x - g2 0| ≤ K * |x| ^ 1 := fun x hx =>
    abs_sub_le_pow (j := 0) hK h2 (fun y hy => by simpa using hb y hy) hx
  -- `e1 x = g1 x - g1 0 - g2 0 x`
  have he1 : ∀ x ∈ Ioo (-ρ) ρ, |g1 x - g1 0 - g2 0 * x| ≤ K * |x| ^ 2 := by
    intro x hx
    have := abs_sub_le_pow (f := fun y => g1 y - g2 0 * y) (f' := fun y => g2 y - g2 0) (j := 1) hK
      (fun y hy => ((h1 y hy).sub ((hasDerivAt_id y).const_mul (g2 0))).congr_deriv (by simp))
      (fun y hy => by simpa using he2 y hy) hx
    calc |g1 x - g1 0 - g2 0 * x| = |(g1 x - g2 0 * x) - (g1 0 - g2 0 * 0)| := by ring_nf
      _ ≤ K * |x| ^ (1 + 1) := this
      _ = K * |x| ^ 2 := by norm_num
  have := abs_sub_le_pow (f := fun y => g y - g1 0 * y - g2 0 * y ^ 2 / 2) (f' := fun y => g1 y - g1 0 - g2 0 * y)
    (j := 2) hK
    (fun y hy => by
      have h := ((h0 y hy).sub ((hasDerivAt_id y).const_mul (g1 0))).sub (((hasDerivAt_pow 2 y).const_mul (g2 0)).div_const 2)
      refine h.congr_deriv ?_
      simp; ring)
    (fun y hy => he1 y hy) ha
  calc |g a - g 0 - g1 0 * a - g2 0 * a ^ 2 / 2| =
      |(g a - g1 0 * a - g2 0 * a ^ 2 / 2) - (g 0 - g1 0 * 0 - g2 0 * 0 ^ 2 / 2)| := by ring_nf
    _ ≤ K * |a| ^ (2 + 1) := this
    _ = K * |a| ^ 3 := by norm_num

/-- **Cubic Taylor remainder at `0` for a `C^4` germ.** -/
lemma taylor2_of_contDiffAt {g : ℝ → ℝ} (hg : ContDiffAt ℝ 4 g 0) :
    ∃ ρ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ a : ℝ, |a| < ρ →
      |g a - g 0 - deriv g 0 * a - deriv (deriv g) 0 * a ^ 2 / 2| ≤ K * |a| ^ 3 := by
  have hev := hg.eventually (by norm_num)
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hU : IsOpen (Ioo (-ρ0) ρ0) := isOpen_Ioo
  have hUb : ∀ x ∈ Ioo (-ρ0) ρ0, ContDiffAt ℝ 4 g x := fun x hx =>
    hball x (by simpa [Real.dist_eq, abs_lt] using hx)
  have hcd : ContDiffOn ℝ 4 g (Ioo (-ρ0) ρ0) := fun x hx => (hUb x hx).contDiffWithinAt
  have hcd1 : ContDiffOn ℝ 3 (deriv g) (Ioo (-ρ0) ρ0) := hcd.deriv_of_isOpen hU (by norm_num)
  have hcd2 : ContDiffOn ℝ 2 (deriv (deriv g)) (Ioo (-ρ0) ρ0) := hcd1.deriv_of_isOpen hU (by norm_num)
  have hcd3 : ContDiffOn ℝ 1 (deriv (deriv (deriv g))) (Ioo (-ρ0) ρ0) := hcd2.deriv_of_isOpen hU (by norm_num)
  have hdiff : ∀ {f : ℝ → ℝ} {m : WithTop ℕ∞}, ContDiffOn ℝ m f (Ioo (-ρ0) ρ0) → m ≠ 0 →
      ∀ y ∈ Ioo (-ρ0) ρ0, HasDerivAt f (deriv f y) y := fun {f m} h hm y hy =>
    ((h.differentiableOn hm) y hy).differentiableAt (hU.mem_nhds hy) |>.hasDerivAt
  have hρ2 : 0 < ρ0 / 2 := by linarith
  obtain ⟨K0, hK0⟩ := (isCompact_Icc (a := -(ρ0 / 2)) (b := ρ0 / 2)).exists_bound_of_continuousOn
    (hcd3.continuousOn.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  refine ⟨ρ0 / 2, hρ2, |K0|, abs_nonneg _, fun a ha => ?_⟩
  have hsub : ∀ y, y ∈ Ioo (-(ρ0 / 2)) (ρ0 / 2) → y ∈ Ioo (-ρ0) ρ0 := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  refine taylor2_bound_of_derivs (g := g) (g1 := deriv g) (g2 := deriv (deriv g)) (g3 := deriv (deriv (deriv g)))
    (ρ := ρ0 / 2) (abs_nonneg _) (fun y hy => hdiff hcd (by norm_num) y (hsub y hy))
    (fun y hy => hdiff hcd1 (by norm_num) y (hsub y hy)) (fun y hy => hdiff hcd2 (by norm_num) y (hsub y hy))
    (fun y hy => ?_) (abs_lt.mp ha |> fun h => ⟨h.1, h.2⟩)
  have := hK0 y ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_abs_self _)

end FormalResearch.SignUncertainty.CtCfu
