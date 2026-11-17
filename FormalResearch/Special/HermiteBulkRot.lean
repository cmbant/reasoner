module

public import Mathlib

/-!
# Rotation (Prüfer) comparison for a perturbed oscillator

Abstract first-order step of the bulk Plancherel–Rotach expansion of the Hermite functions
(W1 `hermite.tex`, `lem:PR`(a)).  If `U' = w V`, `V' = -w (1 + ψ) U` on `[0, b]` with `w ψ ≥ 0`
bounded by `κ` and `S' = w`, `S 0 = 0`, then `U` differs from the exact rotation
`U 0 cos S + V 0 sin S` by at most `2 κ x e^{κ b / 2} √(U 0² + V 0²)`.

Proved by passing to the rotated coordinates `(a, b) = R(-S)(U, V)`: `a' = w ψ U sin S`,
`b' = -w ψ U cos S`, and `U² + V²` grows at most like `e^{κ x}`.
Not formalised here: nothing about Hermite functions (see `HermiteBulkProfile`).
-/

@[expose] public section

open Real

namespace FormalResearch.Special

/-- **Rotation comparison.**  See the module docstring. -/
theorem hbk_rot (U V w ψ S : ℝ → ℝ) (b κ : ℝ) (hb : 0 ≤ b) (hκ : 0 ≤ κ)
    (hU : ∀ x ∈ Set.Icc 0 b, HasDerivAt U (w x * V x) x)
    (hV : ∀ x ∈ Set.Icc 0 b, HasDerivAt V (-(w x * (1 + ψ x)) * U x) x)
    (hS : ∀ x ∈ Set.Icc 0 b, HasDerivAt S (w x) x) (hS0 : S 0 = 0)
    (hw : ∀ x ∈ Set.Icc 0 b, 0 ≤ w x * ψ x ∧ w x * ψ x ≤ κ) :
    ∀ x ∈ Set.Icc 0 b,
      |U x - (U 0 * cos (S x) + V 0 * sin (S x))| ≤
        2 * κ * x * exp (κ * b / 2) * √(U 0 ^ 2 + V 0 ^ 2) := by
  have h0b : (0 : ℝ) ∈ Set.Icc 0 b := ⟨le_rfl, hb⟩
  -- growth of the norm
  have hg : ∀ x ∈ Set.Icc 0 b, (U x ^ 2 + V x ^ 2) ≤ (U 0 ^ 2 + V 0 ^ 2) * exp (κ * x) := by
    set g : ℝ → ℝ := fun x => (U x ^ 2 + V x ^ 2) * exp (-(κ * x)) with hgdef
    have hgd : ∀ x ∈ Set.Icc 0 b, HasDerivAt g
        ((2 * U x * (w x * V x) + 2 * V x * (-(w x * (1 + ψ x)) * U x)) * exp (-(κ * x)) +
          (U x ^ 2 + V x ^ 2) * (exp (-(κ * x)) * (-κ))) x := by
      intro x hx
      have h1 := ((hU x hx).pow 2).add ((hV x hx).pow 2)
      have h2 : HasDerivAt (fun x : ℝ => exp (-(κ * x))) (exp (-(κ * x)) * (-κ)) x := by
        have := ((hasDerivAt_id x).const_mul κ).neg.exp
        simpa using this
      have := h1.mul h2
      convert this using 1
      simp
    have hanti : AntitoneOn g (Set.Icc 0 b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 b)
      · intro x hx; exact (hgd x hx).continuousAt.continuousWithinAt
      · intro x hx; rw [interior_Icc] at hx
        exact (hgd x ⟨hx.1.le, hx.2.le⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' : x ∈ Set.Icc 0 b := ⟨hx.1.le, hx.2.le⟩
        rw [(hgd x hx').deriv]
        obtain ⟨hw0, hwκ⟩ := hw x hx'
        have he : 0 < exp (-(κ * x)) := exp_pos _
        have key : -(2 * w x * ψ x * U x * V x) - κ * (U x ^ 2 + V x ^ 2) ≤ 0 := by
          have hN : 0 ≤ U x ^ 2 + V x ^ 2 := by positivity
          have h2 : |2 * U x * V x| ≤ U x ^ 2 + V x ^ 2 := by
            rw [abs_le]; constructor <;> nlinarith [sq_nonneg (U x + V x), sq_nonneg (U x - V x)]
          have h4 : -(2 * U x * V x) ≤ U x ^ 2 + V x ^ 2 := by linarith [(abs_le.1 h2).1]
          have := mul_le_mul_of_nonneg_left h4 hw0
          nlinarith [mul_le_mul_of_nonneg_right hwκ hN]
        nlinarith [mul_nonneg he.le (neg_nonneg.2 key)]
    intro x hx
    have := hanti h0b hx hx.1
    simp only [hgdef, mul_zero, neg_zero, exp_zero, mul_one] at this
    have he : 0 < exp (κ * x) := exp_pos _
    have hmul : (U x ^ 2 + V x ^ 2) * exp (-(κ * x)) ≤ U 0 ^ 2 + V 0 ^ 2 := by simpa using this
    calc U x ^ 2 + V x ^ 2 = (U x ^ 2 + V x ^ 2) * exp (-(κ * x)) * exp (κ * x) := by
          rw [mul_assoc, ← exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hmul he.le
  set N0 := U 0 ^ 2 + V 0 ^ 2 with hN0
  have hN0nn : 0 ≤ N0 := by positivity
  have hUb : ∀ x ∈ Set.Icc 0 b, |U x| ≤ √N0 * exp (κ * b / 2) := by
    intro x hx
    have h1 := hg x hx
    have h2 : exp (κ * x) ≤ exp (κ * b) := exp_le_exp.2 (mul_le_mul_of_nonneg_left hx.2 hκ)
    have h3 : (√N0 * exp (κ * b / 2)) ^ 2 = N0 * exp (κ * b) := by
      rw [mul_pow, Real.sq_sqrt hN0nn, ← exp_nat_mul]; congr 2; push_cast; ring
    apply abs_le_of_sq_le_sq _ (by positivity)
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left h2 hN0nn, sq_nonneg (V x)]
  set a : ℝ → ℝ := fun x => U x * cos (S x) - V x * sin (S x) with ha
  set bb : ℝ → ℝ := fun x => U x * sin (S x) + V x * cos (S x) with hbb
  have had : ∀ x ∈ Set.Icc 0 b, HasDerivAt a (w x * ψ x * U x * sin (S x)) x := by
    intro x hx
    have := ((hU x hx).mul (hS x hx).cos).sub ((hV x hx).mul (hS x hx).sin)
    convert this using 1; ring
  have hbd : ∀ x ∈ Set.Icc 0 b, HasDerivAt bb (-(w x * ψ x * U x * cos (S x))) x := by
    intro x hx
    have := ((hU x hx).mul (hS x hx).sin).add ((hV x hx).mul (hS x hx).cos)
    convert this using 1; ring
  set C := κ * (√N0 * exp (κ * b / 2)) with hC
  have hCb : ∀ x ∈ Set.Icc 0 b, ‖w x * ψ x * U x * sin (S x)‖ ≤ C ∧
      ‖-(w x * ψ x * U x * cos (S x))‖ ≤ C := by
    intro x hx
    obtain ⟨hw0, hwκ⟩ := hw x hx
    have hu := hUb x hx
    have key : ∀ t : ℝ, |t| ≤ 1 → |w x * ψ x * U x * t| ≤ C := by
      intro t ht
      rw [abs_mul, abs_mul, abs_of_nonneg hw0]
      calc w x * ψ x * |U x| * |t| ≤ κ * (√N0 * exp (κ * b / 2)) * 1 := by
            apply mul_le_mul (mul_le_mul hwκ hu (abs_nonneg _) hκ) ht (abs_nonneg _) (by positivity)
        _ = C := by rw [hC, mul_one]
    constructor
    · rw [Real.norm_eq_abs]; exact key _ (abs_sin_le_one _)
    · rw [Real.norm_eq_abs, abs_neg]; exact key _ (abs_cos_le_one _)
  intro x hx
  have hma : |a x - a 0| ≤ C * x := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := a) (f' := fun x => w x * ψ x * U x * sin (S x)) (C := C) (s := Set.Icc 0 b)
      (fun y hy => (had y hy).hasDerivWithinAt) (fun y hy => (hCb y hy).1) (convex_Icc 0 b) h0b hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using this
  have hmb : |bb x - bb 0| ≤ C * x := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := bb) (f' := fun x => -(w x * ψ x * U x * cos (S x))) (C := C) (s := Set.Icc 0 b)
      (fun y hy => (hbd y hy).hasDerivWithinAt) (fun y hy => (hCb y hy).2) (convex_Icc 0 b) h0b hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using this
  have ha0 : a 0 = U 0 := by simp [ha, hS0]
  have hb0 : bb 0 = V 0 := by simp [hbb, hS0]
  have hid : U x - (U 0 * cos (S x) + V 0 * sin (S x)) =
      (a x - a 0) * cos (S x) + (bb x - bb 0) * sin (S x) := by
    rw [ha0, hb0]; simp only [ha, hbb]
    have := sin_sq_add_cos_sq (S x)
    linear_combination (-U x) * this
  rw [hid]
  calc |(a x - a 0) * cos (S x) + (bb x - bb 0) * sin (S x)|
      ≤ |(a x - a 0) * cos (S x)| + |(bb x - bb 0) * sin (S x)| := abs_add_le _ _
    _ ≤ |a x - a 0| + |bb x - bb 0| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
          (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _))
    _ ≤ 2 * κ * x * exp (κ * b / 2) * √N0 := by rw [hC] at hma hmb; nlinarith

end FormalResearch.Special

/-- info: 'FormalResearch.Special.hbk_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hbk_rot
