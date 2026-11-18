module

public import Mathlib
public import FormalResearch.JB.JBSchur
public import FormalResearch.JacobiEigenvectors.Charts.Regularity
public import FormalResearch.JacobiEigenvectors.Charts.TransferCoefficients

/-!
# Paper J, Theorem B, L3.5a (Schur part): the `C^2` closure and the Schur bounds of the bulk transfer coefficients

Source: Paper J `app_thmB.tex`, "(I2) and the changed coefficient: bulk charts" (the five Schur multipliers of `JB.Chart.Ok`:
`1/alpha`, `B^{[m+1]}/(t_12 alpha)`, `1/t_12`, `t_11/t_12`, `kappa_m`), `thmB.tex` `def:thb-inputs` (I2); the Schur lemmas
`lem:thb-schur` are `JB.jb_schur_of_C2`, `JB.jb_schur_inv`, `JB.jb_schur_div` (`JB/JBSchur.lean`).

## Proved here

* `fullC2_const`, `fullC2_add`, `fullC2_mul`, `fullC2_inv`: the `JB.FullC2` class (joint `C^2` on a rectangle, with the mixed partial)
  is closed under constants, sums, products and reciprocals of functions bounded away from zero.  The product and reciprocal rules
  give explicit derivatives: `(fg)_t = f_t g + f g_t`, `(fg)_s = f_s g + f g_s`, `(fg)_{ts} = f_{ts} g + f_t g_s + f_s g_t + f g_{ts}`;
  `(1/f)_t = -f_t/f^2`, and similarly for `s` and the mixed derivative (`JB.jb_inv_mixedC2`).
* `boundedC2_const`, `boundedC2_add`, `boundedC2_mul`, `boundedC2_inv`, `boundedC2_mono`, `boundedC2_congr`, `boundedC2_full`,
  `boundedC2_mixed`: the same closure for the packaged class `Charts.BoundedC2` (a `FullC2` function with `phi, d_u phi, d_X phi, d_u d_X phi`
  bounded by `S`), with explicit bounds (`S + T`, `4 S T`, `c0^{-1} + 2 S c0^{-2} + 2 S^2 c0^{-3}`), under the rectangle hypotheses only.
* `schur_inv_bound`, `schur_div_bound`, `schur_C2_bound`: `JB.jb_schur_inv`, `jb_schur_div`, `jb_schur_of_C2` with the constants
  `schurInvK`, `schurDivK`, `schurC2K` written out, and their nonnegativity.
* `chart_schur_five`: from `BoundedC2` regularity of `A^{[m+1]}, B^{[m+1]}, t_11, t_12, kappa_m` (bound `S`) and the lower bounds
  `|t_12| >= c_T`, `alpha >= c_alpha` on the rectangle, the five Schur bounds of `JB.Chart.Ok` (`schur_inv_alpha`, `schur_B`,
  `schur_inv_t12`, `schur_t11`, `schur_kappa`) hold for every finite family of sample points in the rectangle, with the constant
  `chartSchurK a b c d S cT cα H`.  This constant is a function of the rectangle and of `S, cT, cα, H` only (`|h| <= H` for the step),
  so it is the same for every function, order, step and parameter `mu`: the uniformity that `JB.OneStepConsts` needs.

## Differences from the paper

* The paper states the five Schur multiplier bounds as hypotheses; here the primitive `C^2` bounds (`Charts.TransferInputs.reg_*`) are the
  hypothesis and the five Schur bounds are derived (`jb_schur_of_C2`, `jb_schur_inv`, `jb_schur_div`), as planned in `TransferCoefficients.lean`.
* `alpha` is `A - h B t_11 / t_12` as in `JB.jbAlpha`; its `C^2` class is obtained by the closure lemmas above.  The step `h` enters only through `|h| <= H`.

## Not formalised

* The chart-level bridge: that the matrices `c.t11 n k`, `c.t12 n k`, ... of an actual `JB.Chart` are the sampled values of the functions
  `t_11(u, X)` etc. of `TransferInputs` (`u_n = uNode h (lo + n)`, `X_k` the eigenvalue), and `JB.Chart.Ok`'s other fields (`transfer`,
  `ext_row`, `overlap_*`, host and matching fields, see the report).
* The Schur norms as infima (only the bound predicate `JB.IsSchurBdd`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Set FormalResearch.JB FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts

/-! ### 1. `FullC2` closure (derivative rules on the rectangle) -/

/-- Constants are `FullC2` with zero derivatives. -/
theorem fullC2_const (k : ℝ) (a b c d : ℝ) :
    FullC2 (fun _ _ => k) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) a b c d where
  d1 := fun _ _ _ _ => hasDerivWithinAt_const _ _ _
  d12 := fun _ _ _ _ => hasDerivWithinAt_const _ _ _
  cont₁ := continuousOn_const
  cont₁₂ := continuousOn_const
  cont := continuousOn_const
  d2 := fun _ _ _ _ => hasDerivWithinAt_const _ _ _
  cont₂ := continuousOn_const

/-- Sums of `FullC2` functions are `FullC2`. -/
theorem fullC2_add {f f₁ f₂ f₁₂ g g₁ g₂ g₁₂ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : FullC2 f f₁ f₂ f₁₂ a b c d) (hg : FullC2 g g₁ g₂ g₁₂ a b c d) :
    FullC2 (fun t s => f t s + g t s) (fun t s => f₁ t s + g₁ t s) (fun t s => f₂ t s + g₂ t s)
      (fun t s => f₁₂ t s + g₁₂ t s) a b c d where
  d1 := fun s hs t ht => (hf.d1 s hs t ht).add (hg.d1 s hs t ht)
  d12 := fun t ht s hs => (hf.d12 t ht s hs).add (hg.d12 t ht s hs)
  cont₁ := hf.cont₁.add hg.cont₁
  cont₁₂ := hf.cont₁₂.add hg.cont₁₂
  cont := hf.cont.add hg.cont
  d2 := fun t ht s hs => (hf.d2 t ht s hs).add (hg.d2 t ht s hs)
  cont₂ := hf.cont₂.add hg.cont₂

/-- Products of `FullC2` functions are `FullC2` (product rule in `t`, in `s`, and for the mixed partial). -/
theorem fullC2_mul {f f₁ f₂ f₁₂ g g₁ g₂ g₁₂ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : FullC2 f f₁ f₂ f₁₂ a b c d) (hg : FullC2 g g₁ g₂ g₁₂ a b c d) :
    FullC2 (fun t s => f t s * g t s)
      (fun t s => f₁ t s * g t s + f t s * g₁ t s)
      (fun t s => f₂ t s * g t s + f t s * g₂ t s)
      (fun t s => f₁₂ t s * g t s + f₁ t s * g₂ t s + f₂ t s * g₁ t s + f t s * g₁₂ t s) a b c d where
  d1 := fun s hs t ht => (hf.d1 s hs t ht).mul (hg.d1 s hs t ht)
  d12 := fun t ht s hs => by
    have h1 := (hf.d12 t ht s hs).mul (hg.d2 t ht s hs)
    have h2 := (hf.d2 t ht s hs).mul (hg.d12 t ht s hs)
    exact (h1.add h2).congr_deriv (by ring)
  cont₁ := (hf.cont₁.mul hg.cont).add (hf.cont.mul hg.cont₁)
  cont₁₂ := (((hf.cont₁₂.mul hg.cont).add (hf.cont₁.mul hg.cont₂)).add (hf.cont₂.mul hg.cont₁)).add
    (hf.cont.mul hg.cont₁₂)
  cont := hf.cont.mul hg.cont
  d2 := fun t ht s hs => (hf.d2 t ht s hs).mul (hg.d2 t ht s hs)
  cont₂ := (hf.cont₂.mul hg.cont).add (hf.cont.mul hg.cont₂)

/-- Reciprocals of `FullC2` functions bounded away from zero are `FullC2`; the derivatives are those of `JB.jb_inv_mixedC2`
(`(1/f)_t = -f_t/f^2`, `(1/f)_s = -f_s/f^2`, mixed partial as there). -/
theorem fullC2_inv {f f₁ f₂ f₁₂ : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : FullC2 f f₁ f₂ f₁₂ a b c d) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hφ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |f t s|) :
    FullC2 (fun t s => (f t s)⁻¹)
      (fun t s => -f₁ t s * (f t s)⁻¹ * (f t s)⁻¹)
      (fun t s => -f₂ t s * (f t s)⁻¹ * (f t s)⁻¹)
      (fun t s => -f₁₂ t s * (f t s)⁻¹ * (f t s)⁻¹ + 2 * f₁ t s * f₂ t s * (f t s)⁻¹ * (f t s)⁻¹ * (f t s)⁻¹)
      a b c d where
  toMixedC2 := jb_inv_mixedC2 hf hc₀ hφ
  cont := by
    refine hf.cont.inv₀ (fun p hp => ?_)
    intro h0
    have h0' : f p.1 p.2 = 0 := h0
    have := hφ p.1 hp.1 p.2 hp.2
    rw [h0', abs_zero] at this
    linarith
  d2 := fun t ht s hs => by
    have hne : f t s ≠ 0 := by
      intro h0
      have := hφ t ht s hs
      rw [h0, abs_zero] at this
      linarith
    exact ((hf.d2 t ht s hs).inv hne).congr_deriv (by ring)
  cont₂ := by
    have hne : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, f t s ≠ 0 := fun t ht s hs h0 => by
      have := hφ t ht s hs
      rw [h0, abs_zero] at this
      linarith
    have hcr : ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2)⁻¹) (Icc a b ×ˢ Icc c d) :=
      hf.cont.inv₀ (fun p hp => hne p.1 hp.1 p.2 hp.2)
    exact (hf.cont₂.neg.mul hcr).mul hcr

/-! ### 2. The packaged class `BoundedC2` -/

/-- Monotonicity of the bound. -/
theorem boundedC2_mono {φ : ℝ → ℝ → ℝ} {a b c d S T : ℝ} (h : BoundedC2 φ a b c d S) (hST : S ≤ T) :
    BoundedC2 φ a b c d T := by
  obtain ⟨φ₁, φ₂, φ₁₂, hF, hb⟩ := h
  refine ⟨φ₁, φ₂, φ₁₂, hF, fun t ht s hs => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hb t ht s hs
  exact ⟨h1.trans hST, h2.trans hST, h3.trans hST, h4.trans hST⟩

/-- The bound is invariant under pointwise equality of the function. -/
theorem boundedC2_congr {f g : ℝ → ℝ → ℝ} {a b c d S : ℝ} (h : BoundedC2 f a b c d S)
    (hfg : ∀ t s, f t s = g t s) : BoundedC2 g a b c d S := by
  have : f = g := funext fun t => funext fun s => hfg t s
  rw [← this]
  exact h

/-- Constants are `BoundedC2` with bound `|k|`. -/
theorem boundedC2_const (k : ℝ) (a b c d : ℝ) : BoundedC2 (fun _ _ => k) a b c d |k| :=
  ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fullC2_const k a b c d, fun _ _ _ _ => by simp⟩

/-- Sums: bounds add. -/
theorem boundedC2_add {f g : ℝ → ℝ → ℝ} {a b c d S T : ℝ} (hf : BoundedC2 f a b c d S)
    (hg : BoundedC2 g a b c d T) : BoundedC2 (fun t s => f t s + g t s) a b c d (S + T) := by
  obtain ⟨f₁, f₂, f₁₂, hF, hfb⟩ := hf
  obtain ⟨g₁, g₂, g₁₂, hG, hgb⟩ := hg
  refine ⟨_, _, _, fullC2_add hF hG, fun t ht s hs => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hfb t ht s hs
  obtain ⟨b1, b2, b3, b4⟩ := hgb t ht s hs
  exact ⟨(abs_add_le _ _).trans (add_le_add a1 b1), (abs_add_le _ _).trans (add_le_add a2 b2),
    (abs_add_le _ _).trans (add_le_add a3 b3), (abs_add_le _ _).trans (add_le_add a4 b4)⟩

/-- Products: with `S, T >= 0`, the bound is `4 S T`. -/
theorem boundedC2_mul {f g : ℝ → ℝ → ℝ} {a b c d S T : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : BoundedC2 f a b c d S) (hg : BoundedC2 g a b c d T) :
    BoundedC2 (fun t s => f t s * g t s) a b c d (4 * S * T) := by
  obtain ⟨f₁, f₂, f₁₂, hF, hfb⟩ := hf
  obtain ⟨g₁, g₂, g₁₂, hG, hgb⟩ := hg
  have hS : 0 ≤ S := (abs_nonneg _).trans ((hfb a ⟨le_rfl, hab⟩ c ⟨le_rfl, hcd⟩).1)
  have hT : 0 ≤ T := (abs_nonneg _).trans ((hgb a ⟨le_rfl, hab⟩ c ⟨le_rfl, hcd⟩).1)
  refine ⟨_, _, _, fullC2_mul hF hG, fun t ht s hs => ?_⟩
  dsimp only
  obtain ⟨a1, a2, a3, a4⟩ := hfb t ht s hs
  obtain ⟨b1, b2, b3, b4⟩ := hgb t ht s hs
  have hST : 0 ≤ S * T := mul_nonneg hS hT
  have mb : ∀ x y X Y : ℝ, |x| ≤ X → |y| ≤ Y → 0 ≤ X → |x * y| ≤ X * Y := fun x y X Y hx hy hX => by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hX
  have s2 : ∀ x y : ℝ, |x| ≤ S * T → |y| ≤ S * T → |x + y| ≤ 4 * S * T := fun x y hx hy => by
    have := abs_add_le x y
    linarith
  have s4 : ∀ x y z w : ℝ, |x| ≤ S * T → |y| ≤ S * T → |z| ≤ S * T → |w| ≤ S * T →
      |x + y + z + w| ≤ 4 * S * T := fun x y z w hx hy hz hw => by
    have h1 := abs_add_le (x + y + z) w
    have h2 := abs_add_le (x + y) z
    have h3 := abs_add_le x y
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := mb _ _ _ _ a1 b1 hS
    linarith
  · exact s2 _ _ (mb _ _ _ _ a2 b1 hS) (mb _ _ _ _ a1 b2 hS)
  · exact s2 _ _ (mb _ _ _ _ a3 b1 hS) (mb _ _ _ _ a1 b3 hS)
  · exact s4 _ _ _ _ (mb _ _ _ _ a4 b1 hS) (mb _ _ _ _ a2 b3 hS) (mb _ _ _ _ a3 b2 hS)
      (mb _ _ _ _ a1 b4 hS)

/-- Reciprocals of `BoundedC2` functions bounded away from zero: with `r = c0^{-1}`, the bound is `r + 2 S r^2 + 2 S^2 r^3`. -/
theorem boundedC2_inv {f : ℝ → ℝ → ℝ} {a b c d S : ℝ} (hab : a ≤ b) (hcd : c ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hf : BoundedC2 f a b c d S) (hφ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |f t s|) :
    BoundedC2 (fun t s => (f t s)⁻¹) a b c d
      (c₀⁻¹ + 2 * S * (c₀⁻¹ * c₀⁻¹) + 2 * S ^ 2 * (c₀⁻¹ * c₀⁻¹ * c₀⁻¹)) := by
  obtain ⟨f₁, f₂, f₁₂, hF, hfb⟩ := hf
  have hS : 0 ≤ S := (abs_nonneg _).trans ((hfb a ⟨le_rfl, hab⟩ c ⟨le_rfl, hcd⟩).1)
  refine ⟨_, _, _, fullC2_inv hF hc₀ hφ, fun t ht s hs => ?_⟩
  dsimp only
  obtain ⟨a1, a2, a3, a4⟩ := hfb t ht s hs
  have hr : 0 ≤ c₀⁻¹ := inv_nonneg.2 hc₀.le
  have hi : |(f t s)⁻¹| ≤ c₀⁻¹ := by
    rw [abs_inv]
    exact inv_anti₀ hc₀ (hφ t ht s hs)
  have m2 : ∀ x y X Y : ℝ, |x| ≤ X → |y| ≤ Y → 0 ≤ X → |x * y| ≤ X * Y := fun x y X Y hx hy hX => by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hX
  have hSr : 0 ≤ S * (c₀⁻¹ * c₀⁻¹) := mul_nonneg hS (mul_nonneg hr hr)
  have hA : 0 ≤ 2 * S * (c₀⁻¹ * c₀⁻¹) := by linarith
  have hB : 0 ≤ 2 * S ^ 2 * (c₀⁻¹ * c₀⁻¹ * c₀⁻¹) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg S)) (mul_nonneg (mul_nonneg hr hr) hr)
  have hSS : 0 ≤ S * S := mul_nonneg hS hS
  have q1 : |-f₁ t s * (f t s)⁻¹ * (f t s)⁻¹| ≤ S * (c₀⁻¹ * c₀⁻¹) := by
    rw [show -f₁ t s * (f t s)⁻¹ * (f t s)⁻¹ = -(f₁ t s * (f t s)⁻¹ * (f t s)⁻¹) by ring, abs_neg]
    have e1 := m2 _ _ _ _ a2 hi hS
    have e2 := m2 _ _ _ _ e1 hi (mul_nonneg hS hr)
    linarith
  have q2 : |-f₂ t s * (f t s)⁻¹ * (f t s)⁻¹| ≤ S * (c₀⁻¹ * c₀⁻¹) := by
    rw [show -f₂ t s * (f t s)⁻¹ * (f t s)⁻¹ = -(f₂ t s * (f t s)⁻¹ * (f t s)⁻¹) by ring, abs_neg]
    have e1 := m2 _ _ _ _ a3 hi hS
    have e2 := m2 _ _ _ _ e1 hi (mul_nonneg hS hr)
    linarith
  have q12 : |-f₁₂ t s * (f t s)⁻¹ * (f t s)⁻¹ + 2 * f₁ t s * f₂ t s * (f t s)⁻¹ * (f t s)⁻¹ * (f t s)⁻¹|
      ≤ S * (c₀⁻¹ * c₀⁻¹) + 2 * S ^ 2 * (c₀⁻¹ * c₀⁻¹ * c₀⁻¹) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [show -f₁₂ t s * (f t s)⁻¹ * (f t s)⁻¹ = -(f₁₂ t s * (f t s)⁻¹ * (f t s)⁻¹) by ring, abs_neg]
      have e1 := m2 _ _ _ _ a4 hi hS
      have e2 := m2 _ _ _ _ e1 hi (mul_nonneg hS hr)
      linarith
    · have f1 : |2 * f₁ t s| ≤ 2 * S := by
        rw [abs_mul, abs_two]
        exact mul_le_mul_of_nonneg_left a2 (by norm_num)
      have f2 := m2 _ _ _ _ f1 a3 (by linarith : (0 : ℝ) ≤ 2 * S)
      have f3 := m2 _ _ _ _ f2 hi (by linarith : (0 : ℝ) ≤ 2 * S * S)
      have f4 := m2 _ _ _ _ f3 hi (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * S * S) hr)
      have f5 := m2 _ _ _ _ f4 hi (mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * S * S) hr) hr)
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith

/-! ### 3. The Schur bounds of the bulk transfer coefficients, with an explicit uniform constant -/

/-- Constant of `JB.jb_schur_inv` for a function bounded by `M` (in `C^2`) and bounded below by `c0` in modulus. -/
def schurInvK (a b c d M c₀ : ℝ) : ℝ :=
  c₀⁻¹ + 2 * c₀⁻¹ + (b - a) * (d - c) * (M * c₀⁻¹ * c₀⁻¹ + 2 * M * M * c₀⁻¹ * c₀⁻¹ * c₀⁻¹)

/-- Constant of `JB.jb_schur_div` (numerator bounds `S₁ S₂ S₃`, denominator `M`, `c0`). -/
def schurDivK (a b c d S₁ S₂ S₃ M c₀ : ℝ) : ℝ :=
  (S₁ + S₂ + (b - a) * (d - c) * S₃) * schurInvK a b c d M c₀

/-- Constant of `JB.jb_schur_of_C2`. -/
def schurC2K (a b c d S₁ S₂ S₃ : ℝ) : ℝ := S₁ + S₂ + (b - a) * (d - c) * S₃

/-- The `BoundedC2` bound of `alpha = A - h B t_11 / t_12` (closure: reciprocal of `t_12` with bound `S`, then products with
`B`, `t_11` and the constant `-h` of bound `H`, then the sum with `A`). -/
def schurAlphaBound (S cT H : ℝ) : ℝ :=
  S + 4 * H * (4 * S * (4 * S * (cT⁻¹ + 2 * S * (cT⁻¹ * cT⁻¹) + 2 * S ^ 2 * (cT⁻¹ * cT⁻¹ * cT⁻¹))))

/-- The uniform constant of the five Schur bounds of `JB.Chart.Ok`: a function of the rectangle and of `S, cT, cα, H` only
(not of the functions, the sample points, the order, the step or `mu`). -/
def chartSchurK (a b c d S cT cα H : ℝ) : ℝ :=
  schurInvK a b c d S cT + schurDivK a b c d S (2 * S) S S cT + schurC2K a b c d S (2 * S) S +
    schurInvK a b c d (schurAlphaBound S cT H) cα +
    schurDivK a b c d S (2 * S) S (4 * S * schurAlphaBound S cT H) (cT * cα)

/-- A `BoundedC2` function is `FullC2` with its three derivatives bounded by the same `S`. -/
theorem boundedC2_full {f : ℝ → ℝ → ℝ} {a b c d S : ℝ} (hf : BoundedC2 f a b c d S) :
    ∃ f₁ f₂ f₁₂ : ℝ → ℝ → ℝ, FullC2 f f₁ f₂ f₁₂ a b c d ∧ (∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₁ t s| ≤ S) ∧
      (∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₂ t s| ≤ S) ∧ (∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₁₂ t s| ≤ S) := by
  obtain ⟨f₁, f₂, f₁₂, hF, hb⟩ := hf
  exact ⟨f₁, f₂, f₁₂, hF, fun t ht s hs => (hb t ht s hs).2.1, fun t ht s hs => (hb t ht s hs).2.2.1,
    fun t ht s hs => (hb t ht s hs).2.2.2⟩

/-- The mixed `C^2` package of a `BoundedC2` numerator, with the three bounds used by `JB.jb_schur_of_C2` and `JB.jb_schur_div`:
`|phi(t,c)| <= S`, `|phi(a,s) - phi(a,c)| <= 2 S`, `|phi_{ts}| <= S` on the rectangle. -/
theorem boundedC2_mixed {f : ℝ → ℝ → ℝ} {a b c d S : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : BoundedC2 f a b c d S) :
    ∃ f₁ f₁₂ : ℝ → ℝ → ℝ, MixedC2 f f₁ f₁₂ a b c d ∧ (∀ t ∈ Icc a b, |f t c| ≤ S) ∧
      (∀ s ∈ Icc c d, |f a s - f a c| ≤ 2 * S) ∧ (∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₁₂ t s| ≤ S) := by
  obtain ⟨f₁, f₂, f₁₂, hF, hfb⟩ := hf
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hc : c ∈ Icc c d := ⟨le_rfl, hcd⟩
  refine ⟨f₁, f₁₂, hF.toMixedC2, fun t ht => (hfb t ht c hc).1, fun s hs => ?_,
    fun t ht s hs => (hfb t ht s hs).2.2.2⟩
  have h1 := (hfb a ha s hs).1
  have h2 := (hfb a ha c hc).1
  calc |f a s - f a c| ≤ |f a s| + |f a c| := abs_sub _ _
    _ ≤ S + S := add_le_add h1 h2
    _ = 2 * S := by ring

/-- **Schur bound of `1/phi`** (`JB.jb_schur_inv`), for a `BoundedC2` function bounded by `S` with `|phi| >= c0`; the constant is `schurInvK`,
and it is nonnegative (`0 <= schurInvK`, from `JB.IsSchurBdd.nonneg`). -/
theorem schur_inv_bound {f : ℝ → ℝ → ℝ} {a b c d S c₀ : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hc₀ : 0 < c₀)
    (hf : BoundedC2 f a b c d S) (hφ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |f t s|) :
    0 ≤ schurInvK a b c d S c₀ ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (u : ι → ℝ) (X : κ → ℝ), (∀ n, u n ∈ Icc a b) → (∀ k, X k ∈ Icc c d) →
        IsSchurBdd (Matrix.of fun n k => (f (u n) (X k))⁻¹) (schurInvK a b c d S c₀) := by
  obtain ⟨f₁, f₂, f₁₂, hF, hfb⟩ := hf
  have h1 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₁ t s| ≤ S := fun t ht s hs => (hfb t ht s hs).2.1
  have h2 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₂ t s| ≤ S := fun t ht s hs => (hfb t ht s hs).2.2.1
  have h3 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₁₂ t s| ≤ S := fun t ht s hs => (hfb t ht s hs).2.2.2
  have hn := (jb_schur_inv hab hcd (fun _ : Fin 1 => a) (fun _ : Fin 1 => c) (fun _ => ⟨le_rfl, hab⟩)
    (fun _ => ⟨le_rfl, hcd⟩) hF hc₀ hφ h1 h2 h3).nonneg
  exact ⟨hn, fun ι κ _ _ _ _ u X hu hX => jb_schur_inv hab hcd u X hu hX hF hc₀ hφ h1 h2 h3⟩

/-- **Schur bound of a quotient** `phi / psi` (`JB.jb_schur_div`): `phi` with its mixed `C^2` package and bounds `S1, S2, S3`,
`psi` `FullC2` with `|psi| >= c0` and derivative bounds `M`. -/
theorem schur_div_bound {φ φ₁ φ₁₂ ψ ψ₁ ψ₂ ψ₁₂ : ℝ → ℝ → ℝ} {a b c d S₁ S₂ S₃ M c₀ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hnum : MixedC2 φ φ₁ φ₁₂ a b c d)
    (hS₁ : ∀ t ∈ Icc a b, |φ t c| ≤ S₁) (hS₂ : ∀ s ∈ Icc c d, |φ a s - φ a c| ≤ S₂)
    (hS₃ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₁₂ t s| ≤ S₃)
    (hden : FullC2 ψ ψ₁ ψ₂ ψ₁₂ a b c d) (hc₀ : 0 < c₀) (hψ0 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |ψ t s|)
    (hM₁ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₁ t s| ≤ M) (hM₂ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₂ t s| ≤ M)
    (hM₁₂ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₁₂ t s| ≤ M) :
    0 ≤ schurDivK a b c d S₁ S₂ S₃ M c₀ ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (u : ι → ℝ) (X : κ → ℝ), (∀ n, u n ∈ Icc a b) → (∀ k, X k ∈ Icc c d) →
        IsSchurBdd (Matrix.of fun n k => φ (u n) (X k) / ψ (u n) (X k)) (schurDivK a b c d S₁ S₂ S₃ M c₀) := by
  have hn := (jb_schur_div hab hcd (fun _ : Fin 1 => a) (fun _ : Fin 1 => c) (fun _ => ⟨le_rfl, hab⟩)
    (fun _ => ⟨le_rfl, hcd⟩) hnum hS₁ hS₂ hS₃ hden hc₀ hψ0 hM₁ hM₂ hM₁₂).nonneg
  exact ⟨hn, fun ι κ _ _ _ _ u X hu hX => jb_schur_div hab hcd u X hu hX hnum hS₁ hS₂ hS₃ hden hc₀ hψ0 hM₁ hM₂ hM₁₂⟩

/-- **Schur bound of a `C^2` multiplier** (`JB.jb_schur_of_C2`). -/
theorem schur_C2_bound {φ φ₁ φ₁₂ : ℝ → ℝ → ℝ} {a b c d S₁ S₂ S₃ : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hφ : MixedC2 φ φ₁ φ₁₂ a b c d)
    (hS₁ : ∀ t ∈ Icc a b, |φ t c| ≤ S₁) (hS₂ : ∀ s ∈ Icc c d, |φ a s - φ a c| ≤ S₂)
    (hS₃ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₁₂ t s| ≤ S₃) :
    0 ≤ schurC2K a b c d S₁ S₂ S₃ ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (u : ι → ℝ) (X : κ → ℝ), (∀ n, u n ∈ Icc a b) → (∀ k, X k ∈ Icc c d) →
        IsSchurBdd (Matrix.of fun n k => φ (u n) (X k)) (schurC2K a b c d S₁ S₂ S₃) := by
  have hn := (jb_schur_of_C2 hab hcd (fun _ : Fin 1 => a) (fun _ : Fin 1 => c) (fun _ => ⟨le_rfl, hab⟩)
    (fun _ => ⟨le_rfl, hcd⟩) hφ hS₁ hS₂ hS₃).nonneg
  exact ⟨hn, fun ι κ _ _ _ _ u X hu hX => jb_schur_of_C2 hab hcd u X hu hX hφ hS₁ hS₂ hS₃⟩

/-- **The five Schur bounds of the bulk transfer coefficients** (`JB.Chart.Ok.schur_inv_alpha`, `schur_B`, `schur_inv_t12`,
`schur_t11`, `schur_kappa`), from the `BoundedC2` regularity `reg_A1, reg_B1, reg_t11, reg_t12, reg_kappa` of `TransferInputs`
(bound `S`), the lower bounds `|t_12| >= c_T` and `alpha >= c_alpha` on the rectangle, and `|h| <= H`
(`alpha = A - h B t_11 / t_12`, `JB.jbAlpha`).  The constant `chartSchurK a b c d S cT cα H` depends only on the rectangle and
`S, cT, cα, H`: it is the same for every function, sample family, order, step and parameter `mu` (the uniformity `JB.OneStepConsts` needs). -/
theorem chart_schur_five {a b c d S cT cα H : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hcT : 0 < cT) (hcα : 0 < cα) :
    ∀ (A B t11 t12 kap : ℝ → ℝ → ℝ) (h : ℝ), |h| ≤ H →
      BoundedC2 A a b c d S → BoundedC2 B a b c d S → BoundedC2 t11 a b c d S → BoundedC2 t12 a b c d S →
      BoundedC2 kap a b c d S → (∀ t ∈ Icc a b, ∀ s ∈ Icc c d, cT ≤ |t12 t s|) →
      (∀ t ∈ Icc a b, ∀ s ∈ Icc c d, cα ≤ A t s - h * B t s * t11 t s / t12 t s) →
      0 ≤ chartSchurK a b c d S cT cα H ∧
        ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (u : ι → ℝ) (X : κ → ℝ),
          (∀ n, u n ∈ Icc a b) → (∀ k, X k ∈ Icc c d) →
          IsSchurBdd (Matrix.of fun n k => 1 / t12 (u n) (X k)) (chartSchurK a b c d S cT cα H) ∧
          IsSchurBdd (Matrix.of fun n k => t11 (u n) (X k) / t12 (u n) (X k)) (chartSchurK a b c d S cT cα H) ∧
          IsSchurBdd (Matrix.of fun n k => kap (u n) (X k)) (chartSchurK a b c d S cT cα H) ∧
          IsSchurBdd (Matrix.of fun n k => 1 / (A (u n) (X k) - h * B (u n) (X k) * t11 (u n) (X k) /
            t12 (u n) (X k))) (chartSchurK a b c d S cT cα H) ∧
          IsSchurBdd (Matrix.of fun n k => B (u n) (X k) /
            (t12 (u n) (X k) * (A (u n) (X k) - h * B (u n) (X k) * t11 (u n) (X k) / t12 (u n) (X k))))
            (chartSchurK a b c d S cT cα H) := by
  intro A B t11 t12 kap h hH hA hB ht11 ht12 hk ht12lb hαlb
  -- (i) reciprocal of t_12, product with t_11, product with B, the constant -h, the sum with A (closure lemmas)
  have hi12 := boundedC2_inv hab hcd hcT ht12 ht12lb
  have hq := boundedC2_mul hab hcd ht11 hi12
  have hbq := boundedC2_mul hab hcd hB hq
  have hmc : BoundedC2 (fun _ _ => -h) a b c d H :=
    boundedC2_mono (boundedC2_const (-h) a b c d) (by rw [abs_neg]; exact hH)
  have hmbq := boundedC2_mul hab hcd hmc hbq
  have hal : BoundedC2 (fun t s => A t s - h * B t s * t11 t s / t12 t s) a b c d (schurAlphaBound S cT H) :=
    boundedC2_congr (boundedC2_add hA hmbq) (fun t s => by ring)
  have hαabs : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, cα ≤ |A t s - h * B t s * t11 t s / t12 t s| :=
    fun t ht s hs => (hαlb t ht s hs).trans (le_abs_self _)
  -- (ii) the five Schur bounds
  obtain ⟨n1, h1⟩ := schur_inv_bound hab hcd hcT ht12 ht12lb
  obtain ⟨n4, h4⟩ := schur_inv_bound hab hcd hcα hal hαabs
  obtain ⟨p1, p2, p3, hT12F, hT12b1, hT12b2, hT12b3⟩ := boundedC2_full ht12
  obtain ⟨t11₁, t11₁₂, t11M, t11a, t11b, t11c⟩ := boundedC2_mixed hab hcd ht11
  obtain ⟨n2, h2⟩ := schur_div_bound hab hcd t11M t11a t11b t11c hT12F hcT ht12lb hT12b1 hT12b2 hT12b3
  have hψ := boundedC2_mul hab hcd ht12 hal
  obtain ⟨q1, q2, q3, hψF, hψb1, hψb2, hψb3⟩ := boundedC2_full hψ
  have hψlb : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d,
      cT * cα ≤ |t12 t s * (A t s - h * B t s * t11 t s / t12 t s)| := fun t ht s hs => by
    rw [abs_mul]
    exact mul_le_mul (ht12lb t ht s hs) (hαabs t ht s hs) hcα.le (abs_nonneg _)
  obtain ⟨B₁, B₁₂, BM, Ba, Bb, Bc⟩ := boundedC2_mixed hab hcd hB
  obtain ⟨n5, h5⟩ := schur_div_bound hab hcd BM Ba Bb Bc hψF (mul_pos hcT hcα) hψlb hψb1 hψb2 hψb3
  obtain ⟨k₁, k₁₂, kM, ka, kb, kc⟩ := boundedC2_mixed hab hcd hk
  obtain ⟨n3, h3⟩ := schur_C2_bound hab hcd kM ka kb kc
  have hK : 0 ≤ chartSchurK a b c d S cT cα H := by
    unfold chartSchurK
    linarith
  refine ⟨hK, fun ι κ _ _ _ _ u X hu hX => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [one_div]
    exact (h1 ι κ u X hu hX).mono (by unfold chartSchurK; linarith)
  · exact (h2 ι κ u X hu hX).mono (by unfold chartSchurK; linarith)
  · exact (h3 ι κ u X hu hX).mono (by unfold chartSchurK; linarith)
  · simp only [one_div]
    exact (h4 ι κ u X hu hX).mono (by unfold chartSchurK; linarith)
  · exact (h5 ι κ u X hu hX).mono (by unfold chartSchurK; linarith)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.fullC2_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.fullC2_add

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.fullC2_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.fullC2_mul

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.fullC2_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.fullC2_inv

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.boundedC2_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.boundedC2_mul

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.boundedC2_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.boundedC2_inv

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.schur_inv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.schur_inv_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.schur_div_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.schur_div_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.schur_C2_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.schur_C2_bound

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.chart_schur_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.chart_schur_five

/-- **The five Schur bounds from the frozen `TransferInputs`** (no further hypothesis): for `mu in P`, `N >= N0` and `|h| <= H`
with `h = F.step N`, the order-`(m+1)` coefficients `A, B, t_11, t_12, kappa_m` of the transfer bundle satisfy the five Schur bounds
of `JB.Chart.Ok` with the uniform constant `chartSchurK`. -/
theorem transfer_schur_five {Par : Type*} [TopologicalSpace Par] {F : SymbolFamily Par} {P : Set Par}
    {Jlo Jhi ulo uhi : Par → ℝ} {m : ℕ} {chain0 chain1 : Par → ℝ → ℕ → LadderData} {patch : ℕ}
    (T : TransferInputs F P Jlo Jhi m chain0 chain1 patch ulo uhi) (H : ℝ) {μ : Par} (hμ : μ ∈ P) {N : ℕ}
    (hN : T.N0 ≤ N) (hH : |F.step N| ≤ H) :
    0 ≤ chartSchurK (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) T.S T.cT T.cα H ∧
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (u : ι → ℝ) (X : κ → ℝ),
        (∀ n, u n ∈ Icc (ulo μ) (uhi μ)) → (∀ k, X k ∈ Icc (Jlo μ) (Jhi μ)) →
        IsSchurBdd (Matrix.of fun n k => 1 / (chain1 μ (X k) N).PiP patch (u n) (F.step N) 0 1)
          (chartSchurK (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) T.S T.cT T.cα H) ∧
        IsSchurBdd (Matrix.of fun n k => (chain1 μ (X k) N).PiP patch (u n) (F.step N) 0 0 /
          (chain1 μ (X k) N).PiP patch (u n) (F.step N) 0 1)
          (chartSchurK (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) T.S T.cT T.cα H) ∧
        IsSchurBdd (Matrix.of fun n k => T.κ μ (X k) N (u n))
          (chartSchurK (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) T.S T.cT T.cα H) ∧
        IsSchurBdd (Matrix.of fun n k => 1 / ((chain1 μ (X k) N).AA patch (u n) (F.step N) -
          F.step N * (chain1 μ (X k) N).BB patch (u n) (F.step N) * (chain1 μ (X k) N).PiP patch (u n) (F.step N) 0 0 /
          (chain1 μ (X k) N).PiP patch (u n) (F.step N) 0 1))
          (chartSchurK (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) T.S T.cT T.cα H) ∧
        IsSchurBdd (Matrix.of fun n k => (chain1 μ (X k) N).BB patch (u n) (F.step N) /
          ((chain1 μ (X k) N).PiP patch (u n) (F.step N) 0 1 *
            ((chain1 μ (X k) N).AA patch (u n) (F.step N) -
              F.step N * (chain1 μ (X k) N).BB patch (u n) (F.step N) *
                (chain1 μ (X k) N).PiP patch (u n) (F.step N) 0 0 / (chain1 μ (X k) N).PiP patch (u n) (F.step N) 0 1)))
          (chartSchurK (ulo μ) (uhi μ) (Jlo μ) (Jhi μ) T.S T.cT T.cα H) :=
  chart_schur_five (T.consts_pos.1 μ hμ).1 (T.consts_pos.1 μ hμ).2 T.consts_pos.2.1 T.consts_pos.2.2.1
    (fun u X => (chain1 μ X N).AA patch u (F.step N)) (fun u X => (chain1 μ X N).BB patch u (F.step N))
    (fun u X => (chain1 μ X N).PiP patch u (F.step N) 0 0) (fun u X => (chain1 μ X N).PiP patch u (F.step N) 0 1)
    (fun u X => T.κ μ X N u) (F.step N) hH (T.reg_A1 μ hμ N hN) (T.reg_B1 μ hμ N hN) (T.reg_t11 μ hμ N hN)
    (T.reg_t12 μ hμ N hN) (T.reg_κ μ hμ N hN)
    (fun t ht s hs => T.t12_lb μ hμ s hs N hN t ht) (fun t ht s hs => T.alpha_lb μ hμ s hs N hN t ht)

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.transfer_schur_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.transfer_schur_five

end FormalResearch.JacobiEigenvectors.TheoremB
