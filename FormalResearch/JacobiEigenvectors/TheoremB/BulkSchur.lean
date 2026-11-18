module

public import Mathlib
public import FormalResearch.JB.JBSchur
public import FormalResearch.JacobiEigenvectors.Charts.Regularity

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
* `boundedC2_const`, `boundedC2_add`, `boundedC2_mul`, `boundedC2_inv`, `boundedC2_mono`, `boundedC2_congr`: the same closure for the
  packaged class `Charts.BoundedC2` (a `FullC2` function with `phi, d_u phi, d_X phi, d_u d_X phi` bounded by `S`), with explicit bounds.
* `schur_inv_exists`, `schur_div_exists`, `schur_C2_exists` (`JB.jb_schur_inv`, `jb_schur_div`, `jb_schur_of_C2` in the existential form:
  one constant, chosen before the finite families of sample points), `boundedC2_mixed`, `boundedC2_full` (the packaged bounds).
* `chart_schur_five`: from `BoundedC2` regularity of `A^{[m+1]}, B^{[m+1]}, t_11, t_12, kappa_m` and the lower bounds
  `|t_12| >= c_T`, `alpha >= c_alpha` on the rectangle, the five Schur bounds of `JB.Chart.Ok` (`schur_inv_alpha`, `schur_B`,
  `schur_inv_t12`, `schur_t11`, `schur_kappa`) hold for every finite family of sample points in the rectangle, with one constant `K`
  chosen before the sample points (and independent of them, of the order, of the step `h` with `|h| <= H`, and of `mu`); the
  constant is produced by the closure lemmas, so it is not stated explicitly.

## Differences from the paper

* The paper states the five Schur multiplier bounds as hypotheses; here the primitive `C^2` bounds (`Charts.TransferInputs.reg_*`) are the
  hypothesis and the five Schur bounds are derived (`jb_schur_of_C2`, `jb_schur_inv`, `jb_schur_div`), as planned in `TransferCoefficients.lean`.
* `alpha` is `A - h B t_11 / t_12` as in `JB.jbAlpha`; its `C^2` class is obtained by the closure lemmas above.  The step `h` enters only through `|h| <= H`.

## Not formalised

* The chart-level bridge: that the matrices `c.t11 n k`, `c.t12 n k`, ... of an actual `JB.Chart` are the sampled values of the functions
  `t_11(u, X)` etc. of `TransferInputs` (`u_n = uNode h (lo + n)`, `X_k` the eigenvalue), and `JB.Chart.Ok`'s other fields (`transfer`,
  `ext_row`, `overlap_*`, host and matching fields, see `TheoremB/SpliceBulk.lean` and the report).
* The Schur norms as infima (only the bound predicate `JB.IsSchurBdd`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Set FormalResearch.JB FormalResearch.JacobiEigenvectors.Charts

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

/-! ### 3. The Schur bounds of the bulk transfer coefficients -/

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

/-- **Schur bound of `1/phi`** (`JB.Chart.Ok.schur_inv_t12`, `schur_inv_alpha`): for `FullC2` `phi` with `|phi| >= c_0 > 0`
and bounds `S`, the Schur bound `c0^{-1} + ...` (`JB.jb_schur_inv`) holds for every finite family of sample points, with one constant. -/
theorem schur_inv_exists {f : ℝ → ℝ → ℝ} {a b c d S c₀ : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hc₀ : 0 < c₀)
    (hf : BoundedC2 f a b c d S) (hφ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |f t s|) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (u : ι → ℝ) (X : κ → ℝ), (∀ n, u n ∈ Icc a b) → (∀ k, X k ∈ Icc c d) →
        IsSchurBdd (Matrix.of fun n k => (f (u n) (X k))⁻¹) K := by
  obtain ⟨f₁, f₂, f₁₂, hF, hfb⟩ := hf
  have h1 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₁ t s| ≤ S := fun t ht s hs => (hfb t ht s hs).2.1
  have h2 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₂ t s| ≤ S := fun t ht s hs => (hfb t ht s hs).2.2.1
  have h3 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |f₁₂ t s| ≤ S := fun t ht s hs => (hfb t ht s hs).2.2.2
  refine ⟨_, (jb_schur_inv hab hcd (fun _ : Fin 1 => a) (fun _ : Fin 1 => c) (fun _ => ⟨le_rfl, hab⟩)
    (fun _ => ⟨le_rfl, hcd⟩) hF hc₀ hφ h1 h2 h3).nonneg, ?_⟩
  intro ι κ _ _ _ _ u X hu hX
  exact jb_schur_inv hab hcd u X hu hX hF hc₀ hφ h1 h2 h3

/-- **Schur bound of a quotient** `phi / psi` (`JB.Chart.Ok.schur_t11`, `schur_B`): `phi` with its mixed `C^2` package (bounds `S1, S2, S3`
as in `JB.jb_schur_of_C2`) and `psi` `FullC2` with `|psi| >= c_0` (bounds `M` as in `JB.jb_schur_inv`). -/
theorem schur_div_exists {φ φ₁ φ₁₂ ψ ψ₁ ψ₂ ψ₁₂ : ℝ → ℝ → ℝ} {a b c d S₁ S₂ S₃ M c₀ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hnum : MixedC2 φ φ₁ φ₁₂ a b c d)
    (hS₁ : ∀ t ∈ Icc a b, |φ t c| ≤ S₁) (hS₂ : ∀ s ∈ Icc c d, |φ a s - φ a c| ≤ S₂)
    (hS₃ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₁₂ t s| ≤ S₃)
    (hden : FullC2 ψ ψ₁ ψ₂ ψ₁₂ a b c d) (hc₀ : 0 < c₀) (hψ0 : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, c₀ ≤ |ψ t s|)
    (hM₁ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₁ t s| ≤ M) (hM₂ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₂ t s| ≤ M)
    (hM₁₂ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |ψ₁₂ t s| ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (u : ι → ℝ) (X : κ → ℝ), (∀ n, u n ∈ Icc a b) → (∀ k, X k ∈ Icc c d) →
        IsSchurBdd (Matrix.of fun n k => φ (u n) (X k) / ψ (u n) (X k)) K := by
  refine ⟨_, (jb_schur_div hab hcd (fun _ : Fin 1 => a) (fun _ : Fin 1 => c) (fun _ => ⟨le_rfl, hab⟩)
    (fun _ => ⟨le_rfl, hcd⟩) hnum hS₁ hS₂ hS₃ hden hc₀ hψ0 hM₁ hM₂ hM₁₂).nonneg, ?_⟩
  intro ι κ _ _ _ _ u X hu hX
  exact jb_schur_div hab hcd u X hu hX hnum hS₁ hS₂ hS₃ hden hc₀ hψ0 hM₁ hM₂ hM₁₂

/-- **Schur bound of a `C^2` multiplier** (`JB.Chart.Ok.schur_κ`): `phi` with its mixed `C^2` package (`JB.jb_schur_of_C2`). -/
theorem schur_C2_exists {φ φ₁ φ₁₂ : ℝ → ℝ → ℝ} {a b c d S₁ S₂ S₃ : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hφ : MixedC2 φ φ₁ φ₁₂ a b c d)
    (hS₁ : ∀ t ∈ Icc a b, |φ t c| ≤ S₁) (hS₂ : ∀ s ∈ Icc c d, |φ a s - φ a c| ≤ S₂)
    (hS₃ : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, |φ₁₂ t s| ≤ S₃) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (u : ι → ℝ) (X : κ → ℝ), (∀ n, u n ∈ Icc a b) → (∀ k, X k ∈ Icc c d) →
        IsSchurBdd (Matrix.of fun n k => φ (u n) (X k)) K := by
  refine ⟨_, (jb_schur_of_C2 hab hcd (fun _ : Fin 1 => a) (fun _ : Fin 1 => c) (fun _ => ⟨le_rfl, hab⟩)
    (fun _ => ⟨le_rfl, hcd⟩) hφ hS₁ hS₂ hS₃).nonneg, ?_⟩
  intro ι κ _ _ _ _ u X hu hX
  exact jb_schur_of_C2 hab hcd u X hu hX hφ hS₁ hS₂ hS₃

/-- **The five Schur bounds of the bulk transfer coefficients** (`JB.Chart.Ok.schur_inv_alpha`, `schur_B`, `schur_inv_t12`,
`schur_t11`, `schur_kappa`), from the `BoundedC2` regularity `reg_A1, reg_B1, reg_t11, reg_t12, reg_kappa` of `TransferInputs` and the
lower bounds `|t_12| >= c_T`, `alpha >= c_alpha` on the rectangle.  `alpha = A - h B t_11 / t_12` (`JB.jbAlpha`), `|h| <= H`.
One constant `K` serves all finite families of sample points in the rectangle (it depends only on the bounds, not on the samples). -/
theorem chart_schur_five {A B t11 t12 kap : ℝ → ℝ → ℝ} {a b c d S cT cα H h : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hH : |h| ≤ H)
    (hA : BoundedC2 A a b c d S) (hB : BoundedC2 B a b c d S) (ht11 : BoundedC2 t11 a b c d S)
    (ht12 : BoundedC2 t12 a b c d S) (hk : BoundedC2 kap a b c d S)
    (hcT : 0 < cT) (ht12lb : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, cT ≤ |t12 t s|)
    (hcα : 0 < cα) (hαlb : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, cα ≤ A t s - h * B t s * t11 t s / t12 t s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ι κ : Type) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
      (u : ι → ℝ) (X : κ → ℝ), (∀ n, u n ∈ Icc a b) → (∀ k, X k ∈ Icc c d) →
        IsSchurBdd (Matrix.of fun n k => 1 / t12 (u n) (X k)) K ∧
        IsSchurBdd (Matrix.of fun n k => t11 (u n) (X k) / t12 (u n) (X k)) K ∧
        IsSchurBdd (Matrix.of fun n k => kap (u n) (X k)) K ∧
        IsSchurBdd (Matrix.of fun n k => 1 / (A (u n) (X k) - h * B (u n) (X k) * t11 (u n) (X k) / t12 (u n) (X k))) K ∧
        IsSchurBdd (Matrix.of fun n k => B (u n) (X k) /
          (t12 (u n) (X k) * (A (u n) (X k) - h * B (u n) (X k) * t11 (u n) (X k) / t12 (u n) (X k)))) K := by
  obtain ⟨Ti, hi12⟩ : ∃ T, BoundedC2 (fun t s => (t12 t s)⁻¹) a b c d T :=
    ⟨_, boundedC2_inv hab hcd hcT ht12 ht12lb⟩
  obtain ⟨Tq, hq⟩ : ∃ T, BoundedC2 (fun t s => t11 t s * (t12 t s)⁻¹) a b c d T :=
    ⟨_, boundedC2_mul hab hcd ht11 hi12⟩
  obtain ⟨Tbq, hbq⟩ : ∃ T, BoundedC2 (fun t s => B t s * (t11 t s * (t12 t s)⁻¹)) a b c d T :=
    ⟨_, boundedC2_mul hab hcd hB hq⟩
  have hmc : BoundedC2 (fun _ _ => -h) a b c d H :=
    boundedC2_mono (boundedC2_const (-h) a b c d) (by rw [abs_neg]; exact hH)
  obtain ⟨Tm, hmbq⟩ : ∃ T, BoundedC2 (fun t s => (-h) * (B t s * (t11 t s * (t12 t s)⁻¹))) a b c d T :=
    ⟨_, boundedC2_mul hab hcd hmc hbq⟩
  obtain ⟨Sa, hal⟩ : ∃ T, BoundedC2 (fun t s => A t s - h * B t s * t11 t s / t12 t s) a b c d T :=
    ⟨_, boundedC2_congr (boundedC2_add hA hmbq) (fun t s => by ring)⟩
  have hαabs : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d, cα ≤ |A t s - h * B t s * t11 t s / t12 t s| :=
    fun t ht s hs => (hαlb t ht s hs).trans (le_abs_self _)
  -- (I2) 1/t_12 and the reciprocal of alpha
  obtain ⟨K1, n1, h1⟩ := schur_inv_exists hab hcd hcT ht12 ht12lb
  obtain ⟨K4, n4, h4⟩ := schur_inv_exists hab hcd hcα hal hαabs
  -- t_11 / t_12 and B / (t_12 alpha): quotients with the mixed package of the numerator
  obtain ⟨p1, p2, p3, hT12F, hT12b1, hT12b2, hT12b3⟩ := boundedC2_full ht12
  obtain ⟨t11₁, t11₁₂, t11M, t11a, t11b, t11c⟩ := boundedC2_mixed hab hcd ht11
  obtain ⟨K2, n2, h2⟩ := schur_div_exists hab hcd t11M t11a t11b t11c hT12F hcT ht12lb hT12b1 hT12b2 hT12b3
  obtain ⟨Mψ, hψ⟩ : ∃ M, BoundedC2 (fun t s => t12 t s * (A t s - h * B t s * t11 t s / t12 t s)) a b c d M :=
    ⟨_, boundedC2_mul hab hcd ht12 hal⟩
  obtain ⟨q1, q2, q3, hψF, hψb1, hψb2, hψb3⟩ := boundedC2_full hψ
  have hψlb : ∀ t ∈ Icc a b, ∀ s ∈ Icc c d,
      cT * cα ≤ |t12 t s * (A t s - h * B t s * t11 t s / t12 t s)| := fun t ht s hs => by
    rw [abs_mul]
    exact mul_le_mul (ht12lb t ht s hs) (hαabs t ht s hs) hcα.le (abs_nonneg _)
  obtain ⟨B₁, B₁₂, BM, Ba, Bb, Bc⟩ := boundedC2_mixed hab hcd hB
  obtain ⟨K5, n5, h5⟩ := schur_div_exists hab hcd BM Ba Bb Bc hψF (mul_pos hcT hcα) hψlb hψb1 hψb2 hψb3
  -- the changed coefficient kappa_m
  obtain ⟨k₁, k₁₂, kM, ka, kb, kc⟩ := boundedC2_mixed hab hcd hk
  obtain ⟨K3, n3, h3⟩ := schur_C2_exists hab hcd kM ka kb kc
  refine ⟨K1 + K2 + K3 + K4 + K5, by linarith, ?_⟩
  intro ι κ _ _ _ _ u X hu hX
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [one_div]
    exact (h1 ι κ u X hu hX).mono (by linarith)
  · exact (h2 ι κ u X hu hX).mono (by linarith)
  · exact (h3 ι κ u X hu hX).mono (by linarith)
  · simp only [one_div]
    exact (h4 ι κ u X hu hX).mono (by linarith)
  · exact (h5 ι κ u X hu hX).mono (by linarith)

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

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.chart_schur_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.chart_schur_five

end FormalResearch.JacobiEigenvectors.TheoremB
