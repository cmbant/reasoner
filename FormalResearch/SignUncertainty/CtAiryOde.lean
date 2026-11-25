module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Uniqueness for `y''' = 4u y' + 2y` with zero data at `0`

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 1 (the ODE
`G_0''' - 4uG_0' - 2G_0 = 0`; uniqueness for the third-order linear ODE is used to identify `G_0`
with `-π(Ai² + i AiBi)`).  **Proved.**

`ode3_eq_zero`: if `D0, D1, D2 : ℝ → ℂ` satisfy `D0' = D1`, `D1' = D2`, `D2' = 4uD1 + 2D0` on `ℝ`
and `D0(0) = D1(0) = D2(0) = 0`, then `D0 = 0`.  Proof: Grönwall for `(D0, D1, D2)` on `[0, T]`
and, after `u ↦ -u`, on `[-T, 0]`.
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty.CtAiry

/-- Linear Grönwall uniqueness on `[-T, T]` for a function `f : ℝ → E` with `f 0 = 0` and
`‖f'‖ ≤ K ‖f‖` there. -/
lemma eq_zero_of_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f f' : ℝ → E}
    {K T : ℝ} (hf : ∀ u, HasDerivAt f (f' u) u) (h0 : f 0 = 0)
    (hb : ∀ u, |u| ≤ T → ‖f' u‖ ≤ K * ‖f u‖) : ∀ u, |u| ≤ T → f u = 0 := by
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun u => (hf u).continuousAt
  intro u hu
  rcases le_total 0 u with h | h
  · have hT : 0 ≤ T := le_trans (abs_nonneg u) hu
    refine eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := f) (f' := f') (K := K)
      (a := 0) (b := T) hcont.continuousOn (fun x _ => (hf x).hasDerivWithinAt) h0 ?_ u
      ⟨h, by rwa [abs_of_nonneg h] at hu⟩
    intro x hx
    exact hb x (by rw [abs_of_nonneg hx.1]; exact hx.2.le)
  · have hT : 0 ≤ T := le_trans (abs_nonneg u) hu
    set g : ℝ → E := fun x => f (-x) with hg
    have hgd : ∀ x, HasDerivAt g (-(f' (-x))) x := by
      intro x
      have := (hf (-x)).scomp x (hasDerivAt_neg x)
      simpa [hg, Function.comp_def] using this
    have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := g)
      (f' := fun x => -(f' (-x))) (K := K) (a := 0) (b := T)
      (continuous_iff_continuousAt.2 fun x => (hgd x).continuousAt).continuousOn
      (fun x _ => (hgd x).hasDerivWithinAt) (by simp [hg, h0]) ?_ (-u)
      ⟨by linarith, by rw [abs_of_nonpos h] at hu; exact hu⟩
    · simpa [hg] using this
    · intro x hx
      have := hb (-x) (by rw [abs_neg, abs_of_nonneg hx.1]; exact hx.2.le)
      simpa [hg, norm_neg] using this

/-- The third-order linear ODE `y''' = 4u y' + 2y`, first-order form, has only the zero solution
with zero data at `0`. -/
theorem ode3_eq_zero {D0 D1 D2 : ℝ → ℂ}
    (h0 : ∀ u : ℝ, HasDerivAt D0 (D1 u) u) (h1 : ∀ u : ℝ, HasDerivAt D1 (D2 u) u)
    (h2 : ∀ u : ℝ, HasDerivAt D2 (4 * (u : ℂ) * D1 u + 2 * D0 u) u)
    (z0 : D0 0 = 0) (z1 : D1 0 = 0) (z2 : D2 0 = 0) : ∀ u, D0 u = 0 := by
  intro u
  set T : ℝ := |u| with hT
  let f : ℝ → (Fin 3 → ℂ) := fun x => ![D0 x, D1 x, D2 x]
  let f' : ℝ → (Fin 3 → ℂ) := fun x => ![D1 x, D2 x, 4 * (x : ℂ) * D1 x + 2 * D0 x]
  have hf : ∀ x, HasDerivAt f (f' x) x := by
    intro x
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact h0 x
    · exact h1 x
    · exact h2 x
  have hf0 : f 0 = 0 := by
    ext i; fin_cases i <;> simp [f, z0, z1, z2]
  have hb : ∀ x, |x| ≤ T → ‖f' x‖ ≤ (7 + 4 * T) * ‖f x‖ := by
    intro x hx
    have hn : 0 ≤ ‖f x‖ := norm_nonneg _
    have c0 : ‖D0 x‖ ≤ ‖f x‖ := by
      have := norm_le_pi_norm (f x) 0
      simpa [f] using this
    have c1 : ‖D1 x‖ ≤ ‖f x‖ := by
      have := norm_le_pi_norm (f x) 1
      simpa [f] using this
    have c2 : ‖D2 x‖ ≤ ‖f x‖ := by
      have := norm_le_pi_norm (f x) 2
      simpa [f] using this
    have hxT : ‖(x : ℂ)‖ ≤ T := by simpa using hx
    have e3 : ‖4 * (x : ℂ) * D1 x + 2 * D0 x‖ ≤ (7 + 4 * T) * ‖f x‖ := by
      calc ‖4 * (x : ℂ) * D1 x + 2 * D0 x‖
          ≤ ‖4 * (x : ℂ) * D1 x‖ + ‖2 * D0 x‖ := norm_add_le _ _
        _ = 4 * ‖(x : ℂ)‖ * ‖D1 x‖ + 2 * ‖D0 x‖ := by
            simp
        _ ≤ 4 * T * ‖f x‖ + 2 * ‖f x‖ := by
            have : ‖(x : ℂ)‖ * ‖D1 x‖ ≤ T * ‖f x‖ :=
              mul_le_mul hxT c1 (norm_nonneg _) (le_trans (norm_nonneg _) hxT)
            nlinarith [this]
        _ ≤ (7 + 4 * T) * ‖f x‖ := by
            have hT0 : 0 ≤ T := abs_nonneg u
            nlinarith [hn]
    have hK : (1 : ℝ) ≤ 7 + 4 * T := by
      have hT0 : 0 ≤ T := abs_nonneg u
      linarith
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
    intro i
    fin_cases i
    · simp only [f']
      exact le_trans c1 (by nlinarith [hn])
    · simp only [f']
      exact le_trans c2 (by nlinarith [hn])
    · simpa [f'] using e3
  have := eq_zero_of_bound hf hf0 hb u (le_of_eq hT.symm)
  have h' := congrFun this 0
  simpa [f] using h'

/-- info: 'FormalResearch.SignUncertainty.CtAiry.ode3_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ode3_eq_zero

end FormalResearch.SignUncertainty.CtAiry
