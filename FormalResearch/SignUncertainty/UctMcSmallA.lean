module

public import FormalResearch.SignUncertainty.UctMcSmallBd
public import FormalResearch.SignUncertainty.UctSeedEdgeKW

/-!
# `SmallBd` for the amplitude `A_*` (F2a, `uct:Mc-small`)

An even real `C^∞` function `A` with `A(0) = 1` satisfies `SmallBd (A : ℂ-valued) p K` for every `p` (`smallBd_of_even_real`);
in particular `A_*` (`smallBd_astar`).
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.SignUncertainty

lemma deriv_ofReal_fun {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (fun τ : ℝ => (f τ : ℂ)) = fun τ => ((deriv f τ : ℝ) : ℂ) := by
  funext τ
  exact ((hf τ).hasDerivAt.ofReal_comp).deriv

lemma deriv_zero_of_even {A : ℝ → ℝ} (hev : ∀ τ, A (-τ) = A τ) : deriv A 0 = 0 := by
  have h : (fun x : ℝ => A (-x)) = A := funext hev
  have h2 := congrArg (fun g => deriv g 0) h
  simp only [deriv_comp_neg, neg_zero] at h2
  linarith

theorem smallBd_of_even_real {A : ℝ → ℝ} (hA : ContDiff ℝ ⊤ A) (h0 : A 0 = 1) (hev : ∀ τ, A (-τ) = A τ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : ℝ, 0 ≤ p → SmallBd (fun τ => (A τ : ℂ)) p K := by
  have hd : ∀ n : ℕ, ContDiff ℝ n A := fun n => hA.of_le (by exact_mod_cast le_top)
  have d1 : Differentiable ℝ A := (hd 1).differentiable (by norm_num)
  have c1 : ContDiff ℝ 2 (deriv A) := by
    have h3 : ContDiff ℝ ((2 : ℕ) + 1) A := by exact hd 3
    exact ((contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 2)).mp h3).2.2
  have d2 : Differentiable ℝ (deriv A) := c1.differentiable (by norm_num)
  have c2 : ContDiff ℝ 1 (deriv (deriv A)) := by
    have h3 : ContDiff ℝ ((1 : ℕ) + 1) (deriv A) := by exact c1
    exact ((contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 1)).mp h3).2.2
  have d3 : Differentiable ℝ (deriv (deriv A)) := c2.differentiable (by norm_num)
  have c3 : Continuous (deriv (deriv (deriv A))) := by
    have h3 : ContDiff ℝ ((0 : ℕ) + 1) (deriv (deriv A)) := by exact c2
    exact contDiff_zero.mp ((contDiff_succ_iff_deriv (𝕜 := ℝ) (n := 0)).mp h3).2.2
  obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := (-(1 / 5) : ℝ)) (b := 1 / 5)).exists_bound_of_continuousOn
    (c2.continuous.continuousOn : ContinuousOn (deriv (deriv A)) _)
  obtain ⟨C3, hC3⟩ := (isCompact_Icc (a := (-(1 / 5) : ℝ)) (b := 1 / 5)).exists_bound_of_continuousOn
    (c3.continuousOn : ContinuousOn (deriv (deriv (deriv A))) _)
  have hC20 : 0 ≤ max C2 0 := le_max_right _ _
  have hC30 : 0 ≤ max C3 0 := le_max_right _ _
  set M2 : ℝ := max C2 0 with hM2
  set M3 : ℝ := max C3 0 with hM3
  have hb2 : ∀ x : ℝ, |x| ≤ 1 / 5 → |deriv (deriv A) x| ≤ M2 := fun x hx =>
    (hC2 x (mem_Icc.mpr (abs_le.mp hx))).trans (le_max_left _ _)
  have hb3 : ∀ x : ℝ, |x| ≤ 1 / 5 → |deriv (deriv (deriv A)) x| ≤ M3 := fun x hx =>
    (hC3 x (mem_Icc.mpr (abs_le.mp hx))).trans (le_max_left _ _)
  have hA1 : ∀ τ : ℝ, |τ| ≤ 1 / 5 → |deriv A τ| ≤ M2 * |τ| := by
    intro τ hτ
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv A) (s := Icc (-(1 / 5) : ℝ) (1 / 5)) (C := M2)
      (fun x _ => d2 x) (fun x hx => by
        have : |x| ≤ 1 / 5 := abs_le.mpr ⟨hx.1, hx.2⟩
        simpa [Real.norm_eq_abs] using hb2 x this) (convex_Icc _ _) (by norm_num : (0 : ℝ) ∈ Icc (-(1 / 5) : ℝ) (1 / 5))
      (mem_Icc.mpr (abs_le.mp hτ))
    rw [deriv_zero_of_even hev, sub_zero, sub_zero] at this
    simpa [Real.norm_eq_abs] using this
  have hA0 : ∀ τ : ℝ, |τ| ≤ 1 / 5 → |A τ - 1| ≤ M2 * τ ^ 2 := by
    intro τ hτ
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := A) (s := Icc (-|τ|) |τ|) (C := M2 * |τ|)
      (fun x _ => d1 x) (fun x hx => by
        have hx' : |x| ≤ |τ| := abs_le.mpr ⟨hx.1, hx.2⟩
        have h := hA1 x (hx'.trans hτ)
        rw [Real.norm_eq_abs]
        nlinarith [mul_le_mul_of_nonneg_left hx' hC20]) (convex_Icc _ _)
      (by simp [abs_nonneg] : (0 : ℝ) ∈ Icc (-|τ|) |τ|) (by constructor <;> linarith [neg_abs_le τ, le_abs_self τ] : τ ∈ Icc (-|τ|) |τ|)
    rw [h0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
    nlinarith [sq_abs τ]
  refine ⟨M2 + M3, by positivity, fun p hp => ?_⟩
  have e1 : deriv (fun τ : ℝ => (A τ : ℂ)) = fun τ => ((deriv A τ : ℝ) : ℂ) := deriv_ofReal_fun d1
  have e2 : deriv (deriv (fun τ : ℝ => (A τ : ℂ))) = fun τ => ((deriv (deriv A) τ : ℝ) : ℂ) := by
    rw [e1]; exact deriv_ofReal_fun d2
  have e3 : deriv (deriv (deriv (fun τ : ℝ => (A τ : ℂ)))) = fun τ => ((deriv (deriv (deriv A)) τ : ℝ) : ℂ) := by
    rw [e2]; exact deriv_ofReal_fun d3
  refine ⟨Complex.ofRealCLM.contDiff.comp (hd 3), fun τ hτ => ?_⟩
  rw [e3, e2, e1]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have h1 := hA0 τ hτ
  have h2 := hA1 τ hτ
  have h3 := hb2 τ hτ
  have h4 := hb3 τ hτ
  have hτ0 := abs_nonneg τ
  have hτ2 : 0 ≤ τ ^ 2 := sq_nonneg τ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [mul_nonneg hp hτ0, mul_nonneg hC30 hτ2, mul_nonneg hC20 (mul_nonneg hp hτ0)]
  · nlinarith [mul_nonneg hC30 hτ0, mul_nonneg hC20 hp, mul_nonneg hC30 hp]
  · nlinarith
  · nlinarith

/-- info: 'FormalResearch.SignUncertainty.smallBd_of_even_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smallBd_of_even_real

end FormalResearch.SignUncertainty
