module

public import FormalResearch.SignUncertainty.UctEnv2
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# `Env2` for holomorphic functions along a line (Cauchy estimates) (F2a helper)

`env2_holo_line`: if `F` is holomorphic on an open `U ⊇ closedBall (c₀ + dτ) R` (`‖d‖ = 1`), then `τ ↦ F(c₀ + dτ)` is `C²`,
`Env2` with the envelope `P₀ + M/R + 2M/R²` where `‖F(c₀+dτ)‖ ≤ P₀ τ` and `‖F‖ ≤ M τ` on the circle of radius `R` about
`c₀ + dτ` (Cauchy's estimates `‖F'‖ ≤ M/R`, `‖F''‖ ≤ 2M/R²`).
-/

@[expose] public section

open Complex Filter Topology Metric Set

namespace FormalResearch.SignUncertainty

lemma cauchy_deriv_two {F : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R) (hF : DifferentiableOn ℂ F (closedBall c R))
    (hM : ∀ z ∈ sphere c R, ‖F z‖ ≤ M) : ‖deriv F c‖ ≤ M / R ∧ ‖deriv (deriv F) c‖ ≤ 2 * M / R ^ 2 := by
  have hd : DiffContOnCl ℂ F (ball c R) := by
    have : DifferentiableOn ℂ F (closure (ball c R)) := by
      rw [closure_ball c hR.ne']; exact hF
    exact this.diffContOnCl
  refine ⟨Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd hM, ?_⟩
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hR hd hM
  rw [iteratedDeriv_succ, iteratedDeriv_one] at this
  simpa using this

theorem env2_holo_line {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {c₀ d : ℂ}
    (hd : ‖d‖ = 1) {R : ℝ} (hR : 0 < R) (hball : ∀ τ : ℝ, closedBall (c₀ + d * (τ : ℂ)) R ⊆ U)
    (P₀ M : ℝ → ℝ) (hP₀ : ∀ τ : ℝ, ‖F (c₀ + d * (τ : ℂ))‖ ≤ P₀ τ)
    (hM : ∀ τ : ℝ, ∀ z ∈ sphere (c₀ + d * (τ : ℂ)) R, ‖F z‖ ≤ M τ) :
    Env2 (fun τ : ℝ => F (c₀ + d * (τ : ℂ))) (fun τ => P₀ τ + M τ / R + 2 * M τ / R ^ 2) := by
  set ℓ : ℝ → ℂ := fun τ => c₀ + d * (τ : ℂ) with hℓ
  have hmem : ∀ τ : ℝ, ℓ τ ∈ U := fun τ => hball τ (mem_closedBall_self hR.le)
  have hF1 : DifferentiableOn ℂ (deriv F) U := hF.deriv hU
  have hF2 : DifferentiableOn ℂ (deriv (deriv F)) U := hF1.deriv hU
  have hℓd : ∀ τ : ℝ, HasDerivAt ℓ d τ := fun τ => by
    have := ((hasDerivAt_id τ).ofReal_comp.const_mul d).const_add c₀
    exact this.congr_deriv (by simp)
  have hder : ∀ (G : ℂ → ℂ), DifferentiableOn ℂ G U → ∀ τ : ℝ,
      HasDerivAt (fun τ : ℝ => G (ℓ τ)) (d * deriv G (ℓ τ)) τ := by
    intro G hG τ
    have h1 : HasDerivAt G (deriv G (ℓ τ)) (ℓ τ) := (hG.differentiableAt (hU.mem_nhds (hmem τ))).hasDerivAt
    have := h1.scomp τ (hℓd τ)
    exact this.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hd1 : deriv (fun τ : ℝ => F (ℓ τ)) = fun τ => d * deriv F (ℓ τ) := by
    funext τ; exact (hder F hF τ).deriv
  have hd2 : deriv (deriv (fun τ : ℝ => F (ℓ τ))) = fun τ => d * (d * deriv (deriv F) (ℓ τ)) := by
    rw [hd1]; funext τ; exact ((hder (deriv F) hF1 τ).const_mul d).deriv
  have hdiff0 : Differentiable ℝ (fun τ : ℝ => F (ℓ τ)) := fun τ => (hder F hF τ).differentiableAt
  have hdiff1 : Differentiable ℝ (fun τ : ℝ => d * deriv F (ℓ τ)) :=
    fun τ => ((hder (deriv F) hF1 τ).const_mul d).differentiableAt
  have hc2 : Continuous (fun τ : ℝ => d * (d * deriv (deriv F) (ℓ τ))) := by
    have hl : Continuous ℓ := by simp only [hℓ]; fun_prop
    have : Continuous (fun τ : ℝ => deriv (deriv F) (ℓ τ)) :=
      hF2.continuousOn.comp_continuous hl hmem
    fun_prop
  have hcd : ContDiff ℝ 2 (fun τ : ℝ => F (ℓ τ)) := by
    have h2 : ContDiff ℝ ((1 : ℕ) + 1) (fun τ : ℝ => F (ℓ τ)) := by
      refine (contDiff_succ_iff_deriv (𝕜 := ℝ)).mpr ⟨hdiff0, by simp, ?_⟩
      rw [hd1]
      have h1 : ContDiff ℝ ((0 : ℕ) + 1) (fun τ : ℝ => d * deriv F (ℓ τ)) := by
        refine (contDiff_succ_iff_deriv (𝕜 := ℝ)).mpr ⟨hdiff1, by simp, ?_⟩
        have : deriv (fun τ : ℝ => d * deriv F (ℓ τ)) = fun τ => d * (d * deriv (deriv F) (ℓ τ)) := by
          rw [← hd1, hd2]
        rw [this]
        simpa using ((contDiff_zero (𝕜 := ℝ)).mpr hc2)
      simpa using h1
    simpa [one_add_one_eq_two] using h2
  refine ⟨hcd, fun τ => ?_⟩
  have hcl : DifferentiableOn ℂ F (closedBall (ℓ τ) R) := hF.mono (hball τ)
  obtain ⟨c1, c2⟩ := cauchy_deriv_two hR hcl (hM τ)
  have h0 := hP₀ τ
  have hs : (ℓ τ + (R : ℂ)) ∈ sphere (ℓ τ) R := by simp [abs_of_pos hR]
  have hMn : 0 ≤ M τ := (norm_nonneg _).trans (hM τ _ hs)
  have hMR : 0 ≤ M τ / R := by positivity
  have hMR2 : 0 ≤ 2 * M τ / R ^ 2 := by positivity
  have hP0n : 0 ≤ P₀ τ := (norm_nonneg _).trans h0
  refine ⟨?_, ?_, ?_⟩
  · show ‖F (ℓ τ)‖ ≤ _
    linarith
  · rw [hd1]
    show ‖d * deriv F (ℓ τ)‖ ≤ _
    rw [norm_mul, hd, one_mul]
    linarith
  · rw [hd2]
    show ‖d * (d * deriv (deriv F) (ℓ τ))‖ ≤ _
    rw [norm_mul, norm_mul, hd, one_mul, one_mul]
    linarith

/-- info: 'FormalResearch.SignUncertainty.env2_holo_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms env2_holo_line

end FormalResearch.SignUncertainty
