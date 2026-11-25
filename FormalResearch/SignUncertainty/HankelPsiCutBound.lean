module

public import FormalResearch.SignUncertainty.HankelQuantC1Feasible

/-!
# Cut-crossing bound and `C¹` bound for `Ψ̃` on `D̄(0, R₁)` (`gt:7.7p` (d), "uniform bound across the cut")

Source: `CFT/sign_uncertainty/paper/langer_transport.tex`, Proposition 7.7' (d), first sentence: for every
`R₁ ≥ 1` there are effective `C₁(R₁)` and `c_A(R₁)` such that every normalised `f_c ∈ 𝒜_c^ε` has
`|Ψ̃'| ≤ C₁(R₁)` on `D̄(0, R₁)` (cut included).

The Lean statement is an instantiation of `hankelI_cut_bound` (type-(I) envelope `hankelPsi_envelope`, `C₀ = 60`)
and the Cauchy estimate on unit circles; the constants differ from the TeX ones
(`|Ψ̃| ≤ 3 e^{1.5R₁ + 1.37R₁²}`, TeX proof: contour shift to `Re ζ = c^{-1/3}` and a Gaussian integral):
here `|Ψ̃| ≤ 32 e^{5/2}·60 (1+R₁)^{3/2} e^{(4/3) R₁^{3/2}}` (from the Airy-envelope shift trick of `HankelQuantC1`),
the same shape of statement with a different, explicit constant, valid for `R₁ + 2 ≤ A_c := langerRadius c`.
-/

@[expose] public section

open Complex Set Metric
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **Cut-inclusive bound for the Hankel Langer-disc density** (`gt:7.7p` (d), uniform bound across the cut;
the constant is `32 e^{5/2}·60 (1+R₁)^{3/2} e^{(4/3)R₁^{3/2}}`, not the TeX's `3 e^{1.5R₁+1.37R₁²}`). -/
theorem hankelPsi_cut_bound {c ε R₁ : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hR₁ : 0 ≤ R₁) (hR : R₁ + 2 ≤ langerRadius c)
    {u : ℂ} (hu : ‖u‖ ≤ R₁) :
    ‖hankelPsi c f u‖ ≤ 32 * Real.exp (5 / 2) * 60 * (1 + R₁) ^ (3 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * R₁ ^ (3 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hb := hankelI_cut_bound (Ψ := hankelPsi c f) (R_dom := langerRadius c) (R₁ := R₁) (C_0 := 60) hR₁
    (by norm_num) (analyticOnNhd_hankelPsi hc0 hf)
    (fun u hu hcut => by
      have h := hankelPsi_envelope hc hf hε hM (u := u) (mem_closedBall_zero_iff.1 hu) hcut
      rw [hankel_norm_exp_eq_airyEnv] at h
      exact h)
    hR (mem_closedBall_zero_iff.2 hu)
  exact hb

/-- **`C¹` bound across the cut** on `D̄(0, R₁)` (`gt:7.7p` (d), `|Ψ̃'| ≤ C₁(R₁)`): Cauchy estimate on unit circles,
valid for `R₁ + 3 ≤ A_c`; `C₁(R₁) = 32 e^{5/2}·60 (2+R₁)^{3/2} e^{(4/3)(R₁+1)^{3/2}}`. -/
theorem hankelPsi_deriv_bound {c ε R₁ : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hR₁ : 0 ≤ R₁) (hR : R₁ + 3 ≤ langerRadius c)
    {u : ℂ} (hu : ‖u‖ ≤ R₁) :
    ‖deriv (hankelPsi c f) u‖ ≤ 32 * Real.exp (5 / 2) * 60 * (1 + (R₁ + 1)) ^ (3 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * (R₁ + 1) ^ (3 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hana := analyticOnNhd_hankelPsi hc0 hf
  have hsub : closedBall u 1 ⊆ closedBall (0 : ℂ) (langerRadius c) := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    have h1 : ‖z‖ ≤ ‖u‖ + 1 := by
      have := mem_closedBall_iff_norm.1 hz
      calc ‖z‖ = ‖(z - u) + u‖ := by ring_nf
        _ ≤ ‖z - u‖ + ‖u‖ := norm_add_le _ _
        _ ≤ 1 + ‖u‖ := by linarith
        _ = ‖u‖ + 1 := by ring
    linarith
  have hd : DiffContOnCl ℂ (hankelPsi c f) (ball u 1) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball u (by norm_num : (1 : ℝ) ≠ 0)]
    exact (hana.differentiableOn).mono hsub
  have hbd : ∀ z ∈ sphere u 1, ‖hankelPsi c f z‖ ≤ 32 * Real.exp (5 / 2) * 60 * (1 + (R₁ + 1)) ^ (3 / 2 : ℝ) *
      Real.exp ((4 / 3 : ℝ) * (R₁ + 1) ^ (3 / 2 : ℝ)) := by
    intro z hz
    have hz1 : ‖z - u‖ = 1 := by simpa [mem_sphere_iff_norm] using hz
    have : ‖z‖ ≤ R₁ + 1 := by
      calc ‖z‖ = ‖(z - u) + u‖ := by ring_nf
        _ ≤ ‖z - u‖ + ‖u‖ := norm_add_le _ _
        _ ≤ R₁ + 1 := by linarith
    exact hankelPsi_cut_bound hc hf hε hM (by linarith) (by linarith) this
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1) hd hbd
  simpa using this

/-- info: 'FormalResearch.SignUncertainty.hankelPsi_cut_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPsi_cut_bound

/-- info: 'FormalResearch.SignUncertainty.hankelPsi_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPsi_deriv_bound

end FormalResearch.SignUncertainty
