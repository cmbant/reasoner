module

public import FormalResearch.SignUncertainty.CtSdSegRem
public import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy estimates for the amplitude along the connecting segment (`ct:cfu` Step 3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3.  **Proved.**
If `g_s` is holomorphic and bounded by `C` on `B(0, 3 s₁)`, then `g_W(w) = g_s(λw)` has, for `|w| ≤ R = s₁/λ`,
derivatives `g_W' = λ g_s'(λ w)`, `g_W'' = λ² g_s''(λ w)` with `|g_W'| ≤ 2C/R`, `|g_W''| ≤ 2C/R²`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real

namespace FormalResearch.SignUncertainty.CtSd

lemma cauchy_deriv_le {f : ℂ → ℂ} {ρ0 C r : ℝ} {z0 : ℂ} (hd : DifferentiableOn ℂ f (ball 0 ρ0))
    (hb : ∀ z ∈ ball (0 : ℂ) ρ0, ‖f z‖ ≤ C) (hr : 0 < r) (hz : ‖z0‖ + r < ρ0) :
    ‖deriv f z0‖ ≤ C / r := by
  have hsub : closedBall z0 r ⊆ ball (0 : ℂ) ρ0 := by
    intro z hz'
    rw [mem_closedBall, dist_eq_norm] at hz'
    rw [mem_ball, dist_zero_right]
    calc ‖z‖ = ‖(z - z0) + z0‖ := by ring_nf
      _ ≤ ‖z - z0‖ + ‖z0‖ := norm_add_le _ _
      _ < ρ0 := by linarith
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hd.diffContOnCl_ball hsub) ?_
  intro z hz'
  exact hb z (hsub (sphere_subset_closedBall hz'))

/-- Data of `g_W(w) = g_s(λ w)` along `|w| ≤ R`. -/
theorem gW_data {gs : ℂ → ℂ} {s1 lam R C : ℝ} (hs1 : 0 < s1) (hlam : 0 < lam) (hsR : s1 = lam * R)
    (hd : DifferentiableOn ℂ gs (ball 0 (3 * s1))) (hb : ∀ z ∈ ball (0 : ℂ) (3 * s1), ‖gs z‖ ≤ C)
    {w : ℂ} (hw : ‖w‖ ≤ R) :
    HasDerivAt (fun w => gs ((lam : ℂ) * w)) ((lam : ℂ) * deriv gs ((lam : ℂ) * w)) w ∧
    HasDerivAt (fun w => (lam : ℂ) * deriv gs ((lam : ℂ) * w))
      ((lam : ℂ) ^ 2 * deriv (deriv gs) ((lam : ℂ) * w)) w ∧
    ‖gs ((lam : ℂ) * w)‖ ≤ C ∧ ‖(lam : ℂ) * deriv gs ((lam : ℂ) * w)‖ ≤ 2 * C / R ∧
    ‖(lam : ℂ) ^ 2 * deriv (deriv gs) ((lam : ℂ) * w)‖ ≤ 2 * C / R ^ 2 := by
  have hR : 0 < R := by
    by_contra h
    push_neg at h
    nlinarith [hsR, hlam, hs1]
  have hz : ‖(lam : ℂ) * w‖ ≤ s1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam, hsR]
    exact mul_le_mul_of_nonneg_left hw hlam.le
  have hopen : IsOpen (ball (0 : ℂ) (3 * s1)) := isOpen_ball
  have hmem : (lam : ℂ) * w ∈ ball (0 : ℂ) (3 * s1) := by
    rw [mem_ball, dist_zero_right]; linarith
  have hdd : DifferentiableOn ℂ (deriv gs) (ball 0 (3 * s1)) := hd.deriv hopen
  -- first derivative bound on the smaller ball
  have hb1 : ∀ z ∈ ball (0 : ℂ) (3 * s1 - 9 / 10 * s1), ‖deriv gs z‖ ≤ C / (9 / 10 * s1) := by
    intro z hz'
    rw [mem_ball, dist_zero_right] at hz'
    exact cauchy_deriv_le hd hb (by positivity) (by linarith)
  have hd1 : ‖deriv gs ((lam : ℂ) * w)‖ ≤ C / (9 / 10 * s1) := by
    refine hb1 _ ?_
    rw [mem_ball, dist_zero_right]; linarith
  have hdd' : DifferentiableOn ℂ (deriv gs) (ball 0 (3 * s1 - 9 / 10 * s1)) :=
    hdd.mono (ball_subset_ball (by linarith))
  have hd2 : ‖deriv (deriv gs) ((lam : ℂ) * w)‖ ≤ C / (9 / 10 * s1) / (9 / 10 * s1) :=
    cauchy_deriv_le hdd' hb1 (by positivity) (by linarith)
  have hgs : HasDerivAt gs (deriv gs ((lam : ℂ) * w)) ((lam : ℂ) * w) :=
    (hd.differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
  have hgs1 : HasDerivAt (deriv gs) (deriv (deriv gs) ((lam : ℂ) * w)) ((lam : ℂ) * w) :=
    (hdd.differentiableAt (hopen.mem_nhds hmem)).hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => (lam : ℂ) * w) (lam : ℂ) w := by
    simpa using (hasDerivAt_id w).const_mul (lam : ℂ)
  refine ⟨?_, ?_, hb _ hmem, ?_, ?_⟩
  · have := hgs.scomp w hlin
    simpa [smul_eq_mul, Function.comp_def] using this
  · have := (hgs1.scomp w hlin).const_mul (lam : ℂ)
    convert this using 1
    simp [smul_eq_mul]; ring
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
    calc lam * ‖deriv gs ((lam : ℂ) * w)‖ ≤ lam * (C / (9 / 10 * s1)) :=
          mul_le_mul_of_nonneg_left hd1 hlam.le
      _ ≤ 2 * C / R := by
          have hC : 0 ≤ C := (norm_nonneg _).trans (hb _ hmem)
          rw [hsR]
          have e : lam * (C / (9 / 10 * (lam * R))) = (10 / 9) * C / R := by field_simp
          rw [e]
          have : (10 / 9) * C / R ≤ 2 * C / R := by
            apply div_le_div_of_nonneg_right _ hR.le; nlinarith
          exact this
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
    calc lam ^ 2 * ‖deriv (deriv gs) ((lam : ℂ) * w)‖ ≤ lam ^ 2 * (C / (9 / 10 * s1) / (9 / 10 * s1)) :=
          mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ ≤ 2 * C / R ^ 2 := by
          have hC : 0 ≤ C := (norm_nonneg _).trans (hb _ hmem)
          rw [hsR]
          have e : lam ^ 2 * (C / (9 / 10 * (lam * R)) / (9 / 10 * (lam * R))) = (100 / 81) * C / R ^ 2 := by
            field_simp; ring
          rw [e]
          apply div_le_div_of_nonneg_right _ (by positivity); nlinarith

/-- info: 'FormalResearch.SignUncertainty.CtSd.gW_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gW_data

end FormalResearch.SignUncertainty.CtSd
