module

public import Mathlib

/-!
# Jacobi operator package: normalisation ratios

This is the elementary finite-dimensional ratio estimate from Paper J, stated for any real normed
vector space and an already projected vector `z`. The existence of a coordinate projection is not
needed after replacing `P Ψ` by `z`.
-/

@[expose] public section

namespace FormalResearch.MatrixAnalysis

/-- Paper J's stability bound for two scalar normalisations. -/
theorem jop_normalisation_ratio {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f g z : V) {s t c₀ ε δ : ℝ} (hs : s ≠ 0) (ht : t ≠ 0)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hδ : 0 ≤ δ) (hδc : δ < c₀)
    (hz : c₀ ≤ ‖z‖) (hfg : ‖f - g‖ ≤ ε * ‖g‖)
    (hsf : ‖s • f - z‖ ≤ δ) (htg : ‖t • g - z‖ ≤ δ) :
    |s / t - 1| ≤ (ε + 2 * δ / (c₀ - δ)) / (1 - ε) := by
  let ρ : ℝ := s / t
  have ht0 : 0 < |t| := abs_pos.mpr ht
  have hscale : c₀ - δ ≤ |t| * ‖g‖ := by
    have hnorm : ‖t • g‖ = |t| * ‖g‖ := by rw [norm_smul, Real.norm_eq_abs]
    have hn := norm_sub_norm_le z (t • g)
    have hn' : ‖z‖ - ‖z - t • g‖ ≤ ‖t • g‖ := by linarith [hn]
    have hd : ‖z - t • g‖ = ‖t • g - z‖ := norm_sub_rev _ _
    calc c₀ - δ ≤ ‖z‖ - ‖z - t • g‖ := by rw [hd]; linarith [hz, htg]
      _ ≤ ‖t • g‖ := hn'
      _ = |t| * ‖g‖ := hnorm
  have hg0 : 0 < ‖g‖ := by
    by_contra hn
    have : ‖g‖ = 0 := by simpa [not_lt] using hn
    have : g = 0 := norm_eq_zero.mp this
    subst g
    simp at hscale
    linarith
  have hdiff : ‖ρ • f - g‖ ≤ 2 * δ / |t| := by
    have hnum : ‖s • f - t • g‖ ≤ 2 * δ := by
      calc ‖s • f - t • g‖ = ‖(s • f - z) + (z - t • g)‖ := by congr 1; abel
        _ ≤ ‖s • f - z‖ + ‖z - t • g‖ := norm_add_le _ _
        _ ≤ 2 * δ := by rw [norm_sub_rev z (t • g)]; linarith [hsf, htg]
    have heq : ρ • f - g = (1 / t) • (s • f - t • g) := by
      rw [smul_sub, smul_smul, smul_smul]
      have hρ : ρ = (1 / t) * s := by dsimp [ρ]; field_simp
      have hti : (1 / t) * t = 1 := by field_simp
      rw [hρ, hti]
      simp
    rw [heq, norm_smul, Real.norm_eq_abs]
    have habs : |1 / t| = 1 / |t| := by rw [abs_div, abs_one]
    rw [habs]
    simpa [div_eq_mul_inv, mul_comm] using
      (mul_le_mul_of_nonneg_left hnum (by positivity : 0 ≤ 1 / |t|))
  have hkey : |ρ - 1| * ‖g‖ ≤ 2 * δ / |t| + |ρ| * (ε * ‖g‖) := by
    have heq : (ρ - 1) • g = (ρ • f - g) + ρ • (g - f) := by module
    have htriangle : ‖(ρ • f - g) + ρ • (g - f)‖ ≤ ‖ρ • f - g‖ + ‖ρ • (g - f)‖ := norm_add_le _ _
    rw [← heq, norm_smul, Real.norm_eq_abs] at htriangle
    calc |ρ - 1| * ‖g‖ ≤ ‖ρ • f - g‖ + ‖ρ • (g - f)‖ := by simpa [mul_comm] using htriangle
      _ ≤ 2 * δ / |t| + |ρ| * (ε * ‖g‖) := by
        rw [norm_smul, Real.norm_eq_abs]
        have hgf : ‖g - f‖ ≤ ε * ‖g‖ := by rwa [norm_sub_rev]
        have hmul := mul_le_mul_of_nonneg_left hgf (abs_nonneg ρ)
        nlinarith [hdiff, hmul]
  have hdelta : 2 * δ / |t| ≤ (2 * δ / (c₀ - δ)) * ‖g‖ := by
    have hpos : 0 < c₀ - δ := by linarith
    rw [div_le_iff₀ ht0]
    have hm := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2 * δ / (c₀ - δ))
    have hcanc : (2 * δ / (c₀ - δ)) * (c₀ - δ) = 2 * δ := by field_simp
    nlinarith [hm, hcanc]
  have hkey' : |ρ - 1| * ‖g‖ ≤ (ε * |ρ| + 2 * δ / (c₀ - δ)) * ‖g‖ := by
    nlinarith [hkey, hdelta, mul_nonneg hε (le_of_lt hg0)]
  have hratio : |ρ - 1| ≤ ε * |ρ| + 2 * δ / (c₀ - δ) :=
    le_of_mul_le_mul_right hkey' hg0
  have hfinal : |ρ - 1| ≤ (ε + 2 * δ / (c₀ - δ)) / (1 - ε) := by
    have hρ : |ρ| ≤ 1 + |ρ - 1| := by
      have h := norm_add_le (ρ - 1) (1 : ℝ)
      have heq : ρ = (ρ - 1) + 1 := by ring
      rw [heq] at h
      simpa [Real.norm_eq_abs, add_comm] using h
    have hden : 0 < 1 - ε := by linarith
    apply (le_div_iff₀ hden).2
    nlinarith [hratio, hρ]
  simpa [ρ, abs_sub_comm] using hfinal

/-- info: 'FormalResearch.MatrixAnalysis.jop_normalisation_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.MatrixAnalysis.jop_normalisation_ratio

end FormalResearch.MatrixAnalysis
