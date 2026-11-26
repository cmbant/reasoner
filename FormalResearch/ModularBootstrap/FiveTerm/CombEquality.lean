module

public import FormalResearch.ModularBootstrap.FiveTerm.CombRegularisation

/-!
# The equality criterion for the comb functional (FIVE-0; `cts:main`, `cts:equality-set`, `ctu:common-functional` (2))

Source: `CFT/modular_bootstrap/paper/constant_term_universality.tex`, Lemma ctu.2a (2): "Equality holds exactly when
`B_H ∈ [0,∞)` and `|H(iy)| ≤ B_H(y)` on `(0,1)`; no uniqueness of the minimiser is claimed."

`comb_equality_iff`: for `F ∈ HAdm` and an outer datum `G`, `𝒥[F] = α_tip g₁` iff for every `y ∈ (0,1)`,
`B_H(y)` is real and nonnegative and `|H(iy)| ≤ B_H(y)` (`H = F G`).  This uses the continuity of the defect integrand
on `(0,1)`; no uniqueness is claimed.  All proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma defectNum_eq_zero_iff (H : ℂ → ℂ) (y : ℝ) :
    defectNum H y = 0 ↔
      (edgeSum H y).im = 0 ∧ 0 ≤ (edgeSum H y).re ∧ ‖H (Complex.I * (y : ℂ))‖ ≤ (edgeSum H y).re := by
  unfold defectNum
  constructor
  · intro h
    have h1 : (edgeSum H y).re ≤ ‖edgeSum H y‖ := Complex.re_le_norm _
    have h2 : ‖edgeSum H y‖ ≤ max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ := le_max_right _ _
    have h3 : ‖H (Complex.I * (y : ℂ))‖ ≤ max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ := le_max_left _ _
    have hm : max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ = (edgeSum H y).re := by linarith only [h]
    have hn : ‖edgeSum H y‖ = (edgeSum H y).re := by linarith only [h1, h2, hm]
    have hre0 : 0 ≤ (edgeSum H y).re := by rw [← hn]; exact norm_nonneg _
    have hsq : ‖edgeSum H y‖ ^ 2 = (edgeSum H y).re ^ 2 + (edgeSum H y).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn] at hsq
    refine ⟨?_, hre0, by linarith only [h3, hm]⟩
    nlinarith only [hsq, sq_nonneg (edgeSum H y).im]
  · rintro ⟨him, hre, hle⟩
    have hn : ‖edgeSum H y‖ = (edgeSum H y).re := by
      have : edgeSum H y = ((edgeSum H y).re : ℂ) := Complex.ext (by simp) (by simpa using him)
      conv_lhs => rw [this]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre]
    rw [hn, max_eq_right hle, sub_self]

/-- **Equality criterion** (`ctu:common-functional` (2)). -/
theorem comb_equality_iff {F G : ℂ → ℂ} {c1 g1 : ℝ} {W : ℝ → ℝ} {K : ℝ → ℂ}
    (hF : HAdm F c1) (hG : OuterDatum W K g1 G) :
    combJ W K F = alphaTip * g1 ↔
      ∀ y ∈ Ioo (0 : ℝ) 1,
        (edgeSum (fun z => F z * G z) y).im = 0 ∧ 0 ≤ (edgeSum (fun z => F z * G z) y).re ∧
          ‖F (Complex.I * (y : ℂ)) * G (Complex.I * (y : ℂ))‖ ≤ (edgeSum (fun z => F z * G z) y).re := by
  have hH := hF.mul_datum hG
  obtain ⟨_, h⟩ := comb_defect_identity hF hG
  have hint := defectInt_integrable hH
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] defectInt (fun z => F z * G z) :=
    Eventually.of_forall (fun y => defectInt_nonneg _)
  constructor
  · intro heq
    rw [h] at heq
    have h0 : ∫ y in Ioo (0 : ℝ) 1, defectInt (fun z => F z * G z) y = 0 := by
      have hpos := alphaC_pos
      have hnn0 : 0 ≤ ∫ y in Ioo (0 : ℝ) 1, defectInt (fun z => F z * G z) y :=
        setIntegral_nonneg measurableSet_Ioo (fun y _ => defectInt_nonneg _)
      by_contra hne
      have : 0 < ∫ y in Ioo (0 : ℝ) 1, defectInt (fun z => F z * G z) y :=
        lt_of_le_of_ne hnn0 (Ne.symm hne)
      nlinarith only [heq, hpos, this]
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0
    have heqon := Measure.eqOn_open_of_ae_eq hae isOpen_Ioo (continuousOn_defectInt hH) continuousOn_const
    intro y hy
    have := heqon hy
    simp only [Pi.zero_apply] at this
    unfold defectInt at this
    have hy2 : (y ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hy.1.ne'
    have hz : defectNum (fun z => F z * G z) y = 0 := by
      rcases div_eq_zero_iff.mp this with h1 | h1
      · exact h1
      · exact absurd h1 hy2
    exact (defectNum_eq_zero_iff _ y).mp hz
  · intro hall
    rw [h]
    have h0 : ∫ y in Ioo (0 : ℝ) 1, defectInt (fun z => F z * G z) y = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))]
      · simp
      · intro y hy
        have := (defectNum_eq_zero_iff _ y).mpr (hall y hy)
        simp only [defectInt, this, zero_div]
    rw [h0]; ring

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.comb_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.comb_equality_iff
