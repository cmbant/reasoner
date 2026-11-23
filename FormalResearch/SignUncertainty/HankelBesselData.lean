module

public import FormalResearch.SignUncertainty.HankelAntiderivValue
public import FormalResearch.SignUncertainty.HankelFiveHalvesWitness

/-!
# `HankelKernelData` for the concrete Hankel kernel

`hankelKernelData`: the concrete `HankelKernelData c` with `φ = hankelPhi c`
(`FormalResearch/SignUncertainty/HankelBessel.lean`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Instantiating `HankelKernelData` -/

/-- The `w^{c/2-1}`-weighted antiderivative of `φ_c`, normalised by `(2π)^c/Γ(c)`, is bounded
(`∫_0^R J_{c-1}(x) dx` is bounded, `DLMF 10.22.1`). -/
theorem hankel_antideriv_bound {c : ℝ} (hc : 1 / 2 < c) :
    ∃ M, 0 ≤ M ∧ ∀ X ≥ 0,
      |((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * hankelPhi c w| ≤ M := by
  obtain ⟨M, hM⟩ := hankelPrimitive_bounded hc
  have hc0 : 0 < c := by linarith
  have hpos : 0 < (2 * π) ^ c / Real.Gamma c :=
    div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.Gamma_pos_of_pos hc0)
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 le_rfl)
  refine ⟨(2 * π) ^ c / Real.Gamma c * M, by positivity, fun X hX => ?_⟩
  rw [abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left (hM X hX) hpos.le

/-- ... and it tends to `1` (`∫_0^∞ J_{c-1}(x) dx = 1`). -/
theorem hankel_antideriv_tendsto {c : ℝ} (hc : 1 / 2 < c) :
    Tendsto (fun X => ((2 * π) ^ c / Real.Gamma c) *
      ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * hankelPhi c w) atTop (𝓝 1) := by
  have h := (hankelPrimitive_tendsto hc).const_mul ((2 * π) ^ c / Real.Gamma c)
  rw [hankelPrimitive_value hc] at h
  exact h

/-- **The concrete Hankel kernel data** at `c > 1/2` (`c ≥ 1` in the paper): `φ = hankelPhi c`. All
five fields are proved: `φ(0) = 1`, continuity, `|φ| ≤ 1`, and the boundedness and limit `1`
of the normalised `w^{c/2-1}`-antiderivative (`hankel_antideriv_bound`, `hankel_antideriv_tendsto`). -/
noncomputable def hankelKernelData {c : ℝ} (hc : 1 / 2 < c) : HankelKernelData c where
  φ := hankelPhi c
  φ_zero := hankelPhi_zero (by linarith)
  φ_cont := hankelPhi_continuous c
  φ_bound := ⟨1, zero_le_one, fun w _ => abs_hankelPhi_le_one hc w⟩
  antideriv_bound := hankel_antideriv_bound hc
  antideriv_tendsto := hankel_antideriv_tendsto hc

/-- For the concrete kernel, `hankelTransform` is `𝓗_c` of `eq:hankel`. -/
theorem hankelTransform_hankelKernelData {c : ℝ} (hc : 1 / 2 < c)
    (f : ℝ → ℝ) (Δ : ℝ) :
    hankelTransform c (hankelKernelData hc) f Δ = besselHankelTransform c f Δ := rfl

/-- The paper's feasibility condition for `f ∈ 𝒜_c^ε`: `ε f(0) = ∫ f ρ₀`. -/
theorem integral_eq_eps_mul_origin {c : ℝ} (hc : 1 / 2 < c)
    {ε : ℝ} {f : ℝ → ℝ} (hf : IsRadialEigenfn c (hankelKernelData hc) ε f) :
    ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s = ε * f 0 := by
  have h := hf.eigen 0 Set.self_mem_Ici
  rw [hankelTransform_hankelKernelData, besselHankelTransform_zero (by linarith)] at h
  exact h

/-- The one-level threshold `T_c^ε` of `fourier_mellin.tex` for the concrete kernel. -/
noncomputable def hankelThresholdBessel {c : ℝ} (hc : 1 / 2 < c) (ε : ℝ) : ℝ :=
  hankelThreshold c (hankelKernelData hc) ε

/-! ### Consistency check at `c = 5/2` -/

/-- The explicit `J_{3/2}` kernel `phi52` of `HankelFiveHalvesWitness` is `hankelPhi (5/2)`. -/
theorem hankelPhi_fiveHalves (w : ℝ) : hankelPhi (5 / 2) w = phi52 w := by
  unfold hankelPhi phi52
  rw [show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num,
    besselNorm_eq_integral (by norm_num), integral_neg_one_one_one_sub_sq_rpow_mul_cos (by norm_num)]
  unfold besselPoissonConst
  rw [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num]
  simp only [Real.rpow_one]
  have h1 : Real.Gamma (3 / 2 + 1) = 3 / 4 * √π := by
    have := gamma_nat_add_half 2
    rw [show (3 / 2 : ℝ) + 1 = ((2 : ℕ) : ℝ) + 1 / 2 by norm_num, this]
    norm_num [Nat.factorial]
    ring
  have h2 : Real.Gamma (3 / 2 + 1 / 2) = 1 := by
    rw [show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num]
    simp
  rw [h1, h2]
  have hsq : √π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  generalize (∫ t in (0 : ℝ)..1, (1 - t ^ 2) * Real.cos (4 * π * √w * t)) = I
  field_simp
  ring

/-! ### Axiom guards -/

/-- info: 'FormalResearch.SignUncertainty.abs_hankelPhi_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_hankelPhi_le_one

/-- info: 'FormalResearch.SignUncertainty.hankelPhi_eq_besselJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPhi_eq_besselJ

/-- info: 'FormalResearch.SignUncertainty.abs_besselHankelTransform_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_besselHankelTransform_le

/-- info: 'FormalResearch.SignUncertainty.hankelKernelData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelKernelData

/-- info: 'FormalResearch.SignUncertainty.hankel_antideriv_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_antideriv_tendsto

/-- info: 'FormalResearch.SignUncertainty.hankel_antideriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_antideriv_bound

/-- info: 'FormalResearch.SignUncertainty.hankelPhi_fiveHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPhi_fiveHalves

end FormalResearch.SignUncertainty
