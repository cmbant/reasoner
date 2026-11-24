module

public import FormalResearch.SignUncertainty.HankelWtBasics
public import FormalResearch.SignUncertainty.ThreeLinesUnit

/-!
# Closed-strip data of `W̃_c` (`(MS1)` of `teb:mellin`, M5-S5)

`hankelWtS c ε f ζ = e^{-c ℋ(ζ)} Fm(ζ)` with `Fm = mellinFm` the reflected Mellin function
(`M̃_f(c(1-ζ))` for `Re ζ ≤ 1/2`, `ε M̃_f(cζ)` for `Re ζ > 1/2`).  On `0 ≤ Re ζ < 1` it equals
`hankelWt c f ζ` (`hankelWtS_eq`).  The plain `hankelWt` is not continuous at `Re ζ = 1`
(`mellinRaw` has no convergent integral at `Re z = 0`), which is why the closed-strip form is a separate
definition.  For `c > 3/2`, `f ∈ 𝒜_c^ε`, `ε = ±1`:

* `hankelWtS_continuousOn`: continuous on `0 ≤ Re ζ ≤ 1`;
* `hankelWtS_differentiableOn`: holomorphic on `0 < Re ζ < 1`;
* `hankelWtS_one_sub`: `W̃(1-ζ) = ε W̃(ζ)` on the closed strip;
* `hankelWtS_norm_le`: `‖W̃(ζ)‖ ≤ M[f] e^{1/(6c)} (1+‖ζ‖)^{1/2}` on the closed strip (Phragmén–Lindelöf,
  `norm_mellinW_le`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `W̃_c` on the closed strip: `e^{-cℋ(ζ)} Fm(ζ)`. -/
noncomputable def hankelWtS (c ε : ℝ) (f : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (-((c : ℂ) * hInt ζ)) * mellinFm c ε f ζ

theorem hankelWtS_eq {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {ζ : ℂ}
    (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1) : hankelWtS c ε f ζ = hankelWt c f ζ := by
  unfold hankelWtS hankelWt
  rw [mellinFm_eq hc hf h0 h1]

theorem hankelWtS_continuousOn {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    ContinuousOn (hankelWtS c ε f) {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := by
  have hH : ContinuousOn hInt {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    differentiableOn_hInt.continuousOn.mono closedStrip_subset
  have hE : ContinuousOn (fun ζ : ℂ => Complex.exp (-((c : ℂ) * hInt ζ)))
      {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (continuous_exp.comp_continuousOn ((continuousOn_const.mul hH).neg))
  exact hE.mul (continuousOn_mellinFm hc hf)

theorem hankelWtS_differentiableOn {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    DifferentiableOn ℂ (hankelWtS c ε f) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} := by
  refine (hankelWt_differentiableOn (by linarith) hf).congr fun ζ hζ => ?_
  exact hankelWtS_eq hc hf hζ.1.le hζ.2

/-- Reflection of the closed-strip Mellin function. -/
theorem mellinFm_one_sub {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    mellinFm c ε f (1 - ζ) = (ε : ℂ) * mellinFm c ε f ζ := by
  have hε2 : (ε : ℂ) * (ε : ℂ) = 1 := by
    rcases hε with h | h <;> simp [h]
  have hc0 : 0 < c := by linarith
  have hre : (1 - ζ).re = 1 - ζ.re := by simp
  rcases lt_trichotomy ζ.re (1 / 2) with hlt | heq | hgt
  · have a1 : ¬ ((1 - ζ).re ≤ 1 / 2) := by rw [hre]; linarith
    unfold mellinFm
    rw [if_neg a1, if_pos hlt.le]
  · have a1 : (1 - ζ).re ≤ 1 / 2 := by rw [hre]; linarith
    have hcz : ((c : ℂ) * ζ).re = c * ζ.re := by simp
    have hrefl := mellinStrip_reflection hc hf (z := (c : ℂ) * ζ)
      (by rw [hcz, heq]; linarith) (by rw [hcz, heq]; linarith)
    unfold mellinFm
    rw [if_pos a1, if_pos heq.le]
    have e1 : (c : ℂ) * (1 - (1 - ζ)) = (c : ℂ) * ζ := by ring
    have e2 : (c : ℂ) * (1 - ζ) = (c : ℂ) - (c : ℂ) * ζ := by ring
    rw [e1, e2, hrefl, ← mul_assoc, hε2, one_mul]
  · have a1 : (1 - ζ).re ≤ 1 / 2 := by rw [hre]; linarith
    have a2 : ¬ (ζ.re ≤ 1 / 2) := not_le.mpr hgt
    unfold mellinFm
    rw [if_pos a1, if_neg a2, ← mul_assoc, hε2, one_mul]
    congr 1; ring_nf

theorem hankelWtS_one_sub {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    hankelWtS c ε f (1 - ζ) = (ε : ℂ) * hankelWtS c ε f ζ := by
  have hζ : ζ ∈ hStrip := closedStrip_subset ⟨h0, h1⟩
  unfold hankelWtS
  rw [hInt_one_sub hζ, mellinFm_one_sub hc hf hε h0 h1]
  ring

theorem hankelWtS_norm_le {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re ≤ 1) :
    ‖hankelWtS c ε f ζ‖ ≤
      hankelMass c f * Real.exp (1 / (6 * c)) * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) := by
  have hW := norm_mellinW_le hc hf hε h0 h1
  have hne := sqrt_cpow_ne_zero h0
  have hid : hankelWtS c ε f ζ = mellinW c ε f ζ * (1 + ζ) ^ (1 / 2 : ℂ) := by
    unfold hankelWtS mellinW
    field_simp
  have hn : ‖(1 + ζ) ^ (1 / 2 : ℂ)‖ ≤ (1 + ‖ζ‖) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_of_ne_zero (one_add_ne_zero h0)]
    have : ((1 / 2 : ℂ)).im = 0 := by simp
    rw [this, mul_zero, Real.exp_zero, div_one]
    have h12 : ((1 / 2 : ℂ)).re = 1 / 2 := by simp
    rw [h12]
    exact Real.rpow_le_rpow (norm_nonneg _)
      ((norm_add_le _ _).trans (by simp)) (by norm_num)
  rw [hid, norm_mul]
  calc ‖mellinW c ε f ζ‖ * ‖(1 + ζ) ^ (1 / 2 : ℂ)‖
      ≤ (hankelMass c f * Real.exp (1 / (6 * c))) * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) :=
        mul_le_mul hW hn (norm_nonneg _) (by
          have := hankelMass_nonneg (by linarith : 0 < c) f
          positivity)
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.hankelWtS_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWtS_continuousOn

/-- info: 'FormalResearch.SignUncertainty.hankelWtS_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWtS_differentiableOn

/-- info: 'FormalResearch.SignUncertainty.hankelWtS_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWtS_one_sub

/-- info: 'FormalResearch.SignUncertainty.hankelWtS_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWtS_norm_le

/-- info: 'FormalResearch.SignUncertainty.hankelWtS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelWtS_eq

/-- info: 'FormalResearch.SignUncertainty.mellinFm_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinFm_one_sub

end FormalResearch.SignUncertainty
