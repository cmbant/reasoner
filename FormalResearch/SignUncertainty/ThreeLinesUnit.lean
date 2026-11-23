module

public import Mathlib.Analysis.Complex.Hadamard
public import FormalResearch.SignUncertainty.MellinMajorantBound

/-!
# Hadamard three-lines on the unit strip, in the form used for `eq:ce-three-lines`

For a function `F` on the strip `0 ≤ Re z ≤ 1`, holomorphic inside and continuous up to the
boundary, bounded on the closed strip, with `‖F‖ ≤ a` on `Re z = 0` and `‖F‖ ≤ b` on `Re z = 1`,
we have `‖F z‖ ≤ a ^ (1 - Re z) * b ^ (Re z)` on the closed strip (`three_lines_unit`).

Classes:
* `three_lines_unit` (statement 1): a restatement, in the hypothesis form of the target
  `eq:ce-three-lines`, of Mathlib's `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`.
  The new content is only the conversion of `BddAbove` and of the preimage-of-singleton edge
  hypotheses (`re ⁻¹' {0}`, `re ⁻¹' {1}`) into the stated form. Proof: Mathlib.
* `mellinW_bddAbove_strip` (statement 2, the check): a restatement of `norm_mellinW_le`
  (`FormalResearch.SignUncertainty.MellinMajorantBound`) in the bounded-on-the-closed-strip form that
  statement 1 needs. It is proved under the sign hypothesis `ε = 1 ∨ ε = -1`, which `norm_mellinW_le`
  requires and `IsHankelEigenfn` alone does not supply. The three-lines corollary for `mellinW` itself
  is not stated here.
* `rpow_mul_le_max` and `rpow_mul_scale` (statement 3, real corollary): elementary facts about real
  powers, proved from Mathlib's `Real.rpow_add`, `Real.mul_rpow` and `Real.rpow_le_rpow`.

Negative regression (stated only, not proved and no explicit counterexample checked here). The
growth hypothesis `hB` cannot simply be dropped: the edge bounds `a`, `b` control the interior only
under a growth bound on the closed strip (Phragmén–Lindelöf type; the classical counterexamples
have double-exponential growth inside the strip).
-/

@[expose] public section

open Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

/-- Hadamard three-lines on the closed unit strip (statement 1).
If `F` is differentiable on the open strip, continuous on its closure, bounded on the closed strip,
`‖F (t i)‖ ≤ a` for all real `t` and `‖F (1 + t i)‖ ≤ b` for all real `t`, then
`‖F z‖ ≤ a ^ (1 - Re z) * b ^ (Re z)` for `0 ≤ Re z ≤ 1`.
Class: proved (restatement of Mathlib's `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`,
with the edge hypotheses converted). -/
theorem three_lines_unit {F : ℂ → ℂ} {a b : ℝ}
    (hd : DiffContOnCl ℂ F (Complex.re ⁻¹' Set.Ioo (0:ℝ) 1))
    (hB : ∃ M, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖F z‖ ≤ M)
    (ha : ∀ t : ℝ, ‖F (t * Complex.I)‖ ≤ a)
    (hb : ∀ t : ℝ, ‖F (1 + t * Complex.I)‖ ≤ b) {z : ℂ} (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1) :
    ‖F z‖ ≤ a ^ (1 - z.re) * b ^ z.re := by
  obtain ⟨M, hM⟩ := hB
  have hB' : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hw0, hw1⟩ := hw
    exact hM w hw0 hw1
  have ha' : ∀ w ∈ re ⁻¹' {0}, ‖F w‖ ≤ a := by
    intro w hw
    have hw0 : w.re = 0 := hw
    have hwe : (w.im : ℂ) * Complex.I = w := Complex.ext (by simp [hw0]) (by simp)
    have h := ha w.im
    rw [hwe] at h
    exact h
  have hb' : ∀ w ∈ re ⁻¹' {1}, ‖F w‖ ≤ b := by
    intro w hw
    have hw1 : w.re = 1 := hw
    have hwe : 1 + (w.im : ℂ) * Complex.I = w := Complex.ext (by simp [hw1]) (by simp)
    have h := hb w.im
    rw [hwe] at h
    exact h
  exact Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (show z ∈ re ⁻¹' Icc (0:ℝ) 1 from ⟨h0, h1⟩) hd hB' ha' hb'

/-- Statement 2 (check only): the Mellin function `mellinW c ε f` is bounded on the closed strip
`0 ≤ Re ζ ≤ 1`, so statement 1 applies to it. The bound is `M[f] e^{1/(6c)}`, from
`norm_mellinW_le`. Requires `3/2 < c` and the sign `ε = 1 ∨ ε = -1`.
Class: proved (from `norm_mellinW_le`). -/
theorem mellinW_bddAbove_strip {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1) :
    ∃ M, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖mellinW c ε f ζ‖ ≤ M :=
  ⟨hankelMass c f * Real.exp (1 / (6 * c)), fun _ h0 h1 => norm_mellinW_le hc hf hε h0 h1⟩

/-- Statement 3a (real corollary): for `0 < σ < 1` and `a, b > 0`,
`a ^ (1 - σ) * b ^ σ ≤ max a b`.
Class: proved (elementary real-power inequality). -/
theorem rpow_mul_le_max {σ a b : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ha : 0 < a) (hb : 0 < b) :
    a ^ (1 - σ) * b ^ σ ≤ max a b := by
  have hm : 0 < max a b := lt_max_of_lt_left ha
  have hsum : max a b ^ (1 - σ) * max a b ^ σ = max a b := by
    rw [← Real.rpow_add hm, sub_add_cancel, Real.rpow_one]
  have hA : a ^ (1 - σ) ≤ max a b ^ (1 - σ) :=
    Real.rpow_le_rpow ha.le (le_max_left a b) (by linarith)
  have hB : b ^ σ ≤ max a b ^ σ :=
    Real.rpow_le_rpow hb.le (le_max_right a b) hσ0.le
  calc a ^ (1 - σ) * b ^ σ ≤ max a b ^ (1 - σ) * max a b ^ σ :=
        mul_le_mul hA hB (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hm.le _)
    _ = max a b := hsum

/-- Statement 3b (real corollary): scaling identity for `s > 0`, `a, b ≥ 0`:
`(a * s) ^ (1 - σ) * (b * s) ^ σ = s * (a ^ (1 - σ) * b ^ σ)`.
Class: proved (elementary real-power identity). -/
theorem rpow_mul_scale {σ a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) :
    (a * s) ^ (1 - σ) * (b * s) ^ σ = s * (a ^ (1 - σ) * b ^ σ) := by
  have hss : s ^ (1 - σ) * s ^ σ = s := by
    rw [← Real.rpow_add hs, sub_add_cancel, Real.rpow_one]
  rw [Real.mul_rpow ha hs.le, Real.mul_rpow hb hs.le]
  linear_combination (a ^ (1 - σ) * b ^ σ) * hss

/-- info: 'FormalResearch.SignUncertainty.three_lines_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms three_lines_unit

/-- info: 'FormalResearch.SignUncertainty.mellinW_bddAbove_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinW_bddAbove_strip

/-- info: 'FormalResearch.SignUncertainty.rpow_mul_le_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rpow_mul_le_max

/-- info: 'FormalResearch.SignUncertainty.rpow_mul_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rpow_mul_scale

end FormalResearch.SignUncertainty
