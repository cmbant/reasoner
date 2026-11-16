module

public import FormalResearch.Special.AiryBiReal
public import FormalResearch.Special.AiryEnvelopeNeg

/-!
# Monotonicity of `Bi/Ai` and positivity of `Bi` on `[0, ∞)`

From the Wronskian `Ai Bi' - Ai' Bi = 1/π` (`airyWronskian_real`): `(Bi/Ai)' = 1/(π Ai²) > 0` wherever `Ai ≠ 0`, so
`Bi/Ai` is strictly increasing on `[-1, ∞)` (`strictMonoOn_airyBi_div_airyAi`, where `Ai > 0`).  With
`Bi(0) = √3 Ai(0)`, `Bi'(0) = -√3 Ai'(0)` this gives, on `[0, ∞)`:

* `airyBi_ge_sqrt3_mul_airyAi`: `Bi ≥ √3 Ai`; hence `Bi > 0`;
* `airyBiDeriv_ge_zero`: `Bi' ≥ Bi'(0) > 0` (since `Bi'' = x Bi ≥ 0`), so `Bi` is strictly increasing on `[0, ∞)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma airyBi_zero_real : airyBi 0 = √3 * airyAi 0 := by
  have h := airyBiC_zero
  have e1 := airyBiC_ofReal 0
  have e2 := airyAiC_ofReal 0
  rw [Complex.ofReal_zero] at e1 e2
  rw [e1, e2] at h
  exact_mod_cast h

lemma airyBiDeriv_zero_real : airyBiDeriv 0 = -(√3 * airyAi' 0) := by
  have h := airyBiC'_zero
  have e1 := airyBiC'_ofReal 0
  have e2 := deriv_airyAiC_ofReal 0
  rw [Complex.ofReal_zero] at e1 e2
  rw [e1, e2] at h
  have : (airyBiDeriv 0 : ℂ) = ((-(√3 * airyAi' 0) : ℝ) : ℂ) := by rw [h]; push_cast; ring
  exact_mod_cast this

lemma hasDerivAt_airyBi_div_airyAi {x : ℝ} (h : airyAi x ≠ 0) :
    HasDerivAt (fun x => airyBi x / airyAi x) (1 / (π * airyAi x ^ 2)) x := by
  have := (hasDerivAt_airyBi x).div (hasDerivAt_airyAi x) h
  refine this.congr_deriv ?_
  have hW := airyWronskian_real x
  have hn : airyBiDeriv x * airyAi x - airyBi x * airyAi' x = 1 / π := by linarith [hW]
  rw [hn]
  have hp := Real.pi_pos
  field_simp

/-- `Bi/Ai` is strictly increasing on `[-1, ∞)` (where `Ai > 0`). -/
theorem strictMonoOn_airyBi_div_airyAi : StrictMonoOn (fun x => airyBi x / airyAi x) (Ici (-1)) := by
  have hpos : ∀ x ∈ Ici (-1 : ℝ), 0 < airyAi x := fun x hx => airyAi_pos_of_neg_one_le hx
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
  · intro x hx
    exact (hasDerivAt_airyBi_div_airyAi (hpos x hx).ne').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_airyBi_div_airyAi (hpos x (le_of_lt hx)).ne').deriv]
    have := hpos x (le_of_lt hx)
    have hp := Real.pi_pos
    positivity


lemma airyBi_zero_pos : 0 < airyBi 0 := by
  rw [airyBi_zero_real]
  have := airyAi_pos (le_refl (0 : ℝ))
  have h3 : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  positivity

lemma airyBiDeriv_zero_pos : 0 < airyBiDeriv 0 := by
  rw [airyBiDeriv_zero_real]
  have := airyAi'_neg (le_refl (0 : ℝ))
  have h3 : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

/-- **`Bi ≥ √3 Ai` on `[0, ∞)`** (monotonicity of `Bi/Ai` and `Bi(0)/Ai(0) = √3`). -/
theorem airyBi_ge_sqrt3_mul_airyAi {x : ℝ} (hx : 0 ≤ x) : √3 * airyAi x ≤ airyBi x := by
  have hA := airyAi_pos hx
  have h := strictMonoOn_airyBi_div_airyAi.monotoneOn (show (0 : ℝ) ∈ Ici (-1) by
    simp only [mem_Ici]; norm_num) (show x ∈ Ici (-1) by simp only [mem_Ici]; linarith) hx
  rw [airyBi_zero_real, mul_div_assoc, div_self (airyAi_pos (le_refl 0)).ne', mul_one] at h
  rw [le_div_iff₀ hA] at h
  linarith

/-- `Bi > 0` on `[0, ∞)`. -/
theorem airyBi_pos {x : ℝ} (hx : 0 ≤ x) : 0 < airyBi x := by
  have := airyBi_ge_sqrt3_mul_airyAi hx
  have hA := airyAi_pos hx
  have h3 : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  nlinarith

/-- `Bi' ≥ Bi'(0) > 0` on `[0, ∞)`. -/
theorem airyBiDeriv_ge_zero {x : ℝ} (hx : 0 ≤ x) : airyBiDeriv 0 ≤ airyBiDeriv x := by
  have hmono : MonotoneOn airyBiDeriv (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun y _ => (hasDerivAt_airyBiDeriv y).continuousAt.continuousWithinAt
    · exact fun y _ => (hasDerivAt_airyBiDeriv y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hasDerivAt_airyBiDeriv y).deriv]
      exact mul_nonneg (le_of_lt hy) (airyBi_pos (le_of_lt hy)).le
  exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx

theorem airyBiDeriv_pos {x : ℝ} (hx : 0 ≤ x) : 0 < airyBiDeriv x :=
  lt_of_lt_of_le airyBiDeriv_zero_pos (airyBiDeriv_ge_zero hx)

/-- `Bi` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_airyBi_Ici : StrictMonoOn airyBi (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
  · exact fun y _ => (hasDerivAt_airyBi y).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    rw [(hasDerivAt_airyBi y).deriv]
    exact airyBiDeriv_pos (le_of_lt hy)

/-- info: 'FormalResearch.Special.strictMonoOn_airyBi_div_airyAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.strictMonoOn_airyBi_div_airyAi

/-- info: 'FormalResearch.Special.airyBi_ge_sqrt3_mul_airyAi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_ge_sqrt3_mul_airyAi

/-- info: 'FormalResearch.Special.strictMonoOn_airyBi_Ici' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.strictMonoOn_airyBi_Ici

end FormalResearch.Special
