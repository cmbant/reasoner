module

public import FormalResearch.Analysis.VanDerCorput
public import FormalResearch.CohnElkies.DualPhaseAndO3

/-!
# Van der Corput on the stationary zone of the cubic phase (GT.2a G2)

For the cubic phase `φ(x) = a0 x - (π²/36) x³` on an interval `[α, β]` with `0 < α ≤ β` (and, by reflection,
`-β ≤ -α < 0`), the second-derivative test (`FormalResearch.Analysis.van_der_corput_second`) gives

`‖∫_α^β h(x) e^{i φ(x)} dx‖ ≤ 8 (M + V) / √(π² α / 6)`,

where `‖h‖ ≤ M` on `[α, β]` and `V ≥ ∫_α^β ‖h'‖` bounds the variation of `h`.

* `mb_vdc_variation`: for `h` of class `C¹`, `h` has bounded variation on `[a, b]` with
  `(eVariationOn h (Icc a b)).toReal ≤ V` whenever `∫_{[a,b]} ‖h'‖ ≤ V`. Proved from
  `eVariationOn_le_integral_norm_deriv`.
* `mb_vdc_core`: the van der Corput bound for `h e^{i(a0 x - π²x³/36)}` on `[a, b]`, under monotonicity of
  `φ'` and the lower bound `lam ≤ |φ''|` on `[a, b]` (a private helper; the general form of van der Corput).
* `cubic_vdc_pos` and `cubic_vdc_neg`: the two stationary-zone bounds of the brief, `lam = π² α / 6`.

The proof is first-order calculus and the variation bound; no numerical constants are assumed (π enters only
through `Real.pi`, and the bound `lam > 0` uses `Real.pi_pos`). Restatements of Mathlib: none beyond the use of
`ContDiff.continuous_deriv` and `ContDiff.differentiable`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Analysis FormalResearch.CohnElkies

/-- Bounded variation of a `C¹` function on a compact interval, with the variation bounded by `∫ ‖h'‖`. -/
theorem mb_vdc_variation {h : ℝ → ℂ} {a b V : ℝ} (hab : a ≤ b) (hh : ContDiff ℝ 1 h)
    (hV : ∫ x in Icc a b, ‖deriv h x‖ ≤ V) :
    BoundedVariationOn h (Icc a b) ∧ (eVariationOn h (Icc a b)).toReal ≤ V := by
  have hd : ∀ x ∈ Icc a b, HasDerivAt h (deriv h x) x := fun x _ =>
    ((hh.differentiable (by norm_num)) x).hasDerivAt
  have hci : IntervalIntegrable (deriv h) volume a b :=
    ((hh.continuous_deriv (by norm_num)).intervalIntegrable a b)
  have hev := eVariationOn_le_integral_norm_deriv hab hd hci
  have hX : ∫ t in a..b, ‖deriv h t‖ ≤ V := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact hV
  have hX0 : 0 ≤ ∫ t in a..b, ‖deriv h t‖ :=
    intervalIntegral.integral_nonneg hab fun t _ => norm_nonneg _
  have hV0 : 0 ≤ V := hX0.trans hX
  have hne : eVariationOn h (Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hev
  refine ⟨hne, ENNReal.toReal_le_of_le_ofReal hV0 (hev.trans (ENNReal.ofReal_le_ofReal hX))⟩

/-- Core van der Corput bound for `h(x) e^{i(a0 x - π² x³/36)}` on `[a, b]`, with `lam` a lower bound for `|φ''|`. -/
private theorem mb_vdc_core {a0 a b lam M V : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    (hmono : MonotoneOn (fun x : ℝ => a0 - Real.pi ^ 2 / 12 * x ^ 2) (Icc a b) ∨
      AntitoneOn (fun x : ℝ => a0 - Real.pi ^ 2 / 12 * x ^ 2) (Icc a b))
    (hlb : ∀ y ∈ Icc a b, lam ≤ |-(Real.pi ^ 2 / 6) * y|)
    {h : ℝ → ℂ} (hh : ContDiff ℝ 1 h) (hM : ∀ x ∈ Icc a b, ‖h x‖ ≤ M)
    (hV : ∫ x in Icc a b, ‖deriv h x‖ ≤ V) :
    ‖∫ x in a..b, h x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      8 * (M + V) / Real.sqrt lam := by
  obtain ⟨hbv, hvar⟩ := mb_vdc_variation hab hh hV
  have hφ : ∀ y ∈ Icc a b, HasDerivAt (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3)
      (a0 - Real.pi ^ 2 / 12 * y ^ 2) y := by
    intro y _
    have h1 : HasDerivAt (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3)
        (a0 * 1 - Real.pi ^ 2 / 36 * ((3 : ℕ) * y ^ (3 - 1))) y :=
      ((hasDerivAt_id y).const_mul a0).sub ((hasDerivAt_pow 3 y).const_mul (Real.pi ^ 2 / 36))
    convert h1 using 1
    norm_num
    ring
  have hφ' : ∀ y ∈ Icc a b, HasDerivAt (fun x : ℝ => a0 - Real.pi ^ 2 / 12 * x ^ 2)
      (-(Real.pi ^ 2 / 6) * y) y := by
    intro y _
    have h1 : HasDerivAt (fun x : ℝ => a0 - Real.pi ^ 2 / 12 * x ^ 2)
        (-(Real.pi ^ 2 / 12 * ((2 : ℕ) * y ^ (2 - 1)))) y :=
      ((hasDerivAt_pow 2 y).const_mul (Real.pi ^ 2 / 12)).const_sub a0
    convert h1 using 1
    norm_num
    ring
  have hcont : ContinuousOn h (Icc a b) := hh.continuous.continuousOn
  have key := van_der_corput_second (c := 1) hab one_pos hlam hφ hφ' hmono hlb hcont hbv hM
  simp only [Complex.ofReal_one, one_mul, mul_one] at key
  have hle : 8 * (M + (eVariationOn h (Icc a b)).toReal) / Real.sqrt lam ≤ 8 * (M + V) / Real.sqrt lam := by
    gcongr
  exact key.trans hle

/-- Stationary-zone van der Corput bound on `[α, β]`, `0 < α ≤ β`, for the cubic phase `a0 x - (π²/36) x³`:
`‖∫_α^β h e^{iφ}‖ ≤ 8 (M + V)/√(π² α/6)`. Here `φ'' = -(π²/6) x` and `|φ''| ≥ π² α/6` on `[α, β]`, and
`φ'` is antitone there (`x²` is increasing on `[α, β] ⊆ (0, ∞)`). -/
theorem cubic_vdc_pos {a0 α β M V : ℝ} (hα : 0 < α) (hαβ : α ≤ β) {h : ℝ → ℂ}
    (hh : ContDiff ℝ 1 h) (hM : ∀ x ∈ Set.Icc α β, ‖h x‖ ≤ M) (hV : ∫ x in Set.Icc α β, ‖deriv h x‖ ≤ V) :
    ‖∫ x in α..β, h x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      8 * (M + V) / Real.sqrt (Real.pi ^ 2 * α / 6) := by
  have hlam : 0 < Real.pi ^ 2 * α / 6 := by positivity
  have hp : (0 : ℝ) < Real.pi ^ 2 := by positivity
  refine mb_vdc_core hαβ hlam (Or.inr ?_) ?_ hh hM hV
  · intro x hx y hy hxy
    have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith [hx.1, hy.1]
    show a0 - Real.pi ^ 2 / 12 * y ^ 2 ≤ a0 - Real.pi ^ 2 / 12 * x ^ 2
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 12) (sub_nonneg.mpr hsq)]
  · intro y hy
    have hy0 : 0 ≤ y := le_trans hα.le hy.1
    have hneg : -(Real.pi ^ 2 / 6) * y ≤ 0 := by nlinarith
    rw [abs_of_nonpos hneg]
    nlinarith [mul_le_mul_of_nonneg_left hy.1 hp.le]

/-- Stationary-zone van der Corput bound on `[-β, -α]`, `0 < α ≤ β`, for the cubic phase: the reflected case,
with the same bound `8 (M + V)/√(π² α/6)` (`φ'` is monotone on `[-β, -α] ⊆ (-∞, 0)`, `|φ''| ≥ π² α/6`). -/
theorem cubic_vdc_neg {a0 α β M V : ℝ} (hα : 0 < α) (hαβ : α ≤ β) {h : ℝ → ℂ}
    (hh : ContDiff ℝ 1 h) (hM : ∀ x ∈ Set.Icc (-β) (-α), ‖h x‖ ≤ M)
    (hV : ∫ x in Set.Icc (-β) (-α), ‖deriv h x‖ ≤ V) :
    ‖∫ x in (-β)..(-α), h x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      8 * (M + V) / Real.sqrt (Real.pi ^ 2 * α / 6) := by
  have hlam : 0 < Real.pi ^ 2 * α / 6 := by positivity
  have hp : (0 : ℝ) < Real.pi ^ 2 := by positivity
  refine mb_vdc_core (by linarith) hlam (Or.inl ?_) ?_ hh hM hV
  · intro x hx y hy hxy
    have hsq : y ^ 2 ≤ x ^ 2 := by nlinarith [hx.1, hy.2]
    show a0 - Real.pi ^ 2 / 12 * x ^ 2 ≤ a0 - Real.pi ^ 2 / 12 * y ^ 2
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 12) (sub_nonneg.mpr hsq)]
  · intro y hy
    have hy0 : α ≤ -y := by linarith [hy.2]
    have hnn : 0 ≤ -(Real.pi ^ 2 / 6) * y := by nlinarith
    rw [abs_of_nonneg hnn]
    nlinarith [mul_le_mul_of_nonneg_left hy0 hp.le]

/-- info: 'FormalResearch.SignUncertainty.mb_vdc_variation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mb_vdc_variation

/-- info: 'FormalResearch.SignUncertainty.cubic_vdc_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_vdc_pos

/-- info: 'FormalResearch.SignUncertainty.cubic_vdc_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_vdc_neg

end FormalResearch.SignUncertainty
