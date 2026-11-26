module

public import FormalResearch.ModularBootstrap.Upper.Positivity.VacuumPrelim

/-!
# The normalisation `F_{2,c}` of the two-zero window (`upper_transfer.tex`, `ut:T2`, "Window and vacuum normalisation")

`F_{2,c} := FV_c (2√2/(πλ))^{5/2} = FK_c^{(2)} · πλ/(2√2)` (`eq:ut:T2-norm`) with `FK_c^{(2)}` the `f = 2` measure
normalisation of Lemma `W`.

* `twoZeroF`, `twoZeroF_eq_const_mul`, `twoZeroF_asymp`: `F_{2,c} = Φ₀ c'^{3/2}` exactly, `Φ₀ > 0`, so `F_{2,c} ≍ c'^{3/2}`;

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Comb
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Positivity

/-- `F_{2,c} = FK_c^{(2)} · πλ/(2√2)` (`eq:ut:T2-norm`). -/
noncomputable def twoZeroF (prob : Crossing.FixedWeightProblem) (c : ℝ) : ℝ :=
  FKc (qProb prob) 2 c * (π * lambdaComb c / (2 * √2))

/-- The constant `Φ₀` with `F_{2,c} = Φ₀ c'^{3/2}`. -/
noncomputable def twoZeroFConst (prob : Crossing.FixedWeightProblem) : ℝ :=
  qProb prob * (√xiStar * (1 - exp (-(4 * π * xiStar))) ^ 2 * (1 / cosh (π * xiStar / 2) ^ 2) /
    (√3 * π)) * (2 * √2 / π) ^ (5 / 2 : ℝ) * kTip

lemma twoZeroFConst_pos (prob : Crossing.FixedWeightProblem) : 0 < twoZeroFConst prob := by
  have := qProb_pos prob
  have := xiStar_pos
  have := one_sub_exp_xiStar_pos
  have := kTip_pos
  unfold twoZeroFConst
  positivity

/-- `λ^{3/2} = 1 / (k_tip c')`. -/
lemma lambdaComb_rpow_three_halves {c : ℝ} (hc : 0 < c) : lambdaComb c ^ (3 / 2 : ℝ) = (kTip * c)⁻¹ := by
  have hk : 0 < kTip * c := mul_pos kTip_pos hc
  unfold lambdaComb
  rw [← Real.rpow_mul hk.le, show (-(2 / 3 : ℝ)) * (3 / 2) = -1 by norm_num, Real.rpow_neg_one]

/-- **`F_{2,c} = Φ₀ c'^{3/2}`** for every `c' > 0`. -/
theorem twoZeroF_eq_const_mul (prob : Crossing.FixedWeightProblem) {c : ℝ} (hc : 0 < c) :
    twoZeroF prob c = twoZeroFConst prob * c ^ (3 / 2 : ℝ) := by
  have hl := lambdaComb_pos' hc
  have hπ := Real.pi_pos
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have h32 := lambdaComb_rpow_three_halves hc
  have hexp : (2 * (((2 : ℕ) : ℝ) - 1 / 4)) = 7 / 2 := by norm_num
  have hdiv : (2 * √2 / (π * lambdaComb c)) ^ (7 / 2 : ℝ) =
      (2 * √2 / π) ^ (7 / 2 : ℝ) / lambdaComb c ^ (7 / 2 : ℝ) := by
    rw [show 2 * √2 / (π * lambdaComb c) = (2 * √2 / π) / lambdaComb c by field_simp]
    exact Real.div_rpow (by positivity) hl.le _
  have h72 : lambdaComb c ^ (7 / 2 : ℝ) = lambdaComb c ^ (2 : ℕ) * lambdaComb c ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hl]; norm_num
  have hs : (2 * √2 / π) ^ (7 / 2 : ℝ) = (2 * √2 / π) ^ (5 / 2 : ℝ) * (2 * √2 / π) := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, Real.rpow_add (by positivity), Real.rpow_one]
  have hc32 : c ^ (3 / 2 : ℝ) = c * √c := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hc, Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold twoZeroF twoZeroFConst FKc FVc
  rw [hexp, hdiv, h72, hs, hc32, h32]
  have hkc : kTip * c ≠ 0 := (mul_pos kTip_pos hc).ne'
  have hk := kTip_pos
  field_simp

/-- **`F_{2,c} ≍ c'^{3/2}`** (`eq:ut:T2-norm`): the `F_asymp` field of `TwoZeroTransferData`. -/
theorem twoZeroF_asymp (prob : Crossing.FixedWeightProblem) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ c : ℝ, 0 < c →
      A * c ^ ((3 : ℝ) / 2) ≤ twoZeroF prob c ∧ twoZeroF prob c ≤ B * c ^ ((3 : ℝ) / 2) :=
  ⟨twoZeroFConst prob, twoZeroFConst prob, twoZeroFConst_pos prob, twoZeroFConst_pos prob,
    fun c hc => by rw [twoZeroF_eq_const_mul prob hc]; exact ⟨le_rfl, le_rfl⟩⟩

lemma twoZeroF_pos (prob : Crossing.FixedWeightProblem) {c : ℝ} (hc : 0 < c) : 0 < twoZeroF prob c := by
  rw [twoZeroF_eq_const_mul prob hc]
  have := twoZeroFConst_pos prob
  positivity

/-- `F_{2,c} = FK^{(2)}_c · πλ/(2√2)` with the measure normalisation `windowMeasureNormK` of Lemma `W`. -/
lemma twoZeroF_eq_windowMeasureNormK (prob : Crossing.FixedWeightProblem) (_hw : prob.w = 1) {c : ℝ}
    (hc : 0 < c) :
    twoZeroF prob c = windowMeasureNormK prob 2 c * (π * lambdaComb c / (2 * √2)) := by
  rw [windowMeasureNormK_eq_FKc prob 2 hc]; rfl

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.twoZeroF_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms twoZeroF_asymp

end FormalResearch.ModularBootstrap.TwoLevel
