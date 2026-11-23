module

public import FormalResearch.ModularBootstrap.Contour.VirasoroBridge

/-!
# Unconditional Scale Choice (`virasoroBVChoice`) and Unconditional Theorem J

Discharges the parameter-ordering hypothesis `VirasoroBVScaleCompat` (`2 b_V^2 ≤ virasoroScaleThresh`)
by selecting the dimensionless bootstrap width
`virasoroBVChoice := min virasoroBV (√(virasoroScaleThresh / 4)) > 0`
*after* both the Langer chart caps (`ConcreteBootstrap.virasoroBV`) and the strip/contour caps
(`virasoroScaleThresh`, from Proposition `Y_V`, Lemma `D'`, and Lemma `Z`) have been constructed,
matching the parameter order in `lower_o1_two_edge.tex` (§J2, §J4, §J8).

Because `0 < virasoroBVChoice ≤ virasoroBV` and `2 * virasoroBVChoice ^ 2 ≤ virasoroScaleThresh`,
`yvInputFor_of_scaleCompat` yields `YVInputFor virasoroBVChoice` unconditionally, and feeding it
into `ConcreteBootstrap.theoremJ_*For` makes Theorem `J` (`vlo:J`) completely unconditional.

## Main declarations
* `virasoroBVChoice`: explicit dimensionless chart scale `min virasoroBV √(virasoroScaleThresh / 4)`.
* `yvInputFor_virasoroBVChoice`: unconditional proof of `YVInputFor virasoroBVChoice` (`vlo:YV`,
  `vlo:Z`, `vlo:L`).
* `theoremJ_unconditional`: unconditional Theorem `J` / `W1'(1)` (`vlo:J`, `wone:genlower(1)`)
  for weakly feasible nonzero Virasoro tests.
* `theoremJ_T_weak`, `theoremJ_T_V`, `theoremJ_Delta_best`: unconditional sharp `O(1)` lower
  bounds for `virasoroProblem.T_weak`, `virasoroProblem.T_V`, and `virasoroProblem.Delta_best`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Contour

open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Crossing

/-- Explicit dimensionless Virasoro bootstrap scale chosen inside both the initial Langer chart
ball (`virasoroBV`) and the inner strip/saddle threshold (`virasoroScaleThresh`). -/
noncomputable def virasoroBVChoice : ℝ :=
  min virasoroBV (Real.sqrt (virasoroScaleThresh / 4))

lemma virasoroBVChoice_pos : 0 < virasoroBVChoice :=
  lt_min virasoroBV_pos (Real.sqrt_pos.mpr (div_pos virasoroScaleThresh_pos (by norm_num)))

lemma virasoroBVChoice_le : virasoroBVChoice ≤ virasoroBV :=
  min_le_left _ _

lemma virasoroBVChoice_scaleCompat : 2 * virasoroBVChoice ^ 2 ≤ virasoroScaleThresh := by
  have hpos := virasoroScaleThresh_pos
  have hle : virasoroBVChoice ≤ Real.sqrt (virasoroScaleThresh / 4) := min_le_right _ _
  have hsq : virasoroBVChoice ^ 2 ≤ virasoroScaleThresh / 4 := by
    calc virasoroBVChoice ^ 2
        ≤ (Real.sqrt (virasoroScaleThresh / 4)) ^ 2 :=
          pow_le_pow_left₀ virasoroBVChoice_pos.le hle 2
      _ = virasoroScaleThresh / 4 := Real.sq_sqrt (div_nonneg hpos.le (by norm_num))
  linarith only [hsq, hpos]

/-- **Unconditional Proposition `Y_V` + Lemma `Z` band-feedback input** (`lower_o1_two_edge.tex`,
`vlo:YV`, `vlo:Z`, `vlo:L`) at scale `virasoroBVChoice`. -/
theorem yvInputFor_virasoroBVChoice : YVInputFor virasoroBVChoice :=
  yvInputFor_of_scaleCompat virasoroBVChoice_pos virasoroBVChoice_le virasoroBVChoice_scaleCompat

/-- **Unconditional Theorem `J` / Theorem `W1'(1)` for weakly feasible nonzero Virasoro tests**
(`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, `vlo:J` & `wone:genlower(1)`):
for every sufficiently large `c` (`c' := c - 1`), every weakly feasible nonzero test `g` at
`(c' / 12, T)` satisfies `T ≥ ξ̄ c' + A_opt c'^{1/3} - C`. -/
theorem theoremJ_unconditional :
    ∃ c_2 C : ℝ, virasoroCQEnv + 1 ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c T : ℝ}, c_2 ≤ c → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible ((c - 1) / 12) T g →
        xiBar * (c - 1) + Aopt * (c - 1) ^ (1 / 3 : ℝ) - C ≤ T :=
  ConcreteBootstrap.theoremJ_of_YVFor
    virasoroBVChoice_pos virasoroBVChoice_le yvInputFor_virasoroBVChoice

/-- **Unconditional Theorem `J` for `T_weak`** (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`vlo:J`): `T_weak(c') ≥ ξ̄ c' + A_opt c'^{1/3} - C` for all `c' ≥ c_2`. -/
theorem theoremJ_T_weak :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.T_weak c' :=
  ConcreteBootstrap.theoremJ_T_weakFor
    virasoroBVChoice_pos virasoroBVChoice_le yvInputFor_virasoroBVChoice

/-- **Unconditional Theorem `J` for `T_V`** (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`vlo:J`): `T_V(c') ≥ ξ̄ c' + A_opt c'^{1/3} - C` for all `c' ≥ c_2`. -/
theorem theoremJ_T_V :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.T_V c' :=
  ConcreteBootstrap.theoremJ_T_VFor
    virasoroBVChoice_pos virasoroBVChoice_le yvInputFor_virasoroBVChoice

/-- **Unconditional Theorem `J` for the optimal primary gap `Δ_best`**
(`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, `vlo:J`; `Δ_best(c') = c'/12 + T_V(c')`):
`Δ_best(c') ≥ c' / Λ_V + A_opt c'^{1/3} - C` for all `c' ≥ c_2`. -/
theorem theoremJ_Delta_best :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        c' / lambdaV + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.Delta_best c' :=
  ConcreteBootstrap.theoremJ_Delta_bestFor
    virasoroBVChoice_pos virasoroBVChoice_le yvInputFor_virasoroBVChoice

/-! ### Foundation Verification -/

/-- info: 'FormalResearch.ModularBootstrap.Contour.yvInputFor_virasoroBVChoice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms yvInputFor_virasoroBVChoice

/-- info: 'FormalResearch.ModularBootstrap.Contour.theoremJ_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_unconditional

/-- info: 'FormalResearch.ModularBootstrap.Contour.theoremJ_T_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_T_weak

/-- info: 'FormalResearch.ModularBootstrap.Contour.theoremJ_T_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_T_V

/-- info: 'FormalResearch.ModularBootstrap.Contour.theoremJ_Delta_best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_Delta_best

end FormalResearch.ModularBootstrap.Contour
