module

public import FormalResearch.ModularBootstrap.ConcreteBootstrap.BootstrapHB
public import FormalResearch.ModularBootstrap.Integration.StripTheoremA

/-!
# Theorem `W1'(1)` and Theorem `J` Assembly for Spinless Virasoro

Assembles the sharp $O(1)$ Virasoro lower bound Theorem `J` (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`vlo:J`, via Theorem `W1'(1)` `wone:genlower` and Theorem `FT-L.FW` `wone:ftlfw` at `(P, Q) = (1, 0)`)
from the concrete Virasoro data and the single unproved band-feedback hypothesis `YVInput` (`vlo:YV`).

## Main results
* `theoremJ_of_YV`: Theorem `J` / `W1'(1)` for weakly feasible nonzero Virasoro tests (`c' = c - 1`).
* `theoremJ_T_weak`, `theoremJ_T_V`: sharp $O(1)$ lower bounds for `virasoroProblem.T_weak c'` and `T_V c'`.
* `theoremJ_Delta_best`: sharp $O(1)$ lower bound `Δ_best c' ≥ c' / Λ_V + A_opt c'^{1/3} - C`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.ConcreteBootstrap

open FormalResearch.ModularBootstrap.Crossing

/-- **Theorem `J` / Theorem `W1'(1)` for weakly feasible nonzero tests** at scale `0 < b ≤ virasoroBV`
(`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, `vlo:J` & `wone:genlower(1)`),
conditional on `YVInputFor b`. -/
theorem theoremJ_of_YVFor {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV) (hYV : YVInputFor b) :
    ∃ c_2 C : ℝ, virasoroCQEnv + 1 ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c T : ℝ}, c_2 ≤ c → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible ((c - 1) / 12) T g →
        xiBar * (c - 1) + Aopt * (c - 1) ^ (1 / 3 : ℝ) - C ≤ T := by
  obtain ⟨c_2, C, hc2, hC, hft⟩ := theoremFTLFW_oneZero_of_YVFor hb_pos hb_le hYV
  refine ⟨c_2 + 1, C, by linarith, hC, fun {c T} hc {g} hg => ?_⟩
  exact hft (by linarith : c_2 ≤ c - 1) hg

/-- **Theorem `J` / Theorem `W1'(1)` for weakly feasible nonzero tests**
(`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, `vlo:J` & `wone:genlower(1)`),
conditional on the unproved band bound `YVInput` (`vlo:YV`):
for every sufficiently large `c` (`c' := c - 1`), every weakly feasible nonzero test `g` at
`(c' / 12, T)` satisfies `T ≥ ξ̄ c' + A_opt c'^{1/3} - C`. -/
theorem theoremJ_of_YV (hYV : YVInput) :
    ∃ c_2 C : ℝ, virasoroCQEnv + 1 ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c T : ℝ}, c_2 ≤ c → ∀ {g : ℝ → ℝ},
        virasoroProblem.IsWeaklyFeasible ((c - 1) / 12) T g →
        xiBar * (c - 1) + Aopt * (c - 1) ^ (1 / 3 : ℝ) - C ≤ T :=
  theoremJ_of_YVFor virasoroBV_pos le_rfl hYV

/-- **Theorem `J` for `T_weak`** (`vlo:J`) at scale `0 < b ≤ virasoroBV`, conditional on `YVInputFor b`. -/
theorem theoremJ_T_weakFor {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV) (hYV : YVInputFor b) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.T_weak c' := by
  obtain ⟨c_2, C, hc2, hC, hft⟩ := theoremFTLFW_oneZero_of_YVFor hb_pos hb_le hYV
  refine ⟨c_2, C, hc2, hC, fun {c'} hc' => ?_⟩
  have hc24 : 24 ≤ c' :=
    ((by norm_num : (24 : ℝ) ≤ 10000).trans virasoroCQEnv_ge).trans (hc2.trans hc')
  have hsh : 12 * virasoroProblem.totalShift ≤ c' := by
    rw [virasoroProblem_totalShift]; linarith
  have hne : {T : ℝ | 0 < T ∧ ∃ g, virasoroProblem.IsWeaklyFeasible (c' / 12) T g}.Nonempty := by
    obtain ⟨T, hT_pos, g, hg⟩ := virasoroProblem.feasible_nonempty hsh
    exact ⟨T, hT_pos, g, hg.isWeaklyFeasible⟩
  refine le_csInf hne ?_
  rintro T ⟨_, g, hg⟩
  exact hft hc' hg

/-- **Theorem `J` for `T_weak`** (`vlo:J`) conditional on `YVInput`:
`T_weak(c') ≥ ξ̄ c' + A_opt c'^{1/3} - C` for all `c' ≥ c_2`. -/
theorem theoremJ_T_weak (hYV : YVInput) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.T_weak c' :=
  theoremJ_T_weakFor virasoroBV_pos le_rfl hYV

/-- **Theorem `J` for `T_V`** (`vlo:J`) at scale `0 < b ≤ virasoroBV`, conditional on `YVInputFor b`. -/
theorem theoremJ_T_VFor {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV) (hYV : YVInputFor b) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.T_V c' := by
  obtain ⟨c_2, C, hc2, hC, hweak⟩ := theoremJ_T_weakFor hb_pos hb_le hYV
  refine ⟨c_2, C, hc2, hC, fun {c'} hc' => ?_⟩
  have hc24 : 24 ≤ c' :=
    ((by norm_num : (24 : ℝ) ≤ 10000).trans virasoroCQEnv_ge).trans (hc2.trans hc')
  have hsh : 12 * virasoroProblem.totalShift ≤ c' := by
    rw [virasoroProblem_totalShift]; linarith
  exact (hweak hc').trans (virasoroProblem.T_weak_le_T_V hsh)

/-- **Theorem `J` for `T_V`** (`vlo:J`) conditional on `YVInput`:
`T_V(c') ≥ ξ̄ c' + A_opt c'^{1/3} - C` for all `c' ≥ c_2`. -/
theorem theoremJ_T_V (hYV : YVInput) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        xiBar * c' + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.T_V c' :=
  theoremJ_T_VFor virasoroBV_pos le_rfl hYV

/-- **Theorem `J` for `Δ_best`** (`vlo:J`) at scale `0 < b ≤ virasoroBV`, conditional on `YVInputFor b`. -/
theorem theoremJ_Delta_bestFor {b : ℝ} (hb_pos : 0 < b) (hb_le : b ≤ virasoroBV)
    (hYV : YVInputFor b) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        c' / lambdaV + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.Delta_best c' := by
  obtain ⟨c_2, C, hc2, hC, hTV⟩ := theoremJ_T_VFor hb_pos hb_le hYV
  refine ⟨c_2, C, hc2, hC, fun {c'} hc' => ?_⟩
  have h := hTV hc'
  unfold FixedWeightProblem.Delta_best
  rw [show c' / lambdaV = xiBar * c' + c' / 12 by rw [xiBar_eq_inv_lambdaV_sub]; ring]
  linarith

/-- **Theorem `J` for the optimal primary gap `Δ_best`** (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`,
`vlo:J`; `Δ_best(c') = c'/12 + T_V(c')`) conditional on `YVInput`:
`Δ_best(c') ≥ c' / Λ_V + A_opt c'^{1/3} - C` for all `c' ≥ c_2`. -/
theorem theoremJ_Delta_best (hYV : YVInput) :
    ∃ c_2 C : ℝ, virasoroCQEnv ≤ c_2 ∧ 0 ≤ C ∧
      ∀ {c' : ℝ}, c_2 ≤ c' →
        c' / lambdaV + Aopt * c' ^ (1 / 3 : ℝ) - C ≤ virasoroProblem.Delta_best c' :=
  theoremJ_Delta_bestFor virasoroBV_pos le_rfl hYV

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.theoremJ_of_YV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_of_YV

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.theoremJ_T_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_T_weak

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.theoremJ_T_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_T_V

/-- info: 'FormalResearch.ModularBootstrap.ConcreteBootstrap.theoremJ_Delta_best' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms theoremJ_Delta_best

end FormalResearch.ModularBootstrap.ConcreteBootstrap
