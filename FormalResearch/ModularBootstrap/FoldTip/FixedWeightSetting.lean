module

public import FormalResearch.ModularBootstrap.FoldTip.Hypotheses
public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure

/-!
# The fixed-weight modular bootstrap as a fold-tip setting (`FT-1`)

Defines `fwScale`, `fwChart`, `fwD`, `fwCMin`, and `FoldTipSetting.ofFixedWeight prob`, realising
the setting of `FoldTip/Hypotheses.lean` for a fixed-weight problem `prob : FixedWeightProblem`.
-/

@[expose] public section

open Filter Topology MeasureTheory Metric Set Asymptotics
open scoped Real

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.FixedWeightTip
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.WeightAxioms

/-! ### The scale and the chart -/

/-- The fold constants of the Virasoro-type tip: `ξ_* = ξ̄`, `β = 1/c_*`. -/
noncomputable def fwScale : FoldTipScale where
  slope := xiBar
  beta := 1 / cStar
  slope_pos := by unfold xiBar; have := xiStar_pos; positivity
  beta_pos := one_div_pos.mpr cStar_pos

/-- `A = |a₁|/β = A_opt`. -/
theorem fwScale_A : fwScale.A = Aopt := by
  unfold FoldTipScale.A fwScale Aopt
  have := cStar_pos
  simp only [div_div_eq_mul_div, div_one]
  ring

/-- `K_ξ = (4/3)β^{3/2}` for the fixed-weight tip, equal to `(3/(2 b_*))^{3/2} K_tip`. -/
theorem fwScale_K : fwScale.K = (3 / (2 * xiStar)) ^ (3 / 2 : ℝ) * KTip := by
  unfold FoldTipScale.K
  show 4 / 3 * (1 / cStar) ^ (3 / 2 : ℝ) = _
  have hbt := betaTip_pos
  have hxi := xiStar_pos
  have hc : (1 / cStar : ℝ) = 3 / (2 * xiStar) * betaTip := by
    unfold cStar; field_simp
  rw [hc, Real.mul_rpow (by positivity) hbt.le, ← four_thirds_betaTip_rpow]
  ring

/-- The Langer chart of the fixed-weight tip as a fold-tip chart. -/
noncomputable def fwChart : FTChart fwScale where
  r0 := virasoroRXiInf
  uInf := virasoroUInf
  r0_pos := virasoroRXiInf_pos
  analytic := virasoroUInf_an
  injOn := langerCore.huInf_inj
  real_on_real := fun x hx => by
    refine virasoroUInf_ofReal_im' ?_
    rwa [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hx
  tip := by
    refine Asymptotics.IsBigO.of_bound chartParams.M_u ?_
    have hmem : closedBall (xiBar : ℂ) chartParams.r_xi0 ∈ 𝓝 (xiBar : ℂ) :=
      closedBall_mem_nhds _ chartParams.hr_xi0_pos
    filter_upwards [hmem] with ξ hξ
    have h := chartParams.hu_err ξ hξ
    have heq : virasoroUInf ξ - ((fwScale.beta : ℝ) : ℂ) * ((fwScale.slope : ℂ) - ξ) =
        virasoroUInf ξ - (1 / (cStar : ℂ)) * ((xiBar : ℂ) - ξ) := by
      simp [fwScale]
    rw [heq, norm_pow]
    exact h

/-! ### The setting -/

/-- The uniform Proposition P data used throughout (chosen from `proposition_P_of_problem`). -/
noncomputable def fwD (prob : FixedWeightProblem) : UniformPropositionPData prob :=
  (proposition_P_of_problem prob).choose

theorem fw_cMin_exists (prob : FixedWeightProblem) :
    ∃ cM : ℝ, 1 ≤ cM ∧ (fwD prob).c₀ ≤ cM ∧
      (∀ c, cM ≤ c → ∀ x : ℝ, 0 < x → 0 < prob.cardyV (c / 12) x) ∧
      (∀ c, cM ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ), prob.IsWeaklyFeasible (c / 12) T g →
        0 < prob.cardyNorm (c / 12) g) := by
  obtain ⟨c_gap, C_gap, κ_gap, hcg, -, -, hgap⟩ := deltaLobe_gap_general (fwD prob)
  have h1 := (fwD prob).hc₀_ge1
  refine ⟨max c_gap (fwD prob).c₀, h1.trans (le_max_right _ _), le_max_right _ _,
    fun c hc x hx => (fwD prob).p1_pos ((le_max_right _ _).trans hc) hx,
    fun c hc T g hg => (hgap.2 ((le_max_left _ _).trans hc) hg).1⟩

/-- The threshold from which the weight is positive and feasible competitors have positive norm. -/
noncomputable def fwCMin (prob : FixedWeightProblem) : ℝ := (fw_cMin_exists prob).choose

theorem fwCMin_spec (prob : FixedWeightProblem) :
    1 ≤ fwCMin prob ∧ (fwD prob).c₀ ≤ fwCMin prob ∧
      (∀ c, fwCMin prob ≤ c → ∀ x : ℝ, 0 < x → 0 < prob.cardyV (c / 12) x) ∧
      (∀ c, fwCMin prob ≤ c → ∀ (T : ℝ) (g : ℝ → ℝ), prob.IsWeaklyFeasible (c / 12) T g →
        0 < prob.cardyNorm (c / 12) g) :=
  (fw_cMin_exists prob).choose_spec

/-- **The fixed-weight modular bootstrap as a fold-tip setting**: competitors are real functions, the weight is
the Cardy weight `V = cardyV (c/12)` (with its entire continuation `cardyVC`), feasible at `T` means weakly
feasible at `a = c/12` with gap `T` (`IsWeaklyFeasible`). -/
noncomputable def FoldTipSetting.ofFixedWeight (prob : FixedWeightProblem) : FoldTipSetting where
  scale := fwScale
  Comp := ℝ → ℝ
  ev := fun g => g
  rho := fun c x => prob.cardyV (c / 12) x
  rhoC := fun c z => cardyVC prob (c / 12) z
  feasible := fun c T g => prob.IsWeaklyFeasible (c / 12) T g
  cMin := fwCMin prob
  rho_pos := fun c hc x hx => (fwCMin_spec prob).2.2.1 c hc x hx
  rhoC_ofReal := fun c _ x _ => cardyVC_ofReal prob (c / 12) x
  feasible_mono := fun _ _ _ _ hT hf =>
    ⟨hf.1, hf.2.1, hf.2.2.1, fun t ht => hf.2.2.2 t (hT.trans ht)⟩
  feasible_nonneg := fun _ _ _ hf x hx => hf.2.2.2 x hx
  normPos := fun c hc T g hf => (fwCMin_spec prob).2.2.2 c hc T g hf

end FormalResearch.ModularBootstrap.FoldTip
