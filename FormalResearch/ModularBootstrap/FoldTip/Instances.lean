module

public import FormalResearch.ModularBootstrap.FoldTip.Hypotheses
public import FormalResearch.ModularBootstrap.FixedWeightTip.PropositionP
public import FormalResearch.ModularBootstrap.FixedWeight.OptimalMeasure
public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapWInterface
public import FormalResearch.ModularBootstrap.Upper.Assembly.FarFirstSite
public import FormalResearch.ModularBootstrap.Upper.Ramped.RampedFinal

/-!
# The fixed-weight modular bootstrap as a fold-tip setting (`FT-1`)

`FoldTipSetting.ofFixedWeight prob` realises the setting of `FoldTip/Hypotheses.lean` for a fixed-weight
problem `prob : FixedWeightProblem`, with `c = c̃ = c'`, weight `ρ_c(t) = V(t) = cardyV (c/12) t` and
feasibility `IsWeaklyFeasible (c/12) T g`; and proves the hypotheses of Theorem FT (`ft:FT`) for it from
Proposition P (`ft:PP`, `FixedWeightTip/PropositionP.lean`).

## Constants

`ξ_*^{FT} = ξ̄ = b_*²/3` is `xiBar` (`b_* = xiStar`); the chart of `FTChart` is the Langer chart
`virasoroUInf` (a function of `ξ`, `u_∞(ξ) = (1/c_*)(ξ̄ - ξ) + O((ξ-ξ̄)²)`), so `β_FT = 1/cStar`
`= (3/(2b_*))·betaTip` and `A = |a₁|/β_FT = Aopt` (`fwScale_A`).

## Results

* `fwH1`: `H1` with `η_vac ≡ 0`, unconditional.
* `fwH2hol`, `fwH2`: `H2-hol` and `H2` with `(N₀, q) = (0, 2)`, `ς_c = generalSigma p_e c`
  (`= C₁ c^{-1/3} log c`) and `δ_lobe = C_gap e^{-κ c}`, unconditional, from `proposition_P_of_problem`.
* `fwH2plus`: `H2+`.
* `fwH4a`: `H4a`, from `propP_H4a_eventually_ne_zero` and the holomorphy of `ψ̃`.
* `fwH3`: `H3` from `TheoremC15UpperInput prob`, so unconditional for `prob.w = 1` (`fwH3_w1`).
* `fwH4b`: `H4b` for `prob.w = 1`, from `sigma_of_threshold_prob` and the design, displaced and omitted
  families of `sigma_unconditional_prob`, for every sequence of extremal crossing measures.  The window
  coordinate of `FTCrossingData` is the tip variable `uAiry` of `Upper.Rigidity.Dictionary`, not the Langer chart
  `u_c` of `FTChart`; the structure does not relate the two (their difference is `o(1)` locally uniformly, not
  formalised).
* `fw_foldTip_hypotheses_w1`: all of the above for a weight-one problem; the non-vacuity of
  `FoldTip/Hypotheses.lean`.  `H3` and `H4b` are open for `w > 1` (designs and the `O(1)` upper bound).
-/

@[expose] public section

open Filter Topology MeasureTheory Metric Set Asymptotics
open scoped Real

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.FixedWeightTip
  FormalResearch.ModularBootstrap.ConcreteBootstrap FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.Duality FormalResearch.ModularBootstrap.FixedWeightBand
  FormalResearch.ModularBootstrap.Upper.Rigidity FormalResearch.ModularBootstrap.Upper.Assembly

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

/-! ### `H3` -/

/-- **`H3` for the fixed-weight setting from the `O(1)` upper bound** `TheoremC15UpperInput prob`
(`T_V ≤ T_* + D_+`): some strictly feasible `g` exists at `T_* + D_+ + 1`, so `R⁺ = D_+ + 1`.
Unconditional for `prob.w = 1` by `Upper.Ramped.theoremC15UpperInput_prob`. -/
theorem fwH3 (prob : FixedWeightProblem) (hHi : TheoremC15UpperInput prob) :
    FTH3 (FoldTipSetting.ofFixedWeight prob) := by
  obtain ⟨c₂, D, hc₂, hD, hup⟩ := hHi
  refine ⟨⟨fun _ => D + 1, ?_, ?_⟩⟩
  · refine Asymptotics.isLittleO_const_left.2 (Or.inr ?_)
    exact tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop (by norm_num))
  · filter_upwards [eventually_ge_atTop c₂] with c hc
    have hc12 : 12 * prob.totalShift ≤ c := (le_max_right _ _).trans (hc₂.trans hc)
    have hne := prob.feasible_nonempty hc12
    have hlt : prob.T_V c < TStar c + D + 1 := by
      have := hup hc; linarith
    obtain ⟨T', ⟨-, g, hg⟩, hT'⟩ := exists_lt_of_csInf_lt hne hlt
    refine ⟨g, ?_⟩
    have hmono := (FoldTipSetting.ofFixedWeight prob).feasible_mono c T' _ g
      (show T' ≤ fwScale.slope * c + fwScale.A * c ^ (1 / 3 : ℝ) + (D + 1) by
        rw [fwScale_A]; unfold TStar at hT'; unfold fwScale; simp only; linarith)
      hg.isWeaklyFeasible
    exact hmono

/-! ### The chart: `ξ_c`, `Ψ̃` and the identification with `psiTilde` -/

lemma fwChart_uc_injOn {c : ℝ} (hc : 0 < c) :
    InjOn (fwChart.uc c) (ball (fwScale.slope : ℂ) fwChart.r0) := by
  intro x hx y hy hxy
  have hpos : ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hc _).ne'
  exact fwChart.injOn hx hy (mul_left_cancel₀ hpos hxy)

/-- `ξ_c = ξ_∞(· c^{-2/3})` on the whole domain `ball 0 (r_u c^{2/3})` of the Langer chart. -/
lemma fwChart_xic_eq {c : ℝ} (hc : 0 < c) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ))) :
    fwChart.xic c u = virasoroXiChartC c u := by
  have hw : u * ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
    rw [mem_ball_zero_iff] at hu ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc.le _)]
    calc ‖u‖ * c ^ (-(2 / 3 : ℝ)) < virasoroRUInf * c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) :=
          mul_lt_mul_of_pos_right hu (Real.rpow_pos_of_pos hc _)
      _ = virasoroRUInf := by
          rw [mul_assoc, ← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero, mul_one]
  have hξ : virasoroXiChartC c u ∈ ball (fwScale.slope : ℂ) fwChart.r0 := virasoroXiInf_mem hw
  have huc : fwChart.uc c (virasoroXiChartC c u) = u := by
    unfold FTChart.uc virasoroXiChartC
    change ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) * virasoroUInf (virasoroXiInf _) = u
    rw [virasoroUInf_xiInf hw, mul_comm u, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  have h := (fwChart_uc_injOn hc).leftInvOn_invFunOn hξ
  change Function.invFunOn (fwChart.uc c) _ (fwChart.uc c (virasoroXiChartC c u)) = _ at h
  rw [huc] at h
  exact h

lemma fwChart_deriv_xic_eq {c : ℝ} (hc : 0 < c) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ))) :
    deriv (fwChart.xic c) u = deriv (virasoroXiChartC c) u := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_ball.mem_nhds hu] with v hv
  exact fwChart_xic_eq hc hv

/-- Real-axis form of the chart: `c Re ξ_c(u) = Δ(u)` and `ξ_c(u)` is real. -/
lemma fwChart_xic_ofReal {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : |u| ≤ virasoroAC c ^ 2) :
    fwChart.xic c (u : ℂ) = ((virasoroDeltaChart c u / c : ℝ) : ℂ) := by
  have hball : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ)) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hu.trans_lt (virasoroAC_sq_lt_domain hc)
  rw [fwChart_xic_eq hc hball]
  have h := virasoroDeltaChartC_ofReal hc hu
  unfold virasoroDeltaChartC at h
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  rw [Complex.ofReal_div, ← h]
  field_simp

private lemma fwDeltaChartC_real_deriv_eq {c' u : ℝ} (hc' : 0 < c')
    (hu : |u| ≤ virasoroAC c' ^ 2) :
    deriv (virasoroDeltaChartC c') (u : ℂ) = ((deriv (virasoroDeltaChart c') u : ℝ) : ℂ) := by
  let R : ℝ := virasoroRUInf * c' ^ (2 / 3 : ℝ)
  have hu_ball : (u : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hu.trans_lt (virasoroAC_sq_lt_domain hc')
  have h_diff_C : DifferentiableAt ℂ (virasoroDeltaChartC c') (u : ℂ) :=
    (virasoroDeltaChartC_analyticOnNhd hc' (u : ℂ) hu_ball).differentiableAt
  have h_eq_R : ∀ᶠ x : ℝ in 𝓝 u, virasoroDeltaChartC c' (x : ℂ) = (virasoroDeltaChart c' x : ℂ) := by
    have hlt : |u| < R := hu.trans_lt (virasoroAC_sq_lt_domain hc')
    filter_upwards [Ioo_mem_nhds (show u - (R - |u|) < u by linarith)
      (show u < u + (R - |u|) by linarith)] with x hx
    have hx_abs : |x| < R := abs_lt.mpr
      ⟨by have := (abs_lt.mp hlt).1; linarith [hx.1, le_abs_self u, neg_le_abs u],
       by have := (abs_lt.mp hlt).2; linarith [hx.2, le_abs_self u, neg_le_abs u]⟩
    have hx_ru : |x * c' ^ (-(2 / 3 : ℝ))| < virasoroRUInf := by
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hc' _)]
      have hmul : R * c' ^ (-(2 / 3 : ℝ)) = virasoroRUInf := by
        dsimp [R]; rw [mul_assoc, ← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero, mul_one]
      calc |x| * c' ^ (-(2 / 3 : ℝ)) < R * c' ^ (-(2 / 3 : ℝ)) :=
            mul_lt_mul_of_pos_right hx_abs (Real.rpow_pos_of_pos hc' _)
        _ = virasoroRUInf := hmul
    unfold virasoroDeltaChart virasoroDeltaChartC virasoroXiChartC
    have hw : ((x : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) =
        (((x * c' ^ (-(2 / 3 : ℝ)) : ℝ)) : ℂ) := by push_cast; rfl
    rw [hw]
    have him := virasoroXiInf_ofReal_im hx_ru
    refine Complex.ext ?_ ?_
    · rw [Complex.re_ofReal_mul, Complex.ofReal_re]
    · rw [Complex.im_ofReal_mul, him, mul_zero, Complex.ofReal_im]
  have hd_C_R : HasDerivAt (fun x : ℝ => virasoroDeltaChartC c' (x : ℂ))
      (deriv (virasoroDeltaChartC c') (u : ℂ)) u := h_diff_C.hasDerivAt.comp_ofReal
  have hd_R : HasDerivAt (fun x : ℝ => (virasoroDeltaChart c' x : ℂ))
      ((deriv (virasoroDeltaChart c') u : ℝ) : ℂ) u := by
    have hd_real := virasoroDeltaChart_hasDerivAt hc' hu
    exact hd_real.deriv ▸ hd_real.ofReal_comp
  exact (hd_C_R.congr_of_eventuallyEq (EventuallyEq.symm h_eq_R)).unique hd_R

/-- `c |ξ_c'(u)| = -Δ'(u)` on the real chart interval. -/
lemma fwChart_norm_deriv_xic {c : ℝ} (hc : 0 < c) {u : ℝ} (hu : |u| ≤ virasoroAC c ^ 2) :
    c * ‖deriv (fwChart.xic c) (u : ℂ)‖ = -(deriv (virasoroDeltaChart c) u) := by
  have hball : (u : ℂ) ∈ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ)) := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact hu.trans_lt (virasoroAC_sq_lt_domain hc)
  rw [fwChart_deriv_xic_eq hc hball]
  have h1 : deriv (virasoroDeltaChartC c) (u : ℂ) = (c : ℂ) * deriv (virasoroXiChartC c) (u : ℂ) := by
    unfold virasoroDeltaChartC
    exact deriv_const_mul _ ((virasoroXiChartC_analyticOnNhd hc _ hball).differentiableAt)
  have h2 := fwDeltaChartC_real_deriv_eq hc hu
  have hder_le := virasoroDeltaChart_deriv_le hc (abs_le.mp hu)
  have hc13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have hneg : deriv (virasoroDeltaChart c) u < 0 := by
    have := mul_pos (half_pos cStar_pos) hc13; linarith
  have h3 : ‖(c : ℂ) * deriv (virasoroXiChartC c) (u : ℂ)‖ = -(deriv (virasoroDeltaChart c) u) := by
    rw [← h1, h2, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hneg]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] at h3
  exact h3

/-- On the real chart interval `Ψ̃_g` of the setting is the real part of `psiTilde`. -/
lemma fwChart_PsiT_eq (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ}
    (hg : TestClass prob (c / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c ^ 2) :
    fwChart.PsiT (FoldTipSetting.ofFixedWeight prob) c g u = (psiTilde prob c g (u : ℂ)).re := by
  rw [psiTilde_re_ofReal prob hc hg hu]
  unfold FTChart.PsiT FoldTipSetting.Psi FoldTipSetting.M
  rw [fwChart_xic_ofReal hc hu, Complex.ofReal_re, fwChart_norm_deriv_xic hc hu]
  have hΔ : c * (virasoroDeltaChart c u / c) = virasoroDeltaChart c u := by field_simp
  rw [hΔ]
  change g (virasoroDeltaChart c u) * prob.cardyV (c / 12) (virasoroDeltaChart c u) /
      prob.cardyNorm (c / 12) g * -deriv (virasoroDeltaChart c) u = _
  unfold FixedWeightProblem.cardyNorm
  ring

/-! ### The far lobe -/

lemma fwChart_uc_re (c ξ : ℝ) : (fwChart.uc c (ξ : ℂ)).re = virasoroUChart c ξ := by
  unfold FTChart.uc virasoroUChart
  change (((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) * virasoroUInf (ξ : ℂ)).re = _
  rw [Complex.re_ofReal_mul]

lemma virasoroChartR0_lt_rXi : virasoroChartR0 < virasoroRXiInf := by
  have := chartParams.hr_xi0_le
  have := virasoroRXiInf_pos
  unfold virasoroChartR0
  linarith

/-- `virasoroUChart c` is strictly decreasing from the Langer interval to the whole analyticity interval:
injectivity and continuity make it monotone on any interval containing `[ξ̄ - r₀', ξ̄ + r₀']`. -/
lemma virasoroUChart_lt_of_gt {c : ℝ} (hc : 0 < c) {ξA ξ : ℝ}
    (hA : ξA ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0))
    (hξ : |ξ - xiBar| < virasoroRXiInf) (hlt : ξA < ξ) :
    virasoroUChart c ξ < virasoroUChart c ξA := by
  have hR0 := virasoroChartR0_pos
  have hR0r := virasoroChartR0_lt_rXi
  set lo : ℝ := min ξ (xiBar - virasoroChartR0) with hlo
  set hi : ℝ := max ξ (xiBar + virasoroChartR0) with hhi
  have hξ' := abs_lt.1 hξ
  have hlohi : lo ≤ hi := by
    refine (min_le_right _ _).trans ?_
    linarith [le_max_right ξ (xiBar + virasoroChartR0)]
  have hI : ∀ y ∈ Icc lo hi, |y - xiBar| < virasoroRXiInf := by
    intro y hy
    rw [abs_lt]
    constructor
    · have : xiBar - virasoroRXiInf < lo := lt_min (by linarith) (by linarith)
      linarith [hy.1]
    · have : hi < xiBar + virasoroRXiInf := max_lt (by linarith) (by linarith)
      linarith [hy.2]
  have hball : ∀ y ∈ Icc lo hi, (y : ℂ) ∈ ball (xiBar : ℂ) virasoroRXiInf := fun y hy => by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hI y hy
  have hcont : ContinuousOn (virasoroUChart c) (Icc lo hi) := by
    intro y hy
    have hd : HasDerivAt (fun t : ℝ => virasoroUInf (t : ℂ))
        (deriv virasoroUInf (y : ℂ)) y := by
      simpa using ((virasoroUInf_an (y : ℂ) (hball y hy)).differentiableAt.hasDerivAt).comp_ofReal
    have h2 : HasDerivAt (fun t : ℝ => (virasoroUInf (t : ℂ)).re) (deriv virasoroUInf (y : ℂ)).re y :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hd
    exact ((h2.const_mul (c ^ (2 / 3 : ℝ))).continuousAt).continuousWithinAt
  have hinj : InjOn (virasoroUChart c) (Icc lo hi) := by
    intro y1 hy1 y2 hy2 h12
    have him1 := virasoroUInf_ofReal_im' (hI y1 hy1)
    have him2 := virasoroUInf_ofReal_im' (hI y2 hy2)
    have hpos : c ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc _).ne'
    have hre : (virasoroUInf (y1 : ℂ)).re = (virasoroUInf (y2 : ℂ)).re := by
      unfold virasoroUChart at h12
      exact mul_left_cancel₀ hpos h12
    have heq : virasoroUInf (y1 : ℂ) = virasoroUInf (y2 : ℂ) := Complex.ext hre (by rw [him1, him2])
    exact_mod_cast langerCore.huInf_inj (hball y1 hy1) (hball y2 hy2) heq
  have hsmall : Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) ⊆ Icc lo hi := by
    intro y hy
    exact ⟨(min_le_right _ _).trans hy.1, hy.2.trans (le_max_right _ _)⟩
  have hanti_small := virasoroUChart_strictAnti hc
  rcases hcont.strictMonoOn_of_injOn_Icc' hlohi hinj with hmono | hanti
  · exfalso
    have h1 : xiBar - virasoroChartR0 ∈ Icc lo hi :=
      hsmall ⟨le_rfl, by linarith⟩
    have h2 : xiBar + virasoroChartR0 ∈ Icc lo hi :=
      hsmall ⟨by linarith, le_rfl⟩
    have := hmono h1 h2 (by linarith)
    have := hanti_small ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
    linarith
  · exact hanti (hsmall hA) ⟨min_le_left _ _, le_max_left _ _⟩ hlt

lemma fwLobe_subset {c a0 : ℝ} (hc : 0 < c) (h0 : 0 ≤ discRadius a0 c)
    (hA : discRadius a0 c ≤ virasoroAC c ^ 2) :
    fwChart.lobe a0 c ⊆ Ioc 0 (virasoroDeltaChart c (discRadius a0 c)) := by
  intro x ⟨hx0, hx⟩
  refine ⟨hx0, ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hmem := virasoroDeltaChart_div_mem hc (u := discRadius a0 c)
    (by rw [abs_of_nonneg h0]; exact hA)
  set ξA := virasoroDeltaChart c (discRadius a0 c) / c with hξA
  have hξlt : ξA < x / c := by
    rw [hξA]; exact div_lt_div_of_pos_right hcon hc
  have hR0r := virasoroChartR0_lt_rXi
  rcases hx with hx | ⟨hxr, hxu⟩
  · have : xiBar - virasoroRXiInf < xiBar - virasoroChartR0 := by linarith
    change x / c ≤ xiBar - virasoroRXiInf at hx
    linarith [hmem.1]
  · have hlt := virasoroUChart_lt_of_gt hc hmem (by exact hxr) hξlt
    rw [virasoroUChart_deltaChart hc (by rw [abs_of_nonneg h0]; exact hA)] at hlt
    rw [fwChart_uc_re] at hxu
    linarith

/-- The far-lobe mass of the setting is at most the normalised mass `deltaLobe` of `psiTilde`'s lobe. -/
lemma fw_farLobeMass_le_deltaLobe (prob : FixedWeightProblem) {c : ℝ} (hc : 0 < c) {g : ℝ → ℝ}
    (hg : TestClass prob (c / 12) g) (hM : 0 < prob.cardyNorm (c / 12) g)
    (hV : ∀ t : ℝ, 0 < t → 0 ≤ prob.cardyV (c / 12) t) {r1 : ℝ} (hr1 : 0 < r1) :
    fwChart.farLobeMass (FoldTipSetting.ofFixedWeight prob) (√2 * chartBV r1) c g ≤
      deltaLobe prob r1 c g := by
  have hAeq : discRadius (√2 * chartBV r1) c = chartAC r1 c ^ 2 := rfl
  have hA0 : 0 ≤ chartAC r1 c ^ 2 := sq_nonneg _
  have hAle := chartAC_sq_le_virasoroAC_sq hr1 hc.le
  have hsub := fwLobe_subset (a0 := √2 * chartBV r1) hc (by rw [hAeq]; exact hA0)
    (by rw [hAeq]; exact hAle)
  rw [hAeq] at hsub
  set Δ := virasoroDeltaChart c (chartAC r1 c ^ 2) with hΔ
  have hΔpos : 0 < Δ := virasoroDeltaChart_pos hc (by rw [abs_of_nonneg hA0]; exact hAle)
  have hPsi : ∀ x : ℝ, 0 < x →
      |(FoldTipSetting.ofFixedWeight prob).Psi c g x| =
        |g x| * prob.cardyV (c / 12) x / prob.cardyNorm (c / 12) g := by
    intro x hx
    change |g x * prob.cardyV (c / 12) x / prob.cardyNorm (c / 12) g| = _
    rw [abs_div, abs_mul, abs_of_nonneg (hV x hx), abs_of_pos hM]
  have hint : IntegrableOn (fun x => |(FoldTipSetting.ofFixedWeight prob).Psi c g x|) (Ioc 0 Δ) := by
    have h1 : IntegrableOn (fun x => |g x| * prob.cardyV (c / 12) x / prob.cardyNorm (c / 12) g)
        (Ioc 0 Δ) :=
      (hg.int_cardy.mono_set Ioc_subset_Ioi_self).div_const _
    exact h1.congr_fun (fun x hx => (hPsi x hx.1).symm) measurableSet_Ioc
  unfold FTChart.farLobeMass deltaLobe
  calc ∫ x in fwChart.lobe (√2 * chartBV r1) c, |(FoldTipSetting.ofFixedWeight prob).Psi c g x|
      ≤ ∫ x in Ioc 0 Δ, |(FoldTipSetting.ofFixedWeight prob).Psi c g x| :=
        setIntegral_mono_set hint (Eventually.of_forall fun x => abs_nonneg _)
          (Eventually.of_forall hsub)
    _ = ∫ x in Ioc 0 Δ, |g x| * prob.cardyV (c / 12) x / prob.cardyNorm (c / 12) g :=
        setIntegral_congr_fun measurableSet_Ioc (fun x hx => hPsi x hx.1)
    _ = (prob.cardyNorm (c / 12) g)⁻¹ * ∫ t in (0 : ℝ)..Δ, |g t| * prob.cardyV (c / 12) t := by
        rw [intervalIntegral.integral_of_le hΔpos.le, integral_div, div_eq_inv_mul]

/-! ### `H2-hol`, `H2`, `H2+`, `H4a` -/

lemma cpow_half_re_pos_of_not_cut {u : ℂ} (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) :
    0 < (u ^ (1 / 2 : ℂ)).re := by
  by_contra hle
  have hre0 : (u ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg u)
  have him_u : u.im = 2 * (u ^ (1 / 2 : ℂ)).re * (u ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im u).symm
  have hre_u : u.re = (u ^ (1 / 2 : ℂ)).re ^ 2 - (u ^ (1 / 2 : ℂ)).im ^ 2 := (airySqrtRe_sq_sub u).symm
  rw [hre0] at him_u hre_u
  exact hcut ⟨by linarith, by nlinarith [sq_nonneg (u ^ (1 / 2 : ℂ)).im]⟩

/-- Type-(II) envelope to the `(N₀, q) = (0, 2)` envelope of `H2`:
`‖u‖^{-1/2} (Re √u)^{-1} ≤ (Re √u)^{-2}`. -/
lemma envelope_typeII_le {u : ℂ} (hcut : ¬ (u.im = 0 ∧ u.re ≤ 0)) {B : ℝ} (hB : 0 ≤ B) :
    B * ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ ≤
      B * (1 + ‖u‖) ^ (0 : ℝ) * ((u ^ (1 / 2 : ℂ)).re) ^ (-(2 : ℝ)) := by
  have hr := cpow_half_re_pos_of_not_cut hcut
  set r := (u ^ (1 / 2 : ℂ)).re with hrdef
  have hu0 : 0 < ‖u‖ := by
    rw [norm_pos_iff]
    rintro rfl
    exact hcut ⟨rfl, le_rfl⟩
  have hrle : r ≤ √‖u‖ := by
    rw [← norm_cpow_half u]
    exact Complex.re_le_norm _
  have h1 : ‖u‖ ^ (-(1 / 2 : ℝ)) ≤ r⁻¹ := by
    rw [Real.rpow_neg hu0.le, ← Real.sqrt_eq_rpow]
    exact inv_anti₀ hr hrle
  rw [Real.rpow_zero, mul_one, Real.rpow_neg hr.le, Real.rpow_two, ← inv_pow, sq]
  have : ‖u‖ ^ (-(1 / 2 : ℝ)) * r⁻¹ ≤ r⁻¹ * r⁻¹ :=
    mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hr.le)
  nlinarith [mul_le_mul_of_nonneg_left this hB]

lemma exp_neg_mul_isLittleO_rate {κ : ℝ} (hκ : 0 < κ) (C : ℝ) :
    (fun c : ℝ => C * Real.exp (-κ * c)) =o[atTop] fun c : ℝ => c ^ (-(1 / 3 : ℝ)) * Real.log c := by
  have h1 : (fun c : ℝ => Real.exp (-κ * c)) =o[atTop] fun c : ℝ => c ^ (-(1 / 3 : ℝ)) :=
    isLittleO_exp_neg_mul_rpow_atTop hκ _
  have h2 : (fun c : ℝ => c ^ (-(1 / 3 : ℝ))) =O[atTop] fun c : ℝ => c ^ (-(1 / 3 : ℝ)) * Real.log c := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with c hc
    have hc0 : 0 < c := (Real.exp_pos 1).trans_le hc
    have hlog : 1 ≤ Real.log c := by
      rw [Real.le_log_iff_exp_le hc0]; exact hc
    have hp : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    rw [Real.norm_of_nonneg hp, Real.norm_of_nonneg (mul_nonneg hp (by linarith)), one_mul]
    nlinarith
  exact (h1.trans_isBigO h2).const_mul_left C

theorem fwH1With_zero (prob : FixedWeightProblem) :
    FTH1With (FoldTipSetting.ofFixedWeight prob) (fun _ => 0) := by
  filter_upwards [eventually_ge_atTop (fwCMin prob)] with c hc T g hf
  have hM : 0 < (FoldTipSetting.ofFixedWeight prob).M c g :=
    (FoldTipSetting.ofFixedWeight prob).normPos c hc T g hf
  have hvac : 0 ≤ prob.gVac (c / 12) g := hf.2.2.1
  have hint : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c / 12) t ≤ 0 := by
    unfold FixedWeightProblem.gVac at hvac
    nlinarith [Real.pi_pos]
  show ∫ x in Ioi (0 : ℝ), g x * prob.cardyV (c / 12) x /
    (FoldTipSetting.ofFixedWeight prob).M c g ≤ 0
  rw [integral_div]
  exact div_nonpos_of_nonpos_of_nonneg hint hM.le

/-- **`H1` for the fixed-weight setting, `η_vac ≡ 0`**: `∫ Ψ_g = -g_vac/(2π M[g]) ≤ 0`. -/
theorem fwH1 (prob : FixedWeightProblem) : FTH1 (FoldTipSetting.ofFixedWeight prob) :=
  ⟨⟨fun _ => 0, tendsto_const_nhds, fwH1With_zero prob⟩⟩

lemma mul_rpow_mem_ball {c : ℝ} (hc : 0 < c) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ))) :
    u * ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf := by
  rw [mem_ball_zero_iff] at hu ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc.le _)]
  calc ‖u‖ * c ^ (-(2 / 3 : ℝ)) < virasoroRUInf * c ^ (2 / 3 : ℝ) * c ^ (-(2 / 3 : ℝ)) :=
        mul_lt_mul_of_pos_right hu (Real.rpow_pos_of_pos hc _)
    _ = virasoroRUInf := by
        rw [mul_assoc, ← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero, mul_one]

/-- `ξ_c'` has no zero on the Langer domain (`u_∞ ∘ ξ_∞ = id`). -/
lemma deriv_xiChartC_ne_zero {c : ℝ} (hc : 0 < c) {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ))) :
    deriv (virasoroXiChartC c) u ≠ 0 := by
  have hw := mul_rpow_mem_ball hc hu
  set k : ℂ := ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) with hk
  have hk0 : k ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hc _).ne'
  have hxd : DifferentiableAt ℂ virasoroXiInf (u * k) :=
    (virasoroXiInf_an _ hw).differentiableAt
  have h1 : HasDerivAt (virasoroXiChartC c) (deriv virasoroXiInf (u * k) * k) u := by
    have := hxd.hasDerivAt.comp u (hasDerivAt_mul_const k)
    exact this
  rw [h1.deriv]
  refine mul_ne_zero ?_ hk0
  intro h0
  have hud : DifferentiableAt ℂ virasoroUInf (virasoroXiInf (u * k)) :=
    (virasoroUInf_an _ (virasoroXiInf_mem hw)).differentiableAt
  have h2 : HasDerivAt (fun v => virasoroUInf (virasoroXiInf v))
      (deriv virasoroUInf (virasoroXiInf (u * k)) * deriv virasoroXiInf (u * k)) (u * k) :=
    hud.hasDerivAt.comp (u * k) hxd.hasDerivAt
  have h3 : HasDerivAt (fun v : ℂ => v) 1 (u * k) := hasDerivAt_id _
  have h4 : (fun v => virasoroUInf (virasoroXiInf v)) =ᶠ[𝓝 (u * k)] fun v => v := by
    filter_upwards [isOpen_ball.mem_nhds hw] with v hv
    exact virasoroUInf_xiInf hv
  have h5 := h2.unique (h3.congr_of_eventuallyEq h4)
  rw [h0, mul_zero] at h5
  exact zero_ne_one h5

/-- The envelope function of Proposition P gives that of `H2`. -/
private lemma fw_envAt {prob : FixedWeightProblem} {c C₀ : ℝ} (hc : 0 < c) {g : ℝ → ℝ}
    (hg : TestClass prob (c / 12) g) {r1 : ℝ} (hr1 : 0 < r1)
    (hana : AnalyticOnNhd ℂ (psiTilde prob c g) (psiDom c))
    (him : ∀ u : ℝ, |u| ≤ chartAC r1 c ^ 2 → (psiTilde prob c g (u : ℂ)).im = 0)
    {ς : ℝ → ℝ}
    (henv : ∀ u : ℂ, u ∈ closedBall (0 : ℂ) (chartAC r1 c ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
      ‖psiTilde prob c g u‖ ≤
        C₀ * airyEnv u * Real.exp (ς c * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) (hC₀ : 0 ≤ C₀) :
    fwChart.EnvAt (FoldTipSetting.ofFixedWeight prob) (√2 * chartBV r1) 0 2 ς C₀ 0 c g := by
  refine ⟨psiTilde prob c g, hana.mono (closedBall_chartAC_subset_psiDom hr1 hc),
    fun u hu => ⟨him u hu, ?_⟩, fun u hu hcut => ?_⟩
  · rw [fwChart_PsiT_eq prob hc hg (chart_real_abs_le_virasoro hr1 hc hu), sub_self, abs_zero]
  · refine (henv u hu hcut).trans ?_
    have hB : 0 ≤ C₀ * airyEnv u * Real.exp (ς c * (u ^ (1 / 2 : ℂ)).re) := by
      have : 0 ≤ airyEnv u := (Real.exp_pos _).le
      positivity
    have h := envelope_typeII_le hcut hB
    calc _ = (C₀ * airyEnv u * Real.exp (ς c * (u ^ (1 / 2 : ℂ)).re)) * ‖u‖ ^ (-(1 / 2 : ℝ)) *
          ((u ^ (1 / 2 : ℂ)).re)⁻¹ := rfl
      _ ≤ _ := h

/-- **`H2-hol`, `H2+` and `H4a` for the fixed-weight setting**, with common data
`(c₀, a₀, (N₀, q) = (0, 2), ς_c = generalSigma p_e c, δ_lobe = C_gap e^{-κ c})`. -/
theorem fw_hypotheses (prob : FixedWeightProblem) :
    ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
      FTH2hol (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
      FTH2plus (FoldTipSetting.ofFixedWeight prob) ς δ ∧
      FTH4a (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ := by
  obtain ⟨c_P, C₀, C_gap, κ_gap, hcP, hC₀, hCg, hκ, hH4, hP⟩ :=
    (proposition_P_of_problem prob).choose_spec
  set D := fwD prob with hD
  obtain ⟨hcM1, hcMD, hcMV, hcMN⟩ := fwCMin_spec prob
  have hr1 := D.hr1_pos
  set c0 : ℝ := max (fwCMin prob) c_P with hc0
  have hc0M : fwCMin prob ≤ c0 := le_max_left _ _
  have hc0P : c_P ≤ c0 := le_max_right _ _
  have hc0pos : 0 < c0 := lt_of_lt_of_le zero_lt_one (hcM1.trans hc0M)
  set a0 : ℝ := √2 * chartBV D.r_1 with ha0
  have ha0pos : 0 < a0 := mul_pos (Real.sqrt_pos.2 two_pos) (chartBV_pos hr1)
  have hAeq : ∀ c, discRadius a0 c = chartAC D.r_1 c ^ 2 := fun c => rfl
  have hframe : FTH2Frame (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2
      (generalSigma D.p_e) (fun _ c => C_gap * Real.exp (-κ_gap * c)) := by
    refine ⟨hc0pos, ha0pos, le_rfl, by norm_num, ?_, ?_, generalSigma_tendsto_zero _, ?_⟩
    · intro c hc u hu
      have hc' : 0 < c := hc0pos.trans_le hc
      rw [hAeq] at hu
      have hu_vir := chart_mem_virasoroClosedBall hr1 hc' hu
      have hw := virasoro_u_mem_open_ball hc' hu_vir
      refine ⟨virasoroXiInf (u * ((c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)), virasoroXiInf_mem hw, ?_⟩
      unfold FTChart.uc
      change ((c ^ (2 / 3 : ℝ) : ℝ) : ℂ) * virasoroUInf (virasoroXiInf _) = u
      rw [virasoroUInf_xiInf hw, mul_comm u, ← mul_assoc, ← Complex.ofReal_mul,
        ← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
    · intro c hc
      exact generalSigma_nonneg D.hp_e_nn (hcM1.trans (hc0M.trans hc))
    · intro K hK
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun c : ℝ => -κ_gap * c) atTop atBot :=
          Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
        simpa using (Real.tendsto_exp_atBot.comp this).const_mul C_gap
      · intro c hc g hg
        obtain ⟨T, -, hf⟩ := hg
        have hc' : 0 < c := hc0pos.trans_le hc
        have hcM : fwCMin prob ≤ c := hc0M.trans hc
        have hV : ∀ t : ℝ, 0 < t → 0 ≤ prob.cardyV (c / 12) t :=
          fun t ht => (hcMV c hcM t ht).le
        refine (fw_farLobeMass_le_deltaLobe prob hc' hf.1 (hcMN c hcM T g hf) hV hr1).trans ?_
        exact (hP (hc0P.trans hc) hf).2.2.2.1
  have hhol : FTH2hol (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2
      (generalSigma D.p_e) (fun _ c => C_gap * Real.exp (-κ_gap * c)) := by
    refine ⟨hframe, fun K hK => ⟨C₀, hC₀, fun c hc g hg => ?_⟩⟩
    obtain ⟨T, -, hf⟩ := hg
    have hc' : 0 < c := hc0pos.trans_le hc
    obtain ⟨hana, hreal, henv, -⟩ := hP (hc0P.trans hc) hf
    exact fw_envAt hc' hf.1 hr1 hana (fun u hu => (hreal u hu).1) henv hC₀.le
  refine ⟨c0, a0, generalSigma D.p_e, fun _ c => C_gap * Real.exp (-κ_gap * c), hhol, ?_, ?_⟩
  · refine ⟨?_, 0, fwH1With_zero prob, fun K hK => ?_⟩
    · have : generalSigma D.p_e = fun c => generalEnvC1 D.p_e * (c ^ (-(1 / 3 : ℝ)) * Real.log c) := by
        funext c; unfold generalSigma; ring
      rw [this]
      exact (Asymptotics.isBigO_refl _ _).const_mul_left _
    · simpa using exp_neg_mul_isLittleO_rate hκ C_gap
  · refine ⟨hhol, fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hbig : Tendsto (fun c : ℝ => discRadius a0 c) atTop atTop := by
      unfold discRadius
      exact (tendsto_pow_atTop two_ne_zero).comp
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul_atTop ha0pos)
    filter_upwards [hbig.eventually_gt_atTop R, eventually_ge_atTop c0] with c hcR hc
    have hc' : 0 < c := hc0pos.trans_le hc
    have hcball : ball (0 : ℂ) (discRadius a0 c) ⊆ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ)) :=
      ball_subset_ball ((chartAC_sq_le_virasoroAC_sq hr1 hc'.le).trans (virasoroAC_sq_lt_domain hc').le)
    have hKsub : K ⊆ ball (0 : ℂ) (discRadius a0 c) := fun u hu => by
      rw [mem_ball_zero_iff]; exact (hR u hu).trans_lt hcR
    refine ⟨hKsub, fun u hu => ?_, fun u hu => ?_⟩
    · have hu1 : u ∈ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ)) := hcball (hKsub hu)
      have hΞ : AnalyticAt ℂ (virasoroXiChartC c) u := virasoroXiChartC_analyticOnNhd hc' u hu1
      have hΞ' : AnalyticAt ℂ (deriv (virasoroXiChartC c)) u :=
        (virasoroXiChartC_analyticOnNhd hc').deriv u hu1
      have hV : AnalyticAt ℂ (fun v => cardyVC prob (c / 12) ((c : ℂ) * virasoroXiChartC c v)) u :=
        ((cardyVC_entire prob (c / 12)).analyticAt _).comp_of_eq (analyticAt_const.mul hΞ) rfl
      have hfun : AnalyticAt ℂ (fun v => (c : ℂ) * cardyVC prob (c / 12) ((c : ℂ) * virasoroXiChartC c v) *
          deriv (virasoroXiChartC c) v) u := (analyticAt_const.mul hV).mul hΞ'
      refine hfun.congr ?_
      filter_upwards [isOpen_ball.mem_nhds hu1] with v hv
      change (c : ℂ) * cardyVC prob (c / 12) ((c : ℂ) * virasoroXiChartC c v) *
          deriv (virasoroXiChartC c) v = (c : ℂ) * cardyVC prob (c / 12) ((c : ℂ) * fwChart.xic c v) *
          deriv (fwChart.xic c) v
      rw [fwChart_xic_eq hc' hv, fwChart_deriv_xic_eq hc' hv]
    · have hu1 : u ∈ ball (0 : ℂ) (virasoroRUInf * c ^ (2 / 3 : ℝ)) := hcball (hKsub hu)
      have hu2 : u ∈ closedBall (0 : ℂ) (chartAC D.r_1 c ^ 2) := ball_subset_closedBall (hKsub hu)
      change (c : ℂ) * cardyVC prob (c / 12) ((c : ℂ) * fwChart.xic c u) * deriv (fwChart.xic c) u ≠ 0
      rw [fwChart_xic_eq hc' hu1, fwChart_deriv_xic_eq hc' hu1]
      have hb := virasoroBChart_sub_xiStar_le_r1 hr1 hc' hu2
      have hcv := hH4 (hc0P.trans hc) (virasoroBChart c u)
        (by rw [mem_closedBall, dist_eq_norm]; exact hb)
      have hsq : (c : ℂ) * virasoroBChart c u ^ 2 / 3 = (c : ℂ) * virasoroXiChartC c u := by
        unfold virasoroBChart
        rw [virasoroBOfXi_sq]; ring
      rw [hsq] at hcv
      exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 hc'.ne') hcv)
        (deriv_xiChartC_ne_zero hc' hu1)

/-! ### `H4b` for weight-one problems -/

/-- The extremal crossing measures at scale `c`: admissible crossing measures at gap exactly `T_V(c)`
(supported on `[T_V(c), ∞)`, charging every `[T_V(c), T_V(c) + ε)`), for `c` in the range where `T_V(c) > 0`
and `c ≥ 12 S`. -/
def fwExtremal (prob : FixedWeightProblem) (c : ℝ) : Set (Measure ℝ) :=
  {ν | ∃ meas : AdmissibleCrossingMeasure prob (c / 12), meas.ν = ν ∧ 0 < c ∧
    12 * prob.totalShift ≤ c ∧ 0 < prob.T_V c ∧ IsAtGap meas (prob.T_V c) ∧
    ∀ ε : ℝ, 0 < ε → 0 < ν (Iio (prob.T_V c + ε))}

/-- The crossing data of a fixed-weight problem: extremal measures, the window measure `μ_S`
(`spectralMeasure`, in the tip variable of `Upper.Rigidity.Dictionary`), the comb-decay tests of Property (P1)
and `v[g] = g_vac`. -/
noncomputable def fwCrossingData (prob : FixedWeightProblem) :
    FTCrossingData (FoldTipSetting.ofFixedWeight prob) where
  extremal := fwExtremal prob
  window := fun c ν => spectralMeasure prob c ν
  tests := fun c => {g : ℝ → ℝ | TestClass prob (c / 12) g ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
    |g t| ≤ C * Real.exp (-4 * π * Real.sqrt ((c / 12) * t) - π * Real.sqrt (3 * t / c))}
  vac := fun c g => prob.gVac (c / 12) g

/-- **`H4b` for every weight-one fixed-weight problem**, from Property (P) for the designs and displaced
designs, the omitted family and `Σ` (`sigma_of_threshold_prob`, the ingredients of
`sigma_unconditional_prob`), for every sequence of extremal crossing measures. -/
theorem fwH4b (prob : FixedWeightProblem) (hw : prob.w = 1) :
    FTH4b (FoldTipSetting.ofFixedWeight prob) (fwCrossingData prob) := by
  refine ⟨⟨0, fun c _ ν hν g hg => ?_⟩, fun cs ν hcs hν => ?_⟩
  · obtain ⟨meas, hmeas, hc, hshift, -, -, -⟩ := hν
    obtain ⟨hgt, C, hC, hdecay⟩ := hg
    obtain ⟨hint, heq⟩ := sumRule_of_comb_decay prob hshift hc meas hgt hC hdecay
    have hae : ∀ᵐ x ∂meas.ν, x ∈ Ici (0 : ℝ) := by
      rw [ae_iff]
      have : {a : ℝ | ¬ a ∈ Ici (0 : ℝ)} = Iio 0 := by ext a; simp
      rw [this]
      exact meas.supp_nonneg
    have hres : meas.ν.restrict (Ici (0 : ℝ)) = meas.ν := Measure.restrict_eq_self_of_ae_mem hae
    subst hmeas
    refine ⟨?_, ?_⟩
    · have := hint
      unfold IntegrableOn at this
      rwa [hres] at this
    · rw [hres] at heq
      exact heq
  · choose meas hmeas using fun j => hν j
    let S : CrossingSequence prob :=
      { c := cs
        τ := fun j => prob.T_V (cs j)
        meas := meas
        tendsto_c := hcs
        c_pos := fun j => (hmeas j).2.1
        shift_le := fun j => by have := (hmeas j).2.2.1; linarith
        τ_pos := fun j => (hmeas j).2.2.2.1
        atGap := fun j => (hmeas j).2.2.2.2.1 }
    have hμ : (fun j => (fwCrossingData prob).window (cs j) (ν j)) = S.μS := by
      funext j
      show spectralMeasure prob (cs j) (ν j) = spectralMeasure prob (cs j) (meas j).ν
      rw [(hmeas j).1]
    have key : ∀ μ : ℕ → Measure ℝ, μ = S.μS →
        LocallyBounded μ ∧
        (∀ (D : Window) (T : DesignTest μ D) (ε : ℝ), 0 < ε →
          ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ᶠ j in atTop, ∫ u in Iio (-R), T.Ψ j u ∂(μ j) ≤ ε) ∧
        ∃ 𝒟 : Set Window, DesignPropertyP μ 𝒟 ∧
          Nonempty (SameSiteFamily 𝒟) ∧ Nonempty (DisplacedFamily 𝒟) ∧ Nonempty (OmittedFamily 𝒟) := by
      intro μ hμ'
      subst hμ'
      have hLo := fixedWeightLowerBoundInput_of_problem prob
      have hSig : SigmaConclusion S.μS :=
        sigma_of_threshold_prob prob hw hLo S (fun j => le_rfl) (𝒟x := displacedClassX)
          (displacedPropertyP_prob prob hw S) sameSiteFamily_designClass_exists.some
          (DisplacedFamily.mono (displacedClass_subset.trans Set.subset_union_right) displacedFamily)
          farFamily
      refine ⟨hSig.1, hSig.2.2.2.2, designClass ∪ displacedClassX, ?_, ?_, ?_, ?_⟩
      · exact designPropertyP_union (designPropertyP_prob prob hw S) (displacedPropertyP_prob prob hw S)
      · exact ⟨SameSiteFamily.mono Set.subset_union_left sameSiteFamily_designClass_exists.some⟩
      · exact ⟨DisplacedFamily.mono (displacedClass_subset.trans Set.subset_union_right) displacedFamily⟩
      · exact ⟨farFamily⟩
    exact key _ hμ

/-! ### Named instances and the weight-one bundle -/

/-- **`H2-hol`** for every fixed-weight problem (`(N₀, q) = (0, 2)`, `ς_c = C₁ c^{-1/3} log c`, `δ_lobe = O(e^{-κ c})`). -/
theorem fwH2hol (prob : FixedWeightProblem) :
    ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
      FTH2hol (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ :=
  by obtain ⟨c0, a0, ς, δ, h, -, -⟩ := fw_hypotheses prob; exact ⟨c0, a0, ς, δ, h⟩

/-- **`H2`** for every fixed-weight problem. -/
theorem fwH2 (prob : FixedWeightProblem) :
    ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
      FTH2 (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ :=
  by obtain ⟨c0, a0, ς, δ, h⟩ := fwH2hol prob; exact ⟨c0, a0, ς, δ, h.toFTH2⟩

/-- **`H2+`** for every fixed-weight problem, for the same `ς`, `δ` as `H2-hol` (`fw_hypotheses`). -/
theorem fwH2plus (prob : FixedWeightProblem) :
    ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
      FTH2hol (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2plus (FoldTipSetting.ofFixedWeight prob) ς δ :=
  by obtain ⟨c0, a0, ς, δ, h, h2, -⟩ := fw_hypotheses prob; exact ⟨c0, a0, ς, δ, h, h2⟩

/-- **`H4a`** for every fixed-weight problem. -/
theorem fwH4a (prob : FixedWeightProblem) :
    ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
      FTH4a (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ :=
  by obtain ⟨c0, a0, ς, δ, -, -, h⟩ := fw_hypotheses prob; exact ⟨c0, a0, ς, δ, h⟩

/-- **`H3` for `prob.w = 1`**, unconditional (`Upper.Ramped.theoremC15UpperInput_prob`). -/
theorem fwH3_w1 (prob : FixedWeightProblem) (hw : prob.w = 1) :
    FTH3 (FoldTipSetting.ofFixedWeight prob) :=
  fwH3 prob (Upper.Ramped.theoremC15UpperInput_prob prob hw)

/-- **All hypotheses of Theorem FT hold for every weight-one fixed-weight problem** (Virasoro and
`𝒩 = 1` super-Virasoro included): `H1`, `H2`, `H2-hol`, `H2+`, `H3`, `H4a` (with common data) and `H4b`.
These instances are the non-vacuity of the structures of `FoldTip/Hypotheses.lean`. -/
theorem fw_foldTip_hypotheses_w1 (prob : FixedWeightProblem) (hw : prob.w = 1) :
    FTH1 (FoldTipSetting.ofFixedWeight prob) ∧ FTH3 (FoldTipSetting.ofFixedWeight prob) ∧
      FTH4b (FoldTipSetting.ofFixedWeight prob) (fwCrossingData prob) ∧
      ∃ (c0 a0 : ℝ) (ς : ℝ → ℝ) (δ : ℝ → ℝ → ℝ),
        FTH2 (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2hol (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ ∧
        FTH2plus (FoldTipSetting.ofFixedWeight prob) ς δ ∧
        FTH4a (FoldTipSetting.ofFixedWeight prob) fwChart c0 a0 0 2 ς δ :=
  by
    obtain ⟨c0, a0, ς, δ, h, h2, h4⟩ := fw_hypotheses prob
    exact ⟨fwH1 prob, fwH3_w1 prob hw, fwH4b prob hw, c0, a0, ς, δ, h.toFTH2, h, h2, h4⟩

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fwH1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwH1

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fwH3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwH3

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fw_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fw_hypotheses

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fwH4b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fwH4b

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.fw_foldTip_hypotheses_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fw_foldTip_hypotheses_w1

end FormalResearch.ModularBootstrap.FoldTip
