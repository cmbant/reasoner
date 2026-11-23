module

public import FormalResearch.ModularBootstrap.FixedWeightTip.PoissonJensenGeneral
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.LangerChart
public import FormalResearch.Special.AiryEnvelope

/-!
# General-`(w, Q)` Proposition P (Steps 1–3) and Lemma Q (`lower_o1_two_edge.tex`)

Formalizes **Proposition P (`ft:PP`)** Steps 1–3 (`(H1)`, `(H2-hol)`, `(H2+)`, `(H4a)`) and
item `(4)` / **Lemma Q (`wone:Q`)** parts `(1)`–`(3)` at every fixed `(w, Q)`
(`prob : FixedWeightProblem`), reusing the Virasoro Langer chart (`ConcreteBootstrap/LangerChart`)
inside the `r₁`-shrunk chart radius `chartAC r₁ c'` (`0 < r₁ ≤ ξ_* / 2`):

* `UniformPropositionPData`: uniform-in-`c'` Proposition P data `(P0)–(P3)`, constructed
  unconditionally for every `prob : FixedWeightProblem` via `UniformPropositionPData.of_problem`.
* `chartBV`, `chartAC`, `virasoroBChart_sub_xiStar_le_r1`: chart scale shrunk so that the image
  of `closedBall 0 (chartAC r₁ c' ^ 2)` under `b(u)` lies in `closedBall (ξ_* : ℂ) r₁` while
  inheriting every `LangerChart.lean` estimate verbatim.
* `cardyVC_ne_zero_of_eta_lt`, `W_C_prob`, `W_C_prob_norm_le`: disc zero-freeness `(H4a)` and the
  `c'`-free `(2b)^{w-1}` weight envelope on `closedBall (ξ_* : ℂ) r₁`.
* `psiTilde`, `deltaLobe`, `chartUT`: transported density `Ψ̃`, far-lobe mass `δ_lobe`, and
  threshold image `u_T`.
* `psiTilde_analyticOnNhd`, `psiTilde_typeII_envelope_general`, `deltaLobe_gap_general`: Steps 1–3
  (`(H2-hol)`, type-(II) envelope with `ς_{c'} = C₁ c'^{-1/3} log c'`, far-lobe decay).
* `lemmaQ_general_part1`, `lemmaQ_general_part2`, `lemmaQ_general_part3`,
  `proposition_P_general`, `proposition_P_of_problem`: general-`(w, Q)` Proposition P and Lemma Q
  (with explicit upper threshold `T < Δ(-A_{c'}^2)` for the interior chart placement of `u_T`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightTip

open Crossing PoissonJensen WeightAxioms TipFront ConcreteBootstrap FormalResearch.Special

/-! ### Section 1: Uniform Proposition P data and non-vacuity / problem witness -/

/-- Uniform-in-`c'` Proposition P data `(P0)–(P3)` for a fixed-weight problem `prob`,
with `η_V(c') → 0` and `η_vac(c') = 0`. -/
structure UniformPropositionPData (prob : FixedWeightProblem) where
  c₀ : ℝ
  hc₀_ge1 : 1 ≤ c₀
  C_e : ℝ
  hCe_pos : 0 < C_e
  p_e : ℝ
  hp_e_nn : 0 ≤ p_e
  c_band : ℝ
  hc_band_pos : 0 < c_band
  C_up : ℝ
  hCup_pos : 0 < C_up
  p_u : ℝ
  hp_u_nn : 0 ≤ p_u
  r_1 : ℝ
  hr1_pos : 0 < r_1
  hr1_le : r_1 ≤ xiStar / 2
  Q_star : ℂ → ℂ
  η_V_max : ℝ
  hηV_max_nn : 0 ≤ η_V_max
  pAt : ∀ {c' : ℝ}, c₀ ≤ c' → PropositionPAxioms prob c'
  uniform_C_e : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').C_e = C_e
  uniform_p_e : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').p_e = p_e
  uniform_c_band : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').c_band = c_band
  uniform_C_up : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').C_up = C_up
  uniform_p_u : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').p_u = p_u
  uniform_r_1 : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').r_1 = r_1
  uniform_Q_star : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').Q_star = Q_star
  uniform_ηV_le : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').η_V ≤ η_V_max
  disc_err_tendsto_zero :
    Tendsto (fun c' : ℝ => if h : c₀ ≤ c' then (pAt h).η_V else 0) atTop (𝓝 0)
  vac_err_zero : ∀ {c' : ℝ} (hc' : c₀ ≤ c'), (pAt hc').η_vac = 0

lemma UniformPropositionPData.hc₀_pos {prob : FixedWeightProblem}
    (D : UniformPropositionPData prob) : 0 < D.c₀ :=
  zero_lt_one.trans_le D.hc₀_ge1

lemma UniformPropositionPData.p1_pos {prob : FixedWeightProblem}
    (D : UniformPropositionPData prob) {c' t : ℝ} (hc' : D.c₀ ≤ c') (ht : 0 < t) :
    0 < prob.cardyV (c' / 12) t :=
  (D.pAt hc').p1_pos ht

lemma UniformPropositionPData.cardyV_nonneg {prob : FixedWeightProblem}
    (D : UniformPropositionPData prob) {c' t : ℝ} (hc' : D.c₀ ≤ c') (ht : 0 ≤ t) :
    0 ≤ prob.cardyV (c' / 12) t := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · have hlim : Tendsto (prob.cardyV (c' / 12)) (𝓝[>] (0 : ℝ)) (𝓝 (prob.cardyV (c' / 12) 0)) :=
      (continuous_cardyV prob (c' / 12)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun s hs => (D.p1_pos hc' hs).le)
  · exact (D.p1_pos hc' ht_pos).le

/-- Build `UniformPropositionPData prob` from `FixedWeightUniformAxioms prob`. -/
noncomputable def UniformPropositionPData.ofUniformAxioms {prob : FixedWeightProblem}
    (U : FixedWeightUniformAxioms prob) : UniformPropositionPData prob where
  c₀ := U.c₀
  hc₀_ge1 := (le_max_left (1 : ℝ) (24 * prob.totalShift)).trans U.hc₀_ge
  C_e := U.C_e
  hCe_pos := U.hCe_pos
  p_e := U.p_e
  hp_e_nn := U.hp_e_nn
  c_band := U.c_band
  hc_band_pos := U.hc_band_pos
  C_up := U.C_up
  hCup_pos := U.hCup_pos
  p_u := U.p_u
  hp_u_nn := U.hp_u_nn
  r_1 := U.r_1
  hr1_pos := U.hr1_pos
  hr1_le := U.hr1_le
  Q_star := U.Q_star
  η_V_max := U.C_V / U.c₀
  hηV_max_nn := div_nonneg U.hCV_nn (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans U.hc₀_ge)).le
  pAt hc' := (U.axioms_at hc').toPropositionPAxioms
  uniform_C_e hc' := U.uniform_C_e hc'
  uniform_p_e hc' := U.uniform_p_e hc'
  uniform_c_band hc' := U.uniform_c_band hc'
  uniform_C_up hc' := U.uniform_C_up hc'
  uniform_p_u hc' := U.uniform_p_u hc'
  uniform_r_1 hc' := U.uniform_r_1 hc'
  uniform_Q_star hc' := U.uniform_Q_star hc'
  uniform_ηV_le hc' := by
    dsimp only [FixedWeightAxioms.toPropositionPAxioms]
    rw [U.uniform_C_V hc']
    have hc₀_pos : 0 < U.c₀ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans U.hc₀_ge)
    exact div_le_div_of_nonneg_left U.hCV_nn hc₀_pos hc'
  disc_err_tendsto_zero := (uniformP_of_uniformAxioms U).disc_err_tendsto_zero
  vac_err_zero hc' := (uniformP_of_uniformAxioms U).vac_err_zero hc'

/-- Unconditional `UniformPropositionPData prob` (and hence non-vacuity) for every
`prob : FixedWeightProblem`. -/
theorem UniformPropositionPData.of_problem (prob : FixedWeightProblem) :
    Nonempty (UniformPropositionPData prob) :=
  let ⟨U⟩ := fixedWeightAxioms_of_problem prob
  ⟨UniformPropositionPData.ofUniformAxioms U⟩

lemma UniformPropositionPData.lemmaG {prob : FixedWeightProblem}
    (D : UniformPropositionPData prob) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < xiStar) :
    ∃ c_deep C_deep κ_deep : ℝ, 1 ≤ c_deep ∧ 0 < C_deep ∧ 0 < κ_deep ∧
      ∀ {c' : ℝ}, c_deep ≤ c' →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          ∫ t in (0 : ℝ)..(c' * (xiStar - δ) ^ 2 / 3), |g t| * prob.cardyV (c' / 12) t ≤
            C_deep * Real.exp (-κ_deep * c') * prob.cardyNorm (c' / 12) g :=
  lemmaG_general_of_uniform prob D.hc₀_ge1 D.hCe_pos D.hp_e_nn D.hc_band_pos D.hCup_pos D.hp_u_nn
    (fun {_c'} hc' => ⟨D.pAt hc', D.uniform_C_e hc', D.uniform_p_e hc', D.uniform_c_band hc',
      D.uniform_C_up hc', D.uniform_p_u hc'⟩) hδ0 hδ1

/-! ### Section 2: Shrunk chart radius `chartAC r₁ c'` and complex-disc `(P2)` bounds -/

/-- Bootstrap radius parameter `b_V(r₁) ≤ virasoroBV`, shrunk if necessary so that
`2 b_V(r₁)² ≤ r₁ / chartParams.C_b`. -/
noncomputable def chartBV (r_1 : ℝ) : ℝ :=
  min virasoroBV (Real.sqrt (r_1 / (2 * chartParams.C_b)))

lemma chartBV_pos {r_1 : ℝ} (hr1 : 0 < r_1) : 0 < chartBV r_1 :=
  lt_min virasoroBV_pos (Real.sqrt_pos.mpr (div_pos hr1 (mul_pos two_pos chartParams.hCb_pos)))

lemma chartBV_le_virasoroBV (r_1 : ℝ) : chartBV r_1 ≤ virasoroBV :=
  min_le_left _ _

lemma two_chartBV_sq_le {r_1 : ℝ} (hr1 : 0 < r_1) :
    2 * chartBV r_1 ^ 2 ≤ r_1 / chartParams.C_b := by
  have hle : chartBV r_1 ≤ Real.sqrt (r_1 / (2 * chartParams.C_b)) := min_le_right _ _
  have hsq : chartBV r_1 ^ 2 ≤ Real.sqrt (r_1 / (2 * chartParams.C_b)) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_pos (chartBV_pos hr1), abs_of_nonneg (Real.sqrt_nonneg _)]; exact hle)
  rw [Real.sq_sqrt (div_nonneg hr1.le (by positivity [chartParams.hCb_pos]))] at hsq
  calc 2 * chartBV r_1 ^ 2 ≤ 2 * (r_1 / (2 * chartParams.C_b)) := by gcongr
    _ = r_1 / chartParams.C_b := by ring

/-- Shrunk chart radius `A_{c'}(r₁) = √2 b_V(r₁) c'^{1/3}`. -/
noncomputable def chartAC (r_1 c' : ℝ) : ℝ :=
  √2 * chartBV r_1 * c' ^ (1 / 3 : ℝ)

lemma chartAC_pos {r_1 c' : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c') : 0 < chartAC r_1 c' := by
  unfold chartAC
  have hb := chartBV_pos hr1
  positivity

lemma chartAC_sq (r_1 c' : ℝ) (hc' : 0 ≤ c') :
    chartAC r_1 c' ^ 2 = 2 * chartBV r_1 ^ 2 * c' ^ (2 / 3 : ℝ) := by
  unfold chartAC
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← Real.rpow_natCast (c' ^ (1 / 3 : ℝ)) 2,
    ← Real.rpow_mul hc']
  norm_num

lemma chartAC_sq_le_virasoroAC_sq {r_1 c' : ℝ} (hr1 : 0 < r_1) (hc' : 0 ≤ c') :
    chartAC r_1 c' ^ 2 ≤ virasoroAC c' ^ 2 := by
  rw [chartAC_sq r_1 c' hc', virasoroAC_sq c' hc']
  have hle : chartBV r_1 ^ 2 ≤ virasoroBV ^ 2 :=
    sq_le_sq.mpr (by rw [abs_of_pos (chartBV_pos hr1), abs_of_pos virasoroBV_pos]; exact chartBV_le_virasoroBV r_1)
  gcongr

lemma chart_mem_virasoroClosedBall {r_1 c' : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (chartAC r_1 c' ^ 2)) :
    u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2) :=
  closedBall_subset_closedBall (chartAC_sq_le_virasoroAC_sq hr1 hc'.le) hu

lemma chart_real_abs_le_virasoro {r_1 c' u : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c')
    (hu : |u| ≤ chartAC r_1 c' ^ 2) :
    |u| ≤ virasoroAC c' ^ 2 :=
  hu.trans (chartAC_sq_le_virasoroAC_sq hr1 hc'.le)

lemma virasoroBChart_sub_xiStar_le_r1 {r_1 c' : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (chartAC r_1 c' ^ 2)) :
    ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤ r_1 := by
  have hu_vir := chart_mem_virasoroClosedBall hr1 hc' hu
  have hw_ball : u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (2 * virasoroBV ^ 2) :=
    virasoro_u_mem_ball hc' hu_vir
  have hlip := chartParams.hCb_bd _ hw_ball
  change ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤
      chartParams.C_b * ‖u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)‖ at hlip
  rw [mem_closedBall_zero_iff] at hu
  have hcr : chartAC r_1 c' ^ 2 * c' ^ (-(2 / 3 : ℝ)) = 2 * chartBV r_1 ^ 2 := by
    rw [chartAC_sq r_1 c' hc'.le, mul_assoc, ← Real.rpow_add hc', add_neg_cancel, Real.rpow_zero, mul_one]
  have hnorm_w : ‖u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)‖ ≤ 2 * chartBV r_1 ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc'.le _), ← hcr]
    exact mul_le_mul_of_nonneg_right hu (Real.rpow_nonneg hc'.le _)
  calc ‖virasoroBChart c' u - (xiStar : ℂ)‖
      ≤ chartParams.C_b * ‖u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)‖ := hlip
    _ ≤ chartParams.C_b * (2 * chartBV r_1 ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm_w chartParams.hCb_pos.le
    _ ≤ chartParams.C_b * (r_1 / chartParams.C_b) :=
        mul_le_mul_of_nonneg_left (two_chartBV_sq_le hr1) chartParams.hCb_pos.le
    _ = r_1 := mul_div_cancel₀ _ chartParams.hCb_pos.ne'

private lemma deriv_virasoroDeltaChartC_eq_bChart {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ))) :
    deriv (virasoroDeltaChartC c') u =
      ((2 * c' / 3 : ℝ) : ℂ) * virasoroBChart c' u * deriv (virasoroBChart c') u := by
  have hb_an : AnalyticAt ℂ (virasoroBChart c') u := virasoroBChart_analyticOnNhd hc' u hu
  have hsq : HasDerivAt (fun z => ((c' : ℂ) / 3) * virasoroBChart c' z ^ 2)
      (((c' : ℂ) / 3) * ((2 : ℂ) * virasoroBChart c' u ^ (2 - 1) * deriv (virasoroBChart c') u)) u :=
    (hb_an.differentiableAt.hasDerivAt.pow 2).const_mul ((c' : ℂ) / 3)
  have heq : (fun z => ((c' : ℂ) / 3) * virasoroBChart c' z ^ 2) = virasoroDeltaChartC c' := by
    ext z
    have hb2 : virasoroBChart c' z ^ 2 = 3 * virasoroXiChartC c' z := by
      unfold virasoroBChart virasoroBOfXi
      exact cpow_half_sq _
    unfold virasoroDeltaChartC
    rw [hb2]
    have h3 : (3 : ℂ) ≠ 0 := by norm_num
    field_simp [h3]
  rw [heq] at hsq
  rw [hsq.deriv]
  simp only [Nat.reduceSub, pow_one]
  push_cast
  ring

private lemma virasoroBChart_deriv_norm_le {c' : ℝ} (hc' : 0 < c') {u : ℂ}
    (hu : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2)) :
    ‖deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)‖ ≤
      (2 / xiStar) * chartParams.C_dxi := by
  have hu_open : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := by
    rw [mem_closedBall_zero_iff] at hu
    rw [mem_ball_zero_iff]
    exact hu.trans_lt (virasoroAC_sq_lt_domain hc')
  have hb_an : AnalyticAt ℂ (virasoroBChart c') u := virasoroBChart_analyticOnNhd hc' u hu_open
  have hxi_an : AnalyticAt ℂ (virasoroXiChartC c') u := virasoroXiChartC_analyticOnNhd hc' u hu_open
  have hsq : (fun z => virasoroBChart c' z ^ 2) = fun z => (3 : ℂ) * virasoroXiChartC c' z := by
    ext z; unfold virasoroBChart virasoroBOfXi; exact cpow_half_sq _
  have hd_lhs : HasDerivAt (fun z => virasoroBChart c' z ^ 2)
      (2 * virasoroBChart c' u * deriv (virasoroBChart c') u) u := by
    convert hb_an.differentiableAt.hasDerivAt.pow 2 using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hd_rhs : HasDerivAt (fun z => (3 : ℂ) * virasoroXiChartC c' z)
      (3 * deriv (virasoroXiChartC c') u) u :=
    hxi_an.differentiableAt.hasDerivAt.const_mul 3
  rw [hsq] at hd_lhs
  have hd_eq : 2 * virasoroBChart c' u * deriv (virasoroBChart c') u =
      3 * deriv (virasoroXiChartC c') u := hd_lhs.unique hd_rhs
  let s : ℝ := c' ^ (-(2 / 3 : ℝ))
  let w : ℂ := u * (s : ℂ)
  have hw_mem : w ∈ ball (0 : ℂ) virasoroRUInf := virasoro_u_mem_open_ball hc' hu
  have hw_cl : w ∈ closedBall (0 : ℂ) (2 * virasoroBV ^ 2) := virasoro_u_mem_ball hc' hu
  have hd_xi : HasDerivAt virasoroXiInf (deriv virasoroXiInf w) w :=
    (virasoroXiInf_an w hw_mem).differentiableAt.hasDerivAt
  have hd_lin : HasDerivAt (fun z : ℂ => z * (s : ℂ)) (s : ℂ) u := by
    simpa using (hasDerivAt_id u).mul_const (s : ℂ)
  have hd_xiChart : deriv (virasoroXiChartC c') u = deriv virasoroXiInf w * (s : ℂ) :=
    ((hd_xi.comp u hd_lin).congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)).deriv
  have hs_eq : (s : ℂ) = ((tipEps c' : ℝ) : ℂ) := rfl
  rw [hd_xiChart, hs_eq] at hd_eq
  have hb_min := virasoro_deltaChart_b_min hc' hu
  have hb_sub : ‖virasoroBChart c' u - (xiStar : ℂ)‖ ≤ xiStar / 4 :=
    hb_min.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb_lb : 3 * xiStar / 4 ≤ ‖virasoroBChart c' u‖ := by
    have htri := norm_sub_norm_le (xiStar : ℂ) (virasoroBChart c' u)
    rw [norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le] at htri
    linarith
  have hb_ne : virasoroBChart c' u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hb_lb; linarith [xiStar_pos]
  have hε_ne : ((tipEps c' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (tipEps_pos hc').ne'
  have hdiv_eq : deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ) =
      (3 / (2 * virasoroBChart c' u)) * deriv virasoroXiInf w := by
    have h2b : (2 : ℂ) * virasoroBChart c' u ≠ 0 := mul_ne_zero (by norm_num) hb_ne
    apply mul_left_cancel₀ h2b
    calc (2 * virasoroBChart c' u) * (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ))
        = (2 * virasoroBChart c' u * deriv (virasoroBChart c') u) / ((tipEps c' : ℝ) : ℂ) := by ring
      _ = (3 * (deriv virasoroXiInf w * ((tipEps c' : ℝ) : ℂ))) / ((tipEps c' : ℝ) : ℂ) := by
          rw [hd_eq]
      _ = (2 * virasoroBChart c' u) * ((3 / (2 * virasoroBChart c' u)) * deriv virasoroXiInf w) := by
          field_simp [hb_ne, hε_ne]
  rw [hdiv_eq, norm_mul, norm_div, Complex.norm_ofNat, norm_mul, Complex.norm_ofNat]
  have h32_bd : (3 : ℝ) / (2 * ‖virasoroBChart c' u‖) ≤ 2 / xiStar := by
    have hden_pos : 0 < 2 * (3 * xiStar / 4) := by linarith [xiStar_pos]
    calc (3 : ℝ) / (2 * ‖virasoroBChart c' u‖)
        ≤ 3 / (2 * (3 * xiStar / 4)) := by gcongr
      _ = 2 / xiStar := by field_simp [xiStar_pos.ne']; ring
  have hdxi_bd : ‖deriv virasoroXiInf w‖ ≤ chartParams.C_dxi := chartParams.hdxi_bd w hw_cl
  exact mul_le_mul h32_bd hdxi_bd (norm_nonneg _) (by positivity [xiStar_pos])

private lemma norm_asC_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ‖asC z‖ = Real.exp z.re / √(2 * Real.pi * ‖z‖) := by
  unfold asC
  have hz_ne : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2piz_ne : 2 * (Real.pi : ℂ) * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) hz_ne
  have hcpow_norm : ‖(2 * (Real.pi : ℂ) * z) ^ (1 / 2 : ℂ)‖ = √(2 * Real.pi * ‖z‖) := by
    rw [Complex.cpow_def_of_ne_zero h2piz_ne, Complex.norm_exp]
    have hre : (Complex.log (2 * (Real.pi : ℂ) * z) * (1 / 2 : ℂ)).re =
        Real.log (2 * Real.pi * ‖z‖) / 2 := by
      rw [Complex.mul_re, Complex.log_re, show (1 / 2 : ℂ).re = 1 / 2 by norm_num,
        show (1 / 2 : ℂ).im = 0 by norm_num, mul_zero, sub_zero,
        norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
      ring
    rw [hre, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    congr 1; ring
  rw [norm_div, Complex.norm_exp, hcpow_norm]

private lemma asC_tipL_ne_zero {c' : ℝ} (hc' : 0 < c') {b : ℂ} (hb : 0 < b.re) :
    asC ((c' : ℂ) * tipL b) ≠ 0 := by
  unfold asC
  have hb_ne : b ≠ 0 := fun h => by rw [h, Complex.zero_re] at hb; exact lt_irrefl 0 hb
  have htip_ne : tipL b ≠ 0 := by
    unfold tipL
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity [Real.pi_pos])) hb_ne
  have hz_ne : (c' : ℂ) * tipL b ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hc'.ne') htip_ne
  have hden_ne : (2 * (Real.pi : ℂ) * ((c' : ℂ) * tipL b)) ^ (1 / 2 : ℂ) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) hz_ne
  exact div_ne_zero (Complex.exp_ne_zero _) hden_ne

private lemma closedBall_disc_re_pos {r_1 : ℝ} (hr1_le : r_1 ≤ xiStar / 2) {b : ℂ}
    (hb : b ∈ closedBall (xiStar : ℂ) r_1) : xiStar / 2 ≤ b.re ∧ ‖b‖ ≤ 3 * xiStar / 2 := by
  rw [mem_closedBall, dist_eq_norm] at hb
  have hre : |b.re - xiStar| ≤ ‖b - (xiStar : ℂ)‖ := by
    simpa [Complex.sub_re] using Complex.abs_re_le_norm (b - (xiStar : ℂ))
  have hre_lb : xiStar / 2 ≤ b.re := by linarith [(abs_le.mp (hre.trans hb)).1]
  have hnorm_ub : ‖b‖ ≤ 3 * xiStar / 2 := by
    calc ‖b‖ = ‖(b - (xiStar : ℂ)) + (xiStar : ℂ)‖ := by ring_nf
      _ ≤ ‖b - (xiStar : ℂ)‖ + ‖(xiStar : ℂ)‖ := norm_add_le _ _
      _ ≤ r_1 + xiStar := add_le_add hb (by simp [Complex.norm_real, Real.norm_of_nonneg xiStar_pos.le])
      _ ≤ 3 * xiStar / 2 := by linarith
  exact ⟨hre_lb, hnorm_ub⟩

/-- From Proposition P `(P2)`, `Q_*` is bounded above and away from zero on `closedBall ξ_* r₁`. -/
lemma disc_Q_bounds {r_1 : ℝ} (hr1_nn : 0 ≤ r_1) (hr1_le : r_1 ≤ xiStar / 2)
    {Q_star : ℂ → ℂ} (hQ_holo : DifferentiableOn ℂ Q_star {b : ℂ | 0 < b.re})
    (hQ_ne : ∀ {b : ℂ}, b ∈ closedBall (xiStar : ℂ) r_1 → Q_star b ≠ 0) :
    ∃ c_Q C_Q : ℝ, 0 < c_Q ∧ c_Q ≤ C_Q ∧
      ∀ b ∈ closedBall (xiStar : ℂ) r_1, c_Q ≤ ‖Q_star b‖ ∧ ‖Q_star b‖ ≤ C_Q := by
  have hsub : closedBall (xiStar : ℂ) r_1 ⊆ {b : ℂ | 0 < b.re} := fun b hb => by
    have := (closedBall_disc_re_pos hr1_le hb).1
    change 0 < b.re; linarith [xiStar_pos]
  have hcont : ContinuousOn (fun b => ‖Q_star b‖) (closedBall (xiStar : ℂ) r_1) :=
    (hQ_holo.continuousOn.mono hsub).norm
  have hne : (closedBall (xiStar : ℂ) r_1).Nonempty := ⟨(xiStar : ℂ), mem_closedBall_self hr1_nn⟩
  obtain ⟨b_min, hb_min, hmin⟩ := (isCompact_closedBall (xiStar : ℂ) r_1).exists_isMinOn hne hcont
  obtain ⟨b_max, hb_max, hmax⟩ := (isCompact_closedBall (xiStar : ℂ) r_1).exists_isMaxOn hne hcont
  refine ⟨‖Q_star b_min‖, ‖Q_star b_max‖, norm_pos_iff.mpr (hQ_ne hb_min),
    hmin (hb_max), fun b hb => ⟨hmin hb, hmax hb⟩⟩

/-- **Proposition P `(H4a)`**: whenever `P.η_V < c_Q` (for any positive lower bound `c_Q` on
`‖P.Q_star b‖` over `closedBall ξ_* P.r_1`), `cardyVC prob (c'/12) (c' b^2 / 3) ≠ 0`
throughout the entire Langer disc `closedBall ξ_* P.r_1`. -/
theorem cardyVC_ne_zero_of_eta_lt {prob : FixedWeightProblem} {c' c_Q : ℝ}
    (P : PropositionPAxioms prob c') (hcQ : ∀ b ∈ closedBall (xiStar : ℂ) P.r_1, c_Q ≤ ‖P.Q_star b‖)
    (hη : P.η_V < c_Q) {b : ℂ} (hb : b ∈ closedBall (xiStar : ℂ) P.r_1) :
    cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) ≠ 0 := by
  have hbre := (closedBall_disc_re_pos P.hr1_le hb).1
  have hb_re_pos : 0 < b.re := by linarith [xiStar_pos]
  have h2b_ne : (2 * b) ^ (prob.w - 1) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have hre0 : (2 * b).re = 0 := by rw [h0, Complex.zero_re]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre0
    linarith
  have has_ne : asC ((c' : ℂ) * tipL b) ≠ 0 := asC_tipL_ne_zero P.hc'_pos hb_re_pos
  intro h0
  have hdisc := P.p2_disc_asymp hb
  rw [h0, zero_div, zero_sub, norm_neg] at hdisc
  linarith [hcQ b hb]

/-- Eventually in `c' → ∞`, `cardyVC prob (c'/12) (c' b^2 / 3)` is zero-free on the full Langer
disc `closedBall (ξ_* : ℂ) D.r_1` (**Proposition P `(H4a)`**). -/
theorem propP_H4a_eventually_ne_zero {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∀ᶠ c' in atTop, ∀ b ∈ closedBall (xiStar : ℂ) D.r_1,
      cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) ≠ 0 := by
  have hc₀ := D.hc₀_ge1
  let P₀ := D.pAt (le_rfl : D.c₀ ≤ D.c₀)
  obtain ⟨c_Q, _, hcQ_pos, _, hcQ⟩ := disc_Q_bounds D.hr1_pos.le D.hr1_le (Q_star := D.Q_star)
    (by rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]; exact P₀.p2_Q_holo)
    (fun {b} hb => by
      rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]
      exact P₀.p2_Q_ne_zero (by rwa [D.uniform_r_1 (le_rfl : D.c₀ ≤ D.c₀)]))
  have hη_lt := D.disc_err_tendsto_zero.eventually (eventually_lt_nhds hcQ_pos)
  filter_upwards [eventually_ge_atTop D.c₀, hη_lt] with c' hc' hη b hb
  rw [dite_eq_left_of_eq_true (eq_true hc')] at hη
  refine cardyVC_ne_zero_of_eta_lt (D.pAt hc') (fun b' hb' => ?_) hη
    (by rwa [D.uniform_r_1 hc'])
  rw [D.uniform_Q_star hc']
  exact (hcQ b' (by rwa [← D.uniform_r_1 hc'])).1

/-- Rescaled general-weight tip factor
`W_{w,Q}(b) = ε (2c'/3) b V(c' b^2 / 3)` (`blowup_limit.tex`, §1; exact `c'`-free factor `(2b)^{w-1}`). -/
noncomputable def W_C_prob (prob : FixedWeightProblem) (c' : ℝ) (b : ℂ) : ℂ :=
  ((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) * b *
    cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)

/-- Explicit uniform upper bound `‖W_C_prob prob c' b‖ ≤ C_W * c'^{-1/6} e^{c' Re L(b)}`
on `closedBall ξ_* P.r_1` from `(P2)` (since `(2b)^{w-1}` is bounded by `(3 ξ_*)^{w-1}`,
independent of `c'`). -/
theorem W_C_prob_norm_le {prob : FixedWeightProblem} {c' C_Q : ℝ}
    (P : PropositionPAxioms prob c')
    (hCQ : ∀ b ∈ closedBall (xiStar : ℂ) P.r_1, ‖P.Q_star b‖ ≤ C_Q)
    {b : ℂ} (hb : b ∈ closedBall (xiStar : ℂ) P.r_1) :
    let C_W_fac := (3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) * (2 / 3 : ℝ) /
      Real.sqrt (2 * π ^ 2 * xiStar / 3)
    ‖W_C_prob prob c' b‖ ≤ C_W_fac * (C_Q + P.η_V) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
  intro C_W_fac
  have hc'_pos : 0 < c' := P.hc'_pos
  have hbre := closedBall_disc_re_pos P.hr1_le hb
  have hb_re_pos : 0 < b.re := by linarith [xiStar_pos]
  have hb_norm_ge : xiStar / 2 ≤ ‖b‖ := hbre.1.trans (Complex.re_le_norm b)
  have h2b_ne : (2 * b) ^ (prob.w - 1) ≠ 0 := by
    apply pow_ne_zero
    intro h0
    have hre0 : (2 * b).re = 0 := by rw [h0, Complex.zero_re]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre0
    linarith
  have has_ne : asC ((c' : ℂ) * tipL b) ≠ 0 := asC_tipL_ne_zero hc'_pos hb_re_pos
  have hV_norm : ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)‖ ≤
      (C_Q + P.η_V) * (3 * xiStar) ^ (prob.w - 1) * ‖asC ((c' : ℂ) * tipL b)‖ := by
    have hdisc := P.p2_disc_asymp hb
    have hq_norm : ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
        ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b))‖ ≤ C_Q + P.η_V := by
      have htri : ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
          ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b))‖ ≤
          ‖P.Q_star b‖ + P.η_V := by
        have := norm_sub_norm_le
          (cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
            ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b))) (P.Q_star b)
        linarith
      linarith [hCQ b hb]
    have hmul_id : cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) =
        (cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
          ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b))) *
        ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b)) := by
      rw [div_mul_cancel₀ _ (mul_ne_zero h2b_ne has_ne)]
    rw [hmul_id, norm_mul, norm_mul]
    have h2b_le : ‖(2 * b) ^ (prob.w - 1)‖ ≤ (3 * xiStar) ^ (prob.w - 1) := by
      rw [norm_pow, norm_mul, Complex.norm_ofNat]
      exact pow_le_pow_left₀ (by positivity) (by linarith [hbre.2]) _
    calc ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) /
            ((2 * b) ^ (prob.w - 1) * asC ((c' : ℂ) * tipL b))‖ *
          (‖(2 * b) ^ (prob.w - 1)‖ * ‖asC ((c' : ℂ) * tipL b)‖)
        ≤ (C_Q + P.η_V) * ((3 * xiStar) ^ (prob.w - 1) * ‖asC ((c' : ℂ) * tipL b)‖) := by
          gcongr
          exact add_nonneg ((norm_nonneg (P.Q_star b)).trans (hCQ b hb)) P.hηV_nn
      _ = (C_Q + P.η_V) * (3 * xiStar) ^ (prob.w - 1) * ‖asC ((c' : ℂ) * tipL b)‖ := by ring
  have htre : (tipL b).re = (2 * Real.pi / 3) * b.re := by
    unfold tipL
    simp only [Complex.re_ofReal_mul]
  have hLre_pos : 0 < ((c' : ℂ) * tipL b).re := by
    rw [Complex.re_ofReal_mul, htre]
    positivity [Real.pi_pos, hb_re_pos]
  have has_ub : ‖asC ((c' : ℂ) * tipL b)‖ ≤
      Real.exp (c' * (tipL b).re) / (Real.sqrt c' * Real.sqrt (2 * π ^ 2 * xiStar / 3)) := by
    rw [norm_asC_of_re_pos hLre_pos, Complex.re_ofReal_mul]
    have hnormL : ‖(c' : ℂ) * tipL b‖ = c' * (2 * π / 3) * ‖b‖ := by
      unfold tipL
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hc'_pos.le, Real.norm_of_nonneg (by positivity [Real.pi_pos])]
      ring
    have hden_lb : Real.sqrt c' * Real.sqrt (2 * π ^ 2 * xiStar / 3) ≤ √(2 * π * ‖(c' : ℂ) * tipL b‖) := by
      rw [← Real.sqrt_mul hc'_pos.le]
      apply Real.sqrt_le_sqrt
      rw [hnormL]
      calc c' * (2 * π ^ 2 * xiStar / 3) = 2 * π * (c' * (2 * π / 3) * (xiStar / 2)) := by ring
        _ ≤ 2 * π * (c' * (2 * π / 3) * ‖b‖) := by gcongr
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity [xiStar_pos]) hden_lb
  have hc_pow : tipEps c' * (2 * c' / 3) / Real.sqrt c' = (2 / 3 : ℝ) * c' ^ (-(1 / 6 : ℝ)) := by
    unfold tipEps
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hc'_pos.le]
    calc c' ^ (-(2 / 3 : ℝ)) * (2 * c' / 3) * c' ^ (-(1 / 2 : ℝ))
        = (2 / 3 : ℝ) * ((c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ))) * c' ^ (-(1 / 2 : ℝ))) := by
          rw [Real.rpow_one]; ring
      _ = (2 / 3 : ℝ) * c' ^ (1 + -(2 / 3 : ℝ) + -(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hc'_pos, ← Real.rpow_add hc'_pos]
      _ = (2 / 3 : ℝ) * c' ^ (-(1 / 6 : ℝ)) := by norm_num
  have hV_ub2 : ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)‖ ≤
      (C_Q + P.η_V) * (3 * xiStar) ^ (prob.w - 1) *
        (Real.exp (c' * (tipL b).re) / (Real.sqrt c' * Real.sqrt (2 * π ^ 2 * xiStar / 3))) := by
    refine hV_norm.trans (mul_le_mul_of_nonneg_left has_ub ?_)
    exact mul_nonneg (add_nonneg ((norm_nonneg (P.Q_star b)).trans (hCQ b hb)) P.hηV_nn)
      (by positivity [xiStar_pos])
  unfold W_C_prob
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (tipEps_pos hc'_pos).le, Real.norm_of_nonneg (by positivity)]
  have hprod_le : tipEps c' * (2 * c' / 3) * ‖b‖ * ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)‖ ≤
      tipEps c' * (2 * c' / 3) * (3 * xiStar / 2) *
        ((C_Q + P.η_V) * (3 * xiStar) ^ (prob.w - 1) *
          (Real.exp (c' * (tipL b).re) / (Real.sqrt c' * Real.sqrt (2 * π ^ 2 * xiStar / 3)))) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hbre.2 (by positivity [tipEps_pos hc'_pos]))
      hV_ub2 (norm_nonneg _) (by positivity [tipEps_pos hc'_pos, xiStar_pos])
  calc tipEps c' * (2 * c' / 3) * ‖b‖ * ‖cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)‖
      ≤ tipEps c' * (2 * c' / 3) * (3 * xiStar / 2) *
          ((C_Q + P.η_V) * (3 * xiStar) ^ (prob.w - 1) *
            (Real.exp (c' * (tipL b).re) / (Real.sqrt c' * Real.sqrt (2 * π ^ 2 * xiStar / 3)))) := hprod_le
    _ = (3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) / Real.sqrt (2 * π ^ 2 * xiStar / 3) *
          (tipEps c' * (2 * c' / 3) / Real.sqrt c') * (C_Q + P.η_V) * Real.exp (c' * (tipL b).re) := by
        ring
    _ = C_W_fac * (C_Q + P.η_V) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
        rw [hc_pow]; dsimp [C_W_fac]; ring

/-! ### Section 3: Transported test density `psiTilde`, `deltaLobe`, `chartUT`, holomorphy & ℝ-identities -/

/-- Open neighborhood of `closedBall 0 (chartAC r_1 c'^2)` on which `psiTilde prob c' g` is analytic. -/
noncomputable def psiDom (c' : ℝ) : Set ℂ :=
  {u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) | |(virasoroBChart c' u).im| < 1 / 2}

lemma psiDom_isOpen {c' : ℝ} (hc' : 0 < c') : IsOpen (psiDom c') := by
  have hcont : ContinuousOn (fun u => |(virasoroBChart c' u).im|)
      (ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ))) :=
    (Complex.continuous_im.comp_continuousOn
      (virasoroBChart_analyticOnNhd hc').continuousOn).abs
  rw [psiDom]
  exact hcont.isOpen_inter_preimage isOpen_ball isOpen_Iio

lemma closedBall_chartAC_subset_psiDom {r_1 c' : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c') :
    closedBall (0 : ℂ) (chartAC r_1 c' ^ 2) ⊆ psiDom c' := by
  intro u hu
  have hu_vir := chart_mem_virasoroClosedBall hr1 hc' hu
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall_zero_iff] at hu_vir
    rw [mem_ball_zero_iff]
    exact hu_vir.trans_lt (virasoroAC_sq_lt_domain hc')
  · have hb := virasoro_deltaChart_b_min hc' hu_vir
    have him : |(virasoroBChart c' u).im| ≤ 0.05 := by
      have h1 : |(virasoroBChart c' u - (xiStar : ℂ)).im| ≤ ‖virasoroBChart c' u - (xiStar : ℂ)‖ :=
        Complex.abs_im_le_norm _
      have h2 : (virasoroBChart c' u - (xiStar : ℂ)).im = (virasoroBChart c' u).im := by
        simp [Complex.sub_im]
      rw [h2] at h1
      exact h1.trans (hb.trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith

/-- Rescaled general-`(w, Q)` test density (`lower_o1_two_edge.tex`, `ft:PP` / `wone:Q`):
`Ψ̃(u) := -(M[g])⁻¹ G(b(u)) V(Δ(u)) Δ'(u)`. -/
noncomputable def psiTilde (prob : FixedWeightProblem) (c' : ℝ) (g : ℝ → ℝ) (u : ℂ) : ℂ :=
  -((prob.cardyNorm (c' / 12) g : ℂ)⁻¹) *
    hankelContinuationW prob.w c' g (virasoroBChart c' u) *
    cardyVC prob (c' / 12) (virasoroDeltaChartC c' u) *
    deriv (virasoroDeltaChartC c') u

/-- Far-lobe normalized mass `δ_lobe := M[g]⁻¹ ∫_0^{Δ(A_{c'}(r₁)^2)} |g| V dt` (`wone:Q`). -/
noncomputable def deltaLobe (prob : FixedWeightProblem) (r_1 c' : ℝ) (g : ℝ → ℝ) : ℝ :=
  (prob.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC r_1 c' ^ 2)),
      |g t| * prob.cardyV (c' / 12) t

/-- Chart image of the sign-change threshold `u_T := u_{c'}(T / c')` (`wone:Q`). -/
noncomputable def chartUT (c' T : ℝ) : ℝ :=
  virasoroUChart c' (T / c')

/-- **Proposition P `(H2-hol)`**: `psiTilde prob c' g` is analytic on `psiDom c'`
(containing `closedBall 0 (chartAC r₁ c'^2)`). Notice this holds whenever `c₀ ≤ c'`, where
`c₀` comes from `WeightAxioms.differentiableOn_hankelContinuationW prob`. -/
theorem psiTilde_analyticOnNhd (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
        AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c') := by
  obtain ⟨c₀, hc₀_ge, hdiff⟩ := WeightAxioms.differentiableOn_hankelContinuationW prob
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le zero_lt_one ((le_max_left (1 : ℝ) (24 * prob.totalShift)).trans hc₀_ge)
  refine ⟨c₀, hc₀_pos, fun {c'} hc' {g} hg u hu => ?_⟩
  have hc'_pos : 0 < c' := hc₀_pos.trans_le hc'
  have hu_ball : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) := hu.1
  have hu_im : |(virasoroBChart c' u).im| < 1 / 2 := hu.2
  have hb_an : AnalyticAt ℂ (virasoroBChart c') u := virasoroBChart_analyticOnNhd hc'_pos u hu_ball
  have hΔ_an : AnalyticAt ℂ (virasoroDeltaChartC c') u :=
    virasoroDeltaChartC_analyticOnNhd hc'_pos u hu_ball
  have hstrip_open : IsOpen {b : ℂ | |b.im| < 1 / 2} :=
    isOpen_lt Complex.continuous_im.abs continuous_const
  have hG_an : AnalyticAt ℂ (fun z => hankelContinuationW prob.w c' g (virasoroBChart c' z)) u :=
    (((hdiff hc' hg).analyticOnNhd hstrip_open) _ hu_im).comp_of_eq hb_an rfl
  have hV_an : AnalyticAt ℂ (fun z => cardyVC prob (c' / 12) (virasoroDeltaChartC c' z)) u :=
    ((cardyVC_entire prob (c' / 12)).analyticAt _).comp_of_eq hΔ_an rfl
  have hdΔ_an : AnalyticAt ℂ (deriv (virasoroDeltaChartC c')) u :=
    (virasoroDeltaChartC_analyticOnNhd hc'_pos).deriv u hu_ball
  exact (((analyticAt_const.mul hG_an).mul hV_an).mul hdΔ_an)

private lemma virasoroDeltaChartC_real_deriv_eq {c' u : ℝ} (hc' : 0 < c')
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

/-- Exact real-axis formula for `psiTilde prob c' g (u : ℂ)` on `|u| ≤ virasoroAC c'^2`. -/
lemma psiTilde_ofReal (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    let M := prob.cardyNorm (c' / 12) g
    let t := virasoroDeltaChart c' u
    psiTilde prob c' g (u : ℂ) =
      ((-(M⁻¹ * g t * prob.cardyV (c' / 12) t *
        deriv (virasoroDeltaChart c') u) : ℝ) : ℂ) := by
  have hb := virasoroBChart_ofReal hc' hu
  have hΔ : virasoroDeltaChartC c' (u : ℂ) = (virasoroDeltaChart c' u : ℂ) :=
    virasoroDeltaChartC_ofReal hc' hu
  have hdΔ := virasoroDeltaChartC_real_deriv_eq hc' hu
  have hG : hankelContinuationW prob.w c' g (virasoroBChart c' (u : ℂ)) =
      (g (virasoroDeltaChart c' u) : ℂ) := by
    rw [hb.2.2.1, WeightAxioms.hankelContinuationW_ofReal prob.hw hc' hg.cont hg.int_lift hg.fourier_odd]
    congr 2
    have hnn : 0 ≤ 3 * virasoroDeltaChart c' u / c' := by positivity [virasoroDeltaChart_pos hc' hu]
    rw [Real.sq_sqrt hnn]
    field_simp [hc'.ne']
  have hV : cardyVC prob (c' / 12) (virasoroDeltaChartC c' (u : ℂ)) =
      (prob.cardyV (c' / 12) (virasoroDeltaChart c' u) : ℂ) := by
    rw [hΔ, cardyVC_ofReal]
  unfold psiTilde
  rw [hG, hV, hdΔ]
  push_cast
  ring

lemma psiTilde_im_ofReal (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    (psiTilde prob c' g (u : ℂ)).im = 0 := by
  rw [psiTilde_ofReal prob hc' hg hu, Complex.ofReal_im]

lemma psiTilde_re_ofReal (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    (psiTilde prob c' g (u : ℂ)).re =
      (prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        (g (virasoroDeltaChart c' u) * prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) := by
  rw [psiTilde_ofReal prob hc' hg hu, Complex.ofReal_re]
  ring

lemma psiTilde_norm_ofReal (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 < c')
    (hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t) {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    {u : ℝ} (hu : |u| ≤ virasoroAC c' ^ 2) :
    ‖psiTilde prob c' g (u : ℂ)‖ =
      (-(deriv (virasoroDeltaChart c') u)) *
        ((prob.cardyNorm (c' / 12) g)⁻¹ * |g (virasoroDeltaChart c' u)| *
          prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) := by
  have hV_nn : 0 ≤ prob.cardyV (c' / 12) (virasoroDeltaChart c' u) :=
    hV_nonneg (virasoroDeltaChart_pos hc' hu).le
  have hder_le := virasoroDeltaChart_deriv_le hc' (abs_le.mp hu)
  have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc' _
  have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
    have := mul_pos (half_pos cStar_pos) hc13_pos; linarith
  rw [psiTilde_ofReal prob hc' hg hu, Complex.norm_real, Real.norm_eq_abs]
  rw [show -((prob.cardyNorm (c' / 12) g)⁻¹ * g (virasoroDeltaChart c' u) *
        prob.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u) =
      (-(deriv (virasoroDeltaChart c') u)) *
        ((prob.cardyNorm (c' / 12) g)⁻¹ * g (virasoroDeltaChart c' u) *
        prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) by ring]
  rw [abs_mul, abs_of_pos hnd_pos, abs_mul, abs_mul, abs_inv,
    abs_of_pos hM_pos, abs_of_nonneg hV_nn]

/-! ### Section 4: Proposition P Step 2 (type-(II) envelope at general `(w, Q)`) -/

/-- Type-(II) log-correction factor `C₁(p_e) = (p_e + 1/2) (2 / (0.3 π)) (3 / (2 √q)) C_tip_hi`
in `ς_{c'} = C₁ c'^{-1/3} log c'`. -/
noncomputable def generalEnvC1 (p_e : ℝ) : ℝ :=
  (p_e + 1 / 2 : ℝ) * (2 / (0.3 * π)) * (3 / (2 * √slitQ)) * virasoroCTipHi

/-- Exponential cut-margin rate `ς_{c'} := generalEnvC1 p_e * c'^{-1/3} * log c'`. -/
noncomputable def generalSigma (p_e c' : ℝ) : ℝ :=
  generalEnvC1 p_e * c' ^ (-(1 / 3 : ℝ)) * Real.log c'

lemma generalEnvC1_pos {p_e : ℝ} (hp_e : 0 ≤ p_e) : 0 < generalEnvC1 p_e := by
  unfold generalEnvC1
  have := slitQ_pos
  have := virasoroCTipHi_pos
  positivity

lemma generalSigma_nonneg {p_e c' : ℝ} (hp_e : 0 ≤ p_e) (hc' : 1 ≤ c') :
    0 ≤ generalSigma p_e c' := by
  unfold generalSigma
  exact mul_nonneg (mul_nonneg (generalEnvC1_pos hp_e).le (Real.rpow_nonneg (by linarith) _))
    (Real.log_nonneg hc')

lemma generalSigma_tendsto_zero (p_e : ℝ) :
    Tendsto (generalSigma p_e) atTop (𝓝 0) := by
  have hlog : Tendsto (fun c' : ℝ => Real.log c' / c' ^ (1 / 3 : ℝ)) atTop (𝓝 0) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3) |>.tendsto_div_nhds_zero
  have hmul : Tendsto (fun c' : ℝ => generalEnvC1 p_e * (Real.log c' / c' ^ (1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlog.const_mul (generalEnvC1 p_e)
  refine hmul.congr' ((eventually_gt_atTop (0 : ℝ)).mono fun c' hc' => ?_)
  unfold generalSigma
  rw [Real.rpow_neg hc'.le, div_eq_mul_inv]
  ring

/-- **Proposition P Step 2** (`lower_o1_two_edge.tex`, `ft:PP` / `wone:Q` part (2)) at general
`(w, Q)`: from `UniformPropositionPData prob`, there exist `c_env ≥ D.c₀` and `C₀ > 0` such that
for all `c' ≥ c_env`, `g ∈ TestClass prob (c' / 12)` with `M[g] > 0`, and
`u ∈ closedBall 0 (chartAC D.r_1 c' ^ 2) \ (-∞, 0]`,
`‖psiTilde prob c' g u‖ ≤ C₀ * airyEnv u * exp(generalSigma D.p_e c' * Re(u^{1/2})) * ‖u‖^{-1/2} * (Re(u^{1/2}))^{-1}`. -/
theorem psiTilde_typeII_envelope_general {prob : FixedWeightProblem}
    (D : UniformPropositionPData prob) :
    ∃ c_env C₀ : ℝ, D.c₀ ≤ c_env ∧ 0 < C₀ ∧
      ∀ {c' : ℝ}, c_env ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
        0 < prob.cardyNorm (c' / 12) g →
        ∀ {u : ℂ}, u ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
          ‖psiTilde prob c' g u‖ ≤
            C₀ * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
              ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
  obtain ⟨c_Kw_cx, C_Klo, hcKw8, _hCKlo, hPJ_cx⟩ := stripPoissonJensen_complex_general prob
  let P₀ := D.pAt (le_rfl : D.c₀ ≤ D.c₀)
  obtain ⟨c_Q_disc, C_Q_disc, hcQ_pos, hCQ_le, hCQ_disc⟩ := disc_Q_bounds D.hr1_pos.le D.hr1_le (Q_star := D.Q_star)
    (by rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]; exact P₀.p2_Q_holo)
    (fun {b} hb => by
      rw [← D.uniform_Q_star (le_rfl : D.c₀ ≤ D.c₀)]
      exact P₀.p2_Q_ne_zero (by rwa [D.uniform_r_1 (le_rfl : D.c₀ ≤ D.c₀)]))
  have hCQ_pos : 0 < C_Q_disc := hcQ_pos.trans_le hCQ_le
  let C_W_fac : ℝ := (3 * xiStar / 2) * (3 * xiStar) ^ (prob.w - 1) * (2 / 3 : ℝ) /
    Real.sqrt (2 * π ^ 2 * xiStar / 3)
  let C_W_hi : ℝ := C_W_fac * (C_Q_disc + D.η_V_max)
  have hCW_hi_pos : 0 < C_W_hi := by
    have hxi := xiStar_pos
    have hCQ_sum : 0 < C_Q_disc + D.η_V_max := add_pos_of_pos_of_nonneg hCQ_pos D.hηV_max_nn
    dsimp [C_W_hi, C_W_fac]
    positivity
  let C_U : ℝ := |majorantU0| + (4 * π / 3) * (Real.log 12 / (2 * π) + 2) ^ 2
  let C_PJ_bound : ℝ := pjConstOf D.C_e D.c_band C_Klo C_U
  let C₀ : ℝ := C_W_hi * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_bound) *
    virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ((2 / xiStar) * chartParams.C_dxi)
  have hC₀_pos : 0 < C₀ := by
    have := slitQ_pos
    have := virasoroCTipLo_pos
    have := xiStar_pos
    have := chartParams.hCdxi_pos
    dsimp [C₀]
    positivity
  refine ⟨max D.c₀ c_Kw_cx, C₀, le_max_left _ _, hC₀_pos,
    fun {c'} hc' {g} hg hM_pos {u} hu hcut => ?_⟩
  have hc'_c₀ : D.c₀ ≤ c' := (le_max_left _ _).trans hc'
  have hc'_PJ : c_Kw_cx ≤ c' := (le_max_right _ _).trans hc'
  have hc'_gt1 : 1 < c' := lt_of_lt_of_le (by linarith [hcKw8]) hc'_PJ
  have hc'_pos : 0 < c' := zero_lt_one.trans hc'_gt1
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hu_vir : u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2) :=
    chart_mem_virasoroClosedBall D.hr1_pos hc'_pos hu
  have hu_re_pos : 0 < (u ^ (1 / 2 : ℂ)).re := by
    by_contra hle
    have hre0 : (u ^ (1 / 2 : ℂ)).re = 0 := le_antisymm (not_lt.mp hle) (cpow_half_re_nonneg u)
    have him_u : u.im = 2 * (u ^ (1 / 2 : ℂ)).re * (u ^ (1 / 2 : ℂ)).im := (airySqrtRe_mul_im u).symm
    have hre_u : u.re = (u ^ (1 / 2 : ℂ)).re ^ 2 - (u ^ (1 / 2 : ℂ)).im ^ 2 := (airySqrtRe_sq_sub u).symm
    rw [hre0] at him_u hre_u
    exact hcut ⟨by linarith, by nlinarith [sq_nonneg (u ^ (1 / 2 : ℂ)).im]⟩
  have hu_ne : u ≠ 0 := fun h0 => hcut (by simp [h0])
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  by_cases hPsi0 : psiTilde prob c' g u = 0
  · rw [hPsi0, norm_zero]
    have := airyEnv_pos u
    positivity
  set P := D.pAt hc'_c₀
  set M := prob.cardyNorm (c' / 12) g
  set b := virasoroBChart c' u
  set ζ : ℂ := ((tipEps c')⁻¹ : ℝ) * (b - (xiStar : ℂ))
  have hb_eq : bScale c' ζ = b := by
    unfold bScale ζ
    have h1 : ((tipEps c' : ℝ) : ℂ) * (((tipEps c')⁻¹ : ℝ) : ℂ) = 1 := by
      push_cast; exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hε_pos.ne')
    calc (xiStar : ℂ) + ((tipEps c' : ℝ) : ℂ) * ((((tipEps c')⁻¹ : ℝ) : ℂ) * (b - (xiStar : ℂ)))
        = (xiStar : ℂ) + (((tipEps c' : ℝ) : ℂ) * (((tipEps c')⁻¹ : ℝ) : ℂ)) * (b - (xiStar : ℂ)) := by ring
      _ = b := by rw [h1, one_mul]; ring
  have hεζ_eq : tipEps c' * ‖ζ‖ = ‖b - (xiStar : ℂ)‖ := by
    dsimp [ζ]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hε_pos.le)]
    field_simp [hε_pos.ne']
  have htip_cap := virasoro_deltaChart_tip_cap hc'_pos hu_vir
  have hεζ_1 : tipEps c' * ‖ζ‖ ≤ chartParams.ρ₁_tip := by
    rw [hεζ_eq]; exact htip_cap.trans (min_le_left _ _)
  have hεζ_T1 : tipEps c' * ‖ζ‖ ≤ 1 / (4 * (chartParams.C_T1_tip + 1) ^ 2) := by
    rw [hεζ_eq]; exact htip_cap.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcomp := virasoro_tip_comparability hc'_pos hu_vir hcut
  have hζ_cut : ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) := by
    intro h0
    have hre_z : ((-ζ) ^ (1 / 2 : ℂ)).re = 0 := by
      have hneg_im : (-ζ).im = 0 := by simp [h0.1]
      have hneg_re : (-ζ).re ≤ 0 := by simp [h0.2]
      by_cases hzero : -ζ = 0
      · rw [hzero, Complex.zero_cpow (by norm_num)]; simp
      · have harg : (-ζ).arg = π := Complex.arg_eq_pi_iff.mpr ⟨by
          have : (-ζ).re ≠ 0 := fun h => hzero (Complex.ext h hneg_im)
          exact lt_of_le_of_ne hneg_re this, hneg_im⟩
        rw [Complex.cpow_def_of_ne_zero hzero, Complex.exp_re]
        have him : (Complex.log (-ζ) * (1 / 2 : ℂ)).im = π / 2 := by
          simp [Complex.log_im, harg]; ring
        rw [him, Real.cos_pi_div_two, mul_zero]
    have hpos_rhs : 0 < chartParams.c_tip_lo * (u ^ (1 / 2 : ℂ)).re :=
      mul_pos chartParams.hc_tip_lo_pos hu_re_pos
    linarith [hcomp.1]
  have hu_open : u ∈ ball (0 : ℂ) (virasoroRUInf * c' ^ (2 / 3 : ℝ)) :=
    (closedBall_chartAC_subset_psiDom D.hr1_pos hc'_pos hu).1
  have hfac : psiTilde prob c' g u =
      -((M : ℂ)⁻¹) * hankelContinuationW prob.w c' g b * W_C_prob prob c' b *
        (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)) := by
    unfold psiTilde W_C_prob
    have hΔsq : virasoroDeltaChartC c' u = (c' : ℂ) * b ^ 2 / 3 := by
      have hb2 : b ^ 2 = 3 * virasoroXiChartC c' u := by
        dsimp [b]; unfold virasoroBChart virasoroBOfXi; exact cpow_half_sq _
      unfold virasoroDeltaChartC
      rw [hb2]
      have h3 : (3 : ℂ) ≠ 0 := by norm_num
      field_simp [h3]
    rw [hΔsq, deriv_virasoroDeltaChartC_eq_bChart hc'_pos hu_open]
    have hε_ne : ((tipEps c' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε_pos.ne'
    change -((M : ℂ)⁻¹) * hankelContinuationW prob.w c' g b *
        cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) *
        (((2 * c' / 3 : ℝ) : ℂ) * b * deriv (virasoroBChart c') u) =
      -((M : ℂ)⁻¹) * hankelContinuationW prob.w c' g b *
        (((tipEps c' : ℝ) : ℂ) * ((2 * c' / 3 : ℝ) : ℂ) * b *
          cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3)) *
        (deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ))
    field_simp [hε_ne]
  have hG_ne : hankelContinuationW prob.w c' g b ≠ 0 := by
    intro h0; apply hPsi0; rw [hfac, h0]; ring
  have hW_ne : W_C_prob prob c' b ≠ 0 := by
    intro h0; apply hPsi0; rw [hfac, h0]; ring
  have hb_im : |b.im| < 1 / 2 := (closedBall_chartAC_subset_psiDom D.hr1_pos hc'_pos hu).2
  -- Lemma T1 gives `z_b`
  obtain ⟨_, hz_im_pos, hz_cl, hz_map, _, hz_im_bd, _, hz_prod_bd⟩ :=
    virasoro_lemma_T1 hc'_pos hζ_cut hεζ_1
  set v : ℂ := I * ((√(tipEps c') : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
  set z_b : ℂ := (sigmaStar : ℂ) + chartParams.ψ_tip v
  have hCT1_sqrt : chartParams.C_T1_tip * Real.sqrt (tipEps c' * ‖ζ‖) ≤ 1 / 2 := by
    have hsqrt_le : Real.sqrt (tipEps c' * ‖ζ‖) ≤ 1 / (2 * (chartParams.C_T1_tip + 1)) := by
      have h1 : 1 / (4 * (chartParams.C_T1_tip + 1) ^ 2) =
          (1 / (2 * (chartParams.C_T1_tip + 1))) ^ 2 := by
        have hp : chartParams.C_T1_tip + 1 ≠ 0 := by linarith [chartParams.hCT1_tip_nn]
        field_simp [hp]; ring
      calc Real.sqrt (tipEps c' * ‖ζ‖) ≤ Real.sqrt ((1 / (2 * (chartParams.C_T1_tip + 1))) ^ 2) :=
            Real.sqrt_le_sqrt (h1 ▸ hεζ_T1)
        _ = 1 / (2 * (chartParams.C_T1_tip + 1)) :=
            Real.sqrt_sq (div_nonneg zero_le_one (by linarith [chartParams.hCT1_tip_nn]))
    calc chartParams.C_T1_tip * Real.sqrt (tipEps c' * ‖ζ‖)
        ≤ chartParams.C_T1_tip * (1 / (2 * (chartParams.C_T1_tip + 1))) :=
          mul_le_mul_of_nonneg_left hsqrt_le chartParams.hCT1_tip_nn
      _ = (chartParams.C_T1_tip / (chartParams.C_T1_tip + 1)) * (1 / 2) := by
          have hp : chartParams.C_T1_tip + 1 ≠ 0 := by linarith [chartParams.hCT1_tip_nn]
          field_simp [hp]
      _ ≤ 1 * (1 / 2) := by
          gcongr; exact (div_le_one (by linarith [chartParams.hCT1_tip_nn])).mpr (by linarith)
      _ = 1 / 2 := one_mul _
  have hd_pos : 0 < tipDist ζ := tipDist_pos_of_not_nonneg hζ_cut
  have hprod_lb : (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) ≤
      z_b.im * ‖z_b - (sigmaStar : ℂ)‖ := by
    have hbase_nn : 0 ≤ (tipEps c' / slitQ) * tipDist ζ :=
      mul_nonneg (div_nonneg hε_pos.le slitQ_pos.le) hd_pos.le
    have h1 := (abs_le.mp hz_prod_bd).1
    have h2 := mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    linarith
  have hy_ub : z_b.im ≤ (3 / (2 * √slitQ)) * virasoroCTipHi * c' ^ (-(1 / 3 : ℝ)) *
      (u ^ (1 / 2 : ℂ)).re := by
    have hzeta_re_nn : 0 ≤ ((-ζ) ^ (1 / 2 : ℂ)).re := cpow_half_re_nonneg (-ζ)
    have hbase_nn : 0 ≤ Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re :=
      mul_nonneg (Real.sqrt_nonneg _) hzeta_re_nn
    have h1 := (abs_le.mp hz_im_bd).2
    have h2 := mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    have hsqrt_eps : Real.sqrt (tipEps c' / slitQ) = c' ^ (-(1 / 3 : ℝ)) / √slitQ := by
      unfold tipEps
      rw [Real.sqrt_div (Real.rpow_nonneg hc'_pos.le _), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hc'_pos.le]
      norm_num
    have hre_hi : ((-ζ) ^ (1 / 2 : ℂ)).re ≤ virasoroCTipHi * (u ^ (1 / 2 : ℂ)).re := hcomp.2.1
    calc z_b.im ≤ (3 / 2 : ℝ) * (Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) := by
          linarith
      _ = (3 / (2 * √slitQ)) * c' ^ (-(1 / 3 : ℝ)) * ((-ζ) ^ (1 / 2 : ℂ)).re := by
          rw [hsqrt_eps]; ring
      _ ≤ (3 / (2 * √slitQ)) * c' ^ (-(1 / 3 : ℝ)) * (virasoroCTipHi * (u ^ (1 / 2 : ℂ)).re) := by
          gcongr
      _ = (3 / (2 * √slitQ)) * virasoroCTipHi * c' ^ (-(1 / 3 : ℝ)) * (u ^ (1 / 2 : ℂ)).re := by
          ring
  -- Complex PJ + Lemma T4
  have hz_eta : (z_b.re : ℂ) + (z_b.im : ℂ) * I = z_b := Complex.re_add_im z_b
  have hT4 := lemma_T4 hz_im_pos (by rw [hz_eta]; exact hz_cl)
  have hmap_b : slitBoundaryMapC z_b = b := hz_map.trans hb_eq
  have hG_PJ := hPJ_cx P hc'_PJ hg hM_pos hz_im_pos hz_cl
    (by rw [hmap_b]; exact hb_im) (by rw [hmap_b]; exact hG_ne)
  rw [hmap_b, D.uniform_C_e hc'_c₀, D.uniform_c_band hc'_c₀, D.uniform_p_e hc'_c₀] at hG_PJ
  have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'_gt1.le
  have hm_term : (D.p_e + 1 / 2 : ℝ) * (1 - slitMass z_b.re z_b.im) * Real.log c' ≤
      generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re := by
    have h1 : 1 - slitMass z_b.re z_b.im ≤
        (2 / (0.3 * π)) * ((3 / (2 * √slitQ)) * virasoroCTipHi * c' ^ (-(1 / 3 : ℝ)) *
          (u ^ (1 / 2 : ℂ)).re) :=
      hT4.1.trans (mul_le_mul_of_nonneg_left hy_ub (by positivity))
    calc (D.p_e + 1 / 2 : ℝ) * (1 - slitMass z_b.re z_b.im) * Real.log c'
        ≤ (D.p_e + 1 / 2 : ℝ) * ((2 / (0.3 * π)) * ((3 / (2 * √slitQ)) * virasoroCTipHi *
            c' ^ (-(1 / 3 : ℝ)) * (u ^ (1 / 2 : ℂ)).re)) * Real.log c' := by gcongr; positivity [D.hp_e_nn]
      _ = generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re := by
          unfold generalSigma generalEnvC1; ring
  have hS_term : slitEntropy z_b.re z_b.im ≤
      (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) +
        slitEntropyComplexConst := by
    have hz_ne_sigma : ‖z_b - (sigmaStar : ℂ)‖ ≠ 0 := by
      intro h0
      have : z_b.im * ‖z_b - (sigmaStar : ℂ)‖ = 0 := by rw [h0, mul_zero]
      have hpos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by
        positivity [slitQ_pos]
      linarith
    have hz_norm_pos : 0 < ‖z_b - (sigmaStar : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) hz_ne_sigma.symm
    have hprod_pos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by
      positivity [slitQ_pos]
    have hlog_inv : Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) ≤
        (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) := by
      have hmul_inv : Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) =
          Real.log (1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)) := by
        rw [← Real.log_mul (one_div_pos.mpr hz_im_pos).ne' (one_div_pos.mpr hz_norm_pos).ne']
        ring_nf
      have hinv_le : 1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖) ≤
          (c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ := by
        calc 1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)
            ≤ 1 / ((1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ)) :=
              one_div_le_one_div_of_le hprod_pos hprod_lb
          _ = (tipEps c')⁻¹ * (2 * slitQ) / tipDist ζ := by
              field_simp [hε_pos.ne', slitQ_pos.ne', hd_pos.ne']
          _ = (c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ := by
              unfold tipEps; rw [← Real.rpow_neg hc'_pos.le, neg_neg]
      have hlog_step : Real.log (1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)) ≤
          Real.log ((c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ) :=
        Real.log_le_log (one_div_pos.mpr (mul_pos hz_im_pos hz_norm_pos)) hinv_le
      have hlog_rhs : Real.log ((c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ) =
          (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) := by
        rw [Real.log_div (by positivity [slitQ_pos]) hd_pos.ne',
          Real.log_mul (Real.rpow_pos_of_pos hc'_pos _).ne' (by positivity [slitQ_pos]),
          Real.log_rpow hc'_pos]
      linarith
    have hS' : slitEntropy z_b.re z_b.im ≤
        Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) +
          slitEntropyComplexConst := by
      simpa [hz_eta] using hT4.2
    linarith
  -- General-w weight bound for `W_C_prob prob c' b`
  have hb_disc : b ∈ closedBall (xiStar : ℂ) P.r_1 := by
    rw [D.uniform_r_1 hc'_c₀]
    rw [mem_closedBall, dist_eq_norm]
    exact virasoroBChart_sub_xiStar_le_r1 D.hr1_pos hc'_pos hu
  have hW_raw := W_C_prob_norm_le P (C_Q := C_Q_disc) (fun b' hb' => by
    rw [D.uniform_Q_star hc'_c₀]
    exact (hCQ_disc b' (by rwa [← D.uniform_r_1 hc'_c₀])).2) hb_disc
  dsimp only at hW_raw
  have hW_ub : ‖W_C_prob prob c' b‖ ≤ C_W_hi * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
    have hη_le : P.η_V ≤ D.η_V_max := D.uniform_ηV_le hc'_c₀
    have hCWf_nn : 0 ≤ C_W_fac := by dsimp [C_W_fac]; positivity [xiStar_pos]
    calc ‖W_C_prob prob c' b‖
        ≤ C_W_fac * (C_Q_disc + P.η_V) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := hW_raw
      _ ≤ C_W_fac * (C_Q_disc + D.η_V_max) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
          gcongr
      _ = C_W_hi * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := rfl
  have hW_log : Real.log ‖W_C_prob prob c' b‖ ≤
      Real.log C_W_hi - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
    have h1 := Real.log_le_log (norm_pos_iff.mpr hW_ne) hW_ub
    have h2 : Real.log (C_W_hi * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) =
        Real.log C_W_hi - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
      rw [Real.log_mul (mul_pos hCW_hi_pos (Real.rpow_pos_of_pos hc'_pos _)).ne' (Real.exp_pos _).ne',
        Real.log_mul hCW_hi_pos.ne' (Real.rpow_pos_of_pos hc'_pos _).ne',
        Real.log_rpow hc'_pos, Real.log_exp]
      ring
    linarith
  have hpot := virasoro_chart_potential_eq hc'_pos hu_vir hcut
  have hdist_lb : Real.log (1 / tipDist ζ) ≤
      Real.log (virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
    have hlo_dist : virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re ≤ tipDist ζ :=
      hcomp.2.2.2.2
    have hlhs_pos : 0 < virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re := by
      have := virasoroCTipLo_pos; positivity
    have hinv : 1 / tipDist ζ ≤
        virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
      calc 1 / tipDist ζ
          ≤ 1 / (virasoroCTipLo ^ (3 / 2 : ℝ) * √‖u‖ * (u ^ (1 / 2 : ℂ)).re) :=
            one_div_le_one_div_of_le hlhs_pos hlo_dist
        _ = virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
            rw [Real.sqrt_eq_rpow, Real.rpow_neg virasoroCTipLo_pos.le,
              Real.rpow_neg hu_norm_pos.le]
            ring
    exact Real.log_le_log (one_div_pos.mpr hd_pos) hinv
  have hGW_ne : -((M : ℂ)⁻¹) * hankelContinuationW prob.w c' g b * W_C_prob prob c' b ≠ 0 := by
    intro h0; apply hPsi0; rw [hfac, h0, zero_mul]
  have hGW_norm_eq : ‖-((M : ℂ)⁻¹) * hankelContinuationW prob.w c' g b * W_C_prob prob c' b‖ =
      M⁻¹ * ‖hankelContinuationW prob.w c' g b‖ * ‖W_C_prob prob c' b‖ := by
    rw [norm_mul, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
  have hGW_log : Real.log ‖-((M : ℂ)⁻¹) * hankelContinuationW prob.w c' g b * W_C_prob prob c' b‖ ≤
      Real.log C_W_hi + Real.log (2 * slitQ) + slitEntropyComplexConst + C_PJ_bound +
        (-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) + generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re +
        Real.log (virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) *
          ((u ^ (1 / 2 : ℂ)).re)⁻¹) := by
    rw [hGW_norm_eq, Real.log_mul (mul_pos (inv_pos.mpr hM_pos) (norm_pos_iff.mpr hG_ne)).ne'
      (norm_pos_iff.mpr hW_ne).ne',
      Real.log_mul (inv_pos.mpr hM_pos).ne' (norm_pos_iff.mpr hG_ne).ne', Real.log_inv]
    have hlog_dist : -Real.log (tipDist ζ) = Real.log (1 / tipDist ζ) := by
      rw [Real.log_div one_ne_zero hd_pos.ne', Real.log_one, zero_sub]
    have hpot_eq : c' * majorant2D b + c' * (tipL b).re = -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
      linarith [hpot]
    have hCPJ_eq : pjConstOf D.C_e D.c_band C_Klo C_U = C_PJ_bound := rfl
    linarith [hG_PJ, hm_term, hS_term, hW_log, hdist_lb, hlog_dist, hpot_eq, hCPJ_eq]
  have hexp_GW : ‖-((M : ℂ)⁻¹) * hankelContinuationW prob.w c' g b * W_C_prob prob c' b‖ ≤
      (C_W_hi * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_bound) *
        virasoroCTipLo ^ (-(3 / 2 : ℝ))) *
        airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
        ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
    have hle := Real.exp_le_exp.mpr hGW_log
    rw [Real.exp_log (norm_pos_iff.mpr hGW_ne)] at hle
    have hpow_rhs :
        Real.exp (Real.log C_W_hi + Real.log (2 * slitQ) + slitEntropyComplexConst +
          C_PJ_bound + (-(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) +
          generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re +
          Real.log (virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) *
            ((u ^ (1 / 2 : ℂ)).re)⁻¹)) =
        (C_W_hi * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_bound) *
          virasoroCTipLo ^ (-(3 / 2 : ℝ))) *
          airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
      have hpos2 : 0 < 2 * slitQ := by positivity [slitQ_pos]
      have hpos3 : 0 < virasoroCTipLo ^ (-(3 / 2 : ℝ)) * ‖u‖ ^ (-(1 / 2 : ℝ)) *
          ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by positivity [virasoroCTipLo_pos]
      simp only [Real.exp_add, Real.exp_log hCW_hi_pos, Real.exp_log hpos2, Real.exp_log hpos3, airyEnv]
      ring
    linarith
  have hder_bd : ‖deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)‖ ≤
      (2 / xiStar) * chartParams.C_dxi :=
    virasoroBChart_deriv_norm_le hc'_pos hu_vir
  calc ‖psiTilde prob c' g u‖
      = ‖-((M : ℂ)⁻¹) * hankelContinuationW prob.w c' g b * W_C_prob prob c' b‖ *
          ‖deriv (virasoroBChart c') u / ((tipEps c' : ℝ) : ℂ)‖ := by
        rw [hfac, norm_mul]
    _ ≤ ((C_W_hi * (2 * slitQ) * Real.exp (slitEntropyComplexConst + C_PJ_bound) *
            virasoroCTipLo ^ (-(3 / 2 : ℝ))) *
            airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
            ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) *
          ((2 / xiStar) * chartParams.C_dxi) :=
        mul_le_mul hexp_GW hder_bd (norm_nonneg _)
          (by have := slitQ_pos; have := virasoroCTipLo_pos; have := airyEnv_pos u; positivity)
    _ = C₀ * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
          ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
        dsimp [C₀]; ring

/-! ### Section 5: Proposition P Step 3 (far-lobe decay) and Lemma Q (1)–(3) -/

private lemma cardyNorm_pos_of_nonzero_P (prob : FixedWeightProblem) {c' : ℝ}
    (P : PropositionPAxioms prob c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hnonzero : ∃ t ≥ 0, g t ≠ 0) :
    0 < prob.cardyNorm (c' / 12) g := by
  unfold FixedWeightProblem.cardyNorm
  have hint : IntegrableOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Ioi 0) := hg.int_cardy
  have hcont : ContinuousOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Ioi 0) :=
    (hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono Ioi_subset_Ici_self
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ |g t| * prob.cardyV (c' / 12) t := fun t ht =>
    mul_nonneg (abs_nonneg _) (P.p1_pos (mem_Ioi.mp ht)).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi hnonneg) hint]
  obtain ⟨t₀, ht₀, hgt₀⟩ := hnonzero
  have hmem_t₀ : t₀ ∈ Ici (0 : ℝ) := ht₀
  have hcont_t₀ : ContinuousWithinAt g (Ici 0) t₀ := hg.cont.continuousWithinAt hmem_t₀
  obtain ⟨r, hr_pos, hr_ne⟩ := Metric.continuousWithinAt_iff.mp hcont_t₀ (|g t₀| / 2)
    (by positivity [abs_pos.mpr hgt₀])
  let t₁ : ℝ := t₀ + r / 2
  have ht₁_pos : 0 < t₁ := by dsimp [t₁]; linarith
  have ht₁_mem : t₁ ∈ Ici (0 : ℝ) := ht₁_pos.le
  have ht₁_dist : dist t₁ t₀ < r := by
    dsimp [t₁]
    rw [Real.dist_eq, show t₀ + r / 2 - t₀ = r / 2 by ring, abs_of_pos (half_pos hr_pos)]
    linarith
  have hgt₁ : g t₁ ≠ 0 := by
    have hlt := hr_ne ht₁_mem ht₁_dist
    rw [Real.dist_eq] at hlt
    intro h0
    rw [h0, zero_sub, abs_neg] at hlt
    linarith [abs_pos.mpr hgt₀]
  have hV_pos : 0 < prob.cardyV (c' / 12) t₁ := P.p1_pos ht₁_pos
  have hf_pos : 0 < |g t₁| * prob.cardyV (c' / 12) t₁ := mul_pos (abs_pos.mpr hgt₁) hV_pos
  have hsupp_nonempty : ∃ δ > 0, Ioo (t₁ - δ) (t₁ + δ) ⊆
      Function.support (fun t => |g t| * prob.cardyV (c' / 12) t) ∩ Ioi 0 := by
    have hcont_at : ContinuousAt (fun t => |g t| * prob.cardyV (c' / 12) t) t₁ :=
      hcont.continuousAt (Ioi_mem_nhds ht₁_pos)
    obtain ⟨ε, hε_pos, hε⟩ := Metric.continuousAt_iff.mp hcont_at
      (|g t₁| * prob.cardyV (c' / 12) t₁ / 2) (half_pos hf_pos)
    refine ⟨min ε (t₁ / 2), lt_min hε_pos (half_pos ht₁_pos), fun t ht => ?_⟩
    have hmem : t ∈ Ioo (t₁ - ε) (t₁ + ε) := ⟨by linarith [ht.1, min_le_left ε (t₁ / 2)],
      by linarith [ht.2, min_le_left ε (t₁ / 2)]⟩
    have ht_pos : 0 < t := by linarith [ht.1, min_le_right ε (t₁ / 2)]
    have hdist : dist t t₁ < ε := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    have hne : |g t| * prob.cardyV (c' / 12) t ≠ 0 := by
      have h1 := hε hdist
      rw [Real.dist_eq] at h1
      intro h0
      rw [h0, zero_sub, abs_neg, abs_of_pos hf_pos] at h1
      linarith
    exact ⟨hne, ht_pos⟩
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hsupp_nonempty
  have hvol_pos : 0 < volume (Ioo (t₁ - δ) (t₁ + δ)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  exact lt_of_lt_of_le hvol_pos (measure_mono hδ_sub)

/-- **Proposition P Step 3** (`lower_o1_two_edge.tex`, `ft:PP` and `wone:Q` part (1)):
far-lobe normalized mass `deltaLobe prob D.r_1 c' g` decays exponentially as `c' → ∞`,
forcing `virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) < T` for any weakly feasible test. -/
theorem deltaLobe_gap_general {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c_gap C_gap κ_gap : ℝ, D.c₀ ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      (∀ {c' : ℝ}, c_gap ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
        0 < prob.cardyNorm (c' / 12) g →
          deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c')) ∧
      ∀ {c' T : ℝ} {g : ℝ → ℝ}, c_gap ≤ c' →
        prob.IsWeaklyFeasible (c' / 12) T g →
          0 < prob.cardyNorm (c' / 12) g ∧
          deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
          deltaLobe prob D.r_1 c' g < 1 / 2 ∧
          virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) < T := by
  let x_end : ℝ := Real.sqrt (3 * virasoroDeltaChart 1 (2 * chartBV D.r_1 ^ 2) / 1)
  have hb_end := virasoroBChart_ofReal one_pos (u := 2 * chartBV D.r_1 ^ 2)
    (by
      rw [abs_of_nonneg (by positivity)]
      have hle := chartAC_sq_le_virasoroAC_sq D.hr1_pos zero_le_one
      rwa [chartAC_sq _ 1 zero_le_one, Real.one_rpow, mul_one] at hle)
  let x_cap : ℝ := (virasoroBChart 1 (2 * chartBV D.r_1 ^ 2 : ℝ)).re
  have hx_cap_gt0 : 0 < x_cap := hb_end.2.1
  have hx_cap_lt_xi : x_cap < xiStar := by
    have hb_min := virasoro_deltaChart_b_min one_pos (u := (2 * chartBV D.r_1 ^ 2 : ℝ))
      (by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hle := chartAC_sq_le_virasoroAC_sq D.hr1_pos zero_le_one
        rwa [chartAC_sq _ 1 zero_le_one, Real.one_rpow, mul_one] at hle)
    have hre : x_cap < xiStar := by
      have h05 : ‖virasoroBChart 1 (2 * chartBV D.r_1 ^ 2 : ℝ) - (xiStar : ℂ)‖ ≤ 0.05 :=
        hb_min.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hneg : virasoroDeltaChart 1 (2 * chartBV D.r_1 ^ 2) < xiBar * 1 := by
        have hA2_1 : 2 * chartBV D.r_1 ^ 2 ≤ virasoroAC 1 ^ 2 := by
          have hle := chartAC_sq_le_virasoroAC_sq D.hr1_pos zero_le_one
          rw [chartAC_sq _ 1 zero_le_one, Real.one_rpow, mul_one] at hle
          exact hle
        have h1 := virasoroDeltaChart_strictAnti one_pos
          (Set.mem_Icc.mpr ⟨neg_nonpos.mpr (sq_nonneg _), sq_nonneg _⟩)
          (Set.mem_Icc.mpr ⟨by linarith [sq_nonneg (virasoroAC 1), sq_nonneg (chartBV D.r_1)], hA2_1⟩)
          (mul_pos two_pos (sq_pos_of_pos (chartBV_pos D.hr1_pos)))
        rw [virasoroDeltaChart_zero] at h1
        exact h1
      have hsq : x_cap ^ 2 < xiStar ^ 2 := by
        have h2 := hb_end.2.2.2
        rw [show ((1 : ℝ) : ℂ) * virasoroBChart 1 (2 * chartBV D.r_1 ^ 2 : ℝ) ^ 2 / 3 =
          ((x_cap ^ 2 / 3 : ℝ) : ℂ) from by
            have him : (virasoroBChart 1 (2 * chartBV D.r_1 ^ 2 : ℝ)).im = 0 := hb_end.1
            have : virasoroBChart 1 (2 * chartBV D.r_1 ^ 2 : ℝ) = (x_cap : ℂ) := Complex.ext rfl him
            rw [this]; push_cast; ring] at h2
        have hre_eq := congrArg Complex.re h2
        simp only [Complex.ofReal_re] at hre_eq
        unfold xiBar at hneg
        linarith
      nlinarith [hx_cap_gt0, xiStar_pos]
    exact hre
  let δ : ℝ := xiStar - x_cap
  have hδ0 : 0 < δ := sub_pos.mpr hx_cap_lt_xi
  have hδ1 : δ < xiStar := by dsimp [δ]; linarith
  obtain ⟨c_deep, C_gap, κ_gap, hc_deep1, hC_pos, hκ_pos, hdeep⟩ := D.lemmaG hδ0 hδ1
  let c_gap : ℝ := max D.c₀ (max c_deep ((Real.log (2 * C_gap) + 1) / κ_gap))
  have hΔ_eq : ∀ {c' : ℝ}, 0 < c' →
      virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) = c' * x_cap ^ 2 / 3 := by
    intro c' hc'_pos
    unfold virasoroDeltaChart virasoroXiChartC
    have hm_r : chartAC D.r_1 c' ^ 2 * c' ^ (-(2 / 3 : ℝ)) = 2 * chartBV D.r_1 ^ 2 := by
      rw [chartAC_sq D.r_1 c' hc'_pos.le, mul_assoc, ← Real.rpow_add hc'_pos, add_neg_cancel,
        Real.rpow_zero, mul_one]
    have hmul : ((chartAC D.r_1 c' ^ 2 : ℝ) : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
        ((2 * chartBV D.r_1 ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hm_r]
    have h1 : (virasoroXiInf (((2 * chartBV D.r_1 ^ 2 : ℝ) : ℂ))).re =
        virasoroDeltaChart 1 (2 * chartBV D.r_1 ^ 2) := by
      unfold virasoroDeltaChart virasoroXiChartC
      simp
    rw [hmul, h1]
    have h2 := hb_end.2.2.2
    have hcap : virasoroBChart 1 (2 * chartBV D.r_1 ^ 2 : ℝ) = (x_cap : ℂ) := Complex.ext rfl hb_end.1
    have hxsq : ((x_cap ^ 2 / 3 : ℝ) : ℂ) =
        ((1 : ℝ) : ℂ) * virasoroBChart 1 (2 * chartBV D.r_1 ^ 2 : ℝ) ^ 2 / 3 := by
      rw [hcap]; push_cast; ring
    have hre_eq := congrArg Complex.re (hxsq.trans h2)
    rw [Complex.ofReal_re, Complex.ofReal_re] at hre_eq
    rw [← hre_eq]
    ring
  refine ⟨c_gap, C_gap, κ_gap, le_max_left _ _, hC_pos, hκ_pos, ?_, ?_⟩
  · intro c' hc' g hg hM_pos
    have hc_deep' : c_deep ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
    have hc'_pos : 0 < c' := lt_of_lt_of_le (zero_lt_one.trans_le hc_deep1) hc_deep'
    have hbd := hdeep hc_deep' hg
    rw [show xiStar - δ = x_cap by dsimp [δ]; ring, ← hΔ_eq hc'_pos] at hbd
    unfold deltaLobe
    calc (prob.cardyNorm (c' / 12) g)⁻¹ *
          ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2)),
            |g t| * prob.cardyV (c' / 12) t
        ≤ (prob.cardyNorm (c' / 12) g)⁻¹ *
            (C_gap * Real.exp (-κ_gap * c') * prob.cardyNorm (c' / 12) g) :=
          mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hM_pos.le)
      _ = C_gap * Real.exp (-κ_gap * c') := by field_simp [hM_pos.ne']
  · intro c' T g hc' hwf
    have hc'_c₀ : D.c₀ ≤ c' := (le_max_left _ _).trans hc'
    have hc'_deep : c_deep ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
    have hlog_bd : (Real.log (2 * C_gap) + 1) / κ_gap ≤ c' :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hc')
    have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'_c₀
    let P := D.pAt hc'_c₀
    have hM_pos : 0 < prob.cardyNorm (c' / 12) g :=
      cardyNorm_pos_of_nonzero_P prob P hwf.1 hwf.2.1
    have hbd_self : deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') := by
      have hbd := hdeep hc'_deep hwf.1
      rw [show xiStar - δ = x_cap by dsimp [δ]; ring, ← hΔ_eq hc'_pos] at hbd
      unfold deltaLobe
      calc (prob.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2)),
              |g t| * prob.cardyV (c' / 12) t
          ≤ (prob.cardyNorm (c' / 12) g)⁻¹ *
              (C_gap * Real.exp (-κ_gap * c') * prob.cardyNorm (c' / 12) g) :=
            mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hM_pos.le)
        _ = C_gap * Real.exp (-κ_gap * c') := by field_simp [hM_pos.ne']
    have hexp_half : C_gap * Real.exp (-κ_gap * c') < 1 / 2 := by
      have hmul : Real.log (2 * C_gap) + 1 ≤ κ_gap * c' := by
        linarith [(div_le_iff₀ hκ_pos).mp hlog_bd]
      have hneg : -κ_gap * c' < -Real.log (2 * C_gap) := by linarith
      have hexp : Real.exp (-κ_gap * c') < (2 * C_gap)⁻¹ := by
        calc Real.exp (-κ_gap * c') < Real.exp (-Real.log (2 * C_gap)) := Real.exp_lt_exp.mpr hneg
          _ = (2 * C_gap)⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
      calc C_gap * Real.exp (-κ_gap * c') < C_gap * (2 * C_gap)⁻¹ :=
            mul_lt_mul_of_pos_left hexp hC_pos
        _ = 1 / 2 := by field_simp [hC_pos.ne']
    have hdl_half : deltaLobe prob D.r_1 c' g < 1 / 2 := hbd_self.trans_lt hexp_half
    have hT_gt : virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) < T := by
      by_contra hle
      push Not at hle
      have hΔ_pos : 0 < virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) :=
        virasoroDeltaChart_pos hc'_pos
          (chart_real_abs_le_virasoro D.hr1_pos hc'_pos (by rw [abs_of_nonneg (sq_nonneg _)]))
      let T' : ℝ := max 0 T
      have hT'_nn : 0 ≤ T' := le_max_left _ _
      have hT'_le : T' ≤ virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) := max_le hΔ_pos.le hle
      have htail' : ∀ t ≥ T', 0 ≤ g t := fun t ht => hwf.2.2.2 t ((le_max_right 0 T).trans ht)
      have hvac_le0 : 0 ≤ -2 * π * ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t := by
        exact hwf.2.2.1
      have hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t := fun ht =>
        D.cardyV_nonneg hc'_c₀ ht
      have hhalf : prob.cardyNorm (c' / 12) g / 2 ≤
          ∫ t in (0 : ℝ)..T', |g t| * prob.cardyV (c' / 12) t := by
        have hint_gV : IntegrableOn (fun t => g t * prob.cardyV (c' / 12) t) (Ioi 0) :=
          hwf.1.int_cardy.norm.mono'
            (((hwf.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
              Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
            (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
        have h1 : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t ≤ 0 := by
          nlinarith [Real.pi_pos]
        have hunion : Ioc (0 : ℝ) T' ∪ Ioi T' = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hT'_nn
        have hdisj := Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := T')
        have hM_split : prob.cardyNorm (c' / 12) g =
            (∫ t in Ioc 0 T', |g t| * prob.cardyV (c' / 12) t) +
            (∫ t in Ioi T', |g t| * prob.cardyV (c' / 12) t) := by
          unfold FixedWeightProblem.cardyNorm
          rw [← hunion]
          exact setIntegral_union hdisj measurableSet_Ioi
            (hwf.1.int_cardy.mono_set Ioc_subset_Ioi_self)
            (hwf.1.int_cardy.mono_set (Ioi_subset_Ioi hT'_nn))
        have hgV_split : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t =
            (∫ t in Ioc 0 T', g t * prob.cardyV (c' / 12) t) +
            (∫ t in Ioi T', g t * prob.cardyV (c' / 12) t) := by
          rw [← hunion]
          exact setIntegral_union hdisj measurableSet_Ioi
            (hint_gV.mono_set Ioc_subset_Ioi_self)
            (hint_gV.mono_set (Ioi_subset_Ioi hT'_nn))
        have htail_eq : ∫ t in Ioi T', g t * prob.cardyV (c' / 12) t =
            ∫ t in Ioi T', |g t| * prob.cardyV (c' / 12) t :=
          setIntegral_congr_fun measurableSet_Ioi fun t ht => by
            rw [abs_of_nonneg (htail' t (mem_Ioi.mp ht).le)]
        have hhead_le : -(∫ t in Ioc 0 T', |g t| * prob.cardyV (c' / 12) t) ≤
            ∫ t in Ioc 0 T', g t * prob.cardyV (c' / 12) t := by
          rw [← integral_neg]
          refine setIntegral_mono_on
            ((hwf.1.int_cardy.mono_set Ioc_subset_Ioi_self).neg)
            (hint_gV.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
          have hV := hV_nonneg ht.1.le
          calc -(|g t| * prob.cardyV (c' / 12) t) = (-|g t|) * prob.cardyV (c' / 12) t := by ring
            _ ≤ g t * prob.cardyV (c' / 12) t := mul_le_mul_of_nonneg_right (neg_abs_le (g t)) hV
        rw [intervalIntegral.integral_of_le hT'_nn]
        linarith
      have hint_le : ∫ t in (0 : ℝ)..T', |g t| * prob.cardyV (c' / 12) t ≤
          ∫ t in (0 : ℝ)..(virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2)),
            |g t| * prob.cardyV (c' / 12) t := by
        rw [intervalIntegral.integral_of_le hT'_nn, intervalIntegral.integral_of_le hΔ_pos.le]
        refine setIntegral_mono_set (hwf.1.int_cardy.mono_set Ioc_subset_Ioi_self) ?_
          (Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hT'_le⟩)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact mul_nonneg (abs_nonneg _) (D.cardyV_nonneg hc'_c₀ ht.1.le)
      have hdiv_le : (1 / 2 : ℝ) ≤ deltaLobe prob D.r_1 c' g := by
        unfold deltaLobe
        have h1 := mul_le_mul_of_nonneg_left (hhalf.trans hint_le) (inv_nonneg.mpr hM_pos.le)
        have h2 : (prob.cardyNorm (c' / 12) g)⁻¹ * (prob.cardyNorm (c' / 12) g / 2) = 1 / 2 := by
          field_simp [hM_pos.ne']
        linarith
      linarith
    exact ⟨hM_pos, hbd_self, hdl_half, hT_gt⟩

/-- **Lemma Q (`wone:Q`), part (1)**: exponential far-lobe bound supplying `(Q1)`/`(B1)`. -/
theorem lemmaQ_general_part1 {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c_gap C_gap κ_gap : ℝ, D.c₀ ≤ c_gap ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      ∀ {c' T : ℝ} {g : ℝ → ℝ}, c_gap ≤ c' →
        prob.IsWeaklyFeasible (c' / 12) T g →
          0 < prob.cardyNorm (c' / 12) g ∧
          deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
          deltaLobe prob D.r_1 c' g < 1 / 2 ∧
          virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) < T := by
  obtain ⟨c_gap, C_gap, κ_gap, hc, hC, hκ, _, hwf⟩ := deltaLobe_gap_general D
  exact ⟨c_gap, C_gap, κ_gap, hc, hC, hκ, fun hc' h => hwf hc' h⟩

/-- **Lemma Q (`wone:Q`), part (2)**: holomorphy on `psiDom c' ⊇ closedBall 0 (chartAC D.r_1 c'^2)`,
real-axis values & sign preservation (**H2+**), and type-(II) envelope (Proposition P Step 2). -/
theorem lemmaQ_general_part2 {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c₂ C₀ : ℝ, D.c₀ ≤ c₂ ∧ 0 < C₀ ∧
      ∀ {c' : ℝ}, c₂ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
        0 < prob.cardyNorm (c' / 12) g →
          AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c') ∧
          (∀ u : ℝ, |u| ≤ chartAC D.r_1 c' ^ 2 →
            (psiTilde prob c' g (u : ℂ)).im = 0 ∧
            (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTilde prob c' g (u : ℂ)).re)) ∧
          ∀ u : ℂ, u ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
            ‖psiTilde prob c' g u‖ ≤
              C₀ * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
                ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹ := by
  obtain ⟨c_an, hc_an, han⟩ := psiTilde_analyticOnNhd prob
  obtain ⟨c_env, C₀, hc_env, hC₀, henv⟩ := psiTilde_typeII_envelope_general D
  refine ⟨max c_env c_an, C₀, hc_env.trans (le_max_left _ _), hC₀,
    fun {c'} hc' {g} hg hM_pos => ?_⟩
  have hc'_env : c_env ≤ c' := (le_max_left _ _).trans hc'
  have hc'_an : c_an ≤ c' := (le_max_right _ _).trans hc'
  have hc'_c₀ : D.c₀ ≤ c' := hc_env.trans hc'_env
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'_c₀
  refine ⟨han hc'_an hg, ?_, fun u hu hcut => henv hc'_env hg hM_pos hu hcut⟩
  intro u hu
  have hu_vir := chart_real_abs_le_virasoro D.hr1_pos hc'_pos hu
  refine ⟨psiTilde_im_ofReal prob hc'_pos hg hu_vir, ?_⟩
  rw [psiTilde_re_ofReal prob hc'_pos hg hu_vir]
  have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hu_vir)
  have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'_pos _
  have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
    have := mul_pos (half_pos cStar_pos) hc13_pos; linarith
  have ht_pos : 0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc'_pos hu_vir
  have hV_pos : 0 < prob.cardyV (c' / 12) (virasoroDeltaChart c' u) := D.p1_pos hc'_c₀ ht_pos
  have hfac_pos : 0 < (prob.cardyNorm (c' / 12) g)⁻¹ *
      (-(deriv (virasoroDeltaChart c') u)) *
      prob.cardyV (c' / 12) (virasoroDeltaChart c' u) := by positivity
  have h_eq : (prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        (g (virasoroDeltaChart c' u) * prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) =
      ((prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) * g (virasoroDeltaChart c' u) := by ring
  rw [h_eq]
  exact (mul_nonneg_iff_of_pos_left hfac_pos).symm

private lemma continuousOn_deriv_virasoroDeltaChart {c' a b : ℝ} (hc' : 0 < c')
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ContinuousOn (deriv (virasoroDeltaChart c')) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  intro u hu
  let x : ℝ := u * c' ^ (-(2 / 3 : ℝ))
  have hx_open : |x| < virasoroRUInf := by
    have h1 := virasoro_u_mem_open_ball hc' (u := (u : ℂ))
      (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_mem u hu)
    have hux : ((u : ℂ) * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) = ((x : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
    rwa [hux, mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
  have hderiv_eq : EqOn (deriv (virasoroDeltaChart c'))
      (fun t : ℝ => c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re)
      (Icc a b) := fun t ht =>
    (virasoroDeltaChart_hasDerivAt hc' (hu_mem t ht)).deriv
  have hcont_rhs : ContinuousOn
      (fun t : ℝ => c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re)
      (Icc a b) := fun t ht => by
    have htu : (((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) ∈ ball (0 : ℂ) virasoroRUInf := by
      have h1 := virasoro_u_mem_open_ball hc' (u := (t : ℂ))
        (by simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hu_mem t ht)
      rwa [← Complex.ofReal_mul] at h1
    have hc_at : ContinuousAt (deriv virasoroXiInf) (((t * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) :=
      (virasoroXiInf_an.deriv _ htu).continuousAt
    have hlin : Continuous (fun s : ℝ => (((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)
    have hcomp : ContinuousAt
        (fun s : ℝ => (deriv virasoroXiInf ((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re) t :=
      Complex.continuous_re.continuousAt.comp
        (hc_at.comp (f := fun s : ℝ => (((s * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ))) hlin.continuousAt)
    exact (continuousAt_const.mul hcomp).continuousWithinAt
  exact (hcont_rhs.congr hderiv_eq) u hu

/-- Oriented real-part change-of-variables for `psiTilde` on `[a, b] ⊆ [-A^2, A^2]`. -/
lemma psiTilde_re_integral_eq (prob : FixedWeightProblem) {c' a b : ℝ} (hc' : 0 < c')
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, (psiTilde prob c' g (u : ℂ)).re =
      (prob.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          g t * prob.cardyV (c' / 12) t := by
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 : ∫ u in a..b, (psiTilde prob c' g (u : ℂ)).re =
      -((prob.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, g (virasoroDeltaChart c' u) *
          prob.cardyV (c' / 12) (virasoroDeltaChart c' u) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [psiTilde_re_ofReal prob hc' hg (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, g (virasoroDeltaChart c' u) *
        prob.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        g t * prob.cardyV (c' / 12) t := by
    have hcont_gV : ContinuousOn (fun t : ℝ => g t * prob.cardyV (c' / 12) t)
        (virasoroDeltaChart c' '' Set.uIcc a b) := by
      refine (hg.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono ?_
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (virasoroDeltaChart_pos hc' (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := virasoroDeltaChart_hasDerivAt hc' (hu_mem u hu)
      exact hd.deriv ▸ hd
    exact intervalIntegral.integral_comp_mul_deriv' hderiv_at
      (continuousOn_deriv_virasoroDeltaChart hc' ha_bd hb_bd hab) hcont_gV
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

/-- Oriented L¹ change-of-variables for `‖psiTilde‖` on `[a, b] ⊆ [-A^2, A^2]`. -/
lemma psiTilde_norm_integral_eq (prob : FixedWeightProblem) {c' a b : ℝ} (hc' : 0 < c')
    (hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t) {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g) (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (ha_bd : -(virasoroAC c' ^ 2) ≤ a) (hb_bd : b ≤ virasoroAC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, ‖psiTilde prob c' g (u : ℂ)‖ =
      (prob.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          |g t| * prob.cardyV (c' / 12) t := by
  have hu_mem : ∀ u ∈ Icc a b, |u| ≤ virasoroAC c' ^ 2 := fun u hu =>
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 : ∫ u in a..b, ‖psiTilde prob c' g (u : ℂ)‖ =
      -((prob.cardyNorm (c' / 12) g)⁻¹ *
        ∫ u in a..b, |g (virasoroDeltaChart c' u)| *
          prob.cardyV (c' / 12) (virasoroDeltaChart c' u) *
          deriv (virasoroDeltaChart c') u) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hab] at hu
    rw [psiTilde_norm_ofReal prob hc' hV_nonneg hg hM_pos (hu_mem u hu)]
    ring
  have hsub : ∫ u in a..b, |g (virasoroDeltaChart c' u)| *
        prob.cardyV (c' / 12) (virasoroDeltaChart c' u) *
        deriv (virasoroDeltaChart c') u =
      ∫ t in (virasoroDeltaChart c' a)..(virasoroDeltaChart c' b),
        |g t| * prob.cardyV (c' / 12) t := by
    have hcont_gV : ContinuousOn (fun t : ℝ => |g t| * prob.cardyV (c' / 12) t)
        (virasoroDeltaChart c' '' Set.uIcc a b) := by
      refine (hg.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono ?_
      rintro t ⟨u, hu, rfl⟩
      rw [Set.uIcc_of_le hab] at hu
      exact (virasoroDeltaChart_pos hc' (hu_mem u hu)).le
    have hderiv_at : ∀ u ∈ Set.uIcc a b,
        HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hd := virasoroDeltaChart_hasDerivAt hc' (hu_mem u hu)
      exact hd.deriv ▸ hd
    exact intervalIntegral.integral_comp_mul_deriv' hderiv_at
      (continuousOn_deriv_virasoroDeltaChart hc' ha_bd hb_bd hab) hcont_gV
  rw [h1, hsub, intervalIntegral.integral_symm (virasoroDeltaChart c' b) (virasoroDeltaChart c' a)]
  ring

private lemma chartUT_mem_Icc_of_between {r_1 c' T : ℝ} (hr1 : 0 < r_1) (hc' : 0 < c')
    (hlo : virasoroDeltaChart c' (chartAC r_1 c' ^ 2) ≤ T)
    (hhi : T ≤ virasoroDeltaChart c' (-(chartAC r_1 c' ^ 2))) :
    chartUT c' T ∈ Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2) ∧
      virasoroDeltaChart c' (chartUT c' T) = T := by
  have hanti := virasoroDeltaChart_strictAnti hc'
  have hA2_le := chartAC_sq_le_virasoroAC_sq hr1 hc'.le
  have hsub : Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2) ⊆
      Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := fun u hu =>
    ⟨by linarith [hu.1], hu.2.trans hA2_le⟩
  have hcont : ContinuousOn (virasoroDeltaChart c')
      (Icc (-(chartAC r_1 c' ^ 2)) (chartAC r_1 c' ^ 2)) := fun u hu =>
    (virasoroDeltaChart_hasDerivAt hc' (abs_le.mpr (hsub hu))).continuousAt.continuousWithinAt
  have himg := intermediate_value_Icc' (show -(chartAC r_1 c' ^ 2) ≤ chartAC r_1 c' ^ 2 by
      linarith [sq_nonneg (chartAC r_1 c')]) hcont ⟨hlo, hhi⟩
  obtain ⟨u, hu_mem, hu_eq⟩ := himg
  have hu_abs : |u| ≤ virasoroAC c' ^ 2 := abs_le.mpr (hsub hu_mem)
  have hu_eq' : chartUT c' T = u := by
    unfold chartUT
    rw [← hu_eq]
    exact virasoroUChart_deltaChart hc' hu_abs
  rw [hu_eq']
  exact ⟨hu_mem, hu_eq⟩

/-- **Lemma Q (`wone:Q`), part (3) (`Proposition P` item (4) + `(H1)`)** at general `(w, Q)`:
real-axis sign preservation `(H2+)`, L¹ mass `≤ 1` `(H1)`, half-mass negative tail, and top-tail
transport identity. Note the explicit upper threshold `T < Δ(-A_{c'}(r₁)^2)` for the interior
placement of `u_T`. -/
theorem lemmaQ_general_part3 {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c₃ : ℝ, D.c₀ ≤ c₃ ∧
      ∀ {c' T : ℝ} {g : ℝ → ℝ}, c₃ ≤ c' →
        prob.IsWeaklyFeasible (c' / 12) T g →
          let A2 := chartAC D.r_1 c' ^ 2
          let M := prob.cardyNorm (c' / 12) g
          (∀ u : ℝ, |u| ≤ A2 → T ≤ virasoroDeltaChart c' u →
            0 ≤ (psiTilde prob c' g (u : ℂ)).re) ∧
          (∫ u in (-A2)..A2, ‖psiTilde prob c' g (u : ℂ)‖ ≤ 1) ∧
          (T < virasoroDeltaChart c' (-A2) →
            virasoroDeltaChart c' A2 < T →
            chartUT c' T ∈ Ioo (-A2) A2) ∧
          (T < virasoroDeltaChart c' (-A2) →
            virasoroDeltaChart c' A2 ≤ T →
            chartUT c' T ∈ Icc (-A2) A2 ∧
            (∀ u ∈ Icc (-A2) (chartUT c' T), 0 ≤ (psiTilde prob c' g (u : ℂ)).re) ∧
            ((1 / 2 : ℝ) - deltaLobe prob D.r_1 c' g ≤
              ∫ u in (chartUT c' T)..A2, max 0 (-(psiTilde prob c' g (u : ℂ)).re))) ∧
          (∀ R' : ℝ, 0 ≤ R' → R' ≤ A2 → T ≤ virasoroDeltaChart c' (-R') →
            ∫ u in (-R')..A2, (psiTilde prob c' g (u : ℂ)).re =
              M⁻¹ * ∫ t in (virasoroDeltaChart c' A2)..(virasoroDeltaChart c' (-R')),
                g t * prob.cardyV (c' / 12) t ∧
            ∫ u in (-R')..A2, (psiTilde prob c' g (u : ℂ)).re ≤ deltaLobe prob D.r_1 c' g) := by
  obtain ⟨c₂, _, hc₂, _, hpart2⟩ := lemmaQ_general_part2 D
  refine ⟨c₂, hc₂, fun {c' T g} hc' hg => ?_⟩
  have hc'_c₀ : D.c₀ ≤ c' := hc₂.trans hc'
  have hc'_pos : 0 < c' := D.hc₀_pos.trans_le hc'_c₀
  let P := D.pAt hc'_c₀
  have hM_pos : 0 < prob.cardyNorm (c' / 12) g :=
    cardyNorm_pos_of_nonzero_P prob P hg.1 hg.2.1
  have hV_nonneg : ∀ {t : ℝ}, 0 ≤ t → 0 ≤ prob.cardyV (c' / 12) t := fun ht =>
    D.cardyV_nonneg hc'_c₀ ht
  have hgv_int : IntegrableOn (fun t => g t * prob.cardyV (c' / 12) t) (Ioi 0) :=
    hg.1.int_cardy.norm.mono'
      (((hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
        Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun t => by simp [Real.norm_eq_abs])
  have hM_int : IntegrableOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Ioi 0) :=
    hg.1.int_cardy
  have hA2_le_vir : chartAC D.r_1 c' ^ 2 ≤ virasoroAC c' ^ 2 :=
    chartAC_sq_le_virasoroAC_sq D.hr1_pos hc'_pos.le
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu hT_le
    exact (hpart2 hc' hg.1 hM_pos).2.1 u hu |>.2.mp (hg.2.2.2 _ hT_le)
  · have hA2_nn : 0 ≤ chartAC D.r_1 c' ^ 2 := sq_nonneg _
    rw [psiTilde_norm_integral_eq prob hc'_pos hV_nonneg hg.1 hM_pos
      (by linarith) hA2_le_vir (by linarith)]
    have hΔ_hi : virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) ≤
        virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2)) :=
      (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        (a := -(chartAC D.r_1 c' ^ 2)) (b := chartAC D.r_1 c' ^ 2)
        (Set.mem_Icc.mpr ⟨by linarith [hA2_le_vir, hA2_nn], by linarith [hA2_le_vir, hA2_nn]⟩)
        (Set.mem_Icc.mpr ⟨by linarith [hA2_le_vir, hA2_nn], hA2_le_vir⟩)
        (by linarith [hA2_nn])
    have hΔ_pos : 0 ≤ virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2) :=
      (virasoroDeltaChart_pos hc'_pos
        (chart_real_abs_le_virasoro D.hr1_pos hc'_pos (by rw [abs_of_nonneg hA2_nn]))).le
    have hint_le : ∫ t in (virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2))..
          (virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2))),
          |g t| * prob.cardyV (c' / 12) t ≤
        prob.cardyNorm (c' / 12) g := by
      rw [intervalIntegral.integral_of_le hΔ_hi]
      change ∫ t in Ioc (virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2))
          (virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2))),
          |g t| * prob.cardyV (c' / 12) t ≤
        ∫ t in Ioi (0 : ℝ), |g t| * prob.cardyV (c' / 12) t
      refine setIntegral_mono_set hM_int ?_
        (Eventually.of_forall fun t ht => hΔ_pos.trans_lt ht.1)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (hV_nonneg ht.le)
    calc (prob.cardyNorm (c' / 12) g)⁻¹ *
          ∫ t in (virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2))..
            (virasoroDeltaChart c' (-(chartAC D.r_1 c' ^ 2))),
            |g t| * prob.cardyV (c' / 12) t
        ≤ (prob.cardyNorm (c' / 12) g)⁻¹ * prob.cardyNorm (c' / 12) g :=
          mul_le_mul_of_nonneg_left hint_le (inv_nonneg.mpr hM_pos.le)
      _ = 1 := inv_mul_cancel₀ hM_pos.ne'
  · intro hT_hi hT_lo
    obtain ⟨huT_mem, huT_eq⟩ := chartUT_mem_Icc_of_between D.hr1_pos hc'_pos hT_lo.le hT_hi.le
    exact ⟨lt_of_le_of_ne huT_mem.1 (fun h => by rw [← huT_eq, ← h] at hT_hi; exact absurd hT_hi (lt_irrefl _)),
      lt_of_le_of_ne huT_mem.2 (fun h => by rw [← huT_eq, h] at hT_lo; exact absurd hT_lo (lt_irrefl _))⟩
  · intro hT_hi hT_lo
    obtain ⟨huT_mem, huT_eq⟩ := chartUT_mem_Icc_of_between D.hr1_pos hc'_pos hT_lo hT_hi.le
    refine ⟨huT_mem, fun u hu => ?_, ?_⟩
    · have hu_abs : |u| ≤ chartAC D.r_1 c' ^ 2 := abs_le.mpr ⟨hu.1, hu.2.trans huT_mem.2⟩
      have hT_le : T ≤ virasoroDeltaChart c' u := by
        rw [← huT_eq]
        exact (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
          ⟨by linarith [hu.1, hA2_le_vir], (hu.2.trans huT_mem.2).trans hA2_le_vir⟩
          ⟨by linarith [huT_mem.1, hA2_le_vir], huT_mem.2.trans hA2_le_vir⟩ hu.2
      exact (hpart2 hc' hg.1 hM_pos).2.1 u hu_abs |>.2.mp (hg.2.2.2 _ hT_le)
    · set t_lo := virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2)
      have hu_mem : ∀ u ∈ Icc (chartUT c' T) (chartAC D.r_1 c' ^ 2), |u| ≤ virasoroAC c' ^ 2 :=
        fun u hu => chart_real_abs_le_virasoro D.hr1_pos hc'_pos
          (abs_le.mpr ⟨huT_mem.1.trans hu.1, hu.2⟩)
      have hneg_eq : ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
            max 0 (-(psiTilde prob c' g (u : ℂ)).re) =
          (prob.cardyNorm (c' / 12) g)⁻¹ *
            ∫ t in t_lo..T, max 0 (-g t) * prob.cardyV (c' / 12) t := by
        have h1 : ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
              max 0 (-(psiTilde prob c' g (u : ℂ)).re) =
            -((prob.cardyNorm (c' / 12) g)⁻¹ *
              ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
                (max 0 (-g (virasoroDeltaChart c' u)) *
                  prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
                deriv (virasoroDeltaChart c') u) := by
          rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
          refine intervalIntegral.integral_congr fun u hu => ?_
          rw [Set.uIcc_of_le huT_mem.2] at hu
          have hua := hu_mem u hu
          have hder_le := virasoroDeltaChart_deriv_le hc'_pos (abs_le.mp hua)
          have hnd_pos : 0 < -(deriv (virasoroDeltaChart c') u) := by
            have := mul_pos (half_pos cStar_pos) (Real.rpow_pos_of_pos hc'_pos (1 / 3 : ℝ))
            linarith
          have ht_pos : 0 < virasoroDeltaChart c' u := virasoroDeltaChart_pos hc'_pos hua
          have hV_nn : 0 ≤ prob.cardyV (c' / 12) (virasoroDeltaChart c' u) := hV_nonneg ht_pos.le
          have hfac_nn : 0 ≤ (prob.cardyNorm (c' / 12) g)⁻¹ *
              (-(deriv (virasoroDeltaChart c') u)) *
              prob.cardyV (c' / 12) (virasoroDeltaChart c' u) := by positivity
          rw [psiTilde_re_ofReal prob hc'_pos hg.1 hua]
          have hprod : -((prob.cardyNorm (c' / 12) g)⁻¹ *
                (-(deriv (virasoroDeltaChart c') u)) *
                (g (virasoroDeltaChart c' u) *
                  prob.cardyV (c' / 12) (virasoroDeltaChart c' u))) =
              ((prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
                prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
                (-g (virasoroDeltaChart c' u)) := by ring
          rw [hprod]
          conv_lhs =>
            arg 1
            rw [← mul_zero ((prob.cardyNorm (c' / 12) g)⁻¹ *
              (-(deriv (virasoroDeltaChart c') u)) *
              prob.cardyV (c' / 12) (virasoroDeltaChart c' u))]
          rw [← mul_max_of_nonneg _ _ hfac_nn]
          ring
        have hsub : ∫ u in (chartUT c' T)..(chartAC D.r_1 c' ^ 2),
              (max 0 (-g (virasoroDeltaChart c' u)) *
                prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) *
              deriv (virasoroDeltaChart c') u =
            ∫ t in T..t_lo, max 0 (-g t) * prob.cardyV (c' / 12) t := by
          have hcont_gV : ContinuousOn
              (fun t : ℝ => max 0 (-g t) * prob.cardyV (c' / 12) t)
              (virasoroDeltaChart c' '' Set.uIcc (chartUT c' T) (chartAC D.r_1 c' ^ 2)) := by
            refine ((ContinuousOn.sup continuousOn_const hg.1.cont.neg).mul
              (continuous_cardyV prob (c' / 12)).continuousOn).mono ?_
            rintro t ⟨u, hu, rfl⟩
            rw [Set.uIcc_of_le huT_mem.2] at hu
            exact (virasoroDeltaChart_pos hc'_pos (hu_mem u hu)).le
          have hderiv_at : ∀ u ∈ Set.uIcc (chartUT c' T) (chartAC D.r_1 c' ^ 2),
              HasDerivAt (virasoroDeltaChart c') (deriv (virasoroDeltaChart c') u) u := fun u hu => by
            rw [Set.uIcc_of_le huT_mem.2] at hu
            have hd := virasoroDeltaChart_hasDerivAt hc'_pos (hu_mem u hu)
            exact hd.deriv ▸ hd
          have hcov := intervalIntegral.integral_comp_mul_deriv' hderiv_at
            (continuousOn_deriv_virasoroDeltaChart hc'_pos
              (by linarith [huT_mem.1, hA2_le_vir]) hA2_le_vir huT_mem.2)
            hcont_gV
          simpa [huT_eq, t_lo] using hcov
        rw [h1, hsub, intervalIntegral.integral_symm t_lo T]
        ring
      rw [hneg_eq]
      have ht_lo_pos : 0 ≤ t_lo :=
        (virasoroDeltaChart_pos hc'_pos
          (chart_real_abs_le_virasoro D.hr1_pos hc'_pos (by rw [abs_of_nonneg (sq_nonneg _)]))).le
      have hT_nn : 0 ≤ T := ht_lo_pos.trans hT_lo
      have hgv_int_0T : IntervalIntegrable (fun t => g t * prob.cardyV (c' / 12) t) volume 0 T :=
        ((hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc hT_nn
      have hM_int_0T : IntervalIntegrable (fun t => |g t| * prob.cardyV (c' / 12) t) volume 0 T :=
        ((hg.1.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono
          Icc_subset_Ici_self).intervalIntegrable_of_Icc hT_nn
      have hhalf_g : prob.cardyNorm (c' / 12) g / 2 ≤
          ∫ t in (0 : ℝ)..T, max 0 (-g t) * prob.cardyV (c' / 12) t := by
        have htail_tail : ∫ t in Ioi T, g t * prob.cardyV (c' / 12) t =
            ∫ t in Ioi T, |g t| * prob.cardyV (c' / 12) t :=
          setIntegral_congr_fun measurableSet_Ioi fun t ht => by
            rw [abs_of_nonneg (hg.2.2.2 t (mem_Ioi.mp ht).le)]
        have hgVac_le0 : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t ≤ 0 := by
          have := hg.2.2.1; unfold FixedWeightProblem.gVac at this; nlinarith [Real.pi_pos]
        have hsplit_g : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t =
            (∫ t in (0 : ℝ)..T, g t * prob.cardyV (c' / 12) t) +
            ∫ t in Ioi T, g t * prob.cardyV (c' / 12) t := by
          rw [intervalIntegral.integral_of_le hT_nn, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
            (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi hT_nn)),
            Ioc_union_Ioi_eq_Ioi hT_nn]
        have hsplit_M : prob.cardyNorm (c' / 12) g =
            (∫ t in (0 : ℝ)..T, |g t| * prob.cardyV (c' / 12) t) +
            ∫ t in Ioi T, |g t| * prob.cardyV (c' / 12) t := by
          rw [intervalIntegral.integral_of_le hT_nn, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
            (hM_int.mono_set Ioc_subset_Ioi_self) (hM_int.mono_set (Ioi_subset_Ioi hT_nn)),
            Ioc_union_Ioi_eq_Ioi hT_nn]
          rfl
        have hid_pt : ∀ t ∈ Icc (0 : ℝ) T,
            (|g t| - g t) / 2 * prob.cardyV (c' / 12) t =
            max 0 (-g t) * prob.cardyV (c' / 12) t := fun t _ => by
          rcases le_total (g t) 0 with h | h
          · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
          · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
        have hid_int : (∫ t in (0 : ℝ)..T, (|g t| * prob.cardyV (c' / 12) t -
              g t * prob.cardyV (c' / 12) t) / 2) =
            ∫ t in (0 : ℝ)..T, max 0 (-g t) * prob.cardyV (c' / 12) t := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le hT_nn] at ht
          have := hid_pt t ht
          linarith
        have hid_val : (∫ t in (0 : ℝ)..T, (|g t| * prob.cardyV (c' / 12) t -
              g t * prob.cardyV (c' / 12) t) / 2) =
            ((∫ t in (0 : ℝ)..T, |g t| * prob.cardyV (c' / 12) t) -
              ∫ t in (0 : ℝ)..T, g t * prob.cardyV (c' / 12) t) / 2 := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hM_int_0T hgv_int_0T]
        linarith
      have hneg_0T_split :
          ∫ t in (0 : ℝ)..T, max 0 (-g t) * prob.cardyV (c' / 12) t =
            (∫ t in (0 : ℝ)..t_lo, max 0 (-g t) * prob.cardyV (c' / 12) t) +
            ∫ t in t_lo..T, max 0 (-g t) * prob.cardyV (c' / 12) t := by
        have hcont_neg : ContinuousOn (fun t : ℝ => max 0 (-g t) * prob.cardyV (c' / 12) t) (Ici 0) :=
          (ContinuousOn.sup continuousOn_const hg.1.cont.neg).mul
            (continuous_cardyV prob (c' / 12)).continuousOn
        exact (intervalIntegral.integral_add_adjacent_intervals
          ((hcont_neg.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos)
          ((hcont_neg.mono (fun t ht => ht_lo_pos.trans ht.1)).intervalIntegrable_of_Icc hT_lo)).symm
      have hneg_lobe_le : ∫ t in (0 : ℝ)..t_lo, max 0 (-g t) * prob.cardyV (c' / 12) t ≤
          ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
        have hcont_neg : ContinuousOn (fun t : ℝ => max 0 (-g t) * prob.cardyV (c' / 12) t) (Icc 0 t_lo) :=
          ((ContinuousOn.sup continuousOn_const hg.1.cont.neg).mul
            (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self
        have hcont_abs : ContinuousOn (fun t : ℝ => |g t| * prob.cardyV (c' / 12) t) (Icc 0 t_lo) :=
          (hg.1.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self
        refine intervalIntegral.integral_mono_on ht_lo_pos
          (hcont_neg.intervalIntegrable_of_Icc ht_lo_pos)
          (hcont_abs.intervalIntegrable_of_Icc ht_lo_pos) fun t ht => ?_
        exact mul_le_mul_of_nonneg_right (max_le (abs_nonneg _) (neg_le_abs _)) (hV_nonneg ht.1)
      have htail_ge : prob.cardyNorm (c' / 12) g / 2 -
            ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t ≤
          ∫ t in t_lo..T, max 0 (-g t) * prob.cardyV (c' / 12) t := by
        linarith
      have hmul := mul_le_mul_of_nonneg_left htail_ge (inv_nonneg.mpr hM_pos.le)
      have hlhs_eq : (prob.cardyNorm (c' / 12) g)⁻¹ * (prob.cardyNorm (c' / 12) g / 2 -
            ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t) =
          (1 / 2 : ℝ) - deltaLobe prob D.r_1 c' g := by
        unfold deltaLobe
        rw [mul_sub]
        have hcancel : (prob.cardyNorm (c' / 12) g)⁻¹ * (prob.cardyNorm (c' / 12) g / 2) = 1 / 2 := by
          field_simp [hM_pos.ne']
        rw [hcancel]
      linarith
  · intro R' hR'_nn hR'_le hT_le
    have hre := psiTilde_re_integral_eq prob hc'_pos hg.1 (a := -R') (b := chartAC D.r_1 c' ^ 2)
      (by linarith) hA2_le_vir (by linarith)
    refine ⟨hre, ?_⟩
    rw [hre]
    set t_lo := virasoroDeltaChart c' (chartAC D.r_1 c' ^ 2)
    set t_hi := virasoroDeltaChart c' (-R')
    have hR'_abs : |-R'| ≤ virasoroAC c' ^ 2 := by
      rw [abs_neg, abs_of_nonneg hR'_nn]; exact hR'_le.trans hA2_le_vir
    have hA2_abs : |chartAC D.r_1 c' ^ 2| ≤ virasoroAC c' ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _)]; exact hA2_le_vir
    have ht_lo_pos : 0 ≤ t_lo := (virasoroDeltaChart_pos hc'_pos hA2_abs).le
    have ht_lo_hi : t_lo ≤ t_hi :=
      (virasoroDeltaChart_strictAnti hc'_pos).antitoneOn
        ⟨by linarith [hR'_abs, abs_le.mp hR'_abs], (abs_le.mp hR'_abs).2⟩
        ⟨(abs_le.mp hA2_abs).1, hA2_le_vir⟩ (by linarith)
    have hsplit : ∫ t in (0 : ℝ)..t_hi, g t * prob.cardyV (c' / 12) t =
        (∫ t in (0 : ℝ)..t_lo, g t * prob.cardyV (c' / 12) t) +
        ∫ t in t_lo..t_hi, g t * prob.cardyV (c' / 12) t := by
      have hcont : ContinuousOn (fun t => g t * prob.cardyV (c' / 12) t) (Ici 0) :=
        hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((hcont.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht_lo_pos)
        ((hcont.mono (fun t ht => ht_lo_pos.trans ht.1)).intervalIntegrable_of_Icc ht_lo_hi)).symm
    have hgv_le0 : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t ≤ 0 := by
      have := hg.2.2.1; unfold FixedWeightProblem.gVac at this; nlinarith [Real.pi_pos]
    have hgv_0_hi : ∫ t in (0 : ℝ)..t_hi, g t * prob.cardyV (c' / 12) t ≤ 0 := by
      have ht_hi_nn : 0 ≤ t_hi := ht_lo_pos.trans ht_lo_hi
      have htot : ∫ t in Ioi (0 : ℝ), g t * prob.cardyV (c' / 12) t =
          (∫ t in (0 : ℝ)..t_hi, g t * prob.cardyV (c' / 12) t) +
          ∫ t in Ioi t_hi, g t * prob.cardyV (c' / 12) t := by
        rw [intervalIntegral.integral_of_le ht_hi_nn, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hgv_int.mono_set Ioc_subset_Ioi_self) (hgv_int.mono_set (Ioi_subset_Ioi ht_hi_nn)),
          Ioc_union_Ioi_eq_Ioi ht_hi_nn]
      have htail_nn : 0 ≤ ∫ t in Ioi t_hi, g t * prob.cardyV (c' / 12) t :=
        setIntegral_nonneg measurableSet_Ioi fun t ht =>
          mul_nonneg (hg.2.2.2 t (le_trans hT_le (mem_Ioi.mp ht).le))
            (hV_nonneg (ht_hi_nn.trans (mem_Ioi.mp ht).le))
      linarith
    have hint_neg : ∫ t in t_lo..t_hi, g t * prob.cardyV (c' / 12) t ≤
        ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
      have hneg_le : -(∫ t in (0 : ℝ)..t_lo, g t * prob.cardyV (c' / 12) t) ≤
          ∫ t in (0 : ℝ)..t_lo, |g t| * prob.cardyV (c' / 12) t := by
        rw [← intervalIntegral.integral_neg]
        have hcont1 : ContinuousOn (fun t => -(g t * prob.cardyV (c' / 12) t)) (Icc 0 t_lo) :=
          ((hg.1.cont.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self).neg
        have hcont2 : ContinuousOn (fun t => |g t| * prob.cardyV (c' / 12) t) (Icc 0 t_lo) :=
          (hg.1.cont.abs.mul (continuous_cardyV prob (c' / 12)).continuousOn).mono Icc_subset_Ici_self
        refine intervalIntegral.integral_mono_on ht_lo_pos
          (hcont1.intervalIntegrable_of_Icc ht_lo_pos)
          (hcont2.intervalIntegrable_of_Icc ht_lo_pos) fun t ht => ?_
        calc -(g t * prob.cardyV (c' / 12) t) = (-g t) * prob.cardyV (c' / 12) t := by ring
          _ ≤ |g t| * prob.cardyV (c' / 12) t :=
              mul_le_mul_of_nonneg_right (neg_le_abs _) (hV_nonneg ht.1)
      linarith
    unfold deltaLobe
    exact mul_le_mul_of_nonneg_left hint_neg (inv_nonneg.mpr hM_pos.le)

/-- Unified **Proposition P (`ft:PP`)** at general `(w, Q)`: packages `(H1)`, `(H2-hol)`,
`(H2+)`, `(H4a)` (lobe zero-freeness on `closedBall ξ_* D.r_1`), type-(II) envelope (Step 2),
far-lobe exponential decay (Step 3), and item `(4)` (Lemma Q `(1)`–`(3)`). -/
theorem proposition_P_general {prob : FixedWeightProblem} (D : UniformPropositionPData prob) :
    ∃ c_P C₀ C_gap κ_gap : ℝ,
      D.c₀ ≤ c_P ∧ 0 < C₀ ∧ 0 < C_gap ∧ 0 < κ_gap ∧
      (∀ {c' : ℝ}, c_P ≤ c' → ∀ b ∈ closedBall (xiStar : ℂ) D.r_1,
        cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) ≠ 0) ∧
      ∀ {c' T : ℝ} {g : ℝ → ℝ}, c_P ≤ c' →
        prob.IsWeaklyFeasible (c' / 12) T g →
          let A2 := chartAC D.r_1 c' ^ 2
          AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c') ∧
          (∀ u : ℝ, |u| ≤ A2 →
            (psiTilde prob c' g (u : ℂ)).im = 0 ∧
            (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTilde prob c' g (u : ℂ)).re)) ∧
          (∀ u : ℂ, u ∈ closedBall (0 : ℂ) A2 → ¬ (u.im = 0 ∧ u.re ≤ 0) →
            ‖psiTilde prob c' g u‖ ≤
              C₀ * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
                ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) ∧
          deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
          deltaLobe prob D.r_1 c' g < 1 / 2 ∧
          virasoroDeltaChart c' A2 < T ∧
          (∫ u in (-A2)..A2, ‖psiTilde prob c' g (u : ℂ)‖ ≤ 1) ∧
          (T < virasoroDeltaChart c' (-A2) →
            chartUT c' T ∈ Ioo (-A2) A2 ∧
            (∀ u ∈ Icc (-A2) (chartUT c' T), 0 ≤ (psiTilde prob c' g (u : ℂ)).re) ∧
            ((1 / 2 : ℝ) - deltaLobe prob D.r_1 c' g ≤
              ∫ u in (chartUT c' T)..A2, max 0 (-(psiTilde prob c' g (u : ℂ)).re))) := by
  obtain ⟨c_gap, C_gap, κ_gap, hc_gap, hC_gap, hκ_gap, _, hpart1⟩ := deltaLobe_gap_general D
  obtain ⟨c₂, C₀, hc₂, hC₀, hpart2⟩ := lemmaQ_general_part2 D
  obtain ⟨c₃, hc₃, hpart3⟩ := lemmaQ_general_part3 D
  obtain ⟨c_h4a, hc_h4a⟩ := eventually_atTop.mp (propP_H4a_eventually_ne_zero D)
  let c_P : ℝ := max (max c_gap c₂) (max c₃ c_h4a)
  have hcP_c₀ : D.c₀ ≤ c_P := hc_gap.trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨c_P, C₀, C_gap, κ_gap, hcP_c₀, hC₀, hC_gap, hκ_gap, ?_, ?_⟩
  · intro c' hc' b hb
    exact hc_h4a c' ((le_max_right _ _).trans ((le_max_right _ _).trans hc')) b hb
  · intro c' T g hc' hwf
    have hc'_1 : c_gap ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
    have hc'_2 : c₂ ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
    have hc'_3 : c₃ ≤ c' := (le_max_left _ _).trans ((le_max_right _ _).trans hc')
    obtain ⟨hM_pos, hdl_bd, hdl_half, hT_gt⟩ := hpart1 hc'_1 hwf
    obtain ⟨han, hreal, henv⟩ := hpart2 hc'_2 hwf.1 hM_pos
    obtain ⟨_, hL1, hIoo, hIcc_neg, _⟩ := hpart3 hc'_3 hwf
    refine ⟨han, hreal, henv, hdl_bd, hdl_half, hT_gt, hL1, fun hT_lt => ?_⟩
    exact ⟨hIoo hT_lt hT_gt, (hIcc_neg hT_lt hT_gt.le).2.1, (hIcc_neg hT_lt hT_gt.le).2.2⟩

/-- Unconditional **Proposition P (`ft:PP`)** for every `prob : FixedWeightProblem`. -/
theorem proposition_P_of_problem (prob : FixedWeightProblem) :
    ∃ D : UniformPropositionPData prob,
      ∃ c_P C₀ C_gap κ_gap : ℝ,
        D.c₀ ≤ c_P ∧ 0 < C₀ ∧ 0 < C_gap ∧ 0 < κ_gap ∧
        (∀ {c' : ℝ}, c_P ≤ c' → ∀ b ∈ closedBall (xiStar : ℂ) D.r_1,
          cardyVC prob (c' / 12) ((c' : ℂ) * b ^ 2 / 3) ≠ 0) ∧
        ∀ {c' T : ℝ} {g : ℝ → ℝ}, c_P ≤ c' →
          prob.IsWeaklyFeasible (c' / 12) T g →
            let A2 := chartAC D.r_1 c' ^ 2
            AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c') ∧
            (∀ u : ℝ, |u| ≤ A2 →
              (psiTilde prob c' g (u : ℂ)).im = 0 ∧
              (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTilde prob c' g (u : ℂ)).re)) ∧
            (∀ u : ℂ, u ∈ closedBall (0 : ℂ) A2 → ¬ (u.im = 0 ∧ u.re ≤ 0) →
              ‖psiTilde prob c' g u‖ ≤
                C₀ * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
                  ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) ∧
            deltaLobe prob D.r_1 c' g ≤ C_gap * Real.exp (-κ_gap * c') ∧
            deltaLobe prob D.r_1 c' g < 1 / 2 ∧
            virasoroDeltaChart c' A2 < T ∧
            (∫ u in (-A2)..A2, ‖psiTilde prob c' g (u : ℂ)‖ ≤ 1) ∧
            (T < virasoroDeltaChart c' (-A2) →
              chartUT c' T ∈ Ioo (-A2) A2 ∧
              (∀ u ∈ Icc (-A2) (chartUT c' T), 0 ≤ (psiTilde prob c' g (u : ℂ)).re) ∧
              ((1 / 2 : ℝ) - deltaLobe prob D.r_1 c' g ≤
                ∫ u in (chartUT c' T)..A2, max 0 (-(psiTilde prob c' g (u : ℂ)).re))) :=
  let ⟨D⟩ := UniformPropositionPData.of_problem prob
  ⟨D, proposition_P_general D⟩

/-! ### Axiom Checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.UniformPropositionPData.of_problem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UniformPropositionPData.of_problem

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.propP_H4a_eventually_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms propP_H4a_eventually_ne_zero

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.psiTilde_typeII_envelope_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms psiTilde_typeII_envelope_general

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.lemmaQ_general_part3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaQ_general_part3

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightTip.proposition_P_of_problem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_P_of_problem

end FormalResearch.ModularBootstrap.FixedWeightTip


