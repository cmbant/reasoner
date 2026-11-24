module

public import FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQScale
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuadratureBounds

/-!
# Concrete Bootstrap at Every Fixed `(w, Q)`: Data Interface (`BootstrapW*`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `FT-L.FW` (`wone:ftlfw`), Lemma `Q`
(`wone:Q`), Proposition `Y_V` (`vlo:YV`), Lemma `D'` (`vlo:Dp`), Lemma `Z` (`vlo:Z`), Theorem `J` (`vlo:J`),
assembled for an arbitrary `prob : FixedWeightProblem` (weight `w = prob.w ≥ 1`, null shifts `Q`).

## Decomposition of the Virasoro proof chain (WP10 of the fixed-weight plan)

Virasoro chain: `TheoremJ ← BootstrapHB ← {ArcBounds, QuadratureBounds, Lemma Q at scale b, Y_V, D', Z,
WindowEnvelope, scale choice}`.  Classification of each ingredient and the module that carries it:

**Weight-free and public (imported, not copied).**
`ConcreteBootstrap/{LangerChart, QuantC1Airy, AiryDiscBounds}` (Langer chart `virasoroDeltaChart`, `virasoroUT`,
`virasoroBV`, `teb_quant_c1_typeII`, `QuantC1B2Holds`, `good_circle_exists`, `airy_circleData`,
`airy_Rplus_bound`); the public elementary lemmas of `ConcreteBootstrap/QuadratureBounds`
(`re_cpow_half_add_real_bounds`, `airyEnv_add_real_le`, `re_cpow_half_circleMap`,
`norm_one_add_circleMap_div`, `integral_Ioi_rpow_mul_exp_neg`, `abs_one_add_pow_sub_one_le`, `YVEnvBound`,
`virasoroAThr`, `virasoroUT_between`) and of `ArcBounds` (`virasoroArcCov`, `virasoroArcCov_le`);
`TwoEdgeBootstrap/{BootstrapParams, BootstrapInstance, Bootstrap, ...}` (`BootstrapHBInstance`,
`teb_bootstrap_hb`, `tebC2`, `tebK0HB`, `teb_band_reduction`); `FixedWeightBand/{LemmaQScale, BandBoundW*,
EdgeKernelW*, LemmaS4W, StirlingW, MellinW, TruncationW*}` (Lemma `Q` at every scale, Proposition `Y_V`/`X_V`,
Lemma `D'` and Lemma `Z` at weight `w`: `lemma_Z_W_band`, `zScaleCapW`).

**Weight-free in content but Virasoro-stated (generalised over `prob`; proofs copied from the Virasoro file):**
* `QuadratureBounds` -> `BootstrapWSchwarz` (`UT_between`, `bandB1W_nonneg`, `bandB2W_nonneg`,
  `yvInputAtW_nonvacuous`, general Schwarz reflection `psiTilde_conj`), `BootstrapWQuad` (tail bound, moment
  identity, shifted function, truncated band moment), `BootstrapWLine` (line bound `hI_line`);
* `ArcBounds` -> `BootstrapWArc` (good-circle quadrature, `quad_arc_boundW`);
* `BootstrapHB` -> `BootstrapWBand` (`B₁ ≤ 1`, `B₂ ≤ 2`, large-`c'` thresholds), `BootstrapWNodes` (node sums),
  `BootstrapWHB` (`BootstrapParams`, `BootstrapHBInstance` with `(B3)`), `BootstrapWMain` (Theorem `FT-L.FW`);
* `VirasoroBridge` -> `BootstrapWYVBand` (uniform band bound over the bootstrap annulus, from `ywBandInstance`),
  `BootstrapWYV` (`YVInputForW prob b` from `Y_V` and Lemma `Z`; scale choice `bvChoice`);
* `TheoremJ`, `VirasoroScaleChoice`, `OptimalMeasure.virasoro_lowerBoundInput` -> `BootstrapWInterface`
  (`T_V ≥ T_* - C`, `FixedWeightLowerBoundInput prob`, unconditional).

**Replaced by constants of Proposition P / Lemma `Q` at weight `w`.**  The Virasoro constants
`virasoroCQEnv`, `virasoroEnvC0`, `virasoroSigma`, `virasoroAC`, `virasoroBV` become the fields and derived
quantities of `LemmaQData prob` (`cQ`, `C0`, `generalSigma D.p_e`, `chartAC D.r_1`, `chartBV D.r_1`);
`virasoro_lobe_scale_down` is `lemmaQ_general_lobe_scale_down`; `virasoroScaleThresh` is
`LemmaQData.scaleThresh = min (c₀/2) (zScaleCapW D)`.

No unproved hypothesis remains: the band-feedback input `YVInputForW prob b` (the Virasoro `YVInput`) is proved
for `b = LemmaQData.bvChoice` (`BootstrapWYV`) and is a hypothesis only of the intermediate theorems at a free
scale `b`.

## This file

* `LemmaQData prob`: the full-scale facts of Lemma `Q` (`wone:Q` (2), (3), holomorphy, positivity of `M[g]`) in
  the form consumed by the Virasoro proofs, thresholds merged into a single `cQ ≥ 10000`
  (`LemmaQData.nonempty`); a class, so that the ported lemmas take it as an instance argument.
* Wrappers `LemmaQData.deltaChart_*` etc. restating the Langer chart lemmas on the shrunk disc
  `closedBall 0 (chartAC D.r_1 c' ^ 2) ⊆ closedBall 0 (virasoroAC c' ^ 2)`.
* `bandB1W`, `bandB2W`, `YVInputAtForWThr`, `YVInputForWThr` (cutoff radius `A_thr` arbitrary), `YVInputAtForW`,
  `YVInputForW` (the case `A_thr = virasoroAThr`); `secondLevelAThr = |a₂| + 1`: the band-feedback hypothesis at weight `w` and
  scale `b` (the Virasoro `YVInputAtFor`, `YVInputFor`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing PoissonJensen TipFront ConcreteBootstrap FixedWeightTip FormalResearch.Special

/-! ### Section 1: Full-scale Lemma `Q` data -/

/-- Full-scale facts of Lemma `Q` (`wone:Q`) at weight `w`, with every threshold merged into `cQ ≥ 10000`.
The disc is `closedBall 0 (chartAC D.r₁ c'^2)`; the Virasoro analogue uses `virasoroAC`. -/
class LemmaQData (prob : FixedWeightProblem) where
  D : UniformPropositionPData prob
  cQ : ℝ
  hcQ_10000 : 10000 ≤ cQ
  hcQ_D : D.c₀ ≤ cQ
  hcQ_shift : 12 * prob.totalShift ≤ cQ
  C0 : ℝ
  hC0 : 0 < C0
  analytic : ∀ {c' : ℝ}, cQ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
    AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c')
  cardyNorm_pos : ∀ {c' T : ℝ} {g : ℝ → ℝ}, cQ ≤ c' →
    prob.IsWeaklyFeasible (c' / 12) T g → 0 < prob.cardyNorm (c' / 12) g
  part2 : ∀ {c' : ℝ}, cQ ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
    0 < prob.cardyNorm (c' / 12) g →
      AnalyticOnNhd ℂ (psiTilde prob c' g) (psiDom c') ∧
      (∀ u : ℝ, |u| ≤ chartAC D.r_1 c' ^ 2 →
        (psiTilde prob c' g (u : ℂ)).im = 0 ∧
        (0 ≤ g (virasoroDeltaChart c' u) ↔ 0 ≤ (psiTilde prob c' g (u : ℂ)).re)) ∧
      ∀ u : ℂ, u ∈ closedBall (0 : ℂ) (chartAC D.r_1 c' ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
        ‖psiTilde prob c' g u‖ ≤
          C0 * airyEnv u * Real.exp (generalSigma D.p_e c' * (u ^ (1 / 2 : ℂ)).re) *
            ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹
  part3 : ∀ {c' T : ℝ} {g : ℝ → ℝ}, cQ ≤ c' →
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
        ∫ u in (-R')..A2, (psiTilde prob c' g (u : ℂ)).re ≤ deltaLobe prob D.r_1 c' g)

/-- `LemmaQData prob` exists for every fixed-weight problem (`lemmaQ_general_part1`-`3`, Proposition P). -/
theorem LemmaQData.nonempty (prob : FixedWeightProblem) : Nonempty (LemmaQData prob) := by
  obtain ⟨D⟩ := UniformPropositionPData.of_problem prob
  obtain ⟨c_an, hc_an, han⟩ := psiTilde_analyticOnNhd prob
  obtain ⟨c_g, C_g, κ_g, hc_g, -, -, hp1⟩ := lemmaQ_general_part1 D
  obtain ⟨c₂, C₀, hc₂, hC₀, hp2⟩ := lemmaQ_general_part2 D
  obtain ⟨c₃, hc₃, hp3⟩ := lemmaQ_general_part3 D
  let cQ : ℝ := max 10000 (max (12 * prob.totalShift) (max c_an (max c_g (max c₂ c₃))))
  have h1 : 10000 ≤ cQ := le_max_left _ _
  have h2 : 12 * prob.totalShift ≤ cQ := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : c_an ≤ cQ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h4 : c_g ≤ cQ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have h5 : c₂ ≤ cQ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have h6 : c₃ ≤ cQ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  exact ⟨{
    D := D
    cQ := cQ
    hcQ_10000 := h1
    hcQ_D := hc_g.trans h4
    hcQ_shift := h2
    C0 := C₀
    hC0 := hC₀
    analytic := fun {c'} hc' {g} hg => han (h3.trans hc') hg
    cardyNorm_pos := fun {c' T g} hc' hwf => (hp1 (h4.trans hc') hwf).1
    part2 := fun {c'} hc' {g} hg hM => hp2 (h5.trans hc') hg hM
    part3 := fun {c' T g} hc' hwf => hp3 (h6.trans hc') hwf }⟩

lemma chartUT_eq_virasoroUT (c' T : ℝ) : chartUT c' T = virasoroUT c' T := rfl

namespace LemmaQData

variable {prob : FixedWeightProblem} (Q : LemmaQData prob)

/-- Full-scale chart cap `b_V = chartBV D.r₁ ≤ virasoroBV`. -/
noncomputable abbrev bV : ℝ := chartBV Q.D.r_1

/-- Full-scale radius `A_{c'} = chartAC D.r₁ c' = √2 b_V c'^{1/3}`. -/
noncomputable abbrev AC (c' : ℝ) : ℝ := chartAC Q.D.r_1 c'

/-- Exponential cut-margin rate of the type-(II) envelope. -/
noncomputable abbrev sigma (c' : ℝ) : ℝ := generalSigma Q.D.p_e c'

/-- Covered-arc/uncovered-wedge factor `C_unc` of the good-circle quadrature at weight `w`. -/
noncomputable def arcUncConst : ℝ :=
  15 * √π * 8 * √2 * Q.C0 * Real.exp 1 * (3 * π) ^ (6 : ℕ)

lemma bV_pos : 0 < Q.bV := chartBV_pos Q.D.hr1_pos

lemma bV_le_virasoroBV : Q.bV ≤ virasoroBV := chartBV_le_virasoroBV _

lemma AC_eq_chartACAt (c' : ℝ) : Q.AC c' = chartACAt Q.bV c' := rfl

lemma AC_sq (c' : ℝ) (hc' : 0 ≤ c') : Q.AC c' ^ 2 = 2 * Q.bV ^ 2 * c' ^ (2 / 3 : ℝ) :=
  chartAC_sq _ _ hc'

lemma AC_pos {c' : ℝ} (hc' : 0 < c') : 0 < Q.AC c' := chartAC_pos Q.D.hr1_pos hc'

lemma AC_sq_le_virasoro {c' : ℝ} (hc' : 0 ≤ c') : Q.AC c' ^ 2 ≤ virasoroAC c' ^ 2 :=
  chartAC_sq_le_virasoroAC_sq Q.D.hr1_pos hc'

lemma abs_le_virasoro {c' u : ℝ} (hc' : 0 ≤ c') (hu : |u| ≤ Q.AC c' ^ 2) :
    |u| ≤ virasoroAC c' ^ 2 := hu.trans (Q.AC_sq_le_virasoro hc')

/-- A smaller scale `0 < b ≤ b_V` has a smaller disc (the Virasoro `virasoroACAt_sq_le`). -/
lemma ACAt_sq_le {b c' : ℝ} (hb : 0 ≤ b) (hle : b ≤ Q.bV) (hc' : 0 ≤ c') :
    chartACAt b c' ^ 2 ≤ Q.AC c' ^ 2 :=
  chartACAt_sq_le_chartAC_sq hb hle hc'

lemma sigma_nonneg {c' : ℝ} (hc' : 1 ≤ c') : 0 ≤ Q.sigma c' :=
  generalSigma_nonneg Q.D.hp_e_nn hc'

lemma sigma_tendsto_zero : Tendsto Q.sigma atTop (𝓝 0) := generalSigma_tendsto_zero _

lemma arcUncConst_pos : 0 < Q.arcUncConst := by
  unfold arcUncConst
  have := Q.hC0
  have := Real.pi_pos
  positivity

lemma closedBall_subset_psiDom {c' : ℝ} (hc' : 0 < c') :
    closedBall (0 : ℂ) (Q.AC c' ^ 2) ⊆ psiDom c' :=
  closedBall_chartAC_subset_psiDom Q.D.hr1_pos hc'

lemma totalShift_le {c' : ℝ} (hc' : Q.cQ ≤ c') : prob.totalShift ≤ c' / 12 := by
  have := Q.hcQ_shift
  linarith

lemma c'_ge_10000 {c' : ℝ} (hc' : Q.cQ ≤ c') : 10000 ≤ c' := Q.hcQ_10000.trans hc'

/-! #### Langer chart lemmas on the shrunk disc -/

lemma deltaChart_pos {c' : ℝ} (hc' : 0 < c') {u : ℝ} (hu : |u| ≤ Q.AC c' ^ 2) :
    0 < virasoroDeltaChart c' u :=
  virasoroDeltaChart_pos hc' (Q.abs_le_virasoro hc'.le hu)

lemma deltaChart_hasDerivAt {c' u : ℝ} (hc' : 0 < c') (hu : |u| ≤ Q.AC c' ^ 2) :
    HasDerivAt (virasoroDeltaChart c')
      (c' ^ (1 / 3 : ℝ) * (deriv virasoroXiInf ((u * c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)).re) u :=
  virasoroDeltaChart_hasDerivAt hc' (Q.abs_le_virasoro hc'.le hu)

lemma deltaChart_strictAnti {c' : ℝ} (hc' : 0 < c') :
    StrictAntiOn (virasoroDeltaChart c') (Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2)) :=
  (virasoroDeltaChart_strictAnti hc').mono (Icc_subset_Icc
    (neg_le_neg (Q.AC_sq_le_virasoro hc'.le)) (Q.AC_sq_le_virasoro hc'.le))

lemma deltaChart_div_mem {c' u : ℝ} (hc' : 0 < c') (hu : |u| ≤ Q.AC c' ^ 2) :
    virasoroDeltaChart c' u / c' ∈ Icc (xiBar - virasoroChartR0) (xiBar + virasoroChartR0) :=
  virasoroDeltaChart_div_mem hc' (Q.abs_le_virasoro hc'.le hu)

lemma uChart_deltaChart {c' u : ℝ} (hc' : 0 < c') (hu : |u| ≤ Q.AC c' ^ 2) :
    virasoroUChart c' (virasoroDeltaChart c' u / c') = u :=
  virasoroUChart_deltaChart hc' (Q.abs_le_virasoro hc'.le hu)

lemma deltaChart_inversion {c' u : ℝ} (hc' : 0 < c') (hu : |u| ≤ Q.AC c' ^ 2) :
    virasoroDeltaChart c' u ≥ xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u -
      chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u ^ 2 :=
  virasoro_deltaChart_inversion hc' (Q.abs_le_virasoro hc'.le hu)

lemma deltaChart_deriv_le {c' u : ℝ} (hc' : 0 < c') (hu : u ∈ Icc (-(Q.AC c' ^ 2)) (Q.AC c' ^ 2)) :
    deriv (virasoroDeltaChart c') u ≤ -(cStar / 2) * c' ^ (1 / 3 : ℝ) :=
  virasoroDeltaChart_deriv_le hc'
    (Icc_subset_Icc (neg_le_neg (Q.AC_sq_le_virasoro hc'.le)) (Q.AC_sq_le_virasoro hc'.le) hu)

lemma u_mem_open_ball {c' : ℝ} (hc' : 0 < c') {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) (Q.AC c' ^ 2)) :
    u * ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) ∈ ball (0 : ℂ) virasoroRUInf :=
  virasoro_u_mem_open_ball hc' (closedBall_subset_closedBall (Q.AC_sq_le_virasoro hc'.le) hu)

/-! #### Real-axis formulas for `psiTilde` on the shrunk disc -/

lemma psiTilde_im_ofReal {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    {u : ℝ} (hu : |u| ≤ Q.AC c' ^ 2) : (psiTilde prob c' g (u : ℂ)).im = 0 :=
  FixedWeightTip.psiTilde_im_ofReal prob hc' hg (Q.abs_le_virasoro hc'.le hu)

lemma psiTilde_re_ofReal {c' : ℝ} (hc' : 0 < c') {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    {u : ℝ} (hu : |u| ≤ Q.AC c' ^ 2) :
    (psiTilde prob c' g (u : ℂ)).re =
      (prob.cardyNorm (c' / 12) g)⁻¹ * (-(deriv (virasoroDeltaChart c') u)) *
        (g (virasoroDeltaChart c' u) * prob.cardyV (c' / 12) (virasoroDeltaChart c' u)) :=
  FixedWeightTip.psiTilde_re_ofReal prob hc' hg (Q.abs_le_virasoro hc'.le hu)

lemma psiTilde_integral_eq {c' a b : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass prob (c' / 12) g)
    (ha_bd : -(Q.AC c' ^ 2) ≤ a) (hb_bd : b ≤ Q.AC c' ^ 2) (hab : a ≤ b) :
    ∫ u in a..b, (psiTilde prob c' g (u : ℂ)).re =
      (prob.cardyNorm (c' / 12) g)⁻¹ *
        ∫ t in (virasoroDeltaChart c' b)..(virasoroDeltaChart c' a),
          g t * prob.cardyV (c' / 12) t := by
  have hc'_pos : 0 < c' := by linarith
  have hle := Q.AC_sq_le_virasoro hc'_pos.le
  exact psiTilde_re_integral_eq prob hc'_pos hg (by linarith) (by linarith) hab

end LemmaQData

/-! ### Section 2: The band-feedback hypothesis at weight `w` (`vlo:YV`, `TE.3(2)`-`(3)`) -/

/-- First band moment `B₁ := R⁻¹ ∫_T^{Δ(-R)} (-ũ(t/c')) dm(t)` at weight `w` (`TE.2` / `vlo:YV`). -/
noncomputable def bandB1W (prob : FixedWeightProblem) (c' R T : ℝ) (g : ℝ → ℝ) : ℝ :=
  R⁻¹ * (prob.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in T..(virasoroDeltaChart c' (-R)),
      (-virasoroUT c' t) * (g t * prob.cardyV (c' / 12) t)

/-- Second band moment `B₂ := ∫_{Δ(-R)}^∞ dm(t)` at weight `w` (`TE.2` / `vlo:YV`). -/
noncomputable def bandB2W (prob : FixedWeightProblem) (c' R : ℝ) (g : ℝ → ℝ) : ℝ :=
  (prob.cardyNorm (c' / 12) g)⁻¹ *
    ∫ t in Ici (virasoroDeltaChart c' (-R)), g t * prob.cardyV (c' / 12) t

/-- The threshold `A_thr = |a₂| + 1` of the second level (`m₀ = 2` with `t₂ ∈ (a₂, a₁)`): the upper end of the
range `[virasoroAThr, secondLevelAThr]` of cutoff radii in Step 3 of Theorem `FT-L.FW`. -/
noncomputable def secondLevelAThr : ℝ := |airyZero 2| + 1

lemma virasoroAThr_le_secondLevelAThr : virasoroAThr ≤ secondLevelAThr := by
  unfold virasoroAThr secondLevelAThr
  have h1 := airyZero_one
  have h2 := airyZero_two
  rw [abs_of_neg (by linarith [h1.2]), abs_of_neg (by linarith [h2.2])]
  linarith [h1.1, h2.1]

lemma virasoroAThr_lt_four : virasoroAThr < 4 := by
  unfold virasoroAThr
  have h1 := airyZero_one
  rw [abs_of_neg (by linarith [h1.2])]
  linarith [h1.1]

lemma secondLevelAThr_lt : secondLevelAThr < 5.84 := by
  unfold secondLevelAThr
  have h2 := airyZero_two
  rw [abs_of_neg (by linarith [h2.2])]
  linarith [h2.1]

/-- Band-feedback conclusion `vlo:YV` + `TE.3(2)-(3)` at weight `w` for a family `Ψ c' g`, at chart scale
`b`, feedback factor `C_fb ≥ 1`, threshold `c_YV` and cutoff radius `A_thr` (`vlo:YV` with `A_thr`
arbitrary; Step 3 of `wone:ftlfw` takes `A_thr = |t_{m₀}| + 1`).  The annulus `R + 1 ≤ A_{c'}(b)^2` is the
scale-`b` disc. -/
def YVInputAtForWThr (prob : FixedWeightProblem) (A_thr : ℝ) (b : ℝ)
    (Ψ : ℝ → (ℝ → ℝ) → ℂ → ℂ) (C_fb c_YV : ℝ) : Prop :=
  ∀ ⦃c' T R : ℝ⦄, c_YV ≤ c' →
    A_thr ≤ R →
    b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R →
    R + 1 ≤ chartACAt b c' ^ 2 →
    ∀ ⦃g : ℝ → ℝ⦄, prob.IsWeaklyFeasible (c' / 12) T g →
    virasoroDeltaChart c' 0 ≤ T →
    T ≤ virasoroDeltaChart c' (-A_thr) →
    YVEnvBound (Ψ c' g) c' R
      (C_fb * (c' ^ (1 / 3 : ℝ) * (bandB1W prob c' R T g + bandB2W prob c' R g) + 1))

/-- Band-feedback conclusion `vlo:YV` + `TE.3(2)-(3)` at weight `w` at the level-one cutoff
`A_thr = virasoroAThr = |a₁| + 1` (the Virasoro `YVInputAtFor`). -/
def YVInputAtForW (prob : FixedWeightProblem) (b : ℝ) (Ψ : ℝ → (ℝ → ℝ) → ℂ → ℂ)
    (C_fb c_YV : ℝ) : Prop :=
  YVInputAtForWThr prob virasoroAThr b Ψ C_fb c_YV

/-- Band-feedback input at weight `w`, scale `b` and cutoff radius `A_thr`: `Ψ = psiTilde prob`. -/
def YVInputForWThr (prob : FixedWeightProblem) (A_thr : ℝ) (b : ℝ) : Prop :=
  ∃ C_fb c_YV : ℝ, 1 ≤ C_fb ∧ 10000 ≤ c_YV ∧
    YVInputAtForWThr prob A_thr b (psiTilde prob) C_fb c_YV

/-- **Band-feedback input at weight `w` and scale `b`** (`YVInput` of the Virasoro chain; Proposition `Y_V`
`vlo:YV` with Lemma `D'`, Lemma `Z`, Proposition `L`): `Ψ = psiTilde prob`.  It is produced from
`proposition_YV_W` and the weight-`w` Lemmas `D'`, `Z` (`BootstrapWInputs`); the threshold lower bound
`10000 ≤ c_YV` is harmless because the conclusion is monotone in `c_YV`. -/
def YVInputForW (prob : FixedWeightProblem) (b : ℝ) : Prop :=
  YVInputForWThr prob virasoroAThr b

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.LemmaQData.nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LemmaQData.nonempty

end FormalResearch.ModularBootstrap.FixedWeightBand
