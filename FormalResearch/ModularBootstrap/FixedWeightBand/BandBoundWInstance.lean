module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BandBoundWAux
public import FormalResearch.ModularBootstrap.FixedWeightBand.BandBoundWDensity

/-!
# The Band-Reduction Instance for `W̃_V` at Weight `w` (Proposition `Y_V`, `vlo:YV`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, proof of Proposition `Y_V`
(`vlo:YV`, l. 548): Lemma S4 gives `(MS1)` (`M = 0`), Lemmas `J4.0`–`J4.2` give `(MS2)` with
`E_sub = {0 < x ≤ ξ*/2}`, `a₀ = A₁`, `a₂ = A₂`, `R₀ = -D(x₀(τ), x)`, `Φ = -Θ`, `ν`, `μ(x) = 2 log (x/ξ*)`,
`m(τ) = 2 log (x₀(τ)/ξ*)`; `lemma_S6` gives the `τ₀` bounds.

* `YWWitness prob`: the weight-`w` constants of `lemma_S4_W`, `lemma_J4_1_W`, `lemma_J4_2_W` (single
  scale `c_W`); the weight-free constants (Lemma `J4.0`, Langer chart, scale `c₀`) are those of the
  Virasoro witness `StripMultiplier.yvWitness pg` and are reused through `langerDelta_props`,
  `langerNegV_*` of `StripMultiplier.BandBound`.
* `ywBandParams`: `BandReductionParams` with the weight-`w` constants `C_W = C_S4`,
  `C_a = max (C_A1 + C_A1') (max C_A2 C_sub)`, `κ_sub`.
* `ywBandInstance`: the `StripBand.BandReductionInstance` for `W̃_V / M[g]`.

The hypothesis `ha_0_bd` of `(MS2)` is `‖a₀‖ + ‖a₀'‖ ≤ C_a (1+|τ|)^M` with `M = 0`: it needs only the
pointwise bounds `|A₁| ≤ C`, `|A₁'| ≤ C` that follow from `|A₁'| ≤ C_w/(1+|τ|)` (`lemma_J4_2_W`),
not the `1/c'` decay of the Virasoro case.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Chart ChartGeometry StripBand
open FormalResearch.ModularBootstrap.StripMultiplier

/-! ### Section 1: The weight-`w` witness and parameters -/

/-- Constants of Lemmas S4, J4.1, J4.2 at weight `w` for `prob`, at one common scale `c_W`. -/
structure YWWitness (prob : FixedWeightProblem) where
  c_W : ℝ
  hc_W : max 1 (24 * prob.totalShift) ≤ c_W
  -- Lemma S4
  C_S4 : ℝ
  hC_S4 : 0 < C_S4
  hS4 : ∀ {c' : ℝ}, c_W ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
    DifferentiableOn ℂ (tildeWW prob.w c' g) stripOpen ∧
    ContinuousOn (tildeWW prob.w c' g) stripClosed ∧
    (∀ ζ ∈ stripClosed, tildeWW prob.w c' g (1 - ζ) = -tildeWW prob.w c' g ζ) ∧
    (∀ ζ ∈ stripClosed, ‖tildeWW prob.w c' g ζ‖ ≤ C_S4 * prob.cardyNorm (c' / 12) g)
  -- Lemma J4.1
  hJ41_edge : ∀ {c' : ℝ}, c_W ≤ c' → ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
    ∀ τ : ℝ, tildeWW prob.w c' g (Complex.I * (τ : ℂ)) =
      ∫ t in Ioi (0 : ℝ), edgeKernelKW prob c' τ t * ((g t * prob.cardyV (c' / 12) t : ℝ) : ℂ)
  -- Lemma J4.2
  C_A1 : ℝ
  C_A1' : ℝ
  C_A2 : ℝ
  C_sub : ℝ
  κ_sub : ℝ
  hC_A1 : 0 < C_A1
  hC_A1' : 0 < C_A1'
  hC_A2 : 0 < C_A2
  hC_sub : 0 < C_sub
  hκ_sub : 0 < κ_sub
  hA1_bd : ∀ {c' : ℝ}, c_W ≤ c' → ∀ τ : ℝ, ‖edgeA1W prob.w c' τ‖ ≤ C_A1 ∧
    ∃ d : ℂ, HasDerivAt (edgeA1W prob.w c') d τ ∧ ‖d‖ ≤ C_A1' / (1 + |τ|)
  hA2_bd : ∀ {c' : ℝ}, c_W ≤ c' → ∀ {t : ℝ}, 0 < t → xiStar / 2 ≤ √(3 * t / c') →
    0 ≤ edgeA2W prob c' t ∧ edgeA2W prob c' t ≤ C_A2
  hK_sub : ∀ {c' : ℝ}, c_W ≤ c' → ∀ {t : ℝ}, 0 < t → √(3 * t / c') ≤ xiStar / 2 →
    ∀ τ : ℝ, ‖edgeKernelKW prob c' τ t‖ ≤ C_sub * Real.exp (-κ_sub * c')

lemma ywWitness_exists (prob : FixedWeightProblem) : Nonempty (YWWitness prob) := by
  obtain ⟨C_S4, c₁, hC_S4, hc₁, hS4⟩ := lemma_S4_W prob
  obtain ⟨c₂, hc₂, hJ41⟩ := lemma_J4_1_W prob
  obtain ⟨C_A1, C_A1', C_A2, C_sub, κ_sub, c₃, hC_A1, hC_A1', hC_A2, hC_sub, hκ_sub, hc₃,
    hJ42⟩ := lemma_J4_2_W prob
  refine ⟨{
    c_W := max c₁ (max c₂ c₃)
    hc_W := hc₁.trans (le_max_left _ _)
    C_S4 := C_S4
    hC_S4 := hC_S4
    hS4 := fun {c'} hc' {g} hg => hS4 ((le_max_left _ _).trans hc') hg
    hJ41_edge := fun {c'} hc' {g} hg =>
      (hJ41 (((le_max_left _ _).trans (le_max_right _ _)).trans hc') hg).1
    C_A1 := C_A1
    C_A1' := C_A1'
    C_A2 := C_A2
    C_sub := C_sub
    κ_sub := κ_sub
    hC_A1 := hC_A1
    hC_A1' := hC_A1'
    hC_A2 := hC_A2
    hC_sub := hC_sub
    hκ_sub := hκ_sub
    hA1_bd := fun {c'} hc' => (hJ42 (((le_max_right _ _).trans (le_max_right _ _)).trans hc')).1
    hA2_bd := fun {c'} hc' {t} ht hx =>
      (hJ42 (((le_max_right _ _).trans (le_max_right _ _)).trans hc')).2.1 ht hx
    hK_sub := fun {c'} hc' {t} ht hx τ =>
      (hJ42 (((le_max_right _ _).trans (le_max_right _ _)).trans hc')).2.2.1 ht hx τ }⟩

noncomputable def ywWitness (prob : FixedWeightProblem) : YWWitness prob :=
  Classical.choice (ywWitness_exists prob)

/-- `BandReductionParams` for `W̃_V` at weight `w`: the weight-free constants are those of
`StripMultiplier.yvBandParams`, the weight-`w` constants come from `ywWitness prob`. -/
noncomputable def ywBandParams (prob : FixedWeightProblem) (pg : LangerChartSpec) (A_thr : ℝ) :
    BandReductionParams :=
  let w := ywWitness prob
  { yvBandParams pg A_thr with
    C_W := w.C_S4
    C_a := max (w.C_A1 + w.C_A1') (max w.C_A2 w.C_sub)
    κ_sub := w.κ_sub
    hC_W := w.hC_S4
    hC_a := lt_of_lt_of_le (add_pos w.hC_A1 w.hC_A1') (le_max_left _ _)
    hκ_sub := w.hκ_sub }

lemma ywBandParams_b (prob : FixedWeightProblem) (pg : LangerChartSpec) (A_thr : ℝ) :
    (ywBandParams prob pg A_thr).b = (yvBandParams pg A_thr).b := rfl

/-- Scale threshold: the Virasoro threshold `yvThresh` (which carries the weight-free scales) and the
weight-`w` scale `c_W`. -/
noncomputable def ywThresh (prob : FixedWeightProblem) (pg : LangerChartSpec) (A_thr : ℝ) : ℝ :=
  max (yvThresh pg A_thr) (ywWitness prob).c_W

lemma ywThresh_ge_yv {prob : FixedWeightProblem} {pg : LangerChartSpec} {A_thr c' : ℝ}
    (hc' : ywThresh prob pg A_thr ≤ c') : yvThresh pg A_thr ≤ c' :=
  (le_max_left _ _).trans hc'

lemma ywThresh_ge_c_W {prob : FixedWeightProblem} {pg : LangerChartSpec} {A_thr c' : ℝ}
    (hc' : ywThresh prob pg A_thr ≤ c') : (ywWitness prob).c_W ≤ c' :=
  (le_max_right _ _).trans hc'

lemma ywThresh_ge (prob : FixedWeightProblem) (pg : LangerChartSpec) (A_thr : ℝ) :
    10000 ≤ ywThresh prob pg A_thr :=
  (yvThresh_ge pg A_thr).trans (le_max_left _ _)

/-! ### Section 2: The instance -/

/-- Canonical `(MS1)–(MS2)` `BandReductionInstance` for `W̃_V(ζ)/M[g]` at weight `w`, from any test
function `g ∈ TestClass prob (c'/12)` with `0 < M[g]`, `g ≥ 0` on `[T, ∞)`, and
`T ∈ [Δ(0), Δ(-A_thr)]` (`-A_thr ≤ ũ_T ≤ 0`). -/
noncomputable def ywBandInstance (prob : FixedWeightProblem) (pg : LangerChartSpec)
    {A_thr c' R T : ℝ}
    (hA_thr : 0 ≤ A_thr)
    (hc' : ywThresh prob pg A_thr ≤ c')
    (hR_lb : (ywBandParams prob pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (ywBandParams prob pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T)
    (hT_hi : T ≤ langerDelta pg c' (-A_thr))
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t) :
    BandReductionInstance (ywBandParams prob pg A_thr) :=
  let P := ywBandParams prob pg A_thr
  let w := ywWitness prob
  let wv := yvWitness pg
  let M := prob.cardyNorm (c' / 12) g
  let hc'_yv : yvThresh pg A_thr ≤ c' := ywThresh_ge_yv hc'
  let hc'_W : w.c_W ≤ c' := ywThresh_ge_c_W hc'
  let hc'_max : max 1 (24 * prob.totalShift) ≤ c' := w.hc_W.trans hc'_W
  let hc'_10000 : 10000 ≤ c' := (ywThresh_ge prob pg A_thr).trans hc'
  let hc'_pos : 0 < c' := by linarith
  let hc'_ge1 : 1 ≤ c' := by linarith
  let hR_lb' : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := hR_lb
  let hR_ub' : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := hR_ub
  let hshift : prob.totalShift ≤ c' / 12 := (shift_le_of_max_le prob hc'_max).1
  let hS4_g := w.hS4 hc'_W hg
  let hProps := langerDelta_props hc'_yv hR_lb' hR_ub'
  let hA_le_R : max A_thr 1 ≤ R := hProps.2.2.1
  let hT_ge_xiBar : c' * xiStar ^ 2 / 3 ≤ T := by
    rwa [← langerDelta_zero pg c']
  let hE_sub_sub : Ioc 0 (c' * (xiStar / 2) ^ 2 / 3) ⊆ Ioo 0 T := by
    intro ξ hξ
    refine ⟨hξ.1, hξ.2.trans_lt ?_⟩
    have hxi_sq : 0 < c' * xiStar ^ 2 / 3 := by have := xiStar_pos; positivity
    calc c' * (xiStar / 2) ^ 2 / 3 = (c' * xiStar ^ 2 / 3) / 4 := by ring
      _ < c' * xiStar ^ 2 / 3 := by linarith
      _ ≤ T := hT_ge_xiBar
  let x_cut : ℝ := c' * (xiStar / 2) ^ 2 / 3
  let a0p : ℝ → ℂ := fun τ => Classical.choose (w.hA1_bd hc'_W τ).2
  let ha0p_spec : ∀ τ, HasDerivAt (edgeA1W prob.w c') (a0p τ) τ ∧
      ‖a0p τ‖ ≤ w.C_A1' / (1 + |τ|) :=
    fun τ => Classical.choose_spec (w.hA1_bd hc'_W τ).2
  { c := c'
    ε := -1
    R := R
    hc := hc'_ge1
    hε := Or.inr rfl
    hR_lb := hR_lb
    hR_ub := hR_ub
    hρR_ub := yv_rhoR_le pg hc'_yv hR_lb' hR_ub'
    W_tilde := fun ζ => ((M⁻¹ : ℝ) : ℂ) * tildeWW prob.w c' g ζ
    hW_cont := continuousOn_const.mul hS4_g.2.1
    hW_holo := (differentiableOn_const _).mul hS4_g.1
    hW_symm := fun ζ h0 h1 => by
      rw [hS4_g.2.2.1 ζ ⟨h0, h1⟩]
      push_cast; ring
    hW_bound := fun ζ h0 h1 => by
      have hbd := hS4_g.2.2.2 ζ ⟨h0, h1⟩
      show ‖((M⁻¹ : ℝ) : ℂ) * tildeWW prob.w c' g ζ‖ ≤ w.C_S4 * (1 + ‖ζ‖) ^ (0 : ℝ)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hM_pos.le),
        Real.rpow_zero, mul_one]
      calc M⁻¹ * ‖tildeWW prob.w c' g ζ‖ ≤ M⁻¹ * (w.C_S4 * M) :=
            mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr hM_pos.le)
        _ = w.C_S4 := by rw [mul_comm w.C_S4 M, ← mul_assoc, inv_mul_cancel₀ hM_pos.ne', one_mul]
    dmPos := bandMeasPos prob (c' / 12) g
    dmNeg := bandMeasNeg prob (c' / 12) g
    hdmPos_fin := bandMeasPos_isFinite hshift hg
    hdmNeg_fin := bandMeasNeg_isFinite hshift hg
    hdmPos_supp := bandMeasPos_Iic g
    hdmNeg_supp := bandMeasNeg_Iic g
    hdm_tv := (bandMeas_tv hshift hg hM_pos).le
    T := T
    hdm_nonneg_tail := bandMeasNeg_Ici_eq_zero hg_nonneg
    E_sub := Ioc 0 x_cut
    hE_sub_meas := measurableSet_Ioc
    hE_sub_sub := hE_sub_sub
    K_edge := edgeKernelKW prob c'
    hK_meas := measurable_edgeKernelKW prob hc'_pos.le
    hW_edge := fun τ => by
      rw [mul_comm (τ : ℂ) Complex.I, w.hJ41_edge hc'_W hg τ]
      exact (edge_integral_split prob hc'_max hg hM_pos τ).symm
    hK_sub := fun ξ hξ τ => by
      have hxt : √(3 * ξ / c') ≤ xiStar / 2 := by
        rw [Real.sqrt_le_iff]
        refine ⟨div_nonneg xiStar_pos.le zero_le_two, ?_⟩
        have h3 : ξ ≤ c' * (xiStar / 2) ^ 2 / 3 := hξ.2
        rw [div_le_iff₀ hc'_pos]
        linarith
      exact (w.hK_sub hc'_W hξ.1 hxt τ).trans (mul_le_mul_of_nonneg_right
        ((le_max_right w.C_A2 w.C_sub).trans (le_max_right _ _)) (Real.exp_pos _).le)
    a_0 := edgeA1W prob.w c'
    a_0' := a0p
    a_2 := fun ξ => (edgeA2W prob c' ξ : ℂ)
    R_0 := edgeRV c'
    Phi := edgePhi c'
    hK_factor := fun ξ hξ τ => edgeKernelKW_factorization prob hc'_max τ hξ.1
    ha_2_bd := fun ξ hξ => by
      have hxt : xiStar / 2 ≤ √(3 * ξ / c') := by
        by_contra hlt; push Not at hlt
        apply hξ.2
        refine ⟨hξ.1, ?_⟩
        have hsq : (√(3 * ξ / c')) ^ 2 ≤ (xiStar / 2) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hlt.le 2
        rw [Real.sq_sqrt (by have := hξ.1.le; positivity), div_le_iff₀ hc'_pos] at hsq
        dsimp [x_cut]
        linarith
      have hbd := w.hA2_bd hc'_W hξ.1 hxt
      rw [Complex.norm_real, Real.norm_of_nonneg hbd.1]
      exact hbd.2.trans ((le_max_left w.C_A2 w.C_sub).trans (le_max_right _ _))
    ha_0_deriv := fun τ => (ha0p_spec τ).1
    ha_0_bd := fun τ => by
      show ‖edgeA1W prob.w c' τ‖ + ‖a0p τ‖ ≤
        max (w.C_A1 + w.C_A1') (max w.C_A2 w.C_sub) * (1 + |τ|) ^ (0 : ℝ)
      rw [Real.rpow_zero, mul_one]
      have h1 := (w.hA1_bd hc'_W τ).1
      have h2 := (ha0p_spec τ).2
      have h1t : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
      have h2' : ‖a0p τ‖ ≤ w.C_A1' := by
        calc ‖a0p τ‖ ≤ w.C_A1' / (1 + |τ|) := h2
          _ ≤ w.C_A1' / 1 := div_le_div_of_nonneg_left w.hC_A1'.le zero_lt_one h1t
          _ = w.C_A1' := div_one _
      exact (add_le_add h1 h2').trans (le_max_left _ _)
    hR_0_nonpos := fun ξ hξ τ => edgeRV_nonpos hξ.1 hc'_pos
    hR_0_cont := fun ξ _ => edgeRV_continuousOn c' ξ
    hR_0_even := fun _ _ τ => edgeRV_even c' τ _
    hR_0_unimodal := fun ξ hξ => ⟨edgeTau0 c' ξ, edgeRV_unimodal hc'_pos hξ.1⟩
    hPhi_odd := fun ξ hξ τ => edgePhi_odd hc'_pos hξ.1
    ν := edgeNu
    ν' := edgeNuDeriv
    invNu' := edgeInvNu
    hν_deriv := fun τ _ => hasDerivAt_edgeNu τ
    hν'_cont := (continuous_iff_continuousAt.mpr fun τ =>
      (hasDerivAt_edgeNuDeriv τ).continuousAt).continuousOn
    hν'_inv_pos := fun τ hτ => by
      have hnu_lb : wv.cnu₁ * (1 + τ) ≤ edgeNuDeriv τ := (wv.hnu_bd τ hτ.le).1
      have h1τ : 1 ≤ 1 + τ := by linarith
      have hnu_ge : wv.cnu₁ ≤ edgeNuDeriv τ := by
        calc wv.cnu₁ = wv.cnu₁ * 1 := (mul_one _).symm
          _ ≤ wv.cnu₁ * (1 + τ) := mul_le_mul_of_nonneg_left h1τ wv.hcnu₁.le
          _ ≤ edgeNuDeriv τ := hnu_lb
      have hnu_pos : 0 < edgeNuDeriv τ := lt_of_lt_of_le wv.hcnu₁ hnu_ge
      refine ⟨inv_pos.mpr hnu_pos, ?_⟩
      exact (inv_anti₀ wv.hcnu₁ hnu_ge).trans (le_max_left _ _)
    hν'_inv_deriv := fun τ hτ => by
      have hnu_pos : 0 < edgeNuDeriv τ := lt_of_lt_of_le
        (mul_pos wv.hcnu₁ (by linarith : 0 < 1 + τ)) (wv.hnu_bd τ hτ.le).1
      exact ((hasDerivAt_edgeNuDeriv τ).inv hnu_pos.ne').congr_deriv (by unfold edgeInvNu; rfl)
    hinvNu'_cont := edgeInvNu_continuousOn pg
    hinvNu'_integrable := edgeInvNu_integrable pg
    hinvNu'_int := (edgeInvNu_int_le pg).trans (le_max_right _ _)
    μ := fun t => 2 * Real.log (√(3 * t / c') / xiStar)
    m := fun τ => 2 * (edgeMV τ - Real.log xiStar)
    m' := fun τ => 2 * (edgeX0Deriv τ / edgeX0 τ)
    hPhi_deriv := fun ξ hξ τ _ => by
      refine (hasDerivAt_edgePhi hc'_pos hξ.1 τ).congr_deriv ?_
      have hx_pos : 0 < √(3 * ξ / c') :=
        Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hξ.1) hc'_pos)
      have hx0_pos : 0 < edgeX0 τ := edgeX0_pos_all τ
      rw [show √(3 * ξ / c') / edgeX0 τ = (√(3 * ξ / c') / xiStar) / (edgeX0 τ / xiStar) by
        field_simp [xiStar_pos.ne', hx0_pos.ne']]
      rw [Real.log_div (div_pos hx_pos xiStar_pos).ne' (div_pos hx0_pos xiStar_pos).ne',
        Real.log_div hx0_pos.ne' xiStar_pos.ne']
      unfold edgeMV; ring
    hm_0 := by unfold edgeMV; rw [edgeX0_zero, sub_self, mul_zero]
    hm_cont := by
      have hx0_cont : Continuous edgeX0 :=
        continuous_iff_continuousAt.mpr fun s => (hasDerivAt_edgeX0 s).continuousAt
      refine ContinuousOn.const_mul (ContinuousOn.sub ?_ continuousOn_const) 2
      exact ContinuousOn.log hx0_cont.continuousOn fun τ _ => (edgeX0_pos_all τ).ne'
    hm_strictMono := by
      intro τ₁ h₁ τ₂ h₂ h12
      unfold edgeMV
      have hlt := edgeX0_strictMonoOn h₁ h₂ h12
      have hlog := Real.log_lt_log (edgeX0_pos h₁) hlt
      linarith
    hm_deriv := fun τ hτ => by
      have hm := (hasDerivAt_edgeMV hτ.le).sub_const (Real.log xiStar)
      exact hm.const_mul 2
    hm_step := fun τ hτ => by
      have h := wv.hmv_step τ hτ
      show 2 * wv.c_mv * min (τ ^ 2) 1 ≤ 2 * (edgeMV τ - Real.log xiStar) -
        2 * (edgeMV (τ / 2) - Real.log xiStar)
      linarith
    hm_slope := fun τ hτ => by
      have h := wv.hmv_slope τ hτ
      show 2 * wv.c_sl * τ / (1 + τ ^ 3) ≤ 2 * (edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ
      rw [show 2 * (edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ =
          2 * ((edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ) by ring]
      calc 2 * wv.c_sl * τ / (1 + τ ^ 3)
          = 2 * (wv.c_sl * (τ / (1 + τ ^ 3))) := by ring
        _ ≤ 2 * ((edgeX0Deriv τ / edgeX0 τ) / edgeNuDeriv τ) := by gcongr
    τ_0 := edgeTau0 c'
    hτ_0_nn := edgeTau0_nonneg c'
    hτ_0_eq_zero := fun ξ hmu => by
      have hx_le : √(3 * ξ / c') ≤ xiStar := by
        by_cases hξ : ξ ≤ 0
        · have hdiv : 3 * ξ / c' ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc'_pos.le
          rw [Real.sqrt_eq_zero_of_nonpos hdiv]
          exact xiStar_pos.le
        · push Not at hξ
          have hx_pos : 0 < √(3 * ξ / c') :=
            Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hξ) hc'_pos)
          have hlog : Real.log (√(3 * ξ / c') / xiStar) ≤ 0 := by linarith
          have hdiv1 : √(3 * ξ / c') / xiStar ≤ 1 :=
            (Real.log_nonpos_iff (div_pos hx_pos xiStar_pos).le).mp hlog
          exact (div_le_one xiStar_pos).mp hdiv1
      unfold edgeTau0
      simp only [hx_le, ↓reduceIte]
    hτ_0_root := fun ξ hmu => by
      by_cases hξ : ξ ≤ 0
      · exfalso
        have hdiv : 3 * ξ / c' ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc'_pos.le
        rw [Real.sqrt_eq_zero_of_nonpos hdiv, zero_div, Real.log_zero, mul_zero] at hmu
        exact lt_irrefl 0 hmu
      · push Not at hξ
        have hx_pos : 0 < √(3 * ξ / c') :=
          Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) hξ) hc'_pos)
        have hlog : 0 < Real.log (√(3 * ξ / c') / xiStar) := by linarith
        have h1lt : 1 < √(3 * ξ / c') / xiStar :=
          (Real.log_pos_iff (div_pos hx_pos xiStar_pos).le).mp hlog
        have hx_gt : xiStar < √(3 * ξ / c') := (one_lt_div xiStar_pos).mp h1lt
        have hxe := (edgeX0_edgeTau0 hc'_pos hx_gt).2
        unfold edgeMV
        rw [hxe, Real.log_div hx_pos.ne' xiStar_pos.ne']
    u_tilde := fun ξ => -langerNegV pg c' R ξ
    Delta := langerDelta pg c'
    hτ_0_below := fun ξ hξ => yv_tau0_below pg hA_thr hc'_yv hR_lb' hR_ub' hT_hi hξ.1
    hτ_0_band := fun ξ hξ => yv_tau0_band pg hc'_yv hR_lb' hR_ub' hT_lo hξ
    hu_tilde_int := by
      have hmono : MonotoneOn (fun ξ => -(-langerNegV pg c' R ξ))
          (Icc T (langerDelta pg c' (-R))) := by
        have hm := langerNegV_monotoneOn hc'_yv hR_lb' hR_ub'
        intro ξ₁ h₁ ξ₂ h₂ h12
        simpa [neg_neg] using hm ⟨hT_lo.trans h₁.1, h₁.2⟩ ⟨hT_lo.trans h₂.1, h₂.2⟩ h12
      have hmeas : AEMeasurable (fun ξ => -(-langerNegV pg c' R ξ))
          ((bandMeasPos prob (c' / 12) g).restrict (Icc T (langerDelta pg c' (-R)))) :=
        aemeasurable_restrict_of_monotoneOn measurableSet_Icc hmono
      have : IsFiniteMeasure (bandMeasPos prob (c' / 12) g) := bandMeasPos_isFinite hshift hg
      refine (integrable_const R).mono' hmeas.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Icc fun ξ hξ => ?_
      have hv_spec := langerNegV_mem_and_eq hc'_yv hR_lb' hR_ub' ⟨hT_lo.trans hξ.1, hξ.2⟩
      rw [neg_neg, Real.norm_of_nonneg hv_spec.1.1]
      exact hv_spec.1.2 }

end FormalResearch.ModularBootstrap.FixedWeightBand
