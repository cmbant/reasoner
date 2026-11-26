module

public import FormalResearch.ModularBootstrap.Contour.VirasoroScaleChoice
public import FormalResearch.ModularBootstrap.ConcreteBootstrap.QuantC1Airy

/-!
# `rem:corL`: effective slope and violation size at spinless Virasoro (FIVE-L input)

Source: `CFT/modular_bootstrap/paper/remainder.tex`, Corollary L$^*$.1 (`rem:corL`), recalled from Proposition P(1)-(3)
and Proposition TE.0 (`teb:quant_c1`).

For `c' ≥ c₁` and every weakly feasible Virasoro test `g` at `(c'/12, T)`, with `Ψ := virasoroPsiTilde c' g` the
rescaled density on the Langer disc `|ũ| ≤ A_c²` (`A_c² = virasoroAC c'^2`) and `ũ_T := virasoroUT c' T`:

* **(a) envelope**: on the disc minus the slit `{ũ ≤ 0}`, `‖Ψ(ũ)‖ ≤ C₀ e(ũ) exp(ς_c Re √ũ) |ũ|^{-1/2} (Re √ũ)^{-1}` with
  `C₀ = virasoroEnvC0` and `ς_c = virasoroEnvC1 c'^{-1/3} log c'` (`virasoroSigma`);
* if `g` is **violating** (`T < Δ(a₁)`, i.e. `ũ_T > a₁`), with `x̃ = ũ_T - a₁`:
  * **(b) slope**: `x̃ ≤ 1/2` and `Re Ψ(a₁ + θ x̃) ≥ 2 κ_* (1 - θ) x̃` for `θ ∈ [0,1]` (at `θ = 1/2`: `Re Ψ(a₁ + x̃/2) ≥ κ_* x̃`;
    here `κ_* = quantC1KappaStar`, Lean's normalisation of the effective constant `Ai'(a₁)²/(8 L_*)`);
  * **(c) `C¹` bound**: on `[a₁ - δ_*, a₁ + δ_*]` (`δ_* = quantC1DeltaStar ≤ 1/2`), `‖Ψ'‖ ≤ C₁` (`quantC1C1`) and
    `Re Ψ' ≤ -2 κ_*` (both packaged in `QuantC1B2Holds`);
  * **(d) violation size**: `x̃ ≤ K c'^{-1/3}` (stronger than the paper's `C_- c'^{-1/3} log c'`).

All proved unconditionally (Theorem J at the unconditional scale `virasoroBVChoice`, `lemmaQ_part1/2/3`,
`teb_quant_c1_typeII`).  **Differences from the paper**: the `C¹`-*convergence* clause of (c)
(`Ψ → f_*/(2 L_*)` in `C¹([a₁-1,a₁+1])`) is not exported (it is an intermediate step of the normal-families proof of
`teb_quant_c1_typeII`); the constants are Lean's `quantC1*`, not the closed form `Ai'(a₁)²/(8 L_*)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special FormalResearch.ModularBootstrap.ConcreteBootstrap
  FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.Contour
  FormalResearch.ModularBootstrap.TipFront

private lemma log_mul_rpow_neg_le {c' α : ℝ} (hc' : 1 ≤ c') (hα : 0 < α) :
    c' ^ (-α) * Real.log c' ≤ (2 / α) * c' ^ (-(α / 2)) := by
  have hc'_pos : 0 < c' := by linarith
  have hlog : (α / 2) * Real.log c' ≤ c' ^ (α / 2) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hc'_pos (α / 2))
    rw [Real.log_rpow hc'_pos] at h
    linarith
  have hlog_bd : Real.log c' ≤ (2 / α) * c' ^ (α / 2) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / α)
    have h1 : (2 / α) * ((α / 2) * Real.log c') = Real.log c' := by
      field_simp [hα.ne']
    linarith [hmul]
  calc c' ^ (-α) * Real.log c'
      ≤ c' ^ (-α) * ((2 / α) * c' ^ (α / 2)) :=
        mul_le_mul_of_nonneg_left hlog_bd (Real.rpow_nonneg hc'_pos.le _)
    _ = (2 / α) * (c' ^ (-α) * c' ^ (α / 2)) := by ring
    _ = (2 / α) * c' ^ (-(α / 2)) := by
        rw [← Real.rpow_add hc'_pos]; ring_nf

/-- `ς_c = virasoroSigma c' → 0` (copy of the private `virasoroSigma_tendsto_zero`). -/
lemma virasoroSigma_tendsto_zero' : Tendsto virasoroSigma atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := virasoroSigma) (g := fun _ => (0 : ℝ))
    (h := fun c' => (6 * virasoroEnvC1) * c' ^ (-(1 / 6 : ℝ))) tendsto_const_nhds ?_ ?_ ?_
  · have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).const_mul
      (6 * virasoroEnvC1)
    simpa only [mul_zero] using h
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
    exact virasoroSigma_nonneg hc'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'
    unfold virasoroSigma
    have hbd := log_mul_rpow_neg_le hc' (by norm_num : (0 : ℝ) < 1 / 3)
    have hrw : (2 / (1 / 3 : ℝ)) * c' ^ (-((1 / 3 : ℝ) / 2)) =
        6 * c' ^ (-(1 / 6 : ℝ)) := by norm_num
    rw [hrw] at hbd
    calc virasoroEnvC1 * c' ^ (-(1 / 3 : ℝ)) * Real.log c'
        = virasoroEnvC1 * (c' ^ (-(1 / 3 : ℝ)) * Real.log c') := by ring
      _ ≤ virasoroEnvC1 * (6 * c' ^ (-(1 / 6 : ℝ))) :=
          mul_le_mul_of_nonneg_left hbd virasoroEnvC1_pos.le
      _ = (6 * virasoroEnvC1) * c' ^ (-(1 / 6 : ℝ)) := by ring

/-- **`rem:corL` at spinless Virasoro** (see the module docstring).  The statement is for every weakly feasible
test; (b)-(d) are for violating tests (`T < Δ(a₁)`). -/
theorem corL_virasoro :
    ∃ c₁ K : ℝ, virasoroCQEnv ≤ c₁ ∧ 0 ≤ K ∧ ∀ {c' T : ℝ}, c₁ ≤ c' → ∀ {g : ℝ → ℝ},
      virasoroProblem.IsWeaklyFeasible (c' / 12) T g →
      (∀ u : ℂ, u ∈ closedBall (0 : ℂ) (virasoroAC c' ^ 2) → ¬ (u.im = 0 ∧ u.re ≤ 0) →
        ‖virasoroPsiTilde c' g u‖ ≤
          virasoroEnvC0 * airyEnv u * Real.exp (virasoroSigma c' * (u ^ (1 / 2 : ℂ)).re) *
            ‖u‖ ^ (-(1 / 2 : ℝ)) * ((u ^ (1 / 2 : ℂ)).re)⁻¹) ∧
      (T < virasoroDeltaChart c' (airyZero 1) →
        airyZero 1 < virasoroUT c' T ∧
        virasoroUT c' T - airyZero 1 ≤ K * c' ^ (-(1 / 3 : ℝ)) ∧
        virasoroUT c' T - airyZero 1 ≤ 1 / 2 ∧
        QuantC1B2Holds (virasoroPsiTilde c' g) (virasoroUT c' T) ∧
        ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
          2 * quantC1KappaStar * (1 - θ) * (virasoroUT c' T - airyZero 1) ≤
            (virasoroPsiTilde c' g
              ((airyZero 1 + θ * (virasoroUT c' T - airyZero 1) : ℝ) : ℂ)).re) := by
  -- inputs
  obtain ⟨c_Q1, C_gap, κ_gap, hc_Q1, hC_gap, hκ_gap, hQ1⟩ := lemmaQ_part1
  obtain ⟨c_J, C_J, hcJ, hCJ, hJ⟩ := theoremFTLFW_oneZero_of_YVFor virasoroBVChoice_pos
    virasoroBVChoice_le yvInputFor_virasoroBVChoice
  have hQ_typeII := teb_quant_c1_typeII virasoroEnvC0_pos
    (fun c' => virasoroAC c' ^ 2) virasoroSigma (fun c' => C_gap * Real.exp (-κ_gap * c'))
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
      (mul_pos two_pos (pow_pos virasoroBV_pos 2)) |>.congr'
        (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with c' hc'
            rw [virasoroAC_sq c' hc']))
    (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with c' hc'; exact virasoroSigma_nonneg hc')
    virasoroSigma_tendsto_zero'
    (Eventually.of_forall fun c' => mul_nonneg hC_gap.le (Real.exp_pos _).le)
    (by
      have ht : Tendsto (fun c' : ℝ => -κ_gap * c') atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa only [mul_zero, Function.comp] using (Real.tendsto_exp_atBot.comp ht).const_mul C_gap)
  obtain ⟨c_1, hc_1, hQuant⟩ := hQ_typeII
  -- the size constant
  set K : ℝ := (C_J + 2) / cStar with hKdef
  have hK0 : 0 ≤ K := by have := cStar_pos; positivity
  set R0 : ℝ := |airyZero 1| + K + 1 with hR0def
  have hR0 : 0 ≤ R0 := by positivity
  have hev1 : ∀ᶠ c' : ℝ in atTop, chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * R0 ^ 2 ≤ 1 := by
    have ht : Tendsto (fun c' : ℝ => chartParams.C_xi * R0 ^ 2 * c' ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul
        (chartParams.C_xi * R0 ^ 2)
    filter_upwards [ht.eventually (Iic_mem_nhds zero_lt_one)] with c' hc'
    calc chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * R0 ^ 2
        = chartParams.C_xi * R0 ^ 2 * c' ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ 1 := hc'
  have hev2 : ∀ᶠ c' : ℝ in atTop, R0 ≤ virasoroAC c' ^ 2 := by
    have ht : Tendsto (fun c' : ℝ => 2 * virasoroBV ^ 2 * c' ^ (2 / 3 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_mul_atTop
        (mul_pos two_pos (pow_pos virasoroBV_pos 2))
    filter_upwards [ht.eventually_ge_atTop R0, eventually_ge_atTop (0 : ℝ)] with c' hc' hc'0
    rwa [virasoroAC_sq c' hc'0]
  obtain ⟨c_ev, hc_ev⟩ := eventually_atTop.1 (hev1.and hev2)
  set c₁ : ℝ := max virasoroCQEnv (max c_Q1 (max c_1 (max c_J c_ev))) with hc₁def
  refine ⟨c₁, K, le_max_left _ _, hK0, fun {c' T} hc' {g} hg => ?_⟩
  have hc'_Qenv : virasoroCQEnv ≤ c' := (le_max_left _ _).trans hc'
  have hc'_Q1 : c_Q1 ≤ c' := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hc')
  have hc'_1 : c_1 ≤ c' :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hc'))
  have hc'_J : c_J ≤ c' :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hc')))
  have hc'_ev : c_ev ≤ c' :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hc')))
  obtain ⟨hev1', hev2'⟩ := hc_ev c' hc'_ev
  have hc'_10000 : 10000 ≤ c' :=
    (by unfold c_PJ_complex; norm_num : (10000 : ℝ) ≤ c_PJ_complex).trans
      (c_PJ_complex_le_virasoroCQEnv.trans hc'_Qenv)
  have hc'_pos : 0 < c' := by linarith
  have hc'_ge1 : 1 ≤ c' := by linarith
  obtain ⟨hM_pos, hdl_bd, hdl_half, hT_A2⟩ := hQ1 hc'_Q1 hg
  have hQ2 := lemmaQ_part2 hc'_Qenv hg.1 hM_pos
  refine ⟨hQ2.2.2, fun hT_lt => ?_⟩
  have hQ3 := lemmaQ_part3 hc'_Qenv hg
  obtain ⟨ha1_lo, ha1_hi⟩ := airyZero_one
  have ha1_neg : airyZero 1 < 0 := by linarith
  have ha1_abs : |airyZero 1| = -airyZero 1 := abs_of_neg ha1_neg
  have hA2_ge : |airyZero 1| + 1 ≤ virasoroAC c' ^ 2 := by
    have : 0 ≤ K := hK0
    linarith [hR0def, hev2']
  have hA2_nn : 0 ≤ virasoroAC c' ^ 2 := sq_nonneg _
  have hsA : StrictAntiOn (virasoroDeltaChart c')
      (Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2)) := virasoroDeltaChart_strictAnti hc'_pos
  have ha1_mem : airyZero 1 ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨by linarith [abs_nonneg (airyZero 1)], by linarith⟩
  have hnegA2_mem : -(virasoroAC c' ^ 2) ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) :=
    ⟨le_rfl, by linarith⟩
  have hT_lt_neg : T < virasoroDeltaChart c' (-(virasoroAC c' ^ 2)) :=
    hT_lt.trans (hsA hnegA2_mem ha1_mem (by linarith))
  have huT_Ioo := hQ3.2.2.1 hT_lt_neg hT_A2
  have hu_mem := virasoroUT_between hc'_pos (a := -(virasoroAC c' ^ 2)) (b := virasoroAC c' ^ 2)
    le_rfl le_rfl (by linarith) hT_A2.le hT_lt_neg.le
  set u_T := virasoroUT c' T with huTdef
  have huT_Icc : u_T ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := hu_mem.1
  have ha1_lt_uT : airyZero 1 < u_T := by
    by_contra hle
    have := hsA.antitoneOn huT_Icc ha1_mem (not_lt.mp hle)
    linarith [hu_mem.2]
  -- (d): the size bound from Theorem J
  have hAopt_eq : Aopt = -cStar * airyZero 1 := by
    unfold Aopt
    rw [abs_of_neg ha1_neg]
    ring
  have hc13_pos : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'_pos _
  have hc13_mul : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hc'_pos]; norm_num
  have hcm13_le : c' ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hc'_ge1 (by norm_num)
  have hcm13_nn : 0 ≤ c' ^ (-(1 / 3 : ℝ)) := (Real.rpow_pos_of_pos hc'_pos _).le
  set u₂ : ℝ := airyZero 1 + K * c' ^ (-(1 / 3 : ℝ)) with hu₂def
  have hu₂_abs : |u₂| ≤ R0 := by
    have h1 : K * c' ^ (-(1 / 3 : ℝ)) ≤ K := by nlinarith only [hK0, hcm13_le]
    have h2 : 0 ≤ K * c' ^ (-(1 / 3 : ℝ)) := mul_nonneg hK0 hcm13_nn
    rw [abs_le]
    constructor <;> linarith [abs_nonneg (airyZero 1), le_abs_self (airyZero 1),
      neg_abs_le (airyZero 1), hR0def]
  have hu₂_mem : u₂ ∈ Icc (-(virasoroAC c' ^ 2)) (virasoroAC c' ^ 2) := by
    have := abs_le.mp hu₂_abs
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have herr := virasoro_deltaChart_err hc'_pos (hu₂_abs.trans hev2')
  have hu₂sq : u₂ ^ 2 ≤ R0 ^ 2 := by
    rw [← sq_abs u₂]; exact pow_le_pow_left₀ (abs_nonneg _) hu₂_abs 2
  have hCxi_nn := chartParams.hCxi_nn
  have herr' : chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u₂ ^ 2 ≤ 1 := by
    calc chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * u₂ ^ 2
        ≤ chartParams.C_xi * c' ^ (-(1 / 3 : ℝ)) * R0 ^ 2 := by gcongr
      _ ≤ 1 := hev1'
  have hΔu₂ : virasoroDeltaChart c' u₂ ≤ xiBar * c' - cStar * c' ^ (1 / 3 : ℝ) * u₂ + 1 := by
    have := (abs_le.mp herr).2
    linarith
  have hlin : cStar * c' ^ (1 / 3 : ℝ) * u₂ = -Aopt * c' ^ (1 / 3 : ℝ) + cStar * K := by
    rw [hu₂def, hAopt_eq]
    have : cStar * c' ^ (1 / 3 : ℝ) * (airyZero 1 + K * c' ^ (-(1 / 3 : ℝ))) =
        cStar * c' ^ (1 / 3 : ℝ) * airyZero 1 + cStar * K * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ))) := by
      ring
    rw [this, hc13_mul]; ring
  have hcK : cStar * K = C_J + 2 := by
    rw [hKdef]; have := cStar_pos; field_simp
  have hJT := hJ hc'_J hg
  have hΔu₂_lt : virasoroDeltaChart c' u₂ < T := by
    rw [hlin, hcK] at hΔu₂
    linarith [hJT]
  have huT_lt_u₂ : u_T < u₂ := by
    by_contra hle
    have := hsA.antitoneOn hu₂_mem huT_Icc (not_lt.mp hle)
    linarith [hu_mem.2]
  have hd : u_T - airyZero 1 ≤ K * c' ^ (-(1 / 3 : ℝ)) := by
    have : u_T < airyZero 1 + K * c' ^ (-(1 / 3 : ℝ)) := huT_lt_u₂
    linarith
  -- (b), (c): `teb_quant_c1_typeII`
  have hB2 : QuantC1B2Holds (virasoroPsiTilde c' g) u_T := by
    refine hQuant c' hc'_1 (virasoroPsiTilde c' g) u_T ?_ ?_ ?_ ha1_lt_uT huT_Ioo.2.le ?_ hQ3.2.1 ?_ ?_
    · exact hQ2.1.mono fun z hz => virasoro_closedBall_subset_psiDom hc'_pos hz
    · intro x hx
      exact (hQ2.2.1 x (abs_le.mpr hx)).1
    · intro u hu hcut
      exact hQ2.2.2 u hu hcut
    · intro x hx
      have hT_le : T ≤ virasoroDeltaChart c' x := by
        rw [← hu_mem.2]
        exact hsA.antitoneOn ⟨hx.1, hx.2.trans huT_Ioo.2.le⟩ huT_Icc hx.2
      exact hQ3.1 x (abs_le.mpr ⟨hx.1, hx.2.trans huT_Ioo.2.le⟩) hT_le
    · have h_half := hQ3.2.2.2.1 hT_lt_neg hT_A2.le
      linarith [h_half.2.2, hdl_bd]
    · intro R' hR'_mem hR'_uT
      have hT_le_R' : T ≤ virasoroDeltaChart c' (-R') := by
        rw [← hu_mem.2]
        exact hsA.antitoneOn ⟨by linarith [hR'_mem.2], by linarith [hR'_mem.1, hR'_mem.2]⟩ huT_Icc hR'_uT
      exact (hQ3.2.2.2.2 R' hR'_mem.1 hR'_mem.2 hT_le_R').2.trans hdl_bd
  have huT_pos : 0 ≤ (virasoroPsiTilde c' g (u_T : ℂ)).re :=
    hQ3.1 u_T (abs_le.mpr huT_Icc) (by rw [hu_mem.2])
  have hx_half : u_T - airyZero 1 ≤ 1 / 2 :=
    (hB2.1.trans (min_le_left _ _)).trans quantC1DeltaStar_le
  refine ⟨ha1_lt_uT, hd, hx_half, hB2, fun θ hθ0 hθ1 => ?_⟩
  exact quantC1B2_secant_lower (R_dom := virasoroAC c' ^ 2) hA2_ge
    (hQ2.1.mono fun z hz => virasoro_closedBall_subset_psiDom hc'_pos hz) ha1_lt_uT huT_pos hB2 hθ0 hθ1

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.corL_virasoro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.corL_virasoro
