module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BandBoundWInstance

/-!
# Proposition `Y_V` (Band Bound) and Proposition `X_V` at Every Fixed `(w, Q)`

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J2 (`Proposition X_V`, `vlo:XV`) and §J4
(`Proposition Y_V`, `vlo:YV`), with the shared strip band reduction
`CFT/common/two_edge_bootstrap.tex`, Proposition TE.3(1) (`teb:mellin`).

For `prob : FixedWeightProblem` (weight `w = prob.w ≥ 1`, any null-state product `Q`) and any
Langer chart `pg : LangerChartSpec`:

* `ywBandInstance_moments`: on the instance of `BandBoundWInstance`, `W̃ = M⁻¹ W̃_V`,
  `ũ (Δ(u)) = u`, `B₁ = R⁻¹ ∫_{[T, Δ(-R)]} (-ũ) g V/M`, `B₂ = ∫_{[Δ(-R), ∞)} g V/M`;
* `proposition_YV_inst_W`, `proposition_YV_of_spec_W`: parametric form of Proposition `Y_V`: for
  `c' ≥ c₀`, `R ∈ [b² c'^{2/3}, b² c'^{2/3} + 1]`, `g ∈ TestClass prob (c'/12)` with `M[g] > 0`, `g ≥ 0`
  on `[T, ∞)`, `Δ(0) ≤ T ≤ Δ(-A_thr)`, on `S = {ρ_R/3 ≤ |ζ₀| ≤ 2ρ_R, cos ψ ≥ c'^{-1/12}}`
  `‖W̃_V(ζ₀)‖ ≤ M[g] C_Y c'^{-5/6} (c'^{1/3}(B₁+B₂) + c'^{-1/6}) / cos ψ` (and the second form of
  `teb:wbound`), with `C_Y, c₀, b` depending on `(prob, A_thr)` only;
* `proposition_YV_W`: the unconditional Proposition `Y_V` for `pg = langerChartSpec_virasoro`
  (the Langer chart is weight free);
* `proposition_XV_W`: Proposition `X_V` (`B₁ + B₂ ≤ C_X (1 + log L) c'^{-1/3}`) for any
  `TwoEdgeBootstrap.BootstrapInstance`, i.e. the shared bootstrap (Theorem TE.2(1)); weight enters only
  through the construction of the instance from `wone:Q`;
* `proposition_YV_XV_W`: the combination `‖W̃_V(ζ₀)‖ ≤ M C_Y c'^{-5/6}(C_X(1+log L) + c'^{-1/6})/cos ψ`.

The Virasoro `StripMultiplier.proposition_YV` is the `w = 1` instance (`BandBoundWBridge`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing Chart ChartGeometry StripBand
open FormalResearch.TwoEdgeBootstrap
open FormalResearch.ModularBootstrap.StripMultiplier

/-! ### Section 1: Exact formulas for the moments -/

/-- Exact bridge formulas for `W_tilde`, `u_tilde`, `bandB1`, `bandB2` on `ywBandInstance`: on `[T, ∞)`,
`g ≥ 0`, so `dmPos = (g V/M) dt` and `u_tilde (Δ u) = u`. -/
lemma ywBandInstance_moments (prob : FixedWeightProblem) (pg : LangerChartSpec) {A_thr c' R T : ℝ}
    (hA_thr : 0 ≤ A_thr)
    (hc' : ywThresh prob pg A_thr ≤ c')
    (hR_lb : (ywBandParams prob pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (ywBandParams prob pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T)
    (hT_hi : T ≤ langerDelta pg c' (-A_thr))
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t) :
    let I := ywBandInstance prob pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
    let M := prob.cardyNorm (c' / 12) g
    (∀ ζ : ℂ, I.W_tilde ζ = ((M⁻¹ : ℝ) : ℂ) * tildeWW prob.w c' g ζ) ∧
    (∀ u ∈ Icc (-R) 0, I.u_tilde (langerDelta pg c' u) = u) ∧
    bandB1 I = R⁻¹ * ∫ t in Icc T (langerDelta pg c' (-R)),
      (-I.u_tilde t) * (g t * prob.cardyV (c' / 12) t / M) ∧
    bandB2 I = ∫ t in Ici (langerDelta pg c' (-R)),
      g t * prob.cardyV (c' / 12) t / M := by
  intro I M
  have hc'_yv : yvThresh pg A_thr ≤ c' := ywThresh_ge_yv hc'
  have hR_lb' : (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R := hR_lb
  have hR_ub' : R ≤ (yvBandParams pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 := hR_ub
  have hc'_max : max 1 (24 * prob.totalShift) ≤ c' :=
    (ywWitness prob).hc_W.trans (ywThresh_ge_c_W hc')
  have hshift : prob.totalShift ≤ c' / 12 := (shift_le_of_max_le prob hc'_max).1
  have hT_pos : 0 < T := by
    have h0 : 0 < langerDelta pg c' 0 := by
      rw [langerDelta_zero]
      have := xiStar_pos
      have : 0 < c' := (shift_le_of_max_le prob hc'_max).2.2
      positivity
    exact lt_of_lt_of_le h0 hT_lo
  have hProps := langerDelta_props hc'_yv hR_lb' hR_ub'
  have hfPos_meas := bandPos_aemeasurable hg
  have hfPos_nn := fun t (ht : t ∈ Ioi (0 : ℝ)) => bandPos_nonneg hshift hg (mem_Ioi.mp ht).le
  have hfPos_int := bandPos_integrableOn hshift hg
  have hfun : ∀ t ∈ Ici T, bandPos prob (c' / 12) g t = g t * prob.cardyV (c' / 12) t / M := by
    intro t ht
    unfold bandPos
    rw [max_eq_left (hg_nonneg t ht)]
  refine ⟨fun _ => by dsimp [I, ywBandInstance], fun u hu => ?_, ?_, ?_⟩
  · simpa [I, ywBandInstance] using langerNegV_inv_delta hc'_yv hR_lb' hR_ub' hu
  · dsimp only [bandB1, I, ywBandInstance, bandMeasPos]
    congr 1
    simp only [neg_neg]
    have hsub_Icc : Icc T (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) :=
      fun t ht => lt_of_lt_of_le hT_pos ht.1
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hfPos_meas.ennreal_ofReal.restrict
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun t => langerNegV pg c' R t)
      measurableSet_Icc]
    have h_meas_eq : (volume.restrict (Ioi 0)).restrict (Icc T (langerDelta pg c' (-R))) =
        volume.restrict (Icc T (langerDelta pg c' (-R))) := by
      rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsub_Icc]
    change ∫ t, (ENNReal.ofReal (bandPos prob (c' / 12) g t)).toReal • langerNegV pg c' R t
        ∂((volume.restrict (Ioi 0)).restrict (Icc T (langerDelta pg c' (-R)))) = _
    rw [h_meas_eq]
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [ENNReal.toReal_ofReal (hfPos_nn t (mem_Ioi.mpr (lt_of_lt_of_le hT_pos ht.1))),
      smul_eq_mul, mul_comm, hfun t ht.1]
  · have hB2_eq : bandB2 I = (((volume.restrict (Ioi 0)).withDensity
        (fun s => ENNReal.ofReal (bandPos prob (c' / 12) g s)))
          (Ici (langerDelta pg c' (-R)))).toReal := by
      dsimp only [bandB2, I, ywBandInstance, bandMeasPos]
    rw [hB2_eq, withDensity_apply _
      (measurableSet_Ici : MeasurableSet (Ici (langerDelta pg c' (-R))))]
    have hsub : Ici (langerDelta pg c' (-R)) ⊆ Ioi (0 : ℝ) := by
      have h0_lt : 0 < langerDelta pg c' 0 := by
        rw [langerDelta_zero]
        have := xiStar_pos
        have : 0 < c' := (shift_le_of_max_le prob hc'_max).2.2
        positivity
      have h_mono := hProps.2.2.2.2.1.monotoneOn ⟨le_rfl, hProps.1.le⟩ ⟨hProps.1.le, le_rfl⟩
        hProps.1.le
      rw [neg_zero] at h_mono
      exact fun t ht => lt_of_lt_of_le (lt_of_lt_of_le h0_lt h_mono) ht
    have hfPos_int_tail : IntegrableOn (bandPos prob (c' / 12) g) (Ici (langerDelta pg c' (-R))) :=
      hfPos_int.mono_set hsub
    have hl_eq : ∫⁻ a in Ici (langerDelta pg c' (-R)),
        ENNReal.ofReal (bandPos prob (c' / 12) g a) ∂(volume.restrict (Ioi 0)) =
        ∫⁻ a in Ici (langerDelta pg c' (-R)), ENNReal.ofReal (bandPos prob (c' / 12) g a) := by
      rw [Measure.restrict_restrict measurableSet_Ici, inter_eq_left.mpr hsub]
    rw [hl_eq, ← ofReal_integral_eq_lintegral_ofReal hfPos_int_tail
        (ae_restrict_of_forall_mem measurableSet_Ici fun t ht => hfPos_nn t (hsub ht)),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ici fun t ht => hfPos_nn t (hsub ht))]
    refine setIntegral_congr_fun measurableSet_Ici fun t ht => ?_
    have ht_T : T ≤ t := by
      have hA_le : langerDelta pg c' (-A_thr) ≤ langerDelta pg c' (-R) :=
        hProps.2.2.2.2.1.monotoneOn ⟨hA_thr, (le_max_left A_thr 1).trans hProps.2.2.1⟩
          ⟨hProps.1.le, le_rfl⟩ ((le_max_left A_thr 1).trans hProps.2.2.1)
      linarith [mem_Ici.mp ht]
    exact hfun t ht_T

/-! ### Section 2: Proposition `Y_V` -/

/-- **Proposition `Y_V` at weight `w` (instance form)** (`lower_o1_two_edge.tex`, §J4, `vlo:YV`):
explicit `BandReductionInstance` band bound on `S` for `c' ≥ ywThresh` and
`R ∈ [P.b² c'^{2/3}, P.b² c'^{2/3} + 1]`. -/
theorem proposition_YV_inst_W (prob : FixedWeightProblem) (pg : LangerChartSpec) {A_thr c' R T : ℝ}
    (hA_thr : 0 ≤ A_thr)
    (hc' : ywThresh prob pg A_thr ≤ c')
    (hR_lb : (ywBandParams prob pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R)
    (hR_ub : R ≤ (ywBandParams prob pg A_thr).b ^ 2 * c' ^ (2 / 3 : ℝ) + 1)
    (hT_lo : langerDelta pg c' 0 ≤ T)
    (hT_hi : T ≤ langerDelta pg c' (-A_thr))
    {g : ℝ → ℝ} (hg : TestClass prob (c' / 12) g)
    (hM_pos : 0 < prob.cardyNorm (c' / 12) g)
    (hg_nonneg : ∀ t ∈ Ici T, 0 ≤ g t)
    {ζ₀ : ℂ} {ψ : ℝ}
    (hlo : rhoR (ywBandParams prob pg A_thr) c' R / 3 ≤ ‖ζ₀‖)
    (hhi : ‖ζ₀‖ ≤ 2 * rhoR (ywBandParams prob pg A_thr) c' R)
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ)
    (hcos_lb : c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ) :
    let P := ywBandParams prob pg A_thr
    let I := ywBandInstance prob pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
    ‖tildeWW prob.w c' g ζ₀‖ ≤ prob.cardyNorm (c' / 12) g *
      (tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) ∧
    ‖tildeWW prob.w c' g ζ₀‖ ≤ prob.cardyNorm (c' / 12) g *
      (tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) := by
  intro P I
  have hlo' : rhoR P I.c I.R / 3 ≤ ‖ζ₀‖ := by dsimp [I, ywBandInstance]; exact hlo
  have hhi' : ‖ζ₀‖ ≤ 2 * rhoR P I.c I.R := by dsimp [I, ywBandInstance]; exact hhi
  have hcos_lb' : I.c ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ := by
    dsimp [I, ywBandInstance]; exact hcos_lb
  have hred := teb_band_reduction I hlo' hhi' hcos_eq hcos_lb'
  have hW_eq : ‖I.W_tilde ζ₀‖ =
      (prob.cardyNorm (c' / 12) g)⁻¹ * ‖tildeWW prob.w c' g ζ₀‖ := by
    have hI_W : I.W_tilde ζ₀ =
        ((prob.cardyNorm (c' / 12) g : ℝ)⁻¹ : ℂ) * tildeWW prob.w c' g ζ₀ := by
      dsimp only [I, ywBandInstance]; simp only [Complex.ofReal_inv]
    rw [hI_W, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM_pos.le]
  rw [hW_eq] at hred
  have hIc : I.c = c' := by dsimp only [I, ywBandInstance]
  have hred' : (prob.cardyNorm (c' / 12) g)⁻¹ * ‖tildeWW prob.w c' g ζ₀‖ ≤
      tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ ∧
      (prob.cardyNorm (c' / 12) g)⁻¹ * ‖tildeWW prob.w c' g ζ₀‖ ≤
      tebBandConst P * c' ^ (-(5 / 6 : ℝ)) *
        (c' ^ (1 / 3 : ℝ) * (bandB1 I + bandB2 I) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ))) := by
    simpa only [hIc] using hred
  refine ⟨?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left hred'.1 hM_pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at h1
  · have h2 := mul_le_mul_of_nonneg_left hred'.2 hM_pos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hM_pos.ne', one_mul] at h2

/-- **Proposition `Y_V` at weight `w` (parametric `LangerChartSpec` form)**
(`lower_o1_two_edge.tex`, §J4, `vlo:YV`): the constants `c₀, C_Y, b` depend on `(prob, A_thr)` only. -/
theorem proposition_YV_of_spec_W (prob : FixedWeightProblem) (pg : LangerChartSpec) {A_thr : ℝ}
    (hA_thr : 0 ≤ A_thr) :
    ∃ (c₀ C_Y b : ℝ), 10000 ≤ c₀ ∧ 0 < C_Y ∧ 0 < b ∧
      ∀ {c' R T : ℝ}, c₀ ≤ c' →
        b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R → R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 →
        langerDelta pg c' 0 ≤ T → T ≤ langerDelta pg c' (-A_thr) →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
          (∀ t ∈ Ici T, 0 ≤ g t) →
          ∃ u_tilde : ℝ → ℝ,
            (∀ u ∈ Icc (-R) 0, u_tilde (langerDelta pg c' u) = u) ∧
            let M := prob.cardyNorm (c' / 12) g
            let B₁ := R⁻¹ * ∫ t in Icc T (langerDelta pg c' (-R)),
              (-u_tilde t) * (g t * prob.cardyV (c' / 12) t / M)
            let B₂ := ∫ t in Ici (langerDelta pg c' (-R)),
              g t * prob.cardyV (c' / 12) t / M
            0 ≤ B₁ ∧ 0 ≤ B₂ ∧
            ∀ {ζ₀ : ℂ} {ψ : ℝ},
              kappaV * c' ^ (-(1 / 3 : ℝ)) * √R / 3 ≤ ‖ζ₀‖ →
              ‖ζ₀‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * √R) →
              ζ₀.re = ‖ζ₀‖ * Real.cos ψ →
              c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ →
              ‖tildeWW prob.w c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) ∧
              ‖tildeWW prob.w c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) := by
  let P := ywBandParams prob pg A_thr
  refine ⟨ywThresh prob pg A_thr, tebBandConst P, P.b,
    ywThresh_ge prob pg A_thr, tebBandConst_pos P, P.hb,
    fun {c' R T} hc' hR_lb hR_ub hT_lo hT_hi {g} hg hM_pos hg_nonneg => ?_⟩
  let I := ywBandInstance prob pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
  have hmom := ywBandInstance_moments prob pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos
    hg_nonneg
  refine ⟨I.u_tilde, hmom.2.1, ?_⟩
  dsimp only
  rw [← hmom.2.2.1, ← hmom.2.2.2]
  refine ⟨bandB1_nonneg I, bandB2_nonneg I, fun {ζ₀} {ψ} hlo hhi hcos_eq hcos_lb => ?_⟩
  have hρ_eq : rhoR P c' R = kappaV * c' ^ (-(1 / 3 : ℝ)) * √R := rfl
  exact proposition_YV_inst_W prob pg hA_thr hc' hR_lb hR_ub hT_lo hT_hi hg hM_pos hg_nonneg
    (hρ_eq.symm ▸ hlo) (hρ_eq.symm ▸ hhi) hcos_eq hcos_lb

/-- **Proposition `Y_V` at weight `w` (band bound, unconditional)** (`lower_o1_two_edge.tex`, §J4,
`vlo:YV`): for `prob : FixedWeightProblem` and `A_thr ≥ 0` there are `c₀ ≥ 10000`, `C_Y > 0`, `b > 0`
such that for `c' ≥ c₀`, `R ∈ [b² c'^{2/3}, b² c'^{2/3} + 1]`, `g ∈ TestClass prob (c'/12)` with
`M[g] > 0`, `g ≥ 0` on `[T, ∞)` and `T ∈ [Δ(0), Δ(-A_thr)]`, the band bound holds on
`S = {ρ_R/3 ≤ |ζ₀| ≤ 2 ρ_R, cos ψ ≥ c'^{-1/12}}`.  The Langer chart is
`ConcreteBootstrap.langerChartSpec_virasoro` (it does not depend on `(w, Q)`). -/
theorem proposition_YV_W (prob : FixedWeightProblem) {A_thr : ℝ} (hA_thr : 0 ≤ A_thr) :
    ∃ (c₀ C_Y b : ℝ), 10000 ≤ c₀ ∧ 0 < C_Y ∧ 0 < b ∧
      ∀ {c' R T : ℝ}, c₀ ≤ c' →
        b ^ 2 * c' ^ (2 / 3 : ℝ) ≤ R → R ≤ b ^ 2 * c' ^ (2 / 3 : ℝ) + 1 →
        langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' 0 ≤ T →
        T ≤ langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-A_thr) →
        ∀ {g : ℝ → ℝ}, TestClass prob (c' / 12) g →
          0 < prob.cardyNorm (c' / 12) g →
          (∀ t ∈ Ici T, 0 ≤ g t) →
          ∃ u_tilde : ℝ → ℝ,
            (∀ u ∈ Icc (-R) 0,
              u_tilde (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' u) = u) ∧
            let M := prob.cardyNorm (c' / 12) g
            let B₁ := R⁻¹ * ∫ t in Icc T
                (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-R)),
              (-u_tilde t) * (g t * prob.cardyV (c' / 12) t / M)
            let B₂ := ∫ t in Ici
                (langerDelta ConcreteBootstrap.langerChartSpec_virasoro c' (-R)),
              g t * prob.cardyV (c' / 12) t / M
            0 ≤ B₁ ∧ 0 ≤ B₂ ∧
            ∀ {ζ₀ : ℂ} {ψ : ℝ},
              kappaV * c' ^ (-(1 / 3 : ℝ)) * √R / 3 ≤ ‖ζ₀‖ →
              ‖ζ₀‖ ≤ 2 * (kappaV * c' ^ (-(1 / 3 : ℝ)) * √R) →
              ζ₀.re = ‖ζ₀‖ * Real.cos ψ →
              c' ^ (-(1 / 12 : ℝ)) ≤ Real.cos ψ →
              ‖tildeWW prob.w c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) ∧
              ‖tildeWW prob.w c' g ζ₀‖ ≤ M *
                (C_Y * c' ^ (-(5 / 6 : ℝ)) *
                  (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) / Real.cos ψ + c' ^ (-(1 / 12 : ℝ)))) :=
  proposition_YV_of_spec_W prob ConcreteBootstrap.langerChartSpec_virasoro hA_thr

/-! ### Section 3: Proposition `X_V` and the combination -/

/-- **Proposition `X_V` at every fixed `(w, Q)`** (`lower_o1_two_edge.tex`, §J2, `vlo:XV`):
any `TwoEdgeBootstrap.BootstrapInstance P` (obtained from `(B1)–(B2)` of `teb:bootstrap` applied to the
exact density of `wone:Q` at `(w, Q)`) satisfies `B₁ + B₂ ≤ C_X (1 + log L) c'^{-1/3}` for
`c ≥ tebC2 P`.  The statement is the weight-free `teb_bootstrap_part1` (Theorem TE.2(1)): the weight
enters only through the verification of `(B1)–(B2)`. -/
theorem proposition_XV_W (P : BootstrapParams) (I : BootstrapInstance P) (hc : tebC2 P ≤ I.c) :
    I.B_1 + I.B_2 ≤ tebCX P * (1 + Real.log I.L) * I.c ^ (-(1 / 3 : ℝ)) :=
  teb_bootstrap_part1 P I hc

/-- **`Y_V` combined with `X_V`**: if the band moments `B₁ + B₂` of a violator obey the bound of
Proposition `X_V`, then the band bound reads
`‖W̃_V(ζ₀)‖ ≤ M C_Y c'^{-5/6} (C_X (1 + log L) + c'^{-1/6})/cos ψ` (first form of `teb:wbound`). -/
theorem proposition_YV_XV_W {c' C_Y C_X L B₁ B₂ M W ψ : ℝ} (hc' : 0 < c') (hCY : 0 < C_Y)
    (hM : 0 ≤ M) (hcos : 0 < Real.cos ψ)
    (hB : B₁ + B₂ ≤ C_X * (1 + Real.log L) * c' ^ (-(1 / 3 : ℝ)))
    (hW : W ≤ M * (C_Y * c' ^ (-(5 / 6 : ℝ)) *
      (c' ^ (1 / 3 : ℝ) * (B₁ + B₂) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ)) :
    W ≤ M * (C_Y * c' ^ (-(5 / 6 : ℝ)) *
      (C_X * (1 + Real.log L) + c' ^ (-(1 / 6 : ℝ))) / Real.cos ψ) := by
  refine hW.trans (mul_le_mul_of_nonneg_left ?_ hM)
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_
    (mul_pos hCY (Real.rpow_pos_of_pos hc' _)).le) hcos.le
  have hc13 : 0 ≤ c' ^ (1 / 3 : ℝ) := Real.rpow_nonneg hc'.le _
  have hmul := mul_le_mul_of_nonneg_left hB hc13
  have hcancel : c' ^ (1 / 3 : ℝ) * (C_X * (1 + Real.log L) * c' ^ (-(1 / 3 : ℝ))) =
      C_X * (1 + Real.log L) := by
    have h : c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc']; simp
    calc _ = C_X * (1 + Real.log L) * (c' ^ (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ))) := by ring
      _ = _ := by rw [h, mul_one]
  linarith

/-! ### Axiom verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.proposition_YV_of_spec_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_YV_of_spec_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.proposition_YV_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_YV_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.proposition_XV_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_XV_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.proposition_YV_XV_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposition_YV_XV_W

end FormalResearch.ModularBootstrap.FixedWeightBand
