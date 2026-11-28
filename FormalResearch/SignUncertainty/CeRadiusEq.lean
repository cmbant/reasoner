module

public import FormalResearch.SignUncertainty.CeHankelDefs
public import FormalResearch.SignUncertainty.EuclidCELift
public import FormalResearch.SignUncertainty.EuclidRadialProjection
public import FormalResearch.SignUncertainty.HankelInversion

/-!
# Integer-`d` Cohn--Elkies radius identification (`general_theorems.tex`, `thm:ct-upper` (ii))

For every integer `d ≥ 2`, `optimalL1CERadius d ^ 2 / 2 = hankelTCE ((d : ℝ) / 2)`.
Direction `≤`: `EuclidCELift.ceAdmissible_of_hankelPair` lifts any `IsHankelCEFeasible (d/2) T h g`
to `IsContinuousL1CEAdmissible d √(2T)`.
Direction `≥`: radial averaging (`SphereAverage.fourier_radialAvg`), radial Hankel transform
(`EuclidRadialHankel.fourier_radial_hankel`), and Hankel inversion (`HankelInversion.besselHankel_involutive`)
project any `IsContinuousL1CEAdmissible d r h` to `IsHankelCEFeasible (d/2) (r^2/2) G Ĝ`.
`EuclidHankelDictionary.sInf_sq_div_two_eq` matches the infima.

Headline theorem:
* `ce_radius`: discharges the `CtUpperCEInputs.ce_radius` field.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped Real FourierTransform

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

private lemma isHankelCEFeasible_pos_T {c T : ℝ} {h g : ℝ → ℝ} (H : IsHankelCEFeasible c T h g) :
    0 < T := by
  by_contra hT
  have hT0 : T = 0 := le_antisymm (not_lt.mp hT) H.T_nonneg
  have h0le := H.h_tail 0 (by linarith)
  linarith [H.origin, H.pos]

private lemma continuous_realAvg_of_continuous (n : ℕ) {f : EuclSp (n + 1) → ℝ} (hf : Continuous f) :
    Continuous (realAvg n f) := by
  unfold realAvg
  refine continuous_const.mul (continuous_iff_continuousAt.2 fun r₀ => ?_)
  have hc : Continuous (fun p : ℝ × USph (n + 1) => f (p.1 • (p.2 : EuclSp (n + 1)))) :=
    hf.comp ((continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨M, hM⟩ := ((isCompact_closedBall r₀ 1).prod isCompact_univ).exists_bound_of_continuousOn
    hc.continuousOn
  have : IsFiniteMeasure (sphMeas (n + 1)) := ⟨by
    unfold sphMeas
    rw [Measure.toSphere_apply_univ]
    simp only [finrank_euclideanSpace_fin]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) measure_ball_lt_top⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_ (integrable_const M) ?_
  · refine Eventually.of_forall fun r => ?_
    exact (hf.comp (continuous_subtype_val.const_smul r)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds r₀ zero_lt_one] with r hr
    refine Eventually.of_forall fun ω => ?_
    exact hM (r, ω) ⟨ball_subset_closedBall hr, mem_univ ω⟩
  · refine Eventually.of_forall fun ω => ?_
    exact (hf.comp (continuous_id.smul continuous_const)).continuousAt.tendsto

/-- **`ce_radius`** (`general_theorems.tex`, proof of `thm:ct-upper` (ii); `gt:7.9b`):
for every integer `d ≥ 2`, `r_CE(d)² / 2 = T_{d/2}^CE`. -/
theorem ce_radius (d : ℕ) (hd : 2 ≤ d) :
    optimalL1CERadius d ^ 2 / 2 = hankelTCE ((d : ℝ) / 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hc : (((n + 1 : ℕ) : ℝ) / 2) = ((n : ℝ) + 1) / 2 := by push_cast; ring
  have hc_half : (1 / 2 : ℝ) < ((n : ℝ) + 1) / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [hc]
  unfold optimalL1CERadius hankelTCE
  refine sInf_sq_div_two_eq ?_ ?_ ?_
  · rintro r ⟨h, hadm⟩
    exact hadm.r_pos
  · rintro r ⟨h, hadm⟩
    refine ⟨fun Δ => realAvg n h (√(2 * Δ)),
      besselHankelTransform (((n : ℝ) + 1) / 2) (fun Δ => realAvg n h (√(2 * Δ))), ?_⟩
    set G : ℝ → ℝ := fun Δ => realAvg n h (√(2 * Δ))
    set Ĝ : ℝ → ℝ := besselHankelTransform (((n : ℝ) + 1) / 2) G
    set hc_fn : EuclSp (n + 1) → ℂ := fun x => (h x : ℂ)
    have hf_int : Integrable hc_fn := Complex.ofRealCLM.integrable_comp hadm.integrable
    have hFG : ∀ x : EuclSp (n + 1), radialAvg hc_fn x = ((G (‖x‖ ^ 2 / 2) : ℝ) : ℂ) := by
      intro x
      have e : √(2 * (‖x‖ ^ 2 / 2)) = ‖x‖ := by
        rw [show 2 * (‖x‖ ^ 2 / 2) = ‖x‖ ^ 2 by ring]
        exact Real.sqrt_sq (norm_nonneg x)
      rw [radialAvg_ofReal]
      simp only [G, e]
    have hG_cont : ContinuousOn G (Ici 0) :=
      ((continuous_realAvg_of_continuous n hadm.continuous).comp
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))).continuousOn
    have hG_lift_int : Integrable (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) :=
      (integrable_radialAvg hf_int).congr (Eventually.of_forall hFG)
    have hG_int : IntegrableOn (fun Δ => G Δ * hankelRho0 (((n : ℝ) + 1) / 2) Δ) (Ioi 0) :=
      (integrable_radialLift_iff n hn G).1 hG_lift_int
    have hĜ_cont : ContinuousOn Ĝ (Ici 0) :=
      (besselHankelTransform_continuous hc_half hG_int).continuousOn
    have hF_avg : ∀ y : EuclSp (n + 1),
        ((Ĝ (‖y‖ ^ 2 / 2) : ℝ) : ℂ) =
          ((realAvg n (fun z => (𝓕 hc_fn z).re) ‖y‖ : ℝ) : ℂ) := by
      intro y
      have h1 := fourier_radial_hankel n hn hG_cont hG_lift_int y
      have h2 : (fun x : EuclSp (n + 1) => (G (‖x‖ ^ 2 / 2) : ℂ)) = radialAvg hc_fn :=
        funext fun x => (hFG x).symm
      rw [h2, fourier_radialAvg hf_int y] at h1
      have hre_sph : ∫ ω : USph (n + 1), 𝓕 hc_fn (‖y‖ • (ω : EuclSp (n + 1))) ∂sphMeas (n + 1) =
          ((∫ ω : USph (n + 1), (𝓕 hc_fn (‖y‖ • (ω : EuclSp (n + 1)))).re ∂sphMeas (n + 1) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        obtain ⟨him, _⟩ := hadm.fourier_nonneg (‖y‖ • (ω : EuclSp (n + 1)))
        exact Complex.ext rfl him
      rw [hre_sph] at h1
      rw [← h1]
      unfold realAvg
      push_cast
      rfl
    have hĜ_avg : ∀ Δ : ℝ, 0 ≤ Δ →
        Ĝ Δ = realAvg n (fun z => (𝓕 hc_fn z).re) (√(2 * Δ)) := by
      intro Δ hΔ
      set y : EuclSp (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) √(2 * Δ)
      have hy2 : ‖y‖ ^ 2 / 2 = Δ := by
        rw [PiLp.norm_single, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]; ring
      have hynorm : ‖y‖ = √(2 * Δ) := by
        rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h := Complex.ofReal_injective (hF_avg y)
      rwa [hy2, hynorm] at h
    have hĜ_lift_int : Integrable (fun x : EuclSp (n + 1) => (Ĝ (‖x‖ ^ 2 / 2) : ℂ)) := by
      have hfre : Integrable (fun z : EuclSp (n + 1) => ((𝓕 hc_fn z).re : ℂ)) :=
        Complex.ofRealCLM.integrable_comp (Complex.reCLM.integrable_comp hadm.fourier_integrable)
      refine (integrable_radialAvg hfre).congr (Eventually.of_forall fun y => ?_)
      rw [radialAvg_ofReal, ← hF_avg y]
    have hĜ_int : IntegrableOn (fun Δ => Ĝ Δ * hankelRho0 (((n : ℝ) + 1) / 2) Δ) (Ioi 0) :=
      (integrable_radialLift_iff n hn Ĝ).1 hĜ_lift_int
    have hĜ0 : Ĝ 0 = h 0 := by
      rw [hĜ_avg 0 le_rfl, mul_zero, Real.sqrt_zero, realAvg_zero]
      exact hadm.origin_eq.symm
    refine
      { h_cont := hG_cont
        g_cont := hĜ_cont
        h_int := hG_int
        g_int := hĜ_int
        g_eq := fun _ _ => rfl
        h_eq := fun Δ hΔ => besselHankel_involutive n hn hG_cont hG_int hĜ_cont hĜ_int hΔ
        origin := by rw [show G 0 = h 0 by simp [G, realAvg_zero], hĜ0]
        pos := by rw [hĜ0]; exact hadm.origin_pos
        g_nonneg := fun Δ hΔ => by
          rw [hĜ_avg Δ hΔ]
          exact realAvg_nonneg n (Real.sqrt_nonneg _) (le_refl 0 |>.trans (Real.sqrt_nonneg _))
            fun z _ => (hadm.fourier_nonneg z).2
        h_tail := fun Δ hΔ => by
          have hr_le : r ≤ √(2 * Δ) :=
            (Real.le_sqrt hadm.r_pos.le (by nlinarith [hadm.r_pos])).2 (by linarith)
          unfold G realAvg
          refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (sphTotal_pos n).le)
            (integral_nonpos fun ω => hadm.nonpos_outside _ ?_)
          rw [norm_smul_sphere _ (Real.sqrt_nonneg _)]
          exact hr_le
        T_nonneg := by positivity }
  · rintro T ⟨h, g, H⟩
    have hT : 0 < T := isHankelCEFeasible_pos_T H
    refine ⟨hT, fun x : Euc (n + 1) => h (‖x‖ ^ 2 / 2), ceAdmissible_of_hankelPair n hn hT H.h_cont H.h_int
      (fun Δ hΔ => by rw [H.g_eq Δ (mem_Ici.2 hΔ)]; exact H.g_nonneg Δ hΔ)
      (H.g_int.congr_fun (fun Δ (hΔ : 0 < Δ) => by rw [H.g_eq Δ (mem_Ici.2 hΔ.le)]) measurableSet_Ioi)
      (H.origin ▸ H.pos)
      (by rw [H.g_eq 0 (mem_Ici.2 le_rfl), H.origin])
      H.h_tail⟩

/-- info: 'FormalResearch.SignUncertainty.ce_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_radius

end FormalResearch.SignUncertainty
